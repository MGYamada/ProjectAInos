"""Regression checks for the mechanics experiment runner and numerical guardrails."""
import contextlib
import io
import math
from pathlib import Path
import re
import subprocess
import sys
import unittest
from unittest.mock import patch

import sympy as sp
from ainos_experiments import verify_identities as experiments


MODULE = 'ainos_experiments.verify_identities'


class RunnerTests(unittest.TestCase):
    def test_import_is_silent_and_does_not_exit(self):
        process = subprocess.run(
            [sys.executable, '-c', f'import {MODULE}; print("import returned")'],
            capture_output=True, text=True, timeout=30, check=True)
        self.assertEqual(process.stdout, 'import returned\n')
        self.assertEqual(process.stderr, '')

    def test_standalone_group_cli(self):
        process = subprocess.run([sys.executable, '-m', MODULE, 'E9'],
                                 capture_output=True, text=True, timeout=60, check=True)
        self.assertEqual(re.findall(r'^\[PASS\] (E\S+):', process.stdout, re.M),
                         ['E9a', 'E9b', 'E9c', 'E9d', 'E9e'])
        self.assertIn('5/5 checks passed', process.stdout)
        self.assertEqual(process.stderr, '')

    def test_groups_are_independent_and_repeatable(self):
        # Run every group without executing another group to set up symbols.
        # Reversed order also detects an accidental dependence on predecessor state.
        expected_counts = {'E1': 3, 'E2': 3, 'E3': 2, 'E4': 7, 'E5': 7, 'E6': 6,
                           'E7': 5, 'E8': 2, 'E9': 5, 'E10': 6, 'E11': 1}
        with contextlib.redirect_stdout(io.StringIO()) as stdout:
            results = experiments.run_groups(list(reversed(experiments.GROUPS)))
            repeated = experiments.run_e9()
        self.assertEqual(stdout.getvalue(), '')
        self.assertEqual(len(results), 47)
        self.assertTrue(all(result.ok for result in results))
        for group, count in expected_counts.items():
            with self.subTest(group=group):
                self.assertEqual(sum(re.match(r'E\d+', result.tag).group() == group for result in results), count)
        self.assertEqual(repeated, [result for result in results if result.tag.startswith('E9')])
        self.assertEqual(len({result.tag for result in results}), 47)
        self.assertIn('E4e-r^k', {result.tag for result in results})
        self.assertIn('E4e-x^2y^(k-2)', {result.tag for result in results})
        guide = Path(__file__).resolve().parents[2] / 'docs' / 'mechanics-experiments.md'
        documented_tags = re.findall(r'^\| `(E[^`]+)` \|', guide.read_text(), re.M)
        self.assertEqual(len(documented_tags), 47)
        self.assertEqual(set(documented_tags), {result.tag for result in results})

    def test_main_success_and_failure_exit_status(self):
        for ok, code in ((True, 0), (False, 1)):
            with self.subTest(ok=ok), patch.dict(experiments.GROUPS, {
                    'E1': lambda: [experiments.CheckResult('E1a', ok, 'test result')]}):
                with contextlib.redirect_stdout(io.StringIO()) as stdout:
                    self.assertEqual(experiments.main(['E1']), code)
                self.assertIn(f"[{'PASS' if ok else 'FAIL'}] E1a: test result", stdout.getvalue())
                self.assertIn(f'{int(ok)}/1 checks passed', stdout.getvalue())

    def test_unknown_or_duplicate_groups_rejected(self):
        for groups in (['E12'], ['E1', 'E1']):
            with self.subTest(groups=groups), self.assertRaises(ValueError):
                experiments.run_groups(groups)

class JetCoverageTests(unittest.TestCase):
    def test_commutators_reject_a_broken_identity_at_either_index(self):
        qs = sp.symbols('q1 q2')
        vs = sp.symbols('v1 v2')
        function = sp.Function('G')(*qs, *vs)
        for broken_index in (0, 1):
            def broken_total_derivative(expr):
                return sum((2 if i == broken_index else 1) * vs[i] * sp.diff(expr, qs[i])
                           for i in range(2))

            residuals = experiments.jet_commutator_residuals(broken_total_derivative, function, qs, vs)
            self.assertEqual(residuals.shape, (4, 1))
            self.assertFalse(experiments.is_zero(residuals[2 * broken_index]))
            self.assertFalse(experiments.is_zero(residuals))

    def test_e9e_includes_both_indices(self):
        original = experiments.jet_commutator_residuals
        for broken_index in (0, 1):
            def corrupted(total_derivative, function, qs, vs):
                self.assertEqual((len(qs), len(vs)), (2, 2))
                def broken(expr):
                    return total_derivative(expr) + vs[broken_index] * sp.diff(expr, qs[broken_index])
                return original(broken, function, qs, vs)

            with patch.object(experiments, 'jet_commutator_residuals', corrupted):
                result = next(result for result in experiments.run_e9() if result.tag == 'E9e')
            self.assertFalse(result.ok, f'E9e failed to detect broken index {broken_index}')


class PeriodTests(unittest.TestCase):
    def test_harmonic_period_has_two_distinct_directed_crossings(self):
        estimate = experiments.estimate_period(0.0, 0.0, 0.1, dt=0.01)
        self.assertAlmostEqual(estimate.period, 2 * math.pi, delta=5e-7)
        first, second = estimate.crossings
        self.assertEqual((first.direction, second.direction), (1, -1))
        self.assertLess(first.position, 0)
        self.assertGreater(second.position, 0)
        self.assertGreater(first.time, 0)
        self.assertGreater(second.time, first.time)
        self.assertEqual(estimate.period, second.time)
        self.assertLess(estimate.max_relative_energy_drift, 1e-6)

    def test_invalid_and_stationary_data_fail_immediately(self):
        cases = [((0, 0, 0), {}), ((0, 0, -1), {}), ((0, 0, 1), {'dt': 0}),
                 ((math.nan, 0, 1), {}), ((0, 0, math.inf), {}),
                 ((0, 0, 1), {'max_steps': 0}), ((0, 0, 1), {'max_steps': 1.5}),
                 ((0, 0, 1), {'max_time': -1}), ((0, 0, 1), {'energy_tolerance': 0}),
                 ((-1, 0, 1), {}), ((-2, 0, 1), {}), ((0, 1, 1e308), {})]
        for args, kwargs in cases:
            with self.subTest(args=args, kwargs=kwargs), self.assertRaises(ValueError):
                experiments.period(*args, **kwargs)

    def test_time_and_step_budgets_are_enforced(self):
        for limits in ({'max_time': 0.01}, {'max_steps': 2}):
            with self.subTest(limits=limits), self.assertRaisesRegex(experiments.PeriodSearchError, 'exhausted'):
                experiments.period(0, 0, 0.1, **limits)

    def test_nonfinite_evolution_and_large_energy_drift_are_rejected(self):
        with self.assertRaisesRegex(experiments.PeriodSearchError, 'nonfinite'):
            experiments.period(0, 1, 1, dt=1e308, max_time=1e308)
        with self.assertRaisesRegex(experiments.PeriodSearchError, 'energy drift'):
            experiments.period(0, 0, 0.1, dt=0.5)

    def test_e11_reports_integration_failure_as_a_failed_check(self):
        with patch.object(experiments, 'period', side_effect=experiments.PeriodSearchError('test budget')):
            result, = experiments.run_e11()
        self.assertFalse(result.ok)
        self.assertIn('A^2', result.description)
        self.assertIn('integration failed: test budget', result.details[0])


if __name__ == '__main__':
    unittest.main()
