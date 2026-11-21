/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.SpecialFunctions.BesselZeros

open ProjectAinos.SpecialFunctions.Bessel Complex

noncomputable section

example (a z : ℂ) (hz : z ∈ slitPlane) :
    HasDerivAt (besselJ a) (a / z * besselJ a z - besselJ (a + 1) z) z := hasDerivAt_besselJ a z hz

example (a z : ℂ) (hz : z ∈ slitPlane) :
    besselJ (a - 1) z + besselJ (a + 1) z = 2 * a / z * besselJ a z := recurrence a z hz

example (a z : ℂ) (hz : z ∈ slitPlane) :
    2 * deriv (besselJ a) z = besselJ (a - 1) z - besselJ (a + 1) z := twice_deriv a z hz

example (a z : ℂ) (hz : z ∈ slitPlane) : z ^ 2 * deriv (deriv (besselJ a)) z +
    z * deriv (besselJ a) z + (z ^ 2 - a ^ 2) * besselJ a z = 0 := equation a z hz

example (n : ℕ) (z : ℂ) : HasSum (fun j : ℕ => (z / 2) ^ n * (-(z / 2) ^ 2) ^ j /
    ((j.factorial : ℂ) * (n + j).factorial)) (besselJ n z) := hasSum_nat n z

example (z : ℂ) {w : ℂ} (hw : w ≠ 0) :
    HasSum (fun k : ℤ => besselJ k z * w ^ k) (exp (z / 2 * (w - w⁻¹))) := hasSum_generating z hw

example (z : ℂ) (t : ℝ) : HasSum (fun k : ℤ => besselJ k z * exp ((k : ℂ) * (t * I)))
    (exp (z * Real.sin t * I)) := hasSum_jacobiAnger z t

example (k : ℤ) (x : ℝ) :
    besselJ k (x : ℂ) = ((1 / Real.pi * ∫ t in 0..Real.pi,
      Real.cos ((k : ℝ) * t - x * Real.sin t) : ℝ) : ℂ) := integral k x

example (k : ℤ) (x : ℝ) :
    deriv (besselJ k) (x : ℂ) = ((1 / Real.pi * ∫ t in 0..Real.pi,
      Real.sin ((k : ℝ) * t - x * Real.sin t) * Real.sin t : ℝ) : ℂ) := deriv_integral k x

example (n : ℤ) {z : ℂ} (hz : z ∈ slitPlane) (hn : besselJ n z = 0) :
    besselJ (n + 1 : ℤ) z ≠ 0 := adjacent_ne_zero n hz hn

example (n : ℤ) {z : ℂ} (hz : z ∈ slitPlane) (hn : besselJ n z = 0) :
    deriv (besselJ n) z ≠ 0 := deriv_ne_zero_of_zero n hz hn

example (n : ℤ) {a : ℝ} (ha : 2 * |(n : ℝ)| + 2 < a) :
    ∃ t ∈ Set.Ioo a (a + 2 * Real.pi), besselJ n (t : ℂ) = 0 := exists_zero_Ioo n ha

example : ∃ t ∈ Set.Ioo 3 (3 + 2 * Real.pi), besselJ 0 (t : ℂ) = 0 := by
  simpa using exists_zero_Ioo (0 : ℤ) (a := 3) (by norm_num)
