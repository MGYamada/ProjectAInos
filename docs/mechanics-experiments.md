# Mechanics Experiment Tags

[verify_identities.py](../experiments/ainos_experiments/verify_identities.py) supplies symbolic identities and one numerical perturbation check for the [Mechanics research plan](landau-lifshitz.md#mechanics). These computations guide formalization; they are not Lean proofs. Section references below use Landau–Lifshitz Volume 1, third edition. The bracket convention is `{f,g} = Σ(f_q g_p − f_p g_q) = X_g(f)`, with `i_XH ω = dH`; the book's bracket is `[f,g]_LL = −{f,g}`.

The package pins SymPy 1.14.0 and its numerical dependency mpmath 1.3.0. From the repository root, use Python 3.12 or newer:

```sh
python3 -m venv experiments/.venv
experiments/.venv/bin/python -m pip install ./experiments
experiments/.venv/bin/python -m ainos_experiments.verify_identities
experiments/.venv/bin/python -m unittest discover -s experiments/tests -v
```

The first command below runs just the jet and numerical groups. The second shows the reusable, silent Python API. Importing the module creates no symbolic experiment state, prints nothing, and does not exit the interpreter. Each group constructs its own symbols and returns `CheckResult` values; groups do not depend on earlier groups having run.

```sh
experiments/.venv/bin/python -m ainos_experiments.verify_identities E9 E11
```

```python
from ainos_experiments.verify_identities import run_e9, run_groups

jet_results = run_e9()
selected_results = run_groups(["E4", "E10"])
assert all(result.ok for result in jet_results + selected_results)
```

The CLI prints the familiar `[PASS]`/`[FAIL]` lines and summary and exits with status 0 exactly when every selected check passes. Group names are E1–E11; duplicate or unknown names are rejected. A full run contains 47 uniquely tagged checks. The former duplicate `E4e` labels are now `E4e-r^k` and `E4e-x^2y^(k-2)`.

## E1: Hamiltonian and Poisson conventions

These checks support §§40 and 42, including the sign relating commutators of Hamiltonian vector fields to Poisson brackets. They use generic smooth symbolic functions of one canonical pair.

| Tag | Statement checked |
| --- | --- |
| `E1a` | Hamilton's equations: `{q,H}=H_p` and `{p,H}=−H_q`. |
| `E1b` | `[X_f,X_g](h)=−X_{ {f,g} }(h)`. |
| `E1c` | The canonical bracket satisfies the Jacobi identity, using equality of mixed second derivatives. |

These identities are now Lean theorems for any finite number of canonical pairs: E1a is `PhaseSpace.canonical_q_bracket` with `PhaseSpace.canonical_p_bracket`, E1b is `PoissonStructure.hamiltonian_bracket` in every Poisson C∞-ring, and E1c is the `jacobi` field of `PhaseSpace.canonical`. The experiment remains as independent evidence for the conventions.

## E2: Closedness and Jacobi

This checks the local geometric identity behind the symplectic/Poisson infrastructure for §§42 and 46. On four coordinates, the test form has blocks `dq₁∧dq₂ + (1+q₁²)dq₃∧dq₄`. It is nondegenerate but not closed. The Jacobiator is deliberately nonzero, so the check tests the sign of the closedness identity rather than silently using a symplectic example. The functions are explicit polynomials.

| Tag | Statement checked |
| --- | --- |
| `E2a` | For the inverse-form vector fields, `{f,g}=ω(X_f,X_g)=X_g(f)`. |
| `E2b` | `dω(X_f,X_g,X_h)=−({{f,g},h}+cyclic)`. |
| `E2c` | The tested Jacobiator is not identically zero. |

## E3: Cotangent momentum functions

For generic vector fields `X,Y` on two configuration coordinates, let `P_X=p·X`. These are local momentum-map identities for the targets around §§7, 9, and 42.

| Tag | Statement checked |
| --- | --- |
| `E3a` | `{f,P_X}=X(f)` for a configuration function `f`. |
| `E3b` | `{P_X,P_Y}=−P_[X,Y]`. |

## E4: Angular momentum, boosts, and virial identities

The variables are three canonical coordinate pairs. Angular momentum supports §9, boosts support §§3 and 8, and the instantaneous homogeneous-potential identity supports the analytic time-averaged virial target in §10. The experiment does not perform the time average.

| Tag | Statement checked |
| --- | --- |
| `E4a` | `{M_i,M_j}=ε_ijk M_k` for `M=q×p`, including all pairs of indices. |
| `E4b` | `{K_i,P_j}=m δ_ij` for `K=mq−tp`. |
| `E4c` | `∂K/∂t+{K,H₀}=0` for `H₀=p²/(2m)`. |
| `E4d` | `{K_i,K_j}=0`. |
| `E4e-r^k` | `{q·p,H}=2T−kU` for the radial homogeneous potential `U=r^k`. |
| `E4e-x^2y^(k-2)` | The same virial identity for `U=x²y^(k−2)`. |
| `E4f` | Free-particle boost quasi-invariance: `L(v+u)−L(v)=D_t(mq·u+m|u|²t/2)`, with `q'=v`. |

The homogeneous-power expressions are symbolic local identities on domains where the displayed potentials and derivatives are defined.

E4a is now a Lean theorem, `AngularMomentum.canonical_M_M`, for all pairs of indices. For one particle, E4b is `Galilei.canonical_K_p` and E4d is `Galilei.canonical_K_K`. E4c is proved as two statements, `Galilei.canonical_K_freeHamiltonian` and `Galilei.K_sub_K`, because time is a real parameter of the generator and not a coordinate of the phase space. The identity behind E4e is `PhaseSpace.virial`, with Euler's relation for the potential as a hypothesis; the potentials `r^k` and `x²y^(k−2)` of the experiment are not instantiated, and `r^k` is not an element of the free ring. `JetRing.conserved_boost` uses the infinitesimal form of E4f; the finite identity has no Lean counterpart.

## E5: Kepler and Rutherford identities

For `H=p²/(2m)−α/r`, set `M=q×p` and `A=p×M−mαq/r`, with `r=√(q·q)`. These support §§14–15 and 19 away from collision. They do not prove the existence or global completeness of the corresponding orbits.

| Tag | Statement checked |
| --- | --- |
| `E5a` | `{A_i,H}=0`. |
| `E5b` | `{M_i,A_j}=ε_ijk A_k`. |
| `E5c` | `{A_i,A_j}=−2mH ε_ijk M_k`. |
| `E5d` | `A·M=0`. |
| `E5e` | `|A|²=m²α²+2mH|M|²`. |
| `E5f` | The orbit identity `A·q=|M|²−mαr`. |
| `E5g` | Rutherford algebra: substituting `E=mv∞²/2` and `M=mρv∞` gives `cot²(χ/2)=e²−1=(mv∞²ρ/α)²`. |

E5a–f are now Lean theorems in every Kepler frame, where `1/r` is an element `ρ` with the brackets of the inverse distance and `ρ²(q·q)=1` is not assumed. E5b, E5d and E5f hold exactly: `Kepler.IsFrame.angularMomentum_rungeLenz`, `Kepler.rungeLenz_dotProduct_angularMomentum`, `Kepler.rungeLenz_dotProduct_q`. E5a, E5c and E5e hold up to explicit multiples of `ρ²(q·q)−1`: `Kepler.IsFrame.rungeLenz_hamiltonian`, `Kepler.IsFrame.rungeLenz_rungeLenz`, `Kepler.rungeLenz_dotProduct_self`. E5g has no Lean counterpart.

## E6: Rigid-body and heavy-top brackets

The body-frame bracket is `{F,G}=−L·(∇F×∇G)`. These checks support §§33–37 and the planned Poisson-reduction infrastructure.

| Tag | Statement checked |
| --- | --- |
| `E6a` | `{L₁,L₂}=−L₃` and the cyclic generator relations. |
| `E6b` | Euler's equations from `H=ΣL_i²/(2I_i)`. |
| `E6c` | `|L|²` Poisson-commutes with each generator. |
| `E6d` | Jacobi for generic symbolic functions of `L`. |
| `E6e` | At the representative inertias `(I₁,I₂,I₃)=(1,2,3)`, the linearized signs give unstable rotation about axis 2 and stable rotation about axes 1 and 3. |
| `E6f` | Heavy-top generator brackets, equations for `L` and `Γ`, Casimirs `|Γ|²` and `L·Γ`, and Jacobi on explicit polynomial test functions. |

E6e checks the stated representative numerical ordering, not a symbolic theorem for every ordered inertia triple. E6f's polynomial Jacobi check is likewise example-based.

E6a–d are now Lean theorems: E6a is `RigidBody.poisson_L_L`, E6b is `RigidBody.euler_equations` with its three components, E6c is `RigidBody.poisson_casimir_left` for every element and not only the generators, and E6d is the `jacobi` field of `RigidBody.poisson`, for all elements of the free C∞-ring. E6f is also a Lean theorem: the generator brackets are `HeavyTop.poisson_L_L`, `HeavyTop.poisson_L_Γ` and `HeavyTop.poisson_Γ_Γ`, the equations of motion are `HeavyTop.poisson_L_hamiltonian` and `HeavyTop.poisson_Γ_hamiltonian`, the Casimirs are `HeavyTop.poisson_Γ_sq_left` and `HeavyTop.poisson_L_dot_Γ_left`, and the Jacobi identity is the `jacobi` field of `HeavyTop.poisson`, for all elements and not only polynomial test functions. E6e has no Lean counterpart.

## E7: Singular reduction examples

These targets extend beyond the section-level Volume 1 correspondence. Set `s₁=q·q`, `s₂=p·p`, and `s₃=q·p`.

| Tag | Statement checked |
| --- | --- |
| `E7a` | `{s₁,s₂}=4s₃`, `{s₁,s₃}=2s₁`, and `{s₂,s₃}=−2s₂`. |
| `E7b` | `|q×p|²=s₁s₂−s₃²`. |
| `E7c` | `s₁s₂−s₃²` Poisson-commutes with `s₁,s₂,s₃`. |
| `E7d` | In one canonical pair, `{pb(q),pc(q)}=p(b'c−bc')`. |
| `E7e` | `{f,p²}=2p ∂f/∂q`. |

## E8: Dirac brackets

For a particle constrained to a circle, use `φ₁=q₁²+q₂²−1`, `φ₂=q₁p₁+q₂p₂`, and invert their bracket matrix. The formulas are checked where that matrix is invertible. This is another extension beyond the Volume 1 section map.

| Tag | Statement checked |
| --- | --- |
| `E8a` | Both constraints Dirac-commute with a generic function: `{F,φ_a}_D=0`. |
| `E8b` | The Dirac bracket satisfies Jacobi for three explicit polynomial functions. |

## E9: Jet calculus, energy, and Noether identities

The jet has two degrees of freedom, with coordinates `(t,q_i,v_i,a_i,j_i,k_i)`. Its total derivative differentiates through third-order jet inputs. These checks support §§2, 6–9 and the planned variational calculus.

| Tag | Statement checked |
| --- | --- |
| `E9a` | `E_i(D_t F)=0` for `F(t,q)`, for both indices. |
| `E9b` | `E_i(D_t G)=0` for `G(t,q,v)`, using the second-order Euler operator, for both indices. |
| `E9c` | `D_t(E_L)=−Σv_i E_i(L)−∂L/∂t`. |
| `E9d` | `pr(ξ)(L)=Σξ_i E_i(L)+D_t(Σξ_i ∂L/∂v_i)`. |
| `E9e` | `[∂/∂v_i,D_t]=∂/∂q_i` and `[∂/∂q_i,D_t]=0`, for **both** indices `i=0,1` (four residuals). |

The regression suite deliberately corrupts either index and requires E9e to fail in each case.

These identities are now Lean theorems in every jet C∞-ring, for any finite number of coordinates and any order: E9a and E9b are `JetRing.euler_totalDeriv`, E9c is `JetRing.totalDeriv_energy`, E9d is `JetRing.prolong_eq_euler_add_totalDeriv`, and E9e is `JetRing.d_succ_totalDeriv` with `JetRing.d_zero_totalDeriv`. The experiment remains as independent evidence for the conventions.

## E10: Canonical coordinates and rotating frames

These identities support §§13–14, 39, 44, and 45. Polar-coordinate expressions are local formulas away from their singularities.

| Tag | Statement checked |
| --- | --- |
| `E10a` | The polar variables `(r,φ,p_r,p_φ)` have canonical pairwise brackets. |
| `E10b` | `|p|²=p_r²+p_φ²/r²`. |
| `E10c` | The two-body kinetic energy splits into centre-of-mass and reduced-mass terms. |
| `E10d` | The rotating-frame Hamiltonian gives `q'=p/m−Ω×q`. |
| `E10e` | The rotating-frame acceleration includes the Coriolis and centrifugal terms with the stated signs. |
| `E10f` | `{g,f(H−E)}−f{g,H}=(H−E){g,f}`, the algebraic identity for Maupertuis reparametrization on the energy surface. |

E10f is now a Lean theorem in every Poisson C∞-ring, `PoissonStructure.bracket_mul_sub_algebraMap`, and `PoissonStructure.maupertuis` is its consequence modulo the ideal `(H − E)`. E10d is `RotatingFrame.canonical_q_hamiltonian`, and E10e is `RotatingFrame.canonical_velocity_hamiltonian`, for every potential that does not depend on the momenta. E10a–c have no Lean counterpart.

## E11: Anharmonic frequency shift

| Tag | Statement checked |
| --- | --- |
| `E11` | For `x''+x=−αx²−βx³`, the measured leading frequency shift is `(3β/8−5α²/12) A²`, with base frequency one (§28). |

The initial state is `(x,v)=(A,0)`, with `A>0` accelerating toward zero. The fixed cases are `(α,β)=(1,1),(0.7,−0.4),(0,1)` and amplitudes `A=0.04,0.02,0.01`. RK4 uses `dt=2×10⁻⁴`. The maximum time is 20 and the independent step budget is 200,000; either limit terminates an unsuccessful search.

The estimator resolves a negative-position minimum by a negative-to-positive velocity crossing, followed by a positive-position maximum with the opposite direction. It requires distinct, increasing crossing times. Times and positions are interpolated linearly using the bracketing velocity values; a zero at the right endpoint is counted once. The second turning point gives a full period from the initial maximum.

At every integration step it checks finiteness and the relative drift of

\[
E(x,v)=\frac{v^2+x^2}{2}+\frac{\alpha x^3}{3}+\frac{\beta x^4}{4}.
\]

The drift tolerance is `10⁻⁶`, normalized by `max(|E_initial|, A²/2)`. Invalid parameters raise `ValueError`; nonfinite evolution, excessive drift, unexpected crossings, and exhausted budgets raise `PeriodSearchError`. `estimate_period` returns the two turning points, step count, and maximum energy drift as well as the period. `period` returns just the validated period. E11 converts integration failures into a failed check with a diagnostic, rather than hanging or reporting a misleading coefficient discrepancy.

For each amplitude the runner computes `κ(A)=(2π/T(A)−1)/A²`. It extrapolates `2κ(0.01)−κ(0.02)` to remove the leading amplitude error and compares that value with `3β/8−5α²/12` using absolute tolerance `2×10⁻⁴`. This is deterministic numerical evidence for the coefficient, with no random seed or stochastic step. It is not a bound on the asymptotic remainder for arbitrary parameters.
