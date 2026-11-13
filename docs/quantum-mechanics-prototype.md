# Qubit comparison prototype for issue #45

This is a research prototype for the finite-dimensional comparison in issue
#45. Its public API remains provisional, and Section 7 is not yet complete.

## Reproducible base

- Project AInos: `89cf6aac5cd41ff9fc1076ba4e50db764e1de28f` (main inspected 2026-11-12).
- Lean: `leanprover/lean4:v4.35.0`.
- Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679` (`v4.35.0`).
- Design: <https://github.com/MGYamada/ProjectAInos/issues/45>.

## Independent types

| Concept | Lean representation | Boundary |
|---|---|---|
| Coordinate vectors in C² | `Ket := Fin 2 → ℂ` | No use of the Pi sup norm as a Hilbert norm |
| Hilbert realization | `Hilbert := EuclideanSpace ℂ (Fin 2)` | `pairing_eq_inner` compares the standard pairing |
| Full observable algebra | `Operator := Matrix (Fin 2) (Fin 2) ℂ` | Ordinary matrix product and conjugate transpose |
| Self-adjoint observables | `{A : Operator // A.IsHermitian}` | Not all smooth functions on a future CP¹ |
| Rays | `Projectivization ℂ Ket` | Quotient by nonzero complex scaling, independent of projectors |
| Positive normalized states | `State` | Complex-linear functional, value 1 at identity, nonnegative on `Matrix.PosSemidef` |
| Rank-one orthogonal projectors | `RankOneProjector` | Hermitian, idempotent, range of complex dimension 1; no chosen vector in the definition |

`ComplexOrder` positivity enforces both a nonnegative real part and zero
imaginary part. It is not merely positivity of the real part. This finite
state type deliberately avoids imposing a C*-norm or introducing analytic GNS
dependencies; continuity is automatic in finite dimension but not yet bundled
as a `PositiveContinuousLinearMap` adapter.

## Mathematical statements

For a nonzero representative v, put q(v) = v†v and P(v) = q(v)⁻¹ vv†.
The implementation establishes positivity of q, Hermitian positivity,
idempotence, trace one, and range(P(v)) = C v. In particular the range has
complex dimension one.

The geometric pairing expression and the algebraic trace functional are
defined separately and compared by

    tr(P(v) A) = q(v)⁻¹ v† A v.

The trace functional is then proved to be an independently defined `State`.
Expectations of Hermitian matrices have zero imaginary part. All nonzero
complex rescalings preserve P(v); equality of projectors is equivalent to
equality of rays. Trace-pairing nondegeneracy gives the same equivalence for
vector states.

There are two different conclusions:

1. A bijection of rays with the intrinsically defined rank-one orthogonal
   projectors (`rayEquivRankOneProjectors`). Its surjectivity is a theorem.
2. An injective map from rays to all positive normalized functionals
   (`rayState_injective`), equivalently a bijection onto the image of vector
   states (`rayEquivVectorStates`). The latter is explicitly an image
   statement, not a classification of pure algebraic states.

For each Pauli matrix σ_a (a = x, y, z), both E_a,± = (I ± σ_a)/2 are proved to
be orthogonal projections. For every `State`, their probabilities are real,
belong to [0,1], and sum to one. Their formula is

    p_a,± = (1 ± Re ω(σ_a))/2.

The vector-state specialization is proved using the expectation comparison.
Explicit coordinate expectations for x, y, z and [σ_x, σ_y] = 2i σ_z are
included. The state represented by (1,i) is a sign-sensitive regression:
the σ_y probabilities are exactly (1,0).

## What is not proved: purity classification

No definition silently equates “pure” with “rank one” or “in the vector-state
image.” The following convex-state theorem remains a separate task:

    extreme points of the positive normalized functionals on M₂(C)
      = the vector states.

A suitable next implementation is:

1. Reconstruct a unique matrix ρ from an arbitrary complex-linear functional
   using matrix units and the nondegenerate trace pairing.
2. Prove that positivity and normalization are equivalent to ρ ≥ 0 and
   tr ρ = 1. Prove both directions, rather than defining `State` as a density
   matrix.
3. Define convex combinations and extremality of the independent state space.
4. Prove rank-one density matrices are extreme and rank-two density matrices
   admit a nontrivial convex decomposition (via the finite spectral theorem,
   or a proved Bloch-ball parametrization).
5. Compose this classification with `rayEquivRankOneProjectors`.

The current Mathlib matrix spectrum and positive-semidefinite APIs supply
useful prerequisites. None of these missing implications is an axiom or a
placeholder theorem in this prototype.

## CP¹, Fubini–Study, and Joyce connection: next theorems

These are future targets, not machine-checked claims of this patch.

### 1. Smooth CP¹ and the existing scheme API

Construct the two affine charts z = v₁/v₀ and w = v₀/v₁, prove they are
well-defined on the ray quotient, cover it, and have transition w = 1/z on
C\{0}. Establish the appropriate topology, charted space, and real smooth
manifold instance. Mathlib's `OnePoint.equivProjectivization` is an existing
set-level comparison that may help; it is not a supplied Fubini–Study atlas.

For the current Project AInos `SmoothGeometry.Manifold.scheme`, the chart
model must be `Fin 2 → ℝ`, so transport the complex chart model through an
explicit real linear equivalence. Once

    [ChartedSpace (Fin 2 → ℝ) CP1]
    [IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ CP1]

are established, `SmoothGeometry.Manifold.scheme 2 CP1` supplies the Joyce
C∞ scheme. `schemeMap` and `isoOfDiffeomorph` are the relevant map/comparison
APIs. The quantum layer should import these general foundations, never the
reverse. Finite-dimensional algebraic proofs do not require them.

### 2. Fix the Fubini–Study scale and sign conventions

One consistent target convention for ħ > 0 is, in z = x + i y coordinates,

    g_ħ = 2ħ (dx² + dy²)/(1 + |z|²)²,
    ω_ħ = 2ħ dx∧dy/(1 + |z|²)²,
    J ∂x = ∂y,
    ι_(X_f) ω_ħ = df,
    {f,g} = ω_ħ(X_f, X_g).

Prove the chart transformations preserve these tensors, hence they glue.
Prove smoothness, positive definiteness, nondegeneracy, dω = 0, and Kähler
compatibility. The existing `SmoothGeometry.DifferentialForm` operations
primarily treat forms on fixed Euclidean spaces; global tangent-bundle forms
and chart gluing need an explicit bridge. No CP¹/Fubini–Study implementation
was found in the inspected pinned source tree.

### 3. Smooth expectation functions and the commutator bracket

Prove ray expectations descend smoothly through the CP¹ atlas. On unit
representatives and horizontal tangent vectors, the target Hamiltonian field
is the class of

    X_A(v) = -(i/ħ)(A - f_A(v) I)v.

For the conventions above, prove

    {f_A, f_B} = f_([A,B]/(iħ)).

First verify this for the Pauli basis and constants, then extend by real
linearity to all Hermitian 2×2 matrices. Constants have zero Hamiltonian
vector field, so the quotient by scalar identity must be distinguished from
the correspondence of expectation functions themselves. A commutator
identity for matrices alone is not yet a Poisson-bracket theorem.

For an intrinsic observable characterization, prove that the real smooth
functions with Hamiltonian Killing fields are exactly these expectation
functions, with constants retained. Do not define that function space as the
image of Hermitian matrices and then call surjectivity a comparison theorem.

### 4. Measurement and dynamics

Prove the transition identity tr(P_v P_w) = |v†w|²/(q(v)q(w)), and separately
its relation to Fubini–Study distance with the selected scale. A bare
symplectic form does not determine the Born rule. For a Hermitian H, prove
the projective action of exp(-itH/ħ) solves the Hamiltonian equation and
preserves the Kähler structure and measurement probabilities.

## Existing Mathlib GNS support and the scope boundary

The pinned Mathlib already has `Analysis/CStarAlgebra/GelfandNaimarkSegal.lean`,
including `PositiveLinearMap.GNS` and `gnsStarAlgHom`. Its documented TODO
still includes an explicit cyclic unit vector. That is a separate analytic
API survey, not evidence that the full state/purity/GNS comparison is already
complete. No unbounded operators, self-adjoint domains, Stone theorem, or
infinite-dimensional probability reconstruction is used here.

## Verification

Required CI gates are the warning-free root build, root import completeness, the project
transitive axiom audit, and the explicit quantum API audit. The axiom
allowlist is `propext`, `Classical.choice`, and `Quot.sound`.

Verified results on the pinned base:

| Command | Result |
|---|---|
| `lake build --wfail ProjectAInos` | Passed; 9,236 build jobs, warnings treated as failures |
| `lake exe mk_all --check --lib ProjectAInos` | Passed; no update necessary |
| `lake env lean -DwarningAsError=true checks/AxiomAudit.lean` | Passed; 5,673 project/YM declarations |
| `lake env lean -DwarningAsError=true checks/QuantumMechanicsAPI.lean` | Passed; 113 quantum declarations, including generated declarations |
| Existing smooth-geometry, Yang–Mills, special-relativity, atomic-nonreactive, and electrodynamics API checks | All five passed with warnings as errors |

The printed axiom dependencies for the projector equivalence, expectation
comparison, probability bounds, and the σ_y example are exactly the allowed
three foundational axioms. An additional generated audit also checked all
72 explicitly named source declarations plus seven `State` constructors,
recursors, and projections. No `sorry`, `admit`, or new `axiom` is used.
