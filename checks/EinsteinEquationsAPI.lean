/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.GeneralRelativity.EinsteinEquations
import ProjectAinos.Electrodynamics.HilbertStress

/-! Public consumers of the Einstein equations with matter: the derivative of a relative
integral, the metric variation of the scalar and Maxwell densities with their Hilbert tensors,
the native Einstein equations with the conservation of their source and the trace-reversed form,
tensors that pair to zero with every metric variation, native tensors from coefficients, matter
actions and the equivalence of stationarity with the Einstein equations, the regressions, and
the Hilbert tensor of the field in Minkowski space as the stress tensor of §33. Default
elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/

noncomputable section

open Set Filter MeasureTheory

open scoped Topology ContDiff

namespace ProjectAinos.Variational

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

example {L : ℝ × E → ℝ} {U K : Set E} (hU : IsOpen U) (hKc : IsCompact K) (hKU : K ⊆ U) {r : ℝ}
    (hr : 0 < r) (hL : ∀ ε ∈ Metric.closedBall (0 : ℝ) r, ∀ z ∈ U, ContDiffAt ℝ ∞ L (ε, z))
    (hconst : ∀ x ∉ K, ∀ t, L (t, x) = L (0, x)) :
    HasDerivAt (fun ε => ∫ x, (L (ε, x) - L (0, x)) ∂μ)
      (∫ x, deriv (fun t => L (t, x)) 0 ∂μ) 0 :=
  hasDerivAt_integral_sub hU hKc hKU hr hL hconst

example {L : ℝ × E → ℝ} {U K : Set E} (hKc : IsCompact K) (hKU : K ⊆ U) {r : ℝ} (hr : 0 < r)
    (hL : ∀ ε ∈ Metric.closedBall (0 : ℝ) r, ∀ z ∈ U, ContDiffAt ℝ ∞ L (ε, z))
    (hconst : ∀ x ∉ K, ∀ t, L (t, x) = L (0, x)) :
    Integrable (fun x => deriv (fun t => L (t, x)) 0) μ :=
  integrable_deriv_sub hKc hKU hr hL hconst

end ProjectAinos.Variational

end

noncomputable section

open Set TopologicalSpace MeasureTheory

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

namespace CoordinateMetric

variable {U : Opens (MinkowskiModel d)} {g : CoordinateMetric σ d U}
  {h : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ}

example {x : MinkowskiModel d} (hx : x ∉ tsupport h) :
    formCoeff h x = 0 :=
  formCoeff_of_notMem hx

example {x : MinkowskiModel d} (hx : x ∉ tsupport h) (i k : Fin (d + 1)) :
    g.inverseVariation h x i k = 0 :=
  inverseVariation_of_notMem hx i k

example {x : MinkowskiModel d} (hx : x ∉ tsupport h) (ε : ℝ) :
    g.variationFamily h (ε, x) = g.variationFamily h (0, x) :=
  variationFamily_of_notMem hx ε

example {x : MinkowskiModel d} (hx : x ∉ tsupport h) (ε : ℝ) :
    familyDensity (g.variationFamily h) (ε, x) = familyDensity (g.variationFamily h) (0, x) :=
  familyDensity_of_notMem hx ε

example (x : MinkowskiModel d) :
    g.variationFamily h (0, x) = g.coefficient x :=
  variationFamily_zero_apply x

example (x : MinkowskiModel d) :
    familyDensity (g.variationFamily h) (0, x) = densityOf g.coefficient x :=
  familyDensity_zero x

example {x : MinkowskiModel d} (hx : x ∈ U) :
    ∑ i, ∑ k, g.coefficient x i k * g.inverseVariation h x i k =
      -∑ a, ∑ b, (g.coefficient x)⁻¹ a b * formCoeff h x a b :=
  sum_coefficient_mul_inverseVariation hx

example (hh : ContDiff ℝ ∞ h) (hK : HasCompactSupport h) (hKU : tsupport h ⊆ U)
    (hs : ∀ z v w, h z v w = h z w v) {L : ℝ × MinkowskiModel d → ℝ}
    (hL : ∀ ε, g.IsAdmissible h ε → ∀ z ∈ U, ContDiffAt ℝ ∞ L (ε, z))
    (hconst : ∀ x ∉ tsupport h, ∀ t, L (t, x) = L (0, x)) {L' : MinkowskiModel d → ℝ}
    (hL' : ∀ x ∈ U, HasDerivAt (fun ε => L (ε, x)) (L' x) 0) (hL'0 : ∀ x ∉ tsupport h, L' x = 0) :
    HasDerivAt (fun ε => ∫ x, (L (ε, x) - L (0, x))) (∫ x, L' x) 0 :=
  hasDerivAt_integral_of_pointwise hh hK hKU hs hL hconst hL' hL'0

section Scalar

example (m : ℝ) (φ : MinkowskiModel d → ℝ) (p : ℝ × MinkowskiModel d) :
    ℝ :=
  scalarFieldDensity g h m φ p

example (m : ℝ) (φ : MinkowskiModel d → ℝ) (x : MinkowskiModel d) (i k : Fin (d + 1)) :
    ℝ :=
  scalarStress g m φ x i k

example {x : MinkowskiModel d} (hx : x ∈ U) (m : ℝ) (φ : MinkowskiModel d → ℝ) (i k : Fin (d + 1)) :
    g.scalarStress m φ x i k = g.scalarStress m φ x k i :=
  scalarStress_symm hx m φ i k

example (m : ℝ) (φ : MinkowskiModel d → ℝ) {x : MinkowskiModel d} (hx : x ∉ tsupport h) (t : ℝ) :
    g.scalarFieldDensity h m φ (t, x) = g.scalarFieldDensity h m φ (0, x) :=
  scalarFieldDensity_of_notMem m φ hx t

example (hh : ContDiff ℝ ∞ h) (m : ℝ) {φ : MinkowskiModel d → ℝ} (hφ : ContDiffOn ℝ ∞ φ U)
    {p : ℝ × MinkowskiModel d} (hp : p.2 ∈ U) (hdet : (g.variationFamily h p).det ≠ 0) :
    ContDiffAt ℝ ∞ (g.scalarFieldDensity h m φ) p :=
  contDiffAt_scalarFieldDensity hh m hφ hp hdet

example (hh : ContDiff ℝ ∞ h) (hs : ∀ z v w, h z v w = h z w v) (m : ℝ) (φ : MinkowskiModel d → ℝ)
    {x : MinkowskiModel d} (hx : x ∈ U) :
    HasDerivAt (fun ε => g.scalarFieldDensity h m φ (ε, x))
      (-(∑ i, ∑ k, g.scalarStress m φ x i k * g.inverseVariation h x i k) / 2 *
        densityOf g.coefficient x) 0 :=
  hasDerivAt_scalarFieldDensity hh hs m φ hx

example (hh : ContDiff ℝ ∞ h) (hK : HasCompactSupport h) (hKU : tsupport h ⊆ U)
    (hs : ∀ z v w, h z v w = h z w v) (m : ℝ) {φ : MinkowskiModel d → ℝ} (hφ : ContDiffOn ℝ ∞ φ U) :
    HasDerivAt (fun ε => ∫ x, (g.scalarFieldDensity h m φ (ε, x) -
        g.scalarFieldDensity h m φ (0, x)))
      (∫ x, -(∑ i, ∑ k, g.scalarStress m φ x i k * g.inverseVariation h x i k) / 2 *
        densityOf g.coefficient x) 0 :=
  hasDerivAt_integral_scalarFieldDensity hh hK hKU hs m hφ

end Scalar

section Maxwell

example (F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (p : ℝ × MinkowskiModel d) :
    ℝ :=
  maxwellDensity g h F p

example (F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d) :
    ℝ :=
  maxwellInvariant g F x

example (F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (i k : Fin (d + 1)) :
    ℝ :=
  maxwellProduct g F x i k

example (F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (i k : Fin (d + 1)) :
    ℝ :=
  maxwellStress g F x i k

example {x : MinkowskiModel d} (hx : x ∈ U)
    (F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (i k : Fin (d + 1)) :
    g.maxwellStress F x i k = g.maxwellStress F x k i :=
  maxwellStress_symm hx F i k

example (hd : d = 3) {x : MinkowskiModel d} (hx : x ∈ U)
    (F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    ∑ i, ∑ k, (g.coefficient x)⁻¹ i k * g.maxwellStress F x i k = 0 :=
  sum_inv_mul_maxwellStress hd hx F

example (F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) {x : MinkowskiModel d}
    (hx : x ∉ tsupport h) (t : ℝ) :
    g.maxwellDensity h F (t, x) = g.maxwellDensity h F (0, x) :=
  maxwellDensity_of_notMem F hx t

example (hh : ContDiff ℝ ∞ h) {F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hF : ∀ a b, ContDiffOn ℝ ∞ (fun x => F x a b) U) {p : ℝ × MinkowskiModel d} (hp : p.2 ∈ U)
    (hdet : (g.variationFamily h p).det ≠ 0) :
    ContDiffAt ℝ ∞ (g.maxwellDensity h F) p :=
  contDiffAt_maxwellDensity hh hF hp hdet

example (hh : ContDiff ℝ ∞ h) (hs : ∀ z v w, h z v w = h z w v)
    {F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}
    (hx : x ∈ U) (hFa : ∀ a b, F x a b = -F x b a) :
    HasDerivAt (fun ε => g.maxwellDensity h F (ε, x))
      (-(∑ i, ∑ k, g.maxwellStress F x i k * g.inverseVariation h x i k) / 2 *
        densityOf g.coefficient x) 0 :=
  hasDerivAt_maxwellDensity hh hs hx hFa

example (hh : ContDiff ℝ ∞ h) (hK : HasCompactSupport h) (hKU : tsupport h ⊆ U)
    (hs : ∀ z v w, h z v w = h z w v)
    {F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hF : ∀ a b, ContDiffOn ℝ ∞ (fun x => F x a b) U) (hFa : ∀ x ∈ U, ∀ a b, F x a b = -F x b a) :
    HasDerivAt (fun ε => ∫ x, (g.maxwellDensity h F (ε, x) - g.maxwellDensity h F (0, x)))
      (∫ x, -(∑ i, ∑ k, g.maxwellStress F x i k * g.inverseVariation h x i k) / 2 *
        densityOf g.coefficient x) 0 :=
  hasDerivAt_integral_maxwellDensity hh hK hKU hs hF hFa

end Maxwell

end CoordinateMetric

end ProjectAinos.SmoothGeometry

end

noncomputable section

open Bundle FiberBundle VectorField ContinuousLinearMap

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)

local notation "I" => 𝓘(ℝ, MinkowskiModel d)

local notation "E" => MinkowskiModel d

local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

local instance (x : M) : T2Space (TM x) := FiberBundle.t2Space E TM x

local instance (x : M) : FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x

example (κ Λ : ℝ) (T : Tensor.SmoothBilinear («I» := I) (M := M)) :
    Prop :=
  SatisfiesEinstein g κ Λ T

variable {g} {κ Λ : ℝ} {T : Tensor.SmoothBilinear («I» := 𝓘(ℝ, MinkowskiModel d)) (M := M)}

example (hT : g.SatisfiesEinstein κ Λ T) (hκ : κ ≠ 0) (x : M) (v w : TM x) :
    T x v w = κ⁻¹ * (g.einstein x v w + Λ * g.form x v w) :=
  SatisfiesEinstein.apply hT hκ x v w

example (hT : g.SatisfiesEinstein κ Λ T) (hκ : κ ≠ 0) (x : M) (v w u : TM x) :
    Tensor.bilinearCovariantDerivative g.leviCivita T x v w u =
      κ⁻¹ * Tensor.bilinearCovariantDerivative g.leviCivita g.einsteinBilinear x v w u :=
  SatisfiesEinstein.bilinearCovariantDerivative_eq hT hκ x v w u

example (hT : g.SatisfiesEinstein κ Λ T) (hκ : κ ≠ 0) (x : M) :
    g.bilinearDivergenceCovector T x = 0 :=
  SatisfiesEinstein.divergence_eq_zero hT hκ x

example (hT : g.SatisfiesEinstein κ Λ T) (x : M) :
    (1 - ((d : ℝ) + 1) / 2) * g.scalarCurvature x + ((d : ℝ) + 1) * Λ =
      κ * g.contract x (T x) :=
  SatisfiesEinstein.contract hT x

example (hT : g.SatisfiesEinstein κ Λ T) (hd : d ≠ 1) (x : M) :
    g.ricci x = κ • (T x - (g.contract x (T x) / ((d : ℝ) - 1)) • g.form x) +
      (2 * Λ / ((d : ℝ) - 1)) • g.form x :=
  SatisfiesEinstein.ricci_eq hT hd x

example (hT : g.SatisfiesEinstein κ Λ T) (hd : d = 3) (x : M) :
    g.ricci x = κ • (T x - (g.contract x (T x) / 2) • g.form x) + Λ • g.form x :=
  SatisfiesEinstein.ricci_eq_four hT hd x

end ProjectAinos.SmoothGeometry.LorentzMetric

end

noncomputable section

open Bundle Set TopologicalSpace MeasureTheory Filter

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

example {n : ℕ} (A R : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ a b, A a b = A b a) (m k : Fin n) :
    ∑ a, ∑ c, A m a * A k c * R a c = (A * R * A) m k :=
  sum_mul_mul_eq_mul_mul A R hA m k

namespace CoordinateMetric

variable {U : Opens (MinkowskiModel d)} {g : CoordinateMetric σ d U}

example {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (fun z => ricciOf g.coefficient z j k) x :=
  contDiffAt_ricciOf hx j k

example {x : MinkowskiModel d} (hx : x ∈ U) :
    ContDiffAt ℝ ∞ (fun z => scalarOf g.coefficient z) x :=
  contDiffAt_scalarOf hx

example {x : MinkowskiModel d} (hx : x ∈ U) (i k : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (fun z => einsteinOf g.coefficient z i k) x :=
  contDiffAt_einsteinOf hx i k

example {x : MinkowskiModel d} (hx : x ∈ U) (i k : Fin (d + 1)) :
    einsteinOf g.coefficient x i k = einsteinOf g.coefficient x k i :=
  einsteinOf_symm hx i k

example {φ : MinkowskiModel d → ℝ} (hφ : ContDiffOn ℝ ∞ φ U) (m : ℝ) (i k : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun x => g.scalarStress m φ x i k) U :=
  contDiffOn_scalarStress hφ m i k

example {F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hF : ∀ a b, ContDiffOn ℝ ∞ (fun x => F x a b) U) (i k : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun x => g.maxwellStress F x i k) U :=
  contDiffOn_maxwellStress hF i k

example {h : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ}
    (hh : Continuous h) (i k : Fin (d + 1)) :
    ContinuousOn (fun x => g.inverseVariation h x i k) U :=
  continuousOn_inverseVariation hh i k

example {x : MinkowskiModel d} (hx : x ∈ U) :
    0 < densityOf g.coefficient x :=
  densityOf_pos hx

example {f : MinkowskiModel d → ℝ} {K : Set (MinkowskiModel d)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hf : ContinuousOn f U) (h0 : ∀ x ∉ K, f x = 0) :
    Integrable f :=
  integrable_of_continuousOn hK hKU hf h0

example (p q : Fin (d + 1)) :
    MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ :=
  symmetricTest p q

example (p q : Fin (d + 1)) (v w : MinkowskiModel d) :
    symmetricTest p q v w = v p * w q + v q * w p :=
  symmetricTest_apply p q v w

example (φ : MinkowskiModel d → ℝ) (p q : Fin (d + 1)) (x : MinkowskiModel d) :
    MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ :=
  testVariation φ p q x

example (φ : MinkowskiModel d → ℝ) (p q : Fin (d + 1)) (x v w : MinkowskiModel d) :
    testVariation φ p q x v w = φ x * (v p * w q + v q * w p) :=
  testVariation_apply φ p q x v w

example (φ : MinkowskiModel d → ℝ) (p q : Fin (d + 1)) (x v w : MinkowskiModel d) :
    testVariation φ p q x v w = testVariation φ p q x w v :=
  testVariation_symm φ p q x v w

example {φ : MinkowskiModel d → ℝ} (hφ : ContDiff ℝ ∞ φ) (p q : Fin (d + 1)) :
    ContDiff ℝ ∞ (testVariation φ p q) :=
  contDiff_testVariation hφ p q

example (φ : MinkowskiModel d → ℝ) (p q : Fin (d + 1)) :
    Function.support (testVariation φ p q) ⊆ Function.support φ :=
  support_testVariation φ p q

example (φ : MinkowskiModel d → ℝ) (p q : Fin (d + 1)) :
    tsupport (testVariation φ p q) ⊆ tsupport φ :=
  tsupport_testVariation φ p q

example {φ : MinkowskiModel d → ℝ} (hφ : HasCompactSupport φ) (p q : Fin (d + 1)) :
    HasCompactSupport (testVariation φ p q) :=
  hasCompactSupport_testVariation hφ p q

example (φ : MinkowskiModel d → ℝ) (p q : Fin (d + 1)) (x : MinkowskiModel d) (a b : Fin (d + 1)) :
    formCoeff (testVariation φ p q) x a b =
      φ x * ((if p = a then 1 else 0) * (if q = b then 1 else 0) +
        (if q = a then 1 else 0) * (if p = b then 1 else 0)) :=
  formCoeff_testVariation φ p q x a b

example (E : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (m n : Fin (d + 1)) :
    ℝ :=
  raised g E x m n

example {x : MinkowskiModel d} (hx : x ∈ U)
    (E : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (φ : MinkowskiModel d → ℝ)
    (p q : Fin (d + 1)) :
    ∑ i, ∑ k, E x i k * g.inverseVariation (testVariation φ p q) x i k =
      -(φ x * (g.raised E x p q + g.raised E x q p)) :=
  sum_mul_inverseVariation_test hx E φ p q

example {x : MinkowskiModel d} (hx : x ∈ U)
    {E : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hE : ∀ m n, g.raised E x m n = 0) (i k : Fin (d + 1)) :
    E x i k = 0 :=
  eq_zero_of_raised_eq_zero hx hE i k

example {x : MinkowskiModel d} {E : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hsym : ∀ i k, E x i k = E x k i) (m n : Fin (d + 1)) :
    g.raised E x m n = g.raised E x n m :=
  raised_symm hsym m n

example {E : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hE : ∀ i k, ContinuousOn (fun x => E x i k) U) (m n : Fin (d + 1)) :
    ContinuousOn (fun x => g.raised E x m n) U :=
  continuousOn_raised hE m n

example {E : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hE : ∀ i k, ContinuousOn (fun x => E x i k) U) (hsym : ∀ x ∈ U, ∀ i k, E x i k = E x k i) :
    (∀ h : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ,
      ContDiff ℝ ∞ h → HasCompactSupport h → tsupport h ⊆ U → (∀ z v w, h z v w = h z w v) →
        ∫ x, (∑ i, ∑ k, E x i k * g.inverseVariation h x i k) * densityOf g.coefficient x = 0) ↔
      ∀ x ∈ U, ∀ i k, E x i k = 0 :=
  integral_inverseVariation_eq_zero_iff hE hsym

example (T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d) :
    MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ :=
  coefficientForm T x

example (T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x v w : MinkowskiModel d) :
    coefficientForm T x v w = ∑ i, ∑ k, T x i k * (v i * w k) :=
  coefficientForm_apply T x v w

example (T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (i k : Fin (d + 1)) :
    coefficientForm T x (Pi.single i 1) (Pi.single k 1) = T x i k :=
  coefficientForm_single T x i k

example {T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hT : ∀ i k, ContDiffOn ℝ ∞ (fun x => T x i k) U) :
    ContDiffOn ℝ ∞ (coefficientForm T) U :=
  contDiffOn_coefficientForm hT

example (T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hT : ∀ i k, ContDiffOn ℝ ∞ (fun x => T x i k) U) :
    Tensor.SmoothBilinear («I» := 𝓘(ℝ, MinkowskiModel d)) (M := U) :=
  bilinearOf T hT

example (T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hT : ∀ i k, ContDiffOn ℝ ∞ (fun x => T x i k) U) (y : U)
    (v w : TangentSpace 𝓘(ℝ, MinkowskiModel d) y) :
    bilinearOf T hT y v w = coefficientForm T y v w :=
  bilinearOf_apply T hT y v w

example (T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hT : ∀ i k, ContDiffOn ℝ ∞ (fun x => T x i k) U) (x y : U) (i k : Fin (d + 1)) :
    bilinearOf T hT y (chartField (physicalChart x) (Pi.single i 1) y)
      (chartField (physicalChart x) (Pi.single k 1) y) = T y i k :=
  bilinearOf_chartField T hT x y i k

example (κ Λ : ℝ) (T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    Prop :=
  IsEinstein g κ Λ T

example {T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hT : ∀ i k, ContDiffOn ℝ ∞ (fun x => T x i k) U) (κ Λ : ℝ) :
    g.toLorentzMetric.SatisfiesEinstein κ Λ (bilinearOf T hT) ↔ g.IsEinstein κ Λ T :=
  satisfiesEinstein_bilinearOf_iff hT κ Λ

end CoordinateMetric

end ProjectAinos.SmoothGeometry

end

noncomputable section

open Set TopologicalSpace MeasureTheory Filter

open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.EinsteinEquations

open SmoothGeometry CoordinateMetric

open LorentzMetric (chartField)

variable {U : Opens (MinkowskiModel 3)}

namespace MatterAction

variable (g : CoordinateMetric .timeNegative 3 U)

example :
    MatterAction g :=
  vacuum g

example (m : ℝ) (φ : MinkowskiModel 3 → ℝ) (hφ : ContDiffOn ℝ ∞ φ U) :
    MatterAction g :=
  scalarField g m φ hφ

example (F : MinkowskiModel 3 → Matrix (Fin (3 + 1)) (Fin (3 + 1)) ℝ)
    (hF : ∀ a b, ContDiffOn ℝ ∞ (fun x => F x a b) U) (hFa : ∀ x ∈ U, ∀ a b, F x a b = -F x b a) :
    MatterAction g :=
  maxwellField g F hF hFa

end MatterAction

variable (g : CoordinateMetric .timeNegative 3 U) (M : MatterAction g)

example (κ Λ : ℝ) (h : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 →L[ℝ] ℝ) (ε : ℝ) :
    ℝ :=
  totalAction g M κ Λ h ε

example (κ Λ : ℝ) (x : MinkowskiModel 3) :
    Matrix (Fin (3 + 1)) (Fin (3 + 1)) ℝ :=
  fieldEquation g M κ Λ x

example (κ Λ : ℝ) :
    Prop :=
  IsStationary g M κ Λ

variable {g M}

example (i k : Fin (3 + 1)) :
    ContinuousOn (fun x => einsteinOf g.coefficient x i k) U :=
  continuousOn_einsteinOf i k

example (κ Λ : ℝ) (i k : Fin (3 + 1)) :
    ContinuousOn (fun x => fieldEquation g M κ Λ x i k) U :=
  continuousOn_fieldEquation κ Λ i k

example (κ Λ : ℝ) {x : MinkowskiModel 3} (hx : x ∈ U) (i k : Fin (3 + 1)) :
    fieldEquation g M κ Λ x i k = fieldEquation g M κ Λ x k i :=
  fieldEquation_symm κ Λ hx i k

example {T : MinkowskiModel 3 → Matrix (Fin (3 + 1)) (Fin (3 + 1)) ℝ}
    (hT : ∀ i k, ContinuousOn (fun x => T x i k) U)
    {h : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 →L[ℝ] ℝ} (hh : Continuous h)
    (hK : HasCompactSupport h) (hKU : tsupport h ⊆ U) :
    Integrable fun x =>
      (∑ i, ∑ k, T x i k * g.inverseVariation h x i k) * densityOf g.coefficient x :=
  integrable_pairing hT hh hK hKU

example {κ : ℝ} (hκ : κ ≠ 0) (Λ : ℝ)
    {h : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 →L[ℝ] ℝ} (hh : ContDiff ℝ ∞ h)
    (hK : HasCompactSupport h) (hKU : tsupport h ⊆ U) (hs : ∀ z v w, h z v w = h z w v) :
    HasDerivAt (totalAction g M κ Λ h) ((2 * κ)⁻¹ * ∫ x, (∑ i, ∑ k,
      fieldEquation g M κ Λ x i k * g.inverseVariation h x i k) * densityOf g.coefficient x) 0 :=
  hasDerivAt_totalAction hκ Λ hh hK hKU hs

example {κ : ℝ} (hκ : κ ≠ 0) (Λ : ℝ) :
    IsStationary g M κ Λ ↔ g.IsEinstein κ Λ M.stress :=
  isStationary_iff hκ Λ

example {κ : ℝ} (hκ : κ ≠ 0) (Λ : ℝ) :
    IsStationary g M κ Λ ↔
      g.toLorentzMetric.SatisfiesEinstein κ Λ (bilinearOf M.stress M.stress_smooth) :=
  isStationary_iff_satisfiesEinstein hκ Λ

example {κ : ℝ} (hκ : κ ≠ 0) {Λ : ℝ} (hst : IsStationary g M κ Λ) (y : U) :
    g.toLorentzMetric.bilinearDivergenceCovector (bilinearOf M.stress M.stress_smooth) y = 0 :=
  divergence_stress_eq_zero hκ hst y

example {κ : ℝ} (hκ : κ ≠ 0) {Λ : ℝ} (hst : IsStationary g M κ Λ) (y : U) :
    g.toLorentzMetric.ricci y = κ • (bilinearOf M.stress M.stress_smooth y -
      (g.toLorentzMetric.contract y (bilinearOf M.stress M.stress_smooth y) / 2) •
        g.toLorentzMetric.form y) + Λ • g.toLorentzMetric.form y :=
  ricci_eq_of_isStationary hκ hst y

section Examples

local notation "η₄" => CoordinateMetric.minkowski LorentzConvention.timeNegative 3 ⊤

local notation "D" => Matrix.diagonal (lorentzSign (d := 3) LorentzConvention.timeNegative)

example {κ : ℝ} (hκ : κ ≠ 0) :
    IsStationary (η₄) (MatterAction.vacuum (η₄)) κ 0 :=
  minkowski_isStationary_vacuum hκ

example {κ : ℝ} (hκ : κ ≠ 0) (m c : ℝ) :
    IsStationary (η₄) (MatterAction.scalarField (η₄) m (fun _ => c) contDiffOn_const) κ
      (-(κ * m ^ 2 * c ^ 2) / 2) :=
  minkowski_isStationary_constantScalar hκ m c

example {κ : ℝ} (hκ : κ ≠ 0) :
    ¬ IsStationary ExponentialConformalExample.metric
      (MatterAction.vacuum ExponentialConformalExample.metric) κ 0 :=
  conformal_not_isStationary_vacuum hκ

example (m : ℝ) (φ : MinkowskiModel 3 → ℝ) (x : MinkowskiModel 3) :
    (η₄).scalarStress m φ x 0 0 = ((fderiv ℝ φ x (Pi.single 0 1)) ^ 2 +
      ∑ i : Fin 3, (fderiv ℝ φ x (Pi.single i.succ 1)) ^ 2 + m ^ 2 * φ x ^ 2) / 2 :=
  scalarStress_minkowski_zero_zero m φ x

end Examples

end ProjectAinos.GeneralRelativity.EinsteinEquations

end

noncomputable section

open TopologicalSpace
open scoped ContDiff

namespace ProjectAinos.GeneralRelativity.EinsteinEquations

open SmoothGeometry CoordinateMetric

variable {U : Opens (MinkowskiModel 3)} {g : CoordinateMetric .timeNegative 3 U}

example (M : MatterAction g) (i k : Fin (3 + 1)) :
    ContDiffOn ℝ ∞ (fun x => M.stress x i k) U :=
  M.stress_smooth i k

example (M : MatterAction g) {x : MinkowskiModel 3} (hx : x ∈ U) (i k : Fin (3 + 1)) :
    M.stress x i k = M.stress x k i :=
  M.stress_symm x hx i k

example (M : MatterAction g)
    (h : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 →L[ℝ] ℝ)
    (hh : ContDiff ℝ ∞ h) (hK : HasCompactSupport h) (hKU : tsupport h ⊆ U)
    (hs : ∀ z v w, h z v w = h z w v) :
    HasDerivAt (M.action h) (∫ x, -(∑ i, ∑ k, M.stress x i k * g.inverseVariation h x i k) / 2 *
      densityOf g.coefficient x) 0 :=
  M.hasDerivAt_action h hh hK hKU hs

end ProjectAinos.GeneralRelativity.EinsteinEquations

end

noncomputable section

open TopologicalSpace

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

example {n : ℕ} (s : Fin n → ℝ) (b : Fin n) (f : Fin n → ℝ) :
    ∑ e, Matrix.diagonal s b e * f e = s b * f b :=
  sum_diagonal_mul s b f

example (G : Spacetime → TwoForm) (x : Spacetime) :
    Matrix (Fin (3 + 1)) (Fin (3 + 1)) ℝ :=
  componentMatrix G x

example (G : Spacetime → TwoForm) (x : Spacetime) (a b : Fin (3 + 1)) :
    componentMatrix G x a b = -componentMatrix G x b a :=
  componentMatrix_antisymm G x a b

example {U : Opens Spacetime} (G : Spacetime → TwoForm) (x : Spacetime) (i k : Fin (3 + 1)) :
    (CoordinateMetric.minkowski .timeNegative 3 U).maxwellStress (componentMatrix G) x i k =
      stressForm (G x) (Pi.single i 1) (Pi.single k 1) :=
  maxwellStress_minkowski G x i k

end ProjectAinos.Electrodynamics

end
