/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.EinsteinHilbertAction
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateEinsteinEquation

/-!
# Matter and the Einstein equations

Landau–Lifshitz, §§94–95, with `c = 1` and the signature `(−+++)`. A metric `g` is given by its
coefficients on an open set `U` of `ℝ⁴`, and varied by smooth symmetric fields `h` with compact
support in `U`.

* `MatterAction g`: a relative action of matter for each variation together with its Hilbert
  tensor `T_{ik}`, smooth and symmetric on `U`, such that `δS_m = −½ ∫ T_{ik} δg^{ik} √|g| d⁴x`.
  The tensor is a theorem of the action, not a datum supplied beside it: the instances are the
  vacuum, a scalar field (`scalarField`) and a fixed electromagnetic field (`maxwellField`),
  whose tensors are derived from their actions in `CoordinateMatter`.
* `hasDerivAt_totalAction`: the total relative action `ΔS_g + ΔS_m` has the first variation
  `(1/2κ) ∫ (G_{ik} + Λ g_{ik} − κ T_{ik}) δg^{ik} √|g| d⁴x`.
* `isStationary_iff`: **the total action is stationary under every compactly supported variation
  of the metric if and only if `G_{ik} + Λ g_{ik} = κ T_{ik}` on `U`**, for `κ ≠ 0`. This is an
  equivalence for given fields, not the existence of a metric for a given source.
* `isStationary_iff_satisfiesEinstein`, `divergence_stress_eq_zero`, `ricci_eq_of_isStationary`:
  the equations are the native Einstein equations of the Lorentz metric on `U`; their source is
  conserved, `∇^a T_{ab} = 0`, by the contracted Bianchi identity; and
  `Ric = κ (T − ½ T^a{}_a g) + Λ g`.
* Regressions: the Minkowski metric in vacuum with `Λ = 0`, and with a constant scalar field `c`
  and `Λ = −κ m² c²/2`, is stationary; the curved metric `e^{2z} η` in vacuum is not. The tensor of
  the scalar field has `T₀₀ = ½ (φ̇² + |∇φ|² + m² φ²)` in Minkowski space.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.EinsteinEquations

open SmoothGeometry CoordinateMetric
open LorentzMetric (chartField)

variable {U : Opens (MinkowskiModel 3)}

/-- A matter action on a coordinate metric `g`: a relative action for each variation `h`, with a
smooth symmetric Hilbert tensor `T_{ik}` that gives its first variation
`δS_m = −½ ∫ T_{ik} δg^{ik} √|g| d⁴x`. -/
structure MatterAction (g : CoordinateMetric .timeNegative 3 U) where
  /-- The relative action `ε ↦ S_m[g + εh] − S_m[g]`. -/
  action : (MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 →L[ℝ] ℝ) → ℝ → ℝ
  /-- The Hilbert tensor `T_{ik}`. -/
  stress : MinkowskiModel 3 → Matrix (Fin (3 + 1)) (Fin (3 + 1)) ℝ
  stress_smooth : ∀ i k, ContDiffOn ℝ ∞ (fun x => stress x i k) U
  stress_symm : ∀ x ∈ U, ∀ i k, stress x i k = stress x k i
  hasDerivAt_action : ∀ h : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 →L[ℝ] ℝ,
    ContDiff ℝ ∞ h → HasCompactSupport h → tsupport h ⊆ U → (∀ z v w, h z v w = h z w v) →
      HasDerivAt (action h) (∫ x, -(∑ i, ∑ k, stress x i k * g.inverseVariation h x i k) / 2 *
        densityOf g.coefficient x) 0

namespace MatterAction

variable (g : CoordinateMetric .timeNegative 3 U)

/-- No matter. -/
def vacuum : MatterAction g where
  action _ _ := 0
  stress _ := 0
  stress_smooth _ _ := contDiffOn_const
  stress_symm _ _ _ _ := rfl
  hasDerivAt_action _ _ _ _ _ := by simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)

/-- A scalar field `φ` of mass `m`, with the density `−½ (g^{ab} ∂_aφ ∂_bφ + m² φ²) √|g|`. -/
def scalarField (m : ℝ) (φ : MinkowskiModel 3 → ℝ) (hφ : ContDiffOn ℝ ∞ φ U) : MatterAction g where
  action h ε := ∫ x, (g.scalarFieldDensity h m φ (ε, x) - g.scalarFieldDensity h m φ (0, x))
  stress := g.scalarStress m φ
  stress_smooth := contDiffOn_scalarStress hφ m
  stress_symm _ hx i k := scalarStress_symm hx m φ i k
  hasDerivAt_action _ hh hK hKU hs := hasDerivAt_integral_scalarFieldDensity hh hK hKU hs m hφ

/-- A fixed electromagnetic field `F_{ab}`, with the density `−¼ F_{ab} F^{ab} √|g|`. -/
def maxwellField (F : MinkowskiModel 3 → Matrix (Fin (3 + 1)) (Fin (3 + 1)) ℝ)
    (hF : ∀ a b, ContDiffOn ℝ ∞ (fun x => F x a b) U)
    (hFa : ∀ x ∈ U, ∀ a b, F x a b = -F x b a) : MatterAction g where
  action h ε := ∫ x, (g.maxwellDensity h F (ε, x) - g.maxwellDensity h F (0, x))
  stress := g.maxwellStress F
  stress_smooth := contDiffOn_maxwellStress hF
  stress_symm _ hx i k := maxwellStress_symm hx F i k
  hasDerivAt_action _ hh hK hKU hs := hasDerivAt_integral_maxwellDensity hh hK hKU hs hF hFa

end MatterAction

variable (g : CoordinateMetric .timeNegative 3 U) (M : MatterAction g)

/-- The total relative action `ΔS_g + ΔS_m` of the variation `g + εh`. -/
def totalAction (κ Λ : ℝ) (h : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 →L[ℝ] ℝ)
    (ε : ℝ) : ℝ :=
  EinsteinHilbert.relativeAction g h κ Λ ε + M.action h ε

/-- The tensor `G_{ik} + Λ g_{ik} − κ T_{ik}` whose vanishing is the Einstein equations. -/
def fieldEquation (κ Λ : ℝ) (x : MinkowskiModel 3) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) ℝ :=
  Matrix.of fun i k => einsteinOf g.coefficient x i k + Λ * g.coefficient x i k -
    κ * M.stress x i k

/-- The total action is stationary under every compactly supported variation of the metric. -/
def IsStationary (κ Λ : ℝ) : Prop :=
  ∀ h : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 →L[ℝ] ℝ,
    ContDiff ℝ ∞ h → HasCompactSupport h → tsupport h ⊆ U → (∀ z v w, h z v w = h z w v) →
      HasDerivAt (totalAction g M κ Λ h) 0 0

variable {g M}

theorem continuousOn_einsteinOf (i k : Fin (3 + 1)) :
    ContinuousOn (fun x => einsteinOf g.coefficient x i k) U :=
  fun _ hx => (contDiffAt_einsteinOf hx i k).continuousAt.continuousWithinAt

theorem continuousOn_fieldEquation (κ Λ : ℝ) (i k : Fin (3 + 1)) :
    ContinuousOn (fun x => fieldEquation g M κ Λ x i k) U := by
  simp only [fieldEquation, Matrix.of_apply]
  exact (((continuousOn_einsteinOf i k).add
    (continuousOn_const.mul (g.coefficient_contDiffOn i k).continuousOn)).sub
      (continuousOn_const.mul (M.stress_smooth i k).continuousOn))

theorem fieldEquation_symm (κ Λ : ℝ) {x : MinkowskiModel 3} (hx : x ∈ U) (i k : Fin (3 + 1)) :
    fieldEquation g M κ Λ x i k = fieldEquation g M κ Λ x k i := by
  simp only [fieldEquation, Matrix.of_apply]
  rw [einsteinOf_symm hx i k, g.coefficient_symmetric hx i k, M.stress_symm x hx i k]

/-- The integrand of a first variation is integrable. -/
theorem integrable_pairing {T : MinkowskiModel 3 → Matrix (Fin (3 + 1)) (Fin (3 + 1)) ℝ}
    (hT : ∀ i k, ContinuousOn (fun x => T x i k) U)
    {h : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 →L[ℝ] ℝ}
    (hh : Continuous h) (hK : HasCompactSupport h) (hKU : tsupport h ⊆ U) :
    Integrable fun x =>
      (∑ i, ∑ k, T x i k * g.inverseVariation h x i k) * densityOf g.coefficient x := by
  refine integrable_of_continuousOn hK hKU ?_ fun x hx => by
    simp [inverseVariation_of_notMem hx]
  exact (continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun k _ =>
    (hT i k).mul (continuousOn_inverseVariation hh i k)).mul
      fun x hx => (contDiffAt_densityOf hx).continuousAt.continuousWithinAt

/-- **The first variation of the total action**:
`(1/2κ) ∫ (G_{ik} + Λ g_{ik} − κ T_{ik}) δg^{ik} √|g| d⁴x`. -/
theorem hasDerivAt_totalAction {κ : ℝ} (hκ : κ ≠ 0) (Λ : ℝ)
    {h : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 →L[ℝ] ℝ}
    (hh : ContDiff ℝ ∞ h) (hK : HasCompactSupport h) (hKU : tsupport h ⊆ U)
    (hs : ∀ z v w, h z v w = h z w v) :
    HasDerivAt (totalAction g M κ Λ h) ((2 * κ)⁻¹ * ∫ x, (∑ i, ∑ k,
      fieldEquation g M κ Λ x i k * g.inverseVariation h x i k) * densityOf g.coefficient x) 0 := by
  have hEH := EinsteinHilbert.hasDerivAt_relativeAction (g := g) hh hK hKU hs κ Λ
  have hm := M.hasDerivAt_action h hh hK hKU hs
  have hP : ∀ i k, ContinuousOn (fun x => einsteinOf g.coefficient x i k +
      Λ * g.coefficient x i k) U := fun i k =>
    (continuousOn_einsteinOf i k).add
      (continuousOn_const.mul (g.coefficient_contDiffOn i k).continuousOn)
  have hA := integrable_pairing (g := g) hP hh.continuous hK hKU
  have hB := integrable_pairing (g := g) (fun i k => (M.stress_smooth i k).continuousOn)
    hh.continuous hK hKU
  refine (hEH.add hm).congr_deriv ?_
  have hpt : ∀ x, (∑ i, ∑ k, fieldEquation g M κ Λ x i k * g.inverseVariation h x i k) *
      densityOf g.coefficient x =
      (∑ i, ∑ k, (einsteinOf g.coefficient x i k + Λ * g.coefficient x i k) *
        g.inverseVariation h x i k) * densityOf g.coefficient x -
      κ * ((∑ i, ∑ k, M.stress x i k * g.inverseVariation h x i k) *
        densityOf g.coefficient x) := by
    intro x
    have hterm (i k : Fin (3 + 1)) : fieldEquation g M κ Λ x i k * g.inverseVariation h x i k =
        (einsteinOf g.coefficient x i k + Λ * g.coefficient x i k) * g.inverseVariation h x i k -
          κ * (M.stress x i k * g.inverseVariation h x i k) := by
      simp only [fieldEquation, Matrix.of_apply]
      ring
    simp only [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hmat : (fun x => -(∑ i, ∑ k, M.stress x i k * g.inverseVariation h x i k) / 2 *
      densityOf g.coefficient x) = fun x => -((∑ i, ∑ k, M.stress x i k *
        g.inverseVariation h x i k) * densityOf g.coefficient x) / 2 := by
    funext x
    ring
  rw [show (fun x => (∑ i, ∑ k, fieldEquation g M κ Λ x i k * g.inverseVariation h x i k) *
      densityOf g.coefficient x) = _ from funext hpt, integral_sub hA (hB.const_mul κ),
    integral_const_mul, hmat, integral_div, integral_neg]
  field_simp
  ring

/-- **The Einstein equations from the action.** For `κ ≠ 0`, the total action is stationary under
every compactly supported variation of the metric if and only if `G_{ik} + Λ g_{ik} = κ T_{ik}`
on `U`. -/
theorem isStationary_iff {κ : ℝ} (hκ : κ ≠ 0) (Λ : ℝ) :
    IsStationary g M κ Λ ↔ g.IsEinstein κ Λ M.stress := by
  have hiff := integral_inverseVariation_eq_zero_iff (g := g)
    (continuousOn_fieldEquation (M := M) κ Λ) fun x hx i k => fieldEquation_symm κ Λ hx i k
  have hE : (∀ x ∈ U, ∀ i k, fieldEquation g M κ Λ x i k = 0) ↔ g.IsEinstein κ Λ M.stress := by
    simp only [fieldEquation, Matrix.of_apply, sub_eq_zero]
    rfl
  rw [← hE, ← hiff]
  constructor
  · intro hst h hh hK hKU hs
    have h0 := (hasDerivAt_totalAction hκ Λ hh hK hKU hs).unique (hst h hh hK hKU hs)
    exact (mul_eq_zero.mp h0).resolve_left (inv_ne_zero (mul_ne_zero two_ne_zero hκ))
  · intro hint h hh hK hKU hs
    have hd := hasDerivAt_totalAction (M := M) hκ Λ hh hK hKU hs
    rwa [hint h hh hK hKU hs, mul_zero] at hd

/-- The stationary metrics are the solutions of the native Einstein equations on `U`. -/
theorem isStationary_iff_satisfiesEinstein {κ : ℝ} (hκ : κ ≠ 0) (Λ : ℝ) :
    IsStationary g M κ Λ ↔
      g.toLorentzMetric.SatisfiesEinstein κ Λ (bilinearOf M.stress M.stress_smooth) := by
  rw [isStationary_iff hκ, satisfiesEinstein_bilinearOf_iff]

/-- **The source is conserved** (§94): at a stationary metric, `∇^a T_{ab} = 0`. -/
theorem divergence_stress_eq_zero {κ : ℝ} (hκ : κ ≠ 0) {Λ : ℝ} (hst : IsStationary g M κ Λ)
    (y : U) :
    g.toLorentzMetric.bilinearDivergenceCovector (bilinearOf M.stress M.stress_smooth) y = 0 :=
  ((isStationary_iff_satisfiesEinstein hκ Λ).mp hst).divergence_eq_zero hκ y

/-- The trace-reversed equations at a stationary metric: `Ric = κ (T − ½ T^a{}_a g) + Λ g`. -/
theorem ricci_eq_of_isStationary {κ : ℝ} (hκ : κ ≠ 0) {Λ : ℝ} (hst : IsStationary g M κ Λ)
    (y : U) :
    g.toLorentzMetric.ricci y = κ • (bilinearOf M.stress M.stress_smooth y -
      (g.toLorentzMetric.contract y (bilinearOf M.stress M.stress_smooth y) / 2) •
        g.toLorentzMetric.form y) + Λ • g.toLorentzMetric.form y :=
  ((isStationary_iff_satisfiesEinstein hκ Λ).mp hst).ricci_eq_four rfl y

/-! ### Regressions -/

section Examples

local notation "η₄" => CoordinateMetric.minkowski LorentzConvention.timeNegative 3 ⊤
local notation "D" => Matrix.diagonal (lorentzSign (d := 3) LorentzConvention.timeNegative)

/-- Minkowski space is a vacuum solution without a cosmological constant. -/
theorem minkowski_isStationary_vacuum {κ : ℝ} (hκ : κ ≠ 0) :
    IsStationary (η₄) (MatterAction.vacuum (η₄)) κ 0 := by
  rw [isStationary_iff hκ]
  intro x _ i k
  rw [show (η₄).coefficient = fun _ => D from funext minkowski_coefficient]
  simp [MatterAction.vacuum]

/-- Minkowski space with a constant scalar field `c` solves the Einstein equations with
`Λ = −κ m² c²/2`: the potential energy of the field acts as a cosmological constant. -/
theorem minkowski_isStationary_constantScalar {κ : ℝ} (hκ : κ ≠ 0) (m c : ℝ) :
    IsStationary (η₄) (MatterAction.scalarField (η₄) m (fun _ => c) contDiffOn_const) κ
      (-(κ * m ^ 2 * c ^ 2) / 2) := by
  rw [isStationary_iff hκ]
  intro x _ i k
  simp only [MatterAction.scalarField, scalarStress, fderiv_fun_const, Pi.zero_apply,
    zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
  rw [show (η₄).coefficient = fun _ => D from funext minkowski_coefficient]
  simp only [einsteinOf_const]
  ring

/-- The curved metric `e^{2z} η` is not a vacuum solution: its Einstein tensor does not
vanish. -/
theorem conformal_not_isStationary_vacuum {κ : ℝ} (hκ : κ ≠ 0) :
    ¬ IsStationary ExponentialConformalExample.metric
      (MatterAction.vacuum ExponentialConformalExample.metric) κ 0 := by
  rw [isStationary_iff hκ]
  intro h
  have h3 := h 0 (by simp) 3 3
  rw [EinsteinHilbert.conformal_einsteinOf] at h3
  norm_num [MatterAction.vacuum, lorentzSign, LorentzConvention.timeSign] at h3

/-- In Minkowski space the energy density of a scalar field is
`T₀₀ = ½ (φ̇² + |∇φ|² + m² φ²)`. -/
theorem scalarStress_minkowski_zero_zero (m : ℝ) (φ : MinkowskiModel 3 → ℝ)
    (x : MinkowskiModel 3) :
    (η₄).scalarStress m φ x 0 0 = ((fderiv ℝ φ x (Pi.single 0 1)) ^ 2 +
      ∑ i : Fin 3, (fderiv ℝ φ x (Pi.single i.succ 1)) ^ 2 + m ^ 2 * φ x ^ 2) / 2 := by
  have hinv : (D)⁻¹ = D := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal]
    simp only [lorentzSign_sq, Matrix.diagonal_one]
  rw [scalarStress, minkowski_coefficient, hinv]
  simp [Matrix.diagonal_apply, Fin.sum_univ_succ, lorentzSign, LorentzConvention.timeSign]
  ring

end Examples

end ProjectAinos.GeneralRelativity.EinsteinEquations
