/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Minkowski.Affine
public import ProjectAInos.External.YM.PublicTheory

/-!
# An explicit bridge between time-first and time-last spacetime coordinates

P⊗AI uses the time-first Minkowski model `(t,x,y,z)`; the upstream public
Yang--Mills API represents the same 4D point with time at index `3`. The
coordinate permutation transports the flat causal cone and affine action.
The Fourier phase uses the metric dual of the physical momentum.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace ProjectAInos.SmoothGeometry.YangMillsCoordinates

open Minkowski
open MeasureTheory
open scoped InnerProductSpace

/-- Relocate time from index `0` to index `3`, swapping the remaining endpoint. -/
def axisSwap : Equiv.Perm (Fin 4) := Equiv.swap 0 3

/-- The time-first and time-last spacetime models are linearly equivalent. -/
def pointLinear : MinkowskiModel 3 ≃ₗ[ℝ] YangMills.Spacetime where
  toFun x := WithLp.toLp 2 (x ∘ axisSwap)
  invFun x := x.ofLp ∘ axisSwap
  left_inv x := by
    ext j
    simp [axisSwap]
  right_inv x := by
    ext j
    simp [axisSwap]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The upstream time coordinate is exactly the P⊗AI time coordinate. -/
@[simp] theorem time_eq (x : MinkowskiModel 3) :
    YangMills.time (pointLinear x) = x 0 := by
  change x (axisSwap 3) = x 0
  simp [axisSwap]

/-- The physical `(+---)` Minkowski square is preserved by the permutation,
even though the underlying coordinates use different time positions. -/
theorem minkowskiSquare_eq (x : MinkowskiModel 3) :
    YangMills.minkowskiSquare (pointLinear x) = minkowskiForm .timePositive 3 x x := by
  unfold YangMills.minkowskiSquare
  rw [EuclideanSpace.real_norm_sq_eq, minkowskiForm_apply]
  simp [YangMills.time, YangMills.timeAxis, YangMills.spatial, pointLinear,
    axisSwap, Equiv.swap_apply_def, Fin.sum_univ_succ, lorentzSign]
  ring

/-- The same change of coordinates applies to each field insertion point. -/
def configurations (n : ℕ) :
    (Fin n → MinkowskiModel 3) ≃ₗ[ℝ] (Fin n → YangMills.Spacetime) :=
  LinearEquiv.piCongrRight (fun _ => pointLinear)

@[simp] theorem configurations_apply {n : ℕ} (x : Fin n → MinkowskiModel 3)
    (i : Fin n) : configurations n x i = pointLinear (x i) := rfl

theorem configurations_injective {n : ℕ} (x : Fin n → MinkowskiModel 3) :
    Function.Injective (configurations n x) ↔ Function.Injective x := by
  constructor
  · intro h i j hij
    exact h (congrArg pointLinear hij)
  · intro h i j hij
    exact h (pointLinear.injective hij)

/-- The upstream squared interval equals the convention-independent quadratic form. -/
theorem interval_eq (x : MinkowskiModel 3) :
    YangMills.minkowskiSquare (pointLinear x) = intervalQuadratic x :=
  minkowskiSquare_eq x

theorem forwardCone_iff (x : MinkowskiModel 3) :
    pointLinear x ∈ YangMills.forwardCone ↔ FutureCausal x := by
  rw [futureCausal_iff]
  change ‖YangMills.spatial (pointLinear x)‖ ≤ YangMills.time (pointLinear x) ↔
    0 ≤ intervalQuadratic x ∧ 0 ≤ time x
  rw [← interval_eq]
  simp only [YangMills.minkowskiSquare, time_eq, time_apply]
  have hnorm := norm_nonneg (YangMills.spatial (pointLinear x))
  constructor
  · intro h
    constructor <;> nlinarith
  · rintro ⟨h, ht⟩
    nlinarith

/-- Conjugate a project Lorentz map into the upstream point coordinates. -/
def lorentzLinear (L : LorentzGroup 3) : YangMills.Spacetime ≃ₗ[ℝ] YangMills.Spacetime :=
  (pointLinear.symm.trans L.val).trans pointLinear

@[simp] theorem lorentzLinear_apply (L : LorentzGroup 3) (x : MinkowskiModel 3) :
    lorentzLinear L (pointLinear x) = pointLinear (L.val x) := by
  simp [lorentzLinear]

/-- Includes the transported project boosts, with the determinant and
forward-cone proofs required by the public upstream type. -/
def properLorentz (L : properOrthochronousLorentzGroup 3) : YangMills.ProperLorentz :=
  ⟨(lorentzLinear L.val).toContinuousLinearEquiv.toUnit, by
    change (lorentzLinear L.val).toLinearMap.det = 1 ∧ _ ∧ _
    refine ⟨?_, ?_, ?_⟩
    · have h : L.val.val.det = 1 := L.property.1
      rw [← LinearEquiv.coe_det, lorentzLinear, LinearEquiv.det_conj, h]
      rfl
    · intro y
      obtain ⟨x, rfl⟩ := pointLinear.surjective y
      change YangMills.minkowskiSquare (lorentzLinear L.val (pointLinear x)) = _
      rw [lorentzLinear_apply, interval_eq, interval_eq, LorentzGroup.preserves_interval]
    · intro y
      obtain ⟨x, rfl⟩ := pointLinear.surjective y
      change lorentzLinear L.val (pointLinear x) ∈ YangMills.forwardCone ↔ _
      rw [lorentzLinear_apply, forwardCone_iff, forwardCone_iff]
      exact L.property.2 x⟩

def poincareCoordinates (L : properOrthochronousLorentzGroup 3) (a : MinkowskiModel 3) :
    YangMills.PoincareCoordinates := (properLorentz L, pointLinear a)

theorem poincare_apply (L : properOrthochronousLorentzGroup 3) (a x : MinkowskiModel 3) :
    let p := poincareCoordinates L a
    p.1.val.val (pointLinear x) + p.2 =
      pointLinear ((PoincareGroup.ofLinearTranslation L.val a).val x) := by
  change lorentzLinear L.val (pointLinear x) + pointLinear a = _
  rw [lorentzLinear_apply, PoincareGroup.ofLinearTranslation_apply, map_add]

/-- The inverse affine point map is the map appearing in the upstream test pullback. -/
theorem poincare_pullback_point (L : properOrthochronousLorentzGroup 3) (a x : MinkowskiModel 3) :
    let p := poincareCoordinates L a
    (p.1.val⁻¹).val (pointLinear x - p.2) = pointLinear (L.val.val.symm (x - a)) := by
  change (lorentzLinear L.val).symm (pointLinear x - pointLinear a) = _
  apply (lorentzLinear L.val).injective
  rw [LinearEquiv.apply_symm_apply, lorentzLinear_apply, LinearEquiv.apply_symm_apply, map_sub]

/-- Lower a physical momentum with signature `(+---)` and express the covector
as the Euclidean vector used by Mathlib's characteristic function. -/
def fourierMomentum (p : MinkowskiModel 3) : YangMills.Spacetime :=
  pointLinear (fun i => lorentzSign .timePositive i * p i)

/-- Recover the physical time-first momentum from a Fourier covector. -/
def physicalMomentum (p : YangMills.Spacetime) : MinkowskiModel 3 :=
  fun i => lorentzSign .timePositive i * pointLinear.symm p i

@[simp] theorem fourierMomentum_physicalMomentum (p : YangMills.Spacetime) :
    fourierMomentum (physicalMomentum p) = p := by
  unfold fourierMomentum physicalMomentum
  rw [show (fun i => lorentzSign .timePositive i * (lorentzSign .timePositive i *
      pointLinear.symm p i)) = pointLinear.symm p by
    funext i
    rw [← mul_assoc, lorentzSign_sq, one_mul]]
  exact pointLinear.apply_symm_apply p

/-- Spatial sign reversal in the Fourier-to-physical identification preserves
the positive-energy cone. -/
theorem physicalMomentum_futureCausal (p : YangMills.Spacetime) :
    FutureCausal (physicalMomentum p) ↔ p ∈ YangMills.forwardCone := by
  have hp : p ∈ YangMills.forwardCone ↔ FutureCausal (pointLinear.symm p) := by
    simpa only [LinearEquiv.apply_symm_apply] using forwardCone_iff (pointLinear.symm p)
  have htime : time (physicalMomentum p) = time (pointLinear.symm p) := by
    simp [physicalMomentum, lorentzSign]
  have hq : intervalQuadratic (physicalMomentum p) = intervalQuadratic (pointLinear.symm p) := by
    simp only [intervalQuadratic_apply, pair, minkowskiForm_apply]
    apply Finset.sum_congr rfl
    intro i _
    let s := lorentzSign .timePositive (d := 3) i
    let v := pointLinear.symm p i
    change s * ((s * v) * (s * v)) = s * (v * v)
    calc
      _ = (s * s) * (s * (v * v)) := by ring
      _ = _ := by rw [lorentzSign_sq, one_mul]
  rw [hp, futureCausal_iff, futureCausal_iff, Causal, Causal, htime, hq]

theorem fourierMomentum_pairing (p a : MinkowskiModel 3) :
    inner ℝ (fourierMomentum p) (pointLinear a) = pair p a := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, fourierMomentum, pointLinear, axisSwap, Equiv.swap_apply_def,
    pair, minkowskiForm_apply, Fin.sum_univ_succ, lorentzSign]
  ring

/-- The Fourier covector transforms contragrediently under the transported
Lorentz map, including a proper orthochronous boost. -/
theorem fourierMomentum_covariance (L : LorentzGroup 3) (p a : MinkowskiModel 3) :
    inner ℝ (fourierMomentum (L.val p)) (pointLinear a) =
      inner ℝ (fourierMomentum p) ((lorentzLinear L).symm (pointLinear a)) := by
  have h : (lorentzLinear L).symm (pointLinear a) = pointLinear (L.val.symm a) := by
    apply (lorentzLinear L).injective
    rw [LinearEquiv.apply_symm_apply, lorentzLinear_apply, LinearEquiv.apply_symm_apply]
  rw [h, fourierMomentum_pairing, fourierMomentum_pairing]
  exact LorentzGroup.flat_natural L .timePositive p a

/-- Rewrite W0's Fourier phase without changing its translation argument.
The equality is conditional on the upstream W0 hypothesis. -/
theorem spectralRepresentation_minkowski {H : YangMills.HilbertSpace}
    {labels : YangMills.FieldLabels} {theory : YangMills.WightmanTheory H labels}
    (h : theory.W0) (state : H.carrier) (a : MinkowskiModel 3) :
    (∫ p, Complex.exp ((pair (physicalMomentum p) a : ℂ) * Complex.I)
      ∂theory.energyMomentum.diagonal state) =
      inner ℂ state (theory.translations.operator (pointLinear a) state) := by
  have hphase (p : YangMills.Spacetime) :
      pair (physicalMomentum p) a = inner ℝ p (pointLinear a) := by
    rw [← fourierMomentum_pairing, fourierMomentum_physicalMomentum]
  simp_rw [hphase]
  exact h.spectralRepresentation state (pointLinear a)

end ProjectAInos.SmoothGeometry.YangMillsCoordinates
