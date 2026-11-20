/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothAlgebra.CotangentModule
public import ProjectAinos.SpecialRelativity.Spacetime
import Mathlib.Tactic.Ring

/-!
# Four-covectors as universal C-infinity covectors

On spacetime `ℝ^{1+d}` in inertial coordinates, the universal C-infinity
cotangent module of the ring of smooth functions is free on `dx⁰, …, dxᵈ`.
Lowering the index with the diagonal Minkowski metric gives a module
isomorphism from vector fields to universal covectors,
`v ↦ Σ_μ η_{μμ} v^μ dx^μ`. Evaluated at an event it is the existing pointwise
`flat`, and its inverse is the existing `sharp`.

Pulling a universal covector back along a Lorentz transformation `L` is the
dual action: at `x` it is the covector at `L x` composed with `L`. Metric
duality commutes with this pullback, by the invariance of the metric
(`flat_natural`): the flat of a vector field pulls back to the flat of the
transformed field `x ↦ L⁻¹ v(L x)`.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.SpecialRelativity

open SmoothAlgebra SmoothAlgebra.SmoothOperation SmoothAlgebra.CotangentModule SmoothGeometry
  SmoothGeometry.Minkowski

variable (σ : LorentzConvention) (d : ℕ)

/-- Lowering the index of a vector field with the diagonal Minkowski metric,
`v ↦ (η_{μμ} v^μ)_μ`. It is its own inverse. -/
def lowerIndex : (Fin (d + 1) → SmoothOperation (d + 1)) ≃ₗ[SmoothOperation (d + 1)]
    (Fin (d + 1) → SmoothOperation (d + 1)) where
  toFun v μ := lorentzSign σ μ • v μ
  invFun v μ := lorentzSign σ μ • v μ
  map_add' v w := by
    funext μ
    simp only [Pi.add_apply, smul_add]
  map_smul' c v := by
    funext μ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul_comm]
  left_inv v := by
    funext μ
    simp only [smul_smul, lorentzSign_sq, one_smul]
  right_inv v := by
    funext μ
    simp only [smul_smul, lorentzSign_sq, one_smul]

variable {σ d}

/-- The components of a lowered field. -/
@[simp] theorem lowerIndex_apply (v : Fin (d + 1) → SmoothOperation (d + 1)) (μ : Fin (d + 1)) :
    lowerIndex σ d v μ = lorentzSign σ μ • v μ := rfl

/-- Raising the index is the same diagonal operation. -/
@[simp] theorem lowerIndex_symm_apply (v : Fin (d + 1) → SmoothOperation (d + 1))
    (μ : Fin (d + 1)) : (lowerIndex σ d).symm v μ = lorentzSign σ μ • v μ := rfl

variable (σ d)

/-- Metric duality between vector fields and universal covectors on `ℝ^{1+d}`:
`v ↦ Σ_μ η_{μμ} v^μ dx^μ`, an isomorphism of modules over the smooth functions. -/
def musical : (Fin (d + 1) → SmoothOperation (d + 1)) ≃ₗ[SmoothOperation (d + 1)]
    CotangentModule (SmoothOperation (d + 1)) :=
  (lowerIndex σ d).trans (coordinateEquiv (d + 1)).symm

variable {σ d}

/-- The lowered covector in coordinates. -/
theorem musical_apply (v : Fin (d + 1) → SmoothOperation (d + 1)) :
    musical σ d v = ∑ μ, (lorentzSign σ μ • v μ) •
      CotangentModule.d (SmoothOperation (d + 1)) (proj μ) :=
  ofCoordinates_apply _

/-- The coefficients of the lowered covector are the lowered components. -/
@[simp] theorem coordinates_musical (v : Fin (d + 1) → SmoothOperation (d + 1)) :
    coordinates (d + 1) (musical σ d v) = lowerIndex σ d v :=
  (coordinateEquiv (d + 1)).apply_symm_apply _

/-- Raising the index of a universal covector: its coefficients with raised index. -/
theorem musical_symm_apply (θ : CotangentModule (SmoothOperation (d + 1))) (μ : Fin (d + 1)) :
    (musical σ d).symm θ μ = lorentzSign σ μ • coordinates (d + 1) θ μ := rfl

/-- Under evaluation at an event, lowering the index of a vector field is the
pointwise `flat` of its value. -/
theorem cotangent_flat (v : Fin (d + 1) → SmoothOperation (d + 1)) (x : MinkowskiModel d) :
    evalAt x (musical σ d v) = flat σ (fun μ => v μ x) := by
  ext w
  rw [evalAt_apply, coordinates_musical, flat_apply, minkowskiForm_apply]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [lowerIndex_apply, ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- Under evaluation at an event, raising the index of a universal covector is
the pointwise `sharp` of its value. -/
theorem cotangent_sharp (θ : CotangentModule (SmoothOperation (d + 1))) (x : MinkowskiModel d) :
    sharp σ (evalAt x θ) = fun μ => (musical σ d).symm θ μ x := by
  funext μ
  rw [sharp_apply, evalAt_single, musical_symm_apply]
  rfl

/-- The lowered covector of a vector field is the unique universal covector
whose value at every event is the pointwise `flat`. -/
theorem musical_eq_iff (v : Fin (d + 1) → SmoothOperation (d + 1))
    (θ : CotangentModule (SmoothOperation (d + 1))) :
    musical σ d v = θ ↔ ∀ x : MinkowskiModel d, evalAt x θ = flat σ (fun μ => v μ x) := by
  constructor
  · rintro rfl x
    exact cotangent_flat v x
  · intro h
    exact ext_evalAt fun x => by rw [cotangent_flat, h]

/-- Pullback of spacetime functions along a Lorentz transformation, `f ↦ f ∘ L`. -/
def lorentzFunctionPullback (L : LorentzGroup d) :
    SmoothRingHom (SmoothOperation (d + 1)) (SmoothOperation (d + 1)) :=
  linearPullback
    (LorentzGroup.toContinuousLinearEquiv L : MinkowskiModel d →L[ℝ] MinkowskiModel d)

/-- The Lorentz pullback of a function is its composite with the transformation. -/
@[simp] theorem lorentzFunctionPullback_apply (L : LorentzGroup d) (f : SmoothOperation (d + 1))
    (x : MinkowskiModel d) : lorentzFunctionPullback L f x = f (L.val x) := rfl

/-- Pullback of universal covectors along a Lorentz transformation is the dual
action: at `x`, the covector at `L x` composed with `L`. -/
theorem cotangent_map_lorentz (L : LorentzGroup d)
    (θ : CotangentModule (SmoothOperation (d + 1))) (x : MinkowskiModel d) :
    evalAt x (map (lorentzFunctionPullback L) θ) =
      (evalAt (L.val x) θ).comp
        (LorentzGroup.toContinuousLinearEquiv L : MinkowskiModel d →L[ℝ] MinkowskiModel d) :=
  evalAt_map_linearPullback _ x θ

/-- The flat of a vector field pulls back along a Lorentz transformation to the
flat of the transformed field `x ↦ L⁻¹ v(L x)`, pointwise. -/
theorem cotangent_flat_lorentz (L : LorentzGroup d) (v : Fin (d + 1) → SmoothOperation (d + 1))
    (x : MinkowskiModel d) :
    evalAt x (map (lorentzFunctionPullback L) (musical σ d v)) =
      flat σ (L.val.symm (fun μ => v μ (L.val x))) := by
  rw [cotangent_map_lorentz, cotangent_flat]
  ext w
  have h := LorentzGroup.flat_natural L σ (L.val.symm (fun μ => v μ (L.val x))) (L.val w)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at h
  exact h

/-- The components of the transformed field `x ↦ L⁻¹ v(L x)`. -/
def lorentzPushforward (L : LorentzGroup d) (v : Fin (d + 1) → SmoothOperation (d + 1)) :
    Fin (d + 1) → SmoothOperation (d + 1) :=
  fun μ => ∑ ν, L.val.symm (Pi.single ν 1) μ • lorentzFunctionPullback L (v ν)

/-- The transformed field at an event is `L⁻¹ v(L x)`. -/
theorem lorentzPushforward_apply (L : LorentzGroup d)
    (v : Fin (d + 1) → SmoothOperation (d + 1)) (x : MinkowskiModel d) :
    (fun μ => lorentzPushforward L v μ x) = L.val.symm (fun ν => v ν (L.val x)) := by
  funext μ
  have hv : (fun ν => v ν (L.val x)) =
      ∑ ν, v ν (L.val x) • (Pi.single ν 1 : MinkowskiModel d) :=
    pi_eq_sum_univ' _
  rw [hv, map_sum, Finset.sum_apply]
  simp only [lorentzPushforward, SmoothOperation.sum_apply, ContMDiffMap.coe_smul,
    lorentzFunctionPullback_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun ν _ => mul_comm _ _

/-- Metric duality commutes with Lorentz pullback, as an identity of universal
covectors: the pullback of the flat of `v` is the flat of `x ↦ L⁻¹ v(L x)`. -/
theorem map_lorentzFunctionPullback_musical (L : LorentzGroup d)
    (v : Fin (d + 1) → SmoothOperation (d + 1)) :
    map (lorentzFunctionPullback L) (musical σ d v) = musical σ d (lorentzPushforward L v) :=
  ext_evalAt fun x => by
    rw [cotangent_flat_lorentz, cotangent_flat, lorentzPushforward_apply]

/-- On the spacetime of the special-relativity library, the value of a lowered
vector field at an event is the `metric` pairing with its value. -/
theorem cotangent_metric (v : Fin 4 → SmoothOperation 4) (x w : Spacetime) :
    evalAt x (musical .timeNegative 3 v) w = metric (fun μ => v μ x) w := by
  rw [cotangent_flat, flat_apply]
  rfl

end ProjectAinos.SpecialRelativity
