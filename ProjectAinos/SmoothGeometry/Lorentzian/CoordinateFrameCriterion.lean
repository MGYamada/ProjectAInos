/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateMetric
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# A frame criterion for coordinate metrics

`CoordinateMetric.ofCriterion` asks the form to be negative on the time axis `e₀` and positive
definite on the spatial vectors, after the factor `−σ.timeSign`. A non-diagonal form such as the
Eddington–Finkelstein or the Kerr form can vanish on `e₀`, for instance where the coefficient
`g₀₀` changes sign (Landau–Lifshitz §§102, 104). The criterion here asks the same of the form
in a pointwise change of basis `P x`.

* `CoordinateMetric.ofFrameCriterion`: a symmetric smooth family that is negative on `P x e₀`
  and positive on `P x (0, v)` for `v ≠ 0`, after the factor `−σ.timeSign`, is a coordinate
  metric. The basis `P x` need not depend smoothly on `x`.
* `CoordinateMetric.ofFrameCriterion_refl`: for `P x = id` it is `ofCriterion`.
* `CoordinateMetric.nullForm`, `CoordinateMetric.nullMetric`: in `1 + 1` dimensions the form
  `v₀ w₁ + v₁ w₀`, which vanishes on `e₀` so that `ofCriterion` does not apply
  (`not_nullForm_timeAxis_neg`), is a Lorentz metric on the whole model space.
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap TopologicalSpace
open scoped ContDiff

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

/-- A symmetric smooth family whose form, in a pointwise basis `P x` and after the factor
`−σ.timeSign`, is negative on `P x e₀` and positive on `P x (0, v)` for every `v ≠ 0`, at every
point of `U`, is a coordinate metric. The basis need not depend smoothly on the point. -/
def ofFrameCriterion (B : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B U) (hs : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (P : MinkowskiModel d → MinkowskiModel d ≃L[ℝ] MinkowskiModel d)
    (ht : ∀ x ∈ U, -σ.timeSign *
      B x (P x (Fin.cons 1 (0 : Fin d → ℝ))) (P x (Fin.cons 1 (0 : Fin d → ℝ))) < 0)
    (hx : ∀ x ∈ U, ∀ v : Fin d → ℝ, v ≠ 0 →
      0 < -σ.timeSign * B x (P x (Fin.cons 0 v)) (P x (Fin.cons 0 v))) :
    CoordinateMetric σ d U where
  form := B
  smooth := hB
  signature x hx' := by
    obtain ⟨e, he⟩ := Minkowski.exists_lorentzFrame_convention σ
      ((B x).bilinearComp (P x : MinkowskiModel d →L[ℝ] MinkowskiModel d)
        (P x : MinkowskiModel d →L[ℝ] MinkowskiModel d))
      (fun v w => by simp only [bilinearComp_apply, hs x hx'])
      (by simpa only [bilinearComp_apply, ContinuousLinearEquiv.coe_coe] using ht x hx')
      (fun v hv => by
        simpa only [bilinearComp_apply, ContinuousLinearEquiv.coe_coe] using hx x hx' v hv)
    refine ⟨(P x).symm.trans e, fun v w => ?_⟩
    have h := he ((P x).symm v) ((P x).symm w)
    simp only [bilinearComp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply] at h
    simpa only [ContinuousLinearEquiv.trans_apply] using h

/-- The form of the coordinate metric given by the frame criterion is the given family. -/
@[simp] theorem ofFrameCriterion_form
    (B : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B U) (hs : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (P : MinkowskiModel d → MinkowskiModel d ≃L[ℝ] MinkowskiModel d)
    (ht : ∀ x ∈ U, -σ.timeSign *
      B x (P x (Fin.cons 1 (0 : Fin d → ℝ))) (P x (Fin.cons 1 (0 : Fin d → ℝ))) < 0)
    (hx : ∀ x ∈ U, ∀ v : Fin d → ℝ, v ≠ 0 →
      0 < -σ.timeSign * B x (P x (Fin.cons 0 v)) (P x (Fin.cons 0 v))) :
    (ofFrameCriterion B hB hs P ht hx).form = B := rfl

/-- With the identity basis at every point, the frame criterion is `ofCriterion`. -/
theorem ofFrameCriterion_refl
    (B : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B U) (hs : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (ht : ∀ x ∈ U, -σ.timeSign *
      B x (Fin.cons 1 (0 : Fin d → ℝ)) (Fin.cons 1 (0 : Fin d → ℝ)) < 0)
    (hx : ∀ x ∈ U, ∀ v : Fin d → ℝ, v ≠ 0 →
      0 < -σ.timeSign * B x (Fin.cons 0 v) (Fin.cons 0 v)) :
    ofFrameCriterion B hB hs (fun _ => ContinuousLinearEquiv.refl ℝ _) ht hx =
      ofCriterion B hB hs ht hx := rfl

/-! ### A non-diagonal instance in `1 + 1` dimensions -/

/-- The constant form `v₀ w₁ + v₁ w₀` on the model space of `1 + 1` dimensions. -/
def nullForm : MinkowskiModel 1 →L[ℝ] MinkowskiModel 1 →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.proj 0)
      (ContinuousLinearMap.proj 1) +
    (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.proj 1)
      (ContinuousLinearMap.proj 0)

/-- The value of the form `v₀ w₁ + v₁ w₀`. -/
@[simp] theorem nullForm_apply (v w : MinkowskiModel 1) :
    nullForm v w = v 0 * w 1 + v 1 * w 0 := rfl

/-- The form `v₀ w₁ + v₁ w₀` vanishes on the time axis, so that `ofCriterion` does not apply
to it. -/
theorem nullForm_timeAxis :
    nullForm (Fin.cons 1 (0 : Fin 1 → ℝ)) (Fin.cons 1 (0 : Fin 1 → ℝ)) = 0 := by
  simp

/-- For either convention, the time hypothesis `−σ.timeSign · g(e₀, e₀) < 0` of `ofCriterion`
fails for the form `v₀ w₁ + v₁ w₀`. -/
theorem not_nullForm_timeAxis_neg (σ : LorentzConvention) :
    ¬ (-σ.timeSign * nullForm (Fin.cons 1 (0 : Fin 1 → ℝ)) (Fin.cons 1 (0 : Fin 1 → ℝ)) < 0) := by
  rw [nullForm_timeAxis, mul_zero]
  exact lt_irrefl 0

/-- The change of basis `(t, x) ↦ (t + x, x − t)`. -/
def nullFrameLinear : MinkowskiModel 1 ≃ₗ[ℝ] MinkowskiModel 1 where
  toFun v := ![v 0 + v 1, v 1 - v 0]
  invFun v := ![(v 0 - v 1) / 2, (v 0 + v 1) / 2]
  map_add' v w := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> simp <;> ring
  left_inv v := by
    funext i
    fin_cases i <;> simp <;> ring
  right_inv v := by
    funext i
    fin_cases i <;> simp <;> ring

/-- The change of basis `(t, x) ↦ (t + x, x − t)`, in which `v₀ w₁ + v₁ w₀` is
`2 (−t t' + x x')`. -/
def nullFrame : MinkowskiModel 1 ≃L[ℝ] MinkowskiModel 1 :=
  nullFrameLinear.toContinuousLinearEquiv

/-- The value of the change of basis `(t, x) ↦ (t + x, x − t)`. -/
@[simp] theorem nullFrame_apply (v : MinkowskiModel 1) :
    nullFrame v = ![v 0 + v 1, v 1 - v 0] := by
  rw [nullFrame, LinearEquiv.coe_toContinuousLinearEquiv']
  rfl

/-- The form `v₀ w₁ + v₁ w₀` is a Lorentz metric on the whole model space of `1 + 1`
dimensions, with the convention `.timeNegative`, by the frame criterion. -/
def nullMetric : CoordinateMetric .timeNegative 1 ⊤ :=
  ofFrameCriterion (fun _ => nullForm) contDiffOn_const
    (fun _ _ v w => by simp only [nullForm_apply]; ring) (fun _ => nullFrame)
    (fun _ _ => by norm_num)
    (fun _ _ v hv => by
      have h0 : v 0 ≠ 0 := fun h => hv (funext fun i => by fin_cases i; exact h)
      have h := mul_self_pos.mpr h0
      norm_num
      nlinarith)

/-- The form of `nullMetric` is `v₀ w₁ + v₁ w₀` at every point. -/
@[simp] theorem nullMetric_form (x : MinkowskiModel 1) : nullMetric.form x = nullForm := rfl

end ProjectAinos.SmoothGeometry.CoordinateMetric
