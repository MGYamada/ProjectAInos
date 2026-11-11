/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian
public import ProjectAInos.External.YM.PublicTheory

/-!
# An explicit bridge between time-first and time-last spacetime coordinates

P⊗AI uses the time-first Minkowski model `(t,x,y,z)`; the upstream public
Yang--Mills API represents the same 4D point with time at index `3`. The
coordinate permutation is an actual real-linear equivalence. It is not an
identification of curved Lorentz manifolds or an assertion about the full
Euclidean-to-Minkowski analytic continuation of correlation functions.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace ProjectAInos.SmoothGeometry.YangMillsCoordinates

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
    YangMills.minkowskiSquare (pointLinear x) = minkowskiForm 3 x x := by
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

end ProjectAInos.SmoothGeometry.YangMillsCoordinates
