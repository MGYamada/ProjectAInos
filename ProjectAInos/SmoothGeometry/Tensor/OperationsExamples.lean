/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.ChartExamples
public import ProjectAInos.SmoothGeometry.Tensor.Operations

/-! # Tensor operations in the nonlinear Minkowski charts -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle ContinuousLinearMap
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzianCharts

open Tensor.Shape

local notation "I" => 𝓘(ℝ, Plane)

/-- The constant coordinate covector on the model plane. -/
def coordinateCovectorField (i : Fin 2) : (cotangent.bundle I (M := Plane)).Section I :=
  ⟨fun _ => proj i, by
    intro p
    rw [contMDiffAt_section]
    have h : ContMDiffAt I 𝓘(ℝ, Plane →L[ℝ] ℝ) ∞ (fun _ : Plane => (proj i : Plane →L[ℝ] ℝ)) p :=
      contMDiffAt_const
    convert h using 1
    funext q
    ext v
    simp [hom_trivializationAt_apply, inCoordinates]
    rfl⟩

/-- The nonlinear pullback of the nonsymmetric tensor `dT ⊗ dX`. -/
theorem shear_tensorProduct_coordinates (p v w : Plane) :
    pullbackField I (covariant 2) shearDiffeomorph
      (tensorProductField I [.tangent] [.tangent]
        (coordinateCovectorField 0) (coordinateCovectorField 1)) p v w =
      v 0 * (w 1 + 2 * p 0 * w 0) := by
  have h := pullbackField_covariantTwo_apply I shearDiffeomorph
    (tensorProductField I [.tangent] [.tangent]
      (coordinateCovectorField 0) (coordinateCovectorField 1)) p v w
  change _ = (mfderiv I I shear p v) 0 * (mfderiv I I shear p w) 1 at h
  rw [mfderiv_shear] at h
  exact h

/-- The mixed tensor `∂ₓ ⊗ dt ⊗ dx` on the model tangent fibre. -/
def mixedCoordinateTensor (p : Plane) :
    ((mixed 1 2).bundle I).Fiber p :=
  tensorProduct I [.tangent, .tangent]
    ((proj 0 : Plane →L[ℝ] ℝ).smulRight (proj 1)) [cotangent]
    (ContinuousLinearMap.apply ℝ ℝ (Pi.single 1 1 : Plane))

/-- Contract the first and third slots of `∂ₓ ⊗ dt ⊗ dx`, retaining `dt`. -/
theorem mixed_tensorProduct_contract (p v : Plane) :
    contractSlots I (x := p) (as := [cotangent, .tangent, .tangent]) (bs := [.tangent])
      (.swap cotangent .tangent [.tangent]) (mixedCoordinateTensor p) v = v 0 := by
  have h := evaluate_contractSlots_eq_sum I (x := p)
    (as := [cotangent, .tangent, .tangent]) (bs := [.tangent])
    (.swap cotangent .tangent [.tangent]) (mixedCoordinateTensor p)
    (v, ()) (Pi.basisFun ℝ (Fin 2))
  refine h.trans ?_
  change (∑ i : Fin 2, ((Pi.basisFun ℝ (Fin 2)).coord i (Pi.single 1 1)) *
      (v 0 * (Pi.basisFun ℝ (Fin 2) i : Plane) 1)) = v 0
  simp [Fin.sum_univ_succ, Pi.basisFun_apply]

end ProjectAInos.SmoothGeometry.LorentzianCharts
