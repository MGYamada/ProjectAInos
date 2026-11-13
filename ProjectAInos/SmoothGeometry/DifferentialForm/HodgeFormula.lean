/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.HodgeTransport

/-! # Hodge coordinates through a fixed reference metric

The inverse metric is transferred in one slot before applying reference
Hodge. The volume coefficient then multiplies the result. This formula
uses only linear algebra on the native fibres.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module exteriorPower

namespace ProjectAInos.SmoothGeometry.DifferentialForm

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [T2Space W] [FiniteDimensional ℝ W]
  {n k l : ℕ}

theorem finiteWedge_smul_right (α : V [⋀^Fin k]→L[ℝ] ℝ)
    (β : V [⋀^Fin l]→L[ℝ] ℝ) (r : ℝ) :
    finiteWedge α (r • β) = r • finiteWedge α β := by
  apply finiteToExterior.injective
  simp only [finiteToExterior_wedge, map_smul]

/-- A reference Hodge gives the actual Hodge after inverse-metric precomposition
and multiplication by the oriented volume coefficient. -/
theorem finiteHodgeOfDegree_formula
    (B : LinearMap.BilinForm ℝ (Dual ℝ V)) (hB : Function.Bijective B)
    (C : LinearMap.BilinForm ℝ (Dual ℝ W)) (hC : Function.Bijective C)
    (volV : V [⋀^Fin n]→L[ℝ] ℝ) (hv : volV ≠ 0) (hnV : n = Module.finrank ℝ (Dual ℝ V))
    (volW : W [⋀^Fin n]→L[ℝ] ℝ) (hw : volW ≠ 0) (hnW : n = Module.finrank ℝ (Dual ℝ W))
    (L : V ≃L[ℝ] W) (T : W →L[ℝ] W) (r : ℝ)
    (hmetric : ∀ α β : Dual ℝ W,
      C (T.toLinearMap.dualMap α) β = B (L.toLinearMap.dualMap α) (L.toLinearMap.dualMap β))
    (hvolume : r • volW.compContinuousLinearMap L.toContinuousLinearMap = volV)
    (hkl : k + l = n) (β : W [⋀^Fin k]→L[ℝ] ℝ) :
    finiteHodgeOfDegree B hB volV hv hnV hkl
      (β.compContinuousLinearMap L.toContinuousLinearMap) =
      r • (finiteHodgeOfDegree C hC volW hw hnW hkl
        (β.compContinuousLinearMap T)).compContinuousLinearMap L.toContinuousLinearMap := by
  symm
  apply finiteHodgeOfDegree_unique
  intro α
  let a := α.compContinuousLinearMap L.symm.toContinuousLinearMap
  have ha : a.compContinuousLinearMap L.toContinuousLinearMap = α := by
    ext v
    change α (fun i => L.symm (L (v i))) = α v
    simp
  rw [← ha, finiteWedge_smul_right, finiteWedge_comp, finiteDegreeCast_smul,
    finiteDegreeCast_comp, finiteHodgeOfDegree_wedge]
  let D := B.compl₁₂ L.toLinearMap.dualMap L.toLinearMap.dualMap
  have hp := exteriorPower_pairing_precomp D C T.toLinearMap.dualMap hmetric
    (finiteToExterior β) (finiteToExterior a)
  have hq := exteriorPower_pairing_map D B L.toLinearMap.dualMap (fun _ _ => rfl)
    (finiteToExterior β) (finiteToExterior a)
  have hp' : C.exteriorPower k (finiteToExterior (β.compContinuousLinearMap T))
      (finiteToExterior a) = B.exteriorPower k
        (finiteToExterior (β.compContinuousLinearMap L.toContinuousLinearMap))
        (finiteToExterior (a.compContinuousLinearMap L.toContinuousLinearMap)) := by
    rw [finiteToExterior_comp T β, finiteToExterior_comp L.toContinuousLinearMap β,
      finiteToExterior_comp L.toContinuousLinearMap a]
    exact hp.trans hq.symm
  rw [hp']
  ext v
  have hv' := congrArg (fun f : V [⋀^Fin n]→L[ℝ] ℝ => f v) hvolume
  change r * volW (fun i => L (v i)) = volV v at hv'
  change r * (_ * volW (fun i => L (v i))) = _ * volV v
  rw [← hv']
  ring

end ProjectAInos.SmoothGeometry.DifferentialForm
