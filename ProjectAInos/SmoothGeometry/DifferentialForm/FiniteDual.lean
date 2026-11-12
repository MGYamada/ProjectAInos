/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.Exterior
public import ProjectAInos.SmoothGeometry.DifferentialForm.Coordinates

/-! # Exterior duality on finite-dimensional topological vector spaces

These equivalences apply to actual tangent fibres. Continuity follows by
transporting through a finite basis; no norm is installed on the fibre.
-/

@[expose] public section
noncomputable section
open Module exteriorPower

namespace ProjectAInos.SmoothGeometry.DifferentialForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V]
  {k : ℕ}

/-- Continuity of a finite alternating form uses only its vector-space topology. -/
theorem finite_alternating_continuous (α : V [⋀^Fin k]→ₗ[ℝ] ℝ) : Continuous α := by
  let e := (Module.finBasis ℝ V).equivFun.toContinuousLinearEquiv
  have h := coordinate_multilinear_continuous
    (α.compLinearMap e.symm.toLinearMap).toMultilinearMap
  have hc : Continuous (fun v : Fin k → V => fun i => e (v i)) := by fun_prop
  have hh := h.comp hc
  convert hh using 1
  ext v
  change α v = α (fun i => e.symm (e (v i)))
  simp

/-- Every algebraic alternating form on a finite native fibre is continuous. -/
def finiteContinuousAlternating (α : V [⋀^Fin k]→ₗ[ℝ] ℝ) : V [⋀^Fin k]→L[ℝ] ℝ :=
  { α with cont := finite_alternating_continuous α }

def finiteForgetContinuous : (V [⋀^Fin k]→L[ℝ] ℝ) ≃ₗ[ℝ] (V [⋀^Fin k]→ₗ[ℝ] ℝ) where
  toLinearMap := ContinuousAlternatingMap.toAlternatingMapLinear
  invFun := finiteContinuousAlternating
  left_inv α := by ext v; rfl
  right_inv α := rfl

/-- Native continuous forms are exterior powers of the algebraic cotangent space. -/
def finiteToExterior : (V [⋀^Fin k]→L[ℝ] ℝ) ≃ₗ[ℝ] ⋀[ℝ]^k (Dual ℝ V) :=
  finiteForgetContinuous.trans (exteriorPower.alternatingMapLinearEquiv.trans
    (LinearEquiv.ofBijective _ (exteriorPower.bijective_pairingDual ℝ V k)).symm)

theorem finite_pairing_toExterior (α : V [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → V) :
    pairingDual ℝ V k (finiteToExterior α) (ιMulti ℝ k v) = α v := by
  change (LinearEquiv.ofBijective _ (exteriorPower.bijective_pairingDual ℝ V k))
    ((LinearEquiv.ofBijective _ (exteriorPower.bijective_pairingDual ℝ V k)).symm
      (exteriorPower.alternatingMapLinearEquiv α.toAlternatingMap)) (ιMulti ℝ k v) = _
  rw [LinearEquiv.apply_symm_apply]
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

theorem finite_fromExterior_apply (α : ⋀[ℝ]^k (Dual ℝ V)) (v : Fin k → V) :
    finiteToExterior.symm α v = pairingDual ℝ V k α (ιMulti ℝ k v) := by
  rw [← finite_pairing_toExterior, LinearEquiv.apply_symm_apply]

/-- The native equivalence preserves the existing coordinate-model convention exactly. -/
theorem finiteToExterior_model {n : ℕ} (α : (Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ) :
    finiteToExterior α = toExterior α := rfl

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [T2Space W] [FiniteDimensional ℝ W]

/-- Exterior duality commutes with every continuous linear pullback, including singular maps. -/
theorem finite_fromExterior_map_dual (L : V →L[ℝ] W) (α : ⋀[ℝ]^k (Dual ℝ W)) :
    finiteToExterior.symm (exteriorPower.map k L.toLinearMap.dualMap α) =
      (finiteToExterior.symm α).compContinuousLinearMap L := by
  ext v
  rw [finite_fromExterior_apply]
  change pairingDual ℝ V k (exteriorPower.map k L.toLinearMap.dualMap α) (ιMulti ℝ k v) =
    finiteToExterior.symm α (L ∘ v)
  rw [finite_fromExterior_apply]
  suffices h : ((pairingDual ℝ V k).flip (ιMulti ℝ k v)).comp
      (exteriorPower.map k L.toLinearMap.dualMap) =
      (pairingDual ℝ W k).flip (ιMulti ℝ k (L ∘ v)) from congrArg (fun f => f α) h
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  change pairingDual ℝ V k (exteriorPower.map k L.toLinearMap.dualMap (ιMulti ℝ k a))
    (ιMulti ℝ k v) = pairingDual ℝ W k (ιMulti ℝ k a) (ιMulti ℝ k (L ∘ v))
  rw [exteriorPower.map_apply_ιMulti, pairingDual_ιMulti_ιMulti, pairingDual_ιMulti_ιMulti]
  rfl

theorem finiteToExterior_comp (L : V →L[ℝ] W) (α : W [⋀^Fin k]→L[ℝ] ℝ) :
    finiteToExterior (α.compContinuousLinearMap L) =
      exteriorPower.map k L.toLinearMap.dualMap (finiteToExterior α) := by
  apply finiteToExterior.symm.injective
  rw [LinearEquiv.symm_apply_apply, finite_fromExterior_map_dual, LinearEquiv.symm_apply_apply]

end ProjectAInos.SmoothGeometry.DifferentialForm
