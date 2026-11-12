/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.FiniteWedge
public import ProjectAInos.SmoothGeometry.DifferentialForm.VolumeNormalization

/-! # Wedge-normalized Hodge duality on finite topological fibres

The inputs are a nondegenerate inverse metric on the algebraic cotangent
space and a nonzero oriented top form. All output forms are continuous;
the construction does not equip the native fibre with a norm.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module exteriorPower

namespace ProjectAInos.SmoothGeometry.DifferentialForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V]
  {k l : ℕ}

/-- Explicit transport of the finite degree of a native form. -/
def finiteDegreeCast (h : k = l) (α : V [⋀^Fin k]→L[ℝ] ℝ) : V [⋀^Fin l]→L[ℝ] ℝ := h ▸ α

theorem finiteToExterior_degreeCast (h : k = l) (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    finiteToExterior (finiteDegreeCast h α) = (h ▸ finiteToExterior α) := by subst l; rfl

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V] in
theorem finiteDegreeCast_ne_zero (h : k = l) {α : V [⋀^Fin k]→L[ℝ] ℝ} (hα : α ≠ 0) :
    finiteDegreeCast h α ≠ 0 := by subst l; exact hα

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V] in
theorem finiteDegreeCast_injective (h : k = l) :
    Function.Injective (finiteDegreeCast (V := V) h) := by subst l; exact Function.injective_id

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V] in
theorem finiteDegreeCast_trans {m : ℕ} (h : k = l) (h' : l = m) (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    finiteDegreeCast h' (finiteDegreeCast h α) = finiteDegreeCast (h.trans h') α := by
  subst m; subst l; rfl

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V] in
theorem finiteDegreeCast_smul (h : k = l) (r : ℝ) (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    finiteDegreeCast h (r • α) = r • finiteDegreeCast h α := by subst l; rfl

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V] in
theorem finiteDegreeCast_neg (h : k = l) (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    finiteDegreeCast h (-α) = -finiteDegreeCast h α := by subst l; rfl

variable (B : LinearMap.BilinForm ℝ (Dual ℝ V)) (hB : Function.Bijective B)
  (vol : V [⋀^Fin (Module.finrank ℝ (Dual ℝ V))]→L[ℝ] ℝ) (hv : vol ≠ 0)

/-- The functional evaluates a top covector as a multiple of the actual volume form. -/
def finiteVolumeFunctional : ⋀[ℝ]^(Module.finrank ℝ (Dual ℝ V)) (Dual ℝ V) ≃ₗ[ℝ] ℝ :=
  exteriorVolume (finiteToExterior vol) (by simpa using hv)

theorem finiteVolumeFunctional_self : finiteVolumeFunctional vol hv (finiteToExterior vol) = 1 :=
  exteriorVolume_self _ _

/-- Intrinsic Hodge equivalence on continuous alternating maps. -/
def finiteHodge (hkl : k + l = Module.finrank ℝ (Dual ℝ V)) :
    (V [⋀^Fin k]→L[ℝ] ℝ) ≃ₗ[ℝ] (V [⋀^Fin l]→L[ℝ] ℝ) :=
  finiteToExterior.trans
    ((hodge B hB (finiteVolumeFunctional vol hv) hkl).trans finiteToExterior.symm)

@[simp] theorem finiteToExterior_hodge (hkl : k + l = Module.finrank ℝ (Dual ℝ V))
    (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    finiteToExterior (finiteHodge B hB vol hv hkl α) =
      hodge B hB (finiteVolumeFunctional vol hv) hkl (finiteToExterior α) :=
  finiteToExterior.apply_symm_apply _

/-- The defining wedge equation on actual continuous forms. -/
theorem finiteHodge_wedge (hkl : k + l = Module.finrank ℝ (Dual ℝ V))
    (α β : V [⋀^Fin k]→L[ℝ] ℝ) :
    finiteDegreeCast hkl (finiteWedge α (finiteHodge B hB vol hv hkl β)) =
      B.exteriorPower k (finiteToExterior β) (finiteToExterior α) • vol := by
  apply finiteToExterior.injective
  rw [finiteToExterior_degreeCast, finiteToExterior_wedge, finiteToExterior_hodge, map_smul]
  exact hodge_wedge_volume B hB (finiteToExterior vol) _ hkl _ _

theorem finiteHodge_wedge_symmetric (hS : B.IsSymm)
    (hkl : k + l = Module.finrank ℝ (Dual ℝ V)) (α β : V [⋀^Fin k]→L[ℝ] ℝ) :
    finiteDegreeCast hkl (finiteWedge α (finiteHodge B hB vol hv hkl β)) =
      B.exteriorPower k (finiteToExterior α) (finiteToExterior β) • vol := by
  rw [finiteHodge_wedge]
  exact congrArg (fun r : ℝ => r • vol) ((exteriorPower_symmetric B hS k).eq _ _)

/-- The wedge equation determines Hodge uniquely. -/
theorem finiteHodge_unique (hkl : k + l = Module.finrank ℝ (Dual ℝ V))
    (β : V [⋀^Fin k]→L[ℝ] ℝ) (γ : V [⋀^Fin l]→L[ℝ] ℝ)
    (h : ∀ α : V [⋀^Fin k]→L[ℝ] ℝ,
      finiteDegreeCast hkl (finiteWedge α γ) =
        B.exteriorPower k (finiteToExterior β) (finiteToExterior α) • vol) :
    γ = finiteHodge B hB vol hv hkl β := by
  apply finiteToExterior.injective
  rw [finiteToExterior_hodge]
  apply hodge_unique
  intro α
  have he := congrArg finiteToExterior (h (finiteToExterior.symm α))
  rw [finiteToExterior_degreeCast, finiteToExterior_wedge, LinearEquiv.apply_symm_apply,
    map_smul] at he
  have hh := congrArg (finiteVolumeFunctional vol hv) he
  rw [map_smul, finiteVolumeFunctional_self, smul_eq_mul, mul_one] at hh
  have cast_apply {i j : ℕ} (hij : i = j)
      (f : ⋀[ℝ]^j (Dual ℝ V) →ₗ[ℝ] ℝ) (z : ⋀[ℝ]^i (Dual ℝ V)) :
      (hij.symm ▸ f) z = f (hij ▸ z) := by subst j; rfl
  change (hkl.symm ▸ (finiteVolumeFunctional vol hv).toLinearMap)
    (exteriorPower.wedge ℝ (Dual ℝ V) k l α (finiteToExterior γ)) = _
  rw [cast_apply hkl]
  exact hh

/-- Rescaling oriented volume by a nonzero scalar rescales Hodge by the same scalar. -/
theorem finiteHodge_scale_volume (r : ℝ) (hr : r ≠ 0)
    (hkl : k + l = Module.finrank ℝ (Dual ℝ V)) (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    finiteHodge B hB (r • vol) (smul_ne_zero hr hv) hkl α =
      r • finiteHodge B hB vol hv hkl α := by
  apply finiteToExterior.injective
  rw [finiteToExterior_hodge, map_smul, finiteToExterior_hodge]
  unfold finiteVolumeFunctional
  simp only [map_smul]
  exact hodge_scale_volume B hB _ _ r hr hkl _

/-- Equal volume forms give the same Hodge map, independently of nonvanishing proofs. -/
theorem finiteHodge_congr_volume
    (vol' : V [⋀^Fin (Module.finrank ℝ (Dual ℝ V))]→L[ℝ] ℝ) (hv' : vol' ≠ 0) (h : vol = vol')
    (hkl : k + l = Module.finrank ℝ (Dual ℝ V)) (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    finiteHodge B hB vol hv hkl α = finiteHodge B hB vol' hv' hkl α := by
  subst vol'
  rfl

/-- Changing only orientation negates Hodge in every degree. -/
theorem finiteHodge_reverse_volume (hkl : k + l = Module.finrank ℝ (Dual ℝ V))
    (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    finiteHodge B hB (-vol) (neg_ne_zero.mpr hv) hkl α = -finiteHodge B hB vol hv hkl α := by
  calc
    _ = finiteHodge B hB ((-1 : ℝ) • vol) (smul_ne_zero (by norm_num) hv) hkl α :=
      finiteHodge_congr_volume B hB _ _ _ _ (_root_.neg_one_smul ℝ vol).symm hkl α
    _ = (-1 : ℝ) • finiteHodge B hB vol hv hkl α :=
      finiteHodge_scale_volume B hB vol hv (-1) (by norm_num) hkl α
    _ = _ := _root_.neg_one_smul ℝ (finiteHodge B hB vol hv hkl α)

/-- Scaling the inverse metric by `a` scales degree-`k` Hodge by `a^k`. -/
theorem finiteHodge_scale_metric (C : LinearMap.BilinForm ℝ (Dual ℝ V))
    (hC : Function.Bijective C) (a : ℝ) (h : C = a • B)
    (hkl : k + l = Module.finrank ℝ (Dual ℝ V)) (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    finiteHodge C hC vol hv hkl α = a ^ k • finiteHodge B hB vol hv hkl α := by
  apply finiteToExterior.injective
  rw [finiteToExterior_hodge, map_smul, finiteToExterior_hodge]
  exact hodge_smul_metric_of_eq B hB _ C hC a h hkl _

end ProjectAInos.SmoothGeometry.DifferentialForm
