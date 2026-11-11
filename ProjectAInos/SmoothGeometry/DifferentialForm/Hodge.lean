/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.Exterior
import all Mathlib.LinearAlgebra.ExteriorPower.BilinForm
import all Mathlib.LinearAlgebra.ExteriorPower.HodgeStar

/-! # Hodge duality normalized by the wedge pairing

The defining equation is `vol (α ∧ star β) = B.exteriorPower k β α`.
For a symmetric metric the right side is the inner product of `α` and `β`.
This uses the perfect wedge pairing; it does not identify mathlib's
exterior-power Hodge map with this normalization without a comparison proof.
-/
@[expose] public section
noncomputable section
open Module exteriorPower
namespace ProjectAInos.SmoothGeometry.DifferentialForm

variable {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
  (B : LinearMap.BilinForm ℝ M) (hB : Function.Bijective B)
  (vol : ⋀[ℝ]^(Module.finrank ℝ M) M ≃ₗ[ℝ] ℝ) {k l : ℕ}

def hodge (hkl : k+l = Module.finrank ℝ M) : ⋀[ℝ]^k M ≃ₗ[ℝ] ⋀[ℝ]^l M :=
  (LinearEquiv.ofBijective (B.exteriorPower k) (B.bijective_exteriorPower k hB)).trans
    (wedgePairing vol hkl).flip.toPerfPair.symm

theorem hodge_pairing (hkl : k+l = Module.finrank ℝ M) (α β : ⋀[ℝ]^k M) :
    wedgePairing vol hkl α (hodge B hB vol hkl β) = B.exteriorPower k β α := by
  exact LinearMap.apply_toPerfPair_flip _ _ _

theorem hodge_unique (hkl : k+l = Module.finrank ℝ M) (β : ⋀[ℝ]^k M) (γ : ⋀[ℝ]^l M)
    (h : ∀ α, wedgePairing vol hkl α γ = B.exteriorPower k β α) :
    γ = hodge B hB vol hkl β := by
  apply (wedgePairing vol hkl).flip.toPerfPair.injective
  apply LinearMap.ext
  intro α
  exact (h α).trans (hodge_pairing B hB vol hkl α β).symm

omit [FiniteDimensional ℝ M] in
theorem exteriorPower_symmetric (h : B.IsSymm) (k : ℕ) : (B.exteriorPower k).IsSymm := by
  rw [LinearMap.isSymm_iff_eq_flip]
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro w
  change B.exteriorPower k (ιMulti ℝ k v) (ιMulti ℝ k w) =
    B.exteriorPower k (ιMulti ℝ k w) (ιMulti ℝ k v)
  simp only [LinearMap.BilinForm.bilinForm_ιMulti_ιMulti]
  rw [← Matrix.det_transpose]
  congr 1
  ext i j
  exact h.eq _ _

theorem hodge_pairing_symmetric (h : B.IsSymm) (hkl : k+l = Module.finrank ℝ M)
    (α β : ⋀[ℝ]^k M) :
    wedgePairing vol hkl α (hodge B hB vol hkl β) = B.exteriorPower k α β := by
  rw [hodge_pairing]
  exact (exteriorPower_symmetric B h k).eq β α

omit [FiniteDimensional ℝ M] in
theorem exteriorPower_smul (a : ℝ) (k : ℕ) :
    (a • B).exteriorPower k = a^k • B.exteriorPower k := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro w
  change (a • B).exteriorPower k (ιMulti ℝ k v) (ιMulti ℝ k w) =
    a^k * B.exteriorPower k (ιMulti ℝ k v) (ιMulti ℝ k w)
  simp only [LinearMap.BilinForm.bilinForm_ιMulti_ιMulti, LinearMap.smul_apply, smul_eq_mul]
  change (a • (Matrix.of fun i j => B (v j) (w i))).det = _
  rw [Matrix.det_smul, Fintype.card_fin]

theorem hodge_smul_metric (a : ℝ) (ha : Function.Bijective (a • B))
    (hkl : k+l = Module.finrank ℝ M) (β : ⋀[ℝ]^k M) :
    hodge (a • B) ha vol hkl β = a^k • hodge B hB vol hkl β := by
  symm
  apply hodge_unique
  intro α
  rw [map_smul, hodge_pairing, exteriorPower_smul]
  rfl

omit [FiniteDimensional ℝ M] in
theorem wedgePairing_reverse_volume (hkl : k+l = Module.finrank ℝ M)
    (α : ⋀[ℝ]^k M) (β : ⋀[ℝ]^l M) :
    wedgePairing (vol.trans (LinearEquiv.neg ℝ)) hkl α β =
      -wedgePairing vol hkl α β := by
  have aux {i j : ℕ} (h : i=j) (v : ⋀[ℝ]^i M ≃ₗ[ℝ] ℝ) :
      (h ▸ (v.trans (LinearEquiv.neg ℝ)).toLinearMap : ⋀[ℝ]^j M →ₗ[ℝ] ℝ) =
       -(h ▸ v.toLinearMap : ⋀[ℝ]^j M →ₗ[ℝ] ℝ) := by
    subst j
    rfl
  change (hkl.symm ▸ (vol.trans (LinearEquiv.neg ℝ)).toLinearMap) (exteriorPower.wedge ℝ M k l α β) =
    -(hkl.symm ▸ vol.toLinearMap) (exteriorPower.wedge ℝ M k l α β)
  rw [aux]
  rfl

theorem hodge_reverse_volume (hkl : k+l = Module.finrank ℝ M) (β : ⋀[ℝ]^k M) :
    hodge B hB (vol.trans (LinearEquiv.neg ℝ)) hkl β = -hodge B hB vol hkl β := by
  symm
  apply hodge_unique
  intro α
  rw [map_neg, wedgePairing_reverse_volume, hodge_pairing, neg_neg]

omit [FiniteDimensional ℝ M] in
private theorem cast_apply {i j : ℕ} (h : i=j) (f : ⋀[ℝ]^j M ≃ₗ[ℝ] ℝ) (x : ⋀[ℝ]^i M) :
    (h.symm ▸ f.toLinearMap) x = f (h ▸ x) := by subst j; rfl
omit [FiniteDimensional ℝ M] in
private theorem cast_coe {i j : ℕ} (h : i=j) (x : ⋀[ℝ]^i M) :
    ((h ▸ x : ⋀[ℝ]^j M) : ExteriorAlgebra ℝ M) = x := by subst j; rfl
omit [FiniteDimensional ℝ M] in
theorem wedgePairing_anticomm (vol : ⋀[ℝ]^(Module.finrank ℝ M) M ≃ₗ[ℝ] ℝ) {k l : ℕ}
    (hkl : k+l = Module.finrank ℝ M) (hlk : l+k = Module.finrank ℝ M) :
    wedgePairing vol hkl = (-1 : ℝ)^(k*l) • (wedgePairing vol hlk).flip := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro w
  change (hkl.symm ▸ vol.toLinearMap) (exteriorPower.wedge ℝ M k l (ιMulti ℝ k v) (ιMulti ℝ l w)) =
    (-1 : ℝ)^(k*l) * (hlk.symm ▸ vol.toLinearMap) (exteriorPower.wedge ℝ M l k (ιMulti ℝ l w) (ιMulti ℝ k v))
  rw [cast_apply, cast_apply, ← smul_eq_mul, ← map_smul]
  apply congrArg vol
  apply Subtype.ext
  rw [cast_coe, Submodule.coe_smul, cast_coe]
  simp only [DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul, ιMulti_apply_coe]
  have h := ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm ℝ v w
  change (ExteriorAlgebra.ιMulti ℝ k v) * (ExteriorAlgebra.ιMulti ℝ l w) =
    ((-1 : ℤ)^(l*k)) • ((ExteriorAlgebra.ιMulti ℝ l w) * (ExteriorAlgebra.ιMulti ℝ k v)) at h
  rw [← Int.cast_smul_eq_zsmul ℝ] at h
  simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one, Nat.mul_comm] using h
  all_goals assumption

theorem hodge_smul_metric_of_eq (C : LinearMap.BilinForm ℝ M) (hC : Function.Bijective C)
    (a : ℝ) (h : C = a • B) (hkl : k+l = Module.finrank ℝ M) (β : ⋀[ℝ]^k M) :
    hodge C hC vol hkl β = a^k • hodge B hB vol hkl β := by
  symm
  apply hodge_unique
  intro α
  rw [map_smul, hodge_pairing, h, exteriorPower_smul]
  rfl

/-- Our wedge-normalized star is the signed inverse of mathlib's opposite-degree map. -/
theorem hodge_eq_mathlib_inverse (hkl : k+l = Module.finrank ℝ M)
    (hlk : l+k = Module.finrank ℝ M) (β : ⋀[ℝ]^k M) :
    hodge B hB vol hkl β = (-1 : ℝ)^(k*l) • (exteriorPower.hodgeStar B hB vol hlk).symm β := by
  symm
  apply hodge_unique
  intro α
  rw [map_smul, wedgePairing_anticomm vol hkl hlk]
  have h := exteriorPower.exteriorPower_hodgeStar_eq_wedgePairing B hB vol hlk
    ((exteriorPower.hodgeStar B hB vol hlk).symm β)
  rw [LinearEquiv.apply_symm_apply] at h
  change (-1 : ℝ)^(k*l) * ((-1 : ℝ)^(k*l) * _) = _
  rw [← mul_assoc, ← mul_pow]
  norm_num

/-- Naturality under maps preserving both the metric pairing and oriented volume pairing. -/
theorem hodge_natural (hkl : k+l = Module.finrank ℝ M)
    (A : ⋀[ℝ]^k M ≃ₗ[ℝ] ⋀[ℝ]^k M) (C : ⋀[ℝ]^l M ≃ₗ[ℝ] ⋀[ℝ]^l M)
    (hmetric : ∀ α β, B.exteriorPower k (A α) (A β) = B.exteriorPower k α β)
    (hvolume : ∀ α γ, wedgePairing vol hkl (A α) (C γ) = wedgePairing vol hkl α γ)
    (β : ⋀[ℝ]^k M) : hodge B hB vol hkl (A β) = C (hodge B hB vol hkl β) := by
  symm
  apply hodge_unique
  intro α
  obtain ⟨α, rfl⟩ := A.surjective α
  rw [hvolume, hodge_pairing, hmetric]

end ProjectAInos.SmoothGeometry.DifferentialForm
