/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ProjectAInos.SmoothGeometry.DifferentialForm.Hodge
import all Mathlib.LinearAlgebra.ExteriorPower.BilinForm
import all Mathlib.LinearAlgebra.ExteriorPower.WedgePairing

/-! # Hodge duality in an orthogonal basis -/
@[expose] public section
noncomputable section
open Module exteriorPower Set
namespace ProjectAInos.SmoothGeometry.DifferentialForm
variable {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
variable {I : Type*} [Fintype I] [LinearOrder I] (b : Basis I ℝ M)
/-- Volume functional at an explicitly given top degree. -/
def basisVolumeDegree (n : ℕ) (hn : n = Fintype.card I) : ⋀[ℝ]^n M ≃ₗ[ℝ] ℝ := by
  letI : Unique (powersetCard I n) :=
    { default := ⟨Finset.univ, by simp [hn]⟩
      uniq s := by
        apply Subtype.ext
        exact Finset.eq_univ_of_card _ (by simp [← hn]) }
  exact (b.exteriorPower n).equivFun.trans (LinearEquiv.funUnique _ ℝ ℝ)

omit [FiniteDimensional ℝ M] in
theorem basisVolumeDegree_cast {n m : ℕ} (h : n=m) (hm : m=Fintype.card I)
    (x : ⋀[ℝ]^n M) :
    (h.symm ▸ (basisVolumeDegree b m hm).toLinearMap) x = basisVolumeDegree b n (h.trans hm) x := by
  subst m
  rfl

/-- Volume functional normalized to one on the ordered top basis vector. -/
def basisVolume : ⋀[ℝ]^(Module.finrank ℝ M) M ≃ₗ[ℝ] ℝ :=
  basisVolumeDegree b _ (Module.finrank_eq_card_basis b)

omit [FiniteDimensional ℝ M] in
@[simp] theorem basisVolume_top : basisVolume b b.topVector = 1 := by
  simp [-Basis.topVector_eq_exteriorPower, -coe_basis, basisVolume, basisVolumeDegree,
    Basis.topVector, Basis.equivFun_apply]
  exact Finsupp.single_eq_same

variable (B : LinearMap.BilinForm ℝ M) (ε : I → ℝ)

def basisSign {k : ℕ} (s : powersetCard I k) : ℝ := (powersetCard.sign s : ℤ)

@[simp] theorem basisSign_sq {k : ℕ} (s : powersetCard I k) : basisSign s * basisSign s = 1 := by
  unfold basisSign
  norm_cast
  exact Int.units_coe_mul_self (powersetCard.sign s)

theorem basisSign_smul {k : ℕ} (s : powersetCard I k) (x : ℝ) :
    powersetCard.sign s • x = basisSign s * x := by
  change (powersetCard.sign s : ℤ) • x = _
  rw [← Int.cast_smul_eq_zsmul ℝ]
  rfl

omit [Fintype I] in
theorem basis_product {k : ℕ} (s : powersetCard I k) :
    (∏ j : Fin k, ε (powersetCard.ofFinEmbEquiv.symm s j)) = ∏ i ∈ s.val, ε i := by
  rw [← Finset.prod_coe_sort s.val ε]
  exact Fintype.prod_equiv (powersetCard.orderIsoOfFin s).toEquiv
    (fun j => ε (powersetCard.ofFinEmbEquiv.symm s j)) (fun i => ε i.val) (fun _ => rfl)

omit [FiniteDimensional ℝ M] [Fintype I] in
theorem exteriorPower_orthogonal_basis (h : ∀ i, B (b i) = ε i • b.coord i)
    (k : ℕ) (s : powersetCard I k) :
    B.exteriorPower k (b.exteriorPower k s) = (∏ i ∈ s.val, ε i) • (b.exteriorPower k).coord s := by
  rw [LinearMap.BilinForm.exteriorPower, LinearMap.comp_apply,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family, exteriorPower.map_apply_ιMulti]
  simp only [Function.comp_def, h]
  rw [AlternatingMap.map_smul_univ, map_smul, basis_product]
  congr 1
  rw [exteriorPower.basis_coord]
  rfl

omit [FiniteDimensional ℝ M] in
theorem wedgePairing_basis (vol : ⋀[ℝ]^(Module.finrank ℝ M) M ≃ₗ[ℝ] ℝ) {k l : ℕ}
    (hkl : k+l = Module.finrank ℝ M) (s : powersetCard I k) (t : powersetCard I l) :
    wedgePairing vol hkl (b.exteriorPower k s) (b.exteriorPower l t) =
      basisSign s * vol b.topVector * if Disjoint s.val t.val then 1 else 0 := by
  rw [← basisSign_smul, wedgePairing_eq_apply_topVector_smul vol hkl b]
  have hcard : k+l = Fintype.card I := hkl.trans (Module.finrank_eq_card_basis b)
  simp [-Basis.coe_dualBasis, -coe_basis, Basis.groupSMul_apply, Basis.dualBasis_apply_self,
    Equiv.eq_symm_apply, eq_comm (b := s), powersetCard.disjoint_iff_eq_compl hcard]

theorem hodge_basis (hB : Function.Bijective B) (h : ∀ i, B (b i) = ε i • b.coord i)
    (vol : ⋀[ℝ]^(Module.finrank ℝ M) M ≃ₗ[ℝ] ℝ) (hv : vol b.topVector = 1)
    {k l : ℕ} (hkl : k+l = Module.finrank ℝ M) (s : powersetCard I k) :
    hodge B hB vol hkl (b.exteriorPower k s) =
      ((∏ i ∈ s.val, ε i) * basisSign s) •
        b.exteriorPower l ((powersetCard.compl (hkl.trans (Module.finrank_eq_card_basis b))).symm s) := by
  symm
  apply hodge_unique
  intro α
  suffices H : (wedgePairing vol hkl).flip
      (((∏ i ∈ s.val, ε i) * basisSign s) •
        b.exteriorPower l ((powersetCard.compl (hkl.trans (Module.finrank_eq_card_basis b))).symm s)) =
      B.exteriorPower k (b.exteriorPower k s) from congrArg (fun f => f α) H
  apply (b.exteriorPower k).ext
  intro t
  change wedgePairing vol hkl (b.exteriorPower k t) _ = _
  rw [map_smul, wedgePairing_basis, hv, exteriorPower_orthogonal_basis b B ε h]
  by_cases ht : s=t
  · subst t
    simp [-coe_basis, powersetCard.compl_symm, Basis.coord_apply, smul_eq_mul, mul_assoc, disjoint_compl_right]
  · have hd : ¬Disjoint t.val ((powersetCard.compl (hkl.trans (Module.finrank_eq_card_basis b))).symm s).val := by
      rw [powersetCard.compl_symm, powersetCard.coe_compl]
      intro hd
      have hts : t.val ⊆ s.val := by
        intro i hit
        by_contra his
        exact Finset.disjoint_left.mp hd hit (Finset.mem_compl.mpr his)
      exact ht (powersetCard.eq_iff_subset.mpr hts).symm
    simp [-coe_basis, hd, Basis.coord_apply, ht]

/- The two complement shuffle signs multiply to the graded commutativity sign. -/
omit [FiniteDimensional ℝ M] in
theorem basisSign_complement (vol : ⋀[ℝ]^(Module.finrank ℝ M) M ≃ₗ[ℝ] ℝ)
    (hv : vol b.topVector = 1) {k l : ℕ} (hkl : k+l = Module.finrank ℝ M)
    (s : powersetCard I k) :
    basisSign s * basisSign ((powersetCard.compl (hkl.trans (Module.finrank_eq_card_basis b))).symm s) =
      (-1 : ℝ)^(k*l) := by
  let t := (powersetCard.compl (hkl.trans (Module.finrank_eq_card_basis b))).symm s
  have hlk : l+k = Module.finrank ℝ M := by omega
  have h := congrArg (fun W : ⋀[ℝ]^k M →ₗ[ℝ] ⋀[ℝ]^l M →ₗ[ℝ] ℝ =>
      W (b.exteriorPower k s) (b.exteriorPower l t)) (wedgePairing_anticomm vol hkl hlk)
  change wedgePairing vol hkl (b.exteriorPower k s) (b.exteriorPower l t) =
    (-1 : ℝ)^(k*l) * wedgePairing vol hlk (b.exteriorPower l t) (b.exteriorPower k s) at h
  rw [wedgePairing_basis, wedgePairing_basis, hv] at h
  have hd : Disjoint s.val t.val := by simp [t, powersetCard.compl_symm, disjoint_compl_right]
  simp only [hd, hd.symm, ite_true, mul_one] at h
  change basisSign s * basisSign t = _
  rw [h, mul_assoc, basisSign_sq, mul_one]

/-- The square of the normalized Hodge operator, with the metric determinant explicit. -/
theorem hodge_square_orthogonal (hB : Function.Bijective B)
    (h : ∀ i, B (b i) = ε i • b.coord i)
    (vol : ⋀[ℝ]^(Module.finrank ℝ M) M ≃ₗ[ℝ] ℝ) (hv : vol b.topVector = 1)
    {k l : ℕ} (hkl : k+l = Module.finrank ℝ M) (hlk : l+k = Module.finrank ℝ M)
    (α : ⋀[ℝ]^k M) :
    hodge B hB vol hlk (hodge B hB vol hkl α) = ((-1 : ℝ)^(k*l) * ∏ i, ε i) • α := by
  suffices H : (hodge B hB vol hlk).toLinearMap.comp (hodge B hB vol hkl).toLinearMap =
      ((-1 : ℝ)^(k*l) * ∏ i, ε i) • LinearMap.id from congrArg (fun f => f α) H
  apply (b.exteriorPower k).ext
  intro s
  change hodge B hB vol hlk (hodge B hB vol hkl (b.exteriorPower k s)) = _
  rw [hodge_basis b B ε hB h vol hv, map_smul, hodge_basis b B ε hB h vol hv, smul_smul]
  have hc : (powersetCard.compl (hlk.trans (Module.finrank_eq_card_basis b))).symm
      ((powersetCard.compl (hkl.trans (Module.finrank_eq_card_basis b))).symm s) = s := by
    apply Subtype.ext
    simp [powersetCard.compl_symm]
  rw [hc]
  change (_ : ℝ) • b.exteriorPower k s = ((-1 : ℝ)^(k*l) * ∏ i, ε i) • b.exteriorPower k s
  congr 1
  have hs := basisSign_complement b vol hv hkl s
  have hp : (∏ i ∈ s.val, ε i) *
      (∏ i ∈ ((powersetCard.compl (hkl.trans (Module.finrank_eq_card_basis b))).symm s).val, ε i) =
      ∏ i, ε i := by
    simp only [powersetCard.compl_symm, powersetCard.coe_compl]
    exact Finset.prod_mul_prod_compl s.val ε
  calc
    _ = (basisSign s * basisSign ((powersetCard.compl (hkl.trans (Module.finrank_eq_card_basis b))).symm s)) *
        ((∏ i ∈ s.val, ε i) *
        (∏ i ∈ ((powersetCard.compl (hkl.trans (Module.finrank_eq_card_basis b))).symm s).val, ε i)) := by ring
    _ = _ := by rw [hs, hp]

end ProjectAInos.SmoothGeometry.DifferentialForm
