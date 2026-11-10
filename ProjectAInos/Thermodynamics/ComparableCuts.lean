module

public import ProjectAInos.Thermodynamics.Representation

/-!
# Entropy coordinates on comparable reference intervals

A state comparable with every mixture of two ordered reference states has a
real coordinate between those references. Comparison on the entire process
space is not needed for this local conclusion.
-/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace ProjectAInos.Thermodynamics

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A nonzero direction in a salient cone has precisely the nonnegative
scalar multiples in the cone. -/
theorem smul_mem_cone_iff_nonneg (P : PointedCone ℝ V)
    (hP : (P : ConvexCone ℝ V).Salient) {e : V} (he : e ∈ P) (hne : e ≠ 0)
    (r : ℝ) : r • e ∈ P ↔ 0 ≤ r := by
  refine ⟨fun hr => ?_, fun hr => P.smul_mem hr he⟩
  by_contra h
  have hrneg : r < 0 := lt_of_not_ge h
  have hminus := P.smul_mem (neg_nonneg.mpr (inv_nonpos.mpr hrneg.le)) hr
  have hcoeff : -r⁻¹ * r = -1 := by rw [neg_mul, inv_mul_cancel₀ hrneg.ne]
  rw [smul_smul, hcoeff, neg_one_smul] at hminus
  exact hP e he hne hminus

/-- Comparing a state with the mixtures of ordered references determines an
actual affine coordinate in the unit interval. -/
theorem exists_smul_eq_of_comparable_interval (P : PointedCone ℝ V)
    (hSC : SequentialOrderClosed P) (hP : (P : ConvexCone ℝ V).Salient)
    {e w : V} (he : e ∈ P) (hne : e ≠ 0) (hw : w ∈ P) (hew : e - w ∈ P)
    (hcompare : ∀ r ∈ Icc (0 : ℝ) 1, w - r • e ∈ P ∨ -(w - r • e) ∈ P) :
    ∃ r ∈ Icc (0 : ℝ) 1, w = r • e := by
  have hfull (r : ℝ) : w - r • e ∈ P ∨ -(w - r • e) ∈ P := by
    by_cases hr : r < 0
    · left
      simpa only [neg_smul, sub_eq_add_neg] using
        P.add_mem hw (P.smul_mem (neg_nonneg.mpr hr.le) he)
    by_cases hr' : 1 < r
    · right
      have h := P.add_mem hew (P.smul_mem (sub_nonneg.mpr hr'.le) he)
      convert h using 1
      module
    exact hcompare r ⟨le_of_not_gt hr, le_of_not_gt hr'⟩
  have hnonempty : (entropyCut P e w).Nonempty := ⟨0, by simpa [entropyCut] using hw⟩
  let r := sSup (entropyCut P e w)
  have heq : w = r • e :=
    (entropyCut_sSup_smul_of_comparable P hSC hP he hne hnonempty hfull).symm
  refine ⟨r, ⟨?_, ?_⟩, heq⟩
  · exact (smul_mem_cone_iff_nonneg P hP he hne r).mp (heq ▸ hw)
  · have h : (1 - r) • e ∈ P := by
      convert hew using 1
      rw [heq]
      module
    have := (smul_mem_cone_iff_nonneg P hP he hne (1 - r)).mp h
    linarith

end ProjectAInos.Thermodynamics
