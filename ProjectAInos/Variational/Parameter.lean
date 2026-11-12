/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Topology.Order.IntermediateValue

/-! # Regular parameter changes on intervals

A positive derivative supplies a single inverse over the whole open
interval, not just unrelated local inverses. These scalar calculus lemmas
are independent of geometric or physical models.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace ProjectAInos.Variational

/-- Endpoint neighborhoods and the closed interval together give one open
interval on which a predicate holds. -/
theorem exists_Ioo_superset_Icc {P : ℝ → Prop} {a b : ℝ}
    (hP : ∀ t ∈ Icc a b, P t) (ha : ∀ᶠ t in 𝓝 a, P t) (hb : ∀ᶠ t in 𝓝 b, P t) :
    ∃ l r : ℝ, l < a ∧ b < r ∧ ∀ t ∈ Ioo l r, P t := by
  obtain ⟨l, u, ⟨hla, hau⟩, hleft⟩ := ha.exists_Ioo_subset
  obtain ⟨v, r, ⟨hvb, hbr⟩, hright⟩ := hb.exists_Ioo_subset
  refine ⟨l, r, hla, hbr, ?_⟩
  intro t ht
  by_cases hta : t < a
  · exact hleft ⟨ht.1, hta.trans hau⟩
  by_cases hbt : b < t
  · exact hright ⟨hvb.trans hbt, ht.2⟩
  exact hP t ⟨le_of_not_gt hta, le_of_not_gt hbt⟩

/-- Positive derivative makes a C² scalar function an actual open partial
homeomorphism on its entire connected interval. Inverse regularity and its
derivative are derived, rather than included as premises. -/
theorem exists_positive_parameter_chart (f : ℝ → ℝ) {a b : ℝ}
    (hf : ContDiffOn ℝ 2 f (Ioo a b))
    (hp : ∀ t ∈ Ioo a b, 0 < deriv f t) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      (e : ℝ → ℝ) = f ∧ e.source = Ioo a b ∧ StrictMonoOn e e.source ∧
      ∀ τ ∈ e.target, ContDiffAt ℝ 2 e.symm τ ∧
        HasDerivAt e.symm (deriv f (e.symm τ))⁻¹ τ := by
  have hm : StrictMonoOn f (Ioo a b) := strictMonoOn_of_deriv_pos (convex_Ioo a b)
    hf.continuousOn (by simpa only [interior_Ioo] using hp)
  have hd : ∀ t ∈ Ioo a b, HasStrictDerivAt f (deriv f t) t := by
    intro t ht
    exact (hf.contDiffAt (isOpen_Ioo.mem_nhds ht)).hasStrictDerivAt (by norm_num)
  have ho : IsOpenMap ((Ioo a b).domRestrict f) := by
    apply isOpenMap_iff_nhds_le.mpr
    intro t
    have he : Filter.map ((Ioo a b).domRestrict f) (𝓝 t) = 𝓝 (f t) := by
      change Filter.map (f ∘ (Subtype.val : Ioo a b → ℝ)) (𝓝 t) = _
      rw [← Filter.map_map, isOpen_Ioo.isOpenEmbedding_subtypeVal.map_nhds_eq]
      exact (hd t t.property).map_nhds_eq (hp t t.property).ne'
    exact he.ge
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hm.injOn.toPartialEquiv f (Ioo a b)) hf.continuousOn ho isOpen_Ioo
  refine ⟨e, rfl, rfl, hm, ?_⟩
  intro τ hτ
  have ht : e.symm τ ∈ Ioo a b := e.map_target hτ
  have hde : HasDerivAt e (deriv f (e.symm τ)) (e.symm τ) := (hd _ ht).hasDerivAt
  exact ⟨e.contDiffAt_symm_deriv (hp _ ht).ne' hτ hde
    (hf.contDiffAt (isOpen_Ioo.mem_nhds ht)), e.hasDerivAt_symm hτ (hp _ ht).ne' hde⟩

end ProjectAInos.Variational
