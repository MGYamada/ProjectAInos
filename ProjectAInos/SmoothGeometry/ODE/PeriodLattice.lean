/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.ODE.JointFlow
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Connected.Clopen

/-!
# The period lattice of commuting flows on a compact connected set

Let the commuting fields `Xᵢ`, `i ∈ ι`, have complete flows on a set `M` that
they preserve, and let the joint flow be locally free on `M`
(`IsLocallyFree`): near every point `x` of `M`, the set `M` is the image of a
neighbourhood of zero of `ℝ^ι` under `t ↦ g^t x`, and this map is injective
near zero.

* `exists_jointFlow_eq`: if `M` is connected, the joint flow is transitive on
  `M`.
* `periods`: the subgroup of the `t` with `g^t x = x`. It does not depend on
  the point (`periods_eq`), and zero is isolated in it
  (`discreteTopology_periods`).
* `span_periods_eq_top`: if `M` is compact, the periods span `ℝ^ι`.
* `exists_basis_periods`: the periods are the integer combinations of a basis
  of `ℝ^ι`.
* `exists_torus_chart`: in the angles `θ` with `t = Σᵢ θᵢ bᵢ`, the map
  `θ ↦ g^t x` is onto `M`, two angles give the same point exactly when they
  differ by integers, and the flow of `Σᵢ sᵢ Xᵢ` is a uniform motion of the
  angles: the motion is conditionally periodic (Landau–Lifshitz §52).
-/

@[expose] public section
noncomputable section

open Set Filter Module
open scoped Topology ContDiff

namespace ProjectAInos.SmoothGeometry.NonlinearODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ι : Type*} [Fintype ι] {X : ι → E → E} {M : Set E}

/-- The joint flow is locally free on `M`: it is injective near the time zero
at every point of `M`, and the orbit of a point of `M` contains a neighbourhood
of the point in `M`, reached with small times. -/
structure IsLocallyFree (X : ι → E → E) (M : Set E) : Prop where
  /-- Near zero the only period is zero. -/
  injective : ∀ x ∈ M, ∃ δ : ℝ, 0 < δ ∧ ∀ t : ι → ℝ, ‖t‖ < δ → jointFlow X t x = x → t = 0
  /-- The orbit of a point with small times is a neighbourhood of the point in
  the set. -/
  open_orbit : ∀ x ∈ M, ∀ ε : ℝ, 0 < ε → ∃ W : Set E, IsOpen W ∧ x ∈ W ∧
    ∀ y ∈ M ∩ W, ∃ t : ι → ℝ, ‖t‖ < ε ∧ jointFlow X t x = y

section Lattice

variable (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hc : PairwiseCommute X) (hM : IsInvariantSet X M)

include hX hc hM in
/-- On a connected set on which the joint flow is locally free, the joint flow
is transitive. -/
theorem exists_jointFlow_eq (hloc : IsLocallyFree X M) (hconn : IsPreconnected M) {x y : E}
    (hx : x ∈ M) (hy : y ∈ M) : ∃ t : ι → ℝ, jointFlow X t x = y := by
  classical
  have hW : ∀ z : E, ∃ W : Set E, z ∈ M → IsOpen W ∧ z ∈ W ∧
      ∀ w ∈ M ∩ W, ∃ t : ι → ℝ, jointFlow X t z = w := fun z => by
    by_cases hz : z ∈ M
    · obtain ⟨W, hWo, hzW, hW⟩ := hloc.open_orbit z hz 1 one_pos
      exact ⟨W, fun _ => ⟨hWo, hzW, fun w hw => (hW w hw).imp fun t ht => ht.2⟩⟩
    · exact ⟨∅, fun h => (hz h).elim⟩
  choose W hW using hW
  obtain ⟨O, hO⟩ : ∃ O : Set E, O = {z | ∃ t : ι → ℝ, jointFlow X t x = z} := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Set E, U = ⋃ z ∈ M ∩ O, W z := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : Set E, V = ⋃ z ∈ M \ O, W z := ⟨_, rfl⟩
  have hUopen : IsOpen U := by
    rw [hU]
    exact isOpen_biUnion fun z hz => (hW z hz.1).1
  have hVopen : IsOpen V := by
    rw [hV]
    exact isOpen_biUnion fun z hz => (hW z hz.1).1
  have hUO : ∀ w ∈ M, w ∈ U → w ∈ O := by
    intro w hw hwU
    rw [hU] at hwU
    obtain ⟨z, hz, hwz⟩ := mem_iUnion₂.mp hwU
    obtain ⟨s, hs⟩ := (hW z hz.1).2.2 w ⟨hw, hwz⟩
    have hzO := hz.2
    rw [hO] at hzO ⊢
    obtain ⟨t, ht⟩ := hzO
    exact ⟨s + t, by rw [jointFlow_add hX hc hM s t hx, ht, hs]⟩
  have hVO : ∀ w ∈ M, w ∈ V → w ∉ O := by
    intro w hw hwV hwO
    rw [hV] at hwV
    obtain ⟨z, hz, hwz⟩ := mem_iUnion₂.mp hwV
    obtain ⟨s, hs⟩ := (hW z hz.1).2.2 w ⟨hw, hwz⟩
    apply hz.2
    rw [hO] at hwO ⊢
    obtain ⟨t, ht⟩ := hwO
    refine ⟨-s + t, ?_⟩
    rw [jointFlow_add hX hc hM (-s) t hx, ht, ← hs, jointFlow_neg hX hc hM s hz.1]
  have hcover : M ⊆ U ∪ V := by
    intro z hz
    by_cases hzO : z ∈ O
    · left
      rw [hU]
      exact mem_iUnion₂.mpr ⟨z, ⟨hz, hzO⟩, (hW z hz).2.1⟩
    · right
      rw [hV]
      exact mem_iUnion₂.mpr ⟨z, ⟨hz, hzO⟩, (hW z hz).2.1⟩
  have hdisj : M ∩ (U ∩ V) = ∅ := by
    ext w
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
    rintro ⟨hw, hwU, hwV⟩
    exact hVO w hw hwV (hUO w hw hwU)
  have hxO : x ∈ O := by
    rw [hO]
    exact ⟨0, jointFlow_zero hX hM hx⟩
  rcases isPreconnected_iff_subset_of_disjoint.mp hconn U V hUopen hVopen hcover hdisj with h | h
  · have := hUO y hy (h hy)
    rw [hO] at this
    exact this
  · exact (hVO x hx (h hx) hxO).elim

/-- The periods of a point: the times `t` with `g^t x = x`. -/
def periods {x : E} (hx : x ∈ M) : AddSubgroup (ι → ℝ) where
  carrier := {t | jointFlow X t x = x}
  zero_mem' := jointFlow_zero hX hM hx
  add_mem' := fun {a b} ha hb => by
    change jointFlow X (a + b) x = x
    have ha' : jointFlow X a x = x := ha
    have hb' : jointFlow X b x = x := hb
    rw [jointFlow_add hX hc hM a b hx, hb', ha']
  neg_mem' := fun {a} ha => by
    change jointFlow X (-a) x = x
    have ha' : jointFlow X a x = x := ha
    have h := jointFlow_neg hX hc hM a hx
    rwa [ha'] at h

theorem mem_periods {x : E} (hx : x ∈ M) {t : ι → ℝ} :
    t ∈ periods hX hc hM hx ↔ jointFlow X t x = x := Iff.rfl

/-- Two times give the same point exactly when they differ by a period. -/
theorem jointFlow_eq_iff {x : E} (hx : x ∈ M) (t s : ι → ℝ) :
    jointFlow X t x = jointFlow X s x ↔ t - s ∈ periods hX hc hM hx := by
  rw [mem_periods, sub_eq_neg_add, jointFlow_add hX hc hM (-s) t hx]
  constructor
  · intro h
    rw [h, jointFlow_neg hX hc hM s hx]
  · intro h
    have h1 := congrArg (jointFlow X s) h
    rw [← jointFlow_add hX hc hM s (-s) (jointFlow_mem hM t hx), add_neg_cancel,
      jointFlow_zero hX hM (jointFlow_mem hM t hx)] at h1
    exact h1

/-- The periods are the same at all points of a connected set. -/
theorem periods_eq (hloc : IsLocallyFree X M) (hconn : IsPreconnected M) {x y : E}
    (hx : x ∈ M) (hy : y ∈ M) : periods hX hc hM hx = periods hX hc hM hy := by
  have key : ∀ {x y : E} (hx : x ∈ M) (hy : y ∈ M),
      periods hX hc hM hx ≤ periods hX hc hM hy := by
    intro x y hx hy t ht
    obtain ⟨s, hs⟩ := exists_jointFlow_eq hX hc hM hloc hconn hx hy
    rw [mem_periods] at ht ⊢
    rw [← hs, jointFlow_comm hX hc hM t s hx, ht]
  exact le_antisymm (key hx hy) (key hy hx)

/-- Zero is isolated in the periods. -/
theorem discreteTopology_periods (hloc : IsLocallyFree X M) {x : E} (hx : x ∈ M) :
    DiscreteTopology (AddSubgroup.toIntSubmodule (periods hX hc hM hx)) := by
  obtain ⟨δ, hδ, hinj⟩ := hloc.injective x hx
  rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_induced_iff]
  refine ⟨Metric.ball 0 δ, Metric.isOpen_ball, ?_⟩
  ext ⟨t, ht⟩
  simp only [mem_preimage, Metric.mem_ball, dist_zero_right, mem_singleton_iff]
  constructor
  · intro h
    exact Subtype.ext (hinj t h ht)
  · intro h
    have h0 : t = 0 := congrArg Subtype.val h
    rw [h0, norm_zero]
    exact hδ

/-- If the set is compact, every time is a time of a compact set plus a
period. -/
theorem exists_isCompact_forall_exists_sub_mem (hloc : IsLocallyFree X M)
    (hconn : IsPreconnected M) (hcomp : IsCompact M) {x : E} (hx : x ∈ M) :
    ∃ K : Set (ι → ℝ), IsCompact K ∧
      ∀ t : ι → ℝ, ∃ k ∈ K, t - k ∈ periods hX hc hM hx := by
  classical
  have hW : ∀ z : E, ∃ (W : Set E) (s : ι → ℝ), z ∈ M → IsOpen W ∧ z ∈ W ∧
      jointFlow X s x = z ∧ ∀ w ∈ M ∩ W, ∃ u : ι → ℝ, ‖u‖ < 1 ∧ jointFlow X u z = w := by
    intro z
    by_cases hz : z ∈ M
    · obtain ⟨W, hWo, hzW, hW⟩ := hloc.open_orbit z hz 1 one_pos
      obtain ⟨s, hs⟩ := exists_jointFlow_eq hX hc hM hloc hconn hx hz
      exact ⟨W, s, fun _ => ⟨hWo, hzW, hs, hW⟩⟩
    · exact ⟨∅, 0, fun h => (hz h).elim⟩
  choose W s hW using hW
  obtain ⟨b, hbM, hbfin, hbcover⟩ := hcomp.elim_finite_subcover_image
    (b := M) (c := W) (fun z hz => (hW z hz).1) fun z hz => mem_iUnion₂.mpr ⟨z, hz, (hW z hz).2.1⟩
  refine ⟨⋃ z ∈ b, Metric.closedBall (s z) 1,
    hbfin.isCompact_biUnion fun z _ => isCompact_closedBall _ _, fun t => ?_⟩
  have hw : jointFlow X t x ∈ M := jointFlow_mem hM t hx
  obtain ⟨z, hzb, hwz⟩ := mem_iUnion₂.mp (hbcover hw)
  have hz := hbM hzb
  obtain ⟨u, hu, huz⟩ := (hW z hz).2.2.2 _ ⟨hw, hwz⟩
  refine ⟨u + s z, mem_iUnion₂.mpr ⟨z, hzb, ?_⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_right]
    exact hu.le
  · rw [← jointFlow_eq_iff hX hc hM hx, jointFlow_add hX hc hM u (s z) hx, (hW z hz).2.2.1, huz]

/-- If the set is compact, the periods span the space of the times. -/
theorem span_periods_eq_top (hloc : IsLocallyFree X M) (hconn : IsPreconnected M)
    (hcomp : IsCompact M) {x : E} (hx : x ∈ M) :
    Submodule.span ℝ (periods hX hc hM hx : Set (ι → ℝ)) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hfker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  obtain ⟨K, hK, hKper⟩ := exists_isCompact_forall_exists_sub_mem hX hc hM hloc hconn hcomp hx
  have hfc : Continuous f := LinearMap.continuous_of_finiteDimensional f
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hfc.continuousOn
  have hbound : ∀ t : ι → ℝ, ‖f t‖ ≤ C := fun t => by
    obtain ⟨k, hk, hper⟩ := hKper t
    have h0 : f (t - k) = 0 := hfker (Submodule.subset_span hper)
    rw [map_sub, sub_eq_zero] at h0
    rw [h0]
    exact hC k hk
  apply hf0
  refine LinearMap.ext fun t => ?_
  by_contra hft
  have hft' : f t ≠ 0 := hft
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hbound 0)
  have h1 := hbound (((C + 1) / ‖f t‖) • t)
  rw [map_smul, smul_eq_mul, norm_mul, norm_div, norm_norm, Real.norm_eq_abs,
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hft'), abs_of_nonneg (by linarith)] at h1
  linarith

/-- The periods are the integer combinations of a basis of the space of the
times. -/
theorem exists_basis_periods (hloc : IsLocallyFree X M) (hconn : IsPreconnected M)
    (hcomp : IsCompact M) {x : E} (hx : x ∈ M) :
    ∃ b : Basis ι ℝ (ι → ℝ), Submodule.span ℤ (Set.range b) =
      AddSubgroup.toIntSubmodule (periods hX hc hM hx) := by
  classical
  have hdisc := discreteTopology_periods hX hc hM hloc hx
  have hlat : IsZLattice ℝ (AddSubgroup.toIntSubmodule (periods hX hc hM hx)) :=
    ⟨span_periods_eq_top hX hc hM hloc hconn hcomp hx⟩
  have hfin : Module.Finite ℤ (AddSubgroup.toIntSubmodule (periods hX hc hM hx)) :=
    ZLattice.module_finite ℝ _
  have hfree : Module.Free ℤ (AddSubgroup.toIntSubmodule (periods hX hc hM hx)) :=
    ZLattice.module_free ℝ _
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ
      (AddSubgroup.toIntSubmodule (periods hX hc hM hx))) = Fintype.card ι := by
    rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ, finrank_fintype_fun_eq_card]
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : Basis (Free.ChooseBasisIndex ℤ
      (AddSubgroup.toIntSubmodule (periods hX hc hM hx))) ℝ (ι → ℝ),
      b₀ = (Free.chooseBasis ℤ _).ofZLatticeBasis ℝ _ := ⟨_, rfl⟩
  refine ⟨b₀.reindex (Fintype.equivOfCardEq hcard), ?_⟩
  rw [Basis.range_reindex, hb₀, Basis.ofZLatticeBasis_span]

include hX hc hM in
/-- Angles on a compact connected set on which the joint flow is locally free.
There is a basis `b` of the times such that, for every point `x` of the set
and `t = Σᵢ θᵢ bᵢ`: the map `θ ↦ g^t x` is onto the set, two angles give the same
point exactly when they differ by integers, and the flow of `Σᵢ sᵢ Xᵢ` moves the
angles uniformly, with the velocities given by the co-ordinates of `s` in the
basis. The motion is conditionally periodic. -/
theorem exists_torus_chart (hloc : IsLocallyFree X M) (hconn : IsPreconnected M)
    (hcomp : IsCompact M) :
    ∃ b : Basis ι ℝ (ι → ℝ), ∀ x ∈ M,
      (∀ y ∈ M, ∃ θ : ι → ℝ, jointFlow X (∑ i, θ i • b i) x = y) ∧
      (∀ θ θ' : ι → ℝ, jointFlow X (∑ i, θ i • b i) x = jointFlow X (∑ i, θ' i • b i) x ↔
        ∀ i, ∃ n : ℤ, θ i - θ' i = n) ∧
      ∀ (s : ι → ℝ) (r : ℝ) (θ : ι → ℝ),
        flow (jointField X s) (r, jointFlow X (∑ i, θ i • b i) x) =
          jointFlow X (∑ i, (θ i + r * b.repr s i) • b i) x := by
  classical
  rcases M.eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
  · exact ⟨Pi.basisFun ℝ ι, fun x hx => by rw [hempty] at hx; exact hx.elim⟩
  obtain ⟨b, hb⟩ := exists_basis_periods hX hc hM hloc hconn hcomp hx₀
  refine ⟨b, fun x hx => ⟨fun y hy => ?_, fun θ θ' => ?_, fun s r θ => ?_⟩⟩
  · obtain ⟨t, ht⟩ := exists_jointFlow_eq hX hc hM hloc hconn hx hy
    exact ⟨fun i => b.repr t i, by rw [b.sum_repr t, ht]⟩
  · rw [jointFlow_eq_iff hX hc hM hx, periods_eq hX hc hM hloc hconn hx hx₀]
    have e : ∑ i, θ i • b i - ∑ i, θ' i • b i = ∑ i, (θ i - θ' i) • b i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => (sub_smul _ _ _).symm
    have hmem : ∑ i, (θ i - θ' i) • b i ∈ periods hX hc hM hx₀ ↔
        ∑ i, (θ i - θ' i) • b i ∈ Submodule.span ℤ (Set.range b) := by
      rw [hb]
      rfl
    rw [e, hmem, Basis.mem_span_iff_repr_mem ℤ b]
    refine forall_congr' fun i => ?_
    rw [Basis.repr_sum_self]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, hn.symm⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, hn.symm⟩
  · have hy : jointFlow X (∑ i, θ i • b i) x ∈ M := jointFlow_mem hM _ hx
    rw [← jointFlow_smul hX hM r s hy, ← jointFlow_add hX hc hM (r • s) _ hx]
    congr 1
    have e : r • s = ∑ i, (r * b.repr s i) • b i := by
      conv_lhs => rw [← b.sum_repr s]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => (mul_smul _ _ _).symm
    rw [e, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_smul, add_comm]

end Lattice

end ProjectAInos.SmoothGeometry.NonlinearODE
