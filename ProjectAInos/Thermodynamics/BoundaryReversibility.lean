module

public import ProjectAInos.Thermodynamics.BoundaryDifferentiability

/-!
# Global propagation of local adiabat agreement

Relative closedness and local graph agreement make the contact set of two
adiabats clopen. Boundary connectedness then propagates agreement globally.
-/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace ProjectAInos.Thermodynamics.Physical.SimpleSystem

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X} {n : ℕ}

/-- Local agreement of two boundary graphs propagates along a connected
relative boundary. This topological lemma is independent of the ODE proof of
its local-agreement premise. -/
theorem boundary_subset_of_local_agreement (S : SimpleSystem P n)
    (hpositive : ∀ z ∈ S.domain, S.Positive z)
    {x y : SimpleCoordinates n} (hx : x ∈ S.domain) (hy : y ∈ S.domain)
    (hlocal : ∀ v ∈ S.boundaryDomain x, v ∈ S.boundaryDomain y →
      S.boundaryEnergy x v = S.boundaryEnergy y v →
      S.boundaryEnergy x =ᶠ[𝓝 v] S.boundaryEnergy y)
    (hcontact : (S.boundary x ∩ S.boundary y).Nonempty) :
    S.boundary x ⊆ S.boundary y := by
  let C : Set (S.boundary x) := {z | (z : SimpleCoordinates n) ∈ S.boundary y}
  have hclosed : IsClosed C := by
    have heq : C = (fun z : S.boundary x => (z : SimpleCoordinates n)) ⁻¹'
        frontier (S.sector y) := by
      ext z
      exact ⟨fun h => h.2, fun h => ⟨z.property.1, h⟩⟩
    rw [heq]
    exact isClosed_frontier.preimage continuous_subtype_val
  have hopen : IsOpen C := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hzX : (z : SimpleCoordinates n).2 ∈ S.boundaryDomain x :=
      ⟨z, z.property, rfl⟩
    have hzY : (z : SimpleCoordinates n).2 ∈ S.boundaryDomain y := ⟨z, hz, rfl⟩
    have heq : S.boundaryEnergy x (z : SimpleCoordinates n).2 =
        S.boundaryEnergy y (z : SimpleCoordinates n).2 := by
      rw [S.boundaryEnergy_eq_of_mem hpositive hx z.property,
        S.boundaryEnergy_eq_of_mem hpositive hy hz]
    have hc : Continuous (fun w : S.boundary x => (w : SimpleCoordinates n).2) :=
      continuous_snd.comp continuous_subtype_val
    have hn := (hc.tendsto z) (hlocal _ hzX hzY heq)
    have hd := (hc.tendsto z) ((S.boundaryDomain_isOpen hpositive hy).mem_nhds hzY)
    filter_upwards [hn, hd] with w hwEq hwDom
    have hgraph := S.boundaryEnergy_mem hwDom
    have hwU : S.boundaryEnergy y (w : SimpleCoordinates n).2 =
        (w : SimpleCoordinates n).1 := by
      rw [← hwEq]
      exact S.boundaryEnergy_eq_of_mem hpositive hx w.property
    change (w : SimpleCoordinates n) ∈ S.boundary y
    simpa only [hwU, Prod.eta] using hgraph
  have hnonempty : C.Nonempty := by
    obtain ⟨z, hzX, hzY⟩ := hcontact
    exact ⟨⟨z, hzX⟩, hzY⟩
  let : ConnectedSpace (S.boundary x) :=
    isConnected_iff_connectedSpace.mp (S.boundary_pathConnected x hx).isConnected
  have hall := (show IsClopen C from ⟨hclosed, hopen⟩).eq_univ hnonempty
  intro z hz
  have hmem : (⟨z, hz⟩ : S.boundary x) ∈ C := by rw [hall]; trivial
  exact hmem

/-- At a common boundary point, local graph uniqueness gives reversibility.
The remaining use of local uniqueness is supplied by the ODE theorem. -/
theorem boundary_reversibility_of_local_agreement (S : SimpleSystem P n)
    (hpositive : ∀ z ∈ S.domain, S.Positive z)
    {x y : SimpleCoordinates n} (hx : x ∈ S.domain) (hy : y ∈ S.boundary x)
    (hlocal : ∀ v ∈ S.boundaryDomain x, v ∈ S.boundaryDomain y →
      S.boundaryEnergy x v = S.boundaryEnergy y v →
      S.boundaryEnergy x =ᶠ[𝓝 v] S.boundaryEnergy y) :
    P.relation (S.represent y) (S.represent x) := by
  have hsub := S.boundary_subset_of_local_agreement hpositive hx hy.1 hlocal
    ⟨y, hy, S.mem_boundary_self hy.1⟩
  exact (S.boundary_subset_sector hy.1 (hsub (S.mem_boundary_self hx))).2

/-- If boundary states are reversible, every irreversible successor is an
interior point of the forward sector, and conversely. -/
theorem strict_iff_interior_of_boundary_reversibility (S : SimpleSystem P n)
    (hreversible : ∀ x ∈ S.domain, ∀ y ∈ S.boundary x,
      P.relation (S.represent y) (S.represent x))
    {x y : SimpleCoordinates n} (hx : x ∈ S.domain) (hy : y ∈ S.domain) :
    (P.relation (S.represent x) (S.represent y) ∧
      ¬ P.relation (S.represent y) (S.represent x)) ↔ y ∈ interior (S.sector x) := by
  constructor
  · rintro ⟨hxy, hyx⟩
    by_contra hi
    exact hyx (hreversible x hx y ⟨hy, subset_closure ⟨hy, hxy⟩, hi⟩)
  · intro hi
    refine ⟨(interior_subset hi).2, ?_⟩
    intro hyx
    have hsub : S.sector x ⊆ S.sector y := S.sector_subset_of_mem ⟨hx, hyx⟩
    exact S.self_not_mem_interior hy (interior_mono hsub hi)

/-- An anchor outside a sector reaches every interior point of that sector
when boundary reversibility is available. -/
theorem interior_accessible_of_not_mem_of_boundary_reversibility (S : SimpleSystem P n)
    (hreversible : ∀ x ∈ S.domain, ∀ y ∈ S.boundary x,
      P.relation (S.represent y) (S.represent x))
    {x y z : SimpleCoordinates n} (hx : x ∈ S.domain) (hy : y ∈ S.domain)
    (hyout : y ∉ S.sector x) (hz : z ∈ interior (S.sector x)) :
    P.relation (S.represent y) (S.represent z) := by
  obtain ⟨w, hwseg, hwfront⟩ := exists_mem_frontier_of_isPreconnected
    (convex_segment (𝕜 := ℝ) y z).isPreconnected
    (right_mem_segment ℝ y z) (interior_subset hz)
    (left_mem_segment ℝ y z) hyout
  have hwdom := S.convex_domain.segment_subset hy (interior_subset hz).1 hwseg
  have hwb : w ∈ S.boundary x := ⟨hwdom, hwfront⟩
  have hwz : P.relation (S.represent w) (S.represent z) :=
    P.trans (hreversible x hx w hwb) (interior_subset hz).2
  obtain ⟨a, b, ha, hb, hab, hw⟩ := hwseg
  have haPos : 0 < a := by
    by_contra h
    have ha0 : a = 0 := le_antisymm (le_of_not_gt h) ha
    have hb1 : b = 1 := by linarith
    have hwzEq : w = z := by simpa only [ha0, hb1, zero_smul, one_smul, zero_add] using hw.symm
    exact hwfront.2 (hwzEq ▸ hz)
  let aa : ℝ≥0 := ⟨a, ha⟩
  let bb : ℝ≥0 := ⟨b, hb⟩
  have hab' : aa + bb = 1 := Subtype.ext hab
  have hyw := P.collinear_accessibility S.domain S.represent S.mixing hy
    (interior_subset hz).1 (show 0 < aa from haPos) hab' hw.symm hwz
  exact P.trans hyw hwz

/-- Boundary reversibility yields the comparison hypothesis for individual
states by convex segment crossing (the comparison part of LY 3.7). -/
theorem comparison_of_boundary_reversibility (S : SimpleSystem P n)
    (hreversible : ∀ x ∈ S.domain, ∀ y ∈ S.boundary x,
      P.relation (S.represent y) (S.represent x))
    {x y : SimpleCoordinates n} (hx : x ∈ S.domain) (hy : y ∈ S.domain) :
    P.relation (S.represent x) (S.represent y) ∨
      P.relation (S.represent y) (S.represent x) := by
  by_cases hxy : P.relation (S.represent x) (S.represent y)
  · exact Or.inl hxy
  right
  have hsub : interior (S.sector x) ⊆ S.sector y := by
    intro z hz
    exact ⟨(interior_subset hz).1,
      S.interior_accessible_of_not_mem_of_boundary_reversibility hreversible hx hy
        (fun h => hxy h.2) hz⟩
  have hclosure : closure (S.sector x) ⊆ closure (S.sector y) := by
    rw [← (S.sector_convex x).closure_interior_eq_closure_of_nonempty_interior
      (S.forwardSector_interior_nonempty x hx)]
    exact closure_mono hsub
  have hxcl := hclosure (subset_closure (S.mem_sector_self hx))
  have hmem : x ∈ closure (S.sector y) ∩ S.domain := ⟨hxcl, hx⟩
  rw [P.forwardSector_closure_inter S.domain S.represent S.isOpen_domain
    S.convex_domain S.mixing y hy] at hmem
  exact hmem.2

/-- Mutual accessibility is equivalent to equality of forward sectors. -/
theorem sector_eq_iff_equivalent (S : SimpleSystem P n)
    {x y : SimpleCoordinates n} (hx : x ∈ S.domain) (hy : y ∈ S.domain) :
    S.sector x = S.sector y ↔
      P.relation (S.represent x) (S.represent y) ∧
        P.relation (S.represent y) (S.represent x) := by
  constructor
  · intro h
    constructor
    · have hm := S.mem_sector_self hy
      rw [← h] at hm
      exact hm.2
    · have hm := S.mem_sector_self hx
      rw [h] at hm
      exact hm.2
  · rintro ⟨hxy, hyx⟩
    exact Set.Subset.antisymm (S.sector_subset_of_mem ⟨hx, hyx⟩)
      (S.sector_subset_of_mem ⟨hy, hxy⟩)

/-- The strict alternative in LY 3.7 is precisely containment in the interior
of the predecessor's forward sector. -/
theorem strict_iff_sector_subset_interior_of_boundary_reversibility (S : SimpleSystem P n)
    (hreversible : ∀ x ∈ S.domain, ∀ y ∈ S.boundary x,
      P.relation (S.represent y) (S.represent x))
    {x y : SimpleCoordinates n} (hx : x ∈ S.domain) (hy : y ∈ S.domain) :
    (P.relation (S.represent x) (S.represent y) ∧
      ¬ P.relation (S.represent y) (S.represent x)) ↔
      S.sector y ⊆ interior (S.sector x) := by
  constructor
  · rintro ⟨hxy, hyx⟩ z hz
    apply (S.strict_iff_interior_of_boundary_reversibility hreversible hx hz.1).mp
    exact ⟨P.trans hxy hz.2, fun hzx => hyx (P.trans hz.2 hzx)⟩
  · intro h
    exact (S.strict_iff_interior_of_boundary_reversibility hreversible hx hy).mpr
      (h (S.mem_sector_self hy))

/-- Relative openness of two-sided strict-accessibility strips. -/
theorem strict_strips_open_of_boundary_reversibility (S : SimpleSystem P n)
    (hreversible : ∀ x ∈ S.domain, ∀ y ∈ S.boundary x,
      P.relation (S.represent y) (S.represent x)) :
    ∀ a b : S.domain, IsOpen {y : S.domain |
      (P.relation (S.represent a) (S.represent y) ∧
        ¬ P.relation (S.represent y) (S.represent a)) ∧
      (P.relation (S.represent y) (S.represent b) ∧
        ¬ P.relation (S.represent b) (S.represent y))} := by
  intro a b
  have heq : {y : S.domain |
      (P.relation (S.represent a) (S.represent y) ∧
        ¬ P.relation (S.represent y) (S.represent a)) ∧
      (P.relation (S.represent y) (S.represent b) ∧
        ¬ P.relation (S.represent b) (S.represent y))} =
      (fun y : S.domain => (y : SimpleCoordinates n)) ⁻¹' interior (S.sector a) ∩
        {y : S.domain | P.relation (S.represent b) (S.represent y)}ᶜ := by
    ext y
    constructor
    · rintro ⟨hay, hyb⟩
      exact ⟨(S.strict_iff_interior_of_boundary_reversibility hreversible a.property y.property).mp hay,
        hyb.2⟩
    · rintro ⟨hyint, hnby⟩
      refine ⟨(S.strict_iff_interior_of_boundary_reversibility hreversible a.property y.property).mpr
        hyint, ?_, hnby⟩
      exact (S.comparison_of_boundary_reversibility hreversible y.property b.property).resolve_right hnby
  rw [heq]
  apply IsOpen.inter (isOpen_interior.preimage continuous_subtype_val)
  exact (P.forwardSector_isClosed_relative S.domain S.represent S.isOpen_domain
    S.convex_domain S.mixing b b.property).isOpen_compl

end ProjectAInos.Thermodynamics.Physical.SimpleSystem
