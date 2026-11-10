module

public import ProjectAInos.Thermodynamics.EnergyOrientation
public import Mathlib.Analysis.Convex.Continuous

/-!
# Forward-sector boundaries as energy graphs

After the common positive-energy orientation has been chosen, the prescribed
pressure plane supports a sector at every relative boundary point. This gives
uniqueness of energy at fixed work coordinates and the open graph domain.
-/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace ProjectAInos.Thermodynamics.Physical

/-- A linear form with the normalized pressure kernel is determined by its
value on the energy unit vector. -/
theorem apply_eq_energy_mul_of_ker_eq {n : ℕ}
    (f : SimpleCoordinates n →ₗ[ℝ] ℝ) (p : WorkCoordinates n)
    (hker : LinearMap.ker f = LinearMap.ker (pressureForm p))
    (v : SimpleCoordinates n) : f v = f (1, 0) * pressureForm p v := by
  have hn : pressureForm p (v - pressureForm p v • (1, 0)) = 0 := by
    simp only [map_sub, map_smul, pressureForm_energy, smul_eq_mul, mul_one, sub_self]
  have hf : f (v - pressureForm p v • (1, 0)) = 0 := by
    have hm : v - pressureForm p v • (1, 0) ∈ LinearMap.ker (pressureForm p) := hn
    rw [← hker] at hm
    exact hm
  simp only [map_sub, map_smul, smul_eq_mul] at hf
  nlinarith

/-- A connected set meeting a set and its complement meets its boundary. -/
theorem exists_mem_frontier_of_isPreconnected
    {E : Type*} [TopologicalSpace E] {K C : Set E} (hK : IsPreconnected K)
    {a b : E} (ha : a ∈ K) (haC : a ∈ C) (hb : b ∈ K) (hbC : b ∉ C) :
    (K ∩ frontier C).Nonempty := by
  by_contra hnot
  have havoid : ∀ x ∈ K, x ∉ frontier C := by
    intro x hx hxf
    exact hnot ⟨x, hx, hxf⟩
  have haint : a ∈ interior C := by
    by_contra h
    exact havoid a ha ⟨subset_closure haC, h⟩
  have hbext : b ∈ (closure C)ᶜ := by
    intro hbc
    exact havoid b hb ⟨hbc, fun hbi => hbC (interior_subset hbi)⟩
  have hcover : K ⊆ interior C ∪ (closure C)ᶜ := by
    intro x hx
    by_cases hi : x ∈ interior C
    · exact Or.inl hi
    · exact Or.inr (fun hc => havoid x hx ⟨hc, hi⟩)
  have hdisjoint : Disjoint (interior C) ((closure C)ᶜ) := by
    apply Set.disjoint_left.mpr
    exact fun x hi he => he (interior_subset_closure hi)
  have hsub := hK.subset_left_of_subset_union isOpen_interior
    isClosed_closure.isOpen_compl hdisjoint hcover ⟨a, ha, haint⟩
  exact hbext (interior_subset_closure (hsub hb))

namespace SimpleSystem

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X} {n : ℕ}

/-- The pressure support at a relative boundary point has the positive
orientation inherited from the simple system. -/
theorem pressure_support_at_boundary (S : SimpleSystem P n)
    (hpositive : ∀ z ∈ S.domain, S.Positive z)
    {x y : SimpleCoordinates n} (hx : x ∈ S.domain) (hy : y ∈ S.boundary x) :
    SupportsAt (S.sector x) y (-pressureForm (S.pressure y)) := by
  obtain ⟨f, hf, hker⟩ := S.exists_support_at_boundary hx hy
  obtain ⟨z, hz, hzv⟩ := S.exists_interior_same_work hy.1
  have hzy : y.1 < z.1 := by
    simpa using HasSign.energy_lt_of_interior_same_work S one_ne_zero
      (hpositive y hy.1) hz hzv
  have hzint : z ∈ interior (S.sector x) :=
    interior_mono (S.sector_subset_of_mem (S.boundary_subset_sector hx hy)) hz
  have hcoeff : f (1, 0) < 0 := by
    have hlt := hf.lt_of_mem_interior hzint
    have heq := apply_eq_energy_mul_of_ker_eq f (S.pressure y) hker (z - y)
    have hp : pressureForm (S.pressure y) (z - y) = z.1 - y.1 := by
      simp [pressureForm, hzv]
    rw [map_sub, hp] at heq
    nlinarith
  refine ⟨neg_ne_zero.mpr (pressureForm_ne_zero _), fun w hw => ?_⟩
  have hle := hf.2 w hw
  have heq := apply_eq_energy_mul_of_ker_eq f (S.pressure y) hker (w - y)
  simp only [map_sub] at heq
  simp only [LinearMap.neg_apply]
  nlinarith

/-- Two relative boundary states with the same work coordinates coincide. -/
theorem boundary_eq_of_same_work (S : SimpleSystem P n)
    (hpositive : ∀ z ∈ S.domain, S.Positive z)
    {x y z : SimpleCoordinates n} (hx : x ∈ S.domain)
    (hy : y ∈ S.boundary x) (hz : z ∈ S.boundary x) (hv : y.2 = z.2) : y = z := by
  have h₁ := (S.pressure_support_at_boundary hpositive hx hy).2 z
    (S.boundary_subset_sector hx hz)
  have h₂ := (S.pressure_support_at_boundary hpositive hx hz).2 y
    (S.boundary_subset_sector hx hy)
  simp only [LinearMap.neg_apply, pressureForm, LinearMap.coe_mk, AddHom.coe_mk] at h₁ h₂
  apply Prod.ext
  · simp only [hv] at h₁ h₂
    linarith
  · exact hv

/-- The work coordinates over which the relative boundary is a graph. -/
def boundaryDomain (S : SimpleSystem P n) (x : SimpleCoordinates n) : Set (WorkCoordinates n) :=
  Prod.snd '' S.boundary x

theorem boundaryDomain_isPathConnected (S : SimpleSystem P n)
    {x : SimpleCoordinates n} (hx : x ∈ S.domain) :
    IsPathConnected (S.boundaryDomain x) :=
  (S.boundary_pathConnected x hx).image continuous_snd

/-- A vertical segment within the equilibrium domain that passes from outside
the sector to inside it meets the relative boundary at the same work coordinate. -/
theorem exists_boundary_on_vertical_segment (S : SimpleSystem P n)
    {x : SimpleCoordinates n} {v : WorkCoordinates n} {a b : ℝ}
    (ha : (a, v) ∈ S.domain) (hb : (b, v) ∈ S.domain)
    (haout : (a, v) ∉ S.sector x) (hbin : (b, v) ∈ S.sector x) :
    v ∈ S.boundaryDomain x := by
  obtain ⟨z, hzseg, hzf⟩ := exists_mem_frontier_of_isPreconnected
    (convex_segment (𝕜 := ℝ) (a, v) (b, v)).isPreconnected
    (right_mem_segment ℝ (a, v) (b, v)) hbin
    (left_mem_segment ℝ (a, v) (b, v)) haout
  have hzdom : z ∈ S.domain := S.convex_domain.segment_subset ha hb hzseg
  refine ⟨z, ⟨hzdom, hzf⟩, ?_⟩
  obtain ⟨c, d, _, _, hcd, rfl⟩ := hzseg
  change c • v + d • v = v
  rw [← add_smul, hcd, one_smul]

/-- The work-coordinate projection of a relative boundary is open (LY 3.5(ii)). -/
theorem boundaryDomain_isOpen (S : SimpleSystem P n)
    (hpositive : ∀ z ∈ S.domain, S.Positive z)
    {x : SimpleCoordinates n} (hx : x ∈ S.domain) :
    IsOpen (S.boundaryDomain x) := by
  rw [isOpen_iff_mem_nhds]
  rintro v ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hzv⟩ := S.exists_interior_same_work_at_boundary hx hy
  have hlim : Tendsto (fun t : ℝ => (y.1 - t, y.2)) (𝓝 0) (𝓝 y) := by
    have hc : Continuous (fun t : ℝ => (y.1 - t, y.2)) :=
      (continuous_const.sub continuous_id).prodMk continuous_const
    simpa using hc.tendsto (0 : ℝ)
  obtain ⟨t, ht, htdom⟩ := (hlim.eventually_mem (S.isOpen_domain.mem_nhds hy.1)).exists_gt
  let a := y.1 - t
  let N := pressureForm (S.pressure y)
  let W : Set (WorkCoordinates n) :=
    {w | (a, w) ∈ S.domain} ∩ {w | (z.1, w) ∈ interior (S.sector x)} ∩
      {w | N (a, w) < N y}
  have hW : IsOpen W := by
    apply IsOpen.inter
    · apply IsOpen.inter
      · exact S.isOpen_domain.preimage (continuous_const.prodMk continuous_id)
      · exact isOpen_interior.preimage (continuous_const.prodMk continuous_id)
    · exact isOpen_lt
        (N.continuous_of_finiteDimensional.comp (continuous_const.prodMk continuous_id))
        continuous_const
  have hyW : y.2 ∈ W := by
    refine ⟨⟨htdom, ?_⟩, ?_⟩
    · change (z.1, y.2) ∈ interior (S.sector x)
      simpa only [← hzv, Prod.eta] using hz
    · change pressureForm (S.pressure y) (y.1 - t, y.2) < pressureForm (S.pressure y) y
      simp only [pressureForm, LinearMap.coe_mk, AddHom.coe_mk]
      linarith
  apply Filter.mem_of_superset (hW.mem_nhds hyW)
  intro w hw
  have htop := interior_subset hw.1.2
  apply S.exists_boundary_on_vertical_segment hw.1.1 htop.1 _ htop
  intro hbottom
  have hsupp := (S.pressure_support_at_boundary hpositive hx hy).2 (a, w) hbottom
  simp only [LinearMap.neg_apply] at hsupp
  exact (not_lt_of_ge (neg_le_neg_iff.mp hsupp)) hw.2

/-- The boundary energy, defined arbitrarily as zero outside its graph domain. -/
noncomputable def boundaryEnergy (S : SimpleSystem P n) (x : SimpleCoordinates n)
    (v : WorkCoordinates n) : ℝ := by
  classical
  exact if h : v ∈ S.boundaryDomain x then (Classical.choose h).1 else 0

theorem boundaryEnergy_mem (S : SimpleSystem P n) {x : SimpleCoordinates n}
    {v : WorkCoordinates n} (hv : v ∈ S.boundaryDomain x) :
    (S.boundaryEnergy x v, v) ∈ S.boundary x := by
  rw [boundaryEnergy, dite_eq_left hv]
  have h := Classical.choose_spec hv
  have heq : ((Classical.choose hv).1, v) = Classical.choose hv := Prod.ext rfl h.2.symm
  exact heq.symm ▸ h.1

theorem boundaryEnergy_eq_of_mem (S : SimpleSystem P n)
    (hpositive : ∀ z ∈ S.domain, S.Positive z)
    {x y : SimpleCoordinates n} (hx : x ∈ S.domain) (hy : y ∈ S.boundary x) :
    S.boundaryEnergy x y.2 = y.1 := by
  have hv : y.2 ∈ S.boundaryDomain x := ⟨y, hy, rfl⟩
  exact congrArg Prod.fst
    (S.boundary_eq_of_same_work hpositive hx (S.boundaryEnergy_mem hv) hy rfl)

/-- Local convexity of the boundary graph, stated on every convex subset of
its possibly nonconvex work-coordinate domain (LY 3.5(iii)). -/
theorem boundaryEnergy_convexOn (S : SimpleSystem P n)
    (hpositive : ∀ z ∈ S.domain, S.Positive z)
    {x : SimpleCoordinates n} (hx : x ∈ S.domain)
    {D : Set (WorkCoordinates n)} (hD : Convex ℝ D) (hsub : D ⊆ S.boundaryDomain x) :
    ConvexOn ℝ D (S.boundaryEnergy x) := by
  refine ⟨hD, ?_⟩
  intro v hv w hw a b ha hb hab
  have hvb := S.boundaryEnergy_mem (hsub hv)
  have hwb := S.boundaryEnergy_mem (hsub hw)
  have hqb := S.boundaryEnergy_mem (hsub (hD hv hw ha hb hab))
  have hcombo := S.sector_convex x (S.boundary_subset_sector hx hvb)
    (S.boundary_subset_sector hx hwb) ha hb hab
  have hineq := (S.pressure_support_at_boundary hpositive hx hqb).2 _ hcombo
  simp only [LinearMap.neg_apply, pressureForm, LinearMap.coe_mk, AddHom.coe_mk,
    Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hineq ⊢
  linarith

/-- The boundary energy is locally Lipschitz on its open graph domain. -/
theorem boundaryEnergy_locallyLipschitzOn (S : SimpleSystem P n)
    (hpositive : ∀ z ∈ S.domain, S.Positive z)
    {x : SimpleCoordinates n} (hx : x ∈ S.domain) :
    LocallyLipschitzOn (S.boundaryDomain x) (S.boundaryEnergy x) := by
  intro v hv
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (S.boundaryDomain_isOpen hpositive hx) v hv
  have hcv := S.boundaryEnergy_convexOn hpositive hx (convex_ball v r) hball
  obtain ⟨K, T, hT, hLip⟩ := hcv.locallyLipschitzOn Metric.isOpen_ball (Metric.mem_ball_self hr)
  rw [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds v hr)] at hT
  exact ⟨K, T, mem_nhdsWithin_of_mem_nhds hT, hLip⟩

theorem boundaryEnergy_continuousOn (S : SimpleSystem P n)
    (hpositive : ∀ z ∈ S.domain, S.Positive z)
    {x : SimpleCoordinates n} (hx : x ∈ S.domain) :
    ContinuousOn (S.boundaryEnergy x) (S.boundaryDomain x) :=
  (S.boundaryEnergy_locallyLipschitzOn hpositive hx).continuousOn

end SimpleSystem

end ProjectAInos.Thermodynamics.Physical
