module

public import ProjectAInos.Thermodynamics.SimpleSystem

/-!
# Geometry of the boundary of a simple-system forward sector

Supports at relative boundary points inherit the prescribed pressure plane.
The projection of the interior onto work coordinates contains the anchor's
work coordinate; this is the local vertical-interior fact needed for the
orientation and energy-range theorems.
-/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace ProjectAInos.Thermodynamics.Physical

/-- A nonzero supporting functional is strictly below its supporting value
at every interior point. -/
theorem SupportsAt.lt_of_mem_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C : Set E} {x : E} {f : E →ₗ[ℝ] ℝ} (hf : SupportsAt C x f)
    {y : E} (hy : y ∈ interior C) : f y < f x := by
  let g : E →L[ℝ] ℝ := f.toContinuousLinearMap
  have hg : g ≠ 0 := by
    intro hz
    exact hf.1 (congrArg ContinuousLinearMap.toLinearMap hz)
  have hopen : IsOpen (f '' interior C) := g.isOpenMap_of_ne_zero hg _ isOpen_interior
  have hsub : f '' interior C ⊆ Iic (f x) := by
    rintro _ ⟨z, hz, rfl⟩
    exact hf.2 z (interior_subset hz)
  have h := interior_maximal hsub hopen ⟨y, hy, rfl⟩
  simpa only [interior_Iic, mem_Iio] using h

theorem SupportsAt.not_mem_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C : Set E} {x : E} {f : E →ₗ[ℝ] ℝ} (hf : SupportsAt C x f) :
    x ∉ interior C := fun hx => (hf.lt_of_mem_interior hx).false

/-- A convex set with nonempty interior and a unique finite-slope supporting
hyperplane at `x` has an interior point with the same work coordinate as `x`. -/
theorem work_mem_projection_interior {n : ℕ}
    {C : Set (SimpleCoordinates n)} (hC : Convex ℝ C)
    (hinterior : (interior C).Nonempty) (x : SimpleCoordinates n)
    (p : WorkCoordinates n)
    (hunique : ∀ f : SimpleCoordinates n →ₗ[ℝ] ℝ, SupportsAt C x f →
      LinearMap.ker f = LinearMap.ker (pressureForm p)) :
    x.2 ∈ Prod.snd '' interior C := by
  by_contra hx
  have hconvex : Convex ℝ (Prod.snd '' interior C) :=
    hC.interior.linear_image (LinearMap.snd ℝ ℝ (WorkCoordinates n))
  have hopen : IsOpen (Prod.snd '' interior C) := isOpenMap_snd _ isOpen_interior
  obtain ⟨g, hg⟩ := geometric_hahn_banach_open_point hconvex hopen hx
  have hgne : g ≠ 0 := by
    obtain ⟨y, hy⟩ := hinterior
    have h := hg y.2 ⟨y, hy, rfl⟩
    intro heq
    simp [heq] at h
  let f : SimpleCoordinates n →ₗ[ℝ] ℝ :=
    g.toLinearMap.comp (LinearMap.snd ℝ ℝ (WorkCoordinates n))
  have hf : f ≠ 0 := by
    intro hfzero
    apply hgne
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun k : SimpleCoordinates n →ₗ[ℝ] ℝ => k (0, v)) hfzero
  have hclosed : IsClosed {y | f y ≤ f x} :=
    isClosed_le f.continuous_of_finiteDimensional continuous_const
  have hsub : interior C ⊆ {y | f y ≤ f x} := by
    intro y hy
    exact (hg y.2 ⟨y, hy, rfl⟩).le
  have hclosure := closure_minimal hsub hclosed
  rw [hC.closure_interior_eq_closure_of_nonempty_interior hinterior] at hclosure
  have hsupport : SupportsAt C x f :=
    ⟨hf, fun y hy => hclosure (subset_closure hy)⟩
  have hker := hunique f hsupport
  have henergy : (1, 0) ∈ LinearMap.ker f := by simp [f]
  rw [hker] at henergy
  simp at henergy

namespace SimpleSystem

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X} {n : ℕ}

/-- Forward accessibility within one equilibrium domain. -/
abbrev sector (S : SimpleSystem P n) (x : SimpleCoordinates n) : Set (SimpleCoordinates n) :=
  P.forwardSector S.domain S.represent x

/-- The boundary inside the open equilibrium domain, excluding its outer edge. -/
def boundary (S : SimpleSystem P n) (x : SimpleCoordinates n) : Set (SimpleCoordinates n) :=
  S.domain ∩ frontier (S.sector x)

theorem sector_convex (S : SimpleSystem P n) (x : SimpleCoordinates n) :
    Convex ℝ (S.sector x) :=
  P.forwardSector_convex S.domain S.represent S.convex_domain S.mixing x

theorem mem_sector_self (S : SimpleSystem P n) {x : SimpleCoordinates n}
    (hx : x ∈ S.domain) : x ∈ S.sector x := ⟨hx, P.refl _⟩

theorem sector_subset_of_mem (S : SimpleSystem P n) {x y : SimpleCoordinates n}
    (hy : y ∈ S.sector x) : S.sector y ⊆ S.sector x := by
  intro z hz
  exact ⟨hz.1, P.trans hy.2 hz.2⟩

theorem boundary_subset_sector (S : SimpleSystem P n) {x : SimpleCoordinates n}
    (hx : x ∈ S.domain) : S.boundary x ⊆ S.sector x := by
  intro y hy
  have hmem : y ∈ closure (S.sector x) ∩ S.domain :=
    ⟨frontier_subset_closure hy.2, hy.1⟩
  rw [P.forwardSector_closure_inter S.domain S.represent S.isOpen_domain
    S.convex_domain S.mixing x hx] at hmem
  exact hmem

theorem self_not_mem_interior (S : SimpleSystem P n) {x : SimpleCoordinates n}
    (hx : x ∈ S.domain) : x ∉ interior (S.sector x) := by
  obtain h | h := S.pressure_support x hx
  · exact h.not_mem_interior
  · exact h.not_mem_interior

theorem mem_boundary_self (S : SimpleSystem P n) {x : SimpleCoordinates n}
    (hx : x ∈ S.domain) : x ∈ S.boundary x := by
  exact ⟨hx, (mem_frontier_iff_notMem_interior (S.mem_sector_self hx)).mpr
    (S.self_not_mem_interior hx)⟩

/-- LY 3.5(i), uniqueness part, before fixing an orientation of energy. -/
theorem support_ker_at_boundary (S : SimpleSystem P n)
    {x y : SimpleCoordinates n} (hx : x ∈ S.domain) (hy : y ∈ S.boundary x)
    (f : SimpleCoordinates n →ₗ[ℝ] ℝ) (hf : SupportsAt (S.sector x) y f) :
    LinearMap.ker f = LinearMap.ker (pressureForm (S.pressure y)) := by
  apply S.unique_support y hy.1 f
  exact ⟨hf.1, fun z hz => hf.2 z
    (S.sector_subset_of_mem (S.boundary_subset_sector hx hy) hz)⟩

/-- LY 3.5(i), existence of the supporting plane at a relative boundary point. -/
theorem exists_support_at_boundary (S : SimpleSystem P n)
    {x y : SimpleCoordinates n} (hx : x ∈ S.domain) (hy : y ∈ S.boundary x) :
    ∃ f : SimpleCoordinates n →ₗ[ℝ] ℝ,
      SupportsAt (S.sector x) y f ∧
        LinearMap.ker f = LinearMap.ker (pressureForm (S.pressure y)) := by
  have hnot : y ∉ interior (S.sector x) := hy.2.2
  obtain ⟨f, hf⟩ := exists_support_of_not_mem_interior (S.sector_convex x)
    (S.boundary_subset_sector hx hy) hnot
  exact ⟨f, hf, S.support_ker_at_boundary hx hy f hf⟩

/-- An interior point exists on the vertical line through every relative
boundary point. This does not assume a preferred orientation of energy. -/
theorem exists_interior_same_work_at_boundary (S : SimpleSystem P n)
    {x y : SimpleCoordinates n} (hx : x ∈ S.domain) (hy : y ∈ S.boundary x) :
    ∃ z ∈ interior (S.sector x), z.2 = y.2 := by
  exact work_mem_projection_interior (S.sector_convex x)
    (S.forwardSector_interior_nonempty x hx) y (S.pressure y)
    (S.support_ker_at_boundary hx hy)

/-- An interior point exists on the vertical line through the anchor. -/
theorem exists_interior_same_work (S : SimpleSystem P n)
    {x : SimpleCoordinates n} (hx : x ∈ S.domain) :
    ∃ y ∈ interior (S.sector x), y.2 = x.2 := by
  exact work_mem_projection_interior (S.sector_convex x)
    (S.forwardSector_interior_nonempty x hx) x (S.pressure x) (S.unique_support x hx)

/-- The local vertical interior is nontrivial: it contains an energy distinct
from the anchor while leaving every work coordinate fixed. -/
theorem exists_vertical_interior (S : SimpleSystem P n)
    {x : SimpleCoordinates n} (hx : x ∈ S.domain) :
    ∃ u : ℝ, (u, x.2) ∈ interior (S.sector x) ∧ u ≠ x.1 := by
  obtain ⟨y, hy, hyv⟩ := S.exists_interior_same_work hx
  have hyeq : (y.1, x.2) = y := Prod.ext rfl hyv.symm
  refine ⟨y.1, hyeq ▸ hy, ?_⟩
  intro hu
  have hyx : y = x := Prod.ext hu hyv
  exact S.self_not_mem_interior hx (hyx ▸ hy)

/-- With the work coordinate fixed, every strictly intermediate point between
the anchor and a vertical interior point lies in the sector's interior. -/
theorem vertical_between_mem_interior (S : SimpleSystem P n)
    {x : SimpleCoordinates n} (hx : x ∈ S.domain) {u : ℝ}
    (hu : (u, x.2) ∈ interior (S.sector x))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ((1 - t) * x.1 + t * u, x.2) ∈ interior (S.sector x) := by
  apply (S.sector_convex x).openSegment_self_interior_subset_interior
    (S.mem_sector_self hx) hu
  refine ⟨1 - t, t, sub_pos.mpr ht1, ht, by ring, ?_⟩
  apply Prod.ext
  · rfl
  · change (1 - t) • x.2 + t • x.2 = x.2
    rw [← add_smul]
    norm_num


end SimpleSystem

end ProjectAInos.Thermodynamics.Physical
