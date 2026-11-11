module
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.Compactness.Compact

/-! # Smooth localization near a compact set

This mathematical helper lets a locally smooth Lagrangian use the established
global variational theorem without asserting smoothness at inadmissible jets.
-/
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold
namespace ProjectAInos.Variational
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A C² function on an open domain has a globally C² representative agreeing
on an open neighborhood of any compact subset of that domain. -/
theorem exists_contDiff_extension_near_compact {f : E → ℝ} {K U : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (hf : ContDiffOn ℝ 2 f U) :
    ∃ g : E → ℝ, ContDiff ℝ 2 g ∧ ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ EqOn g f V := by
  obtain ⟨φ, hzero, hone, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, E)) (n := 2) hU.isClosed_compl hK.isClosed
    (Set.disjoint_left.mpr fun _ hx hk => hx (hKU hk))
  have hφ : ContDiff ℝ 2 (φ : E → ℝ) :=
    contMDiff_iff_contDiff.mp φ.contMDiff
  let g : E → ℝ := fun x => φ x * f x
  have hg : ContDiff ℝ 2 g := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hφ.contDiffAt.mul ((hf x hx).contDiffAt (hU.mem_nhds hx))
    · have h0 : ∀ᶠ y in 𝓝 x, φ y = 0 := hzero.filter_mono (nhds_le_nhdsSet hx)
      have he : g =ᶠ[𝓝 x] fun _ => 0 := h0.mono fun y hy => by simp [g, hy]
      exact contDiffAt_const.congr_of_eventuallyEq he
  obtain ⟨V, hV, hKV, hφV⟩ := mem_nhdsSet_iff_exists.mp hone
  refine ⟨g, hg, V, hV, hKV, fun x hx => ?_⟩
  have hx1 : φ x = 1 := hφV hx
  change φ x * f x = f x
  rw [hx1, one_mul]

/-- A continuous family on a compact base stays in an open admissible region
for all sufficiently small perturbation parameters, uniformly in the base. -/
theorem eventually_mapsTo_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {K : Set X} (hK : IsCompact K) {p : ℝ × X → Y} (hp : Continuous p)
    {U : Set Y} (hU : IsOpen U) (h0 : ∀ x ∈ K, p (0, x) ∈ U) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ x ∈ K, p (ε, x) ∈ U := by
  obtain ⟨V, W, hV, _, h0V, hKW, hVW⟩ := generalized_tube_lemma
    (isCompact_singleton (x := (0 : ℝ))) hK (hU.preimage hp)
    (by rintro ⟨ε, x⟩ ⟨rfl, hx⟩; exact h0 x hx)
  exact Filter.mem_of_superset (hV.mem_nhds (h0V (mem_singleton 0)))
    fun ε hε x hx => hVW ⟨hε, hKW hx⟩

end ProjectAInos.Variational
