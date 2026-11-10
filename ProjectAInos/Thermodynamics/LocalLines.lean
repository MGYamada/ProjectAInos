module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Joining local entropy reference lines

Local reference representations propagate over a connected state domain when
every neighborhood contains distinguishable states. The completed state
space itself requires no topology.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace ProjectAInos.Thermodynamics

variable {X V : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [AddCommGroup V] [Module ℝ V]

/-- Locally affine-line-valued state representations share a single reference
line on a connected domain, provided they vary in every neighborhood. -/
theorem mem_affineSpan_pair_of_locally_line (f : X → V)
    (hvar : ∀ x : X, ∀ U ∈ 𝓝 x, ∃ y ∈ U, f x ≠ f y)
    (hlocal : ∀ x : X, ∃ a b : V, ∃ U : Set X,
      IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, f y ∈ line[ℝ, a, b])
    (x₀ x₁ : X) (hne : f x₀ ≠ f x₁) (x : X) :
    f x ∈ line[ℝ, f x₀, f x₁] := by
  classical
  choose a b U hopen hself hmem using hlocal
  let L : X → AffineSubspace ℝ V := fun x => line[ℝ, a x, b x]
  have hconstant : IsLocallyConstant L := by
    apply (IsLocallyConstant.iff_exists_open L).mpr
    intro u
    refine ⟨U u, hopen u, hself u, ?_⟩
    intro v hv
    have hnbhd : U u ∩ U v ∈ 𝓝 v :=
      inter_mem ((hopen u).mem_nhds hv) ((hopen v).mem_nhds (hself v))
    obtain ⟨z, hz, hvz⟩ := hvar v (U u ∩ U v) hnbhd
    have hu : line[ℝ, f v, f z] = L u :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne (hmem u v hv) (hmem u z hz.1) hvz
    have hv' : line[ℝ, f v, f z] = L v :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne (hmem v v (hself v)) (hmem v z hz.2) hvz
    exact hv'.symm.trans hu
  have h₀ : f x₀ ∈ L x₀ := hmem x₀ x₀ (hself x₀)
  have h₁ : f x₁ ∈ L x₀ := by
    rw [← hconstant.apply_eq_of_preconnectedSpace x₁ x₀]
    exact hmem x₁ x₁ (hself x₁)
  have hline : line[ℝ, f x₀, f x₁] = L x₀ :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne h₀ h₁ hne
  rw [hline, ← hconstant.apply_eq_of_preconnectedSpace x x₀]
  exact hmem x x (hself x)

end ProjectAInos.Thermodynamics
