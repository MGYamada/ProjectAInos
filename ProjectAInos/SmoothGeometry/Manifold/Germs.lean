/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Manifold.LocallyRingedSpace
public import ProjectAInos.SmoothGeometry.StructureSheaf
public import ProjectAInos.SmoothGeometry.RealSpectrumTopology
public import Mathlib.Geometry.Manifold.BumpFunction

/-! # Smooth germs and global representatives -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.Manifold

open SmoothAlgebra TopologicalSpace Filter Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- Every smooth function on an open set agrees near a given point with a
globally defined smooth function. No compactness of the manifold is required. -/
theorem exists_global_representative {U : Opens M} (f : C^∞⟮I, U; ℝ⟯) (x : U) :
    ∃ a : C^∞⟮I, M; ℝ⟯, ∀ᶠ y : U in 𝓝 x, a y = f y := by
  classical
  obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x.val).mem_iff.mp
    (U.isOpen.mem_nhds x.property)
  let g : M → ℝ := Subtype.val.extend f 0
  have hg (y : U) : g y = f y := Subtype.val_injective.extend_apply _ _ y
  have hgd (y : M) (hy : y ∈ U) : ContMDiffAt I 𝓘(ℝ) ∞ g y := by
    apply (contMDiffAt_subtype_iff (x := (⟨y, hy⟩ : U))).mp
    have heq : (fun z : U => g z) = f := funext hg
    rw [heq]
    exact f.contMDiff.contMDiffAt
  have hd : ContMDiff I 𝓘(ℝ) ∞ (fun y => b y * g y) := by
    apply contMDiff_of_tsupport
    intro y hy
    exact b.contMDiffAt.mul (hgd y (hb (tsupport_mul_subset_left hy)))
  refine ⟨⟨fun y => b y * g y, hd⟩, ?_⟩
  have hbone : ∀ᶠ y : U in 𝓝 x, b y = 1 :=
    b.eventuallyEq_one.comp_tendsto continuous_subtype_val.continuousAt
  filter_upwards [hbone] with y hy
  change b y * g y = f y
  rw [hy, one_mul, hg]

/-- Equality near a point is precisely the equality imposed by smooth point
localization on globally smooth Euclidean functions. -/
theorem euclidean_of_eq_iff {n : ℕ} (x : Fin n → ℝ) (a b : SmoothOperation n) :
    PointLocalization.of (SmoothOperation.eval x) a =
      PointLocalization.of (SmoothOperation.eval x) b ↔ a =ᶠ[𝓝 x] b := by
  constructor
  · intro h
    have hl := StructureSheaf.of_eq_locally (SmoothOperation n)
      (x := (SmoothOperation.eval x : RealSpectrum (SmoothOperation n))) h
    have hl' := (RealSpectrum.euclideanHomeomorph n).symm.continuous.tendsto x hl
    filter_upwards [hl'] with y hy
    exact congrArg (PointLocalization.residue (SmoothOperation.eval y)) hy
  · intro h
    obtain ⟨s, hs, hso, hxs⟩ := mem_nhds_iff.mp h
    obtain ⟨c, -, hc⟩ :=
      (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, Fin n → ℝ)) x).mem_iff.mp
        (hso.mem_nhds hxs)
    let c' : SmoothOperation n := ⟨c, c.contMDiff⟩
    apply (PointLocalization.of_eq_of _ _ _).mpr
    apply SmoothRingCon.Generated.of
    refine ⟨c', ?_, ?_⟩
    · change c x ≠ 0
      rw [c.eventuallyEq_one.eq_of_nhds]
      exact one_ne_zero
    apply Subtype.ext
    funext y
    change a y * c y = b y * c y
    by_cases hy : y ∈ tsupport c
    · rw [hs (hc hy)]
    · simp only [image_eq_zero_of_notMem_tsupport hy, mul_zero]

end ProjectAInos.SmoothGeometry.Manifold
