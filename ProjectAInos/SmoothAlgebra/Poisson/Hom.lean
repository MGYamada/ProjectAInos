/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Poisson.Free

/-!
# Poisson morphisms

A morphism of C-infinity rings is a Poisson morphism when it preserves the
bracket. Out of a free C-infinity ring it is enough to preserve the brackets of
the generators, because both sides satisfy the chain rule in each argument.
Canonical transformations and momentum maps are Poisson morphisms.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.SmoothAlgebra

open SmoothRing SmoothOperation

variable {P Q R : Type*} [CommRing P] [Algebra ℝ P] [SmoothRing P]
  [CommRing Q] [Algebra ℝ Q] [SmoothRing Q] [CommRing R] [Algebra ℝ R] [SmoothRing R]

/-- `φ` preserves the bracket. -/
def IsPoissonHom (π : AlmostPoissonStructure P) (ρ : AlmostPoissonStructure Q)
    (φ : SmoothRingHom P Q) : Prop :=
  ∀ f g, φ (π.bracket f g) = ρ.bracket (φ f) (φ g)

namespace IsPoissonHom

theorem id (π : AlmostPoissonStructure P) : IsPoissonHom π π (SmoothRingHom.id P) :=
  fun _ _ => rfl

theorem comp {π : AlmostPoissonStructure P} {ρ : AlmostPoissonStructure Q}
    {σ : AlmostPoissonStructure R} {ψ : SmoothRingHom Q R} {φ : SmoothRingHom P Q}
    (hψ : IsPoissonHom ρ σ ψ) (hφ : IsPoissonHom π ρ φ) : IsPoissonHom π σ (ψ.comp φ) :=
  fun f g => by
    rw [SmoothRingHom.comp_apply, hφ, hψ]
    rfl

end IsPoissonHom

/-- A morphism out of a free C-infinity ring is a Poisson morphism if it
preserves the brackets of the generators. -/
theorem FreeSmoothRing.isPoissonHom_of_generators {κ : Type*}
    {π : AlmostPoissonStructure (FreeSmoothRing κ)} {ρ : AlmostPoissonStructure Q}
    {φ : SmoothRingHom (FreeSmoothRing κ) Q}
    (h : ∀ a b, φ (π.bracket (FreeSmoothRing.generator a) (FreeSmoothRing.generator b)) =
      ρ.bracket (φ (FreeSmoothRing.generator a)) (φ (FreeSmoothRing.generator b))) :
    IsPoissonHom π ρ φ := fun f g => by
  rw [FreeSmoothRing.presentation_eq f, FreeSmoothRing.presentation_eq g, π.bracket_op_op,
    φ.map_op, φ.map_op, ρ.bracket_op_op, φ.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [φ.map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [φ.map_mul, φ.map_mul, φ.map_op, φ.map_op, h]

end ProjectAInos.SmoothAlgebra
