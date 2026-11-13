/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Derivation
public import ProjectAInos.SmoothAlgebra.Free

/-!
# Derivations of free C-infinity rings

A vector field on the free C-infinity ring is determined by its values on the
generators, and those values may be prescribed arbitrarily. Existence uses no
analysis: the universal property of the free ring gives a morphism into its dual
numbers, and a morphism into dual numbers lifting the identity is a derivation.
Coordinate vector fields commute, because their commutator is a derivation that
vanishes on every generator.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.SmoothAlgebra

open SmoothRing SmoothOperation

namespace FreeSmoothRing

variable {ι : Type*}

/-- The morphism into the dual numbers that moves each generator by a
prescribed infinitesimal amount. -/
def infinitesimalShift (w : ι → FreeSmoothRing ι) :
    SmoothRingHom (FreeSmoothRing ι) (DualNumber (FreeSmoothRing ι)) :=
  lift fun i => TrivSqZeroExt.inl (generator i) + TrivSqZeroExt.inr (w i)

@[simp] theorem infinitesimalShift_generator (w : ι → FreeSmoothRing ι) (i : ι) :
    infinitesimalShift w (generator i) =
      TrivSqZeroExt.inl (generator i) + TrivSqZeroExt.inr (w i) :=
  lift_generator _ i

/-- The infinitesimal shift reduces to the identity at `ε = 0`. -/
theorem fst_infinitesimalShift (w : ι → FreeSmoothRing ι) (s : FreeSmoothRing ι) :
    (infinitesimalShift w s).fst = s := by
  have h : DualNumber.fstHom.comp (infinitesimalShift w) = SmoothRingHom.id (FreeSmoothRing ι) :=
    hom_ext fun i => by
      rw [SmoothRingHom.comp_apply, infinitesimalShift_generator, DualNumber.fstHom_apply,
        SmoothRingHom.id_apply, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, add_zero]
  exact DFunLike.congr_fun h s

/-- The vector field on the free ring with prescribed values on the generators. -/
def derivation (w : ι → FreeSmoothRing ι) :
    SmoothDerivation (FreeSmoothRing ι) (FreeSmoothRing ι) :=
  SmoothDerivation.ofInfinitesimalAut (infinitesimalShift w) (fst_infinitesimalShift w)

@[simp] theorem derivation_generator (w : ι → FreeSmoothRing ι) (i : ι) :
    derivation w (generator i) = w i := by
  simp [derivation]

/-- A derivation of the free ring is determined by its values on the generators. -/
theorem derivation_ext {M : Type*} [AddCommGroup M] [Module (FreeSmoothRing ι) M]
    {d e : SmoothDerivation (FreeSmoothRing ι) M}
    (h : ∀ i, d (generator i) = e (generator i)) : d = e := by
  apply SmoothDerivation.ext
  intro s
  rw [presentation_eq s, d.chain, e.chain]
  simp only [h]

/-- Vector fields on the free ring correspond to families of values on the generators. -/
def derivationEquiv :
    SmoothDerivation (FreeSmoothRing ι) (FreeSmoothRing ι) ≃ (ι → FreeSmoothRing ι) where
  toFun d i := d (generator i)
  invFun := derivation
  left_inv _ := derivation_ext fun i => derivation_generator _ i
  right_inv w := funext fun i => derivation_generator w i

variable [DecidableEq ι]

/-- The coordinate vector field of a generator. -/
def partialDerivation (c : ι) : SmoothDerivation (FreeSmoothRing ι) (FreeSmoothRing ι) :=
  derivation fun i => if i = c then 1 else 0

theorem partialDerivation_generator (c i : ι) :
    partialDerivation c (generator i) = if i = c then 1 else 0 :=
  derivation_generator _ i

@[simp] theorem partialDerivation_generator_self (c : ι) :
    partialDerivation c (generator c) = 1 := by
  simp [partialDerivation_generator]

theorem partialDerivation_generator_of_ne {c i : ι} (h : i ≠ c) :
    partialDerivation c (generator i) = 0 := by
  simp [partialDerivation_generator, h]

/-- Coordinate vector fields of the free ring commute. -/
theorem partialDerivation_comm (c c' : ι) (s : FreeSmoothRing ι) :
    partialDerivation c (partialDerivation c' s) =
      partialDerivation c' (partialDerivation c s) := by
  have h : ⁅partialDerivation c, partialDerivation c'⁆ = 0 := derivation_ext fun i => by
    rw [SmoothDerivation.commutator_apply, partialDerivation_generator,
      partialDerivation_generator]
    split_ifs <;> simp
  have hs := DFunLike.congr_fun h s
  rw [SmoothDerivation.commutator_apply, SmoothDerivation.zero_apply] at hs
  exact sub_eq_zero.mp hs

/-- A coordinate vector field vanishes on elements presented without its generator. -/
theorem partialDerivation_op_eq_zero (c : ι) {n : ℕ} (f : SmoothOperation n) (v : Fin n → ι)
    (hc : ∀ j, v j ≠ c) : partialDerivation c (op f fun j => generator (v j)) = 0 := by
  rw [SmoothDerivation.chain]
  simp [partialDerivation_generator, hc]

/-- Every element involves finitely many generators: all but finitely many
coordinate vector fields vanish on it. -/
theorem exists_finset_partialDerivation_eq_zero (s : FreeSmoothRing ι) :
    ∃ S : Finset ι, ∀ c ∉ S, partialDerivation c s = 0 := by
  refine ⟨Finset.univ.image (presentation s).indices, fun c hc => ?_⟩
  rw [presentation_eq s]
  refine partialDerivation_op_eq_zero c _ _ fun j hj => hc ?_
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩

end FreeSmoothRing

end ProjectAInos.SmoothAlgebra
