/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Free
public import ProjectAInos.SmoothAlgebra.Congruence

/-!
# Localization of a C∞-ring at an arbitrary set

Adjoin one inverse for every member of the set, impose the original smooth
operations and the inverse equations, and take the generated smooth quotient.
This is Joyce's general localization, not an ordinary ring localization.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ProjectAInos.SmoothAlgebra

open SmoothRing

variable {A B : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]
  [CommRing B] [Algebra ℝ B] [SmoothRing B]

namespace SmoothLocalization

/-- Equations for the original smooth operations and the adjoined inverses. -/
inductive Relation (S : Set A) : FreeSmoothRing (A ⊕ S) → FreeSmoothRing (A ⊕ S) → Prop
  | operation {n} (f : SmoothOperation n) (a : Fin n → A) :
      Relation S (FreeSmoothRing.generator (.inl (op f a)))
        (op f (fun i => FreeSmoothRing.generator (.inl (a i))))
  | inverse (s : S) : Relation S
      (FreeSmoothRing.generator (.inl s.val) * FreeSmoothRing.generator (.inr s)) 1

def congruence (S : Set A) : SmoothRingCon (FreeSmoothRing (A ⊕ S)) :=
  SmoothRingCon.generate (Relation S)

end SmoothLocalization

/-- The C∞ localization at any set, including empty sets and sets containing zero. -/
abbrev SmoothLocalization (S : Set A) := (SmoothLocalization.congruence S).Quotient

namespace SmoothLocalization

variable (S : Set A)

/-- The canonical smooth morphism to the localization. -/
def of : SmoothRingHom A (SmoothLocalization S) where
  toFun a := (congruence S).projection (FreeSmoothRing.generator (.inl a))
  map_op' f a := by
    rw [← (congruence S).projection.map_op]
    exact ((congruence S).projection_eq_projection _ _).mpr (.of (.operation f a))

/-- The inverse adjoined for a member of the localized set. -/
def inv (s : S) : SmoothLocalization S :=
  (congruence S).projection (FreeSmoothRing.generator (.inr s))

@[simp] theorem of_mul_inv (s : S) : of S s.val * inv S s = 1 := by
  change (congruence S).projection _ * (congruence S).projection _ = 1
  rw [← (congruence S).projection.map_mul, ← (congruence S).projection.map_one]
  exact ((congruence S).projection_eq_projection _ _).mpr (.of (.inverse s))

theorem isUnit_of (s : S) : IsUnit (of S s.val) := IsUnit.of_mul_eq_one (inv S s) (of_mul_inv S s)

def freeLift (f : SmoothRingHom A B) (hf : ∀ s : S, IsUnit (f s.val)) :
    SmoothRingHom (FreeSmoothRing (A ⊕ S)) B :=
  FreeSmoothRing.lift (Sum.elim f (fun s => ↑((hf s).unit⁻¹)))

theorem freeLift_relation (f : SmoothRingHom A B) (hf : ∀ s : S, IsUnit (f s.val))
    {a b} (h : Relation S a b) : freeLift S f hf a = freeLift S f hf b := by
  cases h with
  | operation g a =>
    simp only [freeLift, FreeSmoothRing.lift_generator, Sum.elim_inl, SmoothRingHom.map_op]
  | inverse s =>
    simp only [freeLift, SmoothRingHom.map_mul, SmoothRingHom.map_one,
      FreeSmoothRing.lift_generator, Sum.elim_inl, Sum.elim_inr]
    simpa only [(hf s).unit_spec] using (hf s).unit.mul_inv

/-- Factor a smooth morphism which inverts the localized set. -/
def lift (f : SmoothRingHom A B) (hf : ∀ s : S, IsUnit (f s.val)) :
    SmoothRingHom (SmoothLocalization S) B :=
  (congruence S).lift (freeLift S f hf)
    (fun _ _ h => SmoothRingCon.generated_map _ (fun _ _ h => freeLift_relation S f hf h) h)

@[simp] theorem lift_of (f : SmoothRingHom A B) (hf : ∀ s : S, IsUnit (f s.val)) (a : A) :
    lift S f hf (of S a) = f a := by
  exact FreeSmoothRing.lift_generator (Sum.elim f (fun s : S => ↑((hf s).unit⁻¹))) (Sum.inl a)

@[simp] theorem lift_inv (f : SmoothRingHom A B) (hf : ∀ s : S, IsUnit (f s.val)) (s : S) :
    lift S f hf (inv S s) = ↑((hf s).unit⁻¹) := by
  exact FreeSmoothRing.lift_generator (Sum.elim f (fun s : S => ↑((hf s).unit⁻¹))) (Sum.inr s)

/-- A morphism out of a localization is determined by the original ring. -/
@[ext] theorem hom_ext {f g : SmoothRingHom (SmoothLocalization S) B}
    (h : ∀ a, f (of S a) = g (of S a)) : f = g := by
  apply (congruence S).hom_ext
  have heq : f.comp (congruence S).projection = g.comp (congruence S).projection := by
    apply FreeSmoothRing.hom_ext
    intro i
    cases i with
    | inl a => exact h a
    | inr s =>
      change f (inv S s) = g (inv S s)
      apply ((isUnit_of S s).map f.toAlgHom.toRingHom).mul_left_cancel
      calc
        f (of S s.val) * f (inv S s) = 1 := by rw [← f.map_mul, of_mul_inv, f.map_one]
        _ = g (of S s.val) * g (inv S s) := by rw [← g.map_mul, of_mul_inv, g.map_one]
        _ = f (of S s.val) * g (inv S s) := by rw [h]
  exact fun a => congrArg (fun k : SmoothRingHom (FreeSmoothRing (A ⊕ S)) B => k a) heq

/-- Existence and uniqueness in the category of C∞-rings. -/
theorem existsUnique_lift (f : SmoothRingHom A B) (hf : ∀ s : S, IsUnit (f s.val)) :
    ∃! g : SmoothRingHom (SmoothLocalization S) B, g.comp (of S) = f := by
  refine ⟨lift S f hf, ?_, fun g hg => ?_⟩
  · ext a
    exact lift_of S f hf a
  · apply hom_ext
    intro a
    rw [lift_of]
    exact congrArg (fun k : SmoothRingHom A B => k a) hg

/-- Every element is a finite smooth expression in original elements and inverses. -/
theorem induction_on {P : SmoothLocalization S → Prop} (z : SmoothLocalization S)
    (hOf : ∀ a, P (of S a)) (hInv : ∀ s, P (inv S s))
    (hOp : ∀ {n} (f : SmoothOperation n) (a : Fin n → SmoothLocalization S),
      (∀ i, P (a i)) → P (op f a)) : P z := by
  obtain ⟨a, rfl⟩ := (congruence S).projection_surjective z
  rw [FreeSmoothRing.presentation_eq a, (congruence S).projection.map_op]
  apply hOp
  intro i
  cases (FreeSmoothRing.presentation a).indices i with
  | inl a => exact hOf a
  | inr s => exact hInv s

end SmoothLocalization
end ProjectAInos.SmoothAlgebra
