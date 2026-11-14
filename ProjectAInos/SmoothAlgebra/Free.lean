/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Models
public import Mathlib.Data.Fintype.EquivFin

/-!
# Free C∞-rings on arbitrary sets

The free ring consists of real-valued cylinder functions depending smoothly on
finitely many coordinates. Equality of presentations is tested on real tuples;
the finite smooth-operation laws then imply equality in every C∞-ring.
The universal property works in arbitrary target universes.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ProjectAInos.SmoothAlgebra

open SmoothRing

namespace FreeSmoothRing

variable {ι : Type*}

/-- One finite presentation of a cylinder function. -/
def IsCylinder (s : (ι → ℝ) → ℝ) : Prop :=
  ∃ (n : ℕ) (f : SmoothOperation n) (v : Fin n → ι), ∀ x, s x = f (fun i => x (v i))

def jointEquiv {k : ℕ} (n : Fin k → ℕ) : (Σ i, Fin (n i)) ≃ Fin (∑ i, n i) :=
  (Fintype.equivFin _).trans (finCongr (by simp))

def jointVariables {k : ℕ} (n : Fin k → ℕ) (v : (i : Fin k) → Fin (n i) → ι) :
    Fin (∑ i, n i) → ι := fun j =>
  v ((jointEquiv n).symm j).1 ((jointEquiv n).symm j).2

def jointOperation {k : ℕ} (g : SmoothOperation k) (n : Fin k → ℕ)
    (f : (i : Fin k) → SmoothOperation (n i)) : SmoothOperation (∑ i, n i) :=
  SmoothOperation.comp g fun i =>
    SmoothOperation.comp (f i) fun j => SmoothOperation.proj (jointEquiv n ⟨i, j⟩)

theorem jointOperation_op {A : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]
    {k : ℕ} (g : SmoothOperation k) (n : Fin k → ℕ)
    (f : (i : Fin k) → SmoothOperation (n i))
    (v : (i : Fin k) → Fin (n i) → ι) (a : ι → A) :
    op (jointOperation g n f) (fun j => a (jointVariables n v j)) =
      op g (fun i => op (f i) (fun j => a (v i j))) := by
  simp only [jointOperation, op_comp, op_proj, jointVariables]
  congr 1
  funext i
  congr 1
  funext j
  exact congrArg (fun z : Σ i, Fin (n i) => a (v z.1 z.2))
    ((jointEquiv n).symm_apply_apply ⟨i, j⟩)

theorem isCylinder_op {k : ℕ} (g : SmoothOperation k)
    (s : Fin k → (ι → ℝ) → ℝ) (hs : ∀ i, IsCylinder (s i)) :
    IsCylinder (fun x => g (fun i => s i x)) := by
  choose n f v h using hs
  refine ⟨∑ i, n i, jointOperation g n f, jointVariables n v, fun x => ?_⟩
  simpa only [real_op, h] using (jointOperation_op g n f v x).symm

/-- Cylinder functions form a real subalgebra of all functions. -/
def subalgebra (ι : Type*) : Subalgebra ℝ ((ι → ℝ) → ℝ) where
  carrier := {s | IsCylinder s}
  add_mem' {s t} hs ht := by
    change IsCylinder (fun x => s x + t x)
    simpa using isCylinder_op SmoothOperation.addition ![s, t]
      (by intro i; fin_cases i <;> assumption)
  mul_mem' {s t} hs ht := by
    change IsCylinder (fun x => s x * t x)
    simpa using isCylinder_op SmoothOperation.multiplication ![s, t]
      (by intro i; fin_cases i <;> assumption)
  algebraMap_mem' r := ⟨0, SmoothOperation.const 0 r, Fin.elim0, fun _ => rfl⟩

end FreeSmoothRing

/-- The free C∞-ring on a set of generators. -/
abbrev FreeSmoothRing (ι : Type*) := FreeSmoothRing.subalgebra ι

namespace FreeSmoothRing

variable {ι : Type*}

instance : SmoothRing (FreeSmoothRing ι) where
  op f a := ⟨fun x => f (fun i => (a i).val x), isCylinder_op f _ (fun i => (a i).property)⟩
  op_proj _ _ := rfl
  op_comp _ _ _ := rfl
  op_nullary _ _ := rfl
  op_addition _ := rfl
  op_multiplication _ := rfl

/-- The coordinate associated with a generator. -/
def generator (i : ι) : FreeSmoothRing ι :=
  ⟨fun x => x i, 1, SmoothOperation.proj 0, fun _ => i, fun _ => rfl⟩

/-- A concrete finite presentation, used only to define evaluation. -/
structure Presentation (s : FreeSmoothRing ι) where
  arity : ℕ
  operation : SmoothOperation arity
  indices : Fin arity → ι
  sound : ∀ x, s.val x = operation (fun i => x (indices i))

def presentation (s : FreeSmoothRing ι) : Presentation s :=
  Classical.choice (by
    obtain ⟨n, f, v, h⟩ := s.property
    exact ⟨⟨n, f, v, h⟩⟩)

/-- Equality of cylinder functions implies equality of their interpretation in
any C∞-ring. A common finite set removes repeated and unused coordinates. -/
theorem presentation_independent {A : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]
    {n m : ℕ} (f : SmoothOperation n) (g : SmoothOperation m)
    (v : Fin n → ι) (w : Fin m → ι)
    (h : ∀ x : ι → ℝ, f (fun i => x (v i)) = g (fun j => x (w j))) (a : ι → A) :
    op f (fun i => a (v i)) = op g (fun j => a (w j)) := by
  classical
  let S : Finset ι := Finset.univ.image v ∪ Finset.univ.image w
  have hv (i) : v i ∈ S := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hw (i) : w i ∈ S := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  let e := Fintype.equivFin S
  let vi (i : Fin n) := e ⟨v i, hv i⟩
  let wi (i : Fin m) := e ⟨w i, hw i⟩
  have heq : SmoothOperation.comp f (fun i => SmoothOperation.proj (vi i)) =
      SmoothOperation.comp g (fun i => SmoothOperation.proj (wi i)) := by
    ext t
    let x : ι → ℝ := fun j => if hj : j ∈ S then t (e ⟨j, hj⟩) else 0
    have hxv (i) : x (v i) = t (vi i) := by simp [x, vi, hv]
    have hxw (i) : x (w i) = t (wi i) := by simp [x, wi, hw]
    simpa only [SmoothOperation.comp_apply, SmoothOperation.proj_apply, hxv, hxw] using h x
  have heval := congrArg (fun F => op F (fun j => a (e.symm j).val)) heq
  simpa only [op_comp, op_proj, vi, wi, Equiv.symm_apply_apply] using heval

def liftValue {A : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]
    (a : ι → A) (s : FreeSmoothRing ι) : A :=
  op (presentation s).operation (fun i => a ((presentation s).indices i))

theorem liftValue_eq {A : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]
    (a : ι → A) (s : FreeSmoothRing ι) {n : ℕ} (f : SmoothOperation n) (v : Fin n → ι)
    (h : ∀ x, s.val x = f (fun i => x (v i))) :
    liftValue a s = op f (fun i => a (v i)) :=
  presentation_independent _ _ _ _ (fun x => ((presentation s).sound x).symm.trans (h x)) a

/-- Extend a function on generators to the free C∞-ring. -/
def lift {A : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]
    (a : ι → A) : SmoothRingHom (FreeSmoothRing ι) A where
  toFun := liftValue a
  map_op' g s := by
    let n i := (presentation (s i)).arity
    let f i := (presentation (s i)).operation
    let v i := (presentation (s i)).indices
    calc
      liftValue a (op g s) = op (jointOperation g n f) (fun j => a (jointVariables n v j)) := by
        apply liftValue_eq
        intro x
        change g (fun i => (s i).val x) = _
        simpa only [real_op, fun i => (presentation (s i)).sound x] using
          (jointOperation_op g n f v x).symm
      _ = op g (fun i => liftValue a (s i)) := jointOperation_op g n f v a

@[simp] theorem lift_generator {A : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]
    (a : ι → A) (i : ι) : lift a (generator i) = a i := by
  exact (liftValue_eq a (generator i) (SmoothOperation.proj (0 : Fin 1))
    (fun _ => i) (fun _ => rfl)).trans (op_proj _ _)

theorem presentation_eq (s : FreeSmoothRing ι) :
    s = op (presentation s).operation (fun i => generator ((presentation s).indices i)) :=
  Subtype.ext (funext (presentation s).sound)

@[ext] theorem hom_ext {A : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]
    {f g : SmoothRingHom (FreeSmoothRing ι) A}
    (h : ∀ i, f (generator i) = g (generator i)) : f = g := by
  apply SmoothRingHom.ext
  intro s
  rw [presentation_eq s, f.map_op, g.map_op]
  congr 1
  funext i
  exact h _

/-- A morphism after a substitution is the substitution of the images. -/
theorem map_lift {A B : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]
    [CommRing B] [Algebra ℝ B] [SmoothRing B] (φ : SmoothRingHom A B) (a : ι → A)
    (s : FreeSmoothRing ι) : φ (lift a s) = lift (fun i => φ (a i)) s :=
  congrArg (fun χ : SmoothRingHom (FreeSmoothRing ι) B => χ s)
    (hom_ext (f := φ.comp (lift a)) (g := lift fun i => φ (a i)) fun i => by
      rw [SmoothRingHom.comp_apply, lift_generator, lift_generator])

theorem existsUnique_lift {A : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]
    (a : ι → A) : ∃! f : SmoothRingHom (FreeSmoothRing ι) A, ∀ i, f (generator i) = a i := by
  refine ⟨lift a, lift_generator a, fun f hf => ?_⟩
  apply hom_ext
  intro i
  rw [hf, lift_generator]

end FreeSmoothRing
end ProjectAInos.SmoothAlgebra
