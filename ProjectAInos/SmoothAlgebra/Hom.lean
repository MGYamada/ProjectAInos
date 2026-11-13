/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Basic

/-!
# Morphisms of C-infinity rings

Preservation of all smooth operations is the only condition on the underlying
function. Preservation of the real algebra is a consequence, not a separate
assumption. No topology on the source or target ring is used.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.SmoothAlgebra

open SmoothRing

/-- A function preserving every finite smooth operation, including constants. -/
structure SmoothRingHom (A B : Type*) [CommRing A] [Algebra ℝ A] [SmoothRing A]
    [CommRing B] [Algebra ℝ B] [SmoothRing B] where
  /-- The underlying function. Use the function coercion instead. -/
  toFun : A → B
  /-- Compatibility with smooth operations. -/
  map_op' : ∀ {n} (f : SmoothOperation n) (a : Fin n → A),
    toFun (op f a) = op f (fun i => toFun (a i))

namespace SmoothRingHom

variable {A B C D : Type*}
  [CommRing A] [Algebra ℝ A] [SmoothRing A]
  [CommRing B] [Algebra ℝ B] [SmoothRing B]
  [CommRing C] [Algebra ℝ C] [SmoothRing C]
  [CommRing D] [Algebra ℝ D] [SmoothRing D]

instance : FunLike (SmoothRingHom A B) A B where
  coe := SmoothRingHom.toFun
  coe_injective f g h := by
    cases f
    cases g
    cases h
    rfl

@[ext] theorem ext {f g : SmoothRingHom A B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

@[simp] theorem map_op (h : SmoothRingHom A B) {n : ℕ} (f : SmoothOperation n)
    (a : Fin n → A) : h (op f a) = op f (fun i => h (a i)) := h.map_op' f a

@[simp] theorem map_algebraMap (h : SmoothRingHom A B) (r : ℝ) :
    h (algebraMap ℝ A r) = algebraMap ℝ B r := by
  simpa using h.map_op (SmoothOperation.const 0 r) (Fin.elim0 : Fin 0 → A)

@[simp] theorem map_zero (h : SmoothRingHom A B) : h 0 = 0 := by
  simpa using h.map_algebraMap 0

@[simp] theorem map_one (h : SmoothRingHom A B) : h 1 = 1 := by
  simpa using h.map_algebraMap 1

@[simp] theorem map_add (h : SmoothRingHom A B) (a b : A) : h (a + b) = h a + h b := by
  simpa using h.map_op SmoothOperation.addition ![a, b]

@[simp] theorem map_mul (h : SmoothRingHom A B) (a b : A) : h (a * b) = h a * h b := by
  simpa using h.map_op SmoothOperation.multiplication ![a, b]

/-- Forget the smooth operations; the real algebra laws have been derived. -/
def toAlgHom (h : SmoothRingHom A B) : A →ₐ[ℝ] B where
  toFun := h
  map_zero' := h.map_zero
  map_one' := h.map_one
  map_add' := h.map_add
  map_mul' := h.map_mul
  commutes' := h.map_algebraMap

@[simp] theorem toAlgHom_apply (h : SmoothRingHom A B) (a : A) : h.toAlgHom a = h a := rfl

theorem map_neg (h : SmoothRingHom A B) (a : A) : h (-a) = -h a :=
  _root_.map_neg h.toAlgHom a

theorem map_sub (h : SmoothRingHom A B) (a b : A) : h (a - b) = h a - h b :=
  _root_.map_sub h.toAlgHom a b

theorem map_sum {ι : Type*} (h : SmoothRingHom A B) (s : Finset ι) (f : ι → A) :
    h (∑ i ∈ s, f i) = ∑ i ∈ s, h (f i) :=
  _root_.map_sum h.toAlgHom f s

/-- Identity morphism. -/
def id (A : Type*) [CommRing A] [Algebra ℝ A] [SmoothRing A] : SmoothRingHom A A where
  toFun a := a
  map_op' _ _ := rfl

/-- Composition, with the right-hand morphism applied first. -/
def comp (g : SmoothRingHom B C) (f : SmoothRingHom A B) : SmoothRingHom A C where
  toFun a := g (f a)
  map_op' h a := by rw [f.map_op, g.map_op]

@[simp] theorem id_apply (a : A) : id A a = a := rfl
@[simp] theorem comp_apply (g : SmoothRingHom B C) (f : SmoothRingHom A B) (a : A) :
    g.comp f a = g (f a) := rfl

@[simp] theorem id_comp (f : SmoothRingHom A B) : (id B).comp f = f := rfl
@[simp] theorem comp_id (f : SmoothRingHom A B) : f.comp (id A) = f := rfl

theorem comp_assoc (h : SmoothRingHom C D) (g : SmoothRingHom B C)
    (f : SmoothRingHom A B) : (h.comp g).comp f = h.comp (g.comp f) := rfl

@[simp] theorem toAlgHom_id : (id A).toAlgHom = AlgHom.id ℝ A := rfl
@[simp] theorem toAlgHom_comp (g : SmoothRingHom B C) (f : SmoothRingHom A B) :
    (g.comp f).toAlgHom = g.toAlgHom.comp f.toAlgHom := rfl

@[simp] theorem map_exp (h : SmoothRingHom A B) (a : A) : h (exp a) = exp (h a) := by
  simp [exp, map_op, Matrix.vec_single_eq_const]

end SmoothRingHom
end ProjectAInos.SmoothAlgebra
