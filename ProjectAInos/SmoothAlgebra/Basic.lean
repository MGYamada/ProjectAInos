/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Operations

/-!
# C-infinity rings compatible with a real algebra

A `SmoothRing` supplies all finite smooth operations, with projection and
substitution laws. Compatibility with constants, addition and multiplication
uses the existing real algebra; it does not install a competing ring instance.
No topology or nontriviality is required on the carrier.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.SmoothAlgebra

/-- A real algebra equipped with compatible finite smooth operations.
Nullary operations are included in both the operation and substitution laws. -/
class SmoothRing (A : Type*) [CommRing A] [Algebra ℝ A] where
  /-- Interpret a smooth function on a finite tuple of elements. -/
  op : {n : ℕ} → SmoothOperation n → (Fin n → A) → A
  /-- Coordinate projections select the corresponding argument. -/
  op_proj : ∀ {n} (i : Fin n) (a : Fin n → A), op (SmoothOperation.proj i) a = a i
  /-- Interpretation respects substitution, including empty tuples. -/
  op_comp : ∀ {n m} (f : SmoothOperation n) (g : Fin n → SmoothOperation m)
    (a : Fin m → A), op (SmoothOperation.comp f g) a = op f (fun i => op (g i) a)
  /-- Nullary real constants agree with the existing algebra map. -/
  op_nullary : ∀ (r : ℝ) (a : Fin 0 → A), op (SmoothOperation.const 0 r) a = algebraMap ℝ A r
  /-- Smooth addition agrees with ring addition. -/
  op_addition : ∀ (a : Fin 2 → A), op SmoothOperation.addition a = a 0 + a 1
  /-- Smooth multiplication agrees with ring multiplication. -/
  op_multiplication : ∀ (a : Fin 2 → A), op SmoothOperation.multiplication a = a 0 * a 1

namespace SmoothRing

variable {A : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A] {n : ℕ}

attribute [simp] op_proj op_nullary op_addition op_multiplication

/-- All constant operations are forced by the nullary constants. -/
@[simp] theorem op_const (r : ℝ) (a : Fin n → A) :
    op (SmoothOperation.const n r) a = algebraMap ℝ A r := by
  have h := op_comp (SmoothOperation.const 0 r) (Fin.elim0 : Fin 0 → SmoothOperation n) a
  simpa using h

@[simp] theorem op_zero (a : Fin n → A) : op (0 : SmoothOperation n) a = 0 := by
  change op (SmoothOperation.const n 0) a = 0
  rw [op_const, map_zero]

@[simp] theorem op_one (a : Fin n → A) : op (1 : SmoothOperation n) a = 1 := by
  change op (SmoothOperation.const n 1) a = 1
  rw [op_const, map_one]

/-- Interpreting smooth operations is additive in the operation. -/
@[simp] theorem op_add (f g : SmoothOperation n) (a : Fin n → A) :
    op (f + g) a = op f a + op g a := by
  simpa using op_comp SmoothOperation.addition ![f, g] a

@[simp] theorem op_mul (f g : SmoothOperation n) (a : Fin n → A) :
    op (f * g) a = op f a * op g a := by
  simpa using op_comp SmoothOperation.multiplication ![f, g] a

@[simp] theorem op_neg (f : SmoothOperation n) (a : Fin n → A) :
    op (-f) a = -op f a := by
  apply eq_neg_of_add_eq_zero_left
  rw [← op_add, neg_add_cancel, op_zero]

@[simp] theorem op_sub (f g : SmoothOperation n) (a : Fin n → A) :
    op (f - g) a = op f a - op g a := by
  simp only [sub_eq_add_neg, op_add, op_neg]

@[simp] theorem op_smul (r : ℝ) (f : SmoothOperation n) (a : Fin n → A) :
    op (r • f) a = r • op f a := by
  have h : r • f = SmoothOperation.const n r * f := by
    ext x
    rfl
  rw [h, op_mul, op_const, Algebra.smul_def]

/-- Interpreting smooth operations commutes with finite sums of operations. -/
@[simp] theorem op_sum {ι : Type*} (s : Finset ι) (f : ι → SmoothOperation n)
    (a : Fin n → A) : op (∑ i ∈ s, f i) a = ∑ i ∈ s, op (f i) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, op_add, ih]

@[simp] theorem op_negation (a : Fin 1 → A) : op SmoothOperation.negation a = -a 0 := by
  simp [SmoothOperation.negation]

@[simp] theorem op_subtraction (a : Fin 2 → A) :
    op SmoothOperation.subtraction a = a 0 - a 1 := by
  simp [SmoothOperation.subtraction]

@[simp] theorem op_scaling (r : ℝ) (a : Fin 1 → A) :
    op (SmoothOperation.scaling r) a = r • a 0 := by
  simp [SmoothOperation.scaling]

/-- Exponentiation supplied by the unary smooth exponential operation. -/
def exp (a : A) : A := op SmoothOperation.exponential ![a]

/-- A nonpolynomial identity valid in every C-infinity ring. -/
theorem exp_add (a b : A) : exp (a + b) = exp a * exp b := by
  have h := congrArg (fun f : SmoothOperation 2 => op f ![a, b])
    SmoothOperation.exponential_addition
  simpa [op_comp, exp, Matrix.vec_single_eq_const] using h

end SmoothRing
end ProjectAInos.SmoothAlgebra
