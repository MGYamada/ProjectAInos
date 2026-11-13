/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Models
public import ProjectAInos.SmoothAlgebra.PartialDerivative
public import Mathlib.Algebra.DualNumber
import Mathlib.Tactic.Ring

/-!
# Dual numbers over a C-infinity ring

For every C-infinity ring `A`, Mathlib's dual numbers `A[ε]` carry the smooth
operations `Φ_f(c + ε b) = Φ_f(c) + ε Σᵢ Φ_{∂ᵢf}(c) bᵢ`. The substitution law is
the chain rule for partial derivatives. The ring and real-algebra structures are
Mathlib's; no second ring instance is installed. Setting `ε = 0` and the zero
section are morphisms of C-infinity rings.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.SmoothAlgebra

open SmoothRing SmoothOperation TrivSqZeroExt

variable {A : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A] {n : ℕ}

/-- A projection has Kronecker-delta partial derivatives in every C-infinity ring. -/
theorem op_partialDeriv_proj (j i : Fin n) (a : Fin n → A) :
    op (partialDeriv j (proj i)) a = if j = i then 1 else 0 := by
  rw [partialDeriv_proj]
  split_ifs <;> simp

/-- Smooth operations on dual numbers: the infinitesimal part is the first-order
Taylor term of the operation. -/
instance instSmoothRingDualNumber : SmoothRing (DualNumber A) where
  op f c := inl (op f fun i => (c i).fst) +
    inr (∑ i, op (partialDeriv i f) (fun k => (c k).fst) * (c i).snd)
  op_proj i c := by
    apply TrivSqZeroExt.ext
    · simp
    · simp [op_partialDeriv_proj, ite_mul]
  op_comp f g c := by
    apply TrivSqZeroExt.ext
    · simp [op_comp]
    · simp only [snd_add, snd_inl, snd_inr, zero_add, fst_add, fst_inl, fst_inr, add_zero,
        partialDeriv_comp, op_sum, op_mul, op_comp, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
  op_nullary r c := by
    apply TrivSqZeroExt.ext
    · simp [TrivSqZeroExt.algebraMap_eq_inl']
    · simp [TrivSqZeroExt.algebraMap_eq_inl']
  op_addition c := by
    apply TrivSqZeroExt.ext
    · simp
    · simp [partialDeriv_addition, Fin.sum_univ_two]
  op_multiplication c := by
    apply TrivSqZeroExt.ext
    · simp
    · simp only [snd_add, snd_inl, snd_inr, zero_add, Fin.sum_univ_two,
        partialDeriv_multiplication_zero, partialDeriv_multiplication_one, op_proj,
        DualNumber.snd_mul]
      ring

namespace DualNumber

@[simp] theorem fst_op (f : SmoothOperation n) (c : Fin n → DualNumber A) :
    (op f c).fst = op f fun i => (c i).fst := by
  change (inl (op f fun i => (c i).fst) +
    inr (∑ i, op (partialDeriv i f) (fun k => (c k).fst) * (c i).snd) : DualNumber A).fst = _
  simp

@[simp] theorem snd_op (f : SmoothOperation n) (c : Fin n → DualNumber A) :
    (op f c).snd = ∑ i, op (partialDeriv i f) (fun k => (c k).fst) * (c i).snd := by
  change (inl (op f fun i => (c i).fst) +
    inr (∑ i, op (partialDeriv i f) (fun k => (c k).fst) * (c i).snd) : DualNumber A).snd = _
  simp

/-- Setting `ε = 0`: the projection of the infinitesimal thickening onto its base. -/
def fstHom : SmoothRingHom (DualNumber A) A where
  toFun x := x.fst
  map_op' f c := fst_op f c

@[simp] theorem fstHom_apply (x : DualNumber A) : fstHom x = x.fst := rfl

/-- The zero section of the infinitesimal thickening. -/
def inlHom : SmoothRingHom A (DualNumber A) where
  toFun a := inl a
  map_op' f a := by
    apply TrivSqZeroExt.ext
    · simp
    · simp

@[simp] theorem inlHom_apply (a : A) : (inlHom a : DualNumber A) = inl a := rfl

/-- The zero section is a section of the projection. -/
@[simp] theorem fstHom_comp_inlHom : (fstHom (A := A)).comp inlHom = SmoothRingHom.id A :=
  SmoothRingHom.ext fun _ => rfl

/-- The exponential of a dual number carries its derivative in the infinitesimal
part. This is a nonpolynomial consequence of the smooth structure. -/
theorem exp_inl_add_inr (a b : A) :
    exp (inl a + inr b : DualNumber A) = inl (exp a) + inr (exp a * b) := by
  apply TrivSqZeroExt.ext
  · simp [exp, Matrix.vec_single_eq_const]
  · simp [exp, partialDeriv_exponential, Matrix.vec_single_eq_const]

/-- In `ℝ[ε]`, `exp (a + ε b) = exp a + ε (exp a · b)`. -/
theorem exp_real (a b : ℝ) :
    exp (inl a + inr b : DualNumber ℝ) = inl (Real.exp a) + inr (Real.exp a * b) := by
  rw [exp_inl_add_inr, real_exp]

end DualNumber

end ProjectAInos.SmoothAlgebra
