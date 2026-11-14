/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.TimeFunction

/-!
# The exponential, the cosine and the sine of an element of a C-infinity ring

An element `a` of a C-infinity ring has an exponential `exp a`, a cosine and a
sine, by the smooth operations of one variable. The identities `exp 0 = 1`,
`exp a · exp (−a) = 1` and `cos² a + sin² a = 1` hold because they hold
between the operations, and a vector field differentiates these elements by
the chain rule. Polar co-ordinates use them.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing

variable {A B : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]
  [CommRing B] [Algebra ℝ B] [SmoothRing B]

/-- The cosine of an element of a C-infinity ring. -/
def ringCos (a : A) : A := op TimeFunction.cos fun _ => a

/-- The sine of an element of a C-infinity ring. -/
def ringSin (a : A) : A := op TimeFunction.sin fun _ => a

/-- `cos² a + sin² a = 1`. -/
theorem ringCos_mul_ringCos_add_ringSin_mul_ringSin (a : A) :
    ringCos a * ringCos a + ringSin a * ringSin a = 1 := by
  rw [ringCos, ringSin, ← op_mul, ← op_mul, ← op_add,
    TimeFunction.cos_mul_cos_add_sin_mul_sin, op_one]

/-- A vector field differentiates the cosine by the chain rule. -/
theorem apply_ringCos (d : SmoothDerivation A A) (a : A) :
    d (ringCos a) = -(ringSin a * d a) := by
  have h : SmoothOperation.partialDeriv 0 TimeFunction.cos = -TimeFunction.sin :=
    TimeFunction.timeDerivative_cos
  rw [ringCos, SmoothDerivation.chain, Fin.sum_univ_one, h, op_neg, smul_eq_mul, neg_mul]
  rfl

/-- A vector field differentiates the sine by the chain rule. -/
theorem apply_ringSin (d : SmoothDerivation A A) (a : A) :
    d (ringSin a) = ringCos a * d a := by
  have h : SmoothOperation.partialDeriv 0 TimeFunction.sin = TimeFunction.cos :=
    TimeFunction.timeDerivative_sin
  rw [ringSin, SmoothDerivation.chain, Fin.sum_univ_one, h, smul_eq_mul]
  rfl

theorem map_ringCos (φ : SmoothRingHom A B) (a : A) : φ (ringCos a) = ringCos (φ a) :=
  φ.map_op _ _

theorem map_ringSin (φ : SmoothRingHom A B) (a : A) : φ (ringSin a) = ringSin (φ a) :=
  φ.map_op _ _

/-- `exp 0 = 1`. -/
theorem exp_zero : exp (0 : A) = 1 := by
  have h : SmoothOperation.comp SmoothOperation.exponential
      (fun _ : Fin 1 => (0 : SmoothOperation 1)) = 1 := by
    ext x
    simp
  have h2 := op_comp SmoothOperation.exponential (fun _ : Fin 1 => (0 : SmoothOperation 1))
    (fun _ : Fin 1 => (0 : A))
  rw [h, op_one] at h2
  simp only [op_zero] at h2
  rw [exp, Matrix.vec_single_eq_const]
  exact h2.symm

/-- `exp a · exp (−a) = 1`: the exponential of an element is invertible. -/
theorem exp_mul_exp_neg (a : A) : exp a * exp (-a) = 1 := by
  rw [← exp_add, add_neg_cancel, exp_zero]

/-- A vector field differentiates the exponential by the chain rule. -/
theorem apply_exp (d : SmoothDerivation A A) (a : A) : d (exp a) = exp a * d a := by
  rw [SmoothDerivation.map_exp, smul_eq_mul]

end ProjectAInos.Mechanics
