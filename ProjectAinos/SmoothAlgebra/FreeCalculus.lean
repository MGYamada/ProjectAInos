/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothAlgebra.FreeChainRule
public import ProjectAinos.SmoothAlgebra.Point

/-!
# The elements of a free C∞-ring as differentiable functions

An element of the free C∞-ring on finitely many generators is a function on
`κ → ℝ`. It is smooth for the normed structure of that space, and its Fréchet
derivative is the combination of its partial derivations:

`D s(z) w = Σₐ (∂ₐ s)(z) wₐ`.

A derivation `D` of the ring is a vector field on `κ → ℝ`, with the components
`D xₐ`; `realField D` is that field as a map, and its derivative is expressed
by the partial derivations of the components.
-/

@[expose] public section
noncomputable section

open scoped ContDiff

namespace ProjectAinos.SmoothAlgebra.FreeSmoothRing

open SmoothRing SmoothOperation

variable {κ : Type*} [Fintype κ]

/-- An element of the free ring is a smooth function of the co-ordinates. -/
theorem contDiff_val (s : FreeSmoothRing κ) : ContDiff ℝ ∞ (s.val : (κ → ℝ) → ℝ) := by
  have hval : (s.val : (κ → ℝ) → ℝ) =
      fun x => (presentation s).operation fun i => x ((presentation s).indices i) :=
    funext (presentation s).sound
  rw [hval]
  exact (presentation s).operation.contDiff.comp
    (contDiff_pi.mpr fun i => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ)
      ((presentation s).indices i)).contDiff)

variable [DecidableEq κ]

/-- The Fréchet derivative of an element of the free ring is the combination of
its partial derivations. -/
theorem fderiv_val_apply (s : FreeSmoothRing κ) (z w : κ → ℝ) :
    fderiv ℝ (s.val : (κ → ℝ) → ℝ) z w = ∑ a, (partialDerivation a s).val z * w a := by
  have hval : (s.val : (κ → ℝ) → ℝ) =
      fun x => (presentation s).operation fun i => x ((presentation s).indices i) :=
    funext (presentation s).sound
  have hlin : HasFDerivAt (fun x : κ → ℝ => fun i => x ((presentation s).indices i))
      (ContinuousLinearMap.pi fun i =>
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) ((presentation s).indices i))
      z :=
    (ContinuousLinearMap.pi fun i =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ)
        ((presentation s).indices i)).hasFDerivAt
  have hf := ((presentation s).operation.differentiableAt _).hasFDerivAt.comp z hlin
  have hd : fderiv ℝ (s.val : (κ → ℝ) → ℝ) z w =
      fderiv ℝ (presentation s).operation (fun i => z ((presentation s).indices i))
        (fun i => w ((presentation s).indices i)) := by
    rw [hval]
    exact congrArg (fun L : (κ → ℝ) →L[ℝ] ℝ => L w) hf.fderiv
  rw [hd, fderiv_apply_eq_sum_partialDeriv]
  have hpd : ∀ a, (partialDerivation a s).val z =
      ∑ i, partialDeriv i (presentation s).operation
        (fun j => z ((presentation s).indices j)) *
          (if (presentation s).indices i = a then 1 else 0) := by
    intro a
    rw [← lift_real, lift_partialDerivation_eq_sum]
    simp only [real_op]
  simp only [hpd, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single ((presentation s).indices i)]
  · simp only [↓reduceIte, mul_one]
    ring
  · intro a _ ha
    simp only [Ne.symm ha, ↓reduceIte, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The vector field on `κ → ℝ` of a derivation of the free ring: its components
are the values of the derivation on the generators. -/
def realField (D : SmoothDerivation (FreeSmoothRing κ) (FreeSmoothRing κ)) :
    (κ → ℝ) → κ → ℝ := fun z a => (D (generator a)).val z

omit [Fintype κ] [DecidableEq κ] in
@[simp] theorem realField_apply (D : SmoothDerivation (FreeSmoothRing κ) (FreeSmoothRing κ))
    (z : κ → ℝ) (a : κ) : realField D z a = (D (generator a)).val z := rfl

omit [DecidableEq κ] in
theorem contDiff_realField (D : SmoothDerivation (FreeSmoothRing κ) (FreeSmoothRing κ)) :
    ContDiff ℝ ∞ (realField D) :=
  contDiff_pi.mpr fun a => contDiff_val (D (generator a))

/-- The derivative of the vector field of a derivation. -/
theorem fderiv_realField_apply (D : SmoothDerivation (FreeSmoothRing κ) (FreeSmoothRing κ))
    (z w : κ → ℝ) (a : κ) :
    fderiv ℝ (realField D) z w a =
      ∑ b, (partialDerivation b (D (generator a))).val z * w b := by
  have hd : DifferentiableAt ℝ (realField D) z :=
    (contDiff_realField D).differentiable (by simp) z
  have hcomp := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) a).hasFDerivAt.comp z
    hd.hasFDerivAt
  have ha : fderiv ℝ (fun y => realField D y a) z w = fderiv ℝ (realField D) z w a :=
    congrArg (fun L : (κ → ℝ) →L[ℝ] ℝ => L w) hcomp.fderiv
  rw [← ha]
  exact fderiv_val_apply (D (generator a)) z w

end ProjectAinos.SmoothAlgebra.FreeSmoothRing
