/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Partial derivatives of smooth operations

The `i`-th partial derivative of a finite smooth operation is again a smooth
operation of the same arity. The chain rule is an identity between operations,
and second partial derivatives commute. These are ordinary calculus facts about
the concrete operations; no abstract C-infinity ring appears here.
-/

@[expose] public section

noncomputable section

open scoped ContDiff

namespace ProjectAInos.SmoothAlgebra.SmoothOperation

variable {n m : ℕ}

/-- The underlying function of a smooth operation is smooth in the ordinary sense. -/
theorem contDiff (f : SmoothOperation n) : ContDiff ℝ ∞ f := f.contMDiff.contDiff

/-- A smooth operation is differentiable at every point. -/
theorem differentiableAt (f : SmoothOperation n) (x : Fin n → ℝ) : DifferentiableAt ℝ f x :=
  (f.contDiff.differentiable (by norm_num)) x

/-- A finite sum of smooth operations is evaluated termwise. -/
@[simp] theorem sum_apply {ι : Type*} (s : Finset ι) (F : ι → SmoothOperation n)
    (x : Fin n → ℝ) : (∑ i ∈ s, F i) x = ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

/-- The `i`-th partial derivative, as a smooth operation of the same arity. -/
def partialDeriv (i : Fin n) (f : SmoothOperation n) : SmoothOperation n :=
  ofContDiff (fun x => fderiv ℝ f x (Pi.single i 1))
    ((contDiff_infty_iff_fderiv.mp f.contDiff).2.clm_apply contDiff_const)

@[simp] theorem partialDeriv_apply (i : Fin n) (f : SmoothOperation n) (x : Fin n → ℝ) :
    partialDeriv i f x = fderiv ℝ f x (Pi.single i 1) := rfl

/-- The Fréchet derivative is the combination of the partial derivatives. -/
theorem fderiv_apply_eq_sum_partialDeriv (f : SmoothOperation n) (x v : Fin n → ℝ) :
    fderiv ℝ f x v = ∑ i, v i * partialDeriv i f x := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp [map_sum]

/-- A coordinate projection has constant partial derivatives. -/
theorem partialDeriv_proj (i j : Fin n) :
    partialDeriv i (proj j) = if i = j then 1 else 0 := by
  ext x
  have h : HasFDerivAt (fun y : Fin n → ℝ => y j)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j) x :=
    hasFDerivAt_apply j x
  change fderiv ℝ (fun y : Fin n → ℝ => y j) x (Pi.single i 1) = _
  rw [h.fderiv]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, Ne.symm hij]

@[simp] theorem partialDeriv_const (i : Fin n) (r : ℝ) : partialDeriv i (const n r) = 0 := by
  ext x
  change fderiv ℝ (fun _ : Fin n → ℝ => r) x (Pi.single i 1) = 0
  simp

theorem partialDeriv_add (i : Fin n) (f g : SmoothOperation n) :
    partialDeriv i (f + g) = partialDeriv i f + partialDeriv i g := by
  ext x
  have h : HasFDerivAt (fun y => f y + g y) (fderiv ℝ f x + fderiv ℝ g x) x :=
    (f.differentiableAt x).hasFDerivAt.add (g.differentiableAt x).hasFDerivAt
  change fderiv ℝ (fun y => f y + g y) x (Pi.single i 1) = _
  rw [h.fderiv]
  rfl

/-- The Leibniz rule for partial derivatives. -/
theorem partialDeriv_mul (i : Fin n) (f g : SmoothOperation n) :
    partialDeriv i (f * g) = partialDeriv i f * g + f * partialDeriv i g := by
  ext x
  have h : HasFDerivAt (fun y => f y * g y) (f x • fderiv ℝ g x + g x • fderiv ℝ f x) x :=
    (f.differentiableAt x).hasFDerivAt.mul (g.differentiableAt x).hasFDerivAt
  change fderiv ℝ (fun y => f y * g y) x (Pi.single i 1) =
    fderiv ℝ f x (Pi.single i 1) * g x + f x * fderiv ℝ g x (Pi.single i 1)
  rw [h.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem partialDeriv_smul (i : Fin n) (r : ℝ) (f : SmoothOperation n) :
    partialDeriv i (r • f) = r • partialDeriv i f := by
  have h (g : SmoothOperation n) : r • g = const n r * g := by
    ext x
    rfl
  rw [h, h, partialDeriv_mul, partialDeriv_const, zero_mul, zero_add]

theorem partialDeriv_neg (i : Fin n) (f : SmoothOperation n) :
    partialDeriv i (-f) = -partialDeriv i f := by
  have h (g : SmoothOperation n) : -g = (-1 : ℝ) • g := by simp
  rw [h, h, partialDeriv_smul]

theorem partialDeriv_sub (i : Fin n) (f g : SmoothOperation n) :
    partialDeriv i (f - g) = partialDeriv i f - partialDeriv i g := by
  rw [sub_eq_add_neg, sub_eq_add_neg, partialDeriv_add, partialDeriv_neg]

/-- Both partial derivatives of binary addition are the constant one. -/
theorem partialDeriv_addition (i : Fin 2) : partialDeriv i addition = 1 := by
  rw [addition, partialDeriv_add, partialDeriv_proj, partialDeriv_proj]
  fin_cases i <;> simp

/-- Differentiating a product in its first argument leaves the second argument. -/
theorem partialDeriv_multiplication_zero : partialDeriv 0 multiplication = proj 1 := by
  rw [multiplication, partialDeriv_mul, partialDeriv_proj, partialDeriv_proj]
  simp

/-- Differentiating a product in its second argument leaves the first argument. -/
theorem partialDeriv_multiplication_one : partialDeriv 1 multiplication = proj 0 := by
  rw [multiplication, partialDeriv_mul, partialDeriv_proj, partialDeriv_proj]
  simp

/-- The chain rule for smooth substitution, as an identity between operations. -/
theorem partialDeriv_comp (f : SmoothOperation n) (g : Fin n → SmoothOperation m) (j : Fin m) :
    partialDeriv j (comp f g) = ∑ i, comp (partialDeriv i f) g * partialDeriv j (g i) := by
  ext x
  have hg : HasFDerivAt (fun y i => g i y)
      (ContinuousLinearMap.pi fun i => fderiv ℝ (g i) x) x :=
    hasFDerivAt_pi.mpr fun i => ((g i).differentiableAt x).hasFDerivAt
  have hf : HasFDerivAt f (fderiv ℝ f (fun i => g i x)) (fun i => g i x) :=
    (f.differentiableAt _).hasFDerivAt
  have h : HasFDerivAt (fun y => f (fun i => g i y))
      ((fderiv ℝ f (fun i => g i x)).comp
        (ContinuousLinearMap.pi fun i => fderiv ℝ (g i) x)) x := hf.comp x hg
  change fderiv ℝ (fun y => f (fun i => g i y)) x (Pi.single j 1) = _
  rw [h.fderiv, ContinuousLinearMap.comp_apply, fderiv_apply_eq_sum_partialDeriv, sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  change fderiv ℝ (g i) x (Pi.single j 1) * partialDeriv i f (fun k => g k x) =
    partialDeriv i f (fun k => g k x) * fderiv ℝ (g i) x (Pi.single j 1)
  ring

/-- Second partial derivatives of a smooth operation commute. -/
theorem partialDeriv_comm (i j : Fin n) (f : SmoothOperation n) :
    partialDeriv i (partialDeriv j f) = partialDeriv j (partialDeriv i f) := by
  ext x
  have hsymm : IsSymmSndFDerivAt ℝ f x :=
    (f.contDiff.of_le (by norm_num) : ContDiff ℝ 2 f).contDiffAt.isSymmSndFDerivAt (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((contDiff_infty_iff_fderiv.mp f.contDiff).2.differentiable (by norm_num)) x
  have key (a b : Fin n → ℝ) :
      fderiv ℝ (fun y => fderiv ℝ f y b) x a = fderiv ℝ (fderiv ℝ f) x a b := by
    rw [fderiv_clm_apply hd (differentiableAt_const b)]
    simp
  change fderiv ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) x (Pi.single i 1) =
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single j 1)
  rw [key, key]
  exact hsymm _ _

/-- The exponential operation is its own derivative: a nonpolynomial check. -/
theorem partialDeriv_exponential : partialDeriv 0 exponential = exponential := by
  ext x
  have hproj : HasFDerivAt (fun y : Fin 1 → ℝ => y 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) x :=
    hasFDerivAt_apply 0 x
  have h : HasFDerivAt (Real.exp ∘ fun y : Fin 1 → ℝ => y 0)
      (Real.exp (x 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) x :=
    (Real.hasDerivAt_exp (x 0)).comp_hasFDerivAt x hproj
  change fderiv ℝ (Real.exp ∘ fun y : Fin 1 → ℝ => y 0) x (Pi.single 0 1) = Real.exp (x 0)
  rw [h.fderiv]
  simp

end ProjectAInos.SmoothAlgebra.SmoothOperation
