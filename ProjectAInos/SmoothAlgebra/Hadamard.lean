/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Basic
public import ProjectAInos.SmoothAlgebra.ParametricIntegral
public import ProjectAInos.SmoothAlgebra.PartialDerivative
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Hadamard's lemma

For a smooth function `f` of `n` real variables there are smooth functions
`gᵢ` of `2n` variables with

`f(x) − f(y) = Σᵢ (xᵢ − yᵢ) gᵢ(x, y)`,

namely `gᵢ(x, y) = ∫₀¹ (∂ᵢ f)(y + t (x − y)) dt` (Lemma 3 of the manuscript,
interface statement (H)). In every C-infinity ring this gives

`Φ_f(a) − Φ_f(b) = Σᵢ (aᵢ − bᵢ) Φ_{gᵢ}(a, b)`,

which is the reason why an ideal of a C-infinity ring is compatible with all
smooth operations.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.SmoothAlgebra

open scoped ContDiff

namespace SmoothOperation

variable {n : ℕ}

/-- The point `y + t (x − y)` of the segment from `y` to `x`, as a function of
the pair `(x, y)`, given by its `2n` co-ordinates, and of `t`. -/
def segment (n : ℕ) (p : (Fin (n + n) → ℝ) × ℝ) : Fin n → ℝ :=
  fun j => p.1 (Fin.natAdd n j) + p.2 * (p.1 (Fin.castAdd n j) - p.1 (Fin.natAdd n j))

theorem contDiff_segment (n : ℕ) : ContDiff ℝ ∞ (segment n) := by
  refine contDiff_pi.mpr fun j => ?_
  have hx : ContDiff ℝ ∞ fun p : (Fin (n + n) → ℝ) × ℝ => p.1 (Fin.castAdd n j) :=
    contDiff_pi.mp contDiff_fst (Fin.castAdd n j)
  have hy : ContDiff ℝ ∞ fun p : (Fin (n + n) → ℝ) × ℝ => p.1 (Fin.natAdd n j) :=
    contDiff_pi.mp contDiff_fst (Fin.natAdd n j)
  exact hy.add (contDiff_snd.mul (hx.sub hy))

theorem segment_append (x y : Fin n → ℝ) (t : ℝ) :
    segment n (Fin.append x y, t) = y + t • (x - y) := by
  funext j
  simp only [segment, Fin.append_left, Fin.append_right, Pi.add_apply, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul]

/-- The functions `gᵢ(x, y) = ∫₀¹ (∂ᵢ f)(y + t (x − y)) dt` of Hadamard's
lemma. -/
def hadamard (i : Fin n) (f : SmoothOperation n) : SmoothOperation (n + n) :=
  ofContDiff (fun z => ∫ t in (0 : ℝ)..1, partialDeriv i f (segment n (z, t)))
    (contDiff_infty_parametric_intervalIntegral
      ((partialDeriv i f).contDiff.comp (contDiff_segment n)) 0 1)

theorem hadamard_apply (i : Fin n) (f : SmoothOperation n) (z : Fin (n + n) → ℝ) :
    hadamard i f z = ∫ t in (0 : ℝ)..1, partialDeriv i f (segment n (z, t)) :=
  rfl

/-- Hadamard's lemma: `f(x) − f(y) = Σᵢ (xᵢ − yᵢ) gᵢ(x, y)`. -/
theorem apply_sub_apply_eq_sum_hadamard (f : SmoothOperation n) (x y : Fin n → ℝ) :
    f x - f y = ∑ i, (x i - y i) * hadamard i f (Fin.append x y) := by
  have hγ (t : ℝ) : HasDerivAt (fun s : ℝ => y + s • (x - y)) (x - y) t := by
    have h := ((hasDerivAt_id t).smul_const (x - y)).const_add y
    simpa using h
  have hg (t : ℝ) : HasDerivAt (fun s : ℝ => f (y + s • (x - y)))
      (∑ i, (x i - y i) * partialDeriv i f (y + t • (x - y))) t := by
    have h := ((f.differentiableAt (y + t • (x - y))).hasFDerivAt).comp_hasDerivAt t (hγ t)
    simp only [fderiv_apply_eq_sum_partialDeriv, Pi.sub_apply] at h
    exact h
  have hcont (i : Fin n) : Continuous fun t : ℝ => partialDeriv i f (y + t • (x - y)) :=
    (partialDeriv i f).contDiff.continuous.comp (by fun_prop)
  have hterm (i : Fin n) : IntervalIntegrable
      (fun t : ℝ => (x i - y i) * partialDeriv i f (y + t • (x - y))) MeasureTheory.volume 0 1 :=
    (continuous_const.mul (hcont i)).intervalIntegrable 0 1
  have hint : IntervalIntegrable
      (fun t : ℝ => ∑ i, (x i - y i) * partialDeriv i f (y + t • (x - y)))
      MeasureTheory.volume 0 1 :=
    (continuous_finsetSum _ fun i _ => continuous_const.mul (hcont i)).intervalIntegrable 0 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hg t) hint
  simp only [one_smul, zero_smul, add_zero, add_sub_cancel] at hftc
  rw [← hftc, intervalIntegral.integral_finsetSum fun i _ => hterm i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_const_mul, hadamard_apply]
  simp only [segment_append]

/-- Hadamard's lemma as an identity between smooth operations of `2n`
variables. -/
theorem comp_castAdd_sub_comp_natAdd (f : SmoothOperation n) :
    comp f (fun j => proj (Fin.castAdd n j)) - comp f (fun j => proj (Fin.natAdd n j)) =
      ∑ i, (proj (Fin.castAdd n i) - proj (Fin.natAdd n i)) * hadamard i f := by
  ext z
  have h := apply_sub_apply_eq_sum_hadamard f (fun j => z (Fin.castAdd n j))
    (fun j => z (Fin.natAdd n j))
  rw [Fin.append_castAdd_natAdd] at h
  rw [sum_apply]
  exact h

end SmoothOperation

namespace SmoothRing

open SmoothOperation

variable {A : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A] {n : ℕ}

/-- Hadamard's lemma in a C-infinity ring:
`Φ_f(a) − Φ_f(b) = Σᵢ (aᵢ − bᵢ) Φ_{gᵢ}(a, b)`. -/
theorem op_sub_op (f : SmoothOperation n) (a b : Fin n → A) :
    op f a - op f b = ∑ i, (a i - b i) * op (hadamard i f) (Fin.append a b) := by
  have h := congrArg (fun g => op g (Fin.append a b)) (comp_castAdd_sub_comp_natAdd f)
  simp only [op_sub, op_comp, op_proj, op_sum, op_mul, Fin.append_left, Fin.append_right] at h
  exact h

end SmoothRing

end ProjectAInos.SmoothAlgebra
