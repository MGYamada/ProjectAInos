/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.SmoothAlgebra.FormalSeries.NormalForm
import ProjectAinos.SmoothAlgebra.FormalSeries.Scaling

/-! Typed contracts for the formal power series in `q` and `p`: the filtration
by the order and its limits, the exponential of a map that raises the order,
the Poisson bracket and the Lie transform, the homological equation of the
harmonic oscillator, the Birkhoff normal form, and the canonical scaling.
These examples use default elaborator options. -/

open ProjectAinos ProjectAinos.SmoothAlgebra.FormalSeries
open MvPowerSeries Finset
open scoped Nat

noncomputable section

section Filtration

variable {σ : Type*} {D D' : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ} {j j' m : ℕ}
  {f g : MvPowerSeries σ ℝ}
  {B : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ}

example {n : ℕ} {f : MvPowerSeries σ ℝ} :
    f ∈ orderGE σ n ↔ ∀ d : σ →₀ ℕ, d.degree < n → coeff d f = 0 :=
  mem_orderGE

example {n : ℕ} {f : MvPowerSeries σ ℝ} :
    f ∈ orderGE σ n ↔ (n : ℕ∞) ≤ f.order :=
  mem_orderGE_iff_le_order

example {m n : ℕ} (h : m ≤ n) :
    orderGE σ n ≤ orderGE σ m :=
  orderGE_anti h

example {m n : ℕ} {f : MvPowerSeries σ ℝ} (hf : f ∈ orderGE σ n)
    (h : m ≤ n) :
    f ∈ orderGE σ m :=
  mem_orderGE_of_le hf h

example (f : MvPowerSeries σ ℝ) :
    f ∈ orderGE σ 0 :=
  mem_orderGE_zero f

example {m n : ℕ} {f g : MvPowerSeries σ ℝ} (hf : f ∈ orderGE σ m)
    (hg : g ∈ orderGE σ n) :
    f * g ∈ orderGE σ (m + n) :=
  mul_mem_orderGE hf hg

example (i : σ) :
    (X i : MvPowerSeries σ ℝ) ∈ orderGE σ 1 :=
  X_mem_orderGE i

example {m : ℕ} {f : MvPowerSeries σ ℝ} (hf : f ∈ orderGE σ m) (k : ℕ) :
    f ^ k ∈ orderGE σ (k * m) :=
  pow_mem_orderGE hf k

example {n : ℕ} {f : MvPowerSeries σ ℝ} (hf : f ∈ orderGE σ n) (i : σ) :
    pderiv i f ∈ orderGE σ (n - 1) :=
  pderiv_mem_orderGE hf i

example {f : MvPowerSeries σ ℝ} (h : ∀ n, f ∈ orderGE σ n) :
    f = 0 :=
  eq_zero_of_forall_mem_orderGE h

example {f g : MvPowerSeries σ ℝ}
    (h : ∀ n, f - g ∈ orderGE σ n) :
    f = g :=
  eq_of_forall_sub_mem_orderGE h

example (s : ℕ → MvPowerSeries σ ℝ) :
    seqLimit s =
      fun d => coeff d (s (d.degree + 1)) := rfl

example (s : ℕ → MvPowerSeries σ ℝ) (d : σ →₀ ℕ) :
    coeff d (seqLimit s) = coeff d (s (d.degree + 1)) :=
  coeff_seqLimit s d

example {s : ℕ → MvPowerSeries σ ℝ} {m : ℕ}
    (h : ∀ n, s (n + 1) - s n ∈ orderGE σ (n + m)) {n N : ℕ} (hn : n ≤ N) :
    s N - s n ∈ orderGE σ (n + m) :=
  sub_mem_orderGE_of_le h hn

example {s : ℕ → MvPowerSeries σ ℝ} {m : ℕ}
    (h : ∀ n, s (n + 1) - s n ∈ orderGE σ (n + m)) (n : ℕ) :
    seqLimit s - s n ∈ orderGE σ (n + m) :=
  seqLimit_sub_mem h n

example (D : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ) (j : ℕ) :
    Raises D j ↔
      ∀ (n : ℕ) (g : MvPowerSeries σ ℝ), g ∈ orderGE σ n → D g ∈ orderGE σ (n + j) :=
  Iff.rfl

example {i : ℕ} (h : Raises D j) (hi : i ≤ j) :
    Raises D i :=
  Raises.mono h hi

example (h : Raises D j) (k : ℕ) :
    Raises (D ^ k) (k * j) :=
  Raises.pow h k

example (h : Raises D j) :
    Raises (-D) j :=
  Raises.neg h

example (D : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ) (k : ℕ) (g : MvPowerSeries σ ℝ) :
    expTerm D k g =
      ((k ! : ℝ)⁻¹) • (D ^ k) g := rfl

example (D : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ) (n : ℕ) (g : MvPowerSeries σ ℝ) :
    expPartial D n g =
      ∑ k ∈ range n, expTerm D k g := rfl

example (D : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ)
    (g : MvPowerSeries σ ℝ) :
    expTerm D 0 g = g :=
  expTerm_zero D g

example (D : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ) (n : ℕ)
    (g : MvPowerSeries σ ℝ) :
    expPartial D (n + 1) g = expPartial D n g + expTerm D n g :=
  expPartial_succ D n g

example (D : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ)
    (g : MvPowerSeries σ ℝ) :
    expPartial D 1 g = g :=
  expPartial_one D g

example (D : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ)
    (g : MvPowerSeries σ ℝ) :
    expPartial D 2 g = g + D g :=
  expPartial_two D g

example (D : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ)
    (g : MvPowerSeries σ ℝ) :
    expPartial D 3 g = g + D g + (2⁻¹ : ℝ) • D (D g) :=
  expPartial_three D g

example (hD : Raises D j) (hg : g ∈ orderGE σ m) (k : ℕ) :
    expTerm D k g ∈ orderGE σ (m + k * j) :=
  expTerm_mem hD hg k

example (hD : Raises D j) (hg : g ∈ orderGE σ m) {a b : ℕ} (h : a ≤ b) :
    expPartial D b g - expPartial D a g ∈ orderGE σ (m + a * j) :=
  expPartial_sub_mem hD hg h

example (D : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ)
    (g : MvPowerSeries σ ℝ) :
    lieExp D g = seqLimit fun n => expPartial D n g :=
  lieExp_apply D g

example (hD : Raises D j) (hj : 1 ≤ j) (hg : g ∈ orderGE σ m)
    (a : ℕ) :
    lieExp D g - expPartial D a g ∈ orderGE σ (m + a * j) :=
  lieExp_sub_expPartial_mem hD hj hg a

example (hD : Raises D j) (hj : 1 ≤ j) (hg : g ∈ orderGE σ m) :
    lieExp D g - g ∈ orderGE σ (m + j) :=
  lieExp_sub_self_mem hD hj hg

example (hD : Raises D j) (hj : 1 ≤ j) (hg : g ∈ orderGE σ m) :
    lieExp D g ∈ orderGE σ m :=
  lieExp_mem hD hj hg

example (hD : Raises D j) (hj : 1 ≤ j) (hg : g ∈ orderGE σ m) :
    lieExp D g - (g + D g) ∈ orderGE σ (m + 2 * j) :=
  lieExp_sub_add_mem hD hj hg

example (hD : Raises D j) (hj : 1 ≤ j) (hg : g ∈ orderGE σ m) :
    lieExp D g - (g + D g + (2⁻¹ : ℝ) • D (D g)) ∈ orderGE σ (m + 3 * j) :=
  lieExp_sub_three_mem hD hj hg

example (hD : Raises D j) (hj : 1 ≤ j) :
    Raises (lieExp D - LinearMap.id) j :=
  raises_lieExp_sub_id hD hj

example (hD : Raises D j) (hj : 1 ≤ j) (h : D g = 0) :
    lieExp D g = g :=
  lieExp_eq_self hD hj h

example (hD : Raises D 1) (hD' : Raises D' j') (hj' : 1 ≤ j') :
    Raises (D + D') 1 :=
  Raises.add hD hD' hj'

example (hD : Raises D 1) (hD' : Raises D' j') (hj' : 1 ≤ j')
    (hg : g ∈ orderGE σ m) (i : ℕ) :
    ((D + D') ^ (i + 1)) g - (D ^ (i + 1)) g ∈ orderGE σ (m + j' + i) :=
  pow_add_sub_pow_mem hD hD' hj' hg i

example (hD : Raises D 1) (hD' : Raises D' j') (hj' : 1 ≤ j')
    (hg : g ∈ orderGE σ m) (n : ℕ) :
    expPartial (D + D') (n + 2) g - expPartial D (n + 2) g - D' g ∈ orderGE σ (m + j' + 1) :=
  expPartial_add_sub_mem hD hD' hj' hg n

example (hD : Raises D 1) (hD' : Raises D' j') (hj' : 1 ≤ j')
    (hg : g ∈ orderGE σ m) :
    lieExp (D + D') g - lieExp D g - D' g ∈ orderGE σ (m + j' + 1) :=
  lieExp_add_sub_mem hD hD' hj' hg

example (hD : Raises D 1) (hD' : Raises D' j') (hj' : 1 ≤ j')
    (hg : g ∈ orderGE σ m) :
    lieExp (D + D') g - lieExp D g ∈ orderGE σ (m + j') :=
  lieExp_add_sub_mem' hD hD' hj' hg

example (hder : ∀ f g, D (B f g) = B (D f) g + B f (D g)) (n : ℕ)
    (f g : MvPowerSeries σ ℝ) :
    (D ^ n) (B f g) =
      ∑ ij ∈ antidiagonal n, n.choose ij.1 • B ((D ^ ij.1) f) ((D ^ ij.2) g) :=
  pow_apply_bilinear hder n f g

example (hder : ∀ f g, D (B f g) = B (D f) g + B f (D g)) (n : ℕ)
    (f g : MvPowerSeries σ ℝ) :
    expTerm D n (B f g) =
      ∑ ij ∈ antidiagonal n, B (expTerm D ij.1 f) (expTerm D ij.2 g) :=
  expTerm_bilinear hder n f g

example (hder : ∀ f g, D (B f g) = B (D f) g + B f (D g)) (N : ℕ)
    (f g : MvPowerSeries σ ℝ) :
    expPartial D N (B f g) = ∑ i ∈ range N, B (expTerm D i f) (expPartial D (N - i) g) :=
  expPartial_bilinear hder N f g

example {c : ℕ}
    (hB : ∀ (m n : ℕ) (f g : MvPowerSeries σ ℝ), f ∈ orderGE σ m → g ∈ orderGE σ n →
      B f g ∈ orderGE σ (m + n - c))
    (hD : Raises D j) (hj : 1 ≤ j) (hder : ∀ f g, D (B f g) = B (D f) g + B f (D g))
    (f g : MvPowerSeries σ ℝ) :
    lieExp D (B f g) = B (lieExp D f) (lieExp D g) :=
  lieExp_bilinear hB hD hj hder f g

example {T : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ}
    (h : Raises (T - LinearMap.id) 1) :
    Function.Bijective T :=
  bijective_of_raises_sub_id h

example (hD : Raises D j) (hj : 1 ≤ j) :
    Function.Bijective (lieExp D) :=
  bijective_lieExp hD hj

end Filtration

section Bracket

variable {j : ℕ} {F : PhaseSeries}

example : PhaseSeries = MvPowerSeries (Fin 2) ℝ := rfl

example {σ : Type*} (i k : σ) (f : MvPowerSeries σ ℝ) :
    pderiv i (pderiv k f) = pderiv k (pderiv i f) :=
  pderiv_comm i k f

example (f : PhaseSeries) :
    pderiv 1 (pderiv 0 f) = pderiv 0 (pderiv 1 f) :=
  pderiv_one_zero f

example (f g : PhaseSeries) :
    bracket f g =
      pderiv 0 f * pderiv 1 g - pderiv 1 f * pderiv 0 g := rfl

example (f : PhaseSeries) :
    bracket f f = 0 :=
  bracket_self f

example (f g : PhaseSeries) :
    bracket g f = -bracket f g :=
  bracket_swap f g

example (f g h : PhaseSeries) :
    bracket (f + g) h = bracket f h + bracket g h :=
  bracket_add_left f g h

example (f g h : PhaseSeries) :
    bracket f (g + h) = bracket f g + bracket f h :=
  bracket_add_right f g h

example (c : ℝ) (f g : PhaseSeries) :
    bracket (c • f) g = c • bracket f g :=
  bracket_smul_left c f g

example (c : ℝ) (f g : PhaseSeries) :
    bracket f (c • g) = c • bracket f g :=
  bracket_smul_right c f g

example (f g h : PhaseSeries) :
    bracket (f - g) h = bracket f h - bracket g h :=
  bracket_sub_left f g h

example (f g h : PhaseSeries) :
    bracket f (g - h) = bracket f g - bracket f h :=
  bracket_sub_right f g h

example (g : PhaseSeries) :
    bracket 0 g = 0 :=
  bracket_zero_left g

example (f : PhaseSeries) :
    bracket f 0 = 0 :=
  bracket_zero_right f

example (f g : PhaseSeries) :
    bracket f (-g) = -bracket f g :=
  bracket_neg_right f g

example :
    pderiv 0 (X 0 : PhaseSeries) = 1 :=
  pderiv_zero_X_zero

example :
    pderiv 1 (X 1 : PhaseSeries) = 1 :=
  pderiv_one_X_one

example :
    pderiv 0 (X 1 : PhaseSeries) = 0 :=
  pderiv_zero_X_one

example :
    pderiv 1 (X 0 : PhaseSeries) = 0 :=
  pderiv_one_X_zero

example (f g h : PhaseSeries) :
    bracket f (g * h) = bracket f g * h + g * bracket f h :=
  bracket_mul_right f g h

example (f g h : PhaseSeries) :
    bracket (f * g) h = bracket f h * g + f * bracket g h :=
  bracket_mul_left f g h

example (f g h : PhaseSeries) :
    bracket f (bracket g h) = bracket (bracket f g) h + bracket g (bracket f h) :=
  bracket_bracket f g h

example :
    bracket (X 0 : PhaseSeries) (X 1) = 1 :=
  bracket_X_zero_X_one

example {m n : ℕ} {f g : PhaseSeries} (hf : f ∈ orderGE (Fin 2) m)
    (hg : g ∈ orderGE (Fin 2) n) :
    bracket f g ∈ orderGE (Fin 2) (m + n - 2) :=
  bracket_mem_orderGE hf hg

example (f g : PhaseSeries) :
    bracketₗ f g = bracket f g :=
  bracketₗ_apply f g

example (F : PhaseSeries) :
    ad F =
      bracketₗ F := rfl

example (F g : PhaseSeries) :
    ad F g = bracket F g :=
  ad_apply F g

example (F G : PhaseSeries) :
    ad (F + G) = ad F + ad G :=
  ad_add F G

example {j : ℕ} {F : PhaseSeries} (hF : F ∈ orderGE (Fin 2) (j + 2)) :
    Raises (ad F) j :=
  raises_ad hF

example (hF : F ∈ orderGE (Fin 2) (j + 3)) (f g : PhaseSeries) :
    lieExp (ad F) (f * g) = lieExp (ad F) f * lieExp (ad F) g :=
  lieExp_ad_mul hF f g

example (hF : F ∈ orderGE (Fin 2) (j + 3)) (f g : PhaseSeries) :
    lieExp (ad F) (bracket f g) = bracket (lieExp (ad F) f) (lieExp (ad F) g) :=
  lieExp_ad_bracket hF f g

example (hF : F ∈ orderGE (Fin 2) (j + 3)) :
    lieExp (ad F) 1 = 1 :=
  lieExp_ad_one hF

example (F : PhaseSeries) (hF : F ∈ orderGE (Fin 2) 3) (g : PhaseSeries) :
    lieAlgEquiv F hF g = lieExp (ad F) g :=
  lieAlgEquiv_apply F hF g

end Bracket

section Homological

variable {k : ℕ} {f g : PhaseSeries}

example (a b : ℕ) :
    mono a b =
      Finsupp.single 0 a + Finsupp.single 1 b := rfl

example (a b : ℕ) :
    mono a b 0 = a :=
  mono_apply_zero a b

example (a b : ℕ) :
    mono a b 1 = b :=
  mono_apply_one a b

example (a b : ℕ) :
    (mono a b).degree = a + b :=
  degree_mono a b

example (d : Fin 2 →₀ ℕ) :
    d = mono (d 0) (d 1) :=
  eq_mono d

example (d : Fin 2 →₀ ℕ) :
    d.degree = d 0 + d 1 :=
  degree_eq_add d

example (a b : ℕ) :
    mono a b + Finsupp.single 0 1 = mono (a + 1) b :=
  mono_add_single_zero a b

example (a b : ℕ) :
    mono a b + Finsupp.single 1 1 = mono a (b + 1) :=
  mono_add_single_one a b

example (f : PhaseSeries) (a b : ℕ) :
    coeff (mono a b) (pderiv 0 f) = coeff (mono (a + 1) b) f * (a + 1) :=
  coeff_mono_pderiv_zero f a b

example (f : PhaseSeries) (a b : ℕ) :
    coeff (mono a b) (pderiv 1 f) = coeff (mono a (b + 1)) f * (b + 1) :=
  coeff_mono_pderiv_one f a b

example (f : PhaseSeries) (a b : ℕ) :
    coeff (mono (a + 1) b) (X 0 * f) = coeff (mono a b) f :=
  coeff_mono_succ_X_zero_mul f a b

example (f : PhaseSeries) (b : ℕ) :
    coeff (mono 0 b) (X 0 * f) = 0 :=
  coeff_mono_zero_X_zero_mul f b

example (f : PhaseSeries) (a b : ℕ) :
    coeff (mono a (b + 1)) (X 1 * f) = coeff (mono a b) f :=
  coeff_mono_succ_X_one_mul f a b

example (f : PhaseSeries) (a : ℕ) :
    coeff (mono a 0) (X 1 * f) = 0 :=
  coeff_mono_zero_X_one_mul f a

example :
    f ∈ homogeneous k ↔ ∀ d : Fin 2 →₀ ℕ, d.degree ≠ k → coeff d f = 0 :=
  mem_homogeneous

example :
    f ∈ homogeneous k ↔ f.IsHomogeneous k :=
  mem_homogeneous_iff_isHomogeneous

example {a b : ℕ} (hf : f ∈ homogeneous a) (hg : g ∈ homogeneous b) :
    f * g ∈ homogeneous (a + b) :=
  mul_mem_homogeneous hf hg

example :
    (1 : PhaseSeries) ∈ homogeneous 0 :=
  one_mem_homogeneous

example {a : ℕ} (hf : f ∈ homogeneous a) (n : ℕ) :
    f ^ n ∈ homogeneous (n * a) :=
  pow_mem_homogeneous hf n

example (i : Fin 2) :
    (X i : PhaseSeries) ∈ homogeneous 1 :=
  X_mem_homogeneous i

example (k : ℕ) :
    homogeneous k ≤ orderGE (Fin 2) k :=
  homogeneous_le_orderGE k

example (hf : f ∈ homogeneous (k + 1)) (i : Fin 2) :
    pderiv i f ∈ homogeneous k :=
  pderiv_mem_homogeneous hf i

example (hf : f ∈ homogeneous 0) (i : Fin 2) :
    pderiv i f = 0 :=
  pderiv_eq_zero_of_mem_homogeneous_zero hf i

example {a b : ℕ} (hf : f ∈ homogeneous (a + 1))
    (hg : g ∈ homogeneous (b + 1)) :
    bracket f g ∈ homogeneous (a + b) :=
  bracket_mem_homogeneous hf hg

example (k : ℕ) (f : PhaseSeries) :
    homogeneousComponent k f ∈ homogeneous k :=
  homogeneousComponent_mem k f

example (hf : f ∈ homogeneous k) :
    homogeneousComponent k f = f :=
  homogeneousComponent_eq_self hf

example {n : ℕ} (hf : f ∈ homogeneous k) (h : n ≠ k) :
    homogeneousComponent n f = 0 :=
  homogeneousComponent_eq_zero_of_mem hf h

example (hf : f ∈ orderGE (Fin 2) (k + 1)) :
    homogeneousComponent k f = 0 :=
  homogeneousComponent_eq_zero hf

example (hf : f ∈ orderGE (Fin 2) k) :
    f - homogeneousComponent k f ∈ orderGE (Fin 2) (k + 1) :=
  sub_homogeneousComponent_mem hf

example (h : f - g ∈ orderGE (Fin 2) (k + 1)) :
    homogeneousComponent k f = homogeneousComponent k g :=
  homogeneousComponent_congr h

example :
    action =
      (2⁻¹ : ℝ) • (X 0 ^ 2 + X 1 ^ 2) := rfl

example :
    action ∈ homogeneous 2 :=
  action_mem_homogeneous

example :
    pderiv 0 action = X 0 :=
  pderiv_zero_action

example :
    pderiv 1 action = X 1 :=
  pderiv_one_action

example (g : PhaseSeries) :
    bracket action g = X 0 * pderiv 1 g - X 1 * pderiv 0 g :=
  bracket_action g

example (hg : g ∈ homogeneous k) :
    bracket action g ∈ homogeneous k :=
  bracket_action_mem_homogeneous hg

example (f : PhaseSeries) (a b : ℕ) :
    coeff (mono (a + 1) (b + 1)) (bracket action f) =
      coeff (mono a (b + 2)) f * (b + 2) - coeff (mono (a + 2) b) f * (a + 2) :=
  coeff_mono_bracket_action f a b

example (f : PhaseSeries) (b : ℕ) :
    coeff (mono 0 (b + 1)) (bracket action f) = -coeff (mono 1 b) f :=
  coeff_mono_zero_bracket_action f b

example (f : PhaseSeries) (a : ℕ) :
    coeff (mono (a + 1) 0) (bracket action f) = coeff (mono a 1) f :=
  coeff_mono_bracket_action_zero f a

example (f : PhaseSeries) :
    coeff (mono 0 0) (bracket action f) = 0 :=
  coeff_zero_bracket_action f

example (h : bracket action f = 0) (m b : ℕ) :
    coeff (mono (2 * m + 1) b) f = 0 :=
  coeff_odd_left_eq_zero h m b

example (h : bracket action f = 0) (a m : ℕ) :
    coeff (mono a (2 * m + 1)) f = 0 :=
  coeff_odd_right_eq_zero h a m

example (h : bracket action f = 0)
    (h0 : ∀ b, coeff (mono 0 b) f = 0) (m b : ℕ) :
    coeff (mono (2 * m) b) f = 0 :=
  coeff_even_left_eq_zero h h0 m b

example (h : bracket action f = 0)
    (h0 : ∀ b, coeff (mono 0 b) f = 0) :
    f = 0 :=
  eq_zero_of_bracket_action_eq_zero h h0

example (m : ℕ) :
    bracket action (action ^ m) = 0 :=
  bracket_action_action_pow m

example :
    action = (2⁻¹ : ℝ) • X 1 ^ 2 + X 0 * ((2⁻¹ : ℝ) • X 0) :=
  action_eq

example (m : ℕ) :
    ∃ w : PhaseSeries, action ^ m = ((2⁻¹ : ℝ) • X 1 ^ 2) ^ m + X 0 * w :=
  exists_action_pow m

example (m : ℕ) :
    coeff (mono 0 (2 * m)) (action ^ m) = (2⁻¹ : ℝ) ^ m :=
  coeff_mono_zero_action_pow m

example (k : ℕ) :
    resonant k =
      if Even k then action ^ (k / 2) else 0 := rfl

example (m : ℕ) :
    resonant (2 * m) = action ^ m :=
  resonant_two_mul m

example (m : ℕ) :
    resonant (2 * m + 1) = 0 :=
  resonant_two_mul_add_one m

example (k : ℕ) :
    resonant k ∈ homogeneous k :=
  resonant_mem_homogeneous k

example (k : ℕ) :
    bracket action (resonant k) = 0 :=
  bracket_action_resonant k

example {z : PhaseSeries} (hz : z ∈ homogeneous k)
    (h : bracket action z = 0) :
    ∃ c : ℝ, z = c • resonant k :=
  eq_smul_resonant hz h

example (k : ℕ) (f g : PhaseSeries) :
    fischer k f g =
      ∑ i ∈ range (k + 1),
      (i ! : ℝ) * ((k - i)! : ℝ) * (coeff (mono i (k - i)) f * coeff (mono i (k - i)) g) := rfl

example (k : ℕ) (f g : PhaseSeries) :
    fischer k f g = fischer k g f :=
  fischer_comm k f g

example (k : ℕ) (f₁ f₂ g : PhaseSeries) :
    fischer k (f₁ - f₂) g = fischer k f₁ g - fischer k f₂ g :=
  fischer_sub_left k f₁ f₂ g

example (k : ℕ) (f g : PhaseSeries) :
    fischer (k + 1) (X 0 * f) g = fischer k f (pderiv 0 g) :=
  fischer_X_zero_mul k f g

example (k : ℕ) (f g : PhaseSeries) :
    fischer (k + 1) (X 1 * f) g = fischer k f (pderiv 1 g) :=
  fischer_X_one_mul k f g

example (k : ℕ) (f g : PhaseSeries) :
    fischer k (bracket action f) g = -fischer k f (bracket action g) :=
  fischer_bracket_action k f g

example (hf : f ∈ homogeneous k) (h : fischer k f f = 0) :
    f = 0 :=
  eq_zero_of_fischer_self hf h

example (k : ℕ) :
    FiniteDimensional ℝ (homogeneous k) :=
  finiteDimensional_homogeneous k

example (k : ℕ) {G : PhaseSeries} (hG : G ∈ homogeneous k) :
    ∃ F ∈ homogeneous k, ∃ c : ℝ, G = bracket action F + c • resonant k :=
  exists_homological k hG

end Homological

section NormalForm

variable {ω : ℝ} {H : PhaseSeries}

example (k : ℕ) (G : PhaseSeries) :
    homologicalSolution k G ∈ homogeneous k :=
  homologicalSolution_mem k G

example (k : ℕ) (G : PhaseSeries) :
    ∃ c : ℝ, homogeneousComponent k G =
      bracket action (homologicalSolution k G) + c • resonant k :=
  exists_homogeneousComponent_eq k G

example (hH : H - ω • action ∈ orderGE (Fin 2) 3) :
    H ∈ orderGE (Fin 2) 2 :=
  mem_orderGE_two_of_sub_mem hH

example (hω : ω ≠ 0) (hH : H - ω • action ∈ orderGE (Fin 2) 3)
    {W : PhaseSeries} (hW : W ∈ orderGE (Fin 2) 3) {k : ℕ} (hk : 3 ≤ k) :
    lieExp (ad (W + ω⁻¹ • homologicalSolution k (lieExp (ad W) H))) H - lieExp (ad W) H ∈
        orderGE (Fin 2) k ∧
      ∃ c : ℝ, homogeneousComponent k
        (lieExp (ad (W + ω⁻¹ • homologicalSolution k (lieExp (ad W) H))) H) =
          c • resonant k :=
  normalize_step hω hH hW hk

example (ω : ℝ) (H : PhaseSeries) (N : ℕ) :
    generatorSeq ω H N 0 = 0 :=
  generatorSeq_zero ω H N

example (ω : ℝ) (H : PhaseSeries) (N i : ℕ) :
    generatorSeq ω H N (i + 1) = generatorSeq ω H N i +
      ω⁻¹ • homologicalSolution (N + i) (lieExp (ad (generatorSeq ω H N i)) H) :=
  generatorSeq_succ ω H N i

example (ω : ℝ) (H : PhaseSeries) (N i : ℕ) :
    generatorSeq ω H N (i + 1) - generatorSeq ω H N i ∈ orderGE (Fin 2) (i + N) :=
  generatorSeq_succ_sub_mem ω H N i

example (ω : ℝ) (H : PhaseSeries) (N i : ℕ) :
    generatorSeq ω H N i ∈ orderGE (Fin 2) N :=
  generatorSeq_mem ω H N i

example (ω : ℝ) (H : PhaseSeries) (N : ℕ) :
    generator ω H N =
      seqLimit (generatorSeq ω H N) := rfl

example (ω : ℝ) (H : PhaseSeries) (N i : ℕ) :
    generator ω H N - generatorSeq ω H N i ∈ orderGE (Fin 2) (i + N) :=
  generator_sub_mem ω H N i

example (ω : ℝ) (H : PhaseSeries) (N : ℕ) :
    generator ω H N ∈ orderGE (Fin 2) N :=
  generator_mem ω H N

example (hω : ω ≠ 0) (hH : H - ω • action ∈ orderGE (Fin 2) 3)
    {N : ℕ} (hN : 3 ≤ N) (i : ℕ) :
    ∃ c : ℝ, homogeneousComponent (N + i) (lieExp (ad (generator ω H N)) H) =
      c • resonant (N + i) :=
  exists_component_generator hω hH hN i

example (hH : H - ω • action ∈ orderGE (Fin 2) 3) {N : ℕ}
    (hN : 3 ≤ N) :
    lieExp (ad (generator ω H N)) H - H ∈ orderGE (Fin 2) N :=
  lieExp_generator_sub_mem hH hN

example :
    PowerSeries.HasSubst action :=
  hasSubst_action

example (m : ℕ) :
    action ^ m ∈ homogeneous (2 * m) :=
  action_pow_mem_homogeneous m

example (h : PowerSeries ℝ) {e : Fin 2 →₀ ℕ} {m : ℕ}
    (he : e.degree = 2 * m) :
    coeff e (PowerSeries.subst action h) = PowerSeries.coeff m h * coeff e (action ^ m) :=
  coeff_subst_action_even h he

example (h : PowerSeries ℝ) {e : Fin 2 →₀ ℕ} {m : ℕ}
    (he : e.degree = 2 * m + 1) :
    coeff e (PowerSeries.subst action h) = 0 :=
  coeff_subst_action_odd h he

example (h : PowerSeries ℝ) (m : ℕ) :
    homogeneousComponent (2 * m) (PowerSeries.subst action h) =
      PowerSeries.coeff m h • action ^ m :=
  homogeneousComponent_subst_action h m

example {m : ℕ} {c c' : ℝ} (h : c • action ^ m = c' • action ^ m) :
    c = c' :=
  smul_action_pow_injective h

example {h : PowerSeries ℝ} {G : PhaseSeries} {m : ℕ}
    {c : ℝ} (hG : G = PowerSeries.subst action h)
    (hc : homogeneousComponent (2 * m) G = c • action ^ m) :
    PowerSeries.coeff m h = c :=
  coeff_eq_of_homogeneousComponent hG hc

example {G : PhaseSeries}
    (hG : ∀ k, ∃ c : ℝ, homogeneousComponent k G = c • resonant k) :
    ∃ h : PowerSeries ℝ, G = PowerSeries.subst action h :=
  exists_eq_subst_action hG

example (hω : ω ≠ 0)
    (hH : H - ω • action ∈ orderGE (Fin 2) 3) {N : ℕ} (hN : 3 ≤ N)
    (hres : ∀ k < N, ∃ c : ℝ, homogeneousComponent k H = c • resonant k) :
    ∃ (Ψ : PhaseSeries ≃ₐ[ℝ] PhaseSeries) (h : PowerSeries ℝ),
      (∀ f g, Ψ (bracket f g) = bracket (Ψ f) (Ψ g)) ∧
        Ψ H = PowerSeries.subst action h ∧ Ψ H - H ∈ orderGE (Fin 2) N :=
  exists_normal_form_of_resonant hω hH hN hres

example {k : ℕ} :
    homogeneousComponent k action = if k = 2 then action else 0 :=
  homogeneousComponent_action

example (hω : ω ≠ 0) (hH : H - ω • action ∈ orderGE (Fin 2) 3) :
    ∃ (Ψ : PhaseSeries ≃ₐ[ℝ] PhaseSeries) (h : PowerSeries ℝ),
      (∀ f g, Ψ (bracket f g) = bracket (Ψ f) (Ψ g)) ∧
        Ψ H = PowerSeries.subst action h ∧ PowerSeries.coeff 0 h = 0 ∧
          PowerSeries.coeff 1 h = ω :=
  exists_birkhoff_normal_form hω hH

end NormalForm

section Scaling

example {σ : Type*} (a : σ → ℝ) (n : σ →₀ ℕ) (i : σ) :
    (n + Finsupp.single i 1).prod (fun s m => a s ^ m) =
      n.prod (fun s m => a s ^ m) * a i :=
  prod_add_single a n i

example {σ : Type*} (a : σ → ℝ) (i : σ) (f : MvPowerSeries σ ℝ) :
    pderiv i (rescale a f) = a i • rescale a (pderiv i f) :=
  pderiv_rescale a i f

example {σ : Type*} (a : σ → ℝ) (i : σ) :
    rescale a (X i : MvPowerSeries σ ℝ) = a i • X i :=
  rescale_X a i

example (a : Fin 2 → ℝ) (f g : PhaseSeries) :
    bracket (rescale a f) (rescale a g) = (a 0 * a 1) • rescale a (bracket f g) :=
  bracket_rescale a f g

example (lam : ℝ) :
    scaling lam =
      ![lam, lam⁻¹] := rfl

example {lam : ℝ} (hlam : lam ≠ 0) :
    scaling lam * scaling lam⁻¹ = 1 :=
  scaling_mul_inv hlam

example {lam : ℝ} (hlam : lam ≠ 0) :
    scaling lam⁻¹ * scaling lam = 1 :=
  scaling_inv_mul hlam

example (lam : ℝ) (hlam : lam ≠ 0) (f : PhaseSeries) :
    scale lam hlam f = rescale (scaling lam) f :=
  scale_apply lam hlam f

example (lam : ℝ) (hlam : lam ≠ 0) (f g : PhaseSeries) :
    scale lam hlam (bracket f g) = bracket (scale lam hlam f) (scale lam hlam g) :=
  scale_bracket lam hlam f g

example (lam : ℝ) (hlam : lam ≠ 0) :
    scale lam hlam (X 0 : PhaseSeries) = lam • X 0 :=
  scale_X_zero lam hlam

example (lam : ℝ) (hlam : lam ≠ 0) :
    scale lam hlam (X 1 : PhaseSeries) = lam⁻¹ • X 1 :=
  scale_X_one lam hlam

end Scaling
