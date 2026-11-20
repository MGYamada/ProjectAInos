/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Potential.NewtonPotential
public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Taylor expansions of the Newton kernel

Space is `EuclideanSpace ℝ (Fin 3)` with the Euclidean norm, and `K x = 1/(4π‖x‖)` is the Newton
kernel. For `‖y‖ < ‖x‖` the segment from `x` to `x − y` avoids the origin, so `K(x − y)` has a
Taylor expansion in `y` about `x` with a remainder controlled by `‖x‖ − ‖y‖`.

* `norm_sub_sum_iteratedFDeriv_le`: Taylor's formula with the remainder bounded by a bound on the
  next derivative along the segment, for a function of class `Cⁿ⁺¹` along the segment.
* `abs_newtonKernel_sub_le`: `|K(x − y) − K(x)| ≤ ‖y‖/(4π‖x‖(‖x‖ − ‖y‖))`.
* `iteratedFDeriv_two_newtonKernel`: `D²K(z)(v, w) = (3⟪z,v⟫⟪z,w⟫ − ‖z‖²⟪v,w⟫)/(4π‖z‖⁵)`.
* `abs_newtonKernel_sub_dipole_le`: **the dipole remainder**
  `|K(x − y) − K(x) − ⟪x,y⟫/(4π‖x‖³)| ≤ ‖y‖²/(4π(‖x‖ − ‖y‖)³)`.
* `iteratedFDeriv_newtonKernel_smul`, `norm_iteratedFDeriv_newtonKernel_le`: the derivatives
  are homogeneous, `DⁿK(cz) = c^{-(n+1)} DⁿK(z)` for `c > 0`, so `‖DⁿK(z)‖ ≤ Cₙ/‖z‖ⁿ⁺¹`.
* `newtonKernel_taylor_le`: **the multipole remainder of every order**,
  `|K(x − y) − Σ_{k ≤ n} (k!)⁻¹ DᵏK(x)(−y, …, −y)| ≤ Cₙ‖y‖ⁿ⁺¹/(‖x‖ − ‖y‖)ⁿ⁺²`.
* `iteratedFDeriv_newtonKernel_comp_perm`: the derivatives of `K` away from the origin are
  symmetric; `sum_iteratedFDeriv_newtonKernel_snoc_snoc`: contracting two slots gives `0`,
  because `K` is harmonic away from the origin.
* `norm_iteratedFDeriv_newtonKernel_add_sub_le`: the variation of `DᵏK` under a translation `b`
  is `O(‖b‖/(‖x‖ − ‖b‖)ᵏ⁺²)`.
* `iteratedFDeriv_three_newtonKernel_diag`, `abs_newtonKernel_sub_quadrupole_le`: **the
  quadrupole remainder with an explicit constant**,
  `|K(x − y) − Σ_{k ≤ 2} (k!)⁻¹ DᵏK(x)(−y, …, −y)| ≤ ‖y‖³/(4π(‖x‖ − ‖y‖)⁴)`.
* `eq_zero_of_abs_sum_mul_pow_le`: a polynomial that is `O(tᵏ⁺¹)` as `t → 0⁺` has vanishing
  coefficients up to the degree `k`; it separates the orders of a homogeneous expansion.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real Nat
open scoped Topology ContDiff RealInnerProductSpace

namespace ProjectAinos.SmoothGeometry.Potential

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Taylor's formula with a bounded remainder -/

/-- The integral `∫₀¹ (1 − t)ⁿ dt = 1/(n + 1)`. -/
theorem integral_one_sub_pow (n : ℕ) : ∫ t in (0 : ℝ)..1, (1 - t) ^ n = 1 / (n + 1) := by
  rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ n), integral_pow]
  norm_num

/-- **Taylor's formula with a bounded remainder**: if `f` is `Cⁿ⁺¹` along the segment from `x`
to `x + y` and the `(n + 1)`-st derivative on `(y, …, y)` is bounded by `M` there, then
`‖f(x + y) − Σ_{k ≤ n} (k!)⁻¹ Dᵏf(x)(y, …, y)‖ ≤ M/(n + 1)!`. -/
theorem norm_sub_sum_iteratedFDeriv_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : E → F} {x y : E} {n : ℕ}
    {M : ℝ} (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (n + 1) f (x + t • y))
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖ ≤ M) :
    ‖f (x + y) - ∑ k ∈ Finset.range (n + 1), (k ! : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ => y)‖
      ≤ M / (n + 1)! := by
  rw [map_add_eq_sum_add_integral_iteratedFDeriv hf, add_sub_cancel_left, norm_smul]
  have h1 : ‖∫ t in (0 : ℝ)..1, (1 - t) ^ n • iteratedFDeriv ℝ (n + 1) f (x + t • y)
      (fun _ => y)‖ ≤ ∫ t in (0 : ℝ)..1, (1 - t) ^ n * M := by
    refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (Eventually.of_forall fun t ht => ?_)
      ((by fun_prop : Continuous fun t : ℝ => (1 - t) ^ n * M).intervalIntegrable 0 1)
    have h0 : 0 ≤ (1 - t) ^ n := pow_nonneg (by linarith [ht.2]) n
    rw [norm_smul, Real.norm_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (hM t ⟨ht.1.le, ht.2⟩) h0
  rw [intervalIntegral.integral_mul_const, integral_one_sub_pow] at h1
  have hfac : ((n + 1)! : ℝ) = (n + 1) * n ! := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [Real.norm_of_nonneg (by positivity), hfac]
  calc (n ! : ℝ)⁻¹ * ‖∫ t in (0 : ℝ)..1, (1 - t) ^ n • iteratedFDeriv ℝ (n + 1) f (x + t • y)
        (fun _ => y)‖ ≤ (n ! : ℝ)⁻¹ * (1 / (n + 1) * M) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = M / ((n + 1) * n !) := by
        field_simp

/-- On the segment from `x` to `x + b`, the distance to the origin is at least `‖x‖ − ‖b‖`. -/
theorem sub_le_norm_add_smul (x b : E3) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖x‖ - ‖b‖ ≤ ‖x + t • b‖ := by
  have h1 : ‖x‖ ≤ ‖x + t • b‖ + ‖t • b‖ := by
    calc ‖x‖ = ‖(x + t • b) - t • b‖ := by
          congr 1
          abel
      _ ≤ _ := norm_sub_le _ _
  have h2 : ‖t • b‖ ≤ ‖b‖ := by
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  linarith

/-- On the segment from `x` to `x − y`, the distance to the origin is at least `‖x‖ − ‖y‖`. -/
theorem sub_le_norm_add_smul_neg (x y : E3) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖x‖ - ‖y‖ ≤ ‖x + t • -y‖ := by
  simpa using sub_le_norm_add_smul x (-y) ht

/-- For `‖y‖ < ‖x‖` the segment from `x` to `x − y` avoids the origin. -/
theorem add_smul_neg_ne_zero {x y : E3} (hy : ‖y‖ < ‖x‖) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    x + t • -y ≠ 0 := by
  have := sub_le_norm_add_smul_neg x y ht
  exact norm_pos_iff.mp (by linarith)

/-! ### The first variation of the kernel -/

/-- **The first variation of the kernel**: for `‖y‖ < ‖x‖`,
`|K(x − y) − K(x)| ≤ ‖y‖/(4π‖x‖(‖x‖ − ‖y‖))`. -/
theorem abs_newtonKernel_sub_le {x y : E3} (hy : ‖y‖ < ‖x‖) :
    |newtonKernel (x - y) - newtonKernel x| ≤ ‖y‖ / (4 * π * ‖x‖ * (‖x‖ - ‖y‖)) := by
  have hx : 0 < ‖x‖ := (norm_nonneg y).trans_lt hy
  have hd : 0 < ‖x‖ - ‖y‖ := by linarith
  have hxy : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := by
    have := norm_sub_norm_le x y
    linarith
  have hxy0 : 0 < ‖x - y‖ := hd.trans_le hxy
  have hdiff : |‖x‖ - ‖x - y‖| ≤ ‖y‖ := by
    rw [abs_le]
    constructor
    · have := norm_sub_le x y
      linarith
    · have := norm_sub_norm_le x y
      have h2 : ‖x - y‖ - ‖x‖ ≤ ‖y‖ := by
        have := norm_sub_le_norm_add x y
        calc ‖x - y‖ - ‖x‖ ≤ ‖x‖ + ‖y‖ - ‖x‖ := by
              have := norm_sub_le x y
              linarith
          _ = ‖y‖ := by ring
      linarith
  have heq : newtonKernel (x - y) - newtonKernel x =
      (‖x‖ - ‖x - y‖) / (4 * π * ‖x‖ * ‖x - y‖) := by
    unfold newtonKernel
    field_simp
  rw [heq, abs_div, abs_of_pos (by positivity : 0 < 4 * π * ‖x‖ * ‖x - y‖)]
  calc |‖x‖ - ‖x - y‖| / (4 * π * ‖x‖ * ‖x - y‖) ≤ ‖y‖ / (4 * π * ‖x‖ * ‖x - y‖) :=
        div_le_div_of_nonneg_right hdiff (by positivity)
    _ ≤ ‖y‖ / (4 * π * ‖x‖ * (‖x‖ - ‖y‖)) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
          (mul_le_mul_of_nonneg_left hxy (by positivity))

/-! ### The second derivative of the kernel -/

/-- The second derivative of a radial function `g(‖y‖²)` on `(v, w)` is
`2 g'(‖x‖²)⟪v,w⟫ + 4 g''(‖x‖²)⟪x,v⟫⟪x,w⟫`. -/
theorem fderiv_fderiv_comp_normSq_apply {g g' : ℝ → ℝ} {g'' : ℝ} {x : E3}
    (hg : ∀ᶠ s in 𝓝 (‖x‖ ^ 2), HasDerivAt g (g' s) s) (hg' : HasDerivAt g' g'' (‖x‖ ^ 2))
    (v w : E3) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => g (‖z‖ ^ 2)) y w) x v =
      2 * g' (‖x‖ ^ 2) * ⟪v, w⟫ + 4 * g'' * ⟪x, v⟫ * ⟪x, w⟫ := by
  have hc : ContinuousAt (fun y : E3 => ‖y‖ ^ 2) x := by fun_prop
  have hev : ∀ᶠ y in 𝓝 x, HasDerivAt g (g' (‖y‖ ^ 2)) (‖y‖ ^ 2) := hc.eventually hg
  have heq : (fun y => fderiv ℝ (fun z => g (‖z‖ ^ 2)) y w) =ᶠ[𝓝 x]
      fun y => 2 * g' (‖y‖ ^ 2) * innerSL ℝ w y := by
    filter_upwards [hev] with y hy
    rw [(hasFDerivAt_comp_normSq hy).fderiv]
    simp [real_inner_comm]
  have h1 : HasFDerivAt (fun y : E3 => 2 * g' (‖y‖ ^ 2))
      ((2 : ℝ) • ((2 * g'') • innerSL ℝ x)) x :=
    (hasFDerivAt_comp_normSq hg').const_mul 2
  have h2 : HasFDerivAt (fun y => 2 * g' (‖y‖ ^ 2) * innerSL ℝ w y) _ x :=
    h1.mul (innerSL ℝ w).hasFDerivAt
  rw [heq.fderiv_eq, h2.fderiv]
  simp [smul_eq_mul, real_inner_comm]
  ring

/-- The power `(‖x‖²)^{-k/2} = ‖x‖⁻ᵏ`. -/
theorem normSq_rpow_neg_half (x : E3) (k : ℕ) :
    (‖x‖ ^ 2 + 0) ^ (-((k : ℝ) / 2)) = (‖x‖ ^ k)⁻¹ := by
  rw [add_zero, ← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_mul (norm_nonneg x),
    show ((2 : ℕ) : ℝ) * -((k : ℝ) / 2) = -(k : ℝ) by push_cast; ring,
    Real.rpow_neg (norm_nonneg x), Real.rpow_natCast]

/-- The kernel as the radial profile at `e = 0`. -/
theorem newtonKernel_eq_kernelProfile : newtonKernel = fun y => kernelProfile 0 (‖y‖ ^ 2) := by
  funext y
  rw [newtonKernel_eq_regularKernel, regularKernel_eq_kernelProfile]
  simp

/-- **The second derivative of the kernel**: away from the origin,
`D²K(z)(v, w) = (3⟪z,v⟫⟪z,w⟫ − ‖z‖²⟪v,w⟫)/(4π‖z‖⁵)`. -/
theorem iteratedFDeriv_two_newtonKernel {z : E3} (hz : z ≠ 0) (m : Fin 2 → E3) :
    iteratedFDeriv ℝ 2 newtonKernel z m =
      (3 * ⟪z, m 0⟫ * ⟪z, m 1⟫ - ‖z‖ ^ 2 * ⟪m 0, m 1⟫) / (4 * π * ‖z‖ ^ 5) := by
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h0 : 0 < ‖z‖ ^ 2 + 0 := by positivity
  rw [iteratedFDeriv_two_apply, ← fderiv_fderiv_apply (contDiffAt_newtonKernel hz)]
  have hev : ∀ᶠ s in 𝓝 (‖z‖ ^ 2), HasDerivAt (kernelProfile 0)
      (-(8 * π)⁻¹ * (s + 0) ^ (-(3 / 2 : ℝ))) s := by
    have : ∀ᶠ s in 𝓝 (‖z‖ ^ 2), 0 < s + 0 :=
      (continuous_id.add continuous_const).continuousAt.eventually (lt_mem_nhds h0)
    filter_upwards [this] with s hs using hasDerivAt_kernelProfile hs
  rw [newtonKernel_eq_kernelProfile, fderiv_fderiv_comp_normSq_apply hev
    (hasDerivAt_kernelProfile_deriv h0)]
  have h3 := normSq_rpow_neg_half z 3
  have h5 := normSq_rpow_neg_half z 5
  push_cast at h3 h5
  rw [show -(3 / 2 : ℝ) = -(3 / 2) by norm_num] at h3 ⊢
  rw [h3, h5]
  field_simp
  ring

/-- The second derivative of the kernel on the diagonal is bounded by
`|D²K(z)(v, v)| ≤ ‖v‖²/(2π‖z‖³)`. -/
theorem abs_iteratedFDeriv_two_newtonKernel_le {z : E3} (hz : z ≠ 0) (v : E3) :
    |iteratedFDeriv ℝ 2 newtonKernel z (fun _ => v)| ≤ ‖v‖ ^ 2 / (2 * π * ‖z‖ ^ 3) := by
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [iteratedFDeriv_two_newtonKernel hz, real_inner_self_eq_norm_sq]
  have hc : ⟪z, v⟫ ^ 2 ≤ ‖z‖ ^ 2 * ‖v‖ ^ 2 := by
    have := abs_real_inner_le_norm z v
    rw [← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hnum : |3 * ⟪z, v⟫ * ⟪z, v⟫ - ‖z‖ ^ 2 * ‖v‖ ^ 2| ≤ 2 * (‖z‖ ^ 2 * ‖v‖ ^ 2) := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg ⟪z, v⟫]
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * π * ‖z‖ ^ 5)]
  calc |3 * ⟪z, v⟫ * ⟪z, v⟫ - ‖z‖ ^ 2 * ‖v‖ ^ 2| / (4 * π * ‖z‖ ^ 5)
      ≤ 2 * (‖z‖ ^ 2 * ‖v‖ ^ 2) / (4 * π * ‖z‖ ^ 5) :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ = ‖v‖ ^ 2 / (2 * π * ‖z‖ ^ 3) := by
        field_simp
        ring

/-! ### The dipole remainder -/

/-- The derivative of the kernel on `−y` is `⟪x,y⟫/(4π‖x‖³)`. -/
theorem fderiv_newtonKernel_neg_apply {x : E3} (hx : x ≠ 0) (y : E3) :
    fderiv ℝ newtonKernel x (-y) = ⟪x, y⟫ / (4 * π * ‖x‖ ^ 3) := by
  rw [(hasFDerivAt_newtonKernel hx).fderiv]
  simp [div_eq_inv_mul]

/-- **The dipole remainder**: for `‖y‖ < ‖x‖`,
`|K(x − y) − K(x) − ⟪x,y⟫/(4π‖x‖³)| ≤ ‖y‖²/(4π(‖x‖ − ‖y‖)³)`; the constant `1/(4π)` is attained
in the limit `y ∥ x`, `‖y‖ → 0`. -/
theorem abs_newtonKernel_sub_dipole_le {x y : E3} (hy : ‖y‖ < ‖x‖) :
    |newtonKernel (x - y) - newtonKernel x - ⟪x, y⟫ / (4 * π * ‖x‖ ^ 3)| ≤
      ‖y‖ ^ 2 / (4 * π * (‖x‖ - ‖y‖) ^ 3) := by
  have hx : x ≠ 0 := norm_pos_iff.mp ((norm_nonneg y).trans_lt hy)
  have hd : 0 < ‖x‖ - ‖y‖ := by linarith
  have h := norm_sub_sum_iteratedFDeriv_le (f := newtonKernel) (x := x) (y := -y) (n := 1)
    (M := ‖y‖ ^ 2 / (2 * π * (‖x‖ - ‖y‖) ^ 3))
    (fun t ht => contDiffAt_newtonKernel (add_smul_neg_ne_zero hy ht))
    (fun t ht => by
      have hne := add_smul_neg_ne_zero hy ht
      have hle := sub_le_norm_add_smul_neg x y ht
      show ‖iteratedFDeriv ℝ 2 newtonKernel (x + t • -y) (fun _ => -y)‖ ≤ _
      rw [Real.norm_eq_abs]
      refine (abs_iteratedFDeriv_two_newtonKernel_le hne (-y)).trans ?_
      rw [norm_neg]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd.le hle 3) (by positivity)))
  simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
    iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply, fderiv_newtonKernel_neg_apply hx,
    Nat.factorial, Nat.cast_one, inv_one, one_smul, ← sub_eq_add_neg, Real.norm_eq_abs] at h
  convert h using 1
  · ring_nf
  · norm_num
    field_simp
    ring

/-! ### Homogeneity and the bound of every order -/

/-- The kernel is homogeneous of degree `−1`: `K(cz) = c⁻¹K(z)` for `c > 0`. -/
theorem newtonKernel_smul {c : ℝ} (hc : 0 < c) (z : E3) :
    newtonKernel (c • z) = c⁻¹ * newtonKernel z := by
  unfold newtonKernel
  rw [norm_smul, Real.norm_of_nonneg hc.le]
  field_simp

/-- **Homogeneity of the derivatives**: `DⁿK(cz) = c^{-(n+1)} DⁿK(z)` for `c > 0` and `z ≠ 0`. -/
theorem iteratedFDeriv_newtonKernel_smul {c : ℝ} (hc : 0 < c) {z : E3} (hz : z ≠ 0) (n : ℕ) :
    iteratedFDeriv ℝ n newtonKernel (c • z) =
      (c ^ (n + 1))⁻¹ • iteratedFDeriv ℝ n newtonKernel z := by
  let g : E3 ≃L[ℝ] E3 := (LinearEquiv.smulOfNeZero ℝ E3 c hc.ne').toContinuousLinearEquiv
  have hg (w : E3) : g w = c • w := rfl
  have hfun : newtonKernel ∘ g = fun w => c⁻¹ • newtonKernel w := by
    funext w
    simp only [Function.comp_apply, hg, newtonKernel_smul hc, smul_eq_mul]
  have h1 : iteratedFDeriv ℝ n (newtonKernel ∘ g) z =
      (iteratedFDeriv ℝ n newtonKernel (g z)).compContinuousLinearMap
        fun _ => (g : E3 →L[ℝ] E3) := by
    simpa [iteratedFDerivWithin_univ] using
      g.iteratedFDerivWithin_comp_right newtonKernel uniqueDiffOn_univ (mem_univ _) n
  rw [hfun, iteratedFDeriv_const_smul_apply' (contDiffAt_newtonKernel hz)] at h1
  ext m
  have h2 := congrArg (fun L => L m) h1
  simp only [smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearEquiv.coe_coe, hg,
    ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at h2
  have hcn : (c ^ n) ≠ 0 := pow_ne_zero _ hc.ne'
  rw [smul_apply, smul_eq_mul, pow_succ, mul_inv, mul_assoc, h2, inv_mul_cancel_left₀ hcn]

/-- The derivatives of the kernel are continuous away from the origin. -/
theorem continuousAt_iteratedFDeriv_newtonKernel {z : E3} (hz : z ≠ 0) (n : ℕ) :
    ContinuousAt (iteratedFDeriv ℝ n newtonKernel) z :=
  ((contDiffAt_newtonKernel hz (n := ω)).iteratedFDeriv_right (m := 0) (i := n)
    (by simp)).continuousAt

/-- **The bound of every order**: `‖DⁿK(z)‖ ≤ Cₙ/‖z‖ⁿ⁺¹` away from the origin, with `Cₙ` the
maximum of `‖DⁿK‖` on the unit sphere. -/
theorem norm_iteratedFDeriv_newtonKernel_le (n : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ z : E3, z ≠ 0 → ‖iteratedFDeriv ℝ n newtonKernel z‖ ≤ C / ‖z‖ ^ (n + 1) := by
  have hcont : ContinuousOn (iteratedFDeriv ℝ n newtonKernel) (sphere (0 : E3) 1) := by
    intro u hu
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hu
    exact (continuousAt_iteratedFDeriv_newtonKernel hu0 n).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : E3) 1).exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun z hz => ?_⟩
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  set u : E3 := ‖z‖⁻¹ • z with hu
  have hu1 : u ∈ sphere (0 : E3) 1 := by
    rw [mem_sphere_zero_iff_norm, hu, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hz'.le),
      inv_mul_cancel₀ hz'.ne']
  have hu0 : u ≠ 0 := by
    rintro h
    rw [h] at hu1
    simp at hu1
  have hzu : z = ‖z‖ • u := by
    rw [hu, smul_smul, mul_inv_cancel₀ hz'.ne', one_smul]
  rw [hzu, iteratedFDeriv_newtonKernel_smul hz' hu0, norm_smul,
    Real.norm_of_nonneg (by positivity), ← hzu, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left ((hC u hu1).trans (le_max_left _ _)) (by positivity)

/-- **The multipole remainder of every order**: there is a constant `Cₙ` with
`|K(x − y) − Σ_{k ≤ n} (k!)⁻¹ DᵏK(x)(−y, …, −y)| ≤ Cₙ‖y‖ⁿ⁺¹/(‖x‖ − ‖y‖)ⁿ⁺²` for `‖y‖ < ‖x‖`. -/
theorem newtonKernel_taylor_le (n : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x y : E3, ‖y‖ < ‖x‖ →
      |newtonKernel (x - y) - ∑ k ∈ Finset.range (n + 1),
          (k ! : ℝ)⁻¹ * iteratedFDeriv ℝ k newtonKernel x (fun _ => -y)| ≤
        C * ‖y‖ ^ (n + 1) / (‖x‖ - ‖y‖) ^ (n + 2) := by
  obtain ⟨C, hC0, hC⟩ := norm_iteratedFDeriv_newtonKernel_le (n + 1)
  refine ⟨C / (n + 1)!, by positivity, fun x y hy => ?_⟩
  have hd : 0 < ‖x‖ - ‖y‖ := by linarith [norm_nonneg y]
  have h := norm_sub_sum_iteratedFDeriv_le (f := newtonKernel) (x := x) (y := -y) (n := n)
    (M := C * ‖y‖ ^ (n + 1) / (‖x‖ - ‖y‖) ^ (n + 2))
    (fun t ht => contDiffAt_newtonKernel (add_smul_neg_ne_zero hy ht))
    (fun t ht => by
      have hne := add_smul_neg_ne_zero hy ht
      have hle := sub_le_norm_add_smul_neg x y ht
      refine ((iteratedFDeriv ℝ (n + 1) newtonKernel (x + t • -y)).le_opNorm _).trans ?_
      simp only [norm_neg, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      calc ‖iteratedFDeriv ℝ (n + 1) newtonKernel (x + t • -y)‖ * ‖y‖ ^ (n + 1)
          ≤ C / ‖x + t • -y‖ ^ (n + 1 + 1) * ‖y‖ ^ (n + 1) :=
            mul_le_mul_of_nonneg_right (hC _ hne) (by positivity)
        _ ≤ C / (‖x‖ - ‖y‖) ^ (n + 2) * ‖y‖ ^ (n + 1) := by
            gcongr
        _ = C * ‖y‖ ^ (n + 1) / (‖x‖ - ‖y‖) ^ (n + 2) := by ring)
  simp only [smul_eq_mul, ← sub_eq_add_neg, Real.norm_eq_abs] at h
  calc _ ≤ C * ‖y‖ ^ (n + 1) / (‖x‖ - ‖y‖) ^ (n + 2) / (n + 1)! := h
    _ = _ := by ring

/-! ### Symmetry and the trace -/

/-- **Symmetry**: away from the origin the derivatives of the kernel are symmetric multilinear
maps, because the kernel is analytic there. -/
theorem iteratedFDeriv_newtonKernel_comp_perm {z : E3} (hz : z ≠ 0) {n : ℕ} (v : Fin n → E3)
    (σ : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℝ n newtonKernel z (v ∘ σ) = iteratedFDeriv ℝ n newtonKernel z v :=
  (contDiffAt_newtonKernel hz (n := ω)).iteratedFDeriv_comp_perm v σ

/-- The contraction `B ↦ Σᵢ B eᵢ eᵢ` of a bilinear form with the unit vectors. -/
def traceForm : (E3 →L[ℝ] E3 →L[ℝ] ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin 3, (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).comp
    (ContinuousLinearMap.apply ℝ (E3 →L[ℝ] ℝ) (EuclideanSpace.single i 1))

/-- The contraction is the sum of the diagonal entries. -/
theorem traceForm_apply (B : E3 →L[ℝ] E3 →L[ℝ] ℝ) :
    traceForm B = ∑ i : Fin 3, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  simp [traceForm]

/-- **The trace vanishes**: away from the origin, contracting the last two slots of `Dᵏ⁺²K` with
the unit vectors gives `0`, because `ΔK = 0` there. By `iteratedFDeriv_newtonKernel_comp_perm`
any two slots may be contracted. -/
theorem sum_iteratedFDeriv_newtonKernel_snoc_snoc {z : E3} (hz : z ≠ 0) {k : ℕ}
    (v : Fin k → E3) :
    ∑ i : Fin 3, iteratedFDeriv ℝ (k + 2) newtonKernel z
      (Fin.snoc (Fin.snoc v (EuclideanSpace.single i 1)) (EuclideanSpace.single i 1)) = 0 := by
  have hK := contDiffAt_newtonKernel hz (n := ω)
  have hK2 : ContDiffAt ℝ ω (fderiv ℝ (fderiv ℝ newtonKernel)) z :=
    (hK.fderiv_right (m := ω) le_rfl).fderiv_right (m := ω) le_rfl
  have hslot (e : E3) :
      iteratedFDeriv ℝ (k + 1 + 1) newtonKernel z (Fin.snoc (Fin.snoc v e) e) =
        iteratedFDeriv ℝ k (fderiv ℝ (fderiv ℝ newtonKernel)) z v e e := by
    rw [iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last,
      iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
  change ∑ i : Fin 3, iteratedFDeriv ℝ (k + 1 + 1) newtonKernel z
    (Fin.snoc (Fin.snoc v (EuclideanSpace.single i 1)) (EuclideanSpace.single i 1)) = 0
  simp only [hslot]
  have hcomp : iteratedFDeriv ℝ k (traceForm ∘ fderiv ℝ (fderiv ℝ newtonKernel)) z =
      traceForm.compContinuousMultilinearMap
        (iteratedFDeriv ℝ k (fderiv ℝ (fderiv ℝ newtonKernel)) z) :=
    traceForm.iteratedFDeriv_comp_left hK2 (by simp)
  have hzero : traceForm ∘ fderiv ℝ (fderiv ℝ newtonKernel) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    rw [Function.comp_apply, traceForm_apply, ← coordLaplacian_newtonKernel hw, coordLaplacian]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fderiv_fderiv_apply (contDiffAt_newtonKernel hw)]
  have h0 : iteratedFDeriv ℝ k (traceForm ∘ fderiv ℝ (fderiv ℝ newtonKernel)) z = 0 := by
    rw [(hzero.iteratedFDeriv ℝ k).eq_of_nhds]
    simp
  have h1 := congrArg (fun L => L v) (hcomp.symm.trans h0)
  simpa [traceForm_apply] using h1

/-! ### The variation under a translation -/

/-- **The variation under a translation**: there is a constant `C` with
`‖DᵏK(x + b) − DᵏK(x)‖ ≤ C‖b‖/(‖x‖ − ‖b‖)ᵏ⁺²` for `‖b‖ < ‖x‖`. -/
theorem norm_iteratedFDeriv_newtonKernel_add_sub_le (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x b : E3, ‖b‖ < ‖x‖ →
      ‖iteratedFDeriv ℝ k newtonKernel (x + b) - iteratedFDeriv ℝ k newtonKernel x‖ ≤
        C * ‖b‖ / (‖x‖ - ‖b‖) ^ (k + 2) := by
  obtain ⟨C, hC0, hC⟩ := norm_iteratedFDeriv_newtonKernel_le (k + 1)
  refine ⟨C, hC0, fun x b hb => ?_⟩
  have hd : 0 < ‖x‖ - ‖b‖ := by linarith [norm_nonneg b]
  have hseg : ∀ w ∈ segment ℝ x (x + b), ‖x‖ - ‖b‖ ≤ ‖w‖ := by
    intro w hw
    rw [segment_eq_image'] at hw
    obtain ⟨t, ht, rfl⟩ := hw
    simpa using sub_le_norm_add_smul x b ht
  have hne : ∀ w ∈ segment ℝ x (x + b), w ≠ 0 := fun w hw =>
    norm_pos_iff.mp (hd.trans_le (hseg w hw))
  have h := (convex_segment x (x + b)).norm_image_sub_le_of_norm_fderiv_le
    (f := iteratedFDeriv ℝ k newtonKernel) (C := C / (‖x‖ - ‖b‖) ^ (k + 2))
    (fun w hw => ((contDiffAt_newtonKernel (hne w hw) (n := ω)).differentiableAt_iteratedFDeriv
      (by simp)))
    (fun w hw => by
      rw [norm_fderiv_iteratedFDeriv]
      refine (hC w (hne w hw)).trans ?_
      gcongr
      exact hseg w hw)
    (left_mem_segment ℝ x (x + b)) (right_mem_segment ℝ x (x + b))
  rw [add_sub_cancel_left] at h
  calc _ ≤ C / (‖x‖ - ‖b‖) ^ (k + 2) * ‖b‖ := h
    _ = _ := by ring

/-! ### The quadrupole remainder -/

/-- **The third derivative of the kernel on the diagonal**: away from the origin,
`D³K(z)(v, v, v) = (9⟪z,v⟫‖v‖²‖z‖² − 15⟪z,v⟫³)/(4π‖z‖⁷)`. -/
theorem iteratedFDeriv_three_newtonKernel_diag {z : E3} (hz : z ≠ 0) (v : E3) :
    iteratedFDeriv ℝ 3 newtonKernel z (fun _ => v) =
      (9 * ⟪z, v⟫ * ‖v‖ ^ 2 * ‖z‖ ^ 2 - 15 * ⟪z, v⟫ ^ 3) / (4 * π * ‖z‖ ^ 7) := by
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h1 := (show ContDiffAt ℝ (2 + 1) newtonKernel (z + (0 : ℝ) • v) by
    simpa using contDiffAt_newtonKernel hz).deriv_fderiv_add_smul
  simp only [zero_smul, add_zero] at h1
  change iteratedFDeriv ℝ (2 + 1) newtonKernel z (fun _ => v) = _
  rw [← h1]
  set c := ⟪z, v⟫ with hc
  set n2 := ‖v‖ ^ 2 with hn2
  set r2 := ‖z‖ ^ 2 with hr2
  set q : ℝ → ℝ := fun s => r2 + (2 * c * s + n2 * s ^ 2) with hqdef
  have hq (s : ℝ) : ‖z + s • v‖ ^ 2 = q s := by
    rw [norm_add_sq_real, norm_smul, inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs]
    simp only [hqdef]
    ring
  have hinner (s : ℝ) : ⟪z + s • v, v⟫ = c + n2 * s := by
    rw [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [RCLike.conj_to_real]
    ring
  have hq0 : q 0 = r2 := by simp [hqdef]
  have hr2pos : 0 < r2 := by positivity
  set G : ℝ → ℝ := fun s => (3 * (c + n2 * s) ^ 2 - q s * n2) * ((4 * π)⁻¹ * q s ^ (-(5 / 2 : ℝ)))
    with hGdef
  have hev : (fun s : ℝ => iteratedFDeriv ℝ 2 newtonKernel (z + s • v) (fun _ => v)) =ᶠ[𝓝 0] G := by
    have hcont : ContinuousAt (fun s : ℝ => z + s • v) 0 := by fun_prop
    have hne : ∀ᶠ s in 𝓝 (0 : ℝ), z + s • v ≠ 0 := by
      have := hcont.eventually (isOpen_ne.mem_nhds (by simpa using hz))
      exact this
    filter_upwards [hne] with s hs
    have hs' : 0 < ‖z + s • v‖ := norm_pos_iff.mpr hs
    rw [iteratedFDeriv_two_newtonKernel hs, hinner, real_inner_self_eq_norm_sq, hGdef]
    simp only
    rw [← hq s, show (‖z + s • v‖ ^ 2) ^ (-(5 / 2 : ℝ)) = (‖z + s • v‖ ^ 5)⁻¹ by
      have := normSq_rpow_neg_half (z + s • v) 5
      rw [add_zero] at this
      convert this using 2]
    field_simp
    rw [← hn2]
    ring
  have hqd : HasDerivAt q (2 * c + 2 * n2 * 0) 0 :=
    ((((hasDerivAt_id (0 : ℝ)).const_mul (2 * c)).add
      ((hasDerivAt_pow 2 (0 : ℝ)).const_mul n2)).const_add r2).congr_deriv (by simp)
  have hA : HasDerivAt (fun s => 3 * (c + n2 * s) ^ 2 - q s * n2)
      (3 * (2 * (c + n2 * 0) * n2) - (2 * c + 2 * n2 * 0) * n2) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => c + n2 * s) n2 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul n2).const_add c
    have h2 := (h1.pow 2).const_mul 3
    have h3 := hqd.mul_const n2
    convert h2.sub h3 using 1
    simp
  have hB : HasDerivAt (fun s => (4 * π)⁻¹ * q s ^ (-(5 / 2 : ℝ)))
      ((4 * π)⁻¹ * ((2 * c + 2 * n2 * 0) * (-(5 / 2 : ℝ)) * q 0 ^ (-(5 / 2 : ℝ) - 1))) 0 :=
    (hqd.rpow_const (p := -(5 / 2 : ℝ)) (Or.inl (by rw [hq0]; exact hr2pos.ne'))).const_mul _
  have hGd : HasDerivAt G _ 0 := hA.mul hB
  rw [hev.deriv_eq, hGd.deriv]
  have h5 : r2 ^ (-(5 / 2 : ℝ)) = (‖z‖ ^ 5)⁻¹ := by
    have := normSq_rpow_neg_half z 5
    rw [add_zero] at this
    convert this using 2
  have h7 : r2 ^ (-(5 / 2 : ℝ) - 1) = (‖z‖ ^ 7)⁻¹ := by
    have := normSq_rpow_neg_half z 7
    rw [add_zero] at this
    convert this using 2
    norm_num
  simp only [hq0, h5, h7, mul_zero, add_zero]
  rw [hr2]
  field_simp
  ring

/-- The third derivative of the kernel on the diagonal is bounded by
`|D³K(z)(v, v, v)| ≤ 3‖v‖³/(2π‖z‖⁴)`; with `⟪z,v⟫ = κ‖z‖‖v‖` the bound is
`|9κ − 15κ³| ≤ 6` for `|κ| ≤ 1`. -/
theorem abs_iteratedFDeriv_three_newtonKernel_le {z : E3} (hz : z ≠ 0) (v : E3) :
    |iteratedFDeriv ℝ 3 newtonKernel z (fun _ => v)| ≤ 3 * ‖v‖ ^ 3 / (2 * π * ‖z‖ ^ 4) := by
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [iteratedFDeriv_three_newtonKernel_diag hz]
  set c := ⟪z, v⟫
  set p := ‖z‖ * ‖v‖ with hp
  have hp0 : 0 ≤ p := by positivity
  have hc : |c| ≤ p := abs_real_inner_le_norm z v
  have hc1 : 0 ≤ p + c := by linarith [neg_abs_le c]
  have hc2 : 0 ≤ p - c := by linarith [le_abs_self c]
  have hq1 : 0 ≤ 5 * c ^ 2 - 5 * c * p + 2 * p ^ 2 := by nlinarith [sq_nonneg (2 * c - p)]
  have hq2 : 0 ≤ 5 * c ^ 2 + 5 * c * p + 2 * p ^ 2 := by nlinarith [sq_nonneg (2 * c + p)]
  have hnum : |9 * c * ‖v‖ ^ 2 * ‖z‖ ^ 2 - 15 * c ^ 3| ≤ 6 * p ^ 3 := by
    have hpp : ‖v‖ ^ 2 * ‖z‖ ^ 2 = p ^ 2 := by rw [hp]; ring
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg hc2 hq2]
    · nlinarith [mul_nonneg hc1 hq1]
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * π * ‖z‖ ^ 7)]
  calc |9 * c * ‖v‖ ^ 2 * ‖z‖ ^ 2 - 15 * c ^ 3| / (4 * π * ‖z‖ ^ 7)
      ≤ 6 * p ^ 3 / (4 * π * ‖z‖ ^ 7) := div_le_div_of_nonneg_right hnum (by positivity)
    _ = 3 * ‖v‖ ^ 3 / (2 * π * ‖z‖ ^ 4) := by
        rw [hp]
        field_simp
        ring

/-- **The quadrupole remainder of the kernel**: for `‖y‖ < ‖x‖`,
`|K(x − y) − Σ_{k ≤ 2} (k!)⁻¹ DᵏK(x)(−y, …, −y)| ≤ ‖y‖³/(4π(‖x‖ − ‖y‖)⁴)`. -/
theorem abs_newtonKernel_sub_taylor_two_le {x y : E3} (hy : ‖y‖ < ‖x‖) :
    |newtonKernel (x - y) - ∑ k ∈ Finset.range 3,
        (k ! : ℝ)⁻¹ * iteratedFDeriv ℝ k newtonKernel x (fun _ => -y)| ≤
      ‖y‖ ^ 3 / (4 * π * (‖x‖ - ‖y‖) ^ 4) := by
  have hd : 0 < ‖x‖ - ‖y‖ := by linarith [norm_nonneg y]
  have h := norm_sub_sum_iteratedFDeriv_le (f := newtonKernel) (x := x) (y := -y) (n := 2)
    (M := 3 * ‖y‖ ^ 3 / (2 * π * (‖x‖ - ‖y‖) ^ 4))
    (fun t ht => contDiffAt_newtonKernel (add_smul_neg_ne_zero hy ht))
    (fun t ht => by
      have hne := add_smul_neg_ne_zero hy ht
      have hle := sub_le_norm_add_smul_neg x y ht
      show ‖iteratedFDeriv ℝ 3 newtonKernel (x + t • -y) (fun _ => -y)‖ ≤ _
      rw [Real.norm_eq_abs]
      refine (abs_iteratedFDeriv_three_newtonKernel_le hne (-y)).trans ?_
      rw [norm_neg]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd.le hle 4) (by positivity)))
  simp only [smul_eq_mul, ← sub_eq_add_neg, Real.norm_eq_abs] at h
  calc _ ≤ 3 * ‖y‖ ^ 3 / (2 * π * (‖x‖ - ‖y‖) ^ 4) / (2 + 1)! := h
    _ = _ := by
        rw [show (2 + 1)! = 6 from rfl]
        push_cast
        field_simp
        ring

/-- **The quadrupole remainder of the kernel, explicitly**: for `‖y‖ < ‖x‖`,
`|K(x − y) − K(x) − ⟪x,y⟫/(4π‖x‖³) − (3⟪x,y⟫² − ‖x‖²‖y‖²)/(8π‖x‖⁵)| ≤
‖y‖³/(4π(‖x‖ − ‖y‖)⁴)`. -/
theorem abs_newtonKernel_sub_quadrupole_le {x y : E3} (hy : ‖y‖ < ‖x‖) :
    |newtonKernel (x - y) - newtonKernel x - ⟪x, y⟫ / (4 * π * ‖x‖ ^ 3) -
        (3 * ⟪x, y⟫ ^ 2 - ‖x‖ ^ 2 * ‖y‖ ^ 2) / (8 * π * ‖x‖ ^ 5)| ≤
      ‖y‖ ^ 3 / (4 * π * (‖x‖ - ‖y‖) ^ 4) := by
  have hx : x ≠ 0 := norm_pos_iff.mp ((norm_nonneg y).trans_lt hy)
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h := abs_newtonKernel_sub_taylor_two_le hy
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply, fderiv_newtonKernel_neg_apply hx,
    iteratedFDeriv_two_newtonKernel hx, inner_neg_right] at h
  convert h using 2
  norm_num [Nat.factorial]
  field_simp
  ring

/-! ### Separating the orders -/

/-- **Separating the orders**: if `|Σ_{j ≤ k} cⱼ tʲ| ≤ M tᵏ⁺¹` for `0 < t ≤ t₀`, then
`cⱼ = 0` for every `j ≤ k`. -/
theorem eq_zero_of_abs_sum_mul_pow_le {k : ℕ} {c : ℕ → ℝ} {M t₀ : ℝ} (ht₀ : 0 < t₀)
    (h : ∀ t, 0 < t → t ≤ t₀ → |∑ j ∈ Finset.range (k + 1), c j * t ^ j| ≤ M * t ^ (k + 1)) :
    ∀ j ≤ k, c j = 0 := by
  have hc0 : ∀ {k : ℕ} {c : ℕ → ℝ}, (∀ t, 0 < t → t ≤ t₀ →
      |∑ j ∈ Finset.range (k + 1), c j * t ^ j| ≤ M * t ^ (k + 1)) → c 0 = 0 := by
    intro k c h
    have h1 : Tendsto (fun t : ℝ => ∑ j ∈ Finset.range (k + 1), c j * t ^ j) (𝓝[>] 0)
        (𝓝 (c 0)) := by
      have hcont : Continuous fun t : ℝ => ∑ j ∈ Finset.range (k + 1), c j * t ^ j := by
        fun_prop
      have hval : ∑ j ∈ Finset.range (k + 1), c j * (0 : ℝ) ^ j = c 0 := by
        simp [Finset.sum_range_succ']
      have := hcont.tendsto 0
      rw [hval] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun t : ℝ => ∑ j ∈ Finset.range (k + 1), c j * t ^ j) (𝓝[>] 0)
        (𝓝 0) := by
      have hb : Tendsto (fun t : ℝ => M * t ^ (k + 1)) (𝓝[>] 0) (𝓝 0) := by
        have hcont : Continuous fun t : ℝ => M * t ^ (k + 1) := by fun_prop
        simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
      refine squeeze_zero_norm' ?_ hb
      filter_upwards [Ioo_mem_nhdsGT ht₀] with t ht
      rw [Real.norm_eq_abs]
      exact h t ht.1 ht.2.le
    exact tendsto_nhds_unique h1 h2
  induction k generalizing c with
  | zero =>
    intro j hj
    rw [Nat.le_zero.mp hj]
    exact hc0 h
  | succ k ih =>
    have h0 := hc0 h
    have h' : ∀ t, 0 < t → t ≤ t₀ →
        |∑ j ∈ Finset.range (k + 1), c (j + 1) * t ^ j| ≤ M * t ^ (k + 1) := by
      intro t ht ht'
      have h1 := h t ht ht'
      rw [Finset.sum_range_succ', h0, zero_mul, add_zero] at h1
      have heq : ∑ j ∈ Finset.range (k + 1), c (j + 1) * t ^ (j + 1) =
          t * ∑ j ∈ Finset.range (k + 1), c (j + 1) * t ^ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [heq, abs_mul, abs_of_pos ht] at h1
      have h2 : t * |∑ j ∈ Finset.range (k + 1), c (j + 1) * t ^ j| ≤
          t * (M * t ^ (k + 1)) := by
        calc _ ≤ M * t ^ (k + 1 + 1) := h1
          _ = t * (M * t ^ (k + 1)) := by ring
      exact le_of_mul_le_mul_left h2 ht
    intro j hj
    rcases j with _ | j
    · exact h0
    · exact ih h' j (by omega)

end ProjectAinos.SmoothGeometry.Potential
