/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.OneDimension.Motion
public import ProjectAinos.SmoothAlgebra.ImplicitFunctionReal
public import ProjectAinos.Variational.IntervalParameter
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Anharmonic oscillations: the shift of the frequency

Landau–Lifshitz §28. The oscillator `ẍ + ω₀² x = −α x² − β x³` has the
potential `ω₀² x²/2 + α x³/3 + β x⁴/4` (`potential`; the frequency `ω₀` is
written `ν`). Its oscillations of small amplitude are periodic, and the
frequency depends on the amplitude:

`ω = ω₀ + (3β/8ω₀ − 5α²/12ω₀³) ρ² + o(ρ²)`,

where `2ρ` is the distance between the turning points.

* `wellFactor_potential`: `E − U(x) = (x − a)(b − x) U[a, b, x]` with the
  explicit quadratic polynomial `factor`.
* `exists_slope`, `exists_isWell`: for small `ρ > 0` there is a well with the
  turning points `c − ρ` and `c + ρ`, whose centre is `c = ρ² e(ρ²)` with a
  smooth function `e`, `e(0) = −α/3ω₀²`.
-/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory
open scoped Real ContDiff Topology

namespace ProjectAinos.Mechanics.OneDim.Anharmonic

open SmoothAlgebra

variable {ν α β : ℝ}

/-- The potential `ν² x²/2 + α x³/3 + β x⁴/4` of the anharmonic oscillator. -/
def potential (ν α β x : ℝ) : ℝ := ν ^ 2 * x ^ 2 / 2 + α * x ^ 3 / 3 + β * x ^ 4 / 4

/-- The first divided difference of the potential. -/
def firstDifference (ν α β p q : ℝ) : ℝ :=
  ν ^ 2 * (p + q) / 2 + α * (p ^ 2 + p * q + q ^ 2) / 3 +
    β * (p ^ 3 + p ^ 2 * q + p * q ^ 2 + q ^ 3) / 4

/-- The second divided difference of the potential. -/
def factor (ν α β a b x : ℝ) : ℝ :=
  ν ^ 2 / 2 + α / 3 * (a + b + x) + β / 4 * (a ^ 2 + b ^ 2 + x ^ 2 + a * b + a * x + b * x)

theorem contDiff_potential (ν α β : ℝ) : ContDiff ℝ ∞ (potential ν α β) := by
  unfold potential
  fun_prop

theorem hasDerivAt_potential (ν α β x : ℝ) :
    HasDerivAt (potential ν α β) (ν ^ 2 * x + α * x ^ 2 + β * x ^ 3) x := by
  have h := ((((hasDerivAt_pow 2 x).const_mul (ν ^ 2)).div_const 2).add
    (((hasDerivAt_pow 3 x).const_mul α).div_const 3)).add
    (((hasDerivAt_pow 4 x).const_mul β).div_const 4)
  refine h.congr_deriv ?_
  norm_num
  ring

theorem deriv_potential (ν α β x : ℝ) :
    deriv (potential ν α β) x = ν ^ 2 * x + α * x ^ 2 + β * x ^ 3 :=
  (hasDerivAt_potential ν α β x).deriv

theorem potential_sub (ν α β p q : ℝ) :
    potential ν α β p - potential ν α β q = (p - q) * firstDifference ν α β p q := by
  unfold potential firstDifference
  ring

theorem dividedDifference_potential (ν α β p q : ℝ) :
    dividedDifference (potential ν α β) (p, q) = firstDifference ν α β p q := by
  by_cases h : p = q
  · subst h
    rw [dividedDifference_self, deriv_potential]
    unfold firstDifference
    ring
  · have h1 := sub_eq_mul_dividedDifference ((contDiff_potential ν α β).of_le (by simp)) p q
    rw [potential_sub] at h1
    exact (mul_left_cancel₀ (sub_ne_zero.mpr h) h1).symm

/-- The factor of a well of the anharmonic potential is an explicit quadratic
polynomial. -/
theorem wellFactor_potential (ν α β a b : ℝ) :
    wellFactor (potential ν α β) a b = factor ν α β a b := by
  have hU := contDiff_potential ν α β
  have hc1 : Continuous (wellFactor (potential ν α β) a b) :=
    (contDiff_wellFactor_right hU a b).continuous
  have hc2 : Continuous (factor ν α β a b) := by
    unfold factor
    fun_prop
  refine Continuous.ext_on (dense_compl_singleton a) hc1 hc2 fun x hx => ?_
  have hxa : x - a ≠ 0 := sub_ne_zero.mpr hx
  have h := dividedDifference_sub hU a b x
  rw [dividedDifference_potential, dividedDifference_potential] at h
  have h2 : firstDifference ν α β b x - firstDifference ν α β b a =
      (x - a) * factor ν α β a b x := by
    unfold firstDifference factor
    ring
  rw [h2] at h
  exact (mul_left_cancel₀ hxa h).symm

/-! ### The centre of a small oscillation -/

/-- The equation of the centre `c = s e` of the oscillation with `ρ² = s`:
`e (ν² + α s e + β s² e² + β s) + α/3 = 0`. -/
def slopeEquation (ν α β : ℝ) (v : ℝ × ℝ) : ℝ :=
  v.2 * (ν ^ 2 + α * v.1 * v.2 + β * v.1 ^ 2 * v.2 ^ 2 + β * v.1) + α / 3

/-- The two points `c ± ρ` with `c = ρ² e` are on the same level when `e`
solves the equation of the centre. -/
theorem potential_centre (ν α β ρ e : ℝ) (h : slopeEquation ν α β (ρ ^ 2, e) = 0) :
    potential ν α β (ρ ^ 2 * e - ρ) = potential ν α β (ρ ^ 2 * e + ρ) := by
  have h1 : potential ν α β (ρ ^ 2 * e + ρ) - potential ν α β (ρ ^ 2 * e - ρ) =
      2 * ρ * (ρ ^ 2 * slopeEquation ν α β (ρ ^ 2, e)) := by
    unfold potential slopeEquation
    ring
  rw [h, mul_zero, mul_zero] at h1
  linarith

/-- The centre of the small oscillations: a smooth solution `e(s)` of the
equation of the centre near `s = 0`, with `e(0) = −α/3ν²`. -/
theorem exists_slope (hν : 0 < ν) (α β : ℝ) :
    ∃ (J : Set ℝ) (e : ℝ → ℝ), IsOpen J ∧ (0 : ℝ) ∈ J ∧ e 0 = -α / (3 * ν ^ 2) ∧
      ContDiffOn ℝ ∞ e J ∧ ∀ s ∈ J, slopeEquation ν α β (s, e s) = 0 := by
  have hΦ : ContDiff ℝ ∞ (slopeEquation ν α β) := by
    unfold slopeEquation
    fun_prop
  have hd : ∀ v : ℝ × ℝ, HasDerivAt (fun y => slopeEquation ν α β (v.1, y))
      (ν ^ 2 + 2 * α * v.1 * v.2 + 3 * β * v.1 ^ 2 * v.2 ^ 2 + β * v.1) v.2 := by
    intro v
    have h1 : HasDerivAt (fun y : ℝ => ν ^ 2 + α * v.1 * y + β * v.1 ^ 2 * y ^ 2 + β * v.1)
        (α * v.1 + β * v.1 ^ 2 * (2 * v.2)) v.2 := by
      have h := ((((hasDerivAt_id v.2).const_mul (α * v.1)).const_add (ν ^ 2)).add
        ((hasDerivAt_pow 2 v.2).const_mul (β * v.1 ^ 2))).add_const (β * v.1)
      refine h.congr_deriv ?_
      norm_num
    have h2 := ((hasDerivAt_id v.2).mul h1).add_const (α / 3)
    refine h2.congr_deriv ?_
    simp only [id_eq]
    ring
  have hc : Continuous fun v : ℝ × ℝ =>
      ν ^ 2 + 2 * α * v.1 * v.2 + 3 * β * v.1 ^ 2 * v.2 ^ 2 + β * v.1 := by fun_prop
  have hu : ν ^ 2 + 2 * α * ((0 : ℝ), -α / (3 * ν ^ 2)).1 * ((0 : ℝ), -α / (3 * ν ^ 2)).2 +
      3 * β * ((0 : ℝ), -α / (3 * ν ^ 2)).1 ^ 2 * ((0 : ℝ), -α / (3 * ν ^ 2)).2 ^ 2 +
      β * ((0 : ℝ), -α / (3 * ν ^ 2)).1 ≠ 0 := by
    have h0 : ν ^ 2 + 2 * α * ((0 : ℝ), -α / (3 * ν ^ 2)).1 * ((0 : ℝ), -α / (3 * ν ^ 2)).2 +
        3 * β * ((0 : ℝ), -α / (3 * ν ^ 2)).1 ^ 2 * ((0 : ℝ), -α / (3 * ν ^ 2)).2 ^ 2 +
        β * ((0 : ℝ), -α / (3 * ν ^ 2)).1 = ν ^ 2 := by
      simp
    rw [h0]
    exact (pow_pos hν 2).ne'
  obtain ⟨J, e, hJ, h0, he0, he, hsol⟩ := exists_contDiffOn_implicitFunction_real hΦ hd hc hu
  refine ⟨J, e, hJ, h0, he0, he, fun s hs => ?_⟩
  rw [(hsol s hs).2]
  unfold slopeEquation
  field_simp
  ring

/-- For small `ρ > 0` the points `ρ² e(ρ²) ∓ ρ` are the turning points of a
well of the anharmonic potential. -/
theorem exists_isWell (hν : 0 < ν) (α β : ℝ) {J : Set ℝ} {e : ℝ → ℝ} (hJ : IsOpen J)
    (h0 : (0 : ℝ) ∈ J) (he : ContDiffOn ℝ ∞ e J)
    (hsol : ∀ s ∈ J, slopeEquation ν α β (s, e s) = 0) :
    ∃ ρ₀ > 0, ∀ ρ ∈ Ioo 0 ρ₀, ρ ^ 2 ∈ J ∧
      IsWell (potential ν α β) (potential ν α β (ρ ^ 2 * e (ρ ^ 2) + ρ))
        (ρ ^ 2 * e (ρ ^ 2) - ρ) (ρ ^ 2 * e (ρ ^ 2) + ρ) := by
  have hec : ContinuousAt e 0 := he.continuousOn.continuousAt (hJ.mem_nhds h0)
  have hsq : ContinuousAt (fun ρ : ℝ => ρ ^ 2) 0 := (continuous_pow 2).continuousAt
  have hsq0 : (fun ρ : ℝ => ρ ^ 2) 0 = 0 := by simp
  have hprod : ContinuousAt (fun ρ : ℝ => ρ * e (ρ ^ 2)) 0 := by
    have h2 : ContinuousAt e ((fun ρ : ℝ => ρ ^ 2) 0) := by rw [hsq0]; exact hec
    exact continuousAt_id.mul (ContinuousAt.comp (g := e) (f := fun ρ : ℝ => ρ ^ 2) h2 hsq)
  have E1 : ∀ᶠ ρ : ℝ in 𝓝 0, |ρ * e (ρ ^ 2)| < 1 / 2 := by
    have h := hprod.eventually (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [h] with ρ hρ
    simpa [Real.dist_eq] using hρ
  have E2 : ∀ᶠ ρ : ℝ in 𝓝 0, ρ ^ 2 ∈ J :=
    hsq.eventually (hJ.mem_nhds (by rw [hsq0]; exact h0))
  have hFc : Continuous fun q : ℝ × ℝ × ℝ => factor ν α β q.1 q.2.1 q.2.2 := by
    unfold factor
    fun_prop
  have hF0 : 0 < factor ν α β (0 : ℝ × ℝ × ℝ).1 (0 : ℝ × ℝ × ℝ).2.1 (0 : ℝ × ℝ × ℝ).2.2 := by
    simp only [factor, Prod.fst_zero, Prod.snd_zero]
    have := pow_pos hν 2
    norm_num
    linarith
  obtain ⟨δ, hδ, hFδ⟩ :=
    Metric.eventually_nhds_iff.mp (hFc.continuousAt.eventually (lt_mem_nhds hF0))
  have hgc : Continuous fun y : ℝ => ν ^ 2 + α * y + β * y ^ 2 := by fun_prop
  have hg0 : 0 < ν ^ 2 + α * 0 + β * (0 : ℝ) ^ 2 := by
    have := pow_pos hν 2
    norm_num
    linarith
  obtain ⟨δ', hδ', hgδ⟩ :=
    Metric.eventually_nhds_iff.mp (hgc.continuousAt.eventually (lt_mem_nhds hg0))
  have E3 : ∀ᶠ ρ : ℝ in 𝓝 0, |ρ| < δ / 2 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (half_pos hδ)] with ρ hρ
    simpa [Real.dist_eq] using hρ
  have E4 : ∀ᶠ ρ : ℝ in 𝓝 0, |ρ| < δ' / 2 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (half_pos hδ')] with ρ hρ
    simpa [Real.dist_eq] using hρ
  obtain ⟨ρ₀, hρ₀, hall⟩ := Metric.eventually_nhds_iff.mp (E1.and (E2.and (E3.and E4)))
  refine ⟨ρ₀, hρ₀, fun ρ hρ => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ :=
    hall (show dist ρ 0 < ρ₀ by rw [Real.dist_eq, sub_zero, abs_of_pos hρ.1]; exact hρ.2)
  have hρpos := hρ.1
  have hsol' := hsol _ h2
  obtain ⟨c, hc⟩ : ∃ c, c = ρ ^ 2 * e (ρ ^ 2) := ⟨_, rfl⟩
  have hcabs : |c| < ρ / 2 := by
    have hcr : c = ρ * (ρ * e (ρ ^ 2)) := by rw [hc]; ring
    rw [hcr, abs_mul, abs_of_pos hρpos]
    nlinarith [abs_nonneg (ρ * e (ρ ^ 2))]
  have hcl := (abs_lt.mp hcabs).1
  have hcu := (abs_lt.mp hcabs).2
  have h3' := abs_lt.mp h3
  have h4' := abs_lt.mp h4
  have hdist : ∀ y : ℝ, |y| ≤ 3 * ρ / 2 → dist y 0 < δ' := fun y hy => by
    rw [Real.dist_eq, sub_zero]
    linarith
  have hga : 0 < ν ^ 2 + α * (c - ρ) + β * (c - ρ) ^ 2 :=
    hgδ (hdist _ (abs_le.mpr ⟨by linarith, by linarith⟩))
  have hgb : 0 < ν ^ 2 + α * (c + ρ) + β * (c + ρ) ^ 2 :=
    hgδ (hdist _ (abs_le.mpr ⟨by linarith, by linarith⟩))
  rw [← hc]
  refine ⟨h2, isWell_of_wellFactor_pos (contDiff_potential ν α β) (by linarith)
    (by rw [hc]; exact potential_centre ν α β ρ _ hsol') rfl ?_ ?_ ?_⟩
  · rw [deriv_potential]
    have hfac : ν ^ 2 * (c - ρ) + α * (c - ρ) ^ 2 + β * (c - ρ) ^ 3 =
        (c - ρ) * (ν ^ 2 + α * (c - ρ) + β * (c - ρ) ^ 2) := by ring
    rw [hfac]
    exact mul_neg_of_neg_of_pos (by linarith) hga
  · rw [deriv_potential]
    have hfac : ν ^ 2 * (c + ρ) + α * (c + ρ) ^ 2 + β * (c + ρ) ^ 3 =
        (c + ρ) * (ν ^ 2 + α * (c + ρ) + β * (c + ρ) ^ 2) := by ring
    rw [hfac]
    exact mul_pos (by linarith) hgb
  · intro x hx
    rw [wellFactor_potential]
    have hd : dist ((c - ρ, c + ρ, x) : ℝ × ℝ × ℝ) 0 < δ := by
      rw [Prod.dist_eq, Prod.dist_eq, max_lt_iff, max_lt_iff, Real.dist_eq, Real.dist_eq,
        Real.dist_eq]
      simp only [Prod.fst_zero, Prod.snd_zero, sub_zero]
      refine ⟨?_, ?_, ?_⟩
      · rw [abs_lt]
        constructor <;> linarith
      · rw [abs_lt]
        constructor <;> linarith
      · rw [abs_lt]
        constructor <;> linarith [hx.1, hx.2]
    exact hFδ hd

/-! ### The period as a function of the squared amplitude -/

/-- `1/√(P − r) + 1/√(P + r)` as a function of `P` and `R = r²`, which is
smooth where `P > 0` and `R < P²`. -/
def symRoot (P R : ℝ) : ℝ := √(2 * P + 2 * √(P ^ 2 - R)) / √(P ^ 2 - R)

theorem inv_sqrt_add_inv_sqrt {P r : ℝ} (h1 : 0 < P - r) (h2 : 0 < P + r) :
    1 / √(P - r) + 1 / √(P + r) = symRoot P (r ^ 2) := by
  have hu : 0 < √(P - r) := Real.sqrt_pos.mpr h1
  have hw : 0 < √(P + r) := Real.sqrt_pos.mpr h2
  have hu2 : √(P - r) ^ 2 = P - r := Real.sq_sqrt h1.le
  have hw2 : √(P + r) ^ 2 = P + r := Real.sq_sqrt h2.le
  have hprod : √(P ^ 2 - r ^ 2) = √(P - r) * √(P + r) := by
    rw [← Real.sqrt_mul h1.le]
    congr 1
    ring
  have hsum : √(2 * P + 2 * (√(P - r) * √(P + r))) = √(P - r) + √(P + r) := by
    have e : 2 * P + 2 * (√(P - r) * √(P + r)) = (√(P - r) + √(P + r)) ^ 2 := by
      rw [add_sq, hu2, hw2]
      ring
    rw [e, Real.sqrt_sq (add_pos hu hw).le]
  rw [symRoot, hprod, hsum]
  field_simp
  ring

/-- The derivative of `symRoot` along a curve through a point `(ν², 0)`. -/
theorem hasDerivAt_symRoot (hν : 0 < ν) {P R : ℝ → ℝ} {p₁ r₁ s₀ : ℝ}
    (hP : HasDerivAt P p₁ s₀) (hR : HasDerivAt R r₁ s₀) (hP0 : P s₀ = ν ^ 2) (hR0 : R s₀ = 0) :
    HasDerivAt (fun s => symRoot (P s) (R s)) (-p₁ / ν ^ 3 + 3 * r₁ / (4 * ν ^ 5)) s₀ := by
  have hQ0 : P s₀ ^ 2 - R s₀ = (ν ^ 2) ^ 2 := by rw [hP0, hR0, sub_zero]
  have hS0 : √(P s₀ ^ 2 - R s₀) = ν ^ 2 := by rw [hQ0, Real.sqrt_sq (sq_nonneg ν)]
  have hQ : HasDerivAt (fun s => P s ^ 2 - R s) (2 * P s₀ * p₁ - r₁) s₀ := by
    refine ((hP.pow 2).sub hR).congr_deriv ?_
    norm_num
  have hS := hQ.sqrt (by rw [hQ0]; positivity)
  have hN0 : 2 * P s₀ + 2 * √(P s₀ ^ 2 - R s₀) = (2 * ν) ^ 2 := by
    rw [hS0, hP0]
    ring
  have hM : HasDerivAt (fun s => 2 * P s + 2 * √(P s ^ 2 - R s))
      (2 * p₁ + 2 * ((2 * P s₀ * p₁ - r₁) / (2 * √(P s₀ ^ 2 - R s₀)))) s₀ :=
    (hP.const_mul 2).add (hS.const_mul 2)
  have hN := hM.sqrt (by rw [hN0]; positivity)
  have hNv : √(2 * P s₀ + 2 * √(P s₀ ^ 2 - R s₀)) = 2 * ν := by
    rw [hN0, Real.sqrt_sq (by positivity)]
  have hG : HasDerivAt (fun s => symRoot (P s) (R s))
      (((2 * p₁ + 2 * ((2 * P s₀ * p₁ - r₁) / (2 * √(P s₀ ^ 2 - R s₀)))) /
          (2 * √(2 * P s₀ + 2 * √(P s₀ ^ 2 - R s₀))) * √(P s₀ ^ 2 - R s₀) -
        √(2 * P s₀ + 2 * √(P s₀ ^ 2 - R s₀)) *
          ((2 * P s₀ * p₁ - r₁) / (2 * √(P s₀ ^ 2 - R s₀)))) / √(P s₀ ^ 2 - R s₀) ^ 2) s₀ :=
    hN.div hS (by rw [hS0]; positivity)
  refine hG.congr_deriv ?_
  rw [hNv, hS0, hP0]
  field_simp
  ring

/-- The function `P(s, θ)` of the symmetrized rate. -/
def kernelP (ν α β : ℝ) (e : ℝ → ℝ) (s θ : ℝ) : ℝ :=
  ν ^ 2 + 2 * α * (s * e s) + 3 * β * (s * e s) ^ 2 + β / 2 * s * (1 + Real.cos θ ^ 2)

/-- The coefficient `B(s)` of the odd part of the rate. -/
def kernelB (α β : ℝ) (e : ℝ → ℝ) (s : ℝ) : ℝ := 2 * α / 3 + 2 * β * (s * e s)

/-- The rate at the angle `θ` plus the rate at `θ + π`, as a function of the
squared half-width `s` and of `θ`. -/
def kernel (ν α β : ℝ) (e : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  symRoot (kernelP ν α β e p.1 p.2) (p.1 * kernelB α β e p.1 ^ 2 * Real.cos p.2 ^ 2)

/-- The period as a function of the squared half-width of the oscillation. -/
def periodFunction (ν α β : ℝ) (e : ℝ → ℝ) (s : ℝ) : ℝ :=
  (∫ θ in (0 : ℝ)..2 * π, kernel ν α β e (s, θ)) / 2

theorem two_mul_factor (ν α β : ℝ) (e : ℝ → ℝ) (ρ θ : ℝ) :
    2 * factor ν α β (ρ ^ 2 * e (ρ ^ 2) - ρ) (ρ ^ 2 * e (ρ ^ 2) + ρ)
        (orbitPosition (ρ ^ 2 * e (ρ ^ 2) - ρ) (ρ ^ 2 * e (ρ ^ 2) + ρ) θ) =
      kernelP ν α β e (ρ ^ 2) θ - ρ * kernelB α β e (ρ ^ 2) * Real.cos θ := by
  unfold factor orbitPosition kernelP kernelB
  ring

theorem orbitRate_eq {a b : ℝ} (θ : ℝ)
    (hpos : 0 < factor ν α β a b (orbitPosition a b θ)) :
    orbitRate 1 (potential ν α β) a b θ =
      1 / √(2 * factor ν α β a b (orbitPosition a b θ)) := by
  rw [orbitRate, wellFactor_potential, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    show (1 : ℝ) / 2 = 2⁻¹ by norm_num, Real.sqrt_inv]
  have h2 : 0 < √(2 : ℝ) := Real.sqrt_pos.mpr two_pos
  have hF : 0 < √(factor ν α β a b (orbitPosition a b θ)) := Real.sqrt_pos.mpr hpos
  field_simp

/-- The period of the oscillation of half-width `ρ` is the period function at
`ρ²`: the rates at `θ` and at `θ + π` are added. -/
theorem orbitPeriod_eq_periodFunction (ν α β : ℝ) (e : ℝ → ℝ) {ρ E : ℝ}
    (h : IsWell (potential ν α β) E (ρ ^ 2 * e (ρ ^ 2) - ρ) (ρ ^ 2 * e (ρ ^ 2) + ρ)) :
    orbitPeriod 1 (potential ν α β) (ρ ^ 2 * e (ρ ^ 2) - ρ) (ρ ^ 2 * e (ρ ^ 2) + ρ) =
      periodFunction ν α β e (ρ ^ 2) := by
  have hU : ContDiff ℝ ∞ (potential ν α β) := contDiff_potential ν α β
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, f = orbitRate 1 (potential ν α β)
      (ρ ^ 2 * e (ρ ^ 2) - ρ) (ρ ^ 2 * e (ρ ^ 2) + ρ) := ⟨_, rfl⟩
  have hfac : ∀ θ, 0 < factor ν α β (ρ ^ 2 * e (ρ ^ 2) - ρ) (ρ ^ 2 * e (ρ ^ 2) + ρ)
      (orbitPosition (ρ ^ 2 * e (ρ ^ 2) - ρ) (ρ ^ 2 * e (ρ ^ 2) + ρ) θ) := by
    intro θ
    have h1 := h.wellFactor_orbitPosition_pos hU θ
    rwa [wellFactor_potential] at h1
  have hpos : ∀ θ, 0 < kernelP ν α β e (ρ ^ 2) θ - ρ * kernelB α β e (ρ ^ 2) * Real.cos θ := by
    intro θ
    have h1 := hfac θ
    have h2 := two_mul_factor ν α β e ρ θ
    linarith
  have hrate : ∀ θ, f θ =
      1 / √(kernelP ν α β e (ρ ^ 2) θ - ρ * kernelB α β e (ρ ^ 2) * Real.cos θ) := by
    intro θ
    rw [hf, orbitRate_eq θ (hfac θ), two_mul_factor]
  have hP : ∀ θ, kernelP ν α β e (ρ ^ 2) (θ + π) = kernelP ν α β e (ρ ^ 2) θ := by
    intro θ
    simp [kernelP, Real.cos_add_pi]
  have hsum : ∀ θ, f θ + f (θ + π) = kernel ν α β e (ρ ^ 2, θ) := by
    intro θ
    have h1 := hpos θ
    have h2 := hpos (θ + π)
    rw [hP, Real.cos_add_pi] at h2
    have h3 := inv_sqrt_add_inv_sqrt (P := kernelP ν α β e (ρ ^ 2) θ)
      (r := ρ * kernelB α β e (ρ ^ 2) * Real.cos θ) h1 (by linarith)
    rw [hrate, hrate, hP, Real.cos_add_pi, kernel,
      show kernelP ν α β e (ρ ^ 2) θ - ρ * kernelB α β e (ρ ^ 2) * -Real.cos θ =
        kernelP ν α β e (ρ ^ 2) θ + ρ * kernelB α β e (ρ ^ 2) * Real.cos θ by ring, h3]
    congr 1
    ring
  have hcont : Continuous f := by
    rw [hf]
    have hWc : Continuous fun θ => wellFactor (potential ν α β) (ρ ^ 2 * e (ρ ^ 2) - ρ)
        (ρ ^ 2 * e (ρ ^ 2) + ρ)
        (orbitPosition (ρ ^ 2 * e (ρ ^ 2) - ρ) (ρ ^ 2 * e (ρ ^ 2) + ρ) θ) :=
      (contDiff_wellFactor_right hU _ _).continuous.comp (contDiff_orbitPosition _ _).continuous
    exact continuous_const.div (Real.continuous_sqrt.comp hWc) fun θ =>
      (Real.sqrt_pos.mpr (h.wellFactor_orbitPosition_pos hU θ)).ne'
  have hper : Function.Periodic f (2 * π) := by
    intro θ
    rw [hf]
    exact orbitRate_add_two_pi 1 _ _ _ θ
  have hshift : ∫ θ in (0 : ℝ)..2 * π, f (θ + π) = ∫ θ in (0 : ℝ)..2 * π, f θ := by
    rw [intervalIntegral.integral_comp_add_right (f := f), zero_add, add_comm (2 * π) π,
      hper.intervalIntegral_add_eq π 0, zero_add]
  have hker : ∫ θ in (0 : ℝ)..2 * π, kernel ν α β e (ρ ^ 2, θ) =
      2 * ∫ θ in (0 : ℝ)..2 * π, f θ := by
    have hg : Continuous fun θ => f (θ + π) := hcont.comp (continuous_id.add continuous_const)
    simp_rw [← hsum]
    rw [intervalIntegral.integral_add (f := f) (g := fun θ => f (θ + π))
      (hcont.intervalIntegrable _ _) (hg.intervalIntegrable _ _), hshift]
    ring
  rw [periodFunction, orbitPeriod, ← hf, hker]
  ring

theorem kernel_zero (hν : 0 < ν) (α β : ℝ) (e : ℝ → ℝ) (θ : ℝ) :
    kernel ν α β e (0, θ) = 2 / ν := by
  have h1 : √((ν ^ 2) ^ 2) = ν ^ 2 := Real.sqrt_sq (sq_nonneg ν)
  have h2 : √(2 * ν ^ 2 + 2 * ν ^ 2) = 2 * ν := by
    rw [show 2 * ν ^ 2 + 2 * ν ^ 2 = (2 * ν) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  simp only [kernel, kernelP, symRoot, zero_mul, mul_zero, add_zero, sub_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  rw [h1, h2]
  field_simp

theorem periodFunction_zero (hν : 0 < ν) (α β : ℝ) (e : ℝ → ℝ) :
    periodFunction ν α β e 0 = 2 * π / ν := by
  simp only [periodFunction, kernel_zero hν]
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp

/-- The derivative of the rate kernel in the squared half-width, at zero. -/
def kernelDeriv (ν α β θ : ℝ) : ℝ :=
  -(2 * α * (-α / (3 * ν ^ 2)) + β / 2 * (1 + Real.cos θ ^ 2)) / ν ^ 3 +
    3 * ((2 * α / 3) ^ 2 * Real.cos θ ^ 2) / (4 * ν ^ 5)

theorem hasDerivAt_kernel (hν : 0 < ν) (α β : ℝ) {e : ℝ → ℝ} {e' : ℝ}
    (he : HasDerivAt e e' 0) (he0 : e 0 = -α / (3 * ν ^ 2)) (θ : ℝ) :
    HasDerivAt (fun s => kernel ν α β e (s, θ)) (kernelDeriv ν α β θ) 0 := by
  have hse : HasDerivAt (fun s => s * e s) (e 0) 0 := by
    refine ((hasDerivAt_id (0 : ℝ)).mul he).congr_deriv ?_
    simp
  have hP : HasDerivAt (fun s => kernelP ν α β e s θ)
      (2 * α * (-α / (3 * ν ^ 2)) + β / 2 * (1 + Real.cos θ ^ 2)) 0 := by
    have h1 := ((((hse.const_mul (2 * α)).const_add (ν ^ 2)).add
      ((hse.pow 2).const_mul (3 * β))).add
      (((hasDerivAt_id (0 : ℝ)).const_mul (β / 2)).mul_const (1 + Real.cos θ ^ 2)))
    refine h1.congr_deriv ?_
    rw [he0]
    simp
  have hR : HasDerivAt (fun s => s * kernelB α β e s ^ 2 * Real.cos θ ^ 2)
      ((2 * α / 3) ^ 2 * Real.cos θ ^ 2) 0 := by
    have hB : HasDerivAt (fun s => kernelB α β e s) (2 * β * e 0) 0 :=
      (hse.const_mul (2 * β)).const_add (2 * α / 3)
    have h1 := ((hasDerivAt_id (0 : ℝ)).mul (hB.pow 2)).mul_const (Real.cos θ ^ 2)
    refine h1.congr_deriv ?_
    simp [kernelB]
  exact hasDerivAt_symRoot hν hP hR (by simp [kernelP]) (by simp)

theorem contDiffAt_symRoot {P R : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (hP : ContDiffAt ℝ 1 P x)
    (hR : ContDiffAt ℝ 1 R x) (h1 : 0 < P x) (h2 : R x < P x ^ 2) :
    ContDiffAt ℝ 1 (fun p => symRoot (P p) (R p)) x := by
  have hQ : ContDiffAt ℝ 1 (fun p => P p ^ 2 - R p) x := (hP.pow 2).sub hR
  have hS : ContDiffAt ℝ 1 (fun p => √(P p ^ 2 - R p)) x := hQ.sqrt (by linarith)
  have hSpos : 0 < √(P x ^ 2 - R x) := Real.sqrt_pos.mpr (by linarith)
  have hM : ContDiffAt ℝ 1 (fun p => 2 * P p + 2 * √(P p ^ 2 - R p)) x :=
    (contDiffAt_const.mul hP).add (contDiffAt_const.mul hS)
  have hN : ContDiffAt ℝ 1 (fun p => √(2 * P p + 2 * √(P p ^ 2 - R p))) x :=
    hM.sqrt (by positivity)
  exact hN.div hS hSpos.ne'

theorem contDiffAt_kernel (hν : 0 < ν) (α β : ℝ) {e : ℝ → ℝ} (he : ContDiffAt ℝ 1 e 0)
    (θ : ℝ) : ContDiffAt ℝ 1 (kernel ν α β e) (0, θ) := by
  have he1 : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => e p.1) (0, θ) :=
    ContDiffAt.comp (g := e) (f := Prod.fst) (0, θ) he contDiffAt_fst
  have hse : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => p.1 * e p.1) (0, θ) := contDiffAt_fst.mul he1
  have hcos : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => Real.cos p.2) (0, θ) :=
    ContDiffAt.comp (g := Real.cos) (f := Prod.snd) (0, θ) Real.contDiff_cos.contDiffAt
      contDiffAt_snd
  have hP : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => kernelP ν α β e p.1 p.2) (0, θ) :=
    (((contDiffAt_const.add (contDiffAt_const.mul hse)).add
      (contDiffAt_const.mul (hse.pow 2))).add
      ((contDiffAt_const.mul contDiffAt_fst).mul (contDiffAt_const.add (hcos.pow 2))))
  have hR : ContDiffAt ℝ 1
      (fun p : ℝ × ℝ => p.1 * kernelB α β e p.1 ^ 2 * Real.cos p.2 ^ 2) (0, θ) :=
    (contDiffAt_fst.mul ((contDiffAt_const.add (contDiffAt_const.mul hse)).pow 2)).mul
      (hcos.pow 2)
  have hν2 : 0 < ν ^ 2 := pow_pos hν 2
  exact contDiffAt_symRoot hP hR (by simpa [kernelP] using hν2)
    (by simpa [kernelP] using pow_pos hν2 2)

theorem integral_kernelDeriv (hν : 0 < ν) (α β : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, kernelDeriv ν α β θ =
      5 * π * α ^ 2 / (3 * ν ^ 5) - 3 * π * β / (2 * ν ^ 3) := by
  have hform : ∀ θ, kernelDeriv ν α β θ =
      (2 * α ^ 2 / (3 * ν ^ 5) - β / (2 * ν ^ 3)) +
        (α ^ 2 / (3 * ν ^ 5) - β / (2 * ν ^ 3)) * Real.cos θ ^ 2 := by
    intro θ
    unfold kernelDeriv
    field_simp
    ring
  simp_rw [hform]
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_cos_sq]
  simp only [sub_zero, smul_eq_mul, Real.cos_two_pi, Real.sin_two_pi, Real.cos_zero,
    Real.sin_zero, mul_zero]
  field_simp
  ring

/-- The derivative of the period in the squared half-width, at zero. -/
theorem hasDerivAt_periodFunction (hν : 0 < ν) (α β : ℝ) {e : ℝ → ℝ}
    (he : ContDiffAt ℝ 1 e 0) (he0 : e 0 = -α / (3 * ν ^ 2)) :
    HasDerivAt (periodFunction ν α β e)
      (5 * π * α ^ 2 / (6 * ν ^ 5) - 3 * π * β / (4 * ν ^ 3)) 0 := by
  have hd := (he.differentiableAt one_ne_zero).hasDerivAt
  have h1 := Variational.hasDerivAt_intervalIntegral_of_contDiffAt (F := kernel ν α β e)
    (D := kernelDeriv ν α β) (ε₀ := 0) (a := 0) (b := 2 * π)
    (fun θ _ => contDiffAt_kernel hν α β he θ) (fun θ _ => hasDerivAt_kernel hν α β hd he0 θ)
  rw [integral_kernelDeriv hν] at h1
  refine (h1.div_const 2).congr_deriv ?_
  ring

/-- The derivative of the frequency in the squared half-width, at zero. -/
theorem hasDerivAt_frequency (hν : 0 < ν) (α β : ℝ) {e : ℝ → ℝ}
    (he : ContDiffAt ℝ 1 e 0) (he0 : e 0 = -α / (3 * ν ^ 2)) :
    HasDerivAt (fun s => 2 * π / periodFunction ν α β e s)
      (3 * β / (8 * ν) - 5 * α ^ 2 / (12 * ν ^ 3)) 0 := by
  have hT := hasDerivAt_periodFunction hν α β he he0
  have hT0 := periodFunction_zero hν α β e
  have hne : periodFunction ν α β e 0 ≠ 0 := by
    rw [hT0]
    positivity
  refine ((hasDerivAt_const (0 : ℝ) (2 * π)).div hT hne).congr_deriv ?_
  rw [hT0]
  have hπ := Real.pi_ne_zero
  field_simp
  ring

/-- Landau–Lifshitz §28: the oscillation of half-width `ρ` in the potential
`ν²x²/2 + αx³/3 + βx⁴/4` exists for small `ρ`, its centre is
`−αρ²/(3ν²)` to leading order, and its frequency `2π/T` is
`ν + (3β/(8ν) − 5α²/(12ν³))ρ²` to leading order. -/
theorem exists_tendsto_frequency (hν : 0 < ν) (α β : ℝ) :
    ∃ (c : ℝ → ℝ) (ρ₀ : ℝ), 0 < ρ₀ ∧
      (∀ ρ ∈ Ioo 0 ρ₀,
        IsWell (potential ν α β) (potential ν α β (c ρ + ρ)) (c ρ - ρ) (c ρ + ρ)) ∧
      Tendsto (fun ρ => c ρ / ρ ^ 2) (𝓝[>] 0) (𝓝 (-α / (3 * ν ^ 2))) ∧
      Tendsto
        (fun ρ => (2 * π / orbitPeriod 1 (potential ν α β) (c ρ - ρ) (c ρ + ρ) - ν) / ρ ^ 2)
        (𝓝[>] 0) (𝓝 (3 * β / (8 * ν) - 5 * α ^ 2 / (12 * ν ^ 3))) := by
  obtain ⟨J, e, hJ, h0, he0, he, hsol⟩ := exists_slope hν α β
  obtain ⟨ρ₀, hρ₀, hwell⟩ := exists_isWell hν α β hJ h0 he hsol
  have heat : ContDiffAt ℝ 1 e 0 := (he.contDiffAt (hJ.mem_nhds h0)).of_le (by simp)
  have hsq : Tendsto (fun ρ : ℝ => ρ ^ 2) (𝓝[>] 0) (𝓝 0) :=
    ((continuous_pow 2).tendsto' (0 : ℝ) 0 (by simp)).mono_left nhdsWithin_le_nhds
  have hsq' : Tendsto (fun ρ : ℝ => ρ ^ 2) (𝓝[>] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hsq, by
      filter_upwards [self_mem_nhdsWithin] with ρ hρ
      exact pow_ne_zero 2 (ne_of_gt hρ)⟩
  refine ⟨fun ρ => ρ ^ 2 * e (ρ ^ 2), ρ₀, hρ₀, fun ρ hρ => (hwell ρ hρ).2, ?_, ?_⟩
  · have h1 : Tendsto (fun ρ : ℝ => e (ρ ^ 2)) (𝓝[>] 0) (𝓝 (e 0)) :=
      heat.continuousAt.tendsto.comp hsq
    rw [he0] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    have hρ' : ρ ≠ 0 := ne_of_gt hρ
    field_simp
  · have h1 := (hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_frequency hν α β heat he0)).comp hsq'
    refine h1.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hρ₀] with ρ hρ
    have hρ' : ρ ≠ 0 := ne_of_gt hρ.1
    have hπ := Real.pi_ne_zero
    simp only [Function.comp_apply, slope, vsub_eq_sub, sub_zero, smul_eq_mul]
    rw [orbitPeriod_eq_periodFunction ν α β e (hwell ρ hρ).2, periodFunction_zero hν]
    field_simp

end ProjectAinos.Mechanics.OneDim.Anharmonic
