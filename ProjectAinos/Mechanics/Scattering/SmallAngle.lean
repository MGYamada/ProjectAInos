/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Scattering.Asymptote

/-!
# Small-angle scattering: the motion in the variable `u = ρ/r`

Landau–Lifshitz §20 for a potential that is a smooth function of `1/r`. In the
variable `u = ρ/r` the square of the radial velocity is `v∞² h(ε, u)` with
`h(ε, u) = 1 − u² − ε f(u)` (`radicand`), where `ε f(ρ/r) = 2U(r)/m v∞²` and
`f` is smooth on the line.

* `radicand_eq`: at a zero `c` of `h(ε, ·)`,
  `h(ε, u) = (c² − u²)(1 + ε Γ(c, u))` with the smooth function
  `Γ(c, u) = f[c, u]/(c + u)` (`ratio`).
* `IsClosest f ε c`: `c > 0` is a zero and `1 + ε Γ(c, u) > 0` for `0 ≤ u ≤ c`;
  then `ρ/c` is the closest approach, and it is unique (`IsClosest.unique`).
* `exists_isFactor`: the motion exists; `hasDerivAt_velocity`: it satisfies
  Newton's equation for the potential energy per unit mass `(v∞²/2) ε f(ρ/r)`.
* `integral_Ioi_eq_integral_sin`: the change of variables `r = b/sin ψ`.
* `integral_angleDensity`, `deflectionAngle_eq`: with `ρ/r = c sin ψ` the angle
  (18.4) is `∫₀^{π/2} dψ/√(1 + ε Γ(c, c sin ψ))` (`angleKernel`).
* `integral_ratio_eq`, `integral_sin_mul_deriv_eq`:
  `∫₀^{π/2} Γ(1, sin ψ) dψ = ∫₀^{π/2} sin ψ f′(sin ψ) dψ`, which is
  `−ρ ∫_ρ^∞ (d/dr) f(ρ/r) dr/√(r² − ρ²)`, the integral of (20.3).

The expansion in `ε` is in `Scattering/SmallAngleExpansion`.
-/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory
open scoped Real ContDiff Topology

namespace ProjectAinos.Mechanics.Scattering.SmallAngle

open SmoothAlgebra

variable {f : ℝ → ℝ}

/-- `h(ε, u) = 1 − u² − ε f(u)`: the square of the radial velocity over `v∞²`,
in the variable `u = ρ/r`. -/
def radicand (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := 1 - p.2 ^ 2 - p.1 * f p.2

/-- `Γ(c, u) = f[c, u]/(c + u)`, which is `(f(c) − f(u))/(c² − u²)`. -/
def ratio (f : ℝ → ℝ) (c u : ℝ) : ℝ := dividedDifference f (c, u) / (c + u)

theorem contDiff_radicand (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (radicand f) :=
  (contDiff_const.sub (contDiff_snd.pow 2)).sub (contDiff_fst.mul (hf.comp contDiff_snd))

/-- The factorization of the radicand at a turning point. -/
theorem radicand_eq (hf : ContDiff ℝ ∞ f) {ε c : ℝ} (hc : radicand f (ε, c) = 0) {u : ℝ}
    (hcu : c + u ≠ 0) :
    radicand f (ε, u) = (c ^ 2 - u ^ 2) * (1 + ε * ratio f c u) := by
  have h1 := sub_eq_mul_dividedDifference (hf.of_le (by simp)) c u
  have h2 : radicand f (ε, u) = c ^ 2 - u ^ 2 + ε * (f c - f u) := by
    simp only [radicand] at hc ⊢
    linear_combination hc
  rw [h2, h1, ratio]
  field_simp
  ring

theorem ratio_eq (hf : ContDiff ℝ ∞ f) {c u : ℝ} (hcu : c + u ≠ 0) (hne : c - u ≠ 0) :
    ratio f c u = (f c - f u) / (c ^ 2 - u ^ 2) := by
  have h1 := sub_eq_mul_dividedDifference (hf.of_le (by simp)) c u
  have hprod : c ^ 2 - u ^ 2 ≠ 0 := by
    rw [show c ^ 2 - u ^ 2 = (c - u) * (c + u) by ring]
    exact mul_ne_zero hne hcu
  rw [h1, ratio, eq_div_iff hprod]
  field_simp
  ring

theorem contDiffOn_ratio (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => ratio f q.1 q.2) {q : ℝ × ℝ | q.1 + q.2 ≠ 0} :=
  (contDiff_dividedDifference hf).contDiffOn.div (contDiff_fst.add contDiff_snd).contDiffOn
    fun _ hq => hq

theorem continuousOn_ratio_sin (hf : ContDiff ℝ ∞ f) :
    ContinuousOn (fun ψ => ratio f 1 (Real.sin ψ)) (Icc 0 (π / 2)) := by
  have h1 : ContinuousOn (fun q : ℝ × ℝ => ratio f q.1 q.2) {q : ℝ × ℝ | q.1 + q.2 ≠ 0} :=
    (contDiffOn_ratio hf).continuousOn
  have h2 : ContinuousOn (fun ψ : ℝ => (((1 : ℝ), Real.sin ψ) : ℝ × ℝ)) (Icc 0 (π / 2)) :=
    (continuous_const.prodMk Real.continuous_sin).continuousOn
  refine ContinuousOn.comp (g := fun q : ℝ × ℝ => ratio f q.1 q.2)
    (f := fun ψ : ℝ => (((1 : ℝ), Real.sin ψ) : ℝ × ℝ)) h1 h2 fun ψ hψ => ?_
  have := Real.sin_nonneg_of_nonneg_of_le_pi hψ.1 (by linarith [hψ.2, Real.pi_pos])
  change (1 : ℝ) + Real.sin ψ ≠ 0
  linarith

/-- The function `Γ(1, sin ψ) sin ψ cos ψ`, which is `(f(1) − f(sin ψ)) tan ψ`,
and its derivative. -/
theorem hasDerivAt_ratio_mul (hf : ContDiff ℝ ∞ f) {ψ : ℝ} (hψ : ψ ∈ Ioo (0 : ℝ) (π / 2)) :
    HasDerivAt (fun x => ratio f 1 (Real.sin x) * (Real.sin x * Real.cos x))
      (ratio f 1 (Real.sin ψ) - Real.sin ψ * deriv f (Real.sin ψ)) ψ := by
  have hcos : 0 < Real.cos ψ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hψ.1, Real.pi_pos], hψ.2⟩
  have hsin : 0 < Real.sin ψ :=
    Real.sin_pos_of_pos_of_lt_pi hψ.1 (by linarith [hψ.2, Real.pi_pos])
  have hsq := Real.sin_sq_add_cos_sq ψ
  have hlt : Real.sin ψ < 1 := by nlinarith
  have hne : (1 : ℝ) - Real.sin ψ ≠ 0 := by linarith
  have hsum : (1 : ℝ) + Real.sin ψ ≠ 0 := by linarith
  have hev : (fun x => ratio f 1 (Real.sin x) * (Real.sin x * Real.cos x)) =ᶠ[𝓝 ψ]
      fun x => (f 1 - f (Real.sin x)) * (Real.sin x / Real.cos x) := by
    have hopen : IsOpen {x : ℝ | 0 < Real.cos x ∧ Real.sin x < 1 ∧ -1 < Real.sin x} :=
      (isOpen_lt continuous_const Real.continuous_cos).inter
        ((isOpen_lt Real.continuous_sin continuous_const).inter
          (isOpen_lt continuous_const Real.continuous_sin))
    filter_upwards [hopen.mem_nhds ⟨hcos, hlt, by linarith⟩] with x hx
    have hsqx := Real.sin_sq_add_cos_sq x
    have hden : (1 : ℝ) ^ 2 - Real.sin x ^ 2 = Real.cos x ^ 2 := by linarith
    have hc := hx.1.ne'
    rw [ratio_eq hf (by linarith [hx.2.2]) (by linarith [hx.2.1]), hden]
    field_simp
  have hfd : HasDerivAt (fun x => f 1 - f (Real.sin x))
      (-(deriv f (Real.sin ψ) * Real.cos ψ)) ψ := by
    have h1 : HasDerivAt (fun x => f (Real.sin x)) (deriv f (Real.sin ψ) * Real.cos ψ) ψ :=
      HasDerivAt.comp ψ (hf.differentiable (by simp) (Real.sin ψ)).hasDerivAt
        (Real.hasDerivAt_sin ψ)
    exact h1.const_sub (f 1)
  have htan : HasDerivAt (fun x => Real.sin x / Real.cos x)
      ((Real.cos ψ * Real.cos ψ - Real.sin ψ * -Real.sin ψ) / Real.cos ψ ^ 2) ψ :=
    (Real.hasDerivAt_sin ψ).div (Real.hasDerivAt_cos ψ) hcos.ne'
  have hprod : HasDerivAt (fun x => (f 1 - f (Real.sin x)) * (Real.sin x / Real.cos x))
      (-(deriv f (Real.sin ψ) * Real.cos ψ) * (Real.sin ψ / Real.cos ψ) +
        (f 1 - f (Real.sin ψ)) *
          ((Real.cos ψ * Real.cos ψ - Real.sin ψ * -Real.sin ψ) / Real.cos ψ ^ 2)) ψ :=
    hfd.mul htan
  refine (hprod.congr_of_eventuallyEq hev).congr_deriv ?_
  have hden : (1 : ℝ) ^ 2 - Real.sin ψ ^ 2 = Real.cos ψ ^ 2 := by linarith
  have hc := hcos.ne'
  rw [ratio_eq hf hsum hne, hden]
  field_simp
  linear_combination (f 1 - f (Real.sin ψ)) * hsq

/-- An integration by parts: the first-order coefficient in the two forms. -/
theorem integral_ratio_eq (hf : ContDiff ℝ ∞ f) :
    ∫ ψ in (0 : ℝ)..π / 2, ratio f 1 (Real.sin ψ) =
      ∫ ψ in (0 : ℝ)..π / 2, Real.sin ψ * deriv f (Real.sin ψ) := by
  have hratio := continuousOn_ratio_sin hf
  have hsg : Continuous fun ψ => Real.sin ψ * deriv f (Real.sin ψ) :=
    Real.continuous_sin.mul ((hf.continuous_deriv (by simp)).comp Real.continuous_sin)
  have hle : (0 : ℝ) ≤ π / 2 := by positivity
  have hint1 : IntervalIntegrable (fun ψ => ratio f 1 (Real.sin ψ)) volume 0 (π / 2) :=
    (hratio.mono (by rw [uIcc_of_le hle])).intervalIntegrable
  have hint2 : IntervalIntegrable (fun ψ => Real.sin ψ * deriv f (Real.sin ψ)) volume 0
      (π / 2) := hsg.intervalIntegrable 0 (π / 2)
  have hFc : ContinuousOn (fun x => ratio f 1 (Real.sin x) * (Real.sin x * Real.cos x))
      (Icc 0 (π / 2)) :=
    hratio.mul (Real.continuous_sin.mul Real.continuous_cos).continuousOn
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hFc
    (fun ψ hψ => hasDerivAt_ratio_mul hf hψ) (hint1.sub hint2)
  rw [intervalIntegral.integral_sub hint1 hint2] at hftc
  simp only [Real.sin_zero, Real.cos_pi_div_two, mul_zero, zero_mul, sub_zero] at hftc
  linarith


/-! ### The closest approach -/

/-- `c` is the closest approach in the variable `u = ρ/r`: a positive zero of
the radicand such that `1 + ε Γ(c, u)` is positive for `0 ≤ u ≤ c`. The
radicand is then positive for `0 ≤ u < c`, so that `c` is its first zero. -/
structure IsClosest (f : ℝ → ℝ) (ε c : ℝ) : Prop where
  /-- The closest approach is at a finite distance. -/
  pos : 0 < c
  /-- The radial velocity vanishes there. -/
  radicand_eq_zero : radicand f (ε, c) = 0
  /-- The other factor of the radicand is positive up to the closest approach. -/
  factor_pos : ∀ u ∈ Icc 0 c, 0 < 1 + ε * ratio f c u

/-- Without a field the closest approach is at the impact parameter. -/
theorem isClosest_zero (f : ℝ → ℝ) : IsClosest f 0 1 where
  pos := one_pos
  radicand_eq_zero := by simp [radicand]
  factor_pos _ _ := by simp

theorem IsClosest.radicand_pos (hf : ContDiff ℝ ∞ f) {ε c : ℝ} (h : IsClosest f ε c) {u : ℝ}
    (hu : u ∈ Ico 0 c) : 0 < radicand f (ε, u) := by
  rw [radicand_eq hf h.radicand_eq_zero (by linarith [h.pos, hu.1])]
  exact mul_pos (by nlinarith [hu.1, hu.2]) (h.factor_pos u ⟨hu.1, hu.2.le⟩)

/-- The closest approach is unique. -/
theorem IsClosest.unique (hf : ContDiff ℝ ∞ f) {ε c c' : ℝ} (h : IsClosest f ε c)
    (h' : IsClosest f ε c') : c = c' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := h'.radicand_pos hf ⟨h.pos.le, hlt⟩
    rw [h.radicand_eq_zero] at h1
    exact lt_irrefl _ h1
  · have h1 := h.radicand_pos hf ⟨h'.pos.le, hlt⟩
    rw [h'.radicand_eq_zero] at h1
    exact lt_irrefl _ h1

/-! ### The motion for a given closest approach -/

section Motion

variable {ρ vinf ε c : ℝ}

/-- The square of the radial velocity, `v∞² (1 − ρ²/r² − ε f(ρ/r))`. The
potential energy per unit mass is `(v∞²/2) ε f(ρ/r)`. -/
def speedSq (f : ℝ → ℝ) (ρ vinf ε r : ℝ) : ℝ := vinf ^ 2 * radicand f (ε, ρ / r)

/-- The factor of the square of the radial velocity after the closest approach
`ρ/c`. -/
def factor (f : ℝ → ℝ) (ρ vinf ε c r : ℝ) : ℝ :=
  vinf ^ 2 * (c / r) * (c + ρ / r) * (1 + ε * ratio f c (ρ / r))

theorem speedSq_eq (hf : ContDiff ℝ ∞ f) (hρ : 0 < ρ) (vinf : ℝ) (hc0 : 0 < c)
    (hc : radicand f (ε, c) = 0) {r : ℝ} (hr : 0 < r) :
    speedSq f ρ vinf ε r = (r - ρ / c) * factor f ρ vinf ε c r := by
  have hu : 0 < ρ / r := div_pos hρ hr
  rw [speedSq, radicand_eq hf hc (by positivity), factor]
  field_simp
  ring

theorem contDiffOn_ratio_right (hf : ContDiff ℝ ∞ f) (c : ℝ) :
    ContDiffOn ℝ ∞ (fun u => ratio f c u) {u : ℝ | c + u ≠ 0} :=
  ContDiffOn.comp (g := fun q : ℝ × ℝ => ratio f q.1 q.2) (f := fun u : ℝ => ((c, u) : ℝ × ℝ))
    (contDiffOn_ratio hf) (contDiff_const.prodMk contDiff_id).contDiffOn fun _ hu => hu

theorem continuousOn_ratio_right (hf : ContDiff ℝ ∞ f) (hc0 : 0 < c) :
    ContinuousOn (fun u => ratio f c u) (Icc 0 c) :=
  (contDiffOn_ratio_right hf c).continuousOn.mono fun u hu => by
    change c + u ≠ 0
    linarith [hu.1]

/-- The motion exists if `1 + ε Γ(c, u)` is positive for `0 ≤ u ≤ c`. -/
theorem exists_isFactor (hf : ContDiff ℝ ∞ f) (hρ : 0 < ρ) (hv : 0 < vinf) (hc0 : 0 < c)
    (hpos : ∀ u ∈ Icc 0 c, 0 < 1 + ε * ratio f c u) :
    ∃ C : ℝ, IsFactor (factor f ρ vinf ε c) (ρ / c) C := by
  have hr₀ : 0 < ρ / c := div_pos hρ hc0
  have hr : ∀ s : ℝ, 0 < ρ / c + s ^ 2 := fun s => add_pos_of_pos_of_nonneg hr₀ (sq_nonneg s)
  have hu : ∀ s : ℝ, ρ / (ρ / c + s ^ 2) ∈ Ioc 0 c := fun s => by
    refine ⟨div_pos hρ (hr s), ?_⟩
    rw [div_le_iff₀ (hr s)]
    have e : c * (ρ / c) = ρ := by field_simp
    nlinarith [sq_nonneg s]
  obtain ⟨w, hw⟩ : ∃ w : ℝ → ℝ, w = fun u =>
      vinf ^ 2 * (c * u / ρ) * (c + u) * (1 + ε * ratio f c u) := ⟨_, rfl⟩
  have hwc : ContinuousOn w (Icc 0 c) := by
    rw [hw]
    exact ((continuousOn_const.mul ((continuousOn_const.mul continuousOn_id).div_const ρ)).mul
      (continuousOn_const.add continuousOn_id)).mul
      (continuousOn_const.add (continuousOn_const.mul (continuousOn_ratio_right hf hc0)))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hwc
  have hfw : ∀ s : ℝ, factor f ρ vinf ε c (ρ / c + s ^ 2) = w (ρ / (ρ / c + s ^ 2)) := fun s => by
    have h1 := (hr s).ne'
    rw [hw, factor]
    field_simp
  refine ⟨C, ?_, fun s => ?_, fun s => ?_⟩
  · have hu' : ContDiff ℝ ∞ fun s : ℝ => ρ / (ρ / c + s ^ 2) :=
      contDiff_const.div (contDiff_const.add (contDiff_id.pow 2)) fun s => (hr s).ne'
    have hR : ContDiff ℝ ∞ fun s : ℝ => ratio f c (ρ / (ρ / c + s ^ 2)) :=
      (contDiffOn_ratio_right hf c).comp_contDiff hu' fun s => by
        change c + ρ / (ρ / c + s ^ 2) ≠ 0
        linarith [(hu s).1]
    unfold factor
    exact ((contDiff_const.mul (contDiff_const.div (contDiff_const.add (contDiff_id.pow 2))
      fun s => (hr s).ne')).mul (contDiff_const.add hu')).mul
      (contDiff_const.add (contDiff_const.mul hR))
  · have h1 := hpos _ ⟨(hu s).1.le, (hu s).2⟩
    rw [factor]
    exact mul_pos (mul_pos (mul_pos (pow_pos hv 2) (div_pos hc0 (hr s)))
      (add_pos hc0 (hu s).1)) h1
  · rw [hfw s]
    have h1 := hC _ ⟨(hu s).1.le, (hu s).2⟩
    rw [Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans h1

/-! ### The change of variables `r = b/sin ψ` -/

theorem sin_mem_Ioo {ψ : ℝ} (hψ : ψ ∈ Ioo (0 : ℝ) (π / 2)) : Real.sin ψ ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨Real.sin_pos_of_pos_of_lt_pi hψ.1 (by linarith [hψ.2, Real.pi_pos]), ?_⟩
  have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [hψ.1, Real.pi_pos]) le_rfl hψ.2
  rwa [Real.sin_pi_div_two] at h

theorem cos_pos_of_mem_Ioo {ψ : ℝ} (hψ : ψ ∈ Ioo (0 : ℝ) (π / 2)) : 0 < Real.cos ψ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [hψ.1, Real.pi_pos], hψ.2⟩

theorem hasDerivAt_div_sin (b : ℝ) {ψ : ℝ} (hs : Real.sin ψ ≠ 0) :
    HasDerivAt (fun x => b / Real.sin x) (-(b * Real.cos ψ / Real.sin ψ ^ 2)) ψ := by
  have h : HasDerivAt (fun x => b / Real.sin x)
      ((0 * Real.sin ψ - b * Real.cos ψ) / Real.sin ψ ^ 2) ψ :=
    (hasDerivAt_const ψ b).div (Real.hasDerivAt_sin ψ) hs
  refine h.congr_deriv ?_
  ring

theorem image_div_sin {b : ℝ} (hb : 0 < b) :
    (fun ψ => b / Real.sin ψ) '' Ioo 0 (π / 2) = Ioi b := by
  ext r
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    have hs := sin_mem_Ioo hψ
    change b < b / Real.sin ψ
    rw [lt_div_iff₀ hs.1]
    nlinarith [hs.2]
  · intro hr
    have hr' : b < r := hr
    have hr0 : 0 < r := hb.trans hr'
    have hx : 0 < b / r := div_pos hb hr0
    have hx1 : b / r < 1 := (div_lt_one hr0).mpr hr'
    refine ⟨Real.arcsin (b / r), ⟨Real.arcsin_pos.mpr hx, Real.arcsin_lt_pi_div_two.mpr hx1⟩, ?_⟩
    change b / Real.sin (Real.arcsin (b / r)) = r
    rw [Real.sin_arcsin (by linarith) hx1.le]
    field_simp

theorem injOn_div_sin {b : ℝ} (hb : 0 < b) :
    InjOn (fun ψ => b / Real.sin ψ) (Ioo 0 (π / 2)) := by
  intro x hx y hy hxy
  have hsx := (sin_mem_Ioo hx).1
  have hsy := (sin_mem_Ioo hy).1
  have h : b / Real.sin x = b / Real.sin y := hxy
  rw [div_eq_div_iff hsx.ne' hsy.ne'] at h
  have hsin : Real.sin y = Real.sin x := mul_left_cancel₀ hb.ne' h
  exact Real.injOn_sin ⟨by linarith [hx.1, Real.pi_pos], hx.2.le⟩
    ⟨by linarith [hy.1, Real.pi_pos], hy.2.le⟩ hsin.symm

theorem abs_deriv_div_sin_smul {b : ℝ} (hb : 0 < b) (G : ℝ → ℝ) :
    EqOn (fun ψ => |(-(b * Real.cos ψ / Real.sin ψ ^ 2))| • G (b / Real.sin ψ))
      (fun ψ => b * Real.cos ψ / Real.sin ψ ^ 2 * G (b / Real.sin ψ)) (Ioo 0 (π / 2)) := by
  intro ψ hψ
  have hs := (sin_mem_Ioo hψ).1
  have hc := cos_pos_of_mem_Ioo hψ
  change |(-(b * Real.cos ψ / Real.sin ψ ^ 2))| • G (b / Real.sin ψ) =
    b * Real.cos ψ / Real.sin ψ ^ 2 * G (b / Real.sin ψ)
  rw [abs_neg, abs_of_nonneg (by positivity), smul_eq_mul]

/-- The change of variables `r = b/sin ψ` in an integral over `r > b`. -/
theorem integral_Ioi_eq_integral_sin {b : ℝ} (hb : 0 < b) (G : ℝ → ℝ) :
    ∫ r in Ioi b, G r =
      ∫ ψ in Ioo (0 : ℝ) (π / 2), b * Real.cos ψ / Real.sin ψ ^ 2 * G (b / Real.sin ψ) := by
  rw [← image_div_sin hb, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun ψ hψ => (hasDerivAt_div_sin b (sin_mem_Ioo hψ).1.ne').hasDerivWithinAt)
    (injOn_div_sin hb)]
  exact setIntegral_congr_fun measurableSet_Ioo (abs_deriv_div_sin_smul hb G)

theorem integrableOn_Ioi_iff_integrableOn_sin {b : ℝ} (hb : 0 < b) (G : ℝ → ℝ) :
    IntegrableOn G (Ioi b) ↔ IntegrableOn
      (fun ψ => b * Real.cos ψ / Real.sin ψ ^ 2 * G (b / Real.sin ψ)) (Ioo (0 : ℝ) (π / 2)) := by
  rw [← image_div_sin hb, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun ψ hψ => (hasDerivAt_div_sin b (sin_mem_Ioo hψ).1.ne').hasDerivWithinAt)
    (injOn_div_sin hb)]
  exact integrableOn_congr_fun (abs_deriv_div_sin_smul hb G) measurableSet_Ioo

/-! ### The angle as an integral over `0 ≤ ψ ≤ π/2` -/

/-- The integrand `1/√(1 + ε Γ(c, c sin ψ))` of the angle in the variable `ψ`,
with `ρ/r = c sin ψ`. -/
def angleKernel (f : ℝ → ℝ) (ε c ψ : ℝ) : ℝ := 1 / √(1 + ε * ratio f c (c * Real.sin ψ))

theorem angleDensity_div_sin (hf : ContDiff ℝ ∞ f) (hρ : 0 < ρ) (hv : 0 < vinf) (hc0 : 0 < c)
    (hc : radicand f (ε, c) = 0) {ψ : ℝ} (hψ : ψ ∈ Ioo (0 : ℝ) (π / 2)) :
    ρ / c * Real.cos ψ / Real.sin ψ ^ 2 *
        angleDensity (ρ * vinf) (speedSq f ρ vinf ε) (ρ / c / Real.sin ψ) =
      angleKernel f ε c ψ := by
  have hs := (sin_mem_Ioo hψ).1
  have hcos := cos_pos_of_mem_Ioo hψ
  have hu : ρ / (ρ / c / Real.sin ψ) = c * Real.sin ψ := by field_simp
  have hF : speedSq f ρ vinf ε (ρ / c / Real.sin ψ) =
      (vinf * c * Real.cos ψ) ^ 2 * (1 + ε * ratio f c (c * Real.sin ψ)) := by
    rw [speedSq, hu, radicand_eq hf hc (by positivity)]
    have hsq := Real.sin_sq_add_cos_sq ψ
    linear_combination (-(vinf ^ 2 * c ^ 2 * (1 + ε * ratio f c (c * Real.sin ψ)))) * hsq
  rw [angleDensity, hF, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), angleKernel]
  rcases eq_or_ne (√(1 + ε * ratio f c (c * Real.sin ψ))) 0 with h | h
  · simp [h]
  · field_simp

theorem mul_sin_mem_Icc (hc0 : 0 < c) {ψ : ℝ} (hψ : ψ ∈ Icc (0 : ℝ) (π / 2)) :
    c * Real.sin ψ ∈ Icc 0 c := by
  have h0 := Real.sin_nonneg_of_nonneg_of_le_pi hψ.1 (by linarith [hψ.2, Real.pi_pos])
  have h1 := Real.sin_le_one ψ
  exact ⟨by positivity, by nlinarith⟩

theorem continuousOn_angleKernel (hf : ContDiff ℝ ∞ f) (hc0 : 0 < c)
    (hpos : ∀ u ∈ Icc 0 c, 0 < 1 + ε * ratio f c u) :
    ContinuousOn (angleKernel f ε c) (Icc 0 (π / 2)) := by
  have hratio : ContinuousOn (fun ψ => ratio f c (c * Real.sin ψ)) (Icc 0 (π / 2)) :=
    ContinuousOn.comp (g := fun u => ratio f c u) (f := fun ψ => c * Real.sin ψ)
      (continuousOn_ratio_right hf hc0) (continuous_const.mul Real.continuous_sin).continuousOn
      fun _ hψ => mul_sin_mem_Icc hc0 hψ
  have hb : ContinuousOn (fun ψ => 1 + ε * ratio f c (c * Real.sin ψ)) (Icc 0 (π / 2)) :=
    continuousOn_const.add (continuousOn_const.mul hratio)
  have e : angleKernel f ε c = fun ψ => 1 / √(1 + ε * ratio f c (c * Real.sin ψ)) := rfl
  rw [e]
  exact continuousOn_const.div (Real.continuous_sqrt.comp_continuousOn hb) fun ψ hψ =>
    (Real.sqrt_pos.mpr (hpos _ (mul_sin_mem_Icc hc0 hψ))).ne'

/-- Landau–Lifshitz (18.4) in the variable `ψ`: the angle from the closest
approach `ρ/c` to infinity. -/
theorem integral_angleDensity (hf : ContDiff ℝ ∞ f) (hρ : 0 < ρ) (hv : 0 < vinf) (hc0 : 0 < c)
    (hc : radicand f (ε, c) = 0) (hpos : ∀ u ∈ Icc 0 c, 0 < 1 + ε * ratio f c u) :
    IntegrableOn (angleDensity (ρ * vinf) (speedSq f ρ vinf ε)) (Ioi (ρ / c)) ∧
      ∫ r in Ioi (ρ / c), angleDensity (ρ * vinf) (speedSq f ρ vinf ε) r =
        ∫ ψ in (0 : ℝ)..π / 2, angleKernel f ε c ψ := by
  have hb : 0 < ρ / c := div_pos hρ hc0
  have hle : (0 : ℝ) ≤ π / 2 := by positivity
  have hint : IntervalIntegrable (angleKernel f ε c) volume 0 (π / 2) :=
    ((continuousOn_angleKernel hf hc0 hpos).mono (by rw [uIcc_of_le hle])).intervalIntegrable
  have hint' : IntegrableOn (angleKernel f ε c) (Ioo 0 (π / 2)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp hint).mono_set Ioo_subset_Ioc_self
  have heq : EqOn (fun ψ => ρ / c * Real.cos ψ / Real.sin ψ ^ 2 *
      angleDensity (ρ * vinf) (speedSq f ρ vinf ε) (ρ / c / Real.sin ψ))
      (angleKernel f ε c) (Ioo 0 (π / 2)) := fun _ hψ => angleDensity_div_sin hf hρ hv hc0 hc hψ
  constructor
  · rw [integrableOn_Ioi_iff_integrableOn_sin hb, integrableOn_congr_fun heq measurableSet_Ioo]
    exact hint'
  · rw [integral_Ioi_eq_integral_sin hb, setIntegral_congr_fun measurableSet_Ioo heq,
      intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo]

theorem deflectionAngle_eq (hf : ContDiff ℝ ∞ f) (hρ : 0 < ρ) (hv : 0 < vinf) (hc0 : 0 < c)
    (hc : radicand f (ε, c) = 0) (hpos : ∀ u ∈ Icc 0 c, 0 < 1 + ε * ratio f c u) :
    deflectionAngle (ρ * vinf) (speedSq f ρ vinf ε) (ρ / c) =
      π - 2 * ∫ ψ in (0 : ℝ)..π / 2, angleKernel f ε c ψ := by
  rw [deflectionAngle, (integral_angleDensity hf hρ hv hc0 hc hpos).2]

/-- The angle of the motion tends to the integral over `ψ`. -/
theorem tendsto_angle_atTop (hf : ContDiff ℝ ∞ f) (hρ : 0 < ρ) (hv : 0 < vinf) (hc0 : 0 < c)
    (hc : radicand f (ε, c) = 0) (hpos : ∀ u ∈ Icc 0 c, 0 < 1 + ε * ratio f c u) {C : ℝ}
    (h : IsFactor (factor f ρ vinf ε c) (ρ / c) C) :
    Tendsto (angle (factor f ρ vinf ε c) (ρ / c) (ρ * vinf)) atTop
      (𝓝 (∫ ψ in (0 : ℝ)..π / 2, angleKernel f ε c ψ)) := by
  have hb : 0 < ρ / c := div_pos hρ hc0
  have hI := integral_angleDensity hf hρ hv hc0 hc hpos
  have h1 := (h.tendsto_angle_atTop hb (F := speedSq f ρ vinf ε)
    (fun r hr => speedSq_eq hf hρ vinf hc0 hc (hb.trans_le hr)) (ρ * vinf) hI.1).2
  rwa [hI.2] at h1

/-! ### Newton's equation and the speed at infinity -/

theorem hasDerivAt_comp_div (hf : ContDiff ℝ ∞ f) (ρ : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun r => f (ρ / r)) (deriv f (ρ / r) * -(ρ / r ^ 2)) r := by
  have hu : HasDerivAt (fun r : ℝ => ρ / r) (-(ρ / r ^ 2)) r := by
    have h : HasDerivAt (fun r : ℝ => ρ / r) ((0 * r - ρ * 1) / r ^ 2) r :=
      (hasDerivAt_const r ρ).div (hasDerivAt_id r) hr
    refine h.congr_deriv ?_
    ring
  exact HasDerivAt.comp r (hf.differentiable (by simp) (ρ / r)).hasDerivAt hu

theorem hasDerivAt_speedSq (hf : ContDiff ℝ ∞ f) (ρ vinf ε : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (speedSq f ρ vinf ε)
      (vinf ^ 2 * (2 * ρ ^ 2 / r ^ 3 + ε * (deriv f (ρ / r) * (ρ / r ^ 2)))) r := by
  have hsq : HasDerivAt (fun r : ℝ => ρ ^ 2 / r ^ 2) (-(2 * ρ ^ 2) / r ^ 3) r := by
    have hpow : HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by
      simpa using hasDerivAt_pow 2 r
    have h : HasDerivAt (fun r : ℝ => ρ ^ 2 / r ^ 2)
        ((0 * r ^ 2 - ρ ^ 2 * (2 * r)) / (r ^ 2) ^ 2) r :=
      (hasDerivAt_const r (ρ ^ 2)).div hpow (pow_ne_zero 2 hr)
    refine h.congr_deriv ?_
    field_simp
    ring
  have h3 : HasDerivAt (fun r : ℝ => vinf ^ 2 * (1 - ρ ^ 2 / r ^ 2 - ε * f (ρ / r)))
      (vinf ^ 2 * (0 - -(2 * ρ ^ 2) / r ^ 3 - ε * (deriv f (ρ / r) * -(ρ / r ^ 2)))) r :=
    (((hasDerivAt_const r (1 : ℝ)).sub hsq).sub
      ((hasDerivAt_comp_div hf ρ hr).const_mul ε)).const_mul (vinf ^ 2)
  have e : speedSq f ρ vinf ε = fun r : ℝ => vinf ^ 2 * (1 - ρ ^ 2 / r ^ 2 - ε * f (ρ / r)) := by
    funext x
    simp only [speedSq, radicand, div_pow]
  rw [e]
  refine h3.congr_deriv ?_
  ring

/-- If the potential vanishes at infinity, the speed at infinity is `v∞`. -/
theorem tendsto_speedSq_atTop (hf : ContDiff ℝ ∞ f) (hf0 : f 0 = 0) (ρ vinf ε : ℝ) :
    Tendsto (speedSq f ρ vinf ε) atTop (𝓝 (vinf ^ 2)) := by
  have hu : Tendsto (fun r : ℝ => ρ / r) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hcont : Continuous fun u : ℝ => vinf ^ 2 * radicand f (ε, u) :=
    continuous_const.mul
      ((contDiff_radicand hf).continuous.comp (continuous_const.prodMk continuous_id))
  have h := (hcont.tendsto 0).comp hu
  have e : vinf ^ 2 * radicand f (ε, 0) = vinf ^ 2 := by simp [radicand, hf0]
  rw [e] at h
  exact h

theorem tendsto_radialVelocity_atTop (hf : ContDiff ℝ ∞ f) (hf0 : f 0 = 0) (hρ : 0 < ρ)
    (hv : 0 < vinf) (hc0 : 0 < c) (hc : radicand f (ε, c) = 0) {C : ℝ}
    (h : IsFactor (factor f ρ vinf ε c) (ρ / c) C) :
    Tendsto (radialVelocity (factor f ρ vinf ε c) (ρ / c)) atTop (𝓝 vinf) :=
  h.tendsto_radialVelocity_atTop (F := speedSq f ρ vinf ε)
    (fun _ hr => speedSq_eq hf hρ vinf hc0 hc ((div_pos hρ hc0).trans_le hr)) hv.le
    (tendsto_speedSq_atTop hf hf0 ρ vinf ε)

/-- Newton's equation: the acceleration is `−Φ′(r)` along the radius, for the
potential energy per unit mass `Φ(r) = (v∞²/2) ε f(ρ/r)`. -/
theorem hasDerivAt_velocity (hf : ContDiff ℝ ∞ f) (hρ : 0 < ρ) (hc0 : 0 < c)
    (hc : radicand f (ε, c) = 0) {C : ℝ} (h : IsFactor (factor f ρ vinf ε c) (ρ / c) C)
    (t : ℝ) :
    HasDerivAt (velocity (factor f ρ vinf ε c) (ρ / c) (ρ * vinf))
      ((-deriv (fun r => vinf ^ 2 / 2 * (ε * f (ρ / r)))
          (radius (factor f ρ vinf ε c) (ρ / c) t)) •
        (Real.cos (angle (factor f ρ vinf ε c) (ρ / c) (ρ * vinf) t),
          Real.sin (angle (factor f ρ vinf ε c) (ρ / c) (ρ * vinf) t))) t := by
  have hb : 0 < ρ / c := div_pos hρ hc0
  have hr : 0 < radius (factor f ρ vinf ε c) (ρ / c) t := hb.trans_le (le_radius _ _ t)
  have hd : deriv (fun r => vinf ^ 2 / 2 * (ε * f (ρ / r)))
      (radius (factor f ρ vinf ε c) (ρ / c) t) =
      vinf ^ 2 / 2 * (ε * (deriv f (ρ / radius (factor f ρ vinf ε c) (ρ / c) t) *
        -(ρ / radius (factor f ρ vinf ε c) (ρ / c) t ^ 2))) :=
    (((hasDerivAt_comp_div hf ρ hr.ne').const_mul ε).const_mul (vinf ^ 2 / 2)).deriv
  have h1 := h.hasDerivAt_velocity hb (F := speedSq f ρ vinf ε)
    (F' := fun r => vinf ^ 2 * (2 * ρ ^ 2 / r ^ 3 + ε * (deriv f (ρ / r) * (ρ / r ^ 2))))
    (fun _ hr' => speedSq_eq hf hρ vinf hc0 hc (hb.trans_le hr'))
    (fun r hr' => hasDerivAt_speedSq hf ρ vinf ε (hb.trans_le hr').ne') (ρ * vinf) t
  refine h1.congr_deriv ?_
  rw [hd]
  congr 1
  field_simp
  ring

/-! ### The coefficient of the first order as an integral over the radius -/

/-- The coefficient of the first order in the form of Landau–Lifshitz (20.3):
with `ε f(ρ/r) = 2U(r)/m v∞²` the right-hand side times `ε` is
`−(2ρ/m v∞²) ∫_ρ^∞ U′(r) dr/√(r² − ρ²)`. -/
theorem integral_sin_mul_deriv_eq (hf : ContDiff ℝ ∞ f) (hρ : 0 < ρ) :
    ∫ ψ in (0 : ℝ)..π / 2, Real.sin ψ * deriv f (Real.sin ψ) =
      -ρ * ∫ r in Ioi ρ, deriv (fun r => f (ρ / r)) r / √(r ^ 2 - ρ ^ 2) := by
  have hle : (0 : ℝ) ≤ π / 2 := by positivity
  have hpt : EqOn (fun ψ => ρ * Real.cos ψ / Real.sin ψ ^ 2 *
      (deriv (fun r => f (ρ / r)) (ρ / Real.sin ψ) / √((ρ / Real.sin ψ) ^ 2 - ρ ^ 2)))
      (fun ψ => -(1 / ρ) * (Real.sin ψ * deriv f (Real.sin ψ))) (Ioo 0 (π / 2)) := by
    intro ψ hψ
    have hs := (sin_mem_Ioo hψ).1
    have hcos := cos_pos_of_mem_Ioo hψ
    have hr : ρ / Real.sin ψ ≠ 0 := (div_pos hρ hs).ne'
    have hu : ρ / (ρ / Real.sin ψ) = Real.sin ψ := by field_simp
    have hd : deriv (fun r => f (ρ / r)) (ρ / Real.sin ψ) =
        deriv f (Real.sin ψ) * -(Real.sin ψ ^ 2 / ρ) := by
      rw [(hasDerivAt_comp_div hf ρ hr).deriv, hu]
      field_simp
    have hsqrt : √((ρ / Real.sin ψ) ^ 2 - ρ ^ 2) = ρ * Real.cos ψ / Real.sin ψ := by
      have e : (ρ / Real.sin ψ) ^ 2 - ρ ^ 2 = (ρ * Real.cos ψ / Real.sin ψ) ^ 2 := by
        have hsq := Real.sin_sq_add_cos_sq ψ
        field_simp
        linarith
      rw [e, Real.sqrt_sq (by positivity)]
    change ρ * Real.cos ψ / Real.sin ψ ^ 2 *
      (deriv (fun r => f (ρ / r)) (ρ / Real.sin ψ) / √((ρ / Real.sin ψ) ^ 2 - ρ ^ 2)) =
      -(1 / ρ) * (Real.sin ψ * deriv f (Real.sin ψ))
    rw [hd, hsqrt]
    field_simp
  rw [integral_Ioi_eq_integral_sin hρ, setIntegral_congr_fun measurableSet_Ioo hpt,
    integral_const_mul, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hle]
  field_simp

end Motion

end ProjectAinos.Mechanics.Scattering.SmallAngle
