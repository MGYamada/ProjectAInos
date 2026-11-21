/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Wave.RetardedIntegral
import Mathlib.Tactic

/-!
# The far field of a localized source

Space-time is `ℝ × ℝ³` with `ℝ³ = EuclideanSpace ℝ (Fin 3)`. A source `f` has **localized
support** in the ball of radius `a` (`LocalizedSupport a f`) if `f(t, y) = 0` for `‖y‖ > a` at
all times; it has subluminal support with the speed `0` (`LocalizedSupport.subluminalSupport`,
and conversely `SubluminalSupport.localizedSupport`); the bump `spaceBump`, constant in time, is an
instance (`localizedSupport_spaceBump`). At the distance `R` in the direction `n` of
the unit sphere and at the **retarded time** `u = t − R`, the retarded integral of such a source
falls off as `1/R` with the amplitude

  `farAmplitude f u n = (1/4π) ∫ f(u + ⟨n, y⟩, y) dy`

(Landau–Lifshitz, *The Classical Theory of Fields*, §66). With `y = Rn − z` the retarded integral
is `∫ f(u + R − ‖Rn − z‖, z)/(4π‖Rn − z‖) dz` (`retardedIntegral_eq_integral`), and for `‖z‖ ≤ a`
the delay `‖Rn − z‖ − R + ⟨n, z⟩` lies in `[0, a²/R]` while `R/‖Rn − z‖ → 1`
(`norm_smul_sub_estimates`); `abs_mul_retardedIntegral_sub_le` turns these into a bound of the
remainder.

* `tendstoUniformlyOn_mul_retardedIntegral`: for a continuous localized source,
  `R · Rf(u + R, Rn) → farAmplitude f u n` as `R → ∞`, uniformly for `u` in a compact set and
  `n` on the unit sphere.
* `exists_bound_mul_retardedIntegral_sub`: for a `C¹` source the remainder is `O(1/R)`,
  uniformly, with a constant from the bounds of `f` and `∂ₜf` on a compact set.
* `farAmplitude_spaceDeriv`: `farAmplitude (∂ᵢf) = −nᵢ farAmplitude (∂ₜf)`, since
  `∂ᵢ[f(u + ⟨n, y⟩, y)] = nᵢ ∂ₜf + ∂ᵢf` integrates to zero.
* The derivatives: `tendstoUniformlyOn_mul_timeDeriv_retardedIntegral` and
  `tendstoUniformlyOn_mul_spaceDeriv_retardedIntegral`, `R · ∂ₜ(Rf) → farAmplitude (∂ₜf)` and
  `R · ∂ᵢ(Rf) → −nᵢ farAmplitude (∂ₜf)`, uniformly; for a `C²` source the remainders are
  `O(1/R)` (`exists_bound_mul_timeDeriv_retardedIntegral_sub`,
  `exists_bound_mul_spaceDeriv_retardedIntegral_add`).
* `abs_farAmplitude_le`, `exists_bound_farAmplitude`: the amplitude is bounded for `u` in a
  compact set and `n` on the unit sphere.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real
open scoped Topology

namespace ProjectAinos.SmoothGeometry.Wave

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Sources localized in a ball -/

/-- A function on `ℝ × ℝ³` has **localized support** in the ball of radius `a` if it vanishes at
`(t, y)` for `‖y‖ > a`, at all times `t`. -/
def LocalizedSupport {G : Type*} [Zero G] (a : ℝ) (f : ℝ × E3 → G) : Prop :=
  ∀ (t : ℝ) (y : E3), a < ‖y‖ → f (t, y) = 0

/-- A localized support in a ball is a localized support in a larger ball. -/
theorem LocalizedSupport.mono {G : Type*} [Zero G] {a b : ℝ} {f : ℝ × E3 → G}
    (hf : LocalizedSupport a f) (hab : a ≤ b) : LocalizedSupport b f :=
  fun t y hy => hf t y (hab.trans_lt hy)

/-- A map that sends `0` to `0` keeps a localized support. -/
theorem LocalizedSupport.comp {G G' : Type*} [Zero G] [Zero G'] {a : ℝ} {f : ℝ × E3 → G}
    (hf : LocalizedSupport a f) {g : G → G'} (hg : g 0 = 0) :
    LocalizedSupport a fun p => g (f p) :=
  fun t y hy => show g (f (t, y)) = 0 by rw [hf t y hy, hg]

/-- A localized support is a subluminal support with the speed `0`. -/
theorem LocalizedSupport.subluminalSupport {G : Type*} [NormedAddCommGroup G] {a : ℝ}
    {f : ℝ × E3 → G} (hf : LocalizedSupport a f) : SubluminalSupport a 0 f := by
  have hcl : IsClosed {p : ℝ × E3 | ‖p.2‖ ≤ a + 0 * |p.1|} := by
    simp only [zero_mul, add_zero]
    exact isClosed_le (continuous_norm.comp continuous_snd) continuous_const
  refine ⟨le_rfl, zero_lt_one, closure_minimal (fun p hp => ?_) hcl⟩
  obtain ⟨t, y⟩ := p
  simp only [mem_ofPred_eq, zero_mul, add_zero]
  by_contra h
  exact hp (hf t y (not_le.mp h))

/-- A subluminal support with the speed `0` is a localized support. -/
theorem SubluminalSupport.localizedSupport {G : Type*} [NormedAddCommGroup G] {a : ℝ}
    {f : ℝ × E3 → G} (hf : SubluminalSupport a 0 f) : LocalizedSupport a f := by
  intro t y hy
  by_contra h
  have h' := hf.subset (subset_tsupport f h)
  simp only [mem_ofPred_eq, zero_mul, add_zero] at h'
  linarith

/-- **An instance**: the bump `spaceBump`, constant in time, has localized support in the ball of
radius `2`. -/
theorem localizedSupport_spaceBump : LocalizedSupport 2 fun p : ℝ × E3 => spaceBump p.2 :=
  fun _ y hy => spaceBump.zero_of_le_dist (by rw [dist_zero_right]; exact hy.le)

/-- The derivative of a function with localized support vanishes outside the ball. -/
theorem LocalizedSupport.fderiv_eq_zero {a : ℝ} {f : ℝ × E3 → ℝ} (hf : LocalizedSupport a f)
    {t : ℝ} {y : E3} (hy : a < ‖y‖) : fderiv ℝ f (t, y) = 0 := by
  have ho : IsOpen {p : ℝ × E3 | a < ‖p.2‖} :=
    isOpen_lt continuous_const (continuous_norm.comp continuous_snd)
  have h : f =ᶠ[𝓝 (t, y)] fun _ => 0 := by
    filter_upwards [ho.mem_nhds hy] with p hp
    obtain ⟨t', y'⟩ := p
    exact hf t' y' hp
  rw [h.fderiv_eq, fderiv_const_apply]

/-- The time derivative of a function with localized support has localized support. -/
theorem LocalizedSupport.timeDeriv {a : ℝ} {f : ℝ × E3 → ℝ} (hf : LocalizedSupport a f) :
    LocalizedSupport a (timeDeriv f) := fun _ _ hy => by
  rw [Wave.timeDeriv, hf.fderiv_eq_zero hy]
  rfl

/-- The spatial derivatives of a function with localized support have localized support. -/
theorem LocalizedSupport.spaceDeriv {a : ℝ} {f : ℝ × E3 → ℝ} (hf : LocalizedSupport a f)
    (i : Fin 3) : LocalizedSupport a (spaceDeriv i f) := fun _ _ hy => by
  rw [Wave.spaceDeriv, hf.fderiv_eq_zero hy]
  rfl

/-! ### The amplitude of the far field -/

/-- The **amplitude of the far field** `(1/4π) ∫ f(u + ⟨n, y⟩, y) dy` of a source in the direction
`n` at the retarded time `u`. -/
def farAmplitude (f : ℝ × E3 → ℝ) (u : ℝ) (n : E3) : ℝ :=
  (4 * π)⁻¹ * ∫ y, f (u + inner ℝ n y, y)

/-- The integrand of the amplitude has compact support. -/
theorem hasCompactSupport_farIntegrand {a : ℝ} {f : ℝ × E3 → ℝ} (hf : LocalizedSupport a f)
    (u : ℝ) (n : E3) : HasCompactSupport fun y : E3 => f (u + inner ℝ n y, y) :=
  HasCompactSupport.intro (isCompact_closedBall 0 a) fun y hy =>
    hf _ _ (by rwa [mem_closedBall_zero_iff, not_le] at hy)

/-- The integrand of the amplitude of a continuous source is integrable. -/
theorem integrable_farIntegrand {a : ℝ} {f : ℝ × E3 → ℝ} (hc : Continuous f)
    (hf : LocalizedSupport a f) (u : ℝ) (n : E3) :
    Integrable fun y : E3 => f (u + inner ℝ n y, y) :=
  (hc.comp (by fun_prop)).integrable_of_hasCompactSupport (hasCompactSupport_farIntegrand hf u n)

/-- The indicator of a constant on a ball is integrable. -/
private theorem integrable_indicator_closedBall (a C : ℝ) :
    Integrable ((closedBall (0 : E3) a).indicator fun _ => C) :=
  (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall

/-- A bound of the amplitude by a bound of the source on its support. -/
theorem abs_farAmplitude_le {a M u : ℝ} {n : E3} {f : ℝ × E3 → ℝ} (hf : LocalizedSupport a f)
    (hM : ∀ z : E3, ‖z‖ ≤ a → |f (u + inner ℝ n z, z)| ≤ M) :
    |farAmplitude f u n| ≤ (4 * π)⁻¹ * M * volume.real (closedBall (0 : E3) a) := by
  have hb : ∀ z : E3,
      ‖f (u + inner ℝ n z, z)‖ ≤ (closedBall (0 : E3) a).indicator (fun _ => M) z := by
    intro z
    by_cases hz : ‖z‖ ≤ a
    · rw [indicator_of_mem (by simpa using hz), Real.norm_eq_abs]
      exact hM z hz
    · rw [indicator_of_notMem (by simpa using hz), hf _ _ (not_le.mp hz), norm_zero]
  have h := norm_integral_le_of_norm_le (integrable_indicator_closedBall a M)
    (Eventually.of_forall hb)
  rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, Real.norm_eq_abs] at h
  rw [farAmplitude, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (4 * π)⁻¹), mul_assoc,
    mul_comm M]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-! ### The geometry of a far point -/

/-- **The distance from a far point**: for a unit vector `n`, `‖z‖ ≤ a` and `2a ≤ R`, the distance
`D = ‖Rn − z‖` has `R/2 ≤ D`, `|R − D| ≤ a` and the delay `D − R + ⟨n, z⟩` lies in `[0, a²/R]`. -/
theorem norm_smul_sub_estimates {a R : ℝ} {n z : E3} (hn : ‖n‖ = 1) (hz : ‖z‖ ≤ a)
    (hR : 2 * a ≤ R) (hR0 : 0 < R) :
    R / 2 ≤ ‖R • n - z‖ ∧ |R - ‖R • n - z‖| ≤ a ∧ 0 ≤ ‖R • n - z‖ - R + inner ℝ n z ∧
      ‖R • n - z‖ - R + inner ℝ n z ≤ a ^ 2 / R := by
  have hRn : ‖R • n‖ = R := by rw [norm_smul, hn, mul_one, Real.norm_of_nonneg hR0.le]
  have h1 : |R - ‖R • n - z‖| ≤ a := by
    have h := abs_norm_sub_norm_le (R • n) (R • n - z)
    rw [hRn, sub_sub_cancel] at h
    exact h.trans hz
  have hD : R / 2 ≤ ‖R • n - z‖ := by
    have := (abs_le.mp h1).2
    linarith
  have hsq : ‖R • n - z‖ ^ 2 = R ^ 2 - 2 * (R * inner ℝ n z) + ‖z‖ ^ 2 := by
    rw [norm_sub_sq_real, hRn, real_inner_smul_left]
  have hcs : |inner ℝ n z| ≤ ‖z‖ := by
    have h := abs_real_inner_le_norm n z
    rwa [hn, one_mul] at h
  have hcs2 : inner ℝ n z ^ 2 ≤ ‖z‖ ^ 2 := sq_le_sq' (abs_le.mp hcs).1 (abs_le.mp hcs).2
  have hz2 : ‖z‖ ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hs : inner ℝ n z ≤ a := (le_abs_self _).trans (hcs.trans hz)
  set D := ‖R • n - z‖ with hDdef
  set s := inner ℝ n z with hsdef
  have hD0 : 0 ≤ D := norm_nonneg _
  have hw : R / 2 ≤ R - s := by linarith
  have hD2 : (R - s) ^ 2 ≤ D ^ 2 := by nlinarith
  have hDw : R - s ≤ D := by
    by_contra h
    have h' := not_le.mp h
    nlinarith
  refine ⟨hD, h1, by linarith, ?_⟩
  rw [le_div_iff₀ hR0]
  have hprod : (D - (R - s)) * (D + (R - s)) ≤ a ^ 2 := by nlinarith
  have hsum : R ≤ D + (R - s) := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hDw)]

/-! ### The retarded integral at a far point -/

/-- The retarded integral in the variable `z = x − y`:
`Rf(t, x) = ∫ f(t − ‖x − z‖, z)/(4π‖x − z‖) dz`. -/
theorem retardedIntegral_eq_integral (f : ℝ × E3 → ℝ) (t : ℝ) (x : E3) :
    retardedIntegral f (t, x) = ∫ z, (4 * π * ‖x - z‖)⁻¹ * f (t - ‖x - z‖, z) := by
  rw [retardedIntegral, ← integral_sub_left_eq_self _ volume x]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [smul_eq_mul, Prod.mk_sub_mk, sub_sub_cancel]

/-- **The remainder of the far field**: for a unit vector `n`, `2a ≤ R`, a bound `η` of the change
`f(u + ⟨n, z⟩ − s, z) − f(u + ⟨n, z⟩, z)` over the delays `s ∈ [0, a²/R]` and a bound `M` of
`f(u + ⟨n, z⟩, z)` on the ball `‖z‖ ≤ a`,
`|R · Rf(u + R, Rn) − farAmplitude f u n| ≤ (1/4π)(2η + 2aM/R) vol(B_a)`. -/
theorem abs_mul_retardedIntegral_sub_le {a R η M u : ℝ} {n : E3} {f : ℝ × E3 → ℝ}
    (hc : Continuous f) (hf : LocalizedSupport a f) (ha : 0 ≤ a) (hR0 : 0 < R)
    (hR : 2 * a ≤ R) (hn : ‖n‖ = 1)
    (hη : ∀ z : E3, ‖z‖ ≤ a → ∀ s : ℝ, 0 ≤ s → s ≤ a ^ 2 / R →
      |f (u + inner ℝ n z - s, z) - f (u + inner ℝ n z, z)| ≤ η)
    (hM : ∀ z : E3, ‖z‖ ≤ a → |f (u + inner ℝ n z, z)| ≤ M) :
    |R * retardedIntegral f (u + R, R • n) - farAmplitude f u n| ≤
      (4 * π)⁻¹ * (2 * η + 2 * a * M / R) * volume.real (closedBall (0 : E3) a) := by
  have h0 : ‖(0 : E3)‖ ≤ a := by simpa using ha
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hη 0 h0 0 le_rfl (by positivity))
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 h0)
  set C := (4 * π)⁻¹ * (2 * η + 2 * a * M / R) with hC
  have hI1 : Integrable fun z : E3 =>
      R * ((4 * π * ‖R • n - z‖)⁻¹ * f (u + R - ‖R • n - z‖, z)) := by
    have h := (hf.subluminalSupport.integrable hc (u + R, R • n)).comp_sub_left (R • n)
    refine (h.const_mul R).congr (Eventually.of_forall fun z => ?_)
    simp only [smul_eq_mul, Prod.mk_sub_mk, sub_sub_cancel]
  have hI2 := (integrable_farIntegrand hc hf u n).const_mul (4 * π)⁻¹
  have hbound : ∀ z : E3,
      ‖R * ((4 * π * ‖R • n - z‖)⁻¹ * f (u + R - ‖R • n - z‖, z)) -
        (4 * π)⁻¹ * f (u + inner ℝ n z, z)‖ ≤
        (closedBall (0 : E3) a).indicator (fun _ => C) z := by
    intro z
    by_cases hz : ‖z‖ ≤ a
    · rw [indicator_of_mem (by simpa using hz)]
      obtain ⟨hD, h1, hs0, hs1⟩ := norm_smul_sub_estimates hn hz hR hR0
      have hτ : u + R - ‖R • n - z‖ =
          u + inner ℝ n z - (‖R • n - z‖ - R + inner ℝ n z) := by ring
      have hA := hη z hz _ hs0 hs1
      rw [← hτ] at hA
      have hB := hM z hz
      set D := ‖R • n - z‖ with hDdef
      have hD0 : 0 < D := by linarith
      set A := f (u + R - D, z)
      set B := f (u + inner ℝ n z, z)
      have hq : R / D ≤ 2 := by
        rw [div_le_iff₀ hD0]
        linarith
      have hq0 : 0 ≤ R / D := by positivity
      have hq1 : |R / D - 1| ≤ 2 * a / R := by
        rw [div_sub_one hD0.ne', abs_div, abs_of_pos hD0, div_le_div_iff₀ hD0 hR0]
        nlinarith [mul_le_mul_of_nonneg_right h1 hR0.le, mul_le_mul_of_nonneg_left hD ha]
      have heq : R * ((4 * π * D)⁻¹ * A) - (4 * π)⁻¹ * B =
          (4 * π)⁻¹ * ((A - B) * (R / D) + B * (R / D - 1)) := by
        field_simp
        ring
      rw [heq, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (4 * π)⁻¹), hC]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc |(A - B) * (R / D) + B * (R / D - 1)|
          ≤ |A - B| * (R / D) + |B| * |R / D - 1| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_nonneg hq0]
        _ ≤ η * 2 + M * (2 * a / R) := by
            gcongr
        _ = 2 * η + 2 * a * M / R := by ring
    · have hz' : a < ‖z‖ := not_le.mp hz
      rw [indicator_of_notMem (by simpa using hz), hf _ _ hz', hf _ _ hz']
      simp
  rw [retardedIntegral_eq_integral, farAmplitude, ← integral_const_mul, ← integral_const_mul,
    ← integral_sub hI1 hI2, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (integrable_indicator_closedBall a C)
    (Eventually.of_forall hbound)).trans_eq ?_
  rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, mul_comm]

/-! ### The limit of the retarded integral -/

/-- For `u ∈ [−r, r]`, a unit vector `n`, `‖z‖ ≤ b` and a delay `0 ≤ s ≤ b`, the point
`(u + ⟨n, z⟩ − s, z)` lies in the compact set `[−r − 2b, r + b] × B_b`. -/
private theorem mem_farSet {r b u s : ℝ} {n z : E3} (hu : |u| ≤ r) (hn : ‖n‖ = 1)
    (hz : ‖z‖ ≤ b) (hs0 : 0 ≤ s) (hs : s ≤ b) :
    (u + inner ℝ n z - s, z) ∈ Icc (-r - 2 * b) (r + b) ×ˢ closedBall (0 : E3) b := by
  have hcs : |inner ℝ n z| ≤ ‖z‖ := by
    have h := abs_real_inner_le_norm n z
    rwa [hn, one_mul] at h
  refine ⟨⟨?_, ?_⟩, by simpa using hz⟩
  · linarith [(abs_le.mp hu).1, (abs_le.mp hcs).1]
  · linarith [(abs_le.mp hu).2, (abs_le.mp hcs).2]

/-- The point `(u + ⟨n, z⟩, z)` lies in the compact set `[−r − 2b, r + b] × B_b`. -/
private theorem mem_farSet_zero {r b u : ℝ} {n z : E3} (hu : |u| ≤ r) (hn : ‖n‖ = 1)
    (hz : ‖z‖ ≤ b) :
    (u + inner ℝ n z, z) ∈ Icc (-r - 2 * b) (r + b) ×ˢ closedBall (0 : E3) b := by
  have h := mem_farSet hu hn hz le_rfl ((norm_nonneg z).trans hz)
  rwa [sub_zero] at h

/-- The distance of the delayed point: `dist (τ − s, z) (τ, z) = s` for `s ≥ 0`. -/
private theorem dist_delay {τ s : ℝ} (z : E3) (hs : 0 ≤ s) :
    dist (τ - s, z) (τ, z) = s := by
  rw [Prod.dist_eq]
  dsimp only
  rw [dist_self, Real.dist_eq, show τ - s - τ = -s by ring, abs_neg, abs_of_nonneg hs,
    max_eq_left hs]

/-- **The far field of a localized source**: for a continuous source with localized support,
`R · Rf(u + R, Rn) → farAmplitude f u n = (1/4π) ∫ f(u + ⟨n, y⟩, y) dy` as `R → ∞`, uniformly for
`u` in a compact set and `n` on the unit sphere. -/
theorem tendstoUniformlyOn_mul_retardedIntegral {a : ℝ} {f : ℝ × E3 → ℝ} (hc : Continuous f)
    (hf : LocalizedSupport a f) {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun R (p : ℝ × E3) => R * retardedIntegral f (p.1 + R, R • p.2))
      (fun p => farAmplitude f p.1 p.2) atTop (K ×ˢ sphere (0 : E3) 1) := by
  set b := max a 1 with hbdef
  have hb : 0 < b := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hf' : LocalizedSupport b f := hf.mono (le_max_left a 1)
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  set S := Icc (-r - 2 * b) (r + b) ×ˢ closedBall (0 : E3) b with hSdef
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  have huc := Metric.uniformContinuousOn_iff.mp
    (hS.uniformContinuousOn_of_continuous hc.continuousOn)
  set c := (4 * π)⁻¹ * volume.real (closedBall (0 : E3) b) with hcdef
  have hc0 : 0 ≤ c := by positivity
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set η := ε / (4 * (c + 1)) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := huc η hη
  filter_upwards [eventually_ge_atTop (2 * b), eventually_gt_atTop (b ^ 2 / δ),
    eventually_gt_atTop (4 * c * b * |M| / ε), eventually_gt_atTop 0] with R hR1 hR2 hR3 hR0
  rintro ⟨u, n⟩ ⟨hu, hn⟩
  have hu' : |u| ≤ r := by simpa using hr hu
  have hn' : ‖n‖ = 1 := by simpa using hn
  have hbR : b ^ 2 / R ≤ b := by
    rw [div_le_iff₀ hR0]
    nlinarith
  have hsδ : b ^ 2 / R < δ := by
    rw [div_lt_iff₀ hδ] at hR2
    rw [div_lt_iff₀ hR0]
    linarith
  have key := abs_mul_retardedIntegral_sub_le (η := η) (M := |M|) (u := u) hc hf' hb.le hR0 hR1
    hn' ?_ ?_
  · rw [Real.dist_eq, abs_sub_comm]
    refine key.trans_lt ?_
    have e1 : (4 * π)⁻¹ * (2 * η + 2 * b * |M| / R) * volume.real (closedBall (0 : E3) b) =
        c * (2 * η) + c * (2 * b * |M| / R) := by
      rw [hcdef]
      ring
    have hc1 : 0 < c + 1 := by linarith
    have h1 : c * (2 * η) < ε / 2 := by
      rw [hηdef, show c * (2 * (ε / (4 * (c + 1)))) = ε / 2 * (c / (c + 1)) by
        field_simp
        ring]
      exact mul_lt_of_lt_one_right (by positivity) ((div_lt_one hc1).mpr (by linarith))
    have h2 : c * (2 * b * |M| / R) < ε / 2 := by
      rw [div_lt_iff₀ hε] at hR3
      rw [mul_div_assoc', div_lt_iff₀ hR0]
      linarith
    linarith
  · intro z hz s hs0 hs1
    have h := hδ' _ (mem_farSet hu' hn' hz hs0 (hs1.trans hbR)) _ (mem_farSet_zero hu' hn' hz)
      (by rw [dist_delay z hs0]; exact lt_of_le_of_lt hs1 hsδ)
    rw [Real.dist_eq] at h
    exact h.le
  · intro z hz
    have h := hM _ (mem_farSet_zero hu' hn' hz)
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_abs_self M)

/-- The time derivative along the time line through `(t, z)`. -/
theorem hasDerivAt_timeSlice {f : ℝ × E3 → ℝ} (hf : Differentiable ℝ f) (t : ℝ) (z : E3) :
    HasDerivAt (fun s => f (s, z)) (timeDeriv f (t, z)) t :=
  (hf (t, z)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t z))

/-- **The rate of the far field**: for a `C¹` source with localized support the remainder of the
far field is `O(1/R)`: there is `C` with `|R · Rf(u + R, Rn) − farAmplitude f u n| ≤ C/R` for
large `R`, `u` in a compact set and `n` on the unit sphere. -/
theorem exists_bound_mul_retardedIntegral_sub {a : ℝ} {f : ℝ × E3 → ℝ} (hc : ContDiff ℝ 1 f)
    (hf : LocalizedSupport a f) {K : Set ℝ} (hK : IsCompact K) :
    ∃ C, ∀ᶠ R in atTop, ∀ u ∈ K, ∀ n ∈ sphere (0 : E3) 1,
      |R * retardedIntegral f (u + R, R • n) - farAmplitude f u n| ≤ C / R := by
  set b := max a 1 with hbdef
  have hb : 0 < b := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hf' : LocalizedSupport b f := hf.mono (le_max_left a 1)
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  set S := Icc (-r - 2 * b) (r + b) ×ˢ closedBall (0 : E3) b with hSdef
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hd : Differentiable ℝ f := hc.differentiable (by norm_num)
  have ht : Continuous (timeDeriv f) :=
    (contDiff_timeDeriv (n := 0) (by simpa using hc)).continuous
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hc.continuous.continuousOn
  obtain ⟨M', hM'⟩ := hS.exists_bound_of_continuousOn ht.continuousOn
  refine ⟨(4 * π)⁻¹ * (2 * (|M'| * b ^ 2) + 2 * b * |M|) * volume.real (closedBall (0 : E3) b),
    ?_⟩
  filter_upwards [eventually_ge_atTop (2 * b), eventually_gt_atTop 0] with R hR1 hR0
  intro u hu n hn
  have hu' : |u| ≤ r := by simpa using hr hu
  have hn' : ‖n‖ = 1 := by simpa using hn
  have hbR : b ^ 2 / R ≤ b := by
    rw [div_le_iff₀ hR0]
    nlinarith
  have key := abs_mul_retardedIntegral_sub_le (η := |M'| * (b ^ 2 / R)) (M := |M|) (u := u)
    hc.continuous
    hf' hb.le hR0 hR1 hn' ?_ ?_
  · refine key.trans_eq ?_
    field_simp
  · intro z hz s hs0 hs1
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun t => f (t, z)) (f' := fun t => timeDeriv f (t, z)) (C := |M'|)
      (s := Icc (-r - 2 * b) (r + b))
      (fun t _ => (hasDerivAt_timeSlice hd t z).hasDerivWithinAt)
      (fun t ht => (hM' (t, z) ⟨ht, by simpa using hz⟩).trans (le_abs_self _))
      (convex_Icc _ _) (mem_farSet_zero hu' hn' hz).1
      (mem_farSet hu' hn' hz hs0 (hs1.trans hbR)).1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, show u + inner ℝ n z - s - (u + inner ℝ n z) = -s by
      ring, abs_neg, abs_of_nonneg hs0] at hmvt
    exact hmvt.trans (mul_le_mul_of_nonneg_left hs1 (abs_nonneg _))
  · intro z hz
    have h := hM _ (mem_farSet_zero hu' hn' hz)
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_abs_self M)

/-- The amplitude is bounded for `u` in a compact set and `n` on the unit sphere. -/
theorem exists_bound_farAmplitude {a : ℝ} {f : ℝ × E3 → ℝ} (hc : Continuous f)
    (hf : LocalizedSupport a f) {K : Set ℝ} (hK : IsCompact K) :
    ∃ M, ∀ u ∈ K, ∀ n ∈ sphere (0 : E3) 1, |farAmplitude f u n| ≤ M := by
  set b := max a 1 with hbdef
  have hf' : LocalizedSupport b f := hf.mono (le_max_left a 1)
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  have hS : IsCompact (Icc (-r - 2 * b) (r + b) ×ˢ closedBall (0 : E3) b) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨(4 * π)⁻¹ * M * volume.real (closedBall (0 : E3) b), fun u hu n hn =>
    abs_farAmplitude_le hf' fun z hz => ?_⟩
  have h := hM _ (mem_farSet_zero (by simpa using hr hu) (by simpa using hn) hz)
  rwa [Real.norm_eq_abs] at h

/-! ### The derivatives -/

/-- **The amplitude of a spatial derivative**: `farAmplitude (∂ᵢf) u n = −nᵢ farAmplitude (∂ₜf) u n`
for a `C¹` source with localized support, since `∂ᵢ[f(u + ⟨n, y⟩, y)] = nᵢ ∂ₜf + ∂ᵢf` has the
integral zero. -/
theorem farAmplitude_spaceDeriv {a : ℝ} {f : ℝ × E3 → ℝ} (hc : ContDiff ℝ 1 f)
    (hf : LocalizedSupport a f) (i : Fin 3) (u : ℝ) (n : E3) :
    farAmplitude (spaceDeriv i f) u n = -(n i * farAmplitude (timeDeriv f) u n) := by
  have hL : ∀ y : E3, HasFDerivAt (fun y : E3 => (u + inner ℝ n y, y))
      ((innerSL ℝ n).prod (ContinuousLinearMap.id ℝ E3)) y := fun y =>
    ((innerSL ℝ n).hasFDerivAt.const_add u).prodMk (hasFDerivAt_id y)
  have hW : ContDiff ℝ 1 fun y : E3 => f (u + inner ℝ n y, y) :=
    hc.comp ((contDiff_const.add (contDiff_const.inner ℝ contDiff_id)).prodMk contDiff_id)
  have hd : ∀ y : E3, fderiv ℝ (fun y : E3 => f (u + inner ℝ n y, y)) y
      (EuclideanSpace.single i 1) =
        n i * timeDeriv f (u + inner ℝ n y, y) + spaceDeriv i f (u + inner ℝ n y, y) := by
    intro y
    have h : HasFDerivAt (fun y : E3 => f (u + inner ℝ n y, y))
        ((fderiv ℝ f (u + inner ℝ n y, y)).comp
          ((innerSL ℝ n).prod (ContinuousLinearMap.id ℝ E3))) y := by
      have hfd : HasFDerivAt f (fderiv ℝ f (u + inner ℝ n y, y))
          ((fun y : E3 => (u + inner ℝ n y, y)) y) :=
        ((hc.differentiable (by norm_num)) (u + inner ℝ n y, y)).hasFDerivAt
      exact HasFDerivAt.comp (f := fun y : E3 => (u + inner ℝ n y, y)) y hfd (hL y)
    have hv : ((innerSL ℝ n).prod (ContinuousLinearMap.id ℝ E3)) (EuclideanSpace.single i 1) =
        n i • ((1 : ℝ), (0 : E3)) + ((0 : ℝ), EuclideanSpace.single i 1) := by
      simp only [ContinuousLinearMap.prod_apply, innerSL_apply_apply,
        EuclideanSpace.inner_single_right, ContinuousLinearMap.id_apply]
      ext <;> simp
    rw [h.fderiv, ContinuousLinearMap.comp_apply, hv, map_add, map_smul, smul_eq_mul]
    rfl
  have h0 := integral_fderiv_eq_zero hW (hasCompactSupport_farIntegrand hf u n)
    (EuclideanSpace.single i 1)
  have ht : Continuous (timeDeriv f) :=
    (contDiff_timeDeriv (n := 0) (by simpa using hc)).continuous
  have hs : Continuous (spaceDeriv i f) :=
    (contDiff_spaceDeriv (n := 0) (by simpa using hc) i).continuous
  simp only [hd] at h0
  rw [integral_add ((integrable_farIntegrand ht hf.timeDeriv u n).const_mul (n i))
    (integrable_farIntegrand hs (hf.spaceDeriv i) u n), integral_const_mul] at h0
  rw [farAmplitude, farAmplitude]
  linear_combination (4 * π)⁻¹ * h0

/-- **The time derivative of the far field**: for a `C¹` source with localized support,
`R · ∂ₜ(Rf)(u + R, Rn) → farAmplitude (∂ₜf) u n`, uniformly for `u` in a compact set and `n` on
the unit sphere. -/
theorem tendstoUniformlyOn_mul_timeDeriv_retardedIntegral {a : ℝ} {f : ℝ × E3 → ℝ}
    (hc : ContDiff ℝ 1 f) (hf : LocalizedSupport a f) {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun R (p : ℝ × E3) => R * timeDeriv (retardedIntegral f) (p.1 + R, R • p.2))
      (fun p => farAmplitude (timeDeriv f) p.1 p.2) atTop (K ×ˢ sphere (0 : E3) 1) := by
  rw [timeDeriv_retardedIntegral hc hf.subluminalSupport]
  exact tendstoUniformlyOn_mul_retardedIntegral
    (contDiff_timeDeriv (n := 0) (by simpa using hc)).continuous hf.timeDeriv hK

/-- **The spatial derivatives of the far field**: for a `C¹` source with localized support,
`R · ∂ᵢ(Rf)(u + R, Rn) → −nᵢ farAmplitude (∂ₜf) u n`, uniformly for `u` in a compact set and `n`
on the unit sphere. -/
theorem tendstoUniformlyOn_mul_spaceDeriv_retardedIntegral {a : ℝ} {f : ℝ × E3 → ℝ}
    (hc : ContDiff ℝ 1 f) (hf : LocalizedSupport a f) {K : Set ℝ} (hK : IsCompact K)
    (i : Fin 3) :
    TendstoUniformlyOn
      (fun R (p : ℝ × E3) => R * spaceDeriv i (retardedIntegral f) (p.1 + R, R • p.2))
      (fun p => -(p.2 i * farAmplitude (timeDeriv f) p.1 p.2)) atTop
      (K ×ˢ sphere (0 : E3) 1) := by
  rw [spaceDeriv_retardedIntegral hc hf.subluminalSupport i]
  have h := tendstoUniformlyOn_mul_retardedIntegral
    (contDiff_spaceDeriv (n := 0) (by simpa using hc) i).continuous (hf.spaceDeriv i) hK
  simp only [farAmplitude_spaceDeriv hc hf i] at h
  exact h

/-- The rate of the time derivative of the far field: for a `C²` source with localized support
the remainder of `R · ∂ₜ(Rf)(u + R, Rn) → farAmplitude (∂ₜf) u n` is `O(1/R)`, uniformly. -/
theorem exists_bound_mul_timeDeriv_retardedIntegral_sub {a : ℝ} {f : ℝ × E3 → ℝ}
    (hc : ContDiff ℝ 2 f) (hf : LocalizedSupport a f) {K : Set ℝ} (hK : IsCompact K) :
    ∃ C, ∀ᶠ R in atTop, ∀ u ∈ K, ∀ n ∈ sphere (0 : E3) 1,
      |R * timeDeriv (retardedIntegral f) (u + R, R • n) - farAmplitude (timeDeriv f) u n| ≤
        C / R := by
  rw [timeDeriv_retardedIntegral (hc.of_le (by norm_num)) hf.subluminalSupport]
  exact exists_bound_mul_retardedIntegral_sub (contDiff_timeDeriv (n := 1) hc) hf.timeDeriv hK

/-- The rate of the spatial derivatives of the far field: for a `C²` source with localized
support the remainder of `R · ∂ᵢ(Rf)(u + R, Rn) → −nᵢ farAmplitude (∂ₜf) u n` is `O(1/R)`,
uniformly. -/
theorem exists_bound_mul_spaceDeriv_retardedIntegral_add {a : ℝ} {f : ℝ × E3 → ℝ}
    (hc : ContDiff ℝ 2 f) (hf : LocalizedSupport a f) {K : Set ℝ} (hK : IsCompact K)
    (i : Fin 3) :
    ∃ C, ∀ᶠ R in atTop, ∀ u ∈ K, ∀ n ∈ sphere (0 : E3) 1,
      |R * spaceDeriv i (retardedIntegral f) (u + R, R • n) +
        n i * farAmplitude (timeDeriv f) u n| ≤ C / R := by
  rw [spaceDeriv_retardedIntegral (hc.of_le (by norm_num)) hf.subluminalSupport i]
  obtain ⟨C, hC⟩ := exists_bound_mul_retardedIntegral_sub (contDiff_spaceDeriv (n := 1) hc i)
    (hf.spaceDeriv i) hK
  refine ⟨C, hC.mono fun R hR u hu n hn => ?_⟩
  have h := hR u hu n hn
  rwa [farAmplitude_spaceDeriv (hc.of_le (by norm_num)) hf i, sub_neg_eq_add] at h

end ProjectAinos.SmoothGeometry.Wave
