/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Algebra.Order.Field

/-!
# The Riccati inequality `θ′ ≤ −θ²/n` blows up in finite time

A real function `θ` with `θ′ ≤ −θ²/n`, `n > 0`, on an interval `[t₀, t₀ + T]` and `θ(t₀) < 0`
stays negative and below the solution of the equation `θ′ = −θ²/n` with the same initial value:
`1/θ − t/n` is nondecreasing. Hence the interval is shorter than `n/|θ(t₀)|`. It is the scalar
comparison behind the focusing of the time lines of a synchronous reference system
(Landau–Lifshitz, §97, (97.15)).

* `RiccatiComparison.antitoneOn`: such a `θ` is nonincreasing.
* `RiccatiComparison.inv_add_le`: `θ < 0` and `1/θ(t₀) + (t − t₀)/n ≤ 1/θ(t)`.
* `RiccatiComparison.le_div`: `θ(t) ≤ n θ(t₀)/(n + θ(t₀)(t − t₀))`, with a positive denominator.
* `RiccatiComparison.lt_div_abs`: **the interval is shorter than `n/|θ(t₀)|`**.
* `RiccatiComparison.tendsto_atBot`: a solution on `[t₀, t₀ + n/|θ(t₀)|)` tends to `−∞` at the
  right end.
* `RiccatiComparison.hasDerivAt_div_sub`, `RiccatiComparison.div_abs_div_sub`: the solution
  `n/(t − t₁)` of the equation attains the bound, `n/|θ(t₀)| = t₁ − t₀`.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace ProjectAinos.SmoothGeometry.RiccatiComparison

variable {θ θ' : ℝ → ℝ} {n t₀ T : ℝ}

/-- **A solution of `θ′ ≤ −θ²/n` is nonincreasing.** -/
theorem antitoneOn (hn : 0 < n) (hc : ContinuousOn θ (Icc t₀ (t₀ + T)))
    (hd : ∀ t ∈ Ioo t₀ (t₀ + T), HasDerivAt θ (θ' t) t)
    (hle : ∀ t ∈ Ioo t₀ (t₀ + T), θ' t ≤ -θ t ^ 2 / n) : AntitoneOn θ (Icc t₀ (t₀ + T)) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hc ?_ ?_
  · rw [interior_Icc]
    exact fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    rw [(hd t ht).deriv]
    have h := hle t ht
    have hsq : 0 ≤ θ t ^ 2 / n := div_nonneg (sq_nonneg _) hn.le
    rw [neg_div] at h
    linarith

/-- **The comparison with the equation**: `θ` stays negative and `1/θ − t/n` is nondecreasing,
`1/θ(t₀) + (t − t₀)/n ≤ 1/θ(t)`. -/
theorem inv_add_le (hn : 0 < n) (hc : ContinuousOn θ (Icc t₀ (t₀ + T)))
    (hd : ∀ t ∈ Ioo t₀ (t₀ + T), HasDerivAt θ (θ' t) t)
    (hle : ∀ t ∈ Ioo t₀ (t₀ + T), θ' t ≤ -θ t ^ 2 / n) (h0 : θ t₀ < 0) {t : ℝ}
    (ht : t ∈ Icc t₀ (t₀ + T)) : θ t < 0 ∧ (θ t₀)⁻¹ + (t - t₀) / n ≤ (θ t)⁻¹ := by
  have hmem : t₀ ∈ Icc t₀ (t₀ + T) := ⟨le_rfl, ht.1.trans ht.2⟩
  have hanti := antitoneOn hn hc hd hle
  have hneg : ∀ s ∈ Icc t₀ (t₀ + T), θ s < 0 := fun s hs =>
    (hanti hmem hs hs.1).trans_lt h0
  refine ⟨hneg t ht, ?_⟩
  have hmono : MonotoneOn (fun s => (θ s)⁻¹ - s / n) (Icc t₀ (t₀ + T)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · exact (hc.inv₀ fun s hs => (hneg s hs).ne).sub (continuousOn_id.div_const n)
    · rw [interior_Icc]
      intro s hs
      have hs' : s ∈ Icc t₀ (t₀ + T) := Ioo_subset_Icc_self hs
      exact (((hd s hs).fun_inv (hneg s hs').ne).differentiableAt.sub
        (differentiableAt_id.div_const n)).differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      have hs' : s ∈ Icc t₀ (t₀ + T) := Ioo_subset_Icc_self hs
      have hD : HasDerivAt (fun s => (θ s)⁻¹ - s / n) (-θ' s / θ s ^ 2 - 1 / n) s :=
        ((hd s hs).fun_inv (hneg s hs').ne).sub ((hasDerivAt_id s).div_const n)
      rw [hD.deriv]
      have hpos : 0 < θ s ^ 2 := by
        have := hneg s hs'
        nlinarith
      have h := hle s hs
      rw [neg_div] at h
      rw [sub_nonneg, le_div_iff₀ hpos]
      have : 1 / n * θ s ^ 2 = θ s ^ 2 / n := by ring
      linarith
  have h := hmono hmem ht ht.1
  simp only at h
  have : (θ t₀)⁻¹ + (t - t₀) / n = (θ t₀)⁻¹ - t₀ / n + t / n := by ring
  linarith

/-- **The bound by the solution of the equation**: on `[t₀, t₀ + T]`,
`n + θ(t₀)(t − t₀) > 0` and `θ(t) ≤ n θ(t₀)/(n + θ(t₀)(t − t₀))`. -/
theorem le_div (hn : 0 < n) (hc : ContinuousOn θ (Icc t₀ (t₀ + T)))
    (hd : ∀ t ∈ Ioo t₀ (t₀ + T), HasDerivAt θ (θ' t) t)
    (hle : ∀ t ∈ Ioo t₀ (t₀ + T), θ' t ≤ -θ t ^ 2 / n) (h0 : θ t₀ < 0) {t : ℝ}
    (ht : t ∈ Icc t₀ (t₀ + T)) :
    0 < n + θ t₀ * (t - t₀) ∧ θ t ≤ n * θ t₀ / (n + θ t₀ * (t - t₀)) := by
  obtain ⟨hneg, hq⟩ := inv_add_le hn hc hd hle h0 ht
  set q := (θ t₀)⁻¹ + (t - t₀) / n with hq_def
  have hqneg : q < 0 := hq.trans_lt (inv_lt_zero.mpr hneg)
  have hθ0 : θ t₀ ≠ 0 := h0.ne
  have hden : n + θ t₀ * (t - t₀) = n * θ t₀ * q := by
    rw [hq_def]
    field_simp
  have hnθ : n * θ t₀ < 0 := mul_neg_of_pos_of_neg hn h0
  have hpos : 0 < n + θ t₀ * (t - t₀) := by
    rw [hden]
    exact mul_pos_of_neg_of_neg hnθ hqneg
  refine ⟨hpos, ?_⟩
  rw [hden, div_mul_cancel_left₀ hnθ.ne]
  have h1 : (θ t)⁻¹⁻¹ ≤ q⁻¹ := (inv_le_inv_of_neg (inv_lt_zero.mpr hneg) hqneg).mpr hq
  rwa [inv_inv] at h1

/-- **A solution of `θ′ ≤ −θ²/n` with `θ(t₀) < 0` lives less than `n/|θ(t₀)|`**: if it is defined
on `[t₀, t₀ + T]`, then `T < n/|θ(t₀)|` (Landau–Lifshitz, (97.15)). -/
theorem lt_div_abs (hn : 0 < n) (hc : ContinuousOn θ (Icc t₀ (t₀ + T)))
    (hd : ∀ t ∈ Ioo t₀ (t₀ + T), HasDerivAt θ (θ' t) t)
    (hle : ∀ t ∈ Ioo t₀ (t₀ + T), θ' t ≤ -θ t ^ 2 / n) (h0 : θ t₀ < 0) :
    T < n / |θ t₀| := by
  have habs : 0 < |θ t₀| := abs_pos.mpr h0.ne
  rcases lt_or_ge T 0 with hT | hT
  · exact hT.trans (div_pos hn habs)
  · have h := (le_div hn hc hd hle h0 ⟨by linarith, le_rfl⟩).1
    rw [abs_of_neg h0, lt_div_iff₀ (neg_pos.mpr h0)]
    have : θ t₀ * (t₀ + T - t₀) = θ t₀ * T := by ring
    nlinarith

/-- **A solution blows up at the bound**: if `θ′ ≤ −θ²/n`, `θ(t₀) < 0`, on
`[t₀, t₀ + n/|θ(t₀)|)`, then `θ → −∞` at the right end. -/
theorem tendsto_atBot (hn : 0 < n) (h0 : θ t₀ < 0)
    (hc : ContinuousOn θ (Ico t₀ (t₀ + n / |θ t₀|)))
    (hd : ∀ t ∈ Ioo t₀ (t₀ + n / |θ t₀|), HasDerivAt θ (θ' t) t)
    (hle : ∀ t ∈ Ioo t₀ (t₀ + n / |θ t₀|), θ' t ≤ -θ t ^ 2 / n) :
    Tendsto θ (𝓝[<] (t₀ + n / |θ t₀|)) atBot := by
  set t₁ := t₀ + n / |θ t₀| with ht₁
  have habs : 0 < |θ t₀| := abs_pos.mpr h0.ne
  have hlt : t₀ < t₁ := by
    rw [ht₁]
    linarith [div_pos hn habs]
  have hbound : ∀ t ∈ Ioo t₀ t₁, θ t ≤ n * (t - t₁)⁻¹ := by
    intro t ht
    have hsub : Icc t₀ (t₀ + (t - t₀)) ⊆ Ico t₀ t₁ := by
      intro s hs
      exact ⟨hs.1, by linarith [hs.2, ht.2]⟩
    have hsub' : Ioo t₀ (t₀ + (t - t₀)) ⊆ Ioo t₀ t₁ := by
      intro s hs
      exact ⟨hs.1, by linarith [hs.2, ht.2]⟩
    have h := (le_div (T := t - t₀) hn (hc.mono hsub) (fun s hs => hd s (hsub' hs))
      (fun s hs => hle s (hsub' hs)) h0 ⟨ht.1.le, by linarith⟩).2
    have hθ0 : θ t₀ ≠ 0 := h0.ne
    have hden : n + θ t₀ * (t - t₀) = θ t₀ * (t - t₁) := by
      rw [ht₁, abs_of_neg h0]
      field_simp
      ring
    have hne : t - t₁ ≠ 0 := sub_ne_zero.mpr ht.2.ne
    have heq : n * θ t₀ / (θ t₀ * (t - t₁)) = n * (t - t₁)⁻¹ := by
      field_simp
    rwa [hden, heq] at h
  have hlim : Tendsto (fun t => n * (t - t₁)⁻¹) (𝓝[<] t₁) atBot := by
    refine Tendsto.const_mul_atBot hn (tendsto_inv_nhdsLT_zero.comp ?_)
    have h1 : Tendsto (fun t => t - t₁) (𝓝[<] t₁) (𝓝 0) := by
      have h := (continuous_sub_right t₁).tendsto t₁
      rw [sub_self] at h
      exact h.mono_left nhdsWithin_le_nhds
    refine tendsto_nhdsWithin_iff.mpr ⟨h1, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact sub_neg.mpr ht
  refine tendsto_atBot_mono' _ ?_ hlim
  filter_upwards [Ioo_mem_nhdsLT hlt] with t ht
  exact hbound t ht

/-- **The solution of the equation**: `θ(t) = n/(t − t₁)` solves `θ′ = −θ²/n` away from `t₁`. -/
theorem hasDerivAt_div_sub (hn : n ≠ 0) {t₁ t : ℝ} (ht : t ≠ t₁) :
    HasDerivAt (fun s => n / (s - t₁)) (-(n / (t - t₁)) ^ 2 / n) t := by
  have hne : t - t₁ ≠ 0 := sub_ne_zero.mpr ht
  have h := ((hasDerivAt_id t).sub_const t₁).fun_inv hne
  have h2 := h.const_mul n
  simp only [id] at h2
  convert h2 using 1
  · funext s
    simp [div_eq_mul_inv]
  · field_simp

/-- **The bound is attained**: for `t₀ < t₁`, the solution `n/(t − t₁)` is negative at `t₀` and
`n/|θ(t₀)| = t₁ − t₀`, the time at which it blows up. -/
theorem div_abs_div_sub (hn : 0 < n) {t₁ : ℝ} (h : t₀ < t₁) :
    n / (t₀ - t₁) < 0 ∧ n / |n / (t₀ - t₁)| = t₁ - t₀ := by
  have hneg : t₀ - t₁ < 0 := sub_neg.mpr h
  refine ⟨div_neg_of_pos_of_neg hn hneg, ?_⟩
  rw [abs_of_neg (div_neg_of_pos_of_neg hn hneg)]
  field_simp
  ring

end ProjectAinos.SmoothGeometry.RiccatiComparison
