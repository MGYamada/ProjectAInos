/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Topology.Algebra.Order.Floor

/-!
# A periodic local homeomorphism is injective near a torus on which it is

Let `Ψ(J, φ)` have the period `T` in each of the angles `φ`, for `J` in an open
set `B`. Let it be continuous and locally injective at the points `(J₀, φ)`,
and let two angles give the same point `Ψ(J₀, ·)` only when they differ by
multiples of `T`. `exists_injOn_modPeriod`: then the same holds for `J` in a
neighbourhood of `J₀`: `Ψ(J, φ) = Ψ(J′, φ′)` only when `J = J′` and the angles
differ by multiples of `T`. The angles are reduced to the compact cube
`[0, T]^ι`, and a sequence of pairs of distinct points with the same image
would converge to one point, at which the map is locally injective.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology

namespace ProjectAInos.SmoothGeometry

variable {X : Type*} [TopologicalSpace X] [T2Space X] {ι : Type*} [Fintype ι]

/-- Injectivity modulo the periods spreads from a torus to its neighbourhood. -/
theorem exists_injOn_modPeriod {Ψ : (ι → ℝ) × (ι → ℝ) → X} {B : Set (ι → ℝ)} {J₀ : ι → ℝ}
    {T : ℝ} (hT : 0 < T) (hB : IsOpen B) (hJ₀ : J₀ ∈ B)
    (hcont : ∀ φ : ι → ℝ, ContinuousAt Ψ (J₀, φ))
    (hloc : ∀ φ : ι → ℝ, ∃ U ∈ 𝓝 ((J₀, φ) : (ι → ℝ) × (ι → ℝ)), InjOn Ψ U)
    (hper : ∀ J ∈ B, ∀ (φ : ι → ℝ) (n : ι → ℤ), Ψ (J, fun k => φ k + T * n k) = Ψ (J, φ))
    (heq : ∀ φ φ' : ι → ℝ, Ψ (J₀, φ) = Ψ (J₀, φ') → ∀ k, ∃ n : ℤ, φ k - φ' k = T * n) :
    ∃ B' : Set (ι → ℝ), B' ⊆ B ∧ IsOpen B' ∧ J₀ ∈ B' ∧
      ∀ J ∈ B', ∀ J' ∈ B', ∀ φ φ' : ι → ℝ, Ψ (J, φ) = Ψ (J', φ') →
        J = J' ∧ ∀ k, ∃ n : ℤ, φ k - φ' k = T * n := by
  by_contra hcon
  -- the reduction of the angles to the cube
  obtain ⟨red, hred⟩ : ∃ red : (ι → ℝ) → ι → ℝ,
      red = fun φ k => φ k + T * ((-⌊φ k / T⌋ : ℤ) : ℝ) := ⟨_, rfl⟩
  have hredΨ : ∀ J ∈ B, ∀ φ : ι → ℝ, Ψ (J, red φ) = Ψ (J, φ) := fun J hJ φ => by
    rw [hred]
    exact hper J hJ φ fun k => -⌊φ k / T⌋
  have hredmem : ∀ (φ : ι → ℝ) (k : ι), red φ k ∈ Icc 0 T := by
    intro φ k
    have e : red φ k = T * Int.fract (φ k / T) := by
      rw [hred]
      change φ k + T * ((-⌊φ k / T⌋ : ℤ) : ℝ) = T * (φ k / T - ⌊φ k / T⌋)
      rw [Int.cast_neg, mul_sub, mul_div_assoc', mul_div_cancel_left₀ _ hT.ne']
      ring
    rw [e]
    exact ⟨mul_nonneg hT.le (Int.fract_nonneg _),
      (mul_le_mul_of_nonneg_left (Int.fract_lt_one _).le hT.le).trans (mul_one T).le⟩
  have hredlat : ∀ (φ φ' : ι → ℝ) (k : ι), (∃ m : ℤ, red φ k - red φ' k = T * m) →
      ∃ m : ℤ, φ k - φ' k = T * m := by
    rintro φ φ' k ⟨m, hm⟩
    rw [hred] at hm
    refine ⟨m + ⌊φ k / T⌋ - ⌊φ' k / T⌋, ?_⟩
    have hm' : φ k + T * ((-⌊φ k / T⌋ : ℤ) : ℝ) - (φ' k + T * ((-⌊φ' k / T⌋ : ℤ) : ℝ)) =
        T * m := hm
    push_cast at hm' ⊢
    linarith
  have hex : ∀ n : ℕ, ∃ J ∈ B, ∃ J' ∈ B, ∃ φ φ' : ι → ℝ, dist J J₀ < 1 / ((n : ℝ) + 1) ∧
      dist J' J₀ < 1 / ((n : ℝ) + 1) ∧ (∀ k, φ k ∈ Icc 0 T) ∧ (∀ k, φ' k ∈ Icc 0 T) ∧
      Ψ (J, φ) = Ψ (J', φ') ∧ ¬(J = J' ∧ ∀ k, ∃ m : ℤ, φ k - φ' k = T * m) := by
    intro n
    by_contra hn
    refine hcon ⟨B ∩ Metric.ball J₀ (1 / ((n : ℝ) + 1)), inter_subset_left,
      hB.inter Metric.isOpen_ball, ⟨hJ₀, Metric.mem_ball_self (by positivity)⟩, ?_⟩
    intro J hJ J' hJ' φ φ' hΨ
    by_contra hbad
    exact hn ⟨J, hJ.1, J', hJ'.1, red φ, red φ', hJ.2, hJ'.2, hredmem φ, hredmem φ',
      (hredΨ J hJ.1 φ).trans (hΨ.trans (hredΨ J' hJ'.1 φ').symm),
      fun hlat => hbad ⟨hlat.1, fun k => hredlat φ φ' k (hlat.2 k)⟩⟩
  choose Js hJs J's hJ's φs φ's hd hd' hφ hφ' hΨ hbad using hex
  -- a convergent subsequence of the angles
  have hK : IsCompact ((Set.pi univ fun _ : ι => Icc (0 : ℝ) T) ×ˢ
      (Set.pi univ fun _ : ι => Icc (0 : ℝ) T)) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc)
  obtain ⟨⟨ψ, ψ'⟩, -, σ, hσ, hlim⟩ := hK.tendsto_subseq (x := fun n => (φs n, φ's n))
    (fun n => ⟨fun k _ => hφ n k, fun k _ => hφ' n k⟩)
  have hφlim : Tendsto (fun n => φs (σ n)) atTop (𝓝 ψ) := (continuous_fst.tendsto _).comp hlim
  have hφ'lim : Tendsto (fun n => φ's (σ n)) atTop (𝓝 ψ') :=
    (continuous_snd.tendsto _).comp hlim
  have hzero : Tendsto (fun n : ℕ => 1 / ((σ n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hσ.tendsto_atTop
  have hJlim : Tendsto (fun n => Js (σ n)) atTop (𝓝 J₀) :=
    tendsto_iff_dist_tendsto_zero.mpr
      (squeeze_zero (fun _ => dist_nonneg) (fun n => (hd (σ n)).le) hzero)
  have hJ'lim : Tendsto (fun n => J's (σ n)) atTop (𝓝 J₀) :=
    tendsto_iff_dist_tendsto_zero.mpr
      (squeeze_zero (fun _ => dist_nonneg) (fun n => (hd' (σ n)).le) hzero)
  have hw : Tendsto (fun n => ((Js (σ n), φs (σ n)) : (ι → ℝ) × (ι → ℝ))) atTop
      (𝓝 (J₀, ψ)) := hJlim.prodMk_nhds hφlim
  have hw' : Tendsto (fun n => ((J's (σ n), φ's (σ n)) : (ι → ℝ) × (ι → ℝ))) atTop
      (𝓝 (J₀, ψ')) := hJ'lim.prodMk_nhds hφ'lim
  -- the limits have the same image
  have h1 := (hcont ψ).tendsto.comp hw
  have h2 := (hcont ψ').tendsto.comp hw'
  have hfun : (Ψ ∘ fun n => ((Js (σ n), φs (σ n)) : (ι → ℝ) × (ι → ℝ))) =
      Ψ ∘ fun n => ((J's (σ n), φ's (σ n)) : (ι → ℝ) × (ι → ℝ)) :=
    funext fun n => hΨ (σ n)
  rw [hfun] at h1
  have hΨ₀ := tendsto_nhds_unique h1 h2
  choose m hm using heq ψ ψ' hΨ₀
  have hψ : ψ = fun k => ψ' k + T * m k := funext fun k => by linarith [hm k]
  have hv : Tendsto (fun n => ((J's (σ n), fun k => φ's (σ n) k + T * m k) :
      (ι → ℝ) × (ι → ℝ))) atTop (𝓝 (J₀, ψ)) := by
    have hc : Tendsto (fun n => (fun k => φ's (σ n) k + T * m k : ι → ℝ)) atTop
        (𝓝 (fun k => ψ' k + T * m k)) :=
      hφ'lim.add_const (fun k => T * (m k : ℝ))
    rw [hψ]
    exact hJ'lim.prodMk_nhds hc
  obtain ⟨U, hU, hinj⟩ := hloc ψ
  obtain ⟨n, hn1, hn2⟩ := ((hw.eventually_mem hU).and (hv.eventually_mem hU)).exists
  have himg : Ψ (Js (σ n), φs (σ n)) = Ψ (J's (σ n), fun k => φ's (σ n) k + T * m k) :=
    (hΨ (σ n)).trans (hper _ (hJ's (σ n)) _ m).symm
  have hpt := hinj hn1 hn2 himg
  have hJeq : Js (σ n) = J's (σ n) := congrArg Prod.fst hpt
  have hφeq : φs (σ n) = fun k => φ's (σ n) k + T * m k := congrArg Prod.snd hpt
  refine hbad (σ n) ⟨hJeq, fun k => ⟨m k, ?_⟩⟩
  have h3 := congrFun hφeq k
  beta_reduce at h3
  linarith

end ProjectAInos.SmoothGeometry
