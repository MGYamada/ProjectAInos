/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Optics.Error
public import ProjectAinos.SpecialFunctions.OscillatoryAverage
import Mathlib.Tactic

/-! # Energy of a single real geometrical-optics wave (ED §58)

At a fixed time, the spatial phase gradient is required to be nonzero on the closed support
of the amplitudes. The mean-square estimate gives half the leading energy of the quadrature
pair, including both its time derivative and all its spatial derivatives.
-/

@[expose] public section
noncomputable section

open Complex Set MeasureTheory Filter
open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics.Optics.Limits

open ProjectAinos.SmoothGeometry
local notation "E3" => EuclideanSpace ℝ (Fin 3)

private def part (f : ℝ × E3 → ℝ) (i : Fin 4) : ℝ × E3 → ℝ :=
  Fin.cases (Wave.timeDeriv f) (fun j => Wave.spaceDeriv j f) i

private theorem smooth_part {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin 4) :
    ContDiff ℝ ∞ (part f i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact Wave.contDiff_timeDeriv (n := ∞) (by simpa using hf)
  · exact Wave.contDiff_spaceDeriv (n := ∞) (by simpa using hf) j

private theorem supp_part {T R : ℝ} {f : ℝ × E3 → ℝ} (hT : 0 < T) (hf : ContDiff ℝ 1 f)
    (hs : Wave.BallSupportOn T R f) (i : Fin 4) : Wave.BallSupportOn T R (part f i) :=
  Fin.cases (hs.timeDeriv hT hf) (fun j => hs.spaceDeriv (hf.differentiable one_ne_zero) j) i

private theorem quad (f : ℝ × E3 → ℝ) (p : ℝ × E3) :
    Wave.gradNormSq f p = ∑ i : Fin 4, part f i p ^ 2 := by
  rw [Fin.sum_univ_succ]
  rfl

private theorem slice {f : ℝ × E3 → ℝ} {t : ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun x : E3 => f (t,x) := hf.comp (contDiff_const.prodMk contDiff_id)

private theorem formula {a b ψ : ℝ × E3 → ℝ} {p : ℝ × E3}
    (ha : DifferentiableAt ℝ a p) (hb : DifferentiableAt ℝ b p) (hψ : DifferentiableAt ℝ ψ p)
    (ε : ℝ) (i : Fin 4) : part (Wave.highFrequencyWave a b ψ ε) i p =
      ε⁻¹ * (part ψ i p * (b p * Real.cos (ψ p / ε) - a p * Real.sin (ψ p / ε))) +
      (part a i p * Real.cos (ψ p / ε) + part b i p * Real.sin (ψ p / ε)) :=
  Fin.cases (Wave.timeDeriv_highFrequencyWave ha hb hψ ε)
    (fun j => Wave.spaceDeriv_highFrequencyWave ha hb hψ ε j) i

private theorem one_part {T R t : ℝ} {a b ψ : ℝ × E3 → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hψ : ContDiff ℝ ∞ ψ)
    (hT : 0 < T) (ht : t ∈ Icc 0 T)
    (has : Wave.BallSupportOn T R a) (hbs : Wave.BallSupportOn T R b)
    (hn : ∀ x ∈ tsupport (fun y => a (t,y)) ∪ tsupport (fun y => b (t,y)),
      fderiv ℝ (fun y => ψ (t,y)) x ≠ 0) (i : Fin 4) :
    Tendsto (fun ε : ℝ => ∫ x, (ε * part (Wave.highFrequencyWave a b ψ ε) i (t,x)) ^ 2)
      (𝓝[≠] 0) (𝓝 ((∫ x, (a (t,x) ^ 2 + b (t,x) ^ 2) * part ψ i (t,x) ^ 2) / 2)) := by
  let g (x : E3) : ℂ := (part ψ i (t,x) : ℂ) * (b (t,x) + (a (t,x) : ℂ) * I)
  let h (x : E3) : ℂ := (part a i (t,x) : ℂ) - (part b i (t,x) : ℂ) * I
  have hc {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ ∞ f) :
      ContDiff ℝ ∞ (fun x : E3 => (f (t,x) : ℂ)) := ofRealCLM.contDiff.comp (slice hf)
  have hg : ContDiff ℝ ∞ g := (hc (smooth_part hψ i)).mul ((hc hb).add ((hc ha).mul contDiff_const))
  have hh : Continuous h :=
    ((hc (smooth_part ha i)).sub ((hc (smooth_part hb i)).mul contDiff_const)).continuous
  have outside {f : ℝ × E3 → ℝ} (hs : Wave.BallSupportOn T R f) {x : E3}
      (hx : x ∉ Metric.closedBall 0 R) : f (t,x) = 0 :=
    hs t ht x (by rwa [mem_closedBall_zero_iff, not_le] at hx)
  have cg : HasCompactSupport g := HasCompactSupport.intro (isCompact_closedBall 0 R) fun x hx => by
    simp [g, outside has hx, outside hbs hx]
  have ch : HasCompactSupport h := HasCompactSupport.intro (isCompact_closedBall 0 R) fun x hx => by
    simp [h, outside (supp_part hT (ha.of_le (by simp)) has i) hx,
      outside (supp_part hT (hb.of_le (by simp)) hbs i) hx]
  have hs : tsupport g ⊆ tsupport (fun y => a (t,y)) ∪ tsupport (fun y => b (t,y)) := by
    apply ((isClosed_tsupport _).union (isClosed_tsupport _)).closure_subset_iff.mpr
    intro x hx
    by_contra hout
    simp only [mem_union, not_or] at hout
    exact hx (by simp [g, image_eq_zero_of_notMem_tsupport hout.1,
      image_eq_zero_of_notMem_tsupport hout.2])
  have lim := SpecialFunctions.Oscillatory.tendsto_real_square (slice hψ) hg cg
    (fun x hx => hn x (hs hx)) hh ch
  have norm_g (x : E3) : ‖g x‖ ^ 2 = (a (t,x)^2 + b (t,x)^2) * part ψ i (t,x)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [g, Complex.mul_re, Complex.mul_im]
    ring
  simp_rw [norm_g] at lim
  apply lim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : ε ≠ 0)
  apply integral_congr_ae
  filter_upwards with x
  congr 1
  rw [formula (ha.differentiable (by simp) _) (hb.differentiable (by simp) _)
    (hψ.differentiable (by simp) _)]
  rw [show I / (ε : ℂ) * ↑(ψ (t,x)) = ↑(ψ (t,x) / ε) * I by push_cast; ring,
    exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [g, h, mul_re, mul_im, sub_re, sub_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im]
  field_simp [hε]
  ring

/-- At a nonstationary spatial phase the normalized energy of a single real wave converges to
half the leading energy of the pair. -/
theorem tendsto_sq_mul_energy_single {T R : ℝ} {a b ψ : ℝ × E3 → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hψ : ContDiff ℝ ∞ ψ)
    (hT : 0 < T) (has : Wave.BallSupportOn T R a) (hbs : Wave.BallSupportOn T R b)
    {t : ℝ} (ht : t ∈ Icc 0 T)
    (hn : ∀ x ∈ tsupport (fun y => a (t,y)) ∪ tsupport (fun y => b (t,y)),
      fderiv ℝ (fun y => ψ (t,y)) x ≠ 0) :
    Tendsto (fun ε => ε ^ 2 * Wave.energy (Wave.highFrequencyWave a b ψ ε) t)
      (𝓝[≠] 0) (𝓝 (leadingEnergy a b ψ t / 2)) := by
  let w := Wave.highFrequencyWave a b ψ
  have iw (ε : ℝ) (i : Fin 4) : Integrable (fun x => (ε * part (w ε) i (t,x)) ^ 2) := by
    have hw : ContDiff ℝ ∞ (w ε) := contDiff_iff_contDiffAt.mpr fun p =>
      Wave.contDiffAt_highFrequencyWave ha.contDiffAt hb.contDiffAt hψ.contDiffAt ε
    have hs := supp_part hT (hw.of_le (by simp)) (ballSupportOn_highFrequencyWave has hbs ψ ε) i
    exact (((hs.mul_left (fun _ => ε)).pow two_ne_zero).integrable
      ((continuous_const.mul (smooth_part hw i).continuous).pow 2) ht)
  have il (i : Fin 4) : Integrable (fun x => (a (t,x) ^ 2 + b (t,x) ^ 2) * part ψ i (t,x) ^ 2) :=
    (((has.pow two_ne_zero).add (hbs.pow two_ne_zero)).mul_right _).integrable
      (((ha.continuous.pow 2).add (hb.continuous.pow 2)).mul
        ((smooth_part hψ i).continuous.pow 2)) ht
  have he (ε : ℝ) : ε ^ 2 * Wave.energy (w ε) t = (1/2 : ℝ) *
      ∑ i : Fin 4, ∫ x, (ε * part (w ε) i (t,x)) ^ 2 := by
    rw [← integral_finsetSum _ fun i _ => iw ε i]
    unfold Wave.energy
    simp_rw [quad, mul_pow, ← Finset.mul_sum, integral_const_mul]
    ring
  have hl : leadingEnergy a b ψ t / 2 = (1/2 : ℝ) *
      ∑ i : Fin 4, (∫ x, (a (t,x) ^ 2 + b (t,x) ^ 2) * part ψ i (t,x) ^ 2) / 2 := by
    rw [← Finset.sum_div, ← integral_finsetSum _ fun i _ => il i]
    unfold leadingEnergy
    simp_rw [quad, ← Finset.mul_sum]
    ring
  simp_rw [show Wave.highFrequencyWave a b ψ = w from rfl, he, hl]
  exact (tendsto_finsetSum _ fun i _ => one_part ha hb hψ hT ht has hbs hn i).const_mul _

/-- A positive leading intensity gives a quantitative lower bound for all sufficiently short
wavelengths of the single real wave. -/
theorem eventually_energy_single_ge {T R : ℝ} {a b ψ : ℝ × E3 → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hψ : ContDiff ℝ ∞ ψ)
    (hT : 0 < T) (has : Wave.BallSupportOn T R a) (hbs : Wave.BallSupportOn T R b)
    {t : ℝ} (ht : t ∈ Icc 0 T)
    (hn : ∀ x ∈ tsupport (fun y => a (t,y)) ∪ tsupport (fun y => b (t,y)),
      fderiv ℝ (fun y => ψ (t,y)) x ≠ 0) (hL : 0 < leadingEnergy a b ψ t) :
    ∀ᶠ ε : ℝ in 𝓝[≠] 0,
      leadingEnergy a b ψ t / (4 * ε ^ 2) ≤ Wave.energy (Wave.highFrequencyWave a b ψ ε) t := by
  have h := (tendsto_sq_mul_energy_single ha hb hψ hT has hbs ht hn).eventually_const_lt
    (show leadingEnergy a b ψ t / 4 < leadingEnergy a b ψ t / 2 by linarith)
  filter_upwards [h, self_mem_nhdsWithin] with ε hε (h0 : ε ≠ 0)
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

/-- A transported nonzero bump gives a concrete single, linearly polarized real wave with
a strictly positive energy coefficient on every time slice of the slab. -/
theorem eventually_energy_single_plane_bump {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∀ᶠ ε : ℝ in 𝓝[≠] 0,
      leadingEnergy (planeAmplitude Wave.spaceBump) (planeAmplitude fun _ => 0) planePhase t /
        (4 * ε ^ 2) ≤ Wave.energy (Wave.highFrequencyWave (planeAmplitude Wave.spaceBump)
          (planeAmplitude fun _ => 0) planePhase ε) t := by
  apply eventually_energy_single_ge (R := 2 + T) (contDiff_planeAmplitude Wave.spaceBump.contDiff)
    (contDiff_planeAmplitude contDiff_const) contDiff_planePhase hT
    (ballSupportOn_planeAmplitude (r := 2) (fun y hy => Wave.spaceBump.zero_of_le_dist
      (by rw [dist_zero_right]; exact hy.le)) T)
    (ballSupportOn_planeAmplitude (r := 2) (fun _ _ => rfl) T) ht _
    (leadingEnergy_plane_spaceBump_pos t)
  intro x _ hx
  have h := Wave.fderiv_spaceSlice (s := t) (x := x)
    ((contDiff_planePhase (n := 1)).differentiable one_ne_zero _) 0
  rw [hx, spaceDeriv_planePhase] at h
  norm_num at h

end ProjectAinos.Electrodynamics.Optics.Limits
