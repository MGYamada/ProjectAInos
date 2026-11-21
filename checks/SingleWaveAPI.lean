module

import ProjectAinos.Electrodynamics.Optics.SingleWave

noncomputable section

open Set Filter MeasureTheory Complex
open ProjectAinos.SmoothGeometry ProjectAinos.Electrodynamics.Optics.Limits
open scoped Topology ContDiff
local notation "E3" => EuclideanSpace ℝ (Fin 3)

example {d : ℕ} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    {g h : EuclideanSpace ℝ (Fin d) → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hn : ∀ x ∈ tsupport g, fderiv ℝ ψ x ≠ 0)
    (hh : Continuous h) (hk : HasCompactSupport h) :
    Tendsto (fun ε : ℝ => ∫ x, ((g x + ε * h x) * exp (I / ε * ψ x)).re ^ 2) (𝓝[≠] 0)
      (𝓝 ((∫ x, ‖g x‖ ^ 2) / 2)) :=
  ProjectAinos.SpecialFunctions.Oscillatory.tendsto_real_square hψ hg hc hn hh hk

example {T R : ℝ} {a b ψ : ℝ × E3 → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hψ : ContDiff ℝ ∞ ψ)
    (hT : 0 < T) (has : Wave.BallSupportOn T R a) (hbs : Wave.BallSupportOn T R b)
    {t : ℝ} (ht : t ∈ Icc 0 T)
    (hn : ∀ x ∈ tsupport (fun y => a (t,y)) ∪ tsupport (fun y => b (t,y)),
      fderiv ℝ (fun y => ψ (t,y)) x ≠ 0) :
    Tendsto (fun ε => ε ^ 2 * Wave.energy (Wave.highFrequencyWave a b ψ ε) t)
      (𝓝[≠] 0) (𝓝 (leadingEnergy a b ψ t / 2)) :=
  tendsto_sq_mul_energy_single ha hb hψ hT has hbs ht hn

example {T R : ℝ} {a b ψ : ℝ × E3 → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hψ : ContDiff ℝ ∞ ψ)
    (hT : 0 < T) (has : Wave.BallSupportOn T R a) (hbs : Wave.BallSupportOn T R b)
    {t : ℝ} (ht : t ∈ Icc 0 T)
    (hn : ∀ x ∈ tsupport (fun y => a (t,y)) ∪ tsupport (fun y => b (t,y)),
      fderiv ℝ (fun y => ψ (t,y)) x ≠ 0) (hL : 0 < leadingEnergy a b ψ t) :
    ∀ᶠ ε : ℝ in 𝓝[≠] 0,
      leadingEnergy a b ψ t / (4 * ε ^ 2) ≤ Wave.energy (Wave.highFrequencyWave a b ψ ε) t :=
  eventually_energy_single_ge ha hb hψ hT has hbs ht hn hL

example {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∀ᶠ ε : ℝ in 𝓝[≠] 0,
      leadingEnergy (planeAmplitude Wave.spaceBump) (planeAmplitude fun _ => 0) planePhase t /
        (4 * ε ^ 2) ≤ Wave.energy (Wave.highFrequencyWave (planeAmplitude Wave.spaceBump)
          (planeAmplitude fun _ => 0) planePhase ε) t :=
  eventually_energy_single_plane_bump hT ht
