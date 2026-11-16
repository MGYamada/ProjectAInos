/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAInos.Mechanics.Oscillations.NonlinearResonance
import ProjectAInos.Mechanics.Oscillations.RapidForceExistence

/-! Typed contracts for the method of averaging: integrals of slowly varying
amplitudes against fast oscillations, the comparison with the averaged
equation, the motion in a rapidly oscillating field with its effective
potential, and the resonance of the forced oscillator with a cubic term. These
examples use default elaborator options. -/

open ProjectAInos ProjectAInos.Mechanics ProjectAInos.SmoothGeometry.Averaging
open Set MeasureTheory
open scoped NNReal

noncomputable section

section Averaging

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

example {φ φ' : ℝ → ℝ} {t ω M₀ M₁ : ℝ} (ht : 0 ≤ t) (hω : 0 < ω)
    (hφ : ∀ s ∈ Icc 0 t, HasDerivAt φ (φ' s) s) (hc : ContinuousOn φ' (Icc 0 t))
    (h0 : ∀ s ∈ Icc 0 t, |φ s| ≤ M₀) (h1 : ∀ s ∈ Icc 0 t, |φ' s| ≤ M₁) :
    |∫ s in 0..t, φ s * Real.sin (ω * s)| ≤ (2 * M₀ + t * M₁) / ω :=
  abs_integral_mul_sin_le ht hω hφ hc h0 h1

example {φ φ' : ℝ → ℝ} {t ω M₀ M₁ : ℝ} (ht : 0 ≤ t) (hω : 0 < ω)
    (hφ : ∀ s ∈ Icc 0 t, HasDerivAt φ (φ' s) s) (hc : ContinuousOn φ' (Icc 0 t))
    (h0 : ∀ s ∈ Icc 0 t, |φ s| ≤ M₀) (h1 : ∀ s ∈ Icc 0 t, |φ' s| ≤ M₁) :
    |∫ s in 0..t, φ s * Real.cos (ω * s)| ≤ (2 * M₀ + t * M₁) / ω :=
  abs_integral_mul_cos_le ht hω hφ hc h0 h1

example {r₁ r₂ : ℝ → ℝ} (h₁ : Continuous r₁) (h₂ : Continuous r₂)
    {t δ : ℝ} (hb₁ : |∫ u in 0..t, r₁ u| ≤ δ) (hb₂ : |∫ u in 0..t, r₂ u| ≤ δ) :
    ‖∫ u in 0..t, (r₁ u, r₂ u)‖ ≤ δ :=
  norm_integral_prodMk_le h₁ h₂ hb₁ hb₂

example {δ K ε t L : ℝ} (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (ht : 0 ≤ t) (htL : t ≤ L) :
    gronwallBound δ K ε t ≤ (δ + ε * L) * Real.exp (K * L) :=
  gronwallBound_le_mul_exp hδ hK hε ht htL

example {F : E → E} {K : ℝ≥0} {s : Set E}
    (hF : LipschitzOnWith K F s) {z Z r : ℝ → E} {L δ : ℝ} (hr : Continuous r)
    (hz : ∀ t ∈ Icc 0 L, HasDerivAt z (F (z t) + r t) t)
    (hZ : ∀ t ∈ Icc 0 L, HasDerivAt Z (F (Z t)) t) (hzs : ∀ t ∈ Icc 0 L, z t ∈ s)
    (hZs : ∀ t ∈ Icc 0 L, Z t ∈ s) (hδ : ∀ t ∈ Icc 0 L, ‖∫ u in 0..t, r u‖ ≤ δ)
    (h0 : z 0 = Z 0) :
    ∀ t ∈ Icc 0 L, ‖z t - Z t‖ ≤ δ * Real.exp (K * t) :=
  norm_sub_le_of_norm_integral_le hF hr hz hZ hzs hZs hδ h0

example {F : E → E} {K : ℝ≥0} {s : Set E}
    (hF : LipschitzOnWith K F s) {z Z r : ℝ → E} {L δ : ℝ} (hr : ContinuousOn r (Icc 0 L))
    (hz : ∀ t ∈ Icc 0 L, HasDerivAt z (F (z t) + r t) t)
    (hZ : ∀ t ∈ Icc 0 L, HasDerivAt Z (F (Z t)) t) (hzs : ∀ t ∈ Icc 0 L, z t ∈ s)
    (hZs : ∀ t ∈ Icc 0 L, Z t ∈ s) (hδ : ∀ t ∈ Icc 0 L, ‖∫ u in 0..t, r u‖ ≤ δ)
    (h0 : z 0 = Z 0) :
    ∀ t ∈ Icc 0 L, ‖z t - Z t‖ ≤ δ * Real.exp (K * t) :=
  norm_sub_le_of_norm_integral_le' hF hr hz hZ hzs hZs hδ h0

example {φ φ' : ℝ → E} {t ω M₀ M₁ : ℝ} (ht : 0 ≤ t) (hω : 0 < ω)
    (hφ : ∀ s ∈ Icc 0 t, HasDerivAt φ (φ' s) s) (hc : ContinuousOn φ' (Icc 0 t))
    (h0 : ∀ s ∈ Icc 0 t, ‖φ s‖ ≤ M₀) (h1 : ∀ s ∈ Icc 0 t, ‖φ' s‖ ≤ M₁) :
    ‖∫ s in 0..t, Real.sin (ω * s) • φ s‖ ≤ (2 * M₀ + t * M₁) / ω :=
  norm_integral_sin_smul_le ht hω hφ hc h0 h1

example {φ φ' : ℝ → E} {t ω M₀ M₁ : ℝ} (ht : 0 ≤ t) (hω : 0 < ω)
    (hφ : ∀ s ∈ Icc 0 t, HasDerivAt φ (φ' s) s) (hc : ContinuousOn φ' (Icc 0 t))
    (h0 : ∀ s ∈ Icc 0 t, ‖φ s‖ ≤ M₀) (h1 : ∀ s ∈ Icc 0 t, ‖φ' s‖ ≤ M₁) :
    ‖∫ s in 0..t, Real.cos (ω * s) • φ s‖ ≤ (2 * M₀ + t * M₁) / ω :=
  norm_integral_cos_smul_le ht hω hφ hc h0 h1

example {J : Type*} [Fintype J] (n : J → ℝ) (P Q : J → E → E) (γ t : ℝ) (y : E) :
    harmonics n P Q γ t y =
      ∑ j, (Real.cos (n j * γ * t) • P j y + Real.sin (n j * γ * t) • Q j y) := rfl

example {J : Type*} [Fintype J] {F : E → E} {P Q : J → E → E}
    {n : J → ℝ} (hF : ContDiff ℝ 1 F) (hP : ∀ j, ContDiff ℝ 1 (P j))
    (hQ : ∀ j, ContDiff ℝ 1 (Q j)) (hn : ∀ j, 0 < n j) {K : Set E} (hK : IsCompact K)
    (hconv : Convex ℝ K) (L : ℝ) :
    ∃ C : ℝ, ∀ γ : ℝ, 0 < γ → ∀ z Z : ℝ → E,
      (∀ t ∈ Icc 0 L, HasDerivAt z (F (z t) + harmonics n P Q γ t (z t)) t) →
      (∀ t ∈ Icc 0 L, HasDerivAt Z (F (Z t)) t) → (∀ t ∈ Icc 0 L, z t ∈ K) →
      (∀ t ∈ Icc 0 L, Z t ∈ K) → z 0 = Z 0 → ∀ t ∈ Icc 0 L, ‖z t - Z t‖ ≤ C / γ :=
  exists_forall_norm_sub_le hF hP hQ hn hK hconv L

end Averaging

section RapidForce

open RapidForce
open scoped ContDiff

variable {m Ω A B : ℝ} {U g x v X W : ℝ → ℝ} {V L : ℝ}

example (m : ℝ) (U g : ℝ → ℝ) (x : ℝ) :
    effectivePotential m U g x =
      U x + g x ^ 2 / (4 * m) := rfl

example (hb : RapidBounds U g A B) : ContDiff ℝ ∞ U := hb.contDiff_potential

example (hb : RapidBounds U g A B) : ContDiff ℝ ∞ g := hb.contDiff_amplitude

example (hb : RapidBounds U g A B) (y : ℝ) : |deriv U y| ≤ A := hb.deriv_potential y

example (hb : RapidBounds U g A B) (y : ℝ) : |deriv (deriv U) y| ≤ A :=
  hb.deriv_deriv_potential y

example (hb : RapidBounds U g A B) (y : ℝ) : |g y| ≤ B := hb.amplitude y

example (hb : RapidBounds U g A B) (y : ℝ) : |deriv g y| ≤ B := hb.deriv_amplitude y

example (hb : RapidBounds U g A B) (y : ℝ) : |deriv (deriv g) y| ≤ B :=
  hb.deriv_deriv_amplitude y

example (m Ω : ℝ) (U g x v : ℝ → ℝ) :
    IsRapidMotion m Ω U g x v ↔ (∀ t, HasDerivAt x (v t) t) ∧
      ∀ t, HasDerivAt v ((-deriv U (x t) + Ω * g (x t) * Real.cos (Ω * t)) / m) t := Iff.rfl

example (m : ℝ) (U g X W : ℝ → ℝ) :
    IsSlowMotion m U g X W ↔ (∀ t, HasDerivAt X (W t) t) ∧
      ∀ t, HasDerivAt W (-(deriv U (X t) + g (X t) * deriv g (X t) / (2 * m)) / m) t :=
  Iff.rfl

example (m Ω : ℝ) (g x v : ℝ → ℝ) (t : ℝ) :
    slowVelocity m Ω g x v t =
      v t - g (x t) / m * Real.sin (Ω * t) := rfl

example (m : ℝ) (U g : ℝ → ℝ) (p : ℝ × ℝ) :
    slowField m U g p =
      (p.2, -(deriv U p.1 + g p.1 * deriv g p.1 / (2 * m)) / m) := rfl

example (hU : ContDiff ℝ ∞ U) (hg : ContDiff ℝ ∞ g) (m x : ℝ) :
    HasDerivAt (effectivePotential m U g) (deriv U x + g x * deriv g x / (2 * m)) x :=
  hasDerivAt_effectivePotential hU hg m x

example (hg : ContDiff ℝ ∞ g) (y : ℝ) :
    HasDerivAt (deriv g) (deriv (deriv g) y) y :=
  hasDerivAt_deriv hg y

example (h : IsRapidMotion m Ω U g x v)
    (hg : ContDiff ℝ ∞ g) (hm : m ≠ 0) (t : ℝ) :
    HasDerivAt (slowVelocity m Ω g x v)
      (-deriv U (x t) / m - deriv g (x t) * v t / m * Real.sin (Ω * t)) t :=
  IsRapidMotion.hasDerivAt_slowVelocity h hg hm t

example (m Ω : ℝ) (g x : ℝ → ℝ) (t : ℝ) :
    oscillation₁ m Ω g x t =
      g (x t) / m * Real.sin (Ω * t) := rfl

example (m Ω : ℝ) (g x v : ℝ → ℝ) (t : ℝ) :
    oscillation₂ m Ω g x v t =
      -(deriv g (x t) * slowVelocity m Ω g x v t / m * Real.sin (Ω * t)) +
      g (x t) * deriv g (x t) / (2 * m ^ 2) * Real.cos (2 * Ω * t) := rfl

example (h : IsRapidMotion m Ω U g x v) (hg : ContDiff ℝ ∞ g)
    (hm : m ≠ 0) (t : ℝ) :
    HasDerivAt (fun s => (x s, slowVelocity m Ω g x v s))
      (slowField m U g (x t, slowVelocity m Ω g x v t) +
        (oscillation₁ m Ω g x t, oscillation₂ m Ω g x v t)) t :=
  IsRapidMotion.hasDerivAt_pair h hg hm t

example (h : IsSlowMotion m U g X W) (t : ℝ) :
    HasDerivAt (fun s => (X s, W s)) (slowField m U g (X t, W t)) t :=
  IsSlowMotion.hasDerivAt_pair h t

example (hb : RapidBounds U g A B) : 0 ≤ A := hb.nonneg_potential

example (hb : RapidBounds U g A B) : 0 ≤ B := hb.nonneg_amplitude

example (hb : RapidBounds U g A B) (hm : 0 < m) :
    ∃ K : ℝ≥0, LipschitzWith K (slowField m U g) :=
  hb.exists_lipschitzWith hm

example (hb : RapidBounds U g A B) (hm : 0 < m) {t : ℝ}
    (hv : |v t| ≤ V) :
    |slowVelocity m Ω g x v t| ≤ V + B / m :=
  IsRapidMotion.abs_slowVelocity_le hb hm hv

example (h : IsRapidMotion m Ω U g x v)
    (hb : RapidBounds U g A B) (hm : 0 < m) (hΩ : 0 < Ω)
    (hV : ∀ t ∈ Icc 0 L, |v t| ≤ V) {t : ℝ} (ht : t ∈ Icc 0 L) :
    |∫ s in 0..t, oscillation₁ m Ω g x s| ≤ (2 * (B / m) + L * (B * V / m)) / Ω :=
  IsRapidMotion.abs_integral_oscillation₁_le h hb hm hΩ hV ht

example (h : IsRapidMotion m Ω U g x v)
    (hb : RapidBounds U g A B) (hm : 0 < m) (hΩ : 0 < Ω)
    (hV : ∀ t ∈ Icc 0 L, |v t| ≤ V) {t : ℝ} (ht : t ∈ Icc 0 L) :
    |∫ s in 0..t, oscillation₂ m Ω g x v s| ≤
      ((2 * (B * (V + B / m) / m) +
          L * ((B * V * (V + B / m) + B * (A / m + B * V / m)) / m)) +
        (2 * (B * B / (2 * m ^ 2)) + L * ((B * V * B + B * (B * V)) / (2 * m ^ 2))) / 2) /
        Ω :=
  IsRapidMotion.abs_integral_oscillation₂_le h hb hm hΩ hV ht

example (hm : 0 < m) (hb : RapidBounds U g A B) (V L : ℝ) :
    ∃ C : ℝ, ∀ Ω : ℝ, 0 < Ω → ∀ x v X W : ℝ → ℝ, IsRapidMotion m Ω U g x v →
      IsSlowMotion m U g X W → x 0 = X 0 → v 0 = W 0 → (∀ t ∈ Icc 0 L, |v t| ≤ V) →
      ∀ t ∈ Icc 0 L, |x t - X t| ≤ C / Ω :=
  exists_forall_abs_sub_le hm hb V L

example (h : IsRapidMotion m Ω U g x v)
    (hb : RapidBounds U g A B) (hm : 0 < m) {L t : ℝ} (ht : t ∈ Icc 0 L) :
    |v t| ≤ (|v 0| + (A / m + B / m * (B / m)) * L) * Real.exp (B / m * L) + B / m :=
  IsRapidMotion.abs_velocity_le h hb hm ht

example (hm : 0 < m) (hb : RapidBounds U g A B)
    (V₀ L : ℝ) :
    ∃ C : ℝ, ∀ Ω : ℝ, 0 < Ω → ∀ x v X W : ℝ → ℝ, IsRapidMotion m Ω U g x v →
      IsSlowMotion m U g X W → x 0 = X 0 → v 0 = W 0 → |v 0| ≤ V₀ →
      ∀ t ∈ Icc 0 L, |x t - X t| ≤ C / Ω :=
  exists_forall_abs_sub_le_of_initial hm hb V₀ L

section Pendulum

variable (a b : ℝ)

example :
    RapidBounds (fun y => -(a * Real.cos y)) (fun y => b * Real.sin y) |a| |b| :=
  Pendulum.rapidBounds a b

example (m : ℝ) :
    HasDerivAt (fun y => a * Real.sin y + b * Real.sin y * (b * Real.cos y) / (2 * m))
      (-a + b ^ 2 / (2 * m)) Real.pi :=
  Pendulum.hasDerivAt_effectiveForce a b m

example {m : ℝ} (hm : 0 < m) :
    0 < -a + b ^ 2 / (2 * m) ↔ 2 * m * a < b ^ 2 :=
  Pendulum.pos_iff a b hm

end Pendulum

example (m Ω : ℝ) (U g : ℝ → ℝ) (p : ℝ × ℝ × ℝ) :
    extendedField m Ω U g p =
      (p.2.1, (-deriv U p.1 + Ω * g p.1 * Real.cos (Ω * p.2.2)) / m, 1) := rfl

example (hb : RapidBounds U g A B) (m Ω : ℝ) :
    ContDiff ℝ ∞ (extendedField m Ω U g) :=
  contDiff_extendedField hb m Ω

example (hb : RapidBounds U g A B) (hm : 0 < m) (Ω : ℝ)
    (p : ℝ × ℝ × ℝ) :
    ‖extendedField m Ω U g p‖ ≤ ((A + |Ω| * B) / m + 1) + 1 * ‖p‖ :=
  norm_extendedField_le hb hm Ω p

example (hb : RapidBounds U g A B) (hm : 0 < m) (Ω x₀ v₀ : ℝ) :
    ∃ x v : ℝ → ℝ, IsRapidMotion m Ω U g x v ∧ x 0 = x₀ ∧ v 0 = v₀ :=
  exists_isRapidMotion hb hm Ω x₀ v₀

example (hb : RapidBounds U g A B) (m : ℝ) :
    ContDiff ℝ ∞ (slowField m U g) :=
  contDiff_slowField hb m

example (hb : RapidBounds U g A B) (hm : 0 < m) (p : ℝ × ℝ) :
    ‖slowField m U g p‖ ≤ (A + B * B / (2 * m)) / m + 1 * ‖p‖ :=
  norm_slowField_le hb hm p

example (hb : RapidBounds U g A B) (hm : 0 < m) (x₀ v₀ : ℝ) :
    ∃ X W : ℝ → ℝ, IsSlowMotion m U g X W ∧ X 0 = x₀ ∧ W 0 = v₀ :=
  exists_isSlowMotion hb hm x₀ v₀

example (hm : 0 < m) (hb : RapidBounds U g A B) (V₀ L : ℝ) :
    ∃ C : ℝ, ∀ Ω : ℝ, 0 < Ω → ∀ x₀ v₀ : ℝ, |v₀| ≤ V₀ → ∃ x v X W : ℝ → ℝ,
      IsRapidMotion m Ω U g x v ∧ IsSlowMotion m U g X W ∧ x 0 = x₀ ∧ v 0 = v₀ ∧ X 0 = x₀ ∧
        W 0 = v₀ ∧ ∀ t ∈ Icc 0 L, |x t - X t| ≤ C / Ω :=
  exists_forall_exists_abs_sub_le hm hb V₀ L

end RapidForce

section NonlinearResonance

open NonlinearResonance

variable {lam ω₀ β F γ e k f : ℝ} {x v : ℝ → ℝ} {I : Set ℝ}

example (lam ω₀ β F γ : ℝ) (x v : ℝ → ℝ) (I : Set ℝ) :
    IsMotionOn lam ω₀ β F γ x v I =
      ∀ t ∈ I, HasDerivAt x (v t) t ∧
      HasDerivAt v (-(2 * lam * v t) - ω₀ ^ 2 * x t + F * Real.cos (γ * t) - β * x t ^ 3) t := rfl

example (γ : ℝ) (x v : ℝ → ℝ) (t : ℝ) :
    amplitude γ x v t =
      (x t * Real.cos (γ * t) - v t / γ * Real.sin (γ * t),
      x t * Real.sin (γ * t) + v t / γ * Real.cos (γ * t)) := rfl

example (ω₀ γ : ℝ) :
    detuning ω₀ γ =
      (γ ^ 2 - ω₀ ^ 2) / (2 * γ) := rfl

example (β γ : ℝ) :
    nonlinearity β γ =
      3 * β / (8 * γ) := rfl

example (F γ : ℝ) :
    forcing F γ =
      F / (2 * γ) := rfl

example (lam e k f : ℝ) (z : ℝ × ℝ) :
    averagedField lam e k f z =
      (-(lam * z.1) - (e - k * (z.1 ^ 2 + z.2 ^ 2)) * z.2,
      -(lam * z.2) + (e - k * (z.1 ^ 2 + z.2 ^ 2)) * z.1 + f) := rfl

example :
    multiple =
      ![2, 4] := rfl

example (lam e k f : ℝ) :
    cosAmplitude lam e k f =
      ![fun z => (lam * z.1 + e * z.2 - 4 / 3 * k * z.2 ^ 3,
      -(lam * z.2) + e * z.1 + f - 4 / 3 * k * z.1 ^ 3),
      fun z => (1 / 3 * k * (z.2 ^ 3 - 3 * z.1 ^ 2 * z.2),
      -(1 / 3 * k * (z.1 ^ 3 - 3 * z.1 * z.2 ^ 2)))] := rfl

example (lam e k f : ℝ) :
    sinAmplitude lam e k f =
      ![fun z => (lam * z.2 - e * z.1 - f + 2 / 3 * k * (z.1 ^ 3 + 3 * z.1 * z.2 ^ 2),
      lam * z.1 + e * z.2 - 2 / 3 * k * (3 * z.1 ^ 2 * z.2 + z.2 ^ 3)),
      fun z => (1 / 3 * k * (z.1 ^ 3 - 3 * z.1 * z.2 ^ 2),
      -(1 / 3 * k * (3 * z.1 ^ 2 * z.2 - z.2 ^ 3)))] := rfl

example (γ : ℝ) (x v : ℝ → ℝ) (t : ℝ) :
    (amplitude γ x v t).1 * Real.cos (γ * t) + (amplitude γ x v t).2 * Real.sin (γ * t) =
      x t :=
  amplitude_fst_mul_cos_add γ x v t

example (hγ : γ ≠ 0) (x v : ℝ → ℝ) (t : ℝ) :
    γ * (-((amplitude γ x v t).1 * Real.sin (γ * t)) +
      (amplitude γ x v t).2 * Real.cos (γ * t)) = v t :=
  amplitude_velocity hγ x v t

example (X U c s lam e k f : ℝ) (h : s ^ 2 + c ^ 2 = 1) :
    -(-(2 * lam * U) + 2 * e * X + 2 * f * c - 8 / 3 * k * X ^ 3) * s =
      -(lam * (X * c - U * s)) -
          (e - k * ((X * c - U * s) ^ 2 + (X * s + U * c) ^ 2)) * (X * s + U * c) +
        ((2 * c ^ 2 - 1) *
            (lam * (X * c - U * s) + e * (X * s + U * c) - 4 / 3 * k * (X * s + U * c) ^ 3) +
          2 * s * c * (lam * (X * s + U * c) - e * (X * c - U * s) - f +
            2 / 3 * k * ((X * c - U * s) ^ 3 + 3 * (X * c - U * s) * (X * s + U * c) ^ 2)) +
          ((2 * (2 * c ^ 2 - 1) ^ 2 - 1) *
              (1 / 3 * k * ((X * s + U * c) ^ 3 - 3 * (X * c - U * s) ^ 2 * (X * s + U * c))) +
            2 * (2 * s * c) * (2 * c ^ 2 - 1) *
              (1 / 3 * k *
                ((X * c - U * s) ^ 3 - 3 * (X * c - U * s) * (X * s + U * c) ^ 2)))) :=
  slow_identity₁ X U c s lam e k f h

example (X U c s lam e k f : ℝ) (h : s ^ 2 + c ^ 2 = 1) :
    (-(2 * lam * U) + 2 * e * X + 2 * f * c - 8 / 3 * k * X ^ 3) * c =
      -(lam * (X * s + U * c)) +
          (e - k * ((X * c - U * s) ^ 2 + (X * s + U * c) ^ 2)) * (X * c - U * s) + f +
        ((2 * c ^ 2 - 1) *
            (-(lam * (X * s + U * c)) + e * (X * c - U * s) + f -
              4 / 3 * k * (X * c - U * s) ^ 3) +
          2 * s * c * (lam * (X * c - U * s) + e * (X * s + U * c) -
            2 / 3 * k * (3 * (X * c - U * s) ^ 2 * (X * s + U * c) + (X * s + U * c) ^ 3)) +
          ((2 * (2 * c ^ 2 - 1) ^ 2 - 1) *
              -(1 / 3 * k * ((X * c - U * s) ^ 3 - 3 * (X * c - U * s) * (X * s + U * c) ^ 2)) +
            2 * (2 * s * c) * (2 * c ^ 2 - 1) *
              -(1 / 3 * k *
                (3 * (X * c - U * s) ^ 2 * (X * s + U * c) - (X * s + U * c) ^ 3)))) :=
  slow_identity₂ X U c s lam e k f h

example (h : IsMotionOn lam ω₀ β F γ x v I) (hγ : γ ≠ 0)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (amplitude γ x v)
      (averagedField lam (detuning ω₀ γ) (nonlinearity β γ) (forcing F γ) (amplitude γ x v t) +
        harmonics multiple
          (cosAmplitude lam (detuning ω₀ γ) (nonlinearity β γ) (forcing F γ))
          (sinAmplitude lam (detuning ω₀ γ) (nonlinearity β γ) (forcing F γ)) γ t
          (amplitude γ x v t)) t :=
  IsMotionOn.hasDerivAt_amplitude h hγ ht

example {z : ℝ × ℝ} (hz : averagedField lam e k f z = 0) :
    (z.1 ^ 2 + z.2 ^ 2) * ((e - k * (z.1 ^ 2 + z.2 ^ 2)) ^ 2 + lam ^ 2) = f ^ 2 :=
  amplitude_equation hz

example {s : ℝ}
    (hs : s * ((e - k * s) ^ 2 + lam ^ 2) = f ^ 2) (hD : (e - k * s) ^ 2 + lam ^ 2 ≠ 0) :
    ∃ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 = s ∧ averagedField lam e k f z = 0 :=
  exists_averagedField_eq_zero hs hD

example (lam e k f : ℝ) :
    ContDiff ℝ 1 (averagedField lam e k f) :=
  contDiff_averagedField lam e k f

example (lam e k f : ℝ) (j : Fin 2) :
    ContDiff ℝ 1 (cosAmplitude lam e k f j) :=
  contDiff_cosAmplitude lam e k f j

example (lam e k f : ℝ) (j : Fin 2) :
    ContDiff ℝ 1 (sinAmplitude lam e k f j) :=
  contDiff_sinAmplitude lam e k f j

example (j : Fin 2) :
    0 < multiple j :=
  multiple_pos j

example (lam e k f ρ L : ℝ) :
    ∃ C : ℝ, ∀ γ : ℝ, 0 < γ → ∀ (ω₀ β F : ℝ) (x v : ℝ → ℝ) (Z : ℝ → ℝ × ℝ),
      detuning ω₀ γ = e → nonlinearity β γ = k → forcing F γ = f →
      IsMotionOn lam ω₀ β F γ x v (Icc 0 L) →
      (∀ t ∈ Icc 0 L, HasDerivAt Z (averagedField lam e k f (Z t)) t) →
      (∀ t ∈ Icc 0 L, amplitude γ x v t ∈ Metric.closedBall (0 : ℝ × ℝ) ρ) →
      (∀ t ∈ Icc 0 L, Z t ∈ Metric.closedBall (0 : ℝ × ℝ) ρ) → amplitude γ x v 0 = Z 0 →
      ∀ t ∈ Icc 0 L, ‖amplitude γ x v t - Z t‖ ≤ C / γ :=
  exists_forall_norm_amplitude_sub_le lam e k f ρ L

example (lam e k f ρ L : ℝ) :
    ∃ C : ℝ, ∀ γ : ℝ, 0 < γ → ∀ (ω₀ β F : ℝ) (x v : ℝ → ℝ) (z₀ : ℝ × ℝ),
      detuning ω₀ γ = e → nonlinearity β γ = k → forcing F γ = f →
      IsMotionOn lam ω₀ β F γ x v (Icc 0 L) → averagedField lam e k f z₀ = 0 →
      z₀ ∈ Metric.closedBall (0 : ℝ × ℝ) ρ →
      (∀ t ∈ Icc 0 L, amplitude γ x v t ∈ Metric.closedBall (0 : ℝ × ℝ) ρ) →
      amplitude γ x v 0 = z₀ →
      ∀ t ∈ Icc 0 L,
        |x t - (z₀.1 * Real.cos (γ * t) + z₀.2 * Real.sin (γ * t))| ≤ 2 * C / γ :=
  exists_forall_abs_sub_steady_le lam e k f ρ L

end NonlinearResonance
