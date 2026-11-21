/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Wave.RetardedIntegral
import Mathlib.Tactic

/-!
# The wave operator on a high-frequency phase

For functions on `ℝ × ℝ³`, `wavePairing f g = ∂ₜf ∂ₜg − ∇f · ∇g` is the Minkowski pairing of the
gradients, and the wave operator `□ = ∂ₜ² − Δ` of `a cos(ψ/ε)` and `b sin(ψ/ε)` has an exact
expansion in powers of `1/ε` (Landau–Lifshitz, *The Classical Theory of Fields*, §53):

* `waveOperator_mul_cos`:
  `□(a cos(ψ/ε)) = −ε⁻² ⟨dψ, dψ⟩ a cos − ε⁻¹ (2⟨da, dψ⟩ + a □ψ) sin + □a cos`,
* `waveOperator_mul_sin`:
  `□(b sin(ψ/ε)) = −ε⁻² ⟨dψ, dψ⟩ b sin + ε⁻¹ (2⟨db, dψ⟩ + b □ψ) cos + □b sin`,

at every point where `a`, `b` and `ψ` are `C²`, for every `ε ≠ 0`. With the transport operator
`transport a ψ = 2⟨da, dψ⟩ + a □ψ`, `waveOperator_highFrequencyWave` is the expansion of the
wave `highFrequencyWave a b ψ ε = a cos(ψ/ε) + b sin(ψ/ε)`:
`□ = −ε⁻² ⟨dψ, dψ⟩ (a cos + b sin) + ε⁻¹ (T b cos − T a sin) + (□a cos + □b sin)`, and
`timeDeriv_highFrequencyWave`, `spaceDeriv_highFrequencyWave` are its first derivatives.

* `raisedGradient ψ = (∂ₜψ, −∇ψ)`, the gradient raised with the metric `(+−−−)`, and
  `fderiv_raisedGradient`: the derivative along it is `⟨df, dψ⟩`.
* `wavePairing_comm`, `wavePairing_fun_mul` (the product rule), `waveOperator_fun_add`.
-/

@[expose] public section

noncomputable section

open Real Filter
open scoped Topology ContDiff

namespace ProjectAinos.SmoothGeometry.Wave

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The Minkowski pairing `∂ₜf ∂ₜg − Σᵢ ∂ᵢf ∂ᵢg` of the gradients of two functions on `ℝ × ℝ³`. -/
def wavePairing (f g : ℝ × E3 → ℝ) (p : ℝ × E3) : ℝ :=
  timeDeriv f p * timeDeriv g p - ∑ i, spaceDeriv i f p * spaceDeriv i g p

/-! ### Derivatives along a direction -/

/-- The derivative of the phase `ψ/ε`. -/
theorem hasFDerivAt_div_const {ψ : ℝ × E3 → ℝ} {q : ℝ × E3} (hψ : DifferentiableAt ℝ ψ q)
    (ε : ℝ) : HasFDerivAt (fun y => ψ y / ε) (ε⁻¹ • fderiv ℝ ψ q) q :=
  (hψ.hasFDerivAt.mul_const ε⁻¹).congr_of_eventuallyEq
    (Eventually.of_forall fun y => div_eq_mul_inv (ψ y) ε)

/-- The derivative of `a cos(ψ/ε)` along `v`. -/
theorem fderiv_mul_cos_apply {a ψ : ℝ × E3 → ℝ} {q : ℝ × E3} (ha : DifferentiableAt ℝ a q)
    (hψ : DifferentiableAt ℝ ψ q) (ε : ℝ) (v : ℝ × E3) :
    fderiv ℝ (fun y => a y * cos (ψ y / ε)) q v =
      fderiv ℝ a q v * cos (ψ q / ε) - ε⁻¹ * (a q * fderiv ℝ ψ q v) * sin (ψ q / ε) := by
  rw [(ha.hasFDerivAt.fun_mul (hasFDerivAt_div_const hψ ε).cos).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The derivative of `b sin(ψ/ε)` along `v`. -/
theorem fderiv_mul_sin_apply {b ψ : ℝ × E3 → ℝ} {q : ℝ × E3} (hb : DifferentiableAt ℝ b q)
    (hψ : DifferentiableAt ℝ ψ q) (ε : ℝ) (v : ℝ × E3) :
    fderiv ℝ (fun y => b y * sin (ψ y / ε)) q v =
      fderiv ℝ b q v * sin (ψ q / ε) + ε⁻¹ * (b q * fderiv ℝ ψ q v) * cos (ψ q / ε) := by
  rw [(hb.hasFDerivAt.fun_mul (hasFDerivAt_div_const hψ ε).sin).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The derivative along `v` of a function that is `C²` at a point is differentiable there. -/
theorem differentiableAt_fderiv_apply {f : ℝ × E3 → ℝ} {p : ℝ × E3} (hf : ContDiffAt ℝ 2 f p)
    (v : ℝ × E3) : DifferentiableAt ℝ (fun q => fderiv ℝ f q v) p :=
  ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
    (differentiableAt_const v)

/-- The second derivative of `a cos(ψ/ε)` along `v`. -/
theorem fderiv_fderiv_mul_cos_apply {a ψ : ℝ × E3 → ℝ} {p : ℝ × E3} (ha : ContDiffAt ℝ 2 a p)
    (hψ : ContDiffAt ℝ 2 ψ p) (ε : ℝ) (v : ℝ × E3) :
    fderiv ℝ (fun q => fderiv ℝ (fun y => a y * cos (ψ y / ε)) q v) p v =
      fderiv ℝ (fun q => fderiv ℝ a q v) p v * cos (ψ p / ε) -
        2 * ε⁻¹ * (fderiv ℝ a p v * fderiv ℝ ψ p v) * sin (ψ p / ε) -
        ε⁻¹ ^ 2 * (a p * fderiv ℝ ψ p v ^ 2) * cos (ψ p / ε) -
        ε⁻¹ * (a p * fderiv ℝ (fun q => fderiv ℝ ψ q v) p v) * sin (ψ p / ε) := by
  have hev : (fun q => fderiv ℝ (fun y => a y * cos (ψ y / ε)) q v) =ᶠ[𝓝 p]
      fun q => fderiv ℝ a q v * cos (ψ q / ε) - ε⁻¹ * (a q * fderiv ℝ ψ q v) * sin (ψ q / ε) := by
    filter_upwards [ha.eventually (by simp), hψ.eventually (by simp)] with q hq hq'
    exact fderiv_mul_cos_apply (hq.differentiableAt (by simp)) (hq'.differentiableAt (by simp))
      ε v
  have hA := ha.differentiableAt (by simp)
  have hΨ := hψ.differentiableAt (by simp)
  have H := ((differentiableAt_fderiv_apply ha v).hasFDerivAt.fun_mul
    (hasFDerivAt_div_const hΨ ε).cos).fun_sub
    (((hA.hasFDerivAt.fun_mul (differentiableAt_fderiv_apply hψ v).hasFDerivAt).const_mul
      ε⁻¹).fun_mul (hasFDerivAt_div_const hΨ ε).sin)
  rw [hev.fderiv_eq, H.fderiv]
  simp only [sub_apply, add_apply,
    smul_apply, smul_eq_mul]
  ring

/-- The second derivative of `b sin(ψ/ε)` along `v`. -/
theorem fderiv_fderiv_mul_sin_apply {b ψ : ℝ × E3 → ℝ} {p : ℝ × E3} (hb : ContDiffAt ℝ 2 b p)
    (hψ : ContDiffAt ℝ 2 ψ p) (ε : ℝ) (v : ℝ × E3) :
    fderiv ℝ (fun q => fderiv ℝ (fun y => b y * sin (ψ y / ε)) q v) p v =
      fderiv ℝ (fun q => fderiv ℝ b q v) p v * sin (ψ p / ε) +
        2 * ε⁻¹ * (fderiv ℝ b p v * fderiv ℝ ψ p v) * cos (ψ p / ε) -
        ε⁻¹ ^ 2 * (b p * fderiv ℝ ψ p v ^ 2) * sin (ψ p / ε) +
        ε⁻¹ * (b p * fderiv ℝ (fun q => fderiv ℝ ψ q v) p v) * cos (ψ p / ε) := by
  have hev : (fun q => fderiv ℝ (fun y => b y * sin (ψ y / ε)) q v) =ᶠ[𝓝 p]
      fun q => fderiv ℝ b q v * sin (ψ q / ε) + ε⁻¹ * (b q * fderiv ℝ ψ q v) * cos (ψ q / ε) := by
    filter_upwards [hb.eventually (by simp), hψ.eventually (by simp)] with q hq hq'
    exact fderiv_mul_sin_apply (hq.differentiableAt (by simp)) (hq'.differentiableAt (by simp))
      ε v
  have hB := hb.differentiableAt (by simp)
  have hΨ := hψ.differentiableAt (by simp)
  have H := ((differentiableAt_fderiv_apply hb v).hasFDerivAt.fun_mul
    (hasFDerivAt_div_const hΨ ε).sin).fun_add
    (((hB.hasFDerivAt.fun_mul (differentiableAt_fderiv_apply hψ v).hasFDerivAt).const_mul
      ε⁻¹).fun_mul (hasFDerivAt_div_const hΨ ε).cos)
  rw [hev.fderiv_eq, H.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- `∂ₜ²(a cos(ψ/ε))`. -/
theorem timeDeriv_timeDeriv_mul_cos {a ψ : ℝ × E3 → ℝ} {p : ℝ × E3} (ha : ContDiffAt ℝ 2 a p)
    (hψ : ContDiffAt ℝ 2 ψ p) (ε : ℝ) :
    timeDeriv (timeDeriv fun q => a q * cos (ψ q / ε)) p =
      timeDeriv (timeDeriv a) p * cos (ψ p / ε) -
        2 * ε⁻¹ * (timeDeriv a p * timeDeriv ψ p) * sin (ψ p / ε) -
        ε⁻¹ ^ 2 * (a p * timeDeriv ψ p ^ 2) * cos (ψ p / ε) -
        ε⁻¹ * (a p * timeDeriv (timeDeriv ψ) p) * sin (ψ p / ε) :=
  fderiv_fderiv_mul_cos_apply ha hψ ε _

/-- `∂ᵢ²(a cos(ψ/ε))`. -/
theorem spaceDeriv_spaceDeriv_mul_cos {a ψ : ℝ × E3 → ℝ} {p : ℝ × E3} (ha : ContDiffAt ℝ 2 a p)
    (hψ : ContDiffAt ℝ 2 ψ p) (ε : ℝ) (i : Fin 3) :
    spaceDeriv i (spaceDeriv i fun q => a q * cos (ψ q / ε)) p =
      spaceDeriv i (spaceDeriv i a) p * cos (ψ p / ε) -
        2 * ε⁻¹ * (spaceDeriv i a p * spaceDeriv i ψ p) * sin (ψ p / ε) -
        ε⁻¹ ^ 2 * (a p * spaceDeriv i ψ p ^ 2) * cos (ψ p / ε) -
        ε⁻¹ * (a p * spaceDeriv i (spaceDeriv i ψ) p) * sin (ψ p / ε) :=
  fderiv_fderiv_mul_cos_apply ha hψ ε _

/-- `∂ₜ²(b sin(ψ/ε))`. -/
theorem timeDeriv_timeDeriv_mul_sin {b ψ : ℝ × E3 → ℝ} {p : ℝ × E3} (hb : ContDiffAt ℝ 2 b p)
    (hψ : ContDiffAt ℝ 2 ψ p) (ε : ℝ) :
    timeDeriv (timeDeriv fun q => b q * sin (ψ q / ε)) p =
      timeDeriv (timeDeriv b) p * sin (ψ p / ε) +
        2 * ε⁻¹ * (timeDeriv b p * timeDeriv ψ p) * cos (ψ p / ε) -
        ε⁻¹ ^ 2 * (b p * timeDeriv ψ p ^ 2) * sin (ψ p / ε) +
        ε⁻¹ * (b p * timeDeriv (timeDeriv ψ) p) * cos (ψ p / ε) :=
  fderiv_fderiv_mul_sin_apply hb hψ ε _

/-- `∂ᵢ²(b sin(ψ/ε))`. -/
theorem spaceDeriv_spaceDeriv_mul_sin {b ψ : ℝ × E3 → ℝ} {p : ℝ × E3} (hb : ContDiffAt ℝ 2 b p)
    (hψ : ContDiffAt ℝ 2 ψ p) (ε : ℝ) (i : Fin 3) :
    spaceDeriv i (spaceDeriv i fun q => b q * sin (ψ q / ε)) p =
      spaceDeriv i (spaceDeriv i b) p * sin (ψ p / ε) +
        2 * ε⁻¹ * (spaceDeriv i b p * spaceDeriv i ψ p) * cos (ψ p / ε) -
        ε⁻¹ ^ 2 * (b p * spaceDeriv i ψ p ^ 2) * sin (ψ p / ε) +
        ε⁻¹ * (b p * spaceDeriv i (spaceDeriv i ψ) p) * cos (ψ p / ε) :=
  fderiv_fderiv_mul_sin_apply hb hψ ε _

/-! ### The expansion -/

/-- The wave operator of `a cos(ψ/ε)`. -/
theorem waveOperator_mul_cos {a ψ : ℝ × E3 → ℝ} {p : ℝ × E3} (ha : ContDiffAt ℝ 2 a p)
    (hψ : ContDiffAt ℝ 2 ψ p) {ε : ℝ} (hε : ε ≠ 0) :
    waveOperator (fun q => a q * cos (ψ q / ε)) p =
      -(ε⁻¹ ^ 2 * wavePairing ψ ψ p * a p * cos (ψ p / ε)) -
        ε⁻¹ * (2 * wavePairing a ψ p + a p * waveOperator ψ p) * sin (ψ p / ε) +
        waveOperator a p * cos (ψ p / ε) := by
  -- the expansion holds for `ε = 0` as well, where `ψ/ε = 0`
  have _hε := hε
  rw [waveOperator, timeDeriv_timeDeriv_mul_cos ha hψ ε,
    Finset.sum_congr rfl fun i _ => spaceDeriv_spaceDeriv_mul_cos ha hψ ε i]
  simp only [waveOperator, wavePairing, Fin.sum_univ_three]
  ring

/-- The wave operator of `b sin(ψ/ε)`. -/
theorem waveOperator_mul_sin {b ψ : ℝ × E3 → ℝ} {p : ℝ × E3} (hb : ContDiffAt ℝ 2 b p)
    (hψ : ContDiffAt ℝ 2 ψ p) {ε : ℝ} (hε : ε ≠ 0) :
    waveOperator (fun q => b q * sin (ψ q / ε)) p =
      -(ε⁻¹ ^ 2 * wavePairing ψ ψ p * b p * sin (ψ p / ε)) +
        ε⁻¹ * (2 * wavePairing b ψ p + b p * waveOperator ψ p) * cos (ψ p / ε) +
        waveOperator b p * sin (ψ p / ε) := by
  -- the expansion holds for `ε = 0` as well, where `ψ/ε = 0`
  have _hε := hε
  rw [waveOperator, timeDeriv_timeDeriv_mul_sin hb hψ ε,
    Finset.sum_congr rfl fun i _ => spaceDeriv_spaceDeriv_mul_sin hb hψ ε i]
  simp only [waveOperator, wavePairing, Fin.sum_univ_three]
  ring

/-! ### The pairing, the transport operator and the high-frequency wave -/

/-- The pairing is symmetric. -/
theorem wavePairing_comm (f g : ℝ × E3 → ℝ) (p : ℝ × E3) :
    wavePairing f g p = wavePairing g f p := by
  simp only [wavePairing, mul_comm]

/-- The pairing of a product: `⟨d(fg), dψ⟩ = f ⟨dg, dψ⟩ + g ⟨df, dψ⟩`. -/
theorem wavePairing_fun_mul {f g : ℝ × E3 → ℝ} {p : ℝ × E3} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) (ψ : ℝ × E3 → ℝ) :
    wavePairing (fun q => f q * g q) ψ p = f p * wavePairing g ψ p + g p * wavePairing f ψ p := by
  have h : ∀ v : ℝ × E3, fderiv ℝ (fun q => f q * g q) p v =
      f p * fderiv ℝ g p v + g p * fderiv ℝ f p v := fun v => by
    rw [(hf.hasFDerivAt.fun_mul hg.hasFDerivAt).fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
  simp only [wavePairing, timeDeriv, spaceDeriv, h, Fin.sum_univ_three]
  ring

/-- The derivative along `v` of a sum, twice. -/
theorem fderiv_fderiv_add_apply {f g : ℝ × E3 → ℝ} {p : ℝ × E3} (hf : ContDiffAt ℝ 2 f p)
    (hg : ContDiffAt ℝ 2 g p) (v : ℝ × E3) :
    fderiv ℝ (fun q => fderiv ℝ (fun y => f y + g y) q v) p v =
      fderiv ℝ (fun q => fderiv ℝ f q v) p v + fderiv ℝ (fun q => fderiv ℝ g q v) p v := by
  have hev : (fun q => fderiv ℝ (fun y => f y + g y) q v) =ᶠ[𝓝 p]
      fun q => fderiv ℝ f q v + fderiv ℝ g q v := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with q hq hq'
    rw [fderiv_fun_add (hq.differentiableAt (by simp)) (hq'.differentiableAt (by simp))]
    rfl
  rw [hev.fderiv_eq, fderiv_fun_add (differentiableAt_fderiv_apply hf v)
    (differentiableAt_fderiv_apply hg v)]
  rfl

/-- The wave operator is additive on functions that are `C²` at the point. -/
theorem waveOperator_fun_add {f g : ℝ × E3 → ℝ} {p : ℝ × E3} (hf : ContDiffAt ℝ 2 f p)
    (hg : ContDiffAt ℝ 2 g p) :
    waveOperator (fun q => f q + g q) p = waveOperator f p + waveOperator g p := by
  have ht : timeDeriv (timeDeriv fun q => f q + g q) p =
      timeDeriv (timeDeriv f) p + timeDeriv (timeDeriv g) p := fderiv_fderiv_add_apply hf hg _
  have hs : ∀ i, spaceDeriv i (spaceDeriv i fun q => f q + g q) p =
      spaceDeriv i (spaceDeriv i f) p + spaceDeriv i (spaceDeriv i g) p := fun i =>
    fderiv_fderiv_add_apply hf hg _
  simp only [waveOperator, ht, hs, Finset.sum_add_distrib]
  ring

/-- The transport operator `2⟨da, dψ⟩ + a □ψ` of an amplitude `a` along the phase `ψ`. -/
def transport (a ψ : ℝ × E3 → ℝ) (p : ℝ × E3) : ℝ :=
  2 * wavePairing a ψ p + a p * waveOperator ψ p

/-- The high-frequency wave `a cos(ψ/ε) + b sin(ψ/ε)` with the amplitudes `a`, `b`, the phase
`ψ` and the wavelength parameter `ε`. -/
def highFrequencyWave (a b ψ : ℝ × E3 → ℝ) (ε : ℝ) (p : ℝ × E3) : ℝ :=
  a p * cos (ψ p / ε) + b p * sin (ψ p / ε)

/-- The high-frequency wave is `C²` where the amplitudes and the phase are. -/
theorem contDiffAt_highFrequencyWave {n : ℕ∞ω} {a b ψ : ℝ × E3 → ℝ} {p : ℝ × E3}
    (ha : ContDiffAt ℝ n a p) (hb : ContDiffAt ℝ n b p) (hψ : ContDiffAt ℝ n ψ p) (ε : ℝ) :
    ContDiffAt ℝ n (highFrequencyWave a b ψ ε) p :=
  (ha.mul (hψ.div_const ε).cos).add (hb.mul (hψ.div_const ε).sin)

/-- The derivative of the high-frequency wave along `v`:
`ε⁻¹ ∂ᵥψ (b cos − a sin) + ∂ᵥa cos + ∂ᵥb sin`. -/
theorem fderiv_highFrequencyWave_apply {a b ψ : ℝ × E3 → ℝ} {p : ℝ × E3}
    (ha : DifferentiableAt ℝ a p) (hb : DifferentiableAt ℝ b p) (hψ : DifferentiableAt ℝ ψ p)
    (ε : ℝ) (v : ℝ × E3) :
    fderiv ℝ (highFrequencyWave a b ψ ε) p v =
      ε⁻¹ * (fderiv ℝ ψ p v * (b p * cos (ψ p / ε) - a p * sin (ψ p / ε))) +
        (fderiv ℝ a p v * cos (ψ p / ε) + fderiv ℝ b p v * sin (ψ p / ε)) := by
  have hc := ha.hasFDerivAt.fun_mul (hasFDerivAt_div_const hψ ε).cos
  have hs := hb.hasFDerivAt.fun_mul (hasFDerivAt_div_const hψ ε).sin
  rw [show highFrequencyWave a b ψ ε =
      fun q => a q * cos (ψ q / ε) + b q * sin (ψ q / ε) from rfl,
    fderiv_fun_add hc.differentiableAt hs.differentiableAt, add_apply,
    fderiv_mul_cos_apply ha hψ, fderiv_mul_sin_apply hb hψ]
  ring

/-- The time derivative of the high-frequency wave. -/
theorem timeDeriv_highFrequencyWave {a b ψ : ℝ × E3 → ℝ} {p : ℝ × E3}
    (ha : DifferentiableAt ℝ a p) (hb : DifferentiableAt ℝ b p) (hψ : DifferentiableAt ℝ ψ p)
    (ε : ℝ) :
    timeDeriv (highFrequencyWave a b ψ ε) p =
      ε⁻¹ * (timeDeriv ψ p * (b p * cos (ψ p / ε) - a p * sin (ψ p / ε))) +
        (timeDeriv a p * cos (ψ p / ε) + timeDeriv b p * sin (ψ p / ε)) :=
  fderiv_highFrequencyWave_apply ha hb hψ ε _

/-- The spatial derivatives of the high-frequency wave. -/
theorem spaceDeriv_highFrequencyWave {a b ψ : ℝ × E3 → ℝ} {p : ℝ × E3}
    (ha : DifferentiableAt ℝ a p) (hb : DifferentiableAt ℝ b p) (hψ : DifferentiableAt ℝ ψ p)
    (ε : ℝ) (i : Fin 3) :
    spaceDeriv i (highFrequencyWave a b ψ ε) p =
      ε⁻¹ * (spaceDeriv i ψ p * (b p * cos (ψ p / ε) - a p * sin (ψ p / ε))) +
        (spaceDeriv i a p * cos (ψ p / ε) + spaceDeriv i b p * sin (ψ p / ε)) :=
  fderiv_highFrequencyWave_apply ha hb hψ ε _

/-- **The expansion of the wave operator** of `a cos(ψ/ε) + b sin(ψ/ε)` in powers of `1/ε`:
`□ = −ε⁻² ⟨dψ, dψ⟩ (a cos + b sin) + ε⁻¹ (T b cos − T a sin) + (□a cos + □b sin)` with the
transport operator `T a = 2⟨da, dψ⟩ + a □ψ`, at a point where `a`, `b`, `ψ` are `C²`. -/
theorem waveOperator_highFrequencyWave {a b ψ : ℝ × E3 → ℝ} {p : ℝ × E3}
    (ha : ContDiffAt ℝ 2 a p) (hb : ContDiffAt ℝ 2 b p) (hψ : ContDiffAt ℝ 2 ψ p) {ε : ℝ}
    (hε : ε ≠ 0) :
    waveOperator (highFrequencyWave a b ψ ε) p =
      ε⁻¹ ^ 2 * (-wavePairing ψ ψ p * (a p * cos (ψ p / ε) + b p * sin (ψ p / ε))) +
        ε⁻¹ * (transport b ψ p * cos (ψ p / ε) - transport a ψ p * sin (ψ p / ε)) +
        (waveOperator a p * cos (ψ p / ε) + waveOperator b p * sin (ψ p / ε)) := by
  rw [show highFrequencyWave a b ψ ε =
      fun q => a q * cos (ψ q / ε) + b q * sin (ψ q / ε) from rfl,
    waveOperator_fun_add (ha.mul (hψ.div_const ε).cos) (hb.mul (hψ.div_const ε).sin),
    waveOperator_mul_cos ha hψ hε, waveOperator_mul_sin hb hψ hε, transport, transport]
  ring

/-! ### The raised gradient -/

/-- A linear functional on `ℝ × ℝ³` in the axes: `L (c, x) = c L(1, 0) + Σᵢ xᵢ L(0, eᵢ)`. -/
theorem clm_apply_prod (L : ℝ × E3 →L[ℝ] ℝ) (c : ℝ) (x : E3) :
    L (c, x) = c * L (1, 0) + ∑ i, x i * L (0, EuclideanSpace.single i 1) := by
  have h : ((c, x) : ℝ × E3) =
      c • ((1 : ℝ), (0 : E3)) + ∑ i, x i • ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)) := by
    ext j
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, Pi.single_apply]
  rw [h, map_add, map_smul, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- The gradient `(∂ₜψ, −∇ψ)` of a function on `ℝ × ℝ³` raised with the metric `(+−−−)`. -/
def raisedGradient (ψ : ℝ × E3 → ℝ) (p : ℝ × E3) : ℝ × E3 :=
  (timeDeriv ψ p, WithLp.toLp 2 fun i => -spaceDeriv i ψ p)

/-- The derivative along the raised gradient of `ψ` is the pairing with `dψ`:
`∂_k f = ⟨df, dψ⟩` for `k = (∂ₜψ, −∇ψ)`. -/
theorem fderiv_raisedGradient (f ψ : ℝ × E3 → ℝ) (p : ℝ × E3) :
    fderiv ℝ f p (raisedGradient ψ p) = wavePairing f ψ p := by
  rw [raisedGradient, clm_apply_prod, wavePairing]
  simp only [Fin.sum_univ_three]
  change timeDeriv ψ p * timeDeriv f p + (-spaceDeriv 0 ψ p * spaceDeriv 0 f p +
    -spaceDeriv 1 ψ p * spaceDeriv 1 f p + -spaceDeriv 2 ψ p * spaceDeriv 2 f p) = _
  ring

end ProjectAinos.SmoothGeometry.Wave
