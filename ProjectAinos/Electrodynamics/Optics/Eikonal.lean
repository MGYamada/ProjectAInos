/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Wave.HighFrequency
public import ProjectAinos.SmoothGeometry.Wave.SlowSource
public import ProjectAinos.SmoothGeometry.ODE.LocalFlow
public import ProjectAinos.SmoothGeometry.Minkowski.Causal
public import ProjectAinos.Electrodynamics.CavityModes
import Mathlib.Tactic

/-!
# Geometrical optics: the eikonal and the intensity

A high-frequency family of potentials `A_μ = a_μ cos(ψ/ε) + b_μ sin(ψ/ε)`, with amplitudes
`a_μ`, `b_μ` and a phase `ψ` that are functions of `(t, x)`, in the limit `ε → 0` of short
wavelengths (Landau–Lifshitz, *The Classical Theory of Fields*, §§53, 54). The Minkowski pairing
`⟨df, dg⟩ = ∂ₜf ∂ₜg − ∇f · ∇g` is `Wave.wavePairing`, the wave operator `□ = ∂ₜ² − Δ` is
`Wave.waveOperator`, and `T a = 2⟨da, dψ⟩ + a □ψ` is the transport operator `Wave.transport`.

* `highFrequencyPotential a b ψ ε`: the family on space-time, with
  `potentialComponent_highFrequencyPotential`.
* `box_highFrequencyPotential`: `box A_μ = ε⁻² R₂ + ε⁻¹ R₁ + R₀`, where each `Rₖ` is
  `c₁ cos(ψ/ε) + c₂ sin(ψ/ε)` (`trigValue`) with coefficients `leadingCoeff`
  `= ⟨dψ, dψ⟩ (a_μ, b_μ)`, `subleadingCoeff` `= (−T b_μ, T a_μ)` and `zerothCoeff`
  `= (−□a_μ, −□b_μ)` that do not depend on `ε`.
* `lorenzDivergence_highFrequencyPotential`: `∂^μ A_μ = ε⁻¹ (η(dψ, b) cos − η(dψ, a) sin) + O(1)`
  with `η(dψ, a) = −a₀∂ₜψ + Σᵢ aᵢ∂ᵢψ` (`amplitudePairing`); `lorenz_leading_eq_zero_iff`: the
  gauge of Lorenz at the leading order is the transversality of the amplitudes.
* `leading_eq_zero_iff`: where the amplitude does not vanish, the coefficient of `ε⁻²` vanishes
  if and only if `⟨dψ, dψ⟩ = 0`, the **eikonal equation** (53.8) of the vacuum.
* `maxwell_highFrequencyPotential_iff`: in the gauge of Lorenz the vacuum equations of Maxwell of
  the family are `ε⁻² R₂ + ε⁻¹ R₁ + R₀ = 0`; `leadingOrders_eq_zero_iff`: the coefficients of
  `ε⁻²` and `ε⁻¹` vanish if and only if the eikonal equation and the transport equations hold,
  and then (`maxwell_highFrequencyPotential_iff_of_eikonal`) only the residual `R₀` of order one
  is left. `box_eq_zerothOrder_iff`: at a point where the phase and the amplitude do not vanish,
  `box A_μ = R₀` for every `ε ≠ 0` if and only if the eikonal and the transport equations hold
  there (the vacuum equations hold to the order `ε⁻¹`).
* `subleading_eq_zero_iff_transport`: the coefficient of `ε⁻¹` vanishes if and only if
  `T a_μ = T b_μ = 0`; along a ray, `d/ds a = ⟨da, dψ⟩` (`hasDerivAt_comp_ray`), so the transport
  equation is `d/ds a = −½ a □ψ` (`hasDerivAt_comp_ray_of_transport`).
* Rays: `Wave.raisedGradient ψ = (∂ₜψ, −∇ψ)` is the wave vector `k^μ = ∂^μψ`;
  `raisedGradient_eq_of_isRay`: on an open set where `⟨dψ, dψ⟩ = 0`, along a curve with velocity
  `k`, the velocity is constant, `d/ds k = ½ ∇⟨dψ, dψ⟩ = 0`
  (`timeDeriv_wavePairing_self`, `spaceDeriv_wavePairing_self`), and it is lightlike
  (`lightlike_raisedGradient`, `lightlike_of_isRay`).
* `divergence_intensityCurrent_eq_zero`: the transport equations make the intensity current
  `½ (a² + b²) ∂^μψ` (`intensityDensity`, `intensityFlux`) divergence-free (§54);
  `currentDivergence_intensity` is the identity `∂_μ (I ∂^μψ) = ½ (a T a + b T b)`, and
  `divergence_totalIntensityCurrent_eq_zero` sums the current over the components.
* `intensity_mul_det_eq`: the static form. For a `C¹` field `X` on `ℝ³` (the rays `X = ∇ψ` of a
  static wave) with `div (I X) = 0` on a set and a local flow `Φ` of `X` whose orbit stays in it,
  `I(Φ(t, x)) det DΦ(t, x) = I(x)`: the intensity times the cross-section of a tube of rays is
  constant.
* Instances: the plane wave `ψ = t − x₁` with constant amplitudes (`planePhase`,
  `planeWavePotential`), which solves everything, in particular the vacuum equations of Maxwell
  for a transverse polarization (`maxwell_planeWavePotential`, `box_planeWave_eq_zerothOrder`),
  with the rays `planeRay` (`lightlike_planeRay`); the outgoing spherical wave `ψ = t − r`,
  `a = 1/r` away from the origin, which satisfies the eikonal and the transport equations
  (`wavePairing_sphericalPhase`, `transport_sphericalAmplitude`), with a conserved intensity
  current (`divergence_intensityCurrent_spherical`) and the radial rays `sphericalRay`
  (`lightlike_sphericalRay`, `hasDerivAt_sphericalAmplitude_ray`); and the radial field
  `X(x) = x = ∇(|x|²/2)` with the flow `eᵗ x` and `I = |x|⁻³`, the inverse-square flux
  (`intensity_mul_det_radial`). The spherical field `x/|x|` is not smooth at the origin, and
  `IsLocalFlowOn.det_fderiv` asks for a field that is `C¹` on all of `ℝ³`.
-/

@[expose] public section

noncomputable section

open Real Filter Set MeasureTheory
open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics.Optics.Eikonal

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Wave SpecialRelativity
open SmoothGeometry.LinearODE SmoothGeometry.NonlinearODE

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The family of potentials -/

/-- The high-frequency family of potentials `A_μ = a_μ cos(ψ/ε) + b_μ sin(ψ/ε)` on space-time,
with the amplitudes `a_μ`, `b_μ` and the phase `ψ` written as functions of `(t, x)`. -/
def highFrequencyPotential (a b : Fin 4 → ℝ × E3 → ℝ) (ψ : ℝ × E3 → ℝ) (ε : ℝ) : Potential :=
  potentialOf (fun v => -highFrequencyWave (a 0) (b 0) ψ ε (timeSpaceEquiv v))
    fun v i => highFrequencyWave (a i.succ) (b i.succ) ψ ε (timeSpaceEquiv v)

/-- The components of the family are `a_μ cos(ψ/ε) + b_μ sin(ψ/ε)`. -/
theorem potentialComponent_highFrequencyPotential (a b : Fin 4 → ℝ × E3 → ℝ)
    (ψ : ℝ × E3 → ℝ) (ε : ℝ) (μ : Fin 4) :
    potentialComponent (highFrequencyPotential a b ψ ε) μ =
      fun v => highFrequencyWave (a μ) (b μ) ψ ε (timeSpaceEquiv v) := by
  refine Fin.cases ?_ (fun i => ?_) μ
  · rw [highFrequencyPotential, CavityModes.potentialComponent_potentialOf_zero]
    simp
  · rw [highFrequencyPotential, CavityModes.potentialComponent_potentialOf_succ]

/-- The potential `−φ dt + 𝐚 · d𝐱` is `Cⁿ` at a point where `φ` and the components of `𝐚` are. -/
theorem contDiffAt_potentialOf {n : ℕ∞ω} {φ : Spacetime → ℝ} {a : Spacetime → Fin 3 → ℝ}
    {v : Spacetime} (hφ : ContDiffAt ℝ n φ v) (ha : ∀ i, ContDiffAt ℝ n (fun y => a y i) v) :
    ContDiffAt ℝ n (potentialOf φ a) v := by
  unfold potentialOf
  exact oneCovector.symm.contDiff.contDiffAt.comp v
    ((hφ.neg.smul contDiffAt_const).add (ContDiffAt.sum fun i _ => (ha i).smul contDiffAt_const))

/-- The family is `C²` at a point where the amplitudes and the phase are. -/
theorem contDiffAt_highFrequencyPotential {a b : Fin 4 → ℝ × E3 → ℝ} {ψ : ℝ × E3 → ℝ}
    {v : Spacetime} (ha : ∀ μ, ContDiffAt ℝ 2 (a μ) (timeSpaceEquiv v))
    (hb : ∀ μ, ContDiffAt ℝ 2 (b μ) (timeSpaceEquiv v))
    (hψ : ContDiffAt ℝ 2 ψ (timeSpaceEquiv v)) (ε : ℝ) :
    ContDiffAt ℝ 2 (highFrequencyPotential a b ψ ε) v := by
  have h : ∀ μ, ContDiffAt ℝ 2 (fun w => highFrequencyWave (a μ) (b μ) ψ ε (timeSpaceEquiv w)) v :=
    fun μ => (contDiffAt_highFrequencyWave (ha μ) (hb μ) hψ ε).comp v
      timeSpaceEquiv.contDiff.contDiffAt
  exact contDiffAt_potentialOf (h 0).neg fun i => h i.succ

/-! ### Derivatives on space-time -/

/-- The derivatives on space-time of a function of `(t, x)` at a point where it is
differentiable: `∂₀` is `∂ₜ`. -/
theorem partialAt_comp_timeSpaceEquiv_zero {u : ℝ × E3 → ℝ} {v : Spacetime}
    (hu : DifferentiableAt ℝ u (timeSpaceEquiv v)) :
    partialAt (fun w => u (timeSpaceEquiv w)) 0 v = timeDeriv u (timeSpaceEquiv v) := by
  rw [partialAt, fderiv_comp_timeSpaceEquiv hu, timeSpaceEquiv_single_zero]
  rfl

/-- The derivatives on space-time of a function of `(t, x)` at a point where it is
differentiable: `∂ᵢ₊₁` is `∂ᵢ`. -/
theorem partialAt_comp_timeSpaceEquiv_succ {u : ℝ × E3 → ℝ} {v : Spacetime}
    (hu : DifferentiableAt ℝ u (timeSpaceEquiv v)) (i : Fin 3) :
    partialAt (fun w => u (timeSpaceEquiv w)) i.succ v = spaceDeriv i u (timeSpaceEquiv v) := by
  rw [partialAt, fderiv_comp_timeSpaceEquiv hu, timeSpaceEquiv_single_succ]
  rfl

/-- **The wave operator in time and space**, at a point where the function is `C²`:
`box (u ∘ split) = −□u ∘ split`. -/
theorem box_comp_timeSpaceEquiv_of_contDiffAt {u : ℝ × E3 → ℝ} {v : Spacetime}
    (hu : ContDiffAt ℝ 2 u (timeSpaceEquiv v)) :
    box (fun w => u (timeSpaceEquiv w)) v = -waveOperator u (timeSpaceEquiv v) := by
  have hev : ∀ᶠ w in 𝓝 v, DifferentiableAt ℝ u (timeSpaceEquiv w) :=
    (timeSpaceEquiv.continuous.continuousAt.eventually (hu.eventually (by simp))).mono
      fun w hw => hw.differentiableAt (by simp)
  have h0 : partialAt (fun w => u (timeSpaceEquiv w)) 0 =ᶠ[𝓝 v]
      fun w => timeDeriv u (timeSpaceEquiv w) :=
    hev.mono fun w hw => partialAt_comp_timeSpaceEquiv_zero hw
  have hi : ∀ i : Fin 3, partialAt (fun w => u (timeSpaceEquiv w)) i.succ =ᶠ[𝓝 v]
      fun w => spaceDeriv i u (timeSpaceEquiv w) := fun i =>
    hev.mono fun w hw => partialAt_comp_timeSpaceEquiv_succ hw i
  have h00 : partialAt (partialAt (fun w => u (timeSpaceEquiv w)) 0) 0 v =
      timeDeriv (timeDeriv u) (timeSpaceEquiv v) := by
    rw [partialAt_congr_of_eventuallyEq h0]
    exact partialAt_comp_timeSpaceEquiv_zero (differentiableAt_fderiv_apply hu _)
  have hii : ∀ i : Fin 3, partialAt (partialAt (fun w => u (timeSpaceEquiv w)) i.succ) i.succ v =
      spaceDeriv i (spaceDeriv i u) (timeSpaceEquiv v) := fun i => by
    rw [partialAt_congr_of_eventuallyEq (hi i)]
    exact partialAt_comp_timeSpaceEquiv_succ (differentiableAt_fderiv_apply hu _) i
  simp only [box, h00, hii, waveOperator]
  ring

/-! ### The expansion of the wave operator and of the divergence -/

/-- The value `c₁ cos θ + c₂ sin θ` of a pair of coefficients at the phase `θ`. -/
def trigValue (c : ℝ × ℝ) (θ : ℝ) : ℝ := c.1 * cos θ + c.2 * sin θ

/-- The coefficients of `ε⁻²` in `box A_μ`: `⟨dψ, dψ⟩ (a_μ, b_μ)`. -/
def leadingCoeff (a b : Fin 4 → ℝ × E3 → ℝ) (ψ : ℝ × E3 → ℝ) (μ : Fin 4) (q : ℝ × E3) :
    ℝ × ℝ :=
  (wavePairing ψ ψ q * a μ q, wavePairing ψ ψ q * b μ q)

/-- The coefficients of `ε⁻¹` in `box A_μ`: `(−T b_μ, T a_μ)` with the transport operator
`T a = 2⟨da, dψ⟩ + a □ψ`. -/
def subleadingCoeff (a b : Fin 4 → ℝ × E3 → ℝ) (ψ : ℝ × E3 → ℝ) (μ : Fin 4) (q : ℝ × E3) :
    ℝ × ℝ :=
  (-transport (b μ) ψ q, transport (a μ) ψ q)

/-- The coefficients of `ε⁰` in `box A_μ`: `(−□a_μ, −□b_μ)`. -/
def zerothCoeff (a b : Fin 4 → ℝ × E3 → ℝ) (μ : Fin 4) (q : ℝ × E3) : ℝ × ℝ :=
  (-waveOperator (a μ) q, -waveOperator (b μ) q)

/-- **The expansion of `box A_μ`** in powers of `1/ε`: at a point where the amplitudes and the
phase are `C²`, `box A_μ = ε⁻² R₂ + ε⁻¹ R₁ + R₀` with `Rₖ = c₁ cos(ψ/ε) + c₂ sin(ψ/ε)` and the
coefficients `leadingCoeff`, `subleadingCoeff` and `zerothCoeff`, which do not depend on `ε`. -/
theorem box_highFrequencyPotential {a b : Fin 4 → ℝ × E3 → ℝ} {ψ : ℝ × E3 → ℝ} {v : Spacetime}
    {μ : Fin 4} (ha : ContDiffAt ℝ 2 (a μ) (timeSpaceEquiv v))
    (hb : ContDiffAt ℝ 2 (b μ) (timeSpaceEquiv v)) (hψ : ContDiffAt ℝ 2 ψ (timeSpaceEquiv v))
    {ε : ℝ} (hε : ε ≠ 0) :
    box (potentialComponent (highFrequencyPotential a b ψ ε) μ) v =
      ε⁻¹ ^ 2 * trigValue (leadingCoeff a b ψ μ (timeSpaceEquiv v))
          (ψ (timeSpaceEquiv v) / ε) +
        ε⁻¹ * trigValue (subleadingCoeff a b ψ μ (timeSpaceEquiv v))
          (ψ (timeSpaceEquiv v) / ε) +
        trigValue (zerothCoeff a b μ (timeSpaceEquiv v)) (ψ (timeSpaceEquiv v) / ε) := by
  rw [potentialComponent_highFrequencyPotential,
    box_comp_timeSpaceEquiv_of_contDiffAt (contDiffAt_highFrequencyWave ha hb hψ ε),
    waveOperator_highFrequencyWave ha hb hψ hε]
  simp only [trigValue, leadingCoeff, subleadingCoeff, zerothCoeff]
  ring

/-- The pairing `η(dψ, a) = −a₀ ∂ₜψ + Σᵢ aᵢ ∂ᵢψ` of the amplitudes with the gradient of the phase,
in the signature `(−+++)` of `lorenzDivergence`. -/
def amplitudePairing (a : Fin 4 → ℝ × E3 → ℝ) (ψ : ℝ × E3 → ℝ) (q : ℝ × E3) : ℝ :=
  -(a 0 q * timeDeriv ψ q) + ∑ i : Fin 3, a i.succ q * spaceDeriv i ψ q

/-- The divergence `−∂ₜa₀ + Σᵢ ∂ᵢaᵢ` of the amplitudes. -/
def amplitudeDivergence (a : Fin 4 → ℝ × E3 → ℝ) (q : ℝ × E3) : ℝ :=
  -timeDeriv (a 0) q + ∑ i : Fin 3, spaceDeriv i (a i.succ) q

/-- **The expansion of the divergence** `∂^μ A_μ = ε⁻¹ (η(dψ, b) cos − η(dψ, a) sin) +
(∂^μ a_μ cos + ∂^μ b_μ sin)`, at a point where the amplitudes and the phase are
differentiable. -/
theorem lorenzDivergence_highFrequencyPotential {a b : Fin 4 → ℝ × E3 → ℝ} {ψ : ℝ × E3 → ℝ}
    {v : Spacetime} (ha : ∀ μ, DifferentiableAt ℝ (a μ) (timeSpaceEquiv v))
    (hb : ∀ μ, DifferentiableAt ℝ (b μ) (timeSpaceEquiv v))
    (hψ : DifferentiableAt ℝ ψ (timeSpaceEquiv v)) (ε : ℝ) :
    lorenzDivergence (highFrequencyPotential a b ψ ε) v =
      ε⁻¹ * trigValue (amplitudePairing b ψ (timeSpaceEquiv v),
          -amplitudePairing a ψ (timeSpaceEquiv v)) (ψ (timeSpaceEquiv v) / ε) +
        trigValue (amplitudeDivergence a (timeSpaceEquiv v),
          amplitudeDivergence b (timeSpaceEquiv v)) (ψ (timeSpaceEquiv v) / ε) := by
  have hd : ∀ μ, DifferentiableAt ℝ (highFrequencyWave (a μ) (b μ) ψ ε) (timeSpaceEquiv v) :=
    fun μ => ((ha μ).mul (hasFDerivAt_div_const hψ ε).differentiableAt.cos).add
      ((hb μ).mul (hasFDerivAt_div_const hψ ε).differentiableAt.sin)
  have hs : ∀ i : Fin 3, partialAt (potentialComponent (highFrequencyPotential a b ψ ε) i.succ)
      i.succ v = spaceDeriv i (highFrequencyWave (a i.succ) (b i.succ) ψ ε)
        (timeSpaceEquiv v) := fun i => by
    rw [potentialComponent_highFrequencyPotential]
    exact partialAt_comp_timeSpaceEquiv_succ (hd i.succ) i
  have h0 : partialAt (potentialComponent (highFrequencyPotential a b ψ ε) 0) 0 v =
      timeDeriv (highFrequencyWave (a 0) (b 0) ψ ε) (timeSpaceEquiv v) := by
    rw [potentialComponent_highFrequencyPotential]
    exact partialAt_comp_timeSpaceEquiv_zero (hd 0)
  rw [lorenzDivergence, h0, Finset.sum_congr rfl fun i _ => hs i,
    timeDeriv_highFrequencyWave (ha 0) (hb 0) hψ]
  simp only [spaceDeriv_highFrequencyWave (ha _) (hb _) hψ, trigValue, amplitudePairing,
    amplitudeDivergence, Fin.sum_univ_three]
  ring

/-- **The gauge of Lorenz at the leading order** is the transversality of the amplitudes:
the coefficients of `ε⁻¹` in `∂^μ A_μ` vanish if and only if `η(dψ, a) = η(dψ, b) = 0`. -/
theorem lorenz_leading_eq_zero_iff (a b : Fin 4 → ℝ × E3 → ℝ) (ψ : ℝ × E3 → ℝ) (q : ℝ × E3) :
    ((amplitudePairing b ψ q, -amplitudePairing a ψ q) : ℝ × ℝ) = 0 ↔
      amplitudePairing a ψ q = 0 ∧ amplitudePairing b ψ q = 0 := by
  rw [Prod.mk_eq_zero, neg_eq_zero, and_comm]

/-! ### The eikonal equation and the transport equations -/

/-- **The eikonal equation** (53.8): at a point where the amplitude does not vanish, the
coefficients of `ε⁻²` in `box A_μ` vanish if and only if `⟨dψ, dψ⟩ = 0`. -/
theorem leading_eq_zero_iff {a b : Fin 4 → ℝ × E3 → ℝ} {ψ : ℝ × E3 → ℝ} {q : ℝ × E3}
    (h : ∃ μ, ((a μ q, b μ q) : ℝ × ℝ) ≠ 0) :
    (∀ μ, leadingCoeff a b ψ μ q = 0) ↔ wavePairing ψ ψ q = 0 := by
  constructor
  · intro hc
    obtain ⟨μ, hμ⟩ := h
    have h1 := congrArg Prod.fst (hc μ)
    have h2 := congrArg Prod.snd (hc μ)
    simp only [leadingCoeff, Prod.fst_zero, Prod.snd_zero, mul_eq_zero] at h1 h2
    by_contra hne
    exact hμ (Prod.ext (h1.resolve_left hne) (h2.resolve_left hne))
  · intro hw μ
    simp [leadingCoeff, hw]

/-- **The transport equations**: the coefficients of `ε⁻¹` in `box A_μ` vanish if and only if
`T a_μ = 2⟨da_μ, dψ⟩ + a_μ □ψ = 0` and `T b_μ = 0`. -/
theorem subleading_eq_zero_iff_transport {a b : Fin 4 → ℝ × E3 → ℝ} {ψ : ℝ × E3 → ℝ}
    {q : ℝ × E3} :
    (∀ μ, subleadingCoeff a b ψ μ q = 0) ↔
      ∀ μ, transport (a μ) ψ q = 0 ∧ transport (b μ) ψ q = 0 := by
  refine forall_congr' fun μ => ?_
  rw [subleadingCoeff, Prod.mk_eq_zero, neg_eq_zero, and_comm]

/-- **The vacuum equations at the two leading orders**: on a set where the amplitude does not
vanish, the coefficients of `ε⁻²` and of `ε⁻¹` in every `box A_μ` vanish if and only if the phase
satisfies the eikonal equation and the amplitudes the transport equations. -/
theorem leadingOrders_eq_zero_iff {a b : Fin 4 → ℝ × E3 → ℝ} {ψ : ℝ × E3 → ℝ}
    {U : Set (ℝ × E3)} (hne : ∀ q ∈ U, ∃ μ, ((a μ q, b μ q) : ℝ × ℝ) ≠ 0) :
    (∀ q ∈ U, ∀ μ, leadingCoeff a b ψ μ q = 0 ∧ subleadingCoeff a b ψ μ q = 0) ↔
      (∀ q ∈ U, wavePairing ψ ψ q = 0) ∧
        ∀ q ∈ U, ∀ μ, transport (a μ) ψ q = 0 ∧ transport (b μ) ψ q = 0 := by
  constructor
  · intro h
    exact ⟨fun q hq => (leading_eq_zero_iff (hne q hq)).mp fun μ => (h q hq μ).1,
      fun q hq => subleading_eq_zero_iff_transport.mp fun μ => (h q hq μ).2⟩
  · rintro ⟨he, ht⟩ q hq μ
    exact ⟨(leading_eq_zero_iff (hne q hq)).mpr (he q hq) μ,
      subleading_eq_zero_iff_transport.mpr (ht q hq) μ⟩

/-- **The equations of Maxwell of the family**: on an open set of space-time where the amplitudes
and the phase are `C²` and the family is in the gauge of Lorenz, the vacuum equations of Maxwell
hold if and only if `ε⁻² R₂ + ε⁻¹ R₁ + R₀ = 0` for every component. -/
theorem maxwell_highFrequencyPotential_iff {V : Set Spacetime} (hV : IsOpen V)
    {a b : Fin 4 → ℝ × E3 → ℝ} {ψ : ℝ × E3 → ℝ}
    (ha : ∀ v ∈ V, ∀ μ, ContDiffAt ℝ 2 (a μ) (timeSpaceEquiv v))
    (hb : ∀ v ∈ V, ∀ μ, ContDiffAt ℝ 2 (b μ) (timeSpaceEquiv v))
    (hψ : ∀ v ∈ V, ContDiffAt ℝ 2 ψ (timeSpaceEquiv v)) {ε : ℝ} (hε : ε ≠ 0)
    (hL : ∀ v ∈ V, lorenzDivergence (highFrequencyPotential a b ψ ε) v = 0) :
    (∀ y ∈ V, (divergence3 (magneticField (fieldTensor (highFrequencyPotential a b ψ ε))) y = 0 ∧
        ∀ i, partialAt (magneticField (fieldTensor (highFrequencyPotential a b ψ ε)) i) 0 y +
          curl (electricField (fieldTensor (highFrequencyPotential a b ψ ε))) y i = 0) ∧
      (divergence3 (electricField (fieldTensor (highFrequencyPotential a b ψ ε))) y = 0 ∧
        ∀ i, curl (magneticField (fieldTensor (highFrequencyPotential a b ψ ε))) y i -
          partialAt (electricField (fieldTensor (highFrequencyPotential a b ψ ε)) i) 0 y = 0)) ↔
    ∀ v ∈ V, ∀ μ,
      ε⁻¹ ^ 2 * trigValue (leadingCoeff a b ψ μ (timeSpaceEquiv v)) (ψ (timeSpaceEquiv v) / ε) +
        ε⁻¹ * trigValue (subleadingCoeff a b ψ μ (timeSpaceEquiv v))
          (ψ (timeSpaceEquiv v) / ε) +
        trigValue (zerothCoeff a b μ (timeSpaceEquiv v)) (ψ (timeSpaceEquiv v) / ε) = 0 := by
  have hA : ContDiffOn ℝ 2 (highFrequencyPotential a b ψ ε) V := fun v hv =>
    (contDiffAt_highFrequencyPotential (ha v hv) (hb v hv) (hψ v hv) ε).contDiffWithinAt
  have h := maxwell_iff_box_of_lorenz hV hA hL fun _ => 0
  simp only [Pi.zero_apply, neg_zero] at h
  rw [h]
  refine forall₂_congr fun v hv => ?_
  simp only [← box_highFrequencyPotential (ha v hv _) (hb v hv _) (hψ v hv) hε]
  exact ⟨fun h' μ => Fin.cases h'.1 h'.2 μ, fun h' => ⟨h' 0, fun i => h' i.succ⟩⟩

/-- **Geometrical optics in the gauge of Lorenz**: if the phase satisfies the eikonal equation
and the amplitudes the transport equations, the vacuum equations of Maxwell of the family reduce
to the vanishing of the residual `R₀ = −(□a_μ cos + □b_μ sin)` of order one. -/
theorem maxwell_highFrequencyPotential_iff_of_eikonal {V : Set Spacetime} (hV : IsOpen V)
    {a b : Fin 4 → ℝ × E3 → ℝ} {ψ : ℝ × E3 → ℝ}
    (ha : ∀ v ∈ V, ∀ μ, ContDiffAt ℝ 2 (a μ) (timeSpaceEquiv v))
    (hb : ∀ v ∈ V, ∀ μ, ContDiffAt ℝ 2 (b μ) (timeSpaceEquiv v))
    (hψ : ∀ v ∈ V, ContDiffAt ℝ 2 ψ (timeSpaceEquiv v)) {ε : ℝ} (hε : ε ≠ 0)
    (hL : ∀ v ∈ V, lorenzDivergence (highFrequencyPotential a b ψ ε) v = 0)
    (heik : ∀ v ∈ V, wavePairing ψ ψ (timeSpaceEquiv v) = 0)
    (htr : ∀ v ∈ V, ∀ μ, transport (a μ) ψ (timeSpaceEquiv v) = 0 ∧
      transport (b μ) ψ (timeSpaceEquiv v) = 0) :
    (∀ y ∈ V, (divergence3 (magneticField (fieldTensor (highFrequencyPotential a b ψ ε))) y = 0 ∧
        ∀ i, partialAt (magneticField (fieldTensor (highFrequencyPotential a b ψ ε)) i) 0 y +
          curl (electricField (fieldTensor (highFrequencyPotential a b ψ ε))) y i = 0) ∧
      (divergence3 (electricField (fieldTensor (highFrequencyPotential a b ψ ε))) y = 0 ∧
        ∀ i, curl (magneticField (fieldTensor (highFrequencyPotential a b ψ ε))) y i -
          partialAt (electricField (fieldTensor (highFrequencyPotential a b ψ ε)) i) 0 y = 0)) ↔
    ∀ v ∈ V, ∀ μ, waveOperator (a μ) (timeSpaceEquiv v) * cos (ψ (timeSpaceEquiv v) / ε) +
      waveOperator (b μ) (timeSpaceEquiv v) * sin (ψ (timeSpaceEquiv v) / ε) = 0 := by
  rw [maxwell_highFrequencyPotential_iff hV ha hb hψ hε hL]
  refine forall₂_congr fun v hv => forall_congr' fun μ => ?_
  simp only [trigValue, leadingCoeff, subleadingCoeff, zerothCoeff, heik v hv,
    (htr v hv μ).1, (htr v hv μ).2]
  constructor <;> intro h <;> linarith

/-- Two pairs of coefficients with `ε⁻² R₂ + ε⁻¹ R₁ = 0` at the phase `c/ε` for every `ε ≠ 0`,
`c ≠ 0`, vanish: the phases `2π`, `4π` see the cosine parts and `π/2`, `5π/2` the sine parts. -/
theorem eq_zero_of_forall_trigValue {L S : ℝ × ℝ} {c : ℝ} (hc : c ≠ 0)
    (h : ∀ ε : ℝ, ε ≠ 0 → ε⁻¹ ^ 2 * trigValue L (c / ε) + ε⁻¹ * trigValue S (c / ε) = 0) :
    L = 0 ∧ S = 0 := by
  have key : ∀ θ : ℝ, θ ≠ 0 → θ * trigValue L θ + c * trigValue S θ = 0 := fun θ hθ => by
    have h' := h (c / θ) (div_ne_zero hc hθ)
    rw [inv_div, div_div_cancel₀ hc] at h'
    field_simp at h'
    rw [mul_zero] at h'
    exact (mul_eq_zero.mp h').resolve_left hθ
  have hπ : π ≠ 0 := pi_ne_zero
  have h1 := key (2 * π) (by positivity)
  have h2 := key (2 * π + 2 * π) (by positivity)
  have h3 := key (π / 2) (by positivity)
  have h4 := key (π / 2 + 2 * π) (by positivity)
  simp only [trigValue, cos_two_pi, sin_two_pi,
    cos_pi_div_two, sin_pi_div_two, cos_add_two_pi, sin_add_two_pi, mul_one, mul_zero,
    add_zero, zero_add] at h1 h2 h3 h4
  have hL1 : L.1 = 0 := by
    have : 2 * π * L.1 = 0 := by linarith
    simpa [hπ] using this
  have hL2 : L.2 = 0 := by
    have : 2 * π * L.2 = 0 := by linarith
    simpa [hπ] using this
  have hS1 : S.1 = 0 := by
    rw [hL1, mul_zero, zero_add] at h1
    simpa [hc] using h1
  have hS2 : S.2 = 0 := by
    rw [hL2, mul_zero, zero_add] at h3
    simpa [hc] using h3
  exact ⟨Prod.ext hL1 hL2, Prod.ext hS1 hS2⟩

/-- **The vacuum equations to the order `ε⁻¹`**: at a point where the phase and the amplitude do
not vanish, `box A_μ` of the family is its residual `R₀` of order one for every `ε ≠ 0` and every
component if and only if the eikonal equation and the transport equations hold there. -/
theorem box_eq_zerothOrder_iff {a b : Fin 4 → ℝ × E3 → ℝ} {ψ : ℝ × E3 → ℝ} {v : Spacetime}
    (ha : ∀ μ, ContDiffAt ℝ 2 (a μ) (timeSpaceEquiv v))
    (hb : ∀ μ, ContDiffAt ℝ 2 (b μ) (timeSpaceEquiv v)) (hψ : ContDiffAt ℝ 2 ψ (timeSpaceEquiv v))
    (hψ0 : ψ (timeSpaceEquiv v) ≠ 0)
    (hne : ∃ μ, ((a μ (timeSpaceEquiv v), b μ (timeSpaceEquiv v)) : ℝ × ℝ) ≠ 0) :
    (∀ ε : ℝ, ε ≠ 0 → ∀ μ, box (potentialComponent (highFrequencyPotential a b ψ ε) μ) v =
        trigValue (zerothCoeff a b μ (timeSpaceEquiv v)) (ψ (timeSpaceEquiv v) / ε)) ↔
      wavePairing ψ ψ (timeSpaceEquiv v) = 0 ∧
        ∀ μ, transport (a μ) ψ (timeSpaceEquiv v) = 0 ∧
          transport (b μ) ψ (timeSpaceEquiv v) = 0 := by
  have hbox : ∀ ε : ℝ, ε ≠ 0 → ∀ μ,
      (box (potentialComponent (highFrequencyPotential a b ψ ε) μ) v =
        trigValue (zerothCoeff a b μ (timeSpaceEquiv v)) (ψ (timeSpaceEquiv v) / ε) ↔
      ε⁻¹ ^ 2 * trigValue (leadingCoeff a b ψ μ (timeSpaceEquiv v)) (ψ (timeSpaceEquiv v) / ε) +
        ε⁻¹ * trigValue (subleadingCoeff a b ψ μ (timeSpaceEquiv v))
          (ψ (timeSpaceEquiv v) / ε) = 0) := fun ε hε μ => by
    rw [box_highFrequencyPotential (ha μ) (hb μ) hψ hε]
    constructor <;> intro h <;> linarith
  constructor
  · intro h
    have hc : ∀ μ, leadingCoeff a b ψ μ (timeSpaceEquiv v) = 0 ∧
        subleadingCoeff a b ψ μ (timeSpaceEquiv v) = 0 := fun μ =>
      eq_zero_of_forall_trigValue hψ0 fun ε hε => (hbox ε hε μ).mp (h ε hε μ)
    exact ⟨(leading_eq_zero_iff hne).mp fun μ => (hc μ).1,
      subleading_eq_zero_iff_transport.mp fun μ => (hc μ).2⟩
  · rintro ⟨he, ht⟩ ε hε μ
    rw [hbox ε hε μ, (leading_eq_zero_iff hne).mpr he μ,
      subleading_eq_zero_iff_transport.mpr ht μ]
    simp [trigValue]

/-! ### Rays -/

/-- The derivative of `⟨dψ, dψ⟩` along `w`: `2 (∂_w(∂ₜψ) ∂ₜψ − Σᵢ ∂_w(∂ᵢψ) ∂ᵢψ)`. -/
theorem fderiv_wavePairing_self_apply {ψ : ℝ × E3 → ℝ} {q : ℝ × E3} (hψ : ContDiffAt ℝ 2 ψ q)
    (w : ℝ × E3) :
    fderiv ℝ (wavePairing ψ ψ) q w =
      2 * (fderiv ℝ (timeDeriv ψ) q w * timeDeriv ψ q -
        ∑ i, fderiv ℝ (spaceDeriv i ψ) q w * spaceDeriv i ψ q) := by
  have hT : DifferentiableAt ℝ (timeDeriv ψ) q := differentiableAt_fderiv_apply hψ _
  have hS : ∀ i, DifferentiableAt ℝ (spaceDeriv i ψ) q := fun i =>
    differentiableAt_fderiv_apply hψ _
  have H := (hT.hasFDerivAt.fun_mul hT.hasFDerivAt).fun_sub
    (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      (hS i).hasFDerivAt.fun_mul (hS i).hasFDerivAt)
  rw [show wavePairing ψ ψ = fun p => timeDeriv ψ p * timeDeriv ψ p -
      ∑ i, spaceDeriv i ψ p * spaceDeriv i ψ p from rfl, H.fderiv]
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

/-- `∂ₜ⟨dψ, dψ⟩ = 2⟨d(∂ₜψ), dψ⟩`. -/
theorem timeDeriv_wavePairing_self {ψ : ℝ × E3 → ℝ} {q : ℝ × E3} (hψ : ContDiffAt ℝ 2 ψ q) :
    timeDeriv (wavePairing ψ ψ) q = 2 * wavePairing (timeDeriv ψ) ψ q := by
  rw [timeDeriv, fderiv_wavePairing_self_apply hψ, wavePairing]
  change 2 * (timeDeriv (timeDeriv ψ) q * timeDeriv ψ q -
    ∑ i, timeDeriv (spaceDeriv i ψ) q * spaceDeriv i ψ q) = _
  simp only [timeDeriv_spaceDeriv hψ]

/-- `∂ⱼ⟨dψ, dψ⟩ = 2⟨d(∂ⱼψ), dψ⟩`. -/
theorem spaceDeriv_wavePairing_self {ψ : ℝ × E3 → ℝ} {q : ℝ × E3} (hψ : ContDiffAt ℝ 2 ψ q)
    (j : Fin 3) : spaceDeriv j (wavePairing ψ ψ) q = 2 * wavePairing (spaceDeriv j ψ) ψ q := by
  rw [spaceDeriv, fderiv_wavePairing_self_apply hψ, wavePairing]
  change 2 * (spaceDeriv j (timeDeriv ψ) q * timeDeriv ψ q -
    ∑ i, spaceDeriv j (spaceDeriv i ψ) q * spaceDeriv i ψ q) = _
  simp only [← timeDeriv_spaceDeriv hψ, spaceDeriv_spaceDeriv_comm hψ j]

/-- On an open set where the eikonal equation holds, `⟨d(∂ₜψ), dψ⟩ = 0` and
`⟨d(∂ⱼψ), dψ⟩ = 0`: the derivatives of the gradient along the raised gradient vanish. -/
theorem wavePairing_deriv_eq_zero {ψ : ℝ × E3 → ℝ} {U : Set (ℝ × E3)} (hU : IsOpen U)
    (heik : ∀ q ∈ U, wavePairing ψ ψ q = 0) {q : ℝ × E3} (hq : q ∈ U)
    (hψ : ContDiffAt ℝ 2 ψ q) :
    wavePairing (timeDeriv ψ) ψ q = 0 ∧ ∀ j, wavePairing (spaceDeriv j ψ) ψ q = 0 := by
  have hev : wavePairing ψ ψ =ᶠ[𝓝 q] fun _ => 0 := eventuallyEq_of_mem (hU.mem_nhds hq) heik
  have h0 : fderiv ℝ (wavePairing ψ ψ) q = 0 := by
    rw [hev.fderiv_eq, fderiv_const_apply]
  refine ⟨?_, fun j => ?_⟩
  · have h := timeDeriv_wavePairing_self hψ
    rw [timeDeriv, h0] at h
    simp only [zero_apply] at h
    linarith
  · have h := spaceDeriv_wavePairing_self hψ j
    rw [spaceDeriv, h0] at h
    simp only [zero_apply] at h
    linarith

/-- Along a curve whose velocity is the raised gradient `k = (∂ₜψ, −∇ψ)` of the phase, the
derivative of a function is `d/ds f = ⟨df, dψ⟩`. -/
theorem hasDerivAt_comp_ray {f ψ : ℝ × E3 → ℝ} {γ : ℝ → ℝ × E3} {s : ℝ}
    (hf : DifferentiableAt ℝ f (γ s)) (hγ : HasDerivAt γ (raisedGradient ψ (γ s)) s) :
    HasDerivAt (fun r => f (γ r)) (wavePairing f ψ (γ s)) s := by
  have h := hf.hasFDerivAt.comp_hasDerivAt s hγ
  rwa [fderiv_raisedGradient] at h

/-- A function whose pairing with `dψ` vanishes along a ray is constant on it. -/
theorem eq_of_isRay {f ψ : ℝ × E3 → ℝ} {γ : ℝ → ℝ × E3} {s₀ s₁ : ℝ}
    (hf : ∀ s ∈ Icc s₀ s₁, DifferentiableAt ℝ f (γ s))
    (hγ : ∀ s ∈ Icc s₀ s₁, HasDerivAt γ (raisedGradient ψ (γ s)) s)
    (h0 : ∀ s ∈ Icc s₀ s₁, wavePairing f ψ (γ s) = 0) :
    ∀ s ∈ Icc s₀ s₁, f (γ s) = f (γ s₀) := by
  have hd : ∀ s ∈ Icc s₀ s₁, HasDerivAt (fun r => f (γ r)) 0 s := fun s hs => by
    have h := hasDerivAt_comp_ray (hf s hs) (hγ s hs)
    rwa [h0 s hs] at h
  exact constant_of_has_deriv_right_zero
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt

/-- **The rays are straight lines** (§53): on an open set where `⟨dψ, dψ⟩ = 0`, along a curve in
the set whose velocity is the raised gradient `k = (∂ₜψ, −∇ψ)`, the velocity is constant, since
`d/ds k = ½ ∇⟨dψ, dψ⟩ = 0`. -/
theorem raisedGradient_eq_of_isRay {ψ : ℝ × E3 → ℝ} {U : Set (ℝ × E3)} (hU : IsOpen U)
    (hψ : ∀ q ∈ U, ContDiffAt ℝ 2 ψ q) (heik : ∀ q ∈ U, wavePairing ψ ψ q = 0)
    {γ : ℝ → ℝ × E3} {s₀ s₁ : ℝ} (hγU : ∀ s ∈ Icc s₀ s₁, γ s ∈ U)
    (hγ : ∀ s ∈ Icc s₀ s₁, HasDerivAt γ (raisedGradient ψ (γ s)) s) :
    ∀ s ∈ Icc s₀ s₁, raisedGradient ψ (γ s) = raisedGradient ψ (γ s₀) := by
  intro s hs
  have ht := eq_of_isRay (f := timeDeriv ψ)
    (fun r hr => differentiableAt_fderiv_apply (hψ _ (hγU r hr)) _) hγ
    (fun r hr => (wavePairing_deriv_eq_zero hU heik (hγU r hr) (hψ _ (hγU r hr))).1) s hs
  have hx : ∀ j, spaceDeriv j ψ (γ s) = spaceDeriv j ψ (γ s₀) := fun j =>
    eq_of_isRay (f := spaceDeriv j ψ)
      (fun r hr => differentiableAt_fderiv_apply (hψ _ (hγU r hr)) _) hγ
      (fun r hr => (wavePairing_deriv_eq_zero hU heik (hγU r hr) (hψ _ (hγU r hr))).2 j) s hs
  simp only [raisedGradient, ht, hx]

/-- The interval of the raised gradient is `⟨dψ, dψ⟩`. -/
theorem intervalQuadratic_raisedGradient (ψ : ℝ × E3 → ℝ) (q : ℝ × E3) :
    intervalQuadratic (timeSpaceEquiv.symm (raisedGradient ψ q)) = wavePairing ψ ψ q := by
  rw [intervalQuadratic_coordinates, timeSpaceEquiv_symm_apply, time_vector, space_vector,
    EuclideanSpace.real_norm_sq_eq, wavePairing]
  simp only [raisedGradient, PiLp.toLp_apply, Fin.sum_univ_three]
  ring

/-- Where the eikonal equation holds and the gradient does not vanish, the raised gradient is
lightlike. -/
theorem lightlike_raisedGradient {ψ : ℝ × E3 → ℝ} {q : ℝ × E3} (heik : wavePairing ψ ψ q = 0)
    (hne : raisedGradient ψ q ≠ 0) : Lightlike (timeSpaceEquiv.symm (raisedGradient ψ q)) :=
  ⟨fun h => hne (timeSpaceEquiv.symm.map_eq_zero_iff.mp h),
    (intervalQuadratic_raisedGradient ψ q).trans heik⟩

/-- **The rays are lightlike straight lines**: under the hypotheses of
`raisedGradient_eq_of_isRay`, if the gradient does not vanish at the start, the velocity of the
ray is the same lightlike vector at every point. -/
theorem lightlike_of_isRay {ψ : ℝ × E3 → ℝ} {U : Set (ℝ × E3)} (hU : IsOpen U)
    (hψ : ∀ q ∈ U, ContDiffAt ℝ 2 ψ q) (heik : ∀ q ∈ U, wavePairing ψ ψ q = 0)
    {γ : ℝ → ℝ × E3} {s₀ s₁ : ℝ} (hγU : ∀ s ∈ Icc s₀ s₁, γ s ∈ U)
    (hγ : ∀ s ∈ Icc s₀ s₁, HasDerivAt γ (raisedGradient ψ (γ s)) s)
    (hne : raisedGradient ψ (γ s₀) ≠ 0) :
    ∀ s ∈ Icc s₀ s₁, raisedGradient ψ (γ s) = raisedGradient ψ (γ s₀) ∧
      Lightlike (timeSpaceEquiv.symm (raisedGradient ψ (γ s))) := by
  intro s hs
  have h := raisedGradient_eq_of_isRay hU hψ heik hγU hγ s hs
  exact ⟨h, lightlike_raisedGradient (heik _ (hγU s hs)) (h ▸ hne)⟩

/-- **The transport equation along a ray** (§54): if `T a = 2⟨da, dψ⟩ + a □ψ = 0` at a point of
a ray, there `d/ds a = −½ a □ψ`. -/
theorem hasDerivAt_comp_ray_of_transport {a ψ : ℝ × E3 → ℝ} {γ : ℝ → ℝ × E3} {s : ℝ}
    (ha : DifferentiableAt ℝ a (γ s)) (hγ : HasDerivAt γ (raisedGradient ψ (γ s)) s)
    (htr : transport a ψ (γ s) = 0) :
    HasDerivAt (fun r => a (γ r)) (-(a (γ s) * waveOperator ψ (γ s)) / 2) s := by
  have h := hasDerivAt_comp_ray ha hγ
  rw [transport] at htr
  convert h using 1
  linarith

/-! ### The intensity -/

/-- The divergence `∂ₜρ + Σᵢ ∂ᵢjᵢ` of a current with the density `ρ` and the flux `j` on
`ℝ × ℝ³`. -/
def currentDivergence (ρ : ℝ × E3 → ℝ) (j : Fin 3 → ℝ × E3 → ℝ) (q : ℝ × E3) : ℝ :=
  timeDeriv ρ q + ∑ i, spaceDeriv i (j i) q

/-- The intensity `½ (a² + b²)` of the wave `a cos(ψ/ε) + b sin(ψ/ε)`, its mean square over a
period of the phase. -/
def intensity (a b : ℝ × E3 → ℝ) (q : ℝ × E3) : ℝ := (a q ^ 2 + b q ^ 2) / 2

/-- The density `I ∂ₜψ` of the intensity current `I k = I (∂ₜψ, −∇ψ)`. -/
def intensityDensity (a b ψ : ℝ × E3 → ℝ) (q : ℝ × E3) : ℝ := intensity a b q * timeDeriv ψ q

/-- The flux `−I ∇ψ` of the intensity current `I k = I (∂ₜψ, −∇ψ)`. -/
def intensityFlux (a b ψ : ℝ × E3 → ℝ) (i : Fin 3) (q : ℝ × E3) : ℝ :=
  -(intensity a b q * spaceDeriv i ψ q)

/-- The derivative of the intensity, `dI = a da + b db`. -/
theorem hasFDerivAt_intensity {a b : ℝ × E3 → ℝ} {q : ℝ × E3} (ha : DifferentiableAt ℝ a q)
    (hb : DifferentiableAt ℝ b q) :
    HasFDerivAt (intensity a b) (a q • fderiv ℝ a q + b q • fderiv ℝ b q) q := by
  have h := ((ha.hasFDerivAt.fun_mul ha.hasFDerivAt).fun_add
    (hb.hasFDerivAt.fun_mul hb.hasFDerivAt)).mul_const (1 / 2 : ℝ)
  have he : intensity a b = fun p => (a p * a p + b p * b p) * (1 / 2) := by
    funext p
    simp only [intensity]
    ring
  rw [he]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
  simp only [smul_apply, add_apply, smul_eq_mul]
  ring

/-- The derivative of the product of the intensity with a differentiable function. -/
theorem fderiv_intensity_mul_apply {a b f : ℝ × E3 → ℝ} {q : ℝ × E3}
    (ha : DifferentiableAt ℝ a q) (hb : DifferentiableAt ℝ b q) (hf : DifferentiableAt ℝ f q)
    (w : ℝ × E3) :
    fderiv ℝ (fun p => intensity a b p * f p) q w =
      intensity a b q * fderiv ℝ f q w +
        f q * (a q * fderiv ℝ a q w + b q * fderiv ℝ b q w) := by
  rw [((hasFDerivAt_intensity ha hb).fun_mul hf.hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]

/-- **The divergence of the intensity current**: `∂_μ (I ∂^μψ) = ⟨dI, dψ⟩ + I □ψ =
½ (a T a + b T b)`, at a point where `a`, `b` are differentiable and `ψ` is `C²`. -/
theorem currentDivergence_intensity {a b ψ : ℝ × E3 → ℝ} {q : ℝ × E3}
    (ha : DifferentiableAt ℝ a q) (hb : DifferentiableAt ℝ b q) (hψ : ContDiffAt ℝ 2 ψ q) :
    currentDivergence (intensityDensity a b ψ) (intensityFlux a b ψ) q =
      (a q * transport a ψ q + b q * transport b ψ q) / 2 := by
  have h0 : timeDeriv (intensityDensity a b ψ) q =
      intensity a b q * timeDeriv (timeDeriv ψ) q +
        timeDeriv ψ q * (a q * timeDeriv a q + b q * timeDeriv b q) :=
    fderiv_intensity_mul_apply ha hb (differentiableAt_fderiv_apply hψ _) _
  have hi : ∀ i, spaceDeriv i (intensityFlux a b ψ i) q =
      -(intensity a b q * spaceDeriv i (spaceDeriv i ψ) q +
        spaceDeriv i ψ q * (a q * spaceDeriv i a q + b q * spaceDeriv i b q)) := fun i => by
    have hd : HasFDerivAt (fun p => -(intensity a b p * spaceDeriv i ψ p)) _ q :=
      ((hasFDerivAt_intensity ha hb).fun_mul
        (differentiableAt_fderiv_apply hψ ((0 : ℝ), EuclideanSpace.single i 1)).hasFDerivAt).fun_neg
    rw [spaceDeriv, show intensityFlux a b ψ i = fun p => -(intensity a b p * spaceDeriv i ψ p)
      from rfl, hd.fderiv]
    simp only [neg_apply, add_apply, smul_apply, smul_eq_mul]
    rfl
  rw [currentDivergence, h0, Finset.sum_congr rfl fun i _ => hi i]
  simp only [transport, wavePairing, waveOperator, intensity, Fin.sum_univ_three]
  ring

/-- **The intensity current is conserved** (§54): where the amplitudes satisfy the transport
equations, the current `½ (a² + b²) ∂^μψ` is divergence-free. -/
theorem divergence_intensityCurrent_eq_zero {a b ψ : ℝ × E3 → ℝ} {q : ℝ × E3}
    (ha : DifferentiableAt ℝ a q) (hb : DifferentiableAt ℝ b q) (hψ : ContDiffAt ℝ 2 ψ q)
    (hta : transport a ψ q = 0) (htb : transport b ψ q = 0) :
    currentDivergence (intensityDensity a b ψ) (intensityFlux a b ψ) q = 0 := by
  rw [currentDivergence_intensity ha hb hψ, hta, htb]
  ring

/-- The intensity current summed over the components of the potential is conserved where every
component satisfies the transport equations. -/
theorem divergence_totalIntensityCurrent_eq_zero {a b : Fin 4 → ℝ × E3 → ℝ} {ψ : ℝ × E3 → ℝ}
    {q : ℝ × E3} (ha : ∀ μ, DifferentiableAt ℝ (a μ) q) (hb : ∀ μ, DifferentiableAt ℝ (b μ) q)
    (hψ : ContDiffAt ℝ 2 ψ q)
    (htr : ∀ μ, transport (a μ) ψ q = 0 ∧ transport (b μ) ψ q = 0) :
    currentDivergence (fun p => ∑ μ, intensityDensity (a μ) (b μ) ψ p)
      (fun i p => ∑ μ, intensityFlux (a μ) (b μ) ψ i p) q = 0 := by
  have hI : ∀ μ, DifferentiableAt ℝ (intensity (a μ) (b μ)) q := fun μ =>
    (hasFDerivAt_intensity (ha μ) (hb μ)).differentiableAt
  have hρ : ∀ μ ∈ Finset.univ, DifferentiableAt ℝ (intensityDensity (a μ) (b μ) ψ) q :=
    fun μ _ => (hI μ).mul (differentiableAt_fderiv_apply hψ _)
  have hj : ∀ i, ∀ μ ∈ Finset.univ, DifferentiableAt ℝ (intensityFlux (a μ) (b μ) ψ i) q :=
    fun i μ _ => ((hI μ).mul (differentiableAt_fderiv_apply hψ _)).neg
  rw [currentDivergence, timeDeriv_fun_sum _ hρ,
    Finset.sum_congr rfl fun i _ => spaceDeriv_fun_sum _ (hj i) i, Finset.sum_comm,
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun μ _ => ?_
  exact divergence_intensityCurrent_eq_zero (ha μ) (hb μ) hψ (htr μ).1 (htr μ).2

/-! ### The static form -/

/-- The divergence of `I X` is `dI(X) + I div X`. -/
theorem traceCLM_fderiv_smul {I : E3 → ℝ} {X : E3 → E3} {y : E3} (hI : DifferentiableAt ℝ I y)
    (hX : DifferentiableAt ℝ X y) :
    traceCLM (fderiv ℝ (fun z => I z • X z) y) =
      fderiv ℝ I y (X y) + I y * traceCLM (fderiv ℝ X y) := by
  rw [fderiv_fun_smul hI hX, map_add, map_smul, smul_eq_mul, add_comm]
  congr 1
  rw [traceCLM_apply]
  exact LinearMap.trace_smulRight (fderiv ℝ I y : E3 →ₗ[ℝ] ℝ) (X y)

/-- **The intensity along a tube of rays** (§54, static form): let `Φ` be a local flow of a
`C¹` field `X` on `ℝ³` (the rays of a static wave, `X = ∇ψ`), and let `div (I X) = 0` on a set
that contains the orbit of `x` up to the time `t`. Then `I(Φ(t, x)) det DΦ(t, x) = I(x)`: the
intensity times the cross-section of an infinitesimal tube of rays is constant. -/
theorem intensity_mul_det_eq {X : E3 → E3} {Φ : ℝ × E3 → E3} {Ω : Set (ℝ × E3)}
    (hflow : IsLocalFlowOn X Φ Ω) (hX : ContDiff ℝ 1 X) {U : Set E3}
    {I : E3 → ℝ} (hI : ∀ y ∈ U, DifferentiableAt ℝ I y)
    (hdiv : ∀ y ∈ U, traceCLM (fderiv ℝ (fun z => I z • X z) y) = 0) {t : ℝ} {x : E3}
    (hp : (t, x) ∈ Ω) (horb : ∀ s ∈ uIcc 0 t, Φ (s, x) ∈ U) :
    I (Φ (t, x)) * LinearMap.det (fderiv ℝ (fun y => Φ (t, y)) x : E3 →ₗ[ℝ] E3) = I x := by
  set g : ℝ → ℝ := fun r => traceCLM (fderiv ℝ X (Φ (r, x))) with hg
  set Ωx : Set ℝ := {r | (r, x) ∈ Ω} with hΩx
  have hline : Continuous fun r : ℝ => ((r, x) : ℝ × E3) := continuous_id.prodMk continuous_const
  have hΩo : IsOpen Ωx := hflow.isOpen.preimage hline
  have hgc : ContinuousOn g Ωx := fun r hr =>
    ((traceCLM (E := E3)).continuous.continuousAt.comp
      ((hX.continuous_fderiv one_ne_zero).continuousAt.comp
        (ContinuousAt.comp (f := fun r : ℝ => ((r, x) : ℝ × E3))
          (hflow.differentiableAt hr).continuousAt hline.continuousAt))).continuousWithinAt
  have hseg : ∀ s ∈ uIcc 0 t, uIcc 0 s ⊆ Ωx := fun s hs r hr =>
    hflow.segment (s, x) (hflow.segment _ hp s hs) r hr
  have hmem : ∀ s ∈ uIcc 0 t, s ∈ Ωx := fun s hs => hflow.segment _ hp s hs
  let F : ℝ → ℝ := fun s => I (Φ (s, x)) * Real.exp (∫ r in (0 : ℝ)..s, g r)
  have hF : ∀ s ∈ uIcc 0 t, HasDerivAt F 0 s := by
    intro s hs
    have hG : HasDerivAt (fun u => ∫ r in (0 : ℝ)..u, g r) (g s) s :=
      intervalIntegral.integral_hasDerivAt_right
        ((hgc.mono (hseg s hs)).intervalIntegrable)
        (hgc.stronglyMeasurableAtFilter hΩo s (hmem s hs))
        (hgc.continuousAt (hΩo.mem_nhds (hmem s hs)))
    have hΦ := hflow.hasDerivAt (s, x) (hmem s hs)
    have hIΦ : HasDerivAt (fun r => I (Φ (r, x)))
        (fderiv ℝ I (Φ (s, x)) (X (Φ (s, x)))) s :=
      (hI _ (horb s hs)).hasFDerivAt.comp_hasDerivAt s hΦ
    have H := hIΦ.mul hG.exp
    have htr := traceCLM_fderiv_smul (hI _ (horb s hs))
      ((hX.differentiable one_ne_zero) (Φ (s, x)))
    rw [hdiv _ (horb s hs)] at htr
    convert H using 1
    simp only [hg]
    linear_combination (Real.exp (∫ r in (0 : ℝ)..s, g r)) * htr
  have hconst : ∀ s ∈ Icc (min 0 t) (max 0 t), F s = F (min 0 t) :=
    constant_of_has_deriv_right_zero
      (fun s hs => (hF s hs).continuousAt.continuousWithinAt)
      fun s hs => (hF s (Ico_subset_Icc_self hs)).hasDerivWithinAt
  have hFt := hconst t ⟨min_le_right 0 t, le_max_right 0 t⟩
  have hF0 := hconst 0 ⟨min_le_left 0 t, le_max_left 0 t⟩
  have e0 : F 0 = I x := by
    simp only [F, intervalIntegral.integral_same, Real.exp_zero, mul_one]
    rw [hflow.initial _ hp]
  rw [hflow.det_fderiv hX hp, ← e0, hF0.trans hFt.symm]

/-! ### Constant amplitudes and linear phases -/

/-- The time derivative of a constant vanishes. -/
theorem timeDeriv_const (c : ℝ) (q : ℝ × E3) : timeDeriv (fun _ => c) q = 0 := by
  rw [timeDeriv, fderiv_const_apply, zero_apply]

/-- The spatial derivatives of a constant vanish. -/
theorem spaceDeriv_const (c : ℝ) (i : Fin 3) (q : ℝ × E3) :
    spaceDeriv i (fun _ => c) q = 0 := by
  rw [spaceDeriv, fderiv_const_apply, zero_apply]

/-- The wave operator of a constant vanishes. -/
theorem waveOperator_const (c : ℝ) (q : ℝ × E3) : waveOperator (fun _ => c) q = 0 := by
  have ht : timeDeriv (fun _ : ℝ × E3 => c) = fun _ => 0 := funext (timeDeriv_const c)
  have hs : ∀ i, spaceDeriv i (fun _ : ℝ × E3 => c) = fun _ => 0 := fun i =>
    funext (spaceDeriv_const c i)
  simp only [waveOperator, ht, hs, timeDeriv_const, spaceDeriv_const, Finset.sum_const_zero,
    sub_zero]

/-- The pairing of a constant with any function vanishes. -/
theorem wavePairing_const (c : ℝ) (ψ : ℝ × E3 → ℝ) (q : ℝ × E3) :
    wavePairing (fun _ => c) ψ q = 0 := by
  simp only [wavePairing, timeDeriv_const, spaceDeriv_const, zero_mul, Finset.sum_const_zero,
    sub_zero]

/-- The transport operator of a constant amplitude is `c □ψ`. -/
theorem transport_const (c : ℝ) (ψ : ℝ × E3 → ℝ) (q : ℝ × E3) :
    transport (fun _ => c) ψ q = c * waveOperator ψ q := by
  rw [transport, wavePairing_const, mul_zero, zero_add]

/-- The time derivative of a linear function `L` is `L(1, 0)`. -/
theorem timeDeriv_clm (L : ℝ × E3 →L[ℝ] ℝ) (q : ℝ × E3) : timeDeriv L q = L (1, 0) := by
  rw [timeDeriv, L.fderiv]

/-- The spatial derivatives of a linear function `L` are `L(0, eᵢ)`. -/
theorem spaceDeriv_clm (L : ℝ × E3 →L[ℝ] ℝ) (i : Fin 3) (q : ℝ × E3) :
    spaceDeriv i L q = L (0, EuclideanSpace.single i 1) := by
  rw [spaceDeriv, L.fderiv]

/-- The wave operator of a linear function vanishes. -/
theorem waveOperator_clm (L : ℝ × E3 →L[ℝ] ℝ) (q : ℝ × E3) : waveOperator L q = 0 := by
  have ht : timeDeriv L = fun _ => L (1, 0) := funext (timeDeriv_clm L)
  have hs : ∀ i, spaceDeriv i L = fun _ => L (0, EuclideanSpace.single i 1) := fun i =>
    funext (spaceDeriv_clm L i)
  simp only [waveOperator, ht, hs, timeDeriv_const, spaceDeriv_const, Finset.sum_const_zero,
    sub_zero]

/-- The phase `ψ = t − x₁` of a plane wave along the first axis. -/
def planePhase : ℝ × E3 →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ E3 -
    (EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ E3)

/-- `∂ₜ(t − x₁) = 1`. -/
theorem timeDeriv_planePhase (q : ℝ × E3) : timeDeriv planePhase q = 1 := by
  rw [timeDeriv_clm]
  simp [planePhase]

/-- `∂ᵢ(t − x₁) = −δᵢ₁`. -/
theorem spaceDeriv_planePhase (i : Fin 3) (q : ℝ × E3) :
    spaceDeriv i planePhase q = -if i = 0 then 1 else 0 := by
  rw [spaceDeriv_clm]
  simp [planePhase, eq_comm]

/-- The plane phase satisfies the eikonal equation. -/
theorem wavePairing_planePhase (q : ℝ × E3) : wavePairing planePhase planePhase q = 0 := by
  simp only [wavePairing, timeDeriv_planePhase, spaceDeriv_planePhase, Fin.sum_univ_three]
  simp

/-- The wave vector of the plane phase is `(1, e₁)`. -/
theorem raisedGradient_planePhase (q : ℝ × E3) :
    raisedGradient planePhase q = (1, EuclideanSpace.single 0 1) := by
  simp only [raisedGradient, timeDeriv_planePhase, spaceDeriv_planePhase, neg_neg]
  congr 1
  ext i
  simp

/-- The ray `s ↦ (s, s e₁)` of the plane wave. -/
def planeRay (s : ℝ) : ℝ × E3 := (s, s • EuclideanSpace.single 0 1)

/-- The velocity of `planeRay` is the wave vector of the plane phase. -/
theorem hasDerivAt_planeRay (s : ℝ) :
    HasDerivAt planeRay (raisedGradient planePhase (planeRay s)) s := by
  have h := (hasDerivAt_id s).smul_const (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
  rw [one_smul] at h
  rw [raisedGradient_planePhase]
  exact (hasDerivAt_id s).prodMk h

/-! ### The spherical wave -/

/-- The phase `ψ = t − |x|` of an outgoing spherical wave. -/
def sphericalPhase (q : ℝ × E3) : ℝ := q.1 - ‖q.2‖

/-- The amplitude `1/|x|` of an outgoing spherical wave. -/
def sphericalAmplitude (q : ℝ × E3) : ℝ := ‖q.2‖⁻¹

/-- The derivative of `|x|` away from the origin. -/
theorem hasFDerivAt_norm_snd {q : ℝ × E3} (hq : q.2 ≠ 0) :
    HasFDerivAt (fun p : ℝ × E3 => ‖p.2‖)
      ((‖q.2‖⁻¹ • innerSL ℝ q.2).comp (ContinuousLinearMap.snd ℝ ℝ E3)) q :=
  (hasFDerivAt_norm_of_ne_zero hq).comp q hasFDerivAt_snd

/-- The derivative of the spherical phase: `dψ(w) = w⁰ − ⟨x, 𝐰⟩/|x|`. -/
theorem fderiv_sphericalPhase_apply {q : ℝ × E3} (hq : q.2 ≠ 0) (w : ℝ × E3) :
    fderiv ℝ sphericalPhase q w = w.1 - ‖q.2‖⁻¹ * inner ℝ q.2 w.2 := by
  have h := hasFDerivAt_fst.fun_sub (hasFDerivAt_norm_snd hq)
  rw [show sphericalPhase = fun p : ℝ × E3 => p.1 - ‖p.2‖ from rfl, h.fderiv]
  simp

/-- The derivative of the spherical amplitude: `d(1/|x|)(w) = −⟨x, 𝐰⟩/|x|³`. -/
theorem fderiv_sphericalAmplitude_apply {q : ℝ × E3} (hq : q.2 ≠ 0) (w : ℝ × E3) :
    fderiv ℝ sphericalAmplitude q w = -((‖q.2‖ ^ 3)⁻¹ * inner ℝ q.2 w.2) := by
  have hr : ‖q.2‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have h := (hasDerivAt_inv hr).comp_hasFDerivAt q (hasFDerivAt_norm_snd hq)
  rw [show sphericalAmplitude = (fun x : ℝ => x⁻¹) ∘ fun p : ℝ × E3 => ‖p.2‖ from rfl,
    h.fderiv]
  simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    innerSL_apply_apply, smul_eq_mul, ContinuousLinearMap.coe_snd']
  field_simp

/-- `∂ₜ(t − r) = 1`. -/
theorem timeDeriv_sphericalPhase {q : ℝ × E3} (hq : q.2 ≠ 0) : timeDeriv sphericalPhase q = 1 := by
  rw [timeDeriv, fderiv_sphericalPhase_apply hq]
  simp

/-- `∂ᵢ(t − r) = −xᵢ/r`. -/
theorem spaceDeriv_sphericalPhase {q : ℝ × E3} (hq : q.2 ≠ 0) (i : Fin 3) :
    spaceDeriv i sphericalPhase q = -(sphericalAmplitude q * q.2 i) := by
  rw [spaceDeriv, fderiv_sphericalPhase_apply hq, EuclideanSpace.inner_single_right,
    sphericalAmplitude]
  simp

/-- `∂ₜ(1/r) = 0`. -/
theorem timeDeriv_sphericalAmplitude {q : ℝ × E3} (hq : q.2 ≠ 0) :
    timeDeriv sphericalAmplitude q = 0 := by
  rw [timeDeriv, fderiv_sphericalAmplitude_apply hq]
  simp

/-- `∂ᵢ(1/r) = −xᵢ/r³`. -/
theorem spaceDeriv_sphericalAmplitude {q : ℝ × E3} (hq : q.2 ≠ 0) (i : Fin 3) :
    spaceDeriv i sphericalAmplitude q = -((‖q.2‖ ^ 3)⁻¹ * q.2 i) := by
  rw [spaceDeriv, fderiv_sphericalAmplitude_apply hq, EuclideanSpace.inner_single_right]
  simp

/-- The complement of the world line of the origin is open. -/
theorem isOpen_ne_zero_snd : IsOpen {q : ℝ × E3 | q.2 ≠ 0} :=
  isOpen_ne_fun continuous_snd continuous_const

/-- The spherical phase is smooth away from the origin. -/
theorem contDiffAt_sphericalPhase {n : ℕ∞ω} {q : ℝ × E3} (hq : q.2 ≠ 0) :
    ContDiffAt ℝ n sphericalPhase q :=
  contDiffAt_fst.sub ((contDiffAt_norm ℝ hq).comp q contDiffAt_snd)

/-- The spherical amplitude is smooth away from the origin. -/
theorem contDiffAt_sphericalAmplitude {n : ℕ∞ω} {q : ℝ × E3} (hq : q.2 ≠ 0) :
    ContDiffAt ℝ n sphericalAmplitude q :=
  ((contDiffAt_norm ℝ hq).comp q contDiffAt_snd).inv (norm_ne_zero_iff.mpr hq)

/-- `x₁² + x₂² + x₃² = |x|²`. -/
theorem sum_sq_snd (q : ℝ × E3) : q.2 0 ^ 2 + q.2 1 ^ 2 + q.2 2 ^ 2 = ‖q.2‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

/-- The spherical phase satisfies the eikonal equation away from the origin. -/
theorem wavePairing_sphericalPhase {q : ℝ × E3} (hq : q.2 ≠ 0) :
    wavePairing sphericalPhase sphericalPhase q = 0 := by
  have hr : ‖q.2‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  simp only [wavePairing, timeDeriv_sphericalPhase hq, spaceDeriv_sphericalPhase hq,
    sphericalAmplitude, Fin.sum_univ_three]
  have h := sum_sq_snd q
  field_simp
  linear_combination -h

/-- `□(t − r) = 2/r` away from the origin. -/
theorem waveOperator_sphericalPhase {q : ℝ × E3} (hq : q.2 ≠ 0) :
    waveOperator sphericalPhase q = 2 * sphericalAmplitude q := by
  have hU : {p : ℝ × E3 | p.2 ≠ 0} ∈ 𝓝 q := isOpen_ne_zero_snd.mem_nhds hq
  have ht : timeDeriv sphericalPhase =ᶠ[𝓝 q] fun _ => 1 :=
    eventually_of_mem hU fun p hp => timeDeriv_sphericalPhase hp
  have hs : ∀ i, spaceDeriv i sphericalPhase =ᶠ[𝓝 q]
      fun p => -(sphericalAmplitude p * p.2 i) := fun i =>
    eventually_of_mem hU fun p hp => spaceDeriv_sphericalPhase hp i
  have htt : timeDeriv (timeDeriv sphericalPhase) q = 0 := by
    rw [timeDeriv, ht.fderiv_eq, fderiv_const_apply, zero_apply]
  have hss : ∀ i, spaceDeriv i (spaceDeriv i sphericalPhase) q =
      -(-((‖q.2‖ ^ 3)⁻¹ * q.2 i) * q.2 i + sphericalAmplitude q) := fun i => by
    have hA := (contDiffAt_sphericalAmplitude (n := 1) hq).differentiableAt (by simp)
    have hP : HasFDerivAt (fun p : ℝ × E3 => p.2 i)
        ((EuclideanSpace.proj i : E3 →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ E3)) q :=
      ((EuclideanSpace.proj i : E3 →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ E3)).hasFDerivAt
    have H := (hA.hasFDerivAt.fun_mul hP).fun_neg
    rw [spaceDeriv, (hs i).fderiv_eq, H.fderiv]
    simp only [neg_apply, add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearMap.coe_snd']
    rw [show fderiv ℝ sphericalAmplitude q (0, EuclideanSpace.single i 1) =
      spaceDeriv i sphericalAmplitude q from rfl, spaceDeriv_sphericalAmplitude hq]
    simp
    ring
  have hr : ‖q.2‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have h := sum_sq_snd q
  rw [waveOperator, htt, Finset.sum_congr rfl fun i _ => hss i]
  simp only [sphericalAmplitude, Fin.sum_univ_three]
  field_simp
  linear_combination -h

/-- The amplitude `1/r` satisfies the transport equation of the spherical phase away from the
origin: `2⟨d(1/r), d(t − r)⟩ + (1/r) □(t − r) = −2/r² + 2/r² = 0`. -/
theorem transport_sphericalAmplitude {q : ℝ × E3} (hq : q.2 ≠ 0) :
    transport sphericalAmplitude sphericalPhase q = 0 := by
  have hr : ‖q.2‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have h := sum_sq_snd q
  simp only [transport, wavePairing, waveOperator_sphericalPhase hq, timeDeriv_sphericalPhase hq,
    timeDeriv_sphericalAmplitude hq, spaceDeriv_sphericalPhase hq,
    spaceDeriv_sphericalAmplitude hq, sphericalAmplitude, Fin.sum_univ_three]
  field_simp
  linear_combination (-2 : ℝ) * h

/-! ### Instances -/

/-- A plane wave `A_μ = α_μ cos(ψ/ε) + β_μ sin(ψ/ε)` along the first axis, `ψ = t − x₁`, with
constant amplitudes. -/
def planeWavePotential (α β : Fin 4 → ℝ) (ε : ℝ) : Potential :=
  highFrequencyPotential (fun μ _ => α μ) (fun μ _ => β μ) planePhase ε

/-- `η(dψ, α) = −α₀ − α₁` for the plane phase. -/
theorem amplitudePairing_planePhase (α : Fin 4 → ℝ) (q : ℝ × E3) :
    amplitudePairing (fun μ _ => α μ) planePhase q = -(α 0 + α 1) := by
  simp only [amplitudePairing, timeDeriv_planePhase, spaceDeriv_planePhase, Fin.sum_univ_three]
  simp
  ring

/-- Constant amplitudes have zero divergence. -/
theorem amplitudeDivergence_const (α : Fin 4 → ℝ) (q : ℝ × E3) :
    amplitudeDivergence (fun μ _ => α μ) q = 0 := by
  simp only [amplitudeDivergence, timeDeriv_const, spaceDeriv_const, Finset.sum_const_zero,
    neg_zero, add_zero]

/-- A transverse plane wave, `α₀ + α₁ = β₀ + β₁ = 0`, is in the gauge of Lorenz. -/
theorem lorenzDivergence_planeWavePotential {α β : Fin 4 → ℝ} (hα : α 0 + α 1 = 0)
    (hβ : β 0 + β 1 = 0) (ε : ℝ) (v : Spacetime) :
    lorenzDivergence (planeWavePotential α β ε) v = 0 := by
  rw [planeWavePotential, lorenzDivergence_highFrequencyPotential
    (fun μ => differentiableAt_const _) (fun μ => differentiableAt_const _)
    planePhase.differentiableAt]
  simp only [amplitudePairing_planePhase, amplitudeDivergence_const, hα, hβ, trigValue]
  ring

/-- The plane wave solves the eikonal and the transport equations: the coefficients of `ε⁻²` and
of `ε⁻¹` in `box A_μ` vanish everywhere. -/
theorem leadingOrders_planeWave (α β : Fin 4 → ℝ) :
    ∀ q ∈ (univ : Set (ℝ × E3)), ∀ μ, leadingCoeff (fun μ _ => α μ) (fun μ _ => β μ)
      planePhase μ q = 0 ∧ subleadingCoeff (fun μ _ => α μ) (fun μ _ => β μ) planePhase μ q = 0 :=
  fun q _ μ => by
    simp [leadingCoeff, subleadingCoeff, wavePairing_planePhase, transport_const,
      waveOperator_clm]

/-- **A transverse plane wave solves the vacuum equations of Maxwell**, through
`maxwell_highFrequencyPotential_iff_of_eikonal`, for every `ε ≠ 0`. -/
theorem maxwell_planeWavePotential {α β : Fin 4 → ℝ} (hα : α 0 + α 1 = 0) (hβ : β 0 + β 1 = 0)
    {ε : ℝ} (hε : ε ≠ 0) :
    ∀ y ∈ (univ : Set Spacetime),
      (divergence3 (magneticField (fieldTensor (planeWavePotential α β ε))) y = 0 ∧
        ∀ i, partialAt (magneticField (fieldTensor (planeWavePotential α β ε)) i) 0 y +
          curl (electricField (fieldTensor (planeWavePotential α β ε))) y i = 0) ∧
      (divergence3 (electricField (fieldTensor (planeWavePotential α β ε))) y = 0 ∧
        ∀ i, curl (magneticField (fieldTensor (planeWavePotential α β ε))) y i -
          partialAt (electricField (fieldTensor (planeWavePotential α β ε)) i) 0 y = 0) := by
  have hc : ∀ (c : ℝ) (q : ℝ × E3), ContDiffAt ℝ 2 (fun _ : ℝ × E3 => c) q := fun c q =>
    contDiffAt_const
  refine (maxwell_highFrequencyPotential_iff_of_eikonal isOpen_univ
    (fun v _ μ => hc (α μ) _) (fun v _ μ => hc (β μ) _)
    (fun v _ => planePhase.contDiff.contDiffAt) hε
    (fun v _ => lorenzDivergence_planeWavePotential hα hβ ε v)
    (fun v _ => wavePairing_planePhase _)
    (fun v _ μ => ⟨by rw [transport_const, waveOperator_clm, mul_zero],
      by rw [transport_const, waveOperator_clm, mul_zero]⟩)).mpr fun v _ μ => ?_
  simp [waveOperator_const]

/-- An instance of `box_eq_zerothOrder_iff`: the transverse plane wave of polarization `e₂` at the
event `(1, 0)`, where the phase is `1`, has `box A_μ = R₀` for every `ε ≠ 0`. -/
theorem box_planeWave_eq_zerothOrder :
    ∀ ε : ℝ, ε ≠ 0 → ∀ μ, box (potentialComponent (highFrequencyPotential
        (fun μ _ => (Pi.single 2 1 : Fin 4 → ℝ) μ) (fun _ _ => 0) planePhase ε) μ)
        (Pi.single 0 1) =
      trigValue (zerothCoeff (fun μ _ => (Pi.single 2 1 : Fin 4 → ℝ) μ) (fun _ _ => 0) μ
        (timeSpaceEquiv (Pi.single 0 1))) (planePhase (timeSpaceEquiv (Pi.single 0 1)) / ε) := by
  have hq : timeSpaceEquiv (Pi.single 0 1 : Spacetime) = ((1 : ℝ), (0 : E3)) :=
    timeSpaceEquiv_single_zero
  refine (box_eq_zerothOrder_iff (fun μ => contDiffAt_const) (fun μ => contDiffAt_const)
    planePhase.contDiff.contDiffAt (by rw [hq]; simp [planePhase])
    ⟨2, by simp⟩).mpr ⟨wavePairing_planePhase _, fun μ => ⟨?_, ?_⟩⟩ <;>
    rw [transport_const, waveOperator_clm, mul_zero]

/-- **The rays of the plane wave** are the lightlike lines `s ↦ (s, s e₁)`. -/
theorem lightlike_planeRay {s₀ s₁ : ℝ} :
    ∀ s ∈ Icc s₀ s₁, raisedGradient planePhase (planeRay s) =
        raisedGradient planePhase (planeRay s₀) ∧
      Lightlike (timeSpaceEquiv.symm (raisedGradient planePhase (planeRay s))) :=
  lightlike_of_isRay isOpen_univ (fun q _ => planePhase.contDiff.contDiffAt)
    (fun q _ => wavePairing_planePhase q) (fun s _ => mem_univ _)
    (fun s _ => hasDerivAt_planeRay s) (by simp [raisedGradient_planePhase])

/-- The intensity current of the outgoing spherical wave `cos(ψ/ε)/r`, `ψ = t − r`, is conserved
away from the origin. -/
theorem divergence_intensityCurrent_spherical {q : ℝ × E3} (hq : q.2 ≠ 0) :
    currentDivergence (intensityDensity sphericalAmplitude (fun _ => 0) sphericalPhase)
      (intensityFlux sphericalAmplitude (fun _ => 0) sphericalPhase) q = 0 :=
  divergence_intensityCurrent_eq_zero
    ((contDiffAt_sphericalAmplitude (n := 1) hq).differentiableAt (by simp))
    (differentiableAt_const _) (contDiffAt_sphericalPhase hq) (transport_sphericalAmplitude hq)
    (by rw [transport_const, zero_mul])

/-- The radial ray `s ↦ (s, (s + 1) n)` of the spherical wave, for a unit vector `n`. -/
def sphericalRay (n : E3) (s : ℝ) : ℝ × E3 := (s, (s + 1) • n)

/-- The radial rays of the spherical wave stay away from the origin for `s > −1`. -/
theorem sphericalRay_snd_ne_zero {n : E3} (hn : ‖n‖ = 1) {s : ℝ} (hs : -1 < s) :
    (sphericalRay n s).2 ≠ 0 := by
  simp only [sphericalRay, ne_eq, smul_eq_zero, not_or]
  exact ⟨by linarith, fun h => by simp [h] at hn⟩

/-- On the radial ray the wave vector of the spherical phase is `(1, n)`. -/
theorem raisedGradient_sphericalRay {n : E3} (hn : ‖n‖ = 1) {s : ℝ} (hs : -1 < s) :
    raisedGradient sphericalPhase (sphericalRay n s) = (1, n) := by
  have hq := sphericalRay_snd_ne_zero hn hs
  have h1 : s + 1 ≠ 0 := by linarith
  have hnorm : ‖(sphericalRay n s).2‖ = s + 1 := by
    simp only [sphericalRay, norm_smul, hn, mul_one, Real.norm_eq_abs]
    exact abs_of_pos (by linarith)
  simp only [raisedGradient, timeDeriv_sphericalPhase hq, spaceDeriv_sphericalPhase hq, neg_neg,
    sphericalAmplitude, hnorm]
  congr 1
  ext i
  simp only [sphericalRay, PiLp.smul_apply, smul_eq_mul]
  field_simp

/-- The velocity of `sphericalRay` is the wave vector of the spherical phase. -/
theorem hasDerivAt_sphericalRay {n : E3} (hn : ‖n‖ = 1) {s : ℝ} (hs : -1 < s) :
    HasDerivAt (sphericalRay n) (raisedGradient sphericalPhase (sphericalRay n s)) s := by
  have h := ((hasDerivAt_id s).add_const (1 : ℝ)).smul_const n
  rw [one_smul] at h
  rw [raisedGradient_sphericalRay hn hs]
  exact (hasDerivAt_id s).prodMk h

/-- **The rays of the spherical wave** are the radial lightlike lines. -/
theorem lightlike_sphericalRay {n : E3} (hn : ‖n‖ = 1) {s₀ s₁ : ℝ} (hs₀ : -1 < s₀) :
    ∀ s ∈ Icc s₀ s₁, raisedGradient sphericalPhase (sphericalRay n s) =
        raisedGradient sphericalPhase (sphericalRay n s₀) ∧
      Lightlike (timeSpaceEquiv.symm (raisedGradient sphericalPhase (sphericalRay n s))) :=
  lightlike_of_isRay isOpen_ne_zero_snd (fun q hq => contDiffAt_sphericalPhase hq)
    (fun q hq => wavePairing_sphericalPhase hq)
    (fun s hs => sphericalRay_snd_ne_zero hn (by linarith [hs.1]))
    (fun s hs => hasDerivAt_sphericalRay hn (by linarith [hs.1]))
    (by rw [raisedGradient_sphericalRay hn hs₀]; simp)

/-- **The transport along the radial rays**: the amplitude `1/r` of the spherical wave changes
along a ray by `d/ds a = −½ a □ψ = −1/r²`. -/
theorem hasDerivAt_sphericalAmplitude_ray {n : E3} (hn : ‖n‖ = 1) {s : ℝ} (hs : -1 < s) :
    HasDerivAt (fun r => sphericalAmplitude (sphericalRay n r))
      (-(sphericalAmplitude (sphericalRay n s) *
        waveOperator sphericalPhase (sphericalRay n s)) / 2) s :=
  hasDerivAt_comp_ray_of_transport
    ((contDiffAt_sphericalAmplitude (n := 1) (sphericalRay_snd_ne_zero hn hs)).differentiableAt
      (by simp))
    (hasDerivAt_sphericalRay hn hs) (transport_sphericalAmplitude (sphericalRay_snd_ne_zero hn hs))

/-- The flow `Φ(t, x) = eᵗ x` of the radial field `X(x) = x = ∇(|x|²/2)`. -/
theorem isLocalFlowOn_radial :
    IsLocalFlowOn (fun x : E3 => x) (fun p : ℝ × E3 => Real.exp p.1 • p.2) univ where
  isOpen := isOpen_univ
  contDiffAt _ _ := ((Real.contDiff_exp.comp contDiff_fst).smul contDiff_snd).contDiffAt
  hasDerivAt p _ := (Real.hasDerivAt_exp p.1).smul_const p.2
  segment _ _ _ _ := mem_univ _
  initial p _ := by simp

/-- `div (|x|⁻³ x) = 0` away from the origin. -/
theorem traceCLM_fderiv_radial {y : E3} (hy : y ≠ 0) :
    traceCLM (fderiv ℝ (fun z : E3 => (‖z‖ ^ 3)⁻¹ • z) y) = 0 := by
  have hr : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hN := hasFDerivAt_norm_of_ne_zero hy
  have hI : HasFDerivAt (fun z : E3 => (‖z‖ ^ 3)⁻¹) _ y :=
    (hasDerivAt_inv (pow_ne_zero 3 hr)).comp_hasFDerivAt y (hN.pow 3)
  have key := traceCLM_fderiv_smul hI.differentiableAt (differentiableAt_fun_id (x := y))
  rw [key, hI.fderiv, fderiv_fun_id, traceCLM_apply]
  simp only [ContinuousLinearMap.coe_id, LinearMap.trace_id, finrank_euclideanSpace_fin,
    smul_apply, smul_eq_mul, innerSL_apply_apply, real_inner_self_eq_norm_sq]
  field_simp
  ring

/-- **The intensity of the radial field** (an instance of `intensity_mul_det_eq`): the flux
`|x|⁻³ x` of the inverse-square law along the flow `eᵗ x`,
`|eᵗ x|⁻³ det (eᵗ id) = |x|⁻³`. -/
theorem intensity_mul_det_radial (t : ℝ) {x : E3} (hx : x ≠ 0) :
    (‖Real.exp t • x‖ ^ 3)⁻¹ *
        LinearMap.det (fderiv ℝ (fun y : E3 => Real.exp t • y) x : E3 →ₗ[ℝ] E3) =
      (‖x‖ ^ 3)⁻¹ := by
  have hd : ∀ y : E3, y ≠ 0 → DifferentiableAt ℝ (fun z : E3 => (‖z‖ ^ 3)⁻¹) y := fun y hy =>
    ((hasDerivAt_inv (pow_ne_zero 3 (norm_ne_zero_iff.mpr hy))).comp_hasFDerivAt y
      ((hasFDerivAt_norm_of_ne_zero hy).pow 3)).differentiableAt
  exact intensity_mul_det_eq (U := {y : E3 | y ≠ 0}) (I := fun z : E3 => (‖z‖ ^ 3)⁻¹)
    isLocalFlowOn_radial contDiff_id (fun y hy => hd y hy) (fun y hy => traceCLM_fderiv_radial hy)
    (mem_univ _) fun s _ => smul_ne_zero (Real.exp_pos s).ne' hx

end ProjectAinos.Electrodynamics.Optics.Eikonal
