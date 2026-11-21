/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.Electrodynamics.Scattering.HighFrequency

/-! Public consumers of the scattering of waves by charges (Landau–Lifshitz §§78–80): the motion of
a charge in a wave and its weak-wave expansion, the incident plane wave and its flux, Thomson's
cross section with its angular distribution, the bound charge and Rayleigh's law, the average over
orientations of a polarizability, the free-charge limit at high frequencies and the incoherence of
the scattering by several charges at short wavelengths. Default elaborator options are
intentional: these checks must not rely on the implementation's transparency settings. Every
statement is pinned with its type. -/

noncomputable section

section Thomson

namespace ProjectAinos.Electrodynamics.Scattering.Thomson

open MeasureTheory Set Metric Real Filter
open scoped Topology

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Sphere SmoothGeometry.DifferentialForm
  SpecialRelativity Radiation.Relativistic NonlinearODE InnerProductGeometry

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (u v : E3) :
    ‖cross u v‖ ≤ ‖u‖ * ‖v‖ :=
  norm_cross_le u v

example :
    IsBoundedBilinearMap ℝ fun p : E3 × E3 => cross p.1 p.2 :=
  isBoundedBilinearMap_cross

example {n : WithTop ℕ∞} :
    ContDiff ℝ n fun p : E3 × E3 => cross p.1 p.2 :=
  contDiff_cross

example (k : ℝ) (E B : ℝ → E3 → E3) (x v : ℝ → E3) :
    Prop :=
  IsTrajectory k E B x v

example (k : ℝ) (E B : ℝ → E3 → E3) (z : ℝ × E3 × E3) :
    ℝ × E3 × E3 :=
  motionField k E B z

open scoped ContDiff in
example (k : ℝ) {E B : ℝ → E3 → E3} (hE : ContDiff ℝ ∞ fun p : ℝ × E3 => E p.1 p.2)
    (hB : ContDiff ℝ ∞ fun p : ℝ × E3 => B p.1 p.2) :
    ContDiff ℝ ∞ (motionField k E B) :=
  contDiff_motionField k hE hB

example (k : ℝ) {E B : ℝ → E3 → E3} {ME MB : ℝ} (hEb : ∀ t x, ‖E t x‖ ≤ ME)
    (hBb : ∀ t x, ‖B t x‖ ≤ MB) (z : ℝ × E3 × E3) :
    ‖motionField k E B z‖ ≤ (1 + |k| * ME) + (1 + |k| * MB) * ‖z‖ :=
  norm_motionField_le k hEb hBb z

open scoped ContDiff in
example (k : ℝ) {E B : ℝ → E3 → E3} (hE : ContDiff ℝ ∞ fun p : ℝ × E3 => E p.1 p.2)
    (hB : ContDiff ℝ ∞ fun p : ℝ × E3 => B p.1 p.2) {ME MB : ℝ} (hEb : ∀ t x, ‖E t x‖ ≤ ME)
    (hBb : ∀ t x, ‖B t x‖ ≤ MB) (x₀ v₀ : E3) :
    ∃ x v : ℝ → E3, x 0 = x₀ ∧ v 0 = v₀ ∧ IsTrajectory k E B x v :=
  exists_trajectory k hE hB hEb hBb x₀ v₀

example (k : ℝ) (F : Spacetime → Spacetime →L[ℝ] Spacetime) (x u : ℝ → Spacetime) :
    Prop :=
  IsProperTimeTrajectory k F x u

open scoped ContDiff in
example (k : ℝ) {F : Spacetime → Spacetime →L[ℝ] Spacetime} (hF : ContDiff ℝ ∞ F) {M : ℝ}
    (hM : ∀ x, ‖F x‖ ≤ M) (x₀ u₀ : Spacetime) :
    ∃ x u : ℝ → Spacetime, x 0 = x₀ ∧ u 0 = u₀ ∧ IsProperTimeTrajectory k F x u :=
  exists_properTimeTrajectory k hF hM x₀ u₀

example (k : ℝ) (ℓ : FourCovector) (F₀ : Spacetime →L[ℝ] Spacetime) (x₀ u₀ : Spacetime) :
    ∃ x u : ℝ → Spacetime, x 0 = x₀ ∧ u 0 = u₀ ∧
      IsProperTimeTrajectory k (fun y => Real.cos (ℓ y) • F₀) x u :=
  exists_properTimeTrajectory_planeWave k ℓ F₀ x₀ u₀

example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f f' : ℝ → F} {K ε T : ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) (h0 : f 0 = 0) (hb : ∀ t ∈ Icc 0 T, ‖f' t‖ ≤ K * ‖f t‖ + ε) :
    ∀ t ∈ Icc 0 T, ‖f t‖ ≤ gronwallBound 0 K ε t :=
  norm_le_gronwallBound_of_hasDerivAt hf h0 hb

example (K c ε x : ℝ) :
    gronwallBound 0 K (c * ε) x = c * gronwallBound 0 K ε x :=
  gronwallBound_zero_mul K c ε x

example {K ε t : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    0 ≤ gronwallBound 0 K ε t :=
  gronwallBound_zero_nonneg hK hε ht

example (k : ℝ) {E B : ℝ → E3 → E3} {ME MB L T : ℝ} (hEb : ∀ t x, ‖E t x‖ ≤ ME)
    (hBb : ∀ t x, ‖B t x‖ ≤ MB) (hL : ∀ t x y, ‖E t x - E t y‖ ≤ L * ‖x - y‖) (x₀ : E3)
    {ξ η : ℝ → E3} (hξ0 : ξ 0 = 0) (hη0 : η 0 = 0) (hξ : ∀ t, HasDerivAt ξ (η t) t)
    (hη : ∀ t, HasDerivAt η (k • E t x₀) t) :
    ∃ C, ∀ a : ℝ, |a| ≤ 1 → ∀ x v : ℝ → E3, x 0 = x₀ → v 0 = 0 →
      IsTrajectory k (fun t y => a • E t y) (fun t y => a • B t y) x v →
      ∀ t ∈ Icc 0 T, ‖x t - x₀ - a • ξ t‖ ≤ C * a ^ 2 ∧ ‖v t - a • η t‖ ≤ C * a ^ 2 :=
  norm_trajectory_sub_firstOrder_le k hEb hBb hL x₀ hξ0 hη0 hξ hη

example (ω : ℝ) (n E₀ : E3) (t : ℝ) (x : E3) :
    E3 :=
  waveElectric ω n E₀ t x

example (ω : ℝ) (n E₀ : E3) (t : ℝ) (x : E3) :
    E3 :=
  waveMagnetic ω n E₀ t x

example (ω : ℝ) (n E₀ : E3) :
    ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × E3 => waveElectric ω n E₀ p.1 p.2 :=
  contDiff_waveElectric ω n E₀

example (ω : ℝ) (n E₀ : E3) :
    ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × E3 => waveMagnetic ω n E₀ p.1 p.2 :=
  contDiff_waveMagnetic ω n E₀

example (ω : ℝ) (n E₀ : E3) (t : ℝ) (x : E3) :
    ‖waveElectric ω n E₀ t x‖ ≤ ‖E₀‖ :=
  norm_waveElectric_le ω n E₀ t x

example (ω : ℝ) {n : E3} (hn : ‖n‖ = 1) (E₀ : E3) (t : ℝ) (x : E3) :
    ‖waveMagnetic ω n E₀ t x‖ ≤ ‖E₀‖ :=
  norm_waveMagnetic_le ω hn E₀ t x

example (ω : ℝ) {n : E3} (hn : ‖n‖ = 1) (E₀ : E3) (t : ℝ) (x y : E3) :
    ‖waveElectric ω n E₀ t x - waveElectric ω n E₀ t y‖ ≤ |ω| * ‖E₀‖ * ‖x - y‖ :=
  norm_waveElectric_sub_le ω hn E₀ t x y

example (k ω : ℝ) (n E₀ x₀ : E3) (t : ℝ) :
    E3 :=
  firstOrderResponse k ω n E₀ x₀ t

example (k ω : ℝ) (n E₀ x₀ : E3) (t : ℝ) :
    E3 :=
  firstOrderVelocity k ω n E₀ x₀ t

example (k : ℝ) {ω : ℝ} (hω : ω ≠ 0) (n E₀ x₀ : E3) (t : ℝ) :
    HasDerivAt (firstOrderResponse k ω n E₀ x₀) (firstOrderVelocity k ω n E₀ x₀ t) t :=
  hasDerivAt_firstOrderResponse k hω n E₀ x₀ t

example (k : ℝ) {ω : ℝ} (hω : ω ≠ 0) (n E₀ x₀ : E3) (t : ℝ) :
    HasDerivAt (firstOrderVelocity k ω n E₀ x₀) (k • waveElectric ω n E₀ t x₀) t :=
  hasDerivAt_firstOrderVelocity k hω n E₀ x₀ t

example (k ω : ℝ) (n E₀ x₀ : E3) :
    firstOrderResponse k ω n E₀ x₀ 0 = 0 :=
  firstOrderResponse_zero k ω n E₀ x₀

example (k ω : ℝ) (n E₀ x₀ : E3) :
    firstOrderVelocity k ω n E₀ x₀ 0 = 0 :=
  firstOrderVelocity_zero k ω n E₀ x₀

example (k a ω : ℝ) {n : E3} (hn : ‖n‖ = 1) (E₀ x₀ v₀ : E3) :
    ∃ x v : ℝ → E3, x 0 = x₀ ∧ v 0 = v₀ ∧
      IsTrajectory k (fun t y => a • waveElectric ω n E₀ t y)
        (fun t y => a • waveMagnetic ω n E₀ t y) x v :=
  exists_trajectory_wave k a ω hn E₀ x₀ v₀

example (k : ℝ) {ω : ℝ} (hω : ω ≠ 0) {n : E3} (hn : ‖n‖ = 1) (E₀ x₀ : E3) (T : ℝ) :
    ∃ C, ∀ a : ℝ, |a| ≤ 1 → ∀ x v : ℝ → E3, x 0 = x₀ → v 0 = 0 →
      IsTrajectory k (fun t y => a • waveElectric ω n E₀ t y)
        (fun t y => a • waveMagnetic ω n E₀ t y) x v →
      ∀ t ∈ Icc 0 T, ‖x t - x₀ - a • firstOrderResponse k ω n E₀ x₀ t‖ ≤ C * a ^ 2 ∧
        ‖v t - a • firstOrderVelocity k ω n E₀ x₀ t‖ ≤ C * a ^ 2 :=
  norm_trajectory_sub_firstOrderResponse_le k hω hn E₀ x₀ T

example (ω : ℝ) (E₀ : E3) :
    FourCovector :=
  polarizationCovector ω E₀

example (ω : ℝ) (E₀ : E3) :
    polarizationCovector ω E₀ (Pi.single 0 1) = 0 :=
  polarizationCovector_single_zero ω E₀

example (ω : ℝ) (E₀ : E3) (i : Fin 3) :
    polarizationCovector ω E₀ (Pi.single i.succ 1) = -(ω⁻¹ * E₀ i) :=
  polarizationCovector_single_succ ω E₀ i

example (ω : ℝ) (n E₀ : E3) :
    Potential :=
  incidentPotential ω n E₀

example (ω : ℝ) (n : E3) (t : ℝ) (x : E3) :
    wavevector ω (WithLp.ofLp n) (Minkowski.vector t x) = ω * (t - inner ℝ n x) :=
  wavevector_vector ω n t x

example {ω : ℝ} (hω : ω ≠ 0) (n E₀ : E3) (t : ℝ) (x : E3) :
    electricVector (fieldTensor (incidentPotential ω n E₀) (Minkowski.vector t x)) =
      WithLp.ofLp (waveElectric ω n E₀ t x) :=
  electricVector_incidentPotential hω n E₀ t x

example {ω : ℝ} (hω : ω ≠ 0) {n E₀ : E3} (hn : ‖n‖ = 1) (hnE : inner ℝ n E₀ = 0) (t : ℝ) (x : E3) :
    magneticVector (fieldTensor (incidentPotential ω n E₀) (Minkowski.vector t x)) =
        WithLp.ofLp (waveMagnetic ω n E₀ t x) ∧
      ∑ i, poyntingVector (fieldTensor (incidentPotential ω n E₀)) i (Minkowski.vector t x) *
        n i = ‖waveElectric ω n E₀ t x‖ ^ 2 :=
  transverse_incidentPotential hω hn hnE t x

example (ω : ℝ) (f : ℝ → ℝ) :
    ℝ :=
  periodAverage ω f

example (ω c : ℝ) (f : ℝ → ℝ) :
    periodAverage ω (fun t => c * f t) = c * periodAverage ω f :=
  periodAverage_const_mul ω c f

example {ω : ℝ} (hω : ω ≠ 0) (φ : ℝ) :
    periodAverage ω (fun t => Real.cos (ω * t + φ) ^ 2) = 1 / 2 :=
  periodAverage_cos_sq hω φ

example (ω : ℝ) (n E₀ x₀ : E3) :
    ℝ :=
  incidentFlux ω n E₀ x₀

example {ω : ℝ} (hω : ω ≠ 0) {n E₀ : E3} (hn : ‖n‖ = 1) (hnE : inner ℝ n E₀ = 0) (x₀ : E3) :
    incidentFlux ω n E₀ x₀ = ‖E₀‖ ^ 2 / 2 :=
  incidentFlux_eq hω hn hnE x₀

example (e m : ℝ) :
    ℝ :=
  thomsonCrossSection e m

example (e ω : ℝ) (w : ℝ → E3) (S : ℝ) :
    ℝ :=
  crossSection e ω w S

example (e ω : ℝ) (w : ℝ → E3) (S : ℝ) (n : E3) :
    ℝ :=
  differentialCrossSection e ω w S n

example (e : ℝ) (a : E3) {n : E3} (hn : ‖n‖ = 1) :
    angularPower e 0 a n = e ^ 2 / (16 * π ^ 2) * (‖a‖ ^ 2 - inner ℝ n a ^ 2) :=
  angularPower_zero e a hn

example (e : ℝ) (a : E3) :
    ∫ n : sphere (0 : E3) 1, angularPower e 0 a n ∂sphereMeasure =
      2 / 3 * (e ^ 2 / (4 * π)) * ‖a‖ ^ 2 :=
  integral_angularPower_zero e a

example (e m : ℝ) {ω : ℝ} (hω : ω ≠ 0) {u E₀ : E3} (hu : ‖u‖ = 1) (huE : inner ℝ u E₀ = 0)
    (hE₀ : E₀ ≠ 0) (x₀ : E3) :
    crossSection e ω (fun t => (e / m) • waveElectric ω u E₀ t x₀) (incidentFlux ω u E₀ x₀) =
      thomsonCrossSection e m :=
  crossSection_eq e m hω hu huE hE₀ x₀

example (e m : ℝ) {ω : ℝ} (hω : ω ≠ 0) {u E₀ : E3} (hu : ‖u‖ = 1) (huE : inner ℝ u E₀ = 0)
    (hE₀ : E₀ ≠ 0) (x₀ : E3) {n : E3} (hn : ‖n‖ = 1) :
    differentialCrossSection e ω (fun t => (e / m) • waveElectric ω u E₀ t x₀)
        (incidentFlux ω u E₀ x₀) n =
      (e ^ 2 / (4 * π * m)) ^ 2 * (1 - inner ℝ n E₀ ^ 2 / ‖E₀‖ ^ 2) :=
  differentialCrossSection_eq_inner e m hω hu huE hE₀ x₀ hn

example (e m : ℝ) {ω : ℝ} (hω : ω ≠ 0) {u E₀ : E3} (hu : ‖u‖ = 1) (huE : inner ℝ u E₀ = 0)
    (hE₀ : E₀ ≠ 0) (x₀ : E3) {n : E3} (hn : ‖n‖ = 1) :
    differentialCrossSection e ω (fun t => (e / m) • waveElectric ω u E₀ t x₀)
        (incidentFlux ω u E₀ x₀) n =
      (e ^ 2 / (4 * π * m)) ^ 2 * Real.sin (angle n E₀) ^ 2 :=
  differentialCrossSection_eq e m hω hu huE hE₀ x₀ hn

example (e m : ℝ) {ω : ℝ} (hω : ω ≠ 0) {u E₀ : E3} (hu : ‖u‖ = 1) (huE : inner ℝ u E₀ = 0)
    (hE₀ : E₀ ≠ 0) (x₀ : E3) :
    ∫ n : sphere (0 : E3) 1, differentialCrossSection e ω
        (fun t => (e / m) • waveElectric ω u E₀ t x₀) (incidentFlux ω u E₀ x₀) n
        ∂sphereMeasure = thomsonCrossSection e m :=
  integral_differentialCrossSection e m hω hu huE hE₀ x₀

example {e₁ e₂ u n : E3} (h : Orthonormal ℝ ![e₁, e₂, u]) (hn : ‖n‖ = 1) :
    (Real.sin (angle n e₁) ^ 2 + Real.sin (angle n e₂) ^ 2) / 2 =
      (1 + Real.cos (angle n u) ^ 2) / 2 :=
  sin_sq_angle_add_sin_sq_angle h hn

example (e m : ℝ) {ω : ℝ} (hω : ω ≠ 0) {e₁ e₂ u : E3} (h : Orthonormal ℝ ![e₁, e₂, u]) (x₀ : E3)
    {n : E3} (hn : ‖n‖ = 1) :
    (differentialCrossSection e ω (fun t => (e / m) • waveElectric ω u e₁ t x₀)
        (incidentFlux ω u e₁ x₀) n +
      differentialCrossSection e ω (fun t => (e / m) • waveElectric ω u e₂ t x₀)
        (incidentFlux ω u e₂ x₀) n) / 2 =
      (e ^ 2 / (4 * π * m)) ^ 2 * ((1 + Real.cos (angle n u) ^ 2) / 2) :=
  differentialCrossSection_unpolarized e m hω h x₀ hn

example :
    Orthonormal ℝ ![EuclideanSpace.single (0 : Fin 3) (1 : ℝ), EuclideanSpace.single 1 1,
      EuclideanSpace.single 2 1] :=
  orthonormal_standardFrame

example (e m : ℝ) {ω : ℝ} (hω : ω ≠ 0) (x₀ : E3) :
    crossSection e ω (fun t => (e / m) • waveElectric ω (EuclideanSpace.single 2 1)
        (EuclideanSpace.single 0 1) t x₀)
      (incidentFlux ω (EuclideanSpace.single 2 1) (EuclideanSpace.single 0 1) x₀) =
      thomsonCrossSection e m :=
  crossSection_standardFrame e m hω x₀

end ProjectAinos.Electrodynamics.Scattering.Thomson

end Thomson

section LowFrequency

namespace ProjectAinos.Electrodynamics.Scattering.LowFrequency

open MeasureTheory Set Metric Real Filter
open scoped Topology

open SmoothGeometry SmoothGeometry.Sphere Thomson
open ProjectAinos.Mechanics (steadyCos steadySin responseDenominator)

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (γ ω₀ ω : ℝ) (f : E3) (t : ℝ) :
    E3 :=
  boundResponse γ ω₀ ω f t

example (γ ω₀ ω : ℝ) (f : E3) (t : ℝ) :
    E3 :=
  boundVelocity γ ω₀ ω f t

example (γ ω₀ ω : ℝ) (f : E3) (t : ℝ) :
    HasDerivAt (boundResponse γ ω₀ ω f) (boundVelocity γ ω₀ ω f t) t :=
  hasDerivAt_boundResponse γ ω₀ ω f t

example (γ ω₀ ω : ℝ) (f : E3) (t : ℝ) :
    HasDerivAt (boundVelocity γ ω₀ ω f) (-(ω ^ 2) • boundResponse γ ω₀ ω f t) t :=
  hasDerivAt_boundVelocity γ ω₀ ω f t

example {γ ω₀ ω : ℝ} (hD : responseDenominator γ ω₀ ω ≠ 0) (f : E3) (t : ℝ) :
    -(ω ^ 2) • boundResponse γ ω₀ ω f t = Real.cos (ω * t) • f -
      (2 * γ) • boundVelocity γ ω₀ ω f t - ω₀ ^ 2 • boundResponse γ ω₀ ω f t :=
  boundResponse_equation hD f t

example (γ ω₀ ω : ℝ) :
    steadyCos γ ω₀ 1 ω ^ 2 + steadySin γ ω₀ 1 ω ^ 2 = 1 / responseDenominator γ ω₀ ω :=
  steadyCos_sq_add_steadySin_sq γ ω₀ ω

example (e m γ ω₀ ω : ℝ) :
    ℝ :=
  oscillatorCrossSection e m γ ω₀ ω

example (e m γ ω₀ : ℝ) {ω : ℝ} (hω : ω ≠ 0) {u E₀ : E3} (hu : ‖u‖ = 1) (huE : inner ℝ u E₀ = 0)
    (hE₀ : E₀ ≠ 0) :
    crossSection e ω (fun t => -(ω ^ 2) • boundResponse γ ω₀ ω ((e / m) • E₀) t)
        (incidentFlux ω u E₀ 0) = oscillatorCrossSection e m γ ω₀ ω :=
  crossSection_oscillator e m γ ω₀ hω hu huE hE₀

example (γ ω₀ ω : ℝ) (f : E3) (t : ℝ) :
    HasDerivAt (fun t => -(ω ^ 2) • boundResponse γ ω₀ ω f t)
      (-(ω ^ 2) • boundVelocity γ ω₀ ω f t) t :=
  hasDerivAt_boundAcceleration γ ω₀ ω f t

example {τ ω₀ ω : ℝ} (hD : responseDenominator (τ * ω ^ 2 / 2) ω₀ ω ≠ 0) (f : E3) (t : ℝ) :
    -(ω ^ 2) • boundResponse (τ * ω ^ 2 / 2) ω₀ ω f t = Real.cos (ω * t) • f +
      τ • (-(ω ^ 2) • boundVelocity (τ * ω ^ 2 / 2) ω₀ ω f t) -
        ω₀ ^ 2 • boundResponse (τ * ω ^ 2 / 2) ω₀ ω f t :=
  boundResponse_radiationReaction hD f t

example (τ ω₀ ω : ℝ) :
    responseDenominator (τ * ω ^ 2 / 2) ω₀ ω = (ω₀ ^ 2 - ω ^ 2) ^ 2 + τ ^ 2 * ω ^ 6 :=
  responseDenominator_radiationReaction τ ω₀ ω

example {e m : ℝ} (he : e ≠ 0) (hm : m ≠ 0) {γ ω₀ ω : ℝ} (hω₀ : ω₀ ≠ 0) (hω : 4 * ω ^ 2 ≤ ω₀ ^ 2)
    (hγ : γ ^ 2 ≤ ω₀ ^ 2) :
    |oscillatorCrossSection e m γ ω₀ ω / thomsonCrossSection e m - (ω / ω₀) ^ 4| ≤
      12 * (ω / ω₀) ^ 6 :=
  abs_crossSection_sub_le he hm hω₀ hω hγ

example (ω : ℝ) (α : E3 →ₗ[ℝ] E3) (ê : E3) :
    ℝ :=
  polarizabilityCrossSection ω α ê

example {ω : ℝ} (hω : ω ≠ 0) {u E₀ : E3} (hu : ‖u‖ = 1) (huE : inner ℝ u E₀ = 0) (hE₀ : E₀ ≠ 0)
    (α : E3 →ₗ[ℝ] E3) :
    crossSection 1 ω (fun t => -(ω ^ 2) • α (waveElectric ω u E₀ t 0)) (incidentFlux ω u E₀ 0) =
      polarizabilityCrossSection ω α (‖E₀‖⁻¹ • E₀) :=
  crossSection_polarizable hω hu huE hE₀ α

example (α : E3 →ₗ[ℝ] E3) (hα : α.IsSymmetric) :
    (4 * π)⁻¹ * ∫ ê : sphere (0 : E3) 1, ‖α ê‖ ^ 2 ∂sphereMeasure =
      LinearMap.trace ℝ E3 (α ∘ₗ α) / 3 :=
  orientationAverage α hα

example (ω : ℝ) (α : E3 →ₗ[ℝ] E3) (hα : α.IsSymmetric) :
    (4 * π)⁻¹ * ∫ ê : sphere (0 : E3) 1, polarizabilityCrossSection ω α ê ∂sphereMeasure =
      2 / 3 * (1 / (4 * π)) * ω ^ 4 * (LinearMap.trace ℝ E3 (α ∘ₗ α) / 3) :=
  orientationAverage_polarizabilityCrossSection ω α hα

example (c : ℝ) :
    (c • LinearMap.id : E3 →ₗ[ℝ] E3).IsSymmetric :=
  isSymmetric_smul_id c

example (c : ℝ) :
    LinearMap.trace ℝ E3 ((c • LinearMap.id) ∘ₗ (c • LinearMap.id)) / 3 = c ^ 2 :=
  trace_smul_id_comp c

example (e m ω₀ ω : ℝ) {ê : E3} (hê : ‖ê‖ = 1) :
    polarizabilityCrossSection ω ((e ^ 2 / (m * ω₀ ^ 2)) • LinearMap.id) ê =
      thomsonCrossSection e m * (ω / ω₀) ^ 4 :=
  polarizabilityCrossSection_bound e m ω₀ ω hê

end ProjectAinos.Electrodynamics.Scattering.LowFrequency

end LowFrequency

section HighFrequency

namespace ProjectAinos.Electrodynamics.Scattering.HighFrequency

open MeasureTheory Set Metric Real Filter ProbabilityTheory
open scoped Topology RealInnerProductSpace

open SmoothGeometry Thomson LowFrequency
open ProjectAinos.Mechanics (responseDenominator)

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (e m : ℝ) {γ ω₀ ω : ℝ} (hω : ω ≠ 0) (h : 4 * ω₀ ^ 2 ≤ ω ^ 2) :
    |oscillatorCrossSection e m γ ω₀ ω - thomsonCrossSection e m| ≤
      thomsonCrossSection e m * (4 * (ω₀ ^ 2 + 2 * γ ^ 2) / ω ^ 2) :=
  abs_crossSection_sub_thomson_le e m hω h

example (e m γ ω₀ : ℝ) :
    Tendsto (fun ω => oscillatorCrossSection e m γ ω₀ ω) atTop (𝓝 (thomsonCrossSection e m)) :=
  crossSection_tendsto_thomson e m γ ω₀

example {ι : Type*} (s : Finset ι) (θ : ι → ℝ) :
    ‖∑ a ∈ s, Complex.exp (θ a * Complex.I)‖ ^ 2 =
      ∑ a ∈ s, ∑ b ∈ s, Real.cos (θ a - θ b) :=
  norm_sum_exp_sq s θ

example {N : ℕ} (P : Measure (Fin N → E3)) (q : E3) :
    ℝ :=
  coherentFactor P q

example {N : ℕ} (P : Measure (Fin N → E3)) :
    Prop :=
  HasPairDensities P

example (μ : Measure E3) [IsFiniteMeasure μ] (hμ : μ ≪ volume) :
    Tendsto (fun q : E3 => ∫ u, Real.cos ⟪q, u⟫ ∂μ) (cocompact E3) (𝓝 0) :=
  tendsto_integral_cos_inner μ hμ

example {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] {g : α → E3}
    (hg : Measurable g) (q : E3) :
    Integrable (fun x => Real.cos ⟪q, g x⟫) μ :=
  integrable_cos_inner μ hg q

example {N : ℕ} (P : Measure (Fin N → E3)) [IsFiniteMeasure P] (q : E3) :
    coherentFactor P q = ∑ a, ∑ b, ∫ r, Real.cos ⟪q, r a - r b⟫ ∂P :=
  coherentFactor_eq P q

example {N : ℕ} (P : Measure (Fin N → E3)) [IsProbabilityMeasure P] :
    coherentFactor P 0 = N ^ 2 :=
  coherentFactor_zero P

example {N : ℕ} (P : Measure (Fin N → E3)) [IsProbabilityMeasure P] (hP : HasPairDensities P) :
    Tendsto (coherentFactor P) (cocompact E3) (𝓝 N) :=
  tendsto_coherentFactor P hP

example {N : ℕ} {P : Measure (Fin N → E3)} (hP : P ≪ volume) :
    HasPairDensities P :=
  hasPairDensities_of_absolutelyContinuous hP

example (N : ℕ) :
    Measure (Fin N → E3) :=
  uniformConfiguration N

example (N : ℕ) :
    HasPairDensities (uniformConfiguration N) :=
  hasPairDensities_uniformConfiguration N

example (N : ℕ) :
    Tendsto (coherentFactor (uniformConfiguration N)) (cocompact E3) (𝓝 N) :=
  tendsto_coherentFactor_uniformConfiguration N

example (N : ℕ) : IsProbabilityMeasure (uniformConfiguration N) := inferInstance

end ProjectAinos.Electrodynamics.Scattering.HighFrequency

end HighFrequency
