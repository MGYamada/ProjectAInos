/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SpecialRelativity.MaximalProperTime
import ProjectAinos.SpecialRelativity.ObserverEnergy
import ProjectAinos.SpecialRelativity.NewtonianExpansion
import ProjectAinos.SpecialRelativity.SpatialLegendre

/-! Public consumers of the mechanics of a free relativistic particle: the reverse
Cauchy–Schwarz inequality on the future cone, the greatest proper time of the inertial clock,
the stationary curves of the free action as inertial motions with the Hessian in the velocity,
the energy and the momentum measured by an observer, the expansion in `1/c`, and the Legendre
transformation of the Lagrangian in the time of an observer.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section

open Set MeasureTheory Topology
open scoped ContDiff

namespace ProjectAinos.SmoothGeometry.Minkowski

variable {d : ℕ}

example {v w : MinkowskiModel d} (hv : FutureCausal v)
    (hw : FutureCausal w) : 0 ≤ pair v w :=
  pair_nonneg_of_futureCausal hv hw

example {v w : MinkowskiModel d} (hv : FutureCausal v)
    (hw : FutureCausal w) : intervalQuadratic v * intervalQuadratic w ≤ pair v w ^ 2 :=
  intervalQuadratic_mul_le_pair_sq hv hw

example {v w : MinkowskiModel d} (hv : FutureCausal v)
    (hw : FutureCausal w) :
    Real.sqrt (intervalQuadratic v) * Real.sqrt (intervalQuadratic w) ≤ pair v w :=
  sqrt_mul_sqrt_le_pair hv hw

example (v w : MinkowskiModel d) :
    intervalQuadratic (v + w) = intervalQuadratic v + 2 * pair v w + intervalQuadratic w :=
  intervalQuadratic_add v w

example {v w : MinkowskiModel d} (hv : FutureCausal v) (hw : FutureCausal w) :
    Real.sqrt (intervalQuadratic v) + Real.sqrt (intervalQuadratic w) ≤
      Real.sqrt (intervalQuadratic (v + w)) :=
  sqrt_add_sqrt_le hv hw

example (u : Observer d) (w : MinkowskiModel d) :
    intervalQuadratic w = u.clock w ^ 2 - u.restForm (u.project w) (u.project w) :=
  u.intervalQuadratic_eq w

example (u : Observer d) {w : MinkowskiModel d} (hw : FutureCausal w) :
    Real.sqrt (intervalQuadratic w) ≤ u.clock w :=
  u.sqrt_le_clock hw

example (u : Observer d) {w : MinkowskiModel d}
    (h : u.clock w = Real.sqrt (intervalQuadratic w)) (hw : 0 ≤ intervalQuadratic w) :
    w = u.clock w • u.velocity :=
  u.eq_smul_of_clock_eq_sqrt h hw

end ProjectAinos.SmoothGeometry.Minkowski

namespace ProjectAinos.SpecialRelativity

open SmoothGeometry SmoothGeometry.Minkowski Mechanics

section MaximalProperTime

variable {d : ℕ} {γ : ℝ → MinkowskiModel d} {a b : ℝ}

example {v : MinkowskiModel d} (hv : FutureTimelike v) : 0 < properSpeed v :=
  properSpeed_pos hv

example {v : MinkowskiModel d} (hv : FutureTimelike v) :
    properSpeed v • fourVelocity v = v :=
  properSpeed_smul_fourVelocity hv

example {v : MinkowskiModel d} (hv : FutureTimelike v) :
    (fourVelocityObserver v hv).clock v = properSpeed v :=
  clock_fourVelocityObserver hv

example (p w : MinkowskiModel d) (hab : a < b) :
    properTime (fun t : ℝ => p + ((t - a) / (b - a)) • w) a b = properSpeed w :=
  properTime_inertialSegment p w hab

example (γ : ℝ → MinkowskiModel d)
    (pieces : ℕ → ℝ → MinkowskiModel d) (s : ℕ → ℝ) (n : ℕ)
    (hs : ∀ i < n, s i < s (i + 1))
    (hseg : ∀ i < n, TimelikeSegment (pieces i) (s i) (s (i + 1)))
    (hmatch : ∀ i < n, pieces i (s i) = γ (s i) ∧ pieces i (s (i + 1)) = γ (s (i + 1))) :
    FutureCausal (γ (s n) - γ (s 0)) ∧
      ∑ i ∈ Finset.range n, properTime (pieces i) (s i) (s (i + 1)) ≤
        properSpeed (γ (s n) - γ (s 0)) :=
  sum_properTime_le_properSpeed γ pieces s n hs hseg hmatch

example (h : TimelikeSegment γ a b) : ContinuousOn (deriv γ) (uIcc a b) :=
  h.continuousOn_deriv

example (h : TimelikeSegment γ a b) : γ b - γ a = ∫ t in a..b, deriv γ t :=
  h.displacement_eq_integral

example (h : TimelikeSegment γ a b) (hab : a < b) : FutureTimelike (γ b - γ a) :=
  h.futureTimelike_displacement hab

example (h : TimelikeSegment γ a b) (hab : a < b) :
    properTime γ a b ≤ properSpeed (γ b - γ a) :=
  h.properTime_le_properSpeed hab

example (h : TimelikeSegment γ a b) (hab : a < b) :
    properTime γ a b = properSpeed (γ b - γ a) ↔
      ∀ t ∈ Icc a b, fourVelocity (deriv γ t) = fourVelocity (γ b - γ a) :=
  h.properTime_eq_properSpeed_iff hab

end MaximalProperTime

section FreeMotion

variable {m : ℝ} {γ : ℝ → Spacetime} {a b : ℝ}

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hcont : ContinuousOn f (Icc a b)) (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f 0 x)
    {x : ℝ} (hx : x ∈ Icc a b) : f x = f a :=
  eq_of_hasDerivAt_zero_Ioo hcont hderiv hx

example : IsOpen {v : Spacetime | Timelike v} :=
  isOpen_timelike

example (hγ : ContDiff ℝ 2 γ) {t : ℝ} (hv : Timelike (deriv γ t)) :
    ∀ᶠ s in 𝓝 t, Timelike (deriv γ s) :=
  eventually_timelike_deriv hγ hv

example (m : ℝ) {v : Spacetime} (hv : Timelike v) :
    DifferentiableAt ℝ (kineticMomentum m) v :=
  differentiableAt_kineticMomentum m hv

example (m : ℝ) (hγ : ContDiff ℝ 2 γ) {t : ℝ}
    (hv : Timelike (deriv γ t)) :
    DifferentiableAt ℝ (fun s => kineticMomentum m (deriv γ s)) t :=
  differentiableAt_kineticMomentum_deriv m hγ hv

example (hm : m ≠ 0) (v w : Spacetime) :
    kineticMomentum m v = kineticMomentum m w ↔ fourVelocity v = fourVelocity w :=
  kineticMomentum_eq_iff hm v w

example (m : ℝ) (hγ : ContDiff ℝ 2 γ) {t : ℝ} (hv : Timelike (deriv γ t)) :
    eulerLagrange (freeLagrangian m) γ t =
      -deriv (fun s => kineticMomentum m (deriv γ s)) t :=
  eulerLagrange_free m hγ hv

example (m : ℝ) (hab : a < b) (hγ : ContDiff ℝ 2 γ)
    (hv : ∀ t ∈ Icc a b, Timelike (deriv γ t)) :
    Stationary a b (freeLagrangian m) γ ↔
      ∀ t ∈ Ioo a b, deriv (fun s => kineticMomentum m (deriv γ s)) t = 0 :=
  free_stationary_iff_deriv_kineticMomentum m hab hγ hv

example (m : ℝ) (hab : a < b) (hγ : ContDiff ℝ 2 γ)
    (hv : ∀ t ∈ Icc a b, Timelike (deriv γ t)) :
    Stationary a b (freeLagrangian m) γ ↔
      ∀ t ∈ Icc a b, kineticMomentum m (deriv γ t) = kineticMomentum m (deriv γ a) :=
  free_stationary_iff_kineticMomentum_const m hab hγ hv

example (hm : m ≠ 0) (hab : a < b)
    (hγ : ContDiff ℝ 2 γ) (hv : ∀ t ∈ Icc a b, Timelike (deriv γ t)) :
    Stationary a b (freeLagrangian m) γ ↔
      ∀ t ∈ Icc a b, fourVelocity (deriv γ t) = fourVelocity (deriv γ a) :=
  free_stationary_iff_fourVelocity_const hm hab hγ hv

example {v : Spacetime} (hv : Timelike v) :
    properSpeed v • fourVelocity v = v :=
  properSpeed_smul_fourVelocity_of_timelike hv

example (hm : m ≠ 0) (hab : a < b) (hγ : ContDiff ℝ 2 γ)
    (hv : ∀ t ∈ Icc a b, Timelike (deriv γ t)) :
    Stationary a b (freeLagrangian m) γ ↔
      ∀ t ∈ Icc a b, γ t = γ a + properTime γ a t • fourVelocity (deriv γ a) :=
  free_stationary_iff_inertial hm hab hγ hv

example (hγ : ContDiff ℝ 2 γ) {t : ℝ} (hv : Timelike (deriv γ t)) :
    pair (fourVelocity (deriv γ t)) (deriv (fun s => fourVelocity (deriv γ s)) t) = 0 :=
  pair_fourVelocity_deriv hγ hv

example (m : ℝ) (v w : Spacetime) :
    velocityHessian m v w =
      (-m * (properSpeed v)⁻¹) • (pair w - ((intervalQuadratic v)⁻¹ * pair v w) • pair v) :=
  velocityHessian_apply m v w

example (m : ℝ) {v : Spacetime} (hv : Timelike v) :
    HasFDerivAt (kineticMomentum m) (velocityHessian m v) v :=
  hasFDerivAt_kineticMomentum m hv

example (m : ℝ) {v : Spacetime} (hv : Timelike v) :
    velocityHessian m v v = 0 :=
  velocityHessian_self m hv

example (hm : m ≠ 0) {v : Spacetime} (hv : Timelike v)
    (w : Spacetime) : velocityHessian m v w = 0 ↔ w ∈ Submodule.span ℝ {v} :=
  velocityHessian_eq_zero_iff hm hv w

example (hm : m ≠ 0) {v : Spacetime} (hv : Timelike v) :
    LinearMap.ker (velocityHessian m v).toLinearMap = Submodule.span ℝ {v} :=
  ker_velocityHessian hm hv

example (hm : m ≠ 0) {v : Spacetime} (hv : Timelike v) :
    Module.finrank ℝ (LinearMap.range (velocityHessian m v).toLinearMap) = 3 :=
  finrank_range_velocityHessian hm hv

end FreeMotion

section ObserverEnergy

variable {d : ℕ} (u : Observer d)

example (σ : LorentzConvention) (p : MinkowskiModel d) :
    observerEnergy u p = σ.timeSign * minkowskiForm σ d u.velocity p :=
  observerEnergy_convention u σ p

example (p : MinkowskiModel d) :
    observerEnergy u p • u.velocity + (observerMomentum u p : MinkowskiModel d) = p :=
  observerEnergy_smul_add_observerMomentum u p

example {p : MinkowskiModel d} (hp : FutureCausal p) :
    properSpeed p ≤ observerEnergy u p :=
  properSpeed_le_observerEnergy u hp

example {p : MinkowskiModel d} (hp : FutureTimelike p) :
    0 < observerEnergy u p :=
  observerEnergy_pos u hp

example (p : MinkowskiModel d) :
    observerEnergy u p ^ 2 =
      intervalQuadratic p + u.restForm (observerMomentum u p) (observerMomentum u p) :=
  observerEnergy_sq u p

example {p : MinkowskiModel d} {m : ℝ}
    (hp : intervalQuadratic p = m ^ 2) :
    observerEnergy u p ^ 2 =
      m ^ 2 + u.restForm (observerMomentum u p) (observerMomentum u p) :=
  observerEnergy_sq_of_mass u hp

example (m : ℝ) {v : MinkowskiModel d} (hv : Timelike v) :
    intervalQuadratic (m • fourVelocity v) = m ^ 2 :=
  intervalQuadratic_smul_fourVelocity m hv

example {p : MinkowskiModel d} (hE : observerEnergy u p ≠ 0) :
    u.restForm (observerVelocity u p) (observerVelocity u p) =
      1 - intervalQuadratic p / observerEnergy u p ^ 2 :=
  restForm_observerVelocity u hE

example {p : MinkowskiModel d} (hp : FutureTimelike p) :
    u.restForm (observerVelocity u p) (observerVelocity u p) < 1 :=
  restForm_observerVelocity_lt_one u hp

example (L : orthochronousLorentzGroup d) (p : MinkowskiModel d) :
    observerEnergy (u.transform L) (L.val.val p) = observerEnergy u p :=
  observerEnergy_transform u L p

example (L : orthochronousLorentzGroup d) (p : MinkowskiModel d) :
    (observerMomentum (u.transform L) (L.val.val p) : MinkowskiModel d) =
      L.val.val (observerMomentum u p : MinkowskiModel d) :=
  observerMomentum_transform u L p

example (u' : Observer d) (p : MinkowskiModel d) :
    observerEnergy u' p =
      observerEnergy u u'.velocity * observerEnergy u p -
        u.restForm (observerMomentum u u'.velocity) (observerMomentum u p) :=
  observerEnergy_change u u' p

end ObserverEnergy

end ProjectAinos.SpecialRelativity

namespace ProjectAinos.SpecialRelativity.Newtonian

variable {d : ℕ} {V c : ℝ} {v : Fin d → ℝ}

example {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 4) :
    0 ≤ 1 - x / 2 - Real.sqrt (1 - x) ∧ 1 - x / 2 - Real.sqrt (1 - x) ≤ x ^ 2 / 2 :=
  sqrt_one_sub_bounds h0 h1

example {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 4) :
    0 ≤ (Real.sqrt (1 - x))⁻¹ - 1 - x / 2 ∧ (Real.sqrt (1 - x))⁻¹ - 1 - x / 2 ≤ x ^ 2 / 2 :=
  inv_sqrt_one_sub_bounds h0 h1

example (c : ℝ) (v : Fin d → ℝ) : 0 ≤ betaSq c v :=
  betaSq_nonneg c v

example (c : ℝ) (hc : c ≠ 0) (v : Fin d → ℝ) :
    c ^ 2 * betaSq c v = ∑ i, v i ^ 2 :=
  betaSq_mul c hc v

example (hv : ∑ i, v i ^ 2 ≤ V ^ 2) :
    betaSq c v ≤ V ^ 2 / c ^ 2 :=
  betaSq_le_div hv

example (hV : 0 ≤ V) (hc : 0 < c) (hVc : 2 * V ≤ c)
    (hv : ∑ i, v i ^ 2 ≤ V ^ 2) : betaSq c v ≤ 1 / 4 :=
  betaSq_le_quarter hV hc hVc hv

example (hv : ∑ i, v i ^ 2 ≤ V ^ 2) :
    betaSq c v ^ 2 ≤ V ^ 4 / c ^ 4 :=
  betaSq_sq_le hv

example (m : ℝ) (hV : 0 ≤ V) (hc : 0 < c) (hVc : 2 * V ≤ c)
    (hv : ∑ i, v i ^ 2 ≤ V ^ 2) :
    |energy m c v - m * c ^ 2 - m / 2 * ∑ i, v i ^ 2| ≤ |m| * V ^ 4 / (2 * c ^ 2) :=
  abs_energy_sub_le m hV hc hVc hv

example (m : ℝ) (hV : 0 ≤ V) (hc : 0 < c) (hVc : 2 * V ≤ c)
    (hv : ∑ i, v i ^ 2 ≤ V ^ 2) :
    |lagrangian m c v + m * c ^ 2 - m / 2 * ∑ i, v i ^ 2| ≤ |m| * V ^ 4 / (2 * c ^ 2) :=
  abs_lagrangian_sub_le m hV hc hVc hv

example (hV : 0 ≤ V) (hv : ∑ i, v i ^ 2 ≤ V ^ 2) (i : Fin d) :
    |v i| ≤ V :=
  abs_le_of_sum_sq_le hV hv i

example (m : ℝ) (hV : 0 ≤ V) (hc : 0 < c) (hVc : 2 * V ≤ c)
    (hv : ∑ i, v i ^ 2 ≤ V ^ 2) (i : Fin d) :
    |momentum m c v i - m * v i| ≤ |m| * V ^ 3 / c ^ 2 :=
  abs_momentum_sub_le m hV hc hVc hv i

example (hV : 0 ≤ V) (hc : 0 < c) (hVc : 2 * V ≤ c)
    (hv : ∑ i, v i ^ 2 ≤ V ^ 2) :
    |clockRate c v - (1 - (∑ i, v i ^ 2) / (2 * c ^ 2))| ≤ V ^ 4 / (2 * c ^ 4) :=
  abs_clockRate_sub_le hV hc hVc hv

end ProjectAinos.SpecialRelativity.Newtonian

namespace ProjectAinos.SpecialRelativity.FreeParticle

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace Mechanics
open SmoothGeometry SmoothGeometry.Minkowski

variable {d : ℕ} {m : ℝ} {x : ℝ → Fin d → ℝ} {a b : ℝ}

example {v : Fin d → ℝ} (hv : ∑ i, v i ^ 2 < 1) :
    0 < Real.sqrt (1 - ∑ i, v i ^ 2) :=
  sqrt_one_sub_pos hv

example {v : Fin d → ℝ} (hv : ∑ i, v i ^ 2 < 1) : 0 < gamma v :=
  gamma_pos hv

example {v : Fin d → ℝ} (hv : ∑ i, v i ^ 2 < 1) :
    gamma v ^ 2 * (1 - ∑ i, v i ^ 2) = 1 :=
  gamma_sq_mul hv

example (hm : m ≠ 0) (p : Fin d → ℝ) :
    ∑ i, velocityOfMomentum m p i ^ 2 < 1 :=
  sum_sq_velocityOfMomentum_lt_one hm p

example (hm : 0 < m) {v : Fin d → ℝ} (hv : ∑ i, v i ^ 2 < 1) :
    relEnergy m (legendre m v) = m * gamma v :=
  relEnergy_legendre hm hv

example (hm : 0 < m) {v : Fin d → ℝ} (hv : ∑ i, v i ^ 2 < 1) :
    velocityOfMomentum m (legendre m v) = v :=
  velocityOfMomentum_legendre hm hv

example (hm : 0 < m) (p : Fin d → ℝ) :
    gamma (velocityOfMomentum m p) = relEnergy m p * m⁻¹ :=
  gamma_velocityOfMomentum hm p

example (hm : 0 < m) (p : Fin d → ℝ) :
    legendre m (velocityOfMomentum m p) = p :=
  legendre_velocityOfMomentum hm p

example (hm : 0 < m) {v w : Fin d → ℝ} (hv : ∑ i, v i ^ 2 < 1)
    (hw : ∑ i, w i ^ 2 < 1) : legendre m v = legendre m w ↔ v = w :=
  legendre_eq_iff hm hv hw

example (hm : 0 < m) {v : Fin d → ℝ} (hv : ∑ i, v i ^ 2 < 1) :
    ∑ i, legendre m v i * v i - -m * Real.sqrt (1 - ∑ i, v i ^ 2) =
      relEnergy m (legendre m v) :=
  energy_eq_relEnergy hm hv

example (a w : Fin d → ℝ) : dotCovector a w = ∑ i, a i * w i :=
  dotCovector_apply a w

example (r : ℝ) (a : Fin d → ℝ) : dotCovector (r • a) = r • dotCovector a :=
  dotCovector_smul r a

example : Function.Injective (dotCovector (d := d)) :=
  dotCovector_injective

example {n : ℕ∞ω} : ContDiff ℝ n fun v : Fin d → ℝ => ∑ i, v i ^ 2 :=
  contDiff_sum_sq

example : IsOpen {v : Fin d → ℝ | ∑ i, v i ^ 2 < 1} :=
  isOpen_ball

example : IsOpen (subluminalJets d) :=
  isOpen_subluminalJets

example (m : ℝ) :
    ContDiffOn ℝ 2 (Function.uncurry (lagrangian d m)) (subluminalJets d) :=
  lagrangian_contDiffOn m

example {v : Fin d → ℝ} (hv : ∑ i, v i ^ 2 < 1) :
    HasFDerivAt (fun w : Fin d → ℝ => Real.sqrt (1 - ∑ i, w i ^ 2))
      (-gamma v • dotCovector v) v :=
  hasFDerivAt_sqrt_one_sub hv

example (m : ℝ) {z : (Fin d → ℝ) × (Fin d → ℝ)}
    (hz : ∑ i, z.2 i ^ 2 < 1) (t : ℝ) :
    HasFDerivAt (lagrangian d m t)
      ((dotCovector (legendre m z.2)).comp
        (ContinuousLinearMap.snd ℝ (Fin d → ℝ) (Fin d → ℝ))) z :=
  hasFDerivAt_lagrangian m hz t

example (m : ℝ) {x : ℝ → Fin d → ℝ} {t : ℝ}
    (hv : ∑ i, deriv x t i ^ 2 < 1) : force (lagrangian d m) x t = 0 :=
  force_lagrangian m hv

example (m : ℝ) {x : ℝ → Fin d → ℝ} {t : ℝ}
    (hv : ∑ i, deriv x t i ^ 2 < 1) :
    momentum (lagrangian d m) x t = dotCovector (legendre m (deriv x t)) :=
  momentum_lagrangian m hv

example (hx : ContDiff ℝ 2 x) {t : ℝ} (hv : ∑ i, deriv x t i ^ 2 < 1) :
    ∀ᶠ s in 𝓝 t, ∑ i, deriv x s i ^ 2 < 1 :=
  eventually_subluminal hx hv

example {v : Fin d → ℝ} (hv : ∑ i, v i ^ 2 < 1) :
    DifferentiableAt ℝ (gamma (d := d)) v :=
  differentiableAt_gamma hv

example (m : ℝ) {v : Fin d → ℝ} (hv : ∑ i, v i ^ 2 < 1) :
    DifferentiableAt ℝ (legendre (d := d) m) v :=
  differentiableAt_legendre m hv

example (m : ℝ) (hx : ContDiff ℝ 2 x) {t : ℝ}
    (hv : ∑ i, deriv x t i ^ 2 < 1) :
    DifferentiableAt ℝ (fun s => dotCovector (legendre m (deriv x s))) t :=
  differentiableAt_dotCovector_legendre m hx hv

example (m : ℝ) (hx : ContDiff ℝ 2 x) {t : ℝ}
    (hv : ∑ i, deriv x t i ^ 2 < 1) :
    eulerLagrange (lagrangian d m) x t =
      -deriv (fun s => dotCovector (legendre m (deriv x s))) t :=
  eulerLagrange_lagrangian m hx hv

example (m : ℝ) (hab : a < b) (hx : ContDiff ℝ 2 x)
    (hv : ∀ t ∈ Icc a b, ∑ i, deriv x t i ^ 2 < 1) :
    Stationary a b (lagrangian d m) x ↔
      ∀ t ∈ Ioo a b, deriv (fun s => dotCovector (legendre m (deriv x s))) t = 0 :=
  stationary_iff_deriv_legendre m hab hx hv

example (m : ℝ) (hab : a < b) (hx : ContDiff ℝ 2 x)
    (hv : ∀ t ∈ Icc a b, ∑ i, deriv x t i ^ 2 < 1) :
    Stationary a b (lagrangian d m) x ↔
      ∀ t ∈ Icc a b, legendre m (deriv x t) = legendre m (deriv x a) :=
  stationary_iff_legendre_const m hab hx hv

example (hm : 0 < m) (hab : a < b) (hx : ContDiff ℝ 2 x)
    (hv : ∀ t ∈ Icc a b, ∑ i, deriv x t i ^ 2 < 1) :
    Stationary a b (lagrangian d m) x ↔ ∀ t ∈ Icc a b, deriv x t = deriv x a :=
  stationary_iff_deriv_const hm hab hx hv

example (hm : 0 < m) (c : Fin d ⊕ Fin d → TimeFunction) :
    IsTrajectory (canonical (Fin d)) (hamiltonian d m) c ↔
      ∀ t : ℝ,
        (∑ i, deriv (fun s => realCurve c s (Sum.inl i)) t ^ 2 < 1) ∧
        (fun i => realCurve c t (Sum.inr i)) =
          legendre m (fun i => deriv (fun s => realCurve c s (Sum.inl i)) t) ∧
        ∀ i, deriv (fun s => realCurve c s (Sum.inr i)) t = 0 :=
  isTrajectory_iff_legendre hm c

example (τ : ℝ) (w : Fin d → ℝ) :
    intervalQuadratic (Fin.cons τ w : MinkowskiModel d) = τ ^ 2 - ∑ i, w i ^ 2 :=
  intervalQuadratic_cons τ w

example {x : ℝ → Fin 3 → ℝ} {t : ℝ} (hx : DifferentiableAt ℝ x t) :
    HasDerivAt (graph x) (Fin.cons 1 (deriv x t)) t :=
  hasDerivAt_graph hx

example {x : ℝ → Fin 3 → ℝ} {t : ℝ} (hx : DifferentiableAt ℝ x t) :
    deriv (graph x) t = Fin.cons 1 (deriv x t) :=
  deriv_graph hx

example {x : ℝ → Fin 3 → ℝ} (hx : ContDiff ℝ 2 x) : ContDiff ℝ 2 (graph x) :=
  contDiff_graph hx

example (w : Fin 3 → ℝ) :
    Timelike (Fin.cons 1 w : Spacetime) ↔ ∑ i, w i ^ 2 < 1 :=
  timelike_cons_one w

example (w : Fin 3 → ℝ) :
    properSpeed (Fin.cons 1 w : Spacetime) = Real.sqrt (1 - ∑ i, w i ^ 2) :=
  properSpeed_cons_one w

example (m : ℝ) {x : ℝ → Fin 3 → ℝ} {t : ℝ}
    (hx : DifferentiableAt ℝ x t) :
    freeLagrangian m t (graph x t, deriv (graph x) t) = lagrangian 3 m t (x t, deriv x t) :=
  freeLagrangian_graph m hx

example (w : Fin 3 → ℝ) :
    fourVelocity (Fin.cons 1 w : Spacetime) = gamma w • (Fin.cons 1 w : Spacetime) :=
  fourVelocity_cons_one w

example (v : Fin 3 → ℝ) {w : Fin 3 → ℝ}
    (hw : ∑ i, w i ^ 2 < 1) :
    fourVelocity (Fin.cons 1 v : Spacetime) = fourVelocity (Fin.cons 1 w : Spacetime) ↔
      v = w :=
  fourVelocity_cons_one_eq_iff v hw

example (hm : 0 < m) (hab : a < b) {x : ℝ → Fin 3 → ℝ}
    (hx : ContDiff ℝ 2 x) (hv : ∀ t ∈ Icc a b, ∑ i, deriv x t i ^ 2 < 1) :
    Stationary a b (freeLagrangian m) (graph x) ↔ Stationary a b (lagrangian 3 m) x :=
  free_stationary_graph_iff hm hab hx hv

end ProjectAinos.SpecialRelativity.FreeParticle
