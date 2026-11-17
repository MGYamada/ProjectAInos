/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SpecialRelativity.NumberFlux
import ProjectAinos.SpecialRelativity.OrbitalCharges
import ProjectAinos.SpecialRelativity.CrossSection

/-! Public consumers of the measures and the charges of relativistic particles: the invariant
measure of the mass shell, the number current and the number of particles through a
hypersurface, the momentum, the orbital moment and the centre of energy of a system, the
invariant flux factor and the covariance of a cross-section.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal
namespace ProjectAinos.SpecialRelativity.FutureShell

open SmoothGeometry SmoothGeometry.Minkowski

example {α : Type*} [MeasurableSpace α] {μ : Measure α} {φ : α → α}
    (hφ : Measurable φ) (hμ : Measure.map φ μ = μ) {h : α → ℝ≥0∞} (hh : Measurable h)
    (hcomp : ∀ x, h (φ x) = h x) :
    Measure.map φ (μ.withDensity h) = μ.withDensity h :=
  map_withDensity_of_comp_eq hφ hμ hh hcomp

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {s : Set E} (hs : MeasurableSet s) {φ : E → E}
    {φ' : E → E →L[ℝ] E} (hφ : Measurable φ)
    (hφ' : ∀ x ∈ s, HasFDerivWithinAt φ (φ' x) s x) (hinj : InjOn φ s) (himg : φ '' s = s)
    {h : E → ℝ≥0∞} (hjac : ∀ x ∈ s, ENNReal.ofReal |(φ' x).det| * h (φ x) = h x) :
    Measure.map φ ((μ.restrict s).withDensity h) = (μ.restrict s).withDensity h :=
  map_withDensity_of_jacobian μ hs hφ hφ' hinj himg hjac

variable {d : ℕ} {m : ℝ}

example : Continuous (energy (d := d) m) :=
  continuous_energy

example : Continuous (point (d := d) m) :=
  continuous_point

example (L : orthochronousLorentzGroup d) : Continuous (action m L) :=
  continuous_action L

example : MeasurableSet (domain d m) :=
  measurableSet_domain

example :
    Measurable fun π : Fin d → ℝ => ENNReal.ofReal (energy m π)⁻¹ :=
  measurable_density

example (s t : ℝ) (x y : Fin d → ℝ) :
    pair (Fin.cons s x : MinkowskiModel d) (Fin.cons t y) = s * t - ∑ i, x i * y i :=
  pair_cons s t x y

example (R : LorentzGroup d) (x : Fin d → ℝ) :
    spaceLinear R x = spaceMomentum (R.val (Fin.cons 0 x)) :=
  spaceLinear_apply R x

example {R : LorentzGroup d} (hR : R ∈ rotationGroup d) (x : Fin d → ℝ) :
    R.val (Fin.cons 0 x) = (Fin.cons 0 (spaceLinear R x) : MinkowskiModel d) :=
  rotation_consZero hR x

example (m : ℝ) (π : Fin d → ℝ) :
    point m π = energy m π • timeAxis d + (Fin.cons 0 π : MinkowskiModel d) :=
  point_eq m π

example (m : ℝ) {R : LorentzGroup d} (hR : R ∈ rotationGroup d)
    (π : Fin d → ℝ) :
    action m ⟨R, rotationGroup_le_orthochronous hR⟩ π = spaceLinear R π :=
  action_rotation_eq m hR π

example {R : LorentzGroup d} (hR : R ∈ rotationGroup d)
    (x y : Fin d → ℝ) :
    ∑ i, spaceLinear R x i * spaceLinear R y i = ∑ i, x i * y i :=
  sum_mul_spaceLinear hR x y

example {R : LorentzGroup d} (hR : R ∈ rotationGroup d) (π : Fin d → ℝ) :
    energy m (spaceLinear R π) = energy m π :=
  energy_spaceLinear hR π

example {R : LorentzGroup d} (hR : R ∈ rotationGroup d)
    (π : Fin d → ℝ) : spaceLinear R π ∈ domain d m ↔ π ∈ domain d m :=
  spaceLinear_mem_domain_iff hR π

example {R : LorentzGroup d} (hR : R ∈ rotationGroup d) :
    LinearMap.det (spaceLinear R) ^ 2 = 1 :=
  det_spaceLinear_sq hR

example {R : LorentzGroup d} (hR : R ∈ rotationGroup d) :
    Measure.map (spaceLinear R) (volume : Measure (Fin d → ℝ)) = volume :=
  map_spaceLinear_volume hR

example {R : LorentzGroup d} (hR : R ∈ rotationGroup d) :
    Measure.map (action m ⟨R, rotationGroup_le_orthochronous hR⟩) (measure d m) =
      measure d m :=
  map_action_measure_rotation hR

example {π : Fin d → ℝ} (hπ : π ∈ domain d m) :
    HasFDerivAt (energy (d := d) m) ((energy m π)⁻¹ • FreeParticle.dotCovector π) π :=
  hasFDerivAt_energy hπ

example (c b : Fin d → ℝ) :
    (ContinuousLinearMap.id ℝ (Fin d → ℝ) + (FreeParticle.dotCovector c).smulRight b).det =
      1 + ∑ i, c i * b i :=
  det_id_add_smulRight c b

example (β : Velocity d) (v : MinkowskiModel d) :
    inner ℝ β.val (space v) = ∑ i, velocityCoord β i * spaceMomentum v i :=
  inner_velocity_space β v

example (β : Velocity d) :
    ∑ i, velocityCoord β i * velocityCoord β i = ‖β.val‖ ^ 2 :=
  sum_velocityCoord_mul_self β

example (m : ℝ) (β : Velocity d) (π : Fin d → ℝ) :
    action m (boostOrthochronous β) π = boostMap m β π :=
  action_boost_eq m β π

example (β : Velocity d) {π : Fin d → ℝ} (hπ : π ∈ domain d m) :
    boostMap m β π ∈ domain d m :=
  boostMap_mem β hπ

example (β : Velocity d) {π : Fin d → ℝ} (hπ : π ∈ domain d m) :
    energy m (boostMap m β π) = β.gamma * (energy m π - ∑ j, velocityCoord β j * π j) :=
  energy_boostMap β hπ

example (β : Velocity d) : InjOn (boostMap m β) (domain d m) :=
  injOn_boostMap β

example (β : Velocity d) : boostMap m β '' domain d m = domain d m :=
  image_boostMap β

example (β : Velocity d) {π : Fin d → ℝ} (hπ : π ∈ domain d m) :
    HasFDerivAt (boostMap m β) (boostDeriv m β π) π :=
  hasFDerivAt_boostMap β hπ

example (β : Velocity d) {π : Fin d → ℝ} (hπ : π ∈ domain d m) :
    (boostDeriv m β π).det = energy m (boostMap m β π) / energy m π :=
  det_boostDeriv β hπ

example (β : Velocity d) :
    Measure.map (action m (boostOrthochronous β)) (measure d m) = measure d m :=
  map_action_measure_boost β

example : ∀ᵐ π ∂(measure d m), π ∈ domain d m :=
  ae_mem_domain

example (L : orthochronousLorentzGroup d) :
    Measure.map (action m L) (measure d m) = measure d m :=
  map_action_measure L

example (L : orthochronousLorentzGroup d) :
    MeasurePreserving (action m L) (measure d m) (measure d m) :=
  measurePreserving_action L

example {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : orthochronousLorentzGroup d) (f : (Fin d → ℝ) → G)
    (hf : AEStronglyMeasurable f (measure d m)) :
    ∫ π, f (action m L π) ∂(measure d m) = ∫ π, f π ∂(measure d m) :=
  integral_comp_action L f hf

end ProjectAinos.SpecialRelativity.FutureShell

open Set MeasureTheory
open scoped ENNReal
namespace ProjectAinos.SpecialRelativity.FutureShell

open SmoothGeometry SmoothGeometry.Minkowski

variable {d : ℕ} {m : ℝ}

example (L : orthochronousLorentzGroup d) (v : MinkowskiModel d) :
    lorentzCLM L v = L.val.val v :=
  lorentzCLM_apply L v

example (L : orthochronousLorentzGroup d) {π : Fin d → ℝ}
    (hπ : π ∈ domain d m) : L.val.val (point m (action m L⁻¹ π)) = point m π :=
  point_action_inv L hπ

example (L : orthochronousLorentzGroup d) (f : (Fin d → ℝ) → ℝ)
    (hf : Integrable (fun π => f π • point m π) (measure d m)) :
    numberCurrent m (transformDistribution m L f) = L.val.val (numberCurrent m f) :=
  numberCurrent_transform L f hf

example (u : Observer d) (f : (Fin d → ℝ) → ℝ)
    (hf : Integrable (fun π => f π • point m π) (measure d m)) :
    numberDensity m u f = ∫ π, f π * observerEnergy u (point m π) ∂(measure d m) :=
  numberDensity_eq u f hf

example (L : orthochronousLorentzGroup d) (u : Observer d)
    (f : (Fin d → ℝ) → ℝ) (hf : Integrable (fun π => f π • point m π) (measure d m)) :
    numberDensity m (u.transform L) (transformDistribution m L f) = numberDensity m u f :=
  numberDensity_transform L u f hf

example (u : Observer d) {f : (Fin d → ℝ) → ℝ} (hf0 : ∀ π, 0 ≤ f π)
    (hf : Integrable (fun π => f π • point m π) (measure d m)) : 0 ≤ numberDensity m u f :=
  numberDensity_nonneg u hf0 hf

example (f : (Fin d → ℝ) → ℝ)
    (hf : Integrable (fun π => f π • point m π) (measure d m)) :
    time (numberCurrent m f) = ∫ π in domain d m, f π :=
  time_numberCurrent f hf

example (L : orthochronousLorentzGroup d)
    (σ : Measure (MinkowskiModel d)) (n : MinkowskiModel d)
    (f : MinkowskiModel d → (Fin d → ℝ) → ℝ)
    (hf : ∀ x, Integrable (fun π => f x π • point m π) (measure d m)) :
    numberFlux m (Measure.map L.val.val σ) (L.val.val n)
        (fun y => transformDistribution m L (f (L.val.val.symm y))) =
      numberFlux m σ n f :=
  numberFlux_transform L σ n f hf

example (τ : ℝ) :
    MeasurableEmbedding fun x : Fin d → ℝ => (Fin.cons τ x : MinkowskiModel d) :=
  measurableEmbedding_cons τ

example (τ : ℝ) (f : MinkowskiModel d → (Fin d → ℝ) → ℝ)
    (hf : ∀ x, Integrable (fun π => f x π • point m π) (measure d m)) :
    numberFlux m (hyperplaneMeasure d τ) (timeAxis d) f =
      ∫ x : Fin d → ℝ, ∫ π in domain d m, f (Fin.cons τ x) π :=
  numberFlux_hyperplane τ f hf

end ProjectAinos.SpecialRelativity.FutureShell

open Set
namespace ProjectAinos.SpecialRelativity

open SmoothGeometry SmoothGeometry.Minkowski Mechanics

variable {d : ℕ}

example (x p : MinkowskiModel d) (μ ν : Fin (d + 1)) :
    orbitalMoment x p (ContinuousLinearMap.proj μ) (ContinuousLinearMap.proj ν) =
      x μ * p ν - p μ * x ν :=
  orbitalMoment_proj x p μ ν

example (x p : MinkowskiModel d) (α β : MinkowskiModel d →L[ℝ] ℝ) :
    orbitalMoment x p α β = -orbitalMoment x p β α :=
  orbitalMoment_antisymm x p α β

example (p : MinkowskiModel d) (α β : MinkowskiModel d →L[ℝ] ℝ) :
    orbitalMoment p p α β = 0 :=
  orbitalMoment_self p α β

example (x c p : MinkowskiModel d) (α β : MinkowskiModel d →L[ℝ] ℝ) :
    orbitalMoment (x + c) p α β = orbitalMoment x p α β + orbitalMoment c p α β :=
  orbitalMoment_add_left x c p α β

example (x p q : MinkowskiModel d) (α β : MinkowskiModel d →L[ℝ] ℝ) :
    orbitalMoment x (p + q) α β = orbitalMoment x p α β + orbitalMoment x q α β :=
  orbitalMoment_add_right x p q α β

example (s : ℝ) (x p : MinkowskiModel d)
    (α β : MinkowskiModel d →L[ℝ] ℝ) :
    orbitalMoment (s • x) p α β = s * orbitalMoment x p α β :=
  orbitalMoment_smul_left s x p α β

example (x p : MinkowskiModel d) (s : ℝ)
    (α β : MinkowskiModel d →L[ℝ] ℝ) :
    orbitalMoment (x + s • p) p α β = orbitalMoment x p α β :=
  orbitalMoment_add_smul x p s α β

example (L : LorentzGroup d) (x p : MinkowskiModel d)
    (α β : MinkowskiModel d →L[ℝ] ℝ) :
    orbitalMoment (L.val x) (L.val p) α β =
      orbitalMoment x p (α.comp (LorentzGroup.toContinuousLinearEquiv L).toContinuousLinearMap)
        (β.comp (LorentzGroup.toContinuousLinearEquiv L).toContinuousLinearMap) :=
  orbitalMoment_lorentz L x p α β

example (σ : LorentzConvention) (β : MinkowskiModel d →L[ℝ] ℝ)
    (w : MinkowskiModel d) : minkowskiForm σ d (sharp σ β) w = β w :=
  minkowskiForm_sharp σ β w

example (σ : LorentzConvention)
    (α β : MinkowskiModel d →L[ℝ] ℝ) (v w : MinkowskiModel d) :
    minkowskiForm σ d (lorentzGenerator σ α β v) w +
      minkowskiForm σ d v (lorentzGenerator σ α β w) = 0 :=
  minkowskiForm_lorentzGenerator σ α β v w

example (σ : LorentzConvention) (α β : MinkowskiModel d →L[ℝ] ℝ)
    (x p : MinkowskiModel d) :
    flat σ p (lorentzGenerator σ α β x) = orbitalMoment x p α β :=
  flat_lorentzGenerator σ α β x p

example (m : ℝ) (v x : Spacetime)
    (α β : Spacetime →L[ℝ] ℝ) :
    kineticMomentum m v (lorentzGenerator .timeNegative α β x) =
      orbitalMoment x (m • fourVelocity v) α β :=
  kineticMomentum_lorentzGenerator m v x α β

example {m : ℝ} (hm : m ≠ 0) {γ : ℝ → Spacetime} {a b : ℝ}
    (hab : a < b) (hγ : ContDiff ℝ 2 γ) (hv : ∀ t ∈ Icc a b, Timelike (deriv γ t))
    (h : Stationary a b (freeLagrangian m) γ) {t : ℝ} (ht : t ∈ Icc a b)
    (α β : Spacetime →L[ℝ] ℝ) :
    orbitalMoment (γ t) (m • fourVelocity (deriv γ t)) α β =
      orbitalMoment (γ a) (m • fourVelocity (deriv γ a)) α β :=
  orbitalMoment_eq_of_stationary hm hab hγ hv h ht α β

variable {ι : Type*} [Fintype ι]

example (L : LorentzGroup d) (p : ι → MinkowskiModel d) :
    totalMomentum (fun a => L.val (p a)) = L.val (totalMomentum p) :=
  totalMomentum_lorentz L p

example (L : LorentzGroup d) (x p : ι → MinkowskiModel d)
    (α β : MinkowskiModel d →L[ℝ] ℝ) :
    totalMoment (fun a => L.val (x a)) (fun a => L.val (p a)) α β =
      totalMoment x p (α.comp (LorentzGroup.toContinuousLinearEquiv L).toContinuousLinearMap)
        (β.comp (LorentzGroup.toContinuousLinearEquiv L).toContinuousLinearMap) :=
  totalMoment_lorentz L x p α β

example (x p : ι → MinkowskiModel d) (s : ι → ℝ)
    (α β : MinkowskiModel d →L[ℝ] ℝ) :
    totalMoment (fun a => x a + s a • p a) p α β = totalMoment x p α β :=
  totalMoment_freeMotion x p s α β

example (x p : ι → MinkowskiModel d) (c : MinkowskiModel d)
    (α β : MinkowskiModel d →L[ℝ] ℝ) :
    totalMoment (fun a => x a + c) p α β =
      totalMoment x p α β + orbitalMoment c (totalMomentum p) α β :=
  totalMoment_add_const x p c α β

example (y : MinkowskiModel d) (p : ι → MinkowskiModel d)
    (α β : MinkowskiModel d →L[ℝ] ℝ) :
    ∑ a, orbitalMoment y (p a) α β = orbitalMoment y (totalMomentum p) α β :=
  sum_orbitalMoment_same_event y p α β

example (u : Observer d) (x p : ι → MinkowskiModel d) {t : ℝ}
    (hsim : ∀ a, u.clock (x a) = t) (β : MinkowskiModel d →L[ℝ] ℝ) :
    totalMoment x p u.clock β =
      t * β (totalMomentum p) - β (∑ a, observerEnergy u (p a) • x a) :=
  totalMoment_clock u x p hsim β

example (u : Observer d) (x x' p : ι → MinkowskiModel d) {t t' : ℝ}
    (hsim : ∀ a, u.clock (x a) = t) (hsim' : ∀ a, u.clock (x' a) = t')
    (hJ : ∀ β : MinkowskiModel d →L[ℝ] ℝ,
      totalMoment x' p u.clock β = totalMoment x p u.clock β) :
    centreOfEnergy u x' p - centreOfEnergy u x p =
      ((t' - t) / ∑ a, observerEnergy u (p a)) • totalMomentum p :=
  centreOfEnergy_sub u x x' p hsim hsim' hJ

example (u : Observer d) (x p : ι → MinkowskiModel d) {t : ℝ} (s : ℝ)
    (hsim : ∀ a, u.clock (x a) = t) (hEa : ∀ a, observerEnergy u (p a) ≠ 0) :
    centreOfEnergy u (fun a => x a + (s / observerEnergy u (p a)) • p a) p -
        centreOfEnergy u x p =
      (s / ∑ a, observerEnergy u (p a)) • totalMomentum p :=
  centreOfEnergy_freeMotion u x p s hsim hEa

end ProjectAinos.SpecialRelativity

open MeasureTheory
namespace ProjectAinos.SpecialRelativity

open SmoothGeometry SmoothGeometry.Minkowski

variable {d : ℕ} {p₁ p₂ : MinkowskiModel d}

example (L : LorentzGroup d) (p₁ p₂ : MinkowskiModel d) :
    fluxFactor (L.val p₁) (L.val p₂) = fluxFactor p₁ p₂ :=
  fluxFactor_lorentz L p₁ p₂

example (hp₁ : FutureCausal p₁) (hp₂ : FutureCausal p₂) :
    fluxFactor p₁ p₂ ^ 2 = pair p₁ p₂ ^ 2 - intervalQuadratic p₁ * intervalQuadratic p₂ :=
  fluxFactor_sq_eq hp₁ hp₂

example (hp₁ : FutureCausal p₁) (hp₂ : FutureCausal p₂) :
    fluxFactor p₁ p₂ ^ 2 =
      kallen (mandelstamS p₁ p₂) (intervalQuadratic p₁) (intervalQuadratic p₂) / 4 :=
  fluxFactor_sq hp₁ hp₂

example (u : Observer d) (p₁ : MinkowskiModel d) {m₂ : ℝ}
    (hm₂ : 0 ≤ m₂) :
    fluxFactor p₁ (m₂ • u.velocity) =
      m₂ * Real.sqrt (u.restForm (observerMomentum u p₁) (observerMomentum u p₁)) :=
  fluxFactor_target_at_rest u p₁ hm₂

example (m₃ m₄ : ℝ) (L : orthochronousLorentzGroup d) :
    MeasurePreserving (Prod.map (FutureShell.action m₃ L) (FutureShell.action m₄ L))
      ((FutureShell.measure d m₃).prod (FutureShell.measure d m₄))
      ((FutureShell.measure d m₃).prod (FutureShell.measure d m₄)) :=
  measurePreserving_action_prod m₃ m₄ L

example {α : Type*} [MeasurableSpace α] {ν : Measure α} {φ : α → α}
    (hφ : MeasurePreserving φ ν ν) (hemb : MeasurableEmbedding φ) {W W' : α → ℝ}
    (hW : ∀ y, W' (φ y) = W y) (F : ℝ) (S : Set α) :
    crossSection ν W' F (φ '' S) = crossSection ν W F S :=
  crossSection_covariant hφ hemb hW F S

end ProjectAinos.SpecialRelativity
