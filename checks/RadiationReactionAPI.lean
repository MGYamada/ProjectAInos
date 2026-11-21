/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.Electrodynamics.RadiationReaction

/-! Public consumers of radiation damping (Landau–Lifshitz §§75, 76): the uniform damping field of
a slow source, the self-force of a rigid charge on a prescribed slow path with the electromagnetic
mass and the damping term, the work and the Schott term, the runaway solutions, the reduced
charged oscillator, and the Lorentz–Dirac and Landau–Lifshitz forces with their orthogonality,
their agreement on the undamped motion and the balance of four-momentum. Default elaborator
options are intentional: these checks must not rely on the implementation's transparency
settings. Every statement is pinned with its type. -/

noncomputable section

section RadiationReaction

open MeasureTheory Filter Set Metric Real

open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics.RadiationReaction

open SmoothGeometry SmoothGeometry.Wave SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (timeDeriv^[k] f) :=
  contDiff_iterate_timeDeriv_infty hf k

example (w : E3 → ℝ) (F : ℝ × E3 → ℝ) (s : ℝ) :
    ∫ z, w z * F (s, z) = kernelIntegral (fun y => w (-y)) F (s, 0) :=
  integral_weight_mul_eq_kernelIntegral w F s

example {w : E3 → ℝ} (hw : Continuous w) {F : ℝ × E3 → ℝ} (hF : ContDiff ℝ 1 F) {a : ℝ}
    (hs : SpatialSupport a F) (s : ℝ) :
    HasDerivAt (fun s => ∫ z, w z * F (s, z)) (∫ z, w z * timeDeriv F (s, z)) s :=
  hasDerivAt_integral_weight_mul hw hF hs s

example {w₁ w₂ : E3 → ℝ} (hw₁ : Continuous w₁) (hw₂ : Continuous w₂) {F₁ F₂ : ℝ × E3 → ℝ}
    (h₁ : ContDiff ℝ 1 F₁) (h₂ : ContDiff ℝ 1 F₂) {a : ℝ} (hs₁ : SpatialSupport a F₁)
    (hs₂ : SpatialSupport a F₂) (heq : ∀ s, ∫ z, w₁ z * F₁ (s, z) = ∫ z, w₂ z * F₂ (s, z)) (s : ℝ) :
    ∫ z, w₁ z * timeDeriv F₁ (s, z) = ∫ z, w₂ z * timeDeriv F₂ (s, z) :=
  integral_weight_mul_timeDeriv_eq hw₁ hw₂ h₁ h₂ hs₁ hs₂ heq s

example (ρ : ℝ × E3 → ℝ) (i : Fin 3) (s : ℝ) :
    ℝ :=
  dipoleMoment ρ i s

example (i : Fin 3) :
    Continuous fun z : E3 => z i :=
  continuous_component i

example {ρ : ℝ × E3 → ℝ} (hρ : ContDiff ℝ 1 ρ) {a : ℝ} (hs : SpatialSupport a ρ) (i : Fin 3)
    (s : ℝ) :
    HasDerivAt (dipoleMoment ρ i) (dipoleMoment (timeDeriv ρ) i s) s :=
  hasDerivAt_dipoleMoment hρ hs i s

example {ρ : ℝ × E3 → ℝ} (hρ : ContDiff ℝ ∞ ρ) {a : ℝ} (hs : SpatialSupport a ρ) (i : Fin 3)
    (n : ℕ) :
    deriv^[n] (dipoleMoment ρ i) = dipoleMoment (timeDeriv^[n] ρ) i :=
  iterate_deriv_dipoleMoment hρ hs i n

example {w : E3 → ℝ} (hw : ContDiff ℝ 1 w) {G : ℝ × E3 → ℝ} (hG : ContDiff ℝ 1 G) {a : ℝ}
    (hs : SpatialSupport a G) (s : ℝ) (k : Fin 3) :
    ∫ z, w z * spaceDeriv k G (s, z) =
      -∫ z, fderiv ℝ w z (EuclideanSpace.single k 1) * G (s, z) :=
  integral_mul_spaceDeriv hw hG hs s k

example (i k : Fin 3) (z : E3) :
    fderiv ℝ (fun z : E3 => z i) z (EuclideanSpace.single k 1) = if i = k then 1 else 0 :=
  fderiv_component i k z

variable {a : ℝ} {ρ : ℝ × E3 → ℝ} {j : Fin 3 → ℝ × E3 → ℝ}

example (h : SlowSource a ρ j) (n : ℕ) (s : ℝ) :
    ∫ z, timeDeriv^[n + 1] ρ (s, z) = 0 :=
  integral_iterate_timeDeriv_eq_zero h n s

example (h : SlowSource a ρ j) (i : Fin 3) (s : ℝ) :
    dipoleMoment (timeDeriv ρ) i s = ∫ z, j i (s, z) :=
  dipoleMoment_timeDeriv h i s

example (h : SlowSource a ρ j) (i : Fin 3) (s : ℝ) :
    dipoleMoment (timeDeriv^[3] ρ) i s = ∫ z, timeDeriv^[2] (j i) (s, z) :=
  dipoleMoment_iterate_three h i s

example (h : SlowSource a ρ j) (i : Fin 3) (s : ℝ) (x : E3) :
    slowTerm 3 (spaceDeriv i ρ) s x =
      -(2 * (4 * π)⁻¹) * dipoleMoment (timeDeriv^[3] ρ) i s :=
  slowTerm_three_spaceDeriv h i s x

example (h : SlowSource a ρ j) (ha : 0 ≤ a) {M : ℝ} (hM : DampingBounds M ρ j) {κ : ℝ}
    (hκ : 0 ≤ κ) (t : ℝ) {x : E3} {R : ℝ} (hx : ‖x‖ ≤ R) (i : Fin 3) :
    |electricOf (slowScalar κ ρ) (slowVector κ j) i (t, x) -
        electricOf (darwinScalar κ ρ) (darwinVector κ j) i (t, x) -
        2 / 3 * (4 * π)⁻¹ * κ ^ 3 * deriv^[3] (dipoleMoment ρ i) (κ * t)| ≤
      (M * (R + a) ^ 6 / 72 + M * (R + a) ^ 4 / 6) * κ ^ 4 :=
  dampingField_expansion h ha hM hκ t hx i

example (h : SlowSource a ρ j) (ha : 0 ≤ a) {M : ℝ} (k l : Fin 3)
    (hM : ∀ p, |timeDeriv^[2] (spaceDeriv l (j k)) p| ≤ M) {κ : ℝ} (hκ : 0 ≤ κ) (t : ℝ) {x : E3}
    {R : ℝ} (hx : ‖x‖ ≤ R) :
    |spaceDeriv l (slowVector κ j k) (t, x) - spaceDeriv l (darwinVector κ j k) (t, x) +
        spaceDeriv l (spaceDeriv k (darwinGauge κ ρ)) (t, x)| ≤ M * (R + a) ^ 4 / 6 * κ ^ 3 :=
  spaceDeriv_vector_sub_cubic h ha k l hM hκ t hx

example (h : SlowSource a ρ j) (ha : 0 ≤ a) {M : ℝ} (hM : DampingBounds M ρ j) {κ : ℝ}
    (hκ : 0 ≤ κ) (t : ℝ) {x : E3} {R : ℝ} (hx : ‖x‖ ≤ R) {v : E3} {V : ℝ} (hv : ‖v‖ ≤ V * κ)
    (i : Fin 3) :
    |lorentzDensity (slowScalar κ ρ) (slowVector κ j) v i (t, x) -
        lorentzDensity (darwinScalar κ ρ) (darwinVector κ j) v i (t, x) -
        2 / 3 * (4 * π)⁻¹ * κ ^ 3 * deriv^[3] (dipoleMoment ρ i) (κ * t)| ≤
      (M * (R + a) ^ 6 / 72 + M * (R + a) ^ 4 / 6 + V * (M * (R + a) ^ 4)) * κ ^ 4 :=
  lorentzDensity_expansion h ha hM hκ t hx hv i

example (c : ℝ → E3) (σ : ℝ) (F : ℝ × E3 → ℝ) :
    Prop :=
  ReflectsAbout c σ F

example {G : ℝ × E3 → ℝ} {s : ℝ} {z : E3} (hG : DifferentiableAt ℝ G (s, z)) (m : Fin 3) (α : ℝ) :
    HasDerivAt (fun l : ℝ => G (s, z + (α * l) • EuclideanSpace.single m 1))
      (α * spaceDeriv m G (s, z)) 0 :=
  hasDerivAt_spaceLine hG m α

namespace ReflectsAbout

variable {c : ℝ → E3} {σ : ℝ} {F G : ℝ × E3 → ℝ}

example (hF : ReflectsAbout c σ F) (hG : ReflectsAbout c σ G) :
    ReflectsAbout c σ (fun p => F p + G p) :=
  add hF hG

example (hF : ReflectsAbout c σ F) :
    ReflectsAbout c σ (fun p => -F p) :=
  neg hF

example (hF : ReflectsAbout c σ F) (hG : ReflectsAbout c σ G) :
    ReflectsAbout c σ (fun p => F p - G p) :=
  sub hF hG

example (g : ℝ → ℝ) (hF : ReflectsAbout c σ F) :
    ReflectsAbout c σ (fun p => g p.1 * F p) :=
  mul_left g hF

example (r : ℝ) (hF : ReflectsAbout c σ F) :
    ReflectsAbout c σ (fun p => r * F p) :=
  const_mul r hF

example {ι : Type*} (S : Finset ι) {F : ι → ℝ × E3 → ℝ} (hF : ∀ k ∈ S, ReflectsAbout c σ (F k)) :
    ReflectsAbout c σ (fun p => ∑ k ∈ S, F k p) :=
  sum S hF

example (hF : ReflectsAbout c σ F) (κ : ℝ) :
    ReflectsAbout (fun t => c (κ * t)) σ (slow κ F) :=
  rescale hF κ

example {K : E3 → ℝ} (hK : ∀ y, K (-y) = K y) (hF : ReflectsAbout c σ F) :
    ReflectsAbout c σ (kernelIntegral K F) :=
  kernel hK hF

example (hG : Differentiable ℝ G) (h : ReflectsAbout c σ G) (m : Fin 3) :
    ReflectsAbout c (-σ) (spaceDeriv m G) :=
  gradient hG h m

end ReflectsAbout

example {ρ₀ : E3 → ℝ} (hρ₀ : ∀ y, ρ₀ (-y) = ρ₀ y) {H : E3 → ℝ} {c : E3}
    (hH : ∀ y, H (c - y) = -H (c + y)) :
    ∫ x, ρ₀ (x - c) * H x = 0 :=
  integral_mul_eq_zero_of_odd hρ₀ hH

example {G : E3 → ℝ} (hG : Differentiable ℝ G) {c : ℝ → E3} (hc : Differentiable ℝ c) (s : ℝ)
    (z : E3) :
    timeDeriv (fun p : ℝ × E3 => G (p.2 - c p.1)) (s, z) = -fderiv ℝ G (z - c s) (deriv c s) :=
  timeDeriv_comp_sub_path hG hc s z

example {G : E3 → ℝ} (hG : Differentiable ℝ G) {c : ℝ → E3} (hc : Differentiable ℝ c) (s : ℝ)
    (z : E3) (m : Fin 3) :
    spaceDeriv m (fun p : ℝ × E3 => G (p.2 - c p.1)) (s, z) =
      fderiv ℝ G (z - c s) (EuclideanSpace.single m 1) :=
  spaceDeriv_comp_sub_path hG hc s z m

example {g : ℝ → ℝ} {F : ℝ × E3 → ℝ} (hg : Differentiable ℝ g) (hF : Differentiable ℝ F)
    (m : Fin 3) (p : ℝ × E3) :
    spaceDeriv m (fun q => g q.1 * F q) p = g p.1 * spaceDeriv m F p :=
  spaceDeriv_mul_time hg hF m p

example {g : ℝ → ℝ} {F : ℝ × E3 → ℝ} (hg : Differentiable ℝ g) (hF : Differentiable ℝ F)
    (p : ℝ × E3) :
    timeDeriv (fun q => g q.1 * F q) p = deriv g p.1 * F p + g p.1 * timeDeriv F p :=
  timeDeriv_mul_time hg hF p

example (ℓ : E3 →L[ℝ] ℝ) (w : E3) :
    ℓ w = ∑ k, w k * ℓ (EuclideanSpace.single k 1) :=
  clm_apply_eq_sum ℓ w

example (R : ℝ → E3) (k : Fin 3) (s : ℝ) :
    ℝ :=
  pathVelocity R k s

example {R : ℝ → E3} (hR : ContDiff ℝ ∞ R) (k : Fin 3) :
    ContDiff ℝ ∞ (pathVelocity R k) :=
  contDiff_pathVelocity hR k

example {R : ℝ → E3} (hR : ContDiff ℝ ∞ R) (k : Fin 3) (s : ℝ) :
    deriv (pathVelocity R k) s = deriv (deriv R) s k :=
  deriv_pathVelocity hR k s

example (e : ℝ) (η : E3 → ℝ) (R : ℝ → E3) (k : Fin 3) :
    rigidCurrent e η R k = fun p => pathVelocity R k p.1 * rigidCharge e η R p :=
  rigidCurrent_eq_mul e η R k

section Rigid

variable {e : ℝ} {η : E3 → ℝ} {R : ℝ → E3}

example (hη : ContDiff ℝ ∞ η) (hR : ContDiff ℝ ∞ R) :
    ContDiff ℝ ∞ (rigidCharge e η R) :=
  contDiff_rigidCharge hη hR

example (hη : ContDiff ℝ ∞ η) (hR : ContDiff ℝ ∞ R) (m : Fin 3) (s : ℝ) (z : E3) :
    spaceDeriv m (rigidCharge e η R) (s, z) =
      e * fderiv ℝ η (z - R s) (EuclideanSpace.single m 1) :=
  spaceDeriv_rigidCharge hη hR m s z

example (hη : ContDiff ℝ ∞ η) (hR : ContDiff ℝ ∞ R) (s : ℝ) (z : E3) :
    timeDeriv (rigidCharge e η R) (s, z) = -(e * fderiv ℝ η (z - R s) (deriv R s)) :=
  timeDeriv_rigidCharge hη hR s z

example (e : ℝ) (hη : ContDiff ℝ ∞ η) {b : ℝ} (hb : ∀ z : E3, b < ‖z‖ → η z = 0)
    (hR : ContDiff ℝ ∞ R) {L : ℝ} (hL : ∀ s, ‖R s‖ ≤ L) :
    SlowSource (L + b) (rigidCharge e η R) (rigidCurrent e η R) :=
  slowSource_rigid e hη hb hR hL

example (hηe : ∀ z, η (-z) = η z) :
    ReflectsAbout R 1 (rigidCharge e η R) :=
  reflectsAbout_rigidCharge hηe

example (hηe : ∀ z, η (-z) = η z) (k : Fin 3) :
    ReflectsAbout R 1 (rigidCurrent e η R k) :=
  reflectsAbout_rigidCurrent hηe k

example (hη : ContDiff ℝ ∞ η) {b : ℝ} (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hηe : ∀ z, η (-z) = η z)
    (hR : ContDiff ℝ ∞ R) {L : ℝ} (hL : ∀ s, ‖R s‖ ≤ L) :
    ReflectsAbout R (-1) (timeDeriv (rigidCharge e η R)) :=
  reflectsAbout_timeDeriv_rigidCharge hη hb hηe hR hL

end Rigid

example (y : E3) :
    Potential.newtonKernel (-y) = Potential.newtonKernel y :=
  newtonKernel_neg y

example (i k : Fin 3) (y : E3) :
    darwinKernel i k (-y) = darwinKernel i k y :=
  darwinKernel_neg i k y

example (e : ℝ) (η : E3 → ℝ) (i k : Fin 3) :
    ℝ :=
  selfMass e η i k

example (e : ℝ) (η : E3 → ℝ) :
    ℝ :=
  selfEnergy e η

example (e : ℝ) (η : E3 → ℝ) (R : ℝ → E3) (K : E3 → ℝ) (κ t : ℝ) :
    ∫ x, e * η (x - R (κ * t)) * kernelIntegral K (slow κ (rigidCharge e η R)) (t, x) =
      e ^ 2 * ∫ x, η x * ∫ y, K y * η (x - y) :=
  integral_rigid_mul_kernelIntegral e η R K κ t

example {K : E3 → ℝ} (hK : LocallyIntegrable K) {F G : ℝ × E3 → ℝ} (hF : Continuous F)
    (hG : Continuous G) {a : ℝ} (hFs : SpatialSupport a F) (hGs : SpatialSupport a G)
    (f g : ℝ → ℝ) (κ t : ℝ) (x : E3) :
    kernelIntegral K (slow κ (fun q => f q.1 * F q + g q.1 * G q)) (t, x) =
      f (κ * t) * kernelIntegral K (slow κ F) (t, x) +
        g (κ * t) * kernelIntegral K (slow κ G) (t, x) :=
  kernelIntegral_slow_mul_add hK hF hG hFs hGs f g κ t x

example (h : SlowSource a ρ j) (κ : ℝ) (i : Fin 3) (p : ℝ × E3) :
    timeDeriv (darwinVector κ j i) p =
      κ * ∑ k, κ * kernelIntegral (darwinKernel i k) (slow κ (timeDeriv (j k))) p :=
  timeDeriv_darwinVector h κ i p

example (e : ℝ) {η : E3 → ℝ} (hη : ContDiff ℝ ∞ η) {b : ℝ} (hb : ∀ z : E3, b < ‖z‖ → η z = 0)
    (hηe : ∀ z, η (-z) = η z) {R : ℝ → E3} (hR : ContDiff ℝ ∞ R) {L : ℝ} (hL : ∀ s, ‖R s‖ ≤ L)
    (κ t : ℝ) (i : Fin 3) :
    ∫ x, e * η (x - R (κ * t)) * lorentzDensity (darwinScalar κ (rigidCharge e η R))
        (darwinVector κ (rigidCurrent e η R)) (κ • deriv R (κ * t)) i (t, x) =
      -(κ ^ 2 * ∑ k, selfMass e η i k * deriv (deriv R) (κ * t) k) :=
  selfForce_darwin e hη hb hηe hR hL κ t i

example (A : ℝ) (f : ℝ → ℝ) (n : ℕ) :
    deriv^[n] (fun s => A * f s) = fun s => A * deriv^[n] f s :=
  iterate_deriv_const_mul A f n

example {R : ℝ → E3} (hR : ContDiff ℝ ∞ R) (i : Fin 3) (n : ℕ) :
    deriv^[n] (fun s => R s i) = fun s => deriv^[n] R s i :=
  iterate_deriv_component hR i n

example (e : ℝ) {η : E3 → ℝ} (hη : Continuous η) (hc : HasCompactSupport η) (hη1 : ∫ z, η z = 1)
    (R : ℝ → E3) (i : Fin 3) :
    dipoleMoment (rigidCharge e η R) i = fun s => e * (R s i : ℝ) + e * ∫ y, (y i : ℝ) * η y :=
  dipoleMoment_rigidCharge e hη hc hη1 R i

example (e : ℝ) {η : E3 → ℝ} (hη : Continuous η) (hc : HasCompactSupport η) (hη1 : ∫ z, η z = 1)
    {R : ℝ → E3} (hR : ContDiff ℝ ∞ R) (i : Fin 3) (s : ℝ) :
    deriv^[3] (dipoleMoment (rigidCharge e η R) i) s = e * deriv^[3] R s i :=
  iterate_deriv_dipoleMoment_rigidCharge e hη hc hη1 hR i s

example (e : ℝ) {η : E3 → ℝ} (hη : ContDiff ℝ ∞ η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hηe : ∀ z, η (-z) = η z) (hη1 : ∫ z, η z = 1) {R : ℝ → E3}
    (hR : ContDiff ℝ ∞ R) {L V M : ℝ} (hL : ∀ s, ‖R s‖ ≤ L) (hV : ∀ s, ‖deriv R s‖ ≤ V)
    (hM : DampingBounds M (rigidCharge e η R) (rigidCurrent e η R)) {κ : ℝ} (hκ : 0 ≤ κ) (t : ℝ)
    (i : Fin 3) :
    |(∫ x, e * η (x - R (κ * t)) * lorentzDensity (slowScalar κ (rigidCharge e η R))
        (slowVector κ (rigidCurrent e η R)) (κ • deriv R (κ * t)) i (t, x)) -
      (-(κ ^ 2 * ∑ k, selfMass e η i k * deriv (deriv R) (κ * t) k) +
        2 / 3 * (e ^ 2 / (4 * π)) * (κ ^ 3 * deriv^[3] R (κ * t) i))| ≤
      (∫ z, |e * η z|) * ((M * (2 * (L + b)) ^ 6 / 72 + M * (2 * (L + b)) ^ 4 / 6 +
        V * (M * (2 * (L + b)) ^ 4)) * κ ^ 4) :=
  selfForce_expansion e hη hb0 hb hηe hη1 hR hL hV hM hκ t i

example (y : E3) :
    ∑ i, darwinKernel i i y = 2 * Potential.newtonKernel y :=
  sum_darwinKernel_self y

example (e : ℝ) {η : E3 → ℝ} (hη : Continuous η) (hc : HasCompactSupport η) :
    ∑ i, selfMass e η i i = 4 * selfEnergy e η :=
  trace_selfMass e hη hc

example (T : ℝ) (F : ℝ × E3 → ℝ) :
    Prop :=
  TimePeriodic T F

namespace TimePeriodic

variable {T : ℝ} {F : ℝ × E3 → ℝ}

example (hF : TimePeriodic T F) (s : ℝ) (z : E3) :
    fderiv ℝ F (s + T, z) = fderiv ℝ F (s, z) :=
  fderiv_eq hF s z

example (hF : TimePeriodic T F) :
    TimePeriodic T (timeDeriv F) :=
  deriv_time hF

example (hF : TimePeriodic T F) (i : Fin 3) :
    TimePeriodic T (spaceDeriv i F) :=
  deriv_space hF i

example (hF : TimePeriodic T F) (n : ℕ) :
    TimePeriodic T (timeDeriv^[n] F) :=
  iterate_deriv_time hF n

example (hT : 0 < T) (hF : TimePeriodic T F) (hc : Continuous F) {a : ℝ} (hs : SpatialSupport a F) :
    ∃ M, ∀ p, |F p| ≤ M :=
  exists_bound hT hF hc hs

end TimePeriodic

example {ι : Type*} [Fintype ι] {f : ι → ℝ × E3 → ℝ} (h : ∀ i, ∃ M, ∀ p, |f i p| ≤ M) :
    ∃ M, ∀ i p, |f i p| ≤ M :=
  exists_forall_bound h

example (e : ℝ) (η : E3 → ℝ) {R : ℝ → E3} {T : ℝ} (hRT : Function.Periodic R T) :
    TimePeriodic T (rigidCharge e η R) :=
  timePeriodic_rigidCharge e η hRT

example (e : ℝ) (η : E3 → ℝ) {R : ℝ → E3} {T : ℝ} (hRT : Function.Periodic R T) (k : Fin 3) :
    TimePeriodic T (rigidCurrent e η R k) :=
  timePeriodic_rigidCurrent e η hRT k

example (e : ℝ) {η : E3 → ℝ} (hη : ContDiff ℝ ∞ η) {b : ℝ} (hb : ∀ z : E3, b < ‖z‖ → η z = 0)
    {R : ℝ → E3} (hR : ContDiff ℝ ∞ R) {L : ℝ} (hL : ∀ s, ‖R s‖ ≤ L) {T : ℝ} (hT : 0 < T)
    (hRT : Function.Periodic R T) :
    ∃ M, DampingBounds M (rigidCharge e η R) (rigidCurrent e η R) :=
  exists_dampingBounds_of_periodic e hη hb hR hL hT hRT

example (s : ℝ) :
    E3 :=
  oscillatingPath s

example :
    ContDiff ℝ ∞ oscillatingPath :=
  contDiff_oscillatingPath

example (s : ℝ) :
    ‖oscillatingPath s‖ ≤ 1 :=
  norm_oscillatingPath_le s

example (s : ℝ) :
    deriv oscillatingPath s = Real.cos s • EuclideanSpace.single 0 1 :=
  deriv_oscillatingPath s

example (s : ℝ) :
    ‖deriv oscillatingPath s‖ ≤ 1 :=
  norm_deriv_oscillatingPath_le s

example :
    Function.Periodic oscillatingPath (2 * π) :=
  periodic_oscillatingPath

example :
    pointBump 1 = (⟨1 / 2, 1, by norm_num, by norm_num⟩ : ContDiffBump (0 : E3)).normed volume :=
  pointBump_one_eq

example :
    ContDiff ℝ ∞ (pointBump 1) :=
  contDiff_pointBump_one

example {z : E3} (hz : 1 < ‖z‖) :
    pointBump 1 z = 0 :=
  pointBump_one_eq_zero hz

example (z : E3) :
    pointBump 1 (-z) = pointBump 1 z :=
  pointBump_one_neg z

example :
    ∫ z, pointBump 1 z = 1 :=
  integral_pointBump_one

example (e : ℝ) :
    ∃ C, ∀ κ, 0 ≤ κ → ∀ (t : ℝ) (i : Fin 3),
      |(∫ x, e * pointBump 1 (x - oscillatingPath (κ * t)) *
          lorentzDensity (slowScalar κ (rigidCharge e (pointBump 1) oscillatingPath))
            (slowVector κ (rigidCurrent e (pointBump 1) oscillatingPath))
            (κ • deriv oscillatingPath (κ * t)) i (t, x)) -
        (-(κ ^ 2 * ∑ k, selfMass e (pointBump 1) i k * deriv (deriv oscillatingPath) (κ * t) k) +
          2 / 3 * (e ^ 2 / (4 * π)) * (κ ^ 3 * deriv^[3] oscillatingPath (κ * t) i))| ≤
        C * κ ^ 4 :=
  selfForce_expansion_oscillating e

example (e : ℝ) (v : ℝ → E3) (t : ℝ) :
    E3 :=
  dampingForce e v t

example (e : ℝ) {v : ℝ → E3} (hv : ContDiff ℝ 2 v) (t₀ t₁ : ℝ) :
    ∫ t in t₀..t₁, inner ℝ (dampingForce e v t) (v t) =
      -(2 / 3 * (e ^ 2 / (4 * π))) * (∫ t in t₀..t₁, ‖deriv v t‖ ^ 2) +
        2 / 3 * (e ^ 2 / (4 * π)) *
          (inner ℝ (deriv v t₁) (v t₁) - inner ℝ (deriv v t₀) (v t₀)) :=
  work_dampingForce_eq e hv t₀ t₁

example (e : ℝ) {v : ℝ → E3} (hv : ContDiff ℝ 2 v) {t₀ t₁ : ℝ}
    (h : inner ℝ (deriv v t₁) (v t₁) = inner ℝ (deriv v t₀) (v t₀)) :
    ∫ t in t₀..t₁, inner ℝ (dampingForce e v t) (v t) =
      -(2 / 3 * (e ^ 2 / (4 * π))) * ∫ t in t₀..t₁, ‖deriv v t‖ ^ 2 :=
  work_dampingForce_eq_of_eq e hv h

example {e : ℝ} (he : e ≠ 0) :
    0 < 2 / 3 * (e ^ 2 / (4 * π)) :=
  dampingConstant_pos he

example (e m : ℝ) (he : e ≠ 0) {v : ℝ → E3} (hv : ContDiff ℝ 2 v)
    (h : ∀ t, m • deriv v t = (2 / 3 * (e ^ 2 / (4 * π))) • deriv (deriv v) t) (t : ℝ) :
    deriv v t = Real.exp (m / (2 / 3 * (e ^ 2 / (4 * π))) * t) • deriv v 0 :=
  abrahamLorentz_free e m he hv h t

example (e m : ℝ) (w : E3) (t : ℝ) :
    E3 :=
  runawayVelocity e m w t

example (e m : ℝ) (he : e ≠ 0) (hm : m ≠ 0) (w : E3) (t : ℝ) :
    deriv (runawayVelocity e m w) t =
      Real.exp (m / (2 / 3 * (e ^ 2 / (4 * π))) * t) • w :=
  deriv_runawayVelocity e m he hm w t

example (e m : ℝ) (he : e ≠ 0) (hm : 0 < m) {w : E3} (hw : w ≠ 0) :
    (∀ t, m • deriv (runawayVelocity e m w) t =
        (2 / 3 * (e ^ 2 / (4 * π))) • deriv (deriv (runawayVelocity e m w)) t) ∧
      Tendsto (fun t => ‖deriv (runawayVelocity e m w) t‖) atTop atTop :=
  runaway e m he hm hw

example (e m : ℝ) (he : e ≠ 0) (hm : 0 < m) {v : ℝ → E3} (hv : ContDiff ℝ 2 v)
    (h : ∀ t, m • deriv v t = (2 / 3 * (e ^ 2 / (4 * π))) • deriv (deriv v) t) {C : ℝ}
    (hC : ∀ t, 0 ≤ t → ‖deriv v t‖ ≤ C) (t : ℝ) :
    deriv v t = 0 :=
  abrahamLorentz_free_eq_zero e m he hm hv h hC t

open Mechanics SmoothAlgebra in

example (τ ω₀ : ℝ) (g x : Mechanics.TimeFunction) :
    Prop :=
  IsReducedOscillator τ ω₀ g x

open Mechanics SmoothAlgebra in

example (τ ω₀ : ℝ) (g x : Mechanics.TimeFunction) :
    IsReducedOscillator τ ω₀ g x ↔
      IsForced (τ * ω₀ ^ 2 / 2) ω₀ (g + algebraMap ℝ TimeFunction τ * timeDerivative g) x :=
  isReducedOscillator_iff τ ω₀ g x

open Mechanics SmoothAlgebra in

example (e m ω₀ : ℝ) (g x : Mechanics.TimeFunction) :
    IsReducedOscillator (2 / 3 * (e ^ 2 / (4 * π)) / m) ω₀ g x ↔
      IsForced (e ^ 2 * ω₀ ^ 2 / (12 * π * m)) ω₀
        (g + algebraMap ℝ TimeFunction (2 / 3 * (e ^ 2 / (4 * π)) / m) * timeDerivative g) x :=
  reducedOscillator e m ω₀ g x

open Mechanics SmoothAlgebra in

example (e m ω₀ : ℝ) (he : e ≠ 0) (hm : 0 < m) (hω₀ : ω₀ ≠ 0) {x : Mechanics.TimeFunction}
    (hx : IsReducedOscillator (2 / 3 * (e ^ 2 / (4 * π)) / m) ω₀ 0 x) :
    IsDamped (e ^ 2 * ω₀ ^ 2 / (12 * π * m)) ω₀ x ∧
      Antitone (fun t : ℝ => timeDerivative x (fun _ => t) ^ 2 + ω₀ ^ 2 * x (fun _ => t) ^ 2) ∧
      Tendsto (fun t : ℝ => x fun _ => t) atTop (𝓝 0) :=
  reducedOscillator_free e m ω₀ he hm hω₀ hx

open Mechanics SmoothAlgebra in

example (e m ω₀ : ℝ) (hweak : (e ^ 2 * ω₀ ^ 2 / (12 * π * m)) ^ 2 ≤ ω₀ ^ 2) :
    IsReducedOscillator (2 / 3 * (e ^ 2 / (4 * π)) / m) ω₀ 0
      (TimeFunction.expMul (-(e ^ 2 * ω₀ ^ 2 / (12 * π * m))) *
        TimeFunction.cosMul (√(ω₀ ^ 2 - (e ^ 2 * ω₀ ^ 2 / (12 * π * m)) ^ 2))) :=
  isReducedOscillator_damped e m ω₀ hweak

open Mechanics SmoothAlgebra in

example {τ ω₀ : ℝ} {g x : Mechanics.TimeFunction} (h : IsReducedOscillator τ ω₀ g x) :
    timeDerivative (timeDerivative x) - (g - algebraMap ℝ TimeFunction (ω₀ ^ 2) * x) -
        algebraMap ℝ TimeFunction τ * timeDerivative (timeDerivative (timeDerivative x)) =
      -(algebraMap ℝ TimeFunction τ * algebraMap ℝ TimeFunction τ *
        timeDerivative (timeDerivative (g - algebraMap ℝ TimeFunction (ω₀ ^ 2) * x))) :=
  abrahamLorentz_residual h

section Relativistic

open SmoothGeometry.Minkowski Examples

example {f g : ℝ → Spacetime} {f' g' : Spacetime} {τ : ℝ} (hf : HasDerivAt f f' τ)
    (hg : HasDerivAt g g' τ) :
    HasDerivAt (fun σ => minkowskiForm .timeNegative 3 (f σ) (g σ))
      (minkowskiForm .timeNegative 3 f' (g τ) + minkowskiForm .timeNegative 3 (f τ) g') τ :=
  hasDerivAt_minkowskiForm hf hg

example (e : ℝ) (u : ℝ → Spacetime) (τ : ℝ) :
    Spacetime :=
  lorentzDiracForce e u τ

example (e : ℝ) {u : ℝ → Spacetime} {τ : ℝ} (hu : minkowskiForm .timeNegative 3 (u τ) (u τ) = -1) :
    minkowskiForm .timeNegative 3 (lorentzDiracForce e u τ) (u τ) = 0 :=
  lorentzDirac_orthogonal e hu

example {u : ℝ → Spacetime} (hu : ContDiff ℝ 2 u)
    (hunit : ∀ σ, minkowskiForm .timeNegative 3 (u σ) (u σ) = -1) (τ : ℝ) :
    minkowskiForm .timeNegative 3 (deriv u τ) (u τ) = 0 ∧
      minkowskiForm .timeNegative 3 (deriv (deriv u) τ) (u τ) =
        -minkowskiForm .timeNegative 3 (deriv u τ) (deriv u τ) :=
  minkowskiForm_deriv_of_unit hu hunit τ

example (e : ℝ) {u : ℝ → Spacetime} (hu : ContDiff ℝ 2 u)
    (hunit : ∀ σ, minkowskiForm .timeNegative 3 (u σ) (u σ) = -1) (τ : ℝ) :
    lorentzDiracForce e u τ = (2 / 3 * (e ^ 2 / (4 * π))) • (deriv (deriv u) τ -
      minkowskiForm .timeNegative 3 (deriv u τ) (deriv u τ) • u τ) :=
  lorentzDiracForce_eq_of_unit e hu hunit τ

example (e : ℝ) (u : ℝ → Spacetime) (τ : ℝ) :
    Spacetime :=
  radiatedMomentumRate e u τ

example (e : ℝ) {u : ℝ → Spacetime} (hu : ContDiff ℝ 2 u)
    (hunit : ∀ σ, minkowskiForm .timeNegative 3 (u σ) (u σ) = -1) (τ₀ τ₁ : ℝ) :
    ∫ τ in τ₀..τ₁, lorentzDiracForce e u τ =
      (2 / 3 * (e ^ 2 / (4 * π))) • (deriv u τ₁ - deriv u τ₀) -
        ∫ τ in τ₀..τ₁, radiatedMomentumRate e u τ :=
  integral_lorentzDirac_eq e hu hunit τ₀ τ₁

example (e c : ℝ) (F : TwoForm) (v : Spacetime) :
    lorentzForce e F (c • v) = c • lorentzForce e F v :=
  lorentzForce_smul e c F v

example (e : ℝ) (F : TwoForm) (v w : Spacetime) :
    minkowskiForm .timeNegative 3 (lorentzForce e F v) w =
      -minkowskiForm .timeNegative 3 v (lorentzForce e F w) :=
  minkowskiForm_lorentzForce_swap e F v w

example (F : TwoForm) (v w : Spacetime) :
    F ![v, w] = ∑ ν, v ν * F ![Pi.single ν 1, w] :=
  twoForm_apply_eq_sum F v w

example (e : ℝ) (F : TwoForm) (v : Spacetime) (μ : Fin 4) :
    lorentzForce e F v μ = lorentzSign .timeNegative μ *
      (-e * ∑ ν, v ν * F ![Pi.single ν 1, Pi.single μ 1]) :=
  lorentzForce_apply_eq_sum e F v μ

example (e : ℝ) {Fx : ℝ → TwoForm} {F' : TwoForm} {u : ℝ → Spacetime} {u' : Spacetime} {τ : ℝ}
    (hF : ∀ μ ν : Fin 4, HasDerivAt (fun σ => Fx σ ![Pi.single ν 1, Pi.single μ 1])
      (F' ![Pi.single ν 1, Pi.single μ 1]) τ)
    (hu : HasDerivAt u u' τ) :
    HasDerivAt (fun σ => lorentzForce e (Fx σ) (u σ))
      (lorentzForce e F' (u τ) + lorentzForce e (Fx τ) u') τ :=
  hasDerivAt_lorentzForce e hF hu

example (m e : ℝ) (F F' : TwoForm) (u : Spacetime) :
    Spacetime :=
  landauLifshitzForce m e F F' u

example (m e : ℝ) (F F' : TwoForm) {u : Spacetime} (hu : minkowskiForm .timeNegative 3 u u = -1) :
    minkowskiForm .timeNegative 3 (landauLifshitzForce m e F F' u) u = 0 :=
  landauLifshitz_orthogonal m e F F' hu

example (m e : ℝ) {u : ℝ → Spacetime} {Fx : ℝ → TwoForm} {F' : TwoForm} {τ : ℝ}
    (hF : ∀ μ ν : Fin 4, HasDerivAt (fun σ => Fx σ ![Pi.single ν 1, Pi.single μ 1])
      (F' ![Pi.single ν 1, Pi.single μ 1]) τ)
    (hu : ∀ σ, HasDerivAt u (m⁻¹ • lorentzForce e (Fx σ) (u σ)) σ) :
    lorentzDiracForce e u τ = landauLifshitzForce m e (Fx τ) F' (u τ) :=
  lorentzDirac_eq_landauLifshitz m e hF hu

example :
    ContDiff ℝ 2 hyperbolaVelocity :=
  contDiff_hyperbolaVelocity

example (τ : ℝ) :
    minkowskiForm .timeNegative 3 (hyperbolaVelocity τ) (hyperbolaVelocity τ) = -1 :=
  minkowskiForm_hyperbolaVelocity τ

example (τ : ℝ) :
    minkowskiForm .timeNegative 3 (hyperbola τ) (hyperbola τ) = 1 :=
  minkowskiForm_hyperbola τ

example (e τ : ℝ) :
    lorentzDiracForce e hyperbolaVelocity τ = 0 :=
  lorentzDiracForce_hyperbolaVelocity e τ

example (τ : ℝ) :
    (1 : ℝ) • deriv hyperbolaVelocity τ =
      lorentzForce 1 (uniformField 1 0) (hyperbolaVelocity τ) +
        lorentzDiracForce 1 hyperbolaVelocity τ :=
  hyperbola_lorentzDirac_equation τ

example (τ : ℝ) :
    landauLifshitzForce 1 1 (uniformField 1 0) 0 (hyperbolaVelocity τ) = 0 :=
  landauLifshitzForce_hyperbola τ

example (e τ₀ τ₁ : ℝ) :
    ∫ τ in τ₀..τ₁, radiatedMomentumRate e hyperbolaVelocity τ =
      (2 / 3 * (e ^ 2 / (4 * π))) • (hyperbola τ₁ - hyperbola τ₀) :=
  integral_radiatedMomentumRate_hyperbola e τ₀ τ₁

example (x : ℝ → E3) (t : ℝ) :
    ℝ :=
  lorentzFactor x t

example (x : ℝ → E3) (t : ℝ) :
    Spacetime :=
  pathFourVelocity x t

example (a b : ℝ) (y z : E3) :
    minkowskiForm .timeNegative 3 (Minkowski.vector a y) (Minkowski.vector b z) =
      -(a * b) + inner ℝ y z :=
  minkowskiForm_vector a b y z

example {x : ℝ → E3} {t : ℝ} (hv : ‖deriv x t‖ < 1) :
    minkowskiForm .timeNegative 3 (pathFourVelocity x t) (pathFourVelocity x t) = -1 :=
  minkowskiForm_pathFourVelocity hv

example (c : ℝ) {y : ℝ → E3} (hy : ContDiff ℝ ∞ y) :
    ContDiff ℝ ∞ fun t => Minkowski.vector c (y t) :=
  contDiff_vector c hy

example (c : ℝ) {y : ℝ → E3} {y' : E3} {t : ℝ} (hy : HasDerivAt y y' t) :
    HasDerivAt (fun s => Minkowski.vector c (y s)) (Minkowski.vector 0 y') t :=
  hasDerivAt_vector c hy

example {x : ℝ → E3} (hx : ContDiff ℝ ∞ x) (hv : ∀ t, ‖deriv x t‖ < 1) :
    ContDiff ℝ ∞ (lorentzFactor x) :=
  contDiff_lorentzFactor hx hv

example {x : ℝ → E3} (hx : ContDiff ℝ ∞ x) (hv : ∀ t, ‖deriv x t‖ < 1) {t₀ : ℝ}
    (h0 : deriv x t₀ = 0) :
    HasDerivAt (lorentzFactor x) 0 t₀ :=
  hasDerivAt_lorentzFactor_of_rest hx hv h0

example {U : ℝ → Spacetime} (hU : ContDiff ℝ 2 U) {γ : ℝ → ℝ} (hγ : ContDiff ℝ 1 γ) {θ : ℝ → ℝ}
    (hθ : ∀ τ, HasDerivAt θ (γ (θ τ)) τ) {τ₀ : ℝ} (h1 : γ (θ τ₀) = 1) (h0 : deriv γ (θ τ₀) = 0) :
    deriv (deriv fun τ => U (θ τ)) τ₀ = deriv (deriv U) (θ τ₀) :=
  deriv_deriv_comp_of_rest hU hγ hθ h1 h0

example {x : ℝ → E3} (hx : ContDiff ℝ ∞ x) (hv : ∀ t, ‖deriv x t‖ < 1) {t₀ : ℝ}
    (h0 : deriv x t₀ = 0) :
    ∃ c : ℝ, deriv (deriv (pathFourVelocity x)) t₀ =
      c • Minkowski.vector 1 0 + Minkowski.vector 0 (deriv^[3] x t₀) :=
  deriv_deriv_pathFourVelocity_of_rest hx hv h0

example (e : ℝ) {x : ℝ → E3} (hx : ContDiff ℝ ∞ x) (hv : ∀ t, ‖deriv x t‖ < 1) {θ : ℝ → ℝ}
    (hθ : ∀ τ, HasDerivAt θ (lorentzFactor x (θ τ)) τ) {τ₀ : ℝ} (hrest : deriv x (θ τ₀) = 0) :
    lorentzDiracForce e (fun τ => pathFourVelocity x (θ τ)) τ₀ =
      Minkowski.vector 0 ((2 / 3 * (e ^ 2 / (4 * π))) • deriv^[3] x (θ τ₀)) :=
  lorentzDirac_nonrelativistic e hx hv hθ hrest

example (t : ℝ) :
    E3 :=
  hyperbolicPath t

example (t : ℝ) :
    deriv hyperbolicPath t = (t / √(1 + t ^ 2)) • EuclideanSpace.single 0 1 :=
  deriv_hyperbolicPath t

example :
    ContDiff ℝ ∞ hyperbolicPath :=
  contDiff_hyperbolicPath

example (t : ℝ) :
    ‖deriv hyperbolicPath t‖ < 1 :=
  norm_deriv_hyperbolicPath_lt t

example (τ : ℝ) :
    lorentzFactor hyperbolicPath (Real.sinh τ) =
    Real.cosh τ :=
  lorentzFactor_hyperbolicPath τ

example (e : ℝ) :
    lorentzDiracForce e (fun τ => pathFourVelocity hyperbolicPath (Real.sinh τ)) 0 =
      Minkowski.vector 0 ((2 / 3 * (e ^ 2 / (4 * π))) • deriv^[3] hyperbolicPath (Real.sinh 0)) :=
  lorentzDirac_nonrelativistic_hyperbolic e

end Relativistic

end ProjectAinos.Electrodynamics.RadiationReaction

end RadiationReaction
