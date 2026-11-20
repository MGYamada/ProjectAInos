/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Potential.Laplacian
import ProjectAinos.SmoothGeometry.Potential.NewtonKernel
import ProjectAinos.SmoothGeometry.Potential.MaximumPrinciple
import ProjectAinos.SmoothGeometry.Potential.NewtonPotential
import ProjectAinos.Electrodynamics.Electrostatics
import ProjectAinos.Electrodynamics.ElectrostaticEnergy

/-! Public consumers of electrostatics (Landau–Lifshitz §§36, 37): the co-ordinate Laplacian
and Green's identities, the Newton kernel with its regularization and the pairing
`∫ K Δχ = −χ(0)`, the maximum principle and the uniqueness of decaying harmonic functions, the
Newton potential with `Δφ = −ρ`, its decay and its gradient bound; the electrostatic field with
Maxwell's equations, the point charge with its flux, and the three equal expressions of the
energy with the divergent self-energy of a point charge.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/

noncomputable section

section Laplacian

open MeasureTheory Filter Set

open scoped Topology Laplacian ContDiff

namespace ProjectAinos.SmoothGeometry.Potential

variable {n : ℕ}

example (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ℝ :=
  coordLaplacian f x

example {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ 2 f x) (v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => fderiv ℝ f y w) x v = fderiv ℝ (fderiv ℝ f) x v w :=
  fderiv_fderiv_apply hf v w

example {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ 2 f x) :
    coordLaplacian f x = Δ f x :=
  coordLaplacian_eq_laplacian hf

example {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 2 f) :
    Δ f = coordLaplacian f :=
  laplacian_eq_coordLaplacian hf

example {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (coordLaplacian f) :=
  continuous_coordLaplacian hf

example {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ tsupport f) :
    coordLaplacian f x = 0 :=
  coordLaplacian_eq_zero_of_notMem_tsupport hx

example {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (coordLaplacian f) :=
  hasCompactSupport_coordLaplacian hf

example {g : ℝ → ℝ} {g' : ℝ} {y : EuclideanSpace ℝ (Fin n)} (hg : HasDerivAt g g' (‖y‖ ^ 2)) :
    HasFDerivAt (fun z => g (‖z‖ ^ 2)) ((2 * g') • innerSL ℝ y) y :=
  hasFDerivAt_comp_normSq hg

example {g g' : ℝ → ℝ} {g'' : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hg : ∀ᶠ s in 𝓝 (‖x‖ ^ 2), HasDerivAt g (g' s) s) (hg' : HasDerivAt g' g'' (‖x‖ ^ 2)) :
    coordLaplacian (fun y => g (‖y‖ ^ 2)) x = 2 * n * g' (‖x‖ ^ 2) + 4 * ‖x‖ ^ 2 * g'' :=
  coordLaplacian_comp_normSq hg hg'

example (f : EuclideanSpace ℝ (Fin n) → ℝ) (a x : EuclideanSpace ℝ (Fin n)) :
    coordLaplacian (fun y => f (y - a)) x = coordLaplacian f (x - a) :=
  coordLaplacian_comp_sub f a x

example (f : EuclideanSpace ℝ (Fin n) → ℝ) (a x : EuclideanSpace ℝ (Fin n)) :
    coordLaplacian (fun y => f (a + y)) x = coordLaplacian f (a + x) :=
  coordLaplacian_comp_add_left f a x

example (c x : EuclideanSpace ℝ (Fin n)) :
    coordLaplacian (fun y => ‖y - c‖ ^ 2) x = 2 * n :=
  coordLaplacian_normSq_sub c x

example {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hcg : HasCompactSupport g) (v : EuclideanSpace ℝ (Fin n)) :
    ∫ x, f x * fderiv ℝ (fun y => fderiv ℝ g y v) x v =
      ∫ x, fderiv ℝ (fun y => fderiv ℝ f y v) x v * g x :=
  integral_mul_fderiv_fderiv hf hg hcg v

example {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hcg : HasCompactSupport g) :
    ∫ x, f x * coordLaplacian g x = ∫ x, coordLaplacian f x * g x :=
  integral_mul_coordLaplacian hf hg hcg

example {w φ : EuclideanSpace ℝ (Fin n) → ℝ} (hw : ContDiff ℝ 1 w) (hcw : HasCompactSupport w)
    (hφ : ContDiff ℝ 2 φ) :
    ∫ x, w x * coordLaplacian φ x = -∫ x, ∑ i, fderiv ℝ w x (EuclideanSpace.single i 1) *
      fderiv ℝ φ x (EuclideanSpace.single i 1) :=
  integral_mul_coordLaplacian_eq_neg_sum hw hcw hφ

end ProjectAinos.SmoothGeometry.Potential

end Laplacian

section NewtonKernel

open MeasureTheory Filter Set Metric Real Bornology

open scoped Topology Laplacian ContDiff

namespace ProjectAinos.SmoothGeometry.Potential

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (x : E3) :
    ℝ :=
  newtonKernel x

example (ε : ℝ) (x : E3) :
    ℝ :=
  regularKernel ε x

example (e s : ℝ) :
    ℝ :=
  kernelProfile e s

example :
    newtonKernel = regularKernel 0 :=
  newtonKernel_eq_regularKernel

example (ε : ℝ) (x : E3) :
    regularKernel ε x = kernelProfile (ε ^ 2) (‖x‖ ^ 2) :=
  regularKernel_eq_kernelProfile ε x

example (x : E3) :
    newtonKernel (-x) = newtonKernel x :=
  newtonKernel_neg x

example (x : E3) :
    0 ≤ newtonKernel x :=
  newtonKernel_nonneg x

example {ε : ℝ} (hε : ε ≠ 0) (x : E3) :
    0 < regularKernel ε x :=
  regularKernel_pos hε x

example (ε : ℝ) {x : E3} (hx : x ≠ 0) :
    regularKernel ε x ≤ newtonKernel x :=
  regularKernel_le_newtonKernel ε hx

example {e s : ℝ} (h : 0 < s + e) :
    HasDerivAt (kernelProfile e) (-(8 * π)⁻¹ * (s + e) ^ (-(3 / 2 : ℝ))) s :=
  hasDerivAt_kernelProfile h

example {e s : ℝ} (h : 0 < s + e) :
    HasDerivAt (fun t => -(8 * π)⁻¹ * (t + e) ^ (-(3 / 2 : ℝ)))
      (3 * (16 * π)⁻¹ * (s + e) ^ (-(5 / 2 : ℝ))) s :=
  hasDerivAt_kernelProfile_deriv h

example {ε : ℝ} {x : E3} (h : 0 < ‖x‖ ^ 2 + ε ^ 2) :
    coordLaplacian (regularKernel ε) x =
      -(3 * ε ^ 2 / (4 * π)) * (‖x‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)) :=
  coordLaplacian_regularKernel_rpow h

example {ε : ℝ} {x : E3} (h : 0 < ‖x‖ ^ 2 + ε ^ 2) :
    coordLaplacian (regularKernel ε) x =
      -3 * ε ^ 2 / (4 * π * (‖x‖ ^ 2 + ε ^ 2) ^ (5 / 2 : ℝ)) :=
  coordLaplacian_regularKernel h

example {ε : ℝ} (hε : ε ≠ 0) {n : WithTop ℕ∞} :
    ContDiff ℝ n (regularKernel ε) :=
  contDiff_regularKernel hε

example {ε : ℝ} (hε : ε ≠ 0) (x : E3) :
    Δ (regularKernel ε) x = -3 * ε ^ 2 / (4 * π * (‖x‖ ^ 2 + ε ^ 2) ^ (5 / 2 : ℝ)) :=
  laplacian_regularKernel hε x

example {x : E3} (hx : x ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n newtonKernel x :=
  contDiffAt_newtonKernel hx

example {x : E3} (hx : x ≠ 0) :
    AnalyticAt ℝ newtonKernel x :=
  analyticAt_newtonKernel hx

example {x : E3} (hx : x ≠ 0) :
    coordLaplacian newtonKernel x = 0 :=
  coordLaplacian_newtonKernel hx

example {x : E3} (hx : x ≠ 0) :
    InnerProductSpace.HarmonicAt newtonKernel x :=
  harmonicAt_newtonKernel hx

example {x : E3} (hx : x ≠ 0) :
    HasFDerivAt newtonKernel (-(4 * π * ‖x‖ ^ 3)⁻¹ • innerSL ℝ x) x :=
  hasFDerivAt_newtonKernel hx

example {x : E3} (hx : x ≠ 0) :
    ‖fderiv ℝ newtonKernel x‖ = (4 * π * ‖x‖ ^ 2)⁻¹ :=
  norm_fderiv_newtonKernel hx

example :
    LocallyIntegrable newtonKernel :=
  locallyIntegrable_newtonKernel

example (x : E3) :
    ℝ :=
  peakFunction x

example (x : E3) :
    0 ≤ peakFunction x :=
  peakFunction_nonneg x

example :
    ∫ r in Ioi (0 : ℝ), 3 * r ^ 2 * (r ^ 2 + 1) ^ (-(5 / 2 : ℝ)) = 1 :=
  integral_Ioi_peakProfile

example :
    ∫ x, peakFunction x = 1 :=
  integral_peakFunction

example :
    Tendsto (fun x : E3 => ‖x‖ ^ Module.finrank ℝ E3 * peakFunction x) (cobounded E3)
      (𝓝 0) :=
  tendsto_norm_pow_mul_peakFunction

example {ε : ℝ} (hε : 0 < ε) (y : E3) :
    -coordLaplacian (regularKernel ε) y = ε⁻¹ ^ 3 * peakFunction (ε⁻¹ • y) :=
  neg_coordLaplacian_regularKernel hε y

example {L : E3 → ℝ} (hL : Continuous L) (hcL : HasCompactSupport L) :
    Tendsto (fun ε => ∫ y, regularKernel ε y * L y) (𝓝[>] 0)
      (𝓝 (∫ y, newtonKernel y * L y)) :=
  tendsto_integral_regularKernel_mul hL hcL

example {χ : E3 → ℝ} (hχ : ContDiff ℝ 2 χ) (hcχ : HasCompactSupport χ) :
    ∫ y, newtonKernel y * coordLaplacian χ y = -χ 0 :=
  integral_newtonKernel_mul_coordLaplacian hχ hcχ

example {χ : E3 → ℝ} (hχ : ContDiff ℝ 2 χ) (hcχ : HasCompactSupport χ) :
    ∫ y, newtonKernel y * Δ χ y = -χ 0 :=
  integral_newtonKernel_mul_laplacian hχ hcχ

end ProjectAinos.SmoothGeometry.Potential

end NewtonKernel

section MaximumPrinciple

open Filter Set Metric

open scoped Topology Laplacian ContDiff

namespace ProjectAinos.SmoothGeometry.Potential

variable {n : ℕ}

example {g : ℝ → ℝ} {s₀ : ℝ} (h : IsLocalMax g s₀) (hc : ContinuousAt g s₀) :
    deriv (deriv g) s₀ ≤ 0 :=
  deriv_deriv_nonpos_of_isLocalMax h hc

example {u : EuclideanSpace ℝ (Fin n) → ℝ} {p : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiffAt ℝ 2 u p) (hmax : IsLocalMax u p) :
    coordLaplacian u p ≤ 0 :=
  coordLaplacian_nonpos_of_isLocalMax hu hmax

example [NeZero n] {u : EuclideanSpace ℝ (Fin n) → ℝ} {c : EuclideanSpace ℝ (Fin n)} {R M : ℝ}
    (hu : ∀ x ∈ closedBall c R, ContDiffAt ℝ 2 u x) (hΔ : ∀ x ∈ ball c R, 0 ≤ Δ u x)
    (hM : ∀ x ∈ sphere c R, u x ≤ M) :
    ∀ x ∈ closedBall c R, u x ≤ M :=
  le_of_laplacian_nonneg hu hΔ hM

example [NeZero n] {u : EuclideanSpace ℝ (Fin n) → ℝ} {c : EuclideanSpace ℝ (Fin n)} {R M : ℝ}
    (hu : ∀ x ∈ closedBall c R, ContDiffAt ℝ 2 u x) (hΔ : ∀ x ∈ ball c R, Δ u x = 0)
    (hM : ∀ x ∈ sphere c R, |u x| ≤ M) :
    ∀ x ∈ closedBall c R, |u x| ≤ M :=
  abs_le_of_laplacian_eq_zero hu hΔ hM

example [NeZero n] {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 2 u) (hΔ : ∀ x, Δ u x = 0)
    (hlim : Tendsto u (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0)) :
    u = 0 :=
  eq_zero_of_harmonic_of_tendsto hu hΔ hlim

end ProjectAinos.SmoothGeometry.Potential

end MaximumPrinciple

section NewtonPotential

open MeasureTheory Filter Set Metric Real

open scoped Topology Laplacian ContDiff Convolution

namespace ProjectAinos.SmoothGeometry.Potential

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (ρ : E3 → ℝ) :
    E3 → ℝ :=
  newtonPotential ρ

example (ρ : E3 → ℝ) (x : E3) :
    newtonPotential ρ x = ∫ y, newtonKernel y * ρ (x - y) :=
  newtonPotential_apply ρ x

example (ρ : E3 → ℝ) (x : E3) :
    newtonPotential ρ x = ∫ y, ρ y * newtonKernel (x - y) :=
  newtonPotential_eq_integral ρ x

example {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ) (hρ : Continuous ρ) (x : E3) :
    Integrable fun y => newtonKernel y * ρ (x - y) :=
  integrable_newtonKernel_mul hcρ hρ x

example {ρ : E3 → ℝ} {n : ℕ∞} (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ n ρ) :
    ContDiff ℝ n (newtonPotential ρ) :=
  contDiff_newtonPotential hcρ hρ

example {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) :
    ContDiff ℝ 2 (newtonPotential ρ) :=
  contDiff_two_newtonPotential hcρ hρ

example {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) (x v : E3) :
    fderiv ℝ (newtonPotential ρ) x v = newtonPotential (fun y => fderiv ℝ ρ y v) x :=
  fderiv_newtonPotential_apply hcρ hρ x v

example {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) (x : E3) :
    coordLaplacian (newtonPotential ρ) x = newtonPotential (coordLaplacian ρ) x :=
  coordLaplacian_newtonPotential hcρ hρ x

example {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) (x : E3) :
    Δ (newtonPotential ρ) x = -ρ x :=
  laplacian_newtonPotential hcρ hρ x

example {ρ : E3 → ℝ} {a : ℝ} (ha : tsupport ρ ⊆ closedBall 0 a) {x : E3} (hx : a < ‖x‖) (y : E3) :
    |ρ y * newtonKernel (x - y)| ≤ |ρ y| * (4 * π * (‖x‖ - a))⁻¹ :=
  abs_mul_newtonKernel_le ha hx y

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) {a : ℝ}
    (ha : tsupport ρ ⊆ closedBall 0 a) {x : E3} (hx : a < ‖x‖) :
    |newtonPotential ρ x| ≤ (∫ y, |ρ y|) / (4 * π * (‖x‖ - a)) :=
  abs_newtonPotential_le hρ hcρ ha hx

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) {a : ℝ}
    (ha : tsupport ρ ⊆ closedBall 0 a) {x : E3} (hx : a < ‖x‖) :
    HasFDerivAt (newtonPotential ρ) (∫ y, ρ y • fderiv ℝ newtonKernel (x - y)) x :=
  hasFDerivAt_newtonPotential_of_lt hρ hcρ ha hx

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) {a : ℝ}
    (ha : tsupport ρ ⊆ closedBall 0 a) {x : E3} (hx : a < ‖x‖) :
    ‖fderiv ℝ (newtonPotential ρ) x‖ ≤ (∫ y, |ρ y|) / (4 * π * (‖x‖ - a) ^ 2) :=
  norm_fderiv_newtonPotential_le hρ hcρ ha hx

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) :
    Tendsto (newtonPotential ρ) (cocompact E3) (𝓝 0) :=
  tendsto_newtonPotential_cocompact hρ hcρ

example {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ) :
    ∃ a, 0 ≤ a ∧ tsupport ρ ⊆ closedBall 0 a :=
  exists_tsupport_subset_closedBall hcρ

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) :
    ∃ A, ∀ x, |newtonPotential ρ x| ≤ A * (1 + ‖x‖)⁻¹ :=
  exists_abs_newtonPotential_le hρ hcρ

example {ρ : E3 → ℝ} (hρ : ContDiff ℝ 1 ρ) (hcρ : HasCompactSupport ρ) :
    ∃ B, ∀ x, ‖fderiv ℝ (newtonPotential ρ) x‖ ≤ B * ((1 + ‖x‖) ^ 2)⁻¹ :=
  exists_norm_fderiv_newtonPotential_le hρ hcρ

example {ρ u : E3 → ℝ} (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) (hu : ContDiff ℝ 2 u)
    (hΔ : ∀ x, -Δ u x = ρ x) (hlim : Tendsto u (cocompact E3) (𝓝 0)) :
    u = newtonPotential ρ :=
  eq_newtonPotential_of_tendsto hcρ hρ hu hΔ hlim

end ProjectAinos.SmoothGeometry.Potential

end NewtonPotential

section Electrostatics

open MeasureTheory Filter Set Metric Real

open scoped Topology Laplacian ContDiff

namespace ProjectAinos.Electrodynamics.Electrostatics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Potential SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) (p : E3) :
    -Δ (newtonPotential ρ) p = ρ p :=
  neg_laplacian_newtonPotential hcρ hρ p

example (ρ : E3 → ℝ) (p : E3) :
    Fin 3 → ℝ :=
  coulombField ρ p

example {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) (p : E3) :
    ∑ i, fderiv ℝ (fun q => coulombField ρ q i) p (EuclideanSpace.single i 1) = ρ p :=
  div_coulombField hcρ hρ p

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) {a : ℝ}
    (ha : tsupport ρ ⊆ closedBall 0 a) {p : E3} (hp : a < ‖p‖) (i : Fin 3) :
    |coulombField ρ p i| ≤ (∫ y, |ρ y|) / (4 * π * (‖p‖ - a) ^ 2) :=
  abs_coulombField_le hρ hcρ ha hp i

example (ρ : E3 → ℝ) :
    Potential :=
  electrostaticPotential ρ

example (ρ : E3 → ℝ) :
    electrostaticPotential ρ =
      fun y => (-newtonPotential ρ (space y)) • oneCovector.symm (ContinuousLinearMap.proj 0) :=
  electrostaticPotential_eq ρ

example :
    space (Pi.single 0 1 : Spacetime) = 0 :=
  space_pi_single_zero

example (i : Fin 3) :
    space (Pi.single i.succ 1 : Spacetime) = EuclideanSpace.single i 1 :=
  space_pi_single_succ i

example {g : E3 → ℝ} {y : Spacetime} (hg : DifferentiableAt ℝ g (space y)) (v : Spacetime) :
    fderiv ℝ (fun z => g (space z)) y v = fderiv ℝ g (space y) (space v) :=
  fderiv_comp_space_apply hg v

example {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) (y : Spacetime) :
    HasFDerivAt (electrostaticPotential ρ)
      ((-(fderiv ℝ (newtonPotential ρ) (space y)).comp
        (space : Spacetime →L[ℝ] Space 3)).smulRight
          (oneCovector.symm (ContinuousLinearMap.proj 0))) y :=
  hasFDerivAt_electrostaticPotential hcρ hρ y

example {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) (y v w : Spacetime) :
    fieldTensor (electrostaticPotential ρ) y ![v, w] =
      fderiv ℝ (newtonPotential ρ) (space y) (space w) * v 0 -
        fderiv ℝ (newtonPotential ρ) (space y) (space v) * w 0 :=
  fieldTensor_electrostaticPotential_apply hcρ hρ y v w

example {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) (i : Fin 3) (y : Spacetime) :
    electricField (fieldTensor (electrostaticPotential ρ)) i y = coulombField ρ (space y) i :=
  electricField_electrostaticPotential hcρ hρ i y

example {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) (i : Fin 3) (y : Spacetime) :
    magneticField (fieldTensor (electrostaticPotential ρ)) i y = 0 :=
  magneticField_electrostaticPotential hcρ hρ i y

example {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) (y : Spacetime) :
    (divergence3 (magneticField (fieldTensor (electrostaticPotential ρ))) y = 0 ∧
      ∀ i, partialAt (magneticField (fieldTensor (electrostaticPotential ρ)) i) 0 y +
        curl (electricField (fieldTensor (electrostaticPotential ρ))) y i = 0) ∧
    (divergence3 (electricField (fieldTensor (electrostaticPotential ρ))) y = ρ (space y) ∧
      ∀ i, curl (magneticField (fieldTensor (electrostaticPotential ρ))) y i -
        partialAt (electricField (fieldTensor (electrostaticPotential ρ)) i) 0 y = 0) :=
  maxwell_electrostaticPotential hcρ hρ y

example (q : ℝ) (x : E3) :
    ℝ :=
  pointChargePotential q x

example (q : ℝ) (x : E3) :
    E3 :=
  pointChargeField q x

example (q : ℝ) {x : E3} (hx : x ≠ 0) :
    InnerProductSpace.HarmonicAt (pointChargePotential q) x :=
  harmonicAt_pointChargePotential q hx

example (q : ℝ) {x : E3} (hx : x ≠ 0) (v : E3) :
    inner ℝ (pointChargeField q x) v = -fderiv ℝ (pointChargePotential q) x v :=
  inner_pointChargeField q hx v

example (q : ℝ) {R : ℝ} (hR : 0 < R) :
    ∫ u : sphere (0 : E3) 1, inner ℝ (pointChargeField q (R • (u : E3))) u * R ^ 2
      ∂(volume.toSphere) = q :=
  flux_pointChargeField q hR

example (q : ℝ) {χ : E3 → ℝ} (hχ : ContDiff ℝ 2 χ) (hcχ : HasCompactSupport χ) :
    ∫ x, pointChargePotential q x * Δ χ x = -(q * χ 0) :=
  integral_pointChargePotential_mul_laplacian q hχ hcχ

end ProjectAinos.Electrodynamics.Electrostatics

end Electrostatics

section ElectrostaticEnergy

open MeasureTheory Filter Set Metric Real

open scoped Topology Laplacian ContDiff

namespace ProjectAinos.Electrodynamics.Electrostatics

open SmoothGeometry.Potential

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) :
    Integrable (fun p : E3 × E3 => ρ p.1 * ρ p.2 * newtonKernel (p.1 - p.2))
      (volume.prod volume) :=
  integrable_double hρ hcρ

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) :
    ∫ x, ρ x * newtonPotential ρ x =
      ∫ p, ρ p.1 * ρ p.2 * newtonKernel (p.1 - p.2) ∂(volume.prod volume) :=
  integral_mul_newtonPotential_eq_double hρ hcρ

example (f : E3 → ℝ) (x : E3) :
    ℝ :=
  gradientNormSq f x

example (L : E3 →L[ℝ] ℝ) (i : Fin 3) :
    |L (EuclideanSpace.single i 1)| ≤ ‖L‖ :=
  abs_apply_single_le L i

example (f : E3 → ℝ) (x : E3) :
    gradientNormSq f x ≤ 3 * ‖fderiv ℝ f x‖ ^ 2 :=
  gradientNormSq_le f x

example (f : E3 → ℝ) (x : E3) :
    0 ≤ gradientNormSq f x :=
  gradientNormSq_nonneg f x

example :
    Integrable fun x : E3 => ((1 + ‖x‖) ^ 4)⁻¹ :=
  integrable_inv_one_add_norm_pow_four

example {ρ : E3 → ℝ} (hρ : ContDiff ℝ 1 ρ) (hcρ : HasCompactSupport ρ) :
    Integrable (gradientNormSq (newtonPotential ρ)) :=
  integrable_gradientNormSq_newtonPotential hρ hcρ

example :
    ContDiffBump (0 : E3) :=
  unitBump

example (R : ℝ) (x : E3) :
    ℝ :=
  cutoff R x

example (R : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (cutoff R) :=
  contDiff_cutoff R

example (R : ℝ) :
    ContDiff ℝ 1 (cutoff R) :=
  contDiff_one_cutoff R

example (R : ℝ) :
    Continuous (cutoff R) :=
  continuous_cutoff R

example {R : ℝ} (hR : R ≠ 0) :
    HasCompactSupport (cutoff R) :=
  hasCompactSupport_cutoff hR

example {R : ℝ} (hR : 0 < R) {x : E3} (hx : ‖x‖ ≤ R) :
    cutoff R x = 1 :=
  cutoff_eq_one hR hx

example (R : ℝ) (x : E3) :
    cutoff R x ∈ Icc (0 : ℝ) 1 :=
  cutoff_mem_Icc R x

example {R : ℝ} (hR : 0 < R) {x : E3} (hx : ‖x‖ < R) :
    fderiv ℝ (cutoff R) x = 0 :=
  fderiv_cutoff_eq_zero hR hx

example (R : ℝ) (x : E3) :
    fderiv ℝ (cutoff R) x = R⁻¹ • fderiv ℝ unitBump (R⁻¹ • x) :=
  fderiv_cutoff R x

example :
    ∃ C, ∀ R, 1 ≤ R → ∀ x, ‖fderiv ℝ (cutoff R) x‖ ≤ C * (1 + ‖x‖)⁻¹ :=
  exists_norm_fderiv_cutoff_le

example {ρ : E3 → ℝ} (hρ : ContDiff ℝ 2 ρ) (hcρ : HasCompactSupport ρ) :
    ∫ x, ρ x * newtonPotential ρ x = ∫ x, gradientNormSq (newtonPotential ρ) x :=
  integral_mul_newtonPotential_eq_integral_sq hρ hcρ

example (ρ : E3 → ℝ) (x : E3) :
    ∑ i, coulombField ρ x i ^ 2 = gradientNormSq (newtonPotential ρ) x :=
  sum_sq_coulombField ρ x

example {ρ : E3 → ℝ} (hρ : ContDiff ℝ 2 ρ) (hcρ : HasCompactSupport ρ) :
    (Integrable (fun x => ρ x * newtonPotential ρ x) ∧
      Integrable (fun p : E3 × E3 => ρ p.1 * ρ p.2 * newtonKernel (p.1 - p.2))
        (volume.prod volume) ∧
      Integrable fun x => (∑ i, coulombField ρ x i ^ 2) / 2) ∧
    (1 / 2 * ∫ x, ρ x * newtonPotential ρ x =
      1 / 2 * ∫ p, ρ p.1 * ρ p.2 * newtonKernel (p.1 - p.2) ∂(volume.prod volume)) ∧
    1 / 2 * ∫ x, ρ x * newtonPotential ρ x = ∫ x, (∑ i, coulombField ρ x i ^ 2) / 2 :=
  electrostaticEnergy_eq hρ hcρ

example (x : E3) :
    ℝ :=
  bumpCharge x

example :
    ContDiff ℝ 2 bumpCharge :=
  contDiff_bumpCharge

example :
    HasCompactSupport bumpCharge :=
  hasCompactSupport_bumpCharge

example :
    bumpCharge 0 = 1 :=
  bumpCharge_zero

example :
    (∀ y, divergence3 (electricField (fieldTensor (electrostaticPotential bumpCharge))) y =
      bumpCharge (SmoothGeometry.Minkowski.space y)) ∧
    1 / 2 * ∫ x, bumpCharge x * newtonPotential bumpCharge x =
      ∫ x, (∑ i, coulombField bumpCharge x i ^ 2) / 2 :=
  bumpCharge_instance

example (q : ℝ) {x : E3} (hx : x ≠ 0) :
    ‖pointChargeField q x‖ ^ 2 = q ^ 2 / (16 * π ^ 2 * ‖x‖ ^ 4) :=
  norm_sq_pointChargeField q hx

example (q : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ x in {x : E3 | ε < ‖x‖}, ‖pointChargeField q x‖ ^ 2 / 2 = q ^ 2 / (8 * π * ε) :=
  integral_pointCharge_energy_outside q hε

example {q : ℝ} (hq : q ≠ 0) :
    Tendsto (fun ε => ∫ x in {x : E3 | ε < ‖x‖}, ‖pointChargeField q x‖ ^ 2 / 2) (𝓝[>] 0)
      atTop :=
  tendsto_pointCharge_energy hq

example {q : ℝ} (hq : q ≠ 0) :
    ¬ Integrable fun x : E3 => ‖pointChargeField q x‖ ^ 2 / 2 :=
  not_integrable_pointCharge_energy hq

end ProjectAinos.Electrodynamics.Electrostatics

end ElectrostaticEnergy
