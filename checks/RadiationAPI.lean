/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Euclidean.SphereIntegral
import ProjectAinos.SmoothGeometry.Wave.FarField
import ProjectAinos.Electrodynamics.Radiation.Basic
import ProjectAinos.Electrodynamics.Radiation.FarZone
import ProjectAinos.Electrodynamics.Radiation.NearZone
import ProjectAinos.Electrodynamics.Radiation.Dipole
import ProjectAinos.Electrodynamics.Radiation.Multipole
import ProjectAinos.Electrodynamics.Radiation.Relativistic
import ProjectAinos.Electrodynamics.Radiation.Synchrotron
import ProjectAinos.Electrodynamics.Radiation.Ultrarelativistic

/-! Public consumers of the radiation of a localized source and of a fast charge
(Landau–Lifshitz §§66, 67, 71–74, 77): the integrals over the unit sphere (moments, Archimedes),
the far-field amplitude of the retarded integral with uniform limits and rates, the fields at
large distances and the limit of the Poynting flux through large spheres, the exact field of a
point dipole with the split of its flux into the radiated power and a near-zone energy, the dipole,
quadrupole and magnetic-dipole powers of a slow source with explicit remainders, the angular
distribution and Liénard's formula for a fast charge, the synchrotron power with the loss per turn,
and the angular concentration in the ultrarelativistic case. Default elaborator options are
intentional: these checks must not rely on the implementation's transparency settings. Every
statement is pinned with its type. -/

noncomputable section


section SphereIntegral

open MeasureTheory Set Metric Real

open scoped Pointwise

namespace ProjectAinos.SmoothGeometry.Sphere

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example :
    Measure (sphere (0 : E3) 1) :=
  sphereMeasure

example :
    sphereMeasure.real univ = 4 * π :=
  sphereMeasure_real_univ

example {f : sphere (0 : E3) 1 → ℝ} (hf : Continuous f) :
    Integrable f sphereMeasure :=
  integrable_of_continuous hf

example (L : E3 ≃ₗᵢ[ℝ] E3) :
    sphere (0 : E3) 1 ≃ᵐ sphere (0 : E3) 1 :=
  sphereMap L

example (L : E3 ≃ₗᵢ[ℝ] E3) :
    MeasurePreserving (sphereMap L) sphereMeasure sphereMeasure :=
  measurePreserving_sphereMap L

example {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E3 ≃ₗᵢ[ℝ] E3) (f : E3 → G) :
    ∫ n : sphere (0 : E3) 1, f (L n) ∂sphereMeasure =
      ∫ n : sphere (0 : E3) 1, f n ∂sphereMeasure :=
  integral_comp_linearIsometryEquiv L f

example {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E3 ≃ₗᵢ[ℝ] E3) {f : E3 → G}
    (hf : ∀ x, f (L x) = -f x) :
    ∫ n : sphere (0 : E3) 1, f n ∂sphereMeasure = 0 :=
  integral_eq_zero_of_comp_eq_neg L hf

example {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E3 → G}
    (hf : ∀ x, f (-x) = -f x) :
    ∫ n : sphere (0 : E3) 1, f n ∂sphereMeasure = 0 :=
  integral_eq_zero_of_odd hf

example (a : E3) :
    ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) a ∂sphereMeasure = 0 :=
  integral_inner a

example (a b c : E3) :
    ∫ n : sphere (0 : E3) 1,
      inner ℝ (n : E3) a * inner ℝ (n : E3) b * inner ℝ (n : E3) c ∂sphereMeasure = 0 :=
  integral_inner_mul_inner_mul_inner a b c

example {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {e e' : E3} (h : ‖e‖ = ‖e'‖)
    (F : ℝ → G) :
    ∫ n : sphere (0 : E3) 1, F (inner ℝ (n : E3) e) ∂sphereMeasure =
      ∫ n : sphere (0 : E3) 1, F (inner ℝ (n : E3) e') ∂sphereMeasure :=
  integral_comp_inner_of_norm_eq h F

example (F : E3 → ℝ) (f : sphere (0 : E3) 1 → ℝ) (h : ℝ → ℝ)
    (hF : ∀ (n : sphere (0 : E3) 1) (r : ℝ), 0 < r → F (r • (n : E3)) = f n * h r) :
    ∫ x, F x = (∫ n, f n ∂sphereMeasure) * ∫ r in Ioi (0 : ℝ), r ^ 2 * h r :=
  integral_eq_integral_sphere_mul F f h hF

example {e : E3} (he : ‖e‖ = 1) (n : sphere (0 : E3) 1) :
    inner ℝ (n : E3) e ∈ Icc (-1 : ℝ) 1 :=
  inner_mem_Icc he n

example {e : E3} (he : ‖e‖ = 1) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (-1) 1)) :
    Continuous fun n : sphere (0 : E3) 1 => g (inner ℝ (n : E3) e) :=
  continuous_comp_inner he hg

example {e : E3} (he : ‖e‖ = 1) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (-1) 1)) :
    ∫ n : sphere (0 : E3) 1, g (inner ℝ (n : E3) e) ∂sphereMeasure =
      2 * π * ∫ s in (-1 : ℝ)..1, g s :=
  integral_comp_inner he hg

example (a : E3) (k : ℕ) :
    ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) a ^ k ∂sphereMeasure =
      ‖a‖ ^ k * (2 * π * ∫ s in (-1 : ℝ)..1, s ^ k) :=
  integral_inner_pow a k

example (a : E3) :
    ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) a ^ 2 ∂sphereMeasure = 4 * π / 3 * ‖a‖ ^ 2 :=
  integral_inner_sq a

example (a : E3) :
    ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) a ^ 4 ∂sphereMeasure =
      4 * π / 5 * (‖a‖ ^ 2) ^ 2 :=
  integral_inner_pow_four a

example (a b : E3) :
    ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) a * inner ℝ (n : E3) b ∂sphereMeasure =
      4 * π / 3 * inner ℝ a b :=
  integral_inner_mul_inner a b

example (a b c d : E3) :
    ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) a * inner ℝ (n : E3) b * inner ℝ (n : E3) c *
      inner ℝ (n : E3) d ∂sphereMeasure =
      4 * π / 15 * (inner ℝ a b * inner ℝ c d + inner ℝ a c * inner ℝ b d +
        inner ℝ a d * inner ℝ b c) :=
  integral_inner_mul_inner_mul_inner_mul_inner a b c d

example {e w : E3} (he : ‖e‖ = 1) (hw : inner ℝ w e = 0) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc (-1) 1)) :
    ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) w * g (inner ℝ (n : E3) e) ∂sphereMeasure = 0 :=
  integral_inner_mul_comp_inner he hw hg

example {e w : E3} (he : ‖e‖ = 1) (hw : inner ℝ w e = 0) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc (-1) 1)) :
    ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) w ^ 2 * g (inner ℝ (n : E3) e) ∂sphereMeasure =
      ‖w‖ ^ 2 / 2 * ∫ n : sphere (0 : E3) 1, (1 - inner ℝ (n : E3) e ^ 2) *
        g (inner ℝ (n : E3) e) ∂sphereMeasure :=
  integral_inner_sq_mul_comp_inner he hw hg

example {e w₁ w₂ : E3} (he : ‖e‖ = 1) (hw₁ : inner ℝ w₁ e = 0) (hw₂ : inner ℝ w₂ e = 0)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (-1) 1)) :
    ∫ n : sphere (0 : E3) 1,
      inner ℝ (n : E3) w₁ * inner ℝ (n : E3) w₂ * g (inner ℝ (n : E3) e) ∂sphereMeasure =
      inner ℝ w₁ w₂ / 2 *
        ∫ n : sphere (0 : E3) 1, (1 - inner ℝ (n : E3) e ^ 2) * g (inner ℝ (n : E3) e)
          ∂sphereMeasure :=
  integral_inner_mul_inner_mul_comp_inner he hw₁ hw₂ hg

end ProjectAinos.SmoothGeometry.Sphere

end SphereIntegral

section Basic

open MeasureTheory Set Metric Real

namespace ProjectAinos.Electrodynamics.Radiation

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Sphere SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (S : Fin 3 → Spacetime → ℝ) (t R : ℝ) :
    ℝ :=
  sphereFlux S t R

example (k : Spacetime → Spacetime) :
    Spacetime → Spacetime :=
  currentRate k

example (k : Spacetime → Spacetime) (u : ℝ) (n : E3) (μ : Fin 4) :
    ℝ :=
  radiationAmplitude k u n μ

example (k : Spacetime → Spacetime) (u : ℝ) :
    ℝ :=
  radiatedPower k u

end ProjectAinos.Electrodynamics.Radiation

end Basic

section FarField

open MeasureTheory Filter Set Metric Real

open scoped Topology

namespace ProjectAinos.SmoothGeometry.Wave

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example {G : Type*} [Zero G] (a : ℝ) (f : ℝ × E3 → G) :
    Prop :=
  LocalizedSupport a f

example {G : Type*} [Zero G] {a b : ℝ} {f : ℝ × E3 → G} (hf : LocalizedSupport a f) (hab : a ≤ b) :
    LocalizedSupport b f :=
  LocalizedSupport.mono hf hab

example {G G' : Type*} [Zero G] [Zero G'] {a : ℝ} {f : ℝ × E3 → G} (hf : LocalizedSupport a f)
    {g : G → G'} (hg : g 0 = 0) :
    LocalizedSupport a fun p => g (f p) :=
  LocalizedSupport.comp hf hg

example {G : Type*} [NormedAddCommGroup G] {a : ℝ} {f : ℝ × E3 → G} (hf : LocalizedSupport a f) :
    SubluminalSupport a 0 f :=
  LocalizedSupport.subluminalSupport hf

example {G : Type*} [NormedAddCommGroup G] {a : ℝ} {f : ℝ × E3 → G} (hf : SubluminalSupport a 0 f) :
    LocalizedSupport a f :=
  SubluminalSupport.localizedSupport hf

example :
    LocalizedSupport 2 fun p : ℝ × E3 => spaceBump p.2 :=
  localizedSupport_spaceBump

example {a : ℝ} {f : ℝ × E3 → ℝ} (hf : LocalizedSupport a f) {t : ℝ} {y : E3} (hy : a < ‖y‖) :
    fderiv ℝ f (t, y) = 0 :=
  LocalizedSupport.fderiv_eq_zero hf hy

example {a : ℝ} {f : ℝ × E3 → ℝ} (hf : LocalizedSupport a f) :
    LocalizedSupport a (timeDeriv f) :=
  LocalizedSupport.timeDeriv hf

example {a : ℝ} {f : ℝ × E3 → ℝ} (hf : LocalizedSupport a f) (i : Fin 3) :
    LocalizedSupport a (spaceDeriv i f) :=
  LocalizedSupport.spaceDeriv hf i

example (f : ℝ × E3 → ℝ) (u : ℝ) (n : E3) :
    ℝ :=
  farAmplitude f u n

example {a : ℝ} {f : ℝ × E3 → ℝ} (hf : LocalizedSupport a f) (u : ℝ) (n : E3) :
    HasCompactSupport fun y : E3 => f (u + inner ℝ n y, y) :=
  hasCompactSupport_farIntegrand hf u n

example {a : ℝ} {f : ℝ × E3 → ℝ} (hc : Continuous f) (hf : LocalizedSupport a f) (u : ℝ) (n : E3) :
    Integrable fun y : E3 => f (u + inner ℝ n y, y) :=
  integrable_farIntegrand hc hf u n

example {a M u : ℝ} {n : E3} {f : ℝ × E3 → ℝ} (hf : LocalizedSupport a f)
    (hM : ∀ z : E3, ‖z‖ ≤ a → |f (u + inner ℝ n z, z)| ≤ M) :
    |farAmplitude f u n| ≤ (4 * π)⁻¹ * M * volume.real (closedBall (0 : E3) a) :=
  abs_farAmplitude_le hf hM

example {a R : ℝ} {n z : E3} (hn : ‖n‖ = 1) (hz : ‖z‖ ≤ a) (hR : 2 * a ≤ R) (hR0 : 0 < R) :
    R / 2 ≤ ‖R • n - z‖ ∧ |R - ‖R • n - z‖| ≤ a ∧ 0 ≤ ‖R • n - z‖ - R + inner ℝ n z ∧
      ‖R • n - z‖ - R + inner ℝ n z ≤ a ^ 2 / R :=
  norm_smul_sub_estimates hn hz hR hR0

example (f : ℝ × E3 → ℝ) (t : ℝ) (x : E3) :
    retardedIntegral f (t, x) = ∫ z, (4 * π * ‖x - z‖)⁻¹ * f (t - ‖x - z‖, z) :=
  retardedIntegral_eq_integral f t x

example {a R η M u : ℝ} {n : E3} {f : ℝ × E3 → ℝ} (hc : Continuous f) (hf : LocalizedSupport a f)
    (ha : 0 ≤ a) (hR0 : 0 < R) (hR : 2 * a ≤ R) (hn : ‖n‖ = 1)
    (hη : ∀ z : E3, ‖z‖ ≤ a → ∀ s : ℝ, 0 ≤ s → s ≤ a ^ 2 / R →
      |f (u + inner ℝ n z - s, z) - f (u + inner ℝ n z, z)| ≤ η)
    (hM : ∀ z : E3, ‖z‖ ≤ a → |f (u + inner ℝ n z, z)| ≤ M) :
    |R * retardedIntegral f (u + R, R • n) - farAmplitude f u n| ≤
      (4 * π)⁻¹ * (2 * η + 2 * a * M / R) * volume.real (closedBall (0 : E3) a) :=
  abs_mul_retardedIntegral_sub_le hc hf ha hR0 hR hn hη hM

example {a : ℝ} {f : ℝ × E3 → ℝ} (hc : Continuous f) (hf : LocalizedSupport a f) {K : Set ℝ}
    (hK : IsCompact K) :
    TendstoUniformlyOn (fun R (p : ℝ × E3) => R * retardedIntegral f (p.1 + R, R • p.2))
      (fun p => farAmplitude f p.1 p.2) atTop (K ×ˢ sphere (0 : E3) 1) :=
  tendstoUniformlyOn_mul_retardedIntegral hc hf hK

example {f : ℝ × E3 → ℝ} (hf : Differentiable ℝ f) (t : ℝ) (z : E3) :
    HasDerivAt (fun s => f (s, z)) (timeDeriv f (t, z)) t :=
  hasDerivAt_timeSlice hf t z

example {a : ℝ} {f : ℝ × E3 → ℝ} (hc : ContDiff ℝ 1 f) (hf : LocalizedSupport a f) {K : Set ℝ}
    (hK : IsCompact K) :
    ∃ C, ∀ᶠ R in atTop, ∀ u ∈ K, ∀ n ∈ sphere (0 : E3) 1,
      |R * retardedIntegral f (u + R, R • n) - farAmplitude f u n| ≤ C / R :=
  exists_bound_mul_retardedIntegral_sub hc hf hK

example {a : ℝ} {f : ℝ × E3 → ℝ} (hc : Continuous f) (hf : LocalizedSupport a f) {K : Set ℝ}
    (hK : IsCompact K) :
    ∃ M, ∀ u ∈ K, ∀ n ∈ sphere (0 : E3) 1, |farAmplitude f u n| ≤ M :=
  exists_bound_farAmplitude hc hf hK

example {a : ℝ} {f : ℝ × E3 → ℝ} (hc : ContDiff ℝ 1 f) (hf : LocalizedSupport a f) (i : Fin 3)
    (u : ℝ) (n : E3) :
    farAmplitude (spaceDeriv i f) u n = -(n i * farAmplitude (timeDeriv f) u n) :=
  farAmplitude_spaceDeriv hc hf i u n

example {a : ℝ} {f : ℝ × E3 → ℝ} (hc : ContDiff ℝ 1 f) (hf : LocalizedSupport a f) {K : Set ℝ}
    (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun R (p : ℝ × E3) => R * timeDeriv (retardedIntegral f) (p.1 + R, R • p.2))
      (fun p => farAmplitude (timeDeriv f) p.1 p.2) atTop (K ×ˢ sphere (0 : E3) 1) :=
  tendstoUniformlyOn_mul_timeDeriv_retardedIntegral hc hf hK

example {a : ℝ} {f : ℝ × E3 → ℝ} (hc : ContDiff ℝ 1 f) (hf : LocalizedSupport a f) {K : Set ℝ}
    (hK : IsCompact K) (i : Fin 3) :
    TendstoUniformlyOn
      (fun R (p : ℝ × E3) => R * spaceDeriv i (retardedIntegral f) (p.1 + R, R • p.2))
      (fun p => -(p.2 i * farAmplitude (timeDeriv f) p.1 p.2)) atTop
      (K ×ˢ sphere (0 : E3) 1) :=
  tendstoUniformlyOn_mul_spaceDeriv_retardedIntegral hc hf hK i

example {a : ℝ} {f : ℝ × E3 → ℝ} (hc : ContDiff ℝ 2 f) (hf : LocalizedSupport a f) {K : Set ℝ}
    (hK : IsCompact K) :
    ∃ C, ∀ᶠ R in atTop, ∀ u ∈ K, ∀ n ∈ sphere (0 : E3) 1,
      |R * timeDeriv (retardedIntegral f) (u + R, R • n) - farAmplitude (timeDeriv f) u n| ≤
        C / R :=
  exists_bound_mul_timeDeriv_retardedIntegral_sub hc hf hK

example {a : ℝ} {f : ℝ × E3 → ℝ} (hc : ContDiff ℝ 2 f) (hf : LocalizedSupport a f) {K : Set ℝ}
    (hK : IsCompact K) (i : Fin 3) :
    ∃ C, ∀ᶠ R in atTop, ∀ u ∈ K, ∀ n ∈ sphere (0 : E3) 1,
      |R * spaceDeriv i (retardedIntegral f) (u + R, R • n) +
        n i * farAmplitude (timeDeriv f) u n| ≤ C / R :=
  exists_bound_mul_spaceDeriv_retardedIntegral_add hc hf hK i

end ProjectAinos.SmoothGeometry.Wave

end FarField

section FarZone

open MeasureTheory Filter Set Metric Real

open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics.Radiation

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Sphere SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (k : Spacetime → Spacetime) (μ : Fin 4) :
    ℝ × E3 → ℝ :=
  splitComponent k μ

example (k : Spacetime → Spacetime) (u : ℝ) (n : E3) :
    Fin 3 → ℝ :=
  amplitudeRate k u n

example (k : Spacetime → Spacetime) (u : ℝ) (n : E3) :
    Fin 3 → ℝ :=
  farMagnetic k u n

example (k : Spacetime → Spacetime) (u : ℝ) (n : E3) :
    Fin 3 → ℝ :=
  farElectric k u n

example {n : E3} (hn : ‖n‖ = 1) :
    n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 :=
  sum_sq_of_norm_eq_one hn

example (k : Spacetime → Spacetime) (u : ℝ) {n : E3} (hn : ‖n‖ = 1) :
    farElectric k u n = crossProduct (farMagnetic k u n) ⇑n :=
  farElectric_eq_cross k u hn

example (e b : Fin 3 → ℝ) (n : E3) :
    ℝ :=
  radialCross e b n

example (e b : Fin 3 → ℝ) (n : E3) :
    radialCross e b n = (e 1 * b 2 - e 2 * b 1) * n 0 + (e 2 * b 0 - e 0 * b 2) * n 1 +
      (e 0 * b 1 - e 1 * b 0) * n 2 :=
  radialCross_eq e b n

example (k : Spacetime → Spacetime) (u : ℝ) {n : E3} (hn : ‖n‖ = 1) :
    radialCross (farElectric k u n) (farMagnetic k u n) n =
      (∑ i : Fin 3, radiationAmplitude (currentRate k) u n i.succ ^ 2) -
        (∑ i : Fin 3, n i * radiationAmplitude (currentRate k) u n i.succ) ^ 2 :=
  farPoynting_eq k u hn

example {g : Spacetime → ℝ} (hg : ContDiff ℝ 1 g) {ρ v₀ : ℝ}
    (hs : Wave.SubluminalSupport ρ v₀ fun p => g (Wave.timeSpaceEquiv.symm p)) (v : Spacetime) :
    partialAt (retardedScalar g) 0 v =
      Wave.timeDeriv (Wave.retardedIntegral fun p => g (Wave.timeSpaceEquiv.symm p))
        (Wave.timeSpaceEquiv v) :=
  partialAt_retardedScalar_zero hg hs v

example {g : Spacetime → ℝ} (hg : ContDiff ℝ 1 g) {ρ v₀ : ℝ}
    (hs : Wave.SubluminalSupport ρ v₀ fun p => g (Wave.timeSpaceEquiv.symm p)) (i : Fin 3)
    (v : Spacetime) :
    partialAt (retardedScalar g) i.succ v =
      Wave.spaceDeriv i (Wave.retardedIntegral fun p => g (Wave.timeSpaceEquiv.symm p))
        (Wave.timeSpaceEquiv v) :=
  partialAt_retardedScalar_succ hg hs i v

example {g : Spacetime → ℝ} (hg : Differentiable ℝ g) (p : ℝ × E3) :
    Wave.timeDeriv (fun q => g (Wave.timeSpaceEquiv.symm q)) p =
      partialAt g 0 (Wave.timeSpaceEquiv.symm p) :=
  timeDeriv_comp_symm hg p

example {g : Spacetime → ℝ} (hg : Differentiable ℝ g) (i : Fin 3) (p : ℝ × E3) :
    Wave.spaceDeriv i (fun q => g (Wave.timeSpaceEquiv.symm q)) p =
      partialAt g i.succ (Wave.timeSpaceEquiv.symm p) :=
  spaceDeriv_comp_symm hg i p

example {n : ℕ∞ω} {k : Spacetime → Spacetime} (hk : ContDiff ℝ n k) (μ : Fin 4) :
    ContDiff ℝ n (splitComponent k μ) :=
  contDiff_splitComponent hk μ

example {k : Spacetime → Spacetime} {a : ℝ}
    (hloc : Wave.LocalizedSupport a fun p => k (Wave.timeSpaceEquiv.symm p)) (μ : Fin 4) :
    Wave.LocalizedSupport a (splitComponent k μ) :=
  localizedSupport_splitComponent hloc μ

example {k : Spacetime → Spacetime} (hk : Differentiable ℝ k) (μ : Fin 4) (p : ℝ × E3) :
    Wave.timeDeriv (splitComponent k μ) p = currentRate k (Wave.timeSpaceEquiv.symm p) μ :=
  timeDeriv_splitComponent hk μ p

example {k : Spacetime → Spacetime} (hk : Differentiable ℝ k) (μ : Fin 4) (i : Fin 3) (p : ℝ × E3) :
    Wave.spaceDeriv i (splitComponent k μ) p =
      partialAt (fun w => k w μ) i.succ (Wave.timeSpaceEquiv.symm p) :=
  spaceDeriv_splitComponent hk μ i p

example {k : Spacetime → Spacetime} (hk : Differentiable ℝ k) (μ : Fin 4) (u : ℝ) (n : E3) :
    Wave.farAmplitude (Wave.timeDeriv (splitComponent k μ)) u n =
      radiationAmplitude (currentRate k) u n μ :=
  farAmplitude_timeDeriv_splitComponent hk μ u n

example {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k) {ρ v₀ : ℝ}
    (hs : Wave.SubluminalSupport ρ v₀ fun p => k (Wave.timeSpaceEquiv.symm p)) (i : Fin 3) (t : ℝ)
    (x : E3) :
    electricField (fieldTensor (retardedPotential k)) i (vector t x) =
      -Wave.spaceDeriv i (Wave.retardedIntegral (splitComponent k 0)) (t, x) -
        Wave.timeDeriv (Wave.retardedIntegral (splitComponent k i.succ)) (t, x) :=
  electricField_retardedPotential hk hs i t x

example {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k) {ρ v₀ : ℝ}
    (hs : Wave.SubluminalSupport ρ v₀ fun p => k (Wave.timeSpaceEquiv.symm p)) (t : ℝ) (x : E3) :
    magneticField (fieldTensor (retardedPotential k)) 0 (vector t x) =
        Wave.spaceDeriv 1 (Wave.retardedIntegral (splitComponent k 3)) (t, x) -
          Wave.spaceDeriv 2 (Wave.retardedIntegral (splitComponent k 2)) (t, x) ∧
      magneticField (fieldTensor (retardedPotential k)) 1 (vector t x) =
        Wave.spaceDeriv 2 (Wave.retardedIntegral (splitComponent k 1)) (t, x) -
          Wave.spaceDeriv 0 (Wave.retardedIntegral (splitComponent k 3)) (t, x) ∧
      magneticField (fieldTensor (retardedPotential k)) 2 (vector t x) =
        Wave.spaceDeriv 0 (Wave.retardedIntegral (splitComponent k 2)) (t, x) -
          Wave.spaceDeriv 1 (Wave.retardedIntegral (splitComponent k 1)) (t, x) :=
  magneticField_retardedPotential hk hs t x

example {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k) {a : ℝ}
    (hloc : Wave.LocalizedSupport a fun p => k (Wave.timeSpaceEquiv.symm p))
    (hdiv : ∀ v, divergence4 k v = 0) (u : ℝ) (n : E3) :
    radiationAmplitude (currentRate k) u n 0 = ∑ i, n i * amplitudeRate k u n i :=
  radiationAmplitude_currentRate_zero hk hloc hdiv u n

example {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k) {a : ℝ}
    (hloc : Wave.LocalizedSupport a fun p => k (Wave.timeSpaceEquiv.symm p))
    (hdiv : ∀ v, divergence4 k v = 0) {K : Set ℝ} (hK : IsCompact K) (i : Fin 3) :
    TendstoUniformlyOn
      (fun R (p : ℝ × E3) =>
        R * electricField (fieldTensor (retardedPotential k)) i (vector (p.1 + R) (R • p.2)))
      (fun p => farElectric k p.1 p.2 i) atTop (K ×ˢ sphere (0 : E3) 1) :=
  tendstoUniformlyOn_mul_electricField hk hloc hdiv hK i

example {k : Spacetime → Spacetime} (hk : ContDiff ℝ 1 k) {a : ℝ}
    (hloc : Wave.LocalizedSupport a fun p => k (Wave.timeSpaceEquiv.symm p)) {K : Set ℝ}
    (hK : IsCompact K) (j : Fin 3) (μ : Fin 4) :
    TendstoUniformlyOn
      (fun R (p : ℝ × E3) =>
        R * Wave.spaceDeriv j (Wave.retardedIntegral (splitComponent k μ)) (p.1 + R, R • p.2))
      (fun p => -(p.2 j * radiationAmplitude (currentRate k) p.1 p.2 μ)) atTop
      (K ×ˢ sphere (0 : E3) 1) :=
  tendstoUniformlyOn_mul_spaceDeriv_splitComponent hk hloc hK j μ

example {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k) {a : ℝ}
    (hloc : Wave.LocalizedSupport a fun p => k (Wave.timeSpaceEquiv.symm p)) {K : Set ℝ}
    (hK : IsCompact K) (i : Fin 3) :
    TendstoUniformlyOn
      (fun R (p : ℝ × E3) =>
        R * magneticField (fieldTensor (retardedPotential k)) i (vector (p.1 + R) (R • p.2)))
      (fun p => farMagnetic k p.1 p.2 i) atTop (K ×ˢ sphere (0 : E3) 1) :=
  tendstoUniformlyOn_mul_magneticField hk hloc hK i

example {n : E3} (hn : n ∈ sphere (0 : E3) 1) (i : Fin 3) :
    |n i| ≤ 1 :=
  abs_apply_le_one hn i

example {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k) {a : ℝ}
    (hloc : Wave.LocalizedSupport a fun p => k (Wave.timeSpaceEquiv.symm p)) (u : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ n ∈ sphere (0 : E3) 1, ∀ j, |amplitudeRate k u n j| ≤ M :=
  exists_bound_amplitudeRate hk hloc u

example {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k) {a : ℝ}
    (hloc : Wave.LocalizedSupport a fun p => k (Wave.timeSpaceEquiv.symm p))
    (hdiv : ∀ v, divergence4 k v = 0) (u : ℝ) :
    Tendsto (fun R => sphereFlux (poyntingVector (fieldTensor (retardedPotential k))) (u + R) R)
      atTop (𝓝 (radiatedPower k u)) :=
  tendsto_sphereFlux_poynting hk hloc hdiv u

example {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k) {a : ℝ}
    (hloc : Wave.LocalizedSupport a fun p => k (Wave.timeSpaceEquiv.symm p)) {K : Set ℝ}
    (hK : IsCompact K) (j : Fin 3) (μ : Fin 4) :
    ∃ C, ∀ᶠ R in atTop, ∀ u ∈ K, ∀ n ∈ sphere (0 : E3) 1,
      |R * Wave.spaceDeriv j (Wave.retardedIntegral (splitComponent k μ)) (u + R, R • n) +
        n j * radiationAmplitude (currentRate k) u n μ| ≤ C / R :=
  exists_bound_mul_spaceDeriv_splitComponent_add hk hloc hK j μ

example {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k) {a : ℝ}
    (hloc : Wave.LocalizedSupport a fun p => k (Wave.timeSpaceEquiv.symm p))
    (hdiv : ∀ v, divergence4 k v = 0) {K : Set ℝ} (hK : IsCompact K) (i : Fin 3) :
    ∃ C, ∀ᶠ R in atTop, ∀ u ∈ K, ∀ n ∈ sphere (0 : E3) 1,
      |R * electricField (fieldTensor (retardedPotential k)) i (vector (u + R) (R • n)) -
        farElectric k u n i| ≤ C / R :=
  exists_bound_mul_electricField_sub hk hloc hdiv hK i

example {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k) {a : ℝ}
    (hloc : Wave.LocalizedSupport a fun p => k (Wave.timeSpaceEquiv.symm p)) {K : Set ℝ}
    (hK : IsCompact K) (i : Fin 3) :
    ∃ C, ∀ᶠ R in atTop, ∀ u ∈ K, ∀ n ∈ sphere (0 : E3) 1,
      |R * magneticField (fieldTensor (retardedPotential k)) i (vector (u + R) (R • n)) -
        farMagnetic k u n i| ≤ C / R :=
  exists_bound_mul_magneticField_sub hk hloc hK i

example {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k) {a : ℝ}
    (hloc : Wave.LocalizedSupport a fun p => k (Wave.timeSpaceEquiv.symm p))
    (hdiv : ∀ v, divergence4 k v = 0) {K : Set ℝ} (hK : IsCompact K) :
    ∃ C, ∀ᶠ R in atTop, ∀ u ∈ K, ∀ n ∈ sphere (0 : E3) 1, ∀ i : Fin 3,
      |electricField (fieldTensor (retardedPotential k)) i (vector (u + R) (R • n)) -
        crossProduct (fun j => magneticField (fieldTensor (retardedPotential k)) j
          (vector (u + R) (R • n))) ⇑n i| ≤ C / R ^ 2 :=
  exists_bound_electricField_sub_cross hk hloc hdiv hK

example :
    ∃ a, Wave.LocalizedSupport a fun p => circulatingCurrent (Wave.timeSpaceEquiv.symm p) :=
  localizedSupport_circulatingCurrent

example {K : Set ℝ} (hK : IsCompact K) (i : Fin 3) :
    TendstoUniformlyOn
        (fun R (p : ℝ × E3) => R * electricField (fieldTensor
          (retardedPotential circulatingCurrent)) i (vector (p.1 + R) (R • p.2)))
        (fun p => farElectric circulatingCurrent p.1 p.2 i) atTop (K ×ˢ sphere (0 : E3) 1) ∧
      TendstoUniformlyOn
        (fun R (p : ℝ × E3) => R * magneticField (fieldTensor
          (retardedPotential circulatingCurrent)) i (vector (p.1 + R) (R • p.2)))
        (fun p => farMagnetic circulatingCurrent p.1 p.2 i) atTop (K ×ˢ sphere (0 : E3) 1) :=
  tendstoUniformlyOn_mul_field_circulatingCurrent hK i

example (u : ℝ) :
    Tendsto (fun R => sphereFlux (poyntingVector (fieldTensor
      (retardedPotential circulatingCurrent))) (u + R) R) atTop
      (𝓝 (radiatedPower circulatingCurrent u)) :=
  tendsto_sphereFlux_poynting_circulatingCurrent u

example {K : Set ℝ} (hK : IsCompact K) :
    ∃ C, ∀ᶠ R in atTop, ∀ u ∈ K, ∀ n ∈ sphere (0 : E3) 1, ∀ i : Fin 3,
      |electricField (fieldTensor (retardedPotential circulatingCurrent)) i
          (vector (u + R) (R • n)) -
        crossProduct (fun j => magneticField (fieldTensor (retardedPotential circulatingCurrent))
          j (vector (u + R) (R • n))) ⇑n i| ≤ C / R ^ 2 :=
  exists_bound_electricField_sub_cross_circulatingCurrent hK

end ProjectAinos.Electrodynamics.Radiation

end FarZone

section NearZone

open MeasureTheory Set Metric Real Filter

open scoped Topology ContDiff RealInnerProductSpace

namespace ProjectAinos.Electrodynamics.Radiation.NearZone

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Sphere SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example :
    Set Spacetime :=
  offOrigin

example :
    IsOpen offOrigin :=
  isOpen_offOrigin

example :
    space (Pi.single 0 1 : Spacetime) = 0 :=
  space_single_zero

example (i : Fin 3) :
    space (Pi.single i.succ 1 : Spacetime) = EuclideanSpace.single i 1 :=
  space_single_succ i

example (ν μ : Fin 4) (v : Spacetime) :
    partialAt (fun w : Spacetime => w ν) μ v = (Pi.single μ 1 : Spacetime) ν :=
  partialAt_coord ν μ v

example {v : Spacetime} (hv : space v ≠ 0) :
    HasFDerivAt (fun w : Spacetime => ‖space w‖)
      ((‖space v‖⁻¹ • innerSL ℝ (space v)).comp (space : Spacetime →L[ℝ] E3)) v :=
  hasFDerivAt_radius hv

example {v : Spacetime} (hv : space v ≠ 0) :
    HasFDerivAt (fun w : Spacetime => w 0 - ‖space w‖)
      ((ContinuousLinearMap.proj 0 : Spacetime →L[ℝ] ℝ) -
        (‖space v‖⁻¹ • innerSL ℝ (space v)).comp (space : Spacetime →L[ℝ] E3)) v :=
  hasFDerivAt_retardedTime hv

example (g : ℝ → ℝ) (k : ℕ) (v : Spacetime) :
    ℝ :=
  radialProfile g k v

example {g : ℝ → ℝ} (k : ℕ) {v : Spacetime} (hv : space v ≠ 0)
    (hg : DifferentiableAt ℝ g (v 0 - ‖space v‖)) :
    ∃ L : Spacetime →L[ℝ] ℝ, HasFDerivAt (radialProfile g k) L v ∧
      L (Pi.single 0 1) = deriv g (v 0 - ‖space v‖) / ‖space v‖ ^ k ∧
      ∀ i : Fin 3, L (Pi.single i.succ 1) = -v i.succ *
        (deriv g (v 0 - ‖space v‖) / ‖space v‖ ^ (k + 1) +
          k * g (v 0 - ‖space v‖) / ‖space v‖ ^ (k + 2)) :=
  hasFDerivAt_radialProfile k hv hg

example {g : ℝ → ℝ} (k : ℕ) {v : Spacetime} (hv : space v ≠ 0)
    (hg : DifferentiableAt ℝ g (v 0 - ‖space v‖)) :
    partialAt (radialProfile g k) 0 v = radialProfile (deriv g) k v :=
  partialAt_radialProfile_zero k hv hg

example {g : ℝ → ℝ} (k : ℕ) {v : Spacetime} (hv : space v ≠ 0)
    (hg : DifferentiableAt ℝ g (v 0 - ‖space v‖)) (i : Fin 3) :
    partialAt (radialProfile g k) i.succ v =
      -v i.succ * (radialProfile (deriv g) (k + 1) v + k * radialProfile g (k + 2) v) :=
  partialAt_radialProfile_succ k hv hg i

example {g : ℝ → ℝ} (k : ℕ) {v : Spacetime} (hv : space v ≠ 0)
    (hg : DifferentiableAt ℝ g (v 0 - ‖space v‖)) :
    DifferentiableAt ℝ (radialProfile g k) v :=
  differentiableAt_radialProfile k hv hg

example {n : ℕ∞ω} {v : Spacetime} (hv : space v ≠ 0) :
    ContDiffAt ℝ n (fun w : Spacetime => ‖space w‖) v :=
  contDiffAt_radius hv

example {n : ℕ∞ω} {g : ℝ → ℝ} (hg : ContDiff ℝ n g) (k : ℕ) {v : Spacetime} (hv : space v ≠ 0) :
    ContDiffAt ℝ n (radialProfile g k) v :=
  contDiffAt_radialProfile hg k hv

example (v : Spacetime) :
    ‖space v‖ ^ 2 = ∑ i : Fin 3, v i.succ ^ 2 :=
  norm_space_sq v

example (g : ℝ → ℝ) (v : Spacetime) :
    ℝ :=
  sphericalWave g v

example (g : ℝ → ℝ) :
    sphericalWave g = fun v => (4 * π)⁻¹ * radialProfile g 1 v :=
  sphericalWave_eq g

example {n : ℕ∞ω} {g : ℝ → ℝ} (hg : ContDiff ℝ n g) {v : Spacetime} (hv : space v ≠ 0) :
    ContDiffAt ℝ n (sphericalWave g) v :=
  contDiffAt_sphericalWave hg hv

example {g : ℝ → ℝ} {v : Spacetime} (hv : space v ≠ 0)
    (hg : DifferentiableAt ℝ g (v 0 - ‖space v‖)) :
    partialAt (sphericalWave g) 0 v = sphericalWave (deriv g) v :=
  partialAt_sphericalWave_zero hv hg

example {g : ℝ → ℝ} {v : Spacetime} (hv : space v ≠ 0)
    (hg : DifferentiableAt ℝ g (v 0 - ‖space v‖)) (i : Fin 3) :
    partialAt (sphericalWave g) i.succ v =
      -(4 * π)⁻¹ * (v i.succ * (radialProfile (deriv g) 2 v + radialProfile g 3 v)) :=
  partialAt_sphericalWave_succ hv hg i

example {g : ℝ → ℝ} (hg : Differentiable ℝ g) {v : Spacetime} (hv : space v ≠ 0) :
    partialAt (sphericalWave g) 0 =ᶠ[𝓝 v] sphericalWave (deriv g) :=
  partialAt_sphericalWave_zero_eventuallyEq hg hv

example {g : ℝ → ℝ} (hg : Differentiable ℝ g) {v : Spacetime} (hv : space v ≠ 0) (i : Fin 3) :
    partialAt (sphericalWave g) i.succ =ᶠ[𝓝 v] fun w =>
      -(4 * π)⁻¹ * (w i.succ * (radialProfile (deriv g) 2 w + radialProfile g 3 w)) :=
  partialAt_sphericalWave_succ_eventuallyEq hg hv i

example {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {v : Spacetime} (hv : space v ≠ 0) (i j : Fin 3) :
    partialAt (partialAt (sphericalWave g) i.succ) j.succ v =
      (4 * π)⁻¹ * (v i.succ * v j.succ * (radialProfile (deriv (deriv g)) 3 v +
          3 * radialProfile (deriv g) 4 v + 3 * radialProfile g 5 v) -
        (if i = j then 1 else 0) * (radialProfile (deriv g) 2 v + radialProfile g 3 v)) :=
  partialAt_partialAt_sphericalWave_succ hg hv i j

example {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {v : Spacetime} (hv : space v ≠ 0) :
    partialAt (partialAt (sphericalWave g) 0) 0 v = sphericalWave (deriv (deriv g)) v :=
  partialAt_partialAt_sphericalWave_zero hg hv

example {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {v : Spacetime} (hv : space v ≠ 0) :
    box (sphericalWave g) v = 0 :=
  box_sphericalWave hg hv

example {n : ℕ∞ω} {d : ℝ → E3} (hd : ContDiff ℝ n d) (j : Fin 3) :
    ContDiff ℝ n fun s => d s j :=
  contDiff_coord hd j

example {d : ℝ → E3} (hd : Differentiable ℝ d) (j : Fin 3) :
    deriv (fun s => d s j) = fun s => deriv d s j :=
  deriv_coord hd j

example (d : ℝ → E3) :
    Potential :=
  dipolePotential d

example (d : ℝ → E3) :
    potentialComponent (dipolePotential d) 0 =
      fun v => ∑ j : Fin 3, partialAt (sphericalWave fun s => d s j) j.succ v :=
  potentialComponent_dipolePotential_zero d

example (d : ℝ → E3) (i : Fin 3) :
    potentialComponent (dipolePotential d) i.succ = sphericalWave fun s => deriv d s i :=
  potentialComponent_dipolePotential_succ d i

example {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) {v : Spacetime} (hv : space v ≠ 0) :
    ContDiffAt ℝ ∞ (dipolePotential d) v :=
  contDiffAt_dipolePotential hd hv

example {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) {v : Spacetime} (hv : space v ≠ 0) :
    lorenzDivergence (dipolePotential d) v = 0 :=
  lorenz_dipolePotential hd hv

example {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) {v : Spacetime} (hv : space v ≠ 0) (ν : Fin 4) :
    box (potentialComponent (dipolePotential d) ν) v = 0 :=
  box_dipolePotential hd hv ν

example {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) {v : Spacetime} (hv : space v ≠ 0) :
    CavityModes.VacuumMaxwellAt (dipolePotential d) v :=
  maxwell_dipolePotential hd hv

example (x y : E3) :
    ⟪x, y⟫ = ∑ j : Fin 3, x j * y j :=
  inner_eq_sum x y

example {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) {v : Spacetime} (hv : space v ≠ 0) (i : Fin 3) :
    electricField (fieldTensor (dipolePotential d)) i v =
      ∑ j : Fin 3, (4 * π)⁻¹ * (v j.succ * v i.succ *
          (radialProfile (fun s => deriv (deriv d) s j) 3 v +
            3 * radialProfile (fun s => deriv d s j) 4 v +
            3 * radialProfile (fun s => d s j) 5 v) -
        (if j = i then 1 else 0) *
          (radialProfile (fun s => deriv d s j) 2 v + radialProfile (fun s => d s j) 3 v)) -
      sphericalWave (fun s => deriv (deriv d) s i) v :=
  electricField_dipolePotential_apply hd hv i

example {v : Spacetime} (hv : space v ≠ 0) :
    ∃ r : ℝ, ∃ n : E3, 0 < r ∧ ‖n‖ = 1 ∧ v = vector (v 0) (r • n) :=
  exists_eq_vector_smul hv

example {r : ℝ} (hr : 0 < r) {n : E3} (hn : ‖n‖ = 1) (t : ℝ) :
    ‖space (vector t (r • n))‖ = r ∧ space (vector t (r • n)) ≠ 0 :=
  space_vector_smul hr hn t

example {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) {r : ℝ} (hr : 0 < r) {n : E3} (hn : ‖n‖ = 1) (t : ℝ)
    (i : Fin 3) :
    electricField (fieldTensor (dipolePotential d)) i (vector t (r • n)) =
      (4 * π)⁻¹ * ((3 * ⟪n, d (t - r)⟫ * n i - d (t - r) i) / r ^ 3 +
        (3 * ⟪n, deriv d (t - r)⟫ * n i - deriv d (t - r) i) / r ^ 2 +
        (⟪n, deriv (deriv d) (t - r)⟫ * n i - deriv (deriv d) (t - r) i) / r) :=
  electricField_dipolePotential hd hr hn t i

example {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) {r : ℝ} (hr : 0 < r) {n : E3} (hn : ‖n‖ = 1) (t : ℝ)
    (i : Fin 3) :
    magneticField (fieldTensor (dipolePotential d)) i (vector t (r • n)) =
      (4 * π)⁻¹ * crossProduct
        (WithLp.ofLp (r⁻¹ • deriv (deriv d) (t - r) + (r ^ 2)⁻¹ • deriv d (t - r)))
        (WithLp.ofLp n) i :=
  magneticField_dipolePotential hd hr hn t i

example {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) {R : ℝ} (hR : 0 < R) {n : E3} (hn : ‖n‖ = 1) (t : ℝ) :
    ∑ i : Fin 3, poyntingVector (fieldTensor (dipolePotential d)) i (vector t (R • n)) * n i =
      (4 * π)⁻¹ ^ 2 *
        (⟪(R ^ 3)⁻¹ • d (t - R) + (R ^ 2)⁻¹ • deriv d (t - R) + R⁻¹ • deriv (deriv d) (t - R),
            R⁻¹ • deriv (deriv d) (t - R) + (R ^ 2)⁻¹ • deriv d (t - R)⟫ -
          ⟪n, (R ^ 3)⁻¹ • d (t - R) + (R ^ 2)⁻¹ • deriv d (t - R) +
            R⁻¹ • deriv (deriv d) (t - R)⟫ *
          ⟪n, R⁻¹ • deriv (deriv d) (t - R) + (R ^ 2)⁻¹ • deriv d (t - R)⟫) :=
  poyntingVector_inner_dipolePotential hd hR hn t

example {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    sphereFlux (poyntingVector (fieldTensor (dipolePotential d))) t R =
      R ^ 2 * ((6 * π)⁻¹ *
        ⟪(R ^ 3)⁻¹ • d (t - R) + (R ^ 2)⁻¹ • deriv d (t - R) + R⁻¹ • deriv (deriv d) (t - R),
          R⁻¹ • deriv (deriv d) (t - R) + (R ^ 2)⁻¹ • deriv d (t - R)⟫) :=
  sphereFlux_dipolePotential_eq_inner hd hR t

example (d : ℝ → E3) (R t : ℝ) :
    ℝ :=
  nearZoneEnergy d R t

example {d : ℝ → E3} {R : ℝ} (hR : 0 < R) (t : ℝ) :
    nearZoneEnergy d R t = (12 * π * R ^ 3)⁻¹ *
      (‖d (t - R) + R • deriv d (t - R)‖ ^ 2 + R ^ 2 * ‖deriv d (t - R)‖ ^ 2) :=
  nearZoneEnergy_eq hR t

example {d : ℝ → E3} {R : ℝ} (hR : 0 < R) (t : ℝ) :
    0 ≤ nearZoneEnergy d R t :=
  nearZoneEnergy_nonneg hR t

example {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) (R t : ℝ) :
    HasDerivAt (nearZoneEnergy d R)
      ((6 * π)⁻¹ * (2 * ⟪deriv d (t - R), deriv (deriv d) (t - R)⟫ / R +
        (‖deriv d (t - R)‖ ^ 2 + ⟪d (t - R), deriv (deriv d) (t - R)⟫) / R ^ 2 +
        ⟪d (t - R), deriv d (t - R)⟫ / R ^ 3)) t :=
  hasDerivAt_nearZoneEnergy hd R t

example {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    sphereFlux (poyntingVector (fieldTensor (dipolePotential d))) t R =
      2 / 3 * (4 * π)⁻¹ * ‖deriv (deriv d) (t - R)‖ ^ 2 + deriv (nearZoneEnergy d R) t :=
  sphereFlux_eq hd hR t

example {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) (u : ℝ) :
    Tendsto (fun R => sphereFlux (poyntingVector (fieldTensor (dipolePotential d))) (u + R) R)
      atTop (𝓝 ((6 * π)⁻¹ * ‖deriv (deriv d) u‖ ^ 2)) :=
  tendsto_sphereFlux hd u

example {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) (hc : HasCompactSupport d) {R : ℝ} (hR : 0 < R) :
    ∫ t, sphereFlux (poyntingVector (fieldTensor (dipolePotential d))) t R =
      (6 * π)⁻¹ * ∫ u, ‖deriv (deriv d) u‖ ^ 2 :=
  integral_sphereFlux_eq hd hc hR

example (t : ℝ) :
    E3 :=
  oscillatingMoment t

example :
    ContDiff ℝ ∞ oscillatingMoment :=
  contDiff_oscillatingMoment

example :
    deriv oscillatingMoment = fun t => -Real.sin t • EuclideanSpace.single 2 1 :=
  deriv_oscillatingMoment

example :
    deriv (deriv oscillatingMoment) = fun t => -Real.cos t • EuclideanSpace.single 2 1 :=
  deriv_deriv_oscillatingMoment

example :
    deriv (deriv oscillatingMoment) ≠ 0 ∧
      (∀ v : Spacetime, space v ≠ 0 →
        lorenzDivergence (dipolePotential oscillatingMoment) v = 0 ∧
          CavityModes.VacuumMaxwellAt (dipolePotential oscillatingMoment) v) ∧
      ∀ R : ℝ, 0 < R → ∀ t : ℝ,
        sphereFlux (poyntingVector (fieldTensor (dipolePotential oscillatingMoment))) t R =
          2 / 3 * (4 * π)⁻¹ * Real.cos (t - R) ^ 2 +
            deriv (nearZoneEnergy oscillatingMoment R) t :=
  oscillatingMoment_instance

example {g : ℝ → ℝ} (hg : Differentiable ℝ g) (hc : HasCompactSupport g) (h : ∀ x, deriv g x = 0)
    (x : ℝ) :
    g x = 0 :=
  eq_zero_of_deriv_eq_zero hg hc h x

example :
    ContDiffBump (0 : ℝ) :=
  timeBump

example :
    ∃ x, deriv (deriv timeBump) x ≠ 0 :=
  exists_deriv_deriv_timeBump_ne_zero

example (t : ℝ) :
    E3 :=
  pulseMoment t

example :
    ContDiff ℝ ∞ pulseMoment :=
  contDiff_pulseMoment

example :
    HasCompactSupport pulseMoment :=
  hasCompactSupport_pulseMoment

example :
    deriv (deriv pulseMoment) = fun t => deriv (deriv timeBump) t • EuclideanSpace.single 2 1 :=
  deriv_deriv_pulseMoment

example {R : ℝ} (hR : 0 < R) :
    ∫ t, sphereFlux (poyntingVector (fieldTensor (dipolePotential pulseMoment))) t R =
        (6 * π)⁻¹ * ∫ u, ‖deriv (deriv pulseMoment) u‖ ^ 2 ∧
      0 < ∫ t, sphereFlux (poyntingVector (fieldTensor (dipolePotential pulseMoment))) t R :=
  pulseMoment_instance hR

end ProjectAinos.Electrodynamics.Radiation.NearZone

end NearZone

section Dipole

open MeasureTheory Set Metric Real Filter

open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics.Radiation

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Sphere SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (κ : ℝ) :
    Spacetime →L[ℝ] Spacetime :=
  timeDilation κ

example (κ : ℝ) (v : Spacetime) :
    timeDilation κ v = vector (κ * v 0) (space v) :=
  timeDilation_apply κ v

example (κ t : ℝ) (x : E3) :
    timeDilation κ (vector t x) = vector (κ * t) x :=
  timeDilation_vector κ t x

example (κ : ℝ) :
    Spacetime →L[ℝ] Spacetime :=
  spaceScaling κ

example (κ : ℝ) (w : Spacetime) :
    spaceScaling κ w = vector (w 0) (κ • space w) :=
  spaceScaling_apply κ w

example (κ : ℝ) (w : Spacetime) :
    spaceScaling κ w 0 = w 0 :=
  spaceScaling_apply_zero κ w

example (κ : ℝ) (w : Spacetime) (i : Fin 3) :
    spaceScaling κ w i.succ = κ * w i.succ :=
  spaceScaling_apply_succ κ w i

example (κ : ℝ) (k : Spacetime → Spacetime) :
    Spacetime → Spacetime :=
  slowCurrent κ k

example (κ : ℝ) (k : Spacetime → Spacetime) (t : ℝ) (x : E3) :
    slowCurrent κ k (vector t x) 0 = k (vector (κ * t) x) 0 :=
  slowCurrent_vector_zero κ k t x

example (κ : ℝ) (k : Spacetime → Spacetime) (t : ℝ) (x : E3) (i : Fin 3) :
    slowCurrent κ k (vector t x) i.succ = κ * k (vector (κ * t) x) i.succ :=
  slowCurrent_vector_succ κ k t x i

example (κ : ℝ) (k : Spacetime → Spacetime) (t : ℝ) (x : E3) :
    space (slowCurrent κ k (vector t x)) = κ • space (k (vector (κ * t) x)) :=
  space_slowCurrent_vector κ k t x

example {κ : ℝ} {k : Spacetime → Spacetime} {v : Spacetime}
    (hk : DifferentiableAt ℝ k (timeDilation κ v)) :
    HasFDerivAt (slowCurrent κ k)
      ((spaceScaling κ).comp ((fderiv ℝ k (timeDilation κ v)).comp (timeDilation κ))) v :=
  hasFDerivAt_slowCurrent hk

example (κ : ℝ) :
    timeDilation κ (Pi.single 0 1) = κ • (Pi.single 0 1 : Spacetime) :=
  timeDilation_single_zero κ

example (κ : ℝ) (i : Fin 3) :
    timeDilation κ (Pi.single i.succ 1) = (Pi.single i.succ 1 : Spacetime) :=
  timeDilation_single_succ κ i

example {K : Spacetime → Spacetime} {v : Spacetime} (hK : DifferentiableAt ℝ K v) :
    currentRate K v = fderiv ℝ K v (Pi.single 0 1) :=
  currentRate_eq_fderiv hK

example {k : Spacetime → Spacetime} (hk : Differentiable ℝ k) (κ : ℝ) :
    currentRate (slowCurrent κ k) = κ • slowCurrent κ (currentRate k) :=
  currentRate_slowCurrent hk κ

example {k : Spacetime → Spacetime} (hk : Differentiable ℝ k) (hdiv : ∀ v, divergence4 k v = 0)
    (κ : ℝ) (v : Spacetime) :
    divergence4 (slowCurrent κ k) v = 0 :=
  divergence4_slowCurrent hk hdiv κ v

example {K : Spacetime → Spacetime} (hK : ContDiff ℝ ∞ K) :
    ContDiff ℝ ∞ (currentRate K) :=
  contDiff_currentRate hK

example {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {F : Spacetime → G} {a : ℝ}
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → F (vector t x) = 0) {t : ℝ} {x : E3} (hx : a < ‖x‖) :
    fderiv ℝ F (vector t x) = 0 :=
  fderiv_eq_zero_of_ballSupport hs hx

example {K : Spacetime → Spacetime} {a : ℝ}
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → K (vector t x) = 0) (t : ℝ) (x : E3) (hx : a < ‖x‖) :
    currentRate K (vector t x) = 0 :=
  currentRate_eq_zero_of_ballSupport hs t x hx

example {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ} (hk : LocalizedSource k a M N) (m : ℕ) :
    ContDiff ℝ ∞ (currentRate^[m] k) :=
  LocalizedSource.contDiff_iterate hk m

example {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ} (hk : LocalizedSource k a M N) (m : ℕ) :
    ∀ (t : ℝ) (x : E3), a < ‖x‖ → (currentRate^[m] k) (vector t x) = 0 :=
  LocalizedSource.support_iterate hk m

example {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ} (hk : LocalizedSource k a M N) :
    0 ≤ M :=
  LocalizedSource.bound_nonneg hk

example (a C : ℝ) :
    Integrable ((closedBall (0 : E3) a).indicator fun _ => C) :=
  integrable_indicator_closedBall_const a C

example {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E3 → G} {a C : ℝ} (ha : 0 ≤ a)
    (hf : ∀ y, a < ‖y‖ → f y = 0) (hb : ∀ y, ‖y‖ ≤ a → ‖f y‖ ≤ C) :
    ‖∫ y, f y‖ ≤ C * (4 * π / 3 * a ^ 3) :=
  norm_integral_le_of_ballSupport ha hf hb

example {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E3 → G} {a : ℝ}
    (hc : Continuous f) (hf : ∀ y, a < ‖y‖ → f y = 0) :
    Integrable f :=
  integrable_of_ballSupport hc hf

example {G : Type*} [TopologicalSpace G] {F : Spacetime → G} (hF : Continuous F) :
    Continuous fun p : ℝ × E3 => F (vector p.1 p.2) :=
  continuous_comp_vector_slice hF

example {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] {F F' : ℝ → E3 → G}
    {a : ℝ} (hF : Continuous (Function.uncurry F)) (hF' : Continuous (Function.uncurry F'))
    (hs : ∀ s y, a < ‖y‖ → F s y = 0) (hs' : ∀ s y, a < ‖y‖ → F' s y = 0)
    (hd : ∀ s y, HasDerivAt (fun s => F s y) (F' s y) s) (s₀ : ℝ) :
    HasDerivAt (fun s => ∫ y, F s y) (∫ y, F' s₀ y) s₀ :=
  hasDerivAt_integral_of_ballSupport hF hF' hs hs' hd s₀

example (t : ℝ) (y : E3) :
    HasDerivAt (fun t => vector t y) (Pi.single 0 1 : Spacetime) t :=
  hasDerivAt_vector_time t y

example {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {F : Spacetime → G} {t : ℝ} {y : E3}
    (hF : DifferentiableAt ℝ F (vector t y)) :
    HasDerivAt (fun t => F (vector t y)) (fderiv ℝ F (vector t y) (Pi.single 0 1)) t :=
  hasDerivAt_comp_vector_time hF

example {K : Spacetime → Spacetime} (hK : Differentiable ℝ K) (t : ℝ) (y : E3) :
    HasDerivAt (fun t => K (vector t y)) (currentRate K (vector t y)) t :=
  hasDerivAt_current_vector hK t y

example {K : Spacetime → Spacetime} (hK : Differentiable ℝ K) (t : ℝ) (y : E3) :
    HasDerivAt (fun t => space (K (vector t y))) (space (currentRate K (vector t y))) t :=
  hasDerivAt_space_current_vector hK t y

example (s : ℝ) (y : E3) :
    HasFDerivAt (fun y => vector s y)
      ((Wave.timeSpaceEquiv.symm : ℝ × E3 →L[ℝ] Spacetime).comp
        ((0 : E3 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E3))) y :=
  hasFDerivAt_vector_space s y

example {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {F : Spacetime → G} {s : ℝ} {y : E3}
    (hF : DifferentiableAt ℝ F (vector s y)) (i : Fin 3) :
    fderiv ℝ (fun y => F (vector s y)) y (EuclideanSpace.single i 1) =
      fderiv ℝ F (vector s y) (Pi.single i.succ 1) :=
  fderiv_comp_vector_single hF i

example {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E3 → G} {a : ℝ}
    (hf : ∀ y, a < ‖y‖ → f y = 0) {y : E3} (hy : a < ‖y‖) :
    fderiv ℝ f y = 0 :=
  fderiv_space_eq_zero_of_ballSupport hf hy

example (x : E3) :
    x = ∑ l : Fin 3, x l • EuclideanSpace.single l (1 : ℝ) :=
  eq_sum_euclideanSingle x

example {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {K : Spacetime → Spacetime} {a : ℝ} (hK : ContDiff ℝ ∞ K)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → K (vector t x) = 0) {w : E3 → G} (hw : Continuous w)
    (μ : Fin 4) (s : ℝ) :
    HasDerivAt (fun s => ∫ y, K (vector s y) μ • w y)
      (∫ y, currentRate K (vector s y) μ • w y) s :=
  hasDerivAt_integral_smul hK hs hw μ s

example {K : Spacetime → Spacetime} {a : ℝ} (hK : ContDiff ℝ ∞ K)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → K (vector t x) = 0) (s : ℝ) :
    HasDerivAt (fun s => ∫ y, space (K (vector s y)))
      (∫ y, space (currentRate K (vector s y))) s :=
  hasDerivAt_integral_space hK hs s

example {k : Spacetime → Spacetime} (hk : Differentiable ℝ k) (hdiv : ∀ v, divergence4 k v = 0)
    (s : ℝ) (y : E3) :
    currentRate k (vector s y) 0 =
      -∑ l : Fin 3, fderiv ℝ (fun y => k (vector s y) l.succ) y (EuclideanSpace.single l 1) :=
  currentRate_zero_eq_neg_sum hk hdiv s y

example {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hdiv : ∀ v, divergence4 k v = 0) (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0)
    {W : E3 → ℝ} (hW : ContDiff ℝ 1 W) (s : ℝ) :
    ∫ y, W y * currentRate k (vector s y) 0 = ∫ y, fderiv ℝ W y (space (k (vector s y))) :=
  integral_mul_currentRate_zero hk hdiv hs hW s

example (k : Spacetime → Spacetime) (s : ℝ) :
    E3 :=
  dipoleMoment k s

example {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hdiv : ∀ v, divergence4 k v = 0) (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0)
    (s : ℝ) :
    ∫ y, space (k (vector s y)) = ∫ y, currentRate k (vector s y) 0 • y :=
  integral_space_eq hk hdiv hs s

example {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hdiv : ∀ v, divergence4 k v = 0) (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0)
    (s : ℝ) :
    HasDerivAt (dipoleMoment k) (∫ y, space (k (vector s y))) s :=
  hasDerivAt_dipoleMoment hk hdiv hs s

example {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hdiv : ∀ v, divergence4 k v = 0) (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0)
    (s : ℝ) :
    deriv (deriv (dipoleMoment k)) s = ∫ y, space (currentRate k (vector s y)) :=
  deriv_deriv_dipoleMoment hk hdiv hs s

example {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hdiv : ∀ v, divergence4 k v = 0) (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0)
    (i l : Fin 3) (s : ℝ) :
    HasDerivAt (fun s => ∫ y, k (vector s y) 0 * (y i * y l))
      (∫ y, (y i * k (vector s y) l.succ + y l * k (vector s y) i.succ)) s :=
  hasDerivAt_secondMoment hk hdiv hs i l s

example (x y : E3) :
    inner ℝ x y = ∑ i : Fin 3, x i * y i :=
  inner_eq_sum_mul_fin_three x y

example {X : Type*} [TopologicalSpace X] {τ : X → ℝ} {f : X → E3} (hτ : Continuous τ)
    (hf : Continuous f) :
    Continuous fun x => vector (τ x) (f x) :=
  continuous_vector_of_continuous hτ hf

example (k : Spacetime → Spacetime) (u : ℝ) (n : E3) :
    ℝ :=
  angularIntensity k u n

example (k : Spacetime → Spacetime) (u : ℝ) :
    radiatedPower k u = ∫ n : sphere (0 : E3) 1, angularIntensity k u n ∂sphereMeasure :=
  radiatedPower_eq_integral k u

example (k : Spacetime → Spacetime) (u : ℝ) (n : E3) :
    E3 :=
  amplitudeVector k u n

example (k : Spacetime → Spacetime) (u : ℝ) (n : E3) :
    angularIntensity k u n =
      ‖amplitudeVector k u n‖ ^ 2 - inner ℝ n (amplitudeVector k u n) ^ 2 :=
  angularIntensity_eq k u n

example (k : Spacetime → Spacetime) (κ s : ℝ) (n : E3) :
    E3 :=
  slowAmplitude k κ s n

example (k : Spacetime → Spacetime) (s : ℝ) (n : E3) :
    E3 :=
  firstCorrection k s n

example {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0) (κ u : ℝ) (n : E3) :
    amplitudeVector (slowCurrent κ k) u n = (κ ^ 2 / (4 * π)) • slowAmplitude k κ (κ * u) n :=
  amplitudeVector_slowCurrent hk hs κ u n

example {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0) (κ u : ℝ) (n : E3) :
    angularIntensity (slowCurrent κ k) u n = (κ ^ 2 / (4 * π)) ^ 2 *
      (‖slowAmplitude k κ (κ * u) n‖ ^ 2 - inner ℝ n (slowAmplitude k κ (κ * u) n) ^ 2) :=
  angularIntensity_slowCurrent hk hs κ u n

example {X G : Type*} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {F : X → E3 → G} {a : ℝ}
    (hF : Continuous (Function.uncurry F)) (hs : ∀ x y, a < ‖y‖ → F x y = 0) :
    Continuous fun x => ∫ y, F x y :=
  continuous_integral_of_ballSupport hF hs

example {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0) (κ s : ℝ) :
    Continuous (slowAmplitude k κ s) :=
  continuous_slowAmplitude hk hs κ s

example {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0) (s : ℝ) :
    Continuous (firstCorrection k s) :=
  continuous_firstCorrection hk hs s

example (k : Spacetime → Spacetime) (s : ℝ) (n : E3) :
    firstCorrection k s (-n) = -firstCorrection k s n :=
  firstCorrection_neg k s n

example {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f f' f'' : ℝ → G} {M : ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : ∀ t, HasDerivAt f' (f'' t) t) (hM : ∀ t, ‖f'' t‖ ≤ M)
    (h : ℝ) :
    ‖f h - f 0 - h • f' 0‖ ≤ M * h ^ 2 :=
  norm_sub_sub_smul_le_of_deriv_two hf hf' hM h

example {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ} (hk : LocalizedSource k a M N) (hN : 3 ≤ N)
    (κ s : ℝ) {n : E3} (hn : ‖n‖ = 1) :
    ‖slowAmplitude k κ s n - (∫ y, space (currentRate k (vector s y))) -
        κ • firstCorrection k s n‖ ≤ M * κ ^ 2 * a ^ 2 * (4 * π / 3 * a ^ 3) :=
  norm_slowAmplitude_sub_le hk hN κ s hn

example {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ} (hk : LocalizedSource k a M N) (hN : 1 ≤ N)
    (s : ℝ) :
    ‖∫ y, space (currentRate k (vector s y))‖ ≤ M * (4 * π / 3 * a ^ 3) :=
  norm_integral_currentRate_le hk hN s

example {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ} (hk : LocalizedSource k a M N) (hN : 2 ≤ N)
    (s : ℝ) {n : E3} (hn : ‖n‖ = 1) :
    ‖firstCorrection k s n‖ ≤ a * M * (4 * π / 3 * a ^ 3) :=
  norm_firstCorrection_le hk hN s hn

example (n b c e : E3) (κ : ℝ) :
    ‖b + κ • c + e‖ ^ 2 - inner ℝ n (b + κ • c + e) ^ 2 =
      (‖b‖ ^ 2 - inner ℝ n b ^ 2) + 2 * κ * (inner ℝ b c - inner ℝ n b * inner ℝ n c) +
        (κ ^ 2 * (‖c‖ ^ 2 - inner ℝ n c ^ 2) + 2 * (inner ℝ b e - inner ℝ n b * inner ℝ n e) +
          2 * κ * (inner ℝ c e - inner ℝ n c * inner ℝ n e) + (‖e‖ ^ 2 - inner ℝ n e ^ 2)) :=
  transverse_sq_expand n b c e κ

example {n v : E3} (hn : ‖n‖ = 1) :
    |‖v‖ ^ 2 - inner ℝ n v ^ 2| ≤ ‖v‖ ^ 2 :=
  abs_transverse_sq_le hn

example {n v w : E3} (hn : ‖n‖ = 1) :
    |inner ℝ v w - inner ℝ n v * inner ℝ n w| ≤ 2 * (‖v‖ * ‖w‖) :=
  abs_transverse_inner_le hn

example (b : E3) :
    ∫ n : sphere (0 : E3) 1, (‖b‖ ^ 2 - inner ℝ (n : E3) b ^ 2) ∂sphereMeasure =
      8 * π / 3 * ‖b‖ ^ 2 :=
  integral_norm_sq_sub_inner_sq b

example {n b c e : E3} {κ β γ ε : ℝ} (hn : ‖n‖ = 1) (hκ0 : 0 ≤ κ) (hb : ‖b‖ ≤ β) (hc : ‖c‖ ≤ γ)
    (he : ‖e‖ ≤ ε) :
    |κ ^ 2 * (‖c‖ ^ 2 - inner ℝ n c ^ 2) + 2 * (inner ℝ b e - inner ℝ n b * inner ℝ n e) +
        2 * κ * (inner ℝ c e - inner ℝ n c * inner ℝ n e) + (‖e‖ ^ 2 - inner ℝ n e ^ 2)| ≤
      κ ^ 2 * γ ^ 2 + 4 * β * ε + 4 * κ * γ * ε + ε ^ 2 :=
  abs_transverse_remainder_le hn hκ0 hb hc he

example (k : Spacetime → Spacetime) (s : ℝ) (b : E3) :
    ∫ n : sphere (0 : E3) 1, (inner ℝ b (firstCorrection k s n) -
      inner ℝ (n : E3) b * inner ℝ (n : E3) (firstCorrection k s n)) ∂sphereMeasure = 0 :=
  integral_inner_firstCorrection k s b

example {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ} (hk : LocalizedSource k a M N) (hN : 3 ≤ N)
    {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (u : ℝ) {n : E3} (hn : ‖n‖ = 1) :
    |angularIntensity (slowCurrent κ k) u n - (κ ^ 2 / (4 * π)) ^ 2 *
        ((‖∫ y, space (currentRate k (vector (κ * u) y))‖ ^ 2 -
          inner ℝ n (∫ y, space (currentRate k (vector (κ * u) y))) ^ 2) +
        2 * κ * (inner ℝ (∫ y, space (currentRate k (vector (κ * u) y)))
            (firstCorrection k (κ * u) n) -
          inner ℝ n (∫ y, space (currentRate k (vector (κ * u) y))) *
            inner ℝ n (firstCorrection k (κ * u) n)))| ≤
      (κ ^ 2 / (4 * π)) ^ 2 *
        (κ ^ 2 * (M ^ 2 * (4 * π / 3 * a ^ 3) ^ 2 * a ^ 2 * (5 + 4 * a + a ^ 2))) :=
  abs_angularIntensity_slowCurrent_sub_le hk hN hκ0 hκ1 u hn

example {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ} (hk : LocalizedSource k a M N) (hN : 3 ≤ N)
    {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (u : ℝ) :
    |radiatedPower (slowCurrent κ k) u -
        κ ^ 4 * (1 / (6 * π)) * ‖deriv (deriv (dipoleMoment k)) (κ * u)‖ ^ 2| ≤
      4 * π / 9 * M ^ 2 * a ^ 8 * (5 + 4 * a + a ^ 2) * κ ^ 6 :=
  dipolePower_sub_le hk hN hκ0 hκ1 u

example {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ} (hk : LocalizedSource k a M N) (hN : 3 ≤ N)
    {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (u : ℝ) {n : E3} (hn : ‖n‖ = 1) :
    |angularIntensity (slowCurrent κ k) u n -
        κ ^ 4 * ((‖deriv (deriv (dipoleMoment k)) (κ * u)‖ ^ 2 -
          inner ℝ n (deriv (deriv (dipoleMoment k)) (κ * u)) ^ 2) / (16 * π ^ 2))| ≤
      M ^ 2 * a ^ 7 * (4 + 5 * a + 4 * a ^ 2 + a ^ 3) / 9 * κ ^ 5 :=
  dipoleAngular hk hN hκ0 hκ1 u hn

example (f : E3 → ℝ) (x : E3) :
    ℝ :=
  partialOne f x

example {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (partialOne f) :=
  contDiff_partialOne hf

example {f : E3 → ℝ} {r : ℝ} (hf : ∀ x, r < ‖x‖ → f x = 0) {x : E3} (hx : r < ‖x‖) :
    partialOne f x = 0 :=
  partialOne_eq_zero hf hx

example (f : E3 → ℝ) (φ : ℝ) :
    Spacetime → Spacetime :=
  oscillatingCurrent f φ

example (f : E3 → ℝ) (φ : ℝ) (v : Spacetime) :
    oscillatingCurrent f φ v 0 = cos (v 0 + φ) * partialOne f (space v) :=
  oscillatingCurrent_apply_zero f φ v

example (f : E3 → ℝ) (φ : ℝ) (v : Spacetime) :
    space (oscillatingCurrent f φ v) =
      (sin (v 0 + φ) * f (space v)) • EuclideanSpace.single 0 (1 : ℝ) :=
  space_oscillatingCurrent f φ v

example :
    space (Pi.single 0 1 : Spacetime) = 0 :=
  space_pi_single_time

example :
    space (Pi.single 1 1 : Spacetime) = EuclideanSpace.single 0 1 :=
  space_pi_single_one

example :
    ‖EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖ = 1 :=
  norm_euclideanSingle_one

example {P : ℝ → ℝ} {p : ℝ} {F : E3 → ℝ} {v : Spacetime} (hP : HasDerivAt P p (v 0))
    (hF : DifferentiableAt ℝ F (space v)) :
    HasFDerivAt (fun w : Spacetime => P (w 0) * F (space w))
      (P (v 0) • (fderiv ℝ F (space v)).comp space +
        F (space v) • p • (ContinuousLinearMap.proj 0 : Spacetime →L[ℝ] ℝ)) v :=
  hasFDerivAt_time_mul_space hP hF

example {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (φ : ℝ) (v w : Spacetime) :
    fderiv ℝ (oscillatingCurrent f φ) v w =
      (cos (v 0 + φ) * fderiv ℝ (partialOne f) (space v) (space w) +
          partialOne f (space v) * (-sin (v 0 + φ) * w 0)) • (Pi.single 0 1 : Spacetime) +
        (sin (v 0 + φ) * fderiv ℝ f (space v) (space w) +
          f (space v) * (cos (v 0 + φ) * w 0)) • (Pi.single 1 1 : Spacetime) :=
  fderiv_oscillatingCurrent hf φ v w

example {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (φ : ℝ) :
    ContDiff ℝ ∞ (oscillatingCurrent f φ) :=
  contDiff_oscillatingCurrent hf φ

example {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (φ : ℝ) :
    currentRate (oscillatingCurrent f φ) = oscillatingCurrent f (φ + π / 2) :=
  currentRate_oscillatingCurrent hf φ

example {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (φ : ℝ) (m : ℕ) :
    currentRate^[m] (oscillatingCurrent f φ) = oscillatingCurrent f (φ + m * (π / 2)) :=
  currentRate_iterate_oscillatingCurrent hf φ m

example {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (φ : ℝ) (v : Spacetime) :
    divergence4 (oscillatingCurrent f φ) v = 0 :=
  divergence4_oscillatingCurrent hf φ v

example {f : E3 → ℝ} {r : ℝ} (hf : ∀ x, r < ‖x‖ → f x = 0) (φ : ℝ) (t : ℝ) (x : E3) (hx : r < ‖x‖) :
    oscillatingCurrent f φ (vector t x) = 0 :=
  oscillatingCurrent_eq_zero hf φ t x hx

example {f : E3 → ℝ} {r B : ℝ} (hf : ContDiff ℝ ∞ f) (hr : 0 ≤ r) (hs : ∀ x, r < ‖x‖ → f x = 0)
    (hB : ∀ x, |f x| ≤ B) (φ : ℝ) (N : ℕ) :
    LocalizedSource (oscillatingCurrent f φ) r B N :=
  localizedSource_oscillatingCurrent hf hr hs hB φ N

example {f : E3 → ℝ} {r : ℝ} (hf : ContDiff ℝ ∞ f) (hs : ∀ x, r < ‖x‖ → f x = 0) :
    ∫ y : E3, partialOne f y • y = (-∫ y, f y) • EuclideanSpace.single 0 (1 : ℝ) :=
  integral_partialOne_smul hf hs

example {f : E3 → ℝ} {r : ℝ} (hf : ContDiff ℝ ∞ f) (hs : ∀ x, r < ‖x‖ → f x = 0) (φ s : ℝ) :
    dipoleMoment (oscillatingCurrent f φ) s =
      (-(cos (s + φ) * ∫ y, f y)) • EuclideanSpace.single 0 (1 : ℝ) :=
  dipoleMoment_oscillatingCurrent hf hs φ s

example :
    ContDiffBump (0 : E3) :=
  dipoleBump

example (x : E3) (hx : 2 < ‖x‖) :
    dipoleBump x = 0 :=
  dipoleBump_eq_zero x hx

example (x : E3) :
    |dipoleBump x| ≤ 1 :=
  abs_dipoleBump_le x

example :
    Spacetime → Spacetime :=
  oscillatingDipole

example (N : ℕ) :
    LocalizedSource oscillatingDipole 2 1 N :=
  localizedSource_oscillatingDipole N

example (s : ℝ) :
    dipoleMoment oscillatingDipole s =
      (-(cos s * ∫ y, dipoleBump y)) • EuclideanSpace.single 0 (1 : ℝ) :=
  dipoleMoment_oscillatingDipole s

example (s : ℝ) :
    deriv (deriv (dipoleMoment oscillatingDipole)) s =
      (cos s * ∫ y, dipoleBump y) • EuclideanSpace.single 0 (1 : ℝ) :=
  deriv_deriv_dipoleMoment_oscillatingDipole s

example (s : ℝ) :
    ‖deriv (deriv (dipoleMoment oscillatingDipole)) s‖ ^ 2 =
      cos s ^ 2 * (∫ y, dipoleBump y) ^ 2 :=
  norm_deriv_deriv_dipoleMoment_oscillatingDipole s

example :
    0 < ∫ y : E3, dipoleBump y :=
  integral_dipoleBump_pos

example {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (u : ℝ) :
    |radiatedPower (slowCurrent κ oscillatingDipole) u -
        κ ^ 4 * (1 / (6 * π)) * (cos (κ * u) ^ 2 * (∫ y, dipoleBump y) ^ 2)| ≤
      4 * π / 9 * 2 ^ 8 * 17 * κ ^ 6 ∧
    0 < κ ^ 4 * (1 / (6 * π)) * (cos (κ * 0) ^ 2 * (∫ y, dipoleBump y) ^ 2) :=
  dipolePower_oscillatingDipole hκ0 hκ1 u

end ProjectAinos.Electrodynamics.Radiation

end Dipole

section Multipole

open MeasureTheory Set Metric Real Filter

open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics.Radiation

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Sphere SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (K : Spacetime → Spacetime) (s : ℝ) (i l : Fin 3) :
    ℝ :=
  currentMoment K s i l

example {K : Spacetime → Spacetime} {a : ℝ} (hK : Continuous K)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → K (vector t x) = 0) (s : ℝ) (μ : Fin 4) (i : Fin 3) :
    Integrable fun y : E3 => K (vector s y) μ * y i :=
  integrable_component_mul_coord hK hs s μ i

example {K : Spacetime → Spacetime} {a : ℝ} (hK : ContDiff ℝ ∞ K)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → K (vector t x) = 0) (i l : Fin 3) (s : ℝ) :
    HasDerivAt (fun s => currentMoment K s i l) (currentMoment (currentRate K) s i l) s :=
  hasDerivAt_currentMoment hK hs i l s

example (k : Spacetime → Spacetime) (s : ℝ) (i j : Fin 3) :
    ℝ :=
  quadrupoleMoment k s i j

example (N : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) :
    ℝ :=
  quadrupoleRate N i j

example {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hdiv : ∀ v, divergence4 k v = 0) (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0)
    (i j : Fin 3) (s : ℝ) :
    HasDerivAt (fun s => quadrupoleMoment k s i j) (quadrupoleRate (currentMoment k s) i j) s :=
  hasDerivAt_quadrupoleMoment hk hdiv hs i j s

example {K : Spacetime → Spacetime} {a : ℝ} (hK : ContDiff ℝ ∞ K)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → K (vector t x) = 0) (i j : Fin 3) (s : ℝ) :
    HasDerivAt (fun s => quadrupoleRate (currentMoment K s) i j)
      (quadrupoleRate (currentMoment (currentRate K) s) i j) s :=
  hasDerivAt_quadrupoleRate hK hs i j s

example {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hdiv : ∀ v, divergence4 k v = 0) (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0)
    (i j : Fin 3) (s : ℝ) :
    deriv (deriv (deriv fun s => quadrupoleMoment k s i j)) s =
      quadrupoleRate (currentMoment (currentRate (currentRate k)) s) i j :=
  deriv_deriv_deriv_quadrupoleMoment hk hdiv hs i j s

example (x z : E3) :
    E3 :=
  cross3 x z

example (x z : E3) :
    cross3 x z 0 = x 1 * z 2 - x 2 * z 1 :=
  cross3_apply_zero x z

example (x z : E3) :
    cross3 x z 1 = x 2 * z 0 - x 0 * z 2 :=
  cross3_apply_one x z

example (x z : E3) :
    cross3 x z 2 = x 0 * z 1 - x 1 * z 0 :=
  cross3_apply_two x z

example (x : E3) :
    cross3 x 0 = 0 :=
  cross3_zero_right x

example :
    Continuous fun p : E3 × E3 => cross3 p.1 p.2 :=
  continuous_cross3

example (x : E3) :
    E3 →L[ℝ] E3 :=
  crossLeft x

example (x z : E3) :
    crossLeft x z = cross3 x z :=
  crossLeft_apply x z

example (k : Spacetime → Spacetime) (s : ℝ) :
    E3 :=
  magneticMoment k s

example {K : Spacetime → Spacetime} {a : ℝ} (hK : ContDiff ℝ ∞ K)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → K (vector t x) = 0) (s : ℝ) :
    HasDerivAt (fun s => ∫ y, cross3 y (space (K (vector s y))))
      (∫ y, cross3 y (space (currentRate K (vector s y)))) s :=
  hasDerivAt_integral_cross3 hK hs s

example {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0) (s : ℝ) :
    deriv (deriv (magneticMoment k)) s =
      (2 : ℝ)⁻¹ • ∫ y, cross3 y (space (currentRate (currentRate k) (vector s y))) :=
  deriv_deriv_magneticMoment hk hs s

example {K : Spacetime → Spacetime} {a : ℝ} (hK : Continuous K)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → K (vector t x) = 0) (s : ℝ) :
    ‖∫ y, cross3 y (space (K (vector s y)))‖ ^ 2 =
      (currentMoment K s 1 2 - currentMoment K s 2 1) ^ 2 +
        (currentMoment K s 2 0 - currentMoment K s 0 2) ^ 2 +
        (currentMoment K s 0 1 - currentMoment K s 1 0) ^ 2 :=
  norm_sq_integral_cross3 hK hs s

example (n c e : E3) (κ : ℝ) :
    ‖κ • c + e‖ ^ 2 - inner ℝ n (κ • c + e) ^ 2 =
      κ ^ 2 * (‖c‖ ^ 2 - inner ℝ n c ^ 2) +
        (2 * κ * (inner ℝ c e - inner ℝ n c * inner ℝ n e) + (‖e‖ ^ 2 - inner ℝ n e ^ 2)) :=
  transverse_sq_expand_smul_add n c e κ

example {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0) (s : ℝ) (n : E3) :
    firstCorrection k s n = ∑ l : Fin 3, inner ℝ n (EuclideanSpace.single l 1) •
      ∫ y, y l • space (currentRate (currentRate k) (vector s y)) :=
  firstCorrection_eq_sum hk hs s n

example {K : Spacetime → Spacetime} {a : ℝ} (hK : Continuous K)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → K (vector t x) = 0) (s : ℝ) (l i : Fin 3) :
    (∫ y, y l • space (K (vector s y))) i = currentMoment K s l i :=
  integral_coord_smul_apply hK hs s l i

example (w : Fin 3 → E3) :
    ∫ n : sphere (0 : E3) 1,
      (‖∑ l : Fin 3, inner ℝ (n : E3) (EuclideanSpace.single l 1) • w l‖ ^ 2 -
        inner ℝ (n : E3) (∑ l : Fin 3, inner ℝ (n : E3) (EuclideanSpace.single l 1) • w l) ^ 2)
      ∂sphereMeasure =
      4 * π / 3 * ∑ l : Fin 3, ∑ i : Fin 3, w l i ^ 2 -
        4 * π / 15 * (∑ l : Fin 3, ∑ i : Fin 3, w l i ^ 2 + (∑ l : Fin 3, w l l) ^ 2 +
          ∑ l : Fin 3, ∑ m : Fin 3, w m l * w l m) :=
  integral_transverse_sq_sum w

example (A : Fin 3 → Fin 3 → ℝ) :
    (∑ l : Fin 3, ∑ i : Fin 3, A l i ^ 2) / 3 -
        (∑ l : Fin 3, ∑ i : Fin 3, A l i ^ 2 + (∑ l : Fin 3, A l l) ^ 2 +
          ∑ l : Fin 3, ∑ m : Fin 3, A m l * A l m) / 15 =
      1 / 180 * ∑ i : Fin 3, ∑ j : Fin 3, quadrupoleRate A i j ^ 2 +
        2 / 3 * ((2 : ℝ)⁻¹ ^ 2 *
          ((A 1 2 - A 2 1) ^ 2 + (A 2 0 - A 0 2) ^ 2 + (A 0 1 - A 1 0) ^ 2)) :=
  quadrupole_magnetic_identity A

example {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ} (hk : LocalizedSource k a M N) (hN : 3 ≤ N)
    {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (u : ℝ)
    (hd : ∫ y, space (currentRate k (vector (κ * u) y)) = 0) {n : E3} (hn : ‖n‖ = 1) :
    |angularIntensity (slowCurrent κ k) u n - (κ ^ 2 / (4 * π)) ^ 2 *
        (κ ^ 2 * (‖firstCorrection k (κ * u) n‖ ^ 2 -
          inner ℝ n (firstCorrection k (κ * u) n) ^ 2))| ≤
      (κ ^ 2 / (4 * π)) ^ 2 * (κ ^ 3 * (M ^ 2 * (4 * π / 3 * a ^ 3) ^ 2 * a ^ 3 * (4 + a))) :=
  abs_angularIntensity_slowCurrent_sub_le_of_dipole hk hN hκ0 hκ1 u hd hn

example {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ} (hk : LocalizedSource k a M N) (hN : 3 ≤ N)
    {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (u : ℝ) (hd : deriv (deriv (dipoleMoment k)) (κ * u) = 0) :
    |radiatedPower (slowCurrent κ k) u - κ ^ 6 * (1 / (4 * π)) *
        (1 / 180 * ∑ i : Fin 3, ∑ j : Fin 3,
            deriv (deriv (deriv fun s => quadrupoleMoment k s i j)) (κ * u) ^ 2 +
          2 / 3 * ‖deriv (deriv (magneticMoment k)) (κ * u)‖ ^ 2)| ≤
      4 * π / 9 * M ^ 2 * a ^ 9 * (4 + a) * κ ^ 7 :=
  power_sub_le hk hN hκ0 hκ1 u hd

example {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f f' f'' f''' : ℝ → G} {M : ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : ∀ t, HasDerivAt f' (f'' t) t)
    (hf'' : ∀ t, HasDerivAt f'' (f''' t) t) (hM : ∀ t, ‖f''' t‖ ≤ M) (h : ℝ) :
    ‖f h - f 0 - h • f' 0 - (h ^ 2 / 2) • f'' 0‖ ≤ M * |h| ^ 3 :=
  norm_taylor_three_le hf hf' hf'' hM h

example (k : Spacetime → Spacetime) (s : ℝ) (n : E3) :
    E3 :=
  secondCorrection k s n

example {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0) (s : ℝ) :
    Continuous (secondCorrection k s) :=
  continuous_secondCorrection hk hs s

example {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ} (hk : LocalizedSource k a M N) (hN : 3 ≤ N)
    (s : ℝ) {n : E3} (hn : ‖n‖ = 1) :
    ‖secondCorrection k s n‖ ≤ a ^ 2 * M * (4 * π / 3 * a ^ 3) :=
  norm_secondCorrection_le hk hN s hn

example {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ} (hk : LocalizedSource k a M N) (hN : 4 ≤ N)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (s : ℝ) {n : E3} (hn : ‖n‖ = 1) :
    ‖slowAmplitude k κ s n - (∫ y, space (currentRate k (vector s y))) -
        κ • firstCorrection k s n - (κ ^ 2 / 2) • secondCorrection k s n‖ ≤
      M * κ ^ 3 * a ^ 3 * (4 * π / 3 * a ^ 3) :=
  norm_slowAmplitude_sub_le_three hk hN hκ0 s hn

example (n b c q e : E3) (κ : ℝ) :
    ‖b + κ • c + (κ ^ 2 / 2) • q + e‖ ^ 2 - inner ℝ n (b + κ • c + (κ ^ 2 / 2) • q + e) ^ 2 =
      (‖b‖ ^ 2 - inner ℝ n b ^ 2) + 2 * κ * (inner ℝ b c - inner ℝ n b * inner ℝ n c) +
        κ ^ 2 * ((‖c‖ ^ 2 - inner ℝ n c ^ 2) + (inner ℝ b q - inner ℝ n b * inner ℝ n q)) +
        (2 * (inner ℝ b e - inner ℝ n b * inner ℝ n e) +
          (‖(κ ^ 2 / 2) • q + e‖ ^ 2 - inner ℝ n ((κ ^ 2 / 2) • q + e) ^ 2) +
          2 * κ * (inner ℝ c ((κ ^ 2 / 2) • q + e) -
            inner ℝ n c * inner ℝ n ((κ ^ 2 / 2) • q + e))) :=
  transverse_sq_expand_three n b c q e κ

example {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ} (hk : LocalizedSource k a M N) (hN : 4 ≤ N)
    {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (u : ℝ) :
    |radiatedPower (slowCurrent κ k) u -
        κ ^ 4 * (1 / (6 * π)) * ‖deriv (deriv (dipoleMoment k)) (κ * u)‖ ^ 2 -
        κ ^ 6 * (1 / (4 * π)) * (1 / 180 * ∑ i : Fin 3, ∑ j : Fin 3,
            deriv (deriv (deriv fun s => quadrupoleMoment k s i j)) (κ * u) ^ 2 +
          2 / 3 * ‖deriv (deriv (magneticMoment k)) (κ * u)‖ ^ 2) -
        κ ^ 6 / (16 * π ^ 2) * ∫ n : sphere (0 : E3) 1,
          (inner ℝ (deriv (deriv (dipoleMoment k)) (κ * u)) (secondCorrection k (κ * u) n) -
            inner ℝ (n : E3) (deriv (deriv (dipoleMoment k)) (κ * u)) *
              inner ℝ (n : E3) (secondCorrection k (κ * u) n)) ∂sphereMeasure| ≤
      4 * π / 9 * M ^ 2 * a ^ 9 * (6 + 4 * a + a * (1 / 2 + a) ^ 2) * κ ^ 7 :=
  power_general hk hN hκ0 hκ1 u

example {f : E3 → ℝ} {r : ℝ} (hf : ContDiff ℝ ∞ f) (hs : ∀ x, r < ‖x‖ → f x = 0) :
    ∫ y, partialOne f y = 0 :=
  integral_partialOne_eq_zero hf hs

example :
    Spacetime → Spacetime :=
  oscillatingQuadrupole

example (x : E3) (hx : 2 < ‖x‖) :
    partialOne dipoleBump x = 0 :=
  partialOne_dipoleBump_eq_zero x hx

example :
    ∃ B, ∀ x, |partialOne dipoleBump x| ≤ B :=
  exists_bound_partialOne_dipoleBump

example :
    ∃ M, ∀ N, LocalizedSource oscillatingQuadrupole 2 M N :=
  exists_localizedSource_oscillatingQuadrupole

example (s : ℝ) :
    dipoleMoment oscillatingQuadrupole s = 0 :=
  dipoleMoment_oscillatingQuadrupole s

example (s : ℝ) (l i : Fin 3) :
    currentMoment (currentRate (currentRate oscillatingQuadrupole)) s l i =
      sin s * (∫ y, dipoleBump y) *
        ((EuclideanSpace.single 0 (1 : ℝ) : E3) i * (EuclideanSpace.single 0 (1 : ℝ) : E3) l) :=
  currentMoment_oscillatingQuadrupole s l i

example (s : ℝ) :
    deriv (deriv (deriv fun s => quadrupoleMoment oscillatingQuadrupole s 0 0)) s =
      4 * sin s * ∫ y, dipoleBump y :=
  deriv_deriv_deriv_quadrupoleMoment_oscillatingQuadrupole s

example :
    deriv (deriv (deriv fun s => quadrupoleMoment oscillatingQuadrupole s 0 0)) (π / 2) ≠ 0 :=
  deriv_deriv_deriv_quadrupoleMoment_oscillatingQuadrupole_ne_zero

example (s : ℝ) :
    ∑ i : Fin 3, ∑ j : Fin 3,
        deriv (deriv (deriv fun s => quadrupoleMoment oscillatingQuadrupole s i j)) s ^ 2 =
      24 * sin s ^ 2 * (∫ y, dipoleBump y) ^ 2 :=
  sum_sq_quadrupole_oscillatingQuadrupole s

example (s : ℝ) :
    ‖deriv (deriv (magneticMoment oscillatingQuadrupole)) s‖ ^ 2 = 0 :=
  norm_magneticMoment_oscillatingQuadrupole s

example :
    ∃ C, ∀ κ : ℝ, 0 < κ → κ ≤ 1 → ∀ u : ℝ,
    |radiatedPower (slowCurrent κ oscillatingQuadrupole) u -
        κ ^ 6 * (1 / (30 * π)) * (sin (κ * u) ^ 2 * (∫ y, dipoleBump y) ^ 2)| ≤ C * κ ^ 7 :=
  power_oscillatingQuadrupole

end ProjectAinos.Electrodynamics.Radiation

end Multipole

section Relativistic

open MeasureTheory Set Metric Real Filter

open scoped Topology

namespace ProjectAinos.Electrodynamics.Radiation.Relativistic

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Sphere SmoothGeometry.DifferentialForm
  SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (u v : E3) :
    E3 :=
  cross u v

example (u v : E3) :
    WithLp.ofLp (cross u v) = crossProduct (WithLp.ofLp u) (WithLp.ofLp v) :=
  ofLp_cross u v

example (u v w : E3) :
    cross u (cross v w) = inner ℝ u w • v - inner ℝ u v • w :=
  cross_cross u v w

example (u v : E3) :
    inner ℝ u (cross u v) = 0 :=
  inner_cross_self u v

example (u v : E3) :
    ‖cross u v‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - inner ℝ u v ^ 2 :=
  norm_cross_sq u v

example {n : E3} (hn : ‖n‖ = 1) (v a : E3) :
    ‖cross n (cross (n - v) a)‖ ^ 2 =
      (1 - inner ℝ n v) ^ 2 * ‖a‖ ^ 2 + 2 * (1 - inner ℝ n v) * inner ℝ v a * inner ℝ n a -
        (1 - ‖v‖ ^ 2) * inner ℝ n a ^ 2 :=
  norm_cross_cross_sq hn v a

example (n v a : E3) :
    inner ℝ (cross n (cross v a)) n = 0 :=
  inner_cross_cross_left n v a

example {G : Field} {y : Spacetime} {n X : Space 3} (hE : electricVector (G y) = WithLp.ofLp X)
    (hB : magneticVector (G y) = crossProduct (WithLp.ofLp n) (WithLp.ofLp X)) :
    ∑ i : Fin 3, poyntingVector G i y * n i = ‖X‖ ^ 2 * ‖n‖ ^ 2 - inner ℝ X n ^ 2 :=
  sum_poyntingVector_mul_eq hE hB

example {n X : E3} (hn : ‖n‖ = 1) (hX : inner ℝ X n = 0) :
    inner ℝ (cross X (cross n X)) n = ‖X‖ ^ 2 :=
  inner_cross_cross_self hn hX

variable (w : SubluminalWorldline)

example (τ : ℝ) {n : E3} (hn : ‖n‖ = 1) :
    0 < 1 - inner ℝ n (deriv w.r τ) :=
  one_sub_inner_pos w τ hn

example (e : ℝ) {τ ρ : ℝ} (hρ : 0 < ρ) {n : Space 3} (hn : ‖n‖ = 1) :
    ρ ^ 2 * ∑ i : Fin 3, poyntingVector (fieldTensor (lienardWiechert e w)) i
        (Minkowski.vector (τ + ρ) (w.r τ + ρ • n)) * n i =
      e ^ 2 / (16 * π ^ 2 * (1 - inner ℝ n (deriv w.r τ)) ^ 6) *
        (‖cross n (cross (n - deriv w.r τ) (deriv (deriv w.r) τ))‖ ^ 2 +
          2 * (1 - ‖deriv w.r τ‖ ^ 2) *
            inner ℝ (n - deriv w.r τ) (cross n (cross (n - deriv w.r τ) (deriv (deriv w.r) τ))) /
              ρ +
          (1 - ‖deriv w.r τ‖ ^ 2) ^ 2 *
            (‖n - deriv w.r τ‖ ^ 2 - inner ℝ (n - deriv w.r τ) n ^ 2) / ρ ^ 2) :=
  sq_mul_inner_poyntingVector_lightCone w e hρ hn

example (e : ℝ) {τ ρ : ℝ} (hρ : 0 < ρ) {n : Space 3} (hn : ‖n‖ = 1) :
    LienardWiechert.accelerationField e w (τ + ρ) (w.r τ + ρ • n) =
      (e / (4 * π * ρ * (1 - inner ℝ n (deriv w.r τ)) ^ 3)) •
        cross n (cross (n - deriv w.r τ) (deriv (deriv w.r) τ)) :=
  accelerationField_lightCone_eq_cross w e hρ hn

example (e : ℝ) {τ ρ : ℝ} (hρ : 0 < ρ) {n : Space 3} (hn : ‖n‖ = 1) :
    inner ℝ (LienardWiechert.accelerationField e w (τ + ρ) (w.r τ + ρ • n)) n = 0 :=
  inner_accelerationField_lightCone w e hρ hn

example (e : ℝ) {τ ρ : ℝ} (hρ : 0 < ρ) {n : Space 3} (hn : ‖n‖ = 1) :
    ρ ^ 2 * inner ℝ (cross (LienardWiechert.accelerationField e w (τ + ρ) (w.r τ + ρ • n))
        (cross n (LienardWiechert.accelerationField e w (τ + ρ) (w.r τ + ρ • n)))) n =
      e ^ 2 * ‖cross n (cross (n - deriv w.r τ) (deriv (deriv w.r) τ))‖ ^ 2 /
        (16 * π ^ 2 * (1 - inner ℝ n (deriv w.r τ)) ^ 6) :=
  sq_mul_inner_cross_cross_accelerationField_lightCone w e hρ hn

example (e : ℝ) (v a n : E3) :
    ℝ :=
  angularPower e v a n

example (e τ : ℝ) {n : Space 3} (hn : ‖n‖ = 1) :
    Tendsto (fun ρ => ρ ^ 2 * ∑ i : Fin 3, poyntingVector (fieldTensor (lienardWiechert e w)) i
        (Minkowski.vector (τ + ρ) (w.r τ + ρ • n)) * n i) atTop
      (𝓝 (e ^ 2 * ‖cross n (cross (n - deriv w.r τ) (deriv (deriv w.r) τ))‖ ^ 2 /
        (16 * π ^ 2 * (1 - inner ℝ n (deriv w.r τ)) ^ 6))) :=
  tendsto_sq_mul_inner_poyntingVector_lightCone w e τ hn

example (e τ : ℝ) {n : Space 3} (hn : ‖n‖ = 1) :
    Tendsto (fun ρ => ρ ^ 2 * (∑ i : Fin 3, poyntingVector (fieldTensor (lienardWiechert e w)) i
        (Minkowski.vector (τ + ρ) (w.r τ + ρ • n)) * n i) * (1 - inner ℝ n (deriv w.r τ))) atTop
      (𝓝 (angularPower e (deriv w.r τ) (deriv (deriv w.r) τ) n)) :=
  tendsto_sq_mul_inner_poyntingVector_mul_lightCone w e τ hn

example {τ ρ : ℝ} (hρ : 0 < ρ) {n : Space 3} (hn : ‖n‖ = 1) :
    fderiv ℝ (fun p : ℝ × Space 3 => w.retardedTime p.1 p.2) (τ + ρ, w.r τ + ρ • n) (1, 0) =
      (1 - inner ℝ n (deriv w.r τ))⁻¹ :=
  fderiv_retardedTime_time_lightCone w hρ hn

example {β : ℝ} (hβ : |β| < 1) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    0 < 1 - β * s :=
  one_sub_mul_pos hβ hs

example {β : ℝ} (hβ : |β| < 1) {p : ℝ → ℝ} (hp : ContinuousOn p (Icc (-1) 1)) (m : ℕ) :
    ContinuousOn (fun s => p s / (1 - β * s) ^ m) (Icc (-1) 1) :=
  continuousOn_div_one_sub_mul_pow hβ hp m

example {β : ℝ} (hβ : |β| < 1) :
    ∫ s in (-1 : ℝ)..1, 1 / (1 - β * s) ^ 3 = 2 / (1 - β ^ 2) ^ 2 :=
  integral_one_div_one_sub_mul_pow_three hβ

example {β : ℝ} (hβ : |β| < 1) :
    ∫ s in (-1 : ℝ)..1, s / (1 - β * s) ^ 3 = 2 * β / (1 - β ^ 2) ^ 2 :=
  integral_div_one_sub_mul_pow_three hβ

example {β : ℝ} (hβ : |β| < 1) :
    ∫ s in (-1 : ℝ)..1, (1 - s ^ 2) / (1 - β * s) ^ 5 = 4 / (3 * (1 - β ^ 2) ^ 3) :=
  integral_one_sub_sq_div_one_sub_mul_pow_five hβ

example {β : ℝ} (hβ : |β| < 1) :
    ∫ s in (-1 : ℝ)..1, s * (1 - s ^ 2) / (1 - β * s) ^ 5 = 4 * β / (3 * (1 - β ^ 2) ^ 3) :=
  integral_mul_one_sub_sq_div_one_sub_mul_pow_five hβ

example {ê : E3} (he : ‖ê‖ = 1) {β : ℝ} (hβ : |β| < 1) (a : E3) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc (-1) 1)) :
    ∫ n : sphere (0 : E3) 1, g (inner ℝ (n : E3) ê) *
        (‖cross n (cross ((n : E3) - β • ê) a)‖ ^ 2 / (1 - inner ℝ (n : E3) (β • ê)) ^ 5)
        ∂sphereMeasure =
      2 * π * (inner ℝ a ê ^ 2 * (∫ s in (-1 : ℝ)..1, g s * (1 - s ^ 2) / (1 - β * s) ^ 5) +
        ‖a - inner ℝ a ê • ê‖ ^ 2 * ((∫ s in (-1 : ℝ)..1, g s / (1 - β * s) ^ 3) -
          (1 - β ^ 2) / 2 * ∫ s in (-1 : ℝ)..1, g s * (1 - s ^ 2) / (1 - β * s) ^ 5)) :=
  integral_comp_inner_mul_lienard he hβ a hg

example {v : E3} (hv : ‖v‖ < 1) (a : E3) :
    ∫ n : sphere (0 : E3) 1, ‖cross n (cross ((n : E3) - v) a)‖ ^ 2 /
        (1 - inner ℝ (n : E3) v) ^ 5 ∂sphereMeasure =
      8 * π / 3 * ((1 - ‖v‖ ^ 2)⁻¹) ^ 3 * (‖a‖ ^ 2 - ‖cross v a‖ ^ 2) :=
  integral_lienard hv a

example {v : E3} (hv : ‖v‖ < 1) (n : sphere (0 : E3) 1) :
    0 < 1 - inner ℝ (n : E3) v :=
  one_sub_inner_pos_of_norm_lt hv n

example (e : ℝ) {v : E3} (hv : ‖v‖ < 1) (a : E3) (n : sphere (0 : E3) 1) :
    0 ≤ angularPower e v a n :=
  angularPower_nonneg e hv a n

example (e : ℝ) {v : E3} (hv : ‖v‖ < 1) (a : E3) :
    Continuous fun n : sphere (0 : E3) 1 => angularPower e v a n :=
  continuous_angularPower e hv a

example (e : ℝ) {v a : E3} (hv : ‖v‖ < 1) (hva : inner ℝ v a = 0) {n : E3} (hn : ‖n‖ = 1) :
    angularPower e v a n = e ^ 2 / (16 * π ^ 2) *
      (‖a‖ ^ 2 / (1 - inner ℝ n v) ^ 3 -
        (1 - ‖v‖ ^ 2) * inner ℝ n a ^ 2 / (1 - inner ℝ n v) ^ 5) :=
  angularPower_of_inner_eq_zero e hv hva hn

example (e : ℝ) {v : E3} (hv : ‖v‖ < 1) (a : E3) :
    ∫ n : sphere (0 : E3) 1, angularPower e v a n ∂sphereMeasure =
      2 / 3 * (e ^ 2 / (4 * π)) * ((1 - ‖v‖ ^ 2)⁻¹) ^ 3 * (‖a‖ ^ 2 - ‖cross v a‖ ^ 2) :=
  integral_angularPower e hv a

example (e : ℝ) {ê : E3} (he : ‖ê‖ = 1) {β : ℝ} (hβ : |β| < 1) (a : E3) :
    ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) ê * angularPower e (β • ê) a n ∂sphereMeasure =
      β * ∫ n : sphere (0 : E3) 1, angularPower e (β • ê) a n ∂sphereMeasure :=
  integral_inner_mul_angularPower_of_eq_smul e he hβ a

example (e : ℝ) {v : E3} (hv : ‖v‖ < 1) (a : E3) :
    ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) v * angularPower e v a n ∂sphereMeasure =
      ‖v‖ ^ 2 * ∫ n : sphere (0 : E3) 1, angularPower e v a n ∂sphereMeasure :=
  integral_inner_mul_angularPower e hv a

example {v a : E3} {γ : ℝ} (hγ : γ ^ 2 * (1 - ‖v‖ ^ 2) = 1) :
    ‖γ ^ 2 • a + (γ ^ 4 * inner ℝ v a) • v‖ ^ 2 - (γ ^ 4 * inner ℝ v a) ^ 2 =
      γ ^ 6 * (‖a‖ ^ 2 - ‖cross v a‖ ^ 2) :=
  norm_sq_fourAcceleration hγ

example (e τ : ℝ) :
    Tendsto (fun ρ => ∫ n : sphere (0 : E3) 1, ρ ^ 2 * (∑ i : Fin 3,
        poyntingVector (fieldTensor (lienardWiechert e w)) i
          (Minkowski.vector (τ + ρ) (w.r τ + ρ • (n : E3))) * (n : E3) i) *
        (1 - inner ℝ (n : E3) (deriv w.r τ)) ∂sphereMeasure) atTop
      (𝓝 (2 / 3 * (e ^ 2 / (4 * π)) * ((1 - ‖deriv w.r τ‖ ^ 2)⁻¹) ^ 3 *
        (‖deriv (deriv w.r) τ‖ ^ 2 - ‖cross (deriv w.r τ) (deriv (deriv w.r) τ)‖ ^ 2))) :=
  tendsto_integral_power_lightCone w e τ

end ProjectAinos.Electrodynamics.Radiation.Relativistic

end Relativistic

section Synchrotron

open MeasureTheory Set Metric Real Filter

open scoped Topology

namespace ProjectAinos.Electrodynamics.Radiation.Synchrotron

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Sphere SpecialRelativity
  Relativistic SubluminalWorldline

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (R Ω : ℝ) (h : |R * Ω| < 1) (t : ℝ) :
    deriv (circular R Ω h).r t =
      (-(R * Ω) * Real.sin (Ω * t)) • EuclideanSpace.single 0 1 +
        (R * Ω * Real.cos (Ω * t)) • EuclideanSpace.single 1 1 :=
  deriv_circular R Ω h t

example (R Ω : ℝ) (h : |R * Ω| < 1) (t : ℝ) :
    deriv (deriv (circular R Ω h).r) t = (-Ω ^ 2) • circularPath R Ω t :=
  deriv_deriv_circular R Ω h t

example (R Ω : ℝ) (h : |R * Ω| < 1) (t : ℝ) :
    ‖deriv (circular R Ω h).r t‖ ^ 2 = (R * Ω) ^ 2 :=
  norm_sq_deriv_circular R Ω h t

example (R Ω t : ℝ) :
    ‖circularPath R Ω t‖ ^ 2 = R ^ 2 :=
  norm_sq_circularPath R Ω t

example (R Ω : ℝ) (h : |R * Ω| < 1) (t : ℝ) :
    ‖deriv (deriv (circular R Ω h).r) t‖ ^ 2 = R ^ 2 * Ω ^ 4 :=
  norm_sq_deriv_deriv_circular R Ω h t

example (R Ω : ℝ) (h : |R * Ω| < 1) (t : ℝ) :
    ‖deriv (deriv (circular R Ω h).r) t‖ = |Ω| * ‖deriv (circular R Ω h).r t‖ :=
  norm_deriv_deriv_circular R Ω h t

example (R Ω : ℝ) (h : |R * Ω| < 1) (t : ℝ) :
    inner ℝ (deriv (circular R Ω h).r t) (deriv (deriv (circular R Ω h).r) t) = 0 :=
  inner_deriv_deriv_circular R Ω h t

example (R Ω : ℝ) :
    ℝ :=
  gamma R Ω

example {R Ω : ℝ} (h : |R * Ω| < 1) :
    0 < gamma R Ω :=
  gamma_pos h

example {R Ω : ℝ} (h : |R * Ω| < 1) :
    gamma R Ω ^ 2 = (1 - (R * Ω) ^ 2)⁻¹ :=
  gamma_sq h

example (e R Ω : ℝ) :
    ℝ :=
  synchrotronPower e R Ω

example (e : ℝ) {R Ω : ℝ} (h : |R * Ω| < 1) :
    synchrotronPower e R Ω = 2 / 3 * (e ^ 2 / (4 * π)) * gamma R Ω ^ 4 * (R * Ω) ^ 2 * Ω ^ 2 :=
  synchrotronPower_eq_gamma e h

example (e R Ω : ℝ) (h : |R * Ω| < 1) (τ : ℝ) :
    ∫ n : sphere (0 : E3) 1, angularPower e (deriv (circular R Ω h).r τ)
        (deriv (deriv (circular R Ω h).r) τ) n ∂sphereMeasure = synchrotronPower e R Ω :=
  integral_angularPower_circular e R Ω h τ

example (e R Ω : ℝ) (h : |R * Ω| < 1) (τ : ℝ) :
    Tendsto (fun ρ => ∫ n : sphere (0 : E3) 1, ρ ^ 2 * (∑ i : Fin 3,
        poyntingVector (fieldTensor (lienardWiechert e (circular R Ω h))) i
          (Minkowski.vector (τ + ρ) ((circular R Ω h).r τ + ρ • (n : E3))) * (n : E3) i) *
        (1 - inner ℝ (n : E3) (deriv (circular R Ω h).r τ)) ∂sphereMeasure) atTop
      (𝓝 (synchrotronPower e R Ω)) :=
  tendsto_integral_power_lightCone_circular e R Ω h τ

example (e R Ω : ℝ) (h : |R * Ω| < 1) (τ : ℝ) {n : E3} (hn : ‖n‖ = 1) :
    angularPower e (deriv (circular R Ω h).r τ) (deriv (deriv (circular R Ω h).r) τ) n =
      e ^ 2 * Ω ^ 4 / (16 * π ^ 2) *
        (R ^ 2 / (1 - inner ℝ n (deriv (circular R Ω h).r τ)) ^ 3 -
          (1 - (R * Ω) ^ 2) * inner ℝ n (circularPath R Ω τ) ^ 2 /
            (1 - inner ℝ n (deriv (circular R Ω h).r τ)) ^ 5) :=
  angularPower_circular e R Ω h τ hn

example (e R Ω : ℝ) :
    ℝ :=
  lossPerTurn e R Ω

example (e R Ω : ℝ) (h : |R * Ω| < 1) (τ : ℝ) :
    ∫ t in τ..τ + 2 * π / |Ω|, (∫ n : sphere (0 : E3) 1, angularPower e
        (deriv (circular R Ω h).r t) (deriv (deriv (circular R Ω h).r) t) n ∂sphereMeasure) =
      lossPerTurn e R Ω :=
  integral_integral_angularPower_circular e R Ω h τ

example (e R : ℝ) {Ω : ℝ} (hΩ : Ω ≠ 0) :
    lossPerTurn e R Ω =
      4 * π / 3 * (e ^ 2 / (4 * π)) * ((1 - (R * Ω) ^ 2)⁻¹) ^ 2 * (R * Ω) ^ 2 * |Ω| :=
  lossPerTurn_eq e R hΩ

example (e m : ℝ) {R Ω : ℝ} (h : |R * Ω| < 1) (hm : m ≠ 0) (hΩ : Ω ≠ 0) :
    lossPerTurn e R Ω / (m * gamma R Ω) =
      4 * π / 3 * (e ^ 2 / (4 * π)) * gamma R Ω ^ 3 * (R * Ω) ^ 2 * |Ω| / m :=
  lossPerTurn_div_energy e m h hm hΩ

example (e : ℝ) {m R Ω : ℝ} (h : |R * Ω| < 1) (hm : 0 < m) (hΩ : Ω ≠ 0) {N ε : ℝ}
    (hN : N * (4 * π / 3 * (e ^ 2 / (4 * π)) * gamma R Ω ^ 3 * (R * Ω) ^ 2 * |Ω| / m) ≤ ε) :
    N * lossPerTurn e R Ω ≤ ε * (m * gamma R Ω) :=
  mul_lossPerTurn_le e h hm hΩ hN

example {m e B R Ω : ℝ} (h : |R * Ω| < 1) (hB : m * gamma R Ω * Ω = -(e * B)) (t : ℝ) :
    HasDerivAt (fun t => (m * (√(1 - ‖deriv (circular R Ω h).r t‖ ^ 2))⁻¹) •
        deriv (circular R Ω h).r t)
      (e • cross (deriv (circular R Ω h).r t) (B • EuclideanSpace.single 2 1)) t :=
  hasDerivAt_momentum_circular h hB t

example (m : ℝ) {e : ℝ} (he : e ≠ 0) (R Ω : ℝ) :
    ∃ B : ℝ, m * gamma R Ω * Ω = -(e * B) :=
  exists_magnetic_circular m he R Ω

example {m e B R Ω : ℝ} (h : |R * Ω| < 1) (hm : m ≠ 0) (hB : m * gamma R Ω * Ω = -(e * B)) :
    synchrotronPower e R Ω =
      2 / 3 * (e ^ 2 / (4 * π)) * (e * B) ^ 2 * gamma R Ω ^ 2 * (R * Ω) ^ 2 / m ^ 2 :=
  synchrotronPower_eq_magnetic h hm hB

end ProjectAinos.Electrodynamics.Radiation.Synchrotron

end Synchrotron

section Ultrarelativistic

open MeasureTheory Set Metric Real Filter

open scoped Topology

namespace ProjectAinos.Electrodynamics.Radiation.Ultrarelativistic

open SmoothGeometry SmoothGeometry.Sphere Relativistic

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ π) :
    2 * θ ^ 2 / π ^ 2 ≤ 1 - Real.cos θ :=
  two_mul_sq_div_pi_sq_le_one_sub_cos h0 hπ

example (ê : E3) (θ : ℝ) :
    Set (sphere (0 : E3) 1) :=
  outsideCone ê θ

example {ê : E3} (he : ‖ê‖ = 1) (n : sphere (0 : E3) 1) :
    InnerProductGeometry.angle (n : E3) ê = Real.arccos (inner ℝ (n : E3) ê) :=
  angle_eq_arccos he n

example {ê : E3} (he : ‖ê‖ = 1) (θ : ℝ) :
    MeasurableSet (outsideCone ê θ) :=
  measurableSet_outsideCone he θ

example {ê : E3} (he : ‖ê‖ = 1) {θ : ℝ} (hθ : 0 < θ) {n : sphere (0 : E3) 1}
    (hn : n ∈ outsideCone ê θ) :
    2 * θ ^ 2 / π ^ 2 ≤ 1 - inner ℝ (n : E3) ê :=
  le_one_sub_inner_of_mem_outsideCone he hθ hn

example (e : ℝ) {ê : E3} (he : ‖ê‖ = 1) {β : ℝ} (hβ : |β| < 1) (a : E3) :
    ∫ n : sphere (0 : E3) 1, (1 - inner ℝ (n : E3) ê) * angularPower e (β • ê) a n
        ∂sphereMeasure =
      (1 - β) * ∫ n : sphere (0 : E3) 1, angularPower e (β • ê) a n ∂sphereMeasure :=
  integral_one_sub_inner_mul_angularPower e he hβ a

example (e : ℝ) {ê : E3} (he : ‖ê‖ = 1) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (a : E3) {c : ℝ}
    (hc : 0 < c) :
    ∫ n : sphere (0 : E3) 1, (outsideCone ê (c * √(1 - β ^ 2))).indicator
        (fun n => angularPower e (β • ê) a n) n ∂sphereMeasure ≤
      π ^ 2 / (2 * c ^ 2 * (1 + β)) *
        ∫ n : sphere (0 : E3) 1, angularPower e (β • ê) a n ∂sphereMeasure :=
  integral_indicator_outsideCone_le e he hβ0 hβ1 a hc

example (e : ℝ) {ê : E3} (he : ‖ê‖ = 1) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (a : E3) {c : ℝ}
    (hc : 0 < c) :
    ∫ n : sphere (0 : E3) 1, (outsideCone ê (c * √(1 - β ^ 2))).indicator
        (fun n => angularPower e (β • ê) a n) n ∂sphereMeasure ≤
      π ^ 2 / (2 * c ^ 2) *
        ∫ n : sphere (0 : E3) 1, angularPower e (β • ê) a n ∂sphereMeasure :=
  integral_indicator_outsideCone_le_uniform e he hβ0 hβ1 a hc

example :
    Tendsto (fun c : ℝ => π ^ 2 / (2 * c ^ 2)) atTop (𝓝 0) :=
  tendsto_concentrationBound

example (e α β : ℝ) {ê n : E3} (he : ‖ê‖ = 1) (hn : ‖n‖ = 1) :
    angularPower e (β • ê) (α • ê) n =
      e ^ 2 * α ^ 2 * (1 - inner ℝ n ê ^ 2) / (16 * π ^ 2 * (1 - β * inner ℝ n ê) ^ 5) :=
  angularPower_smul_smul e α β he hn

example (e β : ℝ) {ê a n : E3} (he : ‖ê‖ = 1) (hβ : |β| < 1) (ha : inner ℝ a ê = 0) (hn : ‖n‖ = 1) :
    angularPower e (β • ê) a n = e ^ 2 / (16 * π ^ 2) *
      (‖a‖ ^ 2 / (1 - β * inner ℝ n ê) ^ 3 -
        (1 - β ^ 2) * inner ℝ n a ^ 2 / (1 - β * inner ℝ n ê) ^ 5) :=
  angularPower_smul_of_inner_eq_zero e β he hβ ha hn

end ProjectAinos.Electrodynamics.Radiation.Ultrarelativistic

end Ultrarelativistic
