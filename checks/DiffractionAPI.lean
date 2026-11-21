/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.Electrodynamics.Diffraction.Aperture
import ProjectAinos.Electrodynamics.Diffraction.StraightEdge
import ProjectAinos.Electrodynamics.Diffraction.Fraunhofer

/-! Public consumers of diffraction in the scalar aperture model (Landau–Lifshitz §§59–61): the
Rayleigh–Sommerfeld field of an aperture with its smoothness, the Helmholtz equation, the boundary
values and the radiation condition, the Fresnel approximation with an explicit remainder, the
Fraunhofer limit with its rate, and Babinet's principle. Default elaborator options are
intentional: these checks must not rely on the implementation's transparency settings. Every
statement is pinned with its type. -/

noncomputable section


section Aperture

open MeasureTheory Filter Set Metric Complex

open scoped Topology ContDiff Laplacian InnerProductSpace Real

namespace ProjectAinos.Electrodynamics.Diffraction

local notation "E2" => EuclideanSpace ℝ (Fin 2)

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (y : E2) :
    E3 :=
  planePoint y

example (x : E2) (z : ℝ) :
    E3 :=
  spacePoint x z

example :
    Set E3 :=
  upperHalfSpace

example (y : E2) :
    planePoint y 2 = 0 :=
  planePoint_apply_two y

example (x : E2) (z : ℝ) :
    spacePoint x z 2 = z :=
  spacePoint_apply_two x z

example (p : E3) (y : E2) :
    (p - planePoint y) 2 = p 2 :=
  sub_planePoint_apply_two p y

example (q : E3) :
    ‖q‖ ^ 2 = q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 :=
  norm_sq_eq_three q

example (y : E2) :
    ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 :=
  norm_sq_eq_two y

example (x : E2) (z : ℝ) :
    ‖spacePoint x z‖ ^ 2 = ‖x‖ ^ 2 + z ^ 2 :=
  norm_sq_spacePoint x z

example (x : E2) (z : ℝ) :
    ‖spacePoint x z‖ = √(‖x‖ ^ 2 + z ^ 2) :=
  norm_spacePoint x z

example (y : E2) :
    ‖planePoint y‖ = ‖y‖ :=
  norm_planePoint y

example (x y : E2) (z : ℝ) :
    spacePoint x z - planePoint y = spacePoint (x - y) z :=
  spacePoint_sub_planePoint x y z

example (c : ℝ) (x : E2) (z : ℝ) :
    spacePoint (c • x) (c * z) = c • spacePoint x z :=
  spacePoint_smul c x z

example :
    Continuous planePoint :=
  continuous_planePoint

example :
    IsOpen upperHalfSpace :=
  isOpen_upperHalfSpace

example (p : E3) (y : E2) :
    ⟪p, planePoint y⟫_ℝ = p 0 * y 0 + p 1 * y 1 :=
  inner_planePoint p y

example {p q : E3} (hq : q ∈ closedBall p (p 2 / 2)) :
    p 2 / 2 ≤ q 2 :=
  half_le_of_mem_closedBall hq

example {p : E3} (hp : 0 < p 2) (y : E2) :
    p - planePoint y ≠ 0 :=
  sub_planePoint_ne_zero hp y

example (k R : ℝ) :
    ℂ :=
  kernelProfile k R

example (k R : ℝ) :
    ℂ :=
  kernelSlope k R

example (k R : ℝ) :
    ℂ :=
  kernelSlopeDeriv k R

example (k : ℝ) (q : E3) :
    ℂ :=
  sphericalWave k q

example (k : ℝ) (q : E3) :
    ℂ :=
  rayleighKernel k q

example (k R : ℝ) :
    HasDerivAt (fun R : ℝ => cexp (I * k * R)) (cexp (I * k * R) * (I * k)) R :=
  hasDerivAt_cexp_I_mul k R

example (k R : ℝ) :
    ‖cexp (I * k * R)‖ = 1 :=
  norm_cexp_I_mul k R

example (k : ℝ) {R : ℝ} (hR : R ≠ 0) :
    HasDerivAt (kernelProfile k) (R * kernelSlope k R) R :=
  hasDerivAt_kernelProfile k hR

example (k : ℝ) {R : ℝ} (hR : R ≠ 0) :
    HasDerivAt (kernelSlope k) (kernelSlopeDeriv k R) R :=
  hasDerivAt_kernelSlope k hR

example (k : ℝ) {R : ℝ} (hR : R ≠ 0) :
    5 * kernelSlope k R + R * kernelSlopeDeriv k R + k ^ 2 * kernelProfile k R = 0 :=
  kernelSlope_radial k hR

example (k : ℝ) {R : ℝ} (hR : R ≠ 0) :
    kernelSlope k R = I * k * kernelProfile k R / R +
      cexp (I * k * R) * (2 * I * k * R - 3) / (2 * π * R ^ 5) :=
  kernelSlope_eq k hR

example {q : E3} (hq : q ≠ 0) :
    HasFDerivAt (fun y : E3 => ‖y‖) (‖q‖⁻¹ • innerSL ℝ q) q :=
  hasFDerivAt_norm_of_ne_zero hq

example (q : E3) :
    HasFDerivAt (fun y : E3 => ((y 2 : ℝ) : ℂ))
      (ofRealCLM.comp (EuclideanSpace.proj (2 : Fin 3))) q :=
  hasFDerivAt_height q

example {f : ℝ → ℂ} {f' : ℂ} {q : E3} (hq : q ≠ 0) (hf : HasDerivAt f f' ‖q‖) :
    HasFDerivAt (fun y : E3 => f ‖y‖) ((‖q‖⁻¹ • innerSL ℝ q).smulRight f') q :=
  hasFDerivAt_comp_norm hq hf

example (k : ℝ) {q : E3} (hq : q ≠ 0) :
    HasFDerivAt (rayleighKernel k)
      (((q 2 : ℝ) : ℂ) • ((‖q‖⁻¹ • innerSL ℝ q).smulRight (‖q‖ * kernelSlope k ‖q‖)) +
        kernelProfile k ‖q‖ • ofRealCLM.comp (EuclideanSpace.proj (2 : Fin 3))) q :=
  hasFDerivAt_rayleighKernel k hq

example (k : ℝ) {q : E3} (hq : q ≠ 0) (v : E3) :
    fderiv ℝ (rayleighKernel k) q v =
      v 2 * kernelProfile k ‖q‖ + q 2 * kernelSlope k ‖q‖ * ⟪q, v⟫_ℝ :=
  fderiv_rayleighKernel_apply k hq v

example (k : ℝ) {q : E3} (hq : q ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (rayleighKernel k) q :=
  contDiffAt_rayleighKernel k hq

example (k : ℝ) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (rayleighKernel k) upperHalfSpace :=
  contDiffOn_rayleighKernel k

example (k : ℝ) {q : E3} (hq : q ≠ 0) :
    rayleighKernel k q = -2 * fderiv ℝ (sphericalWave k) q (EuclideanSpace.single 2 1) :=
  rayleighKernel_eq_fderiv_sphericalWave k hq

example {f : E3 → ℂ} {x : E3} (hf : ContDiffAt ℝ 2 f x) :
    Δ f x = ∑ i, fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1) :=
  laplacian_eq_sum_fderiv hf

example (k : ℝ) {q : E3} (hq : q ≠ 0) (v : E3) :
    fderiv ℝ (fun y => fderiv ℝ (rayleighKernel k) y v) q v =
      2 * v 2 * kernelSlope k ‖q‖ * ⟪q, v⟫_ℝ +
        q 2 * kernelSlopeDeriv k ‖q‖ / ‖q‖ * ⟪q, v⟫_ℝ ^ 2 +
        q 2 * kernelSlope k ‖q‖ * ⟪v, v⟫_ℝ :=
  fderiv_fderiv_rayleighKernel k hq v

example (k : ℝ) {q : E3} (hq : q ≠ 0) :
    ∑ i, fderiv ℝ (fun y => fderiv ℝ (rayleighKernel k) y (EuclideanSpace.single i 1)) q
      (EuclideanSpace.single i 1) = -(k ^ 2) * rayleighKernel k q :=
  sum_fderiv_fderiv_rayleighKernel k hq

example (k : ℝ) {q : E3} (hq : q ≠ 0) :
    Δ (rayleighKernel k) q + k ^ 2 * rayleighKernel k q = 0 :=
  helmholtz_rayleighKernel k hq

section PlaneIntegral

universe u

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℂ V]

example (u₀ : E2 → ℂ) (g : E3 → V) (p : E3) :
    V :=
  planeIntegral u₀ g p

example {u₀ : E2 → ℂ} (hc : Continuous u₀) (hs : HasCompactSupport u₀) {g : E3 → V}
    (hg : ContinuousOn g upperHalfSpace) {p : E3} (hp : 0 < p 2) :
    Integrable (fun y => u₀ y • g (p - planePoint y)) :=
  integrable_planeIntegrand hc hs hg hp

example {u₀ : E2 → ℂ} (hc : Continuous u₀) (hs : HasCompactSupport u₀) {g : E3 → V}
    (hg : ContDiffOn ℝ 1 g upperHalfSpace) {p : E3} (hp : 0 < p 2) :
    HasFDerivAt (planeIntegral u₀ g) (planeIntegral u₀ (fderiv ℝ g) p) p :=
  hasFDerivAt_planeIntegral hc hs hg hp

example {u₀ : E2 → ℂ} (hc : Continuous u₀) (hs : HasCompactSupport u₀) {g : E3 → V}
    (hg : ContDiffOn ℝ 1 g upperHalfSpace) {p : E3} (hp : 0 < p 2) :
    fderiv ℝ (planeIntegral u₀ g) p = planeIntegral u₀ (fderiv ℝ g) p :=
  fderiv_planeIntegral hc hs hg hp

example {u₀ : E2 → ℂ} (hc : Continuous u₀) (hs : HasCompactSupport u₀) {g : E3 → V}
    (hg : ContDiffOn ℝ 1 g upperHalfSpace) {p : E3} (hp : 0 < p 2) (v : E3) :
    fderiv ℝ (planeIntegral u₀ g) p v = planeIntegral u₀ (fun q => fderiv ℝ g q v) p :=
  fderiv_planeIntegral_apply hc hs hg hp v

example {u₀ : E2 → ℂ} (hc : Continuous u₀) (hs : HasCompactSupport u₀) (n : ℕ) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℂ W] {g : E3 → W},
      ContDiffOn ℝ (n + 1) g upperHalfSpace →
        ContDiffOn ℝ n (planeIntegral u₀ g) upperHalfSpace :=
  contDiffOn_planeIntegral_of_succ hc hs n

example {u₀ : E2 → ℂ} (hc : Continuous u₀) (hs : HasCompactSupport u₀) {g : E3 → V}
    (hg : ContDiffOn ℝ ∞ g upperHalfSpace) :
    ContDiffOn ℝ ∞ (planeIntegral u₀ g) upperHalfSpace :=
  contDiffOn_planeIntegral hc hs hg

end PlaneIntegral

example (k : ℝ) (u₀ : E2 → ℂ) (p : E3) :
    ℂ :=
  apertureField k u₀ p

example (k : ℝ) (u₀ : E2 → ℂ) :
    apertureField k u₀ = planeIntegral u₀ (rayleighKernel k) :=
  apertureField_eq_planeIntegral k u₀

example (k : ℝ) {u₀ : E2 → ℂ} (hc : Continuous u₀) (hs : HasCompactSupport u₀) :
    ContDiffOn ℝ ∞ (apertureField k u₀) upperHalfSpace :=
  contDiffOn_apertureField k hc hs

example (k : ℝ) {u₀ : E2 → ℂ} (hc : Continuous u₀) (hs : HasCompactSupport u₀) {p : E3}
    (hp : 0 < p 2) :
    Δ (apertureField k u₀) p + k ^ 2 * apertureField k u₀ p = 0 :=
  helmholtz_apertureField k hc hs hp

example (z : ℝ) (w : E2) :
    ℝ :=
  poissonKernel z w

example (k : ℝ) (w : E2) (z : ℝ) :
    rayleighKernel k (spacePoint w z) = poissonKernel z w *
      (cexp (I * k * √(‖w‖ ^ 2 + z ^ 2)) * (1 - I * k * √(‖w‖ ^ 2 + z ^ 2))) :=
  rayleighKernel_spacePoint k w z

example (r : ℝ) :
    HasDerivAt (fun r : ℝ => -(√(r ^ 2 + 1))⁻¹) (r * (√(r ^ 2 + 1) ^ 3)⁻¹) r :=
  hasDerivAt_neg_inv_sqrt r

example :
    ∫ r in Ioi (0 : ℝ), r * (√(r ^ 2 + 1) ^ 3)⁻¹ = 1 :=
  integral_Ioi_poissonProfile

example :
    IntegrableOn (fun r : ℝ => r * (√(r ^ 2 + 1) ^ 3)⁻¹) (Ioi 0) :=
  integrableOn_Ioi_poissonProfile

example (w : E2) :
    poissonKernel 1 w = (2 * π)⁻¹ * (√(‖w‖ ^ 2 + 1) ^ 3)⁻¹ :=
  poissonKernel_one w

example :
    Integrable (poissonKernel 1) :=
  integrable_poissonKernel_one

example :
    ∫ w : E2, poissonKernel 1 w = 1 :=
  integral_poissonKernel_one

example (k : ℝ) (u₀ : E2 → ℂ) (x : E2) {z : ℝ} (hz : 0 < z) :
    apertureField k u₀ (spacePoint x z) = ∫ v : E2, u₀ (x - z • v) *
      (cexp (I * k * (z * √(‖v‖ ^ 2 + 1))) * (1 - I * k * (z * √(‖v‖ ^ 2 + 1)))) *
        (poissonKernel 1 v : ℂ) :=
  apertureField_spacePoint_eq k u₀ x hz

example (k : ℝ) {u₀ : E2 → ℂ} (hc : Continuous u₀) (hs : HasCompactSupport u₀) (x : E2) :
    Tendsto (fun z => apertureField k u₀ (spacePoint x z)) (𝓝[>] 0) (𝓝 (u₀ x)) :=
  tendsto_apertureField_boundary k hc hs x

example (k : ℝ) {z : ℝ} (hz : 0 < z) (s : ℝ) :
    HasDerivAt (fun s : ℝ => -(z * cexp (I * k * √(s ^ 2 + z ^ 2)) /
        (2 * π * √(s ^ 2 + z ^ 2))))
      (s * (z * kernelProfile k √(s ^ 2 + z ^ 2))) s :=
  hasDerivAt_planeWavePrimitive k hz s

example (k : ℝ) {z : ℝ} (hz : 0 < z) {L : ℝ} (hL : 0 ≤ L) :
    ∫ w in ball (0 : E2) L, rayleighKernel k (spacePoint w z) =
      cexp (I * k * z) - z * cexp (I * k * √(L ^ 2 + z ^ 2)) / √(L ^ 2 + z ^ 2) :=
  integral_ball_rayleighKernel k hz hL

example (k : ℝ) {z : ℝ} (hz : 0 < z) :
    Tendsto (fun L => ∫ w in ball (0 : E2) L, rayleighKernel k (spacePoint w z)) atTop
      (𝓝 (cexp (I * k * z))) :=
  tendsto_integral_ball_rayleighKernel k hz

example (k : ℝ) (u : E3 → ℂ) :
    Prop :=
  IsRadiating k u

example (a b : ℝ) :
    ‖cexp (I * a) - cexp (I * b)‖ ≤ |a - b| :=
  norm_cexp_I_mul_sub_le a b

example (k : ℝ) {R : ℝ} (hR : 0 < R) :
    ‖kernelProfile k R‖ ≤ (1 + |k| * R) / (2 * π * R ^ 3) :=
  norm_kernelProfile_le k hR

example {a : ℝ} {p : E3} {y : E2} (hy : ‖y‖ ≤ a) (hr : 2 * a ≤ ‖p‖) :
    ‖p‖ / 2 ≤ ‖p - planePoint y‖ :=
  half_le_norm_sub_planePoint hy hr

example (p : E3) :
    |p 2| ≤ ‖p‖ :=
  abs_apply_two_le p

example {k a : ℝ} (hk : 0 ≤ k) {p : E3} {y : E2} (hp : 0 < p 2) (hy : ‖y‖ ≤ a) (hr : 2 * a ≤ ‖p‖) :
    ‖p‖ * ‖rayleighKernel k (p - planePoint y)‖ ≤ (4 / ‖p‖ + 2 * k) / π :=
  norm_mul_rayleighKernel_le hk hp hy hr

example {k a : ℝ} (hk : 0 ≤ k) {p : E3} {y : E2} (hp : 0 < p 2) (hy : ‖y‖ ≤ a) (hr : 2 * a ≤ ‖p‖) :
    ‖fderiv ℝ (rayleighKernel k) (p - planePoint y) p -
        I * k * ‖p‖ * rayleighKernel k (p - planePoint y)‖ ≤
      (4 * (7 + 2 * k * a) / ‖p‖ ^ 2 + 2 * k * (5 + 2 * k * a) / ‖p‖) / π :=
  norm_radial_rayleighKernel_le hk hp hy hr

example {k a : ℝ} (hk : 0 ≤ k) {u₀ : E2 → ℂ} (hc : Continuous u₀) (hs : HasCompactSupport u₀)
    (ha : ∀ y ∈ tsupport u₀, ‖y‖ ≤ a) {p : E3} (hp : 0 < p 2) (hr : 2 * a ≤ ‖p‖) :
    ‖p‖ * ‖apertureField k u₀ p‖ ≤ (4 / ‖p‖ + 2 * k) / π * ∫ y, ‖u₀ y‖ :=
  norm_mul_apertureField_le hk hc hs ha hp hr

example {k a : ℝ} (hk : 0 ≤ k) {u₀ : E2 → ℂ} (hc : Continuous u₀) (hs : HasCompactSupport u₀)
    (ha : ∀ y ∈ tsupport u₀, ‖y‖ ≤ a) {p : E3} (hp : 0 < p 2) (hr : 2 * a ≤ ‖p‖) :
    ‖p‖ * ‖fderiv ℝ (apertureField k u₀) p (‖p‖⁻¹ • p) - I * k * apertureField k u₀ p‖ ≤
      (4 * (7 + 2 * k * a) / ‖p‖ ^ 2 + 2 * k * (5 + 2 * k * a) / ‖p‖) / π *
        ∫ y, ‖u₀ y‖ :=
  norm_radiation_apertureField_le hk hc hs ha hp hr

example {k : ℝ} (hk : 0 ≤ k) {u₀ : E2 → ℂ} (hc : Continuous u₀) (hs : HasCompactSupport u₀) :
    IsRadiating k (apertureField k u₀) :=
  apertureField_isRadiating hk hc hs

example (y : E2) :
    ℂ :=
  apertureBump y

example {n : ℕ∞} :
    ContDiff ℝ n apertureBump :=
  contDiff_apertureBump

example :
    Continuous apertureBump :=
  continuous_apertureBump

example :
    apertureBump 0 = 1 :=
  apertureBump_zero

example {y : E2} (hy : 1 ≤ ‖y‖) :
    apertureBump y = 0 :=
  apertureBump_eq_zero hy

example :
    tsupport apertureBump ⊆ closedBall 0 1 :=
  tsupport_apertureBump

example {y : E2} (hy : y ∈ tsupport apertureBump) :
    ‖y‖ ≤ 1 :=
  norm_le_one_of_mem_tsupport_apertureBump hy

example :
    HasCompactSupport apertureBump :=
  hasCompactSupport_apertureBump

example (k : ℝ) :
    ContDiffOn ℝ ∞ (apertureField k apertureBump) upperHalfSpace :=
  contDiffOn_apertureField_apertureBump k

example (k : ℝ) {p : E3} (hp : 0 < p 2) :
    Δ (apertureField k apertureBump) p + k ^ 2 * apertureField k apertureBump p = 0 :=
  helmholtz_apertureField_apertureBump k hp

example (k : ℝ) :
    Tendsto (fun z => apertureField k apertureBump (spacePoint 0 z)) (𝓝[>] 0) (𝓝 1) :=
  apertureField_apertureBump_tendsto k

example {k : ℝ} (hk : 0 ≤ k) :
    IsRadiating k (apertureField k apertureBump) :=
  apertureField_apertureBump_isRadiating hk

example {k : ℝ} (hk : 0 ≤ k) {p : E3} (hp : 0 < p 2) (hr : 2 ≤ ‖p‖) :
    ‖p‖ * ‖apertureField k apertureBump p‖ ≤
        (4 / ‖p‖ + 2 * k) / π * ∫ y, ‖apertureBump y‖ ∧
      ‖p‖ * ‖fderiv ℝ (apertureField k apertureBump) p (‖p‖⁻¹ • p) -
          I * k * apertureField k apertureBump p‖ ≤
        (4 * (7 + 2 * k * 1) / ‖p‖ ^ 2 + 2 * k * (5 + 2 * k * 1) / ‖p‖) / π *
          ∫ y, ‖apertureBump y‖ :=
  norm_radiation_apertureField_apertureBump_le hk hp hr

end ProjectAinos.Electrodynamics.Diffraction

end Aperture

section Fresnel

open MeasureTheory Filter Set Metric Complex

open scoped Topology InnerProductSpace Real

namespace ProjectAinos.Electrodynamics.Diffraction

local notation "E2" => EuclideanSpace ℝ (Fin 2)

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (k : ℝ) (w : E2) (z : ℝ) :
    ℂ :=
  fresnelKernel k w z

example (k : ℝ) (u₀ : E2 → ℂ) (x : E2) (z : ℝ) :
    ℂ :=
  fresnelField k u₀ x z

example (k : ℝ) (u₀ : E2 → ℂ) (x : E2) (z : ℝ) :
    fresnelField k u₀ x z = ∫ y, u₀ y * fresnelKernel k (x - y) z :=
  fresnelField_eq k u₀ x z

example {z : ℝ} (hz : 0 < z) (s : ℝ) :
    0 ≤ z + s ^ 2 / (2 * z) - √(s ^ 2 + z ^ 2) ∧
      z + s ^ 2 / (2 * z) - √(s ^ 2 + z ^ 2) ≤ s ^ 4 / (8 * z ^ 3) :=
  phase_sub_sqrt_le hz s

example {k : ℝ} (hk : 0 < k) {z : ℝ} (hz : 0 < z) (w : E2) :
    ‖rayleighKernel k (spacePoint w z) - fresnelKernel k w z‖ ≤
      k / (2 * π * z) * (k * ‖w‖ ^ 4 / (8 * z ^ 3) + ‖w‖ ^ 2 / z ^ 2 + 1 / (k * z)) :=
  norm_rayleighKernel_sub_fresnelKernel_le hk hz w

example {k : ℝ} (hk : 0 < k) {u₀ : E2 → ℂ} (hc : Continuous u₀) (hs : HasCompactSupport u₀)
    {x : E2} {z ρ : ℝ} (hz : 0 < z) (hρ : ∀ y ∈ tsupport u₀, ‖x - y‖ ≤ ρ) :
    ‖apertureField k u₀ (spacePoint x z) - fresnelField k u₀ x z‖ ≤
      k / (2 * π * z) * (k * ρ ^ 4 / (8 * z ^ 3) + ρ ^ 2 / z ^ 2 + 1 / (k * z)) *
        ∫ y, ‖u₀ y‖ :=
  norm_apertureField_sub_fresnelField_le hk hc hs hz hρ

example {k : ℝ} (hk : 0 < k) (x : E2) {z : ℝ} (hz : 0 < z) :
    ‖apertureField k apertureBump (spacePoint x z) - fresnelField k apertureBump x z‖ ≤
      k / (2 * π * z) * (k * (‖x‖ + 1) ^ 4 / (8 * z ^ 3) + (‖x‖ + 1) ^ 2 / z ^ 2 + 1 / (k * z)) *
        ∫ y, ‖apertureBump y‖ :=
  norm_apertureField_sub_fresnelField_apertureBump_le hk x hz

end ProjectAinos.Electrodynamics.Diffraction

end Fresnel

section Fraunhofer

open MeasureTheory Filter Set Metric Complex

open scoped Topology InnerProductSpace Real

namespace ProjectAinos.Electrodynamics.Diffraction

local notation "E2" => EuclideanSpace ℝ (Fin 2)

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (k : ℝ) (u₀ : E2 → ℂ) (n : E3) :
    ℂ :=
  fraunhoferAmplitude k u₀ n

example (k : ℝ) (u₀ : E2 → ℂ) (n : E3) :
    fraunhoferAmplitude k u₀ n =
      ∫ y, u₀ y * (k * n 2 / (2 * π * I) * cexp (-(I * k * ⟪n, planePoint y⟫_ℝ))) :=
  fraunhoferAmplitude_eq k u₀ n

example {a : ℝ} {n : E3} (hn : ‖n‖ = 1) {D : ℝ} (hD : 0 < D) {y : E2} (hy : ‖y‖ ≤ a)
    (hDa : 2 * a ≤ D) :
    D / 2 ≤ ‖D • n - planePoint y‖ ∧
      |D ^ 2 - ‖D • n - planePoint y‖ ^ 2| ≤ 2 * D * a + a ^ 2 ∧
      0 ≤ ‖D • n - planePoint y‖ - D + ⟪n, planePoint y⟫_ℝ ∧
      ‖D • n - planePoint y‖ - D + ⟪n, planePoint y⟫_ℝ ≤ 2 * a ^ 2 / D :=
  farField_geometry hn hD hy hDa

example {k a : ℝ} (hk : 0 < k) {n : E3} (hn : ‖n‖ = 1) (hnz : 0 < n 2) {D : ℝ} (hD : 0 < D)
    {y : E2} (hy : ‖y‖ ≤ a) (hDa : 2 * a ≤ D) :
    ‖D * cexp (-(I * k * D)) * rayleighKernel k (D • n - planePoint y) -
        k * n 2 / (2 * π * I) * cexp (-(I * k * ⟪n, planePoint y⟫_ℝ))‖ ≤
      k / (2 * π) * (2 * k * a ^ 2 / D + 10 * a / D + 8 / (k * D)) :=
  norm_fraunhoferKernel_sub_le hk hn hnz hD hy hDa

example {k a : ℝ} (hk : 0 < k) {u₀ : E2 → ℂ} (hc : Continuous u₀) (hs : HasCompactSupport u₀)
    (ha : ∀ y ∈ tsupport u₀, ‖y‖ ≤ a) {n : E3} (hn : ‖n‖ = 1) (hnz : 0 < n 2) {D : ℝ} (hD : 0 < D)
    (hDa : 2 * a ≤ D) :
    ‖D * cexp (-(I * k * D)) * apertureField k u₀ (D • n) - fraunhoferAmplitude k u₀ n‖ ≤
      k / (2 * π) * (2 * k * a ^ 2 / D + 10 * a / D + 8 / (k * D)) * ∫ y, ‖u₀ y‖ :=
  norm_fraunhofer_sub_le hk hc hs ha hn hnz hD hDa

example {k : ℝ} (hk : 0 < k) {u₀ : E2 → ℂ} (hc : Continuous u₀) (hs : HasCompactSupport u₀)
    {n : E3} (hn : ‖n‖ = 1) (hnz : 0 < n 2) :
    Tendsto (fun D : ℝ => D * cexp (-(I * k * D)) * apertureField k u₀ (D • n)) atTop
      (𝓝 (fraunhoferAmplitude k u₀ n)) :=
  tendsto_fraunhofer hk hc hs hn hnz

example (k : ℝ) {u₀ : E2 → ℂ} (hu : Integrable u₀) {p : E3} (hp : 0 < p 2) :
    Integrable fun y => u₀ y * rayleighKernel k (p - planePoint y) :=
  integrable_mul_rayleighKernel k hu hp

example (k : ℝ) {u₀ u₀' U : E2 → ℂ} (h : ∀ y, u₀ y + u₀' y = U y) (h₁ : Integrable u₀)
    (h₂ : Integrable u₀') {p : E3} (hp : 0 < p 2) :
    apertureField k u₀ p + apertureField k u₀' p = apertureField k U p :=
  babinet k h h₁ h₂ hp

example (h : E2 → ℂ) (x : E2) (L : ℝ) :
    ∫ y in ball x L, h (x - y) = ∫ w in ball (0 : E2) L, h w :=
  setIntegral_ball_sub h x L

example (k : ℝ) {u₀ : E2 → ℂ} (hc : Continuous u₀) (hs : HasCompactSupport u₀) (x : E2) {z : ℝ}
    (hz : 0 < z) :
    Tendsto (fun L => ∫ y in ball x L,
        (1 - u₀ y) * rayleighKernel k (spacePoint x z - planePoint y)) atTop
      (𝓝 (cexp (I * k * z) - apertureField k u₀ (spacePoint x z))) :=
  tendsto_babinet_planeWave k hc hs x hz

example (k : ℝ) {u₀ u₀' U : E2 → ℂ} (h : ∀ y, u₀ y + u₀' y = U y) (h₁ : Integrable u₀)
    (h₂ : Integrable u₀') (n : E3) :
    fraunhoferAmplitude k u₀ n + fraunhoferAmplitude k u₀' n = fraunhoferAmplitude k U n :=
  babinet_fraunhoferAmplitude k h h₁ h₂ n

example (k : ℝ) {p : E3} (hp : 0 < p 2) :
    apertureField k ((ball (0 : E2) (1 / 2)).indicator apertureBump) p +
        apertureField k ((ball (0 : E2) (1 / 2))ᶜ.indicator apertureBump) p =
      apertureField k apertureBump p :=
  babinet_disc k hp

example (k : ℝ) {z : ℝ} (hz : 0 < z) :
    Tendsto (fun L => ∫ y in ball (0 : E2) L,
        (1 - apertureBump y) * rayleighKernel k (spacePoint 0 z - planePoint y)) atTop
      (𝓝 (cexp (I * k * z) - apertureField k apertureBump (spacePoint 0 z))) :=
  tendsto_babinet_planeWave_apertureBump k hz

example :
    ‖(EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : E3)‖ = 1 :=
  norm_single_two

example {k : ℝ} (hk : 0 < k) :
    Tendsto (fun D : ℝ => D * cexp (-(I * k * D)) *
        apertureField k apertureBump (D • EuclideanSpace.single 2 1)) atTop
      (𝓝 (fraunhoferAmplitude k apertureBump (EuclideanSpace.single 2 1))) :=
  tendsto_fraunhofer_apertureBump hk

example {k : ℝ} (hk : 0 < k) {D : ℝ} (hD : 2 ≤ D) :
    ‖D * cexp (-(I * k * D)) * apertureField k apertureBump (D • EuclideanSpace.single 2 1) -
        fraunhoferAmplitude k apertureBump (EuclideanSpace.single 2 1)‖ ≤
      k / (2 * π) * (2 * k * 1 ^ 2 / D + 10 * 1 / D + 8 / (k * D)) *
        ∫ y, ‖apertureBump y‖ :=
  norm_fraunhofer_sub_apertureBump_le hk hD

end ProjectAinos.Electrodynamics.Diffraction

end Fraunhofer

section StraightEdge

open ProjectAinos.Electrodynamics.Diffraction ProjectAinos.SpecialFunctions Filter Complex
open scoped Topology Real

example {L z : ℝ} (hL : 0 < L) (hz : 0 < z) (u : ℝ) :
    Tendsto (fun R => fresnelField (π * z / L ^ 2) (edgeAperture L u R) 0 z) atTop
      (𝓝 (cexp (I * (π * z / L ^ 2 : ℝ) * z) * edgeAmplitude u)) :=
  tendsto_fresnelField_edge hL hz u

example (u : ℝ) : Complex.normSq (edgeAmplitude u) =
    ((1 / 2 + Fresnel.cosine u) ^ 2 + (1 / 2 + Fresnel.sine u) ^ 2) / 2 :=
  normSq_edgeAmplitude u

example : Complex.normSq (edgeAmplitude 0) = 1 / 4 := normSq_edgeAmplitude_zero

end StraightEdge
