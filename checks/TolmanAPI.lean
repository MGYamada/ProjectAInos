/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.GeneralRelativity.Tolman

/-! Public consumers of the collapse of a dustlike sphere (Landau–Lifshitz §103): the synchronous
metric of Tolman with its curvature, the equivalence of the Einstein equations with dust to the
equations of Tolman, the sign of the density, the parabolic solution and the parametric elliptic
and hyperbolic solutions, the collapse at a finite time, and the matching to the Schwarzschild
field in the Lemaître and Eddington–Finkelstein charts. Default elaborator options are
intentional: these checks must not rely on the implementation's transparency settings. Every
statement is pinned with its type. -/

noncomputable section

section Tolman

open ContinuousLinearMap Set TopologicalSpace Filter

open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.Tolman

open SmoothGeometry CoordinateMetric

open SphericalAnsatz (partialT partialR hasDerivAt_partialT hasDerivAt_partialR
  contDiffOn_partialT contDiffOn_partialR partialR_partialT hasFDerivAt_timeRadius
  hasFDerivAt_div gamma233 gamma323 fderiv_gamma233 sum_four)

local notation "E" => MinkowskiModel 3

variable (D : Data)

example :
    Opens E :=
  domain D

variable {D} {x : E}

example (hx : x ∈ domain D) :
    (x 0, x 1) ∈ D.S :=
  mem_S hx

example (hx : x ∈ domain D) :
    0 < D.r (x 0) (x 1) :=
  r_pos_of_mem hx

example (hx : x ∈ domain D) :
    0 < partialR D.r (x 0) (x 1) :=
  partialR_r_pos_of_mem hx

example (hx : x ∈ domain D) :
    0 < Real.sin (x 2) :=
  sin_pos_of_mem hx

example (τ R : ℝ) :
    E :=
  point τ R

example {τ R : ℝ} (h : (τ, R) ∈ D.S) :
    point τ R ∈ domain D :=
  point_mem h

example (τ R : ℝ) :
    point τ R 0 = τ :=
  point_zero τ R

example (τ R : ℝ) :
    point τ R 1 = R :=
  point_one τ R

example {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) D.S) :
    ContDiffOn ℝ ∞ (Function.uncurry (partialT f)) D.S :=
  contDiffOn_dt hf

example {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) D.S) :
    ContDiffOn ℝ ∞ (Function.uncurry (partialR f)) D.S :=
  contDiffOn_dR hf

example {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) D.S) :
    ContDiffOn ℝ ∞ (fun z : E => f (z 0) (z 1)) (domain D) :=
  contDiffOn_lift hf

example (f : ℝ → ℝ → ℝ) (x v : E) :
    ℝ :=
  along f x v

example {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) D.S) (hx : x ∈ domain D) :
    HasFDerivAt (fun z : E => f (z 0) (z 1))
      (partialT f (x 0) (x 1) • (proj 0 : E →L[ℝ] ℝ) +
        partialR f (x 0) (x 1) • (proj 1 : E →L[ℝ] ℝ)) x :=
  hasFDerivAt_lift hf hx

example {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) D.S) (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (fun z : E => f (z 0) (z 1)) x v = along f x v :=
  fderiv_lift hf hx v

example {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) D.S) {τ R : ℝ}
    (h : (τ, R) ∈ D.S) :
    partialT (partialR f) τ R = partialR (partialT f) τ R :=
  partialT_partialR hf h

example (x : E) :
    Fin 4 → ℝ :=
  coefficients D x

example (i : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => coefficients D x i) (domain D) :=
  contDiffOn_coefficients i

example :
    CoordinateMetric .timeNegative 3 (domain D) :=
  metric D

example (y : E) :
    (metric D).coefficient y = Matrix.diagonal (coefficients D y) :=
  coefficient_metric y

example (y v w : E) :
    (metric D).form y v w = -(v 0 * w 0) + Real.exp (D.lam (y 0) (y 1)) * (v 1 * w 1) +
      D.r (y 0) (y 1) ^ 2 * (v 2 * w 2) +
        D.r (y 0) (y 1) ^ 2 * Real.sin (y 2) ^ 2 * (v 3 * w 3) :=
  metric_form_apply y v w

example :
    (metric D).IsSynchronous :=
  isSynchronous

example (hx : x ∈ domain D) (i : Fin 4) :
    coefficients D x i ≠ 0 :=
  coefficients_ne_zero hx i

example (hx : x ∈ domain D) (k : Fin 4) (v : E) :
    fderiv ℝ (fun z => coefficients D z k) x v =
      ![0, Real.exp (D.lam (x 0) (x 1)) * along D.lam x v,
        2 * D.r (x 0) (x 1) * along D.r x v,
        2 * D.r (x 0) (x 1) * Real.sin (x 2) ^ 2 * along D.r x v +
          D.r (x 0) (x 1) ^ 2 * (2 * Real.sin (x 2) * Real.cos (x 2)) * v 2] k :=
  fderiv_coefficients hx k v

example (x : E) :
    ℝ :=
  gamma011 D x

example (x : E) :
    ℝ :=
  gamma022 D x

example (x : E) :
    ℝ :=
  gamma033 D x

example (x : E) :
    ℝ :=
  gamma101 D x

example (x : E) :
    ℝ :=
  gamma111 D x

example (x : E) :
    ℝ :=
  gamma122 D x

example (x : E) :
    ℝ :=
  gamma133 D x

example (x : E) :
    ℝ :=
  gamma202 D x

example (x : E) :
    ℝ :=
  gamma212 D x

example (x : E) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  christoffel D x

example (hx : x ∈ domain D) (k i j : Fin 4) :
    christoffelOf (metric D).coefficient x k i j = christoffel D x k i j :=
  christoffelOf_eq hx k i j

example (hx : x ∈ domain D) :
    ∀ᶠ z in 𝓝 x, ∀ k i j, christoffelOf (metric D).coefficient z k i j = christoffel D z k i j :=
  eventually_christoffelOf_eq hx

example (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (gamma011 D) x v =
      (along (partialT D.lam) x v * Real.exp (D.lam (x 0) (x 1)) +
        partialT D.lam (x 0) (x 1) * Real.exp (D.lam (x 0) (x 1)) * along D.lam x v) / 2 :=
  fderiv_gamma011 hx v

example (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (gamma022 D) x v =
      along D.r x v * partialT D.r (x 0) (x 1) + D.r (x 0) (x 1) * along (partialT D.r) x v :=
  fderiv_gamma022 hx v

example (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (gamma033 D) x v =
      (along D.r x v * partialT D.r (x 0) (x 1) + D.r (x 0) (x 1) * along (partialT D.r) x v) *
          Real.sin (x 2) ^ 2 +
        D.r (x 0) (x 1) * partialT D.r (x 0) (x 1) *
          (2 * Real.sin (x 2) * Real.cos (x 2) * v 2) :=
  fderiv_gamma033 hx v

example (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (gamma101 D) x v = along (partialT D.lam) x v / 2 :=
  fderiv_gamma101 hx v

example (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (gamma111 D) x v = along (partialR D.lam) x v / 2 :=
  fderiv_gamma111 hx v

example (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (gamma122 D) x v =
      (-(along D.r x v * partialR D.r (x 0) (x 1) + D.r (x 0) (x 1) * along (partialR D.r) x v) +
        D.r (x 0) (x 1) * partialR D.r (x 0) (x 1) * along D.lam x v) /
        Real.exp (D.lam (x 0) (x 1)) :=
  fderiv_gamma122 hx v

example (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (gamma133 D) x v =
      (-(along D.r x v * partialR D.r (x 0) (x 1) + D.r (x 0) (x 1) * along (partialR D.r) x v) *
          Real.sin (x 2) ^ 2 -
        D.r (x 0) (x 1) * partialR D.r (x 0) (x 1) *
          (2 * Real.sin (x 2) * Real.cos (x 2) * v 2) +
        D.r (x 0) (x 1) * partialR D.r (x 0) (x 1) * Real.sin (x 2) ^ 2 * along D.lam x v) /
        Real.exp (D.lam (x 0) (x 1)) :=
  fderiv_gamma133 hx v

example (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (gamma202 D) x v =
      (along (partialT D.r) x v * D.r (x 0) (x 1) - partialT D.r (x 0) (x 1) * along D.r x v) /
        D.r (x 0) (x 1) ^ 2 :=
  fderiv_gamma202 hx v

example (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (gamma212 D) x v =
      (along (partialR D.r) x v * D.r (x 0) (x 1) - partialR D.r (x 0) (x 1) * along D.r x v) /
        D.r (x 0) (x 1) ^ 2 :=
  fderiv_gamma212 hx v

example (hx : x ∈ domain D) (v : E) :
    fderiv ℝ gamma323 x v = -v 2 / Real.sin (x 2) ^ 2 :=
  fderiv_gamma323 hx v

example (x : E) :
    Fin 4 → Fin 4 → ℝ :=
  ricci D x

example (hx : x ∈ domain D) (j k : Fin 4) :
    ricciOf (metric D).coefficient x j k = ricci D x j k :=
  ricciOf_eq hx j k

example (hx : x ∈ domain D) :
    ((metric D).coefficient x)⁻¹ = Matrix.diagonal fun l => (coefficients D x l)⁻¹ :=
  coefficient_metric_inv hx

example (hx : x ∈ domain D) :
    scalarOf (metric D).coefficient x = ∑ a, ricci D x a a / coefficients D x a :=
  scalarOf_eq hx

example (x : E) :
    Fin 4 → Fin 4 → ℝ :=
  einstein D x

example (hx : x ∈ domain D) (i k : Fin 4) :
    einsteinOf (metric D).coefficient x i k = einstein D x i k :=
  einsteinOf_eq hx i k

example (y : E) :
    einstein D y 1 0 = einstein D y 0 1 :=
  einstein_one_zero y

example (y : E) :
    einstein D y 3 3 = Real.sin (y 2) ^ 2 * einstein D y 2 2 :=
  einstein_three_three y

example {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) D.S) {τ R : ℝ}
    (h : (τ, R) ∈ D.S) :
    HasDerivAt (fun s => f s R) (partialT f τ R) τ :=
  hasDerivAt_dt hf h

example {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) D.S) {τ R : ℝ}
    (h : (τ, R) ∈ D.S) :
    HasDerivAt (fun s => f τ s) (partialR f τ R) R :=
  hasDerivAt_dR hf h

example (R : ℝ) :
    IsOpen {τ | (τ, R) ∈ D.S} :=
  isOpen_slice R

example (τ : ℝ) :
    IsOpen {R | (τ, R) ∈ D.S} :=
  isOpen_shells τ

example (τ R : ℝ) :
    ℝ :=
  energyOf D τ R

example (τ R : ℝ) :
    ℝ :=
  massOf D τ R

example {τ R : ℝ} (h : (τ, R) ∈ D.S) :
    HasDerivAt (fun s => energyOf D s R)
      (partialR D.r τ R * (2 * partialR (partialT D.r) τ R -
        partialT D.lam τ R * partialR D.r τ R) / Real.exp (D.lam τ R)) τ :=
  hasDerivAt_energyOf_time h

example {τ R : ℝ} (h : (τ, R) ∈ D.S) :
    HasDerivAt (fun s => energyOf D τ s)
      ((2 * partialR D.r τ R * partialR (partialR D.r) τ R -
        partialR D.r τ R ^ 2 * partialR D.lam τ R) / Real.exp (D.lam τ R)) R :=
  hasDerivAt_energyOf_radius h

example {τ R : ℝ} (h : (τ, R) ∈ D.S) :
    HasDerivAt (fun s => massOf D s R)
      (partialT D.r τ R * (partialT D.r τ R ^ 2 - energyOf D τ R +
          2 * D.r τ R * partialT (partialT D.r) τ R) -
        D.r τ R * (partialR D.r τ R * (2 * partialR (partialT D.r) τ R -
          partialT D.lam τ R * partialR D.r τ R) / Real.exp (D.lam τ R))) τ :=
  hasDerivAt_massOf_time h

example {τ R : ℝ} (h : (τ, R) ∈ D.S) :
    HasDerivAt (fun s => massOf D τ s)
      (partialR D.r τ R * (partialT D.r τ R ^ 2 - energyOf D τ R) +
        D.r τ R * (2 * partialT D.r τ R * partialR (partialT D.r) τ R -
          (2 * partialR D.r τ R * partialR (partialR D.r) τ R -
            partialR D.r τ R ^ 2 * partialR D.lam τ R) / Real.exp (D.lam τ R))) R :=
  hasDerivAt_massOf_radius h

example (hx : x ∈ domain D) :
    einstein D x 0 0 * (D.r (x 0) (x 1) ^ 2 * partialR D.r (x 0) (x 1)) =
      (partialR D.r (x 0) (x 1) * (partialT D.r (x 0) (x 1) ^ 2 - energyOf D (x 0) (x 1)) +
        D.r (x 0) (x 1) * (2 * partialT D.r (x 0) (x 1) * partialR (partialT D.r) (x 0) (x 1) -
          (2 * partialR D.r (x 0) (x 1) * partialR (partialR D.r) (x 0) (x 1) -
            partialR D.r (x 0) (x 1) ^ 2 * partialR D.lam (x 0) (x 1)) /
              Real.exp (D.lam (x 0) (x 1)))) +
        D.r (x 0) (x 1) * partialT D.r (x 0) (x 1) * (partialT D.lam (x 0) (x 1) *
          partialR D.r (x 0) (x 1) - 2 * partialR (partialT D.r) (x 0) (x 1)) :=
  einstein_zero_zero_mul hx

example (hx : x ∈ domain D) :
    einstein D x 1 1 = -(Real.exp (D.lam (x 0) (x 1)) *
      (2 * D.r (x 0) (x 1) * partialT (partialT D.r) (x 0) (x 1) + partialT D.r (x 0) (x 1) ^ 2 -
        energyOf D (x 0) (x 1))) / D.r (x 0) (x 1) ^ 2 :=
  einstein_one_one_eq hx

example :
    Fin 4 → ℝ :=
  fluidCovector

example (ε : ℝ → ℝ → ℝ) (x : E) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  dustStress ε x

example {ε : ℝ → ℝ → ℝ} (hε : ContDiffOn ℝ ∞ (Function.uncurry ε) D.S) (i k : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => dustStress ε x i k) (domain D) :=
  contDiffOn_dustStress hε i k

example (hx : x ∈ domain D) (κ : ℝ) (ε : ℝ → ℝ → ℝ) :
    (∀ i k, einsteinOf (metric D).coefficient x i k + 0 * (metric D).coefficient x i k =
      κ * dustStress ε x i k) ↔
      einstein D x 0 0 = κ * ε (x 0) (x 1) ∧ einstein D x 0 1 = 0 ∧ einstein D x 1 1 = 0 ∧
        einstein D x 2 2 = 0 :=
  isEinstein_at_iff hx κ ε

namespace Equations

variable {κ : ℝ} {ε : ℝ → ℝ → ℝ} {f F : ℝ → ℝ} (h : Equations D κ ε f F) {τ R : ℝ}

include h

example (hp : (τ, R) ∈ D.S) :
    energyOf D τ R = f R :=
  energyOf_eq h hp

example (hp : (τ, R) ∈ D.S) :
    0 < 1 + f R :=
  one_add_pos h hp

example (hp : (τ, R) ∈ D.S) :
    massOf D τ R = F R :=
  massOf_eq h hp

example (hp : (τ, R) ∈ D.S) :
    HasDerivAt F
      (partialR D.r τ R * (partialT D.r τ R ^ 2 - energyOf D τ R) +
        D.r τ R * (2 * partialT D.r τ R * partialR (partialT D.r) τ R -
          (2 * partialR D.r τ R * partialR (partialR D.r) τ R -
            partialR D.r τ R ^ 2 * partialR D.lam τ R) / Real.exp (D.lam τ R))) R :=
  hasDerivAt_mass h hp

example (hp : (τ, R) ∈ D.S) :
    partialT D.lam τ R * partialR D.r τ R = 2 * partialR (partialT D.r) τ R :=
  momentum h hp

example (hp : (τ, R) ∈ D.S) :
    partialT (partialT D.lam) τ R * partialR D.r τ R +
        partialT D.lam τ R * partialR (partialT D.r) τ R =
      2 * partialR (partialT (partialT D.r)) τ R :=
  momentum_time h hp

example (hp : (τ, R) ∈ D.S) :
    partialR (partialT (partialT D.r)) τ R =
      -(partialR D.r τ R * (partialT D.r τ R ^ 2 - energyOf D τ R) +
        D.r τ R * (2 * partialT D.r τ R * partialR (partialT D.r) τ R -
          (2 * partialR D.r τ R * partialR (partialR D.r) τ R -
            partialR D.r τ R ^ 2 * partialR D.lam τ R) / Real.exp (D.lam τ R))) /
          (2 * D.r τ R ^ 2) + F R * partialR D.r τ R / D.r τ R ^ 3 :=
  accel_radius h hp

example (hx : x ∈ domain D) :
    einstein D x 0 0 = κ * ε (x 0) (x 1) :=
  einstein_zero_zero h hx

example (hx : x ∈ domain D) :
    einstein D x 0 1 = 0 :=
  einstein_zero_one h hx

example (hx : x ∈ domain D) :
    einstein D x 1 1 = 0 :=
  einstein_one_one h hx

example (hx : x ∈ domain D) :
    einstein D x 2 2 = 0 :=
  einstein_two_two h hx

example :
    (metric D).IsEinstein κ 0 (dustStress ε) :=
  isEinstein h

end Equations

example {f F : ℝ → ℝ} (he : ∀ τ R, (τ, R) ∈ D.S → partialT D.r τ R ^ 2 = f R + F R / D.r τ R)
    {τ R : ℝ} (hp : (τ, R) ∈ D.S) (h0 : partialT D.r τ R ≠ 0) :
    partialT (partialT D.r) τ R = -F R / (2 * D.r τ R ^ 2) :=
  accel_of_energy he hp h0

example (g : ℝ → ℝ → ℝ) (R : ℝ) :
    ℝ :=
  sliceValue D g R

example {g : ℝ → ℝ → ℝ} {R : ℝ} (hS : IsPreconnected {τ | (τ, R) ∈ D.S})
    (hg : ∀ τ, (τ, R) ∈ D.S → HasDerivAt (fun s => g s R) 0 τ) {τ : ℝ} (h : (τ, R) ∈ D.S) :
    g τ R = sliceValue D g R :=
  sliceValue_eq hS hg h

example (hS : ∀ R, IsPreconnected {τ | (τ, R) ∈ D.S}) {κ : ℝ} {ε : ℝ → ℝ → ℝ}
    (h : (metric D).IsEinstein κ 0 (dustStress ε)) :
    Equations D κ ε (sliceValue D (energyOf D)) (sliceValue D (massOf D)) :=
  equations_of_isEinstein hS h

example (hS : ∀ R, IsPreconnected {τ | (τ, R) ∈ D.S}) (κ : ℝ) (ε : ℝ → ℝ → ℝ) :
    (metric D).IsEinstein κ 0 (dustStress ε) ↔ ∃ f F : ℝ → ℝ, Equations D κ ε f F :=
  isEinstein_iff hS κ ε

example (hS : ∀ R, IsPreconnected {τ | (τ, R) ∈ D.S}) (κ : ℝ) {ε : ℝ → ℝ → ℝ}
    (hε : ContDiffOn ℝ ∞ (Function.uncurry ε) D.S) :
    (metric D).toLorentzMetric.SatisfiesEinstein κ 0
        (bilinearOf (dustStress ε) (contDiffOn_dustStress hε)) ↔
      ∃ f F : ℝ → ℝ, Equations D κ ε f F :=
  satisfiesEinstein_iff hS κ hε

example {κ : ℝ} (hκ : κ ≠ 0) {ε : ℝ → ℝ → ℝ} (hε : ContDiffOn ℝ ∞ (Function.uncurry ε) D.S)
    (h : (metric D).IsEinstein κ 0 (dustStress ε)) (y : domain D) (b : Fin 4) :
    (metric D).divergenceOf (dustStress ε) y b = 0 :=
  divergence_dust_eq_zero hκ hε h y b

namespace Equations

variable {κ : ℝ} {ε : ℝ → ℝ → ℝ} {f F : ℝ → ℝ} (h : Equations D κ ε f F) {τ R : ℝ}

include h

example (hκ : 0 < κ) (hp : (τ, R) ∈ D.S) :
    0 ≤ ε τ R ↔ 0 ≤ deriv F R :=
  density_nonneg_iff h hκ hp

example (hκ : κ ≠ 0) (hp : (τ, R) ∈ D.S) :
    HasDerivAt (fun s => ε s R * (partialR D.r s R * D.r s R ^ 2)) 0 τ :=
  hasDerivAt_restMass h hκ hp

end Equations

example {y : ℝ} (hy : 0 ≤ y) :
    (y ^ (1 / 3 : ℝ)) ^ 3 = y :=
  rpow_third_pow_three hy

example {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => t ^ (1 / 3 : ℝ)) (1 / (3 * (y ^ (1 / 3 : ℝ)) ^ 2)) y :=
  hasDerivAt_rpow_third hy

example (F τ₀ : ℝ → ℝ) (τ R : ℝ) :
    ℝ :=
  parabolicRadius F τ₀ τ R

example {F τ₀ : ℝ → ℝ} {τ R : ℝ} (hF : 0 ≤ F R) (hτ : τ ≤ τ₀ R) :
    parabolicRadius F τ₀ τ R = (9 * F R / 4) ^ (1 / 3 : ℝ) * (τ₀ R - τ) ^ (2 / 3 : ℝ) :=
  parabolicRadius_eq hF hτ

example {F τ₀ : ℝ → ℝ} {τ R : ℝ} (hF : 0 ≤ F R) :
    parabolicRadius F τ₀ τ R ^ 3 = 9 * F R * (τ₀ R - τ) ^ 2 / 4 :=
  parabolicRadius_cube hF

example {F τ₀ : ℝ → ℝ} {τ R : ℝ} (hF : 0 < F R) (hτ : τ < τ₀ R) :
    0 < parabolicRadius F τ₀ τ R :=
  parabolicRadius_pos hF hτ

example (F τ₀ : ℝ → ℝ) (R : ℝ) :
    Tendsto (fun τ => parabolicRadius F τ₀ τ R) (𝓝[<] (τ₀ R)) (𝓝 0) :=
  tendsto_radius_zero F τ₀ R

example {F τ₀ : ℝ → ℝ} {τ R : ℝ} (hF : 0 < F R) (hτ : τ < τ₀ R) :
    HasDerivAt (fun s => parabolicRadius F τ₀ s R)
      (-3 * F R * (τ₀ R - τ) / (2 * parabolicRadius F τ₀ τ R ^ 2)) τ :=
  hasDerivAt_parabolicRadius_time hF hτ

example {F τ₀ : ℝ → ℝ} {τ R F' τ₀' : ℝ} (hF' : HasDerivAt F F' R) (hτ₀' : HasDerivAt τ₀ τ₀' R)
    (hF : 0 < F R) (hτ : τ < τ₀ R) :
    HasDerivAt (fun s => parabolicRadius F τ₀ τ s)
      (3 * (F' * (τ₀ R - τ) ^ 2 + 2 * F R * (τ₀ R - τ) * τ₀') /
        (4 * parabolicRadius F τ₀ τ R ^ 2)) R :=
  hasDerivAt_parabolicRadius_radius hF' hτ₀' hF hτ

example {F τ₀ : ℝ → ℝ} {τ R : ℝ} (hF : 0 < F R) (hτ : τ < τ₀ R) :
    HasDerivAt (fun s => -3 * F R * (τ₀ R - s) / (2 * parabolicRadius F τ₀ s R ^ 2))
      (-F R / (2 * parabolicRadius F τ₀ τ R ^ 2)) τ :=
  hasDerivAt_parabolicRate hF hτ

namespace ParabolicData

variable (P : ParabolicData) {τ R : ℝ}

example :
    Set (ℝ × ℝ) :=
  S P

example :
    IsOpen P.S :=
  isOpen_S P

example (hR : R ∈ P.J) :
    HasDerivAt P.F (deriv P.F R) R :=
  hasDerivAt_F P hR

example (hR : R ∈ P.J) :
    HasDerivAt P.τ₀ (deriv P.τ₀ R) R :=
  hasDerivAt_τ₀ P hR

example (hp : (τ, R) ∈ P.S) :
    partialT (parabolicRadius P.F P.τ₀) τ R =
      -3 * P.F R * (P.τ₀ R - τ) / (2 * parabolicRadius P.F P.τ₀ τ R ^ 2) :=
  partialT_radius P hp

example (hp : (τ, R) ∈ P.S) :
    partialR (parabolicRadius P.F P.τ₀) τ R =
      3 * (deriv P.F R * (P.τ₀ R - τ) ^ 2 + 2 * P.F R * (P.τ₀ R - τ) * deriv P.τ₀ R) /
        (4 * parabolicRadius P.F P.τ₀ τ R ^ 2) :=
  partialR_radius P hp

example (hp : (τ, R) ∈ P.S) :
    0 < partialR (parabolicRadius P.F P.τ₀) τ R :=
  partialR_radius_pos P hp

example (hp : (τ, R) ∈ P.S) :
    partialT (partialT (parabolicRadius P.F P.τ₀)) τ R =
      -P.F R / (2 * parabolicRadius P.F P.τ₀ τ R ^ 2) :=
  partialT_partialT_radius P hp

example :
    ContDiffOn ℝ ∞ (Function.uncurry (parabolicRadius P.F P.τ₀)) P.S :=
  contDiffOn_radius P

example :
    Data :=
  toData P

example :
    P.toData.S = P.S :=
  toData_S P

example :
    P.toData.r = parabolicRadius P.F P.τ₀ :=
  toData_r P

example (τ R : ℝ) :
    P.toData.lam τ R = Real.log (partialR (parabolicRadius P.F P.τ₀) τ R ^ 2) :=
  toData_lam P τ R

example (κ τ R : ℝ) :
    ℝ :=
  density P κ τ R

example {κ : ℝ} (hκ : κ ≠ 0) (hp : (τ, R) ∈ P.S) :
    κ * P.density κ τ R = 4 * deriv P.F R /
      (3 * (P.τ₀ R - τ) * (deriv P.F R * (P.τ₀ R - τ) + 2 * P.F R * deriv P.τ₀ R)) :=
  density_eq P hκ hp

end ParabolicData

example (P : ParabolicData) {κ : ℝ} (hκ : κ ≠ 0) :
    Equations P.toData κ (P.density κ) 0 P.F :=
  solution_parabolic P hκ

example (P : ParabolicData) {κ : ℝ} (hκ : κ ≠ 0) :
    (metric P.toData).IsEinstein κ 0 (dustStress (P.density κ)) :=
  isEinstein_parabolic P hκ

example (f F η : ℝ) :
    ℝ :=
  ellipticRadius f F η

example (f F τ₀ η : ℝ) :
    ℝ :=
  ellipticTime f F τ₀ η

example (f F η : ℝ) :
    ℝ :=
  hyperbolicRadius f F η

example (f F τ₀ η : ℝ) :
    ℝ :=
  hyperbolicTime f F τ₀ η

example (f F η : ℝ) :
    HasDerivAt (ellipticRadius f F) (F / (2 * -f) * Real.sin η) η :=
  hasDerivAt_ellipticRadius f F η

example (f F τ₀ η : ℝ) :
    HasDerivAt (ellipticTime f F τ₀) (-(F / (2 * -f * Real.sqrt (-f))) * (1 - Real.cos η)) η :=
  hasDerivAt_ellipticTime f F τ₀ η

example (f F η : ℝ) :
    HasDerivAt (hyperbolicRadius f F) (F / (2 * f) * Real.sinh η) η :=
  hasDerivAt_hyperbolicRadius f F η

example (f F τ₀ η : ℝ) :
    HasDerivAt (hyperbolicTime f F τ₀) (-(F / (2 * f * Real.sqrt f)) * (Real.cosh η - 1)) η :=
  hasDerivAt_hyperbolicTime f F τ₀ η

example (f F : ℝ) :
    deriv (ellipticRadius f F) = fun η => F / (2 * -f) * Real.sin η :=
  deriv_ellipticRadius f F

example (f F τ₀ : ℝ) :
    deriv (ellipticTime f F τ₀) = fun η => -(F / (2 * -f * Real.sqrt (-f))) * (1 - Real.cos η) :=
  deriv_ellipticTime f F τ₀

example (f F : ℝ) :
    deriv (hyperbolicRadius f F) = fun η => F / (2 * f) * Real.sinh η :=
  deriv_hyperbolicRadius f F

example (f F τ₀ : ℝ) :
    deriv (hyperbolicTime f F τ₀) = fun η => -(F / (2 * f * Real.sqrt f)) * (Real.cosh η - 1) :=
  deriv_hyperbolicTime f F τ₀

example {f F : ℝ} (hf : f < 0) (hF : 0 < F) (τ₀ : ℝ) {η : ℝ} (h0 : 0 < η) (h2 : η < 2 * Real.pi) :
    0 < ellipticRadius f F η ∧ deriv (ellipticTime f F τ₀) η < 0 ∧
      (deriv (ellipticRadius f F) η / deriv (ellipticTime f F τ₀) η) ^ 2 =
        f + F / ellipticRadius f F η ∧
      (deriv (deriv (ellipticRadius f F)) η * deriv (ellipticTime f F τ₀) η -
          deriv (ellipticRadius f F) η * deriv (deriv (ellipticTime f F τ₀)) η) /
          deriv (ellipticTime f F τ₀) η ^ 3 = -F / (2 * ellipticRadius f F η ^ 2) :=
  solution_elliptic hf hF τ₀ h0 h2

example {f F : ℝ} (hf : 0 < f) (hF : 0 < F) (τ₀ : ℝ) {η : ℝ} (h0 : 0 < η) :
    0 < hyperbolicRadius f F η ∧ deriv (hyperbolicTime f F τ₀) η < 0 ∧
      (deriv (hyperbolicRadius f F) η / deriv (hyperbolicTime f F τ₀) η) ^ 2 =
        f + F / hyperbolicRadius f F η ∧
      (deriv (deriv (hyperbolicRadius f F)) η * deriv (hyperbolicTime f F τ₀) η -
          deriv (hyperbolicRadius f F) η * deriv (deriv (hyperbolicTime f F τ₀)) η) /
          deriv (hyperbolicTime f F τ₀) η ^ 3 = -F / (2 * hyperbolicRadius f F η ^ 2) :=
  solution_hyperbolic hf hF τ₀ h0

example (f F τ₀ : ℝ) :
    Tendsto (fun η => (ellipticTime f F τ₀ η, ellipticRadius f F η)) (𝓝[>] 0) (𝓝 (τ₀, 0)) :=
  tendsto_elliptic f F τ₀

example {f F : ℝ} (hf : f < 0) (hF : 0 < F) (τ₀ : ℝ) {η : ℝ} (h0 : 0 < η) :
    ellipticTime f F τ₀ η < τ₀ :=
  ellipticTime_lt hf hF τ₀ h0

example (f F τ₀ : ℝ) :
    Tendsto (fun η => (hyperbolicTime f F τ₀ η, hyperbolicRadius f F η)) (𝓝[>] 0)
      (𝓝 (τ₀, 0)) :=
  tendsto_hyperbolic f F τ₀

example {f F : ℝ} (hf : 0 < f) (hF : 0 < F) (τ₀ : ℝ) {η : ℝ} (h0 : 0 < η) :
    hyperbolicTime f F τ₀ η < τ₀ :=
  hyperbolicTime_lt hf hF τ₀ h0

example (rg r : ℝ) :
    ℝ :=
  eddingtonShift rg r

example {rg r : ℝ} (hrg : 0 < rg) (hr : 0 < r) :
    HasDerivAt (eddingtonShift rg) (Real.sqrt r / (Real.sqrt r + Real.sqrt rg)) r :=
  hasDerivAt_eddingtonShift hrg hr

example (rg : ℝ) (x : E) :
    E :=
  eddingtonMap D rg x

example (rg : ℝ) (x : E) :
    E →ₗ[ℝ] E :=
  eddingtonLinear D rg x

example (rg : ℝ) (x : E) :
    E →L[ℝ] E :=
  eddingtonJacobian D rg x

example (rg : ℝ) (x v : E) :
    eddingtonJacobian D rg x v = ![v 0 + Real.sqrt (D.r (x 0) (x 1)) /
      (Real.sqrt (D.r (x 0) (x 1)) + Real.sqrt rg) * along D.r x v, along D.r x v, v 2, v 3] :=
  eddingtonJacobian_apply rg x v

example (rg : ℝ) (hx : x ∈ domain D) :
    eddingtonMap D rg x ∈ EddingtonFinkelstein.domain :=
  eddingtonMap_mem rg hx

example {rg : ℝ} (hrg : 0 < rg) (hx : x ∈ domain D) :
    HasFDerivAt (eddingtonMap D rg) (eddingtonJacobian D rg x) x :=
  hasFDerivAt_eddingtonMap hrg hx

example {r s g rt rR e θ : ℝ} (hs : 0 < s) (hg : 0 < g) (hr : r = s ^ 2) (hrt : rt = -g / s)
    (he : e = rR ^ 2) (v w : E) :
    -(1 - 2 * (g ^ 2 / 2) / r) * ((v 0 + s / (s + g) * (rt * v 0 + rR * v 1)) *
        (w 0 + s / (s + g) * (rt * w 0 + rR * w 1))) +
      (v 0 + s / (s + g) * (rt * v 0 + rR * v 1)) * (rt * w 0 + rR * w 1) +
      (rt * v 0 + rR * v 1) * (w 0 + s / (s + g) * (rt * w 0 + rR * w 1)) +
      r ^ 2 * (v 2 * w 2) + r ^ 2 * Real.sin θ ^ 2 * (v 3 * w 3) =
    -(v 0 * w 0) + e * (v 1 * w 1) + r ^ 2 * (v 2 * w 2) +
      r ^ 2 * Real.sin θ ^ 2 * (v 3 * w 3) :=
  eddington_pullback_algebra hs hg hr hrt he v w

example {κ : ℝ} {ε : ℝ → ℝ → ℝ} {f F : ℝ → ℝ} (h : Equations D κ ε f F) {rg : ℝ} (hrg : 0 < rg)
    (hx : x ∈ domain D) (hf : f (x 1) = 0) (hF : F (x 1) = rg) (hc : partialT D.r (x 0) (x 1) < 0)
    (v w : E) :
    EddingtonFinkelstein.form (rg / 2) (eddingtonMap D rg x) (eddingtonJacobian D rg x v)
        (eddingtonJacobian D rg x w) = (metric D).form x v w :=
  matching h hrg hx hf hF hc v w

example {κ : ℝ} {ε : ℝ → ℝ → ℝ} {f F : ℝ → ℝ} (h : Equations D κ ε f F) {rg Rb : ℝ} (hrg : 0 < rg)
    (hf : ∀ R, Rb < R → f R = 0) (hF : ∀ R, Rb < R → F R = rg)
    (hc : ∀ τ R, (τ, R) ∈ D.S → Rb < R → partialT D.r τ R < 0) (hx : x ∈ domain D) (hb : Rb < x 1) :
    (∀ v w, EddingtonFinkelstein.form (rg / 2) (eddingtonMap D rg x) (eddingtonJacobian D rg x v)
        (eddingtonJacobian D rg x w) = (metric D).form x v w) ∧
      (κ ≠ 0 → ε (x 0) (x 1) = 0) :=
  matching_exterior h hrg hf hF hc hx hb

namespace ParabolicData

example (P : ParabolicData) {κ τ R : ℝ} (hκ : 0 < κ) (hp : (τ, R) ∈ P.S) :
    0 ≤ P.density κ τ R :=
  density_nonneg P hκ hp

example (P : ParabolicData) {τ R : ℝ} (hp : (τ, R) ∈ P.S) :
    partialT (parabolicRadius P.F P.τ₀) τ R < 0 :=
  partialT_radius_neg P hp

example (rg : ℝ) (hrg : 0 < rg) :
    ParabolicData :=
  lemaitre rg hrg

example (rg : ℝ) (hrg : 0 < rg) (κ : ℝ) :
    (lemaitre rg hrg).density κ = fun _ _ => 0 :=
  density_lemaitre rg hrg κ

example (P : ParabolicData) (R : ℝ) :
    IsPreconnected {τ | (τ, R) ∈ P.toData.S} :=
  isPreconnected_slice P R

example (rg : ℝ) (hrg : 0 < rg) {κ : ℝ} (hκ : κ ≠ 0) :
    (metric (lemaitre rg hrg).toData).IsEinstein κ 0 (dustStress fun _ _ => 0) :=
  isEinstein_lemaitre rg hrg hκ

example (rg Rb : ℝ) (hrg : 0 < rg) (hRb : 0 < Rb) :
    ParabolicData :=
  dustBall rg Rb hrg hRb

example {rg Rb : ℝ} (hrg : 0 < rg) (hRb : 0 < Rb) {R : ℝ} (hR : Rb ≤ R) :
    (dustBall rg Rb hrg hRb).F R = rg :=
  dustBall_F hrg hRb hR

end ParabolicData

example (rg τ R : ℝ) :
    ℝ :=
  lemaitreRadius rg τ R

example (rg : ℝ) (x : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  lemaitreForm rg x

example (P : ParabolicData) {rg : ℝ} (hx : x ∈ domain P.toData) (hF : P.F (x 1) = rg)
    (hF' : deriv P.F (x 1) = 0) (hτ : P.τ₀ (x 1) = x 1) (hτ' : deriv P.τ₀ (x 1) = 1) :
    (metric P.toData).form x = lemaitreForm rg x :=
  lemaitre_eq P hx hF hF' hτ hτ'

example {rg Rb κ : ℝ} (hrg : 0 < rg) (hRb : 0 < Rb) (hκ : κ ≠ 0)
    (hx : x ∈ domain (ParabolicData.dustBall rg Rb hrg hRb).toData) (hb : Rb < x 1) :
    (ParabolicData.dustBall rg Rb hrg hRb).density κ (x 0) (x 1) = 0 ∧
      (metric (ParabolicData.dustBall rg Rb hrg hRb).toData).form x = lemaitreForm rg x ∧
      ∀ v w, EddingtonFinkelstein.form (rg / 2)
          (eddingtonMap (ParabolicData.dustBall rg Rb hrg hRb).toData rg x)
          (eddingtonJacobian (ParabolicData.dustBall rg Rb hrg hRb).toData rg x v)
          (eddingtonJacobian (ParabolicData.dustBall rg Rb hrg hRb).toData rg x w) =
        (metric (ParabolicData.dustBall rg Rb hrg hRb).toData).form x v w :=
  dustBall_exterior hrg hRb hκ hx hb

end ProjectAinos.GeneralRelativity.Tolman

end Tolman
