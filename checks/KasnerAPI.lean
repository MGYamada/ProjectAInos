/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.GeneralRelativity.Kasner

/-! Public consumers of the flat anisotropic model (Landau–Lifshitz §117): the diagonal metric
`−dt² + Σ a_α² dx_α²` with its Christoffel, Ricci and Einstein tables, the Einstein equations with
a comoving perfect fluid, the vacuum Kasner metrics and their characterization by
`Σp = Σp² = 1` or `p = 0`, the Lifshitz–Khalatnikov parametrisation, the curvature of the
non-flat Kasner metrics, and the dust-filled solution with its two limits. Default elaborator
options are intentional: these checks must not rely on the implementation's transparency
settings. Every statement is pinned with its type. -/

noncomputable section

open ContinuousLinearMap Set TopologicalSpace Filter

open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.Kasner

open SmoothGeometry CoordinateMetric

local notation "E" => MinkowskiModel 3

variable {D : Data} {x : E}

example (α : Fin 3) {t : ℝ} (ht : t ∈ D.I) :
    HasDerivAt (D.a α) (deriv (D.a α) t) t :=
  hasDerivAt_a α ht

example (α : Fin 3) {t : ℝ} (ht : t ∈ D.I) :
    HasDerivAt (deriv (D.a α)) (deriv (deriv (D.a α)) t) t :=
  hasDerivAt_deriv_a α ht

example :
    Opens E :=
  domain D

example (hx : x ∈ domain D) :
    x 0 ∈ D.I :=
  time_mem hx

example (hx : x ∈ domain D) (α : Fin 3) :
    0 < D.a α (x 0) :=
  a_pos_of_mem hx α

example {t : ℝ} (ht : t ∈ D.I) :
    FLRW.timeAxis t ∈ domain D :=
  timeAxis_mem ht

example (x : E) :
    Fin 4 → ℝ :=
  coefficients D x

example (y : E) (α : Fin 3) :
    coefficients D y α.succ = D.a α (y 0) ^ 2 :=
  coefficients_succ y α

example {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f D.I) :
    ContDiffOn ℝ ∞ (fun z : E => f (z 0)) (domain D) :=
  contDiffOn_time hf

example (i : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => coefficients D x i) (domain D) :=
  contDiffOn_coefficients i

example :
    CoordinateMetric .timeNegative 3 (domain D) :=
  metric D

example (y : E) :
    (metric D).coefficient y = Matrix.diagonal (coefficients D y) :=
  coefficient_metric y

example (hx : x ∈ domain D) (i : Fin 4) :
    coefficients D x i ≠ 0 :=
  coefficients_ne_zero hx i

example :
    (metric D).IsSynchronous :=
  isSynchronous

example (hx : x ∈ domain D) (α : Fin 3) (v : E) :
    fderiv ℝ (fun z : E => D.a α (z 0) ^ 2) x v =
      2 * D.a α (x 0) * deriv (D.a α) (x 0) * v 0 :=
  fderiv_scale_sq hx α v

example (hx : x ∈ domain D) (i : Fin 4) (v : E) :
    fderiv ℝ (fun z => coefficients D z i) x v =
      ![0, 2 * D.a 0 (x 0) * deriv (D.a 0) (x 0) * v 0,
        2 * D.a 1 (x 0) * deriv (D.a 1) (x 0) * v 0,
        2 * D.a 2 (x 0) * deriv (D.a 2) (x 0) * v 0] i :=
  fderiv_coefficients hx i v

example (α : Fin 3) (x : E) :
    ℝ :=
  gammaSpatial D α x

example (α : Fin 3) (x : E) :
    ℝ :=
  gammaExpansion D α x

example (x : E) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  christoffel D x

example (y : E) (k i j : Fin 4) :
    christoffel D y k i j = christoffel D y k j i :=
  christoffel_symm y k i j

example (hx : x ∈ domain D) (k i j : Fin 4) :
    christoffelOf (metric D).coefficient x k i j = christoffel D x k i j :=
  christoffelOf_eq hx k i j

example (hx : x ∈ domain D) (α β : Fin 3) :
    christoffelOf (metric D).coefficient x 0 α.succ β.succ =
      if α = β then D.a α (x 0) * deriv (D.a α) (x 0) else 0 :=
  christoffelOf_zero_succ_succ hx α β

example (hx : x ∈ domain D) (α β : Fin 3) :
    christoffelOf (metric D).coefficient x α.succ 0 β.succ =
      if α = β then deriv (D.a α) (x 0) / D.a α (x 0) else 0 :=
  christoffelOf_succ_zero_succ hx α β

example (hx : x ∈ domain D) (α β : Fin 3) :
    christoffelOf (metric D).coefficient x α.succ β.succ 0 =
      if α = β then deriv (D.a α) (x 0) / D.a α (x 0) else 0 :=
  christoffelOf_succ_succ_zero hx α β

example (hx : x ∈ domain D) :
    christoffelOf (metric D).coefficient x 0 0 0 = 0 :=
  christoffelOf_zero_zero_zero hx

example (hx : x ∈ domain D) (α : Fin 3) :
    christoffelOf (metric D).coefficient x 0 0 α.succ = 0 ∧
      christoffelOf (metric D).coefficient x 0 α.succ 0 = 0 :=
  christoffelOf_zero_zero_succ hx α

example (hx : x ∈ domain D) (α : Fin 3) :
    christoffelOf (metric D).coefficient x α.succ 0 0 = 0 :=
  christoffelOf_succ_zero_zero hx α

example (hx : x ∈ domain D) (α β γ : Fin 3) :
    christoffelOf (metric D).coefficient x α.succ β.succ γ.succ = 0 :=
  christoffelOf_succ_succ_succ hx α β γ

example (hx : x ∈ domain D) :
    ∀ᶠ z in 𝓝 x, ∀ k i j, christoffelOf (metric D).coefficient z k i j = christoffel D z k i j :=
  eventually_christoffelOf_eq hx

example (hx : x ∈ domain D) (α : Fin 3) (v : E) :
    fderiv ℝ (gammaSpatial D α) x v =
      (deriv (D.a α) (x 0) ^ 2 + D.a α (x 0) * deriv (deriv (D.a α)) (x 0)) * v 0 :=
  fderiv_gammaSpatial hx α v

example (hx : x ∈ domain D) (α : Fin 3) (v : E) :
    fderiv ℝ (gammaExpansion D α) x v =
      (deriv (deriv (D.a α)) (x 0) * D.a α (x 0) - deriv (D.a α) (x 0) ^ 2) /
        D.a α (x 0) ^ 2 * v 0 :=
  fderiv_gammaExpansion hx α v

example (α : Fin 3) (t : ℝ) :
    ℝ :=
  hubble D α t

example (α : Fin 3) (t : ℝ) :
    ℝ :=
  accel D α t

example (t : ℝ) :
    ℝ :=
  expansion D t

example (x : E) :
    ℝ :=
  ricciTime D x

example (α : Fin 3) (x : E) :
    ℝ :=
  ricciSpace D α x

example (x : E) :
    Fin 4 → Fin 4 → ℝ :=
  ricci D x

example (hx : x ∈ domain D) (j k : Fin 4) :
    ricciOf (metric D).coefficient x j k = ricci D x j k :=
  ricciOf_eq hx j k

example (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 0 0 = -∑ α, deriv (deriv (D.a α)) (x 0) / D.a α (x 0) :=
  ricci_zero_zero hx

example (hx : x ∈ domain D) (α : Fin 3) :
    ricciOf (metric D).coefficient x 0 α.succ = 0 :=
  ricci_zero_succ hx α

example (hx : x ∈ domain D) (α : Fin 3) :
    ricciOf (metric D).coefficient x α.succ 0 = 0 :=
  ricci_succ_zero hx α

example (hx : x ∈ domain D) (α β : Fin 3) :
    ricciOf (metric D).coefficient x α.succ β.succ =
      if α = β then
        D.a α (x 0) * deriv (deriv (D.a α)) (x 0) + D.a α (x 0) * deriv (D.a α) (x 0) *
          (∑ γ, deriv (D.a γ) (x 0) / D.a γ (x 0) - deriv (D.a α) (x 0) / D.a α (x 0))
      else 0 :=
  ricci_succ_succ hx α β

example (hx : x ∈ domain D) :
    ((metric D).coefficient x)⁻¹ = Matrix.diagonal fun l => (coefficients D x l)⁻¹ :=
  coefficient_metric_inv hx

example (hx : x ∈ domain D) :
    scalarOf (metric D).coefficient x = ∑ a, ricci D x a a / coefficients D x a :=
  scalarOf_eq_sum hx

example (t : ℝ) :
    ℝ :=
  hubblePairs D t

example (hx : x ∈ domain D) :
    scalarOf (metric D).coefficient x = 2 * ∑ α, accel D α (x 0) + 2 * hubblePairs D (x 0) :=
  scalarOf_eq hx

example (t : ℝ) :
    Fin 3 → ℝ :=
  spatialFactor D t

example (x : E) :
    Fin 4 → Fin 4 → ℝ :=
  einstein D x

example (hx : x ∈ domain D) (i k : Fin 4) :
    einsteinOf (metric D).coefficient x i k = einstein D x i k :=
  einsteinOf_eq hx i k

example (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 0 0 = hubblePairs D (x 0) :=
  einstein_zero_zero hx

example (hx : x ∈ domain D) (α : Fin 3) :
    einsteinOf (metric D).coefficient x 0 α.succ = 0 :=
  einstein_zero_succ hx α

example (hx : x ∈ domain D) (α : Fin 3) :
    einsteinOf (metric D).coefficient x α.succ 0 = 0 :=
  einstein_succ_zero hx α

example (hx : x ∈ domain D) (α β : Fin 3) :
    einsteinOf (metric D).coefficient x α.succ β.succ =
      if α = β then -(D.a α (x 0) ^ 2 * spatialFactor D (x 0) α) else 0 :=
  einstein_succ_succ hx α β

example :
    Fin 4 → ℝ :=
  fluidCovector

example (ρ p : ℝ → ℝ) (x : E) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  perfectFluidStress D ρ p x

example (ρ p : ℝ → ℝ) (x : E) :
    Fin 4 → ℝ :=
  fluidDiagonal D ρ p x

example (ρ p : ℝ → ℝ) (y : E) :
    perfectFluidStress D ρ p y = Matrix.diagonal (fluidDiagonal D ρ p y) :=
  perfectFluidStress_eq ρ p y

example :
    perfectFluidStress D 0 0 = 0 :=
  perfectFluidStress_zero

example (κ Λ : ℝ) (ρ : ℝ → ℝ) (t : ℝ) :
    Prop :=
  Constraint D κ Λ ρ t

example (κ Λ : ℝ) (p : ℝ → ℝ) (α : Fin 3) (t : ℝ) :
    Prop :=
  Evolution D κ Λ p α t

example (hx : x ∈ domain D) (κ Λ : ℝ) (ρ p : ℝ → ℝ) :
    einsteinOf (metric D).coefficient x 0 0 + Λ * (metric D).coefficient x 0 0 -
        κ * perfectFluidStress D ρ p x 0 0 =
      hubblePairs D (x 0) - (κ * ρ (x 0) + Λ) :=
  einsteinEquation_zero_zero hx κ Λ ρ p

example (hx : x ∈ domain D) (κ Λ : ℝ) (ρ p : ℝ → ℝ) (α : Fin 3) :
    einsteinOf (metric D).coefficient x α.succ α.succ + Λ * (metric D).coefficient x α.succ α.succ -
        κ * perfectFluidStress D ρ p x α.succ α.succ =
      -(D.a α (x 0) ^ 2) * (spatialFactor D (x 0) α - (-κ * p (x 0) + Λ)) :=
  einsteinEquation_succ_succ hx κ Λ ρ p α

example (hx : x ∈ domain D) (κ Λ : ℝ) (ρ p : ℝ → ℝ) :
    (∀ i k, einsteinOf (metric D).coefficient x i k + Λ * (metric D).coefficient x i k =
      κ * perfectFluidStress D ρ p x i k) ↔
      Constraint D κ Λ ρ (x 0) ∧ ∀ α, Evolution D κ Λ p α (x 0) :=
  isEinstein_at_iff hx κ Λ ρ p

example (κ Λ : ℝ) (ρ p : ℝ → ℝ) :
    (metric D).IsEinstein κ Λ (perfectFluidStress D ρ p) ↔
      ∀ t ∈ D.I, Constraint D κ Λ ρ t ∧ ∀ α, Evolution D κ Λ p α t :=
  isEinstein_iff κ Λ ρ p

example (h : ∀ z ∈ domain D, ∀ j k, ricciOf (metric D).coefficient z j k = 0) (κ : ℝ) :
    (metric D).IsEinstein κ 0 0 :=
  isEinstein_of_ricciOf_eq_zero h κ

example {α : Fin 3} {h : ℝ → ℝ} {t : ℝ} (ht : t ∈ D.I) (hd : HasDerivAt (D.a α) (D.a α t * h t) t) :
    hubble D α t = h t :=
  hubble_eq_of_hasDerivAt ht hd

example {α : Fin 3} {h : ℝ → ℝ} {t h' : ℝ} (ht : t ∈ D.I)
    (hd : ∀ s ∈ D.I, HasDerivAt (D.a α) (D.a α s * h s) s) (hh : HasDerivAt h h' t) :
    accel D α t = h t ^ 2 + h' :=
  accel_eq_of_hasDerivAt ht hd hh

example (q : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => s ^ q) (t ^ q * (q / t)) t :=
  hasDerivAt_rpow q ht

example (p : Fin 3 → ℝ) :
    Data :=
  kasner p

example (p : Fin 3 → ℝ) (α : Fin 3) (t : ℝ) :
    (kasner p).a α t = t ^ p α :=
  kasner_a p α t

example (p : Fin 3 → ℝ) :
    (kasner p).I = Ioi 0 :=
  kasner_I p

example (p : Fin 3 → ℝ) (α : Fin 3) {t : ℝ} (ht : 0 < t) :
    HasDerivAt ((kasner p).a α) ((kasner p).a α t * (p α * t⁻¹)) t :=
  hasDerivAt_kasner p α ht

example (p : Fin 3 → ℝ) (α : Fin 3) {t : ℝ} (ht : 0 < t) :
    hubble (kasner p) α t = p α / t :=
  hubble_kasner p α ht

example (p : Fin 3 → ℝ) (α : Fin 3) {t : ℝ} (ht : 0 < t) :
    accel (kasner p) α t = p α * (p α - 1) / t ^ 2 :=
  accel_kasner p α ht

example {p : Fin 3 → ℝ} {z : E} (hz : z ∈ domain (kasner p)) :
    0 < z 0 :=
  time_pos_kasner hz

example {p : Fin 3 → ℝ} {z : E} (hz : z ∈ domain (kasner p)) :
    ricciOf (metric (kasner p)).coefficient z 0 0 = -(∑ α, p α ^ 2 - ∑ α, p α) / z 0 ^ 2 :=
  ricci_zero_zero_kasner hz

example {t : ℝ} (ht : 0 < t) (q : ℝ) :
    (t ^ q) ^ 2 = t ^ (2 * q) :=
  rpow_sq ht q

example {p : Fin 3 → ℝ} {z : E} (hz : z ∈ domain (kasner p)) (α β : Fin 3) :
    ricciOf (metric (kasner p)).coefficient z α.succ β.succ =
      if α = β then p α * z 0 ^ (2 * p α - 2) * (∑ γ, p γ - 1) else 0 :=
  ricci_succ_succ_kasner hz α β

example {p : Fin 3 → ℝ} (h0 : ∑ α, p α ^ 2 = ∑ α, p α) (hs : ∀ α, p α * (∑ β, p β - 1) = 0)
    {z : E} (hz : z ∈ domain (kasner p)) (j k : Fin 4) :
    ricciOf (metric (kasner p)).coefficient z j k = 0 :=
  ricciOf_kasner_eq_zero_of h0 hs hz j k

example (p : Fin 3 → ℝ) :
    (∀ z ∈ domain (kasner p), ∀ j k, ricciOf (metric (kasner p)).coefficient z j k = 0) ↔
      (∑ α, p α = 1 ∧ ∑ α, p α ^ 2 = 1) ∨ p = 0 :=
  ricciOf_kasner_eq_zero_iff p

example {p : Fin 3 → ℝ} (h : (∑ α, p α = 1 ∧ ∑ α, p α ^ 2 = 1) ∨ p = 0) (κ : ℝ) :
    (metric (kasner p)).IsEinstein κ 0 0 :=
  isEinstein_kasner h κ

example {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) {t : ℝ} (ht : 0 < t) :
    (kasner p).a 0 t * (kasner p).a 1 t * (kasner p).a 2 t = t :=
  volume_kasner h1 ht

example (hx : x ∈ domain D) (α : Fin 3) :
    curvatureOf (christoffel D) x α.succ 0 α.succ 0 = accel D α (x 0) :=
  curvatureOf_christoffel hx α

example (x y : domain D) (α : Fin 3) :
    (metric D).toLorentzMetric.chartCurvature (physicalChart x) y α.succ 0 α.succ 0 =
      accel D α (y.1 0) :=
  chartCurvature_succ_zero_succ_zero x y α

example {a b c : ℝ} (h1 : a + b + c = 1) (h2 : a ^ 2 + b ^ 2 + c ^ 2 = 1) (ha : a = 0) :
    (b = 0 ∧ c = 1) ∨ (b = 1 ∧ c = 0) :=
  kasner_of_eq_zero h1 h2 ha

example {a b c : ℝ} (h1 : a + b + c = 1) (h2 : a ^ 2 + b ^ 2 + c ^ 2 = 1) (ha : a = 1) :
    b = 0 ∧ c = 0 :=
  kasner_of_eq_one h1 h2 ha

example {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1)
    (hp : p ≠ ![1, 0, 0] ∧ p ≠ ![0, 1, 0] ∧ p ≠ ![0, 0, 1]) (α : Fin 3) :
    p α ≠ 0 ∧ p α ≠ 1 :=
  kasner_exponent_ne h1 h2 hp α

example {p : Fin 3 → ℝ} (x y : domain (kasner p)) (α : Fin 3) :
    (metric (kasner p)).toLorentzMetric.chartCurvature (physicalChart x) y α.succ 0 α.succ 0 =
      p α * (p α - 1) / y.1 0 ^ 2 :=
  chartCurvature_kasner x y α

example {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1)
    (hp : p ≠ ![1, 0, 0] ∧ p ≠ ![0, 1, 0] ∧ p ≠ ![0, 0, 1]) (x y : domain (kasner p)) (α : Fin 3) :
    (metric (kasner p)).toLorentzMetric.chartCurvature (physicalChart x) y α.succ 0 α.succ 0 ≠
      0 :=
  chartCurvature_kasner_ne_zero h1 h2 hp x y α

example (u : ℝ) :
    0 < 1 + u + u ^ 2 :=
  kasnerDenom_pos u

example (u : ℝ) :
    Fin 3 → ℝ :=
  kasnerExponents u

example (u : ℝ) :
    ∑ α, kasnerExponents u α = 1 :=
  sum_kasnerExponents u

example (u : ℝ) :
    ∑ α, kasnerExponents u α ^ 2 = 1 :=
  sum_sq_kasnerExponents u

example {u : ℝ} (hu : 1 ≤ u) :
    kasnerExponents u 0 ≤ kasnerExponents u 1 ∧ kasnerExponents u 1 ≤ kasnerExponents u 2 :=
  kasnerExponents_mono hu

example {u : ℝ} (hu : u ≠ 0) :
    kasnerExponents u⁻¹ = ![kasnerExponents u 0, kasnerExponents u 2, kasnerExponents u 1] :=
  kasnerExponents_inv hu

example {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1) :
    p 0 * p 1 + p 0 * p 2 + p 1 * p 2 = 0 :=
  kasner_pairs h1 h2

example {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1) (h01 : p 0 ≤ p 1)
    (h12 : p 1 ≤ p 2) :
    -1 / 3 ≤ p 0 ∧ p 0 ≤ 0 ∧ 0 ≤ p 1 ∧ p 1 ≤ 2 / 3 ∧ 2 / 3 ≤ p 2 ∧ p 2 ≤ 1 :=
  kasner_ranges h1 h2 h01 h12

example {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1) (h01 : p 0 ≤ p 1)
    (h12 : p 1 ≤ p 2) :
    p = ![0, 0, 1] ∨ ∃ u, 1 ≤ u ∧ p = kasnerExponents u :=
  eq_kasnerExponents h1 h2 h01 h12

example (p : Fin 3 → ℝ) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    Data :=
  dustKasner p t₀ ht₀

example (κ t₀ t : ℝ) :
    ℝ :=
  dustDensity κ t₀ t

example {κ t₀ t : ℝ} (hκ : 0 < κ) (ht₀ : 0 ≤ t₀) (ht : 0 < t) :
    0 < dustDensity κ t₀ t :=
  dustDensity_pos hκ ht₀ ht

section Dust

variable {p : Fin 3 → ℝ} {t₀ : ℝ} (ht₀ : 0 ≤ t₀)

example (α : Fin 3) (t : ℝ) :
    (dustKasner p t₀ ht₀).a α t = t ^ p α * (t + t₀) ^ (2 / 3 - p α) :=
  dustKasner_a ht₀ α t

example (α : Fin 3) {t : ℝ} (ht : 0 < t) :
    HasDerivAt ((dustKasner p t₀ ht₀).a α)
      ((dustKasner p t₀ ht₀).a α t * (p α * t⁻¹ + (2 / 3 - p α) * (t + t₀)⁻¹)) t :=
  hasDerivAt_dustKasner ht₀ α ht

example (α : Fin 3) {t : ℝ} (ht : 0 < t) :
    hubble (dustKasner p t₀ ht₀) α t = p α / t + (2 / 3 - p α) / (t + t₀) :=
  hubble_dustKasner ht₀ α ht

example (α : Fin 3) {t : ℝ} (ht : 0 < t) :
    accel (dustKasner p t₀ ht₀) α t = (p α / t + (2 / 3 - p α) / (t + t₀)) ^ 2 -
      p α / t ^ 2 - (2 / 3 - p α) / (t + t₀) ^ 2 :=
  accel_dustKasner ht₀ α ht

example (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1) {κ : ℝ} (hκ : κ ≠ 0) {t : ℝ} (ht : 0 < t) :
    Constraint (dustKasner p t₀ ht₀) κ 0 (dustDensity κ t₀) t :=
  constraint_dustKasner ht₀ h1 h2 hκ ht

example (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1) (κ : ℝ) {t : ℝ} (ht : 0 < t) (α : Fin 3) :
    Evolution (dustKasner p t₀ ht₀) κ 0 0 α t :=
  evolution_dustKasner ht₀ h1 h2 κ ht α

example (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1) {κ : ℝ} (hκ : κ ≠ 0) :
    (metric (dustKasner p t₀ ht₀)).IsEinstein κ 0
      (perfectFluidStress (dustKasner p t₀ ht₀) (dustDensity κ t₀) 0) :=
  isEinstein_dustKasner ht₀ h1 h2 hκ

example (ht₀' : 0 < t₀) (α : Fin 3) :
    Tendsto (fun t => (dustKasner p t₀ ht₀).a α t / t ^ p α) (𝓝[>] 0)
      (𝓝 (t₀ ^ (2 / 3 - p α))) :=
  tendsto_dustKasner_nhdsGT ht₀ ht₀' α

example (α : Fin 3) :
    Tendsto (fun t => (dustKasner p t₀ ht₀).a α t / t ^ (2 / 3 : ℝ)) atTop (𝓝 1) :=
  tendsto_dustKasner_atTop ht₀ α

end Dust

end ProjectAinos.GeneralRelativity.Kasner
