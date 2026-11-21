/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Wave.TransverseTraceless
import ProjectAinos.GeneralRelativity.LinearizedRadiation

/-! Public consumers of the radiation of gravitational waves (Landau–Lifshitz §110): the
transverse-traceless projection with its sphere integral, the retarded perturbation of a localized
conserved stress in harmonic gauge with the linearized Einstein equations, the second moment and
the far-zone quadrupole amplitude, the flux of the quadratic pseudotensor at infinity and the
quadrupole formula, and the circular binary. Default elaborator options are intentional: these
checks must not rely on the implementation's transparency settings. Every statement is pinned with
its type. -/

noncomputable section


section TransverseTraceless

open MeasureTheory Set Metric Real

namespace ProjectAinos.SmoothGeometry.Wave

open Sphere CoordinateMetric

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (n : E3) :
    Fin 4 → ℝ :=
  waveCovector n

example (k : Fin 4 → ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) (c a b : Fin 4) :
    ℝ :=
  planeChristoffel k A c a b

example (n : E3) (A : Matrix (Fin 4) (Fin 4) ℝ) :
    ℝ :=
  planeFlux n A

example (n : E3) (S : Fin 3 → Fin 3 → ℝ) :
    ℝ :=
  ttSquare n S

example (n : E3) (S : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) :
    ℝ :=
  transverseTraceless n S i j

example (S : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) :
    ℝ :=
  quadrupoleOf S i j

example {n : E3} (hn : ‖n‖ = 1) :
    n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 :=
  sum_sq_eq_one hn

example {n : E3} (hn : ‖n‖ = 1) {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : ∀ a b, A a b = A b a) :
    planeFlux n A = ttSquare n (fun i j => A i.succ j.succ) / 4 +
      ((∑ i : Fin 3, A i.succ i.succ) - ∑ i : Fin 3, ∑ j : Fin 3, n i * A i.succ j.succ * n j) *
        (2 * A 0 0 - 3 * (∑ i : Fin 3, A i.succ i.succ) +
          ∑ i : Fin 3, ∑ j : Fin 3, n i * A i.succ j.succ * n j) / 8 :=
  planeFlux_eq hn hA

example {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : ∀ a b, A a b = A b a) (a b : Fin 4) :
    traceReverse .timeNegative A a b = traceReverse .timeNegative A b a :=
  traceReverse_symm hA a b

example {n : E3} (hn : ‖n‖ = 1) {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : ∀ a b, A a b = A b a)
    (hg : ∀ b, A 0 b = -∑ α : Fin 3, n α * A α.succ b) :
    planeFlux n (traceReverse .timeNegative A) = ttSquare n (fun i j => A i.succ j.succ) / 4 :=
  planeFlux_traceReverse hn hA hg

example (n : E3) (S : Fin 3 → Fin 3 → ℝ) (c : ℝ) :
    ttSquare n (fun i j => c * S i j) = c ^ 2 * ttSquare n S :=
  ttSquare_mul n S c

example {n : E3} (hn : ‖n‖ = 1) {S : Fin 3 → Fin 3 → ℝ} (hS : ∀ i j, S i j = S j i) :
    ∑ i, ∑ j, transverseTraceless n S i j ^ 2 = ttSquare n S :=
  sum_sq_transverseTraceless hn hS

example {S : Fin 3 → Fin 3 → ℝ} (hS : ∀ i j, S i j = S j i) :
    ∫ n : sphere (0 : E3) 1, ttSquare (n : E3) S ∂sphereMeasure =
      8 * π / 45 * ∑ i, ∑ j, quadrupoleOf S i j ^ 2 :=
  integral_ttSquare hS

example {m : ℕ} (G : Fin m → Fin m → ℝ) (i k : Fin m) :
    Continuous fun Γ : Fin m → Fin m → Fin m → ℝ => pseudoBraces G Γ i k :=
  continuous_pseudoBraces G i k

example {m : ℕ} (G : Fin m → Fin m → ℝ) (Γ : Fin m → Fin m → Fin m → ℝ) (r : ℝ) (i k : Fin m) :
    pseudoBraces G (fun a b c => r * Γ a b c) i k = r ^ 2 * pseudoBraces G Γ i k :=
  pseudoBraces_mul G Γ r i k

example (n : E3) :
    Continuous fun A : Matrix (Fin 4) (Fin 4) ℝ =>
    planeFlux n A :=
  continuous_planeFlux n

example (n : E3) (U W : Fin 3 → Fin 3 → ℝ) :
    ℝ :=
  ttBilinear n U W

example (n : E3) (X Y : Fin 3 → Fin 3 → ℝ) :
    ttSquare n X - ttSquare n Y = ttBilinear n (fun i j => X i j - Y i j)
      (fun i j => X i j + Y i j) :=
  ttSquare_sub n X Y

example {n : E3} (hn : ∀ i, |n i| ≤ 1) {U W : Fin 3 → Fin 3 → ℝ} {u w : ℝ}
    (hU : ∀ i j, |U i j| ≤ u) (hW : ∀ i j, |W i j| ≤ w) :
    |ttBilinear n U W| ≤ 135 * u * w :=
  abs_ttBilinear_le hn hU hW

example {n : E3} (hn : ∀ i, |n i| ≤ 1) {X Y : Fin 3 → Fin 3 → ℝ} {B δ : ℝ}
    (hX : ∀ i j, |X i j| ≤ B) (hY : ∀ i j, |Y i j| ≤ B) (hXY : ∀ i j, |X i j - Y i j| ≤ δ) :
    |ttSquare n X - ttSquare n Y| ≤ 270 * B * δ :=
  abs_ttSquare_sub_le hn hX hY hXY

end ProjectAinos.SmoothGeometry.Wave

end TransverseTraceless

section LinearizedRadiation

open MeasureTheory Filter Set Metric Real

open scoped Topology ContDiff

namespace ProjectAinos.GeneralRelativity.LinearizedRadiation

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Sphere CoordinateMetric

open Electrodynamics Electrodynamics.Radiation SpecialRelativity WeakWaves

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (f : Spacetime → ℝ) (x : Spacetime) (a b : Fin 4) :
    secondPartial f x a b = partialAt (partialAt f b) a x :=
  secondPartial_eq_partialAt f x a b

example (i : Fin 3) :
    lorentzSign (d := 3) .timeNegative i.succ = 1 :=
  lorentzSign_succ i

example (f : Spacetime → ℝ) (x : Spacetime) :
    flatBox .timeNegative f x = box f x :=
  flatBox_eq_box f x

example (T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (a b : Fin 4) :
    ℝ × E3 → ℝ :=
  splitStress T a b

namespace LocalizedStress

variable {T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ}

example (hT : LocalizedStress T a) (i k : Fin 4) :
    Wave.LocalizedSupport a (splitStress T i k) :=
  localizedSupport hT i k

example (hT : LocalizedStress T a) (i k : Fin 4) :
    Wave.SubluminalSupport a 0 fun p => T (Wave.timeSpaceEquiv.symm p) i k :=
  subluminalSupport hT i k

example (hT : LocalizedStress T a) (i k : Fin 4) :
    ContDiff ℝ ∞ (splitStress T i k) :=
  contDiff_split hT i k

example (hT : LocalizedStress T a) {t : ℝ} {x : E3} (hx : a < ‖x‖) (i k : Fin 4) :
    T (vector t x) i k = 0 :=
  apply_eq_zero hT hx i k

end LocalizedStress

example (κ : ℝ) (T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (z : Spacetime) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  retardedPerturbation κ T z

example (κ : ℝ) (T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (z : Spacetime) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  metricPerturbation κ T z

variable {T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ} {a κ : ℝ}

example (z : Spacetime) (i k : Fin 4) :
    retardedPerturbation κ T z i k = 2 * κ * retardedScalar (fun w => T w i k) z :=
  retardedPerturbation_apply z i k

example (z : Spacetime) :
    traceReverse .timeNegative (metricPerturbation κ T z) = retardedPerturbation κ T z :=
  traceReverse_metricPerturbation z

example (hT : LocalizedStress T a) (i k : Fin 4) :
    ContDiff ℝ ∞ fun z => retardedPerturbation κ T z i k :=
  contDiff_retardedPerturbation hT i k

example (hT : LocalizedStress T a) (i k : Fin 4) :
    ContDiff ℝ ∞ fun z => metricPerturbation κ T z i k :=
  contDiff_metricPerturbation hT i k

example (hT : LocalizedStress T a) (z : Spacetime) (i k : Fin 4) :
    retardedPerturbation κ T z i k = retardedPerturbation κ T z k i :=
  retardedPerturbation_symm hT z i k

example (hT : LocalizedStress T a) (x : Spacetime) (i k : Fin 4) :
    flatBox .timeNegative (fun z => retardedPerturbation κ T z i k) x = -(2 * κ * T x i k) :=
  flatBox_retardedPerturbation hT x i k

example (hT : LocalizedStress T a) (x : Spacetime) (i k c : Fin 4) :
    fderiv ℝ (fun z => retardedPerturbation κ T z i k) x (Pi.single c 1) =
      2 * κ * retardedScalar (partialAt (fun w => T w i k) c) x :=
  fderiv_retardedPerturbation hT x i k c

example (hT : LocalizedStress T a) (x : Spacetime) (b : Fin 4) :
    ∑ c : Fin 4, lorentzSign (d := 3) .timeNegative c *
      fderiv ℝ (fun z => retardedPerturbation κ T z c b) x (Pi.single c 1) = 0 :=
  harmonic_retardedPerturbation hT x b

example (hT : LocalizedStress T a) :
    IsHarmonicGauge .timeNegative (metricPerturbation κ T) ⊤ :=
  isHarmonicGauge_metricPerturbation hT

example (hT : LocalizedStress T a) (x : Spacetime) (j k : Fin 4) :
    linearizedEinstein .timeNegative (metricPerturbation κ T) x j k = κ * T x j k :=
  linearizedEinstein_retardedPerturbation hT x j k

example (T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (b : Fin 4) :
    Spacetime → Spacetime :=
  stressColumn T b

example (b : Fin 4) (v : Spacetime) (μ : Fin 4) :
    stressColumn T b v μ =
      lorentzSign (d := 3) .timeNegative μ * lorentzSign (d := 3) .timeNegative b * T v μ b :=
  stressColumn_apply b v μ

example (hT : LocalizedStress T a) (b : Fin 4) :
    ContDiff ℝ ∞ (stressColumn T b) :=
  contDiff_stressColumn hT b

example (hT : LocalizedStress T a) (b : Fin 4) (v : Spacetime) :
    divergence4 (stressColumn T b) v = 0 :=
  divergence4_stressColumn hT b v

example (hT : LocalizedStress T a) (b : Fin 4) (t : ℝ) (x : E3) (hx : a < ‖x‖) :
    stressColumn T b (vector t x) = 0 :=
  stressColumn_eq_zero hT b t x hx

example {k : Spacetime → Spacetime} (hk : ContDiff ℝ ∞ k) (hdiv : ∀ v, divergence4 k v = 0)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0) (δ : Fin 3) (s : ℝ) :
    HasDerivAt (fun s => ∫ y, k (vector s y) 0 * y δ) (∫ y, k (vector s y) δ.succ) s :=
  hasDerivAt_integral_mul_coord hk hdiv hs δ s

example (T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (s : ℝ) (α β : Fin 3) :
    ℝ :=
  secondMoment T s α β

example (T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (s : ℝ) (γ δ : Fin 3) :
    ℝ :=
  momentumMoment T s γ δ

example (T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (s : ℝ) (i k : Fin 4) :
    ℝ :=
  stressIntegral T s i k

example (hT : LocalizedStress T a) (α β : Fin 3) (s : ℝ) :
    HasDerivAt (fun s => secondMoment T s α β)
      (-(momentumMoment T s β α + momentumMoment T s α β)) s :=
  hasDerivAt_secondMoment_stress hT α β s

example (hT : LocalizedStress T a) (γ δ : Fin 3) (s : ℝ) :
    HasDerivAt (fun s => momentumMoment T s γ δ) (-stressIntegral T s δ.succ γ.succ) s :=
  hasDerivAt_momentumMoment hT γ δ s

example (hT : LocalizedStress T a) (s : ℝ) (α β : Fin 3) :
    ∫ y : E3, T (vector s y) α.succ β.succ =
      deriv (deriv fun s => secondMoment T s α β) s / 2 :=
  integral_stress_eq_moment hT s α β

example {ι X : Type*} {F : ι → X → ℝ} {f : X → ℝ} {l : Filter ι} {s : Set X}
    (h : TendstoUniformlyOn F f l s) (c : ℝ) :
    TendstoUniformlyOn (fun i x => c * F i x) (fun x => c * f x) l s :=
  tendstoUniformlyOn_const_mul h c

example (t : ℝ) (x : E3) (i k : Fin 4) :
    retardedPerturbation κ T (vector t x) i k =
      2 * κ * Wave.retardedIntegral (splitStress T i k) (t, x) :=
  retardedPerturbation_vector t x i k

example (hT : LocalizedStress T a) {K : Set ℝ} (hK : IsCompact K) (i k : Fin 4) :
    TendstoUniformlyOn
      (fun R (p : ℝ × E3) => R * retardedPerturbation κ T (vector (p.1 + R) (R • p.2)) i k)
      (fun p => 2 * κ * Wave.farAmplitude (splitStress T i k) p.1 p.2) atTop
      (K ×ˢ sphere (0 : E3) 1) :=
  tendstoUniformlyOn_mul_retardedPerturbation hT hK i k

example (ε : ℝ) (a : Fin 4) :
    ℝ :=
  indexScale ε a

example (ε : ℝ) (T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (v : Spacetime) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  slowStress ε T v

example (ε : ℝ) (v : Spacetime) (a b : Fin 4) :
    slowStress ε T v a b = indexScale ε a * indexScale ε b * T (timeDilation ε v) a b :=
  slowStress_apply ε v a b

example (hT : LocalizedStress T a) (ε : ℝ) (z : Spacetime) (i k c : Fin 4) :
    fderiv ℝ (fun w => slowStress ε T w i k) z (Pi.single c 1) =
      indexScale ε i * indexScale ε k * (if c = 0 then ε else 1) *
        fderiv ℝ (fun w => T w i k) (timeDilation ε z) (Pi.single c 1) :=
  fderiv_slowStress hT ε z i k c

example (hT : LocalizedStress T a) (ε : ℝ) :
    LocalizedStress (slowStress ε T) a :=
  LocalizedStress.slow hT ε

example {F : Spacetime → ℝ} (hF : Differentiable ℝ F) {M : ℝ}
    (hM : ∀ v, |fderiv ℝ F v (Pi.single 0 1)| ≤ M) (y : E3) (s₁ s₂ : ℝ) :
    |F (vector s₁ y) - F (vector s₂ y)| ≤ M * |s₁ - s₂| :=
  abs_sub_le_of_timeDeriv_le hF hM y s₁ s₂

example {F : Spacetime → ℝ} (hF : ContDiff ℝ 1 F) {M d : ℝ} (ha : 0 ≤ a)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → F (vector t x) = 0)
    (hM : ∀ v, |fderiv ℝ F v (Pi.single 0 1)| ≤ M) {τ : E3 → ℝ} (hτ : Continuous τ)
    (hτd : ∀ y : E3, ‖y‖ ≤ a → |τ y| ≤ d) (s : ℝ) :
    |(∫ y : E3, F (vector (s + τ y) y)) - ∫ y : E3, F (vector s y)| ≤
      M * d * (4 * π / 3 * a ^ 3) :=
  abs_integral_delay_sub_le hF ha hs hM hτ hτd s

example (ε u : ℝ) (n : E3) (i k : Fin 4) :
    Wave.farAmplitude (splitStress (slowStress ε T) i k) u n =
      (4 * π)⁻¹ * (indexScale ε i * indexScale ε k) *
        ∫ y, T (vector (ε * u + ε * inner ℝ n y) y) i k :=
  farAmplitude_slowStress ε u n i k

example (hT : LocalizedStress T a) {α β : Fin 3} {M : ℝ}
    (hM : ∀ v, |fderiv ℝ (fun w => T w α.succ β.succ) v (Pi.single 0 1)| ≤ M) {ε : ℝ} (hε : 0 ≤ ε)
    (u : ℝ) {n : E3} (hn : ‖n‖ = 1) :
    Tendsto (fun R => R * retardedPerturbation κ (slowStress ε T) (vector (u + R) (R • n))
        α.succ β.succ) atTop
      (𝓝 (2 * κ * Wave.farAmplitude (splitStress (slowStress ε T) α.succ β.succ) u n)) ∧
    |2 * κ * Wave.farAmplitude (splitStress (slowStress ε T) α.succ β.succ) u n -
        κ / (4 * π) * ε ^ 2 * deriv (deriv fun s => secondMoment T s α β) (ε * u)| ≤
      2 * |κ| / 3 * M * a ^ 4 * ε ^ 3 :=
  farZone_quadrupole hT hM hε u hn

example (h : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (x : Spacetime) (i k : Fin 4) :
    ℝ :=
  quadraticPseudotensor h x i k

example (d : Fin 4 → Fin 4 → Fin 4 → ℝ) (k i j : Fin 4) :
    ℝ :=
  christoffelOfDerivs d k i j

example (d : Fin 4 → Fin 4 → Fin 4 → ℝ) (c a b : Fin 4) :
    ℝ :=
  traceReverseDerivs d c a b

example (h : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (x : Spacetime) (k i j : Fin 4) :
    linearizedChristoffel .timeNegative h x k i j =
      christoffelOfDerivs (fun c a b => fderiv ℝ (fun z => h z a b) x (Pi.single c 1)) k i j :=
  linearizedChristoffel_eq h x k i j

example (hT : LocalizedStress T a) (x : Spacetime) (i k c : Fin 4) :
    fderiv ℝ (fun z => metricPerturbation κ T z i k) x (Pi.single c 1) =
      traceReverseDerivs (fun c a b => fderiv ℝ (fun z => retardedPerturbation κ T z a b) x
        (Pi.single c 1)) c i k :=
  fderiv_metricPerturbation hT x i k c

example (r : ℝ) (d : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    christoffelOfDerivs (fun c a b => r * d c a b) = fun k i j => r * christoffelOfDerivs d k i j :=
  christoffelOfDerivs_mul r d

example (r : ℝ) (d : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    traceReverseDerivs (fun c a b => r * d c a b) = fun c a b => r * traceReverseDerivs d c a b :=
  traceReverseDerivs_mul r d

example (k : Fin 4 → ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) :
    christoffelOfDerivs (traceReverseDerivs fun c a b => k c * A a b) =
      Wave.planeChristoffel k (traceReverse .timeNegative A) :=
  christoffelOfDerivs_plane k A

example (hT : LocalizedStress T a) (x : Spacetime) (i k c : Fin 4) :
    fderiv ℝ (fun z => retardedPerturbation κ T z i k) x (Pi.single c 1) =
      2 * κ * partialAt (retardedScalar fun w => T w i k) c x :=
  fderiv_retardedPerturbation_eq hT x i k c

example (κ : ℝ) (T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (u : ℝ) (n : E3) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  gravitationalAmplitude κ T u n

example (n : E3) :
    Wave.waveCovector n 0 = 1 :=
  waveCovector_zero n

example (n : E3) (γ : Fin 3) :
    Wave.waveCovector n γ.succ = -n γ :=
  waveCovector_succ n γ

example (hT : LocalizedStress T a) {K : Set ℝ} (hK : IsCompact K) (i k c : Fin 4) :
    TendstoUniformlyOn
      (fun R (p : ℝ × E3) => R * fderiv ℝ (fun z => retardedPerturbation κ T z i k)
        (vector (p.1 + R) (R • p.2)) (Pi.single c 1))
      (fun p => Wave.waveCovector p.2 c * gravitationalAmplitude κ T p.1 p.2 i k) atTop
      (K ×ˢ sphere (0 : E3) 1) :=
  tendstoUniformlyOn_mul_fderiv_retardedPerturbation hT hK i k c

example {ι : Type*} (s : Finset ι) {f : ι → ℝ × E3 → ℝ} (hc : ∀ i ∈ s, Continuous (f i))
    (hl : ∀ i ∈ s, Wave.LocalizedSupport a (f i)) (u : ℝ) (n : E3) :
    Wave.farAmplitude (fun p => ∑ i ∈ s, f i p) u n = ∑ i ∈ s, Wave.farAmplitude (f i) u n :=
  farAmplitude_finsetSum s hc hl u n

example (hT : LocalizedStress T a) (u : ℝ) (n : E3) (b : Fin 4) :
    gravitationalAmplitude κ T u n 0 b =
      -∑ α : Fin 3, n α * gravitationalAmplitude κ T u n α.succ b :=
  gravitationalAmplitude_gauge hT u n b

example (hT : LocalizedStress T a) (u : ℝ) (n : E3) (i k : Fin 4) :
    gravitationalAmplitude κ T u n i k = gravitationalAmplitude κ T u n k i :=
  gravitationalAmplitude_symm hT u n i k

example (κ : ℝ) (T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (u : ℝ) :
    ℝ :=
  gravitationalPower κ T u

example (κ : ℝ) (q : (Fin 4 → Fin 4 → Fin 4 → ℝ) × E3) :
    ℝ :=
  fluxIntegrand κ q

example (κ : ℝ) :
    Continuous (fluxIntegrand κ) :=
  continuous_fluxIntegrand κ

example (κ : ℝ) (n : E3) (A : Matrix (Fin 4) (Fin 4) ℝ) :
    fluxIntegrand κ (fun c i k => Wave.waveCovector n c * A i k, n) =
      Wave.planeFlux n (traceReverse .timeNegative A) / κ :=
  fluxIntegrand_plane κ n A

example (hT : LocalizedStress T a) (R : ℝ) (x : Spacetime) (n : E3) :
    R ^ 2 * ∑ α : Fin 3, quadraticPseudotensor (metricPerturbation κ T) x 0 α.succ / κ * n α =
      fluxIntegrand κ (fun c i k => R * fderiv ℝ (fun z => retardedPerturbation κ T z i k) x
        (Pi.single c 1), n) :=
  fluxIntegrand_mul hT R x n

example {n : E3} (hn : n ∈ sphere (0 : E3) 1) (c : Fin 4) :
    |Wave.waveCovector n c| ≤ 1 :=
  abs_waveCovector_le hn c

example (hT : LocalizedStress T a) (u : ℝ) :
    Tendsto (fun R => sphereFlux
        (fun α v => quadraticPseudotensor (metricPerturbation κ T) v 0 α.succ / κ) (u + R) R)
      atTop (𝓝 (gravitationalPower κ T u)) :=
  tendsto_pseudotensorFlux hT u

example (hT : LocalizedStress T a) (α β : Fin 3) (s : ℝ) :
    deriv (deriv (deriv fun s => secondMoment T s α β)) s =
      2 * ∫ y : E3, fderiv ℝ (fun w => T w α.succ β.succ) (vector s y) (Pi.single 0 1) :=
  deriv_deriv_deriv_secondMoment hT α β s

example (hT : LocalizedStress T a) (ε : ℝ) (α β : Fin 3) (p : ℝ × E3) :
    Wave.timeDeriv (splitStress (slowStress ε T) α.succ β.succ) p =
      ε ^ 3 * fderiv ℝ (fun w => T w α.succ β.succ) (vector (ε * p.1) p.2) (Pi.single 0 1) :=
  timeDeriv_splitStress_slow hT ε α β p

example (hT : LocalizedStress T a) (ε u : ℝ) (n : E3) (α β : Fin 3) :
    gravitationalAmplitude κ (slowStress ε T) u n α.succ β.succ =
      2 * κ * (4 * π)⁻¹ * ε ^ 3 * ∫ y : E3,
        fderiv ℝ (fun w => T w α.succ β.succ) (vector (ε * u + ε * inner ℝ n y) y)
          (Pi.single 0 1) :=
  gravitationalAmplitude_slow hT ε u n α β

example (κ ε : ℝ) :
    (2 * κ * (4 * π)⁻¹ * ε ^ 3) ^ 2 / (4 * κ) = κ * ε ^ 6 / (16 * π ^ 2) :=
  slow_coefficient κ ε

example (hT : LocalizedStress T a) {M₁ M₂ : ℝ}
    (hM₁ : ∀ (α β : Fin 3) (v : Spacetime),
      |fderiv ℝ (fun w => T w α.succ β.succ) v (Pi.single 0 1)| ≤ M₁)
    (hM₂ : ∀ (α β : Fin 3) (v : Spacetime), |fderiv ℝ (fun w =>
      fderiv ℝ (fun w => T w α.succ β.succ) w (Pi.single 0 1)) v (Pi.single 0 1)| ≤ M₂)
    {ε : ℝ} (hε : 0 ≤ ε) (u : ℝ) :
    |gravitationalPower κ (slowStress ε T) u - κ * ε ^ 6 / (360 * π) *
        ∑ α, ∑ β, Wave.quadrupoleOf
          (fun α β => deriv (deriv (deriv fun s => secondMoment T s α β)) (ε * u)) α β ^ 2| ≤
      120 * π * |κ| * M₁ * M₂ * a ^ 7 * ε ^ 7 :=
  gravitationalPower_slow hT hM₁ hM₂ hε u

example (hT : LocalizedStress T a) {M₁ M₂ : ℝ}
    (hM₁ : ∀ (α β : Fin 3) (v : Spacetime),
      |fderiv ℝ (fun w => T w α.succ β.succ) v (Pi.single 0 1)| ≤ M₁)
    (hM₂ : ∀ (α β : Fin 3) (v : Spacetime), |fderiv ℝ (fun w =>
      fderiv ℝ (fun w => T w α.succ β.succ) w (Pi.single 0 1)) v (Pi.single 0 1)| ≤ M₂)
    {ε : ℝ} (hε : 0 ≤ ε) (u : ℝ) :
    ∃ P, Tendsto (fun R => sphereFlux (fun α v =>
        quadraticPseudotensor (metricPerturbation κ (slowStress ε T)) v 0 α.succ / κ) (u + R) R)
      atTop (𝓝 P) ∧
      |P - κ * ε ^ 6 / (360 * π) * ∑ α, ∑ β, Wave.quadrupoleOf
          (fun α β => deriv (deriv (deriv fun s => secondMoment T s α β)) (ε * u)) α β ^ 2| ≤
        120 * π * |κ| * M₁ * M₂ * a ^ 7 * ε ^ 7 :=
  tendsto_pseudotensorFlux_slow hT hM₁ hM₂ hε u

example (a Ω t : ℝ) :
    Fin 3 → ℝ :=
  binaryOrbit a Ω t

example (μ a Ω t : ℝ) (α β : Fin 3) :
    ℝ :=
  binaryMoment μ a Ω t α β

example {f f₁ f₂ f₃ : ℝ → ℝ} (h₁ : ∀ t, HasDerivAt f (f₁ t) t) (h₂ : ∀ t, HasDerivAt f₁ (f₂ t) t)
    (h₃ : ∀ t, HasDerivAt f₂ (f₃ t) t) (t : ℝ) :
    deriv (deriv (deriv f)) t = f₃ t :=
  deriv_deriv_deriv_of_hasDerivAt h₁ h₂ h₃ t

example (μ a Ω t : ℝ) :
    ∑ α, ∑ β, Wave.quadrupoleOf
      (fun α β => deriv (deriv (deriv fun t => binaryMoment μ a Ω t α β)) t) α β ^ 2 =
        288 * μ ^ 2 * a ^ 4 * Ω ^ 6 :=
  sum_sq_quadrupoleOf_binary μ a Ω t

example (κ μ a Ω t : ℝ) :
    κ / (360 * π) * ∑ α, ∑ β, Wave.quadrupoleOf
      (fun α β => deriv (deriv (deriv fun t => binaryMoment μ a Ω t α β)) t) α β ^ 2 =
        32 / 5 * (κ / (8 * π)) * μ ^ 2 * a ^ 4 * Ω ^ 6 :=
  binary_power κ μ a Ω t

example {a : ℝ} (ha : 0 ≤ a) :
    LocalizedStress (fun _ => (0 : Matrix (Fin 4) (Fin 4) ℝ)) a :=
  localizedStress_zero ha

example (γ : Fin 3) (f : E3 → ℝ) (x : E3) :
    ℝ :=
  spacePartial γ f x

example {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (γ : Fin 3) :
    ContDiff ℝ ∞ (spacePartial γ f) :=
  contDiff_spacePartial hf γ

example {f : E3 → ℝ} {r : ℝ} (hf : ∀ x, r < ‖x‖ → f x = 0) (γ : Fin 3) {x : E3} (hx : r < ‖x‖) :
    spacePartial γ f x = 0 :=
  spacePartial_eq_zero hf γ hx

example {f : E3 → ℝ} (hf : ContDiff ℝ 2 f) (γ δ : Fin 3) (x : E3) :
    spacePartial γ (spacePartial δ f) x = spacePartial δ (spacePartial γ f) x :=
  spacePartial_comm hf γ δ x

example (γ : Fin 3) :
    space (Pi.single γ.succ 1 : Spacetime) = EuclideanSpace.single γ 1 :=
  space_single_succ γ

example {q : ℝ → ℝ} {g : E3 → ℝ} (hq : Differentiable ℝ q) (hg : Differentiable ℝ g)
    (z : Spacetime) :
    fderiv ℝ (fun w : Spacetime => q (w 0) * g (space w)) z (Pi.single 0 1) =
      deriv q (z 0) * g (space z) :=
  fderiv_time_mul_space_zero hq hg z

example {q : ℝ → ℝ} {g : E3 → ℝ} (hq : Differentiable ℝ q) (hg : Differentiable ℝ g)
    (z : Spacetime) (γ : Fin 3) :
    fderiv ℝ (fun w : Spacetime => q (w 0) * g (space w)) z (Pi.single γ.succ 1) =
      q (z 0) * spacePartial γ g (space z) :=
  fderiv_time_mul_space_succ hq hg z γ

example {ι : Type*} (s : Finset ι) {F : ι → Spacetime → ℝ} {z : Spacetime}
    (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) z) (v : Spacetime) :
    fderiv ℝ (fun w => ∑ i ∈ s, F i w) z v = ∑ i ∈ s, fderiv ℝ (F i) z v :=
  fderiv_finsetSum_apply s hF v

example (Q : Fin 3 → Fin 3 → ℝ → ℝ) (χ : E3 → ℝ) (v : Spacetime) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  quadrupoleSource Q χ v

section QuadrupoleSource

variable {Q : Fin 3 → Fin 3 → ℝ → ℝ} {χ : E3 → ℝ}

example (v : Spacetime) :
    quadrupoleSource Q χ v 0 0 = ∑ p : Fin 3 × Fin 3, Q p.1 p.2 (v 0) *
      spacePartial p.1 (spacePartial p.2 χ) (space v) :=
  quadrupoleSource_zero_zero v

example (v : Spacetime) (δ : Fin 3) :
    quadrupoleSource Q χ v 0 δ.succ = ∑ α, deriv (Q α δ) (v 0) * spacePartial α χ (space v) :=
  quadrupoleSource_zero_succ v δ

example (v : Spacetime) (γ : Fin 3) :
    quadrupoleSource Q χ v γ.succ 0 = ∑ α, deriv (Q α γ) (v 0) * spacePartial α χ (space v) :=
  quadrupoleSource_succ_zero v γ

example (v : Spacetime) (γ δ : Fin 3) :
    quadrupoleSource Q χ v γ.succ δ.succ = deriv (deriv (Q γ δ)) (v 0) * χ (space v) :=
  quadrupoleSource_succ_succ v γ δ

example (hQ : ∀ γ δ, ContDiff ℝ ∞ (Q γ δ)) (hQs : ∀ γ δ, Q γ δ = Q δ γ) (hχ : ContDiff ℝ ∞ χ)
    {r : ℝ} (hr : 0 ≤ r) (hχs : ∀ x, r < ‖x‖ → χ x = 0) :
    LocalizedStress (quadrupoleSource Q χ) r :=
  localizedStress_quadrupoleSource hQ hQs hχ hr hχs

example {f w : E3 → ℝ} {r : ℝ} (hf : ContDiff ℝ 1 f) (hfs : ∀ x, r < ‖x‖ → f x = 0)
    (hw : ContDiff ℝ 1 w) (γ : Fin 3) :
    ∫ y, spacePartial γ f y * w y = -∫ y, f y * spacePartial γ w y :=
  integral_spacePartial_mul hf hfs hw γ

example (γ δ : Fin 3) (y : E3) :
    spacePartial γ (fun y : E3 => y δ) y = if δ = γ then 1 else 0 :=
  spacePartial_coord γ δ y

example (γ α β : Fin 3) (y : E3) :
    spacePartial γ (fun y : E3 => y α * y β) y =
      (if α = γ then 1 else 0) * y β + y α * (if β = γ then 1 else 0) :=
  spacePartial_coord_mul γ α β y

example (hQs : ∀ γ δ, Q γ δ = Q δ γ) (hχ : ContDiff ℝ ∞ χ) {r : ℝ} (hχs : ∀ x, r < ‖x‖ → χ x = 0)
    (s : ℝ) (α β : Fin 3) :
    secondMoment (quadrupoleSource Q χ) s α β = 2 * Q α β s * ∫ y, χ y :=
  secondMoment_quadrupoleSource hQs hχ hχs s α β

end QuadrupoleSource

example (A B C t : ℝ) :
    ℝ :=
  trigMode A B C t

example (A B C t : ℝ) :
    HasDerivAt (trigMode A B C) (trigMode 0 (2 * C) (-(2 * B)) t) t :=
  hasDerivAt_trigMode A B C t

example (A B C : ℝ) :
    deriv (trigMode A B C) = trigMode 0 (2 * C) (-(2 * B)) :=
  deriv_trigMode A B C

example (A B C : ℝ) :
    ContDiff ℝ ∞ (trigMode A B C) :=
  contDiff_trigMode A B C

example (B C t : ℝ) :
    |trigMode 0 B C t| ≤ |B| + |C| :=
  abs_trigMode_le B C t

example :
    Fin 3 → Fin 3 → ℝ :=
  binaryA

example :
    Fin 3 → Fin 3 → ℝ :=
  binaryB

example :
    Fin 3 → Fin 3 → ℝ :=
  binaryC

example (μ a s : ℝ) (α β : Fin 3) :
    binaryMoment μ a 1 s α β = μ * a ^ 2 / 2 * trigMode (binaryA α β) (binaryB α β)
      (binaryC α β) s :=
  binaryMoment_eq μ a s α β

example (γ δ : Fin 3) :
    binaryA γ δ = binaryA δ γ :=
  binaryA_symm γ δ

example (γ δ : Fin 3) :
    binaryB γ δ = binaryB δ γ :=
  binaryB_symm γ δ

example (γ δ : Fin 3) :
    binaryC γ δ = binaryC δ γ :=
  binaryC_symm γ δ

example (γ δ : Fin 3) :
    |binaryB γ δ| ≤ 1 :=
  abs_binaryB_le γ δ

example (γ δ : Fin 3) :
    |binaryC γ δ| ≤ 1 :=
  abs_binaryC_le γ δ

example :
    ℝ :=
  bumpMass

example :
    0 < bumpMass :=
  bumpMass_pos

example (μ a : ℝ) :
    ℝ :=
  binaryCoeff μ a

example (μ a : ℝ) :
    Spacetime → Matrix (Fin 4) (Fin 4) ℝ :=
  binarySource μ a

example (x : E3) (hx : 2 < ‖x‖) :
    Wave.spaceBump x = 0 :=
  spaceBump_eq_zero x hx

example (μ a : ℝ) :
    LocalizedStress (binarySource μ a) 2 :=
  localizedStress_binarySource μ a

example (μ a s : ℝ) (α β : Fin 3) :
    secondMoment (binarySource μ a) s α β = binaryMoment μ a 1 s α β :=
  secondMoment_binarySource μ a s α β

example (ε s : ℝ) (α β : Fin 3) :
    secondMoment (slowStress ε T) s α β = secondMoment T (ε * s) α β :=
  secondMoment_slowStress ε s α β

example (μ a Ω s : ℝ) (α β : Fin 3) :
    secondMoment (slowStress Ω (binarySource μ a)) s α β = binaryMoment μ a Ω s α β :=
  secondMoment_slowStress_binarySource μ a Ω s α β

example (μ a : ℝ) (α β : Fin 3) (v : Spacetime) :
    |fderiv ℝ (fun w => binarySource μ a w α.succ β.succ) v (Pi.single 0 1)| ≤
        16 * |binaryCoeff μ a| ∧
      |fderiv ℝ (fun w => fderiv ℝ (fun w => binarySource μ a w α.succ β.succ) w
        (Pi.single 0 1)) v (Pi.single 0 1)| ≤ 32 * |binaryCoeff μ a| :=
  binarySource_bounds μ a α β v

example (κ μ a u : ℝ) :
    ∃ C, ∀ Ω : ℝ, 0 ≤ Ω →
    ∃ P, Tendsto (fun R => sphereFlux (fun α v => quadraticPseudotensor
        (metricPerturbation κ (slowStress Ω (binarySource μ a))) v 0 α.succ / κ) (u + R) R)
      atTop (𝓝 P) ∧
      |P - 32 / 5 * (κ / (8 * π)) * μ ^ 2 * a ^ 4 * Ω ^ 6| ≤ C * Ω ^ 7 :=
  binary_power_smooth κ μ a u

end ProjectAinos.GeneralRelativity.LinearizedRadiation

end LinearizedRadiation
