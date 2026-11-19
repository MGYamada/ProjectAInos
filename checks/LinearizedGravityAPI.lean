/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Lorentzian.Linearized
import ProjectAinos.GeneralRelativity.WeakWaves
import ProjectAinos.GeneralRelativity.ExactPlaneWave

/-! Public consumers of gravitational waves (Landau–Lifshitz §§107, 109): the linearized
Christoffel symbols, Ricci and Einstein tensors of `η + εh` as derivatives of an actual family of
Lorentz metrics, their gauge invariance and the harmonic gauge; plane waves, their gauge
transformations and the two polarizations of a nonzero null covector; and the exact plane waves of
diagonal Rosen form with their vacuum equation, a non-flat strong wave and a residual that is
not of first order. Default elaborator options are intentional: these checks must not rely on the
implementation's transparency settings. Every statement is pinned with its type. -/

noncomputable section

section Linearized

open Set TopologicalSpace

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

namespace CoordinateMetric

section SecondPartial

variable {f g : MinkowskiModel d → ℝ} {x : MinkowskiModel d}

example (f : MinkowskiModel d → ℝ) (x : MinkowskiModel d) (a b : Fin (d + 1)) :
    ℝ :=
  secondPartial f x a b

example (hf : ContDiffAt ℝ ∞ f x) (v : MinkowskiModel d) :
    ContDiffAt ℝ ∞ (fun z => fderiv ℝ f z v) x :=
  contDiffAt_fderiv_apply hf v

example (hf : ContDiffAt ℝ ∞ f x) :
    ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ f z :=
  eventually_differentiableAt hf

example (hf : ContDiffAt ℝ ∞ f x) (v : MinkowskiModel d) :
    DifferentiableAt ℝ (fun z => fderiv ℝ f z v) x :=
  differentiableAt_partial hf v

example {ι : Type} (s : Finset ι) {F : ι → MinkowskiModel d → ℝ}
    (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) x) (c : ι → ℝ) (v : MinkowskiModel d) :
    fderiv ℝ (fun z => ∑ i ∈ s, c i * F i z) x v = ∑ i ∈ s, c i * fderiv ℝ (F i) x v :=
  fderiv_sum_mul_apply s hF c v

example (hfg : f =ᶠ[𝓝 x] g) (a b : Fin (d + 1)) :
    secondPartial f x a b = secondPartial g x a b :=
  secondPartial_congr hfg a b

example (c : ℝ) (a b : Fin (d + 1)) :
    secondPartial (fun _ => c) x a b = 0 :=
  secondPartial_const c a b

example (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (a b : Fin (d + 1)) :
    secondPartial (fun z => f z + g z) x a b = secondPartial f x a b + secondPartial g x a b :=
  secondPartial_add hf hg a b

example (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (a b : Fin (d + 1)) :
    secondPartial (fun z => f z - g z) x a b = secondPartial f x a b - secondPartial g x a b :=
  secondPartial_sub hf hg a b

example (hf : ContDiffAt ℝ ∞ f x) (c : ℝ) (a b : Fin (d + 1)) :
    secondPartial (fun z => c * f z) x a b = c * secondPartial f x a b :=
  secondPartial_const_mul hf c a b

example {ι : Type} (s : Finset ι) {F : ι → MinkowskiModel d → ℝ}
    (hF : ∀ i ∈ s, ContDiffAt ℝ ∞ (F i) x) (c : ι → ℝ) (a b : Fin (d + 1)) :
    secondPartial (fun z => ∑ i ∈ s, c i * F i z) x a b =
      ∑ i ∈ s, c i * secondPartial (F i) x a b :=
  secondPartial_sum_mul s hF c a b

example (hf : ContDiffAt ℝ 2 f x) (a b : Fin (d + 1)) :
    secondPartial f x a b = secondPartial f x b a :=
  secondPartial_comm hf a b

example (hf : ContDiffAt ℝ ∞ f x) (a b c : Fin (d + 1)) :
    secondPartial (fun z => fderiv ℝ f z (Pi.single c 1)) x a b =
      secondPartial (fun z => fderiv ℝ f z (Pi.single b 1)) x a c :=
  secondPartial_fderiv_swap hf a b c

end SecondPartial

section Flat

example (i j : Fin (d + 1)) :
    Minkowski.metricMatrix σ d i j = if i = j then lorentzSign σ i else 0 :=
  metricMatrix_apply i j

example :
    (Minkowski.metricMatrix σ d)⁻¹ = Minkowski.metricMatrix σ d :=
  metricMatrix_inv

example (X : Fin (d + 1) → ℝ) (k : Fin (d + 1)) :
    ∑ l, Minkowski.metricMatrix σ d k l * X l = lorentzSign σ k * X k :=
  sum_metricMatrix_mul X k

example (X : Fin (d + 1) → ℝ) (b : Fin (d + 1)) :
    ∑ a, lorentzSign σ a * (Minkowski.metricMatrix σ d a b * X a) = X b :=
  sum_lorentzSign_mul_metricMatrix X b

end Flat

section Christoffel

variable {h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}

example (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (p : ℝ × MinkowskiModel d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  linearFamily σ h p

example (p : ℝ × MinkowskiModel d) (i j : Fin (d + 1)) :
    linearFamily σ h p i j = Minkowski.metricMatrix σ d i j + p.1 * h p.2 i j :=
  linearFamily_apply p i j

example (z : MinkowskiModel d) :
    linearFamily σ h (0, z) = Minkowski.metricMatrix σ d :=
  linearFamily_zero z

example (hh : ∀ i j, ContDiffAt ℝ ∞ (fun z => h z i j) x) (ε : ℝ) (i j : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (fun q => linearFamily σ h q i j) (ε, x) :=
  contDiffAt_linearFamily hh ε i j

example (z : MinkowskiModel d) :
    (linearFamily σ h (0, z)).det ≠ 0 :=
  linearFamily_det_zero z

example (z : MinkowskiModel d) (k i j : Fin (d + 1)) :
    familyChristoffel (linearFamily σ h) (0, z) k i j = 0 :=
  familyChristoffel_linearFamily_zero z k i j

example (z : MinkowskiModel d) (j k : Fin (d + 1)) :
    familyRicci (linearFamily σ h) (0, z) j k = 0 :=
  familyRicci_linearFamily_zero z j k

example (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (k i j : Fin (d + 1)) :
    ℝ :=
  linearizedChristoffel σ h x k i j

example (hh : ∀ i j, ContDiffAt ℝ ∞ (fun z => h z i j) x) (k i j : Fin (d + 1)) :
    HasDerivAt (fun ε => familyChristoffel (linearFamily σ h) (ε, x) k i j)
      (linearizedChristoffel σ h x k i j) 0 :=
  hasDerivAt_christoffelOf_linear hh k i j

end Christoffel

section Ricci

variable {h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}

example (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (j k : Fin (d + 1)) :
    ℝ :=
  linearizedRicci σ h x j k

example (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d) :
    ℝ :=
  linearizedScalar σ h x

example (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (j k : Fin (d + 1)) :
    ℝ :=
  linearizedEinstein σ h x j k

example {P Q R : MinkowskiModel d → ℝ} (hP : DifferentiableAt ℝ P x) (hQ : DifferentiableAt ℝ Q x)
    (hR : DifferentiableAt ℝ R x) (c : ℝ) (v : MinkowskiModel d) :
    fderiv ℝ (fun z => c * (P z + Q z - R z) / 2) x v =
      c * (fderiv ℝ P x v + fderiv ℝ Q x v - fderiv ℝ R x v) / 2 :=
  fderiv_christoffelForm hP hQ hR c v

example {U : Opens (MinkowskiModel d)} (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) (hx : x ∈ U) (j k : Fin (d + 1)) :
    linearizedRicci σ h x j k = ∑ i,
      (fderiv ℝ (fun z => linearizedChristoffel σ h z i j k) x (Pi.single i 1) -
        fderiv ℝ (fun z => linearizedChristoffel σ h z i i k) x (Pi.single j 1)) :=
  linearizedRicci_eq_christoffel hh hs hx j k

example {U : Opens (MinkowskiModel d)} (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) (hx : x ∈ U) (j k : Fin (d + 1)) :
    familyRicciDeriv (linearFamily σ h) x j k = linearizedRicci σ h x j k :=
  familyRicciDeriv_linearFamily hh hs hx j k

example {U : Opens (MinkowskiModel d)} (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) (hx : x ∈ U) (j k : Fin (d + 1)) :
    HasDerivAt (fun ε : ℝ => ricciOf (fun z => Minkowski.metricMatrix σ d + ε • h z) x j k)
      (linearizedRicci σ h x j k) 0 :=
  hasDerivAt_ricciOf_linear hh hs hx j k

example {U : Opens (MinkowskiModel d)} (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) (hx : x ∈ U) :
    HasDerivAt (fun ε : ℝ => scalarOf (fun z => Minkowski.metricMatrix σ d + ε • h z) x)
      (linearizedScalar σ h x) 0 :=
  hasDerivAt_scalarOf_linear hh hs hx

example {U : Opens (MinkowskiModel d)} (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) (hx : x ∈ U) (j k : Fin (d + 1)) :
    HasDerivAt (fun ε : ℝ => einsteinOf (fun z => Minkowski.metricMatrix σ d + ε • h z) x j k)
      (linearizedEinstein σ h x j k) 0 :=
  hasDerivAt_einsteinOf_linear hh hs hx j k

end Ricci

section Metric

variable {U : Opens (MinkowskiModel d)}
  {h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}

example (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) {M : ℝ} (hM : ∀ z ∈ U, ∀ i j, |h z i j| ≤ M)
    {ε : ℝ} (hε : |ε| * (((d : ℝ) + 1) ^ 2 * M) < 1) :
    (minkowski σ d U).IsAdmissible (coefficientForm h) ε :=
  isAdmissible_linear σ hs hM hε

example (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) {M : ℝ} (hM : ∀ z ∈ U, ∀ i j, |h z i j| ≤ M) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), (minkowski σ d U).IsAdmissible (coefficientForm h) ε :=
  eventually_isAdmissible_linear σ hs hM

example (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) (ε : ℝ)
    (hε : (minkowski σ d U).IsAdmissible (coefficientForm h) ε) :
    CoordinateMetric σ d U :=
  linearMetric σ hh ε hε

example (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) (ε : ℝ)
    (hε : (minkowski σ d U).IsAdmissible (coefficientForm h) ε) :
    (linearMetric σ hh ε hε).coefficient = fun z => Minkowski.metricMatrix σ d + ε • h z :=
  coefficient_linearMetric hh ε hε

open Classical in

example (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) (ε : ℝ) :
    CoordinateMetric σ d U :=
  linearMetricFamily σ hh ε

example (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i)
    {M : ℝ} (hM : ∀ z ∈ U, ∀ i j, |h z i j| ≤ M) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), (linearMetricFamily σ hh ε).coefficient =
      fun z => Minkowski.metricMatrix σ d + ε • h z :=
  eventually_coefficient_linearMetricFamily hh hs hM

example (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i)
    {M : ℝ} (hM : ∀ z ∈ U, ∀ i j, |h z i j| ≤ M) (x : U) (j k : Fin (d + 1)) :
    HasDerivAt (fun ε => (linearMetricFamily σ hh ε).toLorentzMetric.ricci x
        (chartField (physicalChart x) (Pi.single j 1) x)
        (chartField (physicalChart x) (Pi.single k 1) x))
      (linearizedRicci σ h x j k) 0 :=
  hasDerivAt_ricci_linearMetricFamily hh hs hM x j k

example (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i)
    {M : ℝ} (hM : ∀ z ∈ U, ∀ i j, |h z i j| ≤ M) (x : U) (j k : Fin (d + 1)) :
    HasDerivAt (fun ε => (linearMetricFamily σ hh ε).toLorentzMetric.einstein x
        (chartField (physicalChart x) (Pi.single j 1) x)
        (chartField (physicalChart x) (Pi.single k 1) x))
      (linearizedEinstein σ h x j k) 0 :=
  hasDerivAt_einstein_linearMetricFamily hh hs hM x j k

end Metric

section Gauge

variable {h h' : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}

example (ξ : MinkowskiModel d → MinkowskiModel d) (y : MinkowskiModel d) (i j : Fin (d + 1)) :
    lieOf (fun _ => Minkowski.metricMatrix σ d) ξ y i j =
      lorentzSign σ j * fderiv ℝ (fun z => ξ z j) y (Pi.single i 1) +
        lorentzSign σ i * fderiv ℝ (fun z => ξ z i) y (Pi.single j 1) :=
  lieOf_metricMatrix ξ y i j

example (hh : ∀ i j, ContDiffAt ℝ ∞ (fun z => h z i j) x)
    (hh' : ∀ i j, ContDiffAt ℝ ∞ (fun z => h' z i j) x) (j k : Fin (d + 1)) :
    linearizedRicci σ (fun z => h z + h' z) x j k =
      linearizedRicci σ h x j k + linearizedRicci σ h' x j k :=
  linearizedRicci_add hh hh' j k

example {ξ : MinkowskiModel d → MinkowskiModel d} (hξ : ∀ m, ContDiffAt ℝ ∞ (fun z => ξ z m) x)
    (j k : Fin (d + 1)) :
    linearizedRicci σ (fun z => Matrix.of (lieOf (fun _ => Minkowski.metricMatrix σ d) ξ z)) x
      j k = 0 :=
  linearizedRicci_lie hξ j k

example {U : Opens (MinkowskiModel d)} (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    {ξ : MinkowskiModel d → MinkowskiModel d} (hξ : ContDiffOn ℝ ∞ ξ U) (hx : x ∈ U)
    (j k : Fin (d + 1)) :
    linearizedRicci σ
        (fun z => h z + Matrix.of (lieOf (fun _ => Minkowski.metricMatrix σ d) ξ z)) x j k =
      linearizedRicci σ h x j k :=
  linearizedRicci_add_lie hh hξ hx j k

example {U : Opens (MinkowskiModel d)} (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    {ξ : MinkowskiModel d → MinkowskiModel d} (hξ : ContDiffOn ℝ ∞ ξ U) (hx : x ∈ U)
    (j k : Fin (d + 1)) :
    linearizedEinstein σ
        (fun z => h z + Matrix.of (lieOf (fun _ => Minkowski.metricMatrix σ d) ξ z)) x j k =
      linearizedEinstein σ h x j k :=
  linearizedEinstein_add_lie hh hξ hx j k

end Gauge

section Harmonic

variable {h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}

example (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    ℝ :=
  flatTrace σ A

example (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  traceReverse σ A

example (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (a b : Fin (d + 1)) :
    traceReverse σ A a b = A a b - flatTrace σ A / 2 * Minkowski.metricMatrix σ d a b :=
  traceReverse_apply A a b

example (A B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    flatTrace σ (A + B) = flatTrace σ A + flatTrace σ B :=
  flatTrace_add A B

example (c : ℝ) (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    flatTrace σ (c • A) = c * flatTrace σ A :=
  flatTrace_smul c A

example (A B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    traceReverse σ (A + B) = traceReverse σ A + traceReverse σ B :=
  traceReverse_add A B

example (c : ℝ) (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    traceReverse σ (c • A) = c • traceReverse σ A :=
  traceReverse_smul c A

example (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    flatTrace σ (traceReverse σ A) = (1 - ((d : ℝ) + 1) / 2) * flatTrace σ A :=
  flatTrace_traceReverse A

example (A : Matrix (Fin 4) (Fin 4) ℝ) :
    traceReverse σ (traceReverse σ A) = A :=
  traceReverse_traceReverse A

example (f : MinkowskiModel d → ℝ) (x : MinkowskiModel d) :
    ℝ :=
  flatBox σ f x

example (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (U : Opens (MinkowskiModel d)) :
    Prop :=
  IsHarmonicGauge σ h U

example (U : Opens (MinkowskiModel d)) :
    IsHarmonicGauge σ (fun _ => 0) U :=
  isHarmonicGauge_zero U

example (hh : ∀ i j, ContDiffAt ℝ ∞ (fun z => h z i j) x) :
    ContDiffAt ℝ ∞ (fun z => flatTrace σ (h z)) x :=
  contDiffAt_flatTrace hh

example (hh : ∀ i j, ContDiffAt ℝ ∞ (fun z => h z i j) x) (a b : Fin (d + 1)) :
    secondPartial (fun z => flatTrace σ (h z)) x a b =
      ∑ c, lorentzSign σ c * secondPartial (fun z => h z c c) x a b :=
  secondPartial_flatTrace hh a b

example {U : Opens (MinkowskiModel d)} (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (hg : IsHarmonicGauge σ h U) {z : MinkowskiModel d} (hz : z ∈ U) (b : Fin (d + 1)) :
    ∑ a, lorentzSign σ a * fderiv ℝ (fun w => h w a b) z (Pi.single a 1) =
      1 / 2 * fderiv ℝ (fun w => flatTrace σ (h w)) z (Pi.single b 1) :=
  sum_fderiv_of_isHarmonicGauge hh hg hz b

example {U : Opens (MinkowskiModel d)} (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (hg : IsHarmonicGauge σ h U) (hx : x ∈ U) (j k : Fin (d + 1)) :
    ∑ i, lorentzSign σ i * secondPartial (fun z => h z i k) x i j =
      1 / 2 * secondPartial (fun z => flatTrace σ (h z)) x j k :=
  sum_secondPartial_of_isHarmonicGauge hh hg hx j k

example {U : Opens (MinkowskiModel d)} (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (hg : IsHarmonicGauge σ h U) (hx : x ∈ U) (j k : Fin (d + 1)) :
    linearizedRicci σ h x j k = -flatBox σ (fun z => h z j k) x / 2 :=
  linearizedRicci_of_isHarmonicGauge hh hg hx j k

example (hh : ∀ i j, ContDiffAt ℝ ∞ (fun z => h z i j) x) (j k : Fin (d + 1)) :
    flatBox σ (fun z => traceReverse σ (h z) j k) x = flatBox σ (fun z => h z j k) x -
      Minkowski.metricMatrix σ d j k / 2 *
        ∑ a, lorentzSign σ a * flatBox σ (fun z => h z a a) x :=
  flatBox_traceReverse hh j k

example {U : Opens (MinkowskiModel d)} (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (hg : IsHarmonicGauge σ h U) (hx : x ∈ U) (j k : Fin (d + 1)) :
    linearizedEinstein σ h x j k = -flatBox σ (fun z => traceReverse σ (h z) j k) x / 2 :=
  linearizedEinstein_of_isHarmonicGauge hh hg hx j k

end Harmonic

end CoordinateMetric

end ProjectAinos.SmoothGeometry

end Linearized

section WeakWaves

open Set TopologicalSpace Module

open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.WeakWaves

open SmoothGeometry CoordinateMetric

open LorentzMetric (chartField)

example :
    lorentzSign (d := 3) .timeNegative 0 = -1 :=
  lorentzSign_zero

example :
    lorentzSign (d := 3) .timeNegative 1 = 1 :=
  lorentzSign_one

example :
    lorentzSign (d := 3) .timeNegative 2 = 1 :=
  lorentzSign_two

example :
    lorentzSign (d := 3) .timeNegative 3 = 1 :=
  lorentzSign_three

example (k : Fin 4 → ℝ) (x : MinkowskiModel 3) :
    ℝ :=
  phase k x

example (k : Fin 4 → ℝ) :
    MinkowskiModel 3 →L[ℝ] ℝ :=
  phaseCLM k

example (k : Fin 4 → ℝ) (x : MinkowskiModel 3) :
    phaseCLM k x = phase k x :=
  phaseCLM_apply k x

example (k : Fin 4 → ℝ) :
    phase k = phaseCLM k :=
  phase_eq k

example (k : Fin 4 → ℝ) (b : Fin 4) :
    phase k (Pi.single b 1) = k b :=
  phase_single k b

example (k : Fin 4 → ℝ) :
    ContDiff ℝ ∞ (phase k) :=
  contDiff_phase k

example (k : Fin 4 → ℝ) (x v : MinkowskiModel 3) :
    fderiv ℝ (fun z => Real.cos (phase k z)) x v = -Real.sin (phase k x) * phase k v :=
  fderiv_cos_phase k x v

example (k : Fin 4 → ℝ) (x v : MinkowskiModel 3) :
    fderiv ℝ (fun z => Real.sin (phase k z)) x v = Real.cos (phase k x) * phase k v :=
  fderiv_sin_phase k x v

example (k : Fin 4 → ℝ) :
    Differentiable ℝ (fun z => Real.cos (phase k z)) :=
  differentiable_cos_phase k

example (k : Fin 4 → ℝ) :
    Differentiable ℝ (fun z => Real.sin (phase k z)) :=
  differentiable_sin_phase k

example (e : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) (x : MinkowskiModel 3) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  planeWave e k x

variable {e : Matrix (Fin 4) (Fin 4) ℝ} {k : Fin 4 → ℝ}

example (x : MinkowskiModel 3) (i j : Fin 4) :
    planeWave e k x i j = Real.cos (phase k x) * e i j :=
  planeWave_apply x i j

example (U : Set (MinkowskiModel 3)) (i j : Fin 4) :
    ContDiffOn ℝ ∞ (fun z => planeWave e k z i j) U :=
  contDiffOn_planeWave U i j

example (x v : MinkowskiModel 3) (i j : Fin 4) :
    fderiv ℝ (fun z => planeWave e k z i j) x v = -Real.sin (phase k x) * phase k v * e i j :=
  fderiv_planeWave x v i j

example (x : MinkowskiModel 3) (a b i j : Fin 4) :
    secondPartial (fun z => planeWave e k z i j) x a b =
      -(Real.cos (phase k x) * k a * k b * e i j) :=
  secondPartial_planeWave x a b i j

example (x : MinkowskiModel 3) (i j : Fin 4) :
    flatBox .timeNegative (fun z => planeWave e k z i j) x =
      -(∑ a, lorentzSign .timeNegative a * k a ^ 2) * (Real.cos (phase k x) * e i j) :=
  flatBox_planeWave x i j

example (k : Fin 4 → ℝ) :
    Prop :=
  IsNull k

example (hk : IsNull k) (x : MinkowskiModel 3) (i j : Fin 4) :
    flatBox .timeNegative (fun z => planeWave e k z i j) x = 0 :=
  flatBox_planeWave_of_isNull hk x i j

example (x : MinkowskiModel 3) :
    traceReverse .timeNegative (planeWave e k x) =
      Real.cos (phase k x) • traceReverse .timeNegative e :=
  traceReverse_planeWave x

example (x : MinkowskiModel 3) (a b : Fin 4) :
    fderiv ℝ (fun z => traceReverse .timeNegative (planeWave e k z) a b) x (Pi.single a 1) =
      -Real.sin (phase k x) * k a * traceReverse .timeNegative e a b :=
  fderiv_traceReverse_planeWave x a b

example :
    IsHarmonicGauge .timeNegative (planeWave e k) ⊤ ↔
      ∀ b, ∑ a, lorentzSign .timeNegative a * k a * traceReverse .timeNegative e a b = 0 :=
  isHarmonicGauge_planeWave_iff

example (hk : IsNull k)
    (he : ∀ b, ∑ a, lorentzSign .timeNegative a * k a * traceReverse .timeNegative e a b = 0)
    (x : MinkowskiModel 3) (j l : Fin 4) :
    linearizedRicci .timeNegative (planeWave e k) x j l = 0 :=
  linearizedRicci_planeWave hk he x j l

example (hk : IsNull k)
    (he : ∀ b, ∑ a, lorentzSign .timeNegative a * k a * traceReverse .timeNegative e a b = 0)
    (x : MinkowskiModel 3) (j l : Fin 4) :
    linearizedEinstein .timeNegative (planeWave e k) x j l = 0 :=
  linearizedEinstein_planeWave hk he x j l

example (x : MinkowskiModel 3) (i j : Fin 4) :
    |planeWave e k x i j| ≤ ∑ a, ∑ c, |e a c| :=
  abs_planeWave_le x i j

example (hsymm : e.IsSymm) (hk : IsNull k)
    (he : ∀ b, ∑ a, lorentzSign .timeNegative a * k a * traceReverse .timeNegative e a b = 0)
    (x : (⊤ : Opens (MinkowskiModel 3))) (j l : Fin 4) :
    HasDerivAt (fun ε => (linearMetricFamily .timeNegative
        (fun i j => contDiffOn_planeWave (e := e) (k := k) _ i j) ε).toLorentzMetric.ricci x
        (chartField (physicalChart x) (Pi.single j 1) x)
        (chartField (physicalChart x) (Pi.single l 1) x)) 0 0 :=
  hasDerivAt_ricci_planeWave hsymm hk he x j l

example (k ζ : Fin 4 → ℝ) (x : MinkowskiModel 3) :
    MinkowskiModel 3 :=
  gaugeVector k ζ x

example (k ζ : Fin 4 → ℝ) :
    ContDiff ℝ ∞ (gaugeVector k ζ) :=
  contDiff_gaugeVector k ζ

example (k : Fin 4 → ℝ) :
    (Fin 4 → ℝ) →ₗ[ℝ] Matrix (Fin 4) (Fin 4) ℝ :=
  gaugeMap k

example (ζ : Fin 4 → ℝ) (i j : Fin 4) :
    gaugeMap k ζ i j = k i * ζ j + ζ i * k j :=
  gaugeMap_apply ζ i j

example (ζ : Fin 4 → ℝ) (x : MinkowskiModel 3) :
    Matrix.of (lieOf (fun _ => Minkowski.metricMatrix .timeNegative 3) (gaugeVector k ζ) x) =
      planeWave (gaugeMap k ζ) k x :=
  lieOf_gaugeVector ζ x

example (ζ : Fin 4 → ℝ) (x : MinkowskiModel 3) (j l : Fin 4) :
    linearizedRicci .timeNegative (planeWave (e + gaugeMap k ζ) k) x j l =
      linearizedRicci .timeNegative (planeWave e k) x j l :=
  linearizedRicci_planeWave_add_gauge ζ x j l

example :
    Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ) :=
  symmetricMatrices

example :
    e ∈ symmetricMatrices ↔ e.IsSymm :=
  mem_symmetricMatrices

example :
    Type :=
  UpperIndex

example :
    symmetricMatrices ≃ₗ[ℝ] (UpperIndex → ℝ) :=
  symmetricEquiv

example :
    finrank ℝ symmetricMatrices = 10 :=
  finrank_symmetricMatrices

example (k : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ →ₗ[ℝ] (Fin 4 → ℝ) :=
  harmonicMap k

example (b : Fin 4) :
    harmonicMap k e b =
      ∑ a, lorentzSign .timeNegative a * k a * traceReverse .timeNegative e a b :=
  harmonicMap_apply b

example (k : Fin 4 → ℝ) :
    Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ) :=
  polarizationSpace k

example :
    e ∈ polarizationSpace k ↔ e.IsSymm ∧
    ∀ b, ∑ a, lorentzSign .timeNegative a * k a * traceReverse .timeNegative e a b = 0 :=
  mem_polarizationSpace

example (k : Fin 4 → ℝ) :
    Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ) :=
  gaugeSpace k

example (hk : IsNull k) :
    gaugeSpace k ≤ polarizationSpace k :=
  gaugeSpace_le_polarizationSpace hk

example (hk : k ≠ 0) :
    Function.Injective (gaugeMap k) :=
  gaugeMap_injective hk

example (hk : k ≠ 0) :
    finrank ℝ (gaugeSpace k) = 4 :=
  finrank_gaugeSpace hk

example (hk : k ≠ 0) (w : Fin 4 → ℝ) :
    ∃ e ∈ symmetricMatrices, harmonicMap k e = w :=
  exists_harmonicMap_eq hk w

example (hk : k ≠ 0) :
    finrank ℝ (polarizationSpace k) = 6 :=
  finrank_polarizationSpace hk

example (k : Fin 4 → ℝ) :
    Submodule ℝ (polarizationSpace k) :=
  gaugeIn k

example (hk : IsNull k) (hk0 : k ≠ 0) :
    finrank ℝ (polarizationSpace k ⧸ gaugeIn k) = 2 :=
  finrank_polarizationQuotient hk hk0

example (ν : ℝ) :
    Fin 4 → ℝ :=
  axialCovector ν

example (ν : ℝ) :
    IsNull (axialCovector ν) :=
  isNull_axialCovector ν

example {ν : ℝ} (hν : ν ≠ 0) :
    axialCovector ν ≠ 0 :=
  axialCovector_ne_zero hν

example :
    Matrix (Fin 4) (Fin 4) ℝ :=
  plusPolarization

example :
    Matrix (Fin 4) (Fin 4) ℝ :=
  crossPolarization

example (ν : ℝ) :
    plusPolarization ∈ polarizationSpace (axialCovector ν) :=
  plusPolarization_mem ν

example (ν : ℝ) :
    crossPolarization ∈ polarizationSpace (axialCovector ν) :=
  crossPolarization_mem ν

example (ν : ℝ) :
    Fin 2 → polarizationSpace (axialCovector ν) ⧸
    gaugeIn (axialCovector ν) :=
  polarizationClasses ν

example {ν : ℝ} :
    LinearIndependent ℝ (polarizationClasses ν) :=
  linearIndependent_polarizationClasses

example {ν : ℝ} (hν : ν ≠ 0) :
    Basis (Fin 2) ℝ (polarizationSpace (axialCovector ν) ⧸ gaugeIn (axialCovector ν)) :=
  polarizationBasis hν

example (ν : ℝ) (x : MinkowskiModel 3) (j l : Fin 4) :
    linearizedRicci .timeNegative (planeWave plusPolarization (axialCovector ν)) x j l = 0 :=
  linearizedRicci_plusWave ν x j l

example (ν : ℝ) :
    planeWave plusPolarization (axialCovector ν) 0 1 1 = 1 :=
  planeWave_plus_apply_zero ν

end ProjectAinos.GeneralRelativity.WeakWaves

end WeakWaves

section ExactPlaneWave

open ContinuousLinearMap Set TopologicalSpace Filter

open scoped ContDiff Topology Real

namespace ProjectAinos.GeneralRelativity.ExactPlaneWave

open SmoothGeometry CoordinateMetric

local notation "E" => MinkowskiModel 3

example (x : E) :
    ℝ :=
  retarded x

example :
    Continuous retarded :=
  continuous_retarded

example :
    ContDiff ℝ ∞ retarded :=
  contDiff_retarded

example (x : E) :
    HasFDerivAt retarded ((proj 0 : E →L[ℝ] ℝ) - proj 3) x :=
  hasFDerivAt_retarded x

example {f : ℝ → ℝ} {f' : ℝ} {x : E} (hf : HasDerivAt f f' (retarded x)) :
    HasFDerivAt (fun z : E => f (retarded z)) (f' • ((proj 0 : E →L[ℝ] ℝ) - proj 3)) x :=
  hasFDerivAt_comp_retarded hf

example (t : ℝ) :
    retarded (FLRW.timeAxis t) = t :=
  retarded_timeAxis t

example {J : Set ℝ} {f : ℝ → ℝ} (hJ : IsOpen J) (hf : ContDiffOn ℝ ∞ f J) {u : ℝ} (hu : u ∈ J) :
    HasDerivAt (deriv f) (deriv (deriv f) u) u :=
  hasDerivAt_deriv_of_contDiffOn hJ hf hu

example {J : Set ℝ} {f : ℝ → ℝ} (hJ : IsOpen J) (hf : ContDiffOn ℝ ∞ f J) {x : E}
    (hx : retarded x ∈ J) (v : E) :
    fderiv ℝ (fun z : E => f (retarded z) ^ 2) x v =
      2 * f (retarded x) * deriv f (retarded x) * (v 0 - v 3) :=
  fderiv_sq_retarded hJ hf hx v

example (f : ℝ → ℝ) (x : E) :
    ℝ :=
  sqGamma f x

example (f : ℝ → ℝ) (x : E) :
    ℝ :=
  logGamma f x

example {J : Set ℝ} {f : ℝ → ℝ} (hJ : IsOpen J) (hf : ContDiffOn ℝ ∞ f J) {x : E}
    (hx : retarded x ∈ J) (v : E) :
    fderiv ℝ (sqGamma f) x v =
      (deriv f (retarded x) ^ 2 + f (retarded x) * deriv (deriv f) (retarded x)) *
        (v 0 - v 3) :=
  fderiv_sqGamma hJ hf hx v

example {J : Set ℝ} {f : ℝ → ℝ} (hJ : IsOpen J) (hf : ContDiffOn ℝ ∞ f J) {x : E}
    (hx : retarded x ∈ J) (hf0 : f (retarded x) ≠ 0) (v : E) :
    fderiv ℝ (logGamma f) x v =
      (deriv (deriv f) (retarded x) * f (retarded x) - deriv f (retarded x) ^ 2) /
        f (retarded x) ^ 2 * (v 0 - v 3) :=
  fderiv_logGamma hJ hf hx hf0 v

variable {D : Data} {x : E}

example :
    Opens E :=
  domain D

example (hx : x ∈ domain D) :
    retarded x ∈ D.J :=
  retarded_mem hx

example (hx : x ∈ domain D) :
    0 < D.a (retarded x) :=
  a_pos_of_mem hx

example (hx : x ∈ domain D) :
    0 < D.b (retarded x) :=
  b_pos_of_mem hx

example {u : ℝ} (hu : u ∈ D.J) :
    FLRW.timeAxis u ∈ domain D :=
  timeAxis_mem hu

example (x : E) :
    Fin 4 → ℝ :=
  coefficients D x

example {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f D.J) :
    ContDiffOn ℝ ∞ (fun z : E => f (retarded z)) (domain D) :=
  contDiffOn_retarded hf

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
    Fin 4 → ℝ :=
  nullCovector

example (y : E) :
    ∑ i, nullCovector i ^ 2 / coefficients D y i = 0 :=
  nullCovector_isNull y

example (hx : x ∈ domain D) (i : Fin 4) (v : E) :
    fderiv ℝ (fun z => coefficients D z i) x v =
      ![0, 2 * D.a (retarded x) * deriv D.a (retarded x) * (v 0 - v 3),
        2 * D.b (retarded x) * deriv D.b (retarded x) * (v 0 - v 3), 0] i :=
  fderiv_coefficients hx i v

example (x : E) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  christoffel D x

example (y : E) (k i j : Fin 4) :
    christoffel D y k i j = christoffel D y k j i :=
  christoffel_symm y k i j

example (hx : x ∈ domain D) (k i j : Fin 4) :
    christoffelOf (metric D).coefficient x k i j = christoffel D x k i j :=
  christoffelOf_eq hx k i j

example (hx : x ∈ domain D) :
    ∀ᶠ z in 𝓝 x, ∀ k i j, christoffelOf (metric D).coefficient z k i j = christoffel D z k i j :=
  eventually_christoffelOf_eq hx

example (u : ℝ) :
    ℝ :=
  ricciFactor D u

example (x : E) :
    Fin 4 → Fin 4 → ℝ :=
  ricci D x

example (hx : x ∈ domain D) (j k : Fin 4) :
    ricciOf (metric D).coefficient x j k = ricci D x j k :=
  ricciOf_eq hx j k

example (hx : x ∈ domain D) (j k : Fin 4) :
    ricciOf (metric D).coefficient x j k =
      -ricciFactor D (retarded x) * nullCovector j * nullCovector k :=
  ricciOf_eq_null hx j k

example (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 0 0 = -ricciFactor D (retarded x) :=
  ricci_zero_zero hx

example (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 0 3 = ricciFactor D (retarded x) :=
  ricci_zero_three hx

example (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 3 0 = ricciFactor D (retarded x) :=
  ricci_three_zero hx

example (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 3 3 = -ricciFactor D (retarded x) :=
  ricci_three_three hx

example :
    (∀ x ∈ domain D, ∀ j k, ricciOf (metric D).coefficient x j k = 0) ↔
      ∀ u ∈ D.J, ricciFactor D u = 0 :=
  ricciOf_eq_zero_iff

example (h : ∀ u ∈ D.J, ricciFactor D u = 0) (κ : ℝ) :
    (metric D).IsEinstein κ 0 0 :=
  isEinstein_vacuum h κ

example (hx : x ∈ domain D) :
    curvatureOf (christoffel D) x 1 0 1 0 =
      deriv (deriv D.a) (retarded x) / D.a (retarded x) :=
  curvatureOf_christoffel_one hx

example (hx : x ∈ domain D) :
    curvatureOf (christoffel D) x 2 0 2 0 =
      deriv (deriv D.b) (retarded x) / D.b (retarded x) :=
  curvatureOf_christoffel_two hx

example (x y : domain D) :
    (metric D).toLorentzMetric.chartCurvature (physicalChart x) y 1 0 1 0 =
      deriv (deriv D.a) (retarded y.1) / D.a (retarded y.1) :=
  chartCurvature_one_zero_one_zero x y

example (x y : domain D) :
    (metric D).toLorentzMetric.chartCurvature (physicalChart x) y 2 0 2 0 =
      deriv (deriv D.b) (retarded y.1) / D.b (retarded y.1) :=
  chartCurvature_two_zero_two_zero x y

namespace LogData

variable (P : LogData)

example (s u : ℝ) :
    ℝ :=
  scale P s u

example (s : ℝ) :
    ContDiffOn ℝ ∞ (P.scale s) P.J :=
  contDiffOn_scale P s

example (s : ℝ) {u : ℝ} (hu : u ∈ P.J) :
    0 < P.scale s u :=
  scale_pos P s hu

example :
    Data :=
  toData P

example :
    P.toData.J = P.J :=
  toData_J P

example :
    P.toData.a = P.scale 1 :=
  toData_a P

example :
    P.toData.b = P.scale (-1) :=
  toData_b P

variable {P}

example (s : ℝ) {u : ℝ} (hu : u ∈ P.J) :
    HasDerivAt (P.scale s)
      ((deriv P.L u + s * deriv P.β u * P.L u) * Real.exp (s * P.β u)) u :=
  hasDerivAt_scale s hu

example (s : ℝ) {u : ℝ} (hu : u ∈ P.J) :
    deriv (deriv (P.scale s)) u =
      (deriv (deriv P.L) u + 2 * s * deriv P.L u * deriv P.β u +
        s * P.L u * deriv (deriv P.β) u + s ^ 2 * P.L u * deriv P.β u ^ 2) *
        Real.exp (s * P.β u) :=
  deriv_deriv_scale s hu

example {u : ℝ} (hu : u ∈ P.J) :
    ricciFactor P.toData u = 2 * (deriv (deriv P.L) u + deriv P.β u ^ 2 * P.L u) / P.L u :=
  ricciFactor_toData hu

example :
    (∀ x ∈ domain P.toData, ∀ j k, ricciOf (metric P.toData).coefficient x j k = 0) ↔
      ∀ u ∈ P.J, deriv (deriv P.L) u + deriv P.β u ^ 2 * P.L u = 0 :=
  ricciOf_toData_eq_zero_iff

end LogData

example :
    LogData :=
  strong

example :
    strong.J = Ioo (-(π / 2)) (π / 2) :=
  strong_J

example :
    ∀ x ∈ domain strong.toData, ∀ j k, ricciOf (metric strong.toData).coefficient x j k = 0 :=
  ricciOf_strong

example (κ : ℝ) :
    (metric strong.toData).IsEinstein κ 0 0 :=
  isEinstein_strong κ

example {u : ℝ} (hu : u ∈ strong.J) :
    deriv (deriv strong.toData.a) u / strong.toData.a u = -2 * Real.tan u :=
  accel_strong hu

example (x y : domain strong.toData) :
    (metric strong.toData).toLorentzMetric.chartCurvature (physicalChart x) y 1 0 1 0 =
      -2 * Real.tan (retarded y.1) :=
  chartCurvature_strong x y

example (x y : domain strong.toData) (hy : retarded y.1 ≠ 0) :
    (metric strong.toData).toLorentzMetric.chartCurvature (physicalChart x) y 1 0 1 0 ≠ 0 :=
  chartCurvature_strong_ne_zero x y hy

example :
    ∃ y : domain strong.toData,
      (metric strong.toData).toLorentzMetric.chartCurvature (physicalChart y) y 1 0 1 0 ≠ 0 :=
  exists_chartCurvature_strong_ne_zero

example (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (ε : ℝ) :
    LogData :=
  weak f hf ε

variable {f : ℝ → ℝ} {hf : ContDiff ℝ ∞ f} {ε : ℝ}

example (y : E) :
    y ∈ domain (weak f hf ε).toData :=
  mem_domain_weak y

example (u : ℝ) :
    ricciFactor (weak f hf ε).toData u = 2 * ε ^ 2 * deriv f u ^ 2 :=
  ricciFactor_weak u

example (y : E) (j k : Fin 4) :
    ricciOf (metric (weak f hf ε).toData).coefficient y j k =
      -(2 * ε ^ 2 * deriv f (retarded y) ^ 2) * nullCovector j * nullCovector k :=
  ricciOf_weak y j k

example (y : E) :
    ricciOf (metric (weak f hf ε).toData).coefficient y 0 0 =
      -2 * ε ^ 2 * deriv f (retarded y) ^ 2 :=
  ricci_zero_zero_weak y

example (y : E) (j k : Fin 4) :
    HasDerivAt (fun ε => ricciOf (metric (weak f hf ε).toData).coefficient y j k) 0 0 :=
  hasDerivAt_ricciOf_weak y j k

example (hε : ε ≠ 0) {u : ℝ} (hu : deriv f u ≠ 0) :
    ¬ ∀ y ∈ domain (weak f hf ε).toData, ∀ j k,
      ricciOf (metric (weak f hf ε).toData).coefficient y j k = 0 :=
  not_ricciFlat_weak hε hu

example (hε : ε ≠ 0) :
    ¬ ∀ y ∈ domain (weak (fun u => u) contDiff_id ε).toData, ∀ j k,
      ricciOf (metric (weak (fun u => u) contDiff_id ε).toData).coefficient y j k = 0 :=
  not_ricciFlat_weak_id hε

end ProjectAinos.GeneralRelativity.ExactPlaneWave

end ExactPlaneWave
