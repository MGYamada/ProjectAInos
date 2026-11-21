module

import ProjectAinos.SpecialFunctions.Kapteyn

noncomputable section
open Complex Set Filter MeasureTheory Function
open scoped Real ContDiff
open ProjectAinos.SmoothGeometry.Fourier.PeriodicSeries
open ProjectAinos.SpecialFunctions.Kapteyn

example {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (a b : ℂ) (n : ℤ) : coefficient (fun t => a * f t + b * g t) n =
      a * coefficient f n + b * coefficient g n :=
  coefficient_linear hf hg a b n

example {f : ℝ → ℂ} (hf : Continuous f) (a : ℂ) (n : ℤ) :
    coefficient (fun t => a * f t) n = a * coefficient f n :=
  coefficient_const_mul hf a n

example {f : ℝ → ℂ} (hp : Periodic f (2 * π)) (hf : Differentiable ℝ f)
    (hd : Continuous (deriv f)) {n : ℤ} (hn : n ≠ 0) :
    coefficient f n = coefficient (deriv f) n / (I * n) :=
  coefficient_deriv hp hf hd hn

example {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hp : Periodic f (2 * π)) :
    Summable (coefficient f) :=
  summable hf hp

example {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hp : Periodic f (2 * π)) (x : ℝ) :
    HasSum (fun n : ℤ => coefficient f n * exp (((n : ℂ) * x) * I)) (f x) :=
  hasSum hf hp x

example (k : ℤ) (x : ℝ) :
    (∫ t in -π..π, exp (-(((k : ℝ) * t - x * Real.sin t : ℝ) : ℂ) * I)) =
      2 * π * besselJ k x :=
  ProjectAinos.SpecialFunctions.Bessel.integral_exponential k x

example (k : ℤ) (z : ℂ) :
    2 * deriv (besselJ k) z = besselJ (k - 1 : ℤ) z - besselJ (k + 1 : ℤ) z :=
  ProjectAinos.SpecialFunctions.Bessel.twice_deriv_int k z

example (k : ℤ) (z : ℂ) : z * (besselJ (k - 1 : ℤ) z + besselJ (k + 1 : ℤ) z) =
    2 * k * besselJ k z :=
  ProjectAinos.SpecialFunctions.Bessel.recurrence_int k z

open Real

example {e : ℝ} (he : |e| < 1) (M : ℝ) :
    meanAnomaly e (eccentricAnomaly e M) = M :=
  mean_eccentric he M

example {e : ℝ} (he : |e| < 1) (E : ℝ) :
    eccentricAnomaly e (meanAnomaly e E) = E :=
  eccentric_mean he E

example {e : ℝ} (he : |e| < 1) (M : ℝ) :
    eccentricAnomaly e (M + 2 * π) = eccentricAnomaly e M + 2 * π :=
  eccentric_add_period he M

example {e : ℝ} (he : |e| < 1) : ContDiff ℝ ∞ (eccentricAnomaly e) :=
  contDiff_eccentric he

example {e : ℝ} (he : |e| < 1) (M : ℝ) :
    HasDerivAt (eccentricAnomaly e) ((1 - e * Real.cos (eccentricAnomaly e M))⁻¹) M :=
  hasDerivAt_eccentric he M

example {e : ℝ} (he : |e| < 1) (m n : ℤ) :
    coefficient (fun M => ((deriv (eccentricAnomaly e) M : ℝ) : ℂ) * mode e m M) n =
      Complex.besselJ (n - m : ℤ) ((n : ℝ) * e) :=
  coefficient_mode_velocity he m n

example {e : ℝ} (he : |e| < 1) (m : ℤ) (M : ℝ) :
    HasSum (fun n : ℤ => Complex.besselJ (n - m : ℤ) ((n : ℝ) * e) *
      Complex.exp (((n : ℂ) * M) * Complex.I))
      (((deriv (eccentricAnomaly e) M : ℝ) : ℂ) * mode e m M) :=
  hasSum_mode_velocity he m M

example {e : ℝ} (he : |e| < 1) (m n : ℤ) (hn : n ≠ 0) :
    coefficient (mode e m) n = (m : ℂ) / n * Complex.besselJ (n - m : ℤ) ((n : ℝ) * e) :=
  coefficient_mode he m n hn

example {e : ℝ} (he : |e| < 1) (n : ℤ) (hn : n ≠ 0) :
    coefficient (fun M => (Real.cos (eccentricAnomaly e M) : ℂ)) n =
      deriv (Complex.besselJ n) ((n : ℝ) * e) / n :=
  coefficient_cos he n hn

example {e : ℝ} (he : |e| < 1) (n : ℤ) (hn : n ≠ 0) :
    coefficient (fun M => (Real.sin (eccentricAnomaly e M) : ℂ)) n =
      (Complex.besselJ (n - 1 : ℤ) ((n : ℝ) * e) +
        Complex.besselJ (n + 1 : ℤ) ((n : ℝ) * e)) / (2 * Complex.I * n) :=
  coefficient_sin he n hn

example {e : ℝ} (he : |e| < 1) (M : ℝ) :
    HasSum (fun n : ℤ => Complex.besselJ n ((n : ℝ) * e) *
      Complex.exp (((n : ℂ) * M) * Complex.I)) ((deriv (eccentricAnomaly e) M : ℝ) : ℂ) :=
  hasSum_deriv_eccentric he M
