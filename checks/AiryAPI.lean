module

import ProjectAinos.SpecialFunctions.AiryMacdonald
import ProjectAinos.SpecialFunctions.AiryVertical
import ProjectAinos.SpecialFunctions.CubicPhase
import ProjectAinos.SpecialFunctions.BesselContour

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology Real ComplexConjugate
open ProjectAinos.SpecialFunctions.Airy
open ProjectAinos.SpecialFunctions.Oscillatory

example (n : ℕ) (z : ℂ) : HasDerivAt (moment n) (-moment (n+1) z) z :=
  hasDerivAt_moment n z

example (z : ℂ) : moment 2 z + z * moment 0 z = 1 :=
  moment_recurrence z

example (n : ℕ) : moment n 0 =
    (((1/3 : ℝ) ^ (-((n : ℝ)+1)/3) * (1/3) * Real.Gamma (((n : ℝ)+1)/3)) : ℝ) :=
  moment_zero n

example {z : ℂ} {B R : ℝ} (hz : ‖z‖ ≤ B) (hR : 0 ≤ R) :
    ‖moment 0 z - ∫ t in 0..R, exp (-(t : ℂ)^3/3 - z*t)‖ ≤
      ∫ t : ℝ in Ioi R, Real.exp ((B^2+9)/2) * Real.exp (-t^2) :=
  moment_tail hz hR

example : upper = (1 + (√3 : ℝ) * I) / 2 :=
  upper_eq

example (n : ℕ) (z : ℂ) : conj (moment n z) = moment n (conj z) :=
  conj_moment n z

example (n : ℕ) (z : ℂ) :
    Tendsto (fun R : ℝ => ∫ t in 0..R, (t : ℂ)^n * exp (-(t : ℂ)^3/3 - z*t))
      atTop (𝓝 (moment n z)) :=
  tendsto_moment n z

example (w z : ℂ) : conj (ray w z) = ray (conj w) (conj z) :=
  conj_ray w z

example (w z : ℂ) : HasDerivAt (ray w) (-w ^ 2 * moment 1 (w*z)) z :=
  hasDerivAt_ray w z

example (z : ℂ) : HasDerivAt ai
    ((deriv (ray upper) z - deriv (ray (starRingEnd ℂ upper)) z) / (2 * π * I)) z :=
  hasDerivAt_ai z

example (z : ℂ) : HasDerivAt bi
    ((deriv (ray upper) z + deriv (ray (starRingEnd ℂ upper)) z - 2 * deriv (ray (-1)) z) /
      (2 * π)) z :=
  hasDerivAt_bi z

example (z : ℂ) : deriv (deriv ai) z = z * ai z :=
  ai_equation z

example (z : ℂ) : deriv (deriv bi) z = z * bi z :=
  bi_equation z

example :
    ai 0 = (√3 : ℝ) * moment 0 0 / (2 * π) ∧
    deriv ai 0 = -(√3 : ℝ) * moment 1 0 / (2 * π) ∧
    bi 0 = 3 * moment 0 0 / (2 * π) ∧ deriv bi 0 = 3 * moment 1 0 / (2 * π) :=
  initialValues

example (z : ℂ) : ai z * deriv bi z - deriv ai z * bi z = 1 / π :=
  wronskian z

example (x : ℝ) :
    Tendsto (fun R : ℝ => (1/π) * ∫ t in 0..R, Real.cos (t^3/3+x*t)) atTop (𝓝 (ai x).re) :=
  tendsto_cos_integral x

example (x : ℝ) :
    Tendsto (fun R : ℝ => (1/π) * ((∫ t in 0..R, Real.sin (t^3/3+x*t)) +
      ∫ t : ℝ in Ioi 0, Real.exp (-t^3/3+x*t))) atTop (𝓝 (bi x).re) :=
  tendsto_bi_integral x

example (x : ℝ) : cubicLimit x + conj (cubicLimit x) = 2 * π * ai x :=
  cubicLimit_add_conj x

example {x R B : ℝ} (hx : |x| ≤ B) (hR : 0 < R) (hB : 3*B ≤ R^2) :
    ‖cubicIntegral x R - cubicLimit x‖ ≤ 3/R^2 +
      ∫ t : ℝ in Ioi (2/√3*R), Real.exp ((B^2+9)/2) * Real.exp (-t^2) :=
  cubic_tail hx hR hB

example {b B : ℝ} (hb : 0 < b) {u : ℝ → ℝ} (hu : ∀ᶠ r in atTop, |u r| ≤ B)
    {A D : ℝ → ℂ} (hA : ∀ t ∈ Icc 0 b, HasDerivAt A (D t) t) (hD : ContinuousOn D (Icc 0 b)) :
    Tendsto (fun r : ℝ => (r : ℂ) * (∫ t in 0..b,
      A t * exp ((((r*t)^3/3+u r*(r*t) : ℝ) : ℂ) * I)) - A 0 * cubicLimit (u r))
      atTop (𝓝 0) :=
  cubic_endpoint hb hu hA hD

example {b B : ℝ} (hb : 0 < b) {u : ℝ → ℝ}
    (hu : ∀ᶠ r in atTop, |u r| ≤ B) {A D : ℝ → ℂ}
    (hA : ∀ t ∈ Icc (-b) b, HasDerivAt A (D t) t) (hD : ContinuousOn D (Icc (-b) b)) :
    Tendsto (fun r : ℝ => (r : ℂ) * (∫ t in -b..b,
      A t * exp ((((r*t)^3/3+u r*(r*t) : ℝ) : ℂ) * I)) - A 0 * (2*π*ai (u r)))
      atTop (𝓝 0) :=
  cubic_coalescence hb hu hA hD

example : upper ^ 3 = -1 :=
  upper_cube

example (z w : ℂ) : HasDerivAt (primitive z) (integrand z w) w :=
  deriv_primitive z w

example (z a b : ℂ) (R : ℝ) :
    primitive z (a+b*R) - primitive z a = ∫ t in 0..R, b * integrand z (a+b*t) :=
  segment z a b R

example (w z : ℂ) (hc : w^3 = -1) : Tendsto (fun R : ℝ => primitive z (w * R)) atTop
    (𝓝 (ray w z)) :=
  ray_limit w z hc

example (x S : ℝ) (hS : 0 ≤ S) :
    Tendsto (fun R : ℝ => primitive x (I*R + S)) atTop (𝓝 (ray upper x)) :=
  shifted_vertical_limit x S hS

open ProjectAinos.SpecialFunctions.Bessel

example {b : ℝ} (hb : 0 < b) :
    ai (b^2 : ℝ) = b / ((√3 : ℝ) * π) * macdonald (1/3) (2*b^3/3 : ℝ) :=
  ai_sq_macdonald hb

example {b : ℝ} (hb : 0 < b) :
    deriv ai (b^2 : ℝ) = -(b^2 : ℝ) / ((√3 : ℝ) * π) * macdonald (2/3) (2*b^3/3 : ℝ) :=
  deriv_ai_sq_macdonald hb

example (u : ℝ) :
    (∫ t : ℝ, integrand u (1+t*I)) = 2*π*ai u :=
  integral_vertical u

example (u : ℝ) :
    (∫ t : ℝ, -(1+t*I) * integrand u (1+t*I)) = 2*π*deriv ai u :=
  integral_vertical_deriv u

example (n : ℤ) (x h : ℝ) :
    (∫ t in -π..π, fourierKernel n x (t-h*I)) = 2*π*besselJ n x :=
  integral_shift n x h

example (n : ℤ) (x h : ℝ) :
    (∫ t in -π..π, I*sin (t-h*I)*fourierKernel n x (t-h*I)) = 2*π*deriv (besselJ n) x :=
  integral_shift_deriv n x h
