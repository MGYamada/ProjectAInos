module

import ProjectAinos.SpecialFunctions.CubicPhase

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
