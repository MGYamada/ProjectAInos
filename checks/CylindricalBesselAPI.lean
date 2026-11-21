module

import ProjectAinos.SpecialFunctions.ModifiedBessel
import ProjectAinos.SpecialFunctions.Hankel

noncomputable section
open Complex MeasureTheory Set ProjectAinos.SpecialFunctions.Bessel
open scoped ComplexConjugate Real

example (b z : ℂ) : HasDerivAt (regularizedHGFun 0 {b}) (regularizedHGFun 0 {b + 1} z) z :=
  hasDerivAt_zeroFone b z

example (b z : ℂ) : regularizedHGFun 0 {b} z =
    b * regularizedHGFun 0 {b + 1} z + z * regularizedHGFun 0 {b + 1 + 1} z :=
  zeroFone_contiguous b z

example (a z : ℂ) (hz : z ∈ slitPlane) :
    HasDerivAt (modifiedI a) (a / z * modifiedI a z + modifiedI (a + 1) z) z :=
  hasDerivAt_modifiedI a z hz

example (a z : ℂ) (hz : z ∈ slitPlane) :
    modifiedI (a - 1) z - modifiedI (a + 1) z = 2 * a / z * modifiedI a z :=
  modifiedI_recurrence a z hz

example (a z : ℂ) (hz : z ∈ slitPlane) :
    z ^ 2 * deriv (deriv (modifiedI a)) z + z * deriv (modifiedI a) z -
      (z ^ 2 + a ^ 2) * modifiedI a z = 0 := modifiedI_equation a z hz

example (a z : ℂ) (hz : 0 < z.re) : Integrable (fun t : ℝ => exp (-z * Real.cosh t + a * t)) :=
  integrable_macdonald a z hz

example (a z : ℂ) (hz : 0 < z.re) :
    HasDerivAt (macdonald a) (-(macdonald (a + 1) z + macdonald (a - 1) z) / 2) z :=
  hasDerivAt_macdonald a z hz

example (a z : ℂ) : macdonald (-a) z = macdonald a z := macdonald_neg_order a z
example (a z : ℂ) : conj (macdonald a z) = macdonald (conj a) (conj z) := macdonald_conj a z

example (b x : ℝ) (hx : 0 < x) : macdonald (b * I) x =
    ((∫ t : ℝ, Real.exp (-x * Real.cosh t) * Real.cos (b * t)) / 2 : ℝ) :=
  macdonald_imaginary b x hx

example (a x : ℝ) (hx : 0 < x) : 0 < (macdonald a x).re := macdonald_re_pos a x hx

example (a z : ℂ) (hz : 0 < z.re) :
    z * (macdonald (a + 1) z - macdonald (a - 1) z) = 2 * a * macdonald a z :=
  macdonald_recurrence a z hz

example (a z : ℂ) (hz : 0 < z.re) :
    z ^ 2 * deriv (deriv (macdonald a)) z + z * deriv (macdonald a) z -
      (z ^ 2 + a ^ 2) * macdonald a z = 0 := macdonald_equation a z hz

open Schlaefli

example (a z : ℂ) (hz : 0 < z.re) :
    HasDerivAt (ray a) ((ray (a - 1) z - ray (a + 1) z) / 2) z := hasDerivAt_ray a z hz

example (a z : ℂ) (hz : 0 < z.re) :
    z / 2 * (ray (a + 1) z + ray (a - 1) z) - a * ray a z = 1 := ray_recurrence a z hz

example (a z : ℂ) : HasDerivAt (arc a) ((arc (a - 1) z - arc (a + 1) z) / 2) z :=
  hasDerivAt_arc a z

example (a z : ℂ) : I * (z / 2 * (arc (a + 1) z + arc (a - 1) z) - a * arc a z) =
    exp (-(a * π) * I) - 1 := arc_recurrence a z

example (a z : ℂ) (hz : 0 < z.re) : HasDerivAt (hankelFirst a)
    ((hankelFirst (a - 1) z - hankelFirst (a + 1) z) / 2) z := hasDerivAt_hankelFirst a z hz

example (a z : ℂ) (hz : 0 < z.re) :
    z / 2 * (hankelFirst (a + 1) z + hankelFirst (a - 1) z) = a * hankelFirst a z :=
  hankelFirst_recurrence a z hz

example (a z : ℂ) (hz : 0 < z.re) : HasDerivAt (neumann a)
    ((neumann (a - 1) z - neumann (a + 1) z) / 2) z := hasDerivAt_neumann a z hz

example (a z : ℂ) (hz : 0 < z.re) : HasDerivAt (hankelSecond a)
    ((hankelSecond (a - 1) z - hankelSecond (a + 1) z) / 2) z := hasDerivAt_hankelSecond a z hz

example (a z : ℂ) (hz : 0 < z.re) :
    z ^ 2 * deriv (deriv (hankelFirst a)) z + z * deriv (hankelFirst a) z +
      (z ^ 2 - a ^ 2) * hankelFirst a z = 0 := hankelFirst_equation a z hz

example (a z : ℂ) (hz : 0 < z.re) :
    z ^ 2 * deriv (deriv (neumann a)) z + z * deriv (neumann a) z +
      (z ^ 2 - a ^ 2) * neumann a z = 0 := neumann_equation a z hz

example (a z : ℂ) (hz : 0 < z.re) :
    z ^ 2 * deriv (deriv (hankelSecond a)) z + z * deriv (hankelSecond a) z +
      (z ^ 2 - a ^ 2) * hankelSecond a z = 0 := hankelSecond_equation a z hz

example (n : ℤ) (x : ℝ) (hx : 0 < x) : neumann n x =
    (((∫ t in 0..π, Real.sin (x * Real.sin t - n * t)) -
      ((∫ t : ℝ in Ioi 0, Real.exp (-x * Real.sinh t + n * t)) + (-1 : ℝ) ^ n *
        ∫ t : ℝ in Ioi 0, Real.exp (-x * Real.sinh t - n * t))) / π : ℝ) :=
  neumann_integral n x hx
