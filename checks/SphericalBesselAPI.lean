/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.SpecialFunctions.SphericalBesselEquation

open Complex Polynomial ProjectAinos.SpecialFunctions
open Legendre Bessel

noncomputable section

example (n : ℕ) : derivative (polynomial (n + 2) - polynomial n) =
    C (2 * (n : ℝ) + 3) * polynomial (n + 1) := derivative_sub_two n

example (n : ℕ) : mulXWeights n = Finsupp.single (n + 1) ((n + 1 : ℝ) / (2 * n + 1)) +
    Finsupp.single (n - 1) (n / (2 * n + 1 : ℝ)) := rfl

example (k n : ℕ) : 0 ≤ monomialWeights k n := monomialWeights_nonneg k n

example (k : ℕ) (x : ℝ) : HasSum (fun n => monomialWeights k n * (polynomial n).eval x)
    (x ^ k) := hasSum_monomial k x

example (k : ℕ) : HasSum (monomialWeights k) 1 := hasSum_monomialWeights k

example (k n : ℕ) : ∫ x in (-1 : ℝ)..1, x ^ k * (polynomial n).eval x =
    monomialWeights k n * (2 / (2 * (n : ℝ) + 1)) := integral_pow_mul k n

example (n : ℕ) (z : ℂ) : sphericalJ n z =
    (∫ t in (-1 : ℝ)..1, exp (I * z * t) * ((polynomial n).eval t : ℝ)) / (2 * I ^ n) := rfl

example (n : ℕ) : sphericalJ n 0 = if n = 0 then 1 else 0 := sphericalJ_zero n

example {z : ℂ} (hz : z ≠ 0) : sphericalJ 0 z = sin z / z := sphericalJ_zero_order hz

example {z : ℂ} (hz : z ≠ 0) : sphericalJ 1 z = sin z / z ^ 2 - cos z / z :=
  sphericalJ_one_order hz

example (z : ℂ) (n : ℕ) : z * (sphericalJ (n + 2) z + sphericalJ n z) =
    (2 * (n : ℂ) + 3) * sphericalJ (n + 1) z := sphericalJ_recurrence z n

example (z : ℂ) {t : ℝ} (ht : |t| ≤ 1) : HasSum (fun n : ℕ =>
    (2 * (n : ℂ) + 1) * I ^ n * sphericalJ n z * ((polynomial n).eval t : ℝ))
    (exp (I * z * t)) := hasSum_planeWave z ht

example (n : ℕ) (z : ℂ) : sphericalY (n + 2) z =
    (2 * (n : ℂ) + 3) / z * sphericalY (n + 1) z - sphericalY n z := rfl

example (n : ℕ) (z : ℂ) : sphericalHankel₁ n z = sphericalJ n z + I * sphericalY n z := rfl

example (n : ℕ) (z : ℂ) : sphericalHankel₂ n z = sphericalJ n z - I * sphericalY n z := rfl

example (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (sphericalJ n) (n / z * sphericalJ n z - sphericalJ (n + 1) z) z :=
  hasDerivAt_sphericalJ n hz

example (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (sphericalY n) (n / z * sphericalY n z - sphericalY (n + 1) z) z :=
  hasDerivAt_sphericalY n hz

example (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    z ^ 2 * deriv (deriv (sphericalJ n)) z + 2 * z * deriv (sphericalJ n) z +
      (z ^ 2 - n * (n + 1 : ℂ)) * sphericalJ n z = 0 := sphericalJ_equation n hz

example (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    z ^ 2 * deriv (deriv (sphericalY n)) z + 2 * z * deriv (sphericalY n) z +
      (z ^ 2 - n * (n + 1 : ℂ)) * sphericalY n z = 0 := sphericalY_equation n hz

example (n : ℕ) {z : ℂ} (hz : z ≠ 0) (f : ℂ → ℂ)
    (hf : f ∈ ({sphericalHankel₁ n, sphericalHankel₂ n} : Set (ℂ → ℂ))) :
    z ^ 2 * deriv (deriv f) z + 2 * z * deriv f z + (z ^ 2 - n * (n + 1 : ℂ)) * f z = 0 :=
  sphericalHankel_equations n hz f hf

example (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    sphericalJ n z * deriv (sphericalY n) z - deriv (sphericalJ n) z * sphericalY n z =
      1 / z ^ 2 := spherical_wronskian n hz
