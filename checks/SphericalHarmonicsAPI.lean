/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.SpecialFunctions.SphericalHarmonics

open MvPolynomial ProjectAinos.SpecialFunctions
open ProjectAinos.SpecialFunctions.HarmonicPolynomial
open ProjectAinos.SpecialFunctions.SphericalHarmonics

noncomputable section

example (d : ℕ) : UnitSphere d = Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := rfl

example (d k : ℕ) (p : homogeneousSubmodule (Fin d) ℝ k) (u : UnitSphere d) :
    restrict d k p u = eval u.val p.val := rfl

example {d : ℕ} (hd : 0 < d) (k : ℕ) : Function.Injective (restrict d k) := restrict_injective hd k

example (d k : ℕ) : space d k = (harmonics d k).map (restrict d k) := rfl

example {d : ℕ} (hd : 0 < d) (k : ℕ) :
    Module.finrank ℝ (space d k) = Module.finrank ℝ (harmonics d k) := finrank_space hd k

example (k : ℕ) : Module.finrank ℝ (space 3 k) = 2 * k + 1 := finrank_space_three k

example {d k : ℕ} (p : harmonics d k) (u : UnitSphere d) :
    eval u.val (angularLaplacian d p.val.val) =
      -((k : ℝ) * (k + d - 2 : ℝ)) * restrict d k p.val u := angular_eigenvalue p u

example {k : ℕ} (p : harmonics 4 k) (u : UnitSphere 4) :
    eval u.val (angularLaplacian 4 p.val.val) = -((k : ℝ) * (k + 2)) * restrict 4 k p.val u :=
  angular_eigenvalue_three_sphere p u

example (n m : ℕ) {e : EuclideanSpace ℝ (Fin 3)} (he : ‖e‖ = 1) :
    (∫ u : UnitSphere 3, (Legendre.polynomial n).eval (inner ℝ u.val e) *
      (Legendre.polynomial m).eval (inner ℝ u.val e)
      ∂ProjectAinos.SmoothGeometry.Sphere.sphereMeasure) =
      if n = m then 4 * Real.pi / (2 * (n : ℝ) + 1) else 0 := integral_zonal_mul n m he
