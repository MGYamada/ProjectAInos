/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.SpecialFunctions.HarmonicPolynomial

open MvPolynomial ProjectAinos.SpecialFunctions.HarmonicPolynomial

noncomputable section

example (d : ℕ) : radiusSq d = ∑ i : Fin d, X i ^ 2 := rfl

example (d : ℕ) : laplacian d =
    ∑ i : Fin d, (pderiv i).toLinearMap.comp (pderiv i).toLinearMap := rfl

example {d k : ℕ} {p : MvPolynomial (Fin d) ℝ} (hp : p.IsHomogeneous k) :
    laplacian d (radiusSq d * p) = (2 * (d : ℝ) + 4 * k) • p + radiusSq d * laplacian d p :=
  laplacian_radiusSq_mul hp

example {d k : ℕ} {p : MvPolynomial (Fin d) ℝ} (hp : p.IsHomogeneous k) (hk : k ≤ 1) :
    laplacian d p = 0 := laplacian_eq_zero_of_degree_le_one hp hk

example {d k : ℕ} (hd : 0 < d) {p : MvPolynomial (Fin d) ℝ} (hp : p.IsHomogeneous (k + 2)) :
    ∃! q : homogeneousSubmodule (Fin d) ℝ k,
      (p - radiusSq d * q.val).IsHomogeneous (k + 2) ∧ laplacian d (p - radiusSq d * q.val) = 0 :=
  existsUnique_fischer hd hp

example (d k : ℕ) (p : homogeneousSubmodule (Fin d) ℝ k) :
    p ∈ harmonics d k ↔ laplacian d p.val = 0 := Iff.rfl

example {d : ℕ} (hd : 0 < d) (k : ℕ) :
    Module.finrank ℝ (harmonics d (k + 2)) + Nat.multichoose d k = Nat.multichoose d (k + 2) :=
  finrank_harmonics_add hd k

example (k : ℕ) : Module.finrank ℝ (harmonics 3 k) = 2 * k + 1 := finrank_harmonics_three k

example {d : ℕ} (i j : Fin d) (p : MvPolynomial (Fin d) ℝ) :
    rotation i j p = X i * pderiv j p - X j * pderiv i p := rfl

example (d : ℕ) (p : MvPolynomial (Fin d) ℝ) :
    angularLaplacian d p = (1 / 2 : ℝ) • ∑ i, ∑ j, rotation i j (rotation i j p) := rfl

example {d k : ℕ} {p : MvPolynomial (Fin d) ℝ} (hp : p.IsHomogeneous k) (hh : laplacian d p = 0) :
    angularLaplacian d p = (-((k : ℝ) * (k + d - 2 : ℝ))) • p := angularLaplacian_harmonic hp hh
