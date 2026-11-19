/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.GeneralRelativity.SphericalAnsatz
import ProjectAinos.GeneralRelativity.EddingtonFinkelstein
import ProjectAinos.GeneralRelativity.SchwarzschildVacuum
import ProjectAinos.GeneralRelativity.Birkhoff

/-! Public consumers of the centrally symmetric field (Landau–Lifshitz §100): the ansatz
`−A dt² + B dr² + r² dΩ²` with its Christoffel symbols, Ricci and Einstein tensors, and the
Schwarzschild field in Eddington–Finkelstein co-ordinates with its ingoing ray, the direction of
causal vectors inside `r = 2M` and the pullback to the exterior chart, the vacuum Einstein
equations of the exterior field, and Birkhoff's theorem within the ansatz with its converse, the
change of time and the uniqueness of the mass. Default elaborator options
are intentional: these checks must not rely on the implementation's transparency settings. Every
statement is pinned with its type. -/

noncomputable section

section SphericalAnsatz


open ContinuousLinearMap Set TopologicalSpace Filter

open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.SphericalAnsatz

open SmoothGeometry CoordinateMetric

example (f : ℝ → ℝ → ℝ) (t r : ℝ) :
    ℝ :=
  partialT f t r

example (f : ℝ → ℝ → ℝ) (t r : ℝ) :
    ℝ :=
  partialR f t r

variable {S : Set (ℝ × ℝ)} {f : ℝ → ℝ → ℝ}

example (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) S) {t r : ℝ} (h : (t, r) ∈ S) :
    HasDerivAt (fun s => f s r) (fderiv ℝ (Function.uncurry f) (t, r) (1, 0)) t :=
  hasDerivAt_uncurry_time hS hf h

example (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) S) {t r : ℝ} (h : (t, r) ∈ S) :
    HasDerivAt (fun s => f t s) (fderiv ℝ (Function.uncurry f) (t, r) (0, 1)) r :=
  hasDerivAt_uncurry_radius hS hf h

example (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) S) {t r : ℝ} (h : (t, r) ∈ S) :
    partialT f t r = fderiv ℝ (Function.uncurry f) (t, r) (1, 0) :=
  partialT_eq_fderiv hS hf h

example (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) S) {t r : ℝ} (h : (t, r) ∈ S) :
    partialR f t r = fderiv ℝ (Function.uncurry f) (t, r) (0, 1) :=
  partialR_eq_fderiv hS hf h

example (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) S) {t r : ℝ} (h : (t, r) ∈ S) :
    HasDerivAt (fun s => f s r) (partialT f t r) t :=
  hasDerivAt_partialT hS hf h

example (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) S) {t r : ℝ} (h : (t, r) ∈ S) :
    HasDerivAt (fun s => f t s) (partialR f t r) r :=
  hasDerivAt_partialR hS hf h

example (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) S) :
    ContDiffOn ℝ ∞ (Function.uncurry (partialT f)) S :=
  contDiffOn_partialT hS hf

example (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) S) :
    ContDiffOn ℝ ∞ (Function.uncurry (partialR f)) S :=
  contDiffOn_partialR hS hf

example (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) S) {t r : ℝ} (h : (t, r) ∈ S) :
    partialR (partialT f) t r = partialT (partialR f) t r :=
  partialR_partialT hS hf h

example (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) S) {x : MinkowskiModel 3}
    (hx : (x 0, x 1) ∈ S) :
    HasFDerivAt (fun z : MinkowskiModel 3 => f (z 0) (z 1))
      (partialT f (x 0) (x 1) • (proj 0 : MinkowskiModel 3 →L[ℝ] ℝ) +
        partialR f (x 0) (x 1) • (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ)) x :=
  hasFDerivAt_timeRadius hS hf hx

example {c d : MinkowskiModel 3 → ℝ} {c' d' : MinkowskiModel 3 →L[ℝ] ℝ} {x : MinkowskiModel 3}
    (hc : HasFDerivAt c c' x) (hd : HasFDerivAt d d' x) (h : d x ≠ 0) :
    HasFDerivAt (fun z => c z / d z) ((d x)⁻¹ • c' - (c x / d x ^ 2) • d') x :=
  hasFDerivAt_div hc hd h

namespace Data

example :
    Data :=
  flat

end Data

variable (D : Data)

example :
    IsOpen (D.I ×ˢ D.J) :=
  isOpen_timeRadius D

example :
    Opens (MinkowskiModel 3) :=
  domain D

variable {D} {x : MinkowskiModel 3}

example (hx : x ∈ domain D) :
    (x 0, x 1) ∈ D.I ×ˢ D.J :=
  mem_timeRadius hx

example (hx : x ∈ domain D) :
    0 < x 1 :=
  radius_pos hx

example (hx : x ∈ domain D) :
    0 < Real.sin (x 2) :=
  sin_pos_of_mem hx

example (hx : x ∈ domain D) :
    0 < D.A (x 0) (x 1) :=
  A_pos_of_mem hx

example (hx : x ∈ domain D) :
    0 < D.B (x 0) (x 1) :=
  B_pos_of_mem hx

example (x : MinkowskiModel 3) :
    Fin 4 → ℝ :=
  coefficients D x

example {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (D.I ×ˢ D.J)) :
    ContDiffOn ℝ ∞ (fun z : MinkowskiModel 3 => f (z 0) (z 1)) (domain D) :=
  contDiffOn_timeRadius hf

example (i : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => coefficients D x i) (domain D) :=
  contDiffOn_coefficients i

example :
    CoordinateMetric .timeNegative 3 (domain D) :=
  metric D

example (y : MinkowskiModel 3) :
    (metric D).coefficient y = Matrix.diagonal (coefficients D y) :=
  coefficient_metric y

example (hx : x ∈ domain D) (i : Fin 4) :
    coefficients D x i ≠ 0 :=
  coefficients_ne_zero hx i

example {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (D.I ×ˢ D.J))
    (hx : x ∈ domain D) :
    HasFDerivAt (fun z : MinkowskiModel 3 => f (z 0) (z 1))
      (partialT f (x 0) (x 1) • (proj 0 : MinkowskiModel 3 →L[ℝ] ℝ) +
        partialR f (x 0) (x 1) • (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ)) x :=
  hasFDerivAt_timeRadius_domain hf hx

example {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (D.I ×ˢ D.J))
    (hx : x ∈ domain D) :
    fderiv ℝ (fun z : MinkowskiModel 3 => f (z 0) (z 1)) x (Pi.single 0 1) =
      partialT f (x 0) (x 1) :=
  fderiv_single_zero hf hx

example {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (D.I ×ˢ D.J))
    (hx : x ∈ domain D) :
    fderiv ℝ (fun z : MinkowskiModel 3 => f (z 0) (z 1)) x (Pi.single 1 1) =
      partialR f (x 0) (x 1) :=
  fderiv_single_one hf hx

example (hx : x ∈ domain D) (v : MinkowskiModel 3) :
    fderiv ℝ (fun z => coefficients D z 0) x v =
      -(partialT D.A (x 0) (x 1) * v 0 + partialR D.A (x 0) (x 1) * v 1) :=
  fderiv_coefficients_zero hx v

example (hx : x ∈ domain D) (v : MinkowskiModel 3) :
    fderiv ℝ (fun z => coefficients D z 1) x v =
      partialT D.B (x 0) (x 1) * v 0 + partialR D.B (x 0) (x 1) * v 1 :=
  fderiv_coefficients_one hx v

example (v : MinkowskiModel 3) :
    fderiv ℝ (fun z => coefficients D z 2) x v = 2 * x 1 * v 1 :=
  fderiv_coefficients_two v

example (v : MinkowskiModel 3) :
    fderiv ℝ (fun z => coefficients D z 3) x v =
      2 * x 1 * Real.sin (x 2) ^ 2 * v 1 +
        x 1 ^ 2 * (2 * Real.sin (x 2) * Real.cos (x 2)) * v 2 :=
  fderiv_coefficients_three v

example (hx : x ∈ domain D) (k : Fin 4) (v : MinkowskiModel 3) :
    fderiv ℝ (fun z => coefficients D z k) x v =
      ![-(partialT D.A (x 0) (x 1) * v 0 + partialR D.A (x 0) (x 1) * v 1),
        partialT D.B (x 0) (x 1) * v 0 + partialR D.B (x 0) (x 1) * v 1, 2 * x 1 * v 1,
        2 * x 1 * Real.sin (x 2) ^ 2 * v 1 +
          x 1 ^ 2 * (2 * Real.sin (x 2) * Real.cos (x 2)) * v 2] k :=
  fderiv_coefficients hx k v

example {P Q : ℝ → ℝ → ℝ} (hP : ContDiffOn ℝ ∞ (Function.uncurry P) (D.I ×ˢ D.J))
    (hQ : ContDiffOn ℝ ∞ (Function.uncurry Q) (D.I ×ˢ D.J)) (hx : x ∈ domain D)
    (hQ0 : Q (x 0) (x 1) ≠ 0) (v : MinkowskiModel 3) :
    fderiv ℝ (fun z : MinkowskiModel 3 => P (z 0) (z 1) / (2 * Q (z 0) (z 1))) x v =
      ((partialT P (x 0) (x 1) * v 0 + partialR P (x 0) (x 1) * v 1) * Q (x 0) (x 1) -
        P (x 0) (x 1) * (partialT Q (x 0) (x 1) * v 0 + partialR Q (x 0) (x 1) * v 1)) /
        (2 * Q (x 0) (x 1) ^ 2) :=
  fderiv_div_two hP hQ hx hQ0 v

example (x : MinkowskiModel 3) :
    ℝ :=
  gamma000 D x

example (x : MinkowskiModel 3) :
    ℝ :=
  gamma001 D x

example (x : MinkowskiModel 3) :
    ℝ :=
  gamma011 D x

example (x : MinkowskiModel 3) :
    ℝ :=
  gamma100 D x

example (x : MinkowskiModel 3) :
    ℝ :=
  gamma101 D x

example (x : MinkowskiModel 3) :
    ℝ :=
  gamma111 D x

example (x : MinkowskiModel 3) :
    ℝ :=
  gamma122 D x

example (x : MinkowskiModel 3) :
    ℝ :=
  gamma133 D x

example (x : MinkowskiModel 3) :
    ℝ :=
  gamma212 x

example (x : MinkowskiModel 3) :
    ℝ :=
  gamma233 x

example (x : MinkowskiModel 3) :
    ℝ :=
  gamma323 x

example (x : MinkowskiModel 3) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  christoffel D x

example (y : MinkowskiModel 3) (k i j : Fin 4) :
    christoffel D y k i j = christoffel D y k j i :=
  christoffel_symm y k i j

example (hx : x ∈ domain D) (k i j : Fin 4) :
    christoffelOf (metric D).coefficient x k i j = christoffel D x k i j :=
  christoffelOf_eq hx k i j

example (hx : x ∈ domain D) :
    ∀ᶠ z in 𝓝 x, ∀ k i j, christoffelOf (metric D).coefficient z k i j = christoffel D z k i j :=
  eventually_christoffelOf_eq hx

example (hx : x ∈ domain D) (v : MinkowskiModel 3) :
    fderiv ℝ (gamma000 D) x v =
      ((partialT (partialT D.A) (x 0) (x 1) * v 0 + partialR (partialT D.A) (x 0) (x 1) * v 1) *
          D.A (x 0) (x 1) -
        partialT D.A (x 0) (x 1) *
          (partialT D.A (x 0) (x 1) * v 0 + partialR D.A (x 0) (x 1) * v 1)) /
        (2 * D.A (x 0) (x 1) ^ 2) :=
  fderiv_gamma000 hx v

example (hx : x ∈ domain D) (v : MinkowskiModel 3) :
    fderiv ℝ (gamma001 D) x v =
      ((partialT (partialR D.A) (x 0) (x 1) * v 0 + partialR (partialR D.A) (x 0) (x 1) * v 1) *
          D.A (x 0) (x 1) -
        partialR D.A (x 0) (x 1) *
          (partialT D.A (x 0) (x 1) * v 0 + partialR D.A (x 0) (x 1) * v 1)) /
        (2 * D.A (x 0) (x 1) ^ 2) :=
  fderiv_gamma001 hx v

example (hx : x ∈ domain D) (v : MinkowskiModel 3) :
    fderiv ℝ (gamma011 D) x v =
      ((partialT (partialT D.B) (x 0) (x 1) * v 0 + partialR (partialT D.B) (x 0) (x 1) * v 1) *
          D.A (x 0) (x 1) -
        partialT D.B (x 0) (x 1) *
          (partialT D.A (x 0) (x 1) * v 0 + partialR D.A (x 0) (x 1) * v 1)) /
        (2 * D.A (x 0) (x 1) ^ 2) :=
  fderiv_gamma011 hx v

example (hx : x ∈ domain D) (v : MinkowskiModel 3) :
    fderiv ℝ (gamma100 D) x v =
      ((partialT (partialR D.A) (x 0) (x 1) * v 0 + partialR (partialR D.A) (x 0) (x 1) * v 1) *
          D.B (x 0) (x 1) -
        partialR D.A (x 0) (x 1) *
          (partialT D.B (x 0) (x 1) * v 0 + partialR D.B (x 0) (x 1) * v 1)) /
        (2 * D.B (x 0) (x 1) ^ 2) :=
  fderiv_gamma100 hx v

example (hx : x ∈ domain D) (v : MinkowskiModel 3) :
    fderiv ℝ (gamma101 D) x v =
      ((partialT (partialT D.B) (x 0) (x 1) * v 0 + partialR (partialT D.B) (x 0) (x 1) * v 1) *
          D.B (x 0) (x 1) -
        partialT D.B (x 0) (x 1) *
          (partialT D.B (x 0) (x 1) * v 0 + partialR D.B (x 0) (x 1) * v 1)) /
        (2 * D.B (x 0) (x 1) ^ 2) :=
  fderiv_gamma101 hx v

example (hx : x ∈ domain D) (v : MinkowskiModel 3) :
    fderiv ℝ (gamma111 D) x v =
      ((partialT (partialR D.B) (x 0) (x 1) * v 0 + partialR (partialR D.B) (x 0) (x 1) * v 1) *
          D.B (x 0) (x 1) -
        partialR D.B (x 0) (x 1) *
          (partialT D.B (x 0) (x 1) * v 0 + partialR D.B (x 0) (x 1) * v 1)) /
        (2 * D.B (x 0) (x 1) ^ 2) :=
  fderiv_gamma111 hx v

example (hx : x ∈ domain D) (v : MinkowskiModel 3) :
    fderiv ℝ (gamma122 D) x v =
      (-v 1 * D.B (x 0) (x 1) +
        x 1 * (partialT D.B (x 0) (x 1) * v 0 + partialR D.B (x 0) (x 1) * v 1)) /
        D.B (x 0) (x 1) ^ 2 :=
  fderiv_gamma122 hx v

example (hx : x ∈ domain D) (v : MinkowskiModel 3) :
    fderiv ℝ (gamma133 D) x v =
      ((-v 1 * Real.sin (x 2) ^ 2 - x 1 * (2 * Real.sin (x 2) * Real.cos (x 2)) * v 2) *
          D.B (x 0) (x 1) +
        x 1 * Real.sin (x 2) ^ 2 *
          (partialT D.B (x 0) (x 1) * v 0 + partialR D.B (x 0) (x 1) * v 1)) /
        D.B (x 0) (x 1) ^ 2 :=
  fderiv_gamma133 hx v

example (hx : x ∈ domain D) (v : MinkowskiModel 3) :
    fderiv ℝ gamma212 x v = -v 1 / x 1 ^ 2 :=
  fderiv_gamma212 hx v

example (v : MinkowskiModel 3) :
    fderiv ℝ gamma233 x v = -(Real.cos (x 2) ^ 2 - Real.sin (x 2) ^ 2) * v 2 :=
  fderiv_gamma233 v

example (hx : x ∈ domain D) (v : MinkowskiModel 3) :
    fderiv ℝ gamma323 x v = -v 2 / Real.sin (x 2) ^ 2 :=
  fderiv_gamma323 hx v

example (g : Fin (3 + 1) → ℝ) :
    ∑ i, g i = g 0 + g 1 + g 2 + g 3 :=
  sum_four g

example (x : MinkowskiModel 3) :
    Fin 4 → Fin 4 → ℝ :=
  ricci D x

example (hx : x ∈ domain D) (j k : Fin 4) :
    ricciOf (metric D).coefficient x j k = ricci D x j k :=
  ricciOf_eq hx j k

example (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 0 0 =
      (-(x 1) * D.A (x 0) (x 1) * (partialR D.A (x 0) (x 1) * partialR D.B (x 0) (x 1) -
          partialT D.B (x 0) (x 1) ^ 2) -
        x 1 * D.B (x 0) (x 1) * (partialR D.A (x 0) (x 1) ^ 2 -
          partialT D.A (x 0) (x 1) * partialT D.B (x 0) (x 1)) +
        2 * x 1 * D.A (x 0) (x 1) * D.B (x 0) (x 1) *
          (partialR (partialR D.A) (x 0) (x 1) - partialT (partialT D.B) (x 0) (x 1)) +
        4 * D.A (x 0) (x 1) * D.B (x 0) (x 1) * partialR D.A (x 0) (x 1)) /
        (4 * x 1 * D.A (x 0) (x 1) * D.B (x 0) (x 1) ^ 2) :=
  ricci_zero_zero hx

example (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 0 1 = partialT D.B (x 0) (x 1) / (x 1 * D.B (x 0) (x 1)) :=
  ricci_zero_one hx

example (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 1 0 = partialT D.B (x 0) (x 1) / (x 1 * D.B (x 0) (x 1)) :=
  ricci_one_zero hx

example (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 1 1 =
      (x 1 * D.A (x 0) (x 1) * (partialR D.A (x 0) (x 1) * partialR D.B (x 0) (x 1) -
          partialT D.B (x 0) (x 1) ^ 2) +
        x 1 * D.B (x 0) (x 1) * (partialR D.A (x 0) (x 1) ^ 2 -
          partialT D.A (x 0) (x 1) * partialT D.B (x 0) (x 1)) -
        2 * x 1 * D.A (x 0) (x 1) * D.B (x 0) (x 1) *
          (partialR (partialR D.A) (x 0) (x 1) - partialT (partialT D.B) (x 0) (x 1)) +
        4 * D.A (x 0) (x 1) ^ 2 * partialR D.B (x 0) (x 1)) /
        (4 * x 1 * D.A (x 0) (x 1) ^ 2 * D.B (x 0) (x 1)) :=
  ricci_one_one hx

example (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 2 2 =
      x 1 * partialR D.B (x 0) (x 1) / (2 * D.B (x 0) (x 1) ^ 2) -
        x 1 * partialR D.A (x 0) (x 1) / (2 * D.A (x 0) (x 1) * D.B (x 0) (x 1)) + 1 -
        1 / D.B (x 0) (x 1) :=
  ricci_two_two hx

example (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 3 3 =
      Real.sin (x 2) ^ 2 * ricciOf (metric D).coefficient x 2 2 :=
  ricci_three_three hx

example (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 0 2 = 0 :=
  ricci_zero_two hx

example (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 2 0 = 0 :=
  ricci_two_zero hx

example (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 0 3 = 0 :=
  ricci_zero_three hx

example (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 3 0 = 0 :=
  ricci_three_zero hx

example (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 1 2 = 0 :=
  ricci_one_two hx

example (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 2 1 = 0 :=
  ricci_two_one hx

example (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 1 3 = 0 :=
  ricci_one_three hx

example (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 3 1 = 0 :=
  ricci_three_one hx

example (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 2 3 = 0 :=
  ricci_two_three hx

example (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 3 2 = 0 :=
  ricci_three_two hx

example (hx : x ∈ domain D) :
    ((metric D).coefficient x)⁻¹ = Matrix.diagonal fun l => (coefficients D x l)⁻¹ :=
  coefficient_metric_inv hx

example (hx : x ∈ domain D) :
    scalarOf (metric D).coefficient x = ∑ a, ricci D x a a / coefficients D x a :=
  scalarOf_eq hx

example (x : MinkowskiModel 3) :
    Fin 4 → Fin 4 → ℝ :=
  einstein D x

example (hx : x ∈ domain D) (i k : Fin 4) :
    einsteinOf (metric D).coefficient x i k = einstein D x i k :=
  einsteinOf_eq hx i k

example (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 0 0 =
      D.A (x 0) (x 1) / x 1 ^ 2 * (1 - 1 / D.B (x 0) (x 1) +
        x 1 * partialR D.B (x 0) (x 1) / D.B (x 0) (x 1) ^ 2) :=
  einstein_zero_zero hx

example (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 0 1 =
      partialT D.B (x 0) (x 1) / (x 1 * D.B (x 0) (x 1)) :=
  einstein_zero_one hx

example (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 1 0 =
      partialT D.B (x 0) (x 1) / (x 1 * D.B (x 0) (x 1)) :=
  einstein_one_zero hx

example (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 1 1 =
      partialR D.A (x 0) (x 1) / (x 1 * D.A (x 0) (x 1)) - (D.B (x 0) (x 1) - 1) / x 1 ^ 2 :=
  einstein_one_one hx

example (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 2 2 =
      x 1 / (4 * D.A (x 0) (x 1) ^ 2 * D.B (x 0) (x 1) ^ 2) *
        (2 * x 1 * D.A (x 0) (x 1) * D.B (x 0) (x 1) * partialR (partialR D.A) (x 0) (x 1) -
          2 * x 1 * D.A (x 0) (x 1) * D.B (x 0) (x 1) * partialT (partialT D.B) (x 0) (x 1) -
          x 1 * D.A (x 0) (x 1) * partialR D.A (x 0) (x 1) * partialR D.B (x 0) (x 1) +
          x 1 * D.A (x 0) (x 1) * partialT D.B (x 0) (x 1) ^ 2 -
          x 1 * D.B (x 0) (x 1) * partialR D.A (x 0) (x 1) ^ 2 +
          x 1 * D.B (x 0) (x 1) * partialT D.A (x 0) (x 1) * partialT D.B (x 0) (x 1) -
          2 * D.A (x 0) (x 1) ^ 2 * partialR D.B (x 0) (x 1) +
          2 * D.A (x 0) (x 1) * D.B (x 0) (x 1) * partialR D.A (x 0) (x 1)) :=
  einstein_two_two hx

example (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 3 3 =
      Real.sin (x 2) ^ 2 * einsteinOf (metric D).coefficient x 2 2 :=
  einstein_three_three hx

example (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 0 2 = 0 :=
  einstein_zero_two hx

example (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 2 0 = 0 :=
  einstein_two_zero hx

example (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 0 3 = 0 :=
  einstein_zero_three hx

example (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 3 0 = 0 :=
  einstein_three_zero hx

example (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 1 2 = 0 :=
  einstein_one_two hx

example (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 2 1 = 0 :=
  einstein_two_one hx

example (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 1 3 = 0 :=
  einstein_one_three hx

example (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 3 1 = 0 :=
  einstein_three_one hx

example (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 2 3 = 0 :=
  einstein_two_three hx

example (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 3 2 = 0 :=
  einstein_three_two hx

example (hx : x ∈ domain D) :
    partialR (fun t r => D.A t r * D.B t r) (x 0) (x 1) =
      partialR D.A (x 0) (x 1) * D.B (x 0) (x 1) +
        D.A (x 0) (x 1) * partialR D.B (x 0) (x 1) :=
  partialR_mul hx

example (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 0 0 / D.A (x 0) (x 1) +
        einsteinOf (metric D).coefficient x 1 1 / D.B (x 0) (x 1) =
      partialR (fun t r => D.A t r * D.B t r) (x 0) (x 1) /
        (x 1 * D.A (x 0) (x 1) * D.B (x 0) (x 1) ^ 2) :=
  einstein_zero_zero_div_add_one_one_div hx

example (c : ℝ) :
    partialT (fun _ _ => c) = fun _ _ => 0 :=
  partialT_const c

example (c : ℝ) :
    partialR (fun _ _ => c) = fun _ _ => 0 :=
  partialR_const c

example (hx : x ∈ domain Data.flat) (j k : Fin 4) :
    ricciOf (metric Data.flat).coefficient x j k = 0 :=
  ricciOf_flat hx j k

example (hx : x ∈ domain Data.flat) (i k : Fin 4) :
    einsteinOf (metric Data.flat).coefficient x i k = 0 :=
  einsteinOf_flat hx i k

end ProjectAinos.GeneralRelativity.SphericalAnsatz

end SphericalAnsatz

section EddingtonFinkelstein


open ContinuousLinearMap Set Filter TopologicalSpace

open scoped Manifold ContDiff Topology

namespace ProjectAinos.GeneralRelativity.EddingtonFinkelstein

open SmoothGeometry Minkowski

open LorentzMetric (chartField curveVelocity)

open CoordinateMetric (physicalChart christoffelOf ricciOf ricciOfChristoffel)

variable {M : ℝ}

example :
    Opens (MinkowskiModel 3) :=
  domain

example (M : ℝ) (x : MinkowskiModel 3) :
    MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 →L[ℝ] ℝ :=
  form M x

example (x v w : MinkowskiModel 3) :
    form M x v w = -(1 - 2 * M / x 1) * (v 0 * w 0) + v 0 * w 1 + v 1 * w 0 +
      x 1 ^ 2 * (v 2 * w 2) + x 1 ^ 2 * Real.sin (x 2) ^ 2 * (v 3 * w 3) :=
  form_apply x v w

example (x v w : MinkowskiModel 3) :
    form M x v w = form M x w v :=
  form_symm x v w

example :
    ContDiffOn ℝ ∞ (form M) domain :=
  contDiffOn_form

example (a b : ℝ) (h : 1 + a * b ≠ 0) :
    MinkowskiModel 3 ≃ₗ[ℝ] MinkowskiModel 3 :=
  frameLinear a b h

example (a b : ℝ) (h : 1 + a * b ≠ 0) :
    MinkowskiModel 3 ≃L[ℝ] MinkowskiModel 3 :=
  frame a b h

example (a b : ℝ) (h : 1 + a * b ≠ 0) (v : MinkowskiModel 3) :
    frame a b h v = ![v 0 + b * v 1, v 1 - a * v 0, v 2, v 3] :=
  frame_apply a b h v

example (M : ℝ) (x : MinkowskiModel 3) :
    ℝ :=
  frameTime M x

example (M : ℝ) (x : MinkowskiModel 3) :
    ℝ :=
  frameSpace M x

example {x : MinkowskiModel 3} (hx : x ∈ domain) :
    frameTime M x = 1 + |M| / x 1 :=
  frameTime_eq hx

example (M : ℝ) (x : MinkowskiModel 3) :
    0 < frameTime M x :=
  frameTime_pos M x

example (M : ℝ) (x : MinkowskiModel 3) :
    0 < frameSpace M x :=
  frameSpace_pos M x

example (M : ℝ) (x : MinkowskiModel 3) :
    1 + frameTime M x * frameSpace M x ≠ 0 :=
  frame_det_ne_zero M x

example (M : ℝ) (x : MinkowskiModel 3) :
    MinkowskiModel 3 ≃L[ℝ] MinkowskiModel 3 :=
  pointFrame M x

example (x : MinkowskiModel 3) :
    form M x (pointFrame M x (Fin.cons 1 (0 : Fin 3 → ℝ)))
        (pointFrame M x (Fin.cons 1 (0 : Fin 3 → ℝ))) =
      -(1 - 2 * M / x 1) - 2 * frameTime M x :=
  form_pointFrame_time x

example (x : MinkowskiModel 3) (v : Fin 3 → ℝ) :
    form M x (pointFrame M x (Fin.cons 0 v)) (pointFrame M x (Fin.cons 0 v)) =
      frameSpace M x * (2 - frameSpace M x * (1 - 2 * M / x 1)) * (v 0 * v 0) +
        x 1 ^ 2 * (v 1 * v 1) + x 1 ^ 2 * Real.sin (x 2) ^ 2 * (v 2 * v 2) :=
  form_pointFrame_space x v

example (M : ℝ) :
    CoordinateMetric .timeNegative 3 domain :=
  metric M

example (x : MinkowskiModel 3) :
    (metric M).form x = form M x :=
  metric_form x

example (x : MinkowskiModel 3) (i j : Fin 4) :
    (metric M).coefficient x i j = form M x (Pi.single i 1) (Pi.single j 1) :=
  coefficient_apply x i j

example (f : Fin (3 + 1) → ℝ) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 :=
  sum_four f

example {F : ℝ → ℝ} {F' : ℝ} {y : MinkowskiModel 3} (hF : HasDerivAt F F' (y 1)) :
    HasFDerivAt (fun z : MinkowskiModel 3 => F (z 1))
      (F' • (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ)) y :=
  hasFDerivAt_radial hF

example {G : ℝ → ℝ} {G' : ℝ} {y : MinkowskiModel 3} (hG : HasDerivAt G G' (y 2)) :
    HasFDerivAt (fun z : MinkowskiModel 3 => G (z 2))
      (G' • (proj 2 : MinkowskiModel 3 →L[ℝ] ℝ)) y :=
  hasFDerivAt_angular hG

example {z : MinkowskiModel 3} (hz : z 1 ≠ 0) (v u : MinkowskiModel 3) :
    HasFDerivAt (fun x => form M x v u)
      ((-(2 * M / z 1 ^ 2) * (v 0 * u 0) + 2 * z 1 * (v 2 * u 2) +
          2 * z 1 * Real.sin (z 2) ^ 2 * (v 3 * u 3)) • (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ) +
        (z 1 ^ 2 * (2 * Real.sin (z 2) * Real.cos (z 2)) * (v 3 * u 3)) •
          (proj 2 : MinkowskiModel 3 →L[ℝ] ℝ)) z :=
  hasFDerivAt_form_apply hz v u

example {z : MinkowskiModel 3} (hz : z 1 ≠ 0) (v u w : MinkowskiModel 3) :
    fderiv ℝ (fun x => form M x v u) z w =
      w 1 * (-(2 * M / z 1 ^ 2) * (v 0 * u 0) + 2 * z 1 * (v 2 * u 2) +
          2 * z 1 * Real.sin (z 2) ^ 2 * (v 3 * u 3)) +
        w 2 * (z 1 ^ 2 * (2 * Real.sin (z 2) * Real.cos (z 2)) * (v 3 * u 3)) :=
  fderiv_form_apply hz v u w

example (M : ℝ) (x : MinkowskiModel 3) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  christoffel M x

example {x : MinkowskiModel 3} (hx : x ∈ domain) (k i j : Fin 4) :
    christoffelOf (metric M).coefficient x k i j = christoffel M x k i j :=
  christoffelOf_eq hx k i j

example (M : ℝ) (x : MinkowskiModel 3) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  christoffelRadial M x

example (M : ℝ) (x : MinkowskiModel 3) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  christoffelAngular M x

example {F : ℝ → ℝ} {F' A B : ℝ} {y : MinkowskiModel 3} (hF : HasDerivAt F F' (y 1)) (hA : F' = A)
    (hB : B = 0) :
    HasFDerivAt (fun z : MinkowskiModel 3 => F (z 1))
      (A • (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ) + B • (proj 2 : MinkowskiModel 3 →L[ℝ] ℝ)) y :=
  hasFDerivAt_radial_of_eq hF hA hB

example {G : ℝ → ℝ} {G' A B : ℝ} {y : MinkowskiModel 3} (hG : HasDerivAt G G' (y 2)) (hA : A = 0)
    (hB : G' = B) :
    HasFDerivAt (fun z : MinkowskiModel 3 => G (z 2))
      (A • (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ) + B • (proj 2 : MinkowskiModel 3 →L[ℝ] ℝ)) y :=
  hasFDerivAt_angular_of_eq hG hA hB

example {F G : ℝ → ℝ} {F' G' A B : ℝ} {y : MinkowskiModel 3} (hF : HasDerivAt F F' (y 1))
    (hG : HasDerivAt G G' (y 2)) (hA : F' * G (y 2) = A) (hB : F (y 1) * G' = B) :
    HasFDerivAt (fun z : MinkowskiModel 3 => F (z 1) * G (z 2))
      (A • (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ) + B • (proj 2 : MinkowskiModel 3 →L[ℝ] ℝ)) y :=
  hasFDerivAt_radial_mul_angular hF hG hA hB

example {A B : ℝ} {y : MinkowskiModel 3} (hA : A = 0) (hB : B = 0) :
    HasFDerivAt (fun _ : MinkowskiModel 3 => (0 : ℝ))
      (A • (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ) + B • (proj 2 : MinkowskiModel 3 →L[ℝ] ℝ)) y :=
  hasFDerivAt_zero_of_eq hA hB

example {y : MinkowskiModel 3} (hy : y ∈ domain) (a b c : Fin 4) :
    HasFDerivAt (fun z => christoffel M z a b c)
      (christoffelRadial M y a b c • (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ) +
        christoffelAngular M y a b c • (proj 2 : MinkowskiModel 3 →L[ℝ] ℝ)) y :=
  hasFDerivAt_christoffel hy a b c

example {y : MinkowskiModel 3} (hy : y ∈ domain) (a b c : Fin 4) (w : MinkowskiModel 3) :
    fderiv ℝ (fun z => christoffel M z a b c) y w =
      w 1 * christoffelRadial M y a b c + w 2 * christoffelAngular M y a b c :=
  fderiv_christoffel hy a b c w

example {y : MinkowskiModel 3} (hy : y ∈ domain) (j k : Fin 4) :
    ricciOfChristoffel (christoffel M) y j k = 0 :=
  ricciOfChristoffel_eq_zero hy j k

example {x : MinkowskiModel 3} (hx : x ∈ domain) (j k : Fin 4) :
    ricciOf (metric M).coefficient x j k = 0 :=
  ricciOf_eq_zero hx j k

example (x y : domain) (j k : Fin 4) :
    (metric M).toLorentzMetric.ricci y (chartField (physicalChart x) (Pi.single j 1) y)
      (chartField (physicalChart x) (Pi.single k 1) y) = 0 :=
  ricci_chartField x y j k

example (y : domain) (u w : TangentSpace 𝓘(ℝ, MinkowskiModel 3) y) :
    (metric M).toLorentzMetric.ricci y u w = 0 :=
  ricci_eq_zero y u w

example (v₀ r₀ θ₀ φ₀ : ℝ) (hr₀ : 0 < r₀) (hθ : θ₀ ∈ Ioo 0 Real.pi) (t : ℝ) :
    domain :=
  ingoingRay v₀ r₀ θ₀ φ₀ hr₀ hθ t

example {v₀ r₀ θ₀ φ₀ : ℝ} (hr₀ : 0 < r₀) (hθ : θ₀ ∈ Ioo 0 Real.pi) {t : ℝ} (ht : t < r₀) :
    (ingoingRay v₀ r₀ θ₀ φ₀ hr₀ hθ t : MinkowskiModel 3) = ![v₀, r₀ - t, θ₀, φ₀] :=
  ingoingRay_val hr₀ hθ ht

example {v₀ r₀ θ₀ φ₀ : ℝ} (hr₀ : 0 < r₀) (hθ : θ₀ ∈ Ioo 0 Real.pi) {t : ℝ} (ht : t < r₀) :
    (ingoingRay v₀ r₀ θ₀ φ₀ hr₀ hθ t : MinkowskiModel 3) =
      ![v₀, r₀, θ₀, φ₀] + t • ![0, -1, 0, 0] :=
  ingoingRay_eq_line hr₀ hθ ht

example {v₀ r₀ θ₀ φ₀ : ℝ} (hr₀ : 0 < r₀) (hθ : θ₀ ∈ Ioo 0 Real.pi) {t : ℝ} (ht : t < r₀) :
    HasDerivAt (fun t => (ingoingRay v₀ r₀ θ₀ φ₀ hr₀ hθ t : MinkowskiModel 3))
      (![0, -1, 0, 0] : MinkowskiModel 3) t :=
  ingoingRay_deriv hr₀ hθ ht

example (M v₀ r₀ θ₀ φ₀ : ℝ) (hr₀ : 0 < r₀) (hθ : θ₀ ∈ Ioo 0 Real.pi) :
    (metric M).toLorentzMetric.IsGeodesicOn (Iio r₀) (ingoingRay v₀ r₀ θ₀ φ₀ hr₀ hθ) :=
  isGeodesicOn_ingoing M v₀ r₀ θ₀ φ₀ hr₀ hθ

example (M : ℝ) {v₀ r₀ θ₀ φ₀ : ℝ} (hr₀ : 0 < r₀) (hθ : θ₀ ∈ Ioo 0 Real.pi) {t : ℝ}
    (ht : t ∈ Iio r₀) :
    (metric M).toLorentzMetric.form (ingoingRay v₀ r₀ θ₀ φ₀ hr₀ hθ t)
      (curveVelocity (ingoingRay v₀ r₀ θ₀ φ₀ hr₀ hθ) t)
      (curveVelocity (ingoingRay v₀ r₀ θ₀ φ₀ hr₀ hθ) t) = 0 :=
  form_ingoingRay_velocity M hr₀ hθ ht

example {v₀ r₀ θ₀ φ₀ : ℝ} (hr₀ : 0 < r₀) (hθ : θ₀ ∈ Ioo 0 Real.pi) (hM : 0 < M) (h : 2 * M < r₀) :
    2 * M < (ingoingRay v₀ r₀ θ₀ φ₀ hr₀ hθ 0 : MinkowskiModel 3) 1 ∧
      ∃ t ∈ Iio r₀, (ingoingRay v₀ r₀ θ₀ φ₀ hr₀ hθ t : MinkowskiModel 3) 1 = r₀ - t ∧
        r₀ - t < 2 * M :=
  exists_ingoingRay_lt hr₀ hθ hM h

example {x : MinkowskiModel 3} (hx : x ∈ domain) (hr : x 1 < 2 * M) {u : MinkowskiModel 3}
    (hu : form M x u u ≤ 0) (hu₀ : 0 < u 0) :
    u 1 < 0 :=
  radial_lt_zero_of_causal hx hr hu hu₀

example (M : ℝ) (x : MinkowskiModel 3) :
    MinkowskiModel 3 :=
  toEddington M x

example (M : ℝ) (x : MinkowskiModel 3) :
    MinkowskiModel 3 →ₗ[ℝ] MinkowskiModel 3 :=
  toEddingtonLinear M x

example (M : ℝ) (x : MinkowskiModel 3) :
    MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 :=
  toEddingtonDeriv M x

example (x v : MinkowskiModel 3) :
    toEddingtonDeriv M x v = ![v 0 + v 1 / (1 - 2 * M / x 1), v 1, v 2, v 3] :=
  toEddingtonDeriv_apply x v

example (hM : 0 ≤ M) {x : MinkowskiModel 3} (hx : x ∈ SchwarzschildExterior.domain M) :
    toEddington M x ∈ domain :=
  toEddington_mem hM hx

example (hM : 0 < M) {x : MinkowskiModel 3} (hx : 2 * M < x 1) :
    HasFDerivAt (toEddington M) (toEddingtonDeriv M x) x :=
  hasFDerivAt_toEddington hM hx

example {x : MinkowskiModel 3} (h0 : 0 < x 1) (hx : 2 * M < x 1) (v w : MinkowskiModel 3) :
    form M (toEddington M x) (toEddingtonDeriv M x v) (toEddingtonDeriv M x w) =
      SchwarzschildExterior.form M x v w :=
  form_toEddington h0 hx v w

end ProjectAinos.GeneralRelativity.EddingtonFinkelstein

end EddingtonFinkelstein

section SchwarzschildVacuum


open ContinuousLinearMap Set

open scoped Manifold ContDiff

namespace ProjectAinos.GeneralRelativity.SchwarzschildExterior

open SmoothGeometry Minkowski

open LorentzMetric (chartField)

open CoordinateMetric (physicalChart ricciOf scalarOf einsteinOf)

open SphericalAnsatz (partialT partialR)

variable {M : ℝ}

example (hM : 0 ≤ M) :
    SphericalAnsatz.Data :=
  ansatzData hM

example (hM : 0 ≤ M) :
    SphericalAnsatz.domain (ansatzData hM) = domain M :=
  domain_ansatzData hM

example (hM : 0 ≤ M) {x : MinkowskiModel 3} (hx : x ∈ domain M) :
    x ∈ SphericalAnsatz.domain (ansatzData hM) :=
  mem_ansatzDomain hM hx

example (hM : 0 ≤ M) :
    diagonalCoefficients M = SphericalAnsatz.coefficients (ansatzData hM) :=
  diagonalCoefficients_eq_coefficients hM

example (hM : 0 ≤ M) :
    (metric hM).coefficient = (SphericalAnsatz.metric (ansatzData hM)).coefficient :=
  coefficient_eq_ansatz hM

example (hM : 0 ≤ M) :
    partialT (ansatzData hM).A = fun _ _ => 0 :=
  partialT_ansatzA hM

example (hM : 0 ≤ M) :
    partialT (ansatzData hM).B = fun _ _ => 0 :=
  partialT_ansatzB hM

example (hM : 0 ≤ M) (t : ℝ) {r : ℝ} (hr : r ≠ 0) :
    partialR (ansatzData hM).A t r = 2 * M / r ^ 2 :=
  partialR_ansatzA hM t hr

example (hM : 0 ≤ M) (t : ℝ) {r : ℝ} (hr : r ≠ 2 * M) :
    partialR (ansatzData hM).B t r = -(2 * M) / (r - 2 * M) ^ 2 :=
  partialR_ansatzB hM t hr

example (hM : 0 ≤ M) (t : ℝ) {r : ℝ} (hr : r ≠ 0) :
    partialR (partialR (ansatzData hM).A) t r = -(4 * M) / r ^ 3 :=
  partialR_partialR_ansatzA hM t hr

example (hM : 0 ≤ M) (t : ℝ) {r : ℝ} (hr : r ≠ 2 * M) :
    partialR (partialR (ansatzData hM).B) t r = 4 * M / (r - 2 * M) ^ 3 :=
  partialR_partialR_ansatzB hM t hr

example (hM : 0 ≤ M) :
    partialT (partialT (ansatzData hM).A) = fun _ _ => 0 :=
  partialT_partialT_ansatzA hM

example (hM : 0 ≤ M) :
    partialT (partialT (ansatzData hM).B) = fun _ _ => 0 :=
  partialT_partialT_ansatzB hM

example (hM : 0 ≤ M) :
    partialT (partialR (ansatzData hM).A) = fun _ _ => 0 :=
  partialT_partialR_ansatzA hM

example (hM : 0 ≤ M) :
    partialT (partialR (ansatzData hM).B) = fun _ _ => 0 :=
  partialT_partialR_ansatzB hM

example (hM : 0 ≤ M) {x : MinkowskiModel 3} (hx : x ∈ domain M) (j k : Fin 4) :
    ricciOf (metric hM).coefficient x j k = 0 :=
  ricciOf_eq_zero hM hx j k

example (hM : 0 ≤ M) {x : MinkowskiModel 3} (hx : x ∈ domain M) :
    scalarOf (metric hM).coefficient x = 0 :=
  scalarOf_eq_zero hM hx

example (hM : 0 ≤ M) {x : MinkowskiModel 3} (hx : x ∈ domain M) (i k : Fin 4) :
    einsteinOf (metric hM).coefficient x i k = 0 :=
  einsteinOf_eq_zero hM hx i k

example (hM : 0 ≤ M) (κ : ℝ) :
    (metric hM).IsEinstein κ 0 0 :=
  isEinstein_zero hM κ

example (hM : 0 ≤ M) (x y : domain M) (i k : Fin 4) :
    (metric hM).toLorentzMetric.einstein y (chartField (physicalChart x) (Pi.single i 1) y)
      (chartField (physicalChart x) (Pi.single k 1) y) = 0 :=
  einstein_chartField hM x y i k

example (hM : 0 ≤ M) (κ : ℝ) :
    (metric hM).toLorentzMetric.SatisfiesEinstein κ 0 0 :=
  satisfiesEinstein_zero hM κ

example (hM : 0 ≤ M) (x y : domain M) (j k : Fin 4) :
    (metric hM).toLorentzMetric.ricci y (chartField (physicalChart x) (Pi.single j 1) y)
      (chartField (physicalChart x) (Pi.single k 1) y) = 0 :=
  ricci_chartField hM x y j k

example (hM : 0 ≤ M) (y : domain M) (u w : TangentSpace 𝓘(ℝ, MinkowskiModel 3) y) :
    (metric hM).toLorentzMetric.ricci y u w = 0 :=
  ricci_eq_zero hM y u w

example {t r : ℝ} (hr : r ∈ (ansatzData (le_refl (0 : ℝ))).J) :
    (ansatzData (le_refl (0 : ℝ))).A t r = 1 :=
  ansatzData_zero_A hr

example {t r : ℝ} (hr : r ∈ (ansatzData (le_refl (0 : ℝ))).J) :
    (ansatzData (le_refl (0 : ℝ))).B t r = 1 :=
  ansatzData_zero_B hr

example :
    (ansatzData (le_refl (0 : ℝ))).I = SphericalAnsatz.Data.flat.I ∧
      (ansatzData (le_refl (0 : ℝ))).J = SphericalAnsatz.Data.flat.J :=
  ansatzData_zero_sets

example :
    domain 0 = SphericalAnsatz.domain SphericalAnsatz.Data.flat :=
  domain_zero

example {x : MinkowskiModel 3} (hx : x ∈ domain 0) :
    (metric (le_refl (0 : ℝ))).coefficient x =
      (SphericalAnsatz.metric SphericalAnsatz.Data.flat).coefficient x :=
  coefficient_zero hx

end ProjectAinos.GeneralRelativity.SchwarzschildExterior

end SchwarzschildVacuum

section Birkhoff


open ContinuousLinearMap Set Filter

open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.SphericalAnsatz

open SmoothGeometry CoordinateMetric

variable {D : Data}

example {x : MinkowskiModel 3} (h : ∀ j k, ricciOf (metric D).coefficient x j k = 0) (i k : Fin 4) :
    einsteinOf (metric D).coefficient x i k = 0 :=
  einsteinOf_eq_zero_of_ricciOf h i k

example (t r : ℝ) :
    MinkowskiModel 3 :=
  equatorialPoint t r

example {t r : ℝ} (ht : t ∈ D.I) (hr : r ∈ D.J) :
    equatorialPoint t r ∈ domain D :=
  equatorialPoint_mem ht hr

example (hvac : ∀ x ∈ domain D, ∀ j k, ricciOf (metric D).coefficient x j k = 0) {t r : ℝ}
    (ht : t ∈ D.I) (hr : r ∈ D.J) :
    partialT D.B t r = 0 :=
  partialT_B_eq_zero_of_vacuum hvac ht hr

example (hvac : ∀ x ∈ domain D, ∀ j k, ricciOf (metric D).coefficient x j k = 0) {t r : ℝ}
    (ht : t ∈ D.I) (hr : r ∈ D.J) :
    1 - 1 / D.B t r + r * partialR D.B t r / D.B t r ^ 2 = 0 :=
  one_sub_inv_add_eq_zero_of_vacuum hvac ht hr

example (hvac : ∀ x ∈ domain D, ∀ j k, ricciOf (metric D).coefficient x j k = 0) {t r : ℝ}
    (ht : t ∈ D.I) (hr : r ∈ D.J) :
    partialR D.A t r * D.B t r + D.A t r * partialR D.B t r = 0 :=
  partialR_mul_eq_zero_of_vacuum hvac ht hr

example (D : Data) (hI : IsPreconnected D.I) (hJ : IsPreconnected D.J)
    (hvac : ∀ x ∈ domain D, ∀ j k, ricciOf (metric D).coefficient x j k = 0) :
    ∃ M : ℝ, (∀ r ∈ D.J, 2 * M < r) ∧ ∃ f : ℝ → ℝ, ContDiffOn ℝ ∞ f D.I ∧
      (∀ t ∈ D.I, 0 < f t) ∧
      ∀ t ∈ D.I, ∀ r ∈ D.J, D.B t r = r / (r - 2 * M) ∧ D.A t r = f t * ((r - 2 * M) / r) :=
  birkhoff D hI hJ hvac

example (M : ℝ) (f : ℝ → ℝ) (t r : ℝ) :
    ℝ :=
  schwarzschildA M f t r

example (M : ℝ) (_t r : ℝ) :
    ℝ :=
  schwarzschildB M _t r

example (M : ℝ) (I J : Set ℝ) (hI : IsOpen I) (hJ : IsOpen J) (hJM : ∀ r ∈ J, 0 < r ∧ 2 * M < r)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ ∞ f I) (hfpos : ∀ t ∈ I, 0 < f t) :
    Data :=
  schwarzschildData M I J hI hJ hJM f hf hfpos

variable {M : ℝ} {f : ℝ → ℝ}

example :
    partialT (schwarzschildB M) = fun _ _ => 0 :=
  partialT_schwarzschildB

example {t r : ℝ} (hr : r - 2 * M ≠ 0) :
    partialR (schwarzschildB M) t r = -(2 * M) / (r - 2 * M) ^ 2 :=
  partialR_schwarzschildB hr

example {t r : ℝ} (hr : r ≠ 0) :
    partialR (schwarzschildA M f) t r = f t * (2 * M / r ^ 2) :=
  partialR_schwarzschildA hr

example {t r : ℝ} (hr : r ≠ 0) :
    partialR (partialR (schwarzschildA M f)) t r = f t * (-(4 * M) / r ^ 3) :=
  partialR_partialR_schwarzschildA hr

section SchwarzschildData

variable {I J : Set ℝ} {hI : IsOpen I} {hJ : IsOpen J} {hJM : ∀ r ∈ J, 0 < r ∧ 2 * M < r}
  {hf : ContDiffOn ℝ ∞ f I} {hfpos : ∀ t ∈ I, 0 < f t}

example {x : MinkowskiModel 3} (hx : x ∈ domain (schwarzschildData M I J hI hJ hJM f hf hfpos))
    (j k : Fin 4) :
    ricciOf (metric (schwarzschildData M I J hI hJ hJM f hf hfpos)).coefficient x j k = 0 :=
  ricciOf_schwarzschildData hx j k

example (T : ℝ → ℝ) (x : MinkowskiModel 3) :
    MinkowskiModel 3 :=
  timeChange T x

example (f : ℝ → ℝ) (x : MinkowskiModel 3) :
    MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 :=
  timeChangeDeriv f x

example (f : ℝ → ℝ) (x v : MinkowskiModel 3) :
    timeChangeDeriv f x v = ![Real.sqrt (f (x 0)) * v 0, v 1, v 2, v 3] :=
  timeChangeDeriv_apply f x v

example {T : ℝ → ℝ} {x : MinkowskiModel 3} (hT : HasDerivAt T (Real.sqrt (f (x 0))) (x 0)) :
    HasFDerivAt (timeChange T) (timeChangeDeriv f x) x :=
  hasFDerivAt_timeChange hT

example (D : Data) {T : ℝ → ℝ} {x : MinkowskiModel 3}
    (hA : D.A (x 0) (x 1) = f (x 0) * ((x 1 - 2 * M) / x 1))
    (hB : D.B (x 0) (x 1) = x 1 / (x 1 - 2 * M)) (hf : 0 ≤ f (x 0)) (v w : MinkowskiModel 3) :
    (metric D).form x v w = SchwarzschildExterior.form M (timeChange T x)
      (timeChangeDeriv f x v) (timeChangeDeriv f x w) :=
  form_eq_timeChange D hA hB hf v w

example {D : Data} (hJM : ∀ r ∈ D.J, 2 * M < r) (T : ℝ → ℝ) {x : MinkowskiModel 3}
    (hx : x ∈ domain D) :
    timeChange T x ∈ SchwarzschildExterior.domain M :=
  timeChange_mem hJM T hx

example {I : Set ℝ} (hI : IsOpen I) (hI' : IsPreconnected I) (hf : ContinuousOn f I) :
    ∃ T : ℝ → ℝ, ∀ t ∈ I, HasDerivAt T (Real.sqrt (f t)) t :=
  exists_hasDerivAt_sqrt hI hI' hf

example (D : Data) (hI : IsPreconnected D.I) (hJ : IsPreconnected D.J)
    (hvac : ∀ x ∈ domain D, ∀ j k, ricciOf (metric D).coefficient x j k = 0) :
    ∃ M : ℝ, (∀ r ∈ D.J, 2 * M < r) ∧ ∃ f T : ℝ → ℝ,
      (∀ t ∈ D.I, 0 < f t ∧ HasDerivAt T (Real.sqrt (f t)) t) ∧
      ∀ x ∈ domain D, HasFDerivAt (timeChange T) (timeChangeDeriv f x) x ∧
        timeChange T x ∈ SchwarzschildExterior.domain M ∧
        ∀ v w, (metric D).form x v w = SchwarzschildExterior.form M (timeChange T x)
          (timeChangeDeriv f x v) (timeChangeDeriv f x w) :=
  birkhoff_timeChange D hI hJ hvac

example {T : ℝ → ℝ} {x : MinkowskiModel 3} (hx : x 0 ∈ I) (v w : MinkowskiModel 3) :
    (metric (schwarzschildData M I J hI hJ hJM f hf hfpos)).form x v w =
      SchwarzschildExterior.form M (timeChange T x) (timeChangeDeriv f x v)
        (timeChangeDeriv f x w) :=
  form_schwarzschildData hx v w

example {T : ℝ → ℝ} (hT : ∀ t ∈ I, HasDerivAt T (Real.sqrt (f t)) t) {x : MinkowskiModel 3}
    (hx : x ∈ domain (schwarzschildData M I J hI hJ hJM f hf hfpos)) :
    HasFDerivAt (timeChange T) (timeChangeDeriv f x) x ∧
      timeChange T x ∈ SchwarzschildExterior.domain M ∧
      ∀ v w, (metric (schwarzschildData M I J hI hJ hJM f hf hfpos)).form x v w =
        SchwarzschildExterior.form M (timeChange T x) (timeChangeDeriv f x v)
          (timeChangeDeriv f x w) :=
  timeChange_schwarzschildData hT hx

example (D : Data) (hI : D.I.Nonempty) (hJ : D.J.Nonempty) {M₁ M₂ : ℝ}
    (h₁ : ∀ t ∈ D.I, ∀ r ∈ D.J, D.B t r = r / (r - 2 * M₁))
    (h₂ : ∀ t ∈ D.I, ∀ r ∈ D.J, D.B t r = r / (r - 2 * M₂)) :
    M₁ = M₂ :=
  eq_of_B_eq D hI hJ h₁ h₂

example (hIne : I.Nonempty) (hJne : J.Nonempty) {M' : ℝ}
    (h : ∀ t ∈ I, ∀ r ∈ J,
      (schwarzschildData M I J hI hJ hJM f hf hfpos).B t r = r / (r - 2 * M')) :
    M' = M :=
  mass_schwarzschildData hIne hJne h

end SchwarzschildData

example (hM : 0 ≤ M) :
    Data :=
  exteriorData hM

example (hM : 0 ≤ M) {x : MinkowskiModel 3} (hx : x ∈ domain (exteriorData hM)) (j k : Fin 4) :
    ricciOf (metric (exteriorData hM)).coefficient x j k = 0 :=
  ricciOf_exteriorData hM hx j k

example (hM : 0 ≤ M) (x : MinkowskiModel 3) :
    (metric (exteriorData hM)).form x = SchwarzschildExterior.form M x :=
  form_exteriorData hM x

example (hM : 0 ≤ M) :
    ∃ M' : ℝ, M' = M ∧ (∀ r ∈ Ioi (2 * M), 2 * M' < r) ∧ ∃ f : ℝ → ℝ,
      ContDiffOn ℝ ∞ f univ ∧ (∀ t ∈ univ, 0 < f t) ∧
      ∀ t ∈ univ, ∀ r ∈ Ioi (2 * M), (exteriorData hM).B t r = r / (r - 2 * M') ∧
        (exteriorData hM).A t r = f t * ((r - 2 * M') / r) :=
  exists_birkhoff_exteriorData hM

example (hM : 0 ≤ M) :
    Data :=
  expTimeData hM

example (hM : 0 ≤ M) {x : MinkowskiModel 3} (hx : x ∈ domain (expTimeData hM)) (j k : Fin 4) :
    ricciOf (metric (expTimeData hM)).coefficient x j k = 0 :=
  ricciOf_expTimeData hM hx j k

example (t : ℝ) :
    HasDerivAt (fun s => 2 * Real.exp (s / 2)) (Real.sqrt (Real.exp t)) t :=
  hasDerivAt_expTime t

example (hM : 0 ≤ M) (x v w : MinkowskiModel 3) :
    (metric (expTimeData hM)).form x v w =
      SchwarzschildExterior.form M (timeChange (fun s => 2 * Real.exp (s / 2)) x)
        (timeChangeDeriv Real.exp x v) (timeChangeDeriv Real.exp x w) :=
  form_expTimeData hM x v w

example (hM : 0 ≤ M) :
    ∃ M' : ℝ, M' = M ∧ (∀ r ∈ Ioi (2 * M), 2 * M' < r) ∧ ∃ f : ℝ → ℝ,
      ContDiffOn ℝ ∞ f univ ∧ (∀ t ∈ univ, 0 < f t) ∧
      ∀ t ∈ univ, ∀ r ∈ Ioi (2 * M), (expTimeData hM).B t r = r / (r - 2 * M') ∧
        (expTimeData hM).A t r = f t * ((r - 2 * M') / r) :=
  exists_birkhoff_expTimeData hM

end ProjectAinos.GeneralRelativity.SphericalAnsatz

end Birkhoff
