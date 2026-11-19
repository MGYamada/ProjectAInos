/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Lorentzian.SpaceForm
import ProjectAinos.GeneralRelativity.FLRW
import ProjectAinos.GeneralRelativity.CosmologicalModels
import ProjectAinos.GeneralRelativity.CosmologicalRedshift

/-! Public consumers of isotropic cosmology (Landau–Lifshitz §§111–114): the spaces of constant
curvature in their conformally flat charts, with the embeddings into the sphere and the hyperboloid
and the volume of the closed space, and the isotropic metric with a lapse, the comoving perfect
fluid and the Friedmann equations, the exact closed, open and flat models with their cosmic time and
the perpetual expansion of open models, and the red shift of light. Default elaborator options are
intentional: these checks must not rely on the implementation's transparency settings. Every
statement is pinned with its type. -/

noncomputable section

section SpaceForm


open Set Filter MeasureTheory

open scoped Topology

namespace ProjectAinos.SmoothGeometry.SpaceForm

open CoordinateMetric

example (k : ℝ) (x : MinkowskiModel 2) :
    ℝ :=
  conformalFactor k x

example (k : ℝ) :
    Set (MinkowskiModel 2) :=
  domain k

example (k : ℝ) (x : MinkowskiModel 2) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  coefficient k x

example (k : ℝ) (x : MinkowskiModel 2) (i j : Fin 3) :
    coefficient k x i j = if i = j then (conformalFactor k x)⁻¹ ^ 2 else 0 :=
  coefficient_apply k x i j

example (k c : ℝ) (x : MinkowskiModel 2) :
    conformalFactor k (c • x) = conformalFactor (c ^ 2 * k) x :=
  conformalFactor_smul k c x

example {k : ℝ} (hk : 0 ≤ k) (x : MinkowskiModel 2) :
    0 < conformalFactor k x :=
  conformalFactor_pos_of_nonneg hk x

example {k : ℝ} (hk : k ≤ 0) (x : MinkowskiModel 2) :
    conformalFactor k x ≤ 1 :=
  conformalFactor_le_one hk x

example {k : ℝ} (hk : 0 ≤ k) :
    domain k = univ :=
  domain_eq_univ hk

example {k : ℝ} (hk : k < 0) :
    domain k = {x | ∑ i, x i ^ 2 < -4 / k} :=
  domain_of_neg hk

example (k : ℝ) (y : MinkowskiModel 2) :
    HasFDerivAt (conformalFactor k)
      ((k / 2) • ∑ i, y i • (ContinuousLinearMap.proj i : MinkowskiModel 2 →L[ℝ] ℝ)) y :=
  hasFDerivAt_conformalFactor k y

example (k : ℝ) (y v : MinkowskiModel 2) :
    fderiv ℝ (conformalFactor k) y v = k / 2 * ∑ i, y i * v i :=
  fderiv_conformalFactor k y v

example (k : ℝ) :
    Continuous (conformalFactor k) :=
  continuous_conformalFactor k

example (k : ℝ) :
    IsOpen (domain k) :=
  isOpen_domain k

example (k : ℝ) {x : MinkowskiModel 2} (hx : x ∈ domain k) :
    (coefficient k x).PosDef :=
  posDef_coefficient k hx

example (k : ℝ) {x : MinkowskiModel 2} (hx : x ∈ domain k) :
    densityOf (coefficient k) x = (conformalFactor k x)⁻¹ ^ 3 :=
  densityOf_coefficient k hx

example (k : ℝ) {y : MinkowskiModel 2} (hy : conformalFactor k y ≠ 0) :
    HasFDerivAt (fun z => (conformalFactor k z)⁻¹)
      ((-(conformalFactor k y ^ 2)⁻¹) •
        (k / 2) • ∑ i, y i • (ContinuousLinearMap.proj i : MinkowskiModel 2 →L[ℝ] ℝ)) y :=
  hasFDerivAt_inv_conformalFactor k hy

example (k : ℝ) {y : MinkowskiModel 2} (hy : conformalFactor k y ≠ 0) (v : MinkowskiModel 2) :
    fderiv ℝ (fun z => (conformalFactor k z)⁻¹ ^ 2) y v =
      -(k * (conformalFactor k y)⁻¹ ^ 3) * ∑ i, y i * v i :=
  fderiv_inv_conformalFactor_sq k hy v

example (k : ℝ) (x : MinkowskiModel 2) (l i j : Fin 3) :
    ℝ :=
  christoffel k x l i j

example (k : ℝ) {y : MinkowskiModel 2} (hy : conformalFactor k y ≠ 0) (l i j : Fin 3)
    (v : MinkowskiModel 2) :
    fderiv ℝ (fun z => christoffel k z l i j) y v =
      k ^ 2 / 4 * (conformalFactor k y)⁻¹ ^ 2 * (∑ a, y a * v a) *
          ((if l = j then y i else 0) + (if l = i then y j else 0) - (if i = j then y l else 0)) -
        k / 2 * (conformalFactor k y)⁻¹ *
          ((if l = j then v i else 0) + (if l = i then v j else 0) -
            (if i = j then v l else 0)) :=
  fderiv_christoffel k hy l i j v

example (k : ℝ) {x : MinkowskiModel 2} (hx : conformalFactor k x ≠ 0) (l i j : Fin 3) :
    christoffelOf (coefficient k) x l i j = christoffel k x l i j :=
  christoffelOf_eq_of_ne_zero k hx l i j

example (k : ℝ) {x : MinkowskiModel 2} (hx : x ∈ domain k) (l i j : Fin 3) :
    christoffelOf (coefficient k) x l i j = christoffel k x l i j :=
  christoffelOf_eq k hx l i j

example (k : ℝ) {x : MinkowskiModel 2} (hx : x ∈ domain k) :
    ∀ᶠ z in 𝓝 x, ∀ l i j, christoffelOf (coefficient k) z l i j = christoffel k z l i j :=
  eventually_christoffelOf_eq k hx

example (k : ℝ) {x : MinkowskiModel 2} (hx : x ∈ domain k) (l i j m : Fin 3) :
    curvatureOf (christoffel k) x l i j m =
      k * ((if l = i then coefficient k x j m else 0) -
        (if l = j then coefficient k x i m else 0)) :=
  curvatureOf_christoffel k hx l i j m

example (k : ℝ) {x : MinkowskiModel 2} (hx : x ∈ domain k) (l i j m : Fin 3) :
    curvatureOf (christoffelOf (coefficient k)) x l i j m =
      k * ((if l = i then coefficient k x j m else 0) -
        (if l = j then coefficient k x i m else 0)) :=
  curvatureOf_eq k hx l i j m

example (k : ℝ) {x : MinkowskiModel 2} (hx : x ∈ domain k) (j m : Fin 3) :
    ricciOf (coefficient k) x j m = 2 * k * coefficient k x j m :=
  ricciOf_eq k hx j m

example (k : ℝ) {x : MinkowskiModel 2} (hx : x ∈ domain k) :
    scalarOf (coefficient k) x = 6 * k :=
  scalarOf_eq k hx

example (k : ℝ) (x : MinkowskiModel 2) :
    MinkowskiModel 3 :=
  lift k x

example (k : ℝ) (x : MinkowskiModel 2) :
    lift k x 0 = 2 * (conformalFactor k x)⁻¹ - 1 :=
  lift_zero k x

example (k : ℝ) (x : MinkowskiModel 2) (a : Fin 3) :
    lift k x a.succ = x a * (conformalFactor k x)⁻¹ :=
  lift_succ k x a

example (x : MinkowskiModel 2) :
    lift 1 x 0 = (4 - ∑ i, x i ^ 2) / (4 + ∑ i, x i ^ 2) ∧
      ∀ a : Fin 3, lift 1 x a.succ = 4 * x a / (4 + ∑ i, x i ^ 2) :=
  lift_one_apply x

example {k : ℝ} (hk : k ^ 2 = 1) {x : MinkowskiModel 2} (hx : conformalFactor k x ≠ 0) :
    k * lift k x 0 ^ 2 + ∑ a : Fin 3, lift k x a.succ ^ 2 = k :=
  quadric_lift hk hx

example (X : MinkowskiModel 3) :
    MinkowskiModel 2 :=
  stereographic X

example (k : ℝ) {x : MinkowskiModel 2} (hx : conformalFactor k x ≠ 0) :
    stereographic (lift k x) = x :=
  stereographic_lift k hx

example {k : ℝ} (hk : k ^ 2 = 1) {X : MinkowskiModel 3}
    (hX : k * X 0 ^ 2 + ∑ a : Fin 3, X a.succ ^ 2 = k) (h : 1 + X 0 ≠ 0) :
    conformalFactor k (stereographic X) = 2 / (1 + X 0) :=
  conformalFactor_stereographic hk hX h

example {k : ℝ} (hk : k ^ 2 = 1) {X : MinkowskiModel 3}
    (hX : k * X 0 ^ 2 + ∑ a : Fin 3, X a.succ ^ 2 = k) (h : 1 + X 0 ≠ 0) :
    lift k (stereographic X) = X :=
  lift_stereographic hk hX h

example (k : ℝ) {x : MinkowskiModel 2} (hx : conformalFactor k x ≠ 0) :
    DifferentiableAt ℝ (lift k) x :=
  differentiableAt_lift k hx

example (k : ℝ) {x : MinkowskiModel 2} (hx : conformalFactor k x ≠ 0) :
    ContinuousAt (lift k) x :=
  continuousAt_lift k hx

example {S : Set (MinkowskiModel 3)} (hS : ∀ X ∈ S, 1 + X 0 ≠ 0) :
    Continuous fun X : S => stereographic X :=
  continuous_stereographic_on hS

example :
    Set (MinkowskiModel 3) :=
  sphere

example :
    MinkowskiModel 3 :=
  southPole

example (X : MinkowskiModel 3) :
    ∑ A, X A ^ 2 = 1 * X 0 ^ 2 + ∑ a : Fin 3, X a.succ ^ 2 :=
  sum_sq_eq_quadric X

example {X : MinkowskiModel 3} (hX : 1 * X 0 ^ 2 + ∑ a : Fin 3, X a.succ ^ 2 = 1) (h : X 0 = -1) :
    X = southPole :=
  eq_southPole hX h

example {X : MinkowskiModel 3} (hX : X ∈ sphere \ {southPole}) :
    1 + X 0 ≠ 0 :=
  one_add_ne_zero_of_mem_sphere hX

example (x : MinkowskiModel 2) :
    lift 1 x ∈ sphere :=
  lift_one_mem_sphere x

example (x : MinkowskiModel 2) :
    lift 1 x ≠ southPole :=
  lift_one_ne_southPole x

example :
    Function.Injective (lift 1) :=
  injective_lift_one

example :
    range (lift 1) = sphere \ {southPole} :=
  range_lift_one

example :
    Function.Injective (lift 1) ∧ range (lift 1) = sphere \ {southPole} :=
  sphere_embedding

example :
    MinkowskiModel 2 ≃ₜ ↥(sphere \ {southPole}) :=
  sphereHomeomorph

example :
    Set (MinkowskiModel 3) :=
  upperSheet

example (V W : MinkowskiModel 3) :
    minkowskiForm .timeNegative 3 V W = -1 * (V 0 * W 0) + ∑ a : Fin 3, V a.succ * W a.succ :=
  minkowskiForm_timeNegative_eq V W

example (X : MinkowskiModel 3) :
    minkowskiForm .timeNegative 3 X X = -1 * X 0 ^ 2 + ∑ a : Fin 3, X a.succ ^ 2 :=
  minkowskiForm_self_eq_quadric X

example {x : MinkowskiModel 2} (hx : x ∈ domain (-1)) :
    lift (-1) x ∈ upperSheet :=
  lift_neg_one_mem_upperSheet hx

example {X : MinkowskiModel 3} (hX : X ∈ upperSheet) :
    stereographic X ∈ domain (-1) :=
  stereographic_mem_domain hX

example :
    InjOn (lift (-1)) (domain (-1)) :=
  injOn_lift_neg_one

example :
    lift (-1) '' domain (-1) = upperSheet :=
  image_lift_neg_one

example :
    InjOn (lift (-1)) (domain (-1)) ∧ lift (-1) '' domain (-1) = upperSheet :=
  hyperboloid_embedding

example :
    ↥(domain (-1)) ≃ₜ ↥upperSheet :=
  hyperboloidHomeomorph

example (k : ℝ) {x : MinkowskiModel 2} (hx : conformalFactor k x ≠ 0) (v : MinkowskiModel 2) :
    fderiv ℝ (fun z => lift k z 0) x v =
      -(k * (conformalFactor k x)⁻¹ ^ 2) * ∑ i, x i * v i :=
  fderiv_lift_zero k hx v

example (k : ℝ) {x : MinkowskiModel 2} (hx : conformalFactor k x ≠ 0) (a : Fin 3)
    (v : MinkowskiModel 2) :
    fderiv ℝ (fun z => lift k z a.succ) x v =
      v a * (conformalFactor k x)⁻¹ -
        k / 2 * (conformalFactor k x)⁻¹ ^ 2 * x a * ∑ i, x i * v i :=
  fderiv_lift_succ k hx a v

example (k : ℝ) {x : MinkowskiModel 2} (hx : conformalFactor k x ≠ 0) (v : MinkowskiModel 2)
    (A : Fin 4) :
    fderiv ℝ (lift k) x v A = fderiv ℝ (fun z => lift k z A) x v :=
  fderiv_lift_apply k hx v A

example {k : ℝ} (hk : k ^ 3 = k) {x : MinkowskiModel 2} (hx : conformalFactor k x ≠ 0)
    (v w : MinkowskiModel 2) :
    k * (fderiv ℝ (lift k) x v 0 * fderiv ℝ (lift k) x w 0) +
        ∑ a : Fin 3, fderiv ℝ (lift k) x v a.succ * fderiv ℝ (lift k) x w a.succ =
      (conformalFactor k x)⁻¹ ^ 2 * ∑ i, v i * w i :=
  lift_pullback hk hx v w

example (x v w : MinkowskiModel 2) :
    ∑ A, fderiv ℝ (lift 1) x v A * fderiv ℝ (lift 1) x w A =
      (conformalFactor 1 x)⁻¹ ^ 2 * ∑ i, v i * w i :=
  sphere_pullback x v w

example (x : MinkowskiModel 2) (i j : Fin 3) :
    ∑ A, fderiv ℝ (lift 1) x (Pi.single i 1) A * fderiv ℝ (lift 1) x (Pi.single j 1) A =
      coefficient 1 x i j :=
  sphere_firstFundamentalForm x i j

example {x : MinkowskiModel 2} (hx : x ∈ domain (-1)) (v w : MinkowskiModel 2) :
    minkowskiForm .timeNegative 3 (fderiv ℝ (lift (-1)) x v) (fderiv ℝ (lift (-1)) x w) =
      (conformalFactor (-1) x)⁻¹ ^ 2 * ∑ i, v i * w i :=
  hyperboloid_pullback hx v w

example {x : MinkowskiModel 2} (hx : x ∈ domain (-1)) (i j : Fin 3) :
    minkowskiForm .timeNegative 3 (fderiv ℝ (lift (-1)) x (Pi.single i 1))
        (fderiv ℝ (lift (-1)) x (Pi.single j 1)) = coefficient (-1) x i j :=
  hyperboloid_firstFundamentalForm hx i j

example :
    ∫ x : MinkowskiModel 2, (conformalFactor 1 x)⁻¹ ^ 3 = 2 * Real.pi ^ 2 :=
  integral_inv_conformalFactor_pow_three

example {k : ℝ} (hk : 0 < k) :
    ∫ x : MinkowskiModel 2, (conformalFactor k x)⁻¹ ^ 3 = 2 * Real.pi ^ 2 / Real.sqrt k ^ 3 :=
  integral_inv_conformalFactor_pow_three_of_pos hk

example (k : ℝ) :
    conformalFactor k 0 = 1 :=
  conformalFactor_origin k

example (x : MinkowskiModel 2) :
    conformalFactor 0 x = 1 :=
  conformalFactor_flat x

example (k : ℝ) :
    (0 : MinkowskiModel 2) ∈ domain k :=
  zero_mem_domain k

example :
    domain (-1) = {x | ∑ i, x i ^ 2 < 4} :=
  domain_neg_one

example (k : ℝ) :
    coefficient k 0 = 1 :=
  coefficient_origin k

example (x : MinkowskiModel 2) :
    coefficient 0 x = 1 :=
  coefficient_flat x

example (k : ℝ) (l i j : Fin 3) :
    christoffel k 0 l i j = 0 :=
  christoffel_origin k l i j

example (x : MinkowskiModel 2) (l i j : Fin 3) :
    christoffel 0 x l i j = 0 :=
  christoffel_flat x l i j

example (k : ℝ) :
    lift k 0 = Pi.single 0 1 :=
  lift_origin k

example (x : MinkowskiModel 2) :
    lift 0 x = Fin.cons 1 x :=
  lift_flat x

example :
    curvatureOf (christoffelOf (coefficient 1)) 0 0 0 1 1 = 1 :=
  curvatureOf_sphere_origin

example :
    ricciOf (coefficient (-1)) 0 0 0 = -2 :=
  ricciOf_hyperbolic_origin

end ProjectAinos.SmoothGeometry.SpaceForm

end SpaceForm

section FLRW


open ContinuousLinearMap Set TopologicalSpace Filter

open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.FLRW

open SmoothGeometry CoordinateMetric

open LorentzMetric (chartField)

local notation "E" => MinkowskiModel 3

example {I : Set ℝ} {f : ℝ → ℝ} (hI : IsOpen I) (hf : ContDiffOn ℝ ∞ f I) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt f (deriv f t) t :=
  hasDerivAt_of_contDiffOn hI hf ht

example {I : Set ℝ} {f : ℝ → ℝ} (hI : IsOpen I) (hf : ContDiffOn ℝ ∞ f I) :
    ContDiffOn ℝ ∞ (deriv f) I :=
  contDiffOn_deriv_of_contDiffOn hI hf

example {f : ℝ → ℝ} {f' : ℝ} {x : E} (hf : HasDerivAt f f' (x 0)) :
    HasFDerivAt (fun z : E => f (z 0)) (f' • (proj 0 : E →L[ℝ] ℝ)) x :=
  hasFDerivAt_time hf

example (k : ℝ) (x : E) :
    ℝ :=
  psi k x

example (x v : E) :
    ℝ :=
  dotSpace x v

example (k : ℝ) :
    ContDiff ℝ ∞ (psi k) :=
  contDiff_psi k

example (k : ℝ) (x : E) :
    HasFDerivAt (psi k) ((k / 2) • (x 1 • (proj 1 : E →L[ℝ] ℝ) + x 2 • (proj 2 : E →L[ℝ] ℝ) +
      x 3 • (proj 3 : E →L[ℝ] ℝ))) x :=
  hasFDerivAt_psi k x

example (k : ℝ) (x v : E) :
    fderiv ℝ (psi k) x v = k / 2 * dotSpace x v :=
  fderiv_psi k x v

namespace Data

example :
    Data :=
  deSitter

example :
    Data :=
  milne

end Data

variable {D : Data} {x : E}

example {t : ℝ} (ht : t ∈ D.I) :
    HasDerivAt D.N (deriv D.N t) t :=
  hasDerivAt_N ht

example {t : ℝ} (ht : t ∈ D.I) :
    HasDerivAt (deriv D.N) (deriv (deriv D.N) t) t :=
  hasDerivAt_deriv_N ht

example {t : ℝ} (ht : t ∈ D.I) :
    HasDerivAt D.a (deriv D.a t) t :=
  hasDerivAt_a ht

example {t : ℝ} (ht : t ∈ D.I) :
    HasDerivAt (deriv D.a) (deriv (deriv D.a) t) t :=
  hasDerivAt_deriv_a ht

example :
    Opens E :=
  domain D

example (hx : x ∈ domain D) :
    x 0 ∈ D.I :=
  time_mem hx

example (hx : x ∈ domain D) :
    0 < psi D.k x :=
  psi_pos hx

example (hx : x ∈ domain D) :
    0 < D.N (x 0) :=
  N_pos_of_mem hx

example (hx : x ∈ domain D) :
    0 < D.a (x 0) :=
  a_pos_of_mem hx

example (t : ℝ) :
    E :=
  timeAxis t

example (t : ℝ) :
    timeAxis t 0 = t :=
  timeAxis_zero t

example (k t : ℝ) :
    psi k (timeAxis t) = 1 :=
  psi_timeAxis k t

example {t : ℝ} (ht : t ∈ D.I) :
    timeAxis t ∈ domain D :=
  timeAxis_mem ht

example (x : E) :
    Fin 4 → ℝ :=
  coefficients D x

example {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f D.I) :
    ContDiffOn ℝ ∞ (fun z : E => f (z 0)) (domain D) :=
  contDiffOn_time hf

example :
    ContDiffOn ℝ ∞ (fun z : E => D.a (z 0) ^ 2 / psi D.k z ^ 2) (domain D) :=
  contDiffOn_spatialCoefficient

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

example (hN : ∀ t ∈ D.I, D.N t = 1) :
    (metric D).IsSynchronous :=
  isSynchronous hN

example (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (fun z => coefficients D z 0) x v =
      -(2 * D.N (x 0) * deriv D.N (x 0) * v 0) :=
  fderiv_coefficients_zero hx v

example (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (fun z : E => D.a (z 0) ^ 2 / psi D.k z ^ 2) x v =
      (2 * D.a (x 0) * deriv D.a (x 0) * v 0 * psi D.k x -
        D.a (x 0) ^ 2 * D.k * dotSpace x v) / psi D.k x ^ 3 :=
  fderiv_spatialCoefficient hx v

example (hx : x ∈ domain D) (i : Fin 4) (v : E) :
    fderiv ℝ (fun z => coefficients D z i) x v =
      ![-(2 * D.N (x 0) * deriv D.N (x 0) * v 0),
        (2 * D.a (x 0) * deriv D.a (x 0) * v 0 * psi D.k x -
          D.a (x 0) ^ 2 * D.k * dotSpace x v) / psi D.k x ^ 3,
        (2 * D.a (x 0) * deriv D.a (x 0) * v 0 * psi D.k x -
          D.a (x 0) ^ 2 * D.k * dotSpace x v) / psi D.k x ^ 3,
        (2 * D.a (x 0) * deriv D.a (x 0) * v 0 * psi D.k x -
          D.a (x 0) ^ 2 * D.k * dotSpace x v) / psi D.k x ^ 3] i :=
  fderiv_coefficients hx i v

example (x : E) :
    ℝ :=
  gammaLapse D x

example (x : E) :
    ℝ :=
  gammaSpatial D x

example (x : E) :
    ℝ :=
  gammaExpansion D x

example (k : ℝ) (i : Fin 4) (x : E) :
    ℝ :=
  gammaConformal k i x

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

example (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (gammaLapse D) x v =
      (deriv (deriv D.N) (x 0) * D.N (x 0) - deriv D.N (x 0) ^ 2) / D.N (x 0) ^ 2 * v 0 :=
  fderiv_gammaLapse hx v

example (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (gammaExpansion D) x v =
      (deriv (deriv D.a) (x 0) * D.a (x 0) - deriv D.a (x 0) ^ 2) / D.a (x 0) ^ 2 * v 0 :=
  fderiv_gammaExpansion hx v

example (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (gammaSpatial D) x v =
      ((deriv D.a (x 0) ^ 2 + D.a (x 0) * deriv (deriv D.a) (x 0)) * D.N (x 0) * psi D.k x * v 0 -
        2 * D.a (x 0) * deriv D.a (x 0) * deriv D.N (x 0) * psi D.k x * v 0 -
        D.a (x 0) * deriv D.a (x 0) * D.N (x 0) * D.k * dotSpace x v) /
        (D.N (x 0) ^ 3 * psi D.k x ^ 3) :=
  fderiv_gammaSpatial hx v

example (k : ℝ) (i : Fin 4) {x : E} (hψ : psi k x ≠ 0) (v : E) :
    fderiv ℝ (gammaConformal k i) x v =
      (k ^ 2 * x i * dotSpace x v - 2 * k * v i * psi k x) / (4 * psi k x ^ 2) :=
  fderiv_gammaConformal k i hψ v

example (x : E) :
    ℝ :=
  ricciTime D x

example (x : E) :
    ℝ :=
  ricciSpace D x

example (x : E) :
    Fin 4 → Fin 4 → ℝ :=
  ricci D x

example (hx : x ∈ domain D) (j k : Fin 4) :
    ricciOf (metric D).coefficient x j k = ricci D x j k :=
  ricciOf_eq hx j k

example (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 0 0 =
      -3 * (deriv (deriv D.a) (x 0) / D.a (x 0) -
        deriv D.N (x 0) * deriv D.a (x 0) / (D.N (x 0) * D.a (x 0))) :=
  ricci_zero_zero hx

example (hx : x ∈ domain D) (α : Fin 3) :
    ricciOf (metric D).coefficient x 0 α.succ = 0 :=
  ricci_zero_succ hx α

example (hx : x ∈ domain D) (α : Fin 3) :
    ricciOf (metric D).coefficient x α.succ 0 = 0 :=
  ricci_succ_zero hx α

example (hx : x ∈ domain D) (α β : Fin 3) :
    ricciOf (metric D).coefficient x α.succ β.succ =
      if α = β then
        ((D.a (x 0) * deriv (deriv D.a) (x 0) + 2 * deriv D.a (x 0) ^ 2) / D.N (x 0) ^ 2 -
          D.a (x 0) * deriv D.a (x 0) * deriv D.N (x 0) / D.N (x 0) ^ 3 + 2 * D.k) /
          psi D.k x ^ 2
      else 0 :=
  ricci_succ_succ hx α β

example (hx : x ∈ domain D) :
    ((metric D).coefficient x)⁻¹ = Matrix.diagonal fun l => (coefficients D x l)⁻¹ :=
  coefficient_metric_inv hx

example (hx : x ∈ domain D) :
    scalarOf (metric D).coefficient x = ∑ a, ricci D x a a / coefficients D x a :=
  scalarOf_eq_sum hx

example (hx : x ∈ domain D) :
    scalarOf (metric D).coefficient x =
      6 * ((D.a (x 0) * deriv (deriv D.a) (x 0) + deriv D.a (x 0) ^ 2) / D.N (x 0) ^ 2 -
        D.a (x 0) * deriv D.a (x 0) * deriv D.N (x 0) / D.N (x 0) ^ 3 + D.k) / D.a (x 0) ^ 2 :=
  scalarOf_eq hx

example (x : E) :
    ℝ :=
  einsteinTime D x

example (x : E) :
    ℝ :=
  einsteinSpace D x

example (x : E) :
    Fin 4 → Fin 4 → ℝ :=
  einstein D x

example (hx : x ∈ domain D) (i k : Fin 4) :
    einsteinOf (metric D).coefficient x i k = einstein D x i k :=
  einsteinOf_eq hx i k

example (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 0 0 =
      3 * ((deriv D.a (x 0) / D.a (x 0)) ^ 2 + D.N (x 0) ^ 2 * D.k / D.a (x 0) ^ 2) :=
  einstein_zero_zero hx

example (hx : x ∈ domain D) (α : Fin 3) :
    einsteinOf (metric D).coefficient x 0 α.succ = 0 :=
  einstein_zero_succ hx α

example (hx : x ∈ domain D) (α : Fin 3) :
    einsteinOf (metric D).coefficient x α.succ 0 = 0 :=
  einstein_succ_zero hx α

example (hx : x ∈ domain D) (α β : Fin 3) :
    einsteinOf (metric D).coefficient x α.succ β.succ =
      if α = β then
        -((2 * D.a (x 0) * deriv (deriv D.a) (x 0) + deriv D.a (x 0) ^ 2) / D.N (x 0) ^ 2 -
          2 * D.a (x 0) * deriv D.a (x 0) * deriv D.N (x 0) / D.N (x 0) ^ 3 + D.k) /
          psi D.k x ^ 2
      else 0 :=
  einstein_succ_succ hx α β

example (x : E) :
    Fin 4 → ℝ :=
  fluidCovector D x

example (hx : x ∈ domain D) :
    ∑ i, ∑ j, ((metric D).coefficient x)⁻¹ i j * fluidCovector D x i * fluidCovector D x j =
      -1 :=
  fluidCovector_norm hx

example (ρ p : ℝ → ℝ) (x : E) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  perfectFluidStress D ρ p x

example (ρ p : ℝ → ℝ) (x : E) :
    Fin 4 → ℝ :=
  fluidDiagonal D ρ p x

example (ρ p : ℝ → ℝ) (y : E) :
    perfectFluidStress D ρ p y = Matrix.diagonal (fluidDiagonal D ρ p y) :=
  perfectFluidStress_eq ρ p y

example (ρ p : ℝ → ℝ) (y : E) :
    perfectFluidStress D ρ p y 0 0 = ρ (y 0) * D.N (y 0) ^ 2 :=
  perfectFluidStress_zero_zero ρ p y

example (ρ p : ℝ → ℝ) (y : E) (α β : Fin 3) :
    perfectFluidStress D ρ p y α.succ β.succ =
      p (y 0) * (metric D).coefficient y α.succ β.succ :=
  perfectFluidStress_succ_succ ρ p y α β

example {ρ p : ℝ → ℝ} (hρ : ContDiffOn ℝ ∞ ρ D.I) (hp : ContDiffOn ℝ ∞ p D.I) (i j : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => perfectFluidStress D ρ p x i j) (domain D) :=
  contDiffOn_perfectFluidStress hρ hp i j

example {ρ p : ℝ → ℝ} (hx : x ∈ domain D) (hρ : DifferentiableAt ℝ ρ (x 0)) (v : E) :
    fderiv ℝ (fun z => fluidDiagonal D ρ p z 0) x v =
      (deriv ρ (x 0) * D.N (x 0) ^ 2 + 2 * ρ (x 0) * D.N (x 0) * deriv D.N (x 0)) * v 0 :=
  fderiv_fluidDiagonal_zero hx hρ v

example {p : ℝ → ℝ} (hx : x ∈ domain D) (hp : DifferentiableAt ℝ p (x 0)) (v : E) :
    fderiv ℝ (fun z : E => p (z 0) * (D.a (z 0) ^ 2 / psi D.k z ^ 2)) x v =
      deriv p (x 0) * v 0 * (D.a (x 0) ^ 2 / psi D.k x ^ 2) +
        p (x 0) * ((2 * D.a (x 0) * deriv D.a (x 0) * v 0 * psi D.k x -
          D.a (x 0) ^ 2 * D.k * dotSpace x v) / psi D.k x ^ 3) :=
  fderiv_fluidSpace hx hp v

example {ρ p : ℝ → ℝ} (hx : x ∈ domain D) (hρ : DifferentiableAt ℝ ρ (x 0))
    (hp : DifferentiableAt ℝ p (x 0)) (i : Fin 4) (v : E) :
    fderiv ℝ (fun z => fluidDiagonal D ρ p z i) x v =
      ![(deriv ρ (x 0) * D.N (x 0) ^ 2 + 2 * ρ (x 0) * D.N (x 0) * deriv D.N (x 0)) * v 0,
        deriv p (x 0) * v 0 * (D.a (x 0) ^ 2 / psi D.k x ^ 2) +
          p (x 0) * ((2 * D.a (x 0) * deriv D.a (x 0) * v 0 * psi D.k x -
            D.a (x 0) ^ 2 * D.k * dotSpace x v) / psi D.k x ^ 3),
        deriv p (x 0) * v 0 * (D.a (x 0) ^ 2 / psi D.k x ^ 2) +
          p (x 0) * ((2 * D.a (x 0) * deriv D.a (x 0) * v 0 * psi D.k x -
            D.a (x 0) ^ 2 * D.k * dotSpace x v) / psi D.k x ^ 3),
        deriv p (x 0) * v 0 * (D.a (x 0) ^ 2 / psi D.k x ^ 2) +
          p (x 0) * ((2 * D.a (x 0) * deriv D.a (x 0) * v 0 * psi D.k x -
            D.a (x 0) ^ 2 * D.k * dotSpace x v) / psi D.k x ^ 3)] i :=
  fderiv_fluidDiagonal hx hρ hp i v

example {ρ p : ℝ → ℝ} (hx : x ∈ domain D) (hρ : DifferentiableAt ℝ ρ (x 0))
    (hp : DifferentiableAt ℝ p (x 0)) (b : Fin 4) :
    (metric D).divergenceOf (perfectFluidStress D ρ p) x b =
      ![-(deriv ρ (x 0) + 3 * (deriv D.a (x 0) / D.a (x 0)) * (ρ (x 0) + p (x 0))), 0, 0, 0] b :=
  divergenceOf_perfectFluidStress hx hρ hp b

example {ρ p : ℝ → ℝ} (hx : x ∈ domain D) (hρ : DifferentiableAt ℝ ρ (x 0))
    (hp : DifferentiableAt ℝ p (x 0)) :
    (∀ b, (metric D).divergenceOf (perfectFluidStress D ρ p) x b = 0) ↔
      deriv ρ (x 0) + 3 * (deriv D.a (x 0) / D.a (x 0)) * (ρ (x 0) + p (x 0)) = 0 :=
  comoving_divergence_iff hx hρ hp

example {ρ p : ℝ → ℝ} (hρ : ContDiffOn ℝ ∞ ρ D.I) (hp : ContDiffOn ℝ ∞ p D.I) (y : domain D)
    (b : Fin 4) :
    (metric D).toLorentzMetric.bilinearDivergenceCovector
        (bilinearOf (perfectFluidStress D ρ p) (contDiffOn_perfectFluidStress hρ hp)) y
        (chartField (physicalChart y) (Pi.single b 1) y) =
      ![-(deriv ρ (y.1 0) + 3 * (deriv D.a (y.1 0) / D.a (y.1 0)) * (ρ (y.1 0) + p (y.1 0))),
        0, 0, 0] b :=
  bilinearDivergence_perfectFluidStress hρ hp y b

example (t : ℝ) :
    ℝ :=
  hubble D t

example (κ Λ : ℝ) (ρ : ℝ → ℝ) (t : ℝ) :
    Prop :=
  FirstFriedmann D κ Λ ρ t

example (κ Λ : ℝ) (p : ℝ → ℝ) (t : ℝ) :
    Prop :=
  SecondFriedmann D κ Λ p t

example (ρ p : ℝ → ℝ) (t : ℝ) :
    Prop :=
  ContinuityEquation D ρ p t

example (hx : x ∈ domain D) (κ Λ : ℝ) (ρ p : ℝ → ℝ) :
    einsteinOf (metric D).coefficient x 0 0 + Λ * (metric D).coefficient x 0 0 -
        κ * perfectFluidStress D ρ p x 0 0 =
      3 * (hubble D (x 0) ^ 2 + D.N (x 0) ^ 2 * D.k / D.a (x 0) ^ 2 -
        (κ / 3 * D.N (x 0) ^ 2 * ρ (x 0) + Λ / 3 * D.N (x 0) ^ 2)) :=
  einsteinEquation_zero_zero hx κ Λ ρ p

example (hx : x ∈ domain D) (κ Λ : ℝ) (ρ p : ℝ → ℝ) (α : Fin 3) :
    einsteinOf (metric D).coefficient x α.succ α.succ + Λ * (metric D).coefficient x α.succ α.succ -
        κ * perfectFluidStress D ρ p x α.succ α.succ =
      -(D.a (x 0) ^ 2 / psi D.k x ^ 2) *
        ((2 * (deriv (deriv D.a) (x 0) / D.a (x 0)) + hubble D (x 0) ^ 2) / D.N (x 0) ^ 2 -
          2 * hubble D (x 0) * deriv D.N (x 0) / D.N (x 0) ^ 3 + D.k / D.a (x 0) ^ 2 -
          (-κ * p (x 0) + Λ)) :=
  einsteinEquation_succ_succ hx κ Λ ρ p α

example (hx : x ∈ domain D) (κ Λ : ℝ) (ρ p : ℝ → ℝ) :
    (∀ i k, einsteinOf (metric D).coefficient x i k + Λ * (metric D).coefficient x i k =
      κ * perfectFluidStress D ρ p x i k) ↔
      FirstFriedmann D κ Λ ρ (x 0) ∧ SecondFriedmann D κ Λ p (x 0) :=
  isEinstein_at_iff hx κ Λ ρ p

example (κ Λ : ℝ) (ρ p : ℝ → ℝ) :
    (metric D).IsEinstein κ Λ (perfectFluidStress D ρ p) ↔
      ∀ t ∈ D.I, FirstFriedmann D κ Λ ρ t ∧ SecondFriedmann D κ Λ p t :=
  isEinstein_iff_friedmann κ Λ ρ p

example {ρ p : ℝ → ℝ} (hρ : ContDiffOn ℝ ∞ ρ D.I) (hp : ContDiffOn ℝ ∞ p D.I) (κ Λ : ℝ) :
    (metric D).toLorentzMetric.SatisfiesEinstein κ Λ
        (bilinearOf (perfectFluidStress D ρ p) (contDiffOn_perfectFluidStress hρ hp)) ↔
      ∀ t ∈ D.I, FirstFriedmann D κ Λ ρ t ∧ SecondFriedmann D κ Λ p t :=
  satisfiesEinstein_iff_friedmann hρ hp κ Λ

example {ρ p : ℝ → ℝ} (hρ : DifferentiableOn ℝ ρ D.I) (hp : DifferentiableOn ℝ p D.I) :
    (∀ x ∈ domain D, ∀ b, (metric D).divergenceOf (perfectFluidStress D ρ p) x b = 0) ↔
      ∀ t ∈ D.I, ContinuityEquation D ρ p t :=
  divergence_eq_zero_iff_continuity hρ hp

example (hN : ∀ s ∈ D.I, D.N s = 1) {t : ℝ} (ht : t ∈ D.I) :
    deriv D.N t = 0 :=
  deriv_N_eq_zero hN ht

example (hN : ∀ s ∈ D.I, D.N s = 1) {t : ℝ} (ht : t ∈ D.I) (κ Λ : ℝ) (ρ : ℝ → ℝ) :
    FirstFriedmann D κ Λ ρ t ↔ hubble D t ^ 2 + D.k / D.a t ^ 2 = κ * ρ t / 3 + Λ / 3 :=
  firstFriedmann_iff_of_lapse_eq_one hN ht κ Λ ρ

example (hN : ∀ s ∈ D.I, D.N s = 1) {t : ℝ} (ht : t ∈ D.I) (κ Λ : ℝ) (p : ℝ → ℝ) :
    SecondFriedmann D κ Λ p t ↔
      2 * (deriv (deriv D.a) t / D.a t) + (deriv D.a t / D.a t) ^ 2 + D.k / D.a t ^ 2 =
        -κ * p t + Λ :=
  secondFriedmann_iff_of_lapse_eq_one hN ht κ Λ p

example (κ Λ : ℝ) (ρ : ℝ → ℝ) (t : ℝ) :
    ℝ :=
  firstDefect D κ Λ ρ t

example (κ Λ : ℝ) (p : ℝ → ℝ) (t : ℝ) :
    ℝ :=
  secondDefect D κ Λ p t

example {t : ℝ} (ht : t ∈ D.I) (κ Λ : ℝ) (ρ : ℝ → ℝ) :
    FirstFriedmann D κ Λ ρ t ↔ firstDefect D κ Λ ρ t = 0 :=
  firstFriedmann_iff_firstDefect ht κ Λ ρ

example {t : ℝ} (ht : t ∈ D.I) (κ Λ : ℝ) (p : ℝ → ℝ) :
    SecondFriedmann D κ Λ p t ↔ secondDefect D κ Λ p t = 0 :=
  secondFriedmann_iff_secondDefect ht κ Λ p

example {t : ℝ} (ht : t ∈ D.I) (κ Λ : ℝ) {ρ : ℝ → ℝ} (hρ : DifferentiableAt ℝ ρ t) :
    HasDerivAt (firstDefect D κ Λ ρ)
      (2 * deriv D.a t * deriv (deriv D.a) t + 2 * D.k * D.N t * deriv D.N t -
        (κ * deriv ρ t * D.N t ^ 2 * D.a t ^ 2 + (κ * ρ t + Λ) *
          (2 * D.N t * deriv D.N t * D.a t ^ 2 + 2 * D.N t ^ 2 * D.a t * deriv D.a t)) / 3) t :=
  hasDerivAt_firstDefect ht κ Λ hρ

example (t κ Λ : ℝ) (ρ p : ℝ → ℝ) :
    D.a t * D.N t * (2 * deriv D.a t * deriv (deriv D.a) t + 2 * D.k * D.N t * deriv D.N t -
        (κ * deriv ρ t * D.N t ^ 2 * D.a t ^ 2 + (κ * ρ t + Λ) *
          (2 * D.N t * deriv D.N t * D.a t ^ 2 + 2 * D.N t ^ 2 * D.a t * deriv D.a t)) / 3) =
      (2 * D.a t * deriv D.N t - deriv D.a t * D.N t) * firstDefect D κ Λ ρ t +
        deriv D.a t * secondDefect D κ Λ p t -
        κ * D.a t ^ 2 * D.N t ^ 3 / 3 * (D.a t * deriv ρ t + 3 * deriv D.a t * (ρ t + p t)) :=
  friedmann_identity D t κ Λ ρ p

example {κ Λ : ℝ} {ρ : ℝ → ℝ} {t : ℝ} (ht : t ∈ D.I) (hρ : DifferentiableAt ℝ ρ t)
    (h1 : ∀ s ∈ D.I, FirstFriedmann D κ Λ ρ s) :
    2 * deriv D.a t * deriv (deriv D.a) t + 2 * D.k * D.N t * deriv D.N t -
        (κ * deriv ρ t * D.N t ^ 2 * D.a t ^ 2 + (κ * ρ t + Λ) *
          (2 * D.N t * deriv D.N t * D.a t ^ 2 + 2 * D.N t ^ 2 * D.a t * deriv D.a t)) / 3 = 0 :=
  deriv_firstDefect_eq_zero ht hρ h1

example {t : ℝ} (ht : t ∈ D.I) (ρ p : ℝ → ℝ) :
    D.a t * (deriv ρ t + 3 * hubble D t * (ρ t + p t)) =
      D.a t * deriv ρ t + 3 * deriv D.a t * (ρ t + p t) :=
  mul_continuity ht ρ p

example {κ Λ : ℝ} (hκ : κ ≠ 0) {ρ p : ℝ → ℝ} {t : ℝ} (ht : t ∈ D.I) (hρ : DifferentiableAt ℝ ρ t)
    (h1 : ∀ s ∈ D.I, FirstFriedmann D κ Λ ρ s) (h2 : SecondFriedmann D κ Λ p t) :
    ContinuityEquation D ρ p t :=
  continuity_of_friedmann hκ ht hρ h1 h2

example {κ Λ : ℝ} {ρ p : ℝ → ℝ} {t : ℝ} (ht : t ∈ D.I) (hda : deriv D.a t ≠ 0)
    (hρ : DifferentiableAt ℝ ρ t) (h1 : ∀ s ∈ D.I, FirstFriedmann D κ Λ ρ s)
    (hc : ContinuityEquation D ρ p t) :
    SecondFriedmann D κ Λ p t :=
  second_of_first_of_continuity ht hda hρ h1 hc

example {κ : ℝ} {ρ : ℝ → ℝ} {t : ℝ} (ht : t ∈ D.I) (hN : D.N t = 1) (h : FirstFriedmann D κ 0 ρ t) :
    D.k = D.a t ^ 2 * (κ * ρ t / 3 - hubble D t ^ 2) :=
  curvature_eq ht hN h

example {κ : ℝ} (hκ : 0 < κ) {ρ : ℝ → ℝ} {t : ℝ} (ht : t ∈ D.I) (hN : D.N t = 1)
    (h : FirstFriedmann D κ 0 ρ t) :
    SignType.sign D.k = SignType.sign (ρ t - 3 * hubble D t ^ 2 / κ) :=
  curvature_sign hκ ht hN h

example :
    perfectFluidStress D 0 0 = 0 :=
  perfectFluidStress_zero

example (z : E) :
    z ∈ domain Data.deSitter :=
  mem_domain_deSitter z

example :
    (metric Data.deSitter).coefficient = DeSitterSlicing.metric.coefficient :=
  coefficient_deSitter

example (z : E) (i j : Fin 4) :
    ricci Data.deSitter z i j = ricciOf DeSitterSlicing.metric.coefficient z i j :=
  ricci_deSitter z i j

example (z : E) (i j : Fin 4) :
    ricciOf (metric Data.deSitter).coefficient z i j =
      3 * (metric Data.deSitter).coefficient z i j :=
  ricciOf_deSitter z i j

example (κ : ℝ) :
    (metric Data.deSitter).IsEinstein κ 3 0 :=
  isEinstein_deSitter κ

example {z : E} (hz : z ∈ domain Data.milne) (i j : Fin 4) :
    ricciOf (metric Data.milne).coefficient z i j = 0 :=
  ricciOf_milne hz i j

example (κ : ℝ) :
    (metric Data.milne).IsEinstein κ 0 0 :=
  isEinstein_milne κ

example :
    Data :=
  Data.static

example {κ : ℝ} (hκ : κ ≠ 0) (t : ℝ) :
    (∀ s ∈ Data.static.I, FirstFriedmann Data.static κ 0 0 s) ∧
      ContinuityEquation Data.static 0 (fun _ => 1) t ∧
      ¬ SecondFriedmann Data.static κ 0 (fun _ => 1) t :=
  not_secondFriedmann_static hκ t

example :
    Data :=
  Data.closedDeSitter

example (κ : ℝ) :
    (metric Data.closedDeSitter).IsEinstein κ 3 0 :=
  isEinstein_closedDeSitter κ

end ProjectAinos.GeneralRelativity.FLRW

end FLRW

section CosmologicalModels


open Set Filter TopologicalSpace

open scoped ContDiff Topology Real

namespace ProjectAinos.GeneralRelativity.CosmologicalModels

open SmoothGeometry CoordinateMetric FLRW

local notation "E" => MinkowskiModel 3

example (I : Set ℝ) (a : ℝ → ℝ) (k : ℝ) (hI : IsOpen I) (ha : ContDiffOn ℝ ∞ a I)
    (hpos : ∀ η ∈ I, 0 < a η) :
    Data :=
  conformalData I a k hI ha hpos

variable {D : Data}

example (hN : D.N = D.a) {η : ℝ} (hη : η ∈ D.I) (κ Λ : ℝ) (ρ : ℝ → ℝ) :
    FirstFriedmann D κ Λ ρ η ↔
      deriv D.a η ^ 2 + D.k * D.a η ^ 2 = (κ * ρ η + Λ) * D.a η ^ 4 / 3 :=
  firstFriedmann_conformal_iff hN hη κ Λ ρ

example (hN : D.N = D.a) {η : ℝ} (hη : η ∈ D.I) (κ Λ : ℝ) (p : ℝ → ℝ) :
    SecondFriedmann D κ Λ p η ↔
      2 * D.a η * deriv (deriv D.a) η - deriv D.a η ^ 2 + D.k * D.a η ^ 2 =
        (-κ * p η + Λ) * D.a η ^ 4 :=
  secondFriedmann_conformal_iff hN hη κ Λ p

example (hN : D.N = D.a) (κ Λ : ℝ) (ρ p : ℝ → ℝ) :
    (metric D).IsEinstein κ Λ (perfectFluidStress D ρ p) ↔ ∀ η ∈ D.I,
      deriv D.a η ^ 2 + D.k * D.a η ^ 2 = (κ * ρ η + Λ) * D.a η ^ 4 / 3 ∧
        2 * D.a η * deriv (deriv D.a) η - deriv D.a η ^ 2 + D.k * D.a η ^ 2 =
          (-κ * p η + Λ) * D.a η ^ 4 :=
  isEinstein_conformal_iff hN κ Λ ρ p

example (κ c : ℝ) (a : ℝ → ℝ) (η : ℝ) :
    ℝ :=
  dustDensity κ c a η

example (κ a₀ : ℝ) (a : ℝ → ℝ) (η : ℝ) :
    ℝ :=
  radiationDensity κ a₀ a η

example (κ a₀ : ℝ) (a : ℝ → ℝ) (η : ℝ) :
    ℝ :=
  radiationPressure κ a₀ a η

example {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c) {a : ℝ → ℝ} {η : ℝ} (ha : 0 < a η) :
    0 < dustDensity κ c a η :=
  dustDensity_pos hκ hc ha

example {κ a₀ : ℝ} (hκ : 0 < κ) (ha₀ : a₀ ≠ 0) {a : ℝ → ℝ} {η : ℝ} (ha : 0 < a η) :
    0 < radiationDensity κ a₀ a η :=
  radiationDensity_pos hκ ha₀ ha

example (hN : D.N = D.a) {κ : ℝ} (hκ : κ ≠ 0) (c : ℝ)
    (h1 : ∀ η ∈ D.I, deriv D.a η ^ 2 + D.k * D.a η ^ 2 = c * D.a η / 3)
    (h2 : ∀ η ∈ D.I, 2 * D.a η * deriv (deriv D.a) η - deriv D.a η ^ 2 + D.k * D.a η ^ 2 = 0) :
    (metric D).IsEinstein κ 0 (perfectFluidStress D (dustDensity κ c D.a) 0) :=
  isEinstein_dust hN hκ c h1 h2

example (hN : D.N = D.a) {κ : ℝ} (hκ : κ ≠ 0) (a₀ : ℝ)
    (h1 : ∀ η ∈ D.I, deriv D.a η ^ 2 + D.k * D.a η ^ 2 = a₀ ^ 2)
    (h2 : ∀ η ∈ D.I,
      2 * D.a η * deriv (deriv D.a) η - deriv D.a η ^ 2 + D.k * D.a η ^ 2 = -a₀ ^ 2) :
    (metric D).IsEinstein κ 0
      (perfectFluidStress D (radiationDensity κ a₀ D.a) (radiationPressure κ a₀ D.a)) :=
  isEinstein_radiation hN hκ a₀ h1 h2

variable {a₀ : ℝ}

example (ha₀ : 0 < a₀) {η : ℝ} (hη : η ∈ Ioo 0 (2 * π)) :
    0 < a₀ * (1 - Real.cos η) :=
  closedDust_pos ha₀ hη

example (a₀ : ℝ) (ha₀ : 0 < a₀) :
    Data :=
  closedDust a₀ ha₀

example (ha₀ : 0 < a₀) :
    deriv (closedDust a₀ ha₀).a = fun η => a₀ * Real.sin η :=
  deriv_closedDust_a ha₀

example (a₀ : ℝ) :
    deriv (fun η => a₀ * Real.sin η) = fun η => a₀ * Real.cos η :=
  deriv_const_mul_sin a₀

example (ha₀ : 0 < a₀) {κ : ℝ} (hκ : κ ≠ 0) :
    (metric (closedDust a₀ ha₀)).IsEinstein κ 0
      (perfectFluidStress (closedDust a₀ ha₀)
        (dustDensity κ (6 * a₀) (closedDust a₀ ha₀).a) 0) :=
  isEinstein_closedDust ha₀ hκ

example (a₀ : ℝ) (ha₀ : 0 < a₀) :
    Data :=
  closedRadiation a₀ ha₀

example (a₀ : ℝ) :
    deriv (fun η => a₀ * Real.cos η) = fun η => -(a₀ * Real.sin η) :=
  deriv_const_mul_cos a₀

example (ha₀ : 0 < a₀) {κ : ℝ} (hκ : κ ≠ 0) :
    (metric (closedRadiation a₀ ha₀)).IsEinstein κ 0
      (perfectFluidStress (closedRadiation a₀ ha₀)
        (radiationDensity κ a₀ (closedRadiation a₀ ha₀).a)
        (radiationPressure κ a₀ (closedRadiation a₀ ha₀).a)) :=
  isEinstein_closedRadiation ha₀ hκ

example (ha₀ : 0 < a₀) {η : ℝ} (hη : η ∈ Ioi 0) :
    0 < a₀ * (Real.cosh η - 1) :=
  openDust_pos ha₀ hη

example (a₀ : ℝ) (ha₀ : 0 < a₀) :
    Data :=
  openDust a₀ ha₀

example (ha₀ : 0 < a₀) :
    deriv (openDust a₀ ha₀).a = fun η => a₀ * Real.sinh η :=
  deriv_openDust_a ha₀

example (a₀ : ℝ) :
    deriv (fun η => a₀ * Real.sinh η) = fun η => a₀ * Real.cosh η :=
  deriv_const_mul_sinh a₀

example (a₀ : ℝ) :
    deriv (fun η => a₀ * Real.cosh η) = fun η => a₀ * Real.sinh η :=
  deriv_const_mul_cosh a₀

example (ha₀ : 0 < a₀) {κ : ℝ} (hκ : κ ≠ 0) :
    (metric (openDust a₀ ha₀)).IsEinstein κ 0
      (perfectFluidStress (openDust a₀ ha₀) (dustDensity κ (6 * a₀) (openDust a₀ ha₀).a) 0) :=
  isEinstein_openDust ha₀ hκ

example (a₀ : ℝ) (ha₀ : 0 < a₀) :
    Data :=
  openRadiation a₀ ha₀

example (ha₀ : 0 < a₀) {κ : ℝ} (hκ : κ ≠ 0) :
    (metric (openRadiation a₀ ha₀)).IsEinstein κ 0
      (perfectFluidStress (openRadiation a₀ ha₀)
        (radiationDensity κ a₀ (openRadiation a₀ ha₀).a)
        (radiationPressure κ a₀ (openRadiation a₀ ha₀).a)) :=
  isEinstein_openRadiation ha₀ hκ

example (a₀ : ℝ) (ha₀ : 0 < a₀) :
    Data :=
  flatDust a₀ ha₀

example (ha₀ : 0 < a₀) :
    deriv (flatDust a₀ ha₀).a = fun η => 2 * a₀ * η :=
  deriv_flatDust_a ha₀

example (a₀ : ℝ) :
    deriv (fun η : ℝ => 2 * a₀ * η) = fun _ => 2 * a₀ :=
  deriv_flatDust_velocity a₀

example (ha₀ : 0 < a₀) {κ : ℝ} (hκ : κ ≠ 0) :
    (metric (flatDust a₀ ha₀)).IsEinstein κ 0
      (perfectFluidStress (flatDust a₀ ha₀) (dustDensity κ (12 * a₀) (flatDust a₀ ha₀).a) 0) :=
  isEinstein_flatDust ha₀ hκ

example (a₀ : ℝ) (ha₀ : 0 < a₀) :
    Data :=
  flatRadiation a₀ ha₀

example (ha₀ : 0 < a₀) {κ : ℝ} (hκ : κ ≠ 0) :
    (metric (flatRadiation a₀ ha₀)).IsEinstein κ 0
      (perfectFluidStress (flatRadiation a₀ ha₀)
        (radiationDensity κ a₀ (flatRadiation a₀ ha₀).a)
        (radiationPressure κ a₀ (flatRadiation a₀ ha₀).a)) :=
  isEinstein_flatRadiation ha₀ hκ

example (a₀ η : ℝ) :
    ℝ :=
  closedDustTime a₀ η

example (a₀ η : ℝ) :
    ℝ :=
  openDustTime a₀ η

example (a₀ η : ℝ) :
    ℝ :=
  closedRadiationTime a₀ η

example (a₀ η : ℝ) :
    ℝ :=
  openRadiationTime a₀ η

example (a₀ η : ℝ) :
    ℝ :=
  flatDustTime a₀ η

example (a₀ η : ℝ) :
    ℝ :=
  flatRadiationTime a₀ η

example (ha₀ : 0 < a₀) (η : ℝ) :
    HasDerivAt (closedDustTime a₀) ((closedDust a₀ ha₀).a η) η :=
  hasDerivAt_closedDustTime ha₀ η

example (ha₀ : 0 < a₀) (η : ℝ) :
    HasDerivAt (openDustTime a₀) ((openDust a₀ ha₀).a η) η :=
  hasDerivAt_openDustTime ha₀ η

example (ha₀ : 0 < a₀) (η : ℝ) :
    HasDerivAt (closedRadiationTime a₀) ((closedRadiation a₀ ha₀).a η) η :=
  hasDerivAt_closedRadiationTime ha₀ η

example (ha₀ : 0 < a₀) (η : ℝ) :
    HasDerivAt (openRadiationTime a₀) ((openRadiation a₀ ha₀).a η) η :=
  hasDerivAt_openRadiationTime ha₀ η

example (ha₀ : 0 < a₀) (η : ℝ) :
    HasDerivAt (flatDustTime a₀) ((flatDust a₀ ha₀).a η) η :=
  hasDerivAt_flatDustTime ha₀ η

example (ha₀ : 0 < a₀) (η : ℝ) :
    HasDerivAt (flatRadiationTime a₀) ((flatRadiation a₀ ha₀).a η) η :=
  hasDerivAt_flatRadiationTime ha₀ η

example (D : Data) {T : ℝ → ℝ} (hT : ∀ s ∈ D.I, HasDerivAt T (D.N s) s) {γ : ℝ → domain D}
    (hγ : ContDiff ℝ ∞ fun t => (γ t : E)) {x₀ : E} {a b : ℝ}
    (hrest : ∀ t ∈ uIcc a b, (γ t : E) = x₀ + t • Pi.single 0 1) :
    properTime (metric D).toLorentzMetric γ a b = T (x₀ 0 + b) - T (x₀ 0 + a) :=
  properTime_comoving D hT hγ hrest

example (x₀ : E) (t : ℝ) :
    domain Data.deSitter :=
  deSitterObserver x₀ t

example (x₀ : E) (a b : ℝ) :
    properTime (metric Data.deSitter).toLorentzMetric (deSitterObserver x₀) a b = b - a :=
  properTime_deSitter x₀ a b

example (ha₀ : 0 < a₀) {γ : ℝ → domain (closedDust a₀ ha₀)} (hγ : ContDiff ℝ ∞ fun t => (γ t : E))
    {x₀ : E} {a b : ℝ} (hrest : ∀ t ∈ uIcc a b, (γ t : E) = x₀ + t • Pi.single 0 1) :
    properTime (metric (closedDust a₀ ha₀)).toLorentzMetric γ a b =
      closedDustTime a₀ (x₀ 0 + b) - closedDustTime a₀ (x₀ 0 + a) :=
  properTime_closedDust ha₀ hγ hrest

example (ha₀ : 0 < a₀) {γ : ℝ → domain (openDust a₀ ha₀)} (hγ : ContDiff ℝ ∞ fun t => (γ t : E))
    {x₀ : E} {a b : ℝ} (hrest : ∀ t ∈ uIcc a b, (γ t : E) = x₀ + t • Pi.single 0 1) :
    properTime (metric (openDust a₀ ha₀)).toLorentzMetric γ a b =
      openDustTime a₀ (x₀ 0 + b) - openDustTime a₀ (x₀ 0 + a) :=
  properTime_openDust ha₀ hγ hrest

example (ha₀ : 0 < a₀) (η : ℝ) :
    (closedDust a₀ ha₀).a η ≤ 2 * a₀ :=
  closedDust_a_le ha₀ η

example (ha₀ : 0 < a₀) :
    (closedDust a₀ ha₀).a π = 2 * a₀ :=
  closedDust_a_pi ha₀

example (ha₀ : 0 < a₀) :
    deriv (closedDust a₀ ha₀).a π = 0 :=
  deriv_closedDust_a_pi ha₀

example (ha₀ : 0 < a₀) :
    closedDustTime a₀ π - closedDustTime a₀ 0 = π * (closedDust a₀ ha₀).a π / 2 :=
  closedDustTime_pi_sub_zero ha₀

example :
    closedDustTime a₀ (2 * π) - closedDustTime a₀ 0 = 2 * π * a₀ :=
  closedDustTime_two_pi_sub_zero

example (ha₀ : 0 < a₀) :
    Tendsto (fun η => closedDustTime a₀ π - closedDustTime a₀ η) (𝓝[>] 0)
      (𝓝 (π * (closedDust a₀ ha₀).a π / 2)) :=
  tendsto_closedDust_age ha₀

example {D : Data} (hN : ∀ t ∈ D.I, D.N t = 1) (hI : IsPreconnected D.I) (hk : D.k ≤ 0) {κ : ℝ}
    (hκ : 0 < κ) {ρ : ℝ → ℝ} (h1 : ∀ t ∈ D.I, FirstFriedmann D κ 0 ρ t) (hρ : ∀ t ∈ D.I, 0 ≤ ρ t)
    (hρ₀ : D.k = 0 → ∀ t ∈ D.I, 0 < ρ t) {t₀ : ℝ} (ht₀ : t₀ ∈ D.I) (hexp : 0 < deriv D.a t₀) :
    ∀ t ∈ D.I, 0 < deriv D.a t :=
  open_expands_forever hN hI hk hκ h1 hρ hρ₀ ht₀ hexp

example {D : Data} (hN : ∀ t ∈ D.I, D.N t = 1) (hI : IsPreconnected D.I) (hk : D.k ≤ 0) {κ : ℝ}
    (hκ : 0 < κ) {ρ : ℝ → ℝ} (h1 : ∀ t ∈ D.I, FirstFriedmann D κ 0 ρ t) (hρ : ∀ t ∈ D.I, 0 ≤ ρ t)
    (hρ₀ : D.k = 0 → ∀ t ∈ D.I, 0 < ρ t) {t₀ : ℝ} (ht₀ : t₀ ∈ D.I) (hexp : 0 < deriv D.a t₀) :
    StrictMonoOn D.a D.I :=
  open_strictMonoOn hN hI hk hκ h1 hρ hρ₀ ht₀ hexp

example (κ : ℝ) (hκ : 0 < κ) :
    ∀ t ∈ Data.milne.I, 0 < deriv Data.milne.a t :=
  milne_expands κ hκ

end ProjectAinos.GeneralRelativity.CosmologicalModels

end CosmologicalModels

section CosmologicalRedshift


open Set Filter TopologicalSpace

open scoped Manifold ContDiff Topology

namespace ProjectAinos.GeneralRelativity.CosmologicalRedshift

open SmoothGeometry CoordinateMetric LorentzMetric FLRW

local notation "E" => MinkowskiModel 3

variable {D : Data}

example (hN : ∀ t ∈ D.I, D.N t = 1) {γ : ℝ → domain D} {s : Set ℝ} (hs : IsOpen s) {z₀ : E}
    (hγ : ∀ t ∈ s, (γ t : E) = z₀ + t • Pi.single 0 1) :
    (metric D).toLorentzMetric.IsGeodesicOn s γ ∧ ∀ t ∈ s,
      (metric D).toLorentzMetric.form (γ t) (curveVelocity γ t) (curveVelocity γ t) = -1 ∧
        ∀ α : Fin 3,
          (metric D).toLorentzMetric.form (γ t) (curveVelocity γ t) (Pi.single α.succ 1) = 0 :=
  comoving_isGeodesicOn hN hs hγ

example (z₀ : E) :
    (metric Data.deSitter).toLorentzMetric.IsGeodesicOn univ
      (fun t => (⟨z₀ + t • Pi.single 0 1, mem_domain_deSitter _⟩ : domain Data.deSitter)) :=
  isGeodesicOn_deSitterObserver z₀

example (x₀ y : domain D) (w : TangentSpace 𝓘(ℝ, E) y) :
    (metric D).toLorentzMetric.form y (chartField (physicalChart x₀) (Pi.single 0 1) y) w =
      -(D.N ((y : E) 0) ^ 2) * (w : E) 0 :=
  form_timeField x₀ y w

example (x₀ y : domain D) :
    (metric D).toLorentzMetric.killingNorm (chartField (physicalChart x₀) (Pi.single 0 1)) y =
      D.N ((y : E) 0) :=
  killingNorm_timeField x₀ y

example (x₀ : domain D) {γ : ℝ → domain D} {t : ℝ}
    (hγ : DifferentiableAt ℝ (fun t => (γ t : E)) t) :
    (metric D).toLorentzMetric.observedFrequency (chartField (physicalChart x₀) (Pi.single 0 1))
        γ t =
      D.N ((γ t : E) 0) * deriv (fun t => (γ t : E)) t 0 :=
  observedFrequency_eq x₀ hγ

example (hN : ∀ t ∈ D.I, D.N t = 1) (x₀ : domain D) {γ : ℝ → domain D} {t : ℝ}
    (hγ : DifferentiableAt ℝ (fun t => (γ t : E)) t) :
    (metric D).toLorentzMetric.observedFrequency (chartField (physicalChart x₀) (Pi.single 0 1))
        γ t =
      deriv (fun t => (γ t : E)) t 0 :=
  observedFrequency_eq_timeVelocity hN x₀ hγ

example (x v : E) :
    ∑ i, ∑ j, FLRW.christoffel D x 0 i j * v i * v j =
      gammaLapse D x * v 0 ^ 2 + gammaSpatial D x * (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) :=
  sum_christoffel_zero x v

example {γ : ℝ → domain D} {s : Set ℝ} (hγ : (metric D).toLorentzMetric.IsGeodesicOn s γ) {t : ℝ}
    (ht : t ∈ s) :
    deriv (deriv (fun t => (γ t : E))) t 0 +
        gammaLapse D (γ t) * deriv (fun t => (γ t : E)) t 0 ^ 2 +
        gammaSpatial D (γ t) * (deriv (fun t => (γ t : E)) t 1 ^ 2 +
          deriv (fun t => (γ t : E)) t 2 ^ 2 + deriv (fun t => (γ t : E)) t 3 ^ 2) = 0 :=
  geodesic_time hγ ht

example {γ : ℝ → domain D} {t : ℝ} (hγ : DifferentiableAt ℝ (fun t => (γ t : E)) t) :
    (metric D).toLorentzMetric.form (γ t) (curveVelocity γ t) (curveVelocity γ t) =
      -(D.N ((γ t : E) 0) ^ 2) * deriv (fun t => (γ t : E)) t 0 ^ 2 +
        D.a ((γ t : E) 0) ^ 2 / psi D.k (γ t) ^ 2 * (deriv (fun t => (γ t : E)) t 1 ^ 2 +
          deriv (fun t => (γ t : E)) t 2 ^ 2 + deriv (fun t => (γ t : E)) t 3 ^ 2) :=
  form_velocity hγ

example {γ : ℝ → domain D} {s : Set ℝ} (hγ : (metric D).toLorentzMetric.IsGeodesicOn s γ) {t : ℝ}
    (ht : t ∈ s)
    (hnull : (metric D).toLorentzMetric.form (γ t) (curveVelocity γ t) (curveVelocity γ t) = 0) :
    HasDerivAt (fun r => D.a ((γ r : E) 0) *
      (D.N ((γ r : E) 0) * deriv (fun t => (γ t : E)) r 0)) 0 t :=
  hasDerivAt_scale_mul_frequency hγ ht hnull

example {γ : ℝ → domain D} {s : Set ℝ} (hγ : (metric D).toLorentzMetric.IsGeodesicOn s γ)
    (hs : Convex ℝ s) {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (hnull : (metric D).toLorentzMetric.form (γ t₀) (curveVelocity γ t₀) (curveVelocity γ t₀) = 0)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ s) (ht₂ : t₂ ∈ s) :
    D.a ((γ t₁ : E) 0) * (D.N ((γ t₁ : E) 0) * deriv (fun t => (γ t : E)) t₁ 0) =
      D.a ((γ t₂ : E) 0) * (D.N ((γ t₂ : E) 0) * deriv (fun t => (γ t : E)) t₂ 0) :=
  scale_mul_lapse_mul_velocity_eq hγ hs ht₀ hnull ht₁ ht₂

example {γ : ℝ → domain D} {s : Set ℝ} (hγ : (metric D).toLorentzMetric.IsGeodesicOn s γ) {t : ℝ}
    (ht : t ∈ s) :
    DifferentiableAt ℝ (fun t => (γ t : E)) t :=
  differentiableAt_of_isGeodesicOn hγ ht

example (x₀ : domain D) {γ : ℝ → domain D} {s : Set ℝ}
    (hγ : (metric D).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (hnull : (metric D).toLorentzMetric.form (γ t₀) (curveVelocity γ t₀) (curveVelocity γ t₀) = 0)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ s) (ht₂ : t₂ ∈ s) :
    D.a ((γ t₁ : E) 0) * (metric D).toLorentzMetric.observedFrequency
        (chartField (physicalChart x₀) (Pi.single 0 1)) γ t₁ =
      D.a ((γ t₂ : E) 0) * (metric D).toLorentzMetric.observedFrequency
        (chartField (physicalChart x₀) (Pi.single 0 1)) γ t₂ :=
  scale_mul_frequency_eq x₀ hγ hs ht₀ hnull ht₁ ht₂

example (hN : ∀ t ∈ D.I, D.N t = 1) {γ : ℝ → domain D} {s : Set ℝ}
    (hγ : (metric D).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (hnull : (metric D).toLorentzMetric.form (γ t₀) (curveVelocity γ t₀) (curveVelocity γ t₀) = 0)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ s) (ht₂ : t₂ ∈ s) :
    D.a ((γ t₁ : E) 0) * deriv (fun t => (γ t : E)) t₁ 0 =
      D.a ((γ t₂ : E) 0) * deriv (fun t => (γ t : E)) t₂ 0 :=
  scale_mul_timeVelocity_eq hN hγ hs ht₀ hnull ht₁ ht₂

example (x₀ : domain D) (γ : ℝ → domain D) (t₁ t₂ : ℝ) :
    ℝ :=
  redshift D x₀ γ t₁ t₂

example (x₀ : domain D) {γ : ℝ → domain D} {s : Set ℝ}
    (hγ : (metric D).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (hnull : (metric D).toLorentzMetric.form (γ t₀) (curveVelocity γ t₀) (curveVelocity γ t₀) = 0)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ s) (ht₂ : t₂ ∈ s)
    (hω : (metric D).toLorentzMetric.observedFrequency
      (chartField (physicalChart x₀) (Pi.single 0 1)) γ t₂ ≠ 0) :
    1 + redshift D x₀ γ t₁ t₂ = D.a ((γ t₂ : E) 0) / D.a ((γ t₁ : E) 0) :=
  redshift_eq x₀ hγ hs ht₀ hnull ht₁ ht₂ hω

example (x₀ : domain D) {γ : ℝ → domain D} {t : ℝ}
    (hγ : DifferentiableAt ℝ (fun t => (γ t : E)) t)
    (hnull : (metric D).toLorentzMetric.form (γ t) (curveVelocity γ t) (curveVelocity γ t) = 0)
    (hv : curveVelocity (d := 3) γ t ≠ 0) :
    (metric D).toLorentzMetric.observedFrequency (chartField (physicalChart x₀) (Pi.single 0 1))
      γ t ≠ 0 :=
  observedFrequency_ne_zero x₀ hγ hnull hv

example (c r : ℝ) :
    domain Data.deSitter :=
  deSitterRay c r

example (c r : ℝ) :
    (deSitterRay c r : E) = ![Real.log r, c - r⁻¹, 0, 0] :=
  deSitterRay_val c r

example (c : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun r => (deSitterRay c r : E)) ![r⁻¹, (r ^ 2)⁻¹, 0, 0] r :=
  hasDerivAt_deSitterRay c hr

example {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun r : ℝ => (![r⁻¹, (r ^ 2)⁻¹, 0, 0] : E))
      ![-(r ^ 2)⁻¹, -(2 / r ^ 3), 0, 0] r :=
  hasDerivAt_deSitterRayVelocity hr

example (c : ℝ) :
    (metric Data.deSitter).toLorentzMetric.IsGeodesicOn (Ioi 0) (deSitterRay c) :=
  isGeodesicOn_deSitterRay c

example (c : ℝ) {r : ℝ} (hr : 0 < r) :
    (metric Data.deSitter).toLorentzMetric.form (deSitterRay c r)
      (curveVelocity (deSitterRay c) r) (curveVelocity (deSitterRay c) r) = 0 :=
  form_deSitterRay_velocity c hr

example (c : ℝ) {r : ℝ} (hr : 0 < r) :
    Data.deSitter.a ((deSitterRay c r : E) 0) = r :=
  scale_deSitterRay c hr

example (x₀ : domain Data.deSitter) (c : ℝ) {r : ℝ} (hr : 0 < r) :
    (metric Data.deSitter).toLorentzMetric.observedFrequency
      (chartField (physicalChart x₀) (Pi.single 0 1)) (deSitterRay c) r = r⁻¹ :=
  observedFrequency_deSitterRay x₀ c hr

example (x₀ : domain Data.deSitter) (c : ℝ) {r : ℝ} (hr : 0 < r) :
    Data.deSitter.a ((deSitterRay c r : E) 0) *
        (metric Data.deSitter).toLorentzMetric.observedFrequency
          (chartField (physicalChart x₀) (Pi.single 0 1)) (deSitterRay c) r = 1 :=
  scale_mul_frequency_deSitterRay x₀ c hr

example (x₀ : domain Data.deSitter) (c : ℝ) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) :
    1 + redshift Data.deSitter x₀ (deSitterRay c) r₁ r₂ = r₂ / r₁ :=
  redshift_deSitterRay x₀ c hr₁ hr₂

end ProjectAinos.GeneralRelativity.CosmologicalRedshift

end CosmologicalRedshift
