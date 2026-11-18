/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.GeodesicHamiltonian
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp

/-!
# Geodesics in the equatorial plane of the exterior Schwarzschild field

The equatorial plane of the exterior Schwarzschild field of mass `M ≥ 0` has the co-ordinates
`(t, s, φ)` with the radius `r = 2M + eˢ`, so that `s` ranges over the real line and every
point has `r > 2M`. The angle `φ` is read on the real line: `ℝ³` with these coefficients is the
universal cover of the exterior equatorial plane. The metric
`ds² = −(1 − 2M/r) dt² + dr²/(1 − 2M/r) + r² dφ²` reads
`−(eˢ/r) dt² + eˢ r ds² + r² dφ²`, and every coefficient and every coefficient of the inverse is
a smooth function of `s` on all of `ℝ`. This is the instance of the geodesic Hamiltonian
planned for stage G-H (Landau–Lifshitz, §§88, 101).

* `isTrajectory_iff`: the trajectories of `H = ½ g^{μν} p_μ p_ν` are the geodesics of the
  chart that are defined for all values of the affine parameter, with `p_μ = g_{μν} ẋ^ν`.
* `isIntegral_p_time`, `isIntegral_p_angle`: the energy `−p_t` and the angular momentum `p_φ`
  are integrals of the motion, since the metric depends on `s` only.
* `killingNorm_eq`, `killingNorm_mul_frequency_eq`: a static observer at the radius `r`
  measures the frequency `ω` of a trajectory, and `ω √(1 − 2M/r)` is the same at all its
  events.

A trajectory is defined for all values of the affine parameter. Every radial geodesic along
which `r` changes, and every ray that enters `r < 3M`, reaches `r = 2M` at a finite parameter and
is not a trajectory; the rays that stay outside `r = 3M`, such as the rays scattered from
infinity, are. The red shift
along a given geodesic segment of a Lorentz manifold, radial rays included, is
`LorentzMetric.killingNorm_mul_observedFrequency_eq`. That a geodesic of the full exterior with
initial data in the plane stays in the plane is a separate statement and is not proved here.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.GeneralRelativity.GeodesicHamiltonian.SchwarzschildEquatorial

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace Mechanics SmoothOperation
open scoped ContDiff

variable {M : ℝ}

/-- The radius `r = 2M + eˢ`. -/
def radius (M s : ℝ) : ℝ := 2 * M + Real.exp s

theorem radius_pos (hM : 0 ≤ M) (s : ℝ) : 0 < radius M s := by
  unfold radius
  positivity

theorem exp_div_radius (M s : ℝ) (hM : 0 ≤ M) :
    Real.exp s / radius M s = 1 - 2 * M / radius M s := by
  have h := (radius_pos hM s).ne'
  field_simp
  unfold radius
  ring

theorem contDiff_exp_coord : ContDiff ℝ ∞ (fun x : Fin 1 → ℝ => Real.exp (x 0)) :=
  Real.contDiff_exp.comp (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0)

theorem contDiff_radius (M : ℝ) : ContDiff ℝ ∞ (fun x : Fin 1 → ℝ => radius M (x 0)) :=
  contDiff_const.add contDiff_exp_coord

/-- The coefficients `−eˢ/r`, `eˢ r` and `r²` of the metric, as functions of `s`. -/
def lowerOp (hM : 0 ≤ M) : Fin 3 → SmoothOperation 1 :=
  ![ofContDiff (fun x => -(Real.exp (x 0) / radius M (x 0)))
      ((contDiff_exp_coord.div (contDiff_radius M) fun x => (radius_pos hM (x 0)).ne').neg),
    ofContDiff (fun x => Real.exp (x 0) * radius M (x 0))
      (contDiff_exp_coord.mul (contDiff_radius M)),
    ofContDiff (fun x => radius M (x 0) ^ 2) ((contDiff_radius M).pow 2)]

/-- The coefficients `−r/eˢ`, `1/(eˢ r)` and `1/r²` of the inverse metric. -/
def upperOp (hM : 0 ≤ M) : Fin 3 → SmoothOperation 1 :=
  ![ofContDiff (fun x => -(radius M (x 0) / Real.exp (x 0)))
      (((contDiff_radius M).div contDiff_exp_coord fun x => (Real.exp_pos (x 0)).ne').neg),
    ofContDiff (fun x => (Real.exp (x 0) * radius M (x 0))⁻¹)
      ((contDiff_exp_coord.mul (contDiff_radius M)).inv fun x =>
        (mul_pos (Real.exp_pos (x 0)) (radius_pos hM (x 0))).ne'),
    ofContDiff (fun x => (radius M (x 0) ^ 2)⁻¹)
      (((contDiff_radius M).pow 2).inv fun x => (pow_pos (radius_pos hM (x 0)) 2).ne')]

theorem lowerOp_mul_upperOp (hM : 0 ≤ M) (μ : Fin 3) : lowerOp hM μ * upperOp hM μ = 1 := by
  ext x
  have hr := (radius_pos hM (x 0)).ne'
  have he := (Real.exp_pos (x 0)).ne'
  fin_cases μ <;>
    simp only [lowerOp, upperOp, ContMDiffMap.coe_mul, Pi.mul_apply, ContMDiffMap.coe_one,
      Pi.one_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, ofContDiff_apply]
  · field_simp
  · field_simp
  · field_simp

/-- A function of the co-ordinate `s`. -/
def ofRadial (f : SmoothOperation 1) : FreeSmoothRing (Fin 3) := op f fun _ => generator 1

/-- The metric of the equatorial plane in the co-ordinates `(t, s, φ)`. -/
def metric (hM : 0 ≤ M) : Fin 3 → Fin 3 → FreeSmoothRing (Fin 3) :=
  Matrix.diagonal fun μ => ofRadial (lowerOp hM μ)

/-- The inverse metric. -/
def inverse (hM : 0 ≤ M) : Fin 3 → Fin 3 → FreeSmoothRing (Fin 3) :=
  Matrix.diagonal fun μ => ofRadial (upperOp hM μ)

theorem metric_symm (hM : 0 ≤ M) (μ ν : Fin 3) : metric hM μ ν = metric hM ν μ :=
  (Matrix.isSymm_diagonal _).apply ν μ

theorem inverse_symm (hM : 0 ≤ M) (μ ν : Fin 3) : inverse hM μ ν = inverse hM ν μ :=
  (Matrix.isSymm_diagonal _).apply ν μ

theorem metric_mul_inverse (hM : 0 ≤ M) (μ ν : Fin 3) :
    ∑ l, metric hM μ l * inverse hM l ν = if μ = ν then 1 else 0 := by
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) (FreeSmoothRing (Fin 3)) => A μ ν)
    (Matrix.diagonal_mul_diagonal (fun μ => ofRadial (lowerOp hM μ))
      (fun μ => ofRadial (upperOp hM μ)))
  simp only [Matrix.mul_apply] at h
  rw [metric, inverse, h, Matrix.diagonal_apply]
  split_ifs with hμν
  · rw [ofRadial, ofRadial, ← op_mul, lowerOp_mul_upperOp, op_one]
  · rfl

theorem partialDerivation_diagonal {k : Fin 3} (hk : k ≠ 1) (a : Fin 3 → SmoothOperation 1)
    (μ ν : Fin 3) : partialDerivation k (Matrix.diagonal (fun μ => ofRadial (a μ)) μ ν) = 0 := by
  rw [Matrix.diagonal_apply]
  split_ifs
  · exact partialDerivation_op_eq_zero k _ (fun _ => 1) fun _ => Ne.symm hk
  · exact map_zero _

/-- The metric depends on `s` only. -/
theorem partialDerivation_metric {k : Fin 3} (hk : k ≠ 1) (hM : 0 ≤ M) (μ ν : Fin 3) :
    partialDerivation k (metric hM μ ν) = 0 :=
  partialDerivation_diagonal hk _ μ ν

/-- The inverse metric depends on `s` only. -/
theorem partialDerivation_inverse {k : Fin 3} (hk : k ≠ 1) (hM : 0 ≤ M) (μ ν : Fin 3) :
    partialDerivation k (inverse hM μ ν) = 0 :=
  partialDerivation_diagonal hk _ μ ν

/-- The trajectories of the geodesic Hamiltonian are the geodesics of the chart. -/
theorem isTrajectory_iff (hM : 0 ≤ M) (c : Fin 3 ⊕ Fin 3 → TimeFunction) :
    IsTrajectory (canonical (Fin 3)) (hamiltonian (inverse hM)) c ↔
      (∀ μ, c (Sum.inr μ) =
        ∑ ν, lift (position c) (metric hM μ ν) * timeDerivative (position c ν)) ∧
        IsCoordinateGeodesic (metric hM) (position c) :=
  GeodesicHamiltonian.isTrajectory_iff (metric_symm hM) (metric_mul_inverse hM) c

/-- The energy `−p_t` is an integral of the motion: the metric does not depend on `t`. -/
theorem isIntegral_p_time (hM : 0 ≤ M) :
    (canonical (Fin 3)).IsIntegral (hamiltonian (inverse hM)) (p 0) :=
  isIntegral_p_of_metric_independent (metric_mul_inverse hM)
    (partialDerivation_metric (by decide) hM)

/-- The angular momentum `p_φ` is an integral of the motion: the metric does not depend on
`φ`. -/
theorem isIntegral_p_angle (hM : 0 ≤ M) :
    (canonical (Fin 3)).IsIntegral (hamiltonian (inverse hM)) (p 2) :=
  isIntegral_p_of_metric_independent (metric_mul_inverse hM)
    (partialDerivation_metric (by decide) hM)

/-- `∂_t` is a Killing field: `L_{∂_t} g = 0`. -/
theorem lieMetric_time (hM : 0 ≤ M) (μ ν : Fin 3) :
    lieMetric (coordinateField 0) (metric hM) μ ν = 0 := by
  rw [lieMetric_coordinateField]
  exact partialDerivation_metric (by decide) hM μ ν

/-- `L_{∂_t} g⁻¹ = 0`. -/
theorem lieInverse_time (hM : 0 ≤ M) (μ ν : Fin 3) :
    lieInverse (coordinateField 0) (inverse hM) μ ν = 0 := by
  rw [lieInverse_coordinateField]
  exact partialDerivation_inverse (by decide) hM μ ν

/-- The momentum of `∂_t` is an integral, by the criterion of the inverse metric. -/
theorem isIntegral_vectorMomentum_time (hM : 0 ≤ M) :
    (canonical (Fin 3)).IsIntegral (hamiltonian (inverse hM))
      (vectorMomentum (coordinateField 0)) :=
  (isIntegral_vectorMomentum_iff (inverse_symm hM) _).mpr (lieInverse_time hM)

theorem lift_ofRadial_apply (f : SmoothOperation 1) (x : Fin 3 → TimeFunction)
    (τ : Fin 1 → ℝ) : lift x (ofRadial f) τ = f fun _ => x 1 τ := by
  rw [ofRadial, SmoothRingHom.map_op]
  simp only [lift_generator]
  rfl

/-- `g(∂_t, ∂_t) = −(1 − 2M/r)`. -/
theorem norm2_time (hM : 0 ≤ M) (x : Fin 3 → TimeFunction) (τ : Fin 1 → ℝ) :
    norm2 (metric hM) (coordinateField 0) x τ = -(1 - 2 * M / radius M (x 1 τ)) := by
  rw [norm2_coordinateField, metric, Matrix.diagonal_apply_eq, lift_ofRadial_apply]
  rw [← exp_div_radius _ _ hM]
  rfl

/-- `∂_t` is timelike at every point: `g(∂_t, ∂_t) < 0`. -/
theorem norm2_time_neg (hM : 0 ≤ M) (x : Fin 3 → TimeFunction) (τ : Fin 1 → ℝ) :
    norm2 (metric hM) (coordinateField 0) x τ < 0 := by
  rw [norm2_coordinateField, metric, Matrix.diagonal_apply_eq, lift_ofRadial_apply]
  change -(Real.exp (x 1 τ) / radius M (x 1 τ)) < 0
  exact neg_neg_of_pos (div_pos (Real.exp_pos _) (radius_pos hM _))

/-- The rate `N = √(1 − 2M/r)` of the proper time of a static observer. -/
theorem killingNorm_eq (hM : 0 ≤ M) (x : Fin 3 → TimeFunction) (τ : Fin 1 → ℝ) :
    killingNorm (metric hM) (coordinateField 0) x τ =
      Real.sqrt (1 - 2 * M / radius M (x 1 τ)) := by
  rw [killingNorm, norm2_time hM, neg_neg]

/-- **The gravitational red shift.** Along every trajectory, a curve defined for all values of
the affine parameter, the frequency `ω` measured by the static observers satisfies
`√(1 − 2M/r) ω = const`. -/
theorem killingNorm_mul_frequency_eq (hM : 0 ≤ M) {c : Fin 3 ⊕ Fin 3 → TimeFunction}
    (h : IsTrajectory (canonical (Fin 3)) (hamiltonian (inverse hM)) c) (s t : Fin 1 → ℝ) :
    Real.sqrt (1 - 2 * M / radius M (position c 1 s)) *
        frequency (metric hM) (coordinateField 0) (position c) s =
      Real.sqrt (1 - 2 * M / radius M (position c 1 t)) *
        frequency (metric hM) (coordinateField 0) (position c) t := by
  rw [← killingNorm_eq hM, ← killingNorm_eq hM]
  exact GeodesicHamiltonian.killingNorm_mul_frequency_eq (metric_symm hM) (metric_mul_inverse hM)
    h (lieMetric_time hM) (norm2_time_neg hM _ s) (norm2_time_neg hM _ t)

end ProjectAinos.GeneralRelativity.GeodesicHamiltonian.SchwarzschildEquatorial
