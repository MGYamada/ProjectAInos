/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.QuadraticLagrangian
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Topology.Sets.Opens

/-! # Time-dependent Newtonian metric families in fixed physical coordinates

The family specifies coefficient data on a common open coordinate domain.
It assumes smoothness and uniform bounds through two spacetime derivatives,
not Lorentz signature, geodesic estimates or convergence. Those are separate
proof obligations. No regularity in the parameter `c` is required.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open ContinuousLinearMap Set TopologicalSpace
open scoped ContDiff Topology

namespace ProjectAInos.GeneralRelativity

/-- Physical coordinates `(t,x)`, with time first and three spatial coordinates. -/
abbrev NewtonianCoordinates := Fin 4 → ℝ
abbrev NewtonianSpace := Fin 3 → ℝ
abbrev NewtonianSpatialMatrix := Fin 3 → Fin 3 → ℝ

/-- A bound for values and the first two spacetime derivatives on a domain.
Derivatives are ordinary derivatives on the coordinate model, not in `c`. -/
structure CoordinateC2Bound {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : Set NewtonianCoordinates) (K : ℝ) (f : NewtonianCoordinates → F) : Prop where
  value : ∀ q ∈ U, ‖f q‖ ≤ K
  first : ∀ q ∈ U, ‖fderiv ℝ f q‖ ≤ K
  second : ∀ q ∈ U, ‖fderiv ℝ (fderiv ℝ f) q‖ ≤ K

theorem CoordinateC2Bound.mono {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U V : Set NewtonianCoordinates} {K L : ℝ} {f : NewtonianCoordinates → F}
    (h : CoordinateC2Bound U K f) (hUV : V ⊆ U) (hKL : K ≤ L) :
    CoordinateC2Bound V L f :=
  ⟨fun q hq => (h.value q (hUV hq)).trans hKL,
    fun q hq => (h.first q (hUV hq)).trans hKL,
    fun q hq => (h.second q (hUV hq)).trans hKL⟩

/-- A compact buffer gives an actual finite bound for fixed smooth coefficient data. -/
theorem exists_coordinateC2Bound {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : NewtonianCoordinates → F} {U K : Set NewtonianCoordinates}
    (hf : ContDiff ℝ 2 f) (hK : IsCompact K) (hUK : U ⊆ K) :
    ∃ C ≥ (0 : ℝ), CoordinateC2Bound U C f := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  obtain ⟨C₀, h₀, hb₀⟩ := (hK.image hf.continuous).isBounded.exists_pos_norm_le
  obtain ⟨C₁, h₁, hb₁⟩ := (hK.image hdf.continuous).isBounded.exists_pos_norm_le
  obtain ⟨C₂, h₂, hb₂⟩ :=
    (hK.image (hdf.continuous_fderiv (by norm_num))).isBounded.exists_pos_norm_le
  refine ⟨C₀ + C₁ + C₂, by positivity, ?_, ?_, ?_⟩
  · intro q hq
    exact (hb₀ _ ⟨q, hUK hq, rfl⟩).trans (by linarith)
  · intro q hq
    exact (hb₁ _ ⟨q, hUK hq, rfl⟩).trans (by linarith)
  · intro q hq
    exact (hb₂ _ ⟨q, hUK hq, rfl⟩).trans (by linarith)

/-- The prescribed-metric scaling class. All coefficients may depend on time.
The common bound applies to `c ≥ 1`; the limit only uses this tail. An open
buffer around the compact trajectory tube can be chosen as the domain `U`. -/
structure NewtonianMetricFamily (U : Opens NewtonianCoordinates) where
  potential : NewtonianCoordinates → ℝ
  timeCorrection : ℝ → NewtonianCoordinates → ℝ
  mixedCorrection : ℝ → NewtonianCoordinates → NewtonianSpace
  spatialCorrection : ℝ → NewtonianCoordinates → NewtonianSpatialMatrix
  potential_smooth : ContDiffOn ℝ ∞ potential U
  time_smooth : ∀ c > 0, ContDiffOn ℝ ∞ (timeCorrection c) U
  mixed_smooth : ∀ c > 0, ContDiffOn ℝ ∞ (mixedCorrection c) U
  spatial_smooth : ∀ c > 0, ContDiffOn ℝ ∞ (spatialCorrection c) U
  spatial_symmetric : ∀ c > 0, ∀ q ∈ U, ∀ i j, spatialCorrection c q i j = spatialCorrection c q j i
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  potential_bound : CoordinateC2Bound U bound potential
  time_bound : ∀ c ≥ 1, CoordinateC2Bound U bound (timeCorrection c)
  mixed_bound : ∀ c ≥ 1, CoordinateC2Bound U bound (mixedCorrection c)
  spatial_bound : ∀ c ≥ 1, CoordinateC2Bound U bound (spatialCorrection c)

namespace NewtonianMetricFamily
variable {U : Opens NewtonianCoordinates} (f : NewtonianMetricFamily U)

/-- `ε = c⁻²`; all estimates use positive `c`. -/
def epsilon (c : ℝ) : ℝ := (c ^ 2)⁻¹

/-- The full coefficient matrix in fixed physical-time coordinates. -/
def coefficient (c : ℝ) (q : NewtonianCoordinates) : Matrix (Fin 4) (Fin 4) ℝ :=
  Fin.cons (Fin.cons (-c ^ 2 - 2 * f.potential q + epsilon c * f.timeCorrection c q)
    (fun j => epsilon c * f.mixedCorrection c q j))
    (fun i => Fin.cons (epsilon c * f.mixedCorrection c q i)
      (fun j => (if i = j then 1 else 0) + epsilon c * f.spatialCorrection c q i j))

@[simp] theorem coefficient_time (c : ℝ) (q : NewtonianCoordinates) :
    f.coefficient c q 0 0 = -c ^ 2 - 2 * f.potential q + epsilon c * f.timeCorrection c q := rfl

@[simp] theorem coefficient_mixed (c : ℝ) (q : NewtonianCoordinates) (j : Fin 3) :
    f.coefficient c q 0 j.succ = epsilon c * f.mixedCorrection c q j := rfl

@[simp] theorem coefficient_spatial (c : ℝ) (q : NewtonianCoordinates) (i j : Fin 3) :
    f.coefficient c q i.succ j.succ =
      (if i = j then 1 else 0) + epsilon c * f.spatialCorrection c q i j := rfl

theorem coefficient_symmetric {c : ℝ} (hc : 0 < c) {q : NewtonianCoordinates}
    (hq : q ∈ U) (i j : Fin 4) : f.coefficient c q i j = f.coefficient c q j i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases rfl (fun _ => rfl) j
  · refine Fin.cases rfl (fun j => ?_) j
    simp only [coefficient_spatial, f.spatial_symmetric c hc q hq i j, eq_comm]

theorem coefficient_contDiffOn {c : ℝ} (hc : 0 < c) (i j : Fin 4) :
    ContDiffOn ℝ ∞ (fun q => f.coefficient c q i j) U := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact (contDiffOn_const.sub (contDiffOn_const.mul f.potential_smooth)).add
        (contDiffOn_const.mul (f.time_smooth c hc))
    · exact contDiffOn_const.mul (contDiffOn_pi.mp (f.mixed_smooth c hc) j)
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact contDiffOn_const.mul (contDiffOn_pi.mp (f.mixed_smooth c hc) i)
    · exact contDiffOn_const.add
        (contDiffOn_const.mul (contDiffOn_pi.mp (contDiffOn_pi.mp (f.spatial_smooth c hc) i) j))

/-- The coefficient bilinear form. Its Lorentz signature is not assumed. -/
def form (c : ℝ) (q : NewtonianCoordinates) :
    NewtonianCoordinates →L[ℝ] NewtonianCoordinates →L[ℝ] ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, f.coefficient c q i j •
    (proj i : NewtonianCoordinates →L[ℝ] ℝ).smulRight (proj j)

theorem form_apply (c : ℝ) (q v w : NewtonianCoordinates) :
    f.form c q v w = ∑ i : Fin 4, ∑ j : Fin 4, f.coefficient c q i j * v i * w j := by
  simp [form, mul_assoc]

theorem form_contDiffOn {c : ℝ} (hc : 0 < c) : ContDiffOn ℝ ∞ (f.form c) U := by
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j _
  let L : ℝ →L[ℝ] (NewtonianCoordinates →L[ℝ] NewtonianCoordinates →L[ℝ] ℝ) :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight
      ((proj i : NewtonianCoordinates →L[ℝ] ℝ).smulRight (proj j))
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := ℝ)
    (F := NewtonianCoordinates →L[ℝ] NewtonianCoordinates →L[ℝ] ℝ) L).comp_contDiffOn
      (f.coefficient_contDiffOn hc i j)

/-- Velocity when physical time itself is the parameter. -/
def timeVelocity (v : NewtonianSpace) : NewtonianCoordinates := Fin.cons 1 v

/-- The exact quadratic expression retains all three correction families. -/
theorem form_timeVelocity (c : ℝ) (q : NewtonianCoordinates) (v : NewtonianSpace) :
    f.form c q (timeVelocity v) (timeVelocity v) =
      -c ^ 2 - 2 * f.potential q + epsilon c * f.timeCorrection c q +
        2 * epsilon c * (∑ i : Fin 3, f.mixedCorrection c q i * v i) +
        (∑ i : Fin 3, v i ^ 2) +
        epsilon c * (∑ i : Fin 3, ∑ j : Fin 3, f.spatialCorrection c q i j * v i * v j) := by
  rw [form_apply]
  simp only [Fin.sum_univ_succ, coefficient, timeVelocity, Fin.cons_zero, Fin.cons_succ]
  norm_num [Fin.sum_univ_succ]
  ring

/-- The restriction to the spatial hyperplane retains the full spatial correction. -/
theorem form_spatial (c : ℝ) (q : NewtonianCoordinates) (v : NewtonianSpace) :
    f.form c q (Fin.cons 0 v) (Fin.cons 0 v) = (∑ i : Fin 3, v i ^ 2) +
      epsilon c * (∑ i : Fin 3, ∑ j : Fin 3, f.spatialCorrection c q i j * v i * v j) := by
  rw [form_apply]
  simp only [Fin.sum_univ_succ, coefficient, Fin.cons_zero, Fin.cons_succ]
  norm_num [Fin.sum_univ_succ]
  ring

end NewtonianMetricFamily
end ProjectAInos.GeneralRelativity
