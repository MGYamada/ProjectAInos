/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Potential.NewtonPotential
public import ProjectAinos.Electrodynamics.Components
public import ProjectAinos.Electrodynamics.ThreePlusOne
import Mathlib.Tactic

/-!
# Coulomb's law

The units have `div E = ρ` and `E = −∇φ`, so the potential of a charge density `ρ` solves
Poisson's equation `−Δφ = ρ` (Landau–Lifshitz, *The Classical Theory of Fields*, §36). Space is
`EuclideanSpace ℝ (Fin 3)`, `Minkowski.Space 3`, with the Euclidean norm. For a `C²` density of
compact support the potential is the Newton potential `φ = ρ ⋆ 1/(4π|x|)` of
`SmoothGeometry.Potential`:

* `neg_laplacian_newtonPotential`: `−Δφ = ρ`, and `div_coulombField`: the field
  `coulombField ρ = −∇φ` satisfies `div E = ρ`;
* `abs_coulombField_le`: outside a ball `|y| ≤ a` that contains the support,
  `|Eᵢ(x)| ≤ Q/(4π(|x| − a)²)` with `Q = ∫|ρ|`; the potential satisfies
  `|φ(x)| ≤ Q/(4π(|x| − a))` (`abs_newtonPotential_le`) and tends to `0` at infinity
  (`tendsto_newtonPotential_cocompact`);
* uniqueness, `eq_newtonPotential_of_tendsto`: a `C²` solution of `−Δu = ρ` that tends to `0` at
  infinity is the Newton potential.

On space-time the potential is `A = −φ dt` (`electrostaticPotential`):
`electricField_electrostaticPotential` gives `E = −∇φ` and `magneticField_electrostaticPotential`
gives `B = 0`, and `maxwell_electrostaticPotential` states the four equations of Maxwell in the
frame of the co-ordinates with the static current `(ρ, 0)`.

The point charge is a separate statement. Its potential `q/(4π|x|)` is harmonic away from the
charge (`harmonicAt_pointChargePotential`), its field is the Coulomb field
`pointChargeField q x = q x/(4π|x|³)` (`inner_pointChargeField`), whose flux through every sphere
about the charge is `q` (`flux_pointChargeField`), and
`integral_pointChargePotential_mul_laplacian` is `−Δ(q/(4π|x|)) = q δ` in pairing form:
`∫ q/(4π|x|) Δχ = −q χ(0)` for every `C²` function `χ` of compact support.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real
open scoped Topology Laplacian ContDiff

namespace ProjectAinos.Electrodynamics.Electrostatics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Potential SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Poisson's equation and the field -/

/-- **Poisson's equation** for the potential of a `C²` charge density of compact support:
`−Δφ = ρ`. -/
theorem neg_laplacian_newtonPotential {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (p : E3) : -Δ (newtonPotential ρ) p = ρ p := by
  rw [laplacian_newtonPotential hcρ hρ, neg_neg]

/-- The electrostatic field `E = −∇φ` of a charge density, in the co-ordinates. -/
def coulombField (ρ : E3 → ℝ) (p : E3) : Fin 3 → ℝ :=
  fun i => -fderiv ℝ (newtonPotential ρ) p (EuclideanSpace.single i 1)

/-- **Gauss's law** `div E = ρ` for the field of a `C²` charge density of compact support. -/
theorem div_coulombField {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (p : E3) :
    ∑ i, fderiv ℝ (fun q => coulombField ρ q i) p (EuclideanSpace.single i 1) = ρ p := by
  have hφ := contDiff_two_newtonPotential hcρ hρ
  have h := laplacian_newtonPotential hcρ hρ p
  rw [← coordLaplacian_eq_laplacian hφ.contDiffAt] at h
  have hterm (i : Fin 3) :
      fderiv ℝ (fun q => coulombField ρ q i) p (EuclideanSpace.single i 1) =
        -fderiv ℝ (fun q => fderiv ℝ (newtonPotential ρ) q (EuclideanSpace.single i 1)) p
          (EuclideanSpace.single i 1) := by
    simp only [coulombField]
    rw [fderiv_fun_neg]
    rfl
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_neg_distrib]
  change -coordLaplacian (newtonPotential ρ) p = ρ p
  rw [h, neg_neg]

/-- **Decay of the field**: `|Eᵢ(x)| ≤ Q/(4π(|x| − a)²)` with `Q = ∫|ρ|`, outside a ball
`|y| ≤ a` that contains the support of `ρ`. -/
theorem abs_coulombField_le {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ)
    {a : ℝ} (ha : tsupport ρ ⊆ closedBall 0 a) {p : E3} (hp : a < ‖p‖) (i : Fin 3) :
    |coulombField ρ p i| ≤ (∫ y, |ρ y|) / (4 * π * (‖p‖ - a) ^ 2) := by
  have h := (fderiv ℝ (newtonPotential ρ) p).le_opNorm (EuclideanSpace.single i 1)
  have h1 : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
  rw [h1, mul_one, Real.norm_eq_abs] at h
  rw [coulombField, abs_neg]
  exact h.trans (norm_fderiv_newtonPotential_le hρ hcρ ha hp)

/-! ### The potential on space-time -/

/-- The four-potential `A = −φ dt` of the electrostatic potential of a charge density. -/
def electrostaticPotential (ρ : E3 → ℝ) : Potential :=
  potentialOf (fun y => newtonPotential ρ (space y)) 0

/-- The four-potential is `−φ dt`. -/
theorem electrostaticPotential_eq (ρ : E3 → ℝ) :
    electrostaticPotential ρ =
      fun y => (-newtonPotential ρ (space y)) • oneCovector.symm (ContinuousLinearMap.proj 0) := by
  funext y
  simp [electrostaticPotential, potentialOf]

/-- The axis of the time has no part in space. -/
theorem space_pi_single_zero : space (Pi.single 0 1 : Spacetime) = 0 := by
  ext j
  simp [space_apply, Fin.succ_ne_zero]

/-- The part in space of the axis `i + 1` of space-time is the axis `i` of space. -/
theorem space_pi_single_succ (i : Fin 3) :
    space (Pi.single i.succ 1 : Spacetime) = EuclideanSpace.single i 1 := by
  ext j
  simp [space_apply, Pi.single_apply, PiLp.single_apply, Fin.succ_inj, eq_comm]

/-- The derivative of a function of the position along a vector of space-time is its derivative
along the part in space. -/
theorem fderiv_comp_space_apply {g : E3 → ℝ} {y : Spacetime} (hg : DifferentiableAt ℝ g (space y))
    (v : Spacetime) : fderiv ℝ (fun z => g (space z)) y v = fderiv ℝ g (space y) (space v) := by
  have h := hg.hasFDerivAt.comp y space.hasFDerivAt
  rw [show (fun z => g (space z)) = g ∘ space from rfl, h.fderiv]
  rfl

/-- The derivative of the four-potential of a `C¹` density of compact support is
`−(Dφ ∘ space) ⊗ dt`. -/
theorem hasFDerivAt_electrostaticPotential {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 1 ρ) (y : Spacetime) :
    HasFDerivAt (electrostaticPotential ρ)
      ((-(fderiv ℝ (newtonPotential ρ) (space y)).comp
        (space : Spacetime →L[ℝ] Space 3)).smulRight
          (oneCovector.symm (ContinuousLinearMap.proj 0))) y := by
  have hφ : ContDiff ℝ 1 (newtonPotential ρ) := by
    have h := contDiff_newtonPotential (n := 1) hcρ (by exact_mod_cast hρ)
    exact_mod_cast h
  rw [electrostaticPotential_eq]
  exact (((hφ.differentiable (by norm_num) (space y)).hasFDerivAt.comp y
    space.hasFDerivAt).neg).smul_const (oneCovector.symm (ContinuousLinearMap.proj 0))

/-- The field of `−φ dt`: `F(v, w) = Dφ(w⃗) v⁰ − Dφ(v⃗) w⁰`. -/
theorem fieldTensor_electrostaticPotential_apply {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 1 ρ) (y v w : Spacetime) :
    fieldTensor (electrostaticPotential ρ) y ![v, w] =
      fderiv ℝ (newtonPotential ρ) (space y) (space w) * v 0 -
        fderiv ℝ (newtonPotential ρ) (space y) (space v) * w 0 := by
  rw [fieldTensor_apply, (hasFDerivAt_electrostaticPotential hcρ hρ y).fderiv]
  simp
  ring

/-- The electric field of `−φ dt` is `E = −∇φ`. -/
theorem electricField_electrostaticPotential {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 1 ρ) (i : Fin 3) (y : Spacetime) :
    electricField (fieldTensor (electrostaticPotential ρ)) i y = coulombField ρ (space y) i := by
  rw [electricField, electricVector_apply, component,
    fieldTensor_electrostaticPotential_apply hcρ hρ, space_pi_single_zero, space_pi_single_succ]
  simp [coulombField, Fin.succ_ne_zero]

/-- The field of `−φ dt` has no magnetic part. -/
theorem magneticField_electrostaticPotential {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 1 ρ) (i : Fin 3) (y : Spacetime) :
    magneticField (fieldTensor (electrostaticPotential ρ)) i y = 0 := by
  rw [magneticField]
  fin_cases i <;>
    simp [magneticVector, component, fieldTensor_electrostaticPotential_apply hcρ hρ]

/-- **The equations of Maxwell for a static charge**: for a `C²` density of compact support the
field of `A = −φ dt` satisfies `div B = 0`, `∂_t B + curl E = 0`, `div E = ρ` and
`curl B − ∂_t E = 0` at every event, with the density at the position of the event. -/
theorem maxwell_electrostaticPotential {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (y : Spacetime) :
    (divergence3 (magneticField (fieldTensor (electrostaticPotential ρ))) y = 0 ∧
      ∀ i, partialAt (magneticField (fieldTensor (electrostaticPotential ρ)) i) 0 y +
        curl (electricField (fieldTensor (electrostaticPotential ρ))) y i = 0) ∧
    (divergence3 (electricField (fieldTensor (electrostaticPotential ρ))) y = ρ (space y) ∧
      ∀ i, curl (magneticField (fieldTensor (electrostaticPotential ρ))) y i -
        partialAt (electricField (fieldTensor (electrostaticPotential ρ)) i) 0 y = 0) := by
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by norm_num)
  have hφ := contDiff_two_newtonPotential hcρ hρ
  have hA : ContDiff ℝ 2 (electrostaticPotential ρ) := by
    rw [electrostaticPotential_eq]
    exact ((hφ.comp space.contDiff).neg).smul contDiff_const
  have hE : electricField (fieldTensor (electrostaticPotential ρ)) =
      fun i z => coulombField ρ (space z) i := by
    funext i z
    exact electricField_electrostaticPotential hcρ hρ1 i z
  have hB : magneticField (fieldTensor (electrostaticPotential ρ)) = fun _ _ => 0 := by
    funext i z
    exact magneticField_electrostaticPotential hcρ hρ1 i z
  have hdE (i : Fin 3) : Differentiable ℝ fun q => coulombField ρ q i := fun q =>
    (((hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num) q).neg
  refine ⟨homogeneous_fieldTensor isOpen_univ hA.contDiffOn (mem_univ y), ?_, fun i => ?_⟩
  · rw [hE, ← div_coulombField hcρ hρ (space y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [partialAt, fderiv_comp_space_apply (hdE i _), space_pi_single_succ]
  · rw [hB, hE, partialAt, fderiv_comp_space_apply (hdE i _), space_pi_single_zero]
    fin_cases i <;> simp [curl, partialAt]

/-! ### The point charge -/

/-- The potential `q/(4π|x|)` of a point charge `q` at the origin. -/
def pointChargePotential (q : ℝ) (x : E3) : ℝ := q * newtonKernel x

/-- The Coulomb field `E_q(x) = q x/(4π|x|³)` of a point charge `q` at the origin. -/
def pointChargeField (q : ℝ) (x : E3) : E3 := (q / (4 * π * ‖x‖ ^ 3)) • x

/-- The potential of a point charge is harmonic away from the charge. -/
theorem harmonicAt_pointChargePotential (q : ℝ) {x : E3} (hx : x ≠ 0) :
    InnerProductSpace.HarmonicAt (pointChargePotential q) x := by
  have h := (harmonicAt_newtonKernel hx).const_smul (c := q)
  exact h

/-- **The Coulomb field is `−∇` of the potential** away from the charge:
`⟨E_q(x), v⟩ = −D(q/(4π|x|)) v`. -/
theorem inner_pointChargeField (q : ℝ) {x : E3} (hx : x ≠ 0) (v : E3) :
    inner ℝ (pointChargeField q x) v = -fderiv ℝ (pointChargePotential q) x v := by
  have h : HasFDerivAt (pointChargePotential q)
      (q • (-(4 * π * ‖x‖ ^ 3)⁻¹ • innerSL ℝ x)) x :=
    (hasFDerivAt_newtonKernel hx).const_mul q
  rw [h.fderiv]
  simp [pointChargeField, real_inner_smul_left]
  ring

/-- **Gauss's law for a point charge**: the flux of the Coulomb field through the sphere of
radius `R > 0` is `q`, `∫_{|u| = 1} ⟨E_q(Ru), u⟩ R² du = q`, with the surface measure
`volume.toSphere` of the unit sphere. -/
theorem flux_pointChargeField (q : ℝ) {R : ℝ} (hR : 0 < R) :
    ∫ u : sphere (0 : E3) 1, inner ℝ (pointChargeField q (R • (u : E3))) u * R ^ 2
      ∂(volume.toSphere) = q := by
  have h (u : sphere (0 : E3) 1) :
      inner ℝ (pointChargeField q (R • (u : E3))) u * R ^ 2 = q / (4 * π) := by
    have hu1 : ‖(u : E3)‖ = 1 := by simp
    rw [pointChargeField, norm_smul, hu1, Real.norm_of_nonneg hR.le, real_inner_smul_left,
      real_inner_smul_left, real_inner_self_eq_norm_sq, hu1]
    field_simp
  have hvol : (volume : Measure E3).real (ball 0 1) = π * 4 / 3 := by
    simp [Measure.real, ENNReal.toReal_ofReal (by positivity : 0 ≤ π * 4 / 3)]
  simp_rw [h]
  rw [integral_const, smul_eq_mul, Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin,
    hvol]
  field_simp
  norm_num

/-- **The point source in pairing form**, `−Δ(q/(4π|x|)) = q δ`: for every `C²` function `χ` of
compact support, `∫ q/(4π|x|) Δχ = −q χ(0)`. -/
theorem integral_pointChargePotential_mul_laplacian (q : ℝ) {χ : E3 → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hcχ : HasCompactSupport χ) :
    ∫ x, pointChargePotential q x * Δ χ x = -(q * χ 0) := by
  simp only [pointChargePotential, mul_assoc]
  rw [integral_const_mul, integral_newtonKernel_mul_laplacian hχ hcχ, mul_neg]

end ProjectAinos.Electrodynamics.Electrostatics
