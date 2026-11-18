/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.EinsteinEquations
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateScalarField

/-!
# The scalar field on a fixed background

Landau–Lifshitz, §94: the energy-momentum tensor of matter is conserved by virtue of the
equations of the matter field, on a fixed metric. For the scalar field of `MatterAction.scalarField`
on a metric given by coefficients on an open set `U` of `ℝ⁴`:

* `isFieldStationary_iff_kleinGordon`: its action is stationary under every smooth variation of
  the field with compact support in `U` if and only if `φ` satisfies the Klein–Gordon equation
  `□φ = m² φ` on `U`;
* `divergence_scalarStress`, `divergence_scalarStress_eq_zero`: the divergence of its Hilbert
  tensor is `∇^a T_{ab} = (□φ − m² φ) ∂_bφ`, so a solution of its own field equation has a conserved
  stress, without the Einstein equations;
* `kleinGordon_exp`: in Minkowski space `φ = e^{m x}` is a solution.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.EinsteinEquations

open SmoothGeometry CoordinateMetric
open LorentzMetric (chartField)

variable {U : Opens (MinkowskiModel 3)} (g : CoordinateMetric .timeNegative 3 U)

/-- The Klein–Gordon equation `□φ = m² φ` on `U`. -/
def KleinGordon (m : ℝ) (φ : MinkowskiModel 3 → ℝ) : Prop :=
  ∀ x ∈ U, g.boxOf φ x = m ^ 2 * φ x

variable {g} {φ : MinkowskiModel 3 → ℝ}

/-- **The field equation of the scalar field is the Klein–Gordon equation.** -/
theorem isFieldStationary_iff_kleinGordon (hφ : ContDiffOn ℝ ∞ φ U) (m : ℝ) :
    (∀ ψ : MinkowskiModel 3 → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      HasDerivAt (g.fieldAction m φ ψ) 0 0) ↔ KleinGordon g m φ :=
  isFieldStationary_iff hφ m

/-- The divergence of the stress of the scalar field: `∇^a T_{ab} = (□φ − m² φ) ∂_bφ`. -/
theorem divergence_scalarStress (hφ : ContDiffOn ℝ ∞ φ U) (m : ℝ) (y : U) (b : Fin (3 + 1)) :
    g.toLorentzMetric.bilinearDivergenceCovector
        (bilinearOf (MatterAction.scalarField g m φ hφ).stress
          (MatterAction.scalarField g m φ hφ).stress_smooth) y
        (chartField (physicalChart y) (Pi.single b 1) y) =
      (g.boxOf φ y - m ^ 2 * φ y) * fderiv ℝ φ y (Pi.single b 1) :=
  bilinearDivergence_scalarStress hφ m y b

/-- **The stress of a solution is conserved on the fixed background** (§94): if `□φ = m² φ`, then
`∇^a T_{ab} = 0`. -/
theorem divergence_scalarStress_eq_zero (hφ : ContDiffOn ℝ ∞ φ U) (m : ℝ)
    (hKG : KleinGordon g m φ) (y : U) :
    g.toLorentzMetric.bilinearDivergenceCovector
      (bilinearOf (MatterAction.scalarField g m φ hφ).stress
        (MatterAction.scalarField g m φ hφ).stress_smooth) y = 0 :=
  bilinearDivergence_scalarStress_eq_zero hφ m hKG y

/-! ### A solution in Minkowski space -/

local notation "η₄" => CoordinateMetric.minkowski LorentzConvention.timeNegative 3 ⊤

theorem hasFDerivAt_exp_coord (m : ℝ) (z : MinkowskiModel 3) :
    HasFDerivAt (fun x : MinkowskiModel 3 => Real.exp (m * x 1))
      ((Real.exp (m * z 1) * m) • (ContinuousLinearMap.proj 1 : MinkowskiModel 3 →L[ℝ] ℝ)) z := by
  have h := (((ContinuousLinearMap.proj 1 : MinkowskiModel 3 →L[ℝ] ℝ).hasFDerivAt
    (x := z)).const_mul m).exp
  convert h using 1
  · rfl
  · rw [smul_smul, ContinuousLinearMap.proj_apply]

/-- **In Minkowski space `φ = e^{m x}` solves the Klein–Gordon equation.** -/
theorem kleinGordon_exp (m : ℝ) : KleinGordon (η₄) m (fun x => Real.exp (m * x 1)) := by
  intro x _
  have hC : (η₄).coefficient = fun _ => Matrix.diagonal (lorentzSign (d := 3) .timeNegative) :=
    funext minkowski_coefficient
  have hd1 (b : Fin (3 + 1)) : (fun z => fderiv ℝ (fun x : MinkowskiModel 3 => Real.exp (m * x 1)) z
      (Pi.single b 1)) = fun z => Real.exp (m * z 1) * (m * (Pi.single b 1 : MinkowskiModel 3) 1) :=
    funext fun z => by
      rw [(hasFDerivAt_exp_coord m z).fderiv]
      simp
      ring
  have hd2 (a b : Fin (3 + 1)) : fderiv ℝ (fun z => Real.exp (m * z 1) *
      (m * (Pi.single b 1 : MinkowskiModel 3) 1)) x (Pi.single a 1) =
      Real.exp (m * x 1) * m * (Pi.single a 1 : MinkowskiModel 3) 1 *
        (m * (Pi.single b 1 : MinkowskiModel 3) 1) := by
    rw [((hasFDerivAt_exp_coord m x).mul_const (m * (Pi.single b 1 : MinkowskiModel 3) 1)).fderiv]
    simp
    ring
  have hinv : (Matrix.diagonal (lorentzSign (d := 3) .timeNegative))⁻¹ =
      Matrix.diagonal (lorentzSign (d := 3) .timeNegative) := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal]
    simp only [lorentzSign_sq, Matrix.diagonal_one]
  simp only [boxOf, hessianOf, hC, christoffelOf_const, zero_mul, Finset.sum_const_zero, sub_zero,
    hd1, hd2, hinv]
  simp [Matrix.diagonal_apply, lorentzSign, LorentzConvention.timeSign, Pi.single_apply]
  ring

end ProjectAinos.GeneralRelativity.EinsteinEquations
