/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateMetric
public import ProjectAinos.SmoothGeometry.Lorentzian.InertialDerivatives
public import ProjectAinos.SmoothGeometry.MetricDensity

/-!
# Curvature of a coordinate metric from its coefficients

For a matrix of coefficients `C : E → Matrix`, given on the model space `E`, the Christoffel
symbols, the Ricci tensor, the scalar curvature and the volume density have the classical
formulas (`christoffelOf`, `ricciOf`, `scalarOf`, `densityOf`); the derivatives are Fréchet
derivatives on `E`. For a coordinate metric on an open set `U` these are the native quantities
of `toLorentzMetric` in the inclusion chart:

* `toLorentzMetric_chartCurvature`: `R^l_{ijk} = ∂_i Γ^l_{jk} − ∂_j Γ^l_{ik} + Γ^l_{ia} Γ^a_{jk}
  − Γ^l_{ja} Γ^a_{ik}`;
* `toLorentzMetric_ricci_chartField`, `toLorentzMetric_scalarCurvature`,
  `toLorentzMetric_chartDensity`.

`contDiffAt_matrix_inv_apply` gives the smoothness of the entries of the inverse matrix where
the determinant does not vanish, and `contDiffOn_christoffelOf` the smoothness of the
Christoffel symbols on `U`.
-/

@[expose] public section

noncomputable section

open Bundle ContinuousLinearMap Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

/-- The entries of the inverse matrix are smooth where the determinant does not vanish. -/
theorem contDiffAt_matrix_inv_apply {n : ℕ} {A : Fin n → Fin n → ℝ}
    (hA : (Matrix.of A).det ≠ 0) (k l : Fin n) :
    ContDiffAt ℝ ∞ (fun B : Fin n → Fin n → ℝ => (Matrix.of B)⁻¹ k l) A := by
  have hform : (fun B : Fin n → Fin n → ℝ => (Matrix.of B)⁻¹ k l) = fun B =>
      ((Matrix.of B).det)⁻¹ * Matrix.det (Matrix.of (Function.update B l (Pi.single k 1))) := by
    funext B
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv',
      Matrix.adjugate_apply]
    rfl
  have hupd : ContDiff ℝ ∞ (fun B : Fin n → Fin n → ℝ =>
      Function.update B l (Pi.single k (1 : ℝ))) := by
    refine contDiff_pi.2 fun i => ?_
    by_cases hi : i = l
    · subst hi
      simp only [Function.update_self]
      exact contDiff_const
    · simp only [Function.update_of_ne hi]
      exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℝ) i).contDiff
  rw [hform]
  exact ((contDiffAt_inv ℝ hA).comp A MetricDensity.contDiff_matrix_det.contDiffAt).mul
    (MetricDensity.contDiff_matrix_det.comp hupd).contDiffAt

namespace CoordinateMetric

/-! ### Formulas from a matrix of coefficients -/

/-- The Christoffel symbols `Γ^k_{ij} = ½ C^{kl}(∂_i C_{jl} + ∂_j C_{li} − ∂_l C_{ij})`. -/
def christoffelOf (C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (y : MinkowskiModel d) (k i j : Fin (d + 1)) : ℝ :=
  ∑ l, (C y)⁻¹ k l *
    (fderiv ℝ (fun z => C z j l) y (Pi.single i 1) +
     fderiv ℝ (fun z => C z l i) y (Pi.single j 1) -
     fderiv ℝ (fun z => C z i j) y (Pi.single l 1)) / 2

/-- The Ricci tensor
`Ric_{jk} = ∂_i Γ^i_{jk} − ∂_j Γ^i_{ik} + Γ^i_{ia} Γ^a_{jk} − Γ^i_{ja} Γ^a_{ik}`. -/
def ricciOf (C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (y : MinkowskiModel d) (j k : Fin (d + 1)) : ℝ :=
  ∑ i, (fderiv ℝ (fun z => christoffelOf C z i j k) y (Pi.single i 1) -
    fderiv ℝ (fun z => christoffelOf C z i i k) y (Pi.single j 1) +
    ∑ a, (christoffelOf C y i i a * christoffelOf C y a j k -
      christoffelOf C y i j a * christoffelOf C y a i k))

/-- The scalar curvature `R = C^{ac} Ric_{ac}`. -/
def scalarOf (C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (y : MinkowskiModel d) : ℝ :=
  ∑ a, ∑ c, ricciOf C y a c * (C y)⁻¹ a c

/-- The volume density `√|det C|`. -/
def densityOf (C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (y : MinkowskiModel d) : ℝ :=
  Real.sqrt |(C y).det|

/-! ### Derivatives on an open set of the model -/

variable {U : Opens (MinkowskiModel d)}

/-- The derivative of a function of the points of `U` along a co-ordinate field is the
Fréchet derivative of the function on the model. -/
theorem mvfderiv_val (x y : U) {F : MinkowskiModel d → ℝ}
    (hF : DifferentiableAt ℝ F y) (v : MinkowskiModel d) :
    mvfderiv 𝓘(ℝ, MinkowskiModel d) (fun z : U => F z) y (chartField (physicalChart x) v y) =
      fderiv ℝ F y v := by
  have hG : MDifferentiableAt 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, ℝ) (fun z : U => F z) y :=
    hF.mdifferentiableAt.comp y
      (((contMDiff_subtype_val (n := 1) (U := U)) y).mdifferentiableAt one_ne_zero)
  rw [mvfderiv_chartField (physicalChart_mem x) (by simp) hG]
  have hEq : (fun z : U => F z) ∘ (physicalChart x).symm =ᶠ[𝓝 (y : MinkowskiModel d)] F := by
    filter_upwards [U.isOpen.mem_nhds y.property] with z hz
    change F ((physicalChart x).symm z : MinkowskiModel d) = F z
    rw [← physicalChart_apply x ((physicalChart x).symm z),
      (physicalChart x).right_inv (by simpa using hz)]
  rw [physicalChart_apply, hEq.fderiv_eq]

variable (g : CoordinateMetric σ d U)

theorem coefficient_det_ne_zero (y : U) : (g.coefficient y).det ≠ 0 := by
  have h := congrArg Matrix.det (g.coefficient_mul_inv y)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact left_ne_zero_of_mul_eq_one h

theorem contDiffOn_coefficient_inv (k l : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => (g.coefficient z)⁻¹ k l) U := by
  intro z hz
  have hC : ContDiffAt ℝ ∞ (fun z => fun i j => g.coefficient z i j) z :=
    contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j =>
      (g.coefficient_contDiffOn i j).contDiffAt (U.isOpen.mem_nhds hz)
  exact ((contDiffAt_matrix_inv_apply (g.coefficient_det_ne_zero ⟨z, hz⟩) k l).comp z
    hC).contDiffWithinAt

theorem contDiffOn_fderiv_coefficient (i j : Fin (d + 1)) (v : MinkowskiModel d) :
    ContDiffOn ℝ ∞ (fun z => fderiv ℝ (fun y => g.coefficient y i j) z v) U :=
  ((g.coefficient_contDiffOn i j).fderiv_of_isOpen U.isOpen (by simp)).clm_apply
    contDiffOn_const

theorem contDiffOn_christoffelOf (k i j : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => christoffelOf g.coefficient z k i j) U := by
  unfold christoffelOf
  refine ContDiffOn.sum fun l _ => ?_
  exact ((g.contDiffOn_coefficient_inv k l).mul
    (((g.contDiffOn_fderiv_coefficient j l _).add (g.contDiffOn_fderiv_coefficient l i _)).sub
      (g.contDiffOn_fderiv_coefficient i j _))).div_const 2

/-! ### The native quantities in the inclusion chart -/

theorem toLorentzMetric_chartChristoffel (x y : U) (k i j : Fin (d + 1)) :
    g.toLorentzMetric.chartChristoffel (physicalChart x) y k i j =
      christoffelOf g.coefficient y k i j :=
  g.toLorentzMetric_christoffel x y k i j

/-- The curvature components in the inclusion chart. -/
theorem toLorentzMetric_chartCurvature (x y : U) (l i j k : Fin (d + 1)) :
    g.toLorentzMetric.chartCurvature (physicalChart x) y l i j k =
      fderiv ℝ (fun z => christoffelOf g.coefficient z l j k) y (Pi.single i 1) -
      fderiv ℝ (fun z => christoffelOf g.coefficient z l i k) y (Pi.single j 1) +
      ∑ a, (christoffelOf g.coefficient y l i a * christoffelOf g.coefficient y a j k -
        christoffelOf g.coefficient y l j a * christoffelOf g.coefficient y a i k) := by
  have hΓ (a b c : Fin (d + 1)) :
      (fun z : U => g.toLorentzMetric.chartChristoffel (physicalChart x) z a b c) =
        fun z : U => christoffelOf g.coefficient z a b c :=
    funext fun z => g.toLorentzMetric_christoffel x z a b c
  have hd (a b c : Fin (d + 1)) :
      DifferentiableAt ℝ (fun z => christoffelOf g.coefficient z a b c) y :=
    ((g.contDiffOn_christoffelOf a b c).contDiffAt
      (U.isOpen.mem_nhds y.property)).differentiableAt (by simp)
  rw [chartCurvature_eq _ (physicalChart_mem x) (by simp), hΓ, hΓ, mvfderiv_val x y (hd _ _ _),
    mvfderiv_val x y (hd _ _ _)]
  simp only [g.toLorentzMetric_chartChristoffel x y]

/-- The Ricci tensor on co-ordinate fields. -/
theorem toLorentzMetric_ricci_chartField (x y : U) (j k : Fin (d + 1)) :
    g.toLorentzMetric.ricci y (chartField (physicalChart x) (Pi.single j 1) y)
      (chartField (physicalChart x) (Pi.single k 1) y) = ricciOf g.coefficient y j k := by
  rw [g.toLorentzMetric.ricci_chartField (physicalChart_mem x) (by simp), ricciOf]
  exact Finset.sum_congr rfl fun i _ => by rw [g.toLorentzMetric_chartCurvature x y]

/-- The scalar curvature is the scalar curvature of the coefficients. -/
theorem toLorentzMetric_scalarCurvature (y : U) :
    g.toLorentzMetric.scalarCurvature y = scalarOf g.coefficient y := by
  rw [scalarCurvature_eq_sum _ y (chartTangentEquiv (physicalChart_mem y) (by simp)), scalarOf]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [chartTangentEquiv_symm, chartTangentEquiv_symm, g.toLorentzMetric_ricci_chartField y y,
    g.toLorentzMetric_inverseComponent y y]

/-- The volume density in the inclusion chart. -/
theorem toLorentzMetric_chartDensity (x y : U) :
    g.toLorentzMetric.chartDensity (physicalChart x) y = densityOf g.coefficient y := by
  have h : g.toLorentzMetric.chartComponent (physicalChart x) y = g.coefficient y := by
    funext i j
    exact g.toLorentzMetric_chartComponent x y i j
  rw [chartDensity, densityOf, h]

end CoordinateMetric

end ProjectAinos.SmoothGeometry
