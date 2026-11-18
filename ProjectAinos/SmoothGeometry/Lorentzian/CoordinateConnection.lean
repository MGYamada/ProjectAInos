/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateMetric
public import ProjectAinos.SmoothGeometry.Lorentzian.CurvatureDerivative

/-!
# The connection and the curvature of a coordinate metric

For a metric given by coefficients on an open set `U` of the model space, the co-ordinate fields
of the inclusion chart commute, so the Koszul formula reads off the connection from the
derivatives of the coefficients.

* `toLorentzMetric_pairing_derivative`: the derivative of `g(∂_v, ∂_w)` along `∂_u` is the
  derivative of the coefficient `q ↦ g_q(v, w)` in the direction `u`.
* `toLorentzMetric_leviCivita_eq`: a vector `c` that satisfies the Koszul identity is
  `∇_{∂_v} ∂_w`.
* `toLorentzMetric_curvature_of_connection` and
  `toLorentzMetric_curvatureDerivative_of_connection`: if `∇_{∂_v} ∂_w = ∂_{Γ(v, w)}` for a
  map `Γ` that does not depend on the point, then
  `R(∂_u, ∂_v)∂_w = ∂_{Γ(u, Γ(v, w)) − Γ(v, Γ(u, w))}`, and the covariant derivative of a
  curvature with constant components is the Leibniz expression in `Γ`.
-/

@[expose] public section

noncomputable section

open Bundle ContinuousLinearMap Set TopologicalSpace VectorField
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

namespace LorentzMetric

variable {M : Type} [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]

@[simp] theorem chartField_sub (e : OpenPartialHomeomorph M (MinkowskiModel d))
    (u v : MinkowskiModel d) (x : M) :
    chartField e (u - v) x = chartField e u x - chartField e v x := by
  simp [chartField, mpullback_apply, modelField]

end LorentzMetric

namespace CoordinateMetric

variable {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U)

/-- The derivative of the pairing of two co-ordinate fields is the derivative of the
coefficient. -/
theorem toLorentzMetric_pairing_derivative (x y : U) (u v w : MinkowskiModel d) :
    mvfderiv 𝓘(ℝ, MinkowskiModel d)
        (fun z => g.toLorentzMetric.form z (chartField (physicalChart x) v z)
          (chartField (physicalChart x) w z)) y (chartField (physicalChart x) u y) =
      fderiv ℝ (fun q => g.form q v w) y u := by
  let G := fun z : U => g.toLorentzMetric.form z (chartField (physicalChart x) v z)
    (chartField (physicalChart x) w z)
  have hEq : G = fun z : U => g.form z v w := funext fun z => by
    change g.toLorentzMetric.form z _ _ = _
    rw [toLorentzMetric_form, physicalChart_chartField, physicalChart_chartField]
  have hG : MDifferentiableAt 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, ℝ) G y := by
    have hs := ((g.smooth.clm_apply (contDiffOn_const (c := v))).clm_apply
      (contDiffOn_const (c := w))).contMDiffOn.comp_contMDiff
      (contMDiff_subtype_val (U := U)) (fun x : U => x.property)
    rw [hEq]
    exact (hs y).mdifferentiableAt (by simp)
  change mvfderiv 𝓘(ℝ, MinkowskiModel d) G y _ = _
  rw [mvfderiv_chartField (physicalChart_mem x) (by simp) hG]
  have hEq' : G ∘ (physicalChart x).symm =ᶠ[𝓝 (y : MinkowskiModel d)]
      fun q => g.form q v w := by
    filter_upwards [U.isOpen.mem_nhds y.property] with z hz
    change G ((physicalChart x).symm z) = _
    rw [hEq]
    change g.form ((physicalChart x).symm z : MinkowskiModel d) v w = _
    rw [← physicalChart_apply x ((physicalChart x).symm z),
      (physicalChart x).right_inv (by simpa using hz)]
  rw [physicalChart_apply, hEq'.fderiv_eq]

/-- **The Koszul formula for co-ordinate fields.** A vector `c` with
`g(c, z) = ½ (∂_v g(w, z) + ∂_w g(z, v) − ∂_z g(v, w))` for all `z` is
`∇_{∂_v} ∂_w`. -/
theorem toLorentzMetric_leviCivita_eq (x y : U) (v w c : MinkowskiModel d)
    (hc : ∀ z, g.form y c z = (fderiv ℝ (fun q => g.form q w z) y v +
      fderiv ℝ (fun q => g.form q z v) y w - fderiv ℝ (fun q => g.form q v w) y z) / 2) :
    g.toLorentzMetric.leviCivita (chartField (physicalChart x) w) y
      (chartField (physicalChart x) v y) = chartField (physicalChart x) c y := by
  have he := physicalChart_mem x
  have hy : y ∈ (physicalChart x).source := by simp
  apply (g.toLorentzMetric.flat y).injective
  ext t
  rw [flat_apply, flat_apply, ← chartField_tangentMap he hy t]
  have h := g.toLorentzMetric.leviCivita_pairing (chartField_mdifferentiableAt he hy v)
    (chartField_mdifferentiableAt he hy w)
    (chartField_mdifferentiableAt he hy (chartTangentMap (physicalChart x) y t))
  rw [h]
  simp only [koszul, chartField_bracket he hy, map_zero, sub_zero, add_zero]
  rw [g.toLorentzMetric_pairing_derivative, g.toLorentzMetric_pairing_derivative,
    g.toLorentzMetric_pairing_derivative, toLorentzMetric_form, physicalChart_chartField,
    physicalChart_chartField, hc]

/-- If the connection on co-ordinate fields is a map `Γ` that does not depend on the point,
the curvature on co-ordinate fields is `Γ(u, Γ(v, w)) − Γ(v, Γ(u, w))`. -/
theorem toLorentzMetric_curvature_of_connection (x : U)
    (Γ : MinkowskiModel d → MinkowskiModel d → MinkowskiModel d)
    (hΓ : ∀ (y : U) (v w : MinkowskiModel d),
      g.toLorentzMetric.leviCivita (chartField (physicalChart x) w) y
        (chartField (physicalChart x) v y) = chartField (physicalChart x) (Γ v w) y)
    (y : U) (u v w : MinkowskiModel d) :
    g.toLorentzMetric.curvature y (chartField (physicalChart x) u y)
        (chartField (physicalChart x) v y) (chartField (physicalChart x) w y) =
      chartField (physicalChart x) (Γ u (Γ v w) - Γ v (Γ u w)) y := by
  have he := physicalChart_mem x
  have hy : y ∈ (physicalChart x).source := by simp
  have h2 (a : MinkowskiModel d) :=
    (chartField_contMDiffAt he hy a).of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)
  have hcov (a b : MinkowskiModel d) :
      g.toLorentzMetric.covariantField (chartField (physicalChart x) a)
        (chartField (physicalChart x) b) = chartField (physicalChart x) (Γ a b) :=
    funext fun z => hΓ z a b
  have hb : g.toLorentzMetric.covariantField
      (mlieBracket 𝓘(ℝ, MinkowskiModel d) (chartField (physicalChart x) u)
        (chartField (physicalChart x) v)) (chartField (physicalChart x) w) y = 0 := by
    simp only [covariantField, chartField_bracket he hy, map_zero]
  rw [g.toLorentzMetric.curvature_apply (h2 u) (h2 v) (h2 w), curvatureField, hcov v w,
    hcov u w, hcov u (Γ v w), hcov v (Γ u w), hb, sub_zero, chartField_sub]

/-- The covariant derivative of a curvature whose components `ℛ` are constant, for a connection
`Γ` that does not depend on the point. -/
theorem toLorentzMetric_curvatureDerivative_of_connection (x : U)
    (Γ : MinkowskiModel d → MinkowskiModel d → MinkowskiModel d)
    (hΓ : ∀ (y : U) (v w : MinkowskiModel d),
      g.toLorentzMetric.leviCivita (chartField (physicalChart x) w) y
        (chartField (physicalChart x) v y) = chartField (physicalChart x) (Γ v w) y)
    (ℛ : MinkowskiModel d → MinkowskiModel d → MinkowskiModel d → MinkowskiModel d)
    (hR : ∀ (y : U) (u v w : MinkowskiModel d),
      g.toLorentzMetric.curvature y (chartField (physicalChart x) u y)
        (chartField (physicalChart x) v y) (chartField (physicalChart x) w y) =
      chartField (physicalChart x) (ℛ u v w) y)
    (y : U) (a u v w : MinkowskiModel d) :
    g.toLorentzMetric.curvatureDerivative y (chartField (physicalChart x) u y)
        (chartField (physicalChart x) v y) (chartField (physicalChart x) w y)
        (chartField (physicalChart x) a y) =
      chartField (physicalChart x)
        (Γ a (ℛ u v w) - ℛ (Γ a u) v w - ℛ u (Γ a v) w - ℛ u v (Γ a w)) y := by
  have he := physicalChart_mem x
  have hy : y ∈ (physicalChart x).source := by simp
  have h1 (b : MinkowskiModel d) :=
    (chartField_contMDiffAt he hy b).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
  have hfield : (fun z => g.toLorentzMetric.curvature z (chartField (physicalChart x) u z)
      (chartField (physicalChart x) v z) (chartField (physicalChart x) w z)) =
      chartField (physicalChart x) (ℛ u v w) :=
    funext fun z => hR z u v w
  have h₁ : g.toLorentzMetric.leviCivita (fun z => g.toLorentzMetric.curvature z
      (chartField (physicalChart x) u z) (chartField (physicalChart x) v z)
      (chartField (physicalChart x) w z)) y (chartField (physicalChart x) a y) =
      chartField (physicalChart x) (Γ a (ℛ u v w)) y := by
    rw [hfield]
    exact hΓ y a _
  have h₂ : g.toLorentzMetric.curvature y
      (g.toLorentzMetric.leviCivita (chartField (physicalChart x) u) y
        (chartField (physicalChart x) a y))
      (chartField (physicalChart x) v y) (chartField (physicalChart x) w y) =
      chartField (physicalChart x) (ℛ (Γ a u) v w) y := by
    rw [hΓ y a u]
    exact hR y _ v w
  have h₃ : g.toLorentzMetric.curvature y (chartField (physicalChart x) u y)
      (g.toLorentzMetric.leviCivita (chartField (physicalChart x) v) y
        (chartField (physicalChart x) a y)) (chartField (physicalChart x) w y) =
      chartField (physicalChart x) (ℛ u (Γ a v) w) y := by
    rw [hΓ y a v]
    exact hR y u _ w
  have h₄ : g.toLorentzMetric.curvature y (chartField (physicalChart x) u y)
      (chartField (physicalChart x) v y)
      (g.toLorentzMetric.leviCivita (chartField (physicalChart x) w) y
        (chartField (physicalChart x) a y)) =
      chartField (physicalChart x) (ℛ u v (Γ a w)) y := by
    rw [hΓ y a w]
    exact hR y u v _
  rw [g.toLorentzMetric.curvatureDerivative_apply (h1 u) (h1 v) (h1 w)]
  simp only [h₁, h₂, h₃, h₄, chartField_sub]

end CoordinateMetric

end ProjectAinos.SmoothGeometry
