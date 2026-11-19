/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.Killing
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateConservation

/-!
# Killing fields of a coordinate metric given by their components

For a metric given by coefficients `C_{ij}` on an open set `U`, a vector field is given by its
components `ξ^k`, smooth on `U` (`CoordinateMetric.vectorFieldOf`). The components of the Lie
derivative of the metric are
`(L_ξ g)_{ij} = ξ^k ∂_k C_{ij} + C_{kj} ∂_i ξ^k + C_{ik} ∂_j ξ^k` (`CoordinateMetric.lieOf`).

* `CoordinateMetric.leviCivita_vectorFieldOf`: the covariant derivative
  `(∇_v ξ)^k = ∂_v ξ^k + Γ^k_{ij} v^i ξ^j`.
* `CoordinateMetric.killing_vectorFieldOf`: the Killing form `g(∇_v ξ, w) + g(v, ∇_w ξ)` is
  `(L_ξ g)_{ij} v^i w^j`.
* `CoordinateMetric.isKillingField_iff_lieOf`, `CoordinateMetric.isKillingField_of_lieOf`: the
  field is a Killing field exactly when the Killing equation `L_ξ g = 0` holds on `U`.
* `CoordinateMetric.isKillingField_const`: a constant field `v` is a Killing field when the
  coefficients do not change along `v`; this recovers `isKillingField_chartField`.
* `CoordinateMetric.lieOf_minkowski_linear`, `CoordinateMetric.isKillingField_minkowski_linear`:
  for the Minkowski coefficients, a linear field `ξ = R x` with `η(Rv, w) + η(v, Rw) = 0`
  satisfies `L_ξ η = 0` and is a Killing field.
* `CoordinateMetric.lieOf_rotation`, `CoordinateMetric.isKillingField_rotation`,
  `CoordinateMetric.isKillingField_boost`: in four-dimensional space-time the rotation
  `ξ = (0, −x², x¹, 0)` and the boost `ξ = (x¹, x⁰, 0, 0)`, whose components are not constant,
  are Killing fields; the boost uses the opposite signs of `η₀₀` and `η₁₁`.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

namespace CoordinateMetric

variable {U : Opens (MinkowskiModel d)}

/-- The vector field on `U` with the components `ξ^k` in the inclusion chart. -/
def vectorFieldOf (x₀ : U) (ξ : MinkowskiModel d → MinkowskiModel d) :
    ∀ y : U, TangentSpace 𝓘(ℝ, MinkowskiModel d) y :=
  fun y => chartField (physicalChart x₀) (ξ y) y

/-- The components `(L_ξ C)_{ij} = ξ^k ∂_k C_{ij} + C_{kj} ∂_i ξ^k + C_{ik} ∂_j ξ^k` of the Lie
derivative of a field of coefficients along the field with the components `ξ^k`. -/
def lieOf (C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (ξ : MinkowskiModel d → MinkowskiModel d) (y : MinkowskiModel d) (i j : Fin (d + 1)) : ℝ :=
  fderiv ℝ (fun z => C z i j) y (ξ y) +
    ∑ k, C y k j * fderiv ℝ (fun z => ξ z k) y (Pi.single i 1) +
    ∑ k, C y i k * fderiv ℝ (fun z => ξ z k) y (Pi.single j 1)

/-- The field has the components `ξ`. -/
@[simp] theorem vectorFieldOf_apply (x₀ y : U) (ξ : MinkowskiModel d → MinkowskiModel d) :
    (vectorFieldOf x₀ ξ y : MinkowskiModel d) = ξ y :=
  physicalChart_chartField x₀ y (ξ y)

/-- A constant field of components is the co-ordinate field of that vector. -/
theorem vectorFieldOf_const (x₀ : U) (v : MinkowskiModel d) :
    vectorFieldOf x₀ (fun _ => v) = chartField (physicalChart x₀) v := rfl

/-- For a constant field of components only the derivative of the coefficients is left. -/
@[simp] theorem lieOf_const (C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (v y : MinkowskiModel d) (i j : Fin (d + 1)) :
    lieOf C (fun _ => v) y i j = fderiv ℝ (fun z => C z i j) y v := by
  simp [lieOf]

/-- Components that are smooth on `U` are a smooth map on the manifold `U`. -/
theorem contMDiff_components {ξ : MinkowskiModel d → MinkowskiModel d}
    (hξ : ContDiffOn ℝ ∞ ξ U) :
    ContMDiff 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) ∞ (fun z : U => ξ z) :=
  hξ.contMDiffOn.comp_contMDiff (contMDiff_subtype_val (U := U)) (fun x : U => x.property)

/-- The manifold derivative of components that are smooth on `U`, along a co-ordinate field, is
their ordinary derivative. -/
theorem mvfderiv_components {ξ : MinkowskiModel d → MinkowskiModel d}
    (hξ : ContDiffOn ℝ ∞ ξ U) (x₀ y : U) (v : MinkowskiModel d) :
    mvfderiv 𝓘(ℝ, MinkowskiModel d) (fun z : U => ξ z) y (chartField (physicalChart x₀) v y) =
      fderiv ℝ ξ y v := by
  rw [mvfderiv_chartField (physicalChart_mem x₀) (by simp)
    ((contMDiff_components hξ y).mdifferentiableAt (by simp))]
  have hEq : (fun z : U => ξ z) ∘ (physicalChart x₀).symm =ᶠ[𝓝 (y : MinkowskiModel d)] ξ := by
    filter_upwards [U.isOpen.mem_nhds y.property] with z hz
    change ξ ((physicalChart x₀).symm z : MinkowskiModel d) = ξ z
    rw [← physicalChart_apply x₀ ((physicalChart x₀).symm z),
      (physicalChart x₀).right_inv (by simpa using hz)]
  rw [physicalChart_apply, hEq.fderiv_eq]

/-- **The covariant derivative of a field given by its components**:
`(∇_v ξ)^k = ∂_v ξ^k + Γ^k_{ij} v^i ξ^j`. -/
theorem leviCivita_vectorFieldOf (g : CoordinateMetric σ d U) (x₀ y : U)
    {ξ : MinkowskiModel d → MinkowskiModel d} (hξ : ContDiffOn ℝ ∞ ξ U)
    (v : MinkowskiModel d) (k : Fin (d + 1)) :
    (g.toLorentzMetric.leviCivita (vectorFieldOf x₀ ξ) y v : MinkowskiModel d) k =
      fderiv ℝ (fun z => ξ z k) y v +
        ∑ i, ∑ j, christoffelOf g.coefficient y k i j * v i * ξ y j := by
  have h := g.toLorentzMetric.leviCivita_chart_coordinates (physicalChart_mem x₀)
    (by simp : y ∈ (physicalChart x₀).source)
    ((contMDiff_components hξ y).mdifferentiableAt (by simp)) v k
  rw [mvfderiv_components hξ, physicalChart_tangentMap, physicalChart_chartField] at h
  simp_rw [g.toLorentzMetric_chartChristoffel] at h
  have hd : DifferentiableAt ℝ ξ y :=
    (hξ.differentiableOn (by simp) y y.property).differentiableAt (U.isOpen.mem_nhds y.property)
  have hk : fderiv ℝ (fun z => ξ z k) y =
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) k).comp
        (fderiv ℝ ξ y) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) k).hasFDerivAt.comp
      (y : MinkowskiModel d) hd.hasFDerivAt).fderiv
  rw [hk]
  exact h

/-- **Metric compatibility along a direction**: the derivative of a coefficient along `v` is
`∂_v C_{ij} = v^b (Γ^l_{ib} C_{lj} + Γ^l_{jb} C_{il})`. -/
theorem fderiv_coefficient_apply (g : CoordinateMetric σ d U) {y : MinkowskiModel d}
    (hy : y ∈ U) (i j : Fin (d + 1)) (v : MinkowskiModel d) :
    fderiv ℝ (fun z => g.coefficient z i j) y v =
      ∑ b, v b * ∑ l, (christoffelOf g.coefficient y l i b * g.coefficient y l j +
        christoffelOf g.coefficient y l j b * g.coefficient y i l) := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp only [map_sum, map_smul, smul_eq_mul, fderiv_coefficient hy]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hs (a : Fin (d + 1)) (l : Fin (d + 1)) : christoffelOf g.coefficient y l b a =
      christoffelOf g.coefficient y l a b := by
    let y' : U := ⟨y, hy⟩
    rw [← g.toLorentzMetric_chartChristoffel y' y', ← g.toLorentzMetric_chartChristoffel y' y',
      g.toLorentzMetric.chartChristoffel_symmetric (physicalChart_mem y') (by simp)]
  simp only [hs]

/-- The covariant derivative along a co-ordinate direction:
`(∇_i ξ)^k = ∂_i ξ^k + Γ^k_{ij} ξ^j`. -/
theorem leviCivita_vectorFieldOf_single (g : CoordinateMetric σ d U) (x₀ y : U)
    {ξ : MinkowskiModel d → MinkowskiModel d} (hξ : ContDiffOn ℝ ∞ ξ U) (i k : Fin (d + 1)) :
    (g.toLorentzMetric.leviCivita (vectorFieldOf x₀ ξ) y (Pi.single i 1) : MinkowskiModel d) k =
      fderiv ℝ (fun z => ξ z k) y (Pi.single i 1) +
        ∑ j, christoffelOf g.coefficient y k i j * ξ y j := by
  rw [leviCivita_vectorFieldOf g x₀ y hξ, Finset.sum_eq_single i]
  · simp
  · intro a _ ha
    simp [ha]
  · simp

/-- The form on a co-ordinate vector on the right: `g(a, eⱼ) = C_{kj} a^k`. -/
theorem form_single_right (g : CoordinateMetric σ d U) (y a : MinkowskiModel d)
    (j : Fin (d + 1)) : g.form y a (Pi.single j 1) = ∑ k, g.coefficient y k j * a k := by
  rw [g.form_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single j]
  · simp only [Pi.single_eq_same, mul_one]
  · intro b _ hb
    simp [hb]
  · simp

/-- The form on a co-ordinate vector on the left: `g(eᵢ, b) = C_{ik} b^k`. -/
theorem form_single_left (g : CoordinateMetric σ d U) (y b : MinkowskiModel d)
    (i : Fin (d + 1)) : g.form y (Pi.single i 1) b = ∑ k, g.coefficient y i k * b k := by
  rw [g.form_apply, Finset.sum_eq_single i]
  · simp
  · intro a _ ha
    simp [ha]
  · simp

/-- The Killing form on two co-ordinate directions is a component of `L_ξ g`. -/
theorem killing_vectorFieldOf_single (g : CoordinateMetric σ d U) (x₀ y : U)
    {ξ : MinkowskiModel d → MinkowskiModel d} (hξ : ContDiffOn ℝ ∞ ξ U) (i j : Fin (d + 1)) :
    g.form y (g.toLorentzMetric.leviCivita (vectorFieldOf x₀ ξ) y (Pi.single i 1))
        (Pi.single j 1) +
      g.form y (Pi.single i 1)
        (g.toLorentzMetric.leviCivita (vectorFieldOf x₀ ξ) y (Pi.single j 1)) =
      lieOf g.coefficient ξ y i j := by
  obtain ⟨A, hA⟩ : ∃ A : MinkowskiModel d,
      A = g.toLorentzMetric.leviCivita (vectorFieldOf x₀ ξ) y (Pi.single i 1) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : MinkowskiModel d,
      B = g.toLorentzMetric.leviCivita (vectorFieldOf x₀ ξ) y (Pi.single j 1) := ⟨_, rfl⟩
  have hAk (k : Fin (d + 1)) := hA ▸ leviCivita_vectorFieldOf_single g x₀ y hξ i k
  have hBk (k : Fin (d + 1)) := hB ▸ leviCivita_vectorFieldOf_single g x₀ y hξ j k
  rw [← hA, ← hB, form_single_right, form_single_left, lieOf,
    g.fderiv_coefficient_apply y.property]
  simp only [hAk, hBk]
  have h1 : ∑ k, g.coefficient y k j * ∑ b, christoffelOf g.coefficient y k i b * ξ y b =
      ∑ b, ξ y b * ∑ l, christoffelOf g.coefficient y l i b * g.coefficient y l j := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have h2 : ∑ k, g.coefficient y i k * ∑ b, christoffelOf g.coefficient y k j b * ξ y b =
      ∑ b, ξ y b * ∑ l, christoffelOf g.coefficient y l j b * g.coefficient y i l := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  simp only [mul_add, Finset.sum_add_distrib]
  linear_combination h1 + h2

/-- **The Killing form of a field given by its components**:
`g(∇_v ξ, w) + g(v, ∇_w ξ) = (L_ξ g)_{ij} v^i w^j`. -/
theorem killing_vectorFieldOf (g : CoordinateMetric σ d U) (x₀ y : U)
    {ξ : MinkowskiModel d → MinkowskiModel d} (hξ : ContDiffOn ℝ ∞ ξ U)
    (v w : TangentSpace 𝓘(ℝ, MinkowskiModel d) y) :
    g.toLorentzMetric.form y (g.toLorentzMetric.leviCivita (vectorFieldOf x₀ ξ) y v) w +
        g.toLorentzMetric.form y v (g.toLorentzMetric.leviCivita (vectorFieldOf x₀ ξ) y w) =
      ∑ i, ∑ j, lieOf g.coefficient ξ y i j * (v : MinkowskiModel d) i *
        (w : MinkowskiModel d) j := by
  set e := physicalChart x₀
  set K := vectorFieldOf x₀ ξ
  have hy : y ∈ e.source := by simp [e]
  have hbasis (i j : Fin (d + 1)) :
      g.toLorentzMetric.form y (g.toLorentzMetric.leviCivita K y (chartField e (Pi.single i 1) y))
          (chartField e (Pi.single j 1) y) +
        g.toLorentzMetric.form y (chartField e (Pi.single i 1) y)
          (g.toLorentzMetric.leviCivita K y (chartField e (Pi.single j 1) y)) =
        lieOf g.coefficient ξ y i j := by
    rw [physicalChart_chartField, physicalChart_chartField]
    exact g.killing_vectorFieldOf_single x₀ y hξ i j
  have hv : v = ∑ i, chartTangentMap e y v i • chartField e (Pi.single i 1) y := by
    conv_lhs => rw [← chartField_tangentMap (physicalChart_mem x₀) hy v]
    exact chartField_eq_sum e y _
  have hw : w = ∑ j, chartTangentMap e y w j • chartField e (Pi.single j 1) y := by
    conv_lhs => rw [← chartField_tangentMap (physicalChart_mem x₀) hy w]
    exact chartField_eq_sum e y _
  have hvi (i : Fin (d + 1)) : (v : MinkowskiModel d) i = chartTangentMap e y v i := by
    rw [physicalChart_tangentMap]
  have hwi (i : Fin (d + 1)) : (w : MinkowskiModel d) i = chartTangentMap e y w i := by
    rw [physicalChart_tangentMap]
  simp only [hvi, hwi]
  conv_lhs => rw [hv, hw]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Eq.trans ?_ Finset.sum_comm
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hbasis i j]
  ring

/-- **The Killing equation in components.** The field with the components `ξ`, smooth on `U`,
is a Killing field exactly when `L_ξ g = 0` on `U`. -/
theorem isKillingField_iff_lieOf (g : CoordinateMetric σ d U) (x₀ : U)
    {ξ : MinkowskiModel d → MinkowskiModel d} (hξ : ContDiffOn ℝ ∞ ξ U) :
    g.toLorentzMetric.IsKillingField (vectorFieldOf x₀ ξ) ↔
      ∀ y ∈ U, ∀ i j, lieOf g.coefficient ξ y i j = 0 := by
  constructor
  · intro hK y hy i j
    rw [← g.killing_vectorFieldOf_single x₀ ⟨y, hy⟩ hξ i j]
    exact hK ⟨y, hy⟩ (Pi.single i 1) (Pi.single j 1)
  · intro h y v w
    rw [killing_vectorFieldOf g x₀ y hξ]
    simp [h y y.property]

/-- **A Killing field from its components**: if `L_ξ g = 0` on `U`, the field with the
components `ξ` is a Killing field. -/
theorem isKillingField_of_lieOf (g : CoordinateMetric σ d U) (x₀ : U)
    {ξ : MinkowskiModel d → MinkowskiModel d} (hξ : ContDiffOn ℝ ∞ ξ U)
    (h : ∀ y ∈ U, ∀ i j, lieOf g.coefficient ξ y i j = 0) :
    g.toLorentzMetric.IsKillingField (vectorFieldOf x₀ ξ) :=
  (g.isKillingField_iff_lieOf x₀ hξ).mpr h

/-- A constant field `v` is a Killing field when the coefficients do not change along `v`. For
`v = eₖ` this is `isKillingField_chartField`. -/
theorem isKillingField_const (g : CoordinateMetric σ d U) (x₀ : U) (v : MinkowskiModel d)
    (h : ∀ y ∈ U, ∀ i j, fderiv ℝ (fun z => g.coefficient z i j) y v = 0) :
    g.toLorentzMetric.IsKillingField (chartField (physicalChart x₀) v) := by
  rw [← vectorFieldOf_const]
  exact g.isKillingField_of_lieOf x₀ contDiffOn_const fun y hy i j => by
    rw [lieOf_const]
    exact h y hy i j

/-! ### Linear fields and the Minkowski metric -/

/-- For a linear field `ξ = R x`,
`(L_ξ g)_{ij} = (R x)^k ∂_k C_{ij} + g(R eᵢ, eⱼ) + g(eᵢ, R eⱼ)`. -/
theorem lieOf_linear (g : CoordinateMetric σ d U)
    (R : MinkowskiModel d →L[ℝ] MinkowskiModel d) (y : MinkowskiModel d) (i j : Fin (d + 1)) :
    lieOf g.coefficient R y i j = fderiv ℝ (fun z => g.coefficient z i j) y (R y) +
      g.form y (R (Pi.single i 1)) (Pi.single j 1) +
      g.form y (Pi.single i 1) (R (Pi.single j 1)) := by
  have hk (k : Fin (d + 1)) (v : MinkowskiModel d) : fderiv ℝ (fun z => R z k) y v = R v k := by
    change fderiv ℝ ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin (d + 1) => ℝ) k).comp R) y v = _
    rw [ContinuousLinearMap.fderiv]
    rfl
  simp only [lieOf, hk, form_single_right, form_single_left]

/-- For the Minkowski coefficients, a linear field `ξ = R x` with `η(Rv, w) + η(v, Rw) = 0`
satisfies the Killing equation `L_ξ η = 0` at every point. -/
theorem lieOf_minkowski_linear (R : MinkowskiModel d →L[ℝ] MinkowskiModel d)
    (hR : ∀ v w, minkowskiForm σ d (R v) w + minkowskiForm σ d v (R w) = 0)
    (y : MinkowskiModel d) (i j : Fin (d + 1)) :
    lieOf (minkowski σ d U).coefficient R y i j = 0 := by
  rw [lieOf_linear]
  have hc : (fun z => (minkowski σ d U).coefficient z i j) =
      fun _ => minkowskiForm σ d (Pi.single i 1) (Pi.single j 1) := rfl
  rw [hc, fderiv_const_apply, zero_apply, zero_add]
  exact hR _ _

/-- **Lorentz generators are Killing fields.** For the Minkowski coefficients, a linear field
`ξ = R x` with `η(Rv, w) + η(v, Rw) = 0` is a Killing field. -/
theorem isKillingField_minkowski_linear (x₀ : U) (R : MinkowskiModel d →L[ℝ] MinkowskiModel d)
    (hR : ∀ v w, minkowskiForm σ d (R v) w + minkowskiForm σ d v (R w) = 0) :
    (minkowski σ d U).toLorentzMetric.IsKillingField (vectorFieldOf x₀ R) :=
  (minkowski σ d U).isKillingField_of_lieOf x₀ R.contDiff.contDiffOn
    fun y _ i j => lieOf_minkowski_linear R hR y i j

/-- The generator `x ↦ (0, −x², x¹, 0)` of the rotations in the `x¹x²`-plane of
four-dimensional space-time. -/
def minkowskiRotation : MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 1).smulRight
      (Pi.single 2 1 : MinkowskiModel 3) -
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 2).smulRight
      (Pi.single 1 1 : MinkowskiModel 3)

/-- The components of the rotation generator are `(0, −x², x¹, 0)`. -/
theorem minkowskiRotation_apply (x : MinkowskiModel 3) :
    minkowskiRotation x = ![0, -x 2, x 1, 0] := by
  funext k
  fin_cases k <;> simp [minkowskiRotation]

/-- The rotation generator is antisymmetric for the Minkowski form:
`η(Rv, w) + η(v, Rw) = 0`. -/
theorem minkowskiForm_rotation_add (v w : MinkowskiModel 3) :
    minkowskiForm σ 3 (minkowskiRotation v) w + minkowskiForm σ 3 v (minkowskiRotation w) = 0 := by
  simp [minkowskiForm_apply, minkowskiRotation_apply, Fin.sum_univ_succ, lorentzSign]

/-- **The rotations are Killing fields of flat space-time.** The field with the components
`(0, −x², x¹, 0)` is a Killing field of the Minkowski coefficients. -/
theorem isKillingField_minkowskiRotation {U : Opens (MinkowskiModel 3)} (x₀ : U) :
    (minkowski σ 3 U).toLorentzMetric.IsKillingField (vectorFieldOf x₀ minkowskiRotation) :=
  isKillingField_minkowski_linear x₀ minkowskiRotation minkowskiForm_rotation_add

/-- The Killing equation `L_ξ η = 0` for the non-constant components
`ξ(x) = (0, −x², x¹, 0)`, at every point of four-dimensional space-time. -/
theorem lieOf_rotation {U : Opens (MinkowskiModel 3)} (y : MinkowskiModel 3) (i j : Fin 4) :
    lieOf (minkowski σ 3 U).coefficient (fun x => ![0, -x 2, x 1, 0]) y i j = 0 := by
  have h : (fun x : MinkowskiModel 3 => ![0, -x 2, x 1, 0]) = ⇑minkowskiRotation :=
    funext fun x => (minkowskiRotation_apply x).symm
  rw [h]
  exact lieOf_minkowski_linear minkowskiRotation minkowskiForm_rotation_add y i j

/-- The field with the non-constant components `ξ(x) = (0, −x², x¹, 0)` is a Killing field of
the Minkowski coefficients on every open set of four-dimensional space-time. -/
theorem isKillingField_rotation {U : Opens (MinkowskiModel 3)} (x₀ : U) :
    (minkowski σ 3 U).toLorentzMetric.IsKillingField
      (vectorFieldOf x₀ fun x => ![0, -x 2, x 1, 0]) := by
  have h : (fun x : MinkowskiModel 3 => ![0, -x 2, x 1, 0]) = ⇑minkowskiRotation :=
    funext fun x => (minkowskiRotation_apply x).symm
  rw [h]
  exact isKillingField_minkowskiRotation x₀

/-- The generator `x ↦ (x¹, x⁰, 0, 0)` of the boosts along `x¹` of four-dimensional
space-time. -/
def minkowskiBoost : MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 1).smulRight
      (Pi.single 0 1 : MinkowskiModel 3) +
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).smulRight
      (Pi.single 1 1 : MinkowskiModel 3)

/-- The components of the boost generator are `(x¹, x⁰, 0, 0)`. -/
theorem minkowskiBoost_apply (x : MinkowskiModel 3) :
    minkowskiBoost x = ![x 1, x 0, 0, 0] := by
  funext k
  fin_cases k <;> simp [minkowskiBoost]

/-- The boost generator is antisymmetric for the Minkowski form, `η(Rv, w) + η(v, Rw) = 0`,
because the signs of `η₀₀` and `η₁₁` are opposite. -/
theorem minkowskiForm_boost_add (v w : MinkowskiModel 3) :
    minkowskiForm σ 3 (minkowskiBoost v) w + minkowskiForm σ 3 v (minkowskiBoost w) = 0 := by
  simp [minkowskiForm_apply, minkowskiBoost_apply, Fin.sum_univ_succ, lorentzSign]

/-- **The boosts are Killing fields of flat space-time.** The field with the non-constant
components `ξ(x) = (x¹, x⁰, 0, 0)` is a Killing field of the Minkowski coefficients on every
open set of four-dimensional space-time. -/
theorem isKillingField_boost {U : Opens (MinkowskiModel 3)} (x₀ : U) :
    (minkowski σ 3 U).toLorentzMetric.IsKillingField
      (vectorFieldOf x₀ fun x => ![x 1, x 0, 0, 0]) := by
  have h : (fun x : MinkowskiModel 3 => ![x 1, x 0, 0, 0]) = ⇑minkowskiBoost :=
    funext fun x => (minkowskiBoost_apply x).symm
  rw [h]
  exact isKillingField_minkowski_linear x₀ minkowskiBoost minkowskiForm_boost_add

end CoordinateMetric

end ProjectAinos.SmoothGeometry
