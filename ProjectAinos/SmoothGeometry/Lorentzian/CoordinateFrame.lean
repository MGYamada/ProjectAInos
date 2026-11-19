/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateKilling
public import ProjectAinos.SmoothGeometry.Lorentzian.DiagonalMetric
public import ProjectAinos.SmoothGeometry.Lorentzian.Tetrad

/-!
# Orthonormal frames of a coordinate metric given by their components

For a metric given by coefficients on an open set `U` of the model space, vector fields are
given by their components `ξ^k`, smooth on `U` (`CoordinateMetric.vectorFieldOf`). This file
builds an orthonormal frame from such components and computes its curvature from the
commutators of the components.

* `CoordinateMetric.lieBracketOf`, `CoordinateMetric.mlieBracket_vectorFieldOf`: the Lie bracket
  of two fields of components has the components `[ξ, η]^k = ∂_ξ η^k − ∂_η ξ^k`.
* `CoordinateMetric.contMDiffAt_vectorFieldOf`, `CoordinateMetric.mvfderiv_vectorFieldOf`:
  components smooth on `U` give a smooth vector field, and the derivative of a function along it
  is the ordinary derivative along the components.
* `CoordinateMetric.orthonormalFrameOf`: components with `g(ξ_a, ξ_b) = η_{ab}` on `U` are an
  orthonormal frame on all of `U`; `commutator_orthonormalFrameOf`: its commutator coefficients
  are `λ_{abc} = g(ξ_a, [ξ_b, ξ_c])`.
* `CoordinateMetric.rotationOf`, `CoordinateMetric.ricciOfFrame`,
  `CoordinateMetric.ricci_orthonormalFrameOf`: **the Ricci tensor from given commutator
  functions**. If `g(ξ_a, [ξ_b, ξ_c]) = Λ_{abc}` on `U` for functions `Λ_{abc}` smooth on `U`,
  then with `γ_{abc} = ½ (Λ_{abc} + Λ_{bca} − Λ_{cab})` the frame components of the Ricci
  tensor are `Ric(E_b, E_k) = Σ_i η_{ii} (∂_{ξ_i} γ_{kib} − ∂_{ξ_b} γ_{kii} −
  Σ_f η_{ff} (γ_{kfb} γ_{ifi} − γ_{kfi} γ_{ifb} + Λ_{fib} γ_{kif}))`.
* `CoordinateMetric.ricci_eq_zero_iff_frame`: the Ricci tensor vanishes on `U` exactly when its
  frame components vanish.
-/

@[expose] public section

noncomputable section

open Bundle VectorField Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

namespace CoordinateMetric

variable {U : Opens (MinkowskiModel d)}

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-! ### Fields of components -/

/-- The components `[ξ, η]^k = ∂_ξ η^k − ∂_η ξ^k` of the Lie bracket of two fields of
components. -/
def lieBracketOf (ξ η : MinkowskiModel d → MinkowskiModel d) (y : MinkowskiModel d) :
    MinkowskiModel d :=
  fderiv ℝ η y (ξ y) - fderiv ℝ ξ y (η y)

/-- Components smooth on `U` give a smooth section of the tangent bundle. -/
theorem contMDiffAt_vectorFieldOf {ξ : MinkowskiModel d → MinkowskiModel d}
    (hξ : ContDiffOn ℝ ∞ ξ U) (x₀ y : U) :
    ContMDiffAt I ((I).prod I) ∞ (T% (vectorFieldOf x₀ ξ)) y := by
  have h : vectorFieldOf x₀ ξ =
      fun z : U => ∑ k, ξ z k • chartField (physicalChart x₀) (Pi.single k 1) z := by
    funext z
    exact LorentzMetric.chartField_eq_sum _ z (ξ z)
  rw [h]
  refine ContMDiffAt.sum_section fun k _ => ?_
  have hk : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun z : U => ξ z k) y :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) k).contMDiff.comp
      (contMDiff_components hξ)) y
  exact hk.smul_section
    (chartField_contMDiffAt (physicalChart_mem x₀) (by simp : y ∈ (physicalChart x₀).source) _)

/-- **The derivative of a function along a field of components** is the ordinary derivative of
the function along the components. -/
theorem mvfderiv_vectorFieldOf {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : MinkowskiModel d → F} (hφ : ContDiffOn ℝ ∞ φ U) (x₀ y : U)
    (ξ : MinkowskiModel d → MinkowskiModel d) :
    mvfderiv I (fun z : U => φ z) y (vectorFieldOf x₀ ξ y) = fderiv ℝ φ y (ξ y) := by
  have hm : MDifferentiableAt I 𝓘(ℝ, F) (fun z : U => φ z) y :=
    ((hφ.contMDiffOn.comp_contMDiff (contMDiff_subtype_val (U := U))
      (fun x : U => x.property)) y).mdifferentiableAt (by simp)
  rw [vectorFieldOf, mvfderiv_chartField (physicalChart_mem x₀) (by simp) hm]
  have hEq : (fun z : U => φ z) ∘ (physicalChart x₀).symm =ᶠ[𝓝 (y : MinkowskiModel d)] φ := by
    filter_upwards [U.isOpen.mem_nhds y.property] with z hz
    change φ ((physicalChart x₀).symm z : MinkowskiModel d) = φ z
    rw [← physicalChart_apply x₀ ((physicalChart x₀).symm z),
      (physicalChart x₀).right_inv (by simpa using hz)]
  rw [physicalChart_apply, hEq.fderiv_eq]

/-- **The Lie bracket of two fields of components** has the components
`[ξ, η]^k = ∂_ξ η^k − ∂_η ξ^k`. The proof uses the torsion-free connection of the Minkowski
coefficients, whose Christoffel symbols vanish. -/
theorem mlieBracket_vectorFieldOf {ξ η : MinkowskiModel d → MinkowskiModel d}
    (hξ : ContDiffOn ℝ ∞ ξ U) (hη : ContDiffOn ℝ ∞ η U) (x₀ y : U) :
    mlieBracket I (vectorFieldOf x₀ ξ) (vectorFieldOf x₀ η) y =
      vectorFieldOf x₀ (lieBracketOf ξ η) y := by
  have h := (minkowski LorentzConvention.timeNegative d U).toLorentzMetric.covariantField_commutator
    ((contMDiffAt_vectorFieldOf hξ x₀ y).mdifferentiableAt (by simp))
    ((contMDiffAt_vectorFieldOf hη x₀ y).mdifferentiableAt (by simp))
  rw [← h]
  have hdξ : DifferentiableAt ℝ ξ y :=
    (hξ.differentiableOn (by simp) y y.property).differentiableAt (U.isOpen.mem_nhds y.property)
  have hdη : DifferentiableAt ℝ η y :=
    (hη.differentiableOn (by simp) y y.property).differentiableAt (U.isOpen.mem_nhds y.property)
  have hk (ζ : MinkowskiModel d → MinkowskiModel d) (hζ : DifferentiableAt ℝ ζ y) (k : Fin (d + 1))
      (v : MinkowskiModel d) : fderiv ℝ (fun z => ζ z k) y v = fderiv ℝ ζ y v k := by
    have h' : fderiv ℝ (fun z => ζ z k) y =
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) k).comp
          (fderiv ℝ ζ y) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) k).hasFDerivAt.comp
        (y : MinkowskiModel d) hζ.hasFDerivAt).fderiv
    rw [h']
    rfl
  have e1 := leviCivita_vectorFieldOf (minkowski LorentzConvention.timeNegative d U) x₀ y hη
    (vectorFieldOf x₀ ξ y : MinkowskiModel d)
  have e2 := leviCivita_vectorFieldOf (minkowski LorentzConvention.timeNegative d U) x₀ y hξ
    (vectorFieldOf x₀ η y : MinkowskiModel d)
  simp only [christoffelOf_minkowski, zero_mul, Finset.sum_const_zero, add_zero] at e1 e2
  funext k
  change (covariantField _ (vectorFieldOf x₀ ξ) (vectorFieldOf x₀ η) y : MinkowskiModel d) k -
      (covariantField _ (vectorFieldOf x₀ η) (vectorFieldOf x₀ ξ) y : MinkowskiModel d) k =
    (vectorFieldOf x₀ (lieBracketOf ξ η) y : MinkowskiModel d) k
  rw [covariantField, covariantField, e1, e2, vectorFieldOf_apply, vectorFieldOf_apply,
    vectorFieldOf_apply, hk η hdη, hk ξ hdξ]
  rfl

/-! ### The frame -/

/-- **An orthonormal frame from its components**: fields of components `ξ_a`, smooth on `U`,
with `g(ξ_a, ξ_b) = η_{ab}` on `U`, are an orthonormal frame on all of `U`. -/
def orthonormalFrameOf (g : CoordinateMetric σ d U) (x₀ : U)
    (ξ : Fin (d + 1) → MinkowskiModel d → MinkowskiModel d) (hξ : ∀ a, ContDiffOn ℝ ∞ (ξ a) U)
    (horth : ∀ y ∈ U, ∀ a b, g.form y (ξ a y) (ξ b y) = if a = b then lorentzSign σ a else 0) :
    g.toLorentzMetric.OrthonormalFrame (univ : Set U) where
  field a := vectorFieldOf x₀ (ξ a)
  isOpen := isOpen_univ
  smooth a y _ := contMDiffAt_vectorFieldOf (hξ a) x₀ y
  orthonormal y _ a b := by
    rw [toLorentzMetric_form, vectorFieldOf_apply, vectorFieldOf_apply]
    exact horth y y.property a b

variable (g : CoordinateMetric σ d U) (x₀ : U)
  {ξ : Fin (d + 1) → MinkowskiModel d → MinkowskiModel d} (hξ : ∀ a, ContDiffOn ℝ ∞ (ξ a) U)
  (horth : ∀ y ∈ U, ∀ a b, g.form y (ξ a y) (ξ b y) = if a = b then lorentzSign σ a else 0)

/-- The fields of the frame are the fields with the given components. -/
@[simp] theorem field_orthonormalFrameOf (a : Fin (d + 1)) :
    (orthonormalFrameOf g x₀ ξ hξ horth).field a = vectorFieldOf x₀ (ξ a) := rfl

/-- **The commutator coefficients of the frame**: `λ_{abc} = g(ξ_a, [ξ_b, ξ_c])`. -/
theorem commutator_orthonormalFrameOf (a b c : Fin (d + 1)) (y : U) :
    (orthonormalFrameOf g x₀ ξ hξ horth).commutator a b c y =
      g.form y (ξ a y) (lieBracketOf (ξ b) (ξ c) y) := by
  unfold OrthonormalFrame.commutator
  rw [field_orthonormalFrameOf, field_orthonormalFrameOf, field_orthonormalFrameOf,
    mlieBracket_vectorFieldOf (hξ b) (hξ c), toLorentzMetric_form, vectorFieldOf_apply,
    vectorFieldOf_apply]

/-! ### The Ricci tensor from the commutators -/

/-- The rotation coefficients `γ_{abc} = ½ (Λ_{abc} + Λ_{bca} − Λ_{cab})` of given commutator
functions `Λ_{abc}`. -/
def rotationOf (Λ : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → MinkowskiModel d → ℝ)
    (a b c : Fin (d + 1)) (z : MinkowskiModel d) : ℝ :=
  (Λ a b c z + Λ b c a z - Λ c a b z) / 2

variable (σ) in
/-- **The frame components of the Ricci tensor from the commutator functions**:
`Σ_i η_{ii} (∂_{ξ_i} γ_{kib} − ∂_{ξ_b} γ_{kii} −
Σ_f η_{ff} (γ_{kfb} γ_{ifi} − γ_{kfi} γ_{ifb} + Λ_{fib} γ_{kif}))`. -/
def ricciOfFrame (Λ : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → MinkowskiModel d → ℝ)
    (ξ : Fin (d + 1) → MinkowskiModel d → MinkowskiModel d) (z : MinkowskiModel d)
    (b k : Fin (d + 1)) : ℝ :=
  ∑ i, lorentzSign σ i * (fderiv ℝ (rotationOf Λ k i b) z (ξ i z) -
    fderiv ℝ (rotationOf Λ k i i) z (ξ b z) -
    ∑ f, lorentzSign σ f * (rotationOf Λ k f b z * rotationOf Λ i f i z -
      rotationOf Λ k f i z * rotationOf Λ i f b z + Λ f i b z * rotationOf Λ k i f z))

/-- The rotation coefficients of the frame are those of the commutator functions. -/
theorem rotation_orthonormalFrameOf
    {Λ : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → MinkowskiModel d → ℝ}
    (hcomm : ∀ z ∈ U, ∀ a b c, g.form z (ξ a z) (lieBracketOf (ξ b) (ξ c) z) = Λ a b c z)
    (a b c : Fin (d + 1)) :
    (orthonormalFrameOf g x₀ ξ hξ horth).rotation a b c =
      fun z : U => rotationOf Λ a b c z := by
  funext z
  rw [OrthonormalFrame.rotation_eq _ (mem_univ z), commutator_orthonormalFrameOf,
    commutator_orthonormalFrameOf, commutator_orthonormalFrameOf, hcomm z z.property,
    hcomm z z.property, hcomm z z.property, rotationOf]

/-- **The Ricci tensor of a frame given by its components**, from commutator functions that are
smooth on `U`. -/
theorem ricci_orthonormalFrameOf
    {Λ : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → MinkowskiModel d → ℝ}
    (hΛ : ∀ a b c, ContDiffOn ℝ ∞ (Λ a b c) U)
    (hcomm : ∀ z ∈ U, ∀ a b c, g.form z (ξ a z) (lieBracketOf (ξ b) (ξ c) z) = Λ a b c z)
    (y : U) (b k : Fin (d + 1)) :
    g.toLorentzMetric.ricci y ((orthonormalFrameOf g x₀ ξ hξ horth).field b y)
        ((orthonormalFrameOf g x₀ ξ hξ horth).field k y) =
      ricciOfFrame σ Λ ξ y b k := by
  have hrot (a b c : Fin (d + 1)) : ContDiffOn ℝ ∞ (rotationOf Λ a b c) U := by
    unfold rotationOf
    exact (((hΛ a b c).add (hΛ b c a)).sub (hΛ c a b)).div_const 2
  rw [OrthonormalFrame.ricci_field_eq _ (mem_univ y)]
  simp only [rotation_orthonormalFrameOf g x₀ hξ horth hcomm, field_orthonormalFrameOf,
    mvfderiv_vectorFieldOf (hrot _ _ _), commutator_orthonormalFrameOf, hcomm y y.property,
    ricciOfFrame]

/-- **The Ricci tensor vanishes on `U` exactly when its frame components vanish.** -/
theorem ricci_eq_zero_iff_frame :
    (∀ y : U, g.toLorentzMetric.ricci y = 0) ↔
      ∀ y : U, ∀ b k, g.toLorentzMetric.ricci y
        ((orthonormalFrameOf g x₀ ξ hξ horth).field b y)
        ((orthonormalFrameOf g x₀ ξ hξ horth).field k y) = 0 := by
  constructor
  · intro h y b k
    rw [h y]
    rfl
  · intro h y
    exact (orthonormalFrameOf g x₀ ξ hξ horth).bilinear_ext (mem_univ y) fun b k => h y b k

end CoordinateMetric

end ProjectAinos.SmoothGeometry
