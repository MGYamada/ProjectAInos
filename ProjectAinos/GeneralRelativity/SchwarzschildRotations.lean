/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.SchwarzschildExterior
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateKilling
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateGeodesic
public import ProjectAinos.SmoothGeometry.Lorentzian.DiagonalMetric
import Mathlib.Tactic.FieldSimp

/-!
# The rotations of the exterior Schwarzschild field

The exterior Schwarzschild metric of `SchwarzschildExterior` is spherically symmetric: in the
co-ordinates `(t, r, θ, φ)` the coefficients `g_tt`, `g_rr` depend on `r` only, `g_θθ = r²` and
`g_φφ = r² sin²θ`. The generators of the rotations about the three axes are Killing fields, and
their pairings with the velocity of a geodesic are the three components of the angular
momentum, which are conserved. This is the statement of Landau–Lifshitz, §101, that the motion
of a body in a centrally symmetric field takes place in a plane through the centre (see also
§100 for the field itself).

* `sphereField`, `lieOf_sphereField`: the components `(0, 0, A(φ), cot θ · B(φ) + D)` with
  `A' = B`, `B' = −A` satisfy the Killing equation `L_ξ g = 0` on the exterior domain.
* `rotationField`, `isKillingField_rotationField`: the generators
  `K₀ = −sin φ ∂_θ − cot θ cos φ ∂_φ`, `K₁ = cos φ ∂_θ − cot θ sin φ ∂_φ`, `K₂ = ∂_φ` of the
  rotations about the `x`, `y` and `z` axes are Killing fields.
* `angularMomentum`, `angularMomentum_eq`: the angular momentum `J_a = g(K_a, γ̇)` is constant
  along every geodesic given on a convex set of parameters.
* `angularMomentum_eq_angularComponent`: in co-ordinates `J_a = r² (K_a^θ θ̇ + sin²θ K_a^φ φ̇)`;
  `sum_angularMomentum_sq`: `J₀² + J₁² + J₂² = r⁴ (θ̇² + sin²θ φ̇²)`;
  `direction_angularMomentum`: `n · J = 0` for the radial unit vector
  `n = (sin θ cos φ, sin θ sin φ, cos θ)`.
* `planar_motion`: **the motion is in a plane through the centre.** Along a geodesic on a
  convex set of parameters, `J` is constant and the radial direction of every event of the
  geodesic is orthogonal to it.
* `angularMomentum_equatorialCircle`: the uniform circular motion `φ = Ω t` in the equatorial
  plane has `J = (0, 0, r² Ω)`; `isGeodesicOn_equatorialCircle`: it is a geodesic when
  `r³ Ω² = M`, so that `planar_motion_equatorialCircle` applies `planar_motion` to a geodesic.

The angle `φ` is read on the real line and the axis `sin θ = 0` is not in the domain, as in
`SchwarzschildExterior`; the fields `K₀`, `K₁` are singular on the axis.
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.GeneralRelativity.SchwarzschildExterior

open SmoothGeometry Minkowski
open LorentzMetric (chartField curveVelocity)
open CoordinateMetric (physicalChart vectorFieldOf lieOf)

variable {M : ℝ}

/-- The components `(0, 0, A(φ), cot θ · B(φ) + D)` of a field that moves the points of each
sphere `t, r = const` along the sphere. -/
def sphereField (A B : ℝ → ℝ) (D : ℝ) (x : MinkowskiModel 3) : MinkowskiModel 3 :=
  ![0, 0, A (x 3), Real.cos (x 2) / Real.sin (x 2) * B (x 3) + D]

/-- The diagonal of the Schwarzschild coefficients. -/
private def diagC (M : ℝ) (x : MinkowskiModel 3) : Fin 4 → ℝ :=
  ![-((x 1 - 2 * M) / x 1), x 1 / (x 1 - 2 * M), x 1 ^ 2, x 1 ^ 2 * Real.sin (x 2) ^ 2]

private theorem coefficient_eq_diagC (hM : 0 ≤ M) :
    (metric hM).coefficient = fun y => Matrix.diagonal (diagC M y) := by
  funext y i j
  simp only [CoordinateMetric.coefficient, Matrix.of_apply, metric_form, form_apply]
  fin_cases i <;> fin_cases j <;> simp [diagC]

private theorem fderiv_comp_apply {g : ℝ → ℝ} {y : MinkowskiModel 3} (k : Fin 4)
    (hg : DifferentiableAt ℝ g (y k)) (v : MinkowskiModel 3) :
    fderiv ℝ (fun z : MinkowskiModel 3 => g (z k)) y v = deriv g (y k) * v k := by
  have hp : HasFDerivAt (fun z : MinkowskiModel 3 => z k)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) k) y :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) k).hasFDerivAt
  have h := hg.hasDerivAt.comp_hasFDerivAt y hp
  rw [show (fun z : MinkowskiModel 3 => g (z k)) = g ∘ fun z => z k from rfl, h.fderiv]
  simp

private theorem lieOf_diagonal (c : MinkowskiModel 3 → Fin 4 → ℝ)
    (ξ : MinkowskiModel 3 → MinkowskiModel 3) (y : MinkowskiModel 3) (i j : Fin 4) :
    lieOf (fun z => Matrix.diagonal (c z)) ξ y i j =
      (if i = j then fderiv ℝ (fun z => c z i) y (ξ y) else 0) +
      c y j * fderiv ℝ (fun z => ξ z j) y (Pi.single i 1) +
      c y i * fderiv ℝ (fun z => ξ z i) y (Pi.single j 1) := by
  unfold lieOf
  by_cases h : i = j
  · subst h
    simp [Matrix.diagonal_apply]
  · simp [Matrix.diagonal_apply, h]

private theorem differentiableAt_comp_apply {g : ℝ → ℝ} {y : MinkowskiModel 3} (k : Fin 4)
    (hg : DifferentiableAt ℝ g (y k)) :
    DifferentiableAt ℝ (fun z : MinkowskiModel 3 => g (z k)) y := by
  have hp : DifferentiableAt ℝ (fun z : MinkowskiModel 3 => z k) y :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) k).differentiableAt
  exact hg.comp y hp

private theorem fderiv_sphereField_zero (A B : ℝ → ℝ) (D : ℝ) (y v : MinkowskiModel 3) :
    fderiv ℝ (fun z => sphereField A B D z 0) y v = 0 := by
  simp [sphereField]

private theorem fderiv_sphereField_one (A B : ℝ → ℝ) (D : ℝ) (y v : MinkowskiModel 3) :
    fderiv ℝ (fun z => sphereField A B D z 1) y v = 0 := by
  simp [sphereField]

private theorem fderiv_sphereField_two {A : ℝ → ℝ} (B : ℝ → ℝ) (D : ℝ) {y : MinkowskiModel 3}
    (hA : DifferentiableAt ℝ A (y 3)) (v : MinkowskiModel 3) :
    fderiv ℝ (fun z => sphereField A B D z 2) y v = deriv A (y 3) * v 3 :=
  fderiv_comp_apply (g := A) 3 hA v

private theorem fderiv_sphereField_three (A : ℝ → ℝ) {B : ℝ → ℝ} (D : ℝ)
    {y : MinkowskiModel 3} (hs : Real.sin (y 2) ≠ 0) (hB : DifferentiableAt ℝ B (y 3))
    (v : MinkowskiModel 3) :
    fderiv ℝ (fun z => sphereField A B D z 3) y v =
      -(v 2 * B (y 3)) / Real.sin (y 2) ^ 2 +
        Real.cos (y 2) / Real.sin (y 2) * (deriv B (y 3) * v 3) := by
  have hc : HasDerivAt (fun θ => Real.cos θ / Real.sin θ)
      ((-Real.sin (y 2) * Real.sin (y 2) - Real.cos (y 2) * Real.cos (y 2)) /
        Real.sin (y 2) ^ 2) (y 2) :=
    (Real.hasDerivAt_cos (y 2)).div (Real.hasDerivAt_sin (y 2)) hs
  have h1 := differentiableAt_comp_apply (g := fun θ => Real.cos θ / Real.sin θ) 2
    hc.differentiableAt
  have h2 := differentiableAt_comp_apply (g := B) 3 hB
  show fderiv ℝ (fun z : MinkowskiModel 3 =>
      Real.cos (z 2) / Real.sin (z 2) * B (z 3) + D) y v = _
  rw [fderiv_fun_add (h1.fun_mul h2) (differentiableAt_const D), fderiv_fun_mul h1 h2]
  simp only [add_apply, smul_apply, smul_eq_mul, fderiv_const_apply, add_zero]
  rw [fderiv_comp_apply (g := fun θ => Real.cos θ / Real.sin θ) 2 hc.differentiableAt,
    fderiv_comp_apply (g := B) 3 hB, hc.deriv]
  have hsc := Real.sin_sq_add_cos_sq (y 2)
  field_simp
  linear_combination (-(v 2 * B (y 3))) * hsc

private theorem fderiv_diagC_sphereField (A B : ℝ → ℝ) (D : ℝ) {y : MinkowskiModel 3}
    (h0 : y 1 ≠ 0) (h1 : y 1 - 2 * M ≠ 0) (i : Fin 4) :
    fderiv ℝ (fun z => diagC M z i) y (sphereField A B D y) =
      if i = 3 then y 1 ^ 2 * (2 * Real.sin (y 2) * Real.cos (y 2)) * A (y 3) else 0 := by
  have hv1 : sphereField A B D y 1 = 0 := rfl
  have hv2 : sphereField A B D y 2 = A (y 3) := rfl
  fin_cases i
  · show fderiv ℝ (fun z : MinkowskiModel 3 => (fun r => -((r - 2 * M) / r)) (z 1)) y _ = _
    rw [fderiv_comp_apply (g := fun r => -((r - 2 * M) / r)) 1
      (by fun_prop (disch := assumption)), hv1]
    simp
  · show fderiv ℝ (fun z : MinkowskiModel 3 => (fun r => r / (r - 2 * M)) (z 1)) y _ = _
    rw [fderiv_comp_apply (g := fun r => r / (r - 2 * M)) 1
      (by fun_prop (disch := assumption)), hv1]
    simp
  · show fderiv ℝ (fun z : MinkowskiModel 3 => (fun r => r ^ 2) (z 1)) y _ = _
    rw [fderiv_comp_apply (g := fun r : ℝ => r ^ 2) 1 (by fun_prop), hv1]
    simp
  · have hd : HasDerivAt (fun θ => Real.sin θ ^ 2)
        ((2 : ℕ) * Real.sin (y 2) ^ (2 - 1) * Real.cos (y 2)) (y 2) :=
      (Real.hasDerivAt_sin (y 2)).pow 2
    have hr : DifferentiableAt ℝ (fun r : ℝ => r ^ 2) (y 1) := by fun_prop
    show fderiv ℝ (fun z : MinkowskiModel 3 =>
      (fun r => r ^ 2) (z 1) * (fun θ => Real.sin θ ^ 2) (z 2)) y _ = _
    rw [fderiv_fun_mul (differentiableAt_comp_apply 1 hr)
      (differentiableAt_comp_apply 2 hd.differentiableAt)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [fderiv_comp_apply 1 hr, fderiv_comp_apply 2 hd.differentiableAt, hv1, hv2, hd.deriv]
    simp
    ring

/-- The derivatives `∂ᵢ ξᵏ` of the components of `sphereField`. -/
private def sphereJac (A B : ℝ → ℝ) (y : MinkowskiModel 3) (k i : Fin 4) : ℝ :=
  ![0, 0, deriv A (y 3) * (Pi.single i 1 : MinkowskiModel 3) 3,
    -((Pi.single i 1 : MinkowskiModel 3) 2 * B (y 3)) / Real.sin (y 2) ^ 2 +
      Real.cos (y 2) / Real.sin (y 2) * (deriv B (y 3) * (Pi.single i 1 : MinkowskiModel 3) 3)] k

private theorem fderiv_sphereField {A B : ℝ → ℝ} (D : ℝ) {y : MinkowskiModel 3}
    (hs : Real.sin (y 2) ≠ 0) (hA : DifferentiableAt ℝ A (y 3))
    (hB : DifferentiableAt ℝ B (y 3)) (k i : Fin 4) :
    fderiv ℝ (fun z => sphereField A B D z k) y (Pi.single i 1) = sphereJac A B y k i := by
  fin_cases k
  · exact fderiv_sphereField_zero A B D y _
  · exact fderiv_sphereField_one A B D y _
  · exact fderiv_sphereField_two B D hA _
  · exact fderiv_sphereField_three A D hs hB _

/-- **The Killing equation for the fields along the spheres.** If `A' = B` and `B' = −A`, the
components `ξ = (0, 0, A(φ), cot θ · B(φ) + D)` satisfy `L_ξ g = 0` on the exterior domain. -/
theorem lieOf_sphereField (hM : 0 ≤ M) {A B : ℝ → ℝ} (D : ℝ)
    (hA : ∀ φ, HasDerivAt A (B φ) φ) (hB : ∀ φ, HasDerivAt B (-A φ) φ) :
    ∀ y ∈ domain M, ∀ i j, lieOf (metric hM).coefficient (sphereField A B D) y i j = 0 := by
  intro y hy i j
  have hr : 2 * M < y 1 := hy.1
  have h0 : y 1 ≠ 0 := by
    have : 0 < y 1 := by linarith
    exact this.ne'
  have h1 : y 1 - 2 * M ≠ 0 := by
    have : 0 < y 1 - 2 * M := by linarith
    exact this.ne'
  have hs : Real.sin (y 2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hy.2.1 hy.2.2).ne'
  have dA := (hA (y 3)).deriv
  have dB := (hB (y 3)).deriv
  rw [coefficient_eq_diagC, lieOf_diagonal, fderiv_diagC_sphereField A B D h0 h1]
  simp only [fderiv_sphereField D hs (hA (y 3)).differentiableAt (hB (y 3)).differentiableAt]
  fin_cases i <;> fin_cases j <;> simp [sphereJac, diagC, dA, dB] <;>
    field_simp <;> ring

/-- A field whose components are smooth on `U` gives a vector field whose section of the
tangent bundle is differentiable. -/
theorem mdifferentiableAt_vectorFieldOf {d : ℕ} {U : Opens (MinkowskiModel d)}
    {ξ : MinkowskiModel d → MinkowskiModel d} (hξ : ContDiffOn ℝ ∞ ξ U) (x₀ y : U) :
    MDifferentiableAt 𝓘(ℝ, MinkowskiModel d)
      ((𝓘(ℝ, MinkowskiModel d)).prod 𝓘(ℝ, MinkowskiModel d)) (T% (vectorFieldOf x₀ ξ)) y := by
  have h : vectorFieldOf x₀ ξ =
      fun z : U => ∑ k, ξ z k • chartField (physicalChart x₀) (Pi.single k 1) z := by
    funext z
    exact LorentzMetric.chartField_eq_sum _ z (ξ z)
  rw [h]
  refine MDifferentiableAt.sum_section fun k _ => ?_
  have hc : MDifferentiableAt 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d)
      (fun z : U => ξ z) y :=
    (CoordinateMetric.contMDiff_components hξ y).mdifferentiableAt (by simp)
  have hk : MDifferentiableAt 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, ℝ) (fun z : U => ξ z k) y :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) k).mdifferentiable
      _).comp y hc
  exact hk.fun_smul_section (CoordinateMetric.chartField_mdifferentiableAt x₀ y _)

/-! ### The rotations -/

/-- **The generators of the rotations** about the `x`, `y` and `z` axes, in the co-ordinates
`(t, r, θ, φ)`: `K₀ = −sin φ ∂_θ − cot θ cos φ ∂_φ`, `K₁ = cos φ ∂_θ − cot θ sin φ ∂_φ` and
`K₂ = ∂_φ`. -/
def rotationField (a : Fin 3) (x : MinkowskiModel 3) : MinkowskiModel 3 :=
  ![![0, 0, -Real.sin (x 3), -(Real.cos (x 2) / Real.sin (x 2)) * Real.cos (x 3)],
    ![0, 0, Real.cos (x 3), -(Real.cos (x 2) / Real.sin (x 2)) * Real.sin (x 3)],
    ![0, 0, 0, 1]] a

/-- The rotations do not move `t` and `r`. -/
@[simp] theorem rotationField_zero (a : Fin 3) (x : MinkowskiModel 3) :
    rotationField a x 0 = 0 := by
  fin_cases a <;> rfl

/-- The rotations do not move `t` and `r`. -/
@[simp] theorem rotationField_one (a : Fin 3) (x : MinkowskiModel 3) :
    rotationField a x 1 = 0 := by
  fin_cases a <;> rfl

private theorem rotationField_eq_sphereField (a : Fin 3) :
    ∃ A B : ℝ → ℝ, ∃ D : ℝ, ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ B ∧
      (∀ φ, HasDerivAt A (B φ) φ) ∧ (∀ φ, HasDerivAt B (-A φ) φ) ∧
        rotationField a = sphereField A B D := by
  fin_cases a
  · refine ⟨fun φ => -Real.sin φ, fun φ => -Real.cos φ, 0, Real.contDiff_sin.neg,
      Real.contDiff_cos.neg, fun φ => (Real.hasDerivAt_sin φ).neg,
      fun φ => (Real.hasDerivAt_cos φ).neg, ?_⟩
    funext x k
    fin_cases k <;> simp [rotationField, sphereField]
  · refine ⟨Real.cos, fun φ => -Real.sin φ, 0, Real.contDiff_cos, Real.contDiff_sin.neg,
      Real.hasDerivAt_cos, fun φ => (Real.hasDerivAt_sin φ).neg, ?_⟩
    funext x k
    fin_cases k <;> simp [rotationField, sphereField]
  · refine ⟨fun _ => 0, fun _ => 0, 1, contDiff_const, contDiff_const,
      fun φ => hasDerivAt_const φ 0,
      fun φ => (hasDerivAt_const φ (0 : ℝ)).congr_deriv (by simp), ?_⟩
    funext x k
    fin_cases k <;> simp [rotationField, sphereField]

/-- The components of `sphereField` are smooth where `sin θ ≠ 0`. -/
theorem contDiffOn_sphereField {A B : ℝ → ℝ} (D : ℝ) (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) : ContDiffOn ℝ ∞ (sphereField A B D) (domain M) := by
  have hθ : ContDiff ℝ ∞ fun x : MinkowskiModel 3 => x 2 := contDiff_apply ℝ (fun _ => ℝ) 2
  have hφ : ContDiff ℝ ∞ fun x : MinkowskiModel 3 => x 3 := contDiff_apply ℝ (fun _ => ℝ) 3
  have hs : ∀ x ∈ (domain M : Set (MinkowskiModel 3)), Real.sin (x 2) ≠ 0 := fun x hx =>
    (Real.sin_pos_of_pos_of_lt_pi hx.2.1 hx.2.2).ne'
  refine contDiffOn_pi.mpr fun k => ?_
  fin_cases k
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact (hA.comp hφ).contDiffOn
  · show ContDiffOn ℝ ∞ (fun x : MinkowskiModel 3 =>
      Real.cos (x 2) / Real.sin (x 2) * B (x 3) + D) _
    exact ((hθ.cos.contDiffOn.div hθ.sin.contDiffOn hs).mul (hB.comp hφ).contDiffOn).add
      contDiffOn_const

/-- The components of the rotation generators are smooth on the exterior domain. -/
theorem contDiffOn_rotationField (a : Fin 3) :
    ContDiffOn ℝ ∞ (rotationField a) (domain M) := by
  obtain ⟨A, B, D, hA, hB, -, -, h⟩ := rotationField_eq_sphereField a
  rw [h]
  exact contDiffOn_sphereField D hA hB

/-- **The Killing equation for the rotations**: `L_{K_a} g = 0` on the exterior domain, since
`g_θθ = r²`, `g_φφ = r² sin²θ` and the other coefficients depend on `r` only. -/
theorem lieOf_rotationField (hM : 0 ≤ M) (a : Fin 3) :
    ∀ y ∈ domain M, ∀ i j, lieOf (metric hM).coefficient (rotationField a) y i j = 0 := by
  obtain ⟨A, B, D, -, -, hA, hB, h⟩ := rotationField_eq_sphereField a
  rw [h]
  exact lieOf_sphereField hM D hA hB

/-- **The rotations are Killing fields** of the exterior Schwarzschild metric. -/
theorem isKillingField_rotationField (hM : 0 ≤ M) (x₀ : domain M) (a : Fin 3) :
    (metric hM).toLorentzMetric.IsKillingField (vectorFieldOf x₀ (rotationField a)) :=
  (metric hM).isKillingField_of_lieOf x₀ (contDiffOn_rotationField a) (lieOf_rotationField hM a)

/-! ### The angular momentum -/

/-- The angular momentum `J_a = g(K_a, γ̇)` of a curve about the axis `a`. -/
def angularMomentum (hM : 0 ≤ M) (x₀ : domain M) (γ : ℝ → domain M) (τ : ℝ) (a : Fin 3) : ℝ :=
  (metric hM).toLorentzMetric.form (γ τ) (vectorFieldOf x₀ (rotationField a) (γ τ))
    (curveVelocity γ τ)

/-- **The conservation of angular momentum.** Along a geodesic, given on a convex set of
parameters, each component `J_a` is constant. -/
theorem angularMomentum_eq (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (a : Fin 3) :
    angularMomentum hM x₀ γ τ₁ a = angularMomentum hM x₀ γ τ₂ a :=
  (isKillingField_rotationField hM x₀ a).pairing_eq
    (fun y => mdifferentiableAt_vectorFieldOf (contDiffOn_rotationField a) x₀ y) hγ hs h₁ h₂

/-- The co-ordinate expression `r² (K_a^θ v^θ + sin²θ K_a^φ v^φ)` of the angular momentum of a
velocity `v` at `x`. -/
def angularComponent (a : Fin 3) (x v : MinkowskiModel 3) : ℝ :=
  x 1 ^ 2 * (rotationField a x 2 * v 2 + Real.sin (x 2) ^ 2 * rotationField a x 3 * v 3)

/-- In co-ordinates, `J_a = r² (K_a^θ θ̇ + sin²θ K_a^φ φ̇)`. -/
theorem angularMomentum_eq_angularComponent (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M}
    {τ : ℝ} (hγ : DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel 3)) τ) (a : Fin 3) :
    angularMomentum hM x₀ γ τ a =
      angularComponent a (γ τ) (deriv (fun t => (γ t : MinkowskiModel 3)) τ) := by
  unfold angularMomentum CoordinateMetric.vectorFieldOf
  rw [(metric hM).pairing_curveVelocity hγ x₀, coefficient_eq_diagC]
  simp [Fin.sum_univ_four, Matrix.diagonal_apply, diagC, angularComponent]
  ring

/-- The angular momentum about the `x` axis in co-ordinates. -/
theorem angularComponent_zero {x : MinkowskiModel 3} (hs : Real.sin (x 2) ≠ 0)
    (v : MinkowskiModel 3) :
    angularComponent 0 x v = x 1 ^ 2 * (-Real.sin (x 3) * v 2 -
      Real.sin (x 2) * Real.cos (x 2) * Real.cos (x 3) * v 3) := by
  have h2 : rotationField 0 x 2 = -Real.sin (x 3) := rfl
  have h3 : rotationField 0 x 3 = -(Real.cos (x 2) / Real.sin (x 2)) * Real.cos (x 3) := rfl
  have hc : Real.sin (x 2) ^ 2 * (Real.cos (x 2) / Real.sin (x 2)) =
      Real.sin (x 2) * Real.cos (x 2) := by
    field_simp
  rw [angularComponent, h2, h3]
  linear_combination (-(x 1 ^ 2 * Real.cos (x 3) * v 3)) * hc

/-- The angular momentum about the `y` axis in co-ordinates. -/
theorem angularComponent_one {x : MinkowskiModel 3} (hs : Real.sin (x 2) ≠ 0)
    (v : MinkowskiModel 3) :
    angularComponent 1 x v = x 1 ^ 2 * (Real.cos (x 3) * v 2 -
      Real.sin (x 2) * Real.cos (x 2) * Real.sin (x 3) * v 3) := by
  have h2 : rotationField 1 x 2 = Real.cos (x 3) := rfl
  have h3 : rotationField 1 x 3 = -(Real.cos (x 2) / Real.sin (x 2)) * Real.sin (x 3) := rfl
  have hc : Real.sin (x 2) ^ 2 * (Real.cos (x 2) / Real.sin (x 2)) =
      Real.sin (x 2) * Real.cos (x 2) := by
    field_simp
  rw [angularComponent, h2, h3]
  linear_combination (-(x 1 ^ 2 * Real.sin (x 3) * v 3)) * hc

/-- The angular momentum about the `z` axis in co-ordinates: `r² sin²θ v^φ`. -/
theorem angularComponent_two (x v : MinkowskiModel 3) :
    angularComponent 2 x v = x 1 ^ 2 * (Real.sin (x 2) ^ 2 * v 3) := by
  simp [angularComponent, rotationField]

/-- The square of the angular momentum is `r⁴ (v_θ² + sin²θ v_φ²)`. -/
theorem sum_angularComponent_sq {x : MinkowskiModel 3} (hs : Real.sin (x 2) ≠ 0)
    (v : MinkowskiModel 3) :
    angularComponent 0 x v ^ 2 + angularComponent 1 x v ^ 2 + angularComponent 2 x v ^ 2 =
      x 1 ^ 4 * (v 2 ^ 2 + Real.sin (x 2) ^ 2 * v 3 ^ 2) := by
  rw [angularComponent_zero hs, angularComponent_one hs, angularComponent_two]
  have hθ := Real.sin_sq_add_cos_sq (x 2)
  have hφ := Real.sin_sq_add_cos_sq (x 3)
  linear_combination (x 1 ^ 4 * v 2 ^ 2 +
    x 1 ^ 4 * Real.sin (x 2) ^ 2 * Real.cos (x 2) ^ 2 * v 3 ^ 2) * hφ +
    x 1 ^ 4 * Real.sin (x 2) ^ 2 * v 3 ^ 2 * hθ

/-- The radial unit vector `n = (sin θ cos φ, sin θ sin φ, cos θ)`. -/
def radialDirection (x : MinkowskiModel 3) : Fin 3 → ℝ :=
  ![Real.sin (x 2) * Real.cos (x 3), Real.sin (x 2) * Real.sin (x 3), Real.cos (x 2)]

/-- The angular momentum is orthogonal to the radial direction: `n · J = 0`. -/
theorem direction_angularComponent {x : MinkowskiModel 3} (hs : Real.sin (x 2) ≠ 0)
    (v : MinkowskiModel 3) :
    radialDirection x 0 * angularComponent 0 x v + radialDirection x 1 * angularComponent 1 x v +
      radialDirection x 2 * angularComponent 2 x v = 0 := by
  rw [angularComponent_zero hs, angularComponent_one hs, angularComponent_two]
  have hφ := Real.sin_sq_add_cos_sq (x 3)
  have n0 : radialDirection x 0 = Real.sin (x 2) * Real.cos (x 3) := rfl
  have n1 : radialDirection x 1 = Real.sin (x 2) * Real.sin (x 3) := rfl
  have n2 : radialDirection x 2 = Real.cos (x 2) := rfl
  rw [n0, n1, n2]
  linear_combination (-(x 1 ^ 2 * Real.sin (x 2) ^ 2 * Real.cos (x 2) * v 3)) * hφ

private theorem sin_ne_zero_of_mem {x : MinkowskiModel 3} (hx : x ∈ domain M) :
    Real.sin (x 2) ≠ 0 :=
  (Real.sin_pos_of_pos_of_lt_pi hx.2.1 hx.2.2).ne'

/-- **The square of the angular momentum** of a curve: `J₀² + J₁² + J₂² = r⁴ (θ̇² + sin²θ φ̇²)`. -/
theorem sum_angularMomentum_sq (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {τ : ℝ}
    (hγ : DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel 3)) τ) :
    angularMomentum hM x₀ γ τ 0 ^ 2 + angularMomentum hM x₀ γ τ 1 ^ 2 +
        angularMomentum hM x₀ γ τ 2 ^ 2 =
      (γ τ : MinkowskiModel 3) 1 ^ 4 * (deriv (fun t => (γ t : MinkowskiModel 3)) τ 2 ^ 2 +
        Real.sin ((γ τ : MinkowskiModel 3) 2) ^ 2 *
          deriv (fun t => (γ t : MinkowskiModel 3)) τ 3 ^ 2) := by
  simp only [angularMomentum_eq_angularComponent hM x₀ hγ]
  exact sum_angularComponent_sq (sin_ne_zero_of_mem (γ τ).property) _

/-- **The angular momentum is orthogonal to the radius**: `n₀ J₀ + n₁ J₁ + n₂ J₂ = 0`, with
`n` the radial unit vector at the event of the curve. -/
theorem direction_angularMomentum (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {τ : ℝ}
    (hγ : DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel 3)) τ) :
    radialDirection (γ τ) 0 * angularMomentum hM x₀ γ τ 0 +
        radialDirection (γ τ) 1 * angularMomentum hM x₀ γ τ 1 +
      radialDirection (γ τ) 2 * angularMomentum hM x₀ γ τ 2 = 0 := by
  simp only [angularMomentum_eq_angularComponent hM x₀ hγ]
  exact direction_angularComponent (sin_ne_zero_of_mem (γ τ).property) _

/-- **The motion is in a plane through the centre** (Landau–Lifshitz, §101). Along a geodesic,
given on a convex set of parameters, the vector `J = (J₀, J₁, J₂)` is constant and the radial
direction `n` of every event of the geodesic is orthogonal to it. -/
theorem planar_motion (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {τ₀ τ : ℝ}
    (h₀ : τ₀ ∈ s) (hτ : τ ∈ s) :
    (∀ a, angularMomentum hM x₀ γ τ a = angularMomentum hM x₀ γ τ₀ a) ∧
      radialDirection (γ τ) 0 * angularMomentum hM x₀ γ τ₀ 0 +
          radialDirection (γ τ) 1 * angularMomentum hM x₀ γ τ₀ 1 +
        radialDirection (γ τ) 2 * angularMomentum hM x₀ γ τ₀ 2 = 0 := by
  have hJ (a : Fin 3) := angularMomentum_eq hM x₀ hγ hs hτ h₀ a
  refine ⟨hJ, ?_⟩
  have hd : DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel 3)) τ :=
    (CoordinateMetric.contMDiffAt_iff_contDiffAt_val.mp (hγ τ hτ).1).differentiableAt
      (by norm_num)
  rw [← hJ 0, ← hJ 1, ← hJ 2]
  exact direction_angularMomentum hM x₀ hd

/-! ### Equatorial motion -/

/-- In the equatorial plane `θ = π/2`, with `v^θ = 0`, the angular momentum is
`(0, 0, r² v^φ)`. -/
theorem angularComponent_equatorial {x v : MinkowskiModel 3} (hθ : x 2 = Real.pi / 2)
    (hv : v 2 = 0) :
    angularComponent 0 x v = 0 ∧ angularComponent 1 x v = 0 ∧
      angularComponent 2 x v = x 1 ^ 2 * v 3 := by
  have hs : Real.sin (x 2) ≠ 0 := by simp [hθ]
  rw [angularComponent_zero hs, angularComponent_one hs, angularComponent_two]
  simp [hθ, hv]

/-- The points `(t, r, π/2, φ)` with `r > 2M` lie in the exterior domain. -/
theorem equatorial_mem_domain {r : ℝ} (hr : 2 * M < r) (t φ : ℝ) :
    (![t, r, Real.pi / 2, φ] : MinkowskiModel 3) ∈ domain M :=
  ⟨hr, show 0 < Real.pi / 2 by positivity, show Real.pi / 2 < Real.pi by linarith [Real.pi_pos]⟩

/-- The uniform circular motion `t ↦ (t, r, π/2, Ω t)` in the equatorial plane. -/
def equatorialCircle {r : ℝ} (hr : 2 * M < r) (Ω : ℝ) (t : ℝ) : domain M :=
  ⟨![t, r, Real.pi / 2, Ω * t], equatorial_mem_domain hr t (Ω * t)⟩

/-- **A regression instance**: the uniform circular motion with the angular velocity `Ω` in the
equatorial plane at the radius `r` has the angular momentum `J = (0, 0, r² Ω)`. -/
theorem angularMomentum_equatorialCircle (hM : 0 ≤ M) (x₀ : domain M) {r : ℝ}
    (hr : 2 * M < r) (Ω τ : ℝ) :
    angularMomentum hM x₀ (equatorialCircle hr Ω) τ 0 = 0 ∧
      angularMomentum hM x₀ (equatorialCircle hr Ω) τ 1 = 0 ∧
        angularMomentum hM x₀ (equatorialCircle hr Ω) τ 2 = r ^ 2 * Ω := by
  have hc : (fun t => (equatorialCircle hr Ω t : MinkowskiModel 3)) =
      fun t => (![t, r, Real.pi / 2, Ω * t] : MinkowskiModel 3) := rfl
  have hd : HasDerivAt (fun t => (equatorialCircle hr Ω t : MinkowskiModel 3))
      (![1, 0, 0, Ω] : MinkowskiModel 3) τ := by
    rw [hc]
    refine hasDerivAt_pi.mpr fun i => ?_
    fin_cases i
    · simpa using hasDerivAt_id' τ
    · simpa using hasDerivAt_const τ r
    · simpa using hasDerivAt_const τ (Real.pi / 2)
    · simpa using (hasDerivAt_id τ).const_mul Ω
  simp only [angularMomentum_eq_angularComponent hM x₀ hd.differentiableAt, hd.deriv]
  obtain ⟨h0, h1, h2⟩ := angularComponent_equatorial
    (x := (equatorialCircle hr Ω τ : MinkowskiModel 3)) (v := ![1, 0, 0, Ω]) rfl rfl
  exact ⟨h0, h1, h2⟩

private theorem fderiv_diagC {y : MinkowskiModel 3} (h0 : y 1 ≠ 0) (h1 : y 1 - 2 * M ≠ 0)
    (v : MinkowskiModel 3) (i : Fin 4) :
    fderiv ℝ (fun z => diagC M z i) y v =
      ![-(2 * M / y 1 ^ 2) * v 1, -(2 * M / (y 1 - 2 * M) ^ 2) * v 1, 2 * y 1 * v 1,
        2 * y 1 * Real.sin (y 2) ^ 2 * v 1 +
          y 1 ^ 2 * (2 * Real.sin (y 2) * Real.cos (y 2)) * v 2] i := by
  fin_cases i
  · have hd : HasDerivAt (fun r => -((r - 2 * M) / r)) (-(2 * M / y 1 ^ 2)) (y 1) := by
      refine ((((hasDerivAt_id' (y 1)).sub_const (2 * M)).div (hasDerivAt_id' (y 1))
        h0).neg).congr_deriv ?_
      field_simp
      ring
    show fderiv ℝ (fun z : MinkowskiModel 3 => (fun r => -((r - 2 * M) / r)) (z 1)) y _ = _
    rw [fderiv_comp_apply 1 hd.differentiableAt, hd.deriv]
    rfl
  · have hd : HasDerivAt (fun r => r / (r - 2 * M)) (-(2 * M / (y 1 - 2 * M) ^ 2)) (y 1) := by
      refine ((hasDerivAt_id' (y 1)).div ((hasDerivAt_id' (y 1)).sub_const (2 * M))
        h1).congr_deriv ?_
      field_simp
      ring
    show fderiv ℝ (fun z : MinkowskiModel 3 => (fun r => r / (r - 2 * M)) (z 1)) y _ = _
    rw [fderiv_comp_apply 1 hd.differentiableAt, hd.deriv]
    rfl
  · show fderiv ℝ (fun z : MinkowskiModel 3 => (fun r => r ^ 2) (z 1)) y _ = _
    rw [fderiv_comp_apply (g := fun r : ℝ => r ^ 2) 1 (by fun_prop)]
    simp
  · have hd : HasDerivAt (fun θ => Real.sin θ ^ 2)
        ((2 : ℕ) * Real.sin (y 2) ^ (2 - 1) * Real.cos (y 2)) (y 2) :=
      (Real.hasDerivAt_sin (y 2)).pow 2
    have hr : DifferentiableAt ℝ (fun r : ℝ => r ^ 2) (y 1) := by fun_prop
    show fderiv ℝ (fun z : MinkowskiModel 3 =>
      (fun r => r ^ 2) (z 1) * (fun θ => Real.sin θ ^ 2) (z 2)) y _ = _
    rw [fderiv_fun_mul (differentiableAt_comp_apply 1 hr)
      (differentiableAt_comp_apply 2 hd.differentiableAt)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [fderiv_comp_apply 1 hr, fderiv_comp_apply 2 hd.differentiableAt, hd.deriv]
    simp
    ring

private theorem diagC_ne_zero (hM : 0 ≤ M) {y : MinkowskiModel 3} (hy : y ∈ domain M)
    (i : Fin 4) : diagC M y i ≠ 0 := by
  have hr : 2 * M < y 1 := hy.1
  have h0 : 0 < y 1 := by linarith
  have h1 : 0 < y 1 - 2 * M := by linarith
  have hs := sin_ne_zero_of_mem hy
  fin_cases i
  · exact neg_ne_zero.mpr (div_pos h1 h0).ne'
  · exact (div_pos h0 h1).ne'
  · exact (pow_pos h0 2).ne'
  · exact mul_ne_zero (pow_pos h0 2).ne' (pow_ne_zero 2 hs)

/-- **The circular orbits** (Landau–Lifshitz, §101): the uniform circular motion
`t ↦ (t, r, π/2, Ω t)` in the equatorial plane is an affinely parametrized geodesic of the
exterior Schwarzschild field when `r³ Ω² = M` (Kepler's third law, exact in the time `t`). -/
theorem isGeodesicOn_equatorialCircle (hM : 0 ≤ M) {r : ℝ} (hr : 2 * M < r) {Ω : ℝ}
    (hΩ : r ^ 3 * Ω ^ 2 = M) :
    (metric hM).toLorentzMetric.IsGeodesicOn univ (equatorialCircle hr Ω) := by
  have hc : (fun t => (equatorialCircle hr Ω t : MinkowskiModel 3)) =
      fun t => (![0, r, Real.pi / 2, 0] : MinkowskiModel 3) + t • ![1, 0, 0, Ω] := by
    funext t i
    fin_cases i <;> simp [equatorialCircle, mul_comm]
  have hline : ContDiff ℝ 2 (fun t : ℝ =>
      (![0, r, Real.pi / 2, 0] : MinkowskiModel 3) + t • ![1, 0, 0, Ω]) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hderiv : deriv (fun t => (equatorialCircle hr Ω t : MinkowskiModel 3)) =
      fun _ => (![1, 0, 0, Ω] : MinkowskiModel 3) := by
    funext t
    rw [hc]
    simpa using (((hasDerivAt_id t).smul_const (![1, 0, 0, Ω] : MinkowskiModel 3)).const_add
      (![0, r, Real.pi / 2, 0] : MinkowskiModel 3)).deriv
  rw [(metric hM).isGeodesicOn_iff isOpen_univ (hc ▸ hline.contDiffOn)]
  intro t _ k
  have hy := (equatorialCircle hr Ω t).property
  set y : MinkowskiModel 3 := (equatorialCircle hr Ω t : MinkowskiModel 3)
  have y1 : y 1 = r := rfl
  have y2 : y 2 = Real.pi / 2 := rfl
  have h0 : y 1 ≠ 0 := by rw [y1]; linarith
  have h1 : y 1 - 2 * M ≠ 0 := by rw [y1]; linarith
  have hr0 : r ≠ 0 := by linarith
  have hr1 : r - 2 * M ≠ 0 := by linarith
  rw [hderiv, deriv_const, coefficient_eq_diagC]
  simp only [CoordinateMetric.christoffelOf_diagonal _ y (diagC_ne_zero hM hy), fderiv_diagC h0 h1,
    y1, y2]
  fin_cases k <;> simp [diagC, Fin.sum_univ_succ]
  rw [y1]
  field_simp
  linear_combination (-(r - 2 * M)) * hΩ

/-- **The conservation of angular momentum on a circular orbit**: along the geodesic
`t ↦ (t, r, π/2, Ω t)` with `r³ Ω² = M`, the hypotheses of `planar_motion` hold on the whole
line, and `J = (0, 0, r² Ω)` is orthogonal to the radial direction of every event. -/
theorem planar_motion_equatorialCircle (hM : 0 ≤ M) (x₀ : domain M) {r : ℝ} (hr : 2 * M < r)
    {Ω : ℝ} (hΩ : r ^ 3 * Ω ^ 2 = M) (τ₀ τ : ℝ) :
    (∀ a, angularMomentum hM x₀ (equatorialCircle hr Ω) τ a =
        angularMomentum hM x₀ (equatorialCircle hr Ω) τ₀ a) ∧
      radialDirection (equatorialCircle hr Ω τ) 0 *
            angularMomentum hM x₀ (equatorialCircle hr Ω) τ₀ 0 +
          radialDirection (equatorialCircle hr Ω τ) 1 *
            angularMomentum hM x₀ (equatorialCircle hr Ω) τ₀ 1 +
        radialDirection (equatorialCircle hr Ω τ) 2 *
          angularMomentum hM x₀ (equatorialCircle hr Ω) τ₀ 2 = 0 :=
  planar_motion hM x₀ (isGeodesicOn_equatorialCircle hM hr hΩ) convex_univ trivial trivial

/- The hypotheses are satisfiable: for `M = 1` the circle of radius `4` with `Ω = 1/8` is a
geodesic, with `J = (0, 0, 2)`. -/
example (x₀ : domain 1) (τ : ℝ) :
    (metric zero_le_one).toLorentzMetric.IsGeodesicOn univ
        (equatorialCircle (M := 1) (r := 4) (by norm_num) (1 / 8)) ∧
      angularMomentum zero_le_one x₀ (equatorialCircle (M := 1) (r := 4) (by norm_num) (1 / 8))
        τ 2 = 2 := by
  refine ⟨isGeodesicOn_equatorialCircle zero_le_one _ (by norm_num), ?_⟩
  rw [(angularMomentum_equatorialCircle zero_le_one x₀ _ (1 / 8) τ).2.2]
  norm_num

/- The co-ordinate expressions at the point `(0, 3, π/2, 0)` with the velocity `(1, 0, 1, 2)`:
`J = (0, 9, 18)`, so that `J² = 405 = 3⁴ (1² + 2²)` and `n · J = 0` with `n = (1, 0, 0)`. -/
example : angularComponent 0 ![0, 3, Real.pi / 2, 0] ![1, 0, 1, 2] = 0 ∧
    angularComponent 1 ![0, 3, Real.pi / 2, 0] ![1, 0, 1, 2] = 9 ∧
    angularComponent 2 ![0, 3, Real.pi / 2, 0] ![1, 0, 1, 2] = 18 := by
  have hs : Real.sin ((![0, 3, Real.pi / 2, 0] : MinkowskiModel 3) 2) ≠ 0 := by simp
  refine ⟨?_, ?_, ?_⟩
  · rw [angularComponent_zero hs]
    simp
  · rw [angularComponent_one hs]
    norm_num
  · rw [angularComponent_two]
    norm_num

end ProjectAinos.GeneralRelativity.SchwarzschildExterior
