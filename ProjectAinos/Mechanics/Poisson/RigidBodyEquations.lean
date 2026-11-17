/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Poisson.AsymmetricTop
public import ProjectAinos.Mechanics.Poisson.HeavyTop
public import ProjectAinos.Mechanics.Rigid.Reconstruction
public import ProjectAinos.Mechanics.Rigid.RotationAction

/-!
# The motion of a rigid body and the Lie–Poisson equations

The equations of motion of a rigid body of point masses, derived from Newton's
equations in `Rigid/Dynamics` and from Hamilton's principle in
`Rigid/RotationAction`, are the Lie–Poisson equations of `RigidBody` and
`HeavyTop` when the axes of the body are principal axes.

* `HeavyTop.field`: the vector field of the Lie–Poisson equations of the heavy
  top, with the values `(L × Ω + Γ × kχ, Γ × Ω)` (`HeavyTop.field_inl`,
  `HeavyTop.field_inr`).
* `IsRigidMotion.hasDerivAt_eulerField`: for a body with no moment of forces
  about its centre of mass, or about a fixed point, the angular momentum in
  the body frame is an integral curve of Euler's equations.
* `IsRigidMotion.hasDerivAt_heavyTopField`: for a body with a fixed point in a
  uniform field, the angular momentum and the direction of the field in the
  body frame are an integral curve of the Lie–Poisson equations of the heavy
  top.
* `hasDerivAt_heavyTopField_of_stationary`: the same for a curve of rotations
  that is stationary for the action with the potential `Γ · kχ`.
* `rotation_mulVec_eulerSolution`: conversely, a solution of Euler's equations
  defines a rotation for all times, and the angular momentum is constant in
  space along it; `rotation_mulVec_ellipticMotion` is the motion of the
  asymmetrical top by elliptic functions.
* `stationary_rotationAction_rotation`: the rotation reconstructed from a
  smooth solution of `d(J Ω)/dt = J Ω × Ω` is stationary for the action of the
  free body.
-/

@[expose] public section
noncomputable section

open Set Matrix
open scoped ContDiff

namespace ProjectAinos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing

namespace HeavyTop

/-- The vector field of the Lie–Poisson equations of the heavy top, on the
space of the angular momentum `L` and of the vertical vector `Γ`. -/
def field (I : Fin 3 → ℝ) (k : ℝ) (χ : Fin 3 → ℝ) :
    (Fin 3 ⊕ Fin 3 → ℝ) → Fin 3 ⊕ Fin 3 → ℝ :=
  realField (poisson.hamiltonian (hamiltonian I k χ))

theorem contDiff_field (I : Fin 3 → ℝ) (k : ℝ) (χ : Fin 3 → ℝ) :
    ContDiff ℝ ∞ (field I k χ) :=
  contDiff_realField _

/-- `L̇ = L × Ω + Γ × kχ` with `Ωᵢ = Lᵢ / Iᵢ`. -/
theorem field_inl (I : Fin 3 → ℝ) (k : ℝ) (χ : Fin 3 → ℝ) (z : Fin 3 ⊕ Fin 3 → ℝ)
    (a : Fin 3) :
    field I k χ z (Sum.inl a) =
      ((fun i => z (Sum.inl i)) ⨯₃ (fun i => (I i)⁻¹ * z (Sum.inl i)) +
        (fun i => z (Sum.inr i)) ⨯₃ (k • χ)) a := by
  change (poisson.bracket (L a) (hamiltonian I k χ)).val z = _
  rw [poisson_L_hamiltonian]
  fin_cases a <;> rfl

/-- `Γ̇ = Γ × Ω`. -/
theorem field_inr (I : Fin 3 → ℝ) (k : ℝ) (χ : Fin 3 → ℝ) (z : Fin 3 ⊕ Fin 3 → ℝ)
    (a : Fin 3) :
    field I k χ z (Sum.inr a) =
      ((fun i => z (Sum.inr i)) ⨯₃ (fun i => (I i)⁻¹ * z (Sum.inl i))) a := by
  change (poisson.bracket (Γ a) (hamiltonian I k χ)).val z = _
  rw [poisson_Γ_hamiltonian]
  fin_cases a <;> rfl

end HeavyTop

namespace Rigid

open RigidBody SmoothGeometry

/-- In principal axes, `L × Ω` with `L = I Ω` is the field of Euler's
equations. -/
theorem cross_eq_eulerField {I : Fin 3 → ℝ} (hI : ∀ i, I i ≠ 0) (w : Fin 3 → ℝ) :
    (diagonal I *ᵥ w) ⨯₃ w = eulerField I (diagonal I *ᵥ w) := by
  have h0 := hI 0
  have h1 := hI 1
  have h2 := hI 2
  have e0 : ((diagonal I *ᵥ w) ⨯₃ w) 0 = eulerField I (diagonal I *ᵥ w) 0 := by
    rw [eulerField_zero]
    simp [cross_apply, mulVec_diagonal]
    field_simp
  have e1 : ((diagonal I *ᵥ w) ⨯₃ w) 1 = eulerField I (diagonal I *ᵥ w) 1 := by
    rw [eulerField_one]
    simp [cross_apply, mulVec_diagonal]
    field_simp
  have e2 : ((diagonal I *ᵥ w) ⨯₃ w) 2 = eulerField I (diagonal I *ᵥ w) 2 := by
    rw [eulerField_two]
    simp [cross_apply, mulVec_diagonal]
    field_simp
  ext i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2

/-- The field of Euler's equations is `L × Ω` with `Ωᵢ = Lᵢ / Iᵢ`. -/
theorem eulerField_eq_cross (I : Fin 3 → ℝ) (L : Fin 3 → ℝ) :
    eulerField I L = L ⨯₃ fun i => (I i)⁻¹ * L i := by
  have e0 : eulerField I L 0 = (L ⨯₃ fun i => (I i)⁻¹ * L i) 0 := by
    rw [eulerField_zero]
    simp [cross_apply]
    ring
  have e1 : eulerField I L 1 = (L ⨯₃ fun i => (I i)⁻¹ * L i) 1 := by
    rw [eulerField_one]
    simp [cross_apply]
    ring
  have e2 : eulerField I L 2 = (L ⨯₃ fun i => (I i)⁻¹ * L i) 2 := by
    rw [eulerField_two]
    simp [cross_apply]
    ring
  ext i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2

/-- A pair of curves `(L, Γ)` with `L̇ = L × Ω + Γ × kχ`, `Γ̇ = Γ × Ω` and
`L = I Ω` in principal axes is an integral curve of the Lie–Poisson equations
of the heavy top. -/
theorem hasDerivAt_heavyTopField_of_equations {I : Fin 3 → ℝ} (hI : ∀ i, I i ≠ 0) {k : ℝ}
    {χ : Fin 3 → ℝ} {L Γ : ℝ → Fin 3 → ℝ} {w : Fin 3 → ℝ} {t : ℝ}
    (hw : L t = diagonal I *ᵥ w)
    (hL : HasDerivAt L (L t ⨯₃ w + Γ t ⨯₃ (k • χ)) t) (hΓ : HasDerivAt Γ (Γ t ⨯₃ w) t) :
    HasDerivAt (fun u => Sum.elim (L u) (Γ u))
      (HeavyTop.field I k χ (Sum.elim (L t) (Γ t))) t := by
  have hΩ : (fun i => (I i)⁻¹ * (Sum.elim (L t) (Γ t) : Fin 3 ⊕ Fin 3 → ℝ) (Sum.inl i)) = w := by
    funext i
    simp only [Sum.elim_inl, hw, mulVec_diagonal]
    rw [← mul_assoc, inv_mul_cancel₀ (hI i), one_mul]
  refine hasDerivAt_pi.mpr fun j => ?_
  rcases j with a | a
  · rw [HeavyTop.field_inl, hΩ]
    exact hasDerivAt_pi.mp hL a
  · rw [HeavyTop.field_inr, hΩ]
    exact hasDerivAt_pi.mp hΓ a

section Newton

variable {ι : Type*} [Fintype ι] {m : ι → ℝ} {r : ι → Fin 3 → ℝ}
  {c c' : ℝ → Fin 3 → ℝ} {R R' : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {I : Fin 3 → ℝ}

/-- Euler's equations from Newton's equations: for a body in principal axes
with no moment of the forces about its centre of mass, or about a fixed
point, the angular momentum in the body frame is an integral curve of the
Lie–Poisson equations of the free body. -/
theorem IsRigidMotion.hasDerivAt_eulerField (h : IsRigidMotion c c' R R')
    (hpt : ∑ a, m a • r a = 0 ∨ ∀ s, c' s = 0) (hI : ∀ i, I i ≠ 0)
    (hin : inertia m r = diagonal I) {F : ι → Fin 3 → ℝ} {t : ℝ}
    (hF : ∀ a, HasDerivAt (fun u => m a • (c' u + R' u *ᵥ r a)) (F a) t)
    (hK : ∑ a, (R t *ᵥ r a) ⨯₃ F a = 0) :
    HasDerivAt (fun u => inertia m r *ᵥ angularVelocityBody (R u) (R' u))
      (eulerField I (inertia m r *ᵥ angularVelocityBody (R t) (R' t))) t := by
  have h1 := h.hasDerivAt_bodyAngularMomentum hpt hF
  rw [hK, mulVec_zero, add_zero] at h1
  refine h1.congr_deriv ?_
  rw [hin]
  exact cross_eq_eulerField hI _

/-- The heavy top from Newton's equations: a body with a fixed point, in
principal axes, under the uniform field `−g e` and forces `N` without moment
about the fixed point. The angular momentum and the direction `Γ = Rᵀ e` of
the field in the body frame are an integral curve of the Lie–Poisson
equations of the heavy top, with the weight `g` and the vector `Σ mₐ rₐ`. -/
theorem IsRigidMotion.hasDerivAt_heavyTopField (h : IsRigidMotion c c' R R')
    (hrest : ∀ s, c' s = 0) (hI : ∀ i, I i ≠ 0) (hin : inertia m r = diagonal I)
    {N : ι → Fin 3 → ℝ} {g : ℝ} {e : Fin 3 → ℝ} {t : ℝ}
    (hF : ∀ a, HasDerivAt (fun u => m a • (c' u + R' u *ᵥ r a)) (-(m a * g) • e + N a) t)
    (hN : ∑ a, (R t *ᵥ r a) ⨯₃ N a = 0) :
    HasDerivAt (fun u => Sum.elim (inertia m r *ᵥ angularVelocityBody (R u) (R' u))
        ((R u)ᵀ *ᵥ e))
      (HeavyTop.field I g (∑ a, m a • r a)
        (Sum.elim (inertia m r *ᵥ angularVelocityBody (R t) (R' t)) ((R t)ᵀ *ᵥ e))) t := by
  have h1 := h.hasDerivAt_bodyAngularMomentum (Or.inr hrest) hF
  have hK : (R t)ᵀ *ᵥ ∑ a, (R t *ᵥ r a) ⨯₃ (-(m a * g) • e + N a) =
      ((R t)ᵀ *ᵥ e) ⨯₃ (g • ∑ a, m a • r a) := by
    simp_rw [map_add]
    rw [Finset.sum_add_distrib, hN, add_zero,
      transpose_mulVec_sum_cross_weight (h.orthogonal t) (h.det_eq_one t)]
  rw [hK] at h1
  exact hasDerivAt_heavyTopField_of_equations hI (by rw [hin]) h1 (h.hasDerivAt_bodyVector e t)

end Newton

/-- The heavy top from Hamilton's principle: where the residual of the action
with the inertia tensor `diag I` and the potential `Γ · kχ` vanishes, the
angular momentum and the vector `Γ = Rᵀ γ` are an integral curve of the
Lie–Poisson equations of the heavy top. -/
theorem hasDerivAt_heavyTopField_of_residual {I : Fin 3 → ℝ} (hI : ∀ i, I i ≠ 0) {k : ℝ}
    {χ γ : Fin 3 → ℝ} {R₀ : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hR₀ : ∀ a b, ContDiff ℝ ∞ fun t => R₀ t a b) (horth : ∀ t, (R₀ t)ᵀ * R₀ t = 1) {t : ℝ}
    (hres : eulerPoissonResidual (diagonal I) (fun Γ : Fin 3 → ℝ => Γ ⬝ᵥ (k • χ)) γ R₀ t = 0) :
    HasDerivAt (fun u => Sum.elim (diagonal I *ᵥ curveVelocity R₀ u) ((R₀ u)ᵀ *ᵥ γ))
      (HeavyTop.field I k χ
        (Sum.elim (diagonal I *ᵥ curveVelocity R₀ t) ((R₀ t)ᵀ *ᵥ γ))) t := by
  have h1 := (eulerPoissonResidual_eq_zero_iff γ hR₀ t).mp hres
  rw [bodyGradient_dotProduct_const] at h1
  have hd : ∀ a b, HasDerivAt (fun s => R₀ s a b) (curveDeriv R₀ t a b) t := fun a b =>
    ((hR₀ a b).differentiable (by simp) t).hasDerivAt
  exact hasDerivAt_heavyTopField_of_equations hI rfl h1
    (hasDerivAt_transpose_mulVec hd horth γ)

/-- Hamilton's principle for the heavy top: a smooth curve of rotations that
is stationary for the action with the potential `Γ · kχ` among the families
with fixed ends follows the Lie–Poisson equations of the heavy top between
the ends. -/
theorem hasDerivAt_heavyTopField_of_stationary {I : Fin 3 → ℝ} (hI : ∀ i, I i ≠ 0) {k : ℝ}
    {χ γ : Fin 3 → ℝ} {R₀ : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {t₀ t₁ : ℝ} (hab : t₀ < t₁)
    (hR₀ : ∀ a b, ContDiff ℝ ∞ fun t => R₀ t a b) (horth : ∀ t, (R₀ t)ᵀ * R₀ t = 1)
    (hs : ∀ R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ, IsRotationFamily R → (∀ t, R (0, t) = R₀ t) →
      (∀ e, R (e, t₀) = R₀ t₀) → (∀ e, R (e, t₁) = R₀ t₁) →
      HasDerivAt (fun e => rotationAction (diagonal I) (fun Γ : Fin 3 → ℝ => Γ ⬝ᵥ (k • χ)) γ
        (fun s => R (e, s)) t₀ t₁) 0 0) {t : ℝ} (ht : t ∈ Ioo t₀ t₁) :
    HasDerivAt (fun u => Sum.elim (diagonal I *ᵥ curveVelocity R₀ u) ((R₀ u)ᵀ *ᵥ γ))
      (HeavyTop.field I k χ
        (Sum.elim (diagonal I *ᵥ curveVelocity R₀ t) ((R₀ t)ᵀ *ᵥ γ))) t := by
  have hV : ContDiff ℝ ∞ fun Γ : Fin 3 → ℝ => Γ ⬝ᵥ (k • χ) :=
    contDiff_dotProduct contDiff_id contDiff_const
  have hres := (stationary_rotationAction_iff hab (diagonal_transpose I) hV γ hR₀ horth).mp
    hs t ht
  exact hasDerivAt_heavyTopField_of_residual hI hR₀ horth hres

/-! ### From a solution of Euler's equations to a motion -/

section Reconstruction

variable {I : Fin 3 → ℝ} {y : ℝ → Fin 3 → ℝ}

/-- The angular velocity `Ωᵢ = Lᵢ / Iᵢ` of a solution of Euler's equations, as
a continuous curve. -/
def eulerVelocity (I : Fin 3 → ℝ) (y : ℝ → Fin 3 → ℝ)
    (hy : ∀ t, HasDerivAt y (eulerField I (y t)) t) : C(ℝ, Fin 3 → ℝ) :=
  ⟨fun t i => (I i)⁻¹ * y t i, by
    have hc : Continuous y := continuous_iff_continuousAt.mpr fun t => (hy t).continuousAt
    fun_prop⟩

/-- A solution of Euler's equations defines a rotation for all times, and the
angular momentum `R L` is constant in space along it. -/
theorem rotation_mulVec_eulerSolution (hy : ∀ t, HasDerivAt y (eulerField I (y t)) t)
    (R₀ : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    rotation (eulerVelocity I y hy) R₀ t *ᵥ y t = R₀ *ᵥ y 0 :=
  rotation_mulVec_eq (fun s => by
    have h := hy s
    rwa [eulerField_eq_cross] at h) t

/-- The motion of the asymmetrical top by elliptic functions as a rotation of
the body: the angular momentum is constant in space. -/
theorem rotation_mulVec_ellipticMotion (h0 : (I 2)⁻¹ - (I 1)⁻¹ < 0)
    (h1 : 0 < (I 0)⁻¹ - (I 2)⁻¹) (h2 : (I 1)⁻¹ - (I 0)⁻¹ ≤ 0) {A C : ℝ} (hC : C ≠ 0)
    (hk : topModulus I A C ^ 2 < 1) (R₀ : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    rotation (eulerVelocity I (ellipticMotion I A C)
        (hasDerivAt_ellipticMotion h0 h1 h2 hC hk)) R₀ t *ᵥ ellipticMotion I A C t =
      R₀ *ᵥ ![A, 0, C] := by
  rw [rotation_mulVec_eulerSolution, ellipticMotion_zero]

/-- The angular velocity of the reconstructed rotation, as a curve. -/
theorem curveVelocity_rotation {Ω : C(ℝ, Fin 3 → ℝ)} {R₀ : Matrix (Fin 3) (Fin 3) ℝ}
    (h₀ : R₀ᵀ * R₀ = 1) (t : ℝ) : curveVelocity (rotation Ω R₀) t = Ω t := by
  have hd : curveDeriv (rotation Ω R₀) t = rotation Ω R₀ t * hat (Ω t) := by
    ext a b
    exact (hasDerivAt_rotation Ω R₀ t a b).deriv
  rw [curveVelocity, hd, angularVelocityBody_rotation Ω R₀ h₀]

/-- The rotation reconstructed from a solution of `d(J Ω)/dt = J Ω × Ω` has no
residual for the action of the free body. -/
theorem eulerPoissonResidual_rotation {J : Matrix (Fin 3) (Fin 3) ℝ} {Ω : C(ℝ, Fin 3 → ℝ)}
    {R₀ : Matrix (Fin 3) (Fin 3) ℝ} (h₀ : R₀ᵀ * R₀ = 1) (γ : Fin 3 → ℝ) {t : ℝ}
    (hL : HasDerivAt (fun s => J *ᵥ Ω s) ((J *ᵥ Ω t) ⨯₃ Ω t) t) :
    eulerPoissonResidual J (fun _ => 0) γ (rotation Ω R₀) t = 0 := by
  have hfun : (fun s => J *ᵥ curveVelocity (rotation Ω R₀) s) = fun s => J *ᵥ Ω s :=
    funext fun s => by rw [curveVelocity_rotation h₀]
  have hg : bodyGradient (fun _ : Fin 3 → ℝ => (0 : ℝ)) ((rotation Ω R₀ t)ᵀ *ᵥ γ) = 0 := by
    funext i
    simp [bodyGradient]
  rw [eulerPoissonResidual, hfun, hL.deriv, curveVelocity_rotation h₀, hg, map_zero, sub_self,
    sub_zero]

/-- A solution of Euler's equations, reconstructed as a curve of rotations, is
stationary for the action of the free body between any two times. -/
theorem stationary_rotationAction_rotation {J : Matrix (Fin 3) (Fin 3) ℝ} (hJ : Jᵀ = J)
    {Ω : C(ℝ, Fin 3 → ℝ)} (hΩ : ContDiff ℝ ∞ Ω)
    (hL : ∀ t, HasDerivAt (fun s => J *ᵥ Ω s) ((J *ᵥ Ω t) ⨯₃ Ω t) t)
    {R₀ : Matrix (Fin 3) (Fin 3) ℝ} (h₀ : R₀ᵀ * R₀ = 1) (γ : Fin 3 → ℝ) {t₀ t₁ : ℝ}
    (hab : t₀ < t₁) {R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hR : IsRotationFamily R)
    (h0 : ∀ t, R (0, t) = rotation Ω R₀ t) (hend₀ : ∀ e, R (e, t₀) = rotation Ω R₀ t₀)
    (hend₁ : ∀ e, R (e, t₁) = rotation Ω R₀ t₁) :
    HasDerivAt (fun e => rotationAction J (fun _ => 0) γ (fun s => R (e, s)) t₀ t₁) 0 0 :=
  (stationary_rotationAction_iff hab hJ contDiff_const γ (contDiff_rotation hΩ R₀)
    (rotation_transpose_mul Ω R₀ h₀)).mpr
    (fun t _ => eulerPoissonResidual_rotation h₀ γ (hL t)) R hR h0 hend₀ hend₁

end Reconstruction

end Rigid

end ProjectAinos.Mechanics
