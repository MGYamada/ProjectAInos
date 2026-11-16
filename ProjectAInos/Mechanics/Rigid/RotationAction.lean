/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Rigid.Variation
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Hamilton's principle for a body with a fixed point

The Lagrangian of a rigid body with a fixed point is a function of the
angular velocity `Ω` in the body frame and of a vector `Γ = Rᵀ γ` fixed in
space, seen from the body: `Ω · J Ω / 2 − V(Γ)` (`bodyLagrangian`), with `J`
the inertia tensor. The action of a curve of rotations is `rotationAction`.

* `hasDerivAt_rotationAction`: for a smooth family of rotations with the
  variation field `η`,
  `dS/dε = [J Ω · η] − ∫ (d(J Ω)/dt − J Ω × Ω − Γ × ∇V(Γ)) · η dt`.
* `cayley`: the Cayley transform, a rational parametrization of rotations by
  vectors with `cayley 0 = 1` and derivative `ξ ↦ hat ξ` at `0`. With it every
  smooth field `η(t)` is the variation field of a family
  (`isRotationFamily_mul_cayley`, `familyVariation_mul_cayley`).
* `stationary_rotationAction_iff`: a smooth curve of rotations is stationary
  for the action among the families with fixed ends if and only if
  `d(J Ω)/dt = J Ω × Ω + Γ × ∇V(Γ)` between the ends: Euler's equations with
  the moment `Γ × ∇V(Γ)` (Landau–Lifshitz §§34–36).
-/

@[expose] public section
noncomputable section

open Set Matrix MeasureTheory
open scoped ContDiff

namespace ProjectAInos.Mechanics.Rigid

/-! ### Smooth curves of vectors -/

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiff_dotProduct {x y : E → Fin 3 → ℝ} (hx : ContDiff ℝ ∞ x)
    (hy : ContDiff ℝ ∞ y) : ContDiff ℝ ∞ fun p => x p ⬝ᵥ y p := by
  have h : ContDiff ℝ ∞ fun p => ∑ i, x p i * y p i :=
    ContDiff.sum fun i _ => (contDiff_pi.mp hx i).mul (contDiff_pi.mp hy i)
  exact h

theorem contDiff_mulVec (J : Matrix (Fin 3) (Fin 3) ℝ) {x : E → Fin 3 → ℝ}
    (hx : ContDiff ℝ ∞ x) : ContDiff ℝ ∞ fun p => J *ᵥ x p := by
  refine contDiff_pi.mpr fun a => ?_
  have h : ContDiff ℝ ∞ fun p => ∑ b, J a b * x p b :=
    ContDiff.sum fun b _ => contDiff_const.mul (contDiff_pi.mp hx b)
  exact h

theorem contDiff_transpose_mulVec {A : E → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ∀ a b, ContDiff ℝ ∞ fun p => A p a b) (γ : Fin 3 → ℝ) :
    ContDiff ℝ ∞ fun p => (A p)ᵀ *ᵥ γ := by
  refine contDiff_pi.mpr fun a => ?_
  have h : ContDiff ℝ ∞ fun p => ∑ b, A p b a * γ b :=
    ContDiff.sum fun b _ => (hA b a).mul contDiff_const
  exact h

theorem contDiff_angularVelocityBody {A B : E → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ∀ a b, ContDiff ℝ ∞ fun p => A p a b) (hB : ∀ a b, ContDiff ℝ ∞ fun p => B p a b) :
    ContDiff ℝ ∞ fun p => angularVelocityBody (A p) (B p) := by
  have h : ∀ a b, ContDiff ℝ ∞ fun p => ((A p)ᵀ * B p) a b := by
    intro a b
    have h1 : ContDiff ℝ ∞ fun p => ∑ k, A p k a * B p k b :=
      ContDiff.sum fun k _ => (hA k a).mul (hB k b)
    exact h1
  refine contDiff_pi.mpr fun i => ?_
  fin_cases i
  · exact h 2 1
  · exact h 0 2
  · exact h 1 0

end Smooth

theorem continuous_cross {x y : ℝ → Fin 3 → ℝ} (hx : Continuous x) (hy : Continuous y) :
    Continuous fun t => x t ⨯₃ y t := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp only [cross_apply] <;> fun_prop

/-- The angular velocity of a smooth curve of matrices is smooth. -/
theorem contDiff_curveVelocity {R : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hR : ∀ a b, ContDiff ℝ ∞ fun t => R t a b) : ContDiff ℝ ∞ (curveVelocity R) :=
  contDiff_angularVelocityBody hR fun a b => (hR a b).iterate_deriv 1

namespace IsRotationFamily

variable {R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ}

theorem contDiff_curveVelocity (h : IsRotationFamily R) :
    ContDiff ℝ ∞ fun p : ℝ × ℝ => curveVelocity (fun s => R (p.1, s)) p.2 := by
  have h1 : ContDiff ℝ ∞ fun p : ℝ × ℝ => angularVelocityBody (R p) (familyDeriv R (0, 1) p) :=
    contDiff_angularVelocityBody h.contDiff (h.contDiff_familyDeriv (0, 1))
  have heq : (fun p : ℝ × ℝ => curveVelocity (fun s => R (p.1, s)) p.2) =
      fun p => angularVelocityBody (R p) (familyDeriv R (0, 1) p) :=
    funext fun p => by rw [curveVelocity, h.curveDeriv_time p]
  rw [heq]
  exact h1

theorem contDiff_familyVariation (h : IsRotationFamily R) :
    ContDiff ℝ ∞ (familyVariation R) := by
  have h1 : ContDiff ℝ ∞ fun p : ℝ × ℝ => angularVelocityBody (R p) (familyDeriv R (1, 0) p) :=
    contDiff_angularVelocityBody h.contDiff (h.contDiff_familyDeriv (1, 0))
  have heq : familyVariation R =
      fun p => angularVelocityBody (R p) (familyDeriv R (1, 0) p) :=
    funext fun p => by rw [familyVariation, h.curveDeriv_parameter p]
  rw [heq]
  exact h1

/-- A family that does not depend on the parameter at a time has no variation
there. -/
theorem familyVariation_eq_zero {p : ℝ × ℝ} (hconst : ∀ e, R (e, p.2) = R p) :
    familyVariation R p = 0 := by
  have h0 : curveDeriv (fun e => R (e, p.2)) p.1 = 0 := by
    ext a b
    have hfun : (fun e : ℝ => R (e, p.2) a b) = fun _ => R p a b :=
      funext fun e => by rw [hconst e]
    change deriv (fun e : ℝ => R (e, p.2) a b) p.1 = 0
    rw [hfun, deriv_const]
  rw [familyVariation, h0, angularVelocityBody, Matrix.mul_zero]
  ext i
  fin_cases i <;> rfl

end IsRotationFamily

/-! ### The Lagrangian and the action -/

/-- The Lagrangian `Ω · J Ω / 2 − V(Γ)` of a body with a fixed point, in the
variables of the body frame. -/
def bodyLagrangian (J : Matrix (Fin 3) (Fin 3) ℝ) (V : (Fin 3 → ℝ) → ℝ) (w Γ : Fin 3 → ℝ) :
    ℝ :=
  w ⬝ᵥ (J *ᵥ w) / 2 - V Γ

/-- The action of a curve of rotations between two times; `γ` is the vector
fixed in space on which the potential depends. -/
def rotationAction (J : Matrix (Fin 3) (Fin 3) ℝ) (V : (Fin 3 → ℝ) → ℝ) (γ : Fin 3 → ℝ)
    (R : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (t₀ t₁ : ℝ) : ℝ :=
  ∫ t in t₀..t₁, bodyLagrangian J V (curveVelocity R t) ((R t)ᵀ *ᵥ γ)

/-- The gradient of a function on `ℝ³`. -/
def bodyGradient (V : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => fderiv ℝ V x (Pi.single i 1)

theorem fderiv_eq_bodyGradient_dotProduct (V : (Fin 3 → ℝ) → ℝ) (x y : Fin 3 → ℝ) :
    fderiv ℝ V x y = bodyGradient V x ⬝ᵥ y := by
  have hy : y = ∑ i, y i • (Pi.single i (1 : ℝ) : Fin 3 → ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hy]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, dotProduct, bodyGradient]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The gradient of a linear potential `Γ · w`, as for a uniform field. -/
theorem bodyGradient_dotProduct_const (w x : Fin 3 → ℝ) :
    bodyGradient (fun Γ : Fin 3 → ℝ => Γ ⬝ᵥ w) x = w := by
  funext i
  have hlin : HasFDerivAt (fun Γ : Fin 3 → ℝ => Γ ⬝ᵥ w)
      (∑ j, w j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j) x := by
    have h : HasFDerivAt (fun Γ : Fin 3 → ℝ => ∑ j, Γ j * w j)
        (∑ j, w j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j) x :=
      HasFDerivAt.fun_sum fun j _ => (hasFDerivAt_apply j x).mul_const (w j)
    exact h
  rw [bodyGradient, hlin.fderiv]
  simp [Pi.single_apply]

/-- The difference of the two sides of `d(J Ω)/dt = J Ω × Ω + Γ × ∇V(Γ)`. -/
def eulerPoissonResidual (J : Matrix (Fin 3) (Fin 3) ℝ) (V : (Fin 3 → ℝ) → ℝ)
    (γ : Fin 3 → ℝ) (R : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) : Fin 3 → ℝ :=
  deriv (fun s => J *ᵥ curveVelocity R s) t - (J *ᵥ curveVelocity R t) ⨯₃ curveVelocity R t -
    ((R t)ᵀ *ᵥ γ) ⨯₃ bodyGradient V ((R t)ᵀ *ᵥ γ)

variable {J : Matrix (Fin 3) (Fin 3) ℝ} {V : (Fin 3 → ℝ) → ℝ}

/-- The derivative of the Lagrangian along curves of the angular velocity and
of the vector `Γ`. -/
theorem hasDerivAt_bodyLagrangian (hJ : Jᵀ = J) (hV : ContDiff ℝ ∞ V)
    {w Γ : ℝ → Fin 3 → ℝ} {w' Γ' : Fin 3 → ℝ} {ε : ℝ}
    (hw : HasDerivAt w w' ε) (hΓ : HasDerivAt Γ Γ' ε) :
    HasDerivAt (fun e => bodyLagrangian J V (w e) (Γ e))
      ((J *ᵥ w ε) ⬝ᵥ w' - bodyGradient V (Γ ε) ⬝ᵥ Γ') ε := by
  have hJw : HasDerivAt (fun e => J *ᵥ w e) (J *ᵥ w') ε := by
    have h := hasDerivAt_mulVec (R := fun _ => J) (R' := 0)
      (fun a b => hasDerivAt_const ε (J a b)) hw
    rwa [zero_mulVec, zero_add] at h
  have h1 := (hasDerivAt_dotProduct hw hJw).div_const 2
  have h2 : HasDerivAt (fun e => V (Γ e)) (fderiv ℝ V (Γ ε) Γ') ε :=
    ((hV.differentiable (by simp) (Γ ε)).hasFDerivAt).comp_hasDerivAt ε hΓ
  refine (h1.sub h2).congr_deriv ?_
  rw [fderiv_eq_bodyGradient_dotProduct]
  have hsym : w ε ⬝ᵥ (J *ᵥ w') = (J *ᵥ w ε) ⬝ᵥ w' := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hJ]
  rw [hsym, dotProduct_comm w' (J *ᵥ w ε)]
  ring

theorem variation_identity (a a' η η' w Γ G : Fin 3 → ℝ) :
    a' ⬝ᵥ η + a ⬝ᵥ η' =
      a ⬝ᵥ (η' + w ⨯₃ η) - G ⬝ᵥ (Γ ⨯₃ η) - -((a' - a ⨯₃ w - Γ ⨯₃ G) ⬝ᵥ η) := by
  have h1 : a ⬝ᵥ (w ⨯₃ η) = (a ⨯₃ w) ⬝ᵥ η := by
    simp [cross_apply, dotProduct, Fin.sum_univ_three]
    ring
  have h2 : G ⬝ᵥ (Γ ⨯₃ η) = -((Γ ⨯₃ G) ⬝ᵥ η) := by
    simp [cross_apply, dotProduct, Fin.sum_univ_three]
    ring
  rw [dotProduct_add, sub_dotProduct, sub_dotProduct, h1, h2]
  ring

/-- The Lagrangian along a family of rotations, as a function of the parameter
and the time. -/
def familyLagrangian (J : Matrix (Fin 3) (Fin 3) ℝ) (V : (Fin 3 → ℝ) → ℝ) (γ : Fin 3 → ℝ)
    (R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ × ℝ) : ℝ :=
  bodyLagrangian J V (curveVelocity (fun s => R (p.1, s)) p.2) ((R p)ᵀ *ᵥ γ)

/-- The derivative of the Lagrangian in the parameter of a family. -/
def variationDensity (J : Matrix (Fin 3) (Fin 3) ℝ) (V : (Fin 3 → ℝ) → ℝ) (γ : Fin 3 → ℝ)
    (R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ × ℝ) : ℝ :=
  (J *ᵥ curveVelocity (fun s => R (p.1, s)) p.2) ⬝ᵥ
      (deriv (fun s => familyVariation R (p.1, s)) p.2 +
        curveVelocity (fun s => R (p.1, s)) p.2 ⨯₃ familyVariation R p) -
    bodyGradient V ((R p)ᵀ *ᵥ γ) ⬝ᵥ (((R p)ᵀ *ᵥ γ) ⨯₃ familyVariation R p)

/-- The boundary term `J Ω · η` of the first variation. -/
def variationMomentum (J : Matrix (Fin 3) (Fin 3) ℝ) (R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (p : ℝ × ℝ) : ℝ :=
  (J *ᵥ curveVelocity (fun s => R (p.1, s)) p.2) ⬝ᵥ familyVariation R p

section FirstVariation

variable {R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ}

theorem contDiff_familyLagrangian (h : IsRotationFamily R) (hV : ContDiff ℝ ∞ V)
    (γ : Fin 3 → ℝ) : ContDiff ℝ ∞ (familyLagrangian J V γ R) :=
  ((contDiff_dotProduct h.contDiff_curveVelocity
    (contDiff_mulVec J h.contDiff_curveVelocity)).div_const 2).sub
      (hV.comp (contDiff_transpose_mulVec h.contDiff γ))

theorem hasDerivAt_familyLagrangian (h : IsRotationFamily R) (hJ : Jᵀ = J)
    (hV : ContDiff ℝ ∞ V) (γ : Fin 3 → ℝ) (ε t : ℝ) :
    HasDerivAt (fun e => familyLagrangian J V γ R (e, t)) (variationDensity J V γ R (ε, t)) ε :=
  hasDerivAt_bodyLagrangian hJ hV (h.hasDerivAt_curveVelocity_family ε t)
    (h.hasDerivAt_bodyVector_family γ ε t)

theorem contDiff_variationMomentum (h : IsRotationFamily R) :
    ContDiff ℝ ∞ (variationMomentum J R) :=
  contDiff_dotProduct (contDiff_mulVec J h.contDiff_curveVelocity) h.contDiff_familyVariation

theorem hasDerivAt_variationMomentum (h : IsRotationFamily R) (γ : Fin 3 → ℝ) (ε t : ℝ) :
    HasDerivAt (fun s => variationMomentum J R (ε, s))
      (variationDensity J V γ R (ε, t) -
        -(eulerPoissonResidual J V γ (fun s => R (ε, s)) t ⬝ᵥ familyVariation R (ε, t))) t := by
  have hι : ContDiff ℝ ∞ fun s : ℝ => (ε, s) := contDiff_const.prodMk contDiff_id
  have hΩt : ContDiff ℝ ∞ fun s : ℝ => J *ᵥ curveVelocity (fun u => R (ε, u)) s :=
    ContDiff.comp (g := fun p : ℝ × ℝ => J *ᵥ curveVelocity (fun u => R (p.1, u)) p.2)
      (f := fun s : ℝ => (ε, s)) (contDiff_mulVec J h.contDiff_curveVelocity) hι
  have hηt : ContDiff ℝ ∞ fun s : ℝ => familyVariation R (ε, s) :=
    ContDiff.comp (g := familyVariation R) (f := fun s : ℝ => (ε, s))
      h.contDiff_familyVariation hι
  have h1 : HasDerivAt
      (fun s : ℝ => (J *ᵥ curveVelocity (fun u => R (ε, u)) s) ⬝ᵥ familyVariation R (ε, s))
      (deriv (fun s : ℝ => J *ᵥ curveVelocity (fun u => R (ε, u)) s) t ⬝ᵥ
          familyVariation R (ε, t) +
        (J *ᵥ curveVelocity (fun u => R (ε, u)) t) ⬝ᵥ
          deriv (fun s : ℝ => familyVariation R (ε, s)) t) t :=
    hasDerivAt_dotProduct (hΩt.differentiable (by simp) t).hasDerivAt
      (hηt.differentiable (by simp) t).hasDerivAt
  have hval := variation_identity (J *ᵥ curveVelocity (fun u => R (ε, u)) t)
    (deriv (fun s : ℝ => J *ᵥ curveVelocity (fun u => R (ε, u)) s) t)
    (familyVariation R (ε, t)) (deriv (fun s : ℝ => familyVariation R (ε, s)) t)
    (curveVelocity (fun u => R (ε, u)) t) ((R (ε, t))ᵀ *ᵥ γ)
    (bodyGradient V ((R (ε, t))ᵀ *ᵥ γ))
  rw [hval] at h1
  exact h1

/-- The first variation of the action of a family of rotations:
`dS/dε = [J Ω · η] − ∫ (d(J Ω)/dt − J Ω × Ω − Γ × ∇V(Γ)) · η dt`. -/
theorem hasDerivAt_rotationAction (h : IsRotationFamily R) (hJ : Jᵀ = J)
    (hV : ContDiff ℝ ∞ V) (γ : Fin 3 → ℝ) (t₀ t₁ ε : ℝ) :
    HasDerivAt (fun e => rotationAction J V γ (fun s => R (e, s)) t₀ t₁)
      ((J *ᵥ curveVelocity (fun s => R (ε, s)) t₁) ⬝ᵥ familyVariation R (ε, t₁) -
        (J *ᵥ curveVelocity (fun s => R (ε, s)) t₀) ⬝ᵥ familyVariation R (ε, t₀) -
        ∫ t in t₀..t₁, eulerPoissonResidual J V γ (fun s => R (ε, s)) t ⬝ᵥ
          familyVariation R (ε, t)) ε := by
  have hF : ContDiff ℝ 1 (familyLagrangian J V γ R) :=
    (contDiff_familyLagrangian h hV γ).of_le (by simp)
  have hD := fun t => hasDerivAt_familyLagrangian h hJ hV γ ε t
  have hA := Variational.hasDerivAt_intervalIntegral_of_contDiff hF
    (D := fun t => variationDensity J V γ R (ε, t)) (a := t₀) (b := t₁) (fun t _ => hD t)
  have hι : ContDiff ℝ ∞ fun s : ℝ => (ε, s) := contDiff_const.prodMk contDiff_id
  have hP : ContDiff ℝ 1 fun s : ℝ => variationMomentum J R (ε, s) :=
    (ContDiff.comp (g := variationMomentum J R) (f := fun s : ℝ => (ε, s))
      (contDiff_variationMomentum h) hι).of_le (by simp)
  have hDc : ContinuousOn (fun t => variationDensity J V γ R (ε, t)) (uIcc t₀ t₁) :=
    Variational.continuousOn_parameter_derivative (F := familyLagrangian J V γ R)
      (fun t _ => hF.contDiffAt) (fun t _ => hD t)
  have hparts := Variational.integral_eq_boundary_add_residual
    (P := fun s : ℝ => variationMomentum J R (ε, s))
    (D := fun t => variationDensity J V γ R (ε, t))
    (R := fun t => -(eulerPoissonResidual J V γ (fun s => R (ε, s)) t ⬝ᵥ
      familyVariation R (ε, t))) (a := t₀) (b := t₁)
    (fun t _ => hP.contDiffAt) hDc (fun t _ => hasDerivAt_variationMomentum h γ ε t)
  have hfun : (fun e => rotationAction J V γ (fun s => R (e, s)) t₀ t₁) =
      fun e => ∫ t in t₀..t₁, familyLagrangian J V γ R (e, t) := rfl
  rw [hfun]
  refine hA.congr_deriv ?_
  rw [hparts, intervalIntegral.integral_neg]
  simp only [variationMomentum]
  ring

end FirstVariation

/-! ### The Cayley transform -/

/-- The Cayley transform of the skew-symmetric matrix `hat ξ / 2`. -/
def cayley (ξ : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  1 + (1 + ξ ⬝ᵥ ξ / 4)⁻¹ • (hat ξ + (1 / 2 : ℝ) • (hat ξ * hat ξ))

@[simp] theorem cayley_zero : cayley 0 = 1 := by
  have h : hat (0 : Fin 3 → ℝ) = 0 := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [hat]
  simp [cayley, h]

/-- The Cayley transform is orthogonal. -/
theorem cayley_transpose_mul (ξ : Fin 3 → ℝ) : (cayley ξ)ᵀ * cayley ξ = 1 := by
  have hpos : (1 + (ξ 0 * ξ 0 + ξ 1 * ξ 1 + ξ 2 * ξ 2) / 4) ≠ 0 :=
    ne_of_gt (by nlinarith [mul_self_nonneg (ξ 0), mul_self_nonneg (ξ 1), mul_self_nonneg (ξ 2)])
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [cayley, hat, Matrix.mul_apply, Fin.sum_univ_three, dotProduct, Matrix.one_apply]
  all_goals field_simp
  all_goals ring

theorem cayley_smul_apply (x : ℝ) (w : Fin 3 → ℝ) (k b : Fin 3) :
    cayley (x • w) k b = (1 : Matrix (Fin 3) (Fin 3) ℝ) k b +
      (1 + x ^ 2 * (w ⬝ᵥ w) / 4)⁻¹ * (x * hat w k b + x ^ 2 / 2 * (hat w * hat w) k b) := by
  rw [cayley, hat_smul]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_dotProduct, dotProduct_smul]
  ring

/-- The derivative of the Cayley transform at the identity is `ξ ↦ hat ξ`. -/
theorem hasDerivAt_cayley_smul (w : Fin 3 → ℝ) (k b : Fin 3) :
    HasDerivAt (fun x : ℝ => cayley (x • w) k b) (hat w k b) 0 := by
  have hu : HasDerivAt (fun x : ℝ => 1 + x ^ 2 * (w ⬝ᵥ w) / 4)
      (2 * (0 : ℝ) ^ 1 * (w ⬝ᵥ w) / 4) 0 :=
    ((((hasDerivAt_pow 2 (0 : ℝ)).mul_const (w ⬝ᵥ w)).div_const 4).const_add 1)
  have hn : HasDerivAt (fun x : ℝ => x * hat w k b + x ^ 2 / 2 * (hat w * hat w) k b)
      (1 * hat w k b + 2 * (0 : ℝ) ^ 1 / 2 * (hat w * hat w) k b) 0 :=
    ((hasDerivAt_id (0 : ℝ)).mul_const _).add
      (((hasDerivAt_pow 2 (0 : ℝ)).div_const 2).mul_const _)
  have h := ((hu.inv (by simp)).mul hn).const_add ((1 : Matrix (Fin 3) (Fin 3) ℝ) k b)
  have heq : (fun x : ℝ => cayley (x • w) k b) = fun x : ℝ =>
      (1 : Matrix (Fin 3) (Fin 3) ℝ) k b + (1 + x ^ 2 * (w ⬝ᵥ w) / 4)⁻¹ *
        (x * hat w k b + x ^ 2 / 2 * (hat w * hat w) k b) :=
    funext fun x => cayley_smul_apply x w k b
  rw [heq]
  refine h.congr_deriv ?_
  simp

theorem contDiff_hat_apply (k b : Fin 3) : ContDiff ℝ ∞ fun ξ : Fin 3 → ℝ => hat ξ k b := by
  fin_cases k <;> fin_cases b <;> simp [hat] <;> fun_prop

theorem contDiff_cayley_apply (k b : Fin 3) :
    ContDiff ℝ ∞ fun ξ : Fin 3 → ℝ => cayley ξ k b := by
  have hdot : ContDiff ℝ ∞ fun ξ : Fin 3 → ℝ => ξ ⬝ᵥ ξ :=
    contDiff_dotProduct contDiff_id contDiff_id
  have hne : ∀ ξ : Fin 3 → ℝ, 1 + ξ ⬝ᵥ ξ / 4 ≠ 0 := fun ξ => by
    have h0 : 0 ≤ ξ ⬝ᵥ ξ := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    exact ne_of_gt (by linarith)
  have hsq : ContDiff ℝ ∞ fun ξ : Fin 3 → ℝ => (hat ξ * hat ξ) k b := by
    have h : ContDiff ℝ ∞ fun ξ : Fin 3 → ℝ => ∑ j, hat ξ k j * hat ξ j b :=
      ContDiff.sum fun j _ => (contDiff_hat_apply k j).mul (contDiff_hat_apply j b)
    exact h
  have h : ContDiff ℝ ∞ fun ξ : Fin 3 → ℝ => (1 : Matrix (Fin 3) (Fin 3) ℝ) k b +
      (1 + ξ ⬝ᵥ ξ / 4)⁻¹ * (hat ξ k b + 1 / 2 * (hat ξ * hat ξ) k b) :=
    contDiff_const.add (((contDiff_const.add (hdot.div_const 4)).inv hne).mul
      ((contDiff_hat_apply k b).add (contDiff_const.mul hsq)))
  exact h

/-- The derivative at `0` of the curve `e ↦ M · cayley (e w)` is `M ŵ`. -/
theorem curveDeriv_mul_cayley (M : Matrix (Fin 3) (Fin 3) ℝ) (w : Fin 3 → ℝ) :
    curveDeriv (fun e => M * cayley (e • w)) 0 = M * hat w := by
  ext a b
  have h : HasDerivAt (fun e : ℝ => ∑ k, M a k * cayley (e • w) k b)
      (∑ k, M a k * hat w k b) 0 :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_cayley_smul w k b).const_mul (M a k)
  exact h.deriv

section Family

variable {R₀ : ℝ → Matrix (Fin 3) (Fin 3) ℝ}

/-- A smooth curve of rotations multiplied by the Cayley transforms of a
smooth field is a family of rotations. -/
theorem isRotationFamily_mul_cayley (hR₀ : ∀ a b, ContDiff ℝ ∞ fun t => R₀ t a b)
    (horth : ∀ t, (R₀ t)ᵀ * R₀ t = 1) {ξ : ℝ × ℝ → Fin 3 → ℝ} (hξ : ContDiff ℝ ∞ ξ) :
    IsRotationFamily fun p => R₀ p.2 * cayley (ξ p) where
  contDiff a b := by
    have h : ContDiff ℝ ∞ fun p : ℝ × ℝ => ∑ k, R₀ p.2 a k * cayley (ξ p) k b :=
      ContDiff.sum fun k _ => ((hR₀ a k).comp contDiff_snd).mul
        ((contDiff_cayley_apply k b).comp hξ)
    exact h
  orthogonal p := by
    rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (R₀ p.2)ᵀ, horth, Matrix.one_mul,
      cayley_transpose_mul]

/-- The variation field of the family `R₀(t) · cayley (ε η(t))` at `ε = 0` is
`η`. -/
theorem familyVariation_mul_cayley (horth : ∀ t, (R₀ t)ᵀ * R₀ t = 1) (η : ℝ → Fin 3 → ℝ)
    (t : ℝ) :
    familyVariation (fun p : ℝ × ℝ => R₀ p.2 * cayley (p.1 • η p.2)) (0, t) = η t := by
  rw [familyVariation]
  change angularVelocityBody (R₀ t * cayley ((0 : ℝ) • η t))
    (curveDeriv (fun e => R₀ t * cayley (e • η t)) 0) = η t
  rw [curveDeriv_mul_cayley, zero_smul, cayley_zero, Matrix.mul_one, angularVelocityBody,
    ← Matrix.mul_assoc, horth, Matrix.one_mul, vee_hat]

end Family

/-! ### Hamilton's principle -/

/-- The residual of a smooth curve is continuous. -/
theorem continuous_eulerPoissonResidual (hV : ContDiff ℝ ∞ V) (γ : Fin 3 → ℝ)
    {R₀ : ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hR₀ : ∀ a b, ContDiff ℝ ∞ fun t => R₀ t a b) :
    Continuous (eulerPoissonResidual J V γ R₀) := by
  have hΩ : ContDiff ℝ ∞ (curveVelocity R₀) := contDiff_curveVelocity hR₀
  have hJΩ : ContDiff ℝ ∞ fun t => J *ᵥ curveVelocity R₀ t := contDiff_mulVec J hΩ
  have hΓ : ContDiff ℝ ∞ fun t => (R₀ t)ᵀ *ᵥ γ := contDiff_transpose_mulVec hR₀ γ
  have hG : Continuous fun t => bodyGradient V ((R₀ t)ᵀ *ᵥ γ) :=
    continuous_pi fun i =>
      ((hV.continuous_fderiv (by simp)).comp hΓ.continuous).clm_apply continuous_const
  exact ((hJΩ.continuous_deriv (by simp)).sub
    (continuous_cross hJΩ.continuous hΩ.continuous)).sub (continuous_cross hΓ.continuous hG)

/-- The residual vanishes at a time if and only if Euler's equations with the
moment `Γ × ∇V(Γ)` hold there. -/
theorem eulerPoissonResidual_eq_zero_iff (γ : Fin 3 → ℝ)
    {R₀ : ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hR₀ : ∀ a b, ContDiff ℝ ∞ fun t => R₀ t a b) (t : ℝ) :
    eulerPoissonResidual J V γ R₀ t = 0 ↔
      HasDerivAt (fun s => J *ᵥ curveVelocity R₀ s)
        ((J *ᵥ curveVelocity R₀ t) ⨯₃ curveVelocity R₀ t +
          ((R₀ t)ᵀ *ᵥ γ) ⨯₃ bodyGradient V ((R₀ t)ᵀ *ᵥ γ)) t := by
  have hd : DifferentiableAt ℝ (fun s => J *ᵥ curveVelocity R₀ s) t :=
    (contDiff_mulVec J (contDiff_curveVelocity hR₀)).differentiable (by simp) t
  rw [eulerPoissonResidual, sub_sub, sub_eq_zero]
  constructor
  · intro h
    rw [← h]
    exact hd.hasDerivAt
  · intro h
    exact h.deriv

/-- Hamilton's principle on the rotations. A smooth curve of rotations makes
the action stationary among the smooth families of rotations with the same
ends if and only if it solves Euler's equations with the moment `Γ × ∇V(Γ)`
between the ends. -/
theorem stationary_rotationAction_iff {t₀ t₁ : ℝ} (hab : t₀ < t₁) (hJ : Jᵀ = J)
    (hV : ContDiff ℝ ∞ V) (γ : Fin 3 → ℝ) {R₀ : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hR₀ : ∀ a b, ContDiff ℝ ∞ fun t => R₀ t a b) (horth : ∀ t, (R₀ t)ᵀ * R₀ t = 1) :
    (∀ R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ, IsRotationFamily R → (∀ t, R (0, t) = R₀ t) →
        (∀ e, R (e, t₀) = R₀ t₀) → (∀ e, R (e, t₁) = R₀ t₁) →
        HasDerivAt (fun e => rotationAction J V γ (fun s => R (e, s)) t₀ t₁) 0 0) ↔
      ∀ t ∈ Ioo t₀ t₁, eulerPoissonResidual J V γ R₀ t = 0 := by
  constructor
  · intro hs t ht
    funext i
    let v : Fin 3 → ℝ := Pi.single i 1
    let r : ℝ → ℝ := fun s => eulerPoissonResidual J V γ R₀ s ⬝ᵥ v
    have hr : Continuous r := by
      have hc := continuous_eulerPoissonResidual (J := J) hV γ hR₀
      simp only [r, dotProduct]
      fun_prop
    have ha := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hr.continuousOn.locallyIntegrableOn (μ := volume) measurableSet_Ioo)
      (fun g hg _hgK hgI => by
        have hga : g t₀ = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => (lt_irrefl t₀) (hgI h).1)
        have hgb : g t₁ = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => (lt_irrefl t₁) (hgI h).2)
        let η : ℝ → Fin 3 → ℝ := fun s => g s • v
        let R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun p => R₀ p.2 * cayley (p.1 • η p.2)
        have hξ : ContDiff ℝ ∞ fun p : ℝ × ℝ => p.1 • η p.2 :=
          contDiff_fst.smul ((hg.comp contDiff_snd).smul contDiff_const)
        have hfam : IsRotationFamily R := isRotationFamily_mul_cayley hR₀ horth hξ
        have h0 : ∀ s, R (0, s) = R₀ s := fun s => by simp [R]
        have hend₀ : ∀ e, R (e, t₀) = R₀ t₀ := fun e => by simp [R, η, hga]
        have hend₁ : ∀ e, R (e, t₁) = R₀ t₁ := fun e => by simp [R, η, hgb]
        have hfirst := hasDerivAt_rotationAction hfam hJ hV γ t₀ t₁ 0
        have hz := hfirst.unique (hs R hfam h0 hend₀ hend₁)
        have hcurve : (fun s => R (0, s)) = R₀ := funext h0
        have hη : ∀ s, familyVariation R (0, s) = η s :=
          familyVariation_mul_cayley horth η
        have hb₁ : (J *ᵥ curveVelocity R₀ t₁) ⬝ᵥ familyVariation R (0, t₁) = 0 := by
          rw [hη, show η t₁ = 0 by simp [η, hgb], dotProduct_zero]
        have hb₀ : (J *ᵥ curveVelocity R₀ t₀) ⬝ᵥ familyVariation R (0, t₀) = 0 := by
          rw [hη, show η t₀ = 0 by simp [η, hga], dotProduct_zero]
        rw [hcurve, hb₁, hb₀, sub_zero, zero_sub, neg_eq_zero] at hz
        have heq : (∫ s in t₀..t₁, eulerPoissonResidual J V γ R₀ s ⬝ᵥ
            familyVariation R (0, s)) = ∫ s, g s • r s := by
          have hint : ∀ s, eulerPoissonResidual J V γ R₀ s ⬝ᵥ familyVariation R (0, s) =
              g s • r s := fun s => by
            rw [hη, dotProduct_smul]
          simp_rw [hint]
          rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
          exact setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => by
            rw [image_eq_zero_of_notMem_tsupport (fun h => hs (hgI h)), zero_smul]
        exact heq.symm.trans hz)
    have hr0 : r =ᵐ[volume.restrict (Ioo t₀ t₁)] (fun _ => 0) :=
      (ae_restrict_iff' measurableSet_Ioo).2 ha
    have hzero := Measure.eqOn_open_of_ae_eq hr0 isOpen_Ioo hr.continuousOn
      continuous_const.continuousOn ht
    simpa [r, v] using hzero
  · intro hres R hfam h0 hend₀ hend₁
    have hfirst := hasDerivAt_rotationAction hfam hJ hV γ t₀ t₁ 0
    have hcurve : (fun s => R (0, s)) = R₀ := funext h0
    have hη₀ : familyVariation R (0, t₀) = 0 :=
      IsRotationFamily.familyVariation_eq_zero (p := (0, t₀)) fun e => by
        rw [hend₀ e, hend₀ 0]
    have hη₁ : familyVariation R (0, t₁) = 0 :=
      IsRotationFamily.familyVariation_eq_zero (p := (0, t₁)) fun e => by
        rw [hend₁ e, hend₁ 0]
    have hint : (∫ t in t₀..t₁, eulerPoissonResidual J V γ R₀ t ⬝ᵥ
        familyVariation R (0, t)) = 0 := by
      rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
      exact setIntegral_eq_zero_of_forall_eq_zero fun t ht => by
        rw [hres t ht, zero_dotProduct]
    rw [hcurve, hη₀, hη₁, hint] at hfirst
    simpa only [dotProduct_zero, sub_zero] using hfirst

end ProjectAInos.Mechanics.Rigid
