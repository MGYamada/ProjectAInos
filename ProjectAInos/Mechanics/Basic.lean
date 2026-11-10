module

public import ProjectAInos.Variational.Regularity
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.NormNum

/-!
# Paths and Lagrangians on the real time line

The position space can be any real normed space, in particular `Fin n → ℝ`.
A mechanical Lagrangian `L t (q, v)` is interpreted in the shared first-jet
calculus by evaluating a time derivative at `1`.
-/

@[expose] public section

open MeasureTheory Set ContinuousLinearMap
open scoped ContDiff

namespace ProjectAInos.Mechanics

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- A time-dependent first-order mechanical Lagrangian. -/
abbrev Lagrangian (Q : Type*) := ℝ → Q × Q → ℝ

/-- Convert the shared first jet into position and velocity. -/
noncomputable def positionVelocity : Variational.JetFiber ℝ Q →L[ℝ] Q × Q :=
  (fst ℝ Q (ℝ →L[ℝ] Q)).prod
    ((ContinuousLinearMap.apply ℝ Q (1 : ℝ)).comp (snd ℝ Q (ℝ →L[ℝ] Q)))

@[simp] theorem positionVelocity_apply (j : Variational.JetFiber ℝ Q) :
    positionVelocity j = (j.1, j.2 1) := rfl

@[simp] theorem positionVelocity_jet (q : ℝ → Q) (t : ℝ) :
    positionVelocity (Variational.jet q t) = (q t, deriv q t) := rfl

/-- Interpret a mechanical Lagrangian in the common variational layer. -/
noncomputable def toVariational (L : Lagrangian Q) : Variational.Lagrangian ℝ Q :=
  fun t j => L t (positionVelocity j)

/-- The actual action, with the usual oriented interval integral. -/
noncomputable def action (a b : ℝ) (L : Lagrangian Q) (q : ℝ → Q) : ℝ :=
  ∫ t in a..b, L t (q t, deriv q t)

/-- The derivative with respect to position, evaluated along a path. -/
noncomputable def force (L : Lagrangian Q) (q : ℝ → Q) (t : ℝ) : Q →L[ℝ] ℝ :=
  (fderiv ℝ (L t) (q t, deriv q t)).comp (inl ℝ Q Q)

/-- The derivative with respect to velocity, evaluated along a path. -/
noncomputable def momentum (L : Lagrangian Q) (q : ℝ → Q) (t : ℝ) : Q →L[ℝ] ℝ :=
  (fderiv ℝ (L t) (q t, deriv q t)).comp (inr ℝ Q Q)

/-- The Euler–Lagrange residual `∂L/∂q - d/dt (∂L/∂v)`, as a covector. -/
noncomputable def eulerLagrange (L : Lagrangian Q) (q : ℝ → Q) (t : ℝ) : Q →L[ℝ] ℝ :=
  force L q t - deriv (momentum L q) t

/-- Smooth variations vanishing at both endpoints. No compact support is required. -/
structure FixedEndpointVariation (a b : ℝ) (η : ℝ → Q) : Prop where
  smooth : ContDiff ℝ ∞ η
  left : η a = 0
  right : η b = 0

/-- Fixed-endpoint stationarity is a statement about the derivative of the action,
not a definition in terms of the Euler–Lagrange residual. -/
def Stationary (a b : ℝ) (L : Lagrangian Q) (q : ℝ → Q) : Prop :=
  ∀ η : ℝ → Q, FixedEndpointVariation a b η →
    HasDerivAt (fun ε => action a b L (Variational.perturb q η ε)) 0 0

theorem FixedEndpointVariation.perturb_left {a b : ℝ} {η : ℝ → Q}
    (hη : FixedEndpointVariation a b η) (q : ℝ → Q) (ε : ℝ) :
    Variational.perturb q η ε a = q a := by simp [Variational.perturb, hη.left]

theorem FixedEndpointVariation.perturb_right {a b : ℝ} {η : ℝ → Q}
    (hη : FixedEndpointVariation a b η) (q : ℝ → Q) (ε : ℝ) :
    Variational.perturb q η ε b = q b := by simp [Variational.perturb, hη.right]

variable {L : Lagrangian Q} {q η : ℝ → Q}

theorem contDiff_toVariational (hL : ContDiff ℝ 2 (Function.uncurry L)) :
    ContDiff ℝ 2 (Function.uncurry (toVariational L)) := by
  exact hL.comp (contDiff_fst.prodMk
    ((positionVelocity (Q := Q)).contDiff.comp contDiff_snd))

theorem contDiff_positionVelocity (hq : ContDiff ℝ 2 q) :
    ContDiff ℝ 1 (fun t => (q t, deriv q t)) :=
  positionVelocity.contDiff.comp (Variational.contDiff_jet hq)

theorem contDiff_force (hL : ContDiff ℝ 2 (Function.uncurry L)) (hq : ContDiff ℝ 2 q) :
    ContDiff ℝ 1 (force L q) :=
  (hL.fderiv (contDiff_positionVelocity hq) (by norm_num)).clm_comp contDiff_const

theorem contDiff_momentum (hL : ContDiff ℝ 2 (Function.uncurry L)) (hq : ContDiff ℝ 2 q) :
    ContDiff ℝ 1 (momentum L q) :=
  (hL.fderiv (contDiff_positionVelocity hq) (by norm_num)).clm_comp contDiff_const

theorem continuous_eulerLagrange (hL : ContDiff ℝ 2 (Function.uncurry L))
    (hq : ContDiff ℝ 2 q) : Continuous (eulerLagrange L q) :=
  (contDiff_force hL hq).continuous.sub
    (((contDiff_momentum hL hq).fderiv_right (m := 0) (by norm_num)).continuous.clm_apply
      continuous_const)

/-- The shared density is exactly the ordinary mechanical density. -/
@[simp] theorem density_toVariational (L : Lagrangian Q) (q : ℝ → Q) (t : ℝ) :
    Variational.density (toVariational L) q t = L t (q t, deriv q t) := rfl

/-- On an ordered interval the mechanical action is the shared action restricted
by Lebesgue measure. The choice of closed endpoints does not affect the integral. -/
theorem action_eq_variational {a b : ℝ} (hab : a ≤ b) (L : Lagrangian Q) (q : ℝ → Q) :
    action a b L q = Variational.action (volume.restrict (Icc a b)) (toVariational L) q := by
  rw [action, intervalIntegral.integral_of_le hab]
  exact (integral_Icc_eq_integral_Ioc).symm

/-- Decompose the shared fibre differential into position and velocity terms. -/
theorem firstVariationDensity_eq (hL : ContDiff ℝ 2 (Function.uncurry L)) (t : ℝ) :
    Variational.firstVariationDensity (toVariational L) q η t =
      force L q t (η t) + momentum L q t (deriv η t) := by
  have hLt : Differentiable ℝ (L t) :=
    (hL.differentiable (by norm_num)).comp
      ((differentiable_const (c := t)).prodMk differentiable_id)
  have hd := ((hLt _).hasFDerivAt.comp (Variational.jet q t)
    (positionVelocity.hasFDerivAt)).fderiv
  simp only [Function.comp_def] at hd
  change (fderiv ℝ (fun j => L t (positionVelocity j)) (Variational.jet q t))
    (Variational.jet η t) = _
  rw [hd]
  change (fderiv ℝ (L t) (q t, deriv q t)) (η t, deriv η t) = _
  rw [show (η t, deriv η t) = (η t, 0) + (0, deriv η t) by simp, map_add]
  rfl

end ProjectAInos.Mechanics
