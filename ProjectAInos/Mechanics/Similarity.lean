/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Legendre
public import ProjectAInos.Mechanics.TimePrimitive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Mechanical similarity

If the potential energy is homogeneous of degree `k` in the co-ordinates, the
equations of motion permit a family of similar paths (Landau–Lifshitz §10): if
`γ(t)` is a solution, so is `α γ(β t)` with `β = α^{(k − 2)/2}`. The linear
dimensions are multiplied by `α` and the times by `α^{1 − k/2}`.

`TimeFunction.scale β` is the change of the unit of time, `f ↦ f(βt)`. A
potential is an element `u` of the free C-infinity ring on the positions, and
`IsHomogeneous k u` says that `u(αx) = α^k u(x)` for `α > 0`. Its partial
derivatives are homogeneous of degree `k − 1`, by the chain rule for a
substitution.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing

/-- The change of the unit of time, `f ↦ f(βt)`. -/
def TimeFunction.scale (β : ℝ) : SmoothRingHom TimeFunction TimeFunction :=
  SmoothOperation.pullback fun _ =>
    algebraMap ℝ (SmoothOperation 1) β * SmoothOperation.proj 0

theorem TimeFunction.scale_apply (β : ℝ) (f : TimeFunction) (t : ℝ) :
    TimeFunction.scale β f (fun _ => t) = f fun _ => β * t := rfl

/-- The derivative of `f(βt)` is `β f'(βt)`. -/
theorem TimeFunction.timeDerivative_scale (β : ℝ) (f : TimeFunction) :
    timeDerivative (TimeFunction.scale β f) =
      algebraMap ℝ TimeFunction β * TimeFunction.scale β (timeDerivative f) := by
  refine TimeFunction.ext_apply_const fun t => ?_
  rw [TimeFunction.timeDerivative_apply]
  have h : HasDerivAt (fun s : ℝ => TimeFunction.scale β f fun _ => s)
      (timeDerivative f (fun _ => β * t) * (β * 1)) t :=
    (TimeFunction.hasDerivAt_apply_const f (β * t)).comp t ((hasDerivAt_id t).const_mul β)
  rw [h.deriv]
  change _ = β * timeDerivative f (fun _ => β * t)
  ring

variable {ι : Type*}

/-- An observable along a rescaled path. -/
theorem TimeFunction.scale_lift (β : ℝ) (γ : ι → TimeFunction) (f : FreeSmoothRing ι) :
    TimeFunction.scale β (FreeSmoothRing.lift γ f) =
      FreeSmoothRing.lift (fun i => TimeFunction.scale β (γ i)) f := by
  have h : (TimeFunction.scale β).comp (FreeSmoothRing.lift γ) =
      FreeSmoothRing.lift fun i => TimeFunction.scale β (γ i) :=
    FreeSmoothRing.hom_ext fun i => by
      rw [SmoothRingHom.comp_apply, lift_generator, lift_generator]
  exact congrArg (fun φ : SmoothRingHom (FreeSmoothRing ι) TimeFunction => φ f) h

/-- The dilation `xᵢ ↦ α xᵢ` of the positions. -/
def dilate (α : ℝ) : SmoothRingHom (FreeSmoothRing ι) (FreeSmoothRing ι) :=
  FreeSmoothRing.lift fun i => algebraMap ℝ (FreeSmoothRing ι) α * generator i

/-- An observable along a dilated path. -/
theorem lift_dilate (α : ℝ) (γ : ι → TimeFunction) (f : FreeSmoothRing ι) :
    FreeSmoothRing.lift γ (dilate α f) =
      FreeSmoothRing.lift (fun i => algebraMap ℝ TimeFunction α * γ i) f := by
  have h : (FreeSmoothRing.lift γ).comp (dilate α) =
      FreeSmoothRing.lift fun i => algebraMap ℝ TimeFunction α * γ i :=
    FreeSmoothRing.hom_ext fun i => by
      rw [SmoothRingHom.comp_apply, dilate, lift_generator, lift_generator,
        SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, lift_generator]
  exact congrArg (fun φ : SmoothRingHom (FreeSmoothRing ι) TimeFunction => φ f) h

/-- `u` is homogeneous of degree `k`: `u(αx) = α^k u(x)` for `α > 0`. -/
def IsHomogeneous (k : ℝ) (u : FreeSmoothRing ι) : Prop :=
  ∀ α : ℝ, 0 < α → dilate α u = algebraMap ℝ (FreeSmoothRing ι) (α ^ k) * u

variable [DecidableEq ι] [Fintype ι]

/-- The partial derivatives of a function homogeneous of degree `k` are
homogeneous of degree `k − 1`. -/
theorem IsHomogeneous.dilate_partialDerivation {k : ℝ} {u : FreeSmoothRing ι}
    (hu : IsHomogeneous k u) {α : ℝ} (hα : 0 < α) (j : ι) :
    dilate α (partialDerivation j u) =
      algebraMap ℝ (FreeSmoothRing ι) (α ^ (k - 1)) * partialDerivation j u := by
  have h := congrArg (partialDerivation j) (hu α hα)
  rw [dilate, derivation_lift_mul, Finset.sum_eq_single j,
    SmoothDerivation.map_algebraMap_mul, SmoothDerivation.map_algebraMap_mul,
    partialDerivation_generator_self, smul_eq_mul, smul_eq_mul, mul_one] at h
  · have hinv : algebraMap ℝ (FreeSmoothRing ι) α⁻¹ * algebraMap ℝ (FreeSmoothRing ι) α = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hα.ne', map_one]
    have hpow : algebraMap ℝ (FreeSmoothRing ι) (α ^ (k - 1)) =
        algebraMap ℝ (FreeSmoothRing ι) α⁻¹ * algebraMap ℝ (FreeSmoothRing ι) (α ^ k) := by
      rw [← map_mul, Real.rpow_sub_one hα.ne', inv_mul_eq_div]
    rw [dilate, hpow]
    linear_combination algebraMap ℝ (FreeSmoothRing ι) α⁻¹ * h -
      FreeSmoothRing.lift (fun i => algebraMap ℝ (FreeSmoothRing ι) α * generator i)
        (partialDerivation j u) * hinv
  · intro a _ haj
    rw [SmoothDerivation.map_algebraMap_mul, partialDerivation_generator_of_ne haj, smul_zero,
      mul_zero]
  · intro h'
    exact absurd (Finset.mem_univ j) h'

/-- Mechanical similarity (Landau–Lifshitz (10.1), (10.2)): for a potential
homogeneous of degree `k`, if `γ(t)` is a solution, so is `α γ(βt)` with
`β = α^{(k − 2)/2}`. -/
theorem StandardJet.IsSolution.similar {m : ι → ℝ} {k : ℝ} {u : FreeSmoothRing ι}
    (hu : IsHomogeneous k u) {γ : ι → TimeFunction}
    (h : StandardJet.IsSolution
      ((StandardJet.jetRing ι).naturalLagrangian m (positionsToJet u)) γ) {α : ℝ}
    (hα : 0 < α) :
    StandardJet.IsSolution ((StandardJet.jetRing ι).naturalLagrangian m (positionsToJet u))
      fun i => algebraMap ℝ TimeFunction α * TimeFunction.scale (α ^ ((k - 2) / 2)) (γ i) := by
  rw [isSolution_natural_iff] at h ⊢
  intro i
  have hreal : α * (α ^ ((k - 2) / 2) * α ^ ((k - 2) / 2)) = α ^ (k - 1) := by
    rw [← Real.rpow_add hα, show (k - 2) / 2 + (k - 2) / 2 = k - 2 by ring,
      show k - 1 = k - 2 + 1 by ring, Real.rpow_add_one hα.ne']
    ring
  have hβ : algebraMap ℝ TimeFunction α *
      (algebraMap ℝ TimeFunction (α ^ ((k - 2) / 2)) *
        algebraMap ℝ TimeFunction (α ^ ((k - 2) / 2))) =
      algebraMap ℝ TimeFunction (α ^ (k - 1)) := by
    rw [← map_mul, ← map_mul, hreal]
  have hs : algebraMap ℝ TimeFunction (m i) * TimeFunction.scale (α ^ ((k - 2) / 2))
        (timeDerivative (timeDerivative (γ i))) =
      -FreeSmoothRing.lift (fun j => TimeFunction.scale (α ^ ((k - 2) / 2)) (γ j))
        (partialDerivation i u) := by
    have h' := congrArg (fun f => TimeFunction.scale (α ^ ((k - 2) / 2)) f) (h i)
    simp only [SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, SmoothRingHom.map_neg,
      TimeFunction.scale_lift] at h'
    exact h'
  have hr : FreeSmoothRing.lift
        (fun j => algebraMap ℝ TimeFunction α * TimeFunction.scale (α ^ ((k - 2) / 2)) (γ j))
        (partialDerivation i u) =
      algebraMap ℝ TimeFunction (α ^ (k - 1)) *
        FreeSmoothRing.lift (fun j => TimeFunction.scale (α ^ ((k - 2) / 2)) (γ j))
          (partialDerivation i u) := by
    rw [← lift_dilate, hu.dilate_partialDerivation hα, SmoothRingHom.map_mul,
      SmoothRingHom.map_algebraMap]
  rw [hr, SmoothDerivation.map_algebraMap_mul, TimeFunction.timeDerivative_scale, smul_eq_mul,
    SmoothDerivation.map_algebraMap_mul, SmoothDerivation.map_algebraMap_mul,
    TimeFunction.timeDerivative_scale, smul_eq_mul, smul_eq_mul]
  linear_combination (algebraMap ℝ TimeFunction α *
      (algebraMap ℝ TimeFunction (α ^ ((k - 2) / 2)) *
        algebraMap ℝ TimeFunction (α ^ ((k - 2) / 2)))) * hs -
    FreeSmoothRing.lift (fun j => TimeFunction.scale (α ^ ((k - 2) / 2)) (γ j))
      (partialDerivation i u) * hβ

/-- The times of similar paths (Landau–Lifshitz (10.2)): if `γ` has the period
`T`, the similar path `α γ(βt)` has the period `T/β`, that is,
`α^{1 − k/2} T`. -/
theorem similar_apply_add_period {γ : TimeFunction} {T : ℝ}
    (hT : ∀ t : ℝ, γ (fun _ => t + T) = γ fun _ => t) (α : ℝ) {β : ℝ} (hβ : β ≠ 0) (t : ℝ) :
    (algebraMap ℝ TimeFunction α * TimeFunction.scale β γ) (fun _ => t + T / β) =
      (algebraMap ℝ TimeFunction α * TimeFunction.scale β γ) fun _ => t := by
  have e : β * (t + T / β) = β * t + T := by
    field_simp
  change α * γ (fun _ => β * (t + T / β)) = α * γ fun _ => β * t
  rw [e, hT]

end ProjectAInos.Mechanics
