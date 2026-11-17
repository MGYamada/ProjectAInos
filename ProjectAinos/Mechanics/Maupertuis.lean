/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.OpenDomain
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Maupertuis' principle

Landau–Lifshitz §44 for a Lagrangian `T(q, q̇) − U(q)` on a normed space, with
a kinetic energy `T` and a potential energy `U`, at a fixed energy `E` in the
region `U < E`.

* `jacobiLength T U E`: the Lagrangian `2 √((E − U(q)) T(q, q̇))`. For
  `T = g(q̇, q̇)/2` it is `√(2 (E − U) g(q̇, q̇))`, the length in the Jacobi
  metric `2 (E − U) g`, and its action is the abbreviated action (44.10).
* `fderiv_jacobiLength_eq`: at a point of the energy surface `T + U = E` with
  `U < E` the derivative of `jacobiLength` is the derivative of `T − U`.
* `eulerLagrange_jacobiLength_eq`: along a curve of the energy `E` the two
  Lagrangians have the same Euler–Lagrange expression.
* `stationary_jacobiLength_iff`: Maupertuis' principle. A curve of the energy
  `E` in the region `U < E` makes the abbreviated action stationary for all
  variations with fixed ends if and only if it satisfies the equations of
  motion.
* `action_jacobiLength_eq_integral_momentum`: along a curve of the energy `E`
  the abbreviated action is `∫ p q̇ dt`, if `T` is homogeneous of degree two in
  the velocity.
-/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory
open ContinuousLinearMap (inl inr fst snd)
open scoped Topology ContDiff

namespace ProjectAinos.Mechanics.Maupertuis

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  {T : Q × Q → ℝ} {U : Q → ℝ} {E : ℝ}

/-- The Lagrangian `T(q, q̇) − U(q)`. -/
def naturalLagrangian (T : Q × Q → ℝ) (U : Q → ℝ) : Lagrangian Q := fun _ z => T z - U z.1

/-- `(E − U(q)) T(q, q̇)`. -/
def radicand (T : Q × Q → ℝ) (U : Q → ℝ) (E : ℝ) (z : Q × Q) : ℝ := (E - U z.1) * T z

/-- The integrand `2 √((E − U(q)) T(q, q̇))` of the abbreviated action at the
energy `E`: the length in the Jacobi metric. -/
def jacobiLength (T : Q × Q → ℝ) (U : Q → ℝ) (E : ℝ) : Lagrangian Q :=
  fun _ z => 2 * √(radicand T U E z)

/-- `2 (E − U(q)) T(q, q̇)`: half of the square of the velocity in the Jacobi
metric. -/
def jacobiEnergy (T : Q × Q → ℝ) (U : Q → ℝ) (E : ℝ) : Lagrangian Q :=
  fun _ z => 2 * radicand T U E z

theorem contDiff_radicand (hT : ContDiff ℝ 2 T) (hU : ContDiff ℝ 2 U) :
    ContDiff ℝ 2 (radicand T U E) :=
  (contDiff_const.sub (hU.comp contDiff_fst)).mul hT

section Derivative

variable {z : Q × Q} {T' : Q × Q →L[ℝ] ℝ} {U' : Q →L[ℝ] ℝ}

theorem hasFDerivAt_radicand (hT : HasFDerivAt T T' z) (hU : HasFDerivAt U U' z.1) :
    HasFDerivAt (radicand T U E) ((E - U z.1) • T' - T z • U'.comp (fst ℝ Q Q)) z := by
  have h1 : HasFDerivAt (fun y : Q × Q => U y.1) (U'.comp (fst ℝ Q Q)) z :=
    hU.comp z hasFDerivAt_fst
  have h2 : HasFDerivAt (fun y : Q × Q => E - U y.1) (-(U'.comp (fst ℝ Q Q))) z :=
    h1.const_sub E
  have h3 : HasFDerivAt (fun y : Q × Q => (E - U y.1) * T y)
      ((E - U z.1) • T' + T z • -(U'.comp (fst ℝ Q Q))) z := h2.mul hT
  refine h3.congr_fderiv ?_
  rw [smul_neg]
  exact (sub_eq_add_neg _ _).symm

theorem hasFDerivAt_jacobiLength (hT : HasFDerivAt T T' z) (hU : HasFDerivAt U U' z.1)
    (hpos : 0 < radicand T U E z) (t : ℝ) :
    HasFDerivAt (jacobiLength T U E t)
      ((1 / √(radicand T U E z)) • ((E - U z.1) • T' - T z • U'.comp (fst ℝ Q Q))) z := by
  have h1 := (hasFDerivAt_radicand (E := E) hT hU).sqrt hpos.ne'
  have h2 : HasFDerivAt (fun y : Q × Q => 2 * √(radicand T U E y))
      ((2 : ℝ) • (1 / (2 * √(radicand T U E z))) •
        ((E - U z.1) • T' - T z • U'.comp (fst ℝ Q Q))) z := h1.const_mul 2
  refine h2.congr_fderiv ?_
  have hs : 0 < √(radicand T U E z) := Real.sqrt_pos.mpr hpos
  rw [smul_smul]
  congr 1
  field_simp

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
/-- On the energy surface `(E − U) T = (E − U)²`. -/
theorem radicand_eq_sq (hE : T z + U z.1 = E) : radicand T U E z = (E - U z.1) ^ 2 := by
  rw [radicand, ← hE]
  ring

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem radicand_pos (hE : T z + U z.1 = E) (hlt : U z.1 < E) : 0 < radicand T U E z := by
  have hpos : 0 < E - U z.1 := sub_pos.mpr hlt
  rw [radicand_eq_sq hE]
  positivity

/-- On the energy surface the derivative of the Jacobi length is the
derivative of `T − U`. -/
theorem hasFDerivAt_jacobiLength_shell (hT : HasFDerivAt T T' z) (hU : HasFDerivAt U U' z.1)
    (hE : T z + U z.1 = E) (hlt : U z.1 < E) (t : ℝ) :
    HasFDerivAt (jacobiLength T U E t) (T' - U'.comp (fst ℝ Q Q)) z := by
  have hpos : 0 < E - U z.1 := sub_pos.mpr hlt
  have h := hasFDerivAt_jacobiLength hT hU (radicand_pos hE hlt) t
  refine h.congr_fderiv ?_
  have hTz : T z = E - U z.1 := by linarith
  have e : 1 / (E - U z.1) * (E - U z.1) = 1 := by field_simp
  rw [radicand_eq_sq hE, Real.sqrt_sq hpos.le, hTz,
    ← smul_sub (E - U z.1) T' (U'.comp (fst ℝ Q Q)), smul_smul, e, one_smul]

theorem hasFDerivAt_naturalLagrangian (hT : HasFDerivAt T T' z) (hU : HasFDerivAt U U' z.1)
    (t : ℝ) : HasFDerivAt (naturalLagrangian T U t) (T' - U'.comp (fst ℝ Q Q)) z :=
  hT.sub (hU.comp z hasFDerivAt_fst)

/-- At a point of the energy surface in the region `U < E` the Jacobi length
and the Lagrangian `T − U` have the same derivative. -/
theorem fderiv_jacobiLength_eq (hT : DifferentiableAt ℝ T z) (hU : DifferentiableAt ℝ U z.1)
    (hE : T z + U z.1 = E) (hlt : U z.1 < E) (t : ℝ) :
    fderiv ℝ (jacobiLength T U E t) z = fderiv ℝ (naturalLagrangian T U t) z :=
  (hasFDerivAt_jacobiLength_shell hT.hasFDerivAt hU.hasFDerivAt hE hlt t).fderiv.trans
    (hasFDerivAt_naturalLagrangian hT.hasFDerivAt hU.hasFDerivAt t).fderiv.symm

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
/-- On the energy surface the Jacobi length is twice the kinetic energy. -/
theorem jacobiLength_eq_two_mul (hE : T z + U z.1 = E) (hlt : U z.1 < E) (t : ℝ) :
    jacobiLength T U E t z = 2 * T z := by
  have hpos : 0 < E - U z.1 := sub_pos.mpr hlt
  rw [jacobiLength, radicand_eq_sq hE, Real.sqrt_sq hpos.le]
  linarith

end Derivative

section Curve

variable {q : ℝ → Q} {a b t : ℝ}

/-- Along a curve of the energy `E` in the region `U < E` the Jacobi length and
the Lagrangian `T − U` have the same Euler–Lagrange expression. -/
theorem eulerLagrange_jacobiLength_eq (hT : Differentiable ℝ T) (hU : Differentiable ℝ U)
    (hE : ∀ᶠ s in 𝓝 t, T (q s, deriv q s) + U (q s) = E ∧ U (q s) < E) :
    eulerLagrange (jacobiLength T U E) q t = eulerLagrange (naturalLagrangian T U) q t := by
  have hfd : ∀ᶠ s in 𝓝 t, fderiv ℝ (jacobiLength T U E s) (q s, deriv q s) =
      fderiv ℝ (naturalLagrangian T U s) (q s, deriv q s) := by
    filter_upwards [hE] with s hs
    exact fderiv_jacobiLength_eq (hT _) (hU _) hs.1 hs.2 s
  have hm : momentum (jacobiLength T U E) q =ᶠ[𝓝 t] momentum (naturalLagrangian T U) q := by
    filter_upwards [hfd] with s hs
    simp only [momentum, hs]
  simp only [eulerLagrange, force, hfd.self_of_nhds, hm.deriv_eq]

/-- Along a curve of the energy `E` the abbreviated action is the integral of
twice the kinetic energy. -/
theorem action_jacobiLength
    (hE : ∀ t ∈ uIcc a b, T (q t, deriv q t) + U (q t) = E ∧ U (q t) < E) :
    action a b (jacobiLength T U E) q = ∫ t in a..b, 2 * T (q t, deriv q t) :=
  intervalIntegral.integral_congr fun t ht =>
    jacobiLength_eq_two_mul (z := (q t, deriv q t)) (hE t ht).1 (hE t ht).2 t

/-- **Maupertuis' principle.** A curve of the energy `E` in the region `U < E`
makes the abbreviated action `∫ 2 √((E − U) T) dt` stationary for all variations
with fixed ends if and only if it satisfies the equations of motion of
`T − U`. -/
theorem stationary_jacobiLength_iff [FiniteDimensional ℝ Q] (hab : a < b)
    (hT : ContDiff ℝ 2 T) (hU : ContDiff ℝ 2 U) (hq : ContDiff ℝ 2 q)
    (hE : ∀ t ∈ Icc a b, T (q t, deriv q t) + U (q t) = E ∧ U (q t) < E) :
    Stationary a b (jacobiLength T U E) q ↔
      ∀ t ∈ Ioo a b, eulerLagrange (naturalLagrangian T U) q t = 0 := by
  have hr : ContDiff ℝ 2 fun x : ℝ × (Q × Q) => radicand T U E x.2 :=
    (contDiff_radicand hT hU).comp contDiff_snd
  have hopen : IsOpen {x : ℝ × (Q × Q) | 0 < radicand T U E x.2} :=
    isOpen_lt continuous_const hr.continuous
  have hL : ContDiffOn ℝ 2 (Function.uncurry (jacobiLength T U E))
      {x : ℝ × (Q × Q) | 0 < radicand T U E x.2} := by
    have e : Function.uncurry (jacobiLength T U E) =
        fun x : ℝ × (Q × Q) => 2 * √(radicand T U E x.2) := rfl
    rw [e]
    exact contDiffOn_const.mul (hr.contDiffOn.sqrt fun x hx => ne_of_gt hx)
  have hqU : ∀ t ∈ Icc a b, pathJet q t ∈ {x : ℝ × (Q × Q) | 0 < radicand T U E x.2} :=
    fun t ht => radicand_pos (z := (q t, deriv q t)) (hE t ht).1 (hE t ht).2
  rw [stationary_iff_eulerLagrange_on hab hq hopen hL hqU]
  refine forall₂_congr fun t ht => ?_
  rw [eulerLagrange_jacobiLength_eq (hT.differentiable (by norm_num))
    (hU.differentiable (by norm_num))]
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact hE s ⟨hs.1.le, hs.2.le⟩

end Curve

/-! ### The abbreviated action as `∫ p dq` -/

/-- The kinetic energy is homogeneous of degree two in the velocity. -/
def IsHomogeneousTwo (T : Q × Q → ℝ) : Prop :=
  ∀ (q w : Q) (c : ℝ), T (q, c • w) = c ^ 2 * T (q, w)

/-- Euler's relation: `(∂T/∂q̇) q̇ = 2T`. -/
theorem IsHomogeneousTwo.fderiv_velocity (hT : IsHomogeneousTwo T) {q w : Q}
    (hd : DifferentiableAt ℝ T (q, w)) : fderiv ℝ T (q, w) (0, w) = 2 * T (q, w) := by
  have hp : HasDerivAt (fun c : ℝ => ((q, c • w) : Q × Q)) ((0 : Q), (1 : ℝ) • w) 1 :=
    (hasDerivAt_const (1 : ℝ) q).prodMk ((hasDerivAt_id (1 : ℝ)).smul_const w)
  have hd' : HasFDerivAt T (fderiv ℝ T (q, w)) (q, (1 : ℝ) • w) := by
    rw [one_smul]
    exact hd.hasFDerivAt
  have h1 : HasDerivAt (fun c : ℝ => T (q, c • w)) (fderiv ℝ T (q, w) (0, (1 : ℝ) • w)) 1 :=
    HasFDerivAt.comp_hasDerivAt (1 : ℝ) hd' hp
  have h2 : HasDerivAt (fun c : ℝ => c ^ 2 * T (q, w)) (2 * 1 * T (q, w)) 1 := by
    have h3 : HasDerivAt (fun c : ℝ => c ^ 2) (2 * 1) 1 := by
      simpa using hasDerivAt_pow 2 (1 : ℝ)
    exact h3.mul_const _
  have e : (fun c : ℝ => T (q, c • w)) = fun c : ℝ => c ^ 2 * T (q, w) :=
    funext fun c => hT q w c
  rw [e] at h1
  have h4 := h1.unique h2
  rw [one_smul] at h4
  rw [h4]
  ring

section Momentum

variable {q : ℝ → Q} {a b : ℝ}

theorem momentum_naturalLagrangian_apply (hT : IsHomogeneousTwo T) (hd : Differentiable ℝ T)
    (hU : Differentiable ℝ U) (t : ℝ) :
    momentum (naturalLagrangian T U) q t (deriv q t) = 2 * T (q t, deriv q t) := by
  have h := hasFDerivAt_naturalLagrangian (z := (q t, deriv q t)) (hd _).hasFDerivAt
    (hU _).hasFDerivAt t
  rw [momentum, h.fderiv]
  change fderiv ℝ T (q t, deriv q t) (0, deriv q t) - fderiv ℝ U (q t) 0 =
    2 * T (q t, deriv q t)
  rw [map_zero, sub_zero]
  exact hT.fderiv_velocity (hd _)

/-- Along a curve of the energy `E` the abbreviated action is `∫ p q̇ dt`. -/
theorem action_jacobiLength_eq_integral_momentum (hT : IsHomogeneousTwo T)
    (hd : Differentiable ℝ T) (hU : Differentiable ℝ U)
    (hE : ∀ t ∈ uIcc a b, T (q t, deriv q t) + U (q t) = E ∧ U (q t) < E) :
    action a b (jacobiLength T U E) q =
      ∫ t in a..b, momentum (naturalLagrangian T U) q t (deriv q t) := by
  rw [action_jacobiLength hE]
  exact intervalIntegral.integral_congr fun t _ =>
    (momentum_naturalLagrangian_apply hT hd hU t).symm

end Momentum

end ProjectAinos.Mechanics.Maupertuis
