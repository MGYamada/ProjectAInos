/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.EulerLagrange
public import ProjectAInos.Mechanics.Jet.Prolongation
public import ProjectAInos.Mechanics.SmoothLagrangian

/-!
# Solutions in the jet ring are the stationary paths of the action

A smooth function `f` of time, position and velocity defines both an element
`firstOrder f` of the standard jet ring and the real analytic Lagrangian
`ofSmoothOperation f`. For a smooth path `γ` the two descriptions agree:

* the prolongation of `firstOrder f`, evaluated at time `t`, is the value of the
  Lagrangian on the path;
* the prolongation of the Euler operator `Eᵢ(firstOrder f)`, evaluated at time
  `t`, is the Euler–Lagrange residual of the path in the direction of the
  `i`-th coordinate.

Hence `γ` is a solution in the sense of the jet ring exactly when its
Euler–Lagrange residual vanishes at all times, and exactly when the action is
stationary under fixed-endpoint variations on every interval. Conservation laws
proved as ideal membership therefore hold along the stationary paths of the
action.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.StandardJet

open SmoothAlgebra SmoothRing SmoothOperation Set
open scoped ContDiff

variable {n : ℕ}

/-- The index of the `i`-th position among the arguments `(t, q, v)`. -/
def positionIndex (i : Fin n) : Fin (n + n + 1) := (Fin.castAdd n i).succ

/-- The index of the `i`-th velocity among the arguments `(t, q, v)`. -/
def velocityIndex (i : Fin n) : Fin (n + n + 1) := (Fin.natAdd n i).succ

/-- Case analysis on an argument index: time, a position or a velocity. -/
theorem index_cases {motive : Fin (n + n + 1) → Prop} (zero : motive 0)
    (position : ∀ a, motive (positionIndex a)) (velocity : ∀ a, motive (velocityIndex a))
    (j : Fin (n + n + 1)) : motive j := by
  induction j using Fin.cases with
  | zero => exact zero
  | succ j =>
    induction j using Fin.addCases with
    | left a => exact position a
    | right a => exact velocity a

theorem positionIndex_injective : Function.Injective (positionIndex (n := n)) :=
  fun _ _ h => Fin.castAdd_injective n n (Fin.succ_injective _ h)

theorem velocityIndex_injective : Function.Injective (velocityIndex (n := n)) :=
  fun _ _ h => Fin.natAdd_injective n n (Fin.succ_injective _ h)

theorem positionIndex_ne_velocityIndex (a b : Fin n) : positionIndex a ≠ velocityIndex b := by
  intro h
  have hv := congrArg Fin.val h
  simp only [positionIndex, velocityIndex, Fin.val_succ, Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

/-- The jet coordinates `(t, qᵢ, q̇ᵢ)` of a first-order Lagrangian. -/
def firstOrderCoordinates (n : ℕ) : Fin (n + n + 1) → StandardJet (Fin n) :=
  Fin.cons (time (Fin n))
    (Fin.append (fun i => (jetRing (Fin n)).q i 0) (fun i => (jetRing (Fin n)).q i 1))

@[simp] theorem firstOrderCoordinates_zero : firstOrderCoordinates n 0 = time (Fin n) := rfl

@[simp] theorem firstOrderCoordinates_position (a : Fin n) :
    firstOrderCoordinates n (positionIndex a) = (jetRing (Fin n)).q a 0 := by
  rw [firstOrderCoordinates, positionIndex, Fin.cons_succ, Fin.append_left]

@[simp] theorem firstOrderCoordinates_velocity (a : Fin n) :
    firstOrderCoordinates n (velocityIndex a) = (jetRing (Fin n)).q a 1 := by
  rw [firstOrderCoordinates, velocityIndex, Fin.cons_succ, Fin.append_right]

/-- The element of the standard jet ring defined by a smooth function of time,
position and velocity. -/
def firstOrder (f : SmoothOperation (n + n + 1)) : StandardJet (Fin n) :=
  op f (firstOrderCoordinates n)

theorem orderLE_firstOrder (f : SmoothOperation (n + n + 1)) :
    (jetRing (Fin n)).OrderLE (firstOrder f) 1 := by
  refine JetRing.OrderLE.op (fun j => ?_) f
  induction j using index_cases with
  | zero => exact fun i k _ => d_time i k
  | position a =>
    rw [firstOrderCoordinates_position]
    exact (JetRing.orderLE_q a 0).mono (by omega)
  | velocity a =>
    rw [firstOrderCoordinates_velocity]
    exact JetRing.orderLE_q a 1

/-- `∂L/∂qᵢ` of a first-order Lagrangian. -/
theorem d_zero_firstOrder (f : SmoothOperation (n + n + 1)) (i : Fin n) :
    (jetRing (Fin n)).d i 0 (firstOrder f) =
      op (partialDeriv (positionIndex i) f) (firstOrderCoordinates n) := by
  rw [firstOrder, SmoothDerivation.chain, Finset.sum_eq_single (positionIndex i)]
  · rw [firstOrderCoordinates_position, (jetRing (Fin n)).d_q_self, smul_eq_mul, mul_one]
  · intro j _ hj
    have h0 : (jetRing (Fin n)).d i 0 (firstOrderCoordinates n j) = 0 := by
      induction j using index_cases with
      | zero => exact d_time i 0
      | position a =>
        rw [firstOrderCoordinates_position]
        exact (jetRing (Fin n)).d_q_ne a 0 i 0 fun h => hj (by rw [(Prod.mk.inj h).1])
      | velocity a =>
        rw [firstOrderCoordinates_velocity]
        exact (jetRing (Fin n)).d_q_ne a 1 i 0 fun h => absurd (Prod.mk.inj h).2 (by omega)
    rw [h0, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `∂L/∂q̇ᵢ` of a first-order Lagrangian. -/
theorem d_one_firstOrder (f : SmoothOperation (n + n + 1)) (i : Fin n) :
    (jetRing (Fin n)).d i 1 (firstOrder f) =
      op (partialDeriv (velocityIndex i) f) (firstOrderCoordinates n) := by
  rw [firstOrder, SmoothDerivation.chain, Finset.sum_eq_single (velocityIndex i)]
  · rw [firstOrderCoordinates_velocity, (jetRing (Fin n)).d_q_self, smul_eq_mul, mul_one]
  · intro j _ hj
    have h0 : (jetRing (Fin n)).d i 1 (firstOrderCoordinates n j) = 0 := by
      induction j using index_cases with
      | zero => exact d_time i 1
      | position a =>
        rw [firstOrderCoordinates_position]
        exact (jetRing (Fin n)).d_q_ne a 0 i 1 fun h => absurd (Prod.mk.inj h).2 (by omega)
      | velocity a =>
        rw [firstOrderCoordinates_velocity]
        exact (jetRing (Fin n)).d_q_ne a 1 i 1 fun h => hj (by rw [(Prod.mk.inj h).1])
    rw [h0, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The Euler operator of a first-order Lagrangian. -/
theorem euler_firstOrder (f : SmoothOperation (n + n + 1)) (i : Fin n) :
    (jetRing (Fin n)).euler i (firstOrder f) =
      op (partialDeriv (positionIndex i) f) (firstOrderCoordinates n) -
        (jetRing (Fin n)).totalDeriv
          (op (partialDeriv (velocityIndex i) f) (firstOrderCoordinates n)) := by
  rw [JetRing.euler_of_orderLE_one (orderLE_firstOrder f), JetRing.momentum, d_zero_firstOrder,
    d_one_firstOrder]

/-- `∂L/∂t` of a first-order Lagrangian. -/
theorem dt_firstOrder (f : SmoothOperation (n + n + 1)) :
    (jetRing (Fin n)).dt (firstOrder f) = op (partialDeriv 0 f) (firstOrderCoordinates n) := by
  rw [firstOrder, SmoothDerivation.chain, Finset.sum_eq_single 0]
  · rw [firstOrderCoordinates_zero, dt_time, smul_eq_mul, mul_one]
  · intro j _ hj
    have h0 : (jetRing (Fin n)).dt (firstOrderCoordinates n j) = 0 := by
      induction j using index_cases with
      | zero => exact absurd rfl hj
      | position a =>
        rw [firstOrderCoordinates_position]
        exact (jetRing (Fin n)).dt_q a 0
      | velocity a =>
        rw [firstOrderCoordinates_velocity]
        exact (jetRing (Fin n)).dt_q a 1
    rw [h0, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A Lagrangian that does not depend on time has `∂L/∂t = 0` in the jet ring. -/
theorem dt_firstOrder_eq_zero {f : SmoothOperation (n + n + 1)} (hf : partialDeriv 0 f = 0) :
    (jetRing (Fin n)).dt (firstOrder f) = 0 := by
  rw [dt_firstOrder, hf, op_zero]

/-! ### The real jet of a path -/

/-- The real path of a family of smooth functions of time. -/
def realPath (γ : Fin n → TimeFunction) : ℝ → Fin n → ℝ := fun t i => γ i (fun _ => t)

theorem contDiff_realPath (γ : Fin n → TimeFunction) : ContDiff ℝ ∞ (realPath γ) :=
  contDiff_pi.mpr fun i => (γ i).contDiff_apply_const

theorem deriv_realPath (γ : Fin n → TimeFunction) (t : ℝ) :
    deriv (realPath γ) t = fun i => timeDerivative (γ i) (fun _ => t) := by
  have h : deriv (realPath γ) t = fun i => deriv (fun s => realPath γ s i) t :=
    deriv_pi fun i => ((γ i).contDiff_apply_const.differentiable (by simp)).differentiableAt
  rw [h]
  funext i
  exact (TimeFunction.timeDerivative_apply (γ i) t).symm

/-- The real jet `(t, γ(t), γ̇(t))` of a path. -/
def realJet (γ : Fin n → TimeFunction) (t : ℝ) : Fin (n + n + 1) → ℝ :=
  Fin.cons t (Fin.append (realPath γ t) (deriv (realPath γ) t))

theorem prolongation_firstOrderCoordinates_apply (γ : Fin n → TimeFunction) (t : ℝ)
    (j : Fin (n + n + 1)) :
    prolongation γ (firstOrderCoordinates n j) (fun _ => t) = realJet γ t j := by
  induction j using index_cases with
  | zero =>
    rw [firstOrderCoordinates_zero, prolongation_time]
    rfl
  | position a =>
    rw [firstOrderCoordinates_position, prolongation_q, realJet, positionIndex, Fin.cons_succ,
      Fin.append_left]
    rfl
  | velocity a =>
    rw [firstOrderCoordinates_velocity, prolongation_q, realJet, velocityIndex, Fin.cons_succ,
      Fin.append_right, deriv_realPath]
    rfl

/-- The prolongation of a function of the first-order jet coordinates, evaluated
at time `t`, is the value of the function on the real jet of the path. -/
theorem prolongation_op_apply (g : SmoothOperation (n + n + 1)) (γ : Fin n → TimeFunction)
    (t : ℝ) :
    prolongation γ (op g (firstOrderCoordinates n)) (fun _ => t) = g (realJet γ t) := by
  rw [SmoothRingHom.map_op, function_op, comp_apply]
  congr 1
  funext j
  exact prolongation_firstOrderCoordinates_apply γ t j

/-- The prolongation of `firstOrder f` is the Lagrangian evaluated along the path. -/
theorem prolongation_firstOrder_apply (f : SmoothOperation (n + n + 1))
    (γ : Fin n → TimeFunction) (t : ℝ) :
    prolongation γ (firstOrder f) (fun _ => t) =
      ofSmoothOperation f t (realPath γ t, deriv (realPath γ) t) :=
  prolongation_op_apply f γ t

/-! ### Derivatives of the analytic Lagrangian -/

theorem cons_append_add (s s' : ℝ) (u u' v v' : Fin n → ℝ) :
    (Fin.cons (s + s') (Fin.append (u + u') (v + v')) : Fin (n + n + 1) → ℝ) =
      Fin.cons s (Fin.append u v) + Fin.cons s' (Fin.append u' v') := by
  funext j
  induction j using Fin.cases with
  | zero => simp only [Fin.cons_zero, Pi.add_apply]
  | succ j =>
    induction j using Fin.addCases with
    | left a => simp only [Fin.cons_succ, Pi.add_apply, Fin.append_left]
    | right a => simp only [Fin.cons_succ, Pi.add_apply, Fin.append_right]

theorem cons_append_smul (c s : ℝ) (u v : Fin n → ℝ) :
    (Fin.cons (c * s) (Fin.append (c • u) (c • v)) : Fin (n + n + 1) → ℝ) =
      c • Fin.cons s (Fin.append u v) := by
  funext j
  induction j using Fin.cases with
  | zero => simp only [Fin.cons_zero, Pi.smul_apply, smul_eq_mul]
  | succ j =>
    induction j using Fin.addCases with
    | left a => simp only [Fin.cons_succ, Pi.smul_apply, Fin.append_left]
    | right a => simp only [Fin.cons_succ, Pi.smul_apply, Fin.append_right]

/-- The linear part of the embedding `(q, v) ↦ (t, q, v)`. -/
def jetEmbedding (n : ℕ) : ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] (Fin (n + n + 1) → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => Fin.cons 0 (Fin.append w.1 w.2)
      map_add' := fun w w' => by
        rw [← cons_append_add, add_zero]
        rfl
      map_smul' := fun c w => by
        rw [RingHom.id_apply, ← cons_append_smul, mul_zero]
        rfl }

@[simp] theorem jetEmbedding_apply (w : (Fin n → ℝ) × (Fin n → ℝ)) :
    jetEmbedding n w = Fin.cons 0 (Fin.append w.1 w.2) := rfl

theorem hasFDerivAt_cons_append (t : ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    HasFDerivAt (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      (Fin.cons t (Fin.append z.1 z.2) : Fin (n + n + 1) → ℝ)) (jetEmbedding n) z := by
  have h : (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      (Fin.cons t (Fin.append z.1 z.2) : Fin (n + n + 1) → ℝ)) =
      fun z => jetEmbedding n z + Fin.cons t (Fin.append 0 0) := by
    funext z
    rw [jetEmbedding_apply, ← cons_append_add, zero_add, add_zero, add_zero]
  rw [h]
  exact (jetEmbedding n).hasFDerivAt.add_const _

/-- The derivative of the analytic Lagrangian in position and velocity is the
derivative of `f` along the embedded direction. -/
theorem fderiv_ofSmoothOperation (f : SmoothOperation (n + n + 1)) (t : ℝ)
    (z w : (Fin n → ℝ) × (Fin n → ℝ)) :
    fderiv ℝ (ofSmoothOperation f t) z w =
      fderiv ℝ f (Fin.cons t (Fin.append z.1 z.2)) (Fin.cons 0 (Fin.append w.1 w.2)) := by
  have hf : HasFDerivAt f (fderiv ℝ f (Fin.cons t (Fin.append z.1 z.2)))
      (Fin.cons t (Fin.append z.1 z.2)) :=
    (f.contMDiff.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  have h : HasFDerivAt (ofSmoothOperation f t)
      ((fderiv ℝ f (Fin.cons t (Fin.append z.1 z.2))).comp (jetEmbedding n)) z :=
    hf.comp z (hasFDerivAt_cons_append t z)
  rw [h.fderiv]
  rfl

theorem cons_append_single_left (i : Fin n) :
    (Fin.cons 0 (Fin.append (Pi.single i 1) 0) : Fin (n + n + 1) → ℝ) =
      Pi.single (positionIndex i) 1 := by
  have h0 : (0 : Fin (n + n + 1)) ≠ positionIndex i := (Fin.succ_ne_zero _).symm
  funext j
  induction j using index_cases with
  | zero => rw [Fin.cons_zero, Pi.single_eq_of_ne h0]
  | position a =>
    rw [positionIndex, Fin.cons_succ, Fin.append_left, ← positionIndex]
    simp only [Pi.single_apply, positionIndex_injective.eq_iff]
  | velocity a =>
    rw [velocityIndex, Fin.cons_succ, Fin.append_right, ← velocityIndex,
      Pi.single_eq_of_ne (positionIndex_ne_velocityIndex i a).symm]
    rfl

theorem cons_append_single_right (i : Fin n) :
    (Fin.cons 0 (Fin.append 0 (Pi.single i 1)) : Fin (n + n + 1) → ℝ) =
      Pi.single (velocityIndex i) 1 := by
  have h0 : (0 : Fin (n + n + 1)) ≠ velocityIndex i := (Fin.succ_ne_zero _).symm
  funext j
  induction j using index_cases with
  | zero => rw [Fin.cons_zero, Pi.single_eq_of_ne h0]
  | position a =>
    rw [positionIndex, Fin.cons_succ, Fin.append_left, ← positionIndex,
      Pi.single_eq_of_ne (positionIndex_ne_velocityIndex a i)]
    rfl
  | velocity a =>
    rw [velocityIndex, Fin.cons_succ, Fin.append_right, ← velocityIndex]
    simp only [Pi.single_apply, velocityIndex_injective.eq_iff]

/-- The force `∂L/∂qᵢ` of the analytic Lagrangian along a path. -/
theorem force_ofSmoothOperation (f : SmoothOperation (n + n + 1)) (q : ℝ → Fin n → ℝ) (t : ℝ)
    (i : Fin n) :
    force (ofSmoothOperation f) q t (Pi.single i 1) =
      partialDeriv (positionIndex i) f (Fin.cons t (Fin.append (q t) (deriv q t))) := by
  rw [force, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    fderiv_ofSmoothOperation, partialDeriv_apply, ← cons_append_single_left]

/-- The momentum `∂L/∂q̇ᵢ` of the analytic Lagrangian along a path. -/
theorem momentum_ofSmoothOperation (f : SmoothOperation (n + n + 1)) (q : ℝ → Fin n → ℝ)
    (t : ℝ) (i : Fin n) :
    momentum (ofSmoothOperation f) q t (Pi.single i 1) =
      partialDeriv (velocityIndex i) f (Fin.cons t (Fin.append (q t) (deriv q t))) := by
  rw [momentum, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    fderiv_ofSmoothOperation, partialDeriv_apply, ← cons_append_single_right]

/-- The Euler–Lagrange residual of the analytic Lagrangian in the direction of
the `i`-th coordinate. -/
theorem eulerLagrange_ofSmoothOperation (f : SmoothOperation (n + n + 1))
    {q : ℝ → Fin n → ℝ} (hq : ContDiff ℝ 2 q) (t : ℝ) (i : Fin n) :
    eulerLagrange (ofSmoothOperation f) q t (Pi.single i 1) =
      partialDeriv (positionIndex i) f (Fin.cons t (Fin.append (q t) (deriv q t))) -
        deriv (fun s => partialDeriv (velocityIndex i) f
          (Fin.cons s (Fin.append (q s) (deriv q s)))) t := by
  have hL : ContDiff ℝ 2 (Function.uncurry (ofSmoothOperation f)) :=
    (contDiff_ofSmoothOperation f).of_le (by norm_num)
  have hm : DifferentiableAt ℝ (momentum (ofSmoothOperation f) q) t :=
    ((contDiff_momentum hL hq).differentiable (by norm_num)).differentiableAt
  have hd : deriv (fun s => momentum (ofSmoothOperation f) q s (Pi.single i 1)) t =
      deriv (momentum (ofSmoothOperation f) q) t (Pi.single i 1) := by
    rw [deriv_clm_apply hm (differentiableAt_const _), deriv_const, map_zero, add_zero]
  rw [eulerLagrange, sub_apply, force_ofSmoothOperation, ← hd]
  simp only [momentum_ofSmoothOperation]

/-! ### Solutions and stationary paths -/

/-- The prolongation of the Euler operator of `firstOrder f`, evaluated at time
`t`, is the Euler–Lagrange residual of the real path. -/
theorem prolongation_euler_firstOrder_apply (f : SmoothOperation (n + n + 1))
    (γ : Fin n → TimeFunction) (i : Fin n) (t : ℝ) :
    prolongation γ ((jetRing (Fin n)).euler i (firstOrder f)) (fun _ => t) =
      eulerLagrange (ofSmoothOperation f) (realPath γ) t (Pi.single i 1) := by
  have hsub (a b : TimeFunction) (x : Fin 1 → ℝ) : (a - b) x = a x - b x := rfl
  rw [eulerLagrange_ofSmoothOperation f ((contDiff_realPath γ).of_le (by norm_num)),
    euler_firstOrder, SmoothRingHom.map_sub, prolongation_totalDeriv, hsub,
    prolongation_op_apply, TimeFunction.timeDerivative_apply]
  simp only [prolongation_op_apply]
  rfl

/-- A smooth path is a solution of the Euler–Lagrange equations of `firstOrder f`
in the jet ring exactly when its Euler–Lagrange residual in the real analytic
model vanishes at all times. -/
theorem isSolution_firstOrder_iff (f : SmoothOperation (n + n + 1))
    (γ : Fin n → TimeFunction) :
    IsSolution (firstOrder f) γ ↔
      ∀ t, eulerLagrange (ofSmoothOperation f) (realPath γ) t = 0 := by
  constructor
  · intro h t
    have hi (i : Fin n) :
        eulerLagrange (ofSmoothOperation f) (realPath γ) t (Pi.single i 1) = 0 := by
      rw [← prolongation_euler_firstOrder_apply, h i]
      rfl
    ext v
    rw [pi_eq_sum_univ' v, map_sum]
    simp [hi]
  · intro h i
    refine TimeFunction.ext_apply_const fun t => ?_
    rw [prolongation_euler_firstOrder_apply, h t]
    rfl

/-- A smooth path is a solution in the jet ring exactly when the action is
stationary under fixed-endpoint variations on every interval. -/
theorem isSolution_firstOrder_iff_stationary (f : SmoothOperation (n + n + 1))
    (γ : Fin n → TimeFunction) :
    IsSolution (firstOrder f) γ ↔
      ∀ a b : ℝ, a < b → Stationary a b (ofSmoothOperation f) (realPath γ) := by
  have hL : ContDiff ℝ 2 (Function.uncurry (ofSmoothOperation f)) :=
    (contDiff_ofSmoothOperation f).of_le (by norm_num)
  have hq : ContDiff ℝ 2 (realPath γ) := (contDiff_realPath γ).of_le (by norm_num)
  rw [isSolution_firstOrder_iff]
  constructor
  · intro h a b hab
    exact (stationary_iff_eulerLagrange hab hL hq).mpr fun t _ => h t
  · intro h t
    exact (stationary_iff_eulerLagrange (show t - 1 < t + 1 by linarith) hL hq).mp
      (h _ _ (by linarith)) t ⟨by linarith, by linarith⟩

/-- A conserved element of the jet ring takes the same value at all times along
every smooth path that makes the action stationary on every interval. -/
theorem prolongation_eq_of_stationary {f : SmoothOperation (n + n + 1)}
    {F : StandardJet (Fin n)} {γ : Fin n → TimeFunction}
    (h : ∀ a b : ℝ, a < b → Stationary a b (ofSmoothOperation f) (realPath γ))
    (hF : (jetRing (Fin n)).Conserved (firstOrder f) F) (s t : Fin 1 → ℝ) :
    prolongation γ F s = prolongation γ F t :=
  prolongation_eq_of_conserved ((isSolution_firstOrder_iff_stationary f γ).mpr h) hF s t

/-- The energy `Σᵢ q̇ᵢ ∂L/∂q̇ᵢ − L` of a first-order Lagrangian along a path. -/
theorem prolongation_energy_firstOrder_apply (f : SmoothOperation (n + n + 1))
    (γ : Fin n → TimeFunction) (t : ℝ) :
    prolongation γ ((jetRing (Fin n)).energy (firstOrder f)) (fun _ => t) =
      ∑ i, deriv (realPath γ) t i * partialDeriv (velocityIndex i) f (realJet γ t) -
        f (realJet γ t) := by
  have hmul (a b : TimeFunction) (x : Fin 1 → ℝ) : (a * b) x = a x * b x := rfl
  change SmoothOperation.eval (fun _ => t)
    (prolongation γ ((jetRing (Fin n)).energy (firstOrder f))) = _
  rw [JetRing.energy, SmoothRingHom.map_sub, SmoothRingHom.map_sum, SmoothRingHom.map_sub,
    SmoothRingHom.map_sum]
  simp only [eval_apply]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [SmoothRingHom.map_mul, hmul, prolongation_q, JetRing.momentum, d_one_firstOrder,
      prolongation_op_apply, deriv_realPath]
    rfl
  · exact prolongation_op_apply f γ t

/-- Conservation of energy in the real analytic model (Landau–Lifshitz §6): if
the Lagrangian does not depend on time, the energy `Σᵢ q̇ᵢ ∂L/∂q̇ᵢ − L` takes the
same value at all times along every smooth path that makes the action
stationary on every interval. -/
theorem energy_eq_of_stationary {f : SmoothOperation (n + n + 1)}
    (hf : partialDeriv 0 f = 0) {γ : Fin n → TimeFunction}
    (h : ∀ a b : ℝ, a < b → Stationary a b (ofSmoothOperation f) (realPath γ)) (s t : ℝ) :
    ∑ i, deriv (realPath γ) s i * partialDeriv (velocityIndex i) f (realJet γ s) -
        f (realJet γ s) =
      ∑ i, deriv (realPath γ) t i * partialDeriv (velocityIndex i) f (realJet γ t) -
        f (realJet γ t) := by
  rw [← prolongation_energy_firstOrder_apply, ← prolongation_energy_firstOrder_apply]
  exact prolongation_eq_of_stationary h
    (JetRing.conserved_energy (orderLE_firstOrder f) (dt_firstOrder_eq_zero hf)) _ _

end ProjectAInos.Mechanics.StandardJet
