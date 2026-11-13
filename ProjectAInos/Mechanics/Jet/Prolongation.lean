/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Jet.Standard
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Ring

/-!
# Prolongation of a path and conservation along solutions

A smooth path `γ : ι → C∞(ℝ)` prolongs to a morphism from the standard jet ring
to the ring of smooth functions of time: it sends the time coordinate to `t`
and `qᵢ⁽ᵏ⁾` to the `k`-th derivative of `γᵢ`. The prolongation turns the total
derivative into `d/dt`.

A path is a solution of the Euler–Lagrange equations of `L` when its
prolongation annihilates the Euler–Lagrange expressions. It then annihilates the
whole Euler–Lagrange ideal, so a conserved element of the jet ring becomes a
function of time with zero derivative: a constant. This is the link between
conservation as ideal membership and conservation along actual trajectories.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing

/-- Smooth functions of time. -/
abbrev TimeFunction := SmoothOperation 1

/-- The derivative `d/dt` of a smooth function of time. -/
def timeDerivative : SmoothDerivation TimeFunction TimeFunction :=
  SmoothDerivation.partialDerivation 0

/-- A smooth function of time with zero derivative is constant. -/
theorem TimeFunction.eq_of_timeDerivative_eq_zero {f : TimeFunction}
    (h : timeDerivative f = 0) (s t : Fin 1 → ℝ) : f s = f t := by
  refine is_const_of_fderiv_eq_zero (𝕜 := ℝ) (f.contMDiff.contDiff.differentiable (by simp))
    (fun x => ?_) s t
  ext v
  rw [SmoothOperation.fderiv_apply_eq_sum_partialDeriv, Fin.sum_univ_one]
  have h0 : SmoothOperation.partialDeriv 0 f x = 0 := congrArg (fun g : TimeFunction => g x) h
  rw [h0, mul_zero]
  rfl

namespace StandardJet

variable {ι : Type*} [DecidableEq ι]

/-- The value of the prolongation on a generator. -/
def prolongationValue (γ : ι → TimeFunction) : Option (ι × ℕ) → TimeFunction
  | none => SmoothOperation.proj 0
  | some (i, k) => (timeDerivative^[k]) (γ i)

/-- The prolongation of a smooth path: the morphism from the standard jet ring
to functions of time with `t ↦ t` and `qᵢ⁽ᵏ⁾ ↦ dᵏγᵢ/dtᵏ`. -/
def prolongation (γ : ι → TimeFunction) : SmoothRingHom (StandardJet ι) TimeFunction :=
  FreeSmoothRing.lift (prolongationValue γ)

omit [DecidableEq ι] in
@[simp] theorem prolongation_time (γ : ι → TimeFunction) :
    prolongation γ (time ι) = SmoothOperation.proj 0 :=
  FreeSmoothRing.lift_generator _ _

@[simp] theorem prolongation_q (γ : ι → TimeFunction) (i : ι) (k : ℕ) :
    prolongation γ ((jetRing ι).q i k) = (timeDerivative^[k]) (γ i) :=
  FreeSmoothRing.lift_generator _ _

variable [Fintype ι]

/-- The prolongation turns the total derivative into `d/dt`. -/
theorem prolongation_totalDeriv (γ : ι → TimeFunction) (F : StandardJet ι) :
    prolongation γ ((jetRing ι).totalDeriv F) = timeDerivative (prolongation γ F) := by
  have hgen (c : Option (ι × ℕ)) :
      prolongation γ ((jetRing ι).totalDeriv (FreeSmoothRing.generator c)) =
        timeDerivative (prolongation γ (FreeSmoothRing.generator c)) := by
    cases c with
    | none =>
      have h1 : (jetRing ι).totalDeriv (FreeSmoothRing.generator none) = 1 := totalDeriv_time
      have h2 : prolongation γ (FreeSmoothRing.generator none) = SmoothOperation.proj 0 :=
        prolongation_time γ
      rw [h1, h2, SmoothRingHom.map_one, timeDerivative,
        SmoothDerivation.partialDerivation_proj]
      rfl
    | some p =>
      have h1 : (jetRing ι).totalDeriv (FreeSmoothRing.generator (some p)) =
          (jetRing ι).q p.1 (p.2 + 1) := JetRing.totalDeriv_q (R := jetRing ι) p.1 p.2
      have h2 : prolongation γ (FreeSmoothRing.generator (some p)) =
          (timeDerivative^[p.2]) (γ p.1) := prolongation_q γ p.1 p.2
      rw [h1, h2, prolongation_q]
      exact Function.iterate_succ_apply' _ _ _
  rw [FreeSmoothRing.presentation_eq F, SmoothDerivation.chain, SmoothRingHom.map_sum,
    SmoothRingHom.map_op, SmoothDerivation.chain]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, smul_eq_mul, SmoothRingHom.map_mul, SmoothRingHom.map_op, hgen]

theorem prolongation_iterate_totalDeriv (γ : ι → TimeFunction) (F : StandardJet ι) (k : ℕ) :
    prolongation γ (((jetRing ι).totalDeriv^[k]) F) =
      (timeDerivative^[k]) (prolongation γ F) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', prolongation_totalDeriv, ih]

/-- A smooth path is a solution of the Euler–Lagrange equations of `L`: its
prolongation annihilates the Euler–Lagrange expressions. -/
def IsSolution (L : StandardJet ι) (γ : ι → TimeFunction) : Prop :=
  ∀ i, prolongation γ ((jetRing ι).euler i L) = 0

/-- The prolongation of a solution annihilates the Euler–Lagrange ideal. -/
theorem prolongation_eq_zero_of_mem {L : StandardJet ι} {γ : ι → TimeFunction}
    (h : IsSolution L γ) {x : StandardJet ι} (hx : x ∈ (jetRing ι).eulerLagrangeIdeal L) :
    prolongation γ x = 0 := by
  refine Submodule.span_induction (p := fun x _ => prolongation γ x = 0) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, k, rfl⟩
    rw [prolongation_iterate_totalDeriv, h i, iterate_map_zero]
  · exact SmoothRingHom.map_zero _
  · intro x y _ _ hx hy
    rw [SmoothRingHom.map_add, hx, hy, add_zero]
  · intro a x _ hx
    rw [smul_eq_mul, SmoothRingHom.map_mul, hx, mul_zero]

/-- Along a solution, a conserved element has zero time derivative. -/
theorem timeDerivative_prolongation_eq_zero {L F : StandardJet ι} {γ : ι → TimeFunction}
    (h : IsSolution L γ) (hF : (jetRing ι).Conserved L F) :
    timeDerivative (prolongation γ F) = 0 := by
  rw [← prolongation_totalDeriv]
  exact prolongation_eq_zero_of_mem h hF

/-- Conservation along trajectories: a conserved element of the jet ring takes
the same value at all times along every smooth solution. -/
theorem prolongation_eq_of_conserved {L F : StandardJet ι} {γ : ι → TimeFunction}
    (h : IsSolution L γ) (hF : (jetRing ι).Conserved L F) (s t : Fin 1 → ℝ) :
    prolongation γ F s = prolongation γ F t :=
  TimeFunction.eq_of_timeDerivative_eq_zero (timeDerivative_prolongation_eq_zero h hF) s t

/-- For a natural Lagrangian the solutions are the solutions of Newton's
equations `mᵢ γ̈ᵢ = −∂ᵢU` along the path. -/
theorem isSolution_naturalLagrangian_iff (m : ι → ℝ) {U : StandardJet ι}
    (hU : (jetRing ι).OrderLE U 0) (γ : ι → TimeFunction) :
    IsSolution ((jetRing ι).naturalLagrangian m U) γ ↔
      ∀ i, algebraMap ℝ TimeFunction (m i) * (timeDerivative^[2]) (γ i) =
        -prolongation γ ((jetRing ι).d i 0 U) := by
  refine forall_congr' fun i => ?_
  rw [JetRing.euler_naturalLagrangian m hU, SmoothRingHom.map_sub, SmoothRingHom.map_neg,
    SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, prolongation_q, sub_eq_zero, eq_comm]

/-- The energy of a natural Lagrangian along a path is
`Σᵢ ½ mᵢ γ̇ᵢ² + U(γ)`. -/
theorem prolongation_energy (m : ι → ℝ) (U : StandardJet ι) (γ : ι → TimeFunction) :
    prolongation γ (∑ i, algebraMap ℝ (StandardJet ι) (m i / 2) *
        ((jetRing ι).q i 1 * (jetRing ι).q i 1) + U) =
      ∑ i, algebraMap ℝ TimeFunction (m i / 2) * (timeDerivative (γ i) * timeDerivative (γ i)) +
        prolongation γ U := by
  rw [SmoothRingHom.map_add, SmoothRingHom.map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SmoothRingHom.map_mul, SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, prolongation_q]
  rfl

/-- Conservation of energy along trajectories (Landau–Lifshitz §6): for a
potential that does not depend explicitly on time, the energy
`Σᵢ ½ mᵢ γ̇ᵢ² + U(γ)` takes the same value at all times along every smooth
solution of Newton's equations. -/
theorem energy_eq_of_isSolution (m : ι → ℝ) {U : StandardJet ι}
    (hU : (jetRing ι).OrderLE U 0) (ht : (jetRing ι).dt U = 0) {γ : ι → TimeFunction}
    (h : IsSolution ((jetRing ι).naturalLagrangian m U) γ) (s t : Fin 1 → ℝ) :
    (∑ i, algebraMap ℝ TimeFunction (m i / 2) * (timeDerivative (γ i) * timeDerivative (γ i)) +
        prolongation γ U) s =
      (∑ i, algebraMap ℝ TimeFunction (m i / 2) *
          (timeDerivative (γ i) * timeDerivative (γ i)) + prolongation γ U) t := by
  rw [← prolongation_energy]
  exact prolongation_eq_of_conserved h (JetRing.conserved_energy_naturalLagrangian m hU ht) s t

/-- The solutions of the isotropic oscillator are the smooth solutions of
`mᵢ γ̈ᵢ = −k γᵢ`. -/
theorem isSolution_oscillator_iff (m : ι → ℝ) (k : ℝ) (γ : ι → TimeFunction) :
    IsSolution ((jetRing ι).naturalLagrangian m (oscillatorPotential k)) γ ↔
      ∀ i, algebraMap ℝ TimeFunction (m i) * (timeDerivative^[2]) (γ i) =
        -(algebraMap ℝ TimeFunction k * γ i) := by
  rw [isSolution_naturalLagrangian_iff m (orderLE_oscillatorPotential k)]
  refine forall_congr' fun i => ?_
  rw [d_zero_oscillatorPotential, SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap,
    prolongation_q]
  rfl

/-- The energy of the isotropic oscillator takes the same value at all times
along every smooth solution. -/
theorem oscillator_energy_eq_of_isSolution (m : ι → ℝ) (k : ℝ) {γ : ι → TimeFunction}
    (h : IsSolution ((jetRing ι).naturalLagrangian m (oscillatorPotential k)) γ)
    (s t : Fin 1 → ℝ) :
    (∑ i, algebraMap ℝ TimeFunction (m i / 2) * (timeDerivative (γ i) * timeDerivative (γ i)) +
        prolongation γ (oscillatorPotential k)) s =
      (∑ i, algebraMap ℝ TimeFunction (m i / 2) *
          (timeDerivative (γ i) * timeDerivative (γ i)) +
        prolongation γ (oscillatorPotential k)) t :=
  energy_eq_of_isSolution m (orderLE_oscillatorPotential k) (dt_oscillatorPotential k) h s t

/-- Uniform motion `γᵢ(t) = aᵢ + bᵢ t`. -/
def uniformMotion (a b : ι → ℝ) : ι → TimeFunction :=
  fun i =>
    algebraMap ℝ TimeFunction (a i) + algebraMap ℝ TimeFunction (b i) * SmoothOperation.proj 0

omit [DecidableEq ι] [Fintype ι] in
theorem timeDerivative_uniformMotion (a b : ι → ℝ) (i : ι) :
    timeDerivative (uniformMotion a b i) = algebraMap ℝ TimeFunction (b i) := by
  rw [uniformMotion, map_add, SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap,
    SmoothDerivation.map_algebraMap, timeDerivative, SmoothDerivation.partialDerivation_proj]
  simp

/-- Uniform motion solves the equations of free particles. -/
theorem isSolution_uniformMotion (m a b : ι → ℝ) :
    IsSolution ((jetRing ι).naturalLagrangian m 0) (uniformMotion a b) := by
  rw [isSolution_naturalLagrangian_iff m (fun _ _ _ => map_zero _)]
  intro i
  have h2 : (timeDerivative^[2]) (uniformMotion a b i) = 0 := by
    rw [Function.iterate_succ_apply', Function.iterate_one, timeDerivative_uniformMotion,
      SmoothDerivation.map_algebraMap]
  rw [h2, mul_zero, map_zero, SmoothRingHom.map_zero, neg_zero]

end StandardJet

end ProjectAInos.Mechanics
