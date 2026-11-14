/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAInos

/-! Public consumers of the similarity API: the change of the unit of time,
homogeneous potentials, similar solutions, the virial theorem for time
averages, and the orbit and the similar motions of Kepler's problem. Default
elaborator options are intentional: these checks must not rely on the
implementation's transparency settings. Every statement is pinned with its
type. -/
noncomputable section
open ProjectAInos.SmoothAlgebra ProjectAInos.SmoothAlgebra.SmoothRing
open ProjectAInos.SmoothAlgebra.FreeSmoothRing ProjectAInos.SmoothAlgebra.PhaseSpace
open ProjectAInos.Mechanics
open Filter Topology

section Similarity

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

example (β : ℝ) (f : TimeFunction) (t : ℝ) :
    TimeFunction.scale β f (fun _ => t) = f fun _ => β * t := rfl

example (β : ℝ) (f : TimeFunction) :
    timeDerivative (TimeFunction.scale β f) =
      algebraMap ℝ TimeFunction β * TimeFunction.scale β (timeDerivative f) :=
  TimeFunction.timeDerivative_scale β f

example (k : ℝ) (u : FreeSmoothRing ι) :
    IsHomogeneous k u ↔
      ∀ α : ℝ, 0 < α → dilate α u = algebraMap ℝ (FreeSmoothRing ι) (α ^ k) * u :=
  Iff.rfl

/-- The derivatives of a homogeneous function are homogeneous of one degree less. -/
example {k : ℝ} {u : FreeSmoothRing ι} (hu : IsHomogeneous k u) {α : ℝ} (hα : 0 < α) (j : ι) :
    dilate α (partialDerivation j u) =
      algebraMap ℝ (FreeSmoothRing ι) (α ^ (k - 1)) * partialDerivation j u :=
  hu.dilate_partialDerivation hα j

/-- Mechanical similarity (Landau–Lifshitz (10.1), (10.2)). -/
example {m : ι → ℝ} {k : ℝ} {u : FreeSmoothRing ι} (hu : IsHomogeneous k u)
    {γ : ι → TimeFunction}
    (h : StandardJet.IsSolution
      ((StandardJet.jetRing ι).naturalLagrangian m (positionsToJet u)) γ) {α : ℝ}
    (hα : 0 < α) :
    StandardJet.IsSolution ((StandardJet.jetRing ι).naturalLagrangian m (positionsToJet u))
      fun i => algebraMap ℝ TimeFunction α * TimeFunction.scale (α ^ ((k - 2) / 2)) (γ i) :=
  h.similar hu hα

/-- The periods of similar paths. -/
example {γ : TimeFunction} {T : ℝ} (hT : ∀ t : ℝ, γ (fun _ => t + T) = γ fun _ => t) (α : ℝ)
    {β : ℝ} (hβ : β ≠ 0) (t : ℝ) :
    (algebraMap ℝ TimeFunction α * TimeFunction.scale β γ) (fun _ => t + T / β) =
      (algebraMap ℝ TimeFunction α * TimeFunction.scale β γ) fun _ => t :=
  similar_apply_add_period hT α hβ t

end Similarity

section Virial

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The average of the derivative of a bounded function tends to zero. -/
example {G : TimeFunction} {B : ℝ} (hB : ∀ t : ℝ, |G fun _ => t| ≤ B) :
    Tendsto (fun τ : ℝ => (1 / τ) * ∫ t in (0 : ℝ)..τ, timeDerivative G fun _ => t) atTop
      (𝓝 0) :=
  TimeFunction.tendsto_average_timeDerivative hB

/-- The virial theorem (Landau–Lifshitz §10). -/
example (m : ι → ℝ) {U : PhaseSpace ι} {k : ℝ}
    (hU : ∑ i, q i * partialDerivation (Sum.inl i) U = algebraMap ℝ (PhaseSpace ι) k * U)
    (hUp : ∀ i, partialDerivation (Sum.inr i) U = 0) {c : ι ⊕ ι → TimeFunction}
    (h : IsTrajectory (canonical ι) (kineticEnergy m + U) c) {B : ℝ}
    (hB : ∀ t : ℝ, |FreeSmoothRing.lift c dilation fun _ => t| ≤ B) :
    Tendsto (fun τ : ℝ => (1 / τ) * ∫ t in (0 : ℝ)..τ,
      FreeSmoothRing.lift c (2 * kineticEnergy m - algebraMap ℝ (PhaseSpace ι) k * U)
        fun _ => t) atTop (𝓝 0) :=
  h.tendsto_average_virial m hU hUp hB

end Virial

section KeplerOrbit

open KeplerModel

/-- The orbit is a conic. -/
example {m α : ℝ} {Q Pm : Fin 3 → TimeFunction} {R : TimeFunction}
    (h : IsKeplerMotion m α Q Pm R) (hm : m ≠ 0) (t : ℝ) :
    ∑ a, Kepler.rungeLenz m α Q Pm R a (fun _ => 0) * Q a (fun _ => t) =
      ∑ a, Kepler.angularMomentum Q Pm a (fun _ => 0) ^ 2 -
        m * α * Kepler.distance Q R fun _ => t :=
  h.conic hm t

/-- Similar Kepler motions. -/
example {m α : ℝ} {Q Pm : Fin 3 → TimeFunction} {R : TimeFunction}
    (h : IsKeplerMotion m α Q Pm R) {lam β : ℝ} (hlam : lam ≠ 0) (hβ : β ^ 2 * lam ^ 3 = 1) :
    IsKeplerMotion m α
      (fun i => algebraMap ℝ TimeFunction lam * TimeFunction.scale β (Q i))
      (fun i => algebraMap ℝ TimeFunction (lam * β) * TimeFunction.scale β (Pm i))
      (algebraMap ℝ TimeFunction lam⁻¹ * TimeFunction.scale β R) :=
  h.similar hlam hβ

/-- Kepler's third law for similar orbits. -/
example {Q : Fin 3 → TimeFunction} {T lam β : ℝ}
    (hT : ∀ i (t : ℝ), Q i (fun _ => t + T) = Q i fun _ => t) (hβ : β ^ 2 * lam ^ 3 = 1) :
    (∀ i (t : ℝ),
      (algebraMap ℝ TimeFunction lam * TimeFunction.scale β (Q i)) (fun _ => t + T / β) =
        (algebraMap ℝ TimeFunction lam * TimeFunction.scale β (Q i)) fun _ => t) ∧
      (T / β) ^ 2 = lam ^ 3 * T ^ 2 :=
  similar_period hT hβ

end KeplerOrbit
