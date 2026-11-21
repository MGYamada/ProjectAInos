/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Optics.Basic
public import ProjectAinos.Mechanics.Poisson.Separation
public import ProjectAinos.Mechanics.Maupertuis
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic

/-!
# Rays in a medium

The rays of geometrical optics in a medium of refractive index `n` (Landau–Lifshitz, *The
Classical Theory of Fields*, §53). With the parameter `σ` along the ray chosen so that
`|dq/dσ| = n`, the rays are the trajectories of the **ray Hamiltonian** `H = (|p|² − n²)/2` at
`H = 0`, and the eikonal is the abbreviated action.

* `rayHamiltonian n²`: `H = Σᵢ pᵢ²/2 − n²/2` on the canonical phase space, with `n²` an element
  of the free C∞-ring of the positions; `isTrajectory_rayHamiltonian_iff`: Hamilton's equations
  `q′ = p`, `p′ = ½ ∇n²`, and so `q″ = ½ ∇n²`
  (`timeDerivative_timeDerivative_of_isTrajectory`).
* `isRay_of_isHamiltonJacobi`: the rays from a complete integral `S(q, α, σ)` of
  `∂S/∂σ + (|∇S|² − n²)/2 = 0`, by Jacobi's theorem
  (`CompleteIntegral.isTrajectory_of_isHamiltonJacobi`).
* Instances: a homogeneous medium, `S = α · q − (|α|² − n²) σ/2` (`constantIndexAction`,
  `isHamiltonJacobi_constantIndex`, the straight rays `isTrajectory_constantIndexRay`), and the
  linear gradient `n² = n₀² + 2 g z` (`linearIndexSq`), whose complete integral
  `S = α · q + g σ z − (|α|² − n₀²) σ/2 − g α₃ σ²/2 − g² σ³/6` is a polynomial
  (`linearIndexAction`, `isHamiltonJacobi_linearIndex`), with the parabolic rays
  `q = β + α σ + g σ² e₃/2` (`isTrajectory_linearIndexRay`,
  `timeDerivative_timeDerivative_linearIndexRay`: `q″ = g e₃`). A quadratic graded-index lens has
  no complete integral that is smooth on all of `ℝ³ × ℝ³ × ℝ` and is not treated.
* **Fermat's principle** `fermat`: for a path with `|γ′| = n(γ)`, the optical length
  `Optics.opticalLength n γ a b = ∫ n(γ) |γ′|` is stationary (`OpticalStationary`) if and only if
  `γ″ = ∇(n²/2)`. The optical Lagrangian `n |q′|` is the Jacobi length `2 √((E − U) T)` of
  `T = |q′|²/2`, `U = −n²/2` at `E = 0` (`jacobiLength_eq_opticalLagrangian`), and the theorem is
  Maupertuis' principle `Maupertuis.stationary_jacobiLength_iff`; `opticalStationary_line` is an
  instance.
-/

@[expose] public section

noncomputable section

open Set

namespace ProjectAinos.Electrodynamics.Optics.RayOptics

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace Mechanics Mechanics.CompleteIntegral

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The ray Hamiltonian -/

/-- The ray Hamiltonian `H = (|p|² − n²)/2` of a medium whose squared index `n²` is a function
of the positions. -/
def rayHamiltonian (nsq : FreeSmoothRing (Fin 3)) : PhaseSpace (Fin 3) :=
  kineticEnergy (fun _ => 1) +
    positionsToPhase (-(algebraMap ℝ (FreeSmoothRing (Fin 3)) (1 / 2) * nsq))

/-- **Hamilton's equations of the rays**: `q′ = p` and `p′ = ½ ∇n²`. -/
theorem isTrajectory_rayHamiltonian_iff (nsq : FreeSmoothRing (Fin 3))
    (c : Fin 3 ⊕ Fin 3 → TimeFunction) :
    IsTrajectory (canonical (Fin 3)) (rayHamiltonian nsq) c ↔
      (∀ i, timeDerivative (c (Sum.inl i)) = c (Sum.inr i)) ∧
      ∀ i, timeDerivative (c (Sum.inr i)) = algebraMap ℝ TimeFunction (1 / 2) *
        FreeSmoothRing.lift (fun k => c (Sum.inl k)) (partialDerivation i nsq) := by
  rw [rayHamiltonian, isTrajectory_natural_iff]
  simp only [inv_one, map_one, one_mul, map_neg, SmoothDerivation.map_algebraMap_mul, smul_eq_mul,
    SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, neg_neg, SmoothRingHom.map_neg]

/-- **The ray equation** `q″ = ½ ∇n²` along a trajectory of the ray Hamiltonian. -/
theorem timeDerivative_timeDerivative_of_isTrajectory {nsq : FreeSmoothRing (Fin 3)}
    {c : Fin 3 ⊕ Fin 3 → TimeFunction}
    (h : IsTrajectory (canonical (Fin 3)) (rayHamiltonian nsq) c) (i : Fin 3) :
    timeDerivative (timeDerivative (c (Sum.inl i))) = algebraMap ℝ TimeFunction (1 / 2) *
      FreeSmoothRing.lift (fun k => c (Sum.inl k)) (partialDerivation i nsq) := by
  rw [isTrajectory_rayHamiltonian_iff] at h
  rw [h.1 i, h.2 i]

/-- **The rays from a complete integral**: if `S(q, α, σ)` solves
`∂S/∂σ + (|∇S|² − n²)/2 = 0`, a curve along which every `∂S/∂αᵢ` is constant and the matrix
`∂²S/∂αᵢ∂qₖ` is non-degenerate is a ray, `q′ = ∇S` and `q″ = ½ ∇n²` (Jacobi's theorem). -/
theorem isRay_of_isHamiltonJacobi {nsq : FreeSmoothRing (Fin 3)} {S : ActionSpace (Fin 3)}
    (hS : IsHamiltonJacobi (rayHamiltonian nsq) S) {Q : Fin 3 → TimeFunction} {α : Fin 3 → ℝ}
    (hβ : ∀ i, timeDerivative (along Q α (partialDerivation (αIndex i) S)) = 0)
    (hnd : ∀ w : Fin 3 → TimeFunction,
      (∀ i, ∑ k, along Q α (partialDerivation (αIndex i) (partialDerivation (qIndex k) S)) *
        w k = 0) → ∀ k, w k = 0) :
    (∀ i, timeDerivative (Q i) = momentum S Q α i) ∧
      ∀ i, timeDerivative (timeDerivative (Q i)) = algebraMap ℝ TimeFunction (1 / 2) *
        FreeSmoothRing.lift Q (partialDerivation i nsq) := by
  have h := isTrajectory_of_isHamiltonJacobi hS hβ hnd
  have h' := (isTrajectory_rayHamiltonian_iff nsq _).mp h
  refine ⟨fun i => h'.1 i, fun i => ?_⟩
  have e := timeDerivative_timeDerivative_of_isTrajectory h i
  simpa using e

/-! ### Complete integrals -/

/-- The time `σ` along the rays, as a function of `(q, α, σ)`. -/
def rayTime : ActionSpace (Fin 3) := generator tIndex

/-- The co-ordinate `qᵢ`, as a function of `(q, α, σ)`. -/
def rayPosition (i : Fin 3) : ActionSpace (Fin 3) := generator (qIndex i)

/-- The time does not depend on the positions. -/
theorem partialDerivation_q_rayTime (k : Fin 3) : partialDerivation (qIndex k) rayTime = 0 :=
  partialDerivation_generator_of_ne (by simp)

/-- The time does not depend on the parameters. -/
theorem partialDerivation_α_rayTime (k : Fin 3) : partialDerivation (αIndex k) rayTime = 0 :=
  partialDerivation_generator_of_ne (by simp)

/-- `∂σ/∂σ = 1`. -/
theorem partialDerivation_t_rayTime :
    partialDerivation (tIndex : Fin 3 ⊕ Fin 3 ⊕ Unit) rayTime = 1 :=
  partialDerivation_generator_self _

/-- `∂qᵢ/∂qₖ = δᵢₖ`. -/
theorem partialDerivation_q_rayPosition (k i : Fin 3) :
    partialDerivation (qIndex k) (rayPosition i) = if i = k then 1 else 0 := by
  rw [rayPosition, partialDerivation_generator]
  simp

/-- The positions do not depend on the parameters. -/
theorem partialDerivation_α_rayPosition (k i : Fin 3) :
    partialDerivation (αIndex k) (rayPosition i) = 0 :=
  partialDerivation_generator_of_ne (by simp)

/-- The positions do not depend on the time. -/
theorem partialDerivation_t_rayPosition (i : Fin 3) :
    partialDerivation (tIndex : Fin 3 ⊕ Fin 3 ⊕ Unit) (rayPosition i) = 0 :=
  partialDerivation_generator_of_ne (by simp)

/-- The parameters do not depend on the positions. -/
theorem partialDerivation_q_parameter (k i : Fin 3) :
    partialDerivation (qIndex k) (parameter i) = 0 :=
  partialDerivation_generator_of_ne (by simp)

/-- `∂αᵢ/∂αₖ = δᵢₖ`. -/
theorem partialDerivation_α_parameter (k i : Fin 3) :
    partialDerivation (αIndex k) (parameter i) = if i = k then 1 else 0 := by
  rw [parameter, partialDerivation_generator]
  simp

/-- The parameters do not depend on the time. -/
theorem partialDerivation_t_parameter (i : Fin 3) :
    partialDerivation (tIndex : Fin 3 ⊕ Fin 3 ⊕ Unit) (parameter i) = 0 :=
  partialDerivation_generator_of_ne (by simp)

/-- The squared index `n² = n₀² + 2 g z` of a medium with a linear gradient. -/
def linearIndexSq (n0sq g : ℝ) : FreeSmoothRing (Fin 3) :=
  algebraMap ℝ (FreeSmoothRing (Fin 3)) n0sq +
    algebraMap ℝ (FreeSmoothRing (Fin 3)) (2 * g) * generator 2

/-- The complete integral `S = α · q − (|α|² − n²) σ / 2` of a homogeneous medium. -/
def constantIndexAction (nsq : ℝ) : ActionSpace (Fin 3) :=
  ∑ i, parameter i * rayPosition i -
    algebraMap ℝ (ActionSpace (Fin 3)) (1 / 2) *
      (∑ i, parameter i * parameter i - algebraMap ℝ (ActionSpace (Fin 3)) nsq) * rayTime

/-- The complete integral
`S = α · q + g σ z − (|α|² − n₀²) σ/2 − g α₃ σ²/2 − g² σ³/6` of the linear gradient. -/
def linearIndexAction (n0sq g : ℝ) : ActionSpace (Fin 3) :=
  constantIndexAction n0sq + algebraMap ℝ (ActionSpace (Fin 3)) g * (rayTime * rayPosition 2) -
    algebraMap ℝ (ActionSpace (Fin 3)) (1 / 2) * algebraMap ℝ (ActionSpace (Fin 3)) g *
      (parameter 2 * (rayTime * rayTime)) -
    algebraMap ℝ (ActionSpace (Fin 3)) (1 / 2) * algebraMap ℝ (ActionSpace (Fin 3)) (1 / 3) *
      (algebraMap ℝ (ActionSpace (Fin 3)) g * algebraMap ℝ (ActionSpace (Fin 3)) g) *
      (rayTime * (rayTime * rayTime))

/-- The momenta of the complete integral of the linear gradient: `∂S/∂qₖ = αₖ + δₖ₃ g σ`. -/
theorem partialDerivation_q_linearIndexAction (n0sq g : ℝ) (k : Fin 3) :
    partialDerivation (qIndex k) (linearIndexAction n0sq g) =
      parameter k + if k = 2 then algebraMap ℝ (ActionSpace (Fin 3)) g * rayTime else 0 := by
  simp only [linearIndexAction, constantIndexAction, map_add, map_sub, map_sum,
    SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap, partialDerivation_q_rayTime,
    partialDerivation_q_rayPosition, partialDerivation_q_parameter, smul_eq_mul]
  by_cases hk : k = 2
  · subst hk
    simp [Finset.sum_ite_eq']
  · simp [hk, Ne.symm hk, Finset.sum_ite_eq']

/-- `∂S/∂σ` of the complete integral of the linear gradient. -/
theorem partialDerivation_t_linearIndexAction (n0sq g : ℝ) :
    partialDerivation (tIndex : Fin 3 ⊕ Fin 3 ⊕ Unit) (linearIndexAction n0sq g) =
      algebraMap ℝ (ActionSpace (Fin 3)) g * rayPosition 2 -
        algebraMap ℝ (ActionSpace (Fin 3)) (1 / 2) *
          (∑ i, parameter i * parameter i - algebraMap ℝ (ActionSpace (Fin 3)) n0sq) -
        algebraMap ℝ (ActionSpace (Fin 3)) (1 / 2) * algebraMap ℝ (ActionSpace (Fin 3)) g *
          (parameter 2 * (rayTime + rayTime)) -
        algebraMap ℝ (ActionSpace (Fin 3)) (1 / 2) * algebraMap ℝ (ActionSpace (Fin 3)) (1 / 3) *
          (algebraMap ℝ (ActionSpace (Fin 3)) g * algebraMap ℝ (ActionSpace (Fin 3)) g) *
          (3 * (rayTime * rayTime)) := by
  simp only [linearIndexAction, constantIndexAction, map_add, map_sub, map_sum,
    SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap, partialDerivation_t_rayTime,
    partialDerivation_t_rayPosition, partialDerivation_t_parameter, smul_eq_mul]
  simp
  ring

/-- `∂S/∂αₖ = qₖ − αₖ σ − δₖ₃ g σ²/2` for the linear gradient. -/
theorem partialDerivation_α_linearIndexAction (n0sq g : ℝ) (k : Fin 3) :
    partialDerivation (αIndex k) (linearIndexAction n0sq g) =
      rayPosition k -
        algebraMap ℝ (ActionSpace (Fin 3)) (1 / 2) * (parameter k + parameter k) * rayTime -
        if k = 2 then algebraMap ℝ (ActionSpace (Fin 3)) (1 / 2) *
          algebraMap ℝ (ActionSpace (Fin 3)) g * (rayTime * rayTime) else 0 := by
  simp only [linearIndexAction, constantIndexAction, map_add, map_sub, map_sum,
    SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap, partialDerivation_α_rayTime,
    partialDerivation_α_rayPosition, partialDerivation_α_parameter, smul_eq_mul]
  fin_cases k <;> simp [Fin.sum_univ_three] <;> ring

/-- **The linear gradient**: `S` solves the Hamilton–Jacobi equation
`∂S/∂σ + (|∇S|² − n₀² − 2 g z)/2 = 0`. -/
theorem isHamiltonJacobi_linearIndex (n0sq g : ℝ) :
    IsHamiltonJacobi (rayHamiltonian (linearIndexSq n0sq g)) (linearIndexAction n0sq g) := by
  have e1 : algebraMap ℝ (ActionSpace (Fin 3)) (1 / 2) * algebraMap ℝ (ActionSpace (Fin 3)) (2 * g)
      = algebraMap ℝ (ActionSpace (Fin 3)) g := by
    rw [← map_mul]
    congr 1
    ring
  have e2 : (3 : ActionSpace (Fin 3)) * algebraMap ℝ (ActionSpace (Fin 3)) (1 / 3) = 1 := by
    rw [← map_ofNat (algebraMap ℝ (ActionSpace (Fin 3))) 3, ← map_mul]
    norm_num
  have hpos : positionsToAction (Fin 3) (generator 2) = rayPosition 2 := by
    rw [positionsToAction, lift_generator]
    rfl
  rw [IsHamiltonJacobi, partialDerivation_t_linearIndexAction, rayHamiltonian,
    SmoothRingHom.map_add, substitution_positionsToPhase, kineticEnergy, SmoothRingHom.map_sum]
  simp only [SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, substitution_p,
    partialDerivation_q_linearIndexAction, linearIndexSq, SmoothRingHom.map_neg,
    SmoothRingHom.map_add, hpos, Fin.sum_univ_three, inv_one]
  simp only [show ((0 : Fin 3) = 2) = False by decide, show ((1 : Fin 3) = 2) = False by decide,
    ↓reduceIte, add_zero]
  linear_combination (-rayPosition 2) * e1 +
    (-(algebraMap ℝ (ActionSpace (Fin 3)) (1 / 2) * algebraMap ℝ (ActionSpace (Fin 3)) g *
      algebraMap ℝ (ActionSpace (Fin 3)) g * (rayTime * rayTime))) * e2

/-- The ray `qₖ(σ) = βₖ + αₖ σ + δₖ₃ g σ²/2` of the linear gradient. -/
def linearIndexRay (g : ℝ) (α β : Fin 3 → ℝ) (k : Fin 3) : TimeFunction :=
  algebraMap ℝ TimeFunction (β k) + algebraMap ℝ TimeFunction (α k) * TimeFunction.time +
    if k = 2 then algebraMap ℝ TimeFunction (g / 2) * (TimeFunction.time * TimeFunction.time)
    else 0

/-- Along a curve the position `qₖ` is the curve. -/
theorem along_rayPosition (Q : Fin 3 → TimeFunction) (α : Fin 3 → ℝ) (k : Fin 3) :
    along Q α (rayPosition k) = Q k := by
  rw [rayPosition, along, lift_generator]
  rfl

/-- Along a curve with fixed parameters `αₖ` is a constant. -/
theorem along_parameter (Q : Fin 3 → TimeFunction) (α : Fin 3 → ℝ) (k : Fin 3) :
    along Q α (parameter k) = algebraMap ℝ TimeFunction (α k) := by
  rw [parameter, along, lift_generator]
  rfl

/-- Along a curve the time is the time. -/
theorem along_rayTime (Q : Fin 3 → TimeFunction) (α : Fin 3 → ℝ) :
    along Q α rayTime = TimeFunction.time := by
  rw [rayTime, along, lift_generator]
  rfl

/-- Along the ray the derivatives `∂S/∂αₖ` are the constants `βₖ`. -/
theorem along_partialDerivation_α_linearIndexAction (n0sq g : ℝ) (α β : Fin 3 → ℝ) (k : Fin 3) :
    along (linearIndexRay g α β) α (partialDerivation (αIndex k) (linearIndexAction n0sq g)) =
      algebraMap ℝ TimeFunction (β k) := by
  have r1 : algebraMap ℝ TimeFunction (1 / 2) *
      (algebraMap ℝ TimeFunction (α k) + algebraMap ℝ TimeFunction (α k)) =
      algebraMap ℝ TimeFunction (α k) := by
    rw [← map_add, ← map_mul]
    congr 1
    ring
  have r2 : algebraMap ℝ TimeFunction (1 / 2) * algebraMap ℝ TimeFunction g =
      algebraMap ℝ TimeFunction (g / 2) := by
    rw [← map_mul]
    congr 1
    ring
  rw [partialDerivation_α_linearIndexAction]
  by_cases hk : k = 2
  · subst hk
    simp only [↓reduceIte, SmoothRingHom.map_sub, SmoothRingHom.map_mul,
      SmoothRingHom.map_add, SmoothRingHom.map_algebraMap, along_rayPosition, along_parameter,
      along_rayTime, linearIndexRay]
    linear_combination (-TimeFunction.time) * r1 +
      (-(TimeFunction.time * TimeFunction.time)) * r2
  · simp only [hk, ↓reduceIte, SmoothRingHom.map_sub, SmoothRingHom.map_mul,
      SmoothRingHom.map_add, SmoothRingHom.map_algebraMap,
      along_rayPosition, along_parameter, along_rayTime, linearIndexRay, add_zero, sub_zero]
    linear_combination (-TimeFunction.time) * r1

/-- The matrix `∂²S/∂αᵢ∂qₖ` of the complete integral is the identity. -/
theorem partialDerivation_α_q_linearIndexAction (n0sq g : ℝ) (i k : Fin 3) :
    partialDerivation (αIndex i) (partialDerivation (qIndex k) (linearIndexAction n0sq g)) =
      if k = i then 1 else 0 := by
  rw [partialDerivation_q_linearIndexAction]
  split_ifs with h1 h2 h2 <;>
    simp [SmoothDerivation.map_algebraMap_mul, partialDerivation_α_rayTime,
      partialDerivation_α_parameter, h2]

/-- **The rays of the linear gradient**: by Jacobi's theorem the parabolae
`qₖ(σ) = βₖ + αₖ σ + δₖ₃ g σ²/2`, with the momenta `∂S/∂q`, are trajectories of the ray
Hamiltonian `(|p|² − n₀² − 2 g z)/2`. -/
theorem isTrajectory_linearIndexRay (n0sq g : ℝ) (α β : Fin 3 → ℝ) :
    IsTrajectory (canonical (Fin 3)) (rayHamiltonian (linearIndexSq n0sq g))
      (Sum.elim (linearIndexRay g α β)
        (momentum (linearIndexAction n0sq g) (linearIndexRay g α β) α)) := by
  refine isTrajectory_of_isHamiltonJacobi (isHamiltonJacobi_linearIndex n0sq g) (fun i => ?_)
    (fun w hw k => ?_)
  · rw [along_partialDerivation_α_linearIndexAction, SmoothDerivation.map_algebraMap]
  · have h := hw k
    simp only [partialDerivation_α_q_linearIndexAction, apply_ite (along (linearIndexRay g α β) α),
      SmoothRingHom.map_one, SmoothRingHom.map_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h
    exact h

/-- `∂ᵢ(n₀² + 2 g z) = 2 g δᵢ₃`. -/
theorem partialDerivation_linearIndexSq (n0sq g : ℝ) (i : Fin 3) :
    partialDerivation i (linearIndexSq n0sq g) =
      if i = 2 then algebraMap ℝ (FreeSmoothRing (Fin 3)) (2 * g) else 0 := by
  rw [linearIndexSq, map_add, SmoothDerivation.map_algebraMap, zero_add,
    SmoothDerivation.map_algebraMap_mul, partialDerivation_generator]
  split_ifs with h1 h2 h2
  · simp
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

/-- Along the rays of the linear gradient, `q̈ = ½ ∇n² = g e₃`. -/
theorem timeDerivative_timeDerivative_linearIndexRay (n0sq g : ℝ) (α β : Fin 3 → ℝ)
    (i : Fin 3) :
    timeDerivative (timeDerivative (linearIndexRay g α β i)) =
      if i = 2 then algebraMap ℝ TimeFunction g else 0 := by
  have h := timeDerivative_timeDerivative_of_isTrajectory
    (isTrajectory_linearIndexRay n0sq g α β) i
  simp only [Sum.elim_inl] at h
  rw [h, partialDerivation_linearIndexSq]
  split_ifs
  · rw [SmoothRingHom.map_algebraMap, ← map_mul]
    congr 1
    ring
  · rw [SmoothRingHom.map_zero, mul_zero]

/-- The squared index `n₀² + 2 g z` with `g = 0` is constant. -/
theorem linearIndexSq_zero (nsq : ℝ) :
    linearIndexSq nsq 0 = algebraMap ℝ (FreeSmoothRing (Fin 3)) nsq := by
  simp [linearIndexSq]

/-- The complete integral of the linear gradient with `g = 0` is that of a homogeneous medium. -/
theorem linearIndexAction_zero (nsq : ℝ) : linearIndexAction nsq 0 = constantIndexAction nsq := by
  simp [linearIndexAction]

/-- **A homogeneous medium**: `S = α · q − (|α|² − n²) σ / 2` solves the Hamilton–Jacobi
equation `∂S/∂σ + (|∇S|² − n²)/2 = 0`. -/
theorem isHamiltonJacobi_constantIndex (nsq : ℝ) :
    IsHamiltonJacobi (rayHamiltonian (algebraMap ℝ (FreeSmoothRing (Fin 3)) nsq))
      (constantIndexAction nsq) := by
  rw [← linearIndexSq_zero, ← linearIndexAction_zero]
  exact isHamiltonJacobi_linearIndex nsq 0

/-- The straight ray `qₖ(σ) = βₖ + αₖ σ`. -/
def constantIndexRay (α β : Fin 3 → ℝ) (k : Fin 3) : TimeFunction :=
  algebraMap ℝ TimeFunction (β k) + algebraMap ℝ TimeFunction (α k) * TimeFunction.time

/-- The rays of the linear gradient with `g = 0` are straight. -/
theorem linearIndexRay_zero (α β : Fin 3 → ℝ) : linearIndexRay 0 α β = constantIndexRay α β := by
  funext k
  simp [linearIndexRay, constantIndexRay]

/-- **The rays of a homogeneous medium** are the straight lines `q = β + α σ`, trajectories of
`(|p|² − n²)/2` by Jacobi's theorem. -/
theorem isTrajectory_constantIndexRay (nsq : ℝ) (α β : Fin 3 → ℝ) :
    IsTrajectory (canonical (Fin 3)) (rayHamiltonian (algebraMap ℝ (FreeSmoothRing (Fin 3)) nsq))
      (Sum.elim (constantIndexRay α β)
        (momentum (constantIndexAction nsq) (constantIndexRay α β) α)) := by
  have h := isTrajectory_linearIndexRay nsq 0 α β
  rwa [linearIndexSq_zero, linearIndexAction_zero, linearIndexRay_zero] at h

/-! ### Fermat's principle -/

/-- The kinetic term `T(q, v) = |v|²/2` of the rays. -/
def rayKinetic (z : E3 × E3) : ℝ := ‖z.2‖ ^ 2 / 2

/-- The potential `U = −n²/2` of the rays. -/
def rayPotential (n : E3 → ℝ) (x : E3) : ℝ := -(n x ^ 2 / 2)

/-- The Lagrangian `n(q) |q′|` of the optical length. -/
def opticalLagrangian (n : E3 → ℝ) : Lagrangian E3 := fun _ z => n z.1 * ‖z.2‖

/-- The action of the optical Lagrangian is the optical length. -/
theorem action_opticalLagrangian (n : E3 → ℝ) (γ : ℝ → E3) (a b : ℝ) :
    action a b (opticalLagrangian n) γ = opticalLength n γ a b := rfl

/-- The optical length is stationary for all variations with fixed ends. -/
def OpticalStationary (n : E3 → ℝ) (a b : ℝ) (γ : ℝ → E3) : Prop :=
  ∀ η : ℝ → E3, FixedEndpointVariation a b η →
    HasDerivAt (fun s => opticalLength n (Variational.perturb γ η s) a b) 0 0

/-- Stationarity of the optical length is stationarity of the optical Lagrangian. -/
theorem opticalStationary_iff (n : E3 → ℝ) (a b : ℝ) (γ : ℝ → E3) :
    OpticalStationary n a b γ ↔ Stationary a b (opticalLagrangian n) γ := Iff.rfl

/-- For `n ≥ 0`, the Jacobi length `2 √((0 − U) T)` with `T = |v|²/2` and `U = −n²/2` is the
optical Lagrangian `n |v|`. -/
theorem jacobiLength_eq_opticalLagrangian {n : E3 → ℝ} (hn : ∀ x, 0 ≤ n x) :
    Maupertuis.jacobiLength rayKinetic (rayPotential n) 0 = opticalLagrangian n := by
  funext t z
  have h : Maupertuis.radicand rayKinetic (rayPotential n) 0 z = (n z.1 * ‖z.2‖ / 2) ^ 2 := by
    simp only [Maupertuis.radicand, rayKinetic, rayPotential]
    ring
  rw [Maupertuis.jacobiLength, h, Real.sqrt_sq (by have := hn z.1; positivity)]
  simp only [opticalLagrangian]
  ring

/-- `|v|²/2` is smooth. -/
theorem contDiff_rayKinetic : ContDiff ℝ 2 rayKinetic :=
  ((contDiff_norm_sq ℝ).comp contDiff_snd).div_const 2

/-- `−n²/2` is `C²` for a `C²` index. -/
theorem contDiff_rayPotential {n : E3 → ℝ} (hn : ContDiff ℝ 2 n) : ContDiff ℝ 2 (rayPotential n) :=
  ((hn.pow 2).div_const 2).neg

/-- The equation of Euler–Lagrange of `T − U = |q′|²/2 + n²/2` is the ray equation
`q″ = ∇(n²/2)`. -/
theorem eulerLagrange_ray_eq_zero_iff {n : E3 → ℝ} (hn : ContDiff ℝ 2 n) {γ : ℝ → E3}
    (hγ : ContDiff ℝ 2 γ) (t : ℝ) :
    eulerLagrange (Maupertuis.naturalLagrangian rayKinetic (rayPotential n)) γ t = 0 ↔
      deriv (deriv γ) t = gradient (fun x => n x ^ 2 / 2) (γ t) := by
  have hT : ∀ z : E3 × E3, HasFDerivAt rayKinetic
      ((innerSL ℝ z.2).comp (ContinuousLinearMap.snd ℝ E3 E3)) z := fun z => by
    have h := ((hasStrictFDerivAt_norm_sq z.2).hasFDerivAt.comp z hasFDerivAt_snd).mul_const
      (1 / 2 : ℝ)
    have e : rayKinetic = fun y : E3 × E3 => ((fun x : E3 => ‖x‖ ^ 2) ∘ Prod.snd) y * (1 / 2) := by
      funext y
      simp only [rayKinetic, Function.comp_apply]
      ring
    rw [e]
    refine h.congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
    simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply, smul_eq_mul,
      innerSL_apply_apply, ContinuousLinearMap.coe_snd']
    ring
  have hU : ∀ x, HasFDerivAt (rayPotential n) (-fderiv ℝ (fun y => n y ^ 2 / 2) x) x := fun x =>
    (((hn.pow 2).div_const 2).differentiable (by norm_num) x).hasFDerivAt.fun_neg
  have hL : ∀ s, fderiv ℝ (Maupertuis.naturalLagrangian rayKinetic (rayPotential n) s)
      (γ s, deriv γ s) = (innerSL ℝ (deriv γ s)).comp (ContinuousLinearMap.snd ℝ E3 E3) +
        (fderiv ℝ (fun y => n y ^ 2 / 2) (γ s)).comp (ContinuousLinearMap.fst ℝ E3 E3) := by
    intro s
    rw [(Maupertuis.hasFDerivAt_naturalLagrangian (hT (γ s, deriv γ s)) (hU (γ s)) s).fderiv]
    ext w <;> simp
  have hp : Mechanics.momentum (Maupertuis.naturalLagrangian rayKinetic (rayPotential n)) γ =
      fun s => innerSL ℝ (deriv γ s) := by
    funext s
    rw [Mechanics.momentum, hL]
    ext w
    simp
  have hf : force (Maupertuis.naturalLagrangian rayKinetic (rayPotential n)) γ t =
      fderiv ℝ (fun y => n y ^ 2 / 2) (γ t) := by
    rw [force, hL]
    ext w
    simp
  have hd : HasDerivAt (fun s => innerSL ℝ (deriv γ s)) (innerSL ℝ (deriv (deriv γ) t)) t := by
    have hγ' : DifferentiableAt ℝ (deriv γ) t := hγ.differentiable_deriv_two t
    exact (innerSL ℝ).hasFDerivAt.comp_hasDerivAt t hγ'.hasDerivAt
  have e : ∀ v : E3, innerSL ℝ v = InnerProductSpace.toDual ℝ E3 v := fun v => by
    ext w
    simp [InnerProductSpace.toDual_apply_apply]
  rw [eulerLagrange, hf, hp, hd.deriv, sub_eq_zero, gradient]
  constructor
  · intro h
    rw [h, e, LinearIsometryEquiv.symm_apply_apply]
  · intro h
    rw [h, e, LinearIsometryEquiv.apply_symm_apply]

/-- **Fermat's principle** (Landau–Lifshitz §53): in a medium of positive index `n` of class
`C²`, a `C²` path parametrized so that `|γ′| = n(γ)` makes the optical length
`∫ n(γ) |γ′| dt` stationary for all variations with fixed ends if and only if it satisfies the
ray equation `γ″ = ∇(n²/2)`. The optical Lagrangian is the Jacobi length `2 √((E − U) T)` with
`T = |q′|²/2`, `U = −n²/2` and `E = 0`, and the condition `|γ′| = n(γ)` is the energy
`T + U = E`. -/
theorem fermat {n : E3 → ℝ} (hn : ContDiff ℝ 2 n) (hpos : ∀ x, 0 < n x) {γ : ℝ → E3}
    (hγ : ContDiff ℝ 2 γ) {a b : ℝ} (hab : a < b)
    (hE : ∀ t ∈ Icc a b, ‖deriv γ t‖ = n (γ t)) :
    OpticalStationary n a b γ ↔
      ∀ t ∈ Ioo a b, deriv (deriv γ) t = gradient (fun x => n x ^ 2 / 2) (γ t) := by
  rw [opticalStationary_iff, ← jacobiLength_eq_opticalLagrangian fun x => (hpos x).le,
    Maupertuis.stationary_jacobiLength_iff hab contDiff_rayKinetic (contDiff_rayPotential hn) hγ
      fun t ht => ⟨?_, ?_⟩]
  · exact forall₂_congr fun t _ => eulerLagrange_ray_eq_zero_iff hn hγ t
  · simp only [rayKinetic, rayPotential, hE t ht]
    ring
  · have := hpos (γ t)
    simp only [rayPotential]
    nlinarith

/-- An instance of Fermat's principle: in a homogeneous medium of index `n₀ > 0` the straight
path `t ↦ x₀ + t v` with `|v| = n₀` makes the optical length stationary. -/
theorem opticalStationary_line {n₀ : ℝ} (hn₀ : 0 < n₀) (x₀ v : E3) (hv : ‖v‖ = n₀) {a b : ℝ}
    (hab : a < b) : OpticalStationary (fun _ => n₀) a b fun t => x₀ + t • v := by
  have hd : ∀ t, deriv (fun t : ℝ => x₀ + t • v) t = v := fun t => by
    have h := ((hasDerivAt_id t).smul_const v).const_add x₀
    rw [one_smul] at h
    exact h.deriv
  have hd' : deriv (fun t : ℝ => x₀ + t • v) = fun _ => v := funext hd
  have hγ : ContDiff ℝ 2 fun t : ℝ => x₀ + t • v :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  refine (fermat (γ := fun t => x₀ + t • v) contDiff_const (fun _ => hn₀) hγ hab
    (fun t _ => by rw [hd, hv])).mpr fun t _ => ?_
  rw [hd', deriv_const]
  simp [gradient]

end ProjectAinos.Electrodynamics.Optics.RayOptics
