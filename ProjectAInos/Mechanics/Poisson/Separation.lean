/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Poisson.CompleteIntegral
public import ProjectAInos.Mechanics.Legendre
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Separation of the variables

Landau–Lifshitz §48. A Hamiltonian of Stäckel's form is
`H = Σᵢ Ψᵢ(q) (gᵢ(q) pᵢ²/2m + uᵢ(q))`, where the functions `Ψᵢ` are a row of
the inverse of a matrix `Φ`: `Σᵢ Ψᵢ Φᵢⱼ = δⱼ,ⱼ₀`. If the derivatives of `S`
satisfy the separated equations

`gᵢ (∂S/∂qᵢ)²/2m + uᵢ = Σⱼ Φᵢⱼ αⱼ`, `∂S/∂t = −αⱼ₀`,

then `S` satisfies the Hamilton–Jacobi equation (`isHamiltonJacobi_stackel`).

Two cases on three co-ordinates cover the separable systems of §48:

* `isHamiltonJacobi_nested`: `H = p₀²/2m + a + ρ (p₁²/2m + b + σ (p₂²/2m + c))`,
  the form of the Hamiltonian in spherical co-ordinates, with `ρ = 1/r²` and
  `σ = 1/sin²θ`;
* `isHamiltonJacobi_liouville`:
  `H = λ (g₀ p₀²/2m + u₀ + g₁ p₁²/2m + u₁ + (κ₀ + κ₁)(p₂²/2m + u₂))` with
  `λ (w₀ + w₁) = 1`, the form in parabolic and in elliptic co-ordinates.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.CompleteIntegral

open SmoothAlgebra SmoothRing FreeSmoothRing Matrix

variable {ι : Type*} [DecidableEq ι]

variable (ι) in
/-- A function of the co-ordinates, as a function of `(q, α, t)`. The index
type is explicit, so that the coercion to a function is resolved with the type
known. -/
def positionsToAction : SmoothRingHom (FreeSmoothRing ι) (ActionSpace ι) :=
  FreeSmoothRing.lift fun i => generator (qIndex i)

/-- The parameter `αᵢ`. -/
def parameter (i : ι) : ActionSpace ι := generator (αIndex i)

theorem substitution_p (S : ActionSpace ι) (i : ι) :
    substitution S (PhaseSpace.p i) = partialDerivation (qIndex i) S := by
  rw [substitution, PhaseSpace.p, lift_generator, Sum.elim_inr]

/-- The substitution `pᵢ = ∂S/∂qᵢ` does not change a function of the
co-ordinates. -/
theorem substitution_positionsToPhase (S : ActionSpace ι) (u : FreeSmoothRing ι) :
    substitution S (positionsToPhase (ι := ι) u) = positionsToAction ι u := by
  have h : (substitution S).comp (positionsToPhase (ι := ι)) = positionsToAction ι :=
    FreeSmoothRing.hom_ext fun i => by
      rw [SmoothRingHom.comp_apply, positionsToPhase, positionsToAction, lift_generator,
        lift_generator, substitution, PhaseSpace.q, lift_generator, Sum.elim_inl]
  exact congrArg (fun φ : SmoothRingHom (FreeSmoothRing ι) (ActionSpace ι) => φ u) h

variable [Fintype ι]

/-- A Hamiltonian of Stäckel's form: `Σᵢ Ψᵢ(q) (gᵢ(q) pᵢ²/2m + uᵢ(q))`. -/
def stackelHamiltonian (m : ℝ) (Ψ g u : ι → FreeSmoothRing ι) : PhaseSpace ι :=
  ∑ i, positionsToPhase (ι := ι) (Ψ i) *
    (algebraMap ℝ (PhaseSpace ι) (1 / (2 * m)) *
      (positionsToPhase (ι := ι) (g i) * (PhaseSpace.p i * PhaseSpace.p i)) +
        positionsToPhase (ι := ι) (u i))

theorem substitution_stackelHamiltonian (m : ℝ) (Ψ g u : ι → FreeSmoothRing ι)
    (S : ActionSpace ι) :
    substitution S (stackelHamiltonian m Ψ g u) =
      ∑ i, positionsToAction ι (Ψ i) *
        (algebraMap ℝ (ActionSpace ι) (1 / (2 * m)) *
          (positionsToAction ι (g i) *
            (partialDerivation (qIndex i) S * partialDerivation (qIndex i) S)) +
          positionsToAction ι (u i)) := by
  rw [stackelHamiltonian, SmoothRingHom.map_sum]
  simp only [SmoothRingHom.map_mul, SmoothRingHom.map_add, SmoothRingHom.map_algebraMap,
    substitution_positionsToPhase, substitution_p]

omit [DecidableEq ι] in
theorem sum_positionsToAction_mul (a b : ι → FreeSmoothRing ι) :
    ∑ i, positionsToAction ι (a i) * positionsToAction ι (b i) =
      positionsToAction ι (∑ i, a i * b i) := by
  rw [SmoothRingHom.map_sum]
  exact Finset.sum_congr rfl fun i _ => (SmoothRingHom.map_mul _ _ _).symm

theorem sum_positionsToAction_mul_eq_ite {Ψ : ι → FreeSmoothRing ι}
    {Φ : Matrix ι ι (FreeSmoothRing ι)} {j₀ : ι}
    (hΨ : ∀ j, ∑ i, Ψ i * Φ i j = if j = j₀ then 1 else 0) (j : ι) :
    ∑ i, positionsToAction ι (Ψ i) * positionsToAction ι (Φ i j) = if j = j₀ then 1 else 0 := by
  rw [sum_positionsToAction_mul Ψ fun i => Φ i j, hΨ j]
  split_ifs
  · rw [SmoothRingHom.map_one]
  · rw [SmoothRingHom.map_zero]

/-- Stäckel's theorem, in the direction of verification: an action whose
derivatives satisfy the separated equations is a solution of the
Hamilton–Jacobi equation. -/
theorem isHamiltonJacobi_stackel {m : ℝ} {Ψ g u : ι → FreeSmoothRing ι}
    {Φ : Matrix ι ι (FreeSmoothRing ι)} {j₀ : ι}
    (hΨ : ∀ j, ∑ i, Ψ i * Φ i j = if j = j₀ then 1 else 0) {S : ActionSpace ι}
    (hS : ∀ i, algebraMap ℝ (ActionSpace ι) (1 / (2 * m)) *
        (positionsToAction ι (g i) *
          (partialDerivation (qIndex i) S * partialDerivation (qIndex i) S)) +
        positionsToAction ι (u i) = ∑ j, positionsToAction ι (Φ i j) * parameter j)
    (ht : partialDerivation tIndex S = -parameter j₀) :
    IsHamiltonJacobi (stackelHamiltonian m Ψ g u) S := by
  rw [IsHamiltonJacobi, ht, substitution_stackelHamiltonian]
  simp only [hS, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← Finset.sum_mul, sum_positionsToAction_mul_eq_ite hΨ, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact neg_add_cancel _

/-! ### The nested form: spherical co-ordinates -/

/-- The Hamiltonian `p₀²/2m + a + ρ (p₁²/2m + b + σ (p₂²/2m + c))`. In
spherical co-ordinates `(r, θ, φ)` the Hamiltonian of a particle in the field
`a(r) + b(θ)/r² + c(φ)/(r² sin²θ)` has this form with `ρ = 1/r²` and
`σ = 1/sin²θ` (Landau–Lifshitz (48.8)). -/
def nestedHamiltonian (m : ℝ) (ρ σ a b c : FreeSmoothRing (Fin 3)) : PhaseSpace (Fin 3) :=
  stackelHamiltonian m ![1, ρ, ρ * σ] ![1, 1, 1] ![a, b, c]

/-- The matrix of Stäckel for the nested form. -/
def nestedMatrix (ρ σ : FreeSmoothRing (Fin 3)) : Matrix (Fin 3) (Fin 3) (FreeSmoothRing (Fin 3)) :=
  !![1, -ρ, 0; 0, 1, -σ; 0, 0, 1]

theorem sum_mul_nestedMatrix (ρ σ : FreeSmoothRing (Fin 3)) (j : Fin 3) :
    ∑ i, (![1, ρ, ρ * σ] : Fin 3 → FreeSmoothRing (Fin 3)) i * nestedMatrix ρ σ i j =
      if j = 0 then 1 else 0 := by
  rw [Fin.sum_univ_three]
  fin_cases j
  · change 1 * 1 + ρ * 0 + ρ * σ * 0 = 1
    ring
  · change 1 * -ρ + ρ * 1 + ρ * σ * 0 = 0
    ring
  · change 1 * 0 + ρ * -σ + ρ * σ * 1 = 0
    ring

/-- Separation of the variables for the nested form: the equations
`p₀²/2m + a = E − ρ β`, `p₁²/2m + b = β − σ γ`, `p₂²/2m + c = γ` for the
derivatives of the action give a solution of the Hamilton–Jacobi equation
with the energy `E = α₀`. -/
theorem isHamiltonJacobi_nested {m : ℝ} {ρ σ a b c : FreeSmoothRing (Fin 3)}
    {S : ActionSpace (Fin 3)}
    (hS : ∀ i, algebraMap ℝ (ActionSpace (Fin 3)) (1 / (2 * m)) *
        (positionsToAction (Fin 3) ((![1, 1, 1] : Fin 3 → FreeSmoothRing (Fin 3)) i) *
          (partialDerivation (qIndex i) S * partialDerivation (qIndex i) S)) +
        positionsToAction (Fin 3) ((![a, b, c] : Fin 3 → FreeSmoothRing (Fin 3)) i) =
          ∑ j, positionsToAction (Fin 3) (nestedMatrix ρ σ i j) * parameter j)
    (ht : partialDerivation tIndex S = -parameter (0 : Fin 3)) :
    IsHamiltonJacobi (nestedHamiltonian m ρ σ a b c) S :=
  isHamiltonJacobi_stackel (sum_mul_nestedMatrix ρ σ) hS ht

/-- `(∂S/∂qᵢ)²/2m`. -/
def kinetic (m : ℝ) (S : ActionSpace (Fin 3)) (i : Fin 3) : ActionSpace (Fin 3) :=
  algebraMap ℝ (ActionSpace (Fin 3)) (1 / (2 * m)) *
    (partialDerivation (qIndex i) S * partialDerivation (qIndex i) S)

theorem stackel_row {m : ℝ} {S : ActionSpace (Fin 3)} {i : Fin 3}
    {gi ui x₀ x₁ x₂ : FreeSmoothRing (Fin 3)} {r : ActionSpace (Fin 3)}
    (hg : positionsToAction (Fin 3) gi * kinetic m S i + positionsToAction (Fin 3) ui = r)
    (hr : r = positionsToAction (Fin 3) x₀ * parameter (0 : Fin 3) +
      positionsToAction (Fin 3) x₁ * parameter (1 : Fin 3) +
      positionsToAction (Fin 3) x₂ * parameter (2 : Fin 3)) :
    algebraMap ℝ (ActionSpace (Fin 3)) (1 / (2 * m)) *
        (positionsToAction (Fin 3) gi *
          (partialDerivation (qIndex i) S * partialDerivation (qIndex i) S)) +
      positionsToAction (Fin 3) ui =
        positionsToAction (Fin 3) x₀ * parameter (0 : Fin 3) +
          positionsToAction (Fin 3) x₁ * parameter (1 : Fin 3) +
          positionsToAction (Fin 3) x₂ * parameter (2 : Fin 3) := by
  rw [← hr, ← hg, kinetic]
  ring

/-- Separation of the variables in the nested form, with the three separated
equations written out: `(∂S/∂q₀)²/2m + a = E − ρ β`,
`(∂S/∂q₁)²/2m + b = β − σ γ`, `(∂S/∂q₂)²/2m + c = γ`, where
`(E, β, γ) = (α₀, α₁, α₂)`. -/
theorem isHamiltonJacobi_nested_of_separated {m : ℝ} {ρ σ a b c : FreeSmoothRing (Fin 3)}
    {S : ActionSpace (Fin 3)}
    (h0 : kinetic m S 0 + positionsToAction (Fin 3) a =
      parameter (0 : Fin 3) - positionsToAction (Fin 3) ρ * parameter (1 : Fin 3))
    (h1 : kinetic m S 1 + positionsToAction (Fin 3) b =
      parameter (1 : Fin 3) - positionsToAction (Fin 3) σ * parameter (2 : Fin 3))
    (h2 : kinetic m S 2 + positionsToAction (Fin 3) c = parameter (2 : Fin 3))
    (ht : partialDerivation tIndex S = -parameter (0 : Fin 3)) :
    IsHamiltonJacobi (nestedHamiltonian m ρ σ a b c) S := by
  refine isHamiltonJacobi_nested (fun i => ?_) ht
  rw [Fin.sum_univ_three]
  fin_cases i
  · exact stackel_row (gi := 1) (ui := a) (x₀ := 1) (x₁ := -ρ) (x₂ := 0)
      (r := parameter (0 : Fin 3) - positionsToAction (Fin 3) ρ * parameter (1 : Fin 3))
      (by rw [SmoothRingHom.map_one, one_mul]; exact h0)
      (by rw [SmoothRingHom.map_one, SmoothRingHom.map_neg, SmoothRingHom.map_zero]; ring)
  · exact stackel_row (gi := 1) (ui := b) (x₀ := 0) (x₁ := 1) (x₂ := -σ)
      (r := parameter (1 : Fin 3) - positionsToAction (Fin 3) σ * parameter (2 : Fin 3))
      (by rw [SmoothRingHom.map_one, one_mul]; exact h1)
      (by rw [SmoothRingHom.map_one, SmoothRingHom.map_neg, SmoothRingHom.map_zero]; ring)
  · exact stackel_row (gi := 1) (ui := c) (x₀ := 0) (x₁ := 0) (x₂ := 1)
      (r := parameter (2 : Fin 3))
      (by rw [SmoothRingHom.map_one, one_mul]; exact h2)
      (by rw [SmoothRingHom.map_one, SmoothRingHom.map_zero]; ring)

/-! ### The form of Liouville: parabolic and elliptic co-ordinates -/

/-- The Hamiltonian
`λ (g₀ p₀²/2m + u₀ + g₁ p₁²/2m + u₁ + (κ₀ + κ₁)(p₂²/2m + u₂))`. With
`λ (w₀ + w₁) = 1` this is the form of the Hamiltonian in parabolic
co-ordinates (`w = (ξ, η)`, `g = (4ξ, 4η)`, `κ = (1/ξ, 1/η)`) and in elliptic
co-ordinates (Landau–Lifshitz (48.15), (48.21)). -/
def liouvilleHamiltonian (m : ℝ) (lam g₀ g₁ κ₀ κ₁ u₀ u₁ u₂ : FreeSmoothRing (Fin 3)) :
    PhaseSpace (Fin 3) :=
  stackelHamiltonian m ![lam, lam, lam * (κ₀ + κ₁)] ![g₀, g₁, 1] ![u₀, u₁, u₂]

/-- The matrix of Stäckel for the form of Liouville. -/
def liouvilleMatrix (w₀ w₁ κ₀ κ₁ : FreeSmoothRing (Fin 3)) :
    Matrix (Fin 3) (Fin 3) (FreeSmoothRing (Fin 3)) :=
  !![w₀, 1, -κ₀; w₁, -1, -κ₁; 0, 0, 1]

theorem sum_mul_liouvilleMatrix {lam w₀ w₁ : FreeSmoothRing (Fin 3)} (h : lam * (w₀ + w₁) = 1)
    (κ₀ κ₁ : FreeSmoothRing (Fin 3)) (j : Fin 3) :
    ∑ i, (![lam, lam, lam * (κ₀ + κ₁)] : Fin 3 → FreeSmoothRing (Fin 3)) i *
        liouvilleMatrix w₀ w₁ κ₀ κ₁ i j = if j = 0 then 1 else 0 := by
  rw [Fin.sum_univ_three]
  fin_cases j
  · change lam * w₀ + lam * w₁ + lam * (κ₀ + κ₁) * 0 = 1
    linear_combination h
  · change lam * 1 + lam * -1 + lam * (κ₀ + κ₁) * 0 = 0
    ring
  · change lam * -κ₀ + lam * -κ₁ + lam * (κ₀ + κ₁) * 1 = 0
    ring

/-- Separation of the variables for the form of Liouville: the equations
`g₀ p₀²/2m + u₀ = E w₀ + β − κ₀ γ`, `g₁ p₁²/2m + u₁ = E w₁ − β − κ₁ γ`,
`p₂²/2m + u₂ = γ` for the derivatives of the action give a solution of the
Hamilton–Jacobi equation with the energy `E = α₀`. -/
theorem isHamiltonJacobi_liouville {m : ℝ} {lam w₀ w₁ g₀ g₁ κ₀ κ₁ u₀ u₁ u₂ : FreeSmoothRing (Fin 3)}
    (h : lam * (w₀ + w₁) = 1) {S : ActionSpace (Fin 3)}
    (hS : ∀ i, algebraMap ℝ (ActionSpace (Fin 3)) (1 / (2 * m)) *
        (positionsToAction (Fin 3) ((![g₀, g₁, 1] : Fin 3 → FreeSmoothRing (Fin 3)) i) *
          (partialDerivation (qIndex i) S * partialDerivation (qIndex i) S)) +
        positionsToAction (Fin 3) ((![u₀, u₁, u₂] : Fin 3 → FreeSmoothRing (Fin 3)) i) =
          ∑ j, positionsToAction (Fin 3) (liouvilleMatrix w₀ w₁ κ₀ κ₁ i j) * parameter j)
    (ht : partialDerivation tIndex S = -parameter (0 : Fin 3)) :
    IsHamiltonJacobi (liouvilleHamiltonian m lam g₀ g₁ κ₀ κ₁ u₀ u₁ u₂) S :=
  isHamiltonJacobi_stackel (sum_mul_liouvilleMatrix h κ₀ κ₁) hS ht

/-- Separation of the variables in the form of Liouville, with the three
separated equations written out: `g₀ (∂S/∂q₀)²/2m + u₀ = E w₀ + β − κ₀ γ`,
`g₁ (∂S/∂q₁)²/2m + u₁ = E w₁ − β − κ₁ γ`, `(∂S/∂q₂)²/2m + u₂ = γ`. -/
theorem isHamiltonJacobi_liouville_of_separated {m : ℝ}
    {lam w₀ w₁ g₀ g₁ κ₀ κ₁ u₀ u₁ u₂ : FreeSmoothRing (Fin 3)} (h : lam * (w₀ + w₁) = 1)
    {S : ActionSpace (Fin 3)}
    (h0 : positionsToAction (Fin 3) g₀ * kinetic m S 0 + positionsToAction (Fin 3) u₀ =
      positionsToAction (Fin 3) w₀ * parameter (0 : Fin 3) + parameter (1 : Fin 3) -
        positionsToAction (Fin 3) κ₀ * parameter (2 : Fin 3))
    (h1 : positionsToAction (Fin 3) g₁ * kinetic m S 1 + positionsToAction (Fin 3) u₁ =
      positionsToAction (Fin 3) w₁ * parameter (0 : Fin 3) - parameter (1 : Fin 3) -
        positionsToAction (Fin 3) κ₁ * parameter (2 : Fin 3))
    (h2 : kinetic m S 2 + positionsToAction (Fin 3) u₂ = parameter (2 : Fin 3))
    (ht : partialDerivation tIndex S = -parameter (0 : Fin 3)) :
    IsHamiltonJacobi (liouvilleHamiltonian m lam g₀ g₁ κ₀ κ₁ u₀ u₁ u₂) S := by
  refine isHamiltonJacobi_liouville h (fun i => ?_) ht
  rw [Fin.sum_univ_three]
  fin_cases i
  · exact stackel_row (gi := g₀) (ui := u₀) (x₀ := w₀) (x₁ := 1) (x₂ := -κ₀) h0
      (by rw [SmoothRingHom.map_one, SmoothRingHom.map_neg]; ring)
  · exact stackel_row (gi := g₁) (ui := u₁) (x₀ := w₁) (x₁ := -1) (x₂ := -κ₁) h1
      (by rw [SmoothRingHom.map_neg, SmoothRingHom.map_neg, SmoothRingHom.map_one]; ring)
  · exact stackel_row (gi := 1) (ui := u₂) (x₀ := 0) (x₁ := 0) (x₂ := 1)
      (r := parameter (2 : Fin 3))
      (by rw [SmoothRingHom.map_one, one_mul]; exact h2)
      (by rw [SmoothRingHom.map_one, SmoothRingHom.map_zero]; ring)

end ProjectAInos.Mechanics.CompleteIntegral
