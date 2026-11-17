/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Variational.IntervalParameter
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Separation of the variables for a Hamiltonian of Stäckel's form

Landau–Lifshitz §48 on an open box of co-ordinates, with real functions. A
`System` consists of a matrix `φ` whose entry `(i, j)` is a function of the
co-ordinate `qᵢ`, functions `gᵢ(qᵢ) > 0` and `uᵢ(qᵢ)`, and functions `Ψᵢ(q)`
with `Σᵢ Ψᵢ(q) φᵢⱼ(qᵢ) = δ_{j j₀}`. Its Hamiltonian is
`H = Σᵢ Ψᵢ(q) (gᵢ(qᵢ) pᵢ²/2 + uᵢ(qᵢ))`.

For parameters `α` the separated momenta are `pᵢ = εᵢ √Rᵢ(qᵢ, α)` with
`Rᵢ = 2 (Σⱼ φᵢⱼ αⱼ − uᵢ)/gᵢ` and signs `εᵢ = ±1`, and the action is
`S = −α_{j₀} t + Σᵢ εᵢ ∫_{cᵢ}^{qᵢ} √Rᵢ(x, α) dx`.

* `hasDerivAt_action_position`, `hasDerivAt_action_time`,
  `hamiltonian_momentum`: `∂S/∂qᵢ = pᵢ`, `∂S/∂t = −α_{j₀}` and
  `H(q, ∂S/∂q) = α_{j₀}`, the Hamilton–Jacobi equation.
* `hasDerivAt_action_param`: `∂S/∂αⱼ = −δ_{j j₀} t + Σᵢ εᵢ Θᵢⱼ(qᵢ, α)` with
  `Θᵢⱼ = ∫_{cᵢ}^{qᵢ} φᵢⱼ/(gᵢ √Rᵢ) dx`, by differentiation under the integral.
* `det_mixed_ne_zero`: the matrix `∂²S/∂qᵢ∂αⱼ = εᵢ φᵢⱼ/(gᵢ √Rᵢ)` has a
  determinant different from zero where the matrix `φ` has: the integral is
  complete.
* `eq_of_jacobi`, `hasDerivAt_momentum_of_jacobi`: Jacobi's theorem. Along a
  curve on which the derivatives `∂S/∂αⱼ` are constant, `q̇ᵢ = ∂H/∂pᵢ` and
  `ṗᵢ = −∂H/∂qᵢ` for the momenta `pᵢ = ∂S/∂qᵢ`.
-/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace ProjectAInos.Mechanics.Stackel

/-- A Hamiltonian of Stäckel's form on an open box of co-ordinates. -/
structure System (ι : Type) [Fintype ι] [DecidableEq ι] where
  /-- The matrix of Stäckel: the entry `(i, j)` is a function of `qᵢ`. -/
  φ : ι → ι → ℝ → ℝ
  /-- The coefficient of `pᵢ²/2`, a function of `qᵢ`. -/
  g : ι → ℝ → ℝ
  /-- The part of the potential that belongs to `qᵢ`. -/
  u : ι → ℝ → ℝ
  /-- The coefficients of the separated parts in the Hamiltonian. -/
  Ψ : ι → (ι → ℝ) → ℝ
  /-- The index of the parameter that is the energy. -/
  j₀ : ι
  /-- The interval of the co-ordinate `qᵢ`. -/
  I : ι → Set ℝ
  isOpen : ∀ i, IsOpen (I i)
  ordConnected : ∀ i, (I i).OrdConnected
  contDiffOn_φ : ∀ i j, ContDiffOn ℝ 1 (φ i j) (I i)
  contDiffOn_g : ∀ i, ContDiffOn ℝ 1 (g i) (I i)
  contDiffOn_u : ∀ i, ContDiffOn ℝ 1 (u i) (I i)
  g_pos : ∀ i, ∀ x ∈ I i, 0 < g i x
  /-- `Ψ` is the row `j₀` of the inverse of the matrix of Stäckel. -/
  sum_Ψ : ∀ q : ι → ℝ, (∀ i, q i ∈ I i) → ∀ j,
    ∑ i, Ψ i q * φ i j (q i) = if j = j₀ then 1 else 0
  differentiableAt_Ψ : ∀ q : ι → ℝ, (∀ i, q i ∈ I i) → ∀ i, DifferentiableAt ℝ (Ψ i) q

variable {ι : Type} [Fintype ι] [DecidableEq ι] (s : System ι)

namespace System

/-- The box of co-ordinates. -/
def domain : Set (ι → ℝ) := {q | ∀ i, q i ∈ s.I i}

/-- The Hamiltonian `Σᵢ Ψᵢ(q) (gᵢ(qᵢ) pᵢ²/2 + uᵢ(qᵢ))`. -/
def hamiltonian (q p : ι → ℝ) : ℝ :=
  ∑ i, s.Ψ i q * (s.g i (q i) * p i ^ 2 / 2 + s.u i (q i))

/-- `Rᵢ(x, α) = 2 (Σⱼ φᵢⱼ(x) αⱼ − uᵢ(x))/gᵢ(x)`, the square of the separated
momentum. -/
def radicand (i : ι) (x : ℝ) (α : ι → ℝ) : ℝ :=
  2 * (∑ j, s.φ i j x * α j - s.u i x) / s.g i x

/-- The separated momentum `pᵢ = εᵢ √Rᵢ(x, α)`. -/
def momentum (ε : ι → ℝ) (i : ι) (x : ℝ) (α : ι → ℝ) : ℝ := ε i * √(s.radicand i x α)

/-- `Wᵢ(x, α) = ∫_{cᵢ}^{x} √Rᵢ(y, α) dy`. -/
def partialAction (c : ι → ℝ) (i : ι) (x : ℝ) (α : ι → ℝ) : ℝ :=
  ∫ y in c i..x, √(s.radicand i y α)

/-- `Θᵢⱼ(x, α) = ∫_{cᵢ}^{x} φᵢⱼ(y)/(gᵢ(y) √Rᵢ(y, α)) dy`, the derivative of `Wᵢ`
in the parameter `αⱼ`. -/
def angleIntegral (c : ι → ℝ) (i j : ι) (x : ℝ) (α : ι → ℝ) : ℝ :=
  ∫ y in c i..x, s.φ i j y / (s.g i y * √(s.radicand i y α))

/-- The action `S = −α_{j₀} t + Σᵢ εᵢ Wᵢ(qᵢ, α)`. -/
def action (ε c : ι → ℝ) (q α : ι → ℝ) (t : ℝ) : ℝ :=
  -(α s.j₀ * t) + ∑ i, ε i * s.partialAction c i (q i) α

/-- The system on a smaller box. The radicands of the separated momenta are
positive only between turning points, so the theorems are applied on such a
box. -/
def restrict (J : ι → Set ℝ) (hJo : ∀ i, IsOpen (J i)) (hJc : ∀ i, (J i).OrdConnected)
    (hJ : ∀ i, J i ⊆ s.I i) : System ι where
  φ := s.φ
  g := s.g
  u := s.u
  Ψ := s.Ψ
  j₀ := s.j₀
  I := J
  isOpen := hJo
  ordConnected := hJc
  contDiffOn_φ i j := (s.contDiffOn_φ i j).mono (hJ i)
  contDiffOn_g i := (s.contDiffOn_g i).mono (hJ i)
  contDiffOn_u i := (s.contDiffOn_u i).mono (hJ i)
  g_pos i x hx := s.g_pos i x (hJ i hx)
  sum_Ψ q hq := s.sum_Ψ q fun i => hJ i (hq i)
  differentiableAt_Ψ q hq := s.differentiableAt_Ψ q fun i => hJ i (hq i)

theorem restrict_hamiltonian (J : ι → Set ℝ) (hJo : ∀ i, IsOpen (J i))
    (hJc : ∀ i, (J i).OrdConnected) (hJ : ∀ i, J i ⊆ s.I i) :
    (s.restrict J hJo hJc hJ).hamiltonian = s.hamiltonian := rfl

theorem restrict_radicand (J : ι → Set ℝ) (hJo : ∀ i, IsOpen (J i))
    (hJc : ∀ i, (J i).OrdConnected) (hJ : ∀ i, J i ⊆ s.I i) :
    (s.restrict J hJo hJc hJ).radicand = s.radicand := rfl

variable {s}
variable {ε c q α : ι → ℝ} {i j : ι} {x t : ℝ}

/-! ### The Hamilton–Jacobi equation -/

theorem sum_mul_update (f α : ι → ℝ) (j : ι) (a : ℝ) :
    ∑ k, f k * Function.update α j a k = ∑ k, f k * α k + f j * (a - α j) := by
  have h : ∀ k, f k * Function.update α j a k =
      f k * α k + if k = j then f j * (a - α j) else 0 := by
    intro k
    by_cases hk : k = j
    · subst hk
      simp only [Function.update_self, ↓reduceIte]
      ring
    · simp only [Function.update_of_ne hk, hk, ↓reduceIte, add_zero]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem radicand_update (i j : ι) (x : ℝ) (α : ι → ℝ) (a : ℝ) :
    s.radicand i x (Function.update α j a) =
      s.radicand i x α + 2 * s.φ i j x * (a - α j) / s.g i x := by
  rw [radicand, radicand, sum_mul_update]
  ring

/-- The separated equation `gᵢ pᵢ²/2 + uᵢ = Σⱼ φᵢⱼ αⱼ`. -/
theorem separated_equation (hε : ∀ i, ε i ^ 2 = 1) (hx : x ∈ s.I i)
    (hR : 0 ≤ s.radicand i x α) :
    s.g i x * s.momentum ε i x α ^ 2 / 2 + s.u i x = ∑ j, s.φ i j x * α j := by
  have hg := (s.g_pos i x hx).ne'
  rw [momentum, mul_pow, hε i, one_mul, Real.sq_sqrt hR, radicand]
  field_simp
  ring

/-- The Hamilton–Jacobi equation: `H(q, ∂S/∂q) = α_{j₀}`. -/
theorem hamiltonian_momentum (hε : ∀ i, ε i ^ 2 = 1) (hq : q ∈ s.domain)
    (hR : ∀ i, 0 ≤ s.radicand i (q i) α) :
    s.hamiltonian q (fun i => s.momentum ε i (q i) α) = α s.j₀ := by
  have h1 : ∀ i, s.Ψ i q * (s.g i (q i) * s.momentum ε i (q i) α ^ 2 / 2 + s.u i (q i)) =
      ∑ j, s.Ψ i q * s.φ i j (q i) * α j := fun i => by
    rw [separated_equation hε (hq i) (hR i), Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
  rw [hamiltonian]
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, s.sum_Ψ q hq, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]

/-! ### The derivatives of the action -/

theorem contDiffOn_radicand (i : ι) (α : ι → ℝ) :
    ContDiffOn ℝ 1 (fun x => s.radicand i x α) (s.I i) :=
  (contDiffOn_const.mul ((ContDiffOn.sum fun j _ =>
    (s.contDiffOn_φ i j).mul contDiffOn_const).sub (s.contDiffOn_u i))).div
      (s.contDiffOn_g i) fun x hx => (s.g_pos i x hx).ne'

theorem continuousOn_sqrt_radicand (i : ι) (α : ι → ℝ) :
    ContinuousOn (fun x => √(s.radicand i x α)) (s.I i) :=
  Real.continuous_sqrt.comp_continuousOn (contDiffOn_radicand i α).continuousOn

/-- `∂Wᵢ/∂x = √Rᵢ`. -/
theorem hasDerivAt_partialAction (hc : c i ∈ s.I i) (hx : x ∈ s.I i) :
    HasDerivAt (fun x => s.partialAction c i x α) (√(s.radicand i x α)) x := by
  have hcont := continuousOn_sqrt_radicand (s := s) i α
  exact intervalIntegral.integral_hasDerivAt_right
    (hcont.mono ((s.ordConnected i).uIcc_subset hc hx)).intervalIntegrable
    (hcont.stronglyMeasurableAtFilter (s.isOpen i) x hx)
    (hcont.continuousAt ((s.isOpen i).mem_nhds hx))

theorem continuousOn_angle_integrand (i j : ι) {α : ι → ℝ}
    (hR : ∀ x ∈ s.I i, 0 < s.radicand i x α) :
    ContinuousOn (fun x => s.φ i j x / (s.g i x * √(s.radicand i x α))) (s.I i) :=
  (s.contDiffOn_φ i j).continuousOn.div
    ((s.contDiffOn_g i).continuousOn.mul (continuousOn_sqrt_radicand i α)) fun x hx =>
      mul_ne_zero (s.g_pos i x hx).ne' (Real.sqrt_pos.mpr (hR x hx)).ne'

/-- `∂Θᵢⱼ/∂x = φᵢⱼ/(gᵢ √Rᵢ)`. -/
theorem hasDerivAt_angleIntegral (hc : c i ∈ s.I i) (hx : x ∈ s.I i)
    (hR : ∀ x ∈ s.I i, 0 < s.radicand i x α) (j : ι) :
    HasDerivAt (fun x => s.angleIntegral c i j x α)
      (s.φ i j x / (s.g i x * √(s.radicand i x α))) x := by
  have hcont := continuousOn_angle_integrand (s := s) i j hR
  exact intervalIntegral.integral_hasDerivAt_right
    (hcont.mono ((s.ordConnected i).uIcc_subset hc hx)).intervalIntegrable
    (hcont.stronglyMeasurableAtFilter (s.isOpen i) x hx)
    (hcont.continuousAt ((s.isOpen i).mem_nhds hx))

/-- `∂Wᵢ/∂αⱼ = Θᵢⱼ`, by differentiation under the integral. -/
theorem hasDerivAt_partialAction_param (hc : c i ∈ s.I i) (hx : x ∈ s.I i)
    (hR : ∀ x ∈ s.I i, 0 < s.radicand i x α) (j : ι) :
    HasDerivAt (fun a => s.partialAction c i x (Function.update α j a))
      (s.angleIntegral c i j x α) (α j) := by
  have hsub := (s.ordConnected i).uIcc_subset hc hx
  have hmem : ∀ y ∈ uIcc (c i) x, s.I i ∈ 𝓝 y := fun y hy => (s.isOpen i).mem_nhds (hsub hy)
  have hF : ∀ y ∈ uIcc (c i) x, ContDiffAt ℝ 1 (fun p : ℝ × ℝ =>
      √(s.radicand i p.2 α + 2 * s.φ i j p.2 * (p.1 - α j) / s.g i p.2)) (α j, y) := by
    intro y hy
    have hy' := hsub hy
    have hr : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => s.radicand i p.2 α) (α j, y) :=
      ContDiffAt.comp (α j, y) (g := fun x => s.radicand i x α) (f := Prod.snd)
        ((contDiffOn_radicand i α).contDiffAt (hmem y hy)) contDiffAt_snd
    have hφ : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => s.φ i j p.2) (α j, y) :=
      ContDiffAt.comp (α j, y) (g := s.φ i j) (f := Prod.snd)
        ((s.contDiffOn_φ i j).contDiffAt (hmem y hy)) contDiffAt_snd
    have hg : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => s.g i p.2) (α j, y) :=
      ContDiffAt.comp (α j, y) (g := s.g i) (f := Prod.snd)
        ((s.contDiffOn_g i).contDiffAt (hmem y hy)) contDiffAt_snd
    have hsum : ContDiffAt ℝ 1 (fun p : ℝ × ℝ =>
        s.radicand i p.2 α + 2 * s.φ i j p.2 * (p.1 - α j) / s.g i p.2) (α j, y) :=
      hr.add (((contDiffAt_const.mul hφ).mul (contDiffAt_fst.sub contDiffAt_const)).div hg
        (s.g_pos i y hy').ne')
    refine hsum.sqrt ?_
    simp only [sub_self, mul_zero, zero_div, add_zero]
    exact (hR y hy').ne'
  have hD : ∀ y ∈ uIcc (c i) x, HasDerivAt (fun a : ℝ =>
      √(s.radicand i y α + 2 * s.φ i j y * (a - α j) / s.g i y))
      (s.φ i j y / (s.g i y * √(s.radicand i y α))) (α j) := by
    intro y hy
    have hy' := hsub hy
    have hg := (s.g_pos i y hy').ne'
    have hs : 0 < √(s.radicand i y α) := Real.sqrt_pos.mpr (hR y hy')
    have h1 : HasDerivAt (fun a : ℝ => s.radicand i y α + 2 * s.φ i j y * (a - α j) / s.g i y)
        (2 * s.φ i j y / s.g i y) (α j) := by
      have h2 : HasDerivAt (fun a : ℝ => 2 * s.φ i j y * (a - α j) / s.g i y)
          (2 * s.φ i j y * 1 / s.g i y) (α j) :=
        (((hasDerivAt_id (α j)).sub_const (α j)).const_mul (2 * s.φ i j y)).div_const _
      have h3 := h2.const_add (s.radicand i y α)
      refine h3.congr_deriv ?_
      ring
    have h4 := h1.sqrt (by
      simp only [sub_self, mul_zero, zero_div, add_zero]
      exact (hR y hy').ne')
    refine h4.congr_deriv ?_
    simp only [sub_self, mul_zero, zero_div, add_zero]
    field_simp
  have h := Variational.hasDerivAt_intervalIntegral_of_contDiffAt
    (F := fun p : ℝ × ℝ => √(s.radicand i p.2 α + 2 * s.φ i j p.2 * (p.1 - α j) / s.g i p.2))
    (D := fun y => s.φ i j y / (s.g i y * √(s.radicand i y α))) (ε₀ := α j) (a := c i) (b := x)
    hF hD
  have e : (fun a => s.partialAction c i x (Function.update α j a)) = fun a =>
      ∫ y in c i..x, √(s.radicand i y α + 2 * s.φ i j y * (a - α j) / s.g i y) := by
    funext a
    simp only [partialAction, radicand_update]
  rw [e]
  exact h

theorem action_update (ε c q α : ι → ℝ) (t : ℝ) (i : ι) (x : ℝ) :
    s.action ε c (Function.update q i x) α t =
      s.action ε c q α t +
        ε i * (s.partialAction c i x α - s.partialAction c i (q i) α) := by
  have h : ∀ k, ε k * s.partialAction c k (Function.update q i x k) α =
      ε k * s.partialAction c k (q k) α +
        if k = i then ε i * (s.partialAction c i x α - s.partialAction c i (q i) α) else 0 := by
    intro k
    by_cases hk : k = i
    · subst hk
      simp only [Function.update_self, ↓reduceIte]
      ring
    · simp only [Function.update_of_ne hk, hk, ↓reduceIte, add_zero]
  simp only [action, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

/-- `∂S/∂qᵢ = pᵢ`. -/
theorem hasDerivAt_action_position (hc : c i ∈ s.I i) (hq : q i ∈ s.I i) (t : ℝ) :
    HasDerivAt (fun x => s.action ε c (Function.update q i x) α t)
      (s.momentum ε i (q i) α) (q i) := by
  have h1 := ((hasDerivAt_partialAction (α := α) hc hq).sub_const
    (s.partialAction c i (q i) α)).const_mul (ε i)
  have h2 := h1.const_add (s.action ε c q α t)
  have e : (fun x => s.action ε c (Function.update q i x) α t) = fun x =>
      s.action ε c q α t + ε i * (s.partialAction c i x α - s.partialAction c i (q i) α) :=
    funext fun x => action_update ε c q α t i x
  rw [e]
  exact h2

/-- `∂S/∂t = −α_{j₀}`. -/
theorem hasDerivAt_action_time (ε c q α : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun τ => s.action ε c q α τ) (-α s.j₀) t := by
  have h1 : HasDerivAt (fun τ : ℝ => -(α s.j₀ * τ)) (-(α s.j₀ * 1)) t :=
    ((hasDerivAt_id t).const_mul (α s.j₀)).neg
  have h2 := h1.add_const (∑ i, ε i * s.partialAction c i (q i) α)
  refine h2.congr_deriv ?_
  ring

/-- `∂S/∂αⱼ = −δ_{j j₀} t + Σᵢ εᵢ Θᵢⱼ(qᵢ, α)`. -/
theorem hasDerivAt_action_param (hc : ∀ i, c i ∈ s.I i) (hq : q ∈ s.domain)
    (hR : ∀ i, ∀ x ∈ s.I i, 0 < s.radicand i x α) (ε : ι → ℝ) (t : ℝ) (j : ι) :
    HasDerivAt (fun a => s.action ε c q (Function.update α j a) t)
      (-((if j = s.j₀ then 1 else 0) * t) + ∑ i, ε i * s.angleIntegral c i j (q i) α)
      (α j) := by
  have h1 : HasDerivAt (fun a : ℝ => -(Function.update α j a s.j₀ * t))
      (-((if j = s.j₀ then 1 else 0) * t)) (α j) := by
    by_cases hj : j = s.j₀
    · subst hj
      simp only [Function.update_self, ↓reduceIte]
      exact ((hasDerivAt_id (α s.j₀)).mul_const t).neg
    · have hne : s.j₀ ≠ j := fun h => hj h.symm
      simp only [Function.update_of_ne hne, hj, ↓reduceIte, zero_mul, neg_zero]
      exact hasDerivAt_const _ _
  have h2 : HasDerivAt (fun a : ℝ => ∑ i, ε i * s.partialAction c i (q i) (Function.update α j a))
      (∑ i, ε i * s.angleIntegral c i j (q i) α) (α j) :=
    HasDerivAt.fun_sum fun i _ =>
      (hasDerivAt_partialAction_param (hc i) (hq i) (hR i) j).const_mul (ε i)
  exact h1.add h2

/-! ### Completeness -/

/-- The matrix `∂²S/∂qᵢ∂αⱼ = εᵢ φᵢⱼ/(gᵢ √Rᵢ)` is non-degenerate where the
matrix of Stäckel is: the integral is complete. -/
theorem det_mixed_ne_zero (hε : ∀ i, ε i ^ 2 = 1) (hq : q ∈ s.domain)
    (hR : ∀ i, 0 < s.radicand i (q i) α)
    (hdet : (Matrix.of fun i j => s.φ i j (q i)).det ≠ 0) :
    (Matrix.of fun i j =>
      ε i * (s.φ i j (q i) / (s.g i (q i) * √(s.radicand i (q i) α)))).det ≠ 0 := by
  have e : (Matrix.of fun i j =>
      ε i * (s.φ i j (q i) / (s.g i (q i) * √(s.radicand i (q i) α)))) =
      Matrix.diagonal (fun i => ε i / (s.g i (q i) * √(s.radicand i (q i) α))) *
        Matrix.of fun i j => s.φ i j (q i) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.of_apply, Matrix.of_apply]
    ring
  rw [e, Matrix.det_mul, Matrix.det_diagonal]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ?_) hdet
  have hεi : ε i ≠ 0 := fun h => by
    have := hε i
    rw [h] at this
    norm_num at this
  exact div_ne_zero hεi (mul_ne_zero (s.g_pos i _ (hq i)).ne' (Real.sqrt_pos.mpr (hR i)).ne')

/-! ### Jacobi's theorem -/

theorem hamiltonian_update_momentum (q p : ι → ℝ) (i : ι) (y : ℝ) :
    s.hamiltonian q (Function.update p i y) =
      s.hamiltonian q p + s.Ψ i q * (s.g i (q i) * (y ^ 2 - p i ^ 2) / 2) := by
  have h : ∀ k, s.Ψ k q * (s.g k (q k) * Function.update p i y k ^ 2 / 2 + s.u k (q k)) =
      s.Ψ k q * (s.g k (q k) * p k ^ 2 / 2 + s.u k (q k)) +
        if k = i then s.Ψ i q * (s.g i (q i) * (y ^ 2 - p i ^ 2) / 2) else 0 := by
    intro k
    by_cases hk : k = i
    · subst hk
      simp only [Function.update_self, ↓reduceIte]
      ring
    · simp only [Function.update_of_ne hk, hk, ↓reduceIte, add_zero]
  simp only [hamiltonian, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]

/-- `∂H/∂pᵢ = Ψᵢ gᵢ pᵢ`. -/
theorem hasDerivAt_hamiltonian_momentum (q p : ι → ℝ) (i : ι) :
    HasDerivAt (fun y => s.hamiltonian q (Function.update p i y))
      (s.Ψ i q * s.g i (q i) * p i) (p i) := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 - p i ^ 2) (2 * p i) (p i) := by
    have h := (hasDerivAt_pow 2 (p i)).sub_const (p i ^ 2)
    simpa using h
  have h2 := (((h1.const_mul (s.g i (q i))).div_const 2).const_mul (s.Ψ i q)).const_add
    (s.hamiltonian q p)
  have e : (fun y => s.hamiltonian q (Function.update p i y)) = fun y =>
      s.hamiltonian q p + s.Ψ i q * (s.g i (q i) * (y ^ 2 - p i ^ 2) / 2) :=
    funext fun y => hamiltonian_update_momentum q p i y
  rw [e]
  refine h2.congr_deriv ?_
  ring

section Jacobi

variable {Q : ι → ℝ → ℝ} {Q' β : ι → ℝ}

/-- Jacobi's theorem for the velocities. Along a curve on which the
derivatives `∂S/∂αⱼ` are constant and the matrix of Stäckel is non-degenerate,
`q̇ᵢ = ∂H/∂pᵢ` with the momenta `pᵢ = ∂S/∂qᵢ`. -/
theorem eq_of_jacobi (hε : ∀ i, ε i ^ 2 = 1) (hc : ∀ i, c i ∈ s.I i)
    (hR : ∀ i, ∀ x ∈ s.I i, 0 < s.radicand i x α)
    (hQ : ∀ i, HasDerivAt (Q i) (Q' i) t) (hD : (fun i => Q i t) ∈ s.domain)
    (hJ : ∀ j, ∀ᶠ τ in 𝓝 t, -((if j = s.j₀ then 1 else 0) * τ) +
      ∑ i, ε i * s.angleIntegral c i j (Q i τ) α = β j)
    (hdet : (Matrix.of fun i j => s.φ i j (Q i t)).det ≠ 0) (i : ι) :
    Q' i = s.Ψ i (fun k => Q k t) * s.g i (Q i t) * s.momentum ε i (Q i t) α := by
  have hrel : ∀ j, ∑ k, ε k *
      (s.φ k j (Q k t) / (s.g k (Q k t) * √(s.radicand k (Q k t) α)) * Q' k) =
      if j = s.j₀ then 1 else 0 := by
    intro j
    have h1 : HasDerivAt (fun τ : ℝ => -((if j = s.j₀ then (1 : ℝ) else 0) * τ))
        (-((if j = s.j₀ then (1 : ℝ) else 0) * 1)) t :=
      ((hasDerivAt_id t).const_mul _).neg
    have h2 : HasDerivAt (fun τ => ∑ k, ε k * s.angleIntegral c k j (Q k τ) α)
        (∑ k, ε k *
          (s.φ k j (Q k t) / (s.g k (Q k t) * √(s.radicand k (Q k t) α)) * Q' k)) t :=
      HasDerivAt.fun_sum fun k _ =>
        (HasDerivAt.comp t (hasDerivAt_angleIntegral (hc k) (hD k) (hR k) j)
          (hQ k)).const_mul (ε k)
    have h4 : HasDerivAt (fun τ => -((if j = s.j₀ then (1 : ℝ) else 0) * τ) +
        ∑ k, ε k * s.angleIntegral c k j (Q k τ) α) 0 t :=
      (hasDerivAt_const t (β j)).congr_of_eventuallyEq (hJ j)
    have h5 := (h1.add h2).unique h4
    linarith
  obtain ⟨v, hv⟩ : ∃ v : ι → ℝ, v = fun k =>
      ε k * Q' k / (s.g k (Q k t) * √(s.radicand k (Q k t) α)) - s.Ψ k (fun l => Q l t) :=
    ⟨_, rfl⟩
  have hvM : Matrix.vecMul v (Matrix.of fun i j => s.φ i j (Q i t)) = 0 := by
    funext j
    have e1 : Matrix.vecMul v (Matrix.of fun i j => s.φ i j (Q i t)) j =
        ∑ k, ε k * (s.φ k j (Q k t) / (s.g k (Q k t) * √(s.radicand k (Q k t) α)) * Q' k) -
          ∑ k, s.Ψ k (fun l => Q l t) * s.φ k j (Q k t) := by
      rw [← Finset.sum_sub_distrib]
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, hv]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e1, hrel j, s.sum_Ψ _ hD j, sub_self]
    rfl
  have hi := congrFun (Matrix.eq_zero_of_vecMul_eq_zero hdet hvM) i
  rw [hv] at hi
  have hgi := (s.g_pos i _ (hD i)).ne'
  have hsi : 0 < √(s.radicand i (Q i t) α) := Real.sqrt_pos.mpr (hR i _ (hD i))
  have h6 : ε i * Q' i =
      s.Ψ i (fun k => Q k t) * (s.g i (Q i t) * √(s.radicand i (Q i t) α)) := by
    have h7 : ε i * Q' i / (s.g i (Q i t) * √(s.radicand i (Q i t) α)) =
        s.Ψ i (fun l => Q l t) := sub_eq_zero.mp hi
    rw [← h7]
    field_simp
  calc Q' i = ε i ^ 2 * Q' i := by rw [hε i, one_mul]
    _ = ε i * (ε i * Q' i) := by ring
    _ = s.Ψ i (fun k => Q k t) * s.g i (Q i t) * s.momentum ε i (Q i t) α := by
        rw [h6, momentum]
        ring

/-- Jacobi's theorem for the momenta: `ṗᵢ = −∂H/∂qᵢ` for `pᵢ = ∂S/∂qᵢ`, where
`∂H/∂qᵢ` is the derivative of the Hamiltonian along the line of the
co-ordinate `qᵢ`. -/
theorem hasDerivAt_momentum_of_jacobi (hε : ∀ i, ε i ^ 2 = 1)
    (hR : ∀ i, ∀ x ∈ s.I i, 0 < s.radicand i x α) (hD : (fun i => Q i t) ∈ s.domain) (i : ι)
    (hQ : HasDerivAt (Q i) (Q' i) t)
    (hvel : Q' i = s.Ψ i (fun k => Q k t) * s.g i (Q i t) * s.momentum ε i (Q i t) α)
    {D : ℝ} (hH : HasDerivAt (fun x => s.hamiltonian (Function.update (fun k => Q k t) i x)
      (fun k => s.momentum ε k (Q k t) α)) D (Q i t)) :
    HasDerivAt (fun τ => s.momentum ε i (Q i τ) α) (-D) t := by
  have hnhds : s.I i ∈ 𝓝 (Q i t) := (s.isOpen i).mem_nhds (hD i)
  have hRd : HasDerivAt (fun x => s.radicand i x α)
      (deriv (fun x => s.radicand i x α) (Q i t)) (Q i t) :=
    (((contDiffOn_radicand i α).contDiffAt hnhds).differentiableAt one_ne_zero).hasDerivAt
  have hpos := hR i _ (hD i)
  obtain ⟨P', hP'⟩ : ∃ P' : ℝ, P' = ε i *
      (deriv (fun x => s.radicand i x α) (Q i t) / (2 * √(s.radicand i (Q i t) α))) :=
    ⟨_, rfl⟩
  have hP : HasDerivAt (fun x => s.momentum ε i x α) P' (Q i t) := by
    rw [hP']
    exact (hRd.sqrt hpos.ne').const_mul (ε i)
  have hp : HasDerivAt (fun τ => s.momentum ε i (Q i τ) α) (P' * Q' i) t :=
    HasDerivAt.comp t (h₂ := fun x => s.momentum ε i x α) (h := Q i) hP hQ
  -- The Hamilton–Jacobi equation along the line of the co-ordinate `qᵢ`.
  have hΨ : HasDerivAt (fun x => s.Ψ i (Function.update (fun k => Q k t) i x))
      (fderiv ℝ (s.Ψ i) (fun k => Q k t) (Pi.single i 1)) (Q i t) := by
    have h1 : HasFDerivAt (s.Ψ i) (fderiv ℝ (s.Ψ i) (fun k => Q k t))
        (Function.update (fun k => Q k t) i (Q i t)) := by
      rw [Function.update_eq_self]
      exact (s.differentiableAt_Ψ _ hD i).hasFDerivAt
    exact HasFDerivAt.comp_hasDerivAt (Q i t) h1 (hasDerivAt_update (fun k => Q k t) i (Q i t))
  have hg : HasDerivAt (s.g i) (deriv (s.g i) (Q i t)) (Q i t) :=
    (((s.contDiffOn_g i).contDiffAt hnhds).differentiableAt one_ne_zero).hasDerivAt
  have hP2 : HasDerivAt (fun x => s.momentum ε i x α ^ 2 - s.momentum ε i (Q i t) α ^ 2)
      (2 * s.momentum ε i (Q i t) α * P') (Q i t) := by
    have h := (hP.pow 2).sub_const (s.momentum ε i (Q i t) α ^ 2)
    simpa using h
  have hB : HasDerivAt (fun x =>
      s.g i x * (s.momentum ε i x α ^ 2 - s.momentum ε i (Q i t) α ^ 2) / 2)
      ((deriv (s.g i) (Q i t) *
          (s.momentum ε i (Q i t) α ^ 2 - s.momentum ε i (Q i t) α ^ 2) +
        s.g i (Q i t) * (2 * s.momentum ε i (Q i t) α * P')) / 2) (Q i t) :=
    (hg.mul hP2).div_const 2
  have hG : HasDerivAt (fun x => α s.j₀ - s.Ψ i (Function.update (fun k => Q k t) i x) *
      (s.g i x * (s.momentum ε i x α ^ 2 - s.momentum ε i (Q i t) α ^ 2) / 2))
      (-(fderiv ℝ (s.Ψ i) (fun k => Q k t) (Pi.single i 1) *
          (s.g i (Q i t) *
            (s.momentum ε i (Q i t) α ^ 2 - s.momentum ε i (Q i t) α ^ 2) / 2) +
        s.Ψ i (Function.update (fun k => Q k t) i (Q i t)) *
          ((deriv (s.g i) (Q i t) *
              (s.momentum ε i (Q i t) α ^ 2 - s.momentum ε i (Q i t) α ^ 2) +
            s.g i (Q i t) * (2 * s.momentum ε i (Q i t) α * P')) / 2))) (Q i t) :=
    (hΨ.mul hB).const_sub (α s.j₀)
  have hev : (fun x => s.hamiltonian (Function.update (fun k => Q k t) i x)
      (fun k => s.momentum ε k (Q k t) α)) =ᶠ[𝓝 (Q i t)] fun x => α s.j₀ -
        s.Ψ i (Function.update (fun k => Q k t) i x) *
          (s.g i x * (s.momentum ε i x α ^ 2 - s.momentum ε i (Q i t) α ^ 2) / 2) := by
    filter_upwards [hnhds] with x hx
    have hdom : Function.update (fun k => Q k t) i x ∈ s.domain := fun k => by
      by_cases hk : k = i
      · subst hk
        rw [Function.update_self]
        exact hx
      · rw [Function.update_of_ne hk]
        exact hD k
    have hRx : ∀ k, 0 ≤ s.radicand k (Function.update (fun k => Q k t) i x k) α := fun k =>
      (hR k _ (hdom k)).le
    have h1 := hamiltonian_momentum hε hdom hRx
    have e : (fun k => s.momentum ε k (Function.update (fun k => Q k t) i x k) α) =
        Function.update (fun k => s.momentum ε k (Q k t) α) i (s.momentum ε i x α) := by
      funext k
      by_cases hk : k = i
      · subst hk
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
    rw [e, hamiltonian_update_momentum, Function.update_self] at h1
    linarith
  have hD' := hH.unique (hG.congr_of_eventuallyEq hev)
  refine hp.congr_deriv ?_
  rw [hD', hvel, Function.update_eq_self]
  ring

end Jacobi

end System

end ProjectAInos.Mechanics.Stackel
