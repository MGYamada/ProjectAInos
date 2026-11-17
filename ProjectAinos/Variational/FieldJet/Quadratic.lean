/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Variational.FieldJet.Noether
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Quadratic Lagrangians of the first derivatives and the gauge identity

For constants `C^{aμ,bν}` the Lagrangian `L = ½ Σ C^{aμ,bν} uᵃ_μ uᵇ_ν` is quadratic in the
first derivatives of the fields.

* `momentum_quadraticLagrangian`: for symmetric constants, `C^{aμ,bν} = C^{bν,aμ}`, the
  momenta are `π^μ_a = Σ C^{aμ,bν} uᵇ_ν`, and `euler_quadraticLagrangian` gives
  `Eₐ(L) = −Σ C^{aμ,bν} uᵇ_{μν}`.

When the fields are indexed by the independent variables, as the components of a one-form
are, and the constants are antisymmetric in the first pair, `C^{aμ,bν} = −C^{μa,bν}`:

* `prolong_gauge_quadraticLagrangian`: the gauge variation `ξₐ = Dₐ χ` does not change the
  Lagrangian, for every `χ`;
* `divergence_euler_quadraticLagrangian`: `Σₐ Dₐ Eₐ(L) = 0`. This is Noether's second identity
  for the gauge symmetry: the Euler–Lagrange expressions are not independent.

The Lagrangian `−¼ F_{μν} F^{μν}` of a one-form with a constant symmetric matrix `η` is the
case `C^{aμ,bν} = −(η^{μν} η^{ab} − η^{μb} η^{νa})` (`gaugeConstants`), and there
`π^μ_a = −F^{μa}`.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.Variational.FieldJetRing

open SmoothAlgebra

variable {ι κ J : Type*} [CommRing J] [Algebra ℝ J] [SmoothRing J] [Fintype κ] [Fintype ι]
  [DecidableEq ι] [DecidableEq κ] (R : FieldJetRing ι κ J)

/-- The Lagrangian `½ Σ C^{aμ,bν} uᵃ_μ uᵇ_ν` of constants `C`. -/
def quadraticLagrangian (C : κ → ι → κ → ι → ℝ) : J :=
  algebraMap ℝ J (1 / 2) *
    ∑ a, ∑ μ, ∑ b, ∑ ν, algebraMap ℝ J (C a μ b ν) * (R.u a {μ} * R.u b {ν})

variable {R}

omit [Fintype κ] [Fintype ι] in
/-- The derivative of a first derivative of a field with respect to a jet co-ordinate. -/
theorem d_u_singleton (c : κ) (K : Multiset ι) (b : κ) (ν : ι) :
    R.d c K (R.u b {ν}) = if b = c ∧ {ν} = K then 1 else 0 := by
  by_cases h : b = c ∧ ({ν} : Multiset ι) = K
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, ↓reduceIte, R.d_u_self]
  · simp only [h, ↓reduceIte]
    exact R.d_u_ne b {ν} c K fun hp => h ⟨(Prod.mk.inj hp).1, (Prod.mk.inj hp).2⟩

omit [Fintype κ] [Fintype ι] [DecidableEq ι] [DecidableEq κ] [SmoothRing J] in
theorem algebraMap_half_mul_two : algebraMap ℝ J (1 / 2) * 2 = 1 := by
  rw [← map_ofNat (algebraMap ℝ J) 2, ← map_mul]
  norm_num

omit [Fintype κ] [Fintype ι] [DecidableEq ι] [DecidableEq κ] [SmoothRing J] in
/-- In a real algebra an element that is equal to its negative is zero. -/
theorem eq_zero_of_eq_neg {X : J} (h : X = -X) : X = 0 := by
  have h2 : (2 : J) * X = 0 := by linear_combination h
  calc X = algebraMap ℝ J (1 / 2) * 2 * X := by rw [algebraMap_half_mul_two, one_mul]
    _ = 0 := by rw [mul_assoc, h2, mul_zero]

/-- The derivative of the quadratic Lagrangian with respect to a jet co-ordinate. -/
theorem d_quadraticLagrangian (C : κ → ι → κ → ι → ℝ) (e : κ) (K : Multiset ι) :
    R.d e K (R.quadraticLagrangian C) = algebraMap ℝ J (1 / 2) *
      ∑ a, ∑ μ, ∑ b, ∑ ν, algebraMap ℝ J (C a μ b ν) *
        (R.u a {μ} * (if b = e ∧ ({ν} : Multiset ι) = K then 1 else 0) +
          R.u b {ν} * (if a = e ∧ ({μ} : Multiset ι) = K then 1 else 0)) := by
  simp only [quadraticLagrangian, map_sum, SmoothDerivation.map_mul, smul_eq_mul,
    SmoothDerivation.map_algebraMap, mul_zero, add_zero, d_u_singleton]

/-- The quadratic Lagrangian is of the first order. -/
theorem firstOrder_quadraticLagrangian (C : κ → ι → κ → ι → ℝ) :
    R.FirstOrder (R.quadraticLagrangian C) := by
  intro e K hK
  have hne : ∀ ν : ι, ({ν} : Multiset ι) ≠ K := fun ν h => hK (by
    rw [← h]
    simp [firstOrderIndices])
  rw [d_quadraticLagrangian]
  simp only [hne, and_false, ↓reduceIte, mul_zero, add_zero, Finset.sum_const_zero]

/-- The quadratic Lagrangian does not depend on the fields themselves. -/
theorem d_zero_quadraticLagrangian (C : κ → ι → κ → ι → ℝ) (e : κ) :
    R.d e 0 (R.quadraticLagrangian C) = 0 := by
  rw [d_quadraticLagrangian]
  simp only [Multiset.singleton_ne_zero, and_false, ↓reduceIte, mul_zero, add_zero,
    Finset.sum_const_zero]

/-- The momenta of the quadratic Lagrangian of symmetric constants:
`π^ρ_e = Σ C^{eρ,bν} uᵇ_ν`. -/
theorem momentum_quadraticLagrangian {C : κ → ι → κ → ι → ℝ}
    (hC : ∀ a μ b ν, C a μ b ν = C b ν a μ) (e : κ) (ρ : ι) :
    R.momentum (R.quadraticLagrangian C) e ρ =
      ∑ b, ∑ ν, algebraMap ℝ J (C e ρ b ν) * R.u b {ν} := by
  have h1 : ∑ a, ∑ μ, ∑ b, ∑ ν, algebraMap ℝ J (C a μ b ν) *
      (R.u a {μ} * (if b = e ∧ ({ν} : Multiset ι) = {ρ} then 1 else 0)) =
      ∑ a, ∑ μ, algebraMap ℝ J (C a μ e ρ) * R.u a {μ} := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_eq_single e, Finset.sum_eq_single ρ]
    · simp
    · intro ν _ hν
      simp [hν]
    · intro h
      exact absurd (Finset.mem_univ ρ) h
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ e) h
  have h2 : ∑ a, ∑ μ, ∑ b, ∑ ν, algebraMap ℝ J (C a μ b ν) *
      (R.u b {ν} * (if a = e ∧ ({μ} : Multiset ι) = {ρ} then 1 else 0)) =
      ∑ b, ∑ ν, algebraMap ℝ J (C e ρ b ν) * R.u b {ν} := by
    rw [Finset.sum_eq_single e, Finset.sum_eq_single ρ]
    · simp
    · intro μ _ hμ
      simp [hμ]
    · intro h
      exact absurd (Finset.mem_univ ρ) h
    · intro a _ ha
      simp [ha]
    · intro h
      exact absurd (Finset.mem_univ e) h
  have hsymm : ∑ a, ∑ μ, algebraMap ℝ J (C a μ e ρ) * R.u a {μ} =
      ∑ b, ∑ ν, algebraMap ℝ J (C e ρ b ν) * R.u b {ν} :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun μ _ => by rw [hC]
  rw [momentum, d_quadraticLagrangian]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [h1, h2, hsymm, ← two_mul, ← mul_assoc, mul_comm (2 : J), algebraMap_half_mul_two,
    one_mul]

/-- The Euler–Lagrange expressions of the quadratic Lagrangian:
`Eₐ(L) = −Σ C^{aμ,bν} uᵇ_{μν}`. -/
theorem euler_quadraticLagrangian {C : κ → ι → κ → ι → ℝ}
    (hC : ∀ a μ b ν, C a μ b ν = C b ν a μ) (a : κ) :
    R.euler a (R.quadraticLagrangian C) =
      -∑ μ, ∑ b, ∑ ν, algebraMap ℝ J (C a μ b ν) * R.u b (μ ::ₘ {ν}) := by
  rw [euler_of_firstOrder (firstOrder_quadraticLagrangian C), d_zero_quadraticLagrangian,
    zero_sub, divergence]
  simp only [momentum_quadraticLagrangian hC, map_sum, SmoothDerivation.map_algebraMap_mul,
    smul_eq_mul, totalDeriv_u]

end ProjectAinos.Variational.FieldJetRing

/-! ### Fields indexed by the independent variables: the gauge identity -/

namespace ProjectAinos.Variational.FieldJetRing

open SmoothAlgebra

variable {ι J : Type*} [CommRing J] [Algebra ℝ J] [SmoothRing J] [Fintype ι] [DecidableEq ι]
  {R : FieldJetRing ι ι J} {C : ι → ι → ι → ι → ℝ}

/-- Noether's second identity for the gauge symmetry: if the constants are symmetric and are
antisymmetric in the first pair of indices, then `Σₐ Dₐ Eₐ(L) = 0`. -/
theorem divergence_euler_quadraticLagrangian (hC : ∀ a μ b ν, C a μ b ν = C b ν a μ)
    (hanti : ∀ a μ b ν, C a μ b ν = -C μ a b ν) :
    ∑ a, R.totalDeriv a (R.euler a (R.quadraticLagrangian C)) = 0 := by
  have hX : ∑ a, ∑ μ, ∑ b, ∑ ν, algebraMap ℝ J (C a μ b ν) * R.u b (a ::ₘ μ ::ₘ {ν}) = 0 := by
    refine eq_zero_of_eq_neg ?_
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [hanti μ a b ν, map_neg, Multiset.cons_swap]
    ring
  simp only [euler_quadraticLagrangian hC, map_neg, map_sum, SmoothDerivation.map_algebraMap_mul,
    smul_eq_mul, totalDeriv_u, Finset.sum_neg_distrib]
  rw [hX, neg_zero]

/-- The gauge variation `ξₐ = Dₐ χ` does not change the Lagrangian, for every `χ`. -/
theorem prolong_gauge_quadraticLagrangian (hC : ∀ a μ b ν, C a μ b ν = C b ν a μ)
    (hanti : ∀ a μ b ν, C a μ b ν = -C μ a b ν) (χ : J) :
    R.prolong (fun a => R.totalDeriv a χ) (R.quadraticLagrangian C) = 0 := by
  rw [prolong_of_firstOrder (firstOrder_quadraticLagrangian C)]
  simp only [d_zero_quadraticLagrangian, mul_zero, Finset.sum_const_zero, zero_add,
    momentum_quadraticLagrangian hC]
  refine eq_zero_of_eq_neg ?_
  conv_lhs => rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hsum : ∑ b, ∑ ν, algebraMap ℝ J (C μ a b ν) * R.u b {ν} =
      -∑ b, ∑ ν, algebraMap ℝ J (C a μ b ν) * R.u b {ν} := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [hanti μ a b ν, map_neg]
    ring
  rw [totalDeriv_comm a μ χ, hsum]
  ring

/-! ### The Lagrangian of a one-form -/

/-- The constants of the Lagrangian `−¼ F_{μν} F^{μν}` of a one-form, for a constant matrix
`η`: `C^{aμ,bν} = −(η^{μν} η^{ab} − η^{μb} η^{νa})`. -/
def gaugeConstants (η : ι → ι → ℝ) (a μ b ν : ι) : ℝ := -(η μ ν * η a b - η μ b * η ν a)

omit [Fintype ι] [DecidableEq ι] in
theorem gaugeConstants_symm {η : ι → ι → ℝ} (hη : ∀ μ ν, η μ ν = η ν μ) (a μ b ν : ι) :
    gaugeConstants η a μ b ν = gaugeConstants η b ν a μ := by
  simp only [gaugeConstants]
  rw [hη ν μ, hη b a, hη ν a, hη μ b]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem gaugeConstants_antisymm {η : ι → ι → ℝ} (hη : ∀ μ ν, η μ ν = η ν μ) (a μ b ν : ι) :
    gaugeConstants η a μ b ν = -gaugeConstants η μ a b ν := by
  simp only [gaugeConstants]
  rw [hη a ν, hη ν μ]
  ring

variable (R) in
/-- The field strength `F_{μν} = ∂_μ A_ν − ∂_ν A_μ` of the one-form. -/
def fieldStrength (μ ν : ι) : J := R.u ν {μ} - R.u μ {ν}

variable (R) in
/-- The field strength with raised indices, `F^{μa} = η^{μν} η^{ab} F_{νb}`. -/
def raisedFieldStrength (η : ι → ι → ℝ) (μ a : ι) : J :=
  ∑ ν, ∑ b, algebraMap ℝ J (η μ ν * η a b) * R.fieldStrength ν b

/-- The momenta of the Lagrangian of a one-form: `π^μ_a = −F^{μa}`. -/
theorem momentum_gauge {η : ι → ι → ℝ} (hη : ∀ μ ν, η μ ν = η ν μ) (a μ : ι) :
    R.momentum (R.quadraticLagrangian (gaugeConstants η)) a μ = -R.raisedFieldStrength η μ a := by
  rw [momentum_quadraticLagrangian (gaugeConstants_symm hη), raisedFieldStrength]
  have h1 : ∑ b, ∑ ν, algebraMap ℝ J (gaugeConstants η a μ b ν) * R.u b {ν} =
      ∑ b, ∑ ν, (algebraMap ℝ J (η μ b * η ν a) * R.u b {ν} -
        algebraMap ℝ J (η μ ν * η a b) * R.u b {ν}) :=
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun ν _ => by
      rw [gaugeConstants, map_neg, map_sub]
      ring
  have h2 : ∑ b, ∑ ν, algebraMap ℝ J (η μ b * η ν a) * R.u b {ν} =
      ∑ ν, ∑ b, algebraMap ℝ J (η μ ν * η a b) * R.u ν {b} :=
    Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun b _ => by rw [hη b a]
  rw [h1]
  simp only [Finset.sum_sub_distrib]
  rw [h2, Finset.sum_comm (f := fun b ν => algebraMap ℝ J (η μ ν * η a b) * R.u b {ν})]
  simp only [fieldStrength, mul_sub, Finset.sum_sub_distrib]
  ring

/-- For a symmetric matrix `η` the Euler–Lagrange expressions of the Lagrangian of a one-form
satisfy `Σₐ Dₐ Eₐ(L) = 0`. -/
theorem divergence_euler_gauge {η : ι → ι → ℝ} (hη : ∀ μ ν, η μ ν = η ν μ) :
    ∑ a, R.totalDeriv a (R.euler a (R.quadraticLagrangian (gaugeConstants η))) = 0 :=
  divergence_euler_quadraticLagrangian (gaugeConstants_symm hη) (gaugeConstants_antisymm hη)

/-- The canonical stress tensor of the one-form is conserved. -/
theorem conserved_stress_gauge (η : ι → ι → ℝ) (ν : ι) :
    R.Conserved (R.quadraticLagrangian (gaugeConstants η))
      fun μ => R.stress (R.quadraticLagrangian (gaugeConstants η)) μ ν := by
  refine conserved_stress (firstOrder_quadraticLagrangian _) ν ?_
  simp only [quadraticLagrangian, map_sum, SmoothDerivation.map_mul, smul_eq_mul,
    SmoothDerivation.map_algebraMap, R.dx_u, mul_zero, add_zero, Finset.sum_const_zero]

end ProjectAinos.Variational.FieldJetRing
