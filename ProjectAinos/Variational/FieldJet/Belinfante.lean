/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Variational.FieldJet.Quadratic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The symmetric stress tensor of a one-form and the canonical tensor

For the Lagrangian `L = −¼ F_{μν} F^{μν}` of a one-form `A` with a constant symmetric matrix `η`
(`quadraticLagrangian (gaugeConstants η)`), the symmetric tensor
`Θ^μ_ν = F^{μa} F_{νa} + δ^μ_ν L` (`symmetricStress`) and the canonical tensor of the
translations `T^μ_ν = Σₐ A_{a,ν} π^μ_a − δ^μ_ν L` (`FieldJetRing.stress`) differ by a divergence
and a multiple of the Euler–Lagrange expressions:

* `symmetricStress_add_stress`: `Θ^μ_ν + T^μ_ν + Σₐ Dₐ(F^{μa} A_ν) = −A_ν E_μ(L)`, so
  `Θ = −T − Dₐ(F^{μa} A_ν)` modulo the field equations (`symmetricStress_add_stress_mem`);
* `divergence_belinfante`: the added term is divergence-free identically,
  `Σ_μ D_μ Σₐ Dₐ(F^{μa} A_ν) = 0`, because `F^{μa}` is antisymmetric;
* `conserved_symmetricStress`: `Θ` is conserved, as `T` is.

The sign of `T` is that of the energy `T^0_0 = H`; with the signature `(−+++)` the symmetric
tensor `Θ^0_0 = η^{00} Θ_{00}` is minus the energy density, which is the sign in the relation
(Landau–Lifshitz, §§32–33).
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.Variational.FieldJetRing

open SmoothAlgebra

variable {ι J : Type*} [CommRing J] [Algebra ℝ J] [SmoothRing J] [Fintype ι] [DecidableEq ι]
  {R : FieldJetRing ι ι J}

omit [DecidableEq ι] in
/-- The raised field strength is antisymmetric. -/
theorem raisedFieldStrength_antisymm (η : ι → ι → ℝ) (μ a : ι) :
    R.raisedFieldStrength η μ a = -R.raisedFieldStrength η a μ := by
  simp only [raisedFieldStrength, fieldStrength]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp only [map_mul]
  ring

/-- The Euler–Lagrange expressions of the Lagrangian of a one-form: `E_b = Σ_μ D_μ F^{μb}`. -/
theorem euler_gauge {η : ι → ι → ℝ} (hη : ∀ μ ν, η μ ν = η ν μ) (b : ι) :
    R.euler b (R.quadraticLagrangian (gaugeConstants η)) =
      ∑ μ, R.totalDeriv μ (R.raisedFieldStrength η μ b) := by
  rw [euler_of_firstOrder (firstOrder_quadraticLagrangian _), d_zero_quadraticLagrangian,
    zero_sub, divergence]
  simp only [momentum_gauge hη, map_neg, Finset.sum_neg_distrib, neg_neg]

variable (R) in
/-- The symmetric stress tensor `Θ^μ_ν = F^{μa} F_{νa} + δ^μ_ν L` of a one-form. -/
def symmetricStress (η : ι → ι → ℝ) (μ ν : ι) : J :=
  ∑ a, R.raisedFieldStrength η μ a * R.fieldStrength ν a +
    if μ = ν then R.quadraticLagrangian (gaugeConstants η) else 0

/-- **The symmetric and the canonical tensor**:
`Θ^μ_ν + T^μ_ν + Σₐ Dₐ(F^{μa} A_ν) = −A_ν E_μ(L)`. -/
theorem symmetricStress_add_stress {η : ι → ι → ℝ} (hη : ∀ μ ν, η μ ν = η ν μ) (μ ν : ι) :
    R.symmetricStress η μ ν + R.stress (R.quadraticLagrangian (gaugeConstants η)) μ ν +
        R.divergence (fun a => R.raisedFieldStrength η μ a * R.u ν 0) =
      -(R.u ν 0 * R.euler μ (R.quadraticLagrangian (gaugeConstants η))) := by
  have hD (a : ι) : R.totalDeriv a (R.raisedFieldStrength η μ a * R.u ν 0) =
      R.raisedFieldStrength η μ a * R.u ν {a} -
        R.u ν 0 * R.totalDeriv a (R.raisedFieldStrength η a μ) := by
    rw [SmoothDerivation.map_mul, totalDeriv_u, Multiset.cons_zero,
      raisedFieldStrength_antisymm η μ a, map_neg, smul_eq_mul, smul_eq_mul]
    ring
  have h1 : ∑ a, R.raisedFieldStrength η μ a * R.fieldStrength ν a +
      ∑ a, R.u a {ν} * -R.raisedFieldStrength η μ a +
      ∑ a, (R.raisedFieldStrength η μ a * R.u ν {a} -
        R.u ν 0 * R.totalDeriv a (R.raisedFieldStrength η a μ)) =
      -(R.u ν 0 * ∑ a, R.totalDeriv a (R.raisedFieldStrength η a μ)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by simp only [fieldStrength]; ring
  rw [euler_gauge hη μ, ← h1]
  simp only [symmetricStress, stress, momentum_gauge hη, divergence, hD]
  ring

/-- The symmetric tensor is `−T − Dₐ(F^{μa} A_ν)` modulo the field equations. -/
theorem symmetricStress_add_stress_mem {η : ι → ι → ℝ} (hη : ∀ μ ν, η μ ν = η ν μ) (μ ν : ι) :
    R.symmetricStress η μ ν + R.stress (R.quadraticLagrangian (gaugeConstants η)) μ ν +
        R.divergence (fun a => R.raisedFieldStrength η μ a * R.u ν 0) ∈
      R.eulerLagrangeIdeal (R.quadraticLagrangian (gaugeConstants η)) := by
  rw [symmetricStress_add_stress hη μ ν]
  exact neg_mem (Ideal.mul_mem_left _ _ (euler_mem _ μ))

/-- The term of Belinfante is divergence-free identically:
`Σ_μ D_μ Σₐ Dₐ(F^{μa} A_ν) = 0`. -/
theorem divergence_belinfante (η : ι → ι → ℝ) (ν : ι) :
    R.divergence (fun μ => R.divergence (fun a => R.raisedFieldStrength η μ a * R.u ν 0)) =
      0 := by
  apply eq_zero_of_eq_neg
  simp only [divergence, map_sum]
  calc ∑ μ, ∑ a, R.totalDeriv μ (R.totalDeriv a (R.raisedFieldStrength η μ a * R.u ν 0)) =
        ∑ a, ∑ μ, R.totalDeriv μ (R.totalDeriv a (R.raisedFieldStrength η μ a * R.u ν 0)) :=
        Finset.sum_comm
    _ = -∑ μ, ∑ a, R.totalDeriv μ (R.totalDeriv a (R.raisedFieldStrength η μ a * R.u ν 0)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [totalDeriv_comm, raisedFieldStrength_antisymm η μ a, neg_mul, map_neg, map_neg]

/-- **The symmetric tensor is conserved.** -/
theorem conserved_symmetricStress {η : ι → ι → ℝ} (hη : ∀ μ ν, η μ ν = η ν μ) (ν : ι) :
    R.Conserved (R.quadraticLagrangian (gaugeConstants η))
      fun μ => R.symmetricStress η μ ν := by
  have hT : R.Conserved (R.quadraticLagrangian (gaugeConstants η))
      fun μ => R.stress (R.quadraticLagrangian (gaugeConstants η)) μ ν :=
    conserved_stress_gauge η ν
  have heq : R.divergence (fun μ => R.symmetricStress η μ ν) =
      -R.divergence (fun μ => R.stress (R.quadraticLagrangian (gaugeConstants η)) μ ν) -
        R.divergence (fun μ => R.divergence
          (fun a => R.raisedFieldStrength η μ a * R.u ν 0)) -
        ∑ μ, R.totalDeriv μ (R.u ν 0 * R.euler μ (R.quadraticLagrangian (gaugeConstants η))) := by
    have h (μ : ι) : R.symmetricStress η μ ν =
        -R.stress (R.quadraticLagrangian (gaugeConstants η)) μ ν -
          R.divergence (fun a => R.raisedFieldStrength η μ a * R.u ν 0) -
          R.u ν 0 * R.euler μ (R.quadraticLagrangian (gaugeConstants η)) := by
      linear_combination symmetricStress_add_stress (R := R) hη μ ν
    simp only [divergence, h, map_sub, map_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  unfold Conserved
  rw [heq, divergence_belinfante, sub_zero]
  refine sub_mem (neg_mem hT) (sum_mem fun μ _ => ?_)
  rw [SmoothDerivation.map_mul, smul_eq_mul, smul_eq_mul]
  refine add_mem (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_right _ _ (euler_mem _ μ))
  rw [← iterTotalDeriv_singleton]
  exact Ideal.subset_span ⟨μ, {μ}, rfl⟩

end ProjectAinos.Variational.FieldJetRing
