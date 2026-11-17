/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothAlgebra.FormalSeries.NormalForm
public import ProjectAinos.SmoothAlgebra.FormalSeries.Scaling
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases

/-!
# The normal form of the anharmonic oscillator

For the formal Hamiltonian `ν (q² + p²)/2 + a q³ + b q⁴` the Birkhoff normal
form is `h(action)` with `h = ν x + (3b/2 − 15a²/(4ν)) x² + ⋯`
(`exists_normal_form`). The terms of degree three and four are removed by the
Lie transforms of the explicit generators `generator₃` and `generator₄`, and
the higher degrees by the general theorem.
-/

@[expose] public section
noncomputable section

open MvPowerSeries
open ProjectAinos.SmoothAlgebra.FormalSeries

namespace ProjectAinos.Mechanics.AnharmonicNormalForm

local notation "q" => (X 0 : PhaseSeries)
local notation "p" => (X 1 : PhaseSeries)

variable {ν : ℝ}

/-- The polynomial `3q²p + 2p³`, whose bracket with the action is `3q³`. -/
def cubic : PhaseSeries := 3 • (q ^ 2 * p) + 2 • p ^ 3

/-- The polynomial `5q³p + 3qp³`. -/
def quarticA : PhaseSeries := 5 • (q ^ 3 * p) + 3 • (q * p ^ 3)

/-- The polynomial `qp³ − q³p`. -/
def quarticB : PhaseSeries := q * p ^ 3 - q ^ 3 * p

theorem bracket_action_cubic : bracket action cubic = 3 • q ^ 3 := by
  rw [bracket_action, cubic]
  simp only [map_add, map_nsmul, Derivation.leibniz, Derivation.leibniz_pow,
    pderiv_zero_X_zero, pderiv_one_X_one, pderiv_zero_X_one, pderiv_one_X_zero, smul_eq_mul,
    Nat.reduceSub]
  ring

theorem bracket_cubic_pow : bracket cubic (q ^ 3) = -(9 • q ^ 4 + 18 • (q ^ 2 * p ^ 2)) := by
  rw [bracket, cubic]
  simp only [map_add, map_nsmul, Derivation.leibniz, Derivation.leibniz_pow,
    pderiv_zero_X_zero, pderiv_one_X_one, pderiv_zero_X_one, pderiv_one_X_zero, smul_eq_mul,
    Nat.reduceSub]
  ring

theorem bracket_action_quarticA :
    bracket action quarticA = 8 • q ^ 4 - 3 • (q ^ 2 + p ^ 2) ^ 2 := by
  rw [bracket_action, quarticA]
  simp only [map_add, map_nsmul, Derivation.leibniz, Derivation.leibniz_pow,
    pderiv_zero_X_zero, pderiv_one_X_one, pderiv_zero_X_one, pderiv_one_X_zero, smul_eq_mul,
    Nat.reduceSub]
  ring

theorem bracket_action_quarticB :
    bracket action quarticB = 8 • (q ^ 2 * p ^ 2) - (q ^ 2 + p ^ 2) ^ 2 := by
  rw [bracket_action, quarticB]
  simp only [map_sub, Derivation.leibniz, Derivation.leibniz_pow,
    pderiv_zero_X_zero, pderiv_one_X_one, pderiv_zero_X_one, pderiv_one_X_zero, smul_eq_mul,
    Nat.reduceSub]
  ring

theorem action_sq : action ^ 2 = (4⁻¹ : ℝ) • (q ^ 2 + p ^ 2) ^ 2 := by
  rw [action, smul_pow]
  norm_num

theorem X_pow_mem_homogeneous (i : Fin 2) (n : ℕ) : (X i : PhaseSeries) ^ n ∈ homogeneous n := by
  simpa using pow_mem_homogeneous (X_mem_homogeneous i) n

theorem cubic_mem : cubic ∈ homogeneous 3 :=
  add_mem (Submodule.smul_of_tower_mem _ 3
      (mul_mem_homogeneous (X_pow_mem_homogeneous 0 2) (X_mem_homogeneous 1)))
    (Submodule.smul_of_tower_mem _ 2 (X_pow_mem_homogeneous 1 3))

theorem quarticA_mem : quarticA ∈ homogeneous 4 :=
  add_mem (Submodule.smul_of_tower_mem _ 5
      (mul_mem_homogeneous (X_pow_mem_homogeneous 0 3) (X_mem_homogeneous 1)))
    (Submodule.smul_of_tower_mem _ 3
      (mul_mem_homogeneous (X_mem_homogeneous 0) (X_pow_mem_homogeneous 1 3)))

theorem quarticB_mem : quarticB ∈ homogeneous 4 :=
  sub_mem (mul_mem_homogeneous (X_mem_homogeneous 0) (X_pow_mem_homogeneous 1 3))
    (mul_mem_homogeneous (X_pow_mem_homogeneous 0 3) (X_mem_homogeneous 1))

/-- The formal Hamiltonian `ν (q² + p²)/2 + a q³ + b q⁴`. -/
def hamiltonian (ν a b : ℝ) : PhaseSeries := ν • action + a • q ^ 3 + b • q ^ 4

/-- The generator that removes the cubic term. -/
def generator₃ (ν a : ℝ) : PhaseSeries := (a / (3 * ν)) • cubic

/-- The terms of degree four after the cubic term is removed. -/
def quarticPart (ν a b : ℝ) : PhaseSeries :=
  (b - 3 * a ^ 2 / (2 * ν)) • q ^ 4 + (-(3 * a ^ 2 / ν)) • (q ^ 2 * p ^ 2)

/-- A solution of the homological equation for `quarticPart`. -/
def quarticGenerator (ν a b : ℝ) : PhaseSeries :=
  ((b - 3 * a ^ 2 / (2 * ν)) / 8) • quarticA + (-(3 * a ^ 2 / ν) / 8) • quarticB

/-- The generator that removes the non-resonant terms of degree four. -/
def generator₄ (ν a b : ℝ) : PhaseSeries := ν⁻¹ • quarticGenerator ν a b

/-- The coefficient of the square of the action in the normal form. -/
def secondCoefficient (ν a b : ℝ) : ℝ := 3 * b / 2 - 15 * a ^ 2 / (4 * ν)

theorem generator₃_mem (ν a : ℝ) : generator₃ ν a ∈ orderGE (Fin 2) 3 :=
  Submodule.smul_mem _ _ (homogeneous_le_orderGE 3 cubic_mem)

theorem generator₄_mem (ν a b : ℝ) : generator₄ ν a b ∈ orderGE (Fin 2) 4 :=
  Submodule.smul_mem _ _ (homogeneous_le_orderGE 4
    (add_mem (Submodule.smul_mem _ _ quarticA_mem) (Submodule.smul_mem _ _ quarticB_mem)))

theorem quarticPart_mem (ν a b : ℝ) : quarticPart ν a b ∈ orderGE (Fin 2) 4 :=
  homogeneous_le_orderGE 4 (add_mem (Submodule.smul_mem _ _ (X_pow_mem_homogeneous 0 4))
    (Submodule.smul_mem _ _
      (mul_mem_homogeneous (X_pow_mem_homogeneous 0 2) (X_pow_mem_homogeneous 1 2))))

theorem bracket_generator₃_action (hν : ν ≠ 0) (a : ℝ) :
    bracket (generator₃ ν a) (ν • action) = -(a • q ^ 3) := by
  rw [generator₃, bracket_smul_left, bracket_smul_right, bracket_swap action cubic,
    bracket_action_cubic, smul_smul]
  have hs : a / (3 * ν) * ν = a / 3 := by
    field_simp
  rw [hs]
  module

theorem smul_bracket_generator₃_pow (ν a b : ℝ) :
    quarticPart ν a b = b • q ^ 4 + (a / 2) • bracket (generator₃ ν a) (q ^ 3) := by
  rw [generator₃, bracket_smul_left, bracket_cubic_pow, quarticPart]
  module

theorem quarticPart_eq (ν a b : ℝ) :
    quarticPart ν a b =
      bracket action (quarticGenerator ν a b) + secondCoefficient ν a b • action ^ 2 := by
  rw [quarticGenerator, bracket_add_right, bracket_smul_right, bracket_smul_right,
    bracket_action_quarticA, bracket_action_quarticB, action_sq, quarticPart, secondCoefficient]
  module

theorem bracket_generator₄_action (hν : ν ≠ 0) (a b : ℝ) :
    bracket (generator₄ ν a b) (ν • action) =
      -(quarticPart ν a b - secondCoefficient ν a b • action ^ 2) := by
  rw [generator₄, bracket_smul_left, bracket_smul_right, smul_smul, inv_mul_cancel₀ hν,
    one_smul, bracket_swap action (quarticGenerator ν a b), quarticPart_eq]
  abel

theorem hamiltonian_mem (ν a b : ℝ) : hamiltonian ν a b ∈ orderGE (Fin 2) 2 :=
  add_mem (add_mem (Submodule.smul_mem _ _ (homogeneous_le_orderGE 2 action_mem_homogeneous))
      (Submodule.smul_mem _ _ (mem_orderGE_of_le
        (homogeneous_le_orderGE 3 (X_pow_mem_homogeneous 0 3)) (by norm_num))))
    (Submodule.smul_mem _ _ (mem_orderGE_of_le
      (homogeneous_le_orderGE 4 (X_pow_mem_homogeneous 0 4)) (by norm_num)))

/-- The Lie transform of `generator₃` removes the cubic term. -/
theorem lieExp_generator₃ (hν : ν ≠ 0) (a b : ℝ) :
    lieExp (ad (generator₃ ν a)) (hamiltonian ν a b) - (ν • action + quarticPart ν a b) ∈
      orderGE (Fin 2) 5 := by
  have hF := generator₃_mem ν a
  have hq3 : q ^ 3 ∈ orderGE (Fin 2) 3 := homogeneous_le_orderGE 3 (X_pow_mem_homogeneous 0 3)
  have hq4 : q ^ 4 ∈ orderGE (Fin 2) 4 := homogeneous_le_orderGE 4 (X_pow_mem_homogeneous 0 4)
  have hB3 : bracket (generator₃ ν a) (q ^ 3) ∈ orderGE (Fin 2) 4 := bracket_mem_orderGE hF hq3
  have hB4 : bracket (generator₃ ν a) (q ^ 4) ∈ orderGE (Fin 2) 5 := bracket_mem_orderGE hF hq4
  have h_ad1 : ad (generator₃ ν a) (hamiltonian ν a b) =
      -(a • q ^ 3) + a • bracket (generator₃ ν a) (q ^ 3) +
        b • bracket (generator₃ ν a) (q ^ 4) := by
    rw [ad_apply, hamiltonian, bracket_add_right, bracket_add_right,
      bracket_smul_right a (generator₃ ν a) (q ^ 3),
      bracket_smul_right b (generator₃ ν a) (q ^ 4), bracket_generator₃_action hν]
  have h_ad2 : ad (generator₃ ν a) (ad (generator₃ ν a) (hamiltonian ν a b)) =
      -(a • bracket (generator₃ ν a) (q ^ 3)) +
        a • bracket (generator₃ ν a) (bracket (generator₃ ν a) (q ^ 3)) +
        b • bracket (generator₃ ν a) (bracket (generator₃ ν a) (q ^ 4)) := by
    rw [h_ad1, ad_apply, bracket_add_right, bracket_add_right, bracket_neg_right,
      bracket_smul_right, bracket_smul_right, bracket_smul_right]
  have h3 := lieExp_sub_three_mem (raises_ad (j := 1) hF) le_rfl (hamiltonian_mem ν a b)
  have e : lieExp (ad (generator₃ ν a)) (hamiltonian ν a b) - (ν • action + quarticPart ν a b) =
      (lieExp (ad (generator₃ ν a)) (hamiltonian ν a b) -
        (hamiltonian ν a b + ad (generator₃ ν a) (hamiltonian ν a b) +
          (2⁻¹ : ℝ) • ad (generator₃ ν a) (ad (generator₃ ν a) (hamiltonian ν a b)))) +
      (b • bracket (generator₃ ν a) (q ^ 4) +
        (a / 2) • bracket (generator₃ ν a) (bracket (generator₃ ν a) (q ^ 3)) +
        (b / 2) • bracket (generator₃ ν a) (bracket (generator₃ ν a) (q ^ 4))) := by
    rw [h_ad2, h_ad1, smul_bracket_generator₃_pow ν a b, hamiltonian]
    module
  rw [e]
  refine add_mem (mem_orderGE_of_le h3 (by norm_num)) (add_mem (add_mem ?_ ?_) ?_)
  · exact Submodule.smul_mem _ _ hB4
  · exact Submodule.smul_mem _ _ (mem_orderGE_of_le (bracket_mem_orderGE hF hB3) (by norm_num))
  · exact Submodule.smul_mem _ _ (mem_orderGE_of_le (bracket_mem_orderGE hF hB4) (by norm_num))

/-- The Lie transform of `generator₄` then removes the non-resonant terms of
degree four. -/
theorem lieExp_generator₄ (hν : ν ≠ 0) (a b : ℝ) :
    lieExp (ad (generator₄ ν a b)) (lieExp (ad (generator₃ ν a)) (hamiltonian ν a b)) -
        (ν • action + secondCoefficient ν a b • action ^ 2) ∈ orderGE (Fin 2) 5 := by
  obtain ⟨H₁, hH₁⟩ : ∃ H₁ : PhaseSeries,
      H₁ = lieExp (ad (generator₃ ν a)) (hamiltonian ν a b) := ⟨_, rfl⟩
  rw [← hH₁]
  have hF3 := generator₃_mem ν a
  have hF4 := generator₄_mem ν a b
  have hH₁2 : H₁ ∈ orderGE (Fin 2) 2 :=
    hH₁ ▸ lieExp_mem (raises_ad (j := 1) hF3) le_rfl (hamiltonian_mem ν a b)
  have h1 : H₁ - (ν • action + quarticPart ν a b) ∈ orderGE (Fin 2) 5 :=
    hH₁ ▸ lieExp_generator₃ hν a b
  have h2 := lieExp_sub_add_mem (raises_ad (j := 2) hF4) (by norm_num) hH₁2
  have h3 : H₁ - ν • action ∈ orderGE (Fin 2) 4 := by
    have e : H₁ - ν • action = (H₁ - (ν • action + quarticPart ν a b)) + quarticPart ν a b := by
      abel
    rw [e]
    exact add_mem (mem_orderGE_of_le h1 (by norm_num)) (quarticPart_mem ν a b)
  have h4 := bracket_mem_orderGE hF4 h3
  have e : lieExp (ad (generator₄ ν a b)) H₁ -
      (ν • action + secondCoefficient ν a b • action ^ 2) =
      (lieExp (ad (generator₄ ν a b)) H₁ - (H₁ + ad (generator₄ ν a b) H₁)) +
        (H₁ - (ν • action + quarticPart ν a b)) +
        bracket (generator₄ ν a b) (H₁ - ν • action) := by
    rw [bracket_sub_right, bracket_generator₄_action hν, ad_apply]
    abel
  rw [e]
  exact add_mem (add_mem (mem_orderGE_of_le h2 (by norm_num)) h1)
    (mem_orderGE_of_le h4 (by norm_num))

theorem homogeneousComponent_action_sq {k : ℕ} :
    homogeneousComponent k (action ^ 2) = if k = 4 then action ^ 2 else 0 := by
  have h := action_pow_mem_homogeneous 2
  split_ifs with hk
  · rw [hk]
    exact homogeneousComponent_eq_self h
  · exact homogeneousComponent_eq_zero_of_mem h hk

/-- Landau–Lifshitz §28: the Birkhoff normal form of the anharmonic
oscillator `ν (q² + p²)/2 + a q³ + b q⁴` is `ν I + (3b/2 − 15a²/(4ν)) I² + ⋯`. -/
theorem exists_normal_form (hν : ν ≠ 0) (a b : ℝ) :
    ∃ (Ψ : PhaseSeries ≃ₐ[ℝ] PhaseSeries) (h : PowerSeries ℝ),
      (∀ f g, Ψ (bracket f g) = bracket (Ψ f) (Ψ g)) ∧
        Ψ (hamiltonian ν a b) = PowerSeries.subst action h ∧ PowerSeries.coeff 0 h = 0 ∧
          PowerSeries.coeff 1 h = ν ∧ PowerSeries.coeff 2 h = secondCoefficient ν a b := by
  obtain ⟨H₂, hH₂⟩ : ∃ H₂ : PhaseSeries, H₂ = lieExp (ad (generator₄ ν a b))
      (lieExp (ad (generator₃ ν a)) (hamiltonian ν a b)) := ⟨_, rfl⟩
  have hF3 := generator₃_mem ν a
  have hF4 : generator₄ ν a b ∈ orderGE (Fin 2) 3 :=
    mem_orderGE_of_le (generator₄_mem ν a b) (by norm_num)
  have hmod : H₂ - (ν • action + secondCoefficient ν a b • action ^ 2) ∈ orderGE (Fin 2) 5 :=
    hH₂ ▸ lieExp_generator₄ hν a b
  have hsq : action ^ 2 ∈ orderGE (Fin 2) 4 :=
    homogeneous_le_orderGE 4 (action_pow_mem_homogeneous 2)
  have hH₂' : H₂ - ν • action ∈ orderGE (Fin 2) 3 := by
    have e : H₂ - ν • action = (H₂ - (ν • action + secondCoefficient ν a b • action ^ 2)) +
        secondCoefficient ν a b • action ^ 2 := by
      abel
    rw [e]
    exact add_mem (mem_orderGE_of_le hmod (by norm_num))
      (Submodule.smul_mem _ _ (mem_orderGE_of_le hsq (by norm_num)))
  have hcomp : ∀ k < 5, homogeneousComponent k H₂ =
      ν • homogeneousComponent k action +
        secondCoefficient ν a b • homogeneousComponent k (action ^ 2) := by
    intro k hk
    rw [homogeneousComponent_congr (mem_orderGE_of_le hmod (by omega)), map_add, map_smul,
      map_smul]
  have hres : ∀ k < 5, ∃ c : ℝ, homogeneousComponent k H₂ = c • resonant k := by
    intro k hk
    rw [hcomp k hk, homogeneousComponent_action, homogeneousComponent_action_sq]
    interval_cases k
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨ν, by simp [resonant]⟩
    · exact ⟨0, by simp⟩
    · exact ⟨secondCoefficient ν a b, by
        have h4 : resonant 4 = action ^ 2 := resonant_two_mul 2
        simp [h4]⟩
  obtain ⟨Ψ', h, hΨ', hh, hsub⟩ :=
    exists_normal_form_of_resonant hν hH₂' (N := 5) (by norm_num) hres
  have hlow : ∀ k < 5, homogeneousComponent k (Ψ' H₂) =
      ν • homogeneousComponent k action +
        secondCoefficient ν a b • homogeneousComponent k (action ^ 2) := by
    intro k hk
    rw [homogeneousComponent_congr (mem_orderGE_of_le hsub (by omega)), hcomp k hk]
  refine ⟨(lieAlgEquiv (generator₃ ν a) hF3).trans ((lieAlgEquiv (generator₄ ν a b) hF4).trans Ψ'),
    h, ?_, ?_, ?_, ?_, ?_⟩
  · intro f g
    simp only [AlgEquiv.trans_apply, lieAlgEquiv_apply]
    rw [lieExp_ad_bracket (j := 0) hF3, lieExp_ad_bracket (j := 0) hF4, hΨ']
  · simp only [AlgEquiv.trans_apply, lieAlgEquiv_apply]
    rw [← hH₂, hh]
  · refine coeff_eq_of_homogeneousComponent (m := 0) hh ?_
    rw [hlow 0 (by norm_num), homogeneousComponent_action, homogeneousComponent_action_sq]
    simp
  · refine coeff_eq_of_homogeneousComponent (m := 1) hh ?_
    rw [hlow 2 (by norm_num), homogeneousComponent_action, homogeneousComponent_action_sq]
    simp
  · refine coeff_eq_of_homogeneousComponent (m := 2) hh ?_
    rw [hlow 4 (by norm_num), homogeneousComponent_action, homogeneousComponent_action_sq]
    simp

/-! ### The Hamiltonian in the physical variables -/

/-- The formal Hamiltonian `p²/2 + ν²q²/2 + αq³/3 + βq⁴/4` of the equation
`ẍ + ν²x = −αx² − βx³`. -/
def physicalHamiltonian (ν α β : ℝ) : PhaseSeries :=
  (2⁻¹ : ℝ) • p ^ 2 + (ν ^ 2 / 2) • q ^ 2 + (α / 3) • q ^ 3 + (β / 4) • q ^ 4

/-- The canonical scaling `q ↦ q/s`, `p ↦ s p` carries the Hamiltonian with
the frequency `s²` to the normalized form. -/
theorem scale_physicalHamiltonian {s : ℝ} (hs : s ≠ 0) (α β : ℝ) :
    scale s⁻¹ (inv_ne_zero hs) (physicalHamiltonian (s ^ 2) α β) =
      hamiltonian (s ^ 2) (α / (3 * s ^ 3)) (β / (4 * s ^ 4)) := by
  rw [physicalHamiltonian, hamiltonian, action]
  simp only [map_add, map_smul, map_pow, scale_X_zero, scale_X_one, smul_pow, inv_inv,
    smul_smul, smul_add]
  match_scalars <;> field_simp

/-- Landau–Lifshitz §28 in the physical variables: the Birkhoff normal form of
`p²/2 + ν²q²/2 + αq³/3 + βq⁴/4` is `ν I + (3β/(8ν²) − 5α²/(12ν⁴)) I² + ⋯`. -/
theorem exists_normal_form_physical (hν : 0 < ν) (α β : ℝ) :
    ∃ (Ψ : PhaseSeries ≃ₐ[ℝ] PhaseSeries) (h : PowerSeries ℝ),
      (∀ f g, Ψ (bracket f g) = bracket (Ψ f) (Ψ g)) ∧
        Ψ (physicalHamiltonian ν α β) = PowerSeries.subst action h ∧
          PowerSeries.coeff 0 h = 0 ∧ PowerSeries.coeff 1 h = ν ∧
            PowerSeries.coeff 2 h = 3 * β / (8 * ν ^ 2) - 5 * α ^ 2 / (12 * ν ^ 4) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ ν = s ^ 2 :=
    ⟨√ν, Real.sqrt_pos.mpr hν, (Real.sq_sqrt hν.le).symm⟩
  obtain ⟨Ψ, h, hΨ, hh, h0, h1, h2⟩ :=
    exists_normal_form (pow_ne_zero 2 hs.ne') (α / (3 * s ^ 3)) (β / (4 * s ^ 4))
  refine ⟨(scale s⁻¹ (inv_ne_zero hs.ne')).trans Ψ, h, ?_, ?_, h0, h1, ?_⟩
  · intro f g
    simp only [AlgEquiv.trans_apply]
    rw [scale_bracket, hΨ]
  · simp only [AlgEquiv.trans_apply]
    rw [scale_physicalHamiltonian hs.ne', hh]
  · rw [h2, secondCoefficient]
    field_simp
    ring

/-- The formal frequency `h'(I) = ν + 2c₂I + ⋯` at the action `I = νρ²/2` of
the oscillation of amplitude `ρ` has the correction of
`OneDim.Anharmonic.exists_tendsto_frequency`. -/
theorem two_mul_coefficient_mul_action (hν : ν ≠ 0) (α β ρ : ℝ) :
    2 * (3 * β / (8 * ν ^ 2) - 5 * α ^ 2 / (12 * ν ^ 4)) * (ν * ρ ^ 2 / 2) =
      (3 * β / (8 * ν) - 5 * α ^ 2 / (12 * ν ^ 3)) * ρ ^ 2 := by
  field_simp

end ProjectAinos.Mechanics.AnharmonicNormalForm
