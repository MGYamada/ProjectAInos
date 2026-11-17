/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.StressTensor
public import ProjectAinos.Electrodynamics.FieldClassification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Charged dust and the conservation of the total stress

Charged dust has a density `μ` of the rest mass, a density `ρₑ` of the charge and a
four-velocity `U` (Landau–Lifshitz, *The Classical Theory of Fields*, §35). Its current is
`k = ρₑ U` and its stress tensor is `T_m^{μν} = μ U^μ U^ν`.

* `divergence_matterStress`: if the mass is conserved, `∂_λ (μ U^λ) = 0`, then
  `∂_μ T_m^{μν} = μ U^λ ∂_λ U^ν`.
* `lorentzForce_zero_eq`, `lorentzForce_succ_eq`: the components of the force `e F♯ v` of
  `LorentzForce` are `e E · 𝐯` and `e (v⁰ E + 𝐯 × B)`.
* `total_stress_conserved`: if the dust moves by the Lorentz force,
  `μ U^λ ∂_λ U = ρₑ F♯ U`, and the field satisfies the equations of Maxwell with the current
  of the dust, then `∂_μ T_EM^{μν} + ∂_μ T_m^{μν} = 0` for every `ν`.
* `total_stress_conserved_uniform`: neutral dust that moves uniformly in a constant field is
  an instance.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

/-- Charged dust: the densities of the rest mass and of the charge, and the four-velocity. -/
structure ChargedDust where
  /-- The density `μ` of the rest mass. -/
  massDensity : Spacetime → ℝ
  /-- The density `ρₑ` of the charge in the rest frame. -/
  chargeDensity : Spacetime → ℝ
  /-- The four-velocity `U`. -/
  velocity : Spacetime → Spacetime

namespace ChargedDust

variable (D : ChargedDust)

/-- The current `k = ρₑ U` of the dust. -/
def current : Spacetime → Spacetime := fun y => D.chargeDensity y • D.velocity y

/-- The stress tensor `T_m^{μν} = μ U^μ U^ν` of the dust. -/
def matterStress (μ ν : Fin 4) : Spacetime → ℝ := fun y =>
  (D.massDensity y * D.velocity y μ) * D.velocity y ν

/-- The derivative of `U^ν` along `U`: `U^λ ∂_λ U^ν`. -/
def convective (x : Spacetime) (ν : Fin 4) : ℝ :=
  ∑ l : Fin 4, D.velocity x l * partialAt (fun y => D.velocity y ν) l x

variable {D}

/-- If the mass is conserved, the divergence of the stress of the dust is `μ U^λ ∂_λ U^ν`. -/
theorem divergence_matterStress {x : Spacetime}
    (hμ : ∀ l : Fin 4, DifferentiableAt ℝ (fun y => D.massDensity y * D.velocity y l) x)
    (hU : ∀ ν : Fin 4, DifferentiableAt ℝ (fun y => D.velocity y ν) x)
    (hcont : ∑ l : Fin 4, partialAt (fun y => D.massDensity y * D.velocity y l) l x = 0)
    (ν : Fin 4) :
    ∑ μ : Fin 4, partialAt (D.matterStress μ ν) μ x = D.massDensity x * D.convective x ν := by
  have h : ∀ μ : Fin 4, partialAt (D.matterStress μ ν) μ x =
      D.massDensity x * D.velocity x μ * partialAt (fun y => D.velocity y ν) μ x +
        D.velocity x ν * partialAt (fun y => D.massDensity y * D.velocity y μ) μ x :=
    fun μ => partialAt_mul (hμ μ) (hU ν) μ
  rw [Finset.sum_congr rfl fun μ _ => h μ, Finset.sum_add_distrib, ← Finset.mul_sum, hcont,
    mul_zero, add_zero, convective, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

end ChargedDust

/-! ### The force in components -/

/-- The time component of the force `e F♯ v` is `e E · 𝐯`. -/
theorem lorentzForce_zero_eq (e : ℝ) (G : TwoForm) (v : Spacetime) :
    lorentzForce e G v 0 = e * (electricVector G 0 * v 1 + electricVector G 1 * v 2 +
      electricVector G 2 * v 3) := by
  rw [lorentzForce_vectors]
  rfl

/-- The space components of the force `e F♯ v` are `e (v⁰ E + 𝐯 × B)`. -/
theorem lorentzForce_succ_eq (e : ℝ) (G : TwoForm) (v : Spacetime) :
    lorentzForce e G v 1 = e * (v 0 * electricVector G 0 + (v 2 * magneticVector G 2 -
      v 3 * magneticVector G 1)) ∧
    lorentzForce e G v 2 = e * (v 0 * electricVector G 1 + (v 3 * magneticVector G 0 -
      v 1 * magneticVector G 2)) ∧
    lorentzForce e G v 3 = e * (v 0 * electricVector G 2 + (v 1 * magneticVector G 1 -
      v 2 * magneticVector G 0)) := by
  rw [lorentzForce_vectors]
  exact ⟨rfl, rfl, rfl⟩

/-! ### The conservation of the total stress -/

/-- The total stress of the field and of charged dust is conserved: if the dust conserves its
mass and moves by the Lorentz force, and the field satisfies the equations of Maxwell with the
current of the dust, then `∂_μ T_EM^{μν} + ∂_μ T_m^{μν} = 0`. -/
theorem total_stress_conserved {F : Field} {D : ChargedDust} {x : Spacetime}
    (hF : DifferentiableAt ℝ F x)
    (hμ : ∀ l : Fin 4, DifferentiableAt ℝ (fun y => D.massDensity y * D.velocity y l) x)
    (hU : ∀ ν : Fin 4, DifferentiableAt ℝ (fun y => D.velocity y ν) x)
    (hcont : ∑ l : Fin 4, partialAt (fun y => D.massDensity y * D.velocity y l) l x = 0)
    (hmotion : ∀ ν : Fin 4, D.massDensity x * D.convective x ν =
      lorentzForce (D.chargeDensity x) (F x) (D.velocity x) ν)
    (hgB : divergence3 (magneticField F) x = 0)
    (hfar : ∀ i, partialAt (magneticField F i) 0 x + curl (electricField F) x i = 0)
    (hgE : divergence3 (electricField F) x = D.current x 0)
    (hamp : ∀ i, curl (magneticField F) x i - partialAt (electricField F i) 0 x =
      D.current x i.succ)
    (ν : Fin 4) :
    ∑ μ : Fin 4, partialAt (raisedStress F μ ν) μ x +
      ∑ μ : Fin 4, partialAt (D.matterStress μ ν) μ x = 0 := by
  rw [ChargedDust.divergence_matterStress hμ hU hcont ν, hmotion ν]
  have hk (μ : Fin 4) : D.current x μ = D.chargeDensity x * D.velocity x μ := rfl
  refine Fin.cases ?_ (fun i => ?_) ν
  · rw [divergence_raisedStress_zero hF hfar hamp, lorentzForce_zero_eq]
    simp only [hk, electricField]
    ring
  · rw [divergence_raisedStress_succ hF hgB hfar hgE hamp i]
    obtain ⟨h1, h2, h3⟩ := lorentzForce_succ_eq (D.chargeDensity x) (F x) (D.velocity x)
    fin_cases i
    · change -forceDensity F D.current x 0 + lorentzForce _ _ _ 1 = 0
      rw [h1]
      simp only [forceDensity, hk, electricField, magneticField, Matrix.cons_val]
      ring
    · change -forceDensity F D.current x 1 + lorentzForce _ _ _ 2 = 0
      rw [h2]
      simp only [forceDensity, hk, electricField, magneticField, Matrix.cons_val]
      ring
    · change -forceDensity F D.current x 2 + lorentzForce _ _ _ 3 = 0
      rw [h3]
      simp only [forceDensity, hk, electricField, magneticField, Matrix.cons_val]
      ring

/-! ### An instance -/

theorem partialAt_const (c : ℝ) (μ : Fin 4) (x : Spacetime) :
    partialAt (fun _ => c) μ x = 0 := by
  rw [partialAt, fderiv_const_apply]
  rfl

/-- Neutral dust of the constant density `μ₀` that moves with the constant four-velocity
`U₀`. -/
def ChargedDust.uniform (μ₀ : ℝ) (U₀ : Spacetime) : ChargedDust where
  massDensity := fun _ => μ₀
  chargeDensity := fun _ => 0
  velocity := fun _ => U₀

/-- An instance of the conservation of the total stress: neutral dust that moves uniformly in a
constant field satisfies all the hypotheses of `total_stress_conserved`. -/
theorem total_stress_conserved_uniform (μ₀ : ℝ) (U₀ : Spacetime) (F₀ : TwoForm)
    (x : Spacetime) (ν : Fin 4) :
    ∑ μ : Fin 4, partialAt (raisedStress (fun _ => F₀) μ ν) μ x +
      ∑ μ : Fin 4, partialAt ((ChargedDust.uniform μ₀ U₀).matterStress μ ν) μ x = 0 := by
  have hE : ∀ i, electricField (fun _ => F₀) i = fun _ => electricVector F₀ i :=
    fun i => rfl
  have hB : ∀ i, magneticField (fun _ => F₀) i = fun _ => magneticVector F₀ i :=
    fun i => rfl
  have hk : ∀ μ, (ChargedDust.uniform μ₀ U₀).current x μ = 0 := fun μ => by
    simp [ChargedDust.current, ChargedDust.uniform]
  refine total_stress_conserved (differentiableAt_const _)
    (fun _ => differentiableAt_const (μ₀ * U₀ _)) (fun _ => differentiableAt_const (U₀ _)) ?_
    (fun ν => ?_) ?_ (fun i => ?_) ?_ (fun i => ?_) ν
  · simp [ChargedDust.uniform, partialAt_const]
  · simp [ChargedDust.convective, ChargedDust.uniform, partialAt_const]
  · simp [divergence3, hB, partialAt_const]
  · fin_cases i <;> simp [curl, hE, hB, partialAt_const]
  · simp [divergence3, hE, partialAt_const, hk]
  · fin_cases i <;> simp [curl, hE, hB, partialAt_const, hk]

end ProjectAinos.Electrodynamics
