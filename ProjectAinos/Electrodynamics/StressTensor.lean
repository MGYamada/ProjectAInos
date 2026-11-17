/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.EnergyMomentum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# The stress tensor of the electromagnetic field

For a two-form `G` on space-time,
`stressForm G v w = g⁻¹(ι_v G, ι_w G) − ¼ g(v, w) G_{αβ} G^{αβ}` is the stress tensor
`T_{μν} = G_{μα} G_ν{}^α − ¼ g_{μν} G²` as a bilinear form (Landau–Lifshitz, *The Classical Theory
of Fields*, §33; target E18 of the plan).

* `stressForm_symm`: it is symmetric, and `stressForm_trace`: its trace `g^{μν} T_{μν}` is zero.
* `stressForm_observer`: for every observer `u`, `T(u, u) = ½ (|E_u|² + |B_u|²)` with the electric
  and the magnetic covector of `u`.
* In the frame of the co-ordinates, `T₀₀ = ½ (E² + B²)`, `T₀ᵢ = −(E × B)ᵢ` and
  `Tᵢⱼ = −(Eᵢ Eⱼ + Bᵢ Bⱼ) + ½ δᵢⱼ (E² + B²)` (`stressForm_zero_zero`, `stressForm_zero_succ`,
  `stressForm_succ_succ`): the energy density, minus the vector of Poynting and the stress of
  Maxwell of `EnergyMomentum`.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

/-- The stress tensor `T(v, w) = g⁻¹(ι_v G, ι_w G) − ¼ g(v, w) G_{αβ} G^{αβ}`. -/
def stressForm (G : TwoForm) (v w : Spacetime) : ℝ :=
  covectorPairing (G.curryLeft v) (G.curryLeft w) -
    (1 / 4 : ℝ) * minkowskiForm .timeNegative 3 v w * tensorContraction G G

theorem covectorPairing_comm (a b : OneForm) : covectorPairing a b = covectorPairing b a := by
  simp only [covectorPairing]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The stress tensor is symmetric. -/
theorem stressForm_symm (G : TwoForm) (v w : Spacetime) : stressForm G v w = stressForm G w v := by
  rw [stressForm, stressForm, covectorPairing_comm, minkowskiForm_symmetric]

theorem oneCovector_curryLeft_single (G : TwoForm) (v : Spacetime) (α : Fin 4) :
    oneCovector (G.curryLeft v) (Pi.single α 1) = G ![v, Pi.single α 1] :=
  oneCovector_curryLeft G v _

theorem lorentzSign_sq (μ : Fin 4) :
    lorentzSign .timeNegative μ * lorentzSign .timeNegative μ = 1 := by
  by_cases h : μ = 0 <;> simp [lorentzSign, h]

theorem minkowskiForm_single (μ ν : Fin 4) :
    minkowskiForm .timeNegative 3 (Pi.single μ 1) (Pi.single ν 1) =
      if μ = ν then lorentzSign .timeNegative μ else 0 := by
  rw [minkowskiForm_apply, Finset.sum_eq_single μ]
  · by_cases h : μ = ν
    · subst h; simp
    · simp [h]
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · intro h
    exact absurd (Finset.mem_univ μ) h

/-- The trace `g^{μν} T_{μν}` of the stress tensor is zero in four dimensions. -/
theorem stressForm_trace (G : TwoForm) :
    ∑ μ : Fin 4, lorentzSign .timeNegative μ * stressForm G (Pi.single μ 1) (Pi.single μ 1) =
      0 := by
  have hc : tensorContraction G G = ∑ μ : Fin 4, ∑ α : Fin 4, lorentzSign .timeNegative μ *
      (lorentzSign .timeNegative α * (G ![Pi.single μ 1, Pi.single α 1] *
        G ![Pi.single μ 1, Pi.single α 1])) := by
    simp only [tensorContraction, raisedComponent, component]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun α _ => by ring
  have hsum : ∑ μ : Fin 4, lorentzSign .timeNegative μ * lorentzSign .timeNegative μ = 4 := by
    simp only [lorentzSign_sq]
    norm_num
  simp only [stressForm, covectorPairing, oneCovector_curryLeft_single, minkowskiForm_single,
    ↓reduceIte, mul_sub, Finset.sum_sub_distrib]
  have h4 : ∑ μ : Fin 4, lorentzSign .timeNegative μ *
      ((1 / 4 : ℝ) * lorentzSign .timeNegative μ * tensorContraction G G) =
      (1 / 4 : ℝ) * (∑ μ : Fin 4, lorentzSign .timeNegative μ * lorentzSign .timeNegative μ) *
        tensorContraction G G := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun μ _ => by ring
  have h3 : ∑ μ : Fin 4, lorentzSign .timeNegative μ * ∑ α : Fin 4,
      lorentzSign .timeNegative α * G ![Pi.single μ 1, Pi.single α 1] *
        G ![Pi.single μ 1, Pi.single α 1] = tensorContraction G G := by
    rw [hc]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun α _ => by ring
  rw [h3, h4, hsum]
  ring

/-- For every observer, `T(u, u) = ½ (|E_u|² + |B_u|²)`. -/
theorem stressForm_observer (u : Observer 3) (G : TwoForm) :
    stressForm G u.velocity u.velocity =
      (1 / 2 : ℝ) * (covectorPairing (electric u G) (electric u G) +
        covectorPairing (magnetic u G) (magnetic u G)) := by
  have hE : G.curryLeft u.velocity = -electric u G := by
    rw [electric, neg_neg]
  have hg : minkowskiForm .timeNegative 3 u.velocity u.velocity = -1 := by
    rw [metric_eq]
    change -1 * intervalQuadratic u.velocity = -1
    rw [u.unit, mul_one]
  have hs := scalarInvariant_observer u G
  have hneg : covectorPairing (-electric u G) (-electric u G) =
      covectorPairing (electric u G) (electric u G) := by
    simp only [covectorPairing, map_neg, neg_apply]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [stressForm, hE, hneg, hg]
  rw [scalarInvariant] at hs
  linear_combination (1 / 2 : ℝ) * hs

/-! ### The components in the frame of the co-ordinates -/

theorem tensorContraction_vectors (G : TwoForm) :
    tensorContraction G G = 2 * (∑ i : Fin 3, magneticVector G i ^ 2 -
      ∑ i : Fin 3, electricVector G i ^ 2) := by
  rw [← scalarInvariant_vectors]
  simp only [scalarInvariant]
  ring

/-- `T₀₀ = ½ (E² + B²)`. -/
theorem stressForm_zero_zero (G : TwoForm) :
    stressForm G (Pi.single 0 1) (Pi.single 0 1) =
      (1 / 2 : ℝ) * (∑ i : Fin 3, electricVector G i ^ 2 +
        ∑ i : Fin 3, magneticVector G i ^ 2) := by
  rw [stressForm, tensorContraction_vectors, minkowskiForm_single]
  simp only [covectorPairing, oneCovector_curryLeft_single, twoForm_apply_vectors,
    Fin.sum_univ_four, Fin.sum_univ_three, ↓reduceIte]
  simp [lorentzSign]
  ring

/-- `T₀ᵢ = −(E × B)ᵢ`. -/
theorem stressForm_zero_succ (G : TwoForm) :
    stressForm G (Pi.single 0 1) (Pi.single 1 1) =
        -(electricVector G 1 * magneticVector G 2 - electricVector G 2 * magneticVector G 1) ∧
      stressForm G (Pi.single 0 1) (Pi.single 2 1) =
        -(electricVector G 2 * magneticVector G 0 - electricVector G 0 * magneticVector G 2) ∧
      stressForm G (Pi.single 0 1) (Pi.single 3 1) =
        -(electricVector G 0 * magneticVector G 1 - electricVector G 1 * magneticVector G 0) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [stressForm, minkowskiForm_single]
    simp only [covectorPairing, oneCovector_curryLeft_single, twoForm_apply_vectors,
      Fin.sum_univ_four]
    simp [lorentzSign]
    ring

/-- `Tᵢⱼ = −(Eᵢ Eⱼ + Bᵢ Bⱼ) + ½ δᵢⱼ (E² + B²)`, the stress of Maxwell. -/
theorem stressForm_succ_succ (G : TwoForm) (i j : Fin 3) :
    stressForm G (Pi.single i.succ 1) (Pi.single j.succ 1) =
      -(electricVector G i * electricVector G j + magneticVector G i * magneticVector G j) +
        if i = j then (1 / 2 : ℝ) * (∑ l : Fin 3, electricVector G l ^ 2 +
          ∑ l : Fin 3, magneticVector G l ^ 2) else 0 := by
  rw [stressForm, tensorContraction_vectors, minkowskiForm_single]
  fin_cases i <;> fin_cases j <;>
  · simp only [covectorPairing, oneCovector_curryLeft_single, twoForm_apply_vectors,
      Fin.sum_univ_four, Fin.sum_univ_three]
    simp [lorentzSign]
    ring

/-! ### The divergence -/

/-- The component `T^{μν} = g^{μμ} g^{νν} T_{μν}` of the stress tensor of a field, as a function
on space-time. -/
def raisedStress (F : Field) (μ ν : Fin 4) : Spacetime → ℝ := fun y =>
  lorentzSign .timeNegative μ * lorentzSign .timeNegative ν *
    stressForm (F y) (Pi.single μ 1) (Pi.single ν 1)

theorem lorentzSign_zero : lorentzSign .timeNegative (0 : Fin 4) = -1 := by simp [lorentzSign]

theorem lorentzSign_succ (i : Fin 3) : lorentzSign .timeNegative i.succ = 1 := by
  simp [lorentzSign]

theorem raisedStress_zero_zero (F : Field) : raisedStress F 0 0 = energyDensity F := by
  funext y
  rw [raisedStress, lorentzSign_zero, stressForm_zero_zero, energyDensity]
  simp only [electricField, magneticField, Fin.sum_univ_three]
  ring

theorem raisedStress_succ_zero (F : Field) (i : Fin 3) :
    raisedStress F i.succ 0 = poyntingVector F i := by
  funext y
  rw [raisedStress, lorentzSign_zero, lorentzSign_succ, stressForm_symm]
  obtain ⟨h1, h2, h3⟩ := stressForm_zero_succ (F y)
  fin_cases i
  · change 1 * -1 * stressForm (F y) (Pi.single 0 1) (Pi.single 1 1) = _
    rw [h1]; simp [poyntingVector, electricField, magneticField]
  · change 1 * -1 * stressForm (F y) (Pi.single 0 1) (Pi.single 2 1) = _
    rw [h2]; simp [poyntingVector, electricField, magneticField]
  · change 1 * -1 * stressForm (F y) (Pi.single 0 1) (Pi.single 3 1) = _
    rw [h3]; simp [poyntingVector, electricField, magneticField]

theorem raisedStress_zero_succ (F : Field) (i : Fin 3) :
    raisedStress F 0 i.succ = poyntingVector F i := by
  rw [← raisedStress_succ_zero]
  funext y
  simp only [raisedStress, stressForm_symm (F y) (Pi.single 0 1)]
  ring

theorem raisedStress_succ_succ (F : Field) (i j : Fin 3) :
    raisedStress F i.succ j.succ = maxwellStress F i j := by
  funext y
  rw [raisedStress, lorentzSign_succ, lorentzSign_succ, one_mul, one_mul, stressForm_succ_succ,
    maxwellStress, energyDensity]
  simp only [electricField, magneticField, Fin.sum_univ_three]
  split_ifs <;> ring

/-- The divergence `Σ_μ ∂_μ T^{μ0} = −E · 𝐤` of the stress tensor. -/
theorem divergence_raisedStress_zero {F : Field} {x : Spacetime} (hF : DifferentiableAt ℝ F x)
    {k : Spacetime → Spacetime}
    (hfar : ∀ i, partialAt (magneticField F i) 0 x + curl (electricField F) x i = 0)
    (hamp : ∀ i, curl (magneticField F) x i - partialAt (electricField F i) 0 x = k x i.succ) :
    ∑ μ : Fin 4, partialAt (raisedStress F μ 0) μ x =
      -(electricField F 0 x * k x 1 + electricField F 1 x * k x 2 +
        electricField F 2 x * k x 3) := by
  rw [Fin.sum_univ_succ, raisedStress_zero_zero]
  simp only [raisedStress_succ_zero]
  have h := poynting_local hF hfar hamp
  rw [divergence3] at h
  exact h

/-- The divergence `Σ_μ ∂_μ T^{μ,i} = −(ρ Eᵢ + (𝐤 × B)ᵢ)` of the stress tensor. -/
theorem divergence_raisedStress_succ {F : Field} {x : Spacetime} (hF : DifferentiableAt ℝ F x)
    {k : Spacetime → Spacetime}
    (hgB : divergence3 (magneticField F) x = 0)
    (hfar : ∀ i, partialAt (magneticField F i) 0 x + curl (electricField F) x i = 0)
    (hgE : divergence3 (electricField F) x = k x 0)
    (hamp : ∀ i, curl (magneticField F) x i - partialAt (electricField F i) 0 x = k x i.succ)
    (i : Fin 3) :
    ∑ μ : Fin 4, partialAt (raisedStress F μ i.succ) μ x = -forceDensity F k x i := by
  rw [Fin.sum_univ_succ, raisedStress_zero_succ]
  have hsym : ∀ j, raisedStress F j.succ i.succ = maxwellStress F i j := fun j => by
    rw [raisedStress_succ_succ]
    funext y
    simp only [maxwellStress]
    split_ifs with h1 h2 h2
    · subst h1; rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · ring
  simp only [hsym]
  exact momentum_local hF hgB hfar hgE hamp i

end ProjectAinos.Electrodynamics
