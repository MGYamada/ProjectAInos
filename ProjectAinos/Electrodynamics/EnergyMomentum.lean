/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.ChargeBalance
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# The energy and the momentum of the field in an inertial frame

For a field `F` on flat space-time with the electric field `E` and the magnetic field `B` of the
frame of the co-ordinates (Landau–Lifshitz, *The Classical Theory of Fields*, §§31, 33):

* `energyDensity F = ½ (E² + B²)` and `poyntingVector F = E × B`;
* `poynting_local`: if `∂_t B + curl E = 0` and `curl B − ∂_t E = 𝐤`, then
  `∂_t u + div S = −E · 𝐤`: the field loses energy by the work `E · 𝐤` on the current;
* `maxwellStress F i j = −(Eᵢ Eⱼ + Bᵢ Bⱼ) + ½ δᵢⱼ (E² + B²)` and `momentum_local`: with
  `div E = ρ` and `div B = 0` in addition, `∂_t Sᵢ + Σⱼ ∂ⱼ σᵢⱼ = −(ρ Eᵢ + (𝐤 × B)ᵢ)`, the
  balance of the momentum with the Lorentz force density;
* `energy_balance`: on a box of the co-ordinates, the energy of the field in the spatial box
  changes by minus the flux of `S` through its faces and minus `∫∫ E · 𝐤`.

The derivatives are taken at a point where the field is differentiable; the balance on a box
needs a field of class `C²`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

/-! ### Rules for the derivative -/

theorem partialAt_mul {f g : Spacetime → ℝ} {x : Spacetime} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (μ : Fin 4) :
    partialAt (fun y => f y * g y) μ x = f x * partialAt g μ x + g x * partialAt f μ x := by
  rw [partialAt, fderiv_fun_mul hf hg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rfl

theorem partialAt_add {f g : Spacetime → ℝ} {x : Spacetime} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (μ : Fin 4) :
    partialAt (fun y => f y + g y) μ x = partialAt f μ x + partialAt g μ x := by
  rw [partialAt, fderiv_fun_add hf hg]
  rfl

theorem partialAt_sub {f g : Spacetime → ℝ} {x : Spacetime} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (μ : Fin 4) :
    partialAt (fun y => f y - g y) μ x = partialAt f μ x - partialAt g μ x := by
  rw [partialAt, fderiv_fun_sub hf hg]
  rfl

theorem partialAt_const_mul (c : ℝ) {f : Spacetime → ℝ} {x : Spacetime}
    (hf : DifferentiableAt ℝ f x) (μ : Fin 4) :
    partialAt (fun y => c * f y) μ x = c * partialAt f μ x := by
  rw [partialAt, fderiv_const_mul hf]
  rfl

/-- The components of a differentiable field are differentiable. -/
theorem differentiableAt_component {G : Field} {x : Spacetime} (hG : DifferentiableAt ℝ G x)
    (a b : Fin 4) : DifferentiableAt ℝ (fun y => component (G y) a b) x :=
  (ContinuousAlternatingMap.apply ℝ Spacetime ℝ
    ![Pi.single a 1, Pi.single b 1]).differentiableAt.comp x hG

theorem differentiableAt_electricField {G : Field} {x : Spacetime}
    (hG : DifferentiableAt ℝ G x) (i : Fin 3) : DifferentiableAt ℝ (electricField G i) x := by
  have h : electricField G i = fun y => component (G y) i.succ 0 :=
    funext fun y => electricVector_apply (G y) i
  rw [h]
  exact differentiableAt_component hG _ _

theorem differentiableAt_magneticField {G : Field} {x : Spacetime}
    (hG : DifferentiableAt ℝ G x) (i : Fin 3) : DifferentiableAt ℝ (magneticField G i) x := by
  fin_cases i
  · exact differentiableAt_component hG 2 3
  · exact differentiableAt_component hG 3 1
  · exact differentiableAt_component hG 1 2

/-! ### The energy -/

/-- The energy density `½ (E² + B²)`. -/
def energyDensity (F : Field) : Spacetime → ℝ := fun y =>
  (1 / 2 : ℝ) * (electricField F 0 y * electricField F 0 y +
    electricField F 1 y * electricField F 1 y + electricField F 2 y * electricField F 2 y +
    (magneticField F 0 y * magneticField F 0 y + magneticField F 1 y * magneticField F 1 y +
      magneticField F 2 y * magneticField F 2 y))

/-- The vector of Poynting `S = E × B`. -/
def poyntingVector (F : Field) : Fin 3 → Spacetime → ℝ :=
  ![fun y => electricField F 1 y * magneticField F 2 y - electricField F 2 y * magneticField F 1 y,
    fun y => electricField F 2 y * magneticField F 0 y - electricField F 0 y * magneticField F 2 y,
    fun y => electricField F 0 y * magneticField F 1 y - electricField F 1 y * magneticField F 0 y]

theorem fin_succ_zero : (Fin.succ (0 : Fin 3) : Fin 4) = 1 := rfl
theorem fin_succ_one : (Fin.succ (1 : Fin 3) : Fin 4) = 2 := rfl
theorem fin_succ_two : (Fin.succ (2 : Fin 3) : Fin 4) = 3 := rfl

/-- The theorem of Poynting: if `∂_t B + curl E = 0` and `curl B − ∂_t E = 𝐤`, then
`∂_t u + div S = −E · 𝐤`. -/
theorem poynting_local {F : Field} {x : Spacetime} (hF : DifferentiableAt ℝ F x)
    {k : Spacetime → Spacetime}
    (hfar : ∀ i, partialAt (magneticField F i) 0 x + curl (electricField F) x i = 0)
    (hamp : ∀ i, curl (magneticField F) x i - partialAt (electricField F i) 0 x = k x i.succ) :
    partialAt (energyDensity F) 0 x + divergence3 (poyntingVector F) x =
      -(electricField F 0 x * k x 1 + electricField F 1 x * k x 2 +
        electricField F 2 x * k x 3) := by
  have e0 := differentiableAt_electricField hF 0
  have e1 := differentiableAt_electricField hF 1
  have e2 := differentiableAt_electricField hF 2
  have b0 := differentiableAt_magneticField hF 0
  have b1 := differentiableAt_magneticField hF 1
  have b2 := differentiableAt_magneticField hF 2
  have f0 := hfar 0
  have f1 := hfar 1
  have f2 := hfar 2
  have a0 := hamp 0
  have a1 := hamp 1
  have a2 := hamp 2
  simp only [curl, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, fin_succ_zero, fin_succ_one, fin_succ_two]
    at f0 f1 f2 a0 a1 a2
  unfold energyDensity
  simp only [divergence3, poyntingVector, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, fin_succ_zero, fin_succ_one, fin_succ_two]
  generalize electricField F 0 = E₀ at e0 f0 f1 f2 a0 a1 a2 ⊢
  generalize electricField F 1 = E₁ at e1 f0 f1 f2 a0 a1 a2 ⊢
  generalize electricField F 2 = E₂ at e2 f0 f1 f2 a0 a1 a2 ⊢
  generalize magneticField F 0 = B₀ at b0 f0 f1 f2 a0 a1 a2 ⊢
  generalize magneticField F 1 = B₁ at b1 f0 f1 f2 a0 a1 a2 ⊢
  generalize magneticField F 2 = B₂ at b2 f0 f1 f2 a0 a1 a2 ⊢
  clear hfar hamp hF
  simp (disch := fun_prop) only [partialAt_const_mul, partialAt_add, partialAt_sub,
    partialAt_mul]
  linear_combination (-E₀ x) * a0 + (-E₁ x) * a1 + (-E₂ x) * a2 + B₀ x * f0 + B₁ x * f1 +
    B₂ x * f2

/-! ### The momentum -/

/-- The stress tensor of Maxwell `σᵢⱼ = −(Eᵢ Eⱼ + Bᵢ Bⱼ) + δᵢⱼ u`. -/
def maxwellStress (F : Field) (i j : Fin 3) : Spacetime → ℝ := fun y =>
  -(electricField F i y * electricField F j y + magneticField F i y * magneticField F j y) +
    if i = j then energyDensity F y else 0

/-- The density `ρ E + 𝐤 × B` of the Lorentz force on the current `k = (ρ, 𝐤)`. -/
def forceDensity (F : Field) (k : Spacetime → Spacetime) (x : Spacetime) : Fin 3 → ℝ :=
  ![k x 0 * electricField F 0 x + (k x 2 * magneticField F 2 x - k x 3 * magneticField F 1 x),
    k x 0 * electricField F 1 x + (k x 3 * magneticField F 0 x - k x 1 * magneticField F 2 x),
    k x 0 * electricField F 2 x + (k x 1 * magneticField F 1 x - k x 2 * magneticField F 0 x)]

/-- The balance of the momentum: with the four equations of Maxwell,
`∂_t Sᵢ + Σⱼ ∂ⱼ σᵢⱼ = −(ρ Eᵢ + (𝐤 × B)ᵢ)`. -/
theorem momentum_local {F : Field} {x : Spacetime} (hF : DifferentiableAt ℝ F x)
    {k : Spacetime → Spacetime}
    (hgB : divergence3 (magneticField F) x = 0)
    (hfar : ∀ i, partialAt (magneticField F i) 0 x + curl (electricField F) x i = 0)
    (hgE : divergence3 (electricField F) x = k x 0)
    (hamp : ∀ i, curl (magneticField F) x i - partialAt (electricField F i) 0 x = k x i.succ)
    (i : Fin 3) :
    partialAt (poyntingVector F i) 0 x + ∑ j : Fin 3, partialAt (maxwellStress F i j) j.succ x =
      -forceDensity F k x i := by
  have e0 := differentiableAt_electricField hF 0
  have e1 := differentiableAt_electricField hF 1
  have e2 := differentiableAt_electricField hF 2
  have b0 := differentiableAt_magneticField hF 0
  have b1 := differentiableAt_magneticField hF 1
  have b2 := differentiableAt_magneticField hF 2
  have f0 := hfar 0
  have f1 := hfar 1
  have f2 := hfar 2
  have a0 := hamp 0
  have a1 := hamp 1
  have a2 := hamp 2
  simp only [curl, divergence3, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, fin_succ_zero, fin_succ_one,
    fin_succ_two] at f0 f1 f2 a0 a1 a2 hgB hgE
  unfold maxwellStress energyDensity
  fin_cases i
  · simp only [poyntingVector, forceDensity, Fin.sum_univ_three, Matrix.cons_val_zero,
      fin_succ_zero, fin_succ_one, fin_succ_two, Fin.isValue, Fin.zero_eta, ↓reduceIte,
      add_zero, Fin.reduceEq]
    generalize electricField F 0 = E₀ at e0 f0 f1 f2 a0 a1 a2 hgB hgE ⊢
    generalize electricField F 1 = E₁ at e1 f0 f1 f2 a0 a1 a2 hgB hgE ⊢
    generalize electricField F 2 = E₂ at e2 f0 f1 f2 a0 a1 a2 hgB hgE ⊢
    generalize magneticField F 0 = B₀ at b0 f0 f1 f2 a0 a1 a2 hgB hgE ⊢
    generalize magneticField F 1 = B₁ at b1 f0 f1 f2 a0 a1 a2 hgB hgE ⊢
    generalize magneticField F 2 = B₂ at b2 f0 f1 f2 a0 a1 a2 hgB hgE ⊢
    clear hfar hamp hF
    simp (disch := fun_prop) only [partialAt_const_mul, partialAt_add, partialAt_sub,
      partialAt_mul, partialAt_neg]
    linear_combination (-B₂ x) * a1 + B₁ x * a2 + E₁ x * f2 - E₂ x * f1 - E₀ x * hgE - B₀ x * hgB
  · simp only [poyntingVector, forceDensity, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, fin_succ_zero, fin_succ_one, fin_succ_two, Fin.isValue, Fin.mk_one,
      ↓reduceIte, add_zero, Fin.reduceEq]
    generalize electricField F 0 = E₀ at e0 f0 f1 f2 a0 a1 a2 hgB hgE ⊢
    generalize electricField F 1 = E₁ at e1 f0 f1 f2 a0 a1 a2 hgB hgE ⊢
    generalize electricField F 2 = E₂ at e2 f0 f1 f2 a0 a1 a2 hgB hgE ⊢
    generalize magneticField F 0 = B₀ at b0 f0 f1 f2 a0 a1 a2 hgB hgE ⊢
    generalize magneticField F 1 = B₁ at b1 f0 f1 f2 a0 a1 a2 hgB hgE ⊢
    generalize magneticField F 2 = B₂ at b2 f0 f1 f2 a0 a1 a2 hgB hgE ⊢
    clear hfar hamp hF
    simp (disch := fun_prop) only [partialAt_const_mul, partialAt_add, partialAt_sub,
      partialAt_mul, partialAt_neg]
    linear_combination (-B₀ x) * a2 + B₂ x * a0 + E₂ x * f0 - E₀ x * f2 - E₁ x * hgE - B₁ x * hgB
  · simp only [poyntingVector, forceDensity, Fin.sum_univ_three, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, fin_succ_zero, fin_succ_one, fin_succ_two, Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte, add_zero, Fin.reduceEq]
    generalize electricField F 0 = E₀ at e0 f0 f1 f2 a0 a1 a2 hgB hgE ⊢
    generalize electricField F 1 = E₁ at e1 f0 f1 f2 a0 a1 a2 hgB hgE ⊢
    generalize electricField F 2 = E₂ at e2 f0 f1 f2 a0 a1 a2 hgB hgE ⊢
    generalize magneticField F 0 = B₀ at b0 f0 f1 f2 a0 a1 a2 hgB hgE ⊢
    generalize magneticField F 1 = B₁ at b1 f0 f1 f2 a0 a1 a2 hgB hgE ⊢
    generalize magneticField F 2 = B₂ at b2 f0 f1 f2 a0 a1 a2 hgB hgE ⊢
    clear hfar hamp hF
    simp (disch := fun_prop) only [partialAt_const_mul, partialAt_add, partialAt_sub,
      partialAt_mul, partialAt_neg]
    linear_combination (-B₁ x) * a0 + B₀ x * a1 + E₀ x * f1 - E₁ x * f0 - E₂ x * hgE - B₂ x * hgB

/-! ### Balances on a box -/

/-- The divergence theorem on a box `[a, b]` of the co-ordinates, with the faces of the time
separated: the charge of `P` at `b⁰` minus that at `a⁰` plus the flux through the six spatial
faces is the integral of `div P`. -/
theorem box_divergence {P : Spacetime → Spacetime} (hP : ContDiff ℝ 1 P) {a b : Spacetime}
    (hle : a ≤ b) :
    charge P a b (b 0) - charge P a b (a 0) + ∑ i : Fin 3, faceFlux P a b i.succ =
      ∫ y in Icc a b, divergence4 P y := by
  have hcont : Continuous fun x => ∑ μ : Fin 4, fderiv ℝ P x (Pi.single μ 1) μ :=
    continuous_finsetSum _ fun μ _ =>
      (continuous_apply μ).comp ((hP.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have h := integral_divergence_of_hasFDerivAt_off_countable a b hle P (fderiv ℝ P) ∅
    countable_empty hP.continuous.continuousOn
    (fun x _ => (hP.differentiable one_ne_zero x).hasFDerivAt)
    (hcont.continuousOn.integrableOn_compact isCompact_Icc)
  rw [Fin.sum_univ_succ] at h
  change (∫ x in Icc a b, divergence4 P x) = faceFlux P a b 0 + _ at h
  rw [h, faceFlux_zero]
  rfl

/-- The divergence in terms of the derivatives of the components. -/
theorem divergence4_eq {P : Spacetime → Spacetime} {x : Spacetime}
    (hP : DifferentiableAt ℝ P x) :
    divergence4 P x = ∑ μ : Fin 4, partialAt (fun y => P y μ) μ x := by
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hd : HasFDerivAt (fun y => P y μ)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) μ).comp (fderiv ℝ P x)) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) μ).hasFDerivAt.comp x
      hP.hasFDerivAt
  rw [partialAt, hd.fderiv]
  rfl

theorem contDiff_component {n : ℕ∞ω} {G : Field} (hG : ContDiff ℝ n G) (a b : Fin 4) :
    ContDiff ℝ n (fun y => component (G y) a b) :=
  (ContinuousAlternatingMap.apply ℝ Spacetime ℝ ![Pi.single a 1, Pi.single b 1]).contDiff.comp hG

theorem contDiff_electricField {n : ℕ∞ω} {G : Field} (hG : ContDiff ℝ n G) (i : Fin 3) :
    ContDiff ℝ n (electricField G i) := by
  have h : electricField G i = fun y => component (G y) i.succ 0 :=
    funext fun y => electricVector_apply (G y) i
  rw [h]
  exact contDiff_component hG _ _

theorem contDiff_magneticField {n : ℕ∞ω} {G : Field} (hG : ContDiff ℝ n G) (i : Fin 3) :
    ContDiff ℝ n (magneticField G i) := by
  fin_cases i
  · exact contDiff_component hG 2 3
  · exact contDiff_component hG 3 1
  · exact contDiff_component hG 1 2

/-- The current `(u, S)` of the energy. -/
def energyCurrent (F : Field) : Spacetime → Spacetime := fun y =>
  ![energyDensity F y, poyntingVector F 0 y, poyntingVector F 1 y, poyntingVector F 2 y]

theorem contDiff_energyCurrent {n : ℕ∞ω} {F : Field} (hF : ContDiff ℝ n F) :
    ContDiff ℝ n (energyCurrent F) := by
  have e := contDiff_electricField hF
  have b := contDiff_magneticField hF
  refine contDiff_pi.mpr fun μ => ?_
  fin_cases μ
  · exact contDiff_const.mul (((((e 0).mul (e 0)).add ((e 1).mul (e 1))).add ((e 2).mul (e 2))).add
      ((((b 0).mul (b 0)).add ((b 1).mul (b 1))).add ((b 2).mul (b 2))))
  · exact ((e 1).mul (b 2)).sub ((e 2).mul (b 1))
  · exact ((e 2).mul (b 0)).sub ((e 0).mul (b 2))
  · exact ((e 0).mul (b 1)).sub ((e 1).mul (b 0))

/-- The balance of the energy on a box: the energy of the field in the spatial box changes by
minus the flux of the vector of Poynting through its faces and minus the work `∫∫ E · 𝐤`. -/
theorem energy_balance {F : Field} (hF : ContDiff ℝ 2 F) {k : Spacetime → Spacetime}
    {a b : Spacetime} (hle : a ≤ b)
    (hfar : ∀ y ∈ Icc a b, ∀ i,
      partialAt (magneticField F i) 0 y + curl (electricField F) y i = 0)
    (hamp : ∀ y ∈ Icc a b, ∀ i,
      curl (magneticField F) y i - partialAt (electricField F i) 0 y = k y i.succ) :
    charge (energyCurrent F) a b (b 0) - charge (energyCurrent F) a b (a 0) =
      -∑ i : Fin 3, faceFlux (energyCurrent F) a b i.succ -
        ∫ y in Icc a b, (electricField F 0 y * k y 1 + electricField F 1 y * k y 2 +
          electricField F 2 y * k y 3) := by
  have hP : ContDiff ℝ 1 (energyCurrent F) := contDiff_energyCurrent (hF.of_le (by norm_num))
  have hdiv : ∀ y ∈ Icc a b, divergence4 (energyCurrent F) y =
      -(electricField F 0 y * k y 1 + electricField F 1 y * k y 2 +
        electricField F 2 y * k y 3) := by
    intro y hy
    rw [divergence4_eq (hP.differentiable one_ne_zero y), Fin.sum_univ_four]
    have hp := poynting_local (hF.differentiable (by norm_num) y) (hfar y hy) (hamp y hy)
    rw [divergence3, Fin.sum_univ_three] at hp
    have h0 : (fun z => energyCurrent F z 0) = energyDensity F := by
      funext z; simp [energyCurrent]
    have h1 : (fun z => energyCurrent F z 1) = poyntingVector F 0 := by
      funext z; simp [energyCurrent]
    have h2 : (fun z => energyCurrent F z 2) = poyntingVector F 1 := by
      funext z; simp [energyCurrent]
    have h3 : (fun z => energyCurrent F z 3) = poyntingVector F 2 := by
      funext z; simp [energyCurrent]
    rw [h0, h1, h2, h3]
    rw [fin_succ_zero, fin_succ_one, fin_succ_two] at hp
    linarith
  have h := box_divergence hP hle
  rw [setIntegral_congr_fun measurableSet_Icc hdiv, integral_neg] at h
  linarith

theorem contDiff_energyDensity {n : ℕ∞ω} {F : Field} (hF : ContDiff ℝ n F) :
    ContDiff ℝ n (energyDensity F) :=
  (contDiff_pi.mp (contDiff_energyCurrent hF)) 0

theorem contDiff_poyntingVector {n : ℕ∞ω} {F : Field} (hF : ContDiff ℝ n F) (i : Fin 3) :
    ContDiff ℝ n (poyntingVector F i) := by
  fin_cases i
  · exact (contDiff_pi.mp (contDiff_energyCurrent hF)) 1
  · exact (contDiff_pi.mp (contDiff_energyCurrent hF)) 2
  · exact (contDiff_pi.mp (contDiff_energyCurrent hF)) 3

theorem contDiff_maxwellStress {n : ℕ∞ω} {F : Field} (hF : ContDiff ℝ n F) (i j : Fin 3) :
    ContDiff ℝ n (maxwellStress F i j) := by
  have e := contDiff_electricField hF
  have b := contDiff_magneticField hF
  by_cases h : i = j
  · have hfun : maxwellStress F i j = fun y => -(electricField F i y * electricField F j y +
        magneticField F i y * magneticField F j y) + energyDensity F y := by
      funext y; simp [maxwellStress, h]
    rw [hfun]
    exact (((e i).mul (e j)).add ((b i).mul (b j))).neg.add (contDiff_energyDensity hF)
  · have hfun : maxwellStress F i j = fun y => -(electricField F i y * electricField F j y +
        magneticField F i y * magneticField F j y) := by
      funext y; simp [maxwellStress, h]
    rw [hfun]
    exact (((e i).mul (e j)).add ((b i).mul (b j))).neg

/-- The current `(Sᵢ, σᵢ₀, σᵢ₁, σᵢ₂)` of the component `i` of the momentum. -/
def momentumCurrent (F : Field) (i : Fin 3) : Spacetime → Spacetime := fun y =>
  ![poyntingVector F i y, maxwellStress F i 0 y, maxwellStress F i 1 y, maxwellStress F i 2 y]

theorem contDiff_momentumCurrent {n : ℕ∞ω} {F : Field} (hF : ContDiff ℝ n F) (i : Fin 3) :
    ContDiff ℝ n (momentumCurrent F i) := by
  refine contDiff_pi.mpr fun μ => ?_
  fin_cases μ
  · exact contDiff_poyntingVector hF i
  · exact contDiff_maxwellStress hF i 0
  · exact contDiff_maxwellStress hF i 1
  · exact contDiff_maxwellStress hF i 2

/-- The balance of the momentum on a box: the component `i` of the momentum `∫ Sᵢ d³x` of the
field in the spatial box changes by minus the flux of the stress `σᵢⱼ` through its faces and
minus the impulse `∫∫ (ρ Eᵢ + (𝐤 × B)ᵢ)` of the Lorentz force on the current. -/
theorem momentum_balance {F : Field} (hF : ContDiff ℝ 2 F) {k : Spacetime → Spacetime}
    {a b : Spacetime} (hle : a ≤ b)
    (hgB : ∀ y ∈ Icc a b, divergence3 (magneticField F) y = 0)
    (hfar : ∀ y ∈ Icc a b, ∀ i,
      partialAt (magneticField F i) 0 y + curl (electricField F) y i = 0)
    (hgE : ∀ y ∈ Icc a b, divergence3 (electricField F) y = k y 0)
    (hamp : ∀ y ∈ Icc a b, ∀ i,
      curl (magneticField F) y i - partialAt (electricField F i) 0 y = k y i.succ)
    (i : Fin 3) :
    charge (momentumCurrent F i) a b (b 0) - charge (momentumCurrent F i) a b (a 0) =
      -∑ j : Fin 3, faceFlux (momentumCurrent F i) a b j.succ -
        ∫ y in Icc a b, forceDensity F k y i := by
  have hP : ContDiff ℝ 1 (momentumCurrent F i) :=
    contDiff_momentumCurrent (hF.of_le (by norm_num)) i
  have hdiv : ∀ y ∈ Icc a b, divergence4 (momentumCurrent F i) y = -forceDensity F k y i := by
    intro y hy
    rw [divergence4_eq (hP.differentiable one_ne_zero y), Fin.sum_univ_four]
    have hp := momentum_local (hF.differentiable (by norm_num) y) (hgB y hy) (hfar y hy)
      (hgE y hy) (hamp y hy) i
    rw [Fin.sum_univ_three, fin_succ_zero, fin_succ_one, fin_succ_two] at hp
    have h0 : (fun z => momentumCurrent F i z 0) = poyntingVector F i := by
      funext z; simp [momentumCurrent]
    have h1 : (fun z => momentumCurrent F i z 1) = maxwellStress F i 0 := by
      funext z; simp [momentumCurrent]
    have h2 : (fun z => momentumCurrent F i z 2) = maxwellStress F i 1 := by
      funext z; simp [momentumCurrent]
    have h3 : (fun z => momentumCurrent F i z 3) = maxwellStress F i 2 := by
      funext z; simp [momentumCurrent]
    rw [h0, h1, h2, h3]
    linarith
  have h := box_divergence hP hle
  rw [setIntegral_congr_fun measurableSet_Icc hdiv, integral_neg] at h
  linarith

end ProjectAinos.Electrodynamics
