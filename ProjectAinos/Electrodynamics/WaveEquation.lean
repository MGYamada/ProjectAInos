/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.EnergyMomentum
public import ProjectAinos.Electrodynamics.Components
public import ProjectAinos.Electrodynamics.SourceCovariance
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# The wave equation of the potentials

For a potential `A = A_ν dx^ν = −φ dt + 𝐚 · d𝐱` on flat space-time of the signature `(−+++)`,
`box f = −∂₀∂₀f + Σᵢ ∂ᵢ∂ᵢf` is the wave operator and `lorenzDivergence A = −∂₀A₀ + Σᵢ ∂ᵢAᵢ`,
which is `∂ₜφ + div 𝐚`, the divergence `∂^μ A_μ` (Landau–Lifshitz, *The Classical Theory of
Fields*, §46).

* `divergence3_electricField_fieldTensor`: `div E = box A₀ − ∂ₜ(∂^μ A_μ)`, that is
  `−box φ − ∂ₜ(∂^μ A_μ)`, and `curl_magneticField_sub_fieldTensor`:
  `curl B − ∂ₜE = −box aᵢ + ∂ᵢ(∂^μ A_μ)`, for a potential that is `C²` near the point.
* `maxwell_iff_box_of_lorenz`: on an open set where `∂^μ A_μ = 0`, the four equations of Maxwell
  with the current `k = (k⁰, 𝐤)` hold if and only if `box A₀ = k⁰` (that is, `box φ = −k⁰`) and
  `box aᵢ = −kⁱ`: in the gauge of Lorenz the potential solves the wave equation.
  `excitation_iff_box_of_lorenz` is the same statement for the equation `d(−⋆dA) = −ι_k vol` of
  the forms.
* `lorenzDivergence_gaugeShift`: the gauge function `χ` changes `∂^μ A_μ` by `box χ`, and
  `lorenz_gaugeShift`: a gauge function with `box χ = −∂^μ A_μ` brings the potential into the
  gauge of Lorenz without changing its field. The existence of such a `χ` is not proved here.
* `box_lorenzDivergence`: if `box A_ν = −k_ν` and `∂_μ k^μ = 0`, then `box (∂^μ A_μ) = 0`, for a
  potential of class `C³`.
* `eq_zero_of_box_eq_zero`: a `C²` solution of `box u = 0` on `[0, T] × ℝ³` that vanishes outside
  a fixed spatial box and has zero initial data vanishes on `[0, T] × ℝ³`; the proof is the
  conservation of the energy `½ ∫ (∂ₜu)² + |∇u|²` of `waveEnergyCurrent`
  (`divergence4_waveEnergyCurrent`) by `box_divergence`. With it
  `lorenzDivergence_eq_zero_of_initial`: the gauge condition propagates from the initial data.
* `constraint_propagation`: the equations of Faraday and Ampère and `∂_μ k^μ = 0` give
  `∂ₜ(div B) = 0` and `∂ₜ(div E − k⁰) = 0`.

Finite propagation speed is not proved.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

/-! ### The wave operator and the divergence of the potential -/

/-- The wave operator `box f = −∂₀∂₀f + Σᵢ ∂ᵢ∂ᵢf` of the signature `(−+++)`. -/
def box (f : Spacetime → ℝ) (x : Spacetime) : ℝ :=
  -partialAt (partialAt f 0) 0 x + ∑ i : Fin 3, partialAt (partialAt f i.succ) i.succ x

/-- The divergence `∂^μ A_μ = −∂₀A₀ + Σᵢ ∂ᵢAᵢ` of a potential; for `A = −φ dt + 𝐚 · d𝐱` it is
`∂ₜφ + div 𝐚`. -/
def lorenzDivergence (A : Potential) (x : Spacetime) : ℝ :=
  -partialAt (potentialComponent A 0) 0 x +
    ∑ i : Fin 3, partialAt (potentialComponent A i.succ) i.succ x

/-! ### Rules for the derivatives -/

/-- Functions that agree near a point have the same derivatives there. -/
theorem partialAt_congr_of_eventuallyEq {f g : Spacetime → ℝ} {x : Spacetime}
    (h : f =ᶠ[𝓝 x] g) (μ : Fin 4) : partialAt f μ x = partialAt g μ x := by
  rw [partialAt, partialAt, h.fderiv_eq]

/-- The derivative of a constant function is zero. -/
theorem partialAt_const (c : ℝ) (μ : Fin 4) (x : Spacetime) :
    partialAt (fun _ => c) μ x = 0 := by
  rw [partialAt, fderiv_const_apply]
  rfl

/-- The derivative of a function that is `Cⁿ` near a point is `Cᵐ` near it, for `m + 1 ≤ n`. -/
theorem contDiffAt_partialAt {m n : ℕ∞ω} {f : Spacetime → ℝ} {x : Spacetime}
    (hf : ContDiffAt ℝ n f x) (hmn : m + 1 ≤ n) (μ : Fin 4) :
    ContDiffAt ℝ m (partialAt f μ) x :=
  (hf.fderiv_right hmn).clm_apply contDiffAt_const

/-- The second derivatives of a function that is `C²` near a point commute at the point. -/
theorem partialAt_partialAt_comm {f : Spacetime → ℝ} {x : Spacetime} (hf : ContDiffAt ℝ 2 f x)
    (μ ν : Fin 4) : partialAt (partialAt f ν) μ x = partialAt (partialAt f μ) ν x := by
  have hsymm : IsSymmSndFDerivAt ℝ f x := hf.isSymmSndFDerivAt (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have key (a b : Spacetime) :
      fderiv ℝ (fun y => fderiv ℝ f y b) x a = fderiv ℝ (fderiv ℝ f) x a b := by
    rw [fderiv_clm_apply hd (differentiableAt_const b)]
    simp
  change fderiv ℝ (fun y => fderiv ℝ f y (Pi.single ν 1)) x (Pi.single μ 1) =
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single μ 1)) x (Pi.single ν 1)
  rw [key, key]
  exact hsymm _ _

/-- The derivative of a finite sum. -/
theorem partialAt_sum {ι : Type*} (s : Finset ι) {f : ι → Spacetime → ℝ} {x : Spacetime}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) (μ : Fin 4) :
    partialAt (fun y => ∑ i ∈ s, f i y) μ x = ∑ i ∈ s, partialAt (f i) μ x := by
  rw [partialAt, fderiv_fun_sum hf, _root_.sum_apply]
  rfl

/-- The components of a potential that is `Cⁿ` near a point are `Cⁿ` near it. -/
theorem contDiffAt_potentialComponent {n : ℕ∞ω} {A : Potential} {x : Spacetime}
    (hA : ContDiffAt ℝ n A x) (ν : Fin 4) : ContDiffAt ℝ n (potentialComponent A ν) x := by
  let ev : OneForm →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ (Pi.single ν 1)).comp oneCovector.toContinuousLinearMap
  exact ev.contDiff.contDiffAt.comp x hA

/-- The components of a potential that is differentiable at a point are differentiable there. -/
theorem differentiableAt_potentialComponent {A : Potential} {x : Spacetime}
    (hA : DifferentiableAt ℝ A x) (ν : Fin 4) :
    DifferentiableAt ℝ (potentialComponent A ν) x := by
  let ev : OneForm →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ (Pi.single ν 1)).comp oneCovector.toContinuousLinearMap
  exact ev.differentiableAt.comp x hA

/-- Near a point where the potential is `C¹`, `F_{μν} = ∂_μ A_ν − ∂_ν A_μ`. -/
theorem component_fieldTensor_eventuallyEq {A : Potential} {x : Spacetime}
    (hA : ContDiffAt ℝ 1 A x) (μ ν : Fin 4) :
    (fun y => component (fieldTensor A y) μ ν) =ᶠ[𝓝 x]
      fun y => partialAt (potentialComponent A ν) μ y - partialAt (potentialComponent A μ) ν y :=
  (hA.eventually (by simp)).mono fun _ hy =>
    fieldTensor_component (hy.differentiableAt one_ne_zero) μ ν

/-- Near a point where the potential is `C¹`, `Eᵢ = ∂ᵢA₀ − ∂₀Aᵢ`. -/
theorem electricField_fieldTensor_eventuallyEq {A : Potential} {x : Spacetime}
    (hA : ContDiffAt ℝ 1 A x) (i : Fin 3) :
    electricField (fieldTensor A) i =ᶠ[𝓝 x] fun y =>
      partialAt (potentialComponent A 0) i.succ y - partialAt (potentialComponent A i.succ) 0 y :=
  (component_fieldTensor_eventuallyEq hA i.succ 0).mono fun y hy =>
    (electricVector_apply (fieldTensor A y) i).trans hy

/-- Near a point where the potential is `C¹`, `B = curl 𝐚`. -/
theorem magneticField_fieldTensor_eventuallyEq {A : Potential} {x : Spacetime}
    (hA : ContDiffAt ℝ 1 A x) :
    (magneticField (fieldTensor A) 0 =ᶠ[𝓝 x] fun y =>
      partialAt (potentialComponent A 3) 2 y - partialAt (potentialComponent A 2) 3 y) ∧
    (magneticField (fieldTensor A) 1 =ᶠ[𝓝 x] fun y =>
      partialAt (potentialComponent A 1) 3 y - partialAt (potentialComponent A 3) 1 y) ∧
    (magneticField (fieldTensor A) 2 =ᶠ[𝓝 x] fun y =>
      partialAt (potentialComponent A 2) 1 y - partialAt (potentialComponent A 1) 2 y) :=
  ⟨component_fieldTensor_eventuallyEq hA 2 3, component_fieldTensor_eventuallyEq hA 3 1,
    component_fieldTensor_eventuallyEq hA 1 2⟩

/-- The derivative of `∂^μ A_μ`, for a potential that is `C²` near the point. -/
theorem partialAt_lorenzDivergence {A : Potential} {x : Spacetime} (hA : ContDiffAt ℝ 2 A x)
    (μ : Fin 4) :
    partialAt (lorenzDivergence A) μ x =
      -partialAt (partialAt (potentialComponent A 0) 0) μ x +
        ∑ i : Fin 3, partialAt (partialAt (potentialComponent A i.succ) i.succ) μ x := by
  have hd : ∀ ν ρ, DifferentiableAt ℝ (partialAt (potentialComponent A ν) ρ) x := fun ν ρ =>
    (contDiffAt_partialAt (m := 1) (contDiffAt_potentialComponent hA ν) (by norm_num)
      ρ).differentiableAt one_ne_zero
  have hL : lorenzDivergence A = fun y => -partialAt (potentialComponent A 0) 0 y +
      ∑ i : Fin 3, partialAt (potentialComponent A i.succ) i.succ y := rfl
  rw [hL, partialAt_add (hd 0 0).fun_neg (DifferentiableAt.fun_sum (u := Finset.univ)
    (A := fun i : Fin 3 => partialAt (potentialComponent A i.succ) i.succ) fun i _ => hd _ _),
    partialAt_neg, partialAt_sum _ fun i _ => hd _ _]

/-! ### The equations of Maxwell for the potential -/

/-- `div E = box A₀ − ∂ₜ(∂^μ A_μ)`, that is `−box φ − ∂ₜ(∂^μ A_μ)` for `A₀ = −φ`, for a potential
that is `C²` near the point. -/
theorem divergence3_electricField_fieldTensor {A : Potential} {x : Spacetime}
    (hA : ContDiffAt ℝ 2 A x) :
    divergence3 (electricField (fieldTensor A)) x =
      box (potentialComponent A 0) x - partialAt (lorenzDivergence A) 0 x := by
  have ha := contDiffAt_potentialComponent hA
  have hd : ∀ ν ρ, DifferentiableAt ℝ (partialAt (potentialComponent A ν) ρ) x := fun ν ρ =>
    (contDiffAt_partialAt (m := 1) (ha ν) (by norm_num) ρ).differentiableAt one_ne_zero
  have hE : ∀ i : Fin 3, partialAt (electricField (fieldTensor A) i) i.succ x =
      partialAt (partialAt (potentialComponent A 0) i.succ) i.succ x -
        partialAt (partialAt (potentialComponent A i.succ) 0) i.succ x := fun i => by
    rw [partialAt_congr_of_eventuallyEq
      (electricField_fieldTensor_eventuallyEq (hA.of_le (by norm_num)) i),
      partialAt_sub (hd _ _) (hd _ _)]
  have hc : ∀ i : Fin 3, partialAt (partialAt (potentialComponent A i.succ) 0) i.succ x =
      partialAt (partialAt (potentialComponent A i.succ) i.succ) 0 x := fun i =>
    partialAt_partialAt_comm (ha _) _ _
  rw [divergence3, partialAt_lorenzDivergence hA, box]
  simp only [hE, hc, Finset.sum_sub_distrib]
  ring

/-- `curl B − ∂ₜE = −box aᵢ + ∂ᵢ(∂^μ A_μ)`, for a potential that is `C²` near the point. -/
theorem curl_magneticField_sub_fieldTensor {A : Potential} {x : Spacetime}
    (hA : ContDiffAt ℝ 2 A x) (i : Fin 3) :
    curl (magneticField (fieldTensor A)) x i - partialAt (electricField (fieldTensor A) i) 0 x =
      -box (potentialComponent A i.succ) x + partialAt (lorenzDivergence A) i.succ x := by
  have ha := contDiffAt_potentialComponent hA
  have hd : ∀ ν ρ, DifferentiableAt ℝ (partialAt (potentialComponent A ν) ρ) x := fun ν ρ =>
    (contDiffAt_partialAt (m := 1) (ha ν) (by norm_num) ρ).differentiableAt one_ne_zero
  have hA1 : ContDiffAt ℝ 1 A x := hA.of_le (by norm_num)
  obtain ⟨hB0, hB1, hB2⟩ := magneticField_fieldTensor_eventuallyEq hA1
  have hE : ∀ (j : Fin 3) (μ : Fin 4), partialAt (electricField (fieldTensor A) j) μ x =
      partialAt (partialAt (potentialComponent A 0) j.succ) μ x -
        partialAt (partialAt (potentialComponent A j.succ) 0) μ x := fun j μ => by
    rw [partialAt_congr_of_eventuallyEq (electricField_fieldTensor_eventuallyEq hA1 j),
      partialAt_sub (hd _ _) (hd _ _)]
  have hc : ∀ (ν μ ρ : Fin 4), partialAt (partialAt (potentialComponent A ν) ρ) μ x =
      partialAt (partialAt (potentialComponent A ν) μ) ρ x := fun ν μ ρ =>
    partialAt_partialAt_comm (ha ν) μ ρ
  rw [partialAt_lorenzDivergence hA, box, hE]
  simp only [Fin.sum_univ_three, fin_succ_zero, fin_succ_one, fin_succ_two]
  fin_cases i
  · simp only [curl, Matrix.cons_val_zero, Fin.zero_eta, fin_succ_zero]
    rw [partialAt_congr_of_eventuallyEq hB2, partialAt_congr_of_eventuallyEq hB1,
      partialAt_sub (hd _ _) (hd _ _), partialAt_sub (hd _ _) (hd _ _)]
    linear_combination -hc 2 1 2 - hc 3 1 3 + hc 0 1 0
  · simp only [curl, Matrix.cons_val_one, Matrix.cons_val_zero, Fin.mk_one, fin_succ_one]
    rw [partialAt_congr_of_eventuallyEq hB0, partialAt_congr_of_eventuallyEq hB2,
      partialAt_sub (hd _ _) (hd _ _), partialAt_sub (hd _ _) (hd _ _)]
    linear_combination -hc 3 2 3 - hc 1 2 1 + hc 0 2 0
  · simp only [curl, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Fin.reduceFinMk,
      fin_succ_two]
    rw [partialAt_congr_of_eventuallyEq hB1, partialAt_congr_of_eventuallyEq hB0,
      partialAt_sub (hd _ _) (hd _ _), partialAt_sub (hd _ _) (hd _ _)]
    linear_combination -hc 1 3 1 - hc 2 3 2 + hc 0 3 0

/-- In the gauge of Lorenz the equations of Maxwell are wave equations: on an open set where
`∂^μ A_μ = 0`, the field of a `C²` potential satisfies the four equations of Maxwell with the
current `k = (k⁰, 𝐤)` if and only if `box A₀ = k⁰` (that is, `box φ = −k⁰` for `A₀ = −φ`) and
`box aᵢ = −kⁱ`, that is `box A_ν = −k_ν`. -/
theorem maxwell_iff_box_of_lorenz {U : Set Spacetime} (hU : IsOpen U) {A : Potential}
    (hA : ContDiffOn ℝ 2 A U) (hL : ∀ y ∈ U, lorenzDivergence A y = 0)
    (k : Spacetime → Spacetime) :
    (∀ y ∈ U, (divergence3 (magneticField (fieldTensor A)) y = 0 ∧
        ∀ i, partialAt (magneticField (fieldTensor A) i) 0 y +
          curl (electricField (fieldTensor A)) y i = 0) ∧
      (divergence3 (electricField (fieldTensor A)) y = k y 0 ∧
        ∀ i, curl (magneticField (fieldTensor A)) y i -
          partialAt (electricField (fieldTensor A) i) 0 y = k y i.succ)) ↔
    ∀ y ∈ U, box (potentialComponent A 0) y = k y 0 ∧
      ∀ i : Fin 3, box (potentialComponent A i.succ) y = -k y i.succ := by
  have hdL : ∀ y ∈ U, ∀ μ, partialAt (lorenzDivergence A) μ y = 0 := fun y hy μ => by
    have hev : lorenzDivergence A =ᶠ[𝓝 y] fun _ => 0 :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hy) hL
    rw [partialAt_congr_of_eventuallyEq hev, partialAt_const]
  have hdiv : ∀ y ∈ U, divergence3 (electricField (fieldTensor A)) y =
      box (potentialComponent A 0) y := fun y hy => by
    rw [divergence3_electricField_fieldTensor ((hA y hy).contDiffAt (hU.mem_nhds hy)),
      hdL y hy, sub_zero]
  have hamp : ∀ y ∈ U, ∀ i, curl (magneticField (fieldTensor A)) y i -
      partialAt (electricField (fieldTensor A) i) 0 y = -box (potentialComponent A i.succ) y :=
    fun y hy i => by
      rw [curl_magneticField_sub_fieldTensor ((hA y hy).contDiffAt (hU.mem_nhds hy)),
        hdL y hy, add_zero]
  constructor
  · intro h y hy
    obtain ⟨-, hgE, hA'⟩ := h y hy
    refine ⟨(hdiv y hy).symm.trans hgE, fun i => ?_⟩
    have h' := hA' i
    rw [hamp y hy i] at h'
    linarith
  · intro h y hy
    refine ⟨homogeneous_fieldTensor hU hA hy, (hdiv y hy).trans (h y hy).1, fun i => ?_⟩
    rw [hamp y hy i, (h y hy).2 i, neg_neg]

/-- The components of a sum of potentials are the sums of the components. -/
theorem potentialComponent_add (A B : Potential) (ν : Fin 4) :
    potentialComponent (A + B) ν =
      fun y => potentialComponent A ν y + potentialComponent B ν y := by
  funext y
  simp only [potentialComponent, Pi.add_apply, map_add, _root_.add_apply]

/-- The divergence `∂^μ A_μ` is additive on potentials that are differentiable at the point. -/
theorem lorenzDivergence_add {A B : Potential} {x : Spacetime} (hA : DifferentiableAt ℝ A x)
    (hB : DifferentiableAt ℝ B x) :
    lorenzDivergence (A + B) x = lorenzDivergence A x + lorenzDivergence B x := by
  have hs : ∀ ν μ, partialAt (fun y => potentialComponent A ν y + potentialComponent B ν y) μ x =
      partialAt (potentialComponent A ν) μ x + partialAt (potentialComponent B ν) μ x :=
    fun ν μ => partialAt_add (differentiableAt_potentialComponent hA ν)
      (differentiableAt_potentialComponent hB ν) μ
  simp only [lorenzDivergence, potentialComponent_add, hs, Finset.sum_add_distrib]
  ring

/-- In the gauge of Lorenz the equation of the forms is a wave equation: on an open set where
`∂^μ A_μ = 0`, the field of a `C²` potential satisfies `d(−⋆dA) = −ι_k vol` if and only if
`box A₀ = k⁰` and `box aᵢ = −kⁱ`; the equation `d(dA) = 0` holds in any case. -/
theorem excitation_iff_box_of_lorenz {U : Set Spacetime} (hU : IsOpen U) {A : Potential}
    (hA : ContDiffOn ℝ 2 A U) (hL : ∀ y ∈ U, lorenzDivergence A y = 0)
    (k : Spacetime → Spacetime) :
    (∀ y ∈ U, exteriorDerivative (fun z => -star (fieldTensor A z)) y =
      SourcedAction.matterCurrentForm k y) ↔
    ∀ y ∈ U, box (potentialComponent A 0) y = k y 0 ∧
      ∀ i : Fin 3, box (potentialComponent A i.succ) y = -k y i.succ := by
  rw [← maxwell_iff_box_of_lorenz hU hA hL k]
  constructor
  · intro h y hy
    exact ⟨homogeneous_fieldTensor hU hA hy,
      inhomogeneous_of_excitation (differentiableAt_fieldTensor hU hA hy) (h y hy)⟩
  · intro h y hy
    obtain ⟨-, hgE, hamp⟩ := h y hy
    exact excitation_of_inhomogeneous (differentiableAt_fieldTensor hU hA hy) hgE hamp

/-! ### The change of the gauge -/

/-- The components of the potential after the change of the gauge by `χ` are `A_ν + ∂_ν χ`. -/
theorem potentialComponent_gaugeShift (A : Potential) (χ : Spacetime → ℝ) (ν : Fin 4) :
    potentialComponent (gaugeShift A χ) ν =
      fun y => potentialComponent A ν y + partialAt χ ν y := by
  funext y
  simp only [potentialComponent, gaugeShift, Pi.add_apply, map_add,
    _root_.add_apply, scalar_derivative]
  rfl

/-- The change of the gauge by `χ` changes the divergence `∂^μ A_μ` by `box χ`. -/
theorem lorenzDivergence_gaugeShift {A : Potential} {χ : Spacetime → ℝ} {x : Spacetime}
    (hA : DifferentiableAt ℝ A x) (hχ : ContDiffAt ℝ 2 χ x) :
    lorenzDivergence (gaugeShift A χ) x = lorenzDivergence A x + box χ x := by
  have ha := differentiableAt_potentialComponent hA
  have hc : ∀ ν, DifferentiableAt ℝ (partialAt χ ν) x := fun ν =>
    (contDiffAt_partialAt (m := 1) hχ (by norm_num) ν).differentiableAt one_ne_zero
  have hs : ∀ ν μ, partialAt (fun y => potentialComponent A ν y + partialAt χ ν y) μ x =
      partialAt (potentialComponent A ν) μ x + partialAt (partialAt χ ν) μ x := fun ν μ =>
    partialAt_add (ha ν) (hc ν) μ
  simp only [lorenzDivergence, box, potentialComponent_gaugeShift, hs, Finset.sum_add_distrib]
  ring

/-- A gauge function with `box χ = −∂^μ A_μ` on an open set brings the potential into the gauge of
Lorenz there, and does not change the field. -/
theorem lorenz_gaugeShift {U : Set Spacetime} (hU : IsOpen U) {A : Potential}
    {χ : Spacetime → ℝ} (hA : ContDiffOn ℝ 1 A U) (hχ : ContDiffOn ℝ 2 χ U)
    (hbox : ∀ y ∈ U, box χ y = -lorenzDivergence A y) :
    (∀ y ∈ U, lorenzDivergence (gaugeShift A χ) y = 0) ∧
      Set.EqOn (fieldTensor (gaugeShift A χ)) (fieldTensor A) U :=
  ⟨fun y hy => by
    rw [lorenzDivergence_gaugeShift
      (((hA y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt one_ne_zero)
      ((hχ y hy).contDiffAt (hU.mem_nhds hy)), hbox y hy, add_neg_cancel],
    fieldTensor_gauge_on A χ hU hA hχ⟩

/-! ### The propagation of the gauge condition -/

/-- The wave operator commutes with the sign. -/
theorem box_neg (f : Spacetime → ℝ) (x : Spacetime) : box (fun y => -f y) x = -box f x := by
  have h : ∀ μ, partialAt (fun y => -f y) μ = fun y => -partialAt f μ y := fun μ =>
    funext fun y => partialAt_neg f μ y
  simp only [box, h, partialAt_neg, Finset.sum_neg_distrib]
  ring

/-- The wave operator is additive on functions that are `C²` near the point. -/
theorem box_add {f g : Spacetime → ℝ} {x : Spacetime} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) : box (fun y => f y + g y) x = box f x + box g x := by
  have hev : ∀ μ, partialAt (fun y => f y + g y) μ =ᶠ[𝓝 x]
      fun y => partialAt f μ y + partialAt g μ y := fun μ =>
    ((hf.eventually (by simp)).and (hg.eventually (by simp))).mono fun y hy =>
      partialAt_add (hy.1.differentiableAt (by simp)) (hy.2.differentiableAt (by simp)) μ
  have hdf : ∀ μ, DifferentiableAt ℝ (partialAt f μ) x := fun μ =>
    (contDiffAt_partialAt (m := 1) hf (by norm_num) μ).differentiableAt one_ne_zero
  have hdg : ∀ μ, DifferentiableAt ℝ (partialAt g μ) x := fun μ =>
    (contDiffAt_partialAt (m := 1) hg (by norm_num) μ).differentiableAt one_ne_zero
  have h2 : ∀ μ, partialAt (partialAt (fun y => f y + g y) μ) μ x =
      partialAt (partialAt f μ) μ x + partialAt (partialAt g μ) μ x := fun μ => by
    rw [partialAt_congr_of_eventuallyEq (hev μ), partialAt_add (hdf μ) (hdg μ)]
  simp only [box, h2, Finset.sum_add_distrib]
  ring

/-- The wave operator of a `Cⁿ` function is `Cᵐ` for `m + 2 ≤ n`. -/
theorem contDiffAt_box {m n : ℕ∞ω} {f : Spacetime → ℝ} {x : Spacetime}
    (hf : ContDiffAt ℝ n f x) (hmn : m + 2 ≤ n) : ContDiffAt ℝ m (box f) x := by
  have h2 : ∀ μ, ContDiffAt ℝ m (partialAt (partialAt f μ) μ) x := fun μ =>
    contDiffAt_partialAt (contDiffAt_partialAt (m := m + 1) hf
      (by rwa [add_assoc, one_add_one_eq_two]) μ) le_rfl μ
  exact (h2 0).neg.add (ContDiffAt.sum fun i _ => h2 i.succ)

/-- The wave operator commutes with the derivatives on a function that is `C³` near the point. -/
theorem box_partialAt {f : Spacetime → ℝ} {x : Spacetime} (hf : ContDiffAt ℝ 3 f x)
    (ν : Fin 4) : box (partialAt f ν) x = partialAt (box f) ν x := by
  have h2 : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 f y :=
    (hf.eventually (by simp)).mono fun y hy => hy.of_le (by norm_num)
  have hcomm : ∀ μ, partialAt (partialAt (partialAt f ν) μ) μ x =
      partialAt (partialAt (partialAt f μ) μ) ν x := fun μ => by
    have hev : partialAt (partialAt f ν) μ =ᶠ[𝓝 x] partialAt (partialAt f μ) ν :=
      h2.mono fun y hy => partialAt_partialAt_comm hy μ ν
    rw [partialAt_congr_of_eventuallyEq hev]
    exact partialAt_partialAt_comm (contDiffAt_partialAt hf (by norm_num) μ) μ ν
  have hd : ∀ μ, DifferentiableAt ℝ (partialAt (partialAt f μ) μ) x := fun μ =>
    (contDiffAt_partialAt (m := 1) (contDiffAt_partialAt (m := 2) hf (by norm_num) μ)
      (by norm_num) μ).differentiableAt one_ne_zero
  have hbox : box f = fun y => -partialAt (partialAt f 0) 0 y +
      ∑ i : Fin 3, partialAt (partialAt f i.succ) i.succ y := rfl
  rw [hbox, partialAt_add (hd 0).fun_neg (DifferentiableAt.fun_sum (u := Finset.univ)
    (A := fun i : Fin 3 => partialAt (partialAt f i.succ) i.succ) fun i _ => hd _),
    partialAt_neg, partialAt_sum _ fun i _ => hd _]
  simp only [box, hcomm]

/-- The gauge condition solves the wave equation: if `box A_ν = −k_ν` (that is, `box A₀ = k⁰` and
`box aᵢ = −kⁱ`) and `∂_μ k^μ = 0` on an open set, then `box (∂^μ A_μ) = 0` there, for a potential
of class `C³`. -/
theorem box_lorenzDivergence {U : Set Spacetime} (hU : IsOpen U) {A : Potential}
    (hA : ContDiffOn ℝ 3 A U) {k : Spacetime → Spacetime}
    (hk0 : ∀ y ∈ U, box (potentialComponent A 0) y = k y 0)
    (hk : ∀ y ∈ U, ∀ i : Fin 3, box (potentialComponent A i.succ) y = -k y i.succ)
    (hdiv : ∀ y ∈ U, divergence4 k y = 0) {x : Spacetime} (hx : x ∈ U) :
    box (lorenzDivergence A) x = 0 := by
  have hAx : ContDiffAt ℝ 3 A x := (hA x hx).contDiffAt (hU.mem_nhds hx)
  have ha := contDiffAt_potentialComponent hAx
  have hg : ∀ ν, ContDiffAt ℝ 2 (partialAt (potentialComponent A ν) ν) x := fun ν =>
    contDiffAt_partialAt (ha ν) (by norm_num) ν
  have hev0 : (fun y => k y 0) =ᶠ[𝓝 x] box (potentialComponent A 0) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hx) fun y hy => (hk0 y hy).symm
  have hev : ∀ i : Fin 3, (fun y => k y i.succ) =ᶠ[𝓝 x]
      fun y => -box (potentialComponent A i.succ) y := fun i =>
    Filter.eventuallyEq_of_mem (hU.mem_nhds hx) fun y hy => by rw [hk y hy i, neg_neg]
  have hb : ∀ ν, DifferentiableAt ℝ (box (potentialComponent A ν)) x := fun ν =>
    (contDiffAt_box (m := 1) (ha ν) (by norm_num)).differentiableAt one_ne_zero
  have hkd : DifferentiableAt ℝ k x := by
    refine differentiableAt_pi.mpr fun ν => ?_
    refine Fin.cases ?_ (fun i => ?_) ν
    · exact (hb 0).congr_of_eventuallyEq hev0
    · exact (hb i.succ).fun_neg.congr_of_eventuallyEq (hev i)
  have hdk := hdiv x hx
  rw [divergence4_eq hkd, Fin.sum_univ_succ, partialAt_congr_of_eventuallyEq hev0] at hdk
  simp only [partialAt_congr_of_eventuallyEq (hev _), partialAt_neg] at hdk
  have hL : lorenzDivergence A = fun y => -partialAt (potentialComponent A 0) 0 y +
      (partialAt (potentialComponent A 1) 1 y + partialAt (potentialComponent A 2) 2 y +
        partialAt (potentialComponent A 3) 3 y) := by
    funext y
    simp only [lorenzDivergence, Fin.sum_univ_three]
    rfl
  rw [hL, box_add (hg 0).neg (((hg 1).add (hg 2)).add (hg 3)), box_neg,
    box_add ((hg 1).add (hg 2)) (hg 3), box_add (hg 1) (hg 2), box_partialAt (ha 0),
    box_partialAt (ha 1), box_partialAt (ha 2), box_partialAt (ha 3)]
  simp only [Fin.sum_univ_three, fin_succ_zero, fin_succ_one, fin_succ_two] at hdk
  linarith


/-! ### The propagation of the constraints -/

/-- The electric components of a field that is `Cⁿ` near a point are `Cⁿ` near it. -/
theorem contDiffAt_electricField {n : ℕ∞ω} {G : Field} {x : Spacetime}
    (hG : ContDiffAt ℝ n G x) (i : Fin 3) : ContDiffAt ℝ n (electricField G i) x := by
  have h : electricField G i = fun y => component (G y) i.succ 0 :=
    funext fun y => electricVector_apply (G y) i
  rw [h]
  exact (ContinuousAlternatingMap.apply ℝ Spacetime ℝ
    ![Pi.single i.succ 1, Pi.single 0 1]).contDiff.contDiffAt.comp x hG

/-- The magnetic components of a field that is `Cⁿ` near a point are `Cⁿ` near it. -/
theorem contDiffAt_magneticField {n : ℕ∞ω} {G : Field} {x : Spacetime}
    (hG : ContDiffAt ℝ n G x) (i : Fin 3) : ContDiffAt ℝ n (magneticField G i) x := by
  fin_cases i
  · exact (ContinuousAlternatingMap.apply ℝ Spacetime ℝ
      ![Pi.single 2 1, Pi.single 3 1]).contDiff.contDiffAt.comp x hG
  · exact (ContinuousAlternatingMap.apply ℝ Spacetime ℝ
      ![Pi.single 3 1, Pi.single 1 1]).contDiff.contDiffAt.comp x hG
  · exact (ContinuousAlternatingMap.apply ℝ Spacetime ℝ
      ![Pi.single 1 1, Pi.single 2 1]).contDiff.contDiffAt.comp x hG

/-- The divergence of a curl vanishes: `div curl f = 0` for `f` that is `C²` near the point. -/
theorem partialAt_curl_sum {f : Fin 3 → Spacetime → ℝ} {x : Spacetime}
    (hf : ∀ i, ContDiffAt ℝ 2 (f i) x) :
    partialAt (fun y => curl f y 0) 1 x + partialAt (fun y => curl f y 1) 2 x +
      partialAt (fun y => curl f y 2) 3 x = 0 := by
  have hd : ∀ i μ, DifferentiableAt ℝ (partialAt (f i) μ) x := fun i μ =>
    (contDiffAt_partialAt (m := 1) (hf i) (by norm_num) μ).differentiableAt one_ne_zero
  simp only [curl, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [partialAt_sub (hd _ _) (hd _ _), partialAt_sub (hd _ _) (hd _ _),
    partialAt_sub (hd _ _) (hd _ _)]
  linear_combination partialAt_partialAt_comm (hf 2) 1 2 - partialAt_partialAt_comm (hf 1) 1 3 +
    partialAt_partialAt_comm (hf 0) 2 3

/-- The propagation of the constraints: where the field is `C²` and satisfies the equations of
Faraday and Ampère with a differentiable current of zero divergence, `∂ₜ(div B) = 0` and
`∂ₜ(div E − k⁰) = 0`. -/
theorem constraint_propagation {U : Set Spacetime} (hU : IsOpen U) {F : Field}
    (hF : ContDiffOn ℝ 2 F U) {k : Spacetime → Spacetime} (hk : DifferentiableOn ℝ k U)
    (hfar : ∀ y ∈ U, ∀ i, partialAt (magneticField F i) 0 y + curl (electricField F) y i = 0)
    (hamp : ∀ y ∈ U, ∀ i,
      curl (magneticField F) y i - partialAt (electricField F i) 0 y = k y i.succ)
    (hdiv : ∀ y ∈ U, divergence4 k y = 0) {x : Spacetime} (hx : x ∈ U) :
    partialAt (divergence3 (magneticField F)) 0 x = 0 ∧
      partialAt (fun y => divergence3 (electricField F) y - k y 0) 0 x = 0 := by
  have hFx : ContDiffAt ℝ 2 F x := (hF x hx).contDiffAt (hU.mem_nhds hx)
  have hkx : DifferentiableAt ℝ k x := (hk x hx).differentiableAt (hU.mem_nhds hx)
  have hE := contDiffAt_electricField hFx
  have hB := contDiffAt_magneticField hFx
  have hdE : ∀ i μ, DifferentiableAt ℝ (partialAt (electricField F i) μ) x := fun i μ =>
    (contDiffAt_partialAt (m := 1) (hE i) (by norm_num) μ).differentiableAt one_ne_zero
  have hdB : ∀ i μ, DifferentiableAt ℝ (partialAt (magneticField F i) μ) x := fun i μ =>
    (contDiffAt_partialAt (m := 1) (hB i) (by norm_num) μ).differentiableAt one_ne_zero
  have hkc : ∀ μ, DifferentiableAt ℝ (fun y => k y μ) x := fun μ =>
    (differentiableAt_pi.mp hkx) μ
  have hcE : ∀ i, DifferentiableAt ℝ (fun y => curl (electricField F) y i) x := fun i => by
    fin_cases i <;>
      simpa [curl] using (hdE _ _).fun_sub (hdE _ _)
  have hcB : ∀ i, DifferentiableAt ℝ (fun y => curl (magneticField F) y i) x := fun i => by
    fin_cases i <;>
      simpa [curl] using (hdB _ _).fun_sub (hdB _ _)
  have hfar' : ∀ i, partialAt (magneticField F i) 0 =ᶠ[𝓝 x]
      fun y => -curl (electricField F) y i := fun i =>
    Filter.eventuallyEq_of_mem (hU.mem_nhds hx) fun y hy => by linarith [hfar y hy i]
  have hamp' : ∀ i, partialAt (electricField F i) 0 =ᶠ[𝓝 x]
      fun y => curl (magneticField F) y i - k y i.succ := fun i =>
    Filter.eventuallyEq_of_mem (hU.mem_nhds hx) fun y hy => by linarith [hamp y hy i]
  have hdivB : divergence3 (magneticField F) = fun y => partialAt (magneticField F 0) 1 y +
      partialAt (magneticField F 1) 2 y + partialAt (magneticField F 2) 3 y := by
    funext y
    simp only [divergence3, Fin.sum_univ_three]
    rfl
  have hdivE : divergence3 (electricField F) = fun y => partialAt (electricField F 0) 1 y +
      partialAt (electricField F 1) 2 y + partialAt (electricField F 2) 3 y := by
    funext y
    simp only [divergence3, Fin.sum_univ_three]
    rfl
  have hcurlE := partialAt_curl_sum hE
  have hcurlB := partialAt_curl_sum hB
  have hd4 := hdiv x hx
  rw [divergence4_eq hkx, Fin.sum_univ_four] at hd4
  constructor
  · rw [hdivB, partialAt_add ((hdB _ _).fun_add (hdB _ _)) (hdB _ _),
      partialAt_add (hdB _ _) (hdB _ _), partialAt_partialAt_comm (hB 0) 0 1,
      partialAt_partialAt_comm (hB 1) 0 2, partialAt_partialAt_comm (hB 2) 0 3,
      partialAt_congr_of_eventuallyEq (hfar' 0), partialAt_congr_of_eventuallyEq (hfar' 1),
      partialAt_congr_of_eventuallyEq (hfar' 2), partialAt_neg, partialAt_neg, partialAt_neg]
    linear_combination -hcurlE
  · have hdivEd : DifferentiableAt ℝ (divergence3 (electricField F)) x := by
      rw [hdivE]
      exact ((hdE _ _).fun_add (hdE _ _)).add (hdE _ _)
    rw [partialAt_sub hdivEd (hkc 0), hdivE,
      partialAt_add ((hdE _ _).fun_add (hdE _ _)) (hdE _ _),
      partialAt_add (hdE _ _) (hdE _ _), partialAt_partialAt_comm (hE 0) 0 1,
      partialAt_partialAt_comm (hE 1) 0 2, partialAt_partialAt_comm (hE 2) 0 3,
      partialAt_congr_of_eventuallyEq (hamp' 0), partialAt_congr_of_eventuallyEq (hamp' 1),
      partialAt_congr_of_eventuallyEq (hamp' 2), partialAt_sub (hcB 0) (hkc _),
      partialAt_sub (hcB 1) (hkc _), partialAt_sub (hcB 2) (hkc _)]
    simp only [fin_succ_zero, fin_succ_one, fin_succ_two]
    linear_combination hcurlB - hd4


/-! ### Uniqueness for the wave equation -/

/-- The derivative of a `Cⁿ` function along a co-ordinate is `Cᵐ` for `m + 1 ≤ n`. -/
theorem contDiff_partialAt_of_le {m n : ℕ∞ω} {f : Spacetime → ℝ} (hf : ContDiff ℝ n f)
    (hmn : m + 1 ≤ n) (μ : Fin 4) : ContDiff ℝ m (partialAt f μ) :=
  (hf.fderiv_right hmn).clm_apply contDiff_const

/-- The divergence `∂^μ A_μ` of a `Cⁿ` potential is `Cᵐ` for `m + 1 ≤ n`. -/
theorem contDiff_lorenzDivergence {m n : ℕ∞ω} {A : Potential} (hA : ContDiff ℝ n A)
    (hmn : m + 1 ≤ n) : ContDiff ℝ m (lorenzDivergence A) := by
  have ha : ∀ ν, ContDiff ℝ n (potentialComponent A ν) := fun ν =>
    ((ContinuousLinearMap.apply ℝ ℝ (Pi.single ν 1)).comp
      oneCovector.toContinuousLinearMap).contDiff.comp hA
  have hp : ∀ ν, ContDiff ℝ m (partialAt (potentialComponent A ν) ν) := fun ν =>
    contDiff_partialAt_of_le (ha ν) hmn ν
  exact (hp 0).neg.add (ContDiff.sum fun i _ => hp i.succ)

/-- The derivative along a line through a point: `d/ds u(y + s eμ) = ∂_μ u(y + s eμ)`. -/
theorem hasDerivAt_comp_line {u : Spacetime → ℝ} {y : Spacetime} {r : ℝ} (μ : Fin 4)
    (hu : DifferentiableAt ℝ u (y + r • Pi.single μ 1)) :
    HasDerivAt (fun s => u (y + s • Pi.single μ 1)) (partialAt u μ (y + r • Pi.single μ 1)) r := by
  have hl : HasDerivAt (fun s : ℝ => y + s • (Pi.single μ 1 : Spacetime)) (Pi.single μ 1) r := by
    simpa using ((hasDerivAt_id r).smul_const (Pi.single μ 1 : Spacetime)).const_add y
  exact hu.hasFDerivAt.comp_hasDerivAt r hl

/-- A function that vanishes on a line near a point has the derivative zero along the line. -/
theorem partialAt_eq_zero_of_eventually {u : Spacetime → ℝ} {y : Spacetime} (μ : Fin 4)
    (hu : DifferentiableAt ℝ u y) (h : ∀ᶠ s in 𝓝 (0 : ℝ), u (y + s • Pi.single μ 1) = 0) :
    partialAt u μ y = 0 := by
  have hd := hasDerivAt_comp_line (y := y) (r := 0) μ (by simpa using hu)
  simp only [zero_smul, add_zero] at hd
  exact hd.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq h)

/-- The current `(e, S)` of the energy of the wave equation: `e = ½ ((∂₀u)² + Σᵢ (∂ᵢu)²)` and
`Sᵢ = −∂₀u ∂ᵢu`. -/
def waveEnergyCurrent (u : Spacetime → ℝ) : Spacetime → Spacetime := fun y =>
  ![(1 / 2 : ℝ) * (partialAt u 0 y * partialAt u 0 y + partialAt u 1 y * partialAt u 1 y +
      partialAt u 2 y * partialAt u 2 y + partialAt u 3 y * partialAt u 3 y),
    -(partialAt u 0 y * partialAt u 1 y), -(partialAt u 0 y * partialAt u 2 y),
    -(partialAt u 0 y * partialAt u 3 y)]

/-- The spatial components `Sᵢ = −∂₀u ∂ᵢu` of the current of the energy. -/
theorem waveEnergyCurrent_succ (u : Spacetime → ℝ) (y : Spacetime) (i : Fin 3) :
    waveEnergyCurrent u y i.succ = -(partialAt u 0 y * partialAt u i.succ y) := by
  fin_cases i <;> rfl

/-- The current of the energy of a `C²` function is `C¹`. -/
theorem contDiff_waveEnergyCurrent {u : Spacetime → ℝ} (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (waveEnergyCurrent u) := by
  have p : ∀ μ, ContDiff ℝ 1 (partialAt u μ) := fun μ =>
    contDiff_partialAt_of_le hu (by norm_num) μ
  refine contDiff_pi.mpr fun μ => ?_
  fin_cases μ
  · exact contDiff_const.mul (((((p 0).mul (p 0)).add ((p 1).mul (p 1))).add
      ((p 2).mul (p 2))).add ((p 3).mul (p 3)))
  · exact ((p 0).mul (p 1)).neg
  · exact ((p 0).mul (p 2)).neg
  · exact ((p 0).mul (p 3)).neg

/-- The balance of the energy of the wave equation: `∂₀e + Σᵢ ∂ᵢSᵢ = −∂₀u box u`. -/
theorem divergence4_waveEnergyCurrent {u : Spacetime → ℝ} (hu : ContDiff ℝ 2 u)
    (y : Spacetime) : divergence4 (waveEnergyCurrent u) y = -(partialAt u 0 y * box u y) := by
  have hP := contDiff_waveEnergyCurrent hu
  have hc : ∀ μ, partialAt (partialAt u μ) 0 y = partialAt (partialAt u 0) μ y := fun μ =>
    partialAt_partialAt_comm hu.contDiffAt 0 μ
  have hc1 := hc 1
  have hc2 := hc 2
  have hc3 := hc 3
  have hd : ∀ μ, DifferentiableAt ℝ (partialAt u μ) y := fun μ =>
    ((contDiff_partialAt_of_le (m := 1) hu (by norm_num) μ).differentiable one_ne_zero) y
  have hd0 := hd 0
  have hd1 := hd 1
  have hd2 := hd 2
  have hd3 := hd 3
  rw [divergence4_eq (hP.differentiable one_ne_zero y), Fin.sum_univ_four]
  have h0 : (fun z => waveEnergyCurrent u z 0) = fun z => (1 / 2 : ℝ) *
      (partialAt u 0 z * partialAt u 0 z + partialAt u 1 z * partialAt u 1 z +
        partialAt u 2 z * partialAt u 2 z + partialAt u 3 z * partialAt u 3 z) := rfl
  have h1 : (fun z => waveEnergyCurrent u z 1) = fun z =>
      -(partialAt u 0 z * partialAt u 1 z) := rfl
  have h2 : (fun z => waveEnergyCurrent u z 2) = fun z =>
      -(partialAt u 0 z * partialAt u 2 z) := rfl
  have h3 : (fun z => waveEnergyCurrent u z 3) = fun z =>
      -(partialAt u 0 z * partialAt u 3 z) := rfl
  rw [h0, h1, h2, h3]
  simp only [box, Fin.sum_univ_three, fin_succ_zero, fin_succ_one, fin_succ_two]
  generalize partialAt u 0 = p₀ at hc1 hc2 hc3 hd0 ⊢
  generalize partialAt u 1 = p₁ at hc1 hd1 ⊢
  generalize partialAt u 2 = p₂ at hc2 hd2 ⊢
  generalize partialAt u 3 = p₃ at hc3 hd3 ⊢
  simp (disch := fun_prop) only [partialAt_const_mul, partialAt_add, partialAt_mul,
    partialAt_neg]
  linear_combination p₁ y * hc1 + p₂ y * hc2 + p₃ y * hc3

/-- Uniqueness for the wave equation by the conservation of the energy: a `C²` function `u` on
space-time with `box u = 0` on `[0, T] × ℝ³` that vanishes for `t ∈ [0, T]` outside the spatial
box `|xⁱ| < R`, and that has `u = ∂ₜu = 0` at `t = 0`, vanishes on `[0, T] × ℝ³`. -/
theorem eq_zero_of_box_eq_zero {u : Spacetime → ℝ} (hu : ContDiff ℝ 2 u) {T R : ℝ}
    (hbox : ∀ y, 0 ≤ y 0 → y 0 ≤ T → box u y = 0)
    (hsupp : ∀ y, 0 ≤ y 0 → y 0 ≤ T → u y ≠ 0 → ∀ i : Fin 3, |y i.succ| < R)
    (h0 : ∀ y, y 0 = 0 → u y = 0) (h1 : ∀ y, y 0 = 0 → partialAt u 0 y = 0) :
    ∀ y, 0 ≤ y 0 → y 0 ≤ T → u y = 0 := by
  set c : ℝ := |R| + 1 with hc
  have hc1 : |R| + 1 = c := hc.symm
  have hRc : R < c := by linarith [le_abs_self R]
  have hc0 : 0 < c := by linarith [abs_nonneg R]
  have hdu : ∀ z, DifferentiableAt ℝ u z := hu.differentiable (by norm_num)
  have hout : ∀ z, 0 ≤ z 0 → z 0 ≤ T → ∀ j : Fin 3, R ≤ |z j.succ| → u z = 0 :=
    fun z hz0 hzT j hj => by
      by_contra hne
      exact absurd (hsupp z hz0 hzT hne j) (not_lt.mpr hj)
  have hsingle : ∀ (j : Fin 3) (r : ℝ) (z : Spacetime),
      (z + r • (Pi.single j.succ 1 : Spacetime)) 0 = z 0 := fun j r z => by
    simp [(Fin.succ_ne_zero j).symm]
  -- the spatial derivatives vanish on the faces `xʲ = ±c` of the box
  have hface : ∀ z, 0 ≤ z 0 → z 0 ≤ T → ∀ j : Fin 3, (z j.succ = c ∨ z j.succ = -c) →
      partialAt u j.succ z = 0 := by
    intro z hz0 hzT j hj
    refine partialAt_eq_zero_of_eventually _ (hdu z) ?_
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
      (show (0 : ℝ) < 1 by norm_num)] with r hr
    refine hout _ (by rw [hsingle]; exact hz0) (by rw [hsingle]; exact hzT) j ?_
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    obtain ⟨hr1, hr2⟩ := hr
    rcases hj with h | h <;> rw [h]
    · rw [abs_of_pos (by linarith [abs_nonneg R])]
      linarith [le_abs_self R, abs_nonneg R]
    · rw [abs_of_neg (by linarith [abs_nonneg R])]
      linarith [le_abs_self R, abs_nonneg R]
  -- the spatial derivatives vanish at the time zero
  have hspatial0 : ∀ z : Spacetime, z 0 = 0 → ∀ j : Fin 3, partialAt u j.succ z = 0 :=
    fun z hz j => partialAt_eq_zero_of_eventually _ (hdu z)
      (Filter.Eventually.of_forall fun r => h0 _ (by rw [hsingle]; exact hz))
  -- the time derivative vanishes inside the slab
  have key : ∀ y : Spacetime, 0 < y 0 → y 0 < T → partialAt u 0 y = 0 := by
    intro y hy0 hyT
    by_cases hin : ∀ j : Fin 3, |y j.succ| < c
    · let a : Spacetime := Fin.cons 0 fun _ => -c
      let b : Spacetime := Fin.cons (y 0) fun _ => c
      have ha0 : a 0 = 0 := rfl
      have hb0 : b 0 = y 0 := rfl
      have has : ∀ j : Fin 3, a j.succ = -c := fun _ => rfl
      have hbs : ∀ j : Fin 3, b j.succ = c := fun _ => rfl
      have hab : a ≤ b := by
        intro μ
        refine Fin.cases ?_ (fun j => ?_) μ
        · rw [ha0, hb0]
          exact hy0.le
        · rw [has, hbs]
          linarith
      have hP := contDiff_waveEnergyCurrent hu
      have hbd := box_divergence hP hab
      have hint : ∫ z in Icc a b, divergence4 (waveEnergyCurrent u) z = 0 :=
        setIntegral_eq_zero_of_forall_eq_zero fun z hz => by
          rw [divergence4_waveEnergyCurrent hu,
            hbox z (ha0 ▸ hz.1 0) (le_trans (hb0 ▸ hz.2 0) hyT.le), mul_zero, neg_zero]
      have hsucc : ∀ i : Fin 3, (0 : Fin 4) = i.succ.succAbove 0 := fun i =>
        (Fin.succ_succAbove_zero i).symm
      have hflux : ∀ i : Fin 3, faceFlux (waveEnergyCurrent u) a b i.succ = 0 := by
        intro i
        have hw : ∀ (x : ℝ), (x = c ∨ x = -c) → ∀ w ∈ Icc (a ∘ i.succ.succAbove)
            (b ∘ i.succ.succAbove), waveEnergyCurrent u (Fin.insertNth i.succ x w) i.succ = 0 :=
          by
          intro x hx w hw
          have hz0 : (Fin.insertNth i.succ x w : Spacetime) 0 = w 0 := by
            rw [hsucc i, Fin.insertNth_apply_succAbove]
          have hw0 : 0 ≤ w 0 := by
            have h := hw.1 0
            simp only [Function.comp_apply, ← hsucc i, ha0] at h
            exact h
          have hwT : w 0 ≤ T := by
            have h := hw.2 0
            simp only [Function.comp_apply, ← hsucc i, hb0] at h
            linarith
          rw [waveEnergyCurrent_succ, hface _ (hz0 ▸ hw0) (hz0 ▸ hwT) i
            (by rw [Fin.insertNth_apply_same]; exact hx), mul_zero, neg_zero]
        rw [faceFlux, setIntegral_eq_zero_of_forall_eq_zero (hw _ (Or.inl (hbs i))),
          setIntegral_eq_zero_of_forall_eq_zero (hw _ (Or.inr (has i))), sub_zero]
      have hcharge0 : charge (waveEnergyCurrent u) a b (a 0) = 0 := by
        rw [charge, ha0]
        refine setIntegral_eq_zero_of_forall_eq_zero fun w _ => ?_
        have hz : (Fin.insertNth 0 (0 : ℝ) w : Spacetime) 0 = 0 := Fin.insertNth_apply_same _ _ _
        have hs1 : partialAt u 1 (Fin.insertNth 0 (0 : ℝ) w) = 0 := hspatial0 _ hz 0
        have hs2 : partialAt u 2 (Fin.insertNth 0 (0 : ℝ) w) = 0 := hspatial0 _ hz 1
        have hs3 : partialAt u 3 (Fin.insertNth 0 (0 : ℝ) w) = 0 := hspatial0 _ hz 2
        have ht := h1 _ hz
        change (1 / 2 : ℝ) * (_ * _ + _ * _ + _ * _ + _ * _) = 0
        rw [hs1, hs2, hs3, ht]
        ring
      simp only [hflux, Finset.sum_const_zero, add_zero, hint, hcharge0, sub_zero, hb0] at hbd
      -- the energy at the time `y 0` vanishes, so its density vanishes inside the box
      let f : (Fin 3 → ℝ) → ℝ := fun w => waveEnergyCurrent u (Fin.insertNth 0 (y 0) w) 0
      have hPc : Continuous (waveEnergyCurrent u) := hP.continuous
      have hfc : Continuous f :=
        (continuous_apply 0).comp (hPc.comp (continuous_const.finInsertNth 0 continuous_id))
      have hnonneg : ∀ w, 0 ≤ f w := fun w => by
        change 0 ≤ (1 / 2 : ℝ) * (_ * _ + _ * _ + _ * _ + _ * _)
        exact mul_nonneg (by norm_num) (add_nonneg (add_nonneg (add_nonneg (mul_self_nonneg _)
          (mul_self_nonneg _)) (mul_self_nonneg _)) (mul_self_nonneg _))
      have hzero : ∫ w in Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0), f w = 0 := hbd
      have hae := (setIntegral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hnonneg)
        (hfc.continuousOn.integrableOn_compact isCompact_Icc)).mp hzero
      let O : Set (Fin 3 → ℝ) := Set.pi univ fun _ => Ioo (-c) c
      have hO : O ⊆ Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0) := fun w hw =>
        ⟨fun j => by
          simp only [Function.comp_apply, Fin.succAbove_zero, has]
          exact (hw j (mem_univ j)).1.le,
        fun j => by
          simp only [Function.comp_apply, Fin.succAbove_zero, hbs]
          exact (hw j (mem_univ j)).2.le⟩
      have heq := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset hO hae)
        (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo) hfc.continuousOn continuousOn_const
      have hyO : Fin.removeNth 0 y ∈ O := fun j _ => by
        have h := abs_lt.mp (hin j)
        simp only [Fin.removeNth, Fin.succAbove_zero]
        exact h
      have hfy := heq hyO
      simp only [f, Fin.insertNth_self_removeNth] at hfy
      change (1 / 2 : ℝ) * (partialAt u 0 y * partialAt u 0 y + partialAt u 1 y * partialAt u 1 y +
        partialAt u 2 y * partialAt u 2 y + partialAt u 3 y * partialAt u 3 y) = 0 at hfy
      have hsq : partialAt u 0 y * partialAt u 0 y = 0 := by
        nlinarith [mul_self_nonneg (partialAt u 0 y), mul_self_nonneg (partialAt u 1 y),
          mul_self_nonneg (partialAt u 2 y), mul_self_nonneg (partialAt u 3 y)]
      exact mul_self_eq_zero.mp hsq
    · push Not at hin
      obtain ⟨j, hj⟩ := hin
      refine partialAt_eq_zero_of_eventually _ (hdu y) ?_
      filter_upwards [Ioo_mem_nhds (show -(y 0) < 0 by linarith)
        (show (0 : ℝ) < T - y 0 by linarith)] with r hr
      have ht : (y + r • (Pi.single 0 1 : Spacetime)) 0 = y 0 + r := by simp
      have hs : (y + r • (Pi.single 0 1 : Spacetime)) j.succ = y j.succ := by
        simp [Fin.succ_ne_zero]
      refine hout _ (by rw [ht]; linarith [hr.1]) (by rw [ht]; linarith [hr.2]) j ?_
      rw [hs]
      linarith
  -- integrate the time derivative from the time zero
  intro y hy0 hyT
  let y₀ : Spacetime := y - y 0 • Pi.single 0 1
  have hy₀ : ∀ r : ℝ, (y₀ + r • (Pi.single 0 1 : Spacetime)) 0 = r := fun r => by simp [y₀]
  have hcont : ContinuousOn (fun r : ℝ => u (y₀ + r • Pi.single 0 1)) (Icc 0 T) :=
    (hu.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
  have hderiv : ∀ r ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (fun r : ℝ => u (y₀ + r • Pi.single 0 1)) 0 (Ici r) r := by
    intro r hr
    have hd := hasDerivAt_comp_line (y := y₀) (r := r) 0 (hdu _)
    have hz : partialAt u 0 (y₀ + r • Pi.single 0 1) = 0 := by
      rcases hr.1.eq_or_lt with h | h
      · exact h1 _ (by rw [hy₀, ← h])
      · exact key _ (by rw [hy₀]; exact h) (by rw [hy₀]; exact hr.2)
    rw [hz] at hd
    exact hd.hasDerivWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont hderiv (y 0) ⟨hy0, hyT⟩
  have hy : y₀ + y 0 • Pi.single 0 1 = y := by simp [y₀]
  rw [hy, zero_smul, add_zero] at hconst
  rw [hconst]
  exact h0 _ (by simp [y₀])

/-- The gauge condition propagates: for a `C³` potential with `box A_ν = −k_ν` and
`∂_μ k^μ = 0` on an open set that contains `[0, T] × ℝ³`, whose divergence `∂^μ A_μ` vanishes for
`t ∈ [0, T]` outside a spatial box and has `∂^μ A_μ = ∂ₜ(∂^μ A_μ) = 0` at `t = 0`, the condition
of Lorenz `∂^μ A_μ = 0` holds on `[0, T] × ℝ³`. -/
theorem lorenzDivergence_eq_zero_of_initial {A : Potential} (hA : ContDiff ℝ 3 A)
    {U : Set Spacetime} (hU : IsOpen U) {T R : ℝ} (hslab : ∀ y, 0 ≤ y 0 → y 0 ≤ T → y ∈ U)
    {k : Spacetime → Spacetime}
    (hk0 : ∀ y ∈ U, box (potentialComponent A 0) y = k y 0)
    (hk : ∀ y ∈ U, ∀ i : Fin 3, box (potentialComponent A i.succ) y = -k y i.succ)
    (hdiv : ∀ y ∈ U, divergence4 k y = 0)
    (hsupp : ∀ y, 0 ≤ y 0 → y 0 ≤ T → lorenzDivergence A y ≠ 0 → ∀ i : Fin 3, |y i.succ| < R)
    (h0 : ∀ y, y 0 = 0 → lorenzDivergence A y = 0)
    (h1 : ∀ y, y 0 = 0 → partialAt (lorenzDivergence A) 0 y = 0) :
    ∀ y, 0 ≤ y 0 → y 0 ≤ T → lorenzDivergence A y = 0 :=
  eq_zero_of_box_eq_zero (contDiff_lorenzDivergence hA (by norm_num))
    (fun y hy0 hyT => box_lorenzDivergence hU hA.contDiffOn hk0 hk hdiv (hslab y hy0 hyT))
    hsupp h0 h1

end ProjectAinos.Electrodynamics
