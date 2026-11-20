/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.WaveEquation
public import ProjectAinos.Electrodynamics.StressTensor
public import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Plane waves

For a covector `ℓ`, an amplitude `a` and a real profile `f`, `planeWave ℓ a f` is the potential
`A = f(ℓ(x)) a` (Landau–Lifshitz, *The Classical Theory of Fields*, §47). `covectorInner α β` is
the pairing `g⁻¹(α, β) = −α₀β₀ + Σᵢ αᵢβᵢ` of two covectors.

* `fieldTensor_planeWave`: the field is `f′(ℓx) ℓ ∧ a`; `lorenzDivergence_planeWave`:
  `∂^μ A_μ = f′(ℓx) ⟨ℓ, a⟩`; `box_planeWave`: `box A_ν = f″(ℓx) ⟨ℓ, ℓ⟩ a_ν`.
* `vacuum_planeWave`: for a null `ℓ` and `⟨ℓ, a⟩ = 0` both field equations hold in the vacuum,
  and `scalarInvariant_planeWave`, `pseudoscalarInvariant_planeWave`: both invariants vanish,
  while `fieldTensor_planeWave_ne_zero`: the field is not zero where `f′(ℓx) ≠ 0` if `a` is not
  a multiple of `ℓ`.
* `wavevector κ n` is `ℓ = κ (dt − ⟨n, dx⟩)`; `transverse_planeWave`: for a unit vector `n` and
  `⟨ℓ, a⟩ = 0`, `E · n = 0`, `B = n × E`, `|B| = |E|`, the energy density is `|E|²`, the vector of
  Poynting is `|E|² n` and the stress is `T^{μν} = |E|² ℓ^μ ℓ^ν / κ²`; `transverse_stress` is the
  algebra of a field with `E · n = 0` and `B = n × E`.
* `transverse_of_vacuum`: a field in the vacuum that depends only on `t − ⟨n, x⟩` has constant
  components `E · n` and `B · n`, and `B − n × E` is constant.

The flux of the stress is local: an infinite plane wave has an infinite energy, and no statement
about a finite energy is made.
-/

@[expose] public section

noncomputable section

open Set Filter Matrix
open scoped ContDiff Topology

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

/-! ### The pairing of covectors -/

/-- The pairing `g⁻¹(α, β) = −α₀β₀ + Σᵢ αᵢβᵢ` of two covectors in the signature `(−+++)`. -/
def covectorInner (α β : FourCovector) : ℝ :=
  ∑ μ : Fin 4, lorentzSign .timeNegative μ * α (Pi.single μ 1) * β (Pi.single μ 1)

/-- The pairing of covectors in components. -/
theorem covectorInner_apply (α β : FourCovector) :
    covectorInner α β = -(α (Pi.single 0 1) * β (Pi.single 0 1)) +
      α (Pi.single 1 1) * β (Pi.single 1 1) + α (Pi.single 2 1) * β (Pi.single 2 1) +
      α (Pi.single 3 1) * β (Pi.single 3 1) := by
  simp only [covectorInner, Fin.sum_univ_four]
  simp [lorentzSign]

/-- The pairing of covectors is the metric on the raised vectors. -/
theorem covectorInner_eq_minkowskiForm (α β : FourCovector) :
    covectorInner α β = minkowskiForm .timeNegative 3 (sharp .timeNegative α)
      (sharp .timeNegative β) := by
  rw [minkowskiForm_apply, covectorInner]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [sharp_apply, sharp_apply]
  have h := ProjectAinos.Electrodynamics.lorentzSign_sq μ
  linear_combination
    (-(lorentzSign .timeNegative μ * α (Pi.single μ 1) * β (Pi.single μ 1))) * h

/-! ### The plane wave -/

/-- The plane wave `A = f(ℓ(x)) a` with the covector `ℓ`, the amplitude `a` and the profile
`f`. -/
def planeWave (ℓ a : FourCovector) (f : ℝ → ℝ) : Potential :=
  fun y => f (ℓ y) • oneCovector.symm a

/-- The components `A_ν = a_ν f(ℓx)` of a plane wave. -/
theorem potentialComponent_planeWave (ℓ a : FourCovector) (f : ℝ → ℝ) (ν : Fin 4) :
    potentialComponent (planeWave ℓ a f) ν = fun y => a (Pi.single ν 1) * f (ℓ y) := by
  funext y
  simp [potentialComponent, planeWave, mul_comm]

/-- A plane wave with a `Cⁿ` profile is `Cⁿ`. -/
theorem contDiff_planeWave {n : ℕ∞ω} (ℓ a : FourCovector) {f : ℝ → ℝ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (planeWave ℓ a f) :=
  (hf.comp ℓ.contDiff).smul contDiff_const

/-- The derivative of a function of the phase: `d f(ℓx) = f′(ℓx) ℓ`. -/
theorem hasFDerivAt_comp_covector (ℓ : FourCovector) {f : ℝ → ℝ} {x : Spacetime}
    (hf : DifferentiableAt ℝ f (ℓ x)) :
    HasFDerivAt (fun y => f (ℓ y)) (deriv f (ℓ x) • ℓ) x :=
  hf.hasDerivAt.comp_hasFDerivAt x ℓ.hasFDerivAt

/-- `∂_μ f(ℓx) = f′(ℓx) ℓ_μ`. -/
theorem partialAt_comp_covector (ℓ : FourCovector) {f : ℝ → ℝ} {x : Spacetime}
    (hf : DifferentiableAt ℝ f (ℓ x)) (μ : Fin 4) :
    partialAt (fun y => f (ℓ y)) μ x = deriv f (ℓ x) * ℓ (Pi.single μ 1) := by
  rw [partialAt, (hasFDerivAt_comp_covector ℓ hf).fderiv]
  rfl

/-- The field of a plane wave is `f′(ℓx) ℓ ∧ a`. -/
theorem fieldTensor_planeWave (ℓ a : FourCovector) {f : ℝ → ℝ} {x : Spacetime}
    (hf : DifferentiableAt ℝ f (ℓ x)) (v w : Spacetime) :
    fieldTensor (planeWave ℓ a f) x ![v, w] = deriv f (ℓ x) * (ℓ v * a w - ℓ w * a v) := by
  have hd : HasFDerivAt (planeWave ℓ a f)
      ((deriv f (ℓ x) • ℓ).smulRight (oneCovector.symm a)) x := by
    unfold planeWave
    exact (hasFDerivAt_comp_covector ℓ hf).smul_const (oneCovector.symm a)
  rw [fieldTensor_apply, hd.fderiv]
  simp
  ring

/-- The electric components of a plane wave: `Eᵢ = f′(ℓx) (ℓᵢ a₀ − ℓ₀ aᵢ)`. -/
theorem electricVector_planeWave (ℓ a : FourCovector) {f : ℝ → ℝ} {x : Spacetime}
    (hf : DifferentiableAt ℝ f (ℓ x)) (i : Fin 3) :
    electricVector (fieldTensor (planeWave ℓ a f) x) i =
      deriv f (ℓ x) * (ℓ (Pi.single i.succ 1) * a (Pi.single 0 1) -
        ℓ (Pi.single 0 1) * a (Pi.single i.succ 1)) := by
  rw [electricVector_apply, component, fieldTensor_planeWave ℓ a hf]

/-- The magnetic components of a plane wave: `B₁ = f′(ℓx) (ℓ₂ a₃ − ℓ₃ a₂)` and cyclically. -/
theorem magneticVector_planeWave (ℓ a : FourCovector) {f : ℝ → ℝ} {x : Spacetime}
    (hf : DifferentiableAt ℝ f (ℓ x)) :
    magneticVector (fieldTensor (planeWave ℓ a f) x) =
      ![deriv f (ℓ x) * (ℓ (Pi.single 2 1) * a (Pi.single 3 1) -
          ℓ (Pi.single 3 1) * a (Pi.single 2 1)),
        deriv f (ℓ x) * (ℓ (Pi.single 3 1) * a (Pi.single 1 1) -
          ℓ (Pi.single 1 1) * a (Pi.single 3 1)),
        deriv f (ℓ x) * (ℓ (Pi.single 1 1) * a (Pi.single 2 1) -
          ℓ (Pi.single 2 1) * a (Pi.single 1 1))] := by
  ext i
  fin_cases i <;> simp [magneticVector, component, fieldTensor_planeWave ℓ a hf]

/-- The derivative of a component of a plane wave: `∂_μ A_ν = a_ν f′(ℓx) ℓ_μ`. -/
theorem partialAt_potentialComponent_planeWave (ℓ a : FourCovector) {f : ℝ → ℝ} {x : Spacetime}
    (hf : DifferentiableAt ℝ f (ℓ x)) (ν μ : Fin 4) :
    partialAt (potentialComponent (planeWave ℓ a f) ν) μ x =
      a (Pi.single ν 1) * (deriv f (ℓ x) * ℓ (Pi.single μ 1)) := by
  rw [potentialComponent_planeWave,
    partialAt_const_mul _ (hasFDerivAt_comp_covector ℓ hf).differentiableAt,
    partialAt_comp_covector ℓ hf]

/-- The divergence of a plane wave: `∂^μ A_μ = f′(ℓx) ⟨ℓ, a⟩`. -/
theorem lorenzDivergence_planeWave (ℓ a : FourCovector) {f : ℝ → ℝ} {x : Spacetime}
    (hf : DifferentiableAt ℝ f (ℓ x)) :
    lorenzDivergence (planeWave ℓ a f) x = deriv f (ℓ x) * covectorInner ℓ a := by
  simp only [lorenzDivergence, partialAt_potentialComponent_planeWave ℓ a hf,
    Fin.sum_univ_three, covectorInner_apply, fin_succ_zero, fin_succ_one, fin_succ_two]
  ring

/-- The derivative of a `C²` profile is differentiable. -/
theorem differentiable_deriv_of_contDiff_two {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (deriv f) := by
  simpa [iteratedDeriv_one] using hf.differentiable_iteratedDeriv 1 (by norm_num)

/-- The wave operator of a plane wave: `box A_ν = f″(ℓx) ⟨ℓ, ℓ⟩ a_ν`. -/
theorem box_planeWave (ℓ a : FourCovector) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (ν : Fin 4)
    (x : Spacetime) :
    box (potentialComponent (planeWave ℓ a f) ν) x =
      deriv (deriv f) (ℓ x) * covectorInner ℓ ℓ * a (Pi.single ν 1) := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd' := differentiable_deriv_of_contDiff_two hf
  have h1 : ∀ μ, partialAt (potentialComponent (planeWave ℓ a f) ν) μ =
      fun y => a (Pi.single ν 1) * ℓ (Pi.single μ 1) * deriv f (ℓ y) := fun μ => by
    funext y
    rw [partialAt_potentialComponent_planeWave ℓ a (hd _)]
    ring
  have h2 : ∀ μ, partialAt (partialAt (potentialComponent (planeWave ℓ a f) ν) μ) μ x =
      a (Pi.single ν 1) * ℓ (Pi.single μ 1) *
        (deriv (deriv f) (ℓ x) * ℓ (Pi.single μ 1)) := fun μ => by
    rw [h1, partialAt_const_mul _ (hasFDerivAt_comp_covector ℓ (hd' _)).differentiableAt,
      partialAt_comp_covector ℓ (hd' _)]
  simp only [box, h2, Fin.sum_univ_three, covectorInner_apply, fin_succ_zero, fin_succ_one,
    fin_succ_two]
  ring

/-- The current form of the vanishing current vanishes. -/
theorem matterCurrentForm_const_zero (y : Spacetime) :
    SourcedAction.matterCurrentForm (fun _ => (0 : Spacetime)) y = 0 := by
  have h0 := interior_smul_vector (0 : ℝ) (0 : Spacetime) (coordinateForm (n := 4) id)
  rw [zero_smul, zero_smul] at h0
  change -interior (0 : Spacetime) (coordinateForm (n := 4) id) = 0
  rw [h0, neg_zero]

/-- A plane wave with a null covector `ℓ` and `⟨ℓ, a⟩ = 0` satisfies both field equations in the
vacuum: `dF = 0` and `d(−⋆F) = 0`, and in the frame of the co-ordinates `div B = 0`,
`∂ₜB + curl E = 0`, `div E = 0`, `curl B − ∂ₜE = 0`. -/
theorem vacuum_planeWave {ℓ a : FourCovector} (hnull : covectorInner ℓ ℓ = 0)
    (horth : covectorInner ℓ a = 0) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    (∀ x, exteriorDerivative (fieldTensor (planeWave ℓ a f)) x = 0) ∧
    (∀ x, exteriorDerivative (fun y => -star (fieldTensor (planeWave ℓ a f) y)) x = 0) ∧
    ∀ x, (divergence3 (magneticField (fieldTensor (planeWave ℓ a f))) x = 0 ∧
        ∀ i, partialAt (magneticField (fieldTensor (planeWave ℓ a f)) i) 0 x +
          curl (electricField (fieldTensor (planeWave ℓ a f))) x i = 0) ∧
      (divergence3 (electricField (fieldTensor (planeWave ℓ a f))) x = 0 ∧
        ∀ i, curl (magneticField (fieldTensor (planeWave ℓ a f))) x i -
          partialAt (electricField (fieldTensor (planeWave ℓ a f)) i) 0 x = 0) := by
  have hA := contDiff_planeWave ℓ a hf
  refine ⟨fun x => bianchi_on _ isOpen_univ hA.contDiffOn (mem_univ x), ?_⟩
  have hL : ∀ y ∈ (univ : Set Spacetime), lorenzDivergence (planeWave ℓ a f) y = 0 :=
    fun y _ => by
      rw [lorenzDivergence_planeWave ℓ a (hf.differentiable (by norm_num) _), horth, mul_zero]
  have hbox : ∀ y ∈ (univ : Set Spacetime),
      box (potentialComponent (planeWave ℓ a f) 0) y = (fun _ => (0 : Spacetime)) y 0 ∧
        ∀ i : Fin 3, box (potentialComponent (planeWave ℓ a f) i.succ) y =
          -(fun _ => (0 : Spacetime)) y i.succ := fun y _ =>
    ⟨by rw [box_planeWave ℓ a hf, hnull]; simp,
      fun i => by rw [box_planeWave ℓ a hf, hnull]; simp⟩
  have h := (maxwell_iff_box_of_lorenz isOpen_univ hA.contDiffOn hL _).mpr hbox
  have he := (excitation_iff_box_of_lorenz isOpen_univ hA.contDiffOn hL _).mpr hbox
  refine ⟨fun x => (he x (mem_univ x)).trans (matterCurrentForm_const_zero x), fun x => ?_⟩
  simpa using h x (mem_univ x)

/-- The invariant `B² − E²` of a plane wave with a null `ℓ` and `⟨ℓ, a⟩ = 0` vanishes. -/
theorem scalarInvariant_planeWave {ℓ a : FourCovector} (hnull : covectorInner ℓ ℓ = 0)
    (horth : covectorInner ℓ a = 0) {f : ℝ → ℝ} {x : Spacetime}
    (hf : DifferentiableAt ℝ f (ℓ x)) :
    scalarInvariant (fieldTensor (planeWave ℓ a f) x) = 0 := by
  rw [scalarInvariant_vectors, magneticVector_planeWave ℓ a hf]
  simp only [Fin.sum_univ_three, electricVector_planeWave ℓ a hf, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, fin_succ_zero,
    fin_succ_one, fin_succ_two]
  rw [covectorInner_apply] at hnull horth
  generalize deriv f (ℓ x) = c at *
  generalize ℓ (Pi.single 0 1) = l0 at *
  generalize ℓ (Pi.single 1 1) = l1 at *
  generalize ℓ (Pi.single 2 1) = l2 at *
  generalize ℓ (Pi.single 3 1) = l3 at *
  generalize a (Pi.single 0 1) = a0 at *
  generalize a (Pi.single 1 1) = a1 at *
  generalize a (Pi.single 2 1) = a2 at *
  generalize a (Pi.single 3 1) = a3 at *
  linear_combination c ^ 2 * (-(a0 * a0) + a1 * a1 + a2 * a2 + a3 * a3) * hnull -
    c ^ 2 * (-(l0 * a0) + l1 * a1 + l2 * a2 + l3 * a3) * horth

/-- The invariant `E · B` of a plane wave vanishes. -/
theorem pseudoscalarInvariant_planeWave (ℓ a : FourCovector) {f : ℝ → ℝ} {x : Spacetime}
    (hf : DifferentiableAt ℝ f (ℓ x)) :
    pseudoscalarInvariant (fieldTensor (planeWave ℓ a f) x) = 0 := by
  rw [pseudoscalarInvariant_vectors, magneticVector_planeWave ℓ a hf]
  simp only [Fin.sum_univ_three, electricVector_planeWave ℓ a hf, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, fin_succ_zero,
    fin_succ_one, fin_succ_two]
  ring

/-- A nonzero covector takes the value one somewhere. -/
theorem exists_apply_eq_one {ℓ : FourCovector} (hℓ : ℓ ≠ 0) : ∃ v, ℓ v = 1 := by
  obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hℓ (ContinuousLinearMap.ext hc)
  exact ⟨(ℓ v)⁻¹ • v, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv]⟩

/-- If `ℓ ∧ c = 0` for a nonzero `ℓ`, then `c` is a multiple of `ℓ`. -/
theorem exists_eq_smul_of_wedge_eq_zero {ℓ c : FourCovector} (hℓ : ℓ ≠ 0)
    (h : ∀ v w, ℓ v * c w - ℓ w * c v = 0) : ∃ t : ℝ, c = t • ℓ := by
  obtain ⟨v₀, hv₀⟩ := exists_apply_eq_one hℓ
  refine ⟨c v₀, ContinuousLinearMap.ext fun w => ?_⟩
  have hw := h v₀ w
  rw [hv₀] at hw
  rw [_root_.smul_apply, smul_eq_mul]
  linarith

/-- The field of a plane wave is not zero where `f′(ℓx) ≠ 0`, if `ℓ ≠ 0` and `a` is not a multiple
of `ℓ`. -/
theorem fieldTensor_planeWave_ne_zero {ℓ a : FourCovector} (hℓ : ℓ ≠ 0)
    (ha : ∀ t : ℝ, a ≠ t • ℓ) {f : ℝ → ℝ} {x : Spacetime} (hf : DifferentiableAt ℝ f (ℓ x))
    (hf' : deriv f (ℓ x) ≠ 0) : fieldTensor (planeWave ℓ a f) x ≠ 0 := by
  intro h
  obtain ⟨t, ht⟩ := exists_eq_smul_of_wedge_eq_zero hℓ fun v w => by
    have hvw := fieldTensor_planeWave ℓ a hf v w
    rw [h] at hvw
    exact (mul_eq_zero.mp hvw.symm).resolve_left hf'
  exact ha t ht

/-! ### Transverse waves -/

/-- The covector `ℓ = κ (dt − ⟨n, dx⟩)` of a wave with the frequency `κ` that travels in the
direction `n`; its phase is `κ (t − ⟨n, x⟩)`. -/
def wavevector (κ : ℝ) (n : Fin 3 → ℝ) : FourCovector :=
  κ • (ContinuousLinearMap.proj 0 - ∑ i : Fin 3, n i • ContinuousLinearMap.proj i.succ)

/-- `ℓ(v) = κ (v⁰ − ⟨n, 𝐯⟩)`. -/
theorem wavevector_apply (κ : ℝ) (n : Fin 3 → ℝ) (v : Spacetime) :
    wavevector κ n v = κ * (v 0 - ∑ i : Fin 3, n i * v i.succ) := by
  simp [wavevector]

/-- The time component `ℓ₀ = κ`. -/
theorem wavevector_single_zero (κ : ℝ) (n : Fin 3 → ℝ) :
    wavevector κ n (Pi.single 0 1) = κ := by
  simp [wavevector_apply]

/-- The space components `ℓᵢ = −κ nᵢ`. -/
theorem wavevector_single_succ (κ : ℝ) (n : Fin 3 → ℝ) (i : Fin 3) :
    wavevector κ n (Pi.single i.succ 1) = -(κ * n i) := by
  rw [wavevector_apply]
  fin_cases i <;> simp [Fin.sum_univ_three, Pi.single_apply]

/-- For a unit vector `n` the covector `κ (dt − ⟨n, dx⟩)` is null. -/
theorem covectorInner_wavevector_self (κ : ℝ) {n : Fin 3 → ℝ} (hn : ∑ i, n i ^ 2 = 1) :
    covectorInner (wavevector κ n) (wavevector κ n) = 0 := by
  rw [covectorInner_apply, wavevector_single_zero]
  simp only [← fin_succ_zero, ← fin_succ_one, ← fin_succ_two, wavevector_single_succ]
  rw [Fin.sum_univ_three] at hn
  linear_combination κ ^ 2 * hn

/-- The algebra of a transverse field: if `E · n = 0` and `B = n × E` for a unit vector `n`, then
`|B| = |E|`, the energy density is `|E|²`, the vector of Poynting is `|E|² n` and the stress of
Maxwell is `|E|² nᵢ nⱼ`. -/
theorem transverse_stress (F : Field) (x : Spacetime) {n : Fin 3 → ℝ}
    (hn : ∑ i, n i ^ 2 = 1) (hE : ∑ i, electricVector (F x) i * n i = 0)
    (hB : magneticVector (F x) = n ⨯₃ electricVector (F x)) :
    ∑ i, magneticVector (F x) i ^ 2 = ∑ i, electricVector (F x) i ^ 2 ∧
      energyDensity F x = ∑ i, electricVector (F x) i ^ 2 ∧
      (∀ i, poyntingVector F i x = (∑ j, electricVector (F x) j ^ 2) * n i) ∧
      ∀ i j, maxwellStress F i j x = (∑ l, electricVector (F x) l ^ 2) * (n i * n j) := by
  have hb : ∀ i, magneticVector (F x) i = (n ⨯₃ electricVector (F x)) i := fun i =>
    congrFun hB i
  have hb0 := hb 0
  have hb1 := hb 1
  have hb2 := hb 2
  simp [cross_apply] at hb0 hb1 hb2
  simp only [Fin.sum_univ_three] at hn hE ⊢
  refine ⟨?_, ?_, fun i => ?_, fun i j => ?_⟩
  · rw [hb0, hb1, hb2]
    linear_combination (electricVector (F x) 0 ^ 2 + electricVector (F x) 1 ^ 2 +
      electricVector (F x) 2 ^ 2) * hn - (electricVector (F x) 0 * n 0 +
        electricVector (F x) 1 * n 1 + electricVector (F x) 2 * n 2) * hE
  · simp only [energyDensity, electricField, magneticField]
    rw [hb0, hb1, hb2]
    linear_combination (1 / 2 : ℝ) * (electricVector (F x) 0 ^ 2 + electricVector (F x) 1 ^ 2 +
      electricVector (F x) 2 ^ 2) * hn - (1 / 2 : ℝ) * (electricVector (F x) 0 * n 0 +
        electricVector (F x) 1 * n 1 + electricVector (F x) 2 * n 2) * hE
  · fin_cases i <;> simp [poyntingVector, electricField, magneticField, hb0, hb1, hb2] <;>
      generalize electricVector (F x) 0 = E₀ at hE ⊢ <;>
      generalize electricVector (F x) 1 = E₁ at hE ⊢ <;>
      generalize electricVector (F x) 2 = E₂ at hE ⊢
    · linear_combination (-E₀) * hE
    · linear_combination (-E₁) * hE
    · linear_combination (-E₂) * hE
  · fin_cases i <;> fin_cases j <;>
      simp [maxwellStress, energyDensity, electricField, magneticField, hb0, hb1, hb2] <;>
      generalize electricVector (F x) 0 = E₀ at hE ⊢ <;>
      generalize electricVector (F x) 1 = E₁ at hE ⊢ <;>
      generalize electricVector (F x) 2 = E₂ at hE ⊢
    · linear_combination (E₀ * E₀ - (E₀ ^ 2 + E₁ ^ 2 + E₂ ^ 2) / 2) * hn +
        ((E₀ * n 0 + E₁ * n 1 + E₂ * n 2) / 2 - 2 * n 0 * E₀) * hE
    · linear_combination (E₀ * E₁) * hn - (n 0 * E₁ + E₀ * n 1) * hE
    · linear_combination (E₀ * E₂) * hn - (n 0 * E₂ + E₀ * n 2) * hE
    · linear_combination (E₁ * E₀) * hn - (n 1 * E₀ + E₁ * n 0) * hE
    · linear_combination (E₁ * E₁ - (E₀ ^ 2 + E₁ ^ 2 + E₂ ^ 2) / 2) * hn +
        ((E₀ * n 0 + E₁ * n 1 + E₂ * n 2) / 2 - 2 * n 1 * E₁) * hE
    · linear_combination (E₁ * E₂) * hn - (n 1 * E₂ + E₁ * n 2) * hE
    · linear_combination (E₂ * E₀) * hn - (n 2 * E₀ + E₂ * n 0) * hE
    · linear_combination (E₂ * E₁) * hn - (n 2 * E₁ + E₂ * n 1) * hE
    · linear_combination (E₂ * E₂ - (E₀ ^ 2 + E₁ ^ 2 + E₂ ^ 2) / 2) * hn +
        ((E₀ * n 0 + E₁ * n 1 + E₂ * n 2) / 2 - 2 * n 2 * E₂) * hE

/-- The component `ℓ₁ = −κ n₁`. -/
theorem wavevector_single_one (κ : ℝ) (n : Fin 3 → ℝ) :
    wavevector κ n (Pi.single 1 1) = -(κ * n 0) :=
  wavevector_single_succ κ n 0

/-- The component `ℓ₂ = −κ n₂`. -/
theorem wavevector_single_two (κ : ℝ) (n : Fin 3 → ℝ) :
    wavevector κ n (Pi.single 2 1) = -(κ * n 1) :=
  wavevector_single_succ κ n 1

/-- The component `ℓ₃ = −κ n₃`. -/
theorem wavevector_single_three (κ : ℝ) (n : Fin 3 → ℝ) :
    wavevector κ n (Pi.single 3 1) = -(κ * n 2) :=
  wavevector_single_succ κ n 2

/-- A transverse plane wave: for `ℓ = κ (dt − ⟨n, dx⟩)` with `κ ≠ 0`, a unit vector `n` and
`⟨ℓ, a⟩ = 0`, the field has `E · n = 0`, `B = n × E`, `|B| = |E|`, the energy density `|E|²`, the
vector of Poynting `|E|² n` and the stress `T^{μν} = |E|² ℓ^μ ℓ^ν / κ²`. -/
theorem transverse_planeWave {κ : ℝ} (hκ : κ ≠ 0) {n : Fin 3 → ℝ} (hn : ∑ i, n i ^ 2 = 1)
    {a : FourCovector} (horth : covectorInner (wavevector κ n) a = 0) {f : ℝ → ℝ}
    {x : Spacetime} (hf : DifferentiableAt ℝ f (wavevector κ n x)) :
    let F := fieldTensor (planeWave (wavevector κ n) a f)
    ∑ i, electricVector (F x) i * n i = 0 ∧
      magneticVector (F x) = n ⨯₃ electricVector (F x) ∧
      ∑ i, magneticVector (F x) i ^ 2 = ∑ i, electricVector (F x) i ^ 2 ∧
      energyDensity F x = ∑ i, electricVector (F x) i ^ 2 ∧
      (∀ i, poyntingVector F i x = (∑ j, electricVector (F x) j ^ 2) * n i) ∧
      ∀ μ ν, raisedStress F μ ν x = (∑ j, electricVector (F x) j ^ 2) *
        (sharp .timeNegative (wavevector κ n) μ * sharp .timeNegative (wavevector κ n) ν) /
          κ ^ 2 := by
  intro F
  have hE : ∑ i, electricVector (F x) i * n i = 0 := by
    simp only [F, Fin.sum_univ_three, electricVector_planeWave _ a hf, wavevector_single_zero,
      wavevector_single_succ, fin_succ_zero, fin_succ_one, fin_succ_two]
    rw [covectorInner_apply, wavevector_single_zero, wavevector_single_one,
      wavevector_single_two, wavevector_single_three] at horth
    rw [Fin.sum_univ_three] at hn
    linear_combination (-(deriv f (wavevector κ n x) * κ * a (Pi.single 0 1))) * hn +
      deriv f (wavevector κ n x) * horth
  have hB : magneticVector (F x) = n ⨯₃ electricVector (F x) := by
    ext i
    fin_cases i <;>
      simp [F, magneticVector_planeWave _ a hf, electricVector_planeWave _ a hf, cross_apply,
        wavevector_single_zero, wavevector_single_one, wavevector_single_two,
        wavevector_single_three] <;> ring
  obtain ⟨h1, h2, h3, h4⟩ := transverse_stress F x hn hE hB
  have hs0 : sharp .timeNegative (wavevector κ n) 0 = -κ := by
    rw [sharp_apply, wavevector_single_zero, lorentzSign_zero]
    ring
  have hs : ∀ i : Fin 3, sharp .timeNegative (wavevector κ n) i.succ = -(κ * n i) := fun i => by
    rw [sharp_apply, wavevector_single_succ, lorentzSign_succ, one_mul]
  have hκ2 : κ ^ 2 ≠ 0 := pow_ne_zero 2 hκ
  refine ⟨hE, hB, h1, h2, h3, fun μ ν => ?_⟩
  refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν
  · rw [raisedStress_zero_zero, h2, hs0]
    field_simp
  · rw [raisedStress_zero_succ, h3, hs0, hs]
    field_simp
  · rw [raisedStress_succ_zero, h3, hs0, hs]
    field_simp
  · rw [raisedStress_succ_succ, h4, hs, hs]
    field_simp

/-- A function with a vanishing derivative everywhere is constant. -/
theorem const_of_hasDerivAt_zero {g g' : ℝ → ℝ} (hg : ∀ s, HasDerivAt g (g' s) s)
    (hz : ∀ s, g' s = 0) (s t : ℝ) : g s = g t :=
  is_const_of_deriv_eq_zero (fun r => (hg r).differentiableAt)
    (fun r => (hg r).deriv.trans (hz r)) s t

/-- A field in the vacuum that depends only on `t − ⟨n, x⟩` has constant components `E · n` and
`B · n`, and `B − n × E` is constant: the part of the field that varies is transverse, with
`B = n × E` up to a constant. -/
theorem transverse_of_vacuum {n : Fin 3 → ℝ} {F : Field} {G : ℝ → TwoForm}
    (hG : Differentiable ℝ G) (hF : F = fun y => G (wavevector 1 n y))
    (hgE : ∀ y, divergence3 (electricField F) y = 0)
    (hgB : ∀ y, divergence3 (magneticField F) y = 0)
    (hfar : ∀ y i, partialAt (magneticField F i) 0 y + curl (electricField F) y i = 0)
    (y z : Spacetime) :
    ∑ i, electricVector (F y) i * n i = ∑ i, electricVector (F z) i * n i ∧
      ∑ i, magneticVector (F y) i * n i = ∑ i, magneticVector (F z) i * n i ∧
      magneticVector (F y) - n ⨯₃ electricVector (F y) =
        magneticVector (F z) - n ⨯₃ electricVector (F z) := by
  subst hF
  have hc : ∀ (a b : Fin 4), Differentiable ℝ (fun s => component (G s) a b) := fun a b s =>
    (ContinuousAlternatingMap.apply ℝ Spacetime ℝ
      ![Pi.single a 1, Pi.single b 1]).differentiableAt.comp s (hG s)
  -- the profiles of the components
  let e : Fin 3 → ℝ → ℝ := fun i s => electricVector (G s) i
  let b : Fin 3 → ℝ → ℝ := fun i s => magneticVector (G s) i
  have he : ∀ i, Differentiable ℝ (e i) := fun i => by
    have h : e i = fun s => component (G s) i.succ 0 :=
      funext fun s => electricVector_apply (G s) i
    rw [h]
    exact hc _ _
  have hb : ∀ i, Differentiable ℝ (b i) := fun i => by
    fin_cases i
    · exact hc 2 3
    · exact hc 3 1
    · exact hc 1 2
  have hpe : ∀ i μ w, partialAt (electricField (fun y => G (wavevector 1 n y)) i) μ w =
      deriv (e i) (wavevector 1 n w) * wavevector 1 n (Pi.single μ 1) := fun i μ w =>
    partialAt_comp_covector (wavevector 1 n) (f := e i) (he i _) μ
  have hpb : ∀ i μ w, partialAt (magneticField (fun y => G (wavevector 1 n y)) i) μ w =
      deriv (b i) (wavevector 1 n w) * wavevector 1 n (Pi.single μ 1) := fun i μ w =>
    partialAt_comp_covector (wavevector 1 n) (f := b i) (hb i _) μ
  have hφ : ∀ s, wavevector 1 n (Pi.single 0 s) = s := fun s => by
    simp [wavevector_apply]
  -- the equations on the profiles
  have k1 : ∀ s, deriv (e 0) s * n 0 + deriv (e 1) s * n 1 + deriv (e 2) s * n 2 = 0 :=
    fun s => by
      have h := hgE (Pi.single 0 s)
      simp only [divergence3, hpe, Fin.sum_univ_three, hφ, wavevector_single_succ] at h
      linarith
  have k2 : ∀ s, deriv (b 0) s * n 0 + deriv (b 1) s * n 1 + deriv (b 2) s * n 2 = 0 :=
    fun s => by
      have h := hgB (Pi.single 0 s)
      simp only [divergence3, hpb, Fin.sum_univ_three, hφ, wavevector_single_succ] at h
      linarith
  have k3 : ∀ s i, deriv (b i) s - (n ⨯₃ fun j => deriv (e j) s) i = 0 := fun s i => by
    have h := hfar (Pi.single 0 s) i
    fin_cases i <;>
      simp [curl, hpe, hpb, hφ, wavevector_single_one, wavevector_single_two,
        wavevector_single_three, cross_apply] at h ⊢ <;>
      linarith
  refine ⟨?_, ?_, ?_⟩
  · simp only [Fin.sum_univ_three]
    exact const_of_hasDerivAt_zero (fun s =>
      ((((he 0 s).hasDerivAt.mul_const (n 0)).add ((he 1 s).hasDerivAt.mul_const (n 1))).add
        ((he 2 s).hasDerivAt.mul_const (n 2)))) k1 _ _
  · simp only [Fin.sum_univ_three]
    exact const_of_hasDerivAt_zero (fun s =>
      ((((hb 0 s).hasDerivAt.mul_const (n 0)).add ((hb 1 s).hasDerivAt.mul_const (n 1))).add
        ((hb 2 s).hasDerivAt.mul_const (n 2)))) k2 _ _
  · ext i
    have k := fun s => k3 s i
    fin_cases i <;> simp [cross_apply] at k ⊢
    · exact const_of_hasDerivAt_zero (fun s => (hb 0 s).hasDerivAt.sub
        (((he 2 s).hasDerivAt.const_mul (n 1)).sub ((he 1 s).hasDerivAt.const_mul (n 2))))
        (fun s => by linarith [k s]) _ _
    · exact const_of_hasDerivAt_zero (fun s => (hb 1 s).hasDerivAt.sub
        (((he 0 s).hasDerivAt.const_mul (n 2)).sub ((he 2 s).hasDerivAt.const_mul (n 0))))
        (fun s => by linarith [k s]) _ _
    · exact const_of_hasDerivAt_zero (fun s => (hb 2 s).hasDerivAt.sub
        (((he 1 s).hasDerivAt.const_mul (n 0)).sub ((he 0 s).hasDerivAt.const_mul (n 1))))
        (fun s => by linarith [k s]) _ _

end ProjectAinos.Electrodynamics
