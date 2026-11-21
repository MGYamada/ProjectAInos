/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.WaveEquation
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Characteristic vibrations of the field

The field in a finite volume as a sum of characteristic vibrations (Landau–Lifshitz, *The
Classical Theory of Fields*, §52). The potential is in the gauge of Coulomb, `φ = 0` and
`div 𝐚 = 0`, so that `E = −∂ₜ𝐚` and `B = curl 𝐚`. Two cavities are treated.

**The perfectly conducting rectangular cavity** `[0, L₁] × [0, L₂] × [0, L₃]`, by explicit modes.

* `conductingMode L n c Ω` is the potential `φ = 0`,
  `aᵢ = cᵢ cos(Ωt) cos(πnᵢxᵢ/Lᵢ) ∏_{j ≠ i} sin(πnⱼxⱼ/Lⱼ)` with the mode numbers `n ∈ ℕ³`, built
  from the separable products `trigProduct` (`box_trigProduct`: `box f = (k₀² − Σᵢ kᵢ²) f`).
* `conductingMode_maxwell`: for `Σᵢ (πnᵢ/Lᵢ) cᵢ = 0` and `Ω² = Σᵢ (πnᵢ/Lᵢ)²` the potential is in
  the gauge of Coulomb, the field satisfies the equations of Maxwell in the vacuum
  (`VacuumMaxwellAt`) everywhere, and on the walls `xᵢ ∈ {0, Lᵢ}` the tangential components `Eⱼ`,
  `j ≠ i`, and the normal component `Bᵢ` vanish; `conductingMode_boundary_cross` states this as
  `n × E = 0` and `n · B = 0`. `box_modeComponent`: `box aᵢ = (Ω² − Σⱼ (πnⱼ/Lⱼ)²) aᵢ`, so the
  relation of dispersion is necessary for a mode that is not zero. `conductingMode_unitCube`: the
  mode `(1, 1, 0)` of the unit cube satisfies the hypotheses and is not zero.

**The periodic box** with the sides `L₁, L₂, L₃`, the setting of Landau–Lifshitz. A function on
the space `Fin 3 → ℝ` is periodic (`BoxPeriodic L f`) if `f(x + Σᵢ mᵢLᵢeᵢ) = f(x)` for all
integers `mᵢ`; a function `u` on space-time is periodic in space if every slice
`slice u t = u(t, ·)` is. The coefficients are integrals over the box `boxSet L = ∏ᵢ (0, Lᵢ]`,
and the unit torus `UnitAddTorus (Fin 3)` with its Haar probability measure enters only through
the rescaling `toTorus L : x ↦ (xᵢ/Lᵢ mod 1)ᵢ`.

* `boxCoeff L f k = (1/V) ∫_box e^{−2πi Σⱼ kⱼxⱼ/Lⱼ} f(x) dx` for `k ∈ ℤ³` and `V = L₁L₂L₃`
  (`boxVolume`). `integral_boxSet_toTorus`: `∫_box G(x/L) dx = V ∫_torus G`, the measure-preserving
  rescaling of the box to the unit torus, and `boxCoeff_eq_mFourierCoeff`.
* `boxCoeff_comp_add`: `(f(· + v))_k = e^{2πi Σⱼ kⱼvⱼ/Lⱼ} f_k` for a periodic `f`, and
  `boxCoeff_partial`: `(∂ⱼf)_k = i Kⱼ f_k` with the wave vector `Kⱼ = 2πkⱼ/Lⱼ`
  (`boxWavevector`) for a periodic `C¹` function: the boundary terms cancel by periodicity.
* `hasDerivAt_boxCoeff_of_box`: for a periodic `C²` solution of `box u = 0`, `ü_k = −ω_k² u_k`
  with `ω_k = |K| = 2π ‖(kⱼ/Lⱼ)ⱼ‖` (`boxFreq`); `transverse_boxCoeff`: `div 𝐚 = 0` gives
  `K · 𝐚_k = 0`; `hasDerivAt_boxCoeff_of_maxwell` combines both for a potential in the gauge of
  Coulomb whose field satisfies the equations of Maxwell in the vacuum.
* `hasSum_sq_boxCoeff`: the identity of Parseval `Σ_k |f_k|² = (1/V) ∫_box f²`, from
  `UnitAddTorus.hasSum_sq_mFourierCoeff`.
* `hasSum_fieldEnergy`, `fieldEnergy_eq_tsum`: `∫_box ½(E² + B²) = V Σ_k ½ (|ȧ_k|² + ω_k² |a_k|²)`.
* `boxPeriodic_modeComponent`, `hasSum_fieldEnergy_conductingMode`: a mode of the conducting box
  is a field on the doubled periodic box with the sides `2Lᵢ`.

The energy density is `½(E² + B²)` of `energyDensity`, in the units of Heaviside and Lorentz with
`c = 1`; Landau–Lifshitz write `(E² + H²)/8π`. The completeness of the modes of the conducting
box, by the even and odd reflection of a field to the doubled periodic box, is not proved here;
the module `CylindricalCavity` treats the axisymmetric modes of a conducting cylinder.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace ProjectAinos.Electrodynamics.CavityModes

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity
open ProjectAinos.Electrodynamics

/- The unit torus carries the Haar probability measure of `Mathlib.Analysis.Fourier.AddCircleMulti`,
the measure of its Fourier coefficients and of the identity of Parseval. -/
attribute [local instance] instMeasureSpaceUnitAddCircle

/-- The Haar measure on `ℝ / ℤ` is a probability measure. -/
local instance : IsProbabilityMeasure (MeasureTheory.volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The Haar probability measure on `ℝ / ℤ` is invariant under the translations. -/
local instance : Measure.IsAddRightInvariant (MeasureTheory.volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddRightInvariant AddCircle.haarAddCircle)

/-! ### Separable trigonometric products on space-time -/

/-- The factor `a cos(k t) + b sin(k t)`. -/
def trigFactor (k a b t : ℝ) : ℝ := a * Real.cos (k * t) + b * Real.sin (k * t)

/-- The derivative of `a cos(k t) + b sin(k t)` is `(k b) cos(k t) − (k a) sin(k t)`. -/
theorem hasDerivAt_trigFactor (k a b t : ℝ) :
    HasDerivAt (trigFactor k a b) (trigFactor k (k * b) (-(k * a)) t) t := by
  have h := ((((hasDerivAt_id t).const_mul k).cos).const_mul a).add
    ((((hasDerivAt_id t).const_mul k).sin).const_mul b)
  convert h using 1
  · funext s
    simp [trigFactor]
  · simp only [trigFactor, id]
    ring

/-- The separable product `∏_μ (a_μ cos(k_μ x^μ) + b_μ sin(k_μ x^μ))` on space-time. -/
def trigProduct (k a b : Fin 4 → ℝ) (y : Spacetime) : ℝ :=
  ∏ ν, trigFactor (k ν) (a ν) (b ν) (y ν)

/-- The derivative along `x^μ` of a separable product differentiates the factor `μ`. -/
theorem partialAt_trigProduct (k a b : Fin 4 → ℝ) (μ : Fin 4) :
    partialAt (trigProduct k a b) μ =
      trigProduct k (Function.update a μ (k μ * b μ))
        (Function.update b μ (-(k μ * a μ))) := by
  funext y
  have hg : ∀ ν ∈ (Finset.univ : Finset (Fin 4)),
      HasFDerivAt (fun y : Spacetime => trigFactor (k ν) (a ν) (b ν) (y ν))
        (trigFactor (k ν) (k ν * b ν) (-(k ν * a ν)) (y ν) •
          (ContinuousLinearMap.proj ν : Spacetime →L[ℝ] ℝ)) y :=
    fun ν _ => (hasDerivAt_trigFactor _ _ _ _).comp_hasFDerivAt y
      (ContinuousLinearMap.proj ν : Spacetime →L[ℝ] ℝ).hasFDerivAt
  have hd := HasFDerivAt.finsetProd hg
  rw [partialAt, show trigProduct k a b = fun y : Spacetime =>
    ∏ ν ∈ Finset.univ, trigFactor (k ν) (a ν) (b ν) (y ν) from rfl, hd.fderiv]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [trigProduct, ← Finset.mul_prod_erase _ _ (Finset.mem_univ μ)]
  simp only [Function.update_self]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun ν hν => ?_
  have hne := Finset.ne_of_mem_erase hν
  simp only [Function.update_of_ne hne]

/-- Scaling the factor `μ` of a separable product scales the product. -/
theorem trigProduct_update_smul (k a b : Fin 4 → ℝ) (μ : Fin 4) (c : ℝ) (y : Spacetime) :
    trigProduct k (Function.update a μ (c * a μ)) (Function.update b μ (c * b μ)) y =
      c * trigProduct k a b y := by
  rw [trigProduct, trigProduct, ← Finset.mul_prod_erase _ _ (Finset.mem_univ μ),
    ← Finset.mul_prod_erase _ (fun ν => trigFactor (k ν) (a ν) (b ν) (y ν))
      (Finset.mem_univ μ)]
  simp only [Function.update_self]
  rw [← mul_assoc]
  congr 1
  · simp only [trigFactor]
    ring
  · refine Finset.prod_congr rfl fun ν hν => ?_
    have hne := Finset.ne_of_mem_erase hν
    simp only [Function.update_of_ne hne]

/-- The second derivative along `x^μ` of a separable product is `−k_μ²` times the product. -/
theorem partialAt_partialAt_trigProduct (k a b : Fin 4 → ℝ) (μ : Fin 4) :
    partialAt (partialAt (trigProduct k a b) μ) μ = fun y => -k μ ^ 2 * trigProduct k a b y := by
  funext y
  rw [partialAt_trigProduct, partialAt_trigProduct]
  simp only [Function.update_self, Function.update_idem]
  have ha : k μ * -(k μ * a μ) = -k μ ^ 2 * a μ := by ring
  have hb : -(k μ * (k μ * b μ)) = -k μ ^ 2 * b μ := by ring
  rw [ha, hb, trigProduct_update_smul]

/-- The wave operator on a separable product: `box f = (k₀² − Σᵢ kᵢ²) f`. -/
theorem box_trigProduct (k a b : Fin 4 → ℝ) (y : Spacetime) :
    box (trigProduct k a b) y = (k 0 ^ 2 - ∑ i : Fin 3, k i.succ ^ 2) * trigProduct k a b y := by
  simp only [box, partialAt_partialAt_trigProduct, Fin.sum_univ_three]
  ring

/-- A separable product is smooth. -/
theorem contDiff_trigProduct {n : ℕ∞ω} (k a b : Fin 4 → ℝ) : ContDiff ℝ n (trigProduct k a b) := by
  unfold trigProduct trigFactor
  fun_prop

/-- A separable product vanishes where one of its factors vanishes. -/
theorem trigProduct_eq_zero {k a b : Fin 4 → ℝ} {y : Spacetime} {ν : Fin 4}
    (h : trigFactor (k ν) (a ν) (b ν) (y ν) = 0) : trigProduct k a b y = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ ν) h

/-- The derivative along `x^μ` of a separable product vanishes where a factor `ν ≠ μ`
vanishes. -/
theorem partialAt_trigProduct_eq_zero {k a b : Fin 4 → ℝ} {y : Spacetime} {μ ν : Fin 4}
    (hμν : μ ≠ ν) (h : trigFactor (k ν) (a ν) (b ν) (y ν) = 0) :
    partialAt (trigProduct k a b) μ y = 0 := by
  rw [partialAt_trigProduct]
  refine trigProduct_eq_zero (ν := ν) ?_
  rwa [Function.update_of_ne hμν.symm, Function.update_of_ne hμν.symm]

/-! ### The potential with the scalar potential and the vector potential -/

/-- The time component of `A = −φ dt + 𝐚 · d𝐱` is `−φ`. -/
theorem potentialComponent_potentialOf_zero (φ : Spacetime → ℝ) (a : Spacetime → Fin 3 → ℝ) :
    potentialComponent (potentialOf φ a) 0 = fun y => -φ y := by
  funext y
  rw [potentialComponent, potentialOf_apply]
  simp

/-- The spatial components of `A = −φ dt + 𝐚 · d𝐱` are the components of `𝐚`. -/
theorem potentialComponent_potentialOf_succ (φ : Spacetime → ℝ) (a : Spacetime → Fin 3 → ℝ)
    (j : Fin 3) : potentialComponent (potentialOf φ a) j.succ = fun y => a y j := by
  funext y
  rw [potentialComponent, potentialOf_apply]
  simp [Pi.single_apply]

/-- The potential `−φ dt + 𝐚 · d𝐱` of a `Cⁿ` scalar potential and `Cⁿ` components of `𝐚` is
`Cⁿ`. -/
theorem contDiff_potentialOf {n : ℕ∞ω} {φ : Spacetime → ℝ} {a : Spacetime → Fin 3 → ℝ}
    (hφ : ContDiff ℝ n φ) (ha : ∀ i, ContDiff ℝ n fun y => a y i) :
    ContDiff ℝ n (potentialOf φ a) := by
  unfold potentialOf
  refine oneCovector.symm.contDiff.comp ?_
  exact (hφ.neg.smul contDiff_const).add (ContDiff.sum fun i _ => (ha i).smul contDiff_const)

/-! ### The modes of a perfectly conducting rectangular cavity -/

/-- The entry `2` of `Fin.cons x p` on `Fin 4` is `p 1`. -/
@[simp] theorem fin4_cons_two {α : Type*} (x : α) (p : Fin 3 → α) :
    (Fin.cons x p : Fin 4 → α) 2 = p 1 := rfl

/-- The entry `3` of `Fin.cons x p` on `Fin 4` is `p 2`. -/
@[simp] theorem fin4_cons_three {α : Type*} (x : α) (p : Fin 3 → α) :
    (Fin.cons x p : Fin 4 → α) 3 = p 2 := rfl

/-- The wave numbers `π nᵢ / Lᵢ` of a mode of the box `[0, L₁] × [0, L₂] × [0, L₃]`. -/
def wallWavenumber (L : Fin 3 → ℝ) (n : Fin 3 → ℕ) (i : Fin 3) : ℝ := Real.pi * n i / L i

/-- The wave numbers `(Ω, πn₁/L₁, πn₂/L₂, πn₃/L₃)` of a mode of the frequency `Ω`. -/
def modeWavenumbers (L : Fin 3 → ℝ) (n : Fin 3 → ℕ) (freq : ℝ) : Fin 4 → ℝ :=
  Fin.cons freq (wallWavenumber L n)

/-- The coefficients of the cosines of the component `i`: the amplitude `c` in time, `1` in the
direction `i` and `0` in the other directions. -/
def modeCosCoeff (c : ℝ) (i : Fin 3) : Fin 4 → ℝ := Fin.cons c fun j => if j = i then 1 else 0

/-- The coefficients of the sines of the component `i`: `0` in time and in the direction `i`, and
`1` in the other directions. -/
def modeSinCoeff (i : Fin 3) : Fin 4 → ℝ := Fin.cons 0 fun j => if j = i then 0 else 1

/-- The component `aᵢ = cᵢ cos(Ωt) cos(πnᵢxᵢ/Lᵢ) ∏_{j ≠ i} sin(πnⱼxⱼ/Lⱼ)` of the vector potential
of a mode of the conducting box. -/
def modeComponent (L : Fin 3 → ℝ) (n : Fin 3 → ℕ) (c : Fin 3 → ℝ) (freq : ℝ) (i : Fin 3) :
    Spacetime → ℝ :=
  trigProduct (modeWavenumbers L n freq) (modeCosCoeff (c i) i) (modeSinCoeff i)

/-- The potential `φ = 0`, `𝐚 = (a₁, a₂, a₃)` of a mode of the conducting box, with the mode
numbers `n`, the amplitude `c` and the frequency `Ω`. -/
def conductingMode (L : Fin 3 → ℝ) (n : Fin 3 → ℕ) (c : Fin 3 → ℝ) (freq : ℝ) : Potential :=
  potentialOf 0 fun y i => modeComponent L n c freq i y

/-- The time component of the potential of a mode is zero: `φ = 0`. -/
theorem potentialComponent_conductingMode_zero (L : Fin 3 → ℝ) (n : Fin 3 → ℕ) (c : Fin 3 → ℝ)
    (freq : ℝ) : potentialComponent (conductingMode L n c freq) 0 = fun _ => 0 := by
  rw [conductingMode, potentialComponent_potentialOf_zero]
  simp

/-- The spatial components of the potential of a mode. -/
theorem potentialComponent_conductingMode_succ (L : Fin 3 → ℝ) (n : Fin 3 → ℕ) (c : Fin 3 → ℝ)
    (freq : ℝ) (j : Fin 3) :
    potentialComponent (conductingMode L n c freq) j.succ = modeComponent L n c freq j := by
  rw [conductingMode, potentialComponent_potentialOf_succ]

/-- The potential of a mode is smooth. -/
theorem contDiff_conductingMode {m : ℕ∞ω} (L : Fin 3 → ℝ) (n : Fin 3 → ℕ) (c : Fin 3 → ℝ)
    (freq : ℝ) : ContDiff ℝ m (conductingMode L n c freq) :=
  contDiff_potentialOf contDiff_const fun _ => contDiff_trigProduct _ _ _

/-- The wave operator on a component of a mode: `box aᵢ = (Ω² − Σⱼ (πnⱼ/Lⱼ)²) aᵢ`. -/
theorem box_modeComponent (L : Fin 3 → ℝ) (n : Fin 3 → ℕ) (c : Fin 3 → ℝ) (freq : ℝ)
    (i : Fin 3) (y : Spacetime) :
    box (modeComponent L n c freq i) y =
      (freq ^ 2 - ∑ j : Fin 3, wallWavenumber L n j ^ 2) * modeComponent L n c freq i y := by
  rw [modeComponent, box_trigProduct]
  simp [modeWavenumbers]

/-- The divergence `∂^μ A_μ = div 𝐚` of the potential of a mode:
`−(Σⱼ (πnⱼ/Lⱼ) cⱼ) cos(Ωt) ∏ⱼ sin(πnⱼxⱼ/Lⱼ)`. -/
theorem lorenzDivergence_conductingMode (L : Fin 3 → ℝ) (n : Fin 3 → ℕ) (c : Fin 3 → ℝ)
    (freq : ℝ) (y : Spacetime) :
    lorenzDivergence (conductingMode L n c freq) y =
      -(∑ j : Fin 3, wallWavenumber L n j * c j) * (Real.cos (freq * y 0) *
        Real.sin (wallWavenumber L n 0 * y 1) * Real.sin (wallWavenumber L n 1 * y 2) *
        Real.sin (wallWavenumber L n 2 * y 3)) := by
  simp only [lorenzDivergence, potentialComponent_conductingMode_zero, partialAt_const,
    potentialComponent_conductingMode_succ, modeComponent, partialAt_trigProduct]
  simp [trigProduct, Fin.prod_univ_four, Fin.sum_univ_three, trigFactor, modeWavenumbers,
    modeCosCoeff, modeSinCoeff, Function.update_apply]
  ring

/-- On the walls `xᵢ = 0` and `xᵢ = Lᵢ`, the derivatives of a component `aⱼ`, `j ≠ i`, along the
directions other than `xᵢ` vanish, because `aⱼ` has the factor `sin(πnᵢxᵢ/Lᵢ)`. -/
theorem partialAt_modeComponent_wall {L : Fin 3 → ℝ} {i j : Fin 3} (hL : L i ≠ 0)
    (n : Fin 3 → ℕ) (c : Fin 3 → ℝ) (freq : ℝ) (hij : j ≠ i) {μ : Fin 4} (hμ : μ ≠ i.succ)
    {y : Spacetime} (hy : y i.succ = 0 ∨ y i.succ = L i) :
    partialAt (modeComponent L n c freq j) μ y = 0 := by
  refine partialAt_trigProduct_eq_zero hμ ?_
  simp only [modeWavenumbers, modeCosCoeff, modeSinCoeff, Fin.cons_succ, trigFactor,
    hij.symm, ↓reduceIte, zero_mul, one_mul, zero_add]
  rcases hy with h | h
  · rw [h, mul_zero, Real.sin_zero]
  · rw [h, wallWavenumber, div_mul_cancel₀ _ hL, mul_comm]
    exact Real.sin_nat_mul_pi (n i)

/-- The electric field of a mode is `E = −∂ₜ𝐚`. -/
theorem electricField_conductingMode (L : Fin 3 → ℝ) (n : Fin 3 → ℕ) (c : Fin 3 → ℝ)
    (freq : ℝ) (j : Fin 3) (y : Spacetime) :
    electricField (fieldTensor (conductingMode L n c freq)) j y =
      -partialAt (modeComponent L n c freq j) 0 y := by
  have hd : DifferentiableAt ℝ (conductingMode L n c freq) y :=
    (contDiff_conductingMode (m := 1) L n c freq).differentiable one_ne_zero y
  change electricVector _ j = _
  rw [electricVector_apply, fieldTensor_component hd, potentialComponent_conductingMode_zero,
    potentialComponent_conductingMode_succ, fderiv_const_apply]
  simp [partialAt]

/-- The magnetic field of a mode is `B = curl 𝐚`. -/
theorem magneticField_conductingMode (L : Fin 3 → ℝ) (n : Fin 3 → ℕ) (c : Fin 3 → ℝ)
    (freq : ℝ) (y : Spacetime) :
    magneticField (fieldTensor (conductingMode L n c freq)) 0 y =
        partialAt (modeComponent L n c freq 2) 2 y -
          partialAt (modeComponent L n c freq 1) 3 y ∧
      magneticField (fieldTensor (conductingMode L n c freq)) 1 y =
        partialAt (modeComponent L n c freq 0) 3 y -
          partialAt (modeComponent L n c freq 2) 1 y ∧
      magneticField (fieldTensor (conductingMode L n c freq)) 2 y =
        partialAt (modeComponent L n c freq 1) 1 y -
          partialAt (modeComponent L n c freq 0) 2 y := by
  have hd : DifferentiableAt ℝ (conductingMode L n c freq) y :=
    (contDiff_conductingMode (m := 1) L n c freq).differentiable one_ne_zero y
  have h0 := potentialComponent_conductingMode_succ L n c freq 0
  have h1 := potentialComponent_conductingMode_succ L n c freq 1
  have h2 := potentialComponent_conductingMode_succ L n c freq 2
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at h0 h1
  change potentialComponent _ 3 = _ at h2
  refine ⟨?_, ?_, ?_⟩
  · change component _ 2 3 = _
    rw [fieldTensor_component hd, h1, h2]
    rfl
  · change component _ 3 1 = _
    rw [fieldTensor_component hd, h0, h2]
    rfl
  · change component _ 1 2 = _
    rw [fieldTensor_component hd, h0, h1]
    rfl

/-- **The boundary conditions of a perfect conductor.** On the walls `xᵢ = 0` and `xᵢ = Lᵢ` of
the box, the tangential components `Eⱼ`, `j ≠ i`, of the electric field and the normal component
`Bᵢ` of the magnetic field of a mode vanish. -/
theorem conductingMode_boundary {L : Fin 3 → ℝ} (hL : ∀ i, L i ≠ 0) (n : Fin 3 → ℕ)
    (c : Fin 3 → ℝ) (freq : ℝ) (i : Fin 3) {y : Spacetime}
    (hy : y i.succ = 0 ∨ y i.succ = L i) :
    (∀ j, j ≠ i → electricField (fieldTensor (conductingMode L n c freq)) j y = 0) ∧
      magneticField (fieldTensor (conductingMode L n c freq)) i y = 0 := by
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [electricField_conductingMode,
      partialAt_modeComponent_wall (hL i) n c freq hj (Fin.succ_ne_zero i).symm hy, neg_zero]
  · obtain ⟨hB0, hB1, hB2⟩ := magneticField_conductingMode L n c freq y
    have hw := fun (j : Fin 3) (hj : j ≠ i) (μ : Fin 4) (hμ : μ ≠ i.succ) =>
      partialAt_modeComponent_wall (hL i) n c freq hj hμ hy
    fin_cases i
    · change magneticField _ 0 y = 0
      rw [hB0, hw 2 (by decide) 2 (by decide), hw 1 (by decide) 3 (by decide), sub_zero]
    · change magneticField _ 1 y = 0
      rw [hB1, hw 0 (by decide) 3 (by decide), hw 2 (by decide) 1 (by decide), sub_zero]
    · change magneticField _ 2 y = 0
      rw [hB2, hw 1 (by decide) 1 (by decide), hw 0 (by decide) 2 (by decide), sub_zero]

/-- On the walls `xᵢ = 0` and `xᵢ = Lᵢ` with the normal `n = ±eᵢ`, a mode has `n × E = 0` and
`n · B = 0`. -/
theorem conductingMode_boundary_cross {L : Fin 3 → ℝ} (hL : ∀ i, L i ≠ 0) (n : Fin 3 → ℕ)
    (c : Fin 3 → ℝ) (freq : ℝ) (i : Fin 3) {y : Spacetime}
    (hy : y i.succ = 0 ∨ y i.succ = L i) :
    crossProduct (Pi.single i 1 : Fin 3 → ℝ)
        (fun j => electricField (fieldTensor (conductingMode L n c freq)) j y) = 0 ∧
      dotProduct (Pi.single i 1 : Fin 3 → ℝ)
        (fun j => magneticField (fieldTensor (conductingMode L n c freq)) j y) = 0 := by
  obtain ⟨hE, hB⟩ := conductingMode_boundary hL n c freq i hy
  refine ⟨?_, ?_⟩
  · rw [cross_apply]
    fin_cases i
    · have h1 := hE 1 (by decide)
      have h2 := hE 2 (by decide)
      ext l
      fin_cases l <;> simp [h1, h2]
    · have h0 := hE 0 (by decide)
      have h2 := hE 2 (by decide)
      ext l
      fin_cases l <;> simp [h0, h2]
    · have h0 := hE 0 (by decide)
      have h1 := hE 1 (by decide)
      ext l
      fin_cases l <;> simp [h0, h1]
  · rw [single_dotProduct, one_mul]
    exact hB

/-- The wave operator of the zero function is zero. -/
theorem box_zero (y : Spacetime) : box (fun _ => 0) y = 0 := by
  have h : ∀ μ, partialAt (fun _ : Spacetime => (0 : ℝ)) μ = fun _ => 0 := fun μ =>
    funext (partialAt_const 0 μ)
  simp [box, h]

/-- The four equations of Maxwell in the vacuum at the event `y` for the field of the potential
`A`: `div B = 0`, `∂ₜB + curl E = 0`, `div E = 0` and `curl B − ∂ₜE = 0`. -/
def VacuumMaxwellAt (A : Potential) (y : Spacetime) : Prop :=
  (divergence3 (magneticField (fieldTensor A)) y = 0 ∧
      ∀ i, partialAt (magneticField (fieldTensor A) i) 0 y +
        curl (electricField (fieldTensor A)) y i = 0) ∧
    (divergence3 (electricField (fieldTensor A)) y = 0 ∧
      ∀ i, curl (magneticField (fieldTensor A)) y i -
        partialAt (electricField (fieldTensor A) i) 0 y = 0)

/-- In the gauge of Lorenz the equations of Maxwell in the vacuum hold everywhere if and only if
every component of the potential solves the wave equation `box A_ν = 0`. -/
theorem vacuumMaxwellAt_iff_box {A : Potential} (hA : ContDiff ℝ 2 A)
    (hL : ∀ y, lorenzDivergence A y = 0) :
    (∀ y, VacuumMaxwellAt A y) ↔ ∀ y ν, box (potentialComponent A ν) y = 0 := by
  have h := maxwell_iff_box_of_lorenz isOpen_univ hA.contDiffOn (fun y _ => hL y)
    (fun _ => 0)
  simp only [mem_univ, forall_const, Pi.zero_apply, neg_zero] at h
  constructor
  · intro hv y ν
    have hy := h.mp hv y
    exact Fin.cases hy.1 (fun i => hy.2 i) ν
  · intro hb
    exact h.mpr fun y => ⟨hb y 0, fun i => hb y i.succ⟩

/-- **The modes of a perfectly conducting rectangular cavity** (Landau–Lifshitz, §52, checked by
explicit modes). For `Σᵢ (πnᵢ/Lᵢ) cᵢ = 0` and `Ω² = Σᵢ (πnᵢ/Lᵢ)²`, the potential of the mode is in
the gauge of Coulomb (`φ = 0` and `∂^μ A_μ = div 𝐚 = 0`), its field satisfies the four equations
of Maxwell in the vacuum everywhere, and on the walls `xᵢ ∈ {0, Lᵢ}` the tangential components of
the electric field and the normal component of the magnetic field vanish. -/
theorem conductingMode_maxwell {L : Fin 3 → ℝ} (hL : ∀ i, L i ≠ 0) (n : Fin 3 → ℕ)
    {c : Fin 3 → ℝ} {freq : ℝ} (hc : ∑ i : Fin 3, wallWavenumber L n i * c i = 0)
    (hfreq : freq ^ 2 = ∑ i : Fin 3, wallWavenumber L n i ^ 2) :
    (∀ y, lorenzDivergence (conductingMode L n c freq) y = 0) ∧
    (∀ y, VacuumMaxwellAt (conductingMode L n c freq) y) ∧
    (∀ (i : Fin 3) (y : Spacetime), (y i.succ = 0 ∨ y i.succ = L i) →
      (∀ j, j ≠ i → electricField (fieldTensor (conductingMode L n c freq)) j y = 0) ∧
        magneticField (fieldTensor (conductingMode L n c freq)) i y = 0) := by
  have hLor : ∀ y, lorenzDivergence (conductingMode L n c freq) y = 0 := fun y => by
    rw [lorenzDivergence_conductingMode, hc, neg_zero, zero_mul]
  refine ⟨hLor, ?_, fun i y hy => conductingMode_boundary hL n c freq i hy⟩
  refine (vacuumMaxwellAt_iff_box (contDiff_conductingMode L n c freq) hLor).mpr fun y ν => ?_
  refine Fin.cases ?_ (fun i => ?_) ν
  · rw [potentialComponent_conductingMode_zero, box_zero]
  · rw [potentialComponent_conductingMode_succ, box_modeComponent, hfreq, sub_self, zero_mul]

/-- **The lowest mode `(1, 1, 0)` of the unit cube** satisfies the hypotheses of
`conductingMode_maxwell` with `c = (0, 0, 1)` and `Ω = π√2`, and its potential is not zero:
`a₃ = cos(Ωt) sin(πx₁) sin(πx₂)` is `1` at `t = 0`, `x = (½, ½, 0)`. -/
theorem conductingMode_unitCube :
    ∑ i : Fin 3, wallWavenumber 1 ![1, 1, 0] i * ![0, 0, 1] i = 0 ∧
      (Real.pi * Real.sqrt 2) ^ 2 = ∑ i : Fin 3, wallWavenumber 1 ![1, 1, 0] i ^ 2 ∧
      modeComponent 1 ![1, 1, 0] ![0, 0, 1] (Real.pi * Real.sqrt 2) 2 ![0, 1 / 2, 1 / 2, 0] =
        1 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Fin.sum_univ_three, wallWavenumber]
  · simp [Fin.sum_univ_three, wallWavenumber, mul_pow]
    ring
  · have h : Real.sin (Real.pi * 2⁻¹) = 1 := by
      rw [← div_eq_mul_inv, Real.sin_pi_div_two]
    simp [modeComponent, trigProduct, Fin.prod_univ_four, trigFactor, modeWavenumbers,
      modeCosCoeff, modeSinCoeff, wallWavenumber, h]

/-! ### The periodic box and the unit torus -/

/-- The box `(0, L₁] × (0, L₂] × (0, L₃]`, a fundamental domain of the periods `Lᵢ`. -/
def boxSet (L : Fin 3 → ℝ) : Set (Fin 3 → ℝ) := Set.pi univ fun i => Ioc 0 (L i)

/-- The box is measurable. -/
theorem measurableSet_boxSet (L : Fin 3 → ℝ) : MeasurableSet (boxSet L) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

/-- The volume `V = L₁ L₂ L₃` of the box. -/
def boxVolume (L : Fin 3 → ℝ) : ℝ := ∏ i, L i

/-- The rescaling `x ↦ (xᵢ / Lᵢ mod 1)ᵢ` of the space onto the unit torus. -/
def toTorus (L : Fin 3 → ℝ) (x : Fin 3 → ℝ) : UnitAddTorus (Fin 3) :=
  fun i => ((x i / L i : ℝ) : UnitAddCircle)

/-- The point of the box `(0, L₁] × (0, L₂] × (0, L₃]` over a point of the unit torus. -/
def fromTorus (L : Fin 3 → ℝ) (z : UnitAddTorus (Fin 3)) : Fin 3 → ℝ :=
  fun i => L i * (AddCircle.equivIoc 1 0 (z i) : ℝ)

/-- `f` has the period `Lᵢ` in each co-ordinate: `f(x + Σᵢ mᵢ Lᵢ eᵢ) = f(x)` for all integers
`mᵢ`. -/
def BoxPeriodic {E : Type*} (L : Fin 3 → ℝ) (f : (Fin 3 → ℝ) → E) : Prop :=
  ∀ (x : Fin 3 → ℝ) (m : Fin 3 → ℤ), f (fun i => x i + m i * L i) = f x

/-- The rescaling onto the torus is additive. -/
theorem toTorus_add (L x y : Fin 3 → ℝ) : toTorus L (x + y) = toTorus L x + toTorus L y := by
  funext i
  simp [toTorus, add_div]

/-- The point of the box over a point of the torus lies over it. -/
theorem toTorus_fromTorus {L : Fin 3 → ℝ} (hL : ∀ i, L i ≠ 0) (z : UnitAddTorus (Fin 3)) :
    toTorus L (fromTorus L z) = z := by
  funext i
  simp only [toTorus, fromTorus, mul_div_cancel_left₀ _ (hL i), AddCircle.coe_equivIoc]

/-- A point of the box is the point of the box over its image in the torus. -/
theorem fromTorus_toTorus {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) {x : Fin 3 → ℝ}
    (hx : x ∈ boxSet L) : fromTorus L (toTorus L x) = x := by
  funext i
  have hxi := hx i (mem_univ i)
  have hm : x i / L i ∈ Ioc (0 : ℝ) (0 + 1) := by
    rw [zero_add]
    exact ⟨div_pos hxi.1 (hL i), (div_le_one (hL i)).mpr hxi.2⟩
  simp only [fromTorus, toTorus, AddCircle.equivIoc_coe_of_mem hm]
  field_simp [(hL i).ne']

/-- The point of the box over a point of the torus lies in the closed box. -/
theorem fromTorus_mem_Icc {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) (z : UnitAddTorus (Fin 3)) :
    fromTorus L z ∈ Set.pi univ fun i => Icc 0 (L i) := by
  intro i _
  have h := (AddCircle.equivIoc 1 0 (z i)).2
  have h1 : ((AddCircle.equivIoc 1 0 (z i) : ℝ)) ≤ 1 := by simpa using h.2
  exact ⟨mul_nonneg (hL i).le h.1.le, mul_le_of_le_one_right (hL i).le h1⟩

/-- The point of the box over a point of the torus depends measurably on it. -/
theorem measurable_fromTorus (L : Fin 3 → ℝ) : Measurable (fromTorus L) :=
  measurable_pi_iff.mpr fun i => measurable_const.mul
    (measurable_subtype_coe.comp ((AddCircle.measurableEquivIoc 1 0).measurable.comp
      (measurable_pi_apply i)))

/-- Points of the space with the same image in the torus differ by a period. -/
theorem exists_period_of_toTorus_eq {L : Fin 3 → ℝ} (hL : ∀ i, L i ≠ 0) {x y : Fin 3 → ℝ}
    (h : toTorus L x = toTorus L y) : ∃ m : Fin 3 → ℤ, x = fun i => y i + m i * L i := by
  have hi : ∀ i, ∃ m : ℤ, x i = y i + m * L i := fun i => by
    have h' := congrFun h i
    simp only [toTorus] at h'
    rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff] at h'
    obtain ⟨m, hm⟩ := h'
    refine ⟨m, ?_⟩
    rw [zsmul_eq_mul, mul_one, ← sub_div, eq_div_iff (hL i)] at hm
    linarith
  choose m hm using hi
  exact ⟨m, funext hm⟩

/-- A periodic function takes the same value at points with the same image in the torus. -/
theorem BoxPeriodic.eq_of_toTorus_eq {E : Type*} {L : Fin 3 → ℝ} (hL : ∀ i, L i ≠ 0)
    {f : (Fin 3 → ℝ) → E} (hf : BoxPeriodic L f) {x y : Fin 3 → ℝ}
    (h : toTorus L x = toTorus L y) : f x = f y := by
  obtain ⟨m, rfl⟩ := exists_period_of_toTorus_eq hL h
  exact hf y m

/-- The volume of a box with positive sides is positive. -/
theorem boxVolume_pos {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) : 0 < boxVolume L :=
  Finset.prod_pos fun i _ => hL i

/-- **The rescaling of the box to the unit torus.** The map `x ↦ (xᵢ/Lᵢ)ᵢ` carries the volume
of the box `(0, L₁] × (0, L₂] × (0, L₃]` to `V` times the Haar probability measure of the unit
torus (the measure `instMeasureSpaceUnitAddCircle` of the Fourier series):
`∫_box G(x/L) dx = V ∫_torus G`. -/
theorem integral_boxSet_toTorus {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) (G : UnitAddTorus (Fin 3) → E) :
    ∫ x in boxSet L, G (toTorus L x) = boxVolume L • ∫ z, G z := by
  set D : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := Matrix.toLin' (Matrix.diagonal fun i => (L i)⁻¹)
  have hDapp : ∀ x, D x = fun i => (L i)⁻¹ * x i := fun x => by
    funext i
    simp [D, Matrix.mulVec_diagonal]
  have hdet : LinearMap.det D = ∏ i, (L i)⁻¹ := by
    simp [D, LinearMap.det_toLin', Matrix.det_diagonal]
  have hdet0 : LinearMap.det D ≠ 0 := by
    rw [hdet]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => inv_ne_zero (hL i).ne'
  have hmap : Measure.map D (MeasureTheory.volume : Measure (Fin 3 → ℝ)) =
      ENNReal.ofReal (boxVolume L) • (MeasureTheory.volume : Measure (Fin 3 → ℝ)) := by
    rw [Measure.map_linearMap_addHaar_pi_eq_smul_addHaar hdet0, hdet, Finset.prod_inv_distrib,
      inv_inv, abs_of_pos (show 0 < ∏ i, L i from boxVolume_pos hL)]
    rfl
  let e : (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) := MeasurableEquiv.piCongrRight fun i =>
    (Homeomorph.mulLeft₀ (L i)⁻¹ (inv_ne_zero (hL i).ne')).toMeasurableEquiv
  have he : ⇑e = ⇑D := by
    funext x
    rw [hDapp]
    rfl
  have hmp : MeasurePreserving e (MeasureTheory.volume : Measure (Fin 3 → ℝ))
      (ENNReal.ofReal (boxVolume L) • (MeasureTheory.volume : Measure (Fin 3 → ℝ))) :=
    ⟨e.measurable, by rw [he, hmap]⟩
  set box1 : Set (Fin 3 → ℝ) := {x | ∀ i, x i ∈ Ioc ((0 : Fin 3 → ℝ) i) ((0 : Fin 3 → ℝ) i + 1)}
  have hpre : e ⁻¹' box1 = boxSet L := by
    ext x
    simp only [box1, mem_preimage, mem_ofPred_eq, he, hDapp, Pi.zero_apply, zero_add, boxSet,
      Set.mem_pi, mem_univ, mem_Ioc, forall_const]
    refine forall_congr' fun i => ?_
    rw [← div_eq_inv_mul, div_pos_iff_of_pos_right (hL i), div_le_one (hL i)]
  have h1 := hmp.setIntegral_preimage_emb e.measurableEmbedding
    (fun y => G (fun i => ((y i : ℝ) : UnitAddCircle))) box1
  rw [hpre, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (boxVolume_pos hL).le] at h1
  have h2 := UnitAddTorus.integral_preimage G 0
  calc ∫ x in boxSet L, G (toTorus L x)
      = ∫ x in boxSet L, G fun i => ((e x i : ℝ) : UnitAddCircle) :=
        setIntegral_congr_fun (measurableSet_boxSet L) fun x _ => by
          simp only [he, hDapp]
          congr 1
          funext i
          rw [toTorus, div_eq_inv_mul]
    _ = _ := h1
    _ = boxVolume L • ∫ z, G z := congrArg (boxVolume L • ·) h2.symm

/-! ### The Fourier coefficients on the box -/

/-- The plane wave `e_k(x) = exp(2πi Σⱼ kⱼxⱼ/Lⱼ)` of the box with the integer wave vector `k`:
the character `mFourier k` of the unit torus pulled back by the rescaling. -/
def boxWave (L : Fin 3 → ℝ) (k : Fin 3 → ℤ) (x : Fin 3 → ℝ) : ℂ :=
  UnitAddTorus.mFourier k (toTorus L x)

/-- The plane wave of the box is `exp(2πi Σⱼ kⱼxⱼ/Lⱼ)`. -/
theorem boxWave_apply (L : Fin 3 → ℝ) (k : Fin 3 → ℤ) (x : Fin 3 → ℝ) :
    boxWave L k x =
      Complex.exp (2 * Real.pi * Complex.I * ∑ j, (k j : ℂ) * ((x j / L j : ℝ) : ℂ)) := by
  simp only [boxWave, UnitAddTorus.mFourier, ContinuousMap.coe_mk, toTorus, fourier_coe_apply,
    Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The plane wave of the box is continuous. -/
theorem continuous_boxWave (L : Fin 3 → ℝ) (k : Fin 3 → ℤ) : Continuous (boxWave L k) := by
  have h : Continuous (toTorus L) :=
    continuous_pi fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp
      (by fun_prop : Continuous fun x : Fin 3 → ℝ => x i / L i)
  exact (UnitAddTorus.mFourier k).continuous.comp h

/-- The plane wave of the box has the modulus `1`. -/
theorem norm_boxWave (L : Fin 3 → ℝ) (k : Fin 3 → ℤ) (x : Fin 3 → ℝ) : ‖boxWave L k x‖ = 1 := by
  simp [boxWave, UnitAddTorus.mFourier, fourier_apply, Circle.norm_coe]

/-- The characters of the torus are additive in the point: `e_n(z − w) = e_n(z) e_{−n}(w)`. -/
theorem mFourier_sub (n : Fin 3 → ℤ) (z w : UnitAddTorus (Fin 3)) :
    UnitAddTorus.mFourier n (z - w) =
      UnitAddTorus.mFourier n z * UnitAddTorus.mFourier (-n) w := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, Pi.neg_apply, fourier_apply, sub_eq_add_neg, zsmul_add,
    AddCircle.toCircle_add, Circle.coe_mul, neg_smul, smul_neg]

/-- The Fourier coefficient `f_k = (1/V) ∫_box e^{−2πi Σⱼ kⱼxⱼ/Lⱼ} f(x) dx` of a real function on
the box. -/
def boxCoeff (L : Fin 3 → ℝ) (f : (Fin 3 → ℝ) → ℝ) (k : Fin 3 → ℤ) : ℂ :=
  (boxVolume L : ℂ)⁻¹ * ∫ x in boxSet L, boxWave L (-k) x * (f x : ℂ)

/-- The function on the unit torus of a function on the box: `z ↦ f(x)` for the point `x` of the
box over `z`. -/
def torusLift (L : Fin 3 → ℝ) (f : (Fin 3 → ℝ) → ℝ) (z : UnitAddTorus (Fin 3)) : ℂ :=
  (f (fromTorus L z) : ℂ)

/-- The Fourier coefficients on the box are the Fourier coefficients on the unit torus of the
lifted function. -/
theorem boxCoeff_eq_mFourierCoeff {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i)
    (f : (Fin 3 → ℝ) → ℝ) (k : Fin 3 → ℤ) :
    boxCoeff L f k = UnitAddTorus.mFourierCoeff (torusLift L f) k := by
  have h := integral_boxSet_toTorus hL
    (fun z => UnitAddTorus.mFourier (-k) z • torusLift L f z)
  have h' : ∫ x in boxSet L, boxWave L (-k) x * (f x : ℂ) =
      ∫ x in boxSet L, UnitAddTorus.mFourier (-k) (toTorus L x) •
        torusLift L f (toTorus L x) :=
    setIntegral_congr_fun (measurableSet_boxSet L) fun x hx => by
      simp only [boxWave, torusLift, fromTorus_toTorus hL hx, smul_eq_mul]
  rw [UnitAddTorus.mFourierCoeff, boxCoeff, h', h, Complex.real_smul]
  have hV : (boxVolume L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (boxVolume_pos hL).ne'
  field_simp

/-- The lift of a periodic function to the torus commutes with the translations. -/
theorem torusLift_add {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) {f : (Fin 3 → ℝ) → ℝ}
    (hf : BoxPeriodic L f) (v : Fin 3 → ℝ) (z : UnitAddTorus (Fin 3)) :
    torusLift L (fun x => f (x + v)) z = torusLift L f (z + toTorus L v) := by
  have hL0 : ∀ i, L i ≠ 0 := fun i => (hL i).ne'
  simp only [torusLift]
  congr 1
  refine hf.eq_of_toTorus_eq hL0 ?_
  rw [toTorus_add, toTorus_fromTorus hL0, toTorus_fromTorus hL0]

/-- The Fourier coefficients of a translate on the torus: `(F(· + w))_k = e_k(w) F_k`. -/
theorem mFourierCoeff_comp_add (F : UnitAddTorus (Fin 3) → ℂ) (w : UnitAddTorus (Fin 3))
    (k : Fin 3 → ℤ) :
    UnitAddTorus.mFourierCoeff (fun z => F (z + w)) k =
      UnitAddTorus.mFourier k w * UnitAddTorus.mFourierCoeff F k := by
  simp only [UnitAddTorus.mFourierCoeff, smul_eq_mul]
  have h := integral_add_right_eq_self (μ := (MeasureTheory.volume :
    Measure (UnitAddTorus (Fin 3)))) (fun z => UnitAddTorus.mFourier (-k) (z - w) * F z) w
  simp only [add_sub_cancel_right] at h
  rw [h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [mFourier_sub, neg_neg]
  ring

/-- **The translation of a periodic function**: `(f(· + v))_k = e_k(v) f_k`. -/
theorem boxCoeff_comp_add {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) {f : (Fin 3 → ℝ) → ℝ}
    (hf : BoxPeriodic L f) (v : Fin 3 → ℝ) (k : Fin 3 → ℤ) :
    boxCoeff L (fun x => f (x + v)) k = boxWave L k v * boxCoeff L f k := by
  rw [boxCoeff_eq_mFourierCoeff hL, boxCoeff_eq_mFourierCoeff hL]
  have h : torusLift L (fun x => f (x + v)) = fun z => torusLift L f (z + toTorus L v) :=
    funext (torusLift_add hL hf v)
  rw [h, mFourierCoeff_comp_add]
  rfl

/-! ### Derivatives of the coefficients -/

/-- The wave vector `Kⱼ = 2π kⱼ / Lⱼ` of the plane wave `e_k`. -/
def boxWavevector (L : Fin 3 → ℝ) (k : Fin 3 → ℤ) (j : Fin 3) : ℝ := 2 * Real.pi * k j / L j

/-- The frequency `ω_k = |K| = 2π ‖(kⱼ/Lⱼ)ⱼ‖` of the mode `k` of the periodic box. -/
def boxFreq (L : Fin 3 → ℝ) (k : Fin 3 → ℤ) : ℝ := Real.sqrt (∑ j, boxWavevector L k j ^ 2)

/-- `ω_k² = Σⱼ Kⱼ²`. -/
theorem boxFreq_sq (L : Fin 3 → ℝ) (k : Fin 3 → ℤ) :
    boxFreq L k ^ 2 = ∑ j, boxWavevector L k j ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The plane wave along a co-ordinate axis: `e_k(s eⱼ) = exp(i Kⱼ s)`. -/
theorem boxWave_smul_single (L : Fin 3 → ℝ) (k : Fin 3 → ℤ) (j : Fin 3) (s : ℝ) :
    boxWave L k (s • Pi.single j 1) =
      Complex.exp (Complex.I * (boxWavevector L k j : ℂ) * (s : ℂ)) := by
  rw [boxWave_apply, Finset.sum_eq_single j]
  · simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, boxWavevector]
    congr 1
    push_cast
    ring
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij]
  · simp

/-- The closed box `[0, L₁] × [0, L₂] × [0, L₃]` contains the box. -/
theorem boxSet_subset_Icc (L : Fin 3 → ℝ) : boxSet L ⊆ Set.pi univ fun i => Icc 0 (L i) :=
  Set.pi_mono fun _ _ => Ioc_subset_Icc_self

/-- The box has a finite volume. -/
theorem volume_boxSet_ne_top (L : Fin 3 → ℝ) :
    (MeasureTheory.volume : Measure (Fin 3 → ℝ)) (boxSet L) ≠ ⊤ :=
  (lt_of_le_of_lt (measure_mono (boxSet_subset_Icc L))
    (isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top).ne

/-- A continuous function is integrable on the box. -/
theorem integrableOn_boxSet {E : Type*} [NormedAddCommGroup E] {g : (Fin 3 → ℝ) → E}
    (hg : Continuous g) (L : Fin 3 → ℝ) : IntegrableOn g (boxSet L) :=
  (hg.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)).mono_set
    (boxSet_subset_Icc L)

/-- **Differentiation under the integral over the box**, for a function of the time and the
point that is continuous together with its time derivative. -/
theorem hasDerivAt_integral_boxSet (L : Fin 3 → ℝ) {F F' : ℝ → (Fin 3 → ℝ) → ℂ}
    (hF : Continuous (Function.uncurry F)) (hF' : Continuous (Function.uncurry F'))
    (hd : ∀ s x, HasDerivAt (fun s => F s x) (F' s x) s) (t : ℝ) :
    HasDerivAt (fun s => ∫ x in boxSet L, F s x) (∫ x in boxSet L, F' t x) t := by
  set K : Set (Fin 3 → ℝ) := Set.pi univ fun i => Icc 0 (L i)
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := t - 1) (b := t + 1)).prod hK).exists_bound_of_continuousOn
    hF'.continuousOn
  have hcont : ∀ s, Continuous (F s) := fun s =>
    hF.comp (continuous_const.prodMk continuous_id)
  have hcont' : ∀ s, Continuous (F' s) := fun s =>
    hF'.comp (continuous_const.prodMk continuous_id)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (Icc_mem_nhds (by linarith : t - 1 < t) (by linarith : t < t + 1))
    (Eventually.of_forall fun s => (hcont s).aestronglyMeasurable)
    (integrableOn_boxSet (hcont t) L) (hcont' t).aestronglyMeasurable ?_
    (integrableOn_const (volume_boxSet_ne_top L)) ?_).2
  · filter_upwards [ae_restrict_mem (measurableSet_boxSet L)] with x hx s hs
    exact hC (s, x) ⟨hs, boxSet_subset_Icc L hx⟩
  · exact Eventually.of_forall fun x s _ => hd s x

/-- **The coefficients of a derivative.** For a periodic `C¹` function, the boundary terms of the
integration by parts cancel and `(∂ⱼf)_k = i Kⱼ f_k`. The proof differentiates the translation
law `(f(· + s eⱼ))_k = e^{i Kⱼ s} f_k` at `s = 0`. -/
theorem boxCoeff_partial {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) (hper : BoxPeriodic L f) (j : Fin 3) (k : Fin 3 → ℤ) :
    boxCoeff L (fun x => fderiv ℝ f x (Pi.single j 1)) k =
      Complex.I * boxWavevector L k j * boxCoeff L f k := by
  set e : Fin 3 → ℝ := Pi.single j 1
  have hfd : ∀ s x, HasDerivAt (fun s => f (x + s • e)) (fderiv ℝ f (x + s • e) e) s :=
    fun s x => by
      have hl : HasDerivAt (fun y : ℝ => x + y • e) e s := by
        simpa using ((hasDerivAt_id (𝕜 := ℝ) s).smul_const e).const_add x
      exact (hf.differentiable one_ne_zero (x + s • e)).hasFDerivAt.comp_hasDerivAt s hl
  have hdf : Continuous fun p : ℝ × (Fin 3 → ℝ) => fderiv ℝ f (p.2 + p.1 • e) e :=
    ((hf.continuous_fderiv one_ne_zero).comp (continuous_snd.add
      (continuous_fst.smul continuous_const))).clm_apply continuous_const
  have h1 : HasDerivAt (fun s : ℝ => boxCoeff L (fun x => f (x + s • e)) k)
      (boxCoeff L (fun x => fderiv ℝ f x e) k) 0 := by
    unfold boxCoeff
    refine HasDerivAt.const_mul _ ?_
    have h := hasDerivAt_integral_boxSet L
      (F := fun (s : ℝ) x => boxWave L (-k) x * (f (x + s • e) : ℂ))
      (F' := fun (s : ℝ) x => boxWave L (-k) x * (fderiv ℝ f (x + s • e) e : ℂ))
      ((continuous_boxWave L (-k)).comp continuous_snd |>.mul
        (Complex.continuous_ofReal.comp (hf.continuous.comp (continuous_snd.add
          (continuous_fst.smul continuous_const)))))
      (((continuous_boxWave L (-k)).comp continuous_snd).mul
        (Complex.continuous_ofReal.comp hdf))
      (fun s x => (hfd s x).ofReal_comp.const_mul _) 0
    simpa using h
  have h2 : HasDerivAt (fun s : ℝ => boxCoeff L (fun x => f (x + s • e)) k)
      (Complex.I * boxWavevector L k j * boxCoeff L f k) 0 := by
    have hfun : (fun s : ℝ => boxCoeff L (fun x => f (x + s • e)) k) =
        fun s : ℝ => Complex.exp (Complex.I * (boxWavevector L k j : ℂ) * (s : ℂ)) *
          boxCoeff L f k :=
      funext fun s => by rw [boxCoeff_comp_add hL hper, boxWave_smul_single]
    rw [hfun]
    have h := (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul
      (Complex.I * (boxWavevector L k j : ℂ))).cexp).mul_const (boxCoeff L f k)
    simpa using h
  exact h1.unique h2

/-! ### Linearity of the coefficients -/

/-- The integrand of a coefficient of a continuous function is integrable on the box. -/
theorem integrableOn_boxWave_mul (L : Fin 3 → ℝ) (k : Fin 3 → ℤ) {f : (Fin 3 → ℝ) → ℝ}
    (hf : Continuous f) : IntegrableOn (fun x => boxWave L k x * (f x : ℂ)) (boxSet L) :=
  integrableOn_boxSet ((continuous_boxWave L k).mul (Complex.continuous_ofReal.comp hf)) L

/-- The coefficients of a sum of continuous functions. -/
theorem boxCoeff_add (L : Fin 3 → ℝ) {f g : (Fin 3 → ℝ) → ℝ} (hf : Continuous f)
    (hg : Continuous g) (k : Fin 3 → ℤ) :
    boxCoeff L (fun x => f x + g x) k = boxCoeff L f k + boxCoeff L g k := by
  simp only [boxCoeff, Complex.ofReal_add, mul_add]
  rw [integral_add (integrableOn_boxWave_mul L (-k) hf) (integrableOn_boxWave_mul L (-k) hg),
    mul_add]

/-- The coefficients of a difference of continuous functions. -/
theorem boxCoeff_sub (L : Fin 3 → ℝ) {f g : (Fin 3 → ℝ) → ℝ} (hf : Continuous f)
    (hg : Continuous g) (k : Fin 3 → ℤ) :
    boxCoeff L (fun x => f x - g x) k = boxCoeff L f k - boxCoeff L g k := by
  simp only [boxCoeff, Complex.ofReal_sub, mul_sub]
  rw [integral_sub (integrableOn_boxWave_mul L (-k) hf) (integrableOn_boxWave_mul L (-k) hg),
    mul_sub]

/-- The coefficients of a finite sum of continuous functions. -/
theorem boxCoeff_sum {ι : Type*} (L : Fin 3 → ℝ) (s : Finset ι) {f : ι → (Fin 3 → ℝ) → ℝ}
    (hf : ∀ i, Continuous (f i)) (k : Fin 3 → ℤ) :
    boxCoeff L (fun x => ∑ i ∈ s, f i x) k = ∑ i ∈ s, boxCoeff L (f i) k := by
  simp only [boxCoeff, Complex.ofReal_sum, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => integrableOn_boxWave_mul L (-k) (hf i), Finset.mul_sum]

/-- The coefficients of the zero function vanish. -/
theorem boxCoeff_zero (L : Fin 3 → ℝ) (k : Fin 3 → ℤ) : boxCoeff L (fun _ => 0) k = 0 := by
  simp [boxCoeff]

/-! ### Fields on the periodic box -/

/-- The slice `x ↦ u(t, x)` of a function on space-time at the time `t`. -/
def slice (u : Spacetime → ℝ) (t : ℝ) (x : Fin 3 → ℝ) : ℝ := u (Fin.cons t x)

/-- The event `(t, x)` depends smoothly on the time and the point. -/
theorem contDiff_cons {n : ℕ∞ω} :
    ContDiff ℝ n fun p : ℝ × (Fin 3 → ℝ) => (Fin.cons p.1 p.2 : Spacetime) := by
  refine contDiff_pi.mpr fun μ => ?_
  refine Fin.cases ?_ (fun i => ?_) μ
  · simpa using contDiff_fst
  · simp only [Fin.cons_succ]
    fun_prop

/-- The slice of a `Cⁿ` function is `Cⁿ`. -/
theorem contDiff_slice {n : ℕ∞ω} {u : Spacetime → ℝ} (hu : ContDiff ℝ n u) (t : ℝ) :
    ContDiff ℝ n (slice u t) :=
  hu.comp (contDiff_cons.comp (contDiff_const.prodMk contDiff_id))

/-- A function of the time and the point through the event `(t, x)` is continuous. -/
theorem continuous_slice_uncurry {u : Spacetime → ℝ} (hu : Continuous u) :
    Continuous fun p : ℝ × (Fin 3 → ℝ) => u (Fin.cons p.1 p.2) :=
  hu.comp (contDiff_cons (n := 0)).continuous

/-- The derivative `∂_μ u` of a `Cⁿ⁺¹` function is `Cⁿ`. -/
theorem contDiff_partialAt {n : ℕ∞ω} {u : Spacetime → ℝ} (hu : ContDiff ℝ (n + 1) u)
    (μ : Fin 4) : ContDiff ℝ n (partialAt u μ) :=
  (hu.fderiv_right le_rfl).clm_apply contDiff_const

/-- The spatial derivatives of a slice are the derivatives along the spatial co-ordinates:
`∂ⱼ (u(t, ·)) = (∂_{j+1} u)(t, ·)`. -/
theorem fderiv_slice {u : Spacetime → ℝ} (hu : ContDiff ℝ 1 u) (t : ℝ) (x : Fin 3 → ℝ)
    (j : Fin 3) :
    fderiv ℝ (slice u t) x (Pi.single j 1) = partialAt u j.succ (Fin.cons t x) := by
  set e : Fin 3 → ℝ := Pi.single j 1
  have hl : HasDerivAt (fun y : ℝ => x + y • e) e 0 := by
    simpa using ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const e).const_add x
  have hfx : HasFDerivAt (slice u t) (fderiv ℝ (slice u t) x) (x + (0 : ℝ) • e) := by
    rw [zero_smul, add_zero]
    exact ((contDiff_slice hu t).differentiable one_ne_zero x).hasFDerivAt
  have h1 := hfx.comp_hasDerivAt (0 : ℝ) hl
  have hl' : HasDerivAt (fun y : ℝ => (Fin.cons t x : Spacetime) + y • Pi.single j.succ 1)
      (Pi.single j.succ 1) 0 := by
    simpa using ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const
      (Pi.single j.succ 1 : Spacetime)).const_add (Fin.cons t x : Spacetime)
  have hfy : HasFDerivAt u (fderiv ℝ u (Fin.cons t x))
      ((Fin.cons t x : Spacetime) + (0 : ℝ) • Pi.single j.succ 1) := by
    rw [zero_smul, add_zero]
    exact ((hu.differentiable one_ne_zero) (Fin.cons t x)).hasFDerivAt
  have h2 := hfy.comp_hasDerivAt (0 : ℝ) hl'
  have hfun : (slice u t ∘ fun y : ℝ => x + y • e) =
      (u ∘ fun y : ℝ => (Fin.cons t x : Spacetime) + y • Pi.single j.succ 1) := by
    funext y
    simp only [Function.comp, slice]
    congr 1
    ext μ
    refine Fin.cases ?_ (fun i => ?_) μ
    · simp
    · by_cases h : i = j
      · subst h
        simp [e]
      · simp [e, h]
  rw [hfun] at h1
  exact h1.unique h2

/-- The time derivative of a function at the event `(t, x)`:
`∂ₜ u(t, x) = (∂₀ u)(t, x)`. -/
theorem hasDerivAt_cons {u : Spacetime → ℝ} (hu : ContDiff ℝ 1 u) (t : ℝ) (x : Fin 3 → ℝ) :
    HasDerivAt (fun s => u (Fin.cons s x)) (partialAt u 0 (Fin.cons t x)) t := by
  have hc : HasDerivAt (fun s : ℝ => (Fin.cons s x : Spacetime)) (Pi.single 0 1) t := by
    refine hasDerivAt_pi.mpr fun μ => ?_
    refine Fin.cases ?_ (fun i => ?_) μ
    · simp only [Fin.cons_zero, Pi.single_eq_same]
      exact hasDerivAt_id' t
    · simp only [Fin.cons_succ, ne_eq, Fin.succ_ne_zero, not_false_eq_true,
        Pi.single_eq_of_ne]
      exact hasDerivAt_const t (x i)
  exact ((hu.differentiable one_ne_zero) (Fin.cons t x)).hasFDerivAt.comp_hasDerivAt t hc

/-- The derivatives of a function that is periodic in space are periodic in space. -/
theorem BoxPeriodic.slice_partialAt {L : Fin 3 → ℝ} {u : Spacetime → ℝ}
    (hper : ∀ t, BoxPeriodic L (slice u t)) (μ : Fin 4) (t : ℝ) :
    BoxPeriodic L (slice (partialAt u μ) t) := by
  intro x m
  set c : Spacetime := Fin.cons 0 fun i => m i * L i
  have hu : (fun y => u (y + c)) = u := by
    funext y
    have h := hper (y 0) (Fin.tail y) m
    simp only [slice] at h
    have hy : (Fin.cons (y 0) (Fin.tail y) : Spacetime) = y := Fin.cons_self_tail y
    rw [hy] at h
    rw [← h]
    congr 1
    ext ν
    refine Fin.cases ?_ (fun i => ?_) ν
    · simp [c]
    · simp [c, Fin.tail]
  have hcx : (Fin.cons t (fun i => x i + m i * L i) : Spacetime) = Fin.cons t x + c := by
    ext ν
    refine Fin.cases ?_ (fun i => ?_) ν
    · simp [c]
    · simp [c]
  simp only [slice, partialAt]
  rw [hcx, ← fderiv_comp_add_right, hu]

/-! ### The equations of the modes -/

/-- **The time derivative of a coefficient**: `d/dt u_k(t) = (∂ₜu)_k(t)` for a `C¹` function on
space-time. -/
theorem hasDerivAt_boxCoeff_slice (L : Fin 3 → ℝ) {u : Spacetime → ℝ} (hu : ContDiff ℝ 1 u)
    (k : Fin 3 → ℤ) (t : ℝ) :
    HasDerivAt (fun s => boxCoeff L (slice u s) k) (boxCoeff L (slice (partialAt u 0) t) k) t := by
  unfold boxCoeff
  refine HasDerivAt.const_mul _ ?_
  have hd : Continuous (partialAt u 0) := (contDiff_partialAt (n := 0) hu 0).continuous
  exact hasDerivAt_integral_boxSet L
    (F := fun (s : ℝ) x => boxWave L (-k) x * (u (Fin.cons s x) : ℂ))
    (F' := fun (s : ℝ) x => boxWave L (-k) x * (partialAt u 0 (Fin.cons s x) : ℂ))
    (((continuous_boxWave L (-k)).comp continuous_snd).mul
      (Complex.continuous_ofReal.comp (continuous_slice_uncurry hu.continuous)))
    (((continuous_boxWave L (-k)).comp continuous_snd).mul
      (Complex.continuous_ofReal.comp (continuous_slice_uncurry hd)))
    (fun s x => (hasDerivAt_cons hu s x).ofReal_comp.const_mul _) t

/-- The coefficients of a second spatial derivative: `(∂ⱼ²u)_k = −Kⱼ² u_k` for a `C²` function
that is periodic in space. -/
theorem boxCoeff_partial_partial {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) {u : Spacetime → ℝ}
    (hu : ContDiff ℝ 2 u) (hper : ∀ t, BoxPeriodic L (slice u t)) (j : Fin 3) (t : ℝ)
    (k : Fin 3 → ℤ) :
    boxCoeff L (slice (partialAt (partialAt u j.succ) j.succ) t) k =
      -(boxWavevector L k j : ℂ) ^ 2 * boxCoeff L (slice u t) k := by
  have hu1 : ContDiff ℝ 1 (partialAt u j.succ) := contDiff_partialAt (n := 1) hu j.succ
  have h2 : slice (partialAt (partialAt u j.succ) j.succ) t =
      fun x => fderiv ℝ (slice (partialAt u j.succ) t) x (Pi.single j 1) :=
    funext fun x => (fderiv_slice hu1 t x j).symm
  have h1 : slice (partialAt u j.succ) t = fun x => fderiv ℝ (slice u t) x (Pi.single j 1) :=
    funext fun x => (fderiv_slice (hu.of_le (by norm_num)) t x j).symm
  rw [h2, boxCoeff_partial hL (contDiff_slice hu1 t) (BoxPeriodic.slice_partialAt hper _ t),
    h1, boxCoeff_partial hL (contDiff_slice (hu.of_le (by norm_num)) t) (hper t)]
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  linear_combination (boxWavevector L k j : ℂ) ^ 2 * Complex.I_mul_I

/-- **The equation of the modes** (Landau–Lifshitz, §52). For a `C²` solution of the wave
equation `box u = 0` that is periodic in space, the coefficient `u_k(t)` has the derivative
`(∂ₜu)_k(t)`, whose derivative is `−ω_k² u_k(t)`: `ü_k = −ω_k² u_k` with `ω_k = |K|`. -/
theorem hasDerivAt_boxCoeff_of_box {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) {u : Spacetime → ℝ}
    (hu : ContDiff ℝ 2 u) (hper : ∀ t, BoxPeriodic L (slice u t)) (hbox : ∀ y, box u y = 0)
    (k : Fin 3 → ℤ) (t : ℝ) :
    HasDerivAt (fun s => boxCoeff L (slice u s) k) (boxCoeff L (slice (partialAt u 0) t) k) t ∧
      HasDerivAt (fun s => boxCoeff L (slice (partialAt u 0) s) k)
        (-(boxFreq L k : ℂ) ^ 2 * boxCoeff L (slice u t) k) t := by
  refine ⟨hasDerivAt_boxCoeff_slice L (hu.of_le (by norm_num)) k t, ?_⟩
  have h := hasDerivAt_boxCoeff_slice L (contDiff_partialAt (n := 1) hu 0) k t
  have hcont : ∀ j : Fin 3,
      Continuous (slice (partialAt (partialAt u j.succ) j.succ) t) := fun j =>
    (contDiff_slice (contDiff_partialAt (n := 0)
      (contDiff_partialAt (n := 1) hu j.succ) j.succ) t).continuous
  have hsum : slice (partialAt (partialAt u 0) 0) t =
      fun x => ∑ j : Fin 3, slice (partialAt (partialAt u j.succ) j.succ) t x := by
    funext x
    have hb := hbox (Fin.cons t x)
    simp only [box] at hb
    simp only [slice]
    linarith
  rw [hsum, boxCoeff_sum L _ hcont] at h
  convert h using 1
  simp only [boxCoeff_partial_partial hL hu hper, ← Finset.sum_mul]
  congr 1
  have hf := boxFreq_sq L k
  have hf' : (boxFreq L k : ℂ) ^ 2 = ∑ j, (boxWavevector L k j : ℂ) ^ 2 := by
    exact_mod_cast hf
  rw [Finset.sum_neg_distrib, hf']

/-- **The transversality of the modes**: for a `C¹` field `a` that is periodic in space and has
`div a = 0`, the coefficients satisfy `K · a_k = Σⱼ Kⱼ (aⱼ)_k = 0`. -/
theorem transverse_boxCoeff {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) {a : Fin 3 → Spacetime → ℝ}
    (ha : ∀ j, ContDiff ℝ 1 (a j)) (hper : ∀ j t, BoxPeriodic L (slice (a j) t))
    (hdiv : ∀ y, divergence3 a y = 0) (t : ℝ) (k : Fin 3 → ℤ) :
    ∑ j : Fin 3, (boxWavevector L k j : ℂ) * boxCoeff L (slice (a j) t) k = 0 := by
  have h0 : slice (divergence3 a) t = fun _ => 0 := funext fun x => hdiv _
  have hs : slice (divergence3 a) t =
      fun x => ∑ j : Fin 3, fderiv ℝ (slice (a j) t) x (Pi.single j 1) := by
    funext x
    simp only [slice, divergence3]
    exact Finset.sum_congr rfl fun j _ => (fderiv_slice (ha j) t x j).symm
  have hc : ∀ j : Fin 3, Continuous fun x => fderiv ℝ (slice (a j) t) x (Pi.single j 1) :=
    fun j => ((contDiff_slice (ha j) t).continuous_fderiv one_ne_zero).clm_apply
      continuous_const
  have h := congrArg (fun f => boxCoeff L f k) (h0.symm.trans hs)
  simp only [boxCoeff_zero] at h
  rw [boxCoeff_sum L _ (fun j => hc j)] at h
  simp only [fun j => boxCoeff_partial hL (contDiff_slice (ha j) t) (hper j t) j k] at h
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have h' : Complex.I * ∑ j : Fin 3, (boxWavevector L k j : ℂ) * boxCoeff L (slice (a j) t) k
      = 0 := by
    rw [Finset.mul_sum, h]
    exact Finset.sum_congr rfl fun j _ => by ring
  exact (mul_eq_zero.mp h').resolve_left hI

/-! ### The identity of Parseval on the box -/

/-- **The identity of Parseval on the box**: for a continuous function,
`Σ_k |f_k|² = (1/V) ∫_box f²`. The proof transports `UnitAddTorus.hasSum_sq_mFourierCoeff` along
the rescaling of the box to the unit torus. -/
theorem hasSum_sq_boxCoeff {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) {f : (Fin 3 → ℝ) → ℝ}
    (hf : Continuous f) :
    HasSum (fun k => ‖boxCoeff L f k‖ ^ 2) ((boxVolume L)⁻¹ * ∫ x in boxSet L, f x ^ 2) := by
  set F : UnitAddTorus (Fin 3) → ℂ := torusLift L f
  have hmeas : AEStronglyMeasurable F MeasureTheory.volume :=
    ((Complex.continuous_ofReal.comp hf).measurable.comp
      (measurable_fromTorus L)).aestronglyMeasurable
  obtain ⟨C, hC⟩ := (isCompact_univ_pi fun i => isCompact_Icc (a := (0 : ℝ)) (b := L i))
    |>.exists_bound_of_continuousOn hf.continuousOn
  have hbound : ∀ z, ‖F z‖ ≤ C := fun z => by
    simpa [F, torusLift] using hC _ (fromTorus_mem_Icc hL z)
  have hmem : MemLp F 2 MeasureTheory.volume :=
    MemLp.of_bound hmeas C (Eventually.of_forall hbound)
  have hP := UnitAddTorus.hasSum_sq_mFourierCoeff (hmem.toLp F)
  have hcoe := hmem.coeFn_toLp
  have hc : ∀ k, UnitAddTorus.mFourierCoeff (⇑(hmem.toLp F)) k =
      UnitAddTorus.mFourierCoeff F k := fun k =>
    integral_congr_ae (hcoe.mono fun z hz => by simp only [hz])
  have hn : ∫ z, ‖(hmem.toLp F) z‖ ^ 2 = ∫ z, ‖F z‖ ^ 2 :=
    integral_congr_ae (hcoe.mono fun z hz => by simp only [hz])
  simp only [hc, hn] at hP
  have hbox := integral_boxSet_toTorus hL (fun z => ‖F z‖ ^ 2)
  have hint : ∫ x in boxSet L, ‖F (toTorus L x)‖ ^ 2 = ∫ x in boxSet L, f x ^ 2 :=
    setIntegral_congr_fun (measurableSet_boxSet L) fun x hx => by
      simp [F, torusLift, fromTorus_toTorus hL hx, sq_abs]
  rw [hint, smul_eq_mul] at hbox
  have hV : boxVolume L ≠ 0 := (boxVolume_pos hL).ne'
  rw [hbox, ← mul_assoc, inv_mul_cancel₀ hV, one_mul]
  simpa only [boxCoeff_eq_mFourierCoeff hL] using hP

/-! ### The energy of the field as a sum over the modes -/

/-- The identity of Lagrange for a real vector `K` and a complex vector `a`:
`|K × a|² = |K|² |a|² − |K · a|²`. -/
theorem norm_cross_sq (K : Fin 3 → ℝ) (a : Fin 3 → ℂ) :
    ‖(K 1 : ℂ) * a 2 - K 2 * a 1‖ ^ 2 + ‖(K 2 : ℂ) * a 0 - K 0 * a 2‖ ^ 2 +
        ‖(K 0 : ℂ) * a 1 - K 1 * a 0‖ ^ 2 =
      (∑ j, K j ^ 2) * ∑ j, ‖a j‖ ^ 2 - ‖∑ j, (K j : ℂ) * a j‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Fin.sum_univ_three,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The components of a `C²` potential are `C²`. -/
theorem contDiff_potentialComponent {A : Potential} (hA : ContDiff ℝ 2 A) (ν : Fin 4) :
    ContDiff ℝ 2 (potentialComponent A ν) :=
  contDiff_iff_contDiffAt.mpr fun _ => contDiffAt_potentialComponent hA.contDiffAt ν

/-- With `φ = 0` the electric field is `Eᵢ = −∂ₜaᵢ`. -/
theorem electricField_of_coulomb {A : Potential} (hA : ContDiff ℝ 1 A)
    (hφ : ∀ y, potentialComponent A 0 y = 0) (i : Fin 3) (y : Spacetime) :
    electricField (fieldTensor A) i y = -partialAt (potentialComponent A i.succ) 0 y := by
  rw [(electricField_fieldTensor_eventuallyEq hA.contDiffAt i).eq_of_nhds]
  have h0 : potentialComponent A 0 = fun _ => 0 := funext hφ
  rw [h0, partialAt_const, zero_sub]

/-- The magnetic field is `B = curl 𝐚`, in components. -/
theorem magneticField_fieldTensor_apply {A : Potential} (hA : ContDiff ℝ 1 A) (y : Spacetime) :
    magneticField (fieldTensor A) 0 y =
        partialAt (potentialComponent A 3) 2 y - partialAt (potentialComponent A 2) 3 y ∧
      magneticField (fieldTensor A) 1 y =
        partialAt (potentialComponent A 1) 3 y - partialAt (potentialComponent A 3) 1 y ∧
      magneticField (fieldTensor A) 2 y =
        partialAt (potentialComponent A 2) 1 y - partialAt (potentialComponent A 1) 2 y := by
  obtain ⟨h0, h1, h2⟩ := magneticField_fieldTensor_eventuallyEq hA.contDiffAt (x := y)
  exact ⟨h0.eq_of_nhds, h1.eq_of_nhds, h2.eq_of_nhds⟩

/-- In the gauge of Coulomb, `φ = 0` and `∂^μ A_μ = 0` give `div 𝐚 = 0`. -/
theorem divergence3_of_coulomb {A : Potential} (hφ : ∀ y, potentialComponent A 0 y = 0)
    (hdiv : ∀ y, lorenzDivergence A y = 0) (y : Spacetime) :
    divergence3 (fun j => potentialComponent A j.succ) y = 0 := by
  have h := hdiv y
  have h0 : potentialComponent A 0 = fun _ => 0 := funext hφ
  rw [lorenzDivergence, h0, partialAt_const, neg_zero, zero_add] at h
  exact h

/-- **The energy of the field as a sum over the modes** (Landau–Lifshitz, §52). Let `A` be a `C²`
potential in the gauge of Coulomb (`φ = 0` and `∂^μ A_μ = div 𝐚 = 0`) whose spatial components
`aⱼ` are periodic in space with the periods `Lᵢ`, and let `aⱼ,k(t)` be the coefficients of
`aⱼ(t, ·)`. At each time `t`,
`∫_box ½ (E² + B²) = V Σ_k ½ (Σⱼ |ȧⱼ,k|² + ω_k² Σⱼ |aⱼ,k|²)`,
with `ω_k = |K|`: the field is a sum of independent oscillators. The equations of Maxwell are not
used; with them each `aⱼ,k` solves `ä = −ω_k² a` (`hasDerivAt_boxCoeff_of_maxwell`). -/
theorem hasSum_fieldEnergy {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) {A : Potential}
    (hA : ContDiff ℝ 2 A) (hφ : ∀ y, potentialComponent A 0 y = 0)
    (hdiv : ∀ y, lorenzDivergence A y = 0)
    (hper : ∀ (j : Fin 3) t, BoxPeriodic L (slice (potentialComponent A j.succ) t)) (t : ℝ) :
    HasSum (fun k => boxVolume L *
        ((∑ j : Fin 3,
            ‖deriv (fun s => boxCoeff L (slice (potentialComponent A j.succ) s) k) t‖ ^ 2 +
          boxFreq L k ^ 2 *
            ∑ j : Fin 3, ‖boxCoeff L (slice (potentialComponent A j.succ) t) k‖ ^ 2) / 2))
      (∫ x in boxSet L, energyDensity (fieldTensor A) (Fin.cons t x)) := by
  set a : Fin 3 → Spacetime → ℝ := fun j => potentialComponent A j.succ with ha_def
  have ha1 : ∀ j, ContDiff ℝ 1 (a j) := fun j =>
    (contDiff_potentialComponent hA j.succ).of_le (by norm_num)
  have hA1 : ContDiff ℝ 1 A := hA.of_le (by norm_num)
  have hdiv3 : ∀ y, divergence3 a y = 0 := divergence3_of_coulomb hφ hdiv
  set e : Fin 3 → (Fin 3 → ℝ) → ℝ := fun i => slice (partialAt (a i) 0) t with he_def
  set d : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℝ :=
    fun i j x => fderiv ℝ (slice (a i) t) x (Pi.single j 1) with hd_def
  set b : Fin 3 → (Fin 3 → ℝ) → ℝ :=
    ![fun x => d 2 1 x - d 1 2 x, fun x => d 0 2 x - d 2 0 x, fun x => d 1 0 x - d 0 1 x]
    with hb_def
  have hd : ∀ i j x, d i j x = partialAt (a i) j.succ (Fin.cons t x) := fun i j x =>
    fderiv_slice (ha1 i) t x j
  have hcd : ∀ i j, Continuous (d i j) := fun i j =>
    ((contDiff_slice (ha1 i) t).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hce : ∀ i, Continuous (e i) := fun i =>
    (contDiff_slice (contDiff_partialAt (n := 0) (ha1 i) 0) t).continuous
  have hcb : ∀ i, Continuous (b i) := fun i => by
    fin_cases i
    · exact (hcd 2 1).sub (hcd 1 2)
    · exact (hcd 0 2).sub (hcd 2 0)
    · exact (hcd 1 0).sub (hcd 0 1)
  -- the energy density in terms of the six functions
  have hED : ∀ x, energyDensity (fieldTensor A) (Fin.cons t x) =
      (1 / 2 : ℝ) * (∑ i, e i x ^ 2 + ∑ i, b i x ^ 2) := fun x => by
    obtain ⟨hB0, hB1, hB2⟩ := magneticField_fieldTensor_apply hA1 (Fin.cons t x)
    have h21 : partialAt (potentialComponent A 3) 2 (Fin.cons t x) = d 2 1 x := (hd 2 1 x).symm
    have h12 : partialAt (potentialComponent A 2) 3 (Fin.cons t x) = d 1 2 x := (hd 1 2 x).symm
    have h02 : partialAt (potentialComponent A 1) 3 (Fin.cons t x) = d 0 2 x := (hd 0 2 x).symm
    have h20 : partialAt (potentialComponent A 3) 1 (Fin.cons t x) = d 2 0 x := (hd 2 0 x).symm
    have h10 : partialAt (potentialComponent A 2) 1 (Fin.cons t x) = d 1 0 x := (hd 1 0 x).symm
    have h01 : partialAt (potentialComponent A 1) 2 (Fin.cons t x) = d 0 1 x := (hd 0 1 x).symm
    simp only [energyDensity, electricField_of_coulomb hA1 hφ, hB0, hB1, hB2, h21, h12, h02, h20,
      h10, h01, Fin.sum_univ_three, hb_def, he_def, ha_def, slice]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    ring
  -- the integral of the energy density
  have hie : ∀ i, IntegrableOn (fun x => e i x ^ 2) (boxSet L) := fun i =>
    integrableOn_boxSet ((hce i).pow 2) L
  have hib : ∀ i, IntegrableOn (fun x => b i x ^ 2) (boxSet L) := fun i =>
    integrableOn_boxSet ((hcb i).pow 2) L
  have hint : ∫ x in boxSet L, energyDensity (fieldTensor A) (Fin.cons t x) =
      (1 / 2 : ℝ) * (∑ i, (∫ x in boxSet L, e i x ^ 2) +
        ∑ i, (∫ x in boxSet L, b i x ^ 2)) := by
    simp only [hED]
    rw [integral_const_mul, integral_add (integrable_finsetSum _ fun i _ => hie i)
      (integrable_finsetSum _ fun i _ => hib i), integral_finsetSum _ fun i _ => hie i,
      integral_finsetSum _ fun i _ => hib i]
  -- the identity of Parseval for the six functions
  have hV : boxVolume L ≠ 0 := (boxVolume_pos hL).ne'
  have hP : ∀ {g : (Fin 3 → ℝ) → ℝ}, Continuous g →
      HasSum (fun k => boxVolume L * ‖boxCoeff L g k‖ ^ 2) (∫ x in boxSet L, g x ^ 2) :=
    fun hg => by
      have h := (hasSum_sq_boxCoeff hL hg).mul_left (boxVolume L)
      rwa [← mul_assoc, mul_inv_cancel₀ hV, one_mul] at h
  have hsum := ((hasSum_sum (s := Finset.univ) fun i _ => hP (hce i)).add
    (hasSum_sum (s := Finset.univ) fun i _ => hP (hcb i))).mul_left (1 / 2 : ℝ)
  rw [hint]
  convert hsum using 1
  funext k
  -- the coefficients of the six functions
  have hce' : ∀ j, boxCoeff L (e j) k = deriv (fun s => boxCoeff L (slice (a j) s) k) t :=
    fun j => (hasDerivAt_boxCoeff_slice L (ha1 j) k t).deriv.symm
  have hcd' : ∀ i j, boxCoeff L (d i j) k =
      Complex.I * boxWavevector L k j * boxCoeff L (slice (a i) t) k := fun i j =>
    boxCoeff_partial hL (contDiff_slice (ha1 i) t) (hper i t) j k
  set c : Fin 3 → ℂ := fun j => boxCoeff L (slice (a j) t) k with hc_def
  set K : Fin 3 → ℝ := boxWavevector L k with hK_def
  have hcb0 : boxCoeff L (b 0) k = Complex.I * ((K 1 : ℂ) * c 2 - K 2 * c 1) := by
    rw [show b 0 = fun x => d 2 1 x - d 1 2 x from rfl, boxCoeff_sub L (hcd 2 1) (hcd 1 2),
      hcd', hcd']
    ring
  have hcb1 : boxCoeff L (b 1) k = Complex.I * ((K 2 : ℂ) * c 0 - K 0 * c 2) := by
    rw [show b 1 = fun x => d 0 2 x - d 2 0 x from rfl, boxCoeff_sub L (hcd 0 2) (hcd 2 0),
      hcd', hcd']
    ring
  have hcb2 : boxCoeff L (b 2) k = Complex.I * ((K 0 : ℂ) * c 1 - K 1 * c 0) := by
    rw [show b 2 = fun x => d 1 0 x - d 0 1 x from rfl, boxCoeff_sub L (hcd 1 0) (hcd 0 1),
      hcd', hcd']
    ring
  have htr : ∑ j, (K j : ℂ) * c j = 0 := transverse_boxCoeff hL ha1 hper hdiv3 t k
  have hlag := norm_cross_sq K c
  rw [htr, norm_zero] at hlag
  have hbsum : ∑ i, ‖boxCoeff L (b i) k‖ ^ 2 = boxFreq L k ^ 2 * ∑ j, ‖c j‖ ^ 2 := by
    rw [Fin.sum_univ_three, hcb0, hcb1, hcb2, norm_mul, norm_mul, norm_mul, Complex.norm_I,
      one_mul, one_mul, one_mul, hlag, boxFreq_sq]
    ring
  have hesum : ∑ i, ‖boxCoeff L (e i) k‖ ^ 2 =
      ∑ j, ‖deriv (fun s => boxCoeff L (slice (a j) s) k) t‖ ^ 2 :=
    Finset.sum_congr rfl fun j _ => by rw [hce' j]
  rw [← Finset.mul_sum, ← Finset.mul_sum, hbsum, hesum]
  ring

/-- **The energy of the field as a sum over the modes**, as a sum `Σ'`: under the hypotheses of
`hasSum_fieldEnergy`, `∫_box ½ (E² + B²) = Σ'_k V ½ (Σⱼ |ȧⱼ,k|² + ω_k² Σⱼ |aⱼ,k|²)`. -/
theorem fieldEnergy_eq_tsum {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) {A : Potential}
    (hA : ContDiff ℝ 2 A) (hφ : ∀ y, potentialComponent A 0 y = 0)
    (hdiv : ∀ y, lorenzDivergence A y = 0)
    (hper : ∀ (j : Fin 3) t, BoxPeriodic L (slice (potentialComponent A j.succ) t)) (t : ℝ) :
    ∫ x in boxSet L, energyDensity (fieldTensor A) (Fin.cons t x) =
      ∑' k, boxVolume L *
        ((∑ j : Fin 3,
            ‖deriv (fun s => boxCoeff L (slice (potentialComponent A j.succ) s) k) t‖ ^ 2 +
          boxFreq L k ^ 2 *
            ∑ j : Fin 3, ‖boxCoeff L (slice (potentialComponent A j.succ) t) k‖ ^ 2) / 2) :=
  (hasSum_fieldEnergy hL hA hφ hdiv hper t).tsum_eq.symm

/-- **The modes of a periodic field in the vacuum** (Landau–Lifshitz, §52). For a `C²` potential
in the gauge of Coulomb whose field satisfies the equations of Maxwell in the vacuum and whose
spatial components are periodic in space, every coefficient `aⱼ,k(t)` has the derivative
`ȧⱼ,k = (∂ₜaⱼ)_k`, with `d/dt ȧⱼ,k = −ω_k² aⱼ,k`, and the coefficients are transverse:
`K · a_k = 0`. -/
theorem hasDerivAt_boxCoeff_of_maxwell {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) {A : Potential}
    (hA : ContDiff ℝ 2 A) (hφ : ∀ y, potentialComponent A 0 y = 0)
    (hdiv : ∀ y, lorenzDivergence A y = 0) (hvac : ∀ y, VacuumMaxwellAt A y)
    (hper : ∀ (j : Fin 3) t, BoxPeriodic L (slice (potentialComponent A j.succ) t))
    (k : Fin 3 → ℤ) (t : ℝ) :
    (∀ j : Fin 3,
      HasDerivAt (fun s => boxCoeff L (slice (potentialComponent A j.succ) s) k)
          (boxCoeff L (slice (partialAt (potentialComponent A j.succ) 0) t) k) t ∧
        HasDerivAt (fun s => boxCoeff L (slice (partialAt (potentialComponent A j.succ) 0) s) k)
          (-(boxFreq L k : ℂ) ^ 2 * boxCoeff L (slice (potentialComponent A j.succ) t) k) t) ∧
      ∑ j : Fin 3, (boxWavevector L k j : ℂ) *
        boxCoeff L (slice (potentialComponent A j.succ) t) k = 0 := by
  have hb := (vacuumMaxwellAt_iff_box hA hdiv).mp hvac
  refine ⟨fun j => hasDerivAt_boxCoeff_of_box hL (contDiff_potentialComponent hA j.succ)
    (hper j) (fun y => hb y j.succ) k t, ?_⟩
  exact transverse_boxCoeff hL (fun j => (contDiff_potentialComponent hA j.succ).of_le
    (by norm_num)) hper (divergence3_of_coulomb hφ hdiv) t k

/-! ### The modes of the conducting box on the doubled periodic box -/

/-- A factor `a cos(πnt/L) + b sin(πnt/L)` has the period `2L`. -/
theorem trigFactor_add_two_mul {L : ℝ} (hL : L ≠ 0) (n : ℕ) (a b t : ℝ) (m : ℤ) :
    trigFactor (Real.pi * n / L) a b (t + m * (2 * L)) = trigFactor (Real.pi * n / L) a b t := by
  have h : Real.pi * n / L * (t + m * (2 * L)) =
      Real.pi * n / L * t + ((n * m : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    field_simp
  simp only [trigFactor, h, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-- The components of a mode of the conducting box are periodic in space with the periods
`2Lᵢ`: a mode of the box `[0, L₁] × [0, L₂] × [0, L₃]` is a field on the doubled periodic box. -/
theorem boxPeriodic_modeComponent {L : Fin 3 → ℝ} (hL : ∀ i, L i ≠ 0) (n : Fin 3 → ℕ)
    (c : Fin 3 → ℝ) (freq : ℝ) (j : Fin 3) (t : ℝ) :
    BoxPeriodic (fun i => 2 * L i) (slice (modeComponent L n c freq j) t) := by
  intro x m
  simp only [slice, modeComponent, trigProduct]
  refine Finset.prod_congr rfl fun ν _ => ?_
  refine Fin.cases ?_ (fun i => ?_) ν
  · simp only [Fin.cons_zero]
  · simp only [Fin.cons_succ, modeWavenumbers, wallWavenumber]
    exact trigFactor_add_two_mul (hL i) (n i) _ _ (x i) (m i)

/-- **The energy of a mode of the conducting box** on the doubled periodic box: a mode with
`Σᵢ (πnᵢ/Lᵢ) cᵢ = 0` satisfies the hypotheses of `hasSum_fieldEnergy` on the box with the sides
`2Lᵢ`. -/
theorem hasSum_fieldEnergy_conductingMode {L : Fin 3 → ℝ} (hL : ∀ i, 0 < L i) (n : Fin 3 → ℕ)
    {c : Fin 3 → ℝ} (freq : ℝ) (hc : ∑ i : Fin 3, wallWavenumber L n i * c i = 0) (t : ℝ) :
    HasSum (fun k => boxVolume (fun i => 2 * L i) *
        ((∑ j : Fin 3, ‖deriv (fun s => boxCoeff (fun i => 2 * L i)
              (slice (modeComponent L n c freq j) s) k) t‖ ^ 2 +
          boxFreq (fun i => 2 * L i) k ^ 2 * ∑ j : Fin 3,
            ‖boxCoeff (fun i => 2 * L i) (slice (modeComponent L n c freq j) t) k‖ ^ 2) / 2))
      (∫ x in boxSet (fun i => 2 * L i),
        energyDensity (fieldTensor (conductingMode L n c freq)) (Fin.cons t x)) := by
  have hL0 : ∀ i, L i ≠ 0 := fun i => (hL i).ne'
  have h := hasSum_fieldEnergy (L := fun i => 2 * L i) (fun i => by linarith [hL i])
    (contDiff_conductingMode L n c freq)
    (fun y => by rw [potentialComponent_conductingMode_zero])
    (fun y => by rw [lorenzDivergence_conductingMode, hc, neg_zero, zero_mul])
    (fun j t => by
      rw [potentialComponent_conductingMode_succ]
      exact boxPeriodic_modeComponent hL0 n c freq j t) t
  simpa only [potentialComponent_conductingMode_succ] using h

end ProjectAinos.Electrodynamics.CavityModes
