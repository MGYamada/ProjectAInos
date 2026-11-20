/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.PlaneWave
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Monochromatic plane waves

The potential of a monochromatic plane wave with the covector `ℓ` is the real part of
`(a + i b) e^{−iℓ(x)}` for a complex amplitude `a + i b`, that is `a cos(ℓx) + b sin(ℓx)`
(Landau–Lifshitz, *The Classical Theory of Fields*, §48). The forms of the project are real, so
`monochromatic ℓ a b` takes the complex amplitude as the pair `(a, b)` of real covectors; the
map `a + i b ↦ (a, b)` is a real linear equivalence, and the multiplication by `e^{−iθ}`, the
change of the phase, is the rotation `(a, b) ↦ (a cos θ + b sin θ, −a sin θ + b cos θ)`.

* `vacuum_monochromatic`: for a null `ℓ` and `⟨ℓ, a⟩ = ⟨ℓ, b⟩ = 0` both field equations hold in
  the vacuum; `planeWave_instance` is an instance of the hypotheses with a nonzero field.
* `fieldTensor_monochromatic_eq_iff`: for `ℓ ≠ 0` two amplitudes give the same field if and only if
  `a − a′` and `b − b′` are multiples of `ℓ`, and `monochromatic_eq_gaugeShift`: the gauge function
  `χ = c sin(ℓx) − d cos(ℓx)` realizes the shift by `(c ℓ, d ℓ)`.
* `finrank_polarization_quotient`: for a nonzero null `ℓ` the amplitudes with `⟨ℓ, a⟩ = 0` modulo
  the multiples of `ℓ` (`polarizations`, the kernel of `⟨ℓ, ·⟩` on the covectors modulo the
  multiples of `ℓ`, which is the image of `transverseAmplitudes ℓ` by `polarizations_eq_map`)
  form a space of dimension two: the two polarizations.
* `electricVector_monochromatic`: the electric field is `cos(ℓx) P + sin(ℓx) Q`, and
  `exists_phase_orthogonal`: a change of the phase makes the two vectors orthogonal; they are
  the axes of the ellipse of polarization (`norm_sq_phase_of_orthogonal`), which is a circle when
  they have the same length and a segment when one of them is zero.
* `frequency_boost`: the Doppler effect `κ′ = γ κ (1 − V cos θ)` for the observer with the
  velocity `V` along the first axis, with `cos θ = n₁`; `wavevector_boost` gives all the
  components of the covector for this observer.
-/

@[expose] public section

noncomputable section

open Set Filter Matrix Real
open scoped ContDiff Topology

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

/-! ### The potential -/

/-- The monochromatic plane wave `A = a cos(ℓx) + b sin(ℓx)`, the real part of
`(a + i b) e^{−iℓ(x)}` for the complex amplitude `a + i b`, represented by the pair `(a, b)` of
real covectors. -/
def monochromatic (ℓ a b : FourCovector) : Potential :=
  planeWave ℓ a Real.cos + planeWave ℓ b Real.sin

/-- The components `A_ν = a_ν cos(ℓx) + b_ν sin(ℓx)`. -/
theorem potentialComponent_monochromatic (ℓ a b : FourCovector) (ν : Fin 4) :
    potentialComponent (monochromatic ℓ a b) ν =
      fun y => a (Pi.single ν 1) * Real.cos (ℓ y) + b (Pi.single ν 1) * Real.sin (ℓ y) := by
  rw [monochromatic, potentialComponent_add, potentialComponent_planeWave,
    potentialComponent_planeWave]

/-- A monochromatic plane wave is smooth. -/
theorem contDiff_monochromatic {n : ℕ∞ω} (ℓ a b : FourCovector) :
    ContDiff ℝ n (monochromatic ℓ a b) :=
  (contDiff_planeWave ℓ a Real.contDiff_cos).add (contDiff_planeWave ℓ b Real.contDiff_sin)

/-- The field of a monochromatic plane wave: `F = −sin(ℓx) ℓ ∧ a + cos(ℓx) ℓ ∧ b`. -/
theorem fieldTensor_monochromatic (ℓ a b : FourCovector) (x v w : Spacetime) :
    fieldTensor (monochromatic ℓ a b) x ![v, w] =
      -Real.sin (ℓ x) * (ℓ v * a w - ℓ w * a v) + Real.cos (ℓ x) * (ℓ v * b w - ℓ w * b v) := by
  have hA : DifferentiableAt ℝ (planeWave ℓ a Real.cos) x :=
    (contDiff_planeWave (n := 1) ℓ a Real.contDiff_cos).differentiable one_ne_zero x
  have hB : DifferentiableAt ℝ (planeWave ℓ b Real.sin) x :=
    (contDiff_planeWave (n := 1) ℓ b Real.contDiff_sin).differentiable one_ne_zero x
  have hsum : fieldTensor (monochromatic ℓ a b) x ![v, w] =
      fieldTensor (planeWave ℓ a Real.cos) x ![v, w] +
        fieldTensor (planeWave ℓ b Real.sin) x ![v, w] := by
    rw [monochromatic, fieldTensor_apply, fieldTensor_apply, fieldTensor_apply, fderiv_add hA hB]
    simp only [_root_.add_apply, map_add]
    ring
  rw [hsum, fieldTensor_planeWave ℓ a Real.differentiableAt_cos,
    fieldTensor_planeWave ℓ b Real.differentiableAt_sin, Real.deriv_cos, Real.deriv_sin]

/-- A monochromatic plane wave with a null covector `ℓ` and `⟨ℓ, a⟩ = ⟨ℓ, b⟩ = 0` satisfies both
field equations in the vacuum: `dF = 0` and `d(−⋆F) = 0`, and in the frame of the co-ordinates
`div B = 0`, `∂ₜB + curl E = 0`, `div E = 0`, `curl B − ∂ₜE = 0`. -/
theorem vacuum_monochromatic {ℓ a b : FourCovector} (hnull : covectorInner ℓ ℓ = 0)
    (ha : covectorInner ℓ a = 0) (hb : covectorInner ℓ b = 0) :
    (∀ x, exteriorDerivative (fieldTensor (monochromatic ℓ a b)) x = 0) ∧
    (∀ x, exteriorDerivative (fun y => -star (fieldTensor (monochromatic ℓ a b) y)) x = 0) ∧
    ∀ x, (divergence3 (magneticField (fieldTensor (monochromatic ℓ a b))) x = 0 ∧
        ∀ i, partialAt (magneticField (fieldTensor (monochromatic ℓ a b)) i) 0 x +
          curl (electricField (fieldTensor (monochromatic ℓ a b))) x i = 0) ∧
      (divergence3 (electricField (fieldTensor (monochromatic ℓ a b))) x = 0 ∧
        ∀ i, curl (magneticField (fieldTensor (monochromatic ℓ a b))) x i -
          partialAt (electricField (fieldTensor (monochromatic ℓ a b)) i) 0 x = 0) := by
  have hA : ContDiff ℝ 2 (monochromatic ℓ a b) := contDiff_monochromatic ℓ a b
  have hcos : ContDiff ℝ 2 (planeWave ℓ a Real.cos) := contDiff_planeWave ℓ a Real.contDiff_cos
  have hsin : ContDiff ℝ 2 (planeWave ℓ b Real.sin) := contDiff_planeWave ℓ b Real.contDiff_sin
  refine ⟨fun x => bianchi_on _ isOpen_univ hA.contDiffOn (mem_univ x), ?_⟩
  have hL : ∀ y ∈ (univ : Set Spacetime), lorenzDivergence (monochromatic ℓ a b) y = 0 :=
    fun y _ => by
      rw [monochromatic, lorenzDivergence_add (hcos.differentiable (by norm_num) y)
        (hsin.differentiable (by norm_num) y), lorenzDivergence_planeWave ℓ a
        Real.differentiableAt_cos, lorenzDivergence_planeWave ℓ b Real.differentiableAt_sin, ha,
        hb]
      ring
  have hbox : ∀ ν y, box (potentialComponent (monochromatic ℓ a b) ν) y = 0 := fun ν y => by
    rw [monochromatic, potentialComponent_add,
      box_add (contDiffAt_potentialComponent hcos.contDiffAt ν)
        (contDiffAt_potentialComponent hsin.contDiffAt ν),
      box_planeWave ℓ a Real.contDiff_cos, box_planeWave ℓ b Real.contDiff_sin, hnull]
    ring
  have hbox' : ∀ y ∈ (univ : Set Spacetime),
      box (potentialComponent (monochromatic ℓ a b) 0) y = (fun _ => (0 : Spacetime)) y 0 ∧
        ∀ i : Fin 3, box (potentialComponent (monochromatic ℓ a b) i.succ) y =
          -(fun _ => (0 : Spacetime)) y i.succ := fun y _ =>
    ⟨by rw [hbox]; simp, fun i => by rw [hbox]; simp⟩
  have h := (maxwell_iff_box_of_lorenz isOpen_univ hA.contDiffOn hL _).mpr hbox'
  have he := (excitation_iff_box_of_lorenz isOpen_univ hA.contDiffOn hL _).mpr hbox'
  refine ⟨fun x => (he x (mem_univ x)).trans (matterCurrentForm_const_zero x), fun x => ?_⟩
  simpa using h x (mem_univ x)

/-- An instance of the hypotheses: the covector `ℓ = dt − dx¹` is null, the amplitude `a = dx²` is
transverse, and the plane wave `sin(ℓx) a` has a nonzero field at the origin. -/
theorem planeWave_instance :
    covectorInner (wavevector 1 ![1, 0, 0]) (wavevector 1 ![1, 0, 0]) = 0 ∧
      covectorInner (wavevector 1 ![1, 0, 0]) (ContinuousLinearMap.proj 2 : FourCovector) = 0 ∧
      fieldTensor (planeWave (wavevector 1 ![1, 0, 0]) (ContinuousLinearMap.proj 2 : FourCovector)
        Real.sin) 0 ≠ 0 := by
  refine ⟨covectorInner_wavevector_self 1 (by simp [Fin.sum_univ_three]), ?_, fun h => ?_⟩
  · rw [covectorInner_apply]
    simp [wavevector_apply, Fin.sum_univ_three]
  · have h1 := fieldTensor_planeWave (wavevector 1 ![1, 0, 0])
      (ContinuousLinearMap.proj 2 : FourCovector) Real.differentiableAt_sin
      (x := 0) (Pi.single 0 1) (Pi.single 2 1)
    rw [h] at h1
    simp [wavevector_apply, Fin.sum_univ_three, Real.deriv_sin] at h1

/-! ### The amplitudes modulo the gauge -/

/-- A two-form is determined by its values on pairs of vectors. -/
theorem twoForm_eq_of_apply_pair {F G : TwoForm} (h : ∀ v w, F ![v, w] = G ![v, w]) : F = G := by
  ext m
  have hm : m = ![m 0, m 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hm]
  exact h _ _

/-- The gauge function `χ = c sin(ℓx) − d cos(ℓx)` shifts the amplitudes by `(c ℓ, d ℓ)`. -/
theorem monochromatic_eq_gaugeShift (ℓ a b : FourCovector) (c d : ℝ) :
    monochromatic ℓ (a + c • ℓ) (b + d • ℓ) =
      gaugeShift (monochromatic ℓ a b) (fun y => c * Real.sin (ℓ y) - d * Real.cos (ℓ y)) := by
  funext y
  apply oneCovector.injective
  ext v
  have hs := ((Real.hasDerivAt_sin (ℓ y)).comp_hasFDerivAt y ℓ.hasFDerivAt).const_mul c
  have hc := ((Real.hasDerivAt_cos (ℓ y)).comp_hasFDerivAt y ℓ.hasFDerivAt).const_mul d
  have hχ : HasFDerivAt (fun z => c * Real.sin (ℓ z) - d * Real.cos (ℓ z)) _ y := hs.sub hc
  simp [monochromatic, planeWave, gaugeShift, hχ.fderiv]
  ring

/-- Two amplitudes give the same field if and only if they differ by multiples of `ℓ`, for
`ℓ ≠ 0`; the shift is the change of the gauge of `monochromatic_eq_gaugeShift`. -/
theorem fieldTensor_monochromatic_eq_iff {ℓ : FourCovector} (hℓ : ℓ ≠ 0)
    (a b a' b' : FourCovector) :
    fieldTensor (monochromatic ℓ a b) = fieldTensor (monochromatic ℓ a' b') ↔
      (∃ c : ℝ, a = a' + c • ℓ) ∧ ∃ d : ℝ, b = b' + d • ℓ := by
  constructor
  · intro h
    have hval : ∀ x v w, fieldTensor (monochromatic ℓ a b) x ![v, w] =
        fieldTensor (monochromatic ℓ a' b') x ![v, w] := fun x v w => by rw [h]
    simp only [fieldTensor_monochromatic] at hval
    obtain ⟨v₀, hv₀⟩ := exists_apply_eq_one hℓ
    have hb : ∀ v w, ℓ v * (b - b') w - ℓ w * (b - b') v = 0 := fun v w => by
      have h0 := hval 0 v w
      simp only [map_zero, Real.sin_zero, Real.cos_zero] at h0
      simp only [_root_.sub_apply]
      linarith
    have ha : ∀ v w, ℓ v * (a - a') w - ℓ w * (a - a') v = 0 := fun v w => by
      have h1 := hval ((π / 2) • v₀) v w
      simp only [map_smul, hv₀, smul_eq_mul, mul_one, Real.sin_pi_div_two,
        Real.cos_pi_div_two] at h1
      simp only [_root_.sub_apply]
      linarith
    obtain ⟨c, hc⟩ := exists_eq_smul_of_wedge_eq_zero hℓ ha
    obtain ⟨d, hd⟩ := exists_eq_smul_of_wedge_eq_zero hℓ hb
    exact ⟨⟨c, by rw [← hc, add_sub_cancel]⟩, ⟨d, by rw [← hd, add_sub_cancel]⟩⟩
  · rintro ⟨⟨c, rfl⟩, ⟨d, rfl⟩⟩
    rw [monochromatic_eq_gaugeShift]
    exact fieldTensor_gauge _ _ ((contDiff_monochromatic (n := 1) ℓ a' b').differentiable
      one_ne_zero) ((contDiff_const.mul (Real.contDiff_sin.comp ℓ.contDiff)).sub
        (contDiff_const.mul (Real.contDiff_cos.comp ℓ.contDiff)))

/-- The pairing with `ℓ` is the value on the raised vector `ℓ♯`. -/
theorem covectorInner_eq_apply_sharp (ℓ a : FourCovector) :
    covectorInner ℓ a = a (sharp .timeNegative ℓ) := by
  have hv : a (sharp .timeNegative ℓ) =
      ∑ μ : Fin 4, sharp .timeNegative ℓ μ * a (Pi.single μ 1) := by
    conv_lhs => rw [pi_eq_sum_univ' (sharp .timeNegative ℓ)]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [hv, covectorInner]
  exact Finset.sum_congr rfl fun μ _ => by rw [sharp_apply]

/-- The pairing `a ↦ ⟨ℓ, a⟩` with a covector `ℓ`, as a linear map. -/
def covectorInnerLeft (ℓ : FourCovector) : FourCovector →ₗ[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (sharp .timeNegative ℓ) : FourCovector →L[ℝ] ℝ).toLinearMap

/-- The linear map `covectorInnerLeft ℓ` is the pairing with `ℓ`. -/
theorem covectorInnerLeft_apply (ℓ a : FourCovector) :
    covectorInnerLeft ℓ a = covectorInner ℓ a :=
  (covectorInner_eq_apply_sharp ℓ a).symm

/-- The amplitudes `a` with `⟨ℓ, a⟩ = 0`, the condition of Lorenz on a plane wave with the
covector `ℓ`. -/
def transverseAmplitudes (ℓ : FourCovector) : Submodule ℝ FourCovector :=
  LinearMap.ker (covectorInnerLeft ℓ)

/-- An amplitude is transverse if and only if `⟨ℓ, a⟩ = 0`. -/
theorem mem_transverseAmplitudes (ℓ a : FourCovector) :
    a ∈ transverseAmplitudes ℓ ↔ covectorInner ℓ a = 0 := by
  rw [transverseAmplitudes, LinearMap.mem_ker, covectorInnerLeft_apply]

/-- For a null `ℓ` the multiples of `ℓ`, which are pure gauge, are transverse. -/
theorem span_le_transverseAmplitudes {ℓ : FourCovector} (hnull : covectorInner ℓ ℓ = 0) :
    Submodule.span ℝ {ℓ} ≤ transverseAmplitudes ℓ := by
  rw [Submodule.span_le, Set.singleton_subset_iff]
  exact (mem_transverseAmplitudes ℓ ℓ).mpr hnull

/-- The polarizations of a plane wave with a null covector `ℓ`: the transverse amplitudes modulo
the multiples of `ℓ`, as the kernel of `⟨ℓ, ·⟩` on the amplitudes modulo the multiples of `ℓ`
(`polarizations_eq_map`). -/
def polarizations (ℓ : FourCovector) (hnull : covectorInner ℓ ℓ = 0) :
    Submodule ℝ (FourCovector ⧸ Submodule.span ℝ {ℓ}) :=
  LinearMap.ker ((Submodule.span ℝ {ℓ}).liftQ (covectorInnerLeft ℓ)
    (span_le_transverseAmplitudes hnull))

/-- The polarizations are the image of the transverse amplitudes in the amplitudes modulo the
multiples of `ℓ`. -/
theorem polarizations_eq_map {ℓ : FourCovector} (hnull : covectorInner ℓ ℓ = 0) :
    polarizations ℓ hnull = (transverseAmplitudes ℓ).map (Submodule.span ℝ {ℓ}).mkQ := by
  ext q
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (Submodule.span ℝ {ℓ}) q
  rw [polarizations, LinearMap.mem_ker, Submodule.mkQ_apply]
  change covectorInnerLeft ℓ a = 0 ↔ _
  rw [Submodule.mem_map]
  constructor
  · intro h
    exact ⟨a, h, rfl⟩
  · rintro ⟨b, hb, hab⟩
    rw [Submodule.mkQ_apply, Submodule.Quotient.eq] at hab
    have h1 := span_le_transverseAmplitudes hnull hab
    rw [transverseAmplitudes, LinearMap.mem_ker, map_sub] at h1
    rw [transverseAmplitudes, LinearMap.mem_ker] at hb
    linarith

/-- The space of the covectors has the dimension four. -/
theorem finrank_fourCovector : Module.finrank ℝ FourCovector = 4 := by
  rw [← (LinearMap.toContinuousLinearMap :
    ((Fin 4 → ℝ) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] FourCovector).finrank_eq]
  simp

/-- There are two polarizations: for a nonzero null covector `ℓ`, the amplitudes with
`⟨ℓ, a⟩ = 0` modulo the multiples of `ℓ`, which are pure gauge by
`fieldTensor_monochromatic_eq_iff`, form a space of dimension two. -/
theorem finrank_polarization_quotient {ℓ : FourCovector} (hℓ : ℓ ≠ 0)
    (hnull : covectorInner ℓ ℓ = 0) : Module.finrank ℝ (polarizations ℓ hnull) = 2 := by
  have hsharp : sharp .timeNegative ℓ ≠ 0 := fun h =>
    hℓ ((sharp .timeNegative).injective (h.trans (map_zero _).symm))
  obtain ⟨μ, hμ⟩ : ∃ μ, sharp .timeNegative ℓ μ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hsharp (funext hc)
  let g := (Submodule.span ℝ {ℓ}).liftQ (covectorInnerLeft ℓ)
    (span_le_transverseAmplitudes hnull)
  have hsurj : Function.Surjective g := fun r =>
    ⟨Submodule.Quotient.mk ((r / sharp .timeNegative ℓ μ) • ContinuousLinearMap.proj μ), by
      change covectorInnerLeft ℓ ((r / sharp .timeNegative ℓ μ) • ContinuousLinearMap.proj μ) = r
      rw [map_smul, covectorInnerLeft_apply, covectorInner_eq_apply_sharp,
        ContinuousLinearMap.proj_apply, smul_eq_mul, div_mul_cancel₀ _ hμ]⟩
  have hrange : Module.finrank ℝ (LinearMap.range g) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have hquot : Module.finrank ℝ (FourCovector ⧸ Submodule.span ℝ {ℓ}) = 3 := by
    have h := Submodule.finrank_quotient_add_finrank (Submodule.span ℝ {ℓ})
    rw [finrank_span_singleton hℓ, finrank_fourCovector] at h
    omega
  have h := LinearMap.finrank_range_add_finrank_ker g
  rw [hrange, hquot] at h
  change Module.finrank ℝ (LinearMap.ker g) = 2
  omega

/-! ### The ellipse of polarization -/

/-- The electric components `ℓᵢ a₀ − ℓ₀ aᵢ` of `ℓ ∧ a`. -/
def electricAmplitude (ℓ a : FourCovector) : Fin 3 → ℝ := fun i =>
  ℓ (Pi.single i.succ 1) * a (Pi.single 0 1) - ℓ (Pi.single 0 1) * a (Pi.single i.succ 1)

/-- The electric field of a monochromatic plane wave is `cos(ℓx) P + sin(ℓx) Q` with the
constant vectors `P = E(ℓ ∧ b)` and `Q = −E(ℓ ∧ a)`. -/
theorem electricVector_monochromatic (ℓ a b : FourCovector) (x : Spacetime) :
    electricVector (fieldTensor (monochromatic ℓ a b) x) =
      Real.cos (ℓ x) • electricAmplitude ℓ b + Real.sin (ℓ x) • -electricAmplitude ℓ a := by
  ext i
  rw [electricVector_apply, component, fieldTensor_monochromatic]
  simp only [electricAmplitude, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

/-- The axes of the ellipse of polarization: for two vectors `p` and `q`, a change of the phase
by `θ` makes the vectors `p′ = p cos θ + q sin θ` and `q′ = −p sin θ + q cos θ` orthogonal, and
`p cos(φ + θ) + q sin(φ + θ) = p′ cos φ + q′ sin φ` for every phase `φ`. -/
theorem exists_phase_orthogonal (p q : Fin 3 → ℝ) :
    ∃ θ : ℝ, (Real.cos θ • p + Real.sin θ • q) ⬝ᵥ (-Real.sin θ • p + Real.cos θ • q) = 0 ∧
      ∀ φ : ℝ, Real.cos (φ + θ) • p + Real.sin (φ + θ) • q =
        Real.cos φ • (Real.cos θ • p + Real.sin θ • q) +
          Real.sin φ • (-Real.sin θ • p + Real.cos θ • q) := by
  let g : ℝ → ℝ := fun θ =>
    (Real.cos θ • p + Real.sin θ • q) ⬝ᵥ (-Real.sin θ • p + Real.cos θ • q)
  have hg : ∀ θ, g θ = Real.cos θ ^ 2 * (p ⬝ᵥ q) - Real.sin θ ^ 2 * (p ⬝ᵥ q) +
      Real.sin θ * Real.cos θ * (q ⬝ᵥ q - p ⬝ᵥ p) := fun θ => by
    simp only [g, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm q p]
    ring
  have hcont : Continuous g := by
    rw [funext hg]
    fun_prop
  have h0 : g 0 = p ⬝ᵥ q := by
    rw [hg]
    simp
  have hπ : g (π / 2) = -(p ⬝ᵥ q) := by
    rw [hg]
    simp
  obtain ⟨θ, -, hθ⟩ : ∃ θ ∈ Icc 0 (π / 2), g θ = 0 := by
    rcases le_total 0 (p ⬝ᵥ q) with h | h
    · exact intermediate_value_Icc' (by positivity) hcont.continuousOn
        ⟨by rw [hπ]; linarith, by rw [h0]; linarith⟩
    · exact intermediate_value_Icc (by positivity) hcont.continuousOn
        ⟨by rw [h0]; linarith, by rw [hπ]; linarith⟩
  refine ⟨θ, hθ, fun φ => ?_⟩
  rw [Real.cos_add, Real.sin_add]
  module

/-- The ellipse of polarization: for orthogonal axes `p` and `q`,
`|p cos φ + q sin φ|² = |p|² cos² φ + |q|² sin² φ`. -/
theorem dotProduct_self_phase_of_orthogonal {p q : Fin 3 → ℝ} (h : p ⬝ᵥ q = 0) (φ : ℝ) :
    (Real.cos φ • p + Real.sin φ • q) ⬝ᵥ (Real.cos φ • p + Real.sin φ • q) =
      Real.cos φ ^ 2 * (p ⬝ᵥ p) + Real.sin φ ^ 2 * (q ⬝ᵥ q) := by
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm q p, h]
  ring

/-- Circular polarization: for orthogonal axes of the same length the field has a constant
length. Linear polarization is the case `q = 0`. -/
theorem dotProduct_self_phase_of_circular {p q : Fin 3 → ℝ} (h : p ⬝ᵥ q = 0)
    (hpq : p ⬝ᵥ p = q ⬝ᵥ q) (φ : ℝ) :
    (Real.cos φ • p + Real.sin φ • q) ⬝ᵥ (Real.cos φ • p + Real.sin φ • q) = p ⬝ᵥ p := by
  rw [dotProduct_self_phase_of_orthogonal h, ← hpq]
  linear_combination (p ⬝ᵥ p) * Real.cos_sq_add_sin_sq φ

/-! ### The Doppler effect -/

/-- The covector `ℓ = κ (dt − ⟨n, dx⟩)` on the axes of the observer with the velocity `V` along the
first axis, which are the images of the axes under the boost with the velocity `−V`:
`ℓ′ = γ κ (1 − V n₁) dt′ − γ κ (n₁ − V) dx′¹ − κ n₂ dx′² − κ n₃ dx′³`. -/
theorem wavevector_boost (κ : ℝ) (n : Fin 3 → ℝ) (V : ℝ) (hV : |V| < 1) (v : Spacetime) :
    wavevector κ n ((boost (axisVelocity V hV).neg).val v) =
      (axisVelocity V hV).gamma * κ * (1 - V * n 0) * v 0 -
        ((axisVelocity V hV).gamma * κ * (n 0 - V) * v 1 + κ * n 1 * v 2 + κ * n 2 * v 3) := by
  rw [axisVelocity_neg V hV, boost_axisVelocity_apply, gamma_axisVelocity_neg V hV,
    wavevector_apply]
  simp [Fin.sum_univ_three]
  ring

/-- The Doppler effect: the observer with the velocity `V` along the first axis, whose
four-velocity is the image of the axis of the time under the boost with the velocity `−V`
(`boost_neg_single_zero`), measures the frequency `κ′ = γ κ (1 − V cos θ)` of the wave
`ℓ = κ (dt − ⟨n, dx⟩)`, where `cos θ = n₁` for a unit vector `n`. -/
theorem frequency_boost (κ : ℝ) (n : Fin 3 → ℝ) (V : ℝ) (hV : |V| < 1) :
    wavevector κ n ((boost (axisVelocity V hV).neg).val (Pi.single 0 1)) =
      (axisVelocity V hV).gamma * κ * (1 - V * n 0) := by
  rw [wavevector_boost]
  simp

end ProjectAinos.Electrodynamics
