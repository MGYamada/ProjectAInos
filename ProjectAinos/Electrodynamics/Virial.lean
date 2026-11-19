/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.ChargedDust
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# The virial theorem

For a tensor field `T^{μν}` on flat space-time, conserved on its first index, `Σ_μ ∂_μ T^{μν} = 0`,
the moment `∫ Σ_α x^α T^{0α} d³x` changes by the integral of the spatial trace `Σ_α T^{αα}`
(Landau–Lifshitz, *The Classical Theory of Fields*, §34). The time is the co-ordinate `0`, the
metric has the signature `(−+++)` and `c = 1`.

* `sliceIntegral f a b t`: the integral `∫ f d³x` over the spatial box of `[a, b]` at the time `t`.
* `integral_Icc_eq_intervalIntegral`: the integral over the box `[a, b]` of space-time is the
  integral over `[a⁰, b⁰]` of the integrals over the time slices.
* `virialMoment T a b t = ∫ Σ_α x^α T^{0α} d³x`, `spatialTrace T = Σ_α T^{αα}` and
  `fourTrace T = g_{μν} T^{μν} = −T^{00} + Σ_α T^{αα}`.
* `virial_box`: if `T` is `C¹`, conserved on the box and `T^{iα} = 0` on the faces `xⁱ = aⁱ, bⁱ`,
  then the moment at `b⁰` minus the moment at `a⁰` is the integral of the spatial trace over the
  box; `virialMoment_sub_eq_intervalIntegral` is the same with the integral over the time.
* `tendsto_average_spatialTrace`: if `T` is conserved for `t ≥ 0`, vanishes outside one fixed
  open spatial box for `t ≥ 0` and has a bounded moment, the time average over `[0, τ]` of
  `∫ Σ_α T^{αα} d³x` tends to `0` as `τ → ∞`.
* `tendsto_average_energy_add_fourTrace`: under the same hypotheses, the time average of
  `∫ T^{00} d³x + ∫ T^μ_μ d³x` tends to `0`: the averaged energy is minus the averaged integral
  of the four-trace.
* `fourTrace_raisedStress`: the four-trace of the stress of the field is zero, and
  `ChargedDust.fourTrace_matterStress`: that of dust with `g(U, U) = −1` is `−μ`.
* `ChargedDust.tendsto_average_energy_sub_restMass`: for charged dust that moves by the Lorentz
  force in its own field and stays in a box, the time average of the energy minus `∫ μ d³x` tends
  to `0` (L&L (34.4) for a smooth distribution of the charges).
  `ChargedDust.tendsto_average_energy_sub_restMass_static` is its instance: neutral dust at rest
  without a field.

The stress tensor is `C¹`; it need not be symmetric, since only the conservation on the first
index is used. The stress of point particles is a measure on their world lines and is outside
the scope. Finite motion is read as support in one fixed spatial box for `t ≥ 0` together with
a bounded moment; a version over all of space with decay rates is not proved here. Charged dust
of one species cannot be at rest, and free dust disperses, so the only proved instance of the
corollary for dust is static neutral dust without a field, for which the conclusion is
immediate; the improvement tensor of `VirialExamples` is an instance of the general theorem
with a nonzero spatial trace.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

/-! ### Integrals over the time slices -/

/-- The integral `∫ f d³x` over the spatial box of `[a, b]` at the time `t`. -/
def sliceIntegral (f : Spacetime → ℝ) (a b : Spacetime) (t : ℝ) : ℝ :=
  ∫ z in Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0), f (Fin.insertNth 0 t z)

/-- The charge of a current is the integral of its time component over the time slice. -/
theorem charge_eq_sliceIntegral (k : Spacetime → Spacetime) (a b : Spacetime) (t : ℝ) :
    charge k a b t = sliceIntegral (fun y => k y 0) a b t := rfl

/-- The theorem of Fubini for the time: the integral over the box `[a, b]` of space-time is the
integral over `[a⁰, b⁰]` of the integrals over the time slices. -/
theorem integral_Icc_eq_intervalIntegral {f : Spacetime → ℝ} {a b : Spacetime} (hle : a ≤ b)
    (hf : IntegrableOn f (Icc a b)) :
    ∫ y in Icc a b, f y = ∫ t in a 0..b 0, sliceIntegral f a b t := by
  set e : ℝ × (Fin 3 → ℝ) ≃ᵐ Spacetime :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm _
  have heI : e ⁻¹' Icc a b =
      Icc (a 0) (b 0) ×ˢ Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0) :=
    ((Fin.insertNthOrderIso (fun _ => ℝ) 0).preimage_Icc _ _).trans (Icc_prod_eq _ _)
  rw [← hem.map_eq, setIntegral_map_equiv, heI, Measure.volume_eq_prod, setIntegral_prod,
    intervalIntegral.integral_of_le (hle 0), ← integral_Icc_eq_integral_Ioc]
  · rfl
  · have h := hf
    rwa [← hem.integrableOn_comp_preimage e.measurableEmbedding, heI] at h

/-! ### The moment and the traces -/

/-- The moment current `P^μ = Σ_α x^α T^{μα}` of a tensor field `T^{μν}`. -/
def momentCurrent (T : Fin 4 → Fin 4 → Spacetime → ℝ) : Spacetime → Spacetime :=
  fun y μ => ∑ α : Fin 3, y α.succ * T μ α.succ y

/-- The virial moment `∫ Σ_α x^α T^{0α} d³x` in the spatial box of `[a, b]` at the time `t`. -/
def virialMoment (T : Fin 4 → Fin 4 → Spacetime → ℝ) (a b : Spacetime) (t : ℝ) : ℝ :=
  charge (momentCurrent T) a b t

/-- The spatial trace `Σ_α T^{αα}`. -/
def spatialTrace (T : Fin 4 → Fin 4 → Spacetime → ℝ) (y : Spacetime) : ℝ :=
  ∑ α : Fin 3, T α.succ α.succ y

/-- The four-trace `g_{μν} T^{μν} = −T^{00} + Σ_α T^{αα}`. -/
def fourTrace (T : Fin 4 → Fin 4 → Spacetime → ℝ) (y : Spacetime) : ℝ :=
  -T 0 0 y + spatialTrace T y

/-- The four-trace is the trace with the metric. -/
theorem fourTrace_eq (T : Fin 4 → Fin 4 → Spacetime → ℝ) (y : Spacetime) :
    fourTrace T y = ∑ μ : Fin 4, lorentzSign .timeNegative μ * T μ μ y := by
  rw [Fin.sum_univ_succ, lorentzSign_zero, fourTrace, spatialTrace]
  simp only [lorentzSign_succ, one_mul]
  ring

/-- The energy density and the four-trace add up to the spatial trace. -/
theorem energy_add_fourTrace (T : Fin 4 → Fin 4 → Spacetime → ℝ) (y : Spacetime) :
    T 0 0 y + fourTrace T y = spatialTrace T y := by
  rw [fourTrace]
  ring

/-! ### The derivative of the moment current -/

namespace Virial

/-- The derivative of a finite sum is the sum of the derivatives. -/
theorem partialAt_sum {ι : Type*} (s : Finset ι) {f : ι → Spacetime → ℝ} {x : Spacetime}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) (μ : Fin 4) :
    partialAt (fun y => ∑ i ∈ s, f i y) μ x = ∑ i ∈ s, partialAt (f i) μ x := by
  rw [partialAt, fderiv_fun_sum hf]
  simp only [FunLike.coe_sum, Finset.sum_apply]
  rfl

/-- The derivative of a co-ordinate: `∂_μ x^β = δ_μ^β`. -/
theorem partialAt_coordinate (β μ : Fin 4) (x : Spacetime) :
    partialAt (fun y => y β) μ x = if μ = β then 1 else 0 := by
  have hd : HasFDerivAt (fun y : Spacetime => y β)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) β) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) β).hasFDerivAt
  rw [partialAt, hd.fderiv, ContinuousLinearMap.proj_apply, Pi.single_apply]
  by_cases h : μ = β
  · simp [h]
  · simp [h, Ne.symm h]

end Virial

open Virial

/-- The moment current of a `Cⁿ` tensor field is `Cⁿ`. -/
theorem contDiff_momentCurrent {n : ℕ∞ω} {T : Fin 4 → Fin 4 → Spacetime → ℝ}
    (hT : ∀ μ ν, ContDiff ℝ n (T μ ν)) : ContDiff ℝ n (momentCurrent T) :=
  contDiff_pi.mpr fun μ => ContDiff.sum fun α _ =>
    (contDiff_apply ℝ (fun _ => ℝ) α.succ).mul (hT μ α.succ)

/-- The divergence of the moment current: `∂_μ (Σ_α x^α T^{μα}) = Σ_α T^{αα} +
Σ_α x^α ∂_μ T^{μα}`. -/
theorem divergence4_momentCurrent {T : Fin 4 → Fin 4 → Spacetime → ℝ} {x : Spacetime}
    (hT : ∀ μ ν, DifferentiableAt ℝ (T μ ν) x) :
    divergence4 (momentCurrent T) x = spatialTrace T x +
      ∑ α : Fin 3, x α.succ * ∑ μ : Fin 4, partialAt (T μ α.succ) μ x := by
  have hc : ∀ β : Fin 4, DifferentiableAt ℝ (fun y : Spacetime => y β) x := fun β =>
    differentiableAt_apply β x
  have hP : DifferentiableAt ℝ (momentCurrent T) x :=
    differentiableAt_pi.mpr fun μ => DifferentiableAt.fun_sum fun α _ =>
      (hc α.succ).mul (hT μ α.succ)
  have hd : ∀ μ : Fin 4, partialAt (fun y => momentCurrent T y μ) μ x =
      ∑ α : Fin 3, (x α.succ * partialAt (T μ α.succ) μ x +
        T μ α.succ x * if μ = α.succ then 1 else 0) := by
    intro μ
    rw [show (fun y => momentCurrent T y μ) = fun y => ∑ α : Fin 3, y α.succ * T μ α.succ y
      from rfl, partialAt_sum _ fun α _ => (hc α.succ).mul (hT μ α.succ)]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [partialAt_mul (hc α.succ) (hT μ α.succ), partialAt_coordinate]
  rw [divergence4_eq hP, Finset.sum_congr rfl fun μ _ => hd μ, Finset.sum_comm]
  simp only [Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, ← Finset.mul_sum, spatialTrace]
  ring

/-! ### The virial theorem on a box -/

/-- The virial theorem on a box `[a, b]` of space-time: for a `C¹` tensor field `T` with
`Σ_μ ∂_μ T^{μν} = 0` on the box and `T^{iα} = 0` on the faces `xⁱ = aⁱ, bⁱ`, the moment
`∫ Σ_α x^α T^{0α} d³x` at the time `b⁰` minus that at `a⁰` is the integral of `Σ_α T^{αα}` over
the box. -/
theorem virial_box {T : Fin 4 → Fin 4 → Spacetime → ℝ} (hT : ∀ μ ν, ContDiff ℝ 1 (T μ ν))
    {a b : Spacetime} (hle : a ≤ b)
    (hcons : ∀ y ∈ Icc a b, ∀ ν, ∑ μ : Fin 4, partialAt (T μ ν) μ y = 0)
    (hface : ∀ y ∈ Icc a b, ∀ i : Fin 3, (y i.succ = a i.succ ∨ y i.succ = b i.succ) →
      ∀ α : Fin 3, T i.succ α.succ y = 0) :
    virialMoment T a b (b 0) - virialMoment T a b (a 0) = ∫ y in Icc a b, spatialTrace T y := by
  have h := box_divergence (contDiff_momentCurrent hT) hle
  have hflux : ∀ i : Fin 3, faceFlux (momentCurrent T) a b i.succ = 0 := by
    intro i
    have h1 : ∀ c : ℝ, (c = a i.succ ∨ c = b i.succ) →
        ∫ z in Icc (a ∘ i.succ.succAbove) (b ∘ i.succ.succAbove),
          momentCurrent T (Fin.insertNth i.succ c z) i.succ = 0 := by
      intro c hc
      refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => ?_
      have hcI : c ∈ Icc (a i.succ) (b i.succ) := by
        rcases hc with hc | hc <;> rw [hc]
        · exact ⟨le_rfl, hle _⟩
        · exact ⟨hle _, le_rfl⟩
      have hmem : Fin.insertNth i.succ c z ∈ Icc a b := Fin.insertNth_mem_Icc.mpr ⟨hcI, hz⟩
      refine Finset.sum_eq_zero fun α _ => ?_
      rw [hface _ hmem i (by rwa [Fin.insertNth_apply_same]) α, mul_zero]
    rw [faceFlux, h1 _ (Or.inr rfl), h1 _ (Or.inl rfl), sub_zero]
  have hdiv : ∀ y ∈ Icc a b, divergence4 (momentCurrent T) y = spatialTrace T y := by
    intro y hy
    rw [divergence4_momentCurrent fun μ ν => (hT μ ν).differentiable one_ne_zero y]
    simp [hcons y hy]
  rw [Finset.sum_eq_zero fun i _ => hflux i, add_zero,
    setIntegral_congr_fun measurableSet_Icc hdiv] at h
  exact h

/-- The spatial trace of a continuous tensor field is continuous. -/
theorem continuous_spatialTrace {T : Fin 4 → Fin 4 → Spacetime → ℝ}
    (hT : ∀ μ ν, Continuous (T μ ν)) : Continuous (spatialTrace T) :=
  continuous_finsetSum _ fun α _ => hT α.succ α.succ

/-- The virial theorem on a box with the integral over the time: the moment at `b⁰` minus that
at `a⁰` is `∫_{a⁰}^{b⁰} (∫ Σ_α T^{αα} d³x) dt`. -/
theorem virialMoment_sub_eq_intervalIntegral {T : Fin 4 → Fin 4 → Spacetime → ℝ}
    (hT : ∀ μ ν, ContDiff ℝ 1 (T μ ν)) {a b : Spacetime} (hle : a ≤ b)
    (hcons : ∀ y ∈ Icc a b, ∀ ν, ∑ μ : Fin 4, partialAt (T μ ν) μ y = 0)
    (hface : ∀ y ∈ Icc a b, ∀ i : Fin 3, (y i.succ = a i.succ ∨ y i.succ = b i.succ) →
      ∀ α : Fin 3, T i.succ α.succ y = 0) :
    virialMoment T a b (b 0) - virialMoment T a b (a 0) =
      ∫ t in a 0..b 0, sliceIntegral (spatialTrace T) a b t := by
  rw [virial_box hT hle hcons hface, integral_Icc_eq_intervalIntegral hle]
  exact (continuous_spatialTrace fun μ ν => (hT μ ν).continuous).continuousOn.integrableOn_compact
    isCompact_Icc

/-! ### The time average -/

/-- A continuous function is integrable on the spatial box of every time slice. -/
theorem integrableOn_slice {f : Spacetime → ℝ} (hf : Continuous f) (a b : Spacetime) (t : ℝ) :
    IntegrableOn (fun z => f (Fin.insertNth 0 t z))
      (Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0)) :=
  (hf.comp (Continuous.finInsertNth 0 continuous_const continuous_id)).continuousOn
    |>.integrableOn_compact isCompact_Icc

/-- The integral over the time slices is additive for continuous functions. -/
theorem sliceIntegral_add {f g : Spacetime → ℝ} (hf : Continuous f) (hg : Continuous g)
    (a b : Spacetime) (t : ℝ) :
    sliceIntegral (fun y => f y + g y) a b t = sliceIntegral f a b t + sliceIntegral g a b t :=
  integral_add (integrableOn_slice hf a b t) (integrableOn_slice hg a b t)

/-- Changing the time co-ordinate of a corner does not change the spatial box. -/
theorem update_zero_comp_succAbove (a : Spacetime) (s : ℝ) :
    Function.update a 0 s ∘ Fin.succAbove 0 = a ∘ Fin.succAbove 0 :=
  funext fun j => Function.update_of_ne (Fin.succAbove_ne 0 j) s a

/-- The integral over a time slice depends only on the spatial box. -/
theorem sliceIntegral_update (f : Spacetime → ℝ) (a b : Spacetime) (s s' t : ℝ) :
    sliceIntegral f (Function.update a 0 s) (Function.update b 0 s') t =
      sliceIntegral f a b t := by
  rw [sliceIntegral, sliceIntegral, update_zero_comp_succAbove, update_zero_comp_succAbove]

/-- The virial moment depends only on the spatial box. -/
theorem virialMoment_update (T : Fin 4 → Fin 4 → Spacetime → ℝ) (a b : Spacetime)
    (s s' t : ℝ) :
    virialMoment T (Function.update a 0 s) (Function.update b 0 s') t = virialMoment T a b t :=
  sliceIntegral_update (fun y => momentCurrent T y 0) a b s s' t

/-- The virial theorem for a system in finite motion (Landau–Lifshitz §34): if a `C¹`
tensor field `T` is conserved for `t ≥ 0`, vanishes for `t ≥ 0` outside the open spatial box of
`[a, b]`, and its moment `∫ Σ_α x^α T^{0α} d³x` is bounded for `t ≥ 0`, then the time average
over `[0, τ]` of `∫ Σ_α T^{αα} d³x` tends to `0` as `τ → ∞`. -/
theorem tendsto_average_spatialTrace {T : Fin 4 → Fin 4 → Spacetime → ℝ}
    (hT : ∀ μ ν, ContDiff ℝ 1 (T μ ν)) {a b : Spacetime}
    (hab : ∀ i : Fin 3, a i.succ ≤ b i.succ)
    (hcons : ∀ y : Spacetime, 0 ≤ y 0 → ∀ ν, ∑ μ : Fin 4, partialAt (T μ ν) μ y = 0)
    (hsupp : ∀ y : Spacetime, 0 ≤ y 0 →
      (∃ i : Fin 3, y i.succ ≤ a i.succ ∨ b i.succ ≤ y i.succ) → ∀ μ ν, T μ ν y = 0)
    {B : ℝ} (hB : ∀ t : ℝ, 0 ≤ t → |virialMoment T a b t| ≤ B) :
    Tendsto (fun τ : ℝ => (1 / τ) * ∫ t in (0 : ℝ)..τ, sliceIntegral (spatialTrace T) a b t)
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun τ : ℝ => (2 * B) / τ) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
  have hlo : ∀ i : Fin 3, Function.update a 0 0 i.succ = a i.succ := fun i =>
    Function.update_of_ne (Fin.succ_ne_zero i) _ _
  have hhi : ∀ i : Fin 3, Function.update b 0 τ i.succ = b i.succ := fun i =>
    Function.update_of_ne (Fin.succ_ne_zero i) _ _
  have hle : Function.update a 0 0 ≤ Function.update b 0 τ := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · rw [Function.update_self, Function.update_self]
      exact hτ.le
    · rw [hlo, hhi]
      exact hab i
  have ht : ∀ y ∈ Icc (Function.update a 0 0) (Function.update b 0 τ), 0 ≤ y 0 := by
    intro y hy
    have h0 := hy.1 0
    rwa [Function.update_self] at h0
  have hcons' : ∀ y ∈ Icc (Function.update a 0 0) (Function.update b 0 τ), ∀ ν,
      ∑ μ : Fin 4, partialAt (T μ ν) μ y = 0 := fun y hy => hcons y (ht y hy)
  have hface : ∀ y ∈ Icc (Function.update a 0 0) (Function.update b 0 τ), ∀ i : Fin 3,
      (y i.succ = Function.update a 0 0 i.succ ∨ y i.succ = Function.update b 0 τ i.succ) →
      ∀ α : Fin 3, T i.succ α.succ y = 0 := by
    intro y hy i hyi α
    refine hsupp y (ht y hy) ⟨i, ?_⟩ _ _
    rw [hlo, hhi] at hyi
    rcases hyi with h | h
    · exact Or.inl h.le
    · exact Or.inr h.ge
  have h := virialMoment_sub_eq_intervalIntegral hT hle hcons' hface
  rw [Function.update_self, Function.update_self, virialMoment_update, virialMoment_update] at h
  simp only [sliceIntegral_update] at h
  rw [← h, Real.norm_eq_abs, abs_mul, abs_of_pos (one_div_pos.mpr hτ), one_div, inv_mul_eq_div]
  have h1 : |virialMoment T a b τ - virialMoment T a b 0| ≤ 2 * B := by
    have := abs_sub (virialMoment T a b τ) (virialMoment T a b 0)
    linarith [hB τ hτ.le, hB 0 le_rfl]
  exact div_le_div_of_nonneg_right h1 hτ.le

/-- The energy and the four-trace (Landau–Lifshitz §34): under the hypotheses of
`tendsto_average_spatialTrace`, the time average over `[0, τ]` of
`∫ T^{00} d³x + ∫ T^μ_μ d³x` tends to `0`, so the averaged energy is minus the averaged integral of
the four-trace. -/
theorem tendsto_average_energy_add_fourTrace {T : Fin 4 → Fin 4 → Spacetime → ℝ}
    (hT : ∀ μ ν, ContDiff ℝ 1 (T μ ν)) {a b : Spacetime}
    (hab : ∀ i : Fin 3, a i.succ ≤ b i.succ)
    (hcons : ∀ y : Spacetime, 0 ≤ y 0 → ∀ ν, ∑ μ : Fin 4, partialAt (T μ ν) μ y = 0)
    (hsupp : ∀ y : Spacetime, 0 ≤ y 0 →
      (∃ i : Fin 3, y i.succ ≤ a i.succ ∨ b i.succ ≤ y i.succ) → ∀ μ ν, T μ ν y = 0)
    {B : ℝ} (hB : ∀ t : ℝ, 0 ≤ t → |virialMoment T a b t| ≤ B) :
    Tendsto (fun τ : ℝ => (1 / τ) * ∫ t in (0 : ℝ)..τ,
      (sliceIntegral (T 0 0) a b t + sliceIntegral (fourTrace T) a b t)) atTop (𝓝 0) := by
  have hc : ∀ μ ν, Continuous (T μ ν) := fun μ ν => (hT μ ν).continuous
  have hfour : Continuous (fourTrace T) :=
    (hc 0 0).neg.add (continuous_spatialTrace hc)
  have heq : ∀ t : ℝ, sliceIntegral (T 0 0) a b t + sliceIntegral (fourTrace T) a b t =
      sliceIntegral (spatialTrace T) a b t := by
    intro t
    rw [← sliceIntegral_add (hc 0 0) hfour]
    simp only [energy_add_fourTrace]
  simp only [heq]
  exact tendsto_average_spatialTrace hT hab hcons hsupp hB

/-! ### The field and charged dust -/

/-- The four-trace `g_{μν} T_EM^{μν}` of the stress tensor of the field is zero. -/
theorem fourTrace_raisedStress (F : Field) (y : Spacetime) : fourTrace (raisedStress F) y = 0 := by
  rw [fourTrace_eq, ← stressForm_trace (F y)]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [raisedStress, ← mul_assoc, ← mul_assoc, lorentzSign_sq, one_mul]

/-- The components of the stress tensor of a `Cⁿ` field are `Cⁿ`. -/
theorem Virial.contDiff_raisedStress {n : ℕ∞ω} {F : Field} (hF : ContDiff ℝ n F) (μ ν : Fin 4) :
    ContDiff ℝ n (raisedStress F μ ν) := by
  refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν
  · rw [raisedStress_zero_zero]
    exact contDiff_energyDensity hF
  · rw [raisedStress_zero_succ]
    exact contDiff_poyntingVector hF j
  · rw [raisedStress_succ_zero]
    exact contDiff_poyntingVector hF i
  · rw [raisedStress_succ_succ]
    exact contDiff_maxwellStress hF i j

namespace ChargedDust

/-- The total stress `T^{μν} = T_EM^{μν} + T_m^{μν}` of the field `F` and of the dust. -/
def totalStress (D : ChargedDust) (F : Field) : Fin 4 → Fin 4 → Spacetime → ℝ :=
  fun μ ν y => raisedStress F μ ν y + D.matterStress μ ν y

/-- The components of the stress of `Cⁿ` dust are `Cⁿ`. -/
theorem contDiff_matterStress {n : ℕ∞ω} {D : ChargedDust} (hμ : ContDiff ℝ n D.massDensity)
    (hU : ContDiff ℝ n D.velocity) (μ ν : Fin 4) : ContDiff ℝ n (D.matterStress μ ν) :=
  (hμ.mul (contDiff_pi.mp hU μ)).mul (contDiff_pi.mp hU ν)

/-- The four-trace `g_{μν} μ U^μ U^ν` of the stress of dust with `g(U, U) = −1` is `−μ`. -/
theorem fourTrace_matterStress (D : ChargedDust) {y : Spacetime}
    (hU : minkowskiForm .timeNegative 3 (D.velocity y) (D.velocity y) = -1) :
    fourTrace D.matterStress y = -D.massDensity y := by
  rw [minkowskiForm_apply] at hU
  rw [fourTrace_eq]
  calc ∑ μ : Fin 4, lorentzSign .timeNegative μ * D.matterStress μ μ y
      = D.massDensity y * ∑ μ : Fin 4,
          lorentzSign .timeNegative μ * (D.velocity y μ * D.velocity y μ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun μ _ => ?_
        simp only [matterStress]
        ring
    _ = -D.massDensity y := by
        rw [hU]
        ring

/-- The four-trace of the total stress is that of the dust. -/
theorem fourTrace_totalStress (D : ChargedDust) (F : Field) {y : Spacetime}
    (hU : minkowskiForm .timeNegative 3 (D.velocity y) (D.velocity y) = -1) :
    fourTrace (D.totalStress F) y = -D.massDensity y := by
  have h : fourTrace (D.totalStress F) y =
      fourTrace (raisedStress F) y + fourTrace D.matterStress y := by
    simp only [fourTrace, spatialTrace, totalStress, Finset.sum_add_distrib]
    ring
  rw [h, fourTrace_raisedStress, fourTrace_matterStress D hU, zero_add]

/-- The virial theorem for charged dust in its own field (Landau–Lifshitz (34.4) for a smooth
distribution of the charges): if `C¹` dust with `g(U, U) = −1` conserves its mass and moves by
the Lorentz force, its `C¹` field satisfies the equations of Maxwell with the current of the
dust, the total stress vanishes outside the open spatial box of `[a, b]` and its moment is
bounded, all for `t ≥ 0`, then the time average over `[0, τ]` of the energy `∫ T^{00} d³x`
minus `∫ μ d³x` tends to `0`. The integral `∫ μ d³x` of the density of the rest mass is
`Σ m √(1 − v²)` for particles. The only proved instance is
`tendsto_average_energy_sub_restMass_static`: neutral dust at rest without a field. -/
theorem tendsto_average_energy_sub_restMass {F : Field} {D : ChargedDust}
    (hF : ContDiff ℝ 1 F) (hμ : ContDiff ℝ 1 D.massDensity) (hU : ContDiff ℝ 1 D.velocity)
    (hcont : ∀ y : Spacetime, 0 ≤ y 0 →
      ∑ l : Fin 4, partialAt (fun z => D.massDensity z * D.velocity z l) l y = 0)
    (hmotion : ∀ y : Spacetime, 0 ≤ y 0 → ∀ ν : Fin 4, D.massDensity y * D.convective y ν =
      lorentzForce (D.chargeDensity y) (F y) (D.velocity y) ν)
    (hgB : ∀ y : Spacetime, 0 ≤ y 0 → divergence3 (magneticField F) y = 0)
    (hfar : ∀ y : Spacetime, 0 ≤ y 0 → ∀ i,
      partialAt (magneticField F i) 0 y + curl (electricField F) y i = 0)
    (hgE : ∀ y : Spacetime, 0 ≤ y 0 → divergence3 (electricField F) y = D.current y 0)
    (hamp : ∀ y : Spacetime, 0 ≤ y 0 → ∀ i,
      curl (magneticField F) y i - partialAt (electricField F i) 0 y = D.current y i.succ)
    (hnorm : ∀ y : Spacetime, 0 ≤ y 0 →
      minkowskiForm .timeNegative 3 (D.velocity y) (D.velocity y) = -1)
    {a b : Spacetime} (hab : ∀ i : Fin 3, a i.succ ≤ b i.succ)
    (hsupp : ∀ y : Spacetime, 0 ≤ y 0 →
      (∃ i : Fin 3, y i.succ ≤ a i.succ ∨ b i.succ ≤ y i.succ) →
        ∀ μ ν, D.totalStress F μ ν y = 0)
    {B : ℝ} (hB : ∀ t : ℝ, 0 ≤ t → |virialMoment (D.totalStress F) a b t| ≤ B) :
    Tendsto (fun τ : ℝ => (1 / τ) * ∫ t in (0 : ℝ)..τ,
      (sliceIntegral (D.totalStress F 0 0) a b t - sliceIntegral D.massDensity a b t))
      atTop (𝓝 0) := by
  have hR : ∀ μ ν, ContDiff ℝ 1 (raisedStress F μ ν) := Virial.contDiff_raisedStress hF
  have hM : ∀ μ ν, ContDiff ℝ 1 (D.matterStress μ ν) := contDiff_matterStress hμ hU
  have hT : ∀ μ ν, ContDiff ℝ 1 (D.totalStress F μ ν) := fun μ ν => (hR μ ν).add (hM μ ν)
  have hcons : ∀ y : Spacetime, 0 ≤ y 0 → ∀ ν,
      ∑ μ : Fin 4, partialAt (D.totalStress F μ ν) μ y = 0 := by
    intro y hy ν
    have hsplit : ∀ μ : Fin 4, partialAt (D.totalStress F μ ν) μ y =
        partialAt (raisedStress F μ ν) μ y + partialAt (D.matterStress μ ν) μ y := fun μ =>
      partialAt_add ((hR μ ν).differentiable one_ne_zero y)
        ((hM μ ν).differentiable one_ne_zero y) μ
    rw [Finset.sum_congr rfl fun μ _ => hsplit μ, Finset.sum_add_distrib]
    have hUc : ∀ l : Fin 4, ContDiff ℝ 1 fun z => D.velocity z l := contDiff_pi.mp hU
    exact total_stress_conserved (hF.differentiable one_ne_zero y)
      (fun l => (hμ.mul (hUc l)).differentiable one_ne_zero y)
      (fun l => (hUc l).differentiable one_ne_zero y) (hcont y hy) (hmotion y hy) (hgB y hy)
      (hfar y hy) (hgE y hy) (hamp y hy) ν
  have h := tendsto_average_energy_add_fourTrace hT hab hcons hsupp hB
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hτ.le] at ht
  have hslice : sliceIntegral (fourTrace (D.totalStress F)) a b t =
      -sliceIntegral D.massDensity a b t := by
    rw [sliceIntegral, sliceIntegral, ← integral_neg]
    congr 1
    funext z
    refine fourTrace_totalStress D F (hnorm _ ?_)
    rw [Fin.insertNth_apply_same]
    exact ht.1
  simp only [hslice, sub_eq_add_neg]

/-- Neutral dust at rest with the density `μ₀` of the rest mass. -/
def staticNeutral (μ₀ : Spacetime → ℝ) : ChargedDust where
  massDensity := μ₀
  chargeDensity := fun _ => 0
  velocity := fun _ => Pi.single 0 1

/-- The instance of `tendsto_average_energy_sub_restMass`: neutral dust at rest, with a `C¹`
density `μ₀` that does not depend on the time and vanishes outside the open spatial box of
`[a, b]`, and without a field, satisfies all its hypotheses. Its energy is `∫ μ₀ d³x`, so the
conclusion holds trivially here. -/
theorem tendsto_average_energy_sub_restMass_static {μ₀ : Spacetime → ℝ}
    (hμ₀ : ContDiff ℝ 1 μ₀) (hstat : ∀ y : Spacetime, partialAt μ₀ 0 y = 0) {a b : Spacetime}
    (hab : ∀ i : Fin 3, a i.succ ≤ b i.succ)
    (hsupp : ∀ y : Spacetime, 0 ≤ y 0 →
      (∃ i : Fin 3, y i.succ ≤ a i.succ ∨ b i.succ ≤ y i.succ) → μ₀ y = 0) :
    Tendsto (fun τ : ℝ => (1 / τ) * ∫ t in (0 : ℝ)..τ,
      (sliceIntegral ((staticNeutral μ₀).totalStress (fun _ => 0) 0 0) a b t -
        sliceIntegral (staticNeutral μ₀).massDensity a b t)) atTop (𝓝 0) := by
  have hzero : ∀ μ ν y, raisedStress (fun _ : Spacetime => (0 : TwoForm)) μ ν y = 0 := by
    intro μ ν y
    simp [raisedStress, stressForm, covectorPairing, tensorContraction, component,
      raisedComponent]
  have hE : ∀ i, electricField (fun _ : Spacetime => (0 : TwoForm)) i =
      fun _ => electricVector 0 i := fun i => rfl
  have hB : ∀ i, magneticField (fun _ : Spacetime => (0 : TwoForm)) i =
      fun _ => magneticVector 0 i := fun i => rfl
  have hk : ∀ y μ, (staticNeutral μ₀).current y μ = 0 := fun y μ => by
    simp [current, staticNeutral]
  have hT : ∀ y μ ν, (staticNeutral μ₀).totalStress (fun _ => 0) μ ν y =
      μ₀ y * (Pi.single 0 1 : Spacetime) μ * (Pi.single 0 1 : Spacetime) ν := fun y μ ν => by
    rw [totalStress, hzero, zero_add]
    rfl
  refine tendsto_average_energy_sub_restMass (B := 0) contDiff_const hμ₀ contDiff_const
    (fun y _ => ?_) (fun y _ ν => ?_) (fun y _ => ?_) (fun y _ i => ?_) (fun y _ => ?_)
    (fun y _ i => ?_) (fun y _ => ?_) hab (fun y hy hout μ ν => ?_) (fun t _ => ?_)
  · rw [Fin.sum_univ_succ]
    have h0 : (fun z => (staticNeutral μ₀).massDensity z * (staticNeutral μ₀).velocity z 0) =
        μ₀ := by
      funext z
      simp [staticNeutral]
    have hs : ∀ i : Fin 3, (fun z => (staticNeutral μ₀).massDensity z *
        (staticNeutral μ₀).velocity z i.succ) = fun _ => 0 := fun i => by
      funext z
      simp [staticNeutral]
    rw [h0, hstat]
    simp [hs, partialAt_const]
  · simp [convective, staticNeutral, partialAt_const, lorentzForce]
  · simp [divergence3, hB, partialAt_const]
  · fin_cases i <;> simp [curl, hE, hB, partialAt_const]
  · simp [divergence3, hE, partialAt_const, hk]
  · fin_cases i <;> simp [curl, hE, hB, partialAt_const, hk]
  · change minkowskiForm .timeNegative 3 (Pi.single 0 1) (Pi.single 0 1) = -1
    rw [minkowskiForm_single]
    simp [lorentzSign]
  · rw [hT, hsupp y hy hout, zero_mul, zero_mul]
  · have hm : ∀ y, momentCurrent ((staticNeutral μ₀).totalStress (fun _ => 0)) y 0 = 0 := by
      intro y
      simp [momentCurrent, hT]
    simp [virialMoment, charge, hm]

end ChargedDust

end ProjectAinos.Electrodynamics
