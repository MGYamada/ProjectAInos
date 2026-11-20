/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Wave.RetardedIntegral
public import ProjectAinos.Electrodynamics.CavityModes
import Mathlib.Tactic

/-!
# The retarded potentials

The units have `div E = k⁰` and `c = 1`. For a current `k = (k⁰, 𝐤)` on flat space-time the
**retarded potential** (`retardedPotential`) is `A = −φ dt + 𝐚 · d𝐱` with

  `φ(t, x) = ∫ k⁰(t − ‖y‖, x − y)/(4π‖y‖) dy`,  `𝐚(t, x) = ∫ 𝐤(t − ‖y‖, x − y)/(4π‖y‖) dy`

(Landau–Lifshitz, *The Classical Theory of Fields*, §62). The integrals are the retarded integrals
of `SmoothGeometry.Wave.RetardedIntegral`, carried to `Spacetime` by the splitting
`Wave.timeSpaceEquiv` (`retardedScalar`, `retardedScalar_eq`). The current is admissible if it is
`C²` and, written in `(t, x)`, has subluminal support `‖x‖ ≤ R + v₀|t|` with `v₀ < 1`.

* `box_comp_timeSpaceEquiv`: the wave operator `box = −∂₀² + Δ` of a function of `(t, x)` is
  `−(∂ₜ² − Δ)`, and `box_retardedScalar`: `box (Rg) = −g`.
* `partialAt_retardedScalar`: the derivatives commute with the retarded integral, and
  `lorenz_retardedPotential`: **the gauge of Lorenz** `∂^μ A_μ = ∂ₜφ + div 𝐚 = 0` for a conserved
  current `∂_μ k^μ = 0`.
* `box_retardedPotential`: `box A₀ = k⁰` and `box aᵢ = −kⁱ`, and with the gauge of Lorenz
  `maxwell_retardedPotential`: **the field of the retarded potential satisfies the equations of
  Maxwell** with the current `k` (`maxwell_iff_box_of_lorenz`), and
  `excitation_retardedPotential`: the equation of the forms `d(−⋆dA) = −ι_k vol`
  (`excitation_iff_box_of_lorenz`).
* `retardedPotential_eq_zero_of_le`: causal support, a current that vanishes up to the time `T`
  gives a potential that vanishes up to `T`; `Wave.retardedIntegral_eq_zero_of_support` gives the
  general statement for the past light cone.
* `eq_zero_of_wave_eq_zero`: **uniqueness**, a `C²` solution of `box u = 0` that vanishes up to a
  time and whose spatial support is bounded on every finite interval of time vanishes, from the
  energy identity `eq_zero_of_box_eq_zero`; `eq_retardedScalar` and `eq_retardedPotential`: for a
  current that vanishes in the past, the retarded potential is the only such solution.
* An instance: `circulatingCurrent` `= (∂₁χ, −∂₀χ, 0, 0)` for a smooth bump `χ` is a smooth
  conserved current of compact support (`contDiff_circulatingCurrent`,
  `hasCompactSupport_circulatingCurrent`, `divergence4_circulatingCurrent`) that does not vanish
  (`circulatingCurrent_ne_zero`), and `maxwell_retardedPotential_circulatingCurrent` applies the
  theorem to it.

The uniqueness class is that of the solutions that vanish in the past, so it applies to currents
that vanish in the past; a current with subluminal support for all times has the retarded
potential as a solution, but the statement of uniqueness does not cover it.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The wave operator in time and space -/

/-- The wave operator of a function of `(t, x)` pulled back to space-time:
`box (u ∘ split) = −(∂ₜ² − Δ) u ∘ split`. -/
theorem box_comp_timeSpaceEquiv {u : ℝ × E3 → ℝ} (hu : ContDiff ℝ 2 u) (v : Spacetime) :
    box (fun w => u (Wave.timeSpaceEquiv w)) v =
      -Wave.waveOperator u (Wave.timeSpaceEquiv v) := by
  have hu1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have ht : Differentiable ℝ (Wave.timeDeriv u) :=
    (Wave.contDiff_timeDeriv (n := 1) hu).differentiable (by norm_num)
  have hs : ∀ i, Differentiable ℝ (Wave.spaceDeriv i u) := fun i =>
    (Wave.contDiff_spaceDeriv (n := 1) hu i).differentiable (by norm_num)
  have h0 : partialAt (fun w => u (Wave.timeSpaceEquiv w)) 0 =
      fun w => Wave.timeDeriv u (Wave.timeSpaceEquiv w) :=
    Wave.fderiv_comp_timeSpaceEquiv_zero hu1
  have hi : ∀ i : Fin 3, partialAt (fun w => u (Wave.timeSpaceEquiv w)) i.succ =
      fun w => Wave.spaceDeriv i u (Wave.timeSpaceEquiv w) := fun i =>
    Wave.fderiv_comp_timeSpaceEquiv_succ hu1 i
  have h00 : partialAt (fun w => Wave.timeDeriv u (Wave.timeSpaceEquiv w)) 0 v =
      Wave.timeDeriv (Wave.timeDeriv u) (Wave.timeSpaceEquiv v) :=
    congrFun (Wave.fderiv_comp_timeSpaceEquiv_zero ht) v
  have hii : ∀ i : Fin 3, partialAt (fun w => Wave.spaceDeriv i u (Wave.timeSpaceEquiv w))
      i.succ v = Wave.spaceDeriv i (Wave.spaceDeriv i u) (Wave.timeSpaceEquiv v) := fun i =>
    congrFun (Wave.fderiv_comp_timeSpaceEquiv_succ (hs i) i) v
  simp only [box, h0, hi, h00, hii, Wave.waveOperator]
  ring

/-! ### The retarded integral on space-time -/

/-- The retarded integral `∫ g(v − (‖y‖, y))/(4π‖y‖) dy` of a function on space-time, through the
splitting `v ↦ (v⁰, 𝐯)` (`retardedScalar_eq`). -/
def retardedScalar (g : Spacetime → ℝ) (v : Spacetime) : ℝ :=
  Wave.retardedIntegral (fun p => g (Wave.timeSpaceEquiv.symm p)) (Wave.timeSpaceEquiv v)

/-- The retarded integral on space-time is `∫ g(v − (‖y‖, y))/(4π‖y‖) dy`. -/
theorem retardedScalar_eq (g : Spacetime → ℝ) (v : Spacetime) :
    retardedScalar g v = ∫ y : E3, g (v - Minkowski.vector ‖y‖ y) / (4 * Real.pi * ‖y‖) := by
  rw [retardedScalar, Wave.retardedIntegral_comp_symm]
  simp only [smul_eq_mul, div_eq_inv_mul]

/-- The derivative of a function of space-time written in `(t, x)`. -/
theorem fderiv_comp_timeSpaceEquiv_symm {g : Spacetime → ℝ} (hg : Differentiable ℝ g)
    (p w : ℝ × E3) :
    fderiv ℝ (fun q => g (Wave.timeSpaceEquiv.symm q)) p w =
      fderiv ℝ g (Wave.timeSpaceEquiv.symm p) (Wave.timeSpaceEquiv.symm w) := by
  have h := (hg _).hasFDerivAt.comp p Wave.timeSpaceEquiv.symm.hasFDerivAt
  rw [show (fun q => g (Wave.timeSpaceEquiv.symm q)) = g ∘ Wave.timeSpaceEquiv.symm from rfl,
    h.fderiv]
  rfl

/-- The retarded integral of a `Cⁿ` function with subluminal support is `Cⁿ`. -/
theorem contDiff_retardedScalar {n : ℕ∞} {g : Spacetime → ℝ} (hg : ContDiff ℝ n g) {R v₀ : ℝ}
    (hs : Wave.SubluminalSupport R v₀ fun p => g (Wave.timeSpaceEquiv.symm p)) :
    ContDiff ℝ n (retardedScalar g) :=
  (Wave.contDiff_retardedIntegral (hg.comp Wave.timeSpaceEquiv.symm.contDiff) hs).comp
    Wave.timeSpaceEquiv.contDiff

/-- The retarded integral of a `C²` function with subluminal support is `C²`. -/
theorem contDiff_two_retardedScalar {g : Spacetime → ℝ} (hg : ContDiff ℝ 2 g) {R v₀ : ℝ}
    (hs : Wave.SubluminalSupport R v₀ fun p => g (Wave.timeSpaceEquiv.symm p)) :
    ContDiff ℝ 2 (retardedScalar g) := by
  have h := contDiff_retardedScalar (n := 2) (by exact_mod_cast hg) hs
  exact_mod_cast h

/-- **The retarded integral solves the wave equation**: `box (Rg) = −g`, that is
`(∂ₜ² − Δ)(Rg) = g`, for a `C²` function `g` with subluminal support. -/
theorem box_retardedScalar {g : Spacetime → ℝ} (hg : ContDiff ℝ 2 g) {R v₀ : ℝ}
    (hs : Wave.SubluminalSupport R v₀ fun p => g (Wave.timeSpaceEquiv.symm p)) (v : Spacetime) :
    box (retardedScalar g) v = -g v := by
  have hg' : ContDiff ℝ 2 fun p => g (Wave.timeSpaceEquiv.symm p) :=
    hg.comp Wave.timeSpaceEquiv.symm.contDiff
  have hu : ContDiff ℝ 2 (Wave.retardedIntegral fun p => g (Wave.timeSpaceEquiv.symm p)) := by
    have h := Wave.contDiff_retardedIntegral (n := 2) (by exact_mod_cast hg') hs
    exact_mod_cast h
  rw [show retardedScalar g = fun w => Wave.retardedIntegral
      (fun p => g (Wave.timeSpaceEquiv.symm p)) (Wave.timeSpaceEquiv w) from rfl,
    box_comp_timeSpaceEquiv hu, Wave.wave_retardedIntegral hg' hs,
    ContinuousLinearEquiv.symm_apply_apply]

/-- The derivatives commute with the retarded integral on space-time. -/
theorem partialAt_retardedScalar {g : Spacetime → ℝ} (hg : ContDiff ℝ 1 g) {R v₀ : ℝ}
    (hs : Wave.SubluminalSupport R v₀ fun p => g (Wave.timeSpaceEquiv.symm p)) (μ : Fin 4) :
    partialAt (retardedScalar g) μ = retardedScalar (partialAt g μ) := by
  funext v
  have hg' : ContDiff ℝ 1 fun p => g (Wave.timeSpaceEquiv.symm p) :=
    hg.comp Wave.timeSpaceEquiv.symm.contDiff
  have hu : Differentiable ℝ (Wave.retardedIntegral fun p => g (Wave.timeSpaceEquiv.symm p)) :=
    fun p => (Wave.hasFDerivAt_retardedIntegral hg' hs p).differentiableAt
  rw [partialAt, show retardedScalar g = fun w => Wave.retardedIntegral
      (fun p => g (Wave.timeSpaceEquiv.symm p)) (Wave.timeSpaceEquiv w) from rfl,
    Wave.fderiv_comp_timeSpaceEquiv (hu _), Wave.fderiv_retardedIntegral hg' hs,
    Wave.retardedIntegral_apply_clm (hg'.continuous_fderiv (by norm_num)) hs.fderiv]
  simp only [retardedScalar, partialAt]
  congr 1
  funext p
  rw [fderiv_comp_timeSpaceEquiv_symm (hg.differentiable (by norm_num)),
    ContinuousLinearEquiv.symm_apply_apply]

/-- The retarded integral of a function that vanishes up to the time `T` vanishes up to `T`. -/
theorem retardedScalar_eq_zero_of_le {g : Spacetime → ℝ} {T : ℝ}
    (hpast : ∀ v : Spacetime, v 0 ≤ T → g v = 0) {v : Spacetime} (hv : v 0 ≤ T) :
    retardedScalar g v = 0 :=
  Wave.retardedIntegral_eq_zero_of_le (fun _ hq => hpast _ hq) hv

/-- A component of a function with subluminal support has subluminal support. -/
theorem subluminalSupport_component {k : Spacetime → Spacetime} {R v₀ : ℝ}
    (hs : Wave.SubluminalSupport R v₀ fun p => k (Wave.timeSpaceEquiv.symm p)) (μ : Fin 4) :
    Wave.SubluminalSupport R v₀ fun p => k (Wave.timeSpaceEquiv.symm p) μ :=
  hs.mono (tsupport_comp_subset (g := fun x : Spacetime => x μ) rfl _)

/-! ### The retarded potential -/

/-- The **retarded potential** `A = −φ dt + 𝐚 · d𝐱` of a current `k = (k⁰, 𝐤)`, with
`φ = ∫ k⁰(t − ‖y‖, x − y)/(4π‖y‖) dy` and `𝐚 = ∫ 𝐤(t − ‖y‖, x − y)/(4π‖y‖) dy`. -/
def retardedPotential (k : Spacetime → Spacetime) : Potential :=
  potentialOf (retardedScalar fun w => k w 0) fun v i => retardedScalar (fun w => k w i.succ) v

/-- The time component of the retarded potential is `−φ = −R k⁰`. -/
theorem potentialComponent_retardedPotential_zero (k : Spacetime → Spacetime) :
    potentialComponent (retardedPotential k) 0 = fun v => -retardedScalar (fun w => k w 0) v :=
  CavityModes.potentialComponent_potentialOf_zero _ _

/-- The spatial components of the retarded potential are `aᵢ = R kⁱ`. -/
theorem potentialComponent_retardedPotential_succ (k : Spacetime → Spacetime) (i : Fin 3) :
    potentialComponent (retardedPotential k) i.succ = retardedScalar fun w => k w i.succ :=
  CavityModes.potentialComponent_potentialOf_succ _ _ i

/-- The retarded potential of a `C²` current with subluminal support is `C²`. -/
theorem contDiff_retardedPotential {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k)
    {R v₀ : ℝ} (hs : Wave.SubluminalSupport R v₀ fun p => k (Wave.timeSpaceEquiv.symm p)) :
    ContDiff ℝ 2 (retardedPotential k) := by
  have hc : ∀ μ : Fin 4, ContDiff ℝ 2 fun w => k w μ := fun μ =>
    (ContinuousLinearMap.proj μ : Spacetime →L[ℝ] ℝ).contDiff.comp hk
  exact CavityModes.contDiff_potentialOf
    (contDiff_two_retardedScalar (hc 0) (subluminalSupport_component hs 0)) fun i =>
      contDiff_two_retardedScalar (hc i.succ) (subluminalSupport_component hs i.succ)

/-- The derivative of a component of a vector field is the component of its derivative. -/
theorem partialAt_component_eq {k : Spacetime → Spacetime} {v : Spacetime}
    (hk : DifferentiableAt ℝ k v) (μ ν : Fin 4) :
    partialAt (fun w => k w μ) ν v = fderiv ℝ k v (Pi.single ν 1) μ := by
  have h := (ContinuousLinearMap.proj μ : Spacetime →L[ℝ] ℝ).hasFDerivAt.comp v hk.hasFDerivAt
  rw [partialAt, show (fun w => k w μ) =
    (ContinuousLinearMap.proj μ : Spacetime →L[ℝ] ℝ) ∘ k from rfl, h.fderiv]
  rfl

/-- The derivative of a function with subluminal support has subluminal support. -/
theorem subluminalSupport_partialAt {g : Spacetime → ℝ} (hg : Differentiable ℝ g) {R v₀ : ℝ}
    (hs : Wave.SubluminalSupport R v₀ fun p => g (Wave.timeSpaceEquiv.symm p)) (μ : Fin 4) :
    Wave.SubluminalSupport R v₀ fun p => partialAt g μ (Wave.timeSpaceEquiv.symm p) := by
  have h : (fun p => partialAt g μ (Wave.timeSpaceEquiv.symm p)) = fun p =>
      fderiv ℝ (fun q => g (Wave.timeSpaceEquiv.symm q)) p (Wave.timeSpaceEquiv (Pi.single μ 1)) :=
    funext fun p => by
      rw [fderiv_comp_timeSpaceEquiv_symm hg, ContinuousLinearEquiv.symm_apply_apply]
      rfl
  rw [h]
  exact hs.mono (tsupport_fderiv_apply_subset ℝ _)

/-- The retarded integral on space-time commutes with finite sums. -/
theorem retardedScalar_finsetSum {ι : Type*} (s : Finset ι) {F : ι → Spacetime → ℝ}
    (hc : ∀ i ∈ s, Continuous (F i)) {R v₀ : ℝ}
    (hs : ∀ i ∈ s, Wave.SubluminalSupport R v₀ fun p => F i (Wave.timeSpaceEquiv.symm p))
    (v : Spacetime) :
    retardedScalar (fun w => ∑ i ∈ s, F i w) v = ∑ i ∈ s, retardedScalar (F i) v :=
  Wave.retardedIntegral_finsetSum s fun i hi =>
    (hs i hi).integrable ((hc i hi).comp Wave.timeSpaceEquiv.symm.continuous) _

/-- The four-divergence `∂_μ k^μ` is the sum of the derivatives of the components. -/
theorem divergence4_eq_sum_partialAt {k : Spacetime → Spacetime} {v : Spacetime}
    (hk : DifferentiableAt ℝ k v) :
    divergence4 k v = ∑ μ : Fin 4, partialAt (fun w => k w μ) μ v := by
  simp only [divergence4, partialAt_component_eq hk]

/-- **The gauge of Lorenz**: the retarded potential of a conserved current, `∂_μ k^μ = 0`, of class
`C²` and with subluminal support satisfies `∂^μ A_μ = ∂ₜφ + div 𝐚 = 0`. -/
theorem lorenz_retardedPotential {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k) {R v₀ : ℝ}
    (hs : Wave.SubluminalSupport R v₀ fun p => k (Wave.timeSpaceEquiv.symm p))
    (hdiv : ∀ v, divergence4 k v = 0) (v : Spacetime) :
    lorenzDivergence (retardedPotential k) v = 0 := by
  have hc : ∀ μ : Fin 4, ContDiff ℝ 2 fun w => k w μ := fun μ =>
    (ContinuousLinearMap.proj μ : Spacetime →L[ℝ] ℝ).contDiff.comp hk
  have hc1 : ∀ μ : Fin 4, ContDiff ℝ 1 fun w => k w μ := fun μ => (hc μ).of_le (by norm_num)
  have hp : ∀ μ : Fin 4, partialAt (retardedScalar fun w => k w μ) μ v =
      retardedScalar (partialAt (fun w => k w μ) μ) v := fun μ =>
    congrFun (partialAt_retardedScalar (hc1 μ) (subluminalSupport_component hs μ) μ) v
  have hsum := retardedScalar_finsetSum Finset.univ
    (F := fun μ : Fin 4 => partialAt (fun w => k w μ) μ)
    (fun μ _ => (contDiff_partialAt_of_le (m := 0) (hc1 μ) (by norm_num) μ).continuous)
    (fun μ _ => subluminalSupport_partialAt ((hc1 μ).differentiable (by norm_num))
      (subluminalSupport_component hs μ) μ) v
  have hzero : (fun w => ∑ μ : Fin 4, partialAt (fun w => k w μ) μ w) = fun _ => 0 :=
    funext fun w => by
      rw [← divergence4_eq_sum_partialAt ((hk.differentiable (by norm_num)) w), hdiv]
  rw [hzero, Fin.sum_univ_succ] at hsum
  simp only [← hp] at hsum
  have h0 : retardedScalar (fun _ => (0 : ℝ)) v = 0 := Wave.retardedIntegral_zero _
  rw [lorenzDivergence, potentialComponent_retardedPotential_zero, partialAt_neg]
  simp only [potentialComponent_retardedPotential_succ]
  linarith

/-- The retarded potential solves the wave equations `box A₀ = k⁰` and `box aᵢ = −kⁱ`, that is
`box A_ν = −k_ν`. -/
theorem box_retardedPotential {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k) {R v₀ : ℝ}
    (hs : Wave.SubluminalSupport R v₀ fun p => k (Wave.timeSpaceEquiv.symm p)) (v : Spacetime) :
    box (potentialComponent (retardedPotential k) 0) v = k v 0 ∧
      ∀ i : Fin 3, box (potentialComponent (retardedPotential k) i.succ) v = -k v i.succ := by
  have hc : ∀ μ : Fin 4, ContDiff ℝ 2 fun w => k w μ := fun μ =>
    (ContinuousLinearMap.proj μ : Spacetime →L[ℝ] ℝ).contDiff.comp hk
  refine ⟨?_, fun i => ?_⟩
  · rw [potentialComponent_retardedPotential_zero, box_neg,
      box_retardedScalar (hc 0) (subluminalSupport_component hs 0), neg_neg]
  · rw [potentialComponent_retardedPotential_succ,
      box_retardedScalar (hc i.succ) (subluminalSupport_component hs i.succ)]

/-- **The equations of Maxwell for the retarded potential**: for a conserved current `k` of class
`C²` with subluminal support, the field of the retarded potential satisfies `div B = 0`,
`∂ₜB + curl E = 0`, `div E = k⁰` and `curl B − ∂ₜE = 𝐤`. -/
theorem maxwell_retardedPotential {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k) {R v₀ : ℝ}
    (hs : Wave.SubluminalSupport R v₀ fun p => k (Wave.timeSpaceEquiv.symm p))
    (hdiv : ∀ v, divergence4 k v = 0) (y : Spacetime) :
    (divergence3 (magneticField (fieldTensor (retardedPotential k))) y = 0 ∧
        ∀ i, partialAt (magneticField (fieldTensor (retardedPotential k)) i) 0 y +
          curl (electricField (fieldTensor (retardedPotential k))) y i = 0) ∧
      (divergence3 (electricField (fieldTensor (retardedPotential k))) y = k y 0 ∧
        ∀ i, curl (magneticField (fieldTensor (retardedPotential k))) y i -
          partialAt (electricField (fieldTensor (retardedPotential k)) i) 0 y = k y i.succ) :=
  (maxwell_iff_box_of_lorenz isOpen_univ (contDiff_retardedPotential hk hs).contDiffOn
    (fun v _ => lorenz_retardedPotential hk hs hdiv v) k).mpr
    (fun v _ => box_retardedPotential hk hs v) y (mem_univ y)

/-- **The equation of the forms for the retarded potential**: `d(−⋆dA) = −ι_k vol` for a conserved
current `k` of class `C²` with subluminal support. -/
theorem excitation_retardedPotential {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k)
    {R v₀ : ℝ} (hs : Wave.SubluminalSupport R v₀ fun p => k (Wave.timeSpaceEquiv.symm p))
    (hdiv : ∀ v, divergence4 k v = 0) (y : Spacetime) :
    exteriorDerivative (fun z => -star (fieldTensor (retardedPotential k) z)) y =
      SourcedAction.matterCurrentForm k y :=
  (excitation_iff_box_of_lorenz isOpen_univ (contDiff_retardedPotential hk hs).contDiffOn
    (fun v _ => lorenz_retardedPotential hk hs hdiv v) k).mpr
    (fun v _ => box_retardedPotential hk hs v) y (mem_univ y)

/-- **Causal support of the potential**: the retarded potential of a current that vanishes up to
the time `T` vanishes up to `T`. -/
theorem retardedPotential_eq_zero_of_le {k : Spacetime → Spacetime} {T : ℝ}
    (hpast : ∀ v : Spacetime, v 0 ≤ T → k v = 0) {v : Spacetime} (hv : v 0 ≤ T) :
    retardedPotential k v = 0 := by
  have h : ∀ μ : Fin 4, retardedScalar (fun w => k w μ) v = 0 := fun μ =>
    retardedScalar_eq_zero_of_le (fun w hw => by rw [hpast w hw]; rfl) hv
  simp [retardedPotential, potentialOf, h]

/-! ### Uniqueness -/

/-- The derivatives of a translate are the translates of the derivatives. -/
theorem partialAt_comp_add_right (f : Spacetime → ℝ) (c : Spacetime) (μ : Fin 4) :
    partialAt (fun z => f (z + c)) μ = fun z => partialAt f μ (z + c) :=
  funext fun z => by simp only [partialAt, fderiv_comp_add_right]

/-- The wave operator commutes with translations. -/
theorem box_comp_add_right (f : Spacetime → ℝ) (c z : Spacetime) :
    box (fun z => f (z + c)) z = box f (z + c) := by
  simp only [box, partialAt_comp_add_right]

/-- **Uniqueness for the wave equation**: a `C²` solution of `box u = 0` that vanishes up to the
time `T₀` and whose spatial support is bounded on every finite interval of time vanishes. The
proof translates the initial time to `T₀ − 1` and applies the energy identity
`eq_zero_of_box_eq_zero`. -/
theorem eq_zero_of_wave_eq_zero {u : Spacetime → ℝ} (hu : ContDiff ℝ 2 u) {T₀ : ℝ}
    (hbox : ∀ y, box u y = 0) (hpast : ∀ y : Spacetime, y 0 ≤ T₀ → u y = 0)
    (hsupp : ∀ T : ℝ, ∃ ρ : ℝ, ∀ y : Spacetime, T₀ ≤ y 0 → y 0 ≤ T → u y ≠ 0 →
      ∀ i : Fin 3, |y i.succ| < ρ) (y : Spacetime) : u y = 0 := by
  by_cases hy : y 0 ≤ T₀
  · exact hpast y hy
  rw [not_le] at hy
  obtain ⟨ρ, hρ⟩ := hsupp (y 0)
  set c : Spacetime := Pi.single 0 (T₀ - 1) with hc
  have hc0 : ∀ z : Spacetime, (z + c) 0 = z 0 + (T₀ - 1) := fun z => by simp [hc]
  have hci : ∀ (z : Spacetime) (i : Fin 3), (z + c) i.succ = z i.succ := fun z i => by
    simp [hc, Fin.succ_ne_zero]
  have hu' : ContDiff ℝ 2 fun z => u (z + c) := hu.comp (contDiff_id.add contDiff_const)
  have key := eq_zero_of_box_eq_zero hu' (T := y 0 - T₀ + 1) (R := ρ)
    (fun z _ _ => by rw [box_comp_add_right]; exact hbox _)
    (fun z hz0 hzT hne i => by
      have hT₀ : T₀ ≤ (z + c) 0 := by
        by_contra h
        exact hne (hpast _ (le_of_lt (not_le.mp h)))
      rw [← hci z i]
      exact hρ _ hT₀ (by rw [hc0]; linarith) hne i)
    (fun z hz => hpast _ (by rw [hc0, hz]; linarith))
    (fun z hz => by
      rw [partialAt_comp_add_right]
      refine partialAt_eq_zero_of_eventually 0 ((hu.differentiable (by norm_num)) _) ?_
      filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
        (show (0 : ℝ) < 1 by norm_num)] with s hs
      refine hpast _ ?_
      have : (z + c + s • (Pi.single 0 1 : Spacetime)) 0 = z 0 + (T₀ - 1) + s := by
        simp [hc]
      rw [this, hz]
      linarith [hs.2])
    (y - c) (by simp [hc]; linarith) (by simp [hc])
  simpa using key

/-- **Uniqueness of the retarded solution**: a `C²` solution of `box u = −g` (that is,
`(∂ₜ² − Δ) u = g`) that vanishes up to the time `T₀`, like the source `g`, and whose spatial
support is bounded on every finite interval of time is the retarded integral of `g`. -/
theorem eq_retardedScalar {g u : Spacetime → ℝ} (hg : ContDiff ℝ 2 g) {R v₀ : ℝ}
    (hs : Wave.SubluminalSupport R v₀ fun p => g (Wave.timeSpaceEquiv.symm p)) {T₀ : ℝ}
    (hgpast : ∀ y : Spacetime, y 0 ≤ T₀ → g y = 0) (hu : ContDiff ℝ 2 u)
    (hbox : ∀ y, box u y = -g y) (hupast : ∀ y : Spacetime, y 0 ≤ T₀ → u y = 0)
    (husupp : ∀ T : ℝ, ∃ ρ : ℝ, ∀ y : Spacetime, T₀ ≤ y 0 → y 0 ≤ T → u y ≠ 0 →
      ∀ i : Fin 3, |y i.succ| < ρ) : u = retardedScalar g := by
  have hR := contDiff_two_retardedScalar hg hs
  have hw : ContDiff ℝ 2 fun z => u z - retardedScalar g z := hu.sub hR
  have hbw : ∀ y, box (fun z => u z - retardedScalar g z) y = 0 := fun y => by
    have h := box_add hu.contDiffAt (hR.neg.contDiffAt (x := y))
    simp only [← sub_eq_add_neg] at h
    rw [h, box_neg, hbox, box_retardedScalar hg hs]
    ring
  have hpw : ∀ y : Spacetime, y 0 ≤ T₀ → u y - retardedScalar g y = 0 := fun y hy => by
    rw [hupast y hy, retardedScalar_eq_zero_of_le hgpast hy, sub_zero]
  have hsw : ∀ T : ℝ, ∃ ρ : ℝ, ∀ y : Spacetime, T₀ ≤ y 0 → y 0 ≤ T →
      u y - retardedScalar g y ≠ 0 → ∀ i : Fin 3, |y i.succ| < ρ := fun T => by
    obtain ⟨ρ₁, hρ₁⟩ := husupp T
    refine ⟨max ρ₁ (R + v₀ * (|T₀| + |T|) + (T - T₀) + 1), fun y hy0 hyT hne i => ?_⟩
    by_cases hu0 : u y = 0
    · rw [hu0, zero_sub, neg_ne_zero] at hne
      have hb := Wave.norm_le_of_retardedIntegral_ne_zero hs (T₀ := T₀) (T := T)
        (fun q hq => by
          by_contra h
          exact hq (hgpast _ (le_of_lt (not_le.mp h))))
        hyT hne
      have hi : |y i.succ| ≤ ‖Minkowski.space y‖ := by
        rw [← Minkowski.space_apply y i, ← Real.norm_eq_abs]
        exact PiLp.norm_apply_le _ i
      exact lt_of_lt_of_le (by simp only [Wave.timeSpaceEquiv_apply] at hb; linarith)
        (le_max_right _ _)
    · exact lt_of_lt_of_le (hρ₁ y hy0 hyT hu0 i) (le_max_left _ _)
  funext y
  have := eq_zero_of_wave_eq_zero hw hbw hpw hsw y
  linarith

/-- **Uniqueness of the retarded potential**: a `C²` potential with `box A₀ = k⁰` and
`box aᵢ = −kⁱ` that vanishes up to the time `T₀`, like the current, and whose spatial support is
bounded on every finite interval of time has the components of the retarded potential. -/
theorem eq_retardedPotential {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k) {R v₀ : ℝ}
    (hs : Wave.SubluminalSupport R v₀ fun p => k (Wave.timeSpaceEquiv.symm p)) {T₀ : ℝ}
    (hkpast : ∀ y : Spacetime, y 0 ≤ T₀ → k y = 0) {A : Potential} (hA : ContDiff ℝ 2 A)
    (hbox : ∀ y, box (potentialComponent A 0) y = k y 0 ∧
      ∀ i : Fin 3, box (potentialComponent A i.succ) y = -k y i.succ)
    (hpast : ∀ y : Spacetime, y 0 ≤ T₀ → A y = 0)
    (hsupp : ∀ T : ℝ, ∃ ρ : ℝ, ∀ y : Spacetime, T₀ ≤ y 0 → y 0 ≤ T → A y ≠ 0 →
      ∀ i : Fin 3, |y i.succ| < ρ) (ν : Fin 4) :
    potentialComponent A ν = potentialComponent (retardedPotential k) ν := by
  have hc : ∀ μ : Fin 4, ContDiff ℝ 2 fun w => k w μ := fun μ =>
    (ContinuousLinearMap.proj μ : Spacetime →L[ℝ] ℝ).contDiff.comp hk
  have hkμ : ∀ (μ : Fin 4) (y : Spacetime), y 0 ≤ T₀ → k y μ = 0 := fun μ y hy => by
    rw [hkpast y hy]
    rfl
  have hAν : ∀ (μ : Fin 4) (y : Spacetime), A y = 0 → potentialComponent A μ y = 0 :=
    fun μ y hy => by simp [potentialComponent, hy]
  have hpν : ∀ μ : Fin 4, ∀ y : Spacetime, y 0 ≤ T₀ → potentialComponent A μ y = 0 :=
    fun μ y hy => hAν μ y (hpast y hy)
  have hsν : ∀ μ : Fin 4, ∀ T : ℝ, ∃ ρ : ℝ, ∀ y : Spacetime, T₀ ≤ y 0 → y 0 ≤ T →
      potentialComponent A μ y ≠ 0 → ∀ i : Fin 3, |y i.succ| < ρ := fun μ T => by
    obtain ⟨ρ, hρ⟩ := hsupp T
    exact ⟨ρ, fun y h0 hT hne => hρ y h0 hT fun h => hne (hAν μ y h)⟩
  refine Fin.cases ?_ (fun i => ?_) ν
  · have h := eq_retardedScalar (hc 0) (subluminalSupport_component hs 0) (hkμ 0)
      (u := fun y => -potentialComponent A 0 y) (CavityModes.contDiff_potentialComponent hA 0).neg
      (fun y => by rw [box_neg, (hbox y).1]) (fun y hy => by rw [hpν 0 y hy, neg_zero])
      (fun T => by
        obtain ⟨ρ, hρ⟩ := hsν 0 T
        exact ⟨ρ, fun y h0 hT hne => hρ y h0 hT fun h => hne (by rw [h, neg_zero])⟩)
    rw [potentialComponent_retardedPotential_zero]
    funext y
    have hy := congrFun h y
    linarith
  · rw [potentialComponent_retardedPotential_succ]
    exact eq_retardedScalar (hc i.succ) (subluminalSupport_component hs i.succ) (hkμ i.succ)
      (CavityModes.contDiff_potentialComponent hA i.succ) (fun y => (hbox y).2 i) (hpν i.succ)
      (hsν i.succ)

/-! ### A conserved current of compact support -/

/-- A smooth bump on space-time: `1` on the ball of radius `1` about the origin, supported in the
ball of radius `2`. -/
def spacetimeBump : ContDiffBump (0 : Spacetime) := ⟨1, 2, by norm_num, by norm_num⟩

/-- The current `k = (∂₁χ, −∂₀χ, 0, 0)` of the bump `χ`: the divergence `k^μ = ∂_ν M^{μν}` of the
antisymmetric field with `M^{01} = −M^{10} = χ`, a conserved current of compact support. -/
def circulatingCurrent : Spacetime → Spacetime := fun v =>
  partialAt spacetimeBump 1 v • (Pi.single 0 1 : Spacetime) -
    partialAt spacetimeBump 0 v • (Pi.single 1 1 : Spacetime)

/-- The circulating current is smooth. -/
theorem contDiff_circulatingCurrent : ContDiff ℝ ∞ circulatingCurrent := by
  have hb : ∀ μ : Fin 4, ContDiff ℝ ∞ (partialAt spacetimeBump μ) := fun μ =>
    contDiff_infty.mpr fun n => contDiff_partialAt_of_le
      (spacetimeBump.contDiff (n := ((n + 1 : ℕ) : ℕ∞))) (by norm_cast) μ
  exact ((hb 1).smul contDiff_const).sub ((hb 0).smul contDiff_const)

/-- The circulating current has compact support. -/
theorem hasCompactSupport_circulatingCurrent : HasCompactSupport circulatingCurrent := by
  refine spacetimeBump.hasCompactSupport.mono' fun v hv => ?_
  by_contra h
  have h0 : fderiv ℝ spacetimeBump v = 0 := fderiv_of_notMem_tsupport ℝ h
  exact hv (by simp [circulatingCurrent, partialAt, h0])

/-- The components of the circulating current. -/
theorem circulatingCurrent_apply (v : Spacetime) :
    circulatingCurrent v 0 = partialAt spacetimeBump 1 v ∧
      circulatingCurrent v 1 = -partialAt spacetimeBump 0 v ∧
      circulatingCurrent v 2 = 0 ∧ circulatingCurrent v 3 = 0 := by
  simp [circulatingCurrent]

/-- The circulating current is conserved: `∂_μ k^μ = ∂₀∂₁χ − ∂₁∂₀χ = 0`. -/
theorem divergence4_circulatingCurrent (v : Spacetime) :
    divergence4 circulatingCurrent v = 0 := by
  have hd : Differentiable ℝ circulatingCurrent :=
    contDiff_circulatingCurrent.differentiable (by simp)
  rw [divergence4_eq_sum_partialAt (hd v), Fin.sum_univ_four]
  have h0 : (fun w => circulatingCurrent w 0) = partialAt spacetimeBump 1 :=
    funext fun w => (circulatingCurrent_apply w).1
  have h1 : (fun w => circulatingCurrent w 1) = fun w => -partialAt spacetimeBump 0 w :=
    funext fun w => (circulatingCurrent_apply w).2.1
  have h2 : (fun w => circulatingCurrent w 2) = fun _ => 0 :=
    funext fun w => (circulatingCurrent_apply w).2.2.1
  have h3 : (fun w => circulatingCurrent w 3) = fun _ => 0 :=
    funext fun w => (circulatingCurrent_apply w).2.2.2
  rw [h0, h1, h2, h3, partialAt_neg, partialAt_const, partialAt_const,
    partialAt_partialAt_comm (spacetimeBump.contDiffAt (n := 2)) 0 1]
  ring

/-- The circulating current does not vanish: by the mean value theorem on the segment from the
centre of the bump to the point `2e₀`, where `χ` falls from `1` to `0`, `∂₀χ = −1/2` somewhere. -/
theorem circulatingCurrent_ne_zero : circulatingCurrent ≠ 0 := by
  have hd : Differentiable ℝ spacetimeBump := spacetimeBump.contDiff (n := 1).differentiable
    (by norm_num)
  have hg : ∀ s : ℝ, HasDerivAt (fun s => spacetimeBump (0 + s • Pi.single 0 1))
      (partialAt spacetimeBump 0 (0 + s • Pi.single 0 1)) s := fun s =>
    hasDerivAt_comp_line 0 (hd _)
  obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope
    (fun s => spacetimeBump (0 + s • Pi.single 0 1))
    (fun s => partialAt spacetimeBump 0 (0 + s • Pi.single 0 1)) (show (0 : ℝ) < 2 by norm_num)
    (fun s _ => (hg s).continuousAt.continuousWithinAt) (fun s _ => hg s)
  have hb0 : spacetimeBump (0 + (0 : ℝ) • Pi.single 0 1) = 1 := by
    rw [zero_smul, add_zero]
    exact spacetimeBump.one_of_mem_closedBall (mem_closedBall_self (by norm_num [spacetimeBump]))
  have hb2 : spacetimeBump (0 + (2 : ℝ) • Pi.single 0 1) = 0 := by
    refine spacetimeBump.zero_of_le_dist ?_
    rw [zero_add, dist_zero_right, norm_smul, Pi.norm_single]
    norm_num [spacetimeBump]
  rw [hb0, hb2] at hc
  intro h
  have h1 := congrFun (congrFun h (0 + c • Pi.single 0 1)) 1
  rw [(circulatingCurrent_apply _).2.1, hc] at h1
  norm_num at h1

/-- The circulating current, written in `(t, x)`, has subluminal support. -/
theorem exists_subluminalSupport_circulatingCurrent :
    ∃ R, Wave.SubluminalSupport R 0 fun p => circulatingCurrent (Wave.timeSpaceEquiv.symm p) :=
  Wave.exists_subluminalSupport_of_hasCompactSupport
    (hasCompactSupport_circulatingCurrent.comp_homeomorph Wave.timeSpaceEquiv.symm.toHomeomorph)

/-- **An instance**: the retarded potential of the circulating current, a nonzero conserved
current of compact support, satisfies the equations of Maxwell with this current. -/
theorem maxwell_retardedPotential_circulatingCurrent (y : Spacetime) :
    (divergence3 (magneticField (fieldTensor (retardedPotential circulatingCurrent))) y = 0 ∧
        ∀ i, partialAt (magneticField (fieldTensor (retardedPotential circulatingCurrent)) i) 0 y +
          curl (electricField (fieldTensor (retardedPotential circulatingCurrent))) y i = 0) ∧
      (divergence3 (electricField (fieldTensor (retardedPotential circulatingCurrent))) y =
          circulatingCurrent y 0 ∧
        ∀ i, curl (magneticField (fieldTensor (retardedPotential circulatingCurrent))) y i -
          partialAt (electricField (fieldTensor (retardedPotential circulatingCurrent)) i) 0 y =
            circulatingCurrent y i.succ) := by
  obtain ⟨R, hs⟩ := exists_subluminalSupport_circulatingCurrent
  exact maxwell_retardedPotential (contDiff_circulatingCurrent.of_le (by simp)) hs
    divergence4_circulatingCurrent y

end ProjectAinos.Electrodynamics
