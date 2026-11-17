/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.ODE.VolterraInverse
public import ProjectAinos.SmoothGeometry.ODE.ContinuousFamily
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # The propagator of a linear differential equation on the real line

For a continuous coefficient `A : ℝ → E →L[ℝ] E` the propagator `propagator A t s`
takes the value at time `s` of a solution of `y' = A(t) y` to its value at
time `t`, for every pair of real times. It is the value at the end of the unit
interval of the Volterra solution for the coefficient `σ ↦ (t - s) • A (s +
σ (t - s))`, so no interval is subdivided and no bound on `A` is needed.

The propagator is the identity at `t = s`, satisfies the differential equation
in `t`, is the only solution, obeys the composition law and is invertible. If
the coefficient depends smoothly on a parameter and the time, so does the
propagator.
-/

@[expose] public section
noncomputable section

open Set ContinuousLinearMap
open scoped ContDiff Topology

namespace ProjectAinos.SmoothGeometry.LinearODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem extend_of_mem (f : Curve E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    extend f t = f ⟨t, ht⟩ := by
  change extend f ((⟨t, ht⟩ : unitInterval) : ℝ) = _
  rw [extend_coe]

/-- The coefficient on the segment from `s` to `t`, as a curve on the unit interval. -/
def segmentCoefficient (A : C(ℝ, E →L[ℝ] E)) (s t : ℝ) : Curve (E →L[ℝ] E) :=
  ⟨fun σ => (t - s) • A (s + (σ : ℝ) * (t - s)), by fun_prop⟩

@[simp] theorem segmentCoefficient_apply (A : C(ℝ, E →L[ℝ] E)) (s t : ℝ) (σ : unitInterval) :
    segmentCoefficient A s t σ = (t - s) • A (s + (σ : ℝ) * (t - s)) := rfl

@[simp] theorem segmentCoefficient_self (A : C(ℝ, E →L[ℝ] E)) (s : ℝ) :
    segmentCoefficient A s s = 0 := by
  ext σ v
  simp

variable [CompleteSpace E]

/-- The propagator from time `s` to time `t`. -/
def propagator (A : C(ℝ, E →L[ℝ] E)) (t s : ℝ) : E →L[ℝ] E :=
  (ContinuousMap.evalCLM ℝ (M := E) (1 : unitInterval)).comp
    (solutionOperator (segmentCoefficient A s t))

theorem propagator_apply (A : C(ℝ, E →L[ℝ] E)) (t s : ℝ) (y : E) :
    propagator A t s y = solutionOperator (segmentCoefficient A s t) y 1 := rfl

@[simp] theorem propagator_self (A : C(ℝ, E →L[ℝ] E)) (s : ℝ) :
    propagator A s s = ContinuousLinearMap.id ℝ E := by
  ext y
  rw [propagator_apply, segmentCoefficient_self, solution_zero_coefficient]
  rfl

/-- The Volterra solution on the segment from `s` to `t` is the propagator at
the intermediate times. -/
theorem solutionOperator_segmentCoefficient_apply (A : C(ℝ, E →L[ℝ] E)) (s t : ℝ) (y : E)
    (σ : unitInterval) :
    solutionOperator (segmentCoefficient A s t) y σ =
      propagator A (s + (σ : ℝ) * (t - s)) s y := by
  let z := solutionOperator (segmentCoefficient A s t) y
  let w : Curve E := ⟨fun ρ => z (σ * ρ), by fun_prop⟩
  have hw : w = solutionOperator (segmentCoefficient A s (s + (σ : ℝ) * (t - s))) y := by
    apply eq_solutionOperator_of_integral_eq
    intro ρ
    have h1 := solutionOperator_integral_eq (segmentCoefficient A s t) y (σ * ρ)
    change w ρ = y + ∫ u in 0..((σ * ρ : unitInterval) : ℝ),
      extend (segmentCoefficient A s t) u (extend z u) at h1
    rw [h1]
    congr 1
    have hmul : ((σ * ρ : unitInterval) : ℝ) = (σ : ℝ) * ρ := rfl
    rw [hmul]
    have h2 := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := (ρ : ℝ))
      (fun u => extend (segmentCoefficient A s t) u (extend z u)) (σ : ℝ)
    rw [mul_zero] at h2
    rw [← h2, ← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le ρ.property.1] at hv
    have hv1 : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1, hv.2.trans ρ.property.2⟩
    have hσv : (σ : ℝ) * v ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg σ.property.1 hv1.1,
        (mul_le_mul σ.property.2 hv1.2 hv1.1 zero_le_one).trans_eq (one_mul 1)⟩
    change (σ : ℝ) • extend (segmentCoefficient A s t) (σ * v) (extend z (σ * v)) =
      extend (segmentCoefficient A s (s + (σ : ℝ) * (t - s))) v (extend w v)
    rw [extend_of_mem _ hσv, extend_of_mem _ hσv, extend_of_mem _ hv1, extend_of_mem _ hv1]
    change (σ : ℝ) • ((t - s) • A (s + (σ : ℝ) * v * (t - s))) (z ⟨(σ : ℝ) * v, hσv⟩) =
      ((s + (σ : ℝ) * (t - s) - s) • A (s + v * (s + (σ : ℝ) * (t - s) - s)))
        (z (σ * ⟨v, hv1⟩))
    have hz : z (σ * ⟨v, hv1⟩) = z ⟨(σ : ℝ) * v, hσv⟩ := rfl
    rw [hz, show s + (σ : ℝ) * (t - s) - s = (σ : ℝ) * (t - s) by ring,
      show v * ((σ : ℝ) * (t - s)) = (σ : ℝ) * v * (t - s) by ring]
    simp only [_root_.smul_apply, smul_smul]
  have h := congrArg (fun f : Curve E => f 1) hw
  change z (σ * 1) = _ at h
  rw [mul_one] at h
  exact h

/-- The propagator satisfies the integral equation on the real line. -/
theorem propagator_apply_eq_add_integral (A : C(ℝ, E →L[ℝ] E)) (t s : ℝ) (y : E) :
    propagator A t s y = y + ∫ r in s..t, A r (propagator A r s y) := by
  have h1 := solutionOperator_integral_eq (segmentCoefficient A s t) y 1
  rw [propagator_apply, h1]
  congr 1
  change ∫ u in (0 : ℝ)..1, extend (segmentCoefficient A s t) u
    (extend (solutionOperator (segmentCoefficient A s t) y) u) = _
  have h2 := intervalIntegral.smul_integral_comp_add_mul (a := 0) (b := 1)
    (fun r => A r (propagator A r s y)) (t - s) s
  rw [mul_zero, add_zero, mul_one, add_sub_cancel] at h2
  rw [← h2, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le zero_le_one] at hu
  change extend (segmentCoefficient A s t) u
    (extend (solutionOperator (segmentCoefficient A s t) y) u) =
      (t - s) • A (s + (t - s) * u) (propagator A (s + (t - s) * u) s y)
  rw [extend_of_mem _ hu, extend_of_mem _ hu, solutionOperator_segmentCoefficient_apply]
  change ((t - s) • A (s + u * (t - s))) (propagator A (s + u * (t - s)) s y) = _
  rw [mul_comm u, _root_.smul_apply]

omit [CompleteSpace E] in
theorem continuous_segmentCoefficient (A : C(ℝ, E →L[ℝ] E)) :
    Continuous fun q : ℝ × ℝ => segmentCoefficient A q.2 q.1 := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous fun x : (ℝ × ℝ) × unitInterval =>
    (x.1.1 - x.1.2) • A (x.1.2 + (x.2 : ℝ) * (x.1.1 - x.1.2))
  fun_prop

/-- The propagator is jointly continuous in the two times, in the operator norm. -/
theorem continuous_propagator (A : C(ℝ, E →L[ℝ] E)) :
    Continuous fun q : ℝ × ℝ => propagator A q.1 q.2 :=
  continuous_const.clm_comp
    (solutionOperator_contDiff.continuous.comp (continuous_segmentCoefficient A))

theorem continuous_propagator_left (A : C(ℝ, E →L[ℝ] E)) (s : ℝ) :
    Continuous fun r : ℝ => propagator A r s := by
  have h := (continuous_propagator A).comp
    ((continuous_id (X := ℝ)).prodMk (continuous_const (y := s)))
  exact h

/-- The propagator applied to a vector solves the differential equation. -/
theorem hasDerivAt_propagator_apply (A : C(ℝ, E →L[ℝ] E)) (t s : ℝ) (y : E) :
    HasDerivAt (fun r => propagator A r s y) (A t (propagator A t s y)) t := by
  have hA : Continuous fun r : ℝ => A r := A.continuous
  have hry : Continuous fun r : ℝ => propagator A r s y :=
    (continuous_propagator_left A s).clm_apply continuous_const
  have hc : Continuous fun r => A r (propagator A r s y) := hA.clm_apply hry
  have h := (hc.integral_hasStrictDerivAt s t).hasDerivAt.const_add y
  have heq : (fun r => propagator A r s y) =
      fun r => y + ∫ u in s..r, A u (propagator A u s y) :=
    funext fun r => propagator_apply_eq_add_integral A r s y
  rw [heq]
  exact h

/-- The propagator solves the differential equation as an operator. -/
theorem hasDerivAt_propagator (A : C(ℝ, E →L[ℝ] E)) (t s : ℝ) :
    HasDerivAt (fun r => propagator A r s) (A t ∘L propagator A t s) t := by
  have hA : Continuous fun r : ℝ => A r := A.continuous
  have hc : Continuous fun r => A r ∘L propagator A r s :=
    hA.clm_comp (continuous_propagator_left A s)
  have h := (hc.integral_hasStrictDerivAt s t).hasDerivAt.const_add (ContinuousLinearMap.id ℝ E)
  have heq : (fun r => propagator A r s) =
      fun r => ContinuousLinearMap.id ℝ E + ∫ u in s..r, A u ∘L propagator A u s := by
    funext r
    ext y
    rw [_root_.add_apply,
      ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable s r)]
    exact propagator_apply_eq_add_integral A r s y
  rw [heq]
  exact h

/-- Uniqueness: a solution between `s` and `t`, continuous at the two ends,
is given by the propagator. -/
theorem eq_propagator_apply_of_hasDerivAt (A : C(ℝ, E →L[ℝ] E)) {f : ℝ → E} {s t : ℝ}
    (hc : ContinuousOn f (uIcc s t))
    (hf : ∀ r ∈ Ioo (min s t) (max s t), HasDerivAt f (A r (f r)) r) :
    f t = propagator A t s (f s) := by
  rcases eq_or_ne s t with rfl | hst
  · simp
  have hmem : ∀ σ : unitInterval, s + (σ : ℝ) * (t - s) ∈ uIcc s t := by
    intro σ
    rw [mem_uIcc]
    rcases le_total s t with h | h
    · left
      constructor <;> nlinarith [σ.property.1, σ.property.2]
    · right
      constructor <;> nlinarith [σ.property.1, σ.property.2]
  let g : Curve E := ⟨fun σ => f (s + (σ : ℝ) * (t - s)),
    hc.comp_continuous (by fun_prop) hmem⟩
  have hg : g = solutionOperator (segmentCoefficient A s t) (f s) := by
    apply eq_solutionOperator_of_hasDerivAt
    · change f (s + ((0 : unitInterval) : ℝ) * (t - s)) = f s
      simp
    · intro σ hσ
      have hσ' : σ ∈ Icc (0 : ℝ) 1 := ⟨hσ.1.le, hσ.2.le⟩
      have hr : s + σ * (t - s) ∈ Ioo (min s t) (max s t) := by
        rcases lt_or_gt_of_ne hst with h | h
        · rw [min_eq_left h.le, max_eq_right h.le]
          constructor <;> nlinarith [hσ.1, hσ.2]
        · rw [min_eq_right h.le, max_eq_left h.le]
          constructor <;> nlinarith [hσ.1, hσ.2]
      have hin : HasDerivAt (fun u : ℝ => s + u * (t - s)) (t - s) σ := by
        simpa using ((hasDerivAt_id σ).mul_const (t - s)).const_add s
      have hcomp := (hf _ hr).scomp σ hin
      have hev : extend g =ᶠ[𝓝 σ] fun u => f (s + u * (t - s)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hσ] with u hu
        exact extend_of_mem g ⟨hu.1.le, hu.2.le⟩
      rw [extend_of_mem _ hσ', extend_of_mem _ hσ']
      change HasDerivAt (extend g)
        (((t - s) • A (s + σ * (t - s))) (f (s + σ * (t - s)))) σ
      rw [_root_.smul_apply]
      exact hcomp.congr_of_eventuallyEq hev
  have h := congrArg (fun k : Curve E => k 1) hg
  change f (s + ((1 : unitInterval) : ℝ) * (t - s)) = _ at h
  rw [propagator_apply, ← h]
  congr 1
  simp

/-- The composition law of the propagator. -/
theorem propagator_comp (A : C(ℝ, E →L[ℝ] E)) (t s r : ℝ) :
    propagator A t s ∘L propagator A s r = propagator A t r := by
  ext y
  have h := eq_propagator_apply_of_hasDerivAt A (f := fun u => propagator A u r y) (s := s) (t := t)
    (continuous_iff_continuousAt.mpr fun u =>
      (hasDerivAt_propagator_apply A u r y).continuousAt).continuousOn
    (fun u _ => hasDerivAt_propagator_apply A u r y)
  exact h.symm

theorem propagator_comp_apply (A : C(ℝ, E →L[ℝ] E)) (t s r : ℝ) (y : E) :
    propagator A t s (propagator A s r y) = propagator A t r y :=
  congrArg (fun L : E →L[ℝ] E => L y) (propagator_comp A t s r)

/-- The propagator is invertible, with the propagator in the other direction as its inverse. -/
theorem propagator_isInvertible (A : C(ℝ, E →L[ℝ] E)) (t s : ℝ) :
    (propagator A t s).IsInvertible :=
  ⟨ContinuousLinearEquiv.equivOfInverse (propagator A t s) (propagator A s t)
    (fun y => by rw [propagator_comp_apply, propagator_self]; rfl)
    (fun y => by rw [propagator_comp_apply, propagator_self]; rfl), rfl⟩

theorem propagator_apply_self_apply (A : C(ℝ, E →L[ℝ] E)) (t s : ℝ) (y : E) :
    propagator A t s (propagator A s t y) = y := by
  rw [propagator_comp_apply, propagator_self]
  rfl

/-- Constant coefficients: the propagator is the exponential. -/
theorem propagator_const (A₀ : E →L[ℝ] E) (t s : ℝ) :
    propagator (ContinuousMap.const ℝ A₀) t s = NormedSpace.exp ((t - s) • A₀) := by
  ext y
  have hd : ∀ r : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp ((u - s) • A₀) y)
      (A₀ (NormedSpace.exp ((r - s) • A₀) y)) r := by
    intro r
    have h1 := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A₀ (r - s)).scomp r
      ((hasDerivAt_id r).sub_const s)
    have h2 := h1.clm_apply (hasDerivAt_const r y)
    simpa [Function.comp_def] using h2
  have h := eq_propagator_apply_of_hasDerivAt (ContinuousMap.const ℝ A₀)
    (f := fun u => NormedSpace.exp ((u - s) • A₀) y) (s := s) (t := t)
    (continuous_iff_continuousAt.mpr fun u => (hd u).continuousAt).continuousOn
    (fun u _ => hd u)
  simpa using h.symm

section Parameter

universe u

variable {P V : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- A jointly continuous family of coefficients, as a coefficient for each parameter. -/
def coefficientCurve (A : P × ℝ → V →L[ℝ] V) (hA : Continuous A) (p : P) : C(ℝ, V →L[ℝ] V) :=
  ⟨fun t => A (p, t), by fun_prop⟩

omit [NormedSpace ℝ P] [CompleteSpace V] in
@[simp] theorem coefficientCurve_apply (A : P × ℝ → V →L[ℝ] V) (hA : Continuous A) (p : P)
    (t : ℝ) : coefficientCurve A hA p t = A (p, t) := rfl

/-- If the coefficient depends smoothly on a parameter and the time, the
propagator depends smoothly on the parameter and the two times. -/
theorem propagator_contDiff {A : P × ℝ → V →L[ℝ] V} (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ fun q : P × ℝ × ℝ =>
      propagator (coefficientCurve A hA.continuous q.1) q.2.1 q.2.2 := by
  let f : (P × ℝ × ℝ) × ℝ → V →L[ℝ] V := fun x =>
    (x.1.2.1 - x.1.2.2) • A (x.1.1, x.1.2.2 + x.2 * (x.1.2.1 - x.1.2.2))
  have hf : ContDiff ℝ ∞ f := by
    have h1 : ContDiff ℝ ∞ fun x : (P × ℝ × ℝ) × ℝ => x.1.2.1 - x.1.2.2 := by fun_prop
    have h2 : ContDiff ℝ ∞ fun x : (P × ℝ × ℝ) × ℝ =>
        (x.1.1, x.1.2.2 + x.2 * (x.1.2.1 - x.1.2.2)) := by fun_prop
    exact h1.smul (hA.comp h2)
  let g : C(unitInterval, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩
  have hs := ContinuousFamily.slices_contDiff hf g
  have heq : (fun q : P × ℝ × ℝ =>
      propagator (coefficientCurve A hA.continuous q.1) q.2.1 q.2.2) =
      fun q => (ContinuousMap.evalCLM ℝ (M := V) (1 : unitInterval)).comp
        (solutionOperator (ContinuousFamily.slices f hf.continuous g q)) := by
    funext q
    rfl
  rw [heq]
  exact contDiff_const.clm_comp (solutionOperator_contDiff.comp hs)

/-- The propagator applied to a vector that depends smoothly on the parameter. -/
theorem propagator_apply_contDiff {A : P × ℝ → V →L[ℝ] V} (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ fun q : (P × ℝ × ℝ) × V =>
      propagator (coefficientCurve A hA.continuous q.1.1) q.1.2.1 q.1.2.2 q.2 :=
  ((propagator_contDiff hA).comp contDiff_fst).clm_apply contDiff_snd

end Parameter

/-- A smooth coefficient has a propagator that is smooth in the two times. -/
theorem propagator_contDiff_of_contDiff {A : C(ℝ, E →L[ℝ] E)} (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ fun q : ℝ × ℝ => propagator A q.1 q.2 := by
  let B : E × ℝ → E →L[ℝ] E := fun x => A x.2
  have hB : ContDiff ℝ ∞ B := hA.comp contDiff_snd
  have h := (propagator_contDiff hB).comp
    (contDiff_const (c := (0 : E)).prodMk (contDiff_id (E := ℝ × ℝ)))
  have heq : (fun q : ℝ × ℝ => propagator A q.1 q.2) =
      (fun q : E × ℝ × ℝ => propagator (coefficientCurve B hB.continuous q.1) q.2.1 q.2.2) ∘
        fun q : ℝ × ℝ => ((0 : E), q) := by
    funext q
    rfl
  rw [heq]
  exact h

end ProjectAinos.SmoothGeometry.LinearODE
