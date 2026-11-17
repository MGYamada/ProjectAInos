/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Poisson.InvariantTorus
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The invariant tori of a system of oscillators

The energies `Fᵢ = (qᵢ² + pᵢ²)/2` of the oscillators are integrals in involution,
and a level set with positive values of all the energies is a product of
circles. It satisfies the hypotheses of `exists_torus_chart_of_involution`:

* `bracket_oscillatorEnergy`: `{Fᵢ, Fⱼ} = 0`;
* `linearIndependent_fderiv_oscillatorEnergy`: the differentials are linearly
  independent on the level set;
* `isCompact_oscillator_levelSet`, `isPreconnected_oscillator_levelSet`: the
  level set is compact and connected;
* `exists_torus_chart_oscillators`: the conclusion of the theorem.
-/

@[expose] public section
noncomputable section

open Set Module
open scoped ContDiff

namespace ProjectAinos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing
open SmoothGeometry SmoothGeometry.NonlinearODE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The energy `(qᵢ² + pᵢ²)/2` of the oscillator `i`. -/
def oscillatorEnergy (i : ι) : PhaseSpace ι :=
  algebraMap ℝ (PhaseSpace ι) (1 / 2) *
    (PhaseSpace.q i * PhaseSpace.q i + PhaseSpace.p i * PhaseSpace.p i)

omit [Fintype ι] [DecidableEq ι] in
theorem oscillatorEnergy_val (i : ι) (z : ι ⊕ ι → ℝ) :
    (oscillatorEnergy i).val z = (z (Sum.inl i) ^ 2 + z (Sum.inr i) ^ 2) / 2 := by
  change (1 / 2 : ℝ) * (z (Sum.inl i) * z (Sum.inl i) + z (Sum.inr i) * z (Sum.inr i)) = _
  ring

omit [DecidableEq ι] in
theorem fderiv_oscillatorEnergy_apply (i : ι) (z w : ι ⊕ ι → ℝ) :
    fderiv ℝ ((oscillatorEnergy i).val : (ι ⊕ ι → ℝ) → ℝ) z w =
      z (Sum.inl i) * w (Sum.inl i) + z (Sum.inr i) * w (Sum.inr i) := by
  have e : ((oscillatorEnergy i).val : (ι ⊕ ι → ℝ) → ℝ) =
      fun z => (1 / 2 : ℝ) * (z (Sum.inl i) ^ 2 + z (Sum.inr i) ^ 2) :=
    funext fun z => by
      rw [oscillatorEnergy_val]
      ring
  have ha : ∀ a : ι ⊕ ι, HasFDerivAt (fun z : ι ⊕ ι → ℝ => z a)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ⊕ ι => ℝ) a) z := fun a =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ⊕ ι => ℝ) a).hasFDerivAt
  have h1 : HasFDerivAt (fun z : ι ⊕ ι → ℝ => z (Sum.inl i) ^ 2)
      ((2 • z (Sum.inl i) ^ (2 - 1)) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ⊕ ι => ℝ) (Sum.inl i)) z :=
    (ha (Sum.inl i)).pow 2
  have h2 : HasFDerivAt (fun z : ι ⊕ ι → ℝ => z (Sum.inr i) ^ 2)
      ((2 • z (Sum.inr i) ^ (2 - 1)) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ⊕ ι => ℝ) (Sum.inr i)) z :=
    (ha (Sum.inr i)).pow 2
  have h3 : HasFDerivAt (fun z : ι ⊕ ι → ℝ => z (Sum.inl i) ^ 2 + z (Sum.inr i) ^ 2)
      ((2 • z (Sum.inl i) ^ (2 - 1)) •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ⊕ ι => ℝ) (Sum.inl i) +
        (2 • z (Sum.inr i) ^ (2 - 1)) •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ⊕ ι => ℝ) (Sum.inr i)) z :=
    h1.add h2
  have h4 := h3.const_mul (1 / 2 : ℝ)
  rw [e, h4.fderiv]
  change (1 / 2 : ℝ) * ((2 • z (Sum.inl i) ^ (2 - 1)) * w (Sum.inl i) +
    (2 • z (Sum.inr i) ^ (2 - 1)) * w (Sum.inr i)) = _
  norm_num
  ring

theorem partialDerivation_oscillatorEnergy_val (b : ι ⊕ ι) (i : ι) (z : ι ⊕ ι → ℝ) :
    (partialDerivation b (oscillatorEnergy i)).val z =
      z (Sum.inl i) * (Pi.single b (1 : ℝ) : ι ⊕ ι → ℝ) (Sum.inl i) +
        z (Sum.inr i) * (Pi.single b (1 : ℝ) : ι ⊕ ι → ℝ) (Sum.inr i) := by
  rw [← fderiv_oscillatorEnergy_apply, fderiv_val_apply]
  simp [Pi.single_apply]

/-- The energies of the oscillators are in involution. -/
theorem bracket_oscillatorEnergy (i j : ι) :
    (PhaseSpace.canonical ι).bracket (oscillatorEnergy i) (oscillatorEnergy j) = 0 := by
  refine Subtype.ext (funext fun z => ?_)
  rw [← fderiv_val_hamiltonianField, fderiv_oscillatorEnergy_apply, hamiltonianField_inl,
    hamiltonianField_inr, partialDerivation_oscillatorEnergy_val,
    partialDerivation_oscillatorEnergy_val]
  by_cases hij : i = j
  · subst hij
    simp
    ring
  · have hji : ¬j = i := fun h => hij h.symm
    simp [hji]

/-- On a level set with positive energies the differentials of the energies are
linearly independent. -/
theorem linearIndependent_fderiv_oscillatorEnergy {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {z : ι ⊕ ι → ℝ} (hz : z ∈ integralMap (oscillatorEnergy (ι := ι)) ⁻¹' {c}) :
    LinearIndependent ℝ fun i =>
      fderiv ℝ ((oscillatorEnergy i).val : (ι ⊕ ι → ℝ) → ℝ) z := by
  rw [Fintype.linearIndependent_iff]
  intro τ hτ k
  have happ : ∀ w : ι ⊕ ι → ℝ,
      ∑ i, τ i * (z (Sum.inl i) * w (Sum.inl i) + z (Sum.inr i) * w (Sum.inr i)) = 0 := by
    intro w
    have h1 := congrArg (fun L : (ι ⊕ ι → ℝ) →L[ℝ] ℝ => L w) hτ
    have h2 : (∑ i, τ i • fderiv ℝ ((oscillatorEnergy i).val : (ι ⊕ ι → ℝ) → ℝ) z) w =
        ∑ i, τ i * fderiv ℝ ((oscillatorEnergy i).val : (ι ⊕ ι → ℝ) → ℝ) z w := by
      change ContinuousLinearMap.apply ℝ ℝ w
        (∑ i, τ i • fderiv ℝ ((oscillatorEnergy i).val : (ι ⊕ ι → ℝ) → ℝ) z) = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]
      rfl
    have h3 : (∑ i, τ i • fderiv ℝ ((oscillatorEnergy i).val : (ι ⊕ ι → ℝ) → ℝ) z) w = 0 := h1
    rw [h2] at h3
    simpa only [fderiv_oscillatorEnergy_apply] using h3
  have h1 := happ (Pi.single (Sum.inl k) 1)
  have h2 := happ (Pi.single (Sum.inr k) 1)
  simp [Pi.single_apply] at h1 h2
  have hzk : (z (Sum.inl k) ^ 2 + z (Sum.inr k) ^ 2) / 2 = c k := by
    have h := congrFun hz k
    rwa [integralMap, oscillatorEnergy_val] at h
  have hpos := hc k
  rcases h1 with h1 | h1
  · exact h1
  · rcases h2 with h2 | h2
    · exact h2
    · rw [h1, h2] at hzk
      norm_num at hzk
      linarith

omit [DecidableEq ι] in
/-- A level set of the energies of the oscillators is compact. -/
theorem isCompact_oscillator_levelSet (c : ι → ℝ) :
    IsCompact (integralMap (oscillatorEnergy (ι := ι)) ⁻¹' {c}) := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_singleton.preimage (contDiff_integralMap _).continuous) ?_
  refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨∑ i, (1 + 2 * |c i|), fun z hz => ?_⟩
  have hR : ∀ k : ι, 1 + 2 * |c k| ≤ ∑ i, (1 + 2 * |c i|) := fun k =>
    Finset.single_le_sum (f := fun i => 1 + 2 * |c i|) (fun i _ => by positivity)
      (Finset.mem_univ k)
  have hR0 : 0 ≤ ∑ i, (1 + 2 * |c i|) := Finset.sum_nonneg fun i _ => by positivity
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR0]
  intro a
  have key : ∀ (k : ι) (x y : ℝ), (x ^ 2 + y ^ 2) / 2 = c k → |x| ≤ 1 + 2 * |c k| := by
    intro k x y h
    have h1 : x ^ 2 ≤ 2 * |c k| := by
      have h2 := le_abs_self (c k)
      nlinarith [sq_nonneg y]
    nlinarith [sq_abs x, abs_nonneg x, abs_nonneg (c k), sq_nonneg (|x| - 1)]
  rcases a with k | k
  · have h := congrFun hz k
    rw [integralMap, oscillatorEnergy_val] at h
    rw [Real.norm_eq_abs]
    exact (key k _ _ h).trans (hR k)
  · have h := congrFun hz k
    rw [integralMap, oscillatorEnergy_val, add_comm] at h
    rw [Real.norm_eq_abs]
    exact (key k _ _ h).trans (hR k)

omit [Fintype ι] [DecidableEq ι] in
/-- A level set with positive energies is connected: it is a product of
circles. -/
theorem isPreconnected_oscillator_levelSet {c : ι → ℝ} (hc : ∀ i, 0 < c i) :
    IsPreconnected (integralMap (oscillatorEnergy (ι := ι)) ⁻¹' {c}) := by
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : (ι → ℝ) → ι ⊕ ι → ℝ, Θ = fun θ a =>
      Sum.elim (fun i => √(2 * c i) * Real.cos (θ i)) (fun i => √(2 * c i) * Real.sin (θ i)) a :=
    ⟨_, rfl⟩
  have hcont : Continuous Θ := by
    rw [hΘ]
    refine continuous_pi fun a => ?_
    rcases a with i | i
    · exact continuous_const.mul (Real.continuous_cos.comp (continuous_apply i))
    · exact continuous_const.mul (Real.continuous_sin.comp (continuous_apply i))
  have hrange : Θ '' univ = integralMap (oscillatorEnergy (ι := ι)) ⁻¹' {c} := by
    ext z
    constructor
    · rintro ⟨θ, -, rfl⟩
      funext i
      have h := Real.sin_sq_add_cos_sq (θ i)
      have hs : √(2 * c i) ^ 2 = 2 * c i := Real.sq_sqrt (by linarith [hc i])
      rw [integralMap, oscillatorEnergy_val, hΘ]
      simp only [Sum.elim_inl, Sum.elim_inr, mul_pow, hs]
      linear_combination (c i) * h
    · intro hz
      have hzi : ∀ i, (z (Sum.inl i) ^ 2 + z (Sum.inr i) ^ 2) / 2 = c i := fun i => by
        have h := congrFun hz i
        rwa [integralMap, oscillatorEnergy_val] at h
      refine ⟨fun i => Complex.arg (z (Sum.inl i) + z (Sum.inr i) * Complex.I), mem_univ _, ?_⟩
      funext a
      have hn : ∀ i, ‖(z (Sum.inl i) + z (Sum.inr i) * Complex.I : ℂ)‖ = √(2 * c i) := fun i => by
        rw [Complex.norm_add_mul_I]
        congr 1
        linarith [hzi i]
      rcases a with i | i
      · rw [hΘ]
        simp only [Sum.elim_inl]
        rw [← hn i, Complex.norm_mul_cos_arg]
        simp
      · rw [hΘ]
        simp only [Sum.elim_inr]
        rw [← hn i, Complex.norm_mul_sin_arg]
        simp
  rw [← hrange]
  exact isPreconnected_univ.image Θ hcont.continuousOn

/-- The invariant tori of a system of oscillators: an instance of the theorem
of Liouville and Arnold. -/
theorem exists_torus_chart_oscillators {c : ι → ℝ} (hc : ∀ i, 0 < c i) :
    ∃ b : Basis ι ℝ (ι → ℝ), ∀ z ∈ integralMap (oscillatorEnergy (ι := ι)) ⁻¹' {c},
      (∀ y ∈ integralMap (oscillatorEnergy (ι := ι)) ⁻¹' {c}, ∃ θ : ι → ℝ,
        jointFlow (fun i => hamiltonianField (oscillatorEnergy i)) (∑ i, θ i • b i) z = y) ∧
      (∀ θ θ' : ι → ℝ,
        jointFlow (fun i => hamiltonianField (oscillatorEnergy i)) (∑ i, θ i • b i) z =
          jointFlow (fun i => hamiltonianField (oscillatorEnergy i)) (∑ i, θ' i • b i) z ↔
        ∀ i, ∃ n : ℤ, θ i - θ' i = n) ∧
      ∀ (s : ι → ℝ) (r : ℝ) (θ : ι → ℝ),
        flow (jointField (fun i => hamiltonianField (oscillatorEnergy i)) s)
            (r, jointFlow (fun i => hamiltonianField (oscillatorEnergy i)) (∑ i, θ i • b i) z) =
          jointFlow (fun i => hamiltonianField (oscillatorEnergy i))
            (∑ i, (θ i + r * b.repr s i) • b i) z :=
  exists_torus_chart_of_involution bracket_oscillatorEnergy
    (fun _ hz => linearIndependent_fderiv_oscillatorEnergy hc hz)
    (isCompact_oscillator_levelSet c) (isPreconnected_oscillator_levelSet hc)

end ProjectAinos.Mechanics
