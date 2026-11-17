/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.ODE.Flow
public import Mathlib.Analysis.ODE.Gronwall

/-!
# The group law of a flow and criteria for completeness

* `neg_mem_flowDomain`, `flow_add`: the flow can be followed backwards, and
  `Φ(s + t, x) = Φ(t, Φ(s, x))` whenever the right-hand side is defined. The
  times may have any signs.
* `mem_flowDomain_of_isCompact`: a solution that stays in a compact set, as long
  as it exists, exists for the whole time.
* `flowDomain_eq_univ_of_norm_le`: on a finite-dimensional space a field with
  `‖X(x)‖ ≤ a + b ‖x‖` has a flow defined for all times and points.
* `flowDomain_linear`, `flow_linear`: the flow of a linear field is the
  propagator of the constant coefficient, on any Banach space.
-/

@[expose] public section
noncomputable section

open Set Filter ContinuousLinearMap MeasureTheory Metric
open scoped Topology ContDiff

namespace ProjectAinos.SmoothGeometry.NonlinearODE

open LinearODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {X : E → E} {t : ℝ} {x : E}

/-! ### The group law -/

/-- The flow can be followed backwards to the initial point. -/
theorem neg_mem_flowDomain (hX : ContDiff ℝ ∞ X) (h : (t, x) ∈ flowDomain X) :
    (-t, flow X (t, x)) ∈ flowDomain X ∧ flow X (-t, flow X (t, x)) = x := by
  have hX1 : ContDiff ℝ 1 X := hX.of_le (by simp)
  have hmem : ∀ r ∈ uIcc 0 (-t), (t + r, x) ∈ flowDomain X := by
    intro r hr
    refine mem_flowDomain_of_mem_uIcc h ?_
    rcases mem_uIcc.mp hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact mem_uIcc.mpr (Or.inr ⟨by linarith, by linarith⟩)
    · exact mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩)
  have hy : ∀ r ∈ uIcc 0 (-t), HasDerivWithinAt (fun u => flow X (t + u, x))
      (X (flow X (t + r, x))) (uIcc 0 (-t)) r := fun r hr =>
    ((hasDerivAt_flow hX (hmem r hr)).comp_const_add t r).hasDerivWithinAt
  have h0 : (fun u => flow X (t + u, x)) 0 = flow X (t, x) := by simp
  refine ⟨mem_flowDomain_of_hasDerivWithinAt hX.continuous h0 hy, ?_⟩
  rw [flow_eq_of_hasDerivWithinAt hX1 h0 hy]
  simp

/-- The group law: `Φ(s + t, x) = Φ(t, Φ(s, x))` whenever the right-hand side is
defined. -/
theorem flow_add (hX : ContDiff ℝ ∞ X) {s : ℝ} (hs : (s, x) ∈ flowDomain X)
    (ht : (t, flow X (s, x)) ∈ flowDomain X) :
    (s + t, x) ∈ flowDomain X ∧ flow X (s + t, x) = flow X (t, flow X (s, x)) := by
  have hX1 : ContDiff ℝ 1 X := hX.of_le (by simp)
  obtain ⟨hneg, hback⟩ := neg_mem_flowDomain hX hs
  have hmem : ∀ r ∈ uIcc 0 (s + t), (r - s, flow X (s, x)) ∈ flowDomain X := by
    intro r hr
    have hr' : r - s ∈ uIcc (-s) t := by
      rcases mem_uIcc.mp hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩)
      · exact mem_uIcc.mpr (Or.inr ⟨by linarith, by linarith⟩)
    rcases uIcc_subset_uIcc_union_uIcc (b := 0) hr' with h1 | h1
    · rw [uIcc_comm] at h1
      exact mem_flowDomain_of_mem_uIcc hneg h1
    · exact mem_flowDomain_of_mem_uIcc ht h1
  have hy : ∀ r ∈ uIcc 0 (s + t), HasDerivWithinAt (fun u => flow X (u - s, flow X (s, x)))
      (X (flow X (r - s, flow X (s, x)))) (uIcc 0 (s + t)) r := fun r hr =>
    ((hasDerivAt_flow hX (hmem r hr)).comp_sub_const r s).hasDerivWithinAt
  have h0 : (fun u => flow X (u - s, flow X (s, x))) 0 = x := by
    simpa using hback
  refine ⟨mem_flowDomain_of_hasDerivWithinAt hX.continuous h0 hy, ?_⟩
  rw [flow_eq_of_hasDerivWithinAt hX1 h0 hy]
  simp

/-! ### Completeness -/

/-- A solution that stays in a compact set, as long as it exists, exists for the
whole time. -/
theorem mem_flowDomain_of_isCompact (hX : ContDiff ℝ ∞ X) {K : Set E} (hK : IsCompact K)
    {T : ℝ} (h : ∀ t ∈ uIcc 0 T, (t, x) ∈ flowDomain X → flow X (t, x) ∈ K) :
    (T, x) ∈ flowDomain X := by
  -- a step of the time that is admissible at every point of the compact set
  obtain ⟨U, V, hU, -, h0U, hKV, hUV⟩ := generalized_tube_lemma
    (isCompact_singleton (x := (0 : ℝ))) hK (isOpen_flowDomain hX)
    (by rintro ⟨s, y⟩ ⟨rfl, -⟩; exact zero_mem_flowDomain X y)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU 0 (h0U rfl)
  have hstep : ∀ δ : ℝ, |δ| < ε → ∀ y ∈ K, (δ, y) ∈ flowDomain X := fun δ hδ y hy =>
    hUV ⟨hball (by simpa [Real.dist_eq] using hδ), hKV hy⟩
  let S : Set ℝ := {c | (c * T, x) ∈ flowDomain X}
  have hη : 0 < ε / (|T| + 1) := div_pos hε (by positivity)
  have hclosed : IsClosed (S ∩ Icc 0 1) := by
    refine isClosed_of_closure_subset fun c hc => ?_
    have hc01 : c ∈ Icc (0 : ℝ) 1 :=
      closure_minimal inter_subset_right isClosed_Icc hc
    obtain ⟨c₀, ⟨hc₀S, hc₀I⟩, hdist⟩ := Metric.mem_closure_iff.mp hc _ hη
    have hK₀ : flow X (c₀ * T, x) ∈ K := by
      refine h (c₀ * T) ?_ hc₀S
      rw [mul_comm]
      exact mul_mem_uIcc T hc₀I
    have hδ : |(c - c₀) * T| < ε := by
      rw [abs_mul]
      have h1 : |c - c₀| < ε / (|T| + 1) := by simpa [Real.dist_eq] using hdist
      calc |c - c₀| * |T| ≤ ε / (|T| + 1) * |T| :=
            mul_le_mul_of_nonneg_right h1.le (abs_nonneg T)
        _ < ε / (|T| + 1) * (|T| + 1) := mul_lt_mul_of_pos_left (by linarith) hη
        _ = ε := div_mul_cancel₀ ε (by positivity)
    have hadd := (flow_add hX hc₀S (hstep _ hδ _ hK₀)).1
    have he : c₀ * T + (c - c₀) * T = c * T := by ring
    rw [he] at hadd
    exact ⟨hadd, hc01⟩
  have hopen : ∀ c ∈ S ∩ Ico 0 1, S ∈ 𝓝[>] c := by
    intro c hc
    have hcont : Continuous fun c : ℝ => (c * T, x) :=
      (continuous_id.mul continuous_const).prodMk continuous_const
    exact mem_nhdsWithin_of_mem_nhds
      (((isOpen_flowDomain hX).preimage hcont).mem_nhds hc.1)
  have h0 : (0 : ℝ) ∈ S := by
    change ((0 : ℝ) * T, x) ∈ flowDomain X
    rw [zero_mul]
    exact zero_mem_flowDomain X x
  have h1 := hclosed.Icc_subset_of_forall_mem_nhdsWithin h0 hopen (right_mem_Icc.mpr zero_le_one)
  change ((1 : ℝ) * T, x) ∈ flowDomain X at h1
  rwa [one_mul] at h1

/-- A bound for the flow of a field of linear growth. -/
theorem norm_flow_le_gronwallBound (hX : ContDiff ℝ ∞ X) {a b : ℝ}
    (hab : ∀ y, ‖X y‖ ≤ a + b * ‖y‖) (h : (t, x) ∈ flowDomain X) :
    ‖flow X (t, x)‖ ≤ gronwallBound ‖x‖ b a |t| := by
  rcases le_total 0 t with ht | ht
  · have hmem : ∀ s ∈ Icc 0 t, (s, x) ∈ flowDomain X := fun s hs =>
      mem_flowDomain_of_mem_uIcc h (by rwa [uIcc_of_le ht])
    have hb := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := fun s => flow X (s, x)) (f' := fun s => X (flow X (s, x))) (δ := ‖x‖) (K := b)
      (ε := a) (a := 0) (b := t)
      (fun s hs => (hasDerivAt_flow hX (hmem s hs)).continuousAt.continuousWithinAt)
      (fun s hs => (hasDerivAt_flow hX (hmem s ⟨hs.1, hs.2.le⟩)).hasDerivWithinAt)
      (by simp) (fun s _ => by rw [add_comm]; exact hab _) t ⟨ht, le_rfl⟩
    simpa [abs_of_nonneg ht] using hb
  · have hmem : ∀ s ∈ Icc 0 (-t), (-s, x) ∈ flowDomain X := fun s hs =>
      mem_flowDomain_of_mem_uIcc h (by
        rw [uIcc_of_ge ht]
        exact ⟨by linarith [hs.2], by linarith [hs.1]⟩)
    have hd : ∀ s ∈ Icc 0 (-t),
        HasDerivAt (fun s => flow X (-s, x)) (-X (flow X (-s, x))) s := by
      intro s hs
      have h1 : HasDerivAt (fun s => flow X (-s, x)) ((-1 : ℝ) • X (flow X (-s, x))) s :=
        (hasDerivAt_flow hX (hmem s hs)).scomp s (hasDerivAt_neg s)
      simpa using h1
    have hb := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := fun s => flow X (-s, x)) (f' := fun s => -X (flow X (-s, x))) (δ := ‖x‖)
      (K := b) (ε := a) (a := 0) (b := -t)
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hd s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
      (by simp) (fun s _ => by rw [norm_neg, add_comm]; exact hab _) (-t)
      ⟨by linarith, le_rfl⟩
    simpa [abs_of_nonpos ht] using hb

/-- On a finite-dimensional space a field of linear growth has a flow defined
for all times and points. -/
theorem flowDomain_eq_univ_of_norm_le [FiniteDimensional ℝ E] (hX : ContDiff ℝ ∞ X)
    {a b : ℝ} (hab : ∀ y, ‖X y‖ ≤ a + b * ‖y‖) : flowDomain X = univ := by
  have ha : 0 ≤ a := (norm_nonneg _).trans (by simpa using hab 0)
  have hab' : ∀ y, ‖X y‖ ≤ a + |b| * ‖y‖ := fun y =>
    (hab y).trans (by gcongr; exact le_abs_self b)
  refine eq_univ_of_forall fun p => ?_
  obtain ⟨T, x⟩ := p
  refine mem_flowDomain_of_isCompact hX
    (isCompact_closedBall (0 : E) (gronwallBound ‖x‖ |b| a |T|)) fun t ht h => ?_
  rw [mem_closedBall_zero_iff]
  refine (norm_flow_le_gronwallBound hX hab' h).trans ?_
  refine gronwallBound_mono (norm_nonneg x) ha (abs_nonneg b) ?_
  rcases mem_uIcc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]
    exact h2
  · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]
    linarith

/-! ### The flow of a linear field -/

/-- The flow of a linear field is defined for all times and points. -/
theorem flowDomain_linear (A₀ : E →L[ℝ] E) : flowDomain (fun y => A₀ y) = univ := by
  refine eq_univ_of_forall fun p => ?_
  exact mem_flowDomain_of_hasDerivWithinAt (X := fun y => A₀ y) (t := p.1) (x := p.2)
    (y := fun s => propagator (ContinuousMap.const ℝ A₀) s 0 p.2) A₀.continuous
    (by simp [propagator_self])
    (fun r _ => (hasDerivAt_propagator_const_apply A₀ r p.2).hasDerivWithinAt)

/-- The flow of a linear field is the propagator of the constant coefficient. -/
theorem flow_linear (A₀ : E →L[ℝ] E) (t : ℝ) (x : E) :
    flow (fun y => A₀ y) (t, x) = propagator (ContinuousMap.const ℝ A₀) t 0 x :=
  flow_eq_of_hasDerivWithinAt (X := fun y => A₀ y)
    (y := fun s => propagator (ContinuousMap.const ℝ A₀) s 0 x) A₀.contDiff
    (by simp [propagator_self])
    (fun r _ => (hasDerivAt_propagator_const_apply A₀ r x).hasDerivWithinAt)

end ProjectAinos.SmoothGeometry.NonlinearODE
