module

public import ProjectAInos.Thermodynamics.ReactionCycles

/-!
# Weak entropy from raw composite transformations

Additive labels and calibrated entropies on raw composite states determine the
transition costs. Composition, invertible positive scaling, equal-label entropy
monotonicity, and the physical absence of sinks supply all the cost laws used
to select compatible entropy constants.
-/

@[expose] public section

open scoped NNReal

namespace ProjectAInos.Thermodynamics.Reactions

variable {S Γ : Type*} [AddCommMonoid S] [AddCommMonoid Γ]

/-- A chain of actual transitions supplies a chain of direct infimum costs. -/
theorem ActualCostChain.exists_cost_le {label : S →+ Γ} {entropy : S →+ ℝ}
    {accessible : S → S → Prop} {a b : Γ} {r : ℝ}
    (h : ActualCostChain label entropy accessible a b r) :
    ∃ c : EReal, CostChain (calibratedDirectCost label entropy accessible) a b c ∧
      c ≤ (r : EReal) := by
  induction h with
  | nil => exact ⟨0, CostChain.nil, le_rfl⟩
  | @step b c r x y _ hx hy hxy ih =>
    obtain ⟨t, ht, htr⟩ := ih
    have hedge : calibratedDirectCost label entropy accessible b c ≤
        ((entropy y - entropy x : ℝ) : EReal) :=
      directCost_le (fun a => {x : S // label x = a}) (fun _ x => entropy x.val)
        (fun x y => accessible x.2.val y.2.val)
        (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) hxy
    refine ⟨_, CostChain.step ht (hedge.trans_lt (EReal.coe_lt_top _)), ?_⟩
    simpa only [EReal.coe_add] using add_le_add htr hedge

/-- Finite-cost system connectivity is exactly connectivity by actual
transformations, with a common ancillary label. -/
theorem calibrated_connected_iff_actual (label : S →+ Γ) (entropy : S →+ ℝ)
    (accessible : S → S → Prop) (a b : Γ) :
    Connected (calibratedDirectCost label entropy accessible) a b ↔
      ∃ z c, ActualCostChain label entropy accessible (a + z) (b + z) c := by
  constructor
  · rintro ⟨z, r, hr⟩
    obtain ⟨t, hrt, _⟩ := EReal.exists_between_coe_real hr.finite
    obtain ⟨c, hc, _⟩ := hr.exists_actual_lt t hrt
    exact ⟨z, c, hc⟩
  · rintro ⟨z, c, hc⟩
    obtain ⟨r, hr, _⟩ := hc.exists_cost_le
    exact ⟨z, r, hr⟩

/-- Calibrated raw-state entropy admits compatible extensive constants across
all transformation sectors. The returned total entropy is additive, extensive,
and monotone for every accessible transformation. -/
theorem exists_weak_entropy_from_raw_states
    [DistribMulAction ℝ≥0 S] [Module ℝ≥0 Γ]
    (label : S →+ Γ) (entropy : S →+ ℝ) (accessible : S → S → Prop)
    (hlabel : Function.Surjective label)
    (hlabel_scale : ∀ (r : ℝ≥0) (x : S), label (r • x) = r • label x)
    (hentropy_scale : ∀ (r : ℝ≥0) (x : S), entropy (r • x) = (r : ℝ) * entropy x)
    (hrefl : ∀ x, accessible x x)
    (hadd : ∀ {x y u v}, accessible x y → accessible u v → accessible (x + u) (y + v))
    (hscale : ∀ (r : ℝ≥0), 0 < r → ∀ x y,
      accessible (r • x) (r • y) ↔ accessible x y)
    (hmono : ∀ {x y}, accessible x y → label x = label y → entropy x ≤ entropy y)
    (hno_sinks : ∀ a b,
      (∃ z c, ActualCostChain label entropy accessible (a + z) (b + z) c) →
        ∃ z c, ActualCostChain label entropy accessible (b + z) (a + z) c) :
    ∃ (B : Γ →ₗ[ℝ≥0] ℝ) (totalEntropy : S →+ ℝ),
      (∀ x, totalEntropy x = entropy x + B (label x)) ∧
      (∀ (r : ℝ≥0) x, totalEntropy (r • x) = (r : ℝ) * totalEntropy x) ∧
      (∀ x y, accessible x y → totalEntropy x ≤ totalEntropy y) := by
  let State (a : Γ) := {x : S // label x = a}
  let E : ∀ a, State a → ℝ := fun _ x => entropy x.val
  let R : (Σ a, State a) → (Σ a, State a) → Prop :=
    fun x y => accessible x.2.val y.2.val
  let compose {a b : Γ} (x : State a) (y : State b) : State (a + b) :=
    ⟨x.val + y.val, by simp only [map_add, x.property, y.property]⟩
  have hnonempty (a : Γ) : Nonempty (State a) := by
    obtain ⟨x, hx⟩ := hlabel a
    exact ⟨⟨x, hx⟩⟩
  let := hnonempty
  have hshift a b z : directCost State E R (a + z) (b + z) ≤ directCost State E R a b := by
    apply directCost_add_same State E R compose
    · intro a b x y
      exact entropy.map_add x.val y.val
    · intro a b z x y w hxy
      exact hadd hxy (hrefl w.val)
  let scale (r : ℝ≥0) (hr : 0 < r) (a : Γ) : State a ≃ State (r • a) :=
    { toFun x := ⟨r • x.val, by rw [hlabel_scale, x.property]⟩
      invFun y := ⟨r⁻¹ • y.val, by rw [hlabel_scale, y.property, inv_smul_smul₀ hr.ne']⟩
      left_inv x := Subtype.ext (inv_smul_smul₀ hr.ne' x.val)
      right_inv y := Subtype.ext (smul_inv_smul₀ hr.ne' y.val) }
  have hcost_scale (r : ℝ≥0) (hr : 0 < r) a b :
      directCost State E R (r • a) (r • b) =
        costScale r (NNReal.coe_pos.mpr hr) (directCost State E R a b) := by
    apply directCost_smul State E R scale
    · intro r hr a x
      exact hentropy_scale r x.val
    · intro r hr a b x y
      exact hscale r hr x.val y.val
    · exact hr
  have hcycle a r (h : CostChain (directCost State E R) a a r) : 0 ≤ r :=
    calibratedDirectCost_cycle_nonneg label entropy accessible hlabel hrefl hadd hmono a r h
  have hsinks : NoSinks (directCost State E R) := by
    intro a b hab
    apply (calibrated_connected_iff_actual label entropy accessible b a).mpr
    exact hno_sinks a b ((calibrated_connected_iff_actual label entropy accessible a b).mp hab)
  obtain ⟨B, hB⟩ := exists_weak_entropy_from_cost_model State E R hshift hcost_scale hcycle
    hsinks.cost_symmetry
  let totalEntropy : S →+ ℝ := entropy + B.toAddMonoidHom.comp label
  refine ⟨B, totalEntropy, fun _ => rfl, ?_, ?_⟩
  · intro r x
    change entropy (r • x) + B (label (r • x)) =
      (r : ℝ) * (entropy x + B (label x))
    rw [hentropy_scale, hlabel_scale, map_smul, NNReal.smul_def, smul_eq_mul, mul_add]
  · intro x y hxy
    exact hB (x := ⟨x, rfl⟩) (y := ⟨y, rfl⟩) hxy

end ProjectAInos.Thermodynamics.Reactions
