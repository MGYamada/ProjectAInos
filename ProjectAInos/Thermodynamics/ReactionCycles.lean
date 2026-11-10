module

public import ProjectAInos.Thermodynamics.Reactions
public import Mathlib.Tactic.Linarith

/-!
# Cycle consistency from calibrated composite states

Parallel composition turns a finite cycle of transformations into an
equal-label transformation. Additive entropy and its monotonicity within each
label then force a nonnegative total entropy change. Approximation from above
passes this result to chains of direct infimum costs, including negative
infinite candidate costs.
-/

@[expose] public section

namespace ProjectAInos.Thermodynamics.Reactions

variable {S Γ : Type*} [AddCommMonoid S] [AddCommMonoid Γ]

/-- A chain of actual transformations with the sum of their real entropy
changes. Intermediate states may differ while their labels agree. -/
inductive ActualCostChain (label : S →+ Γ) (entropy : S →+ ℝ)
    (accessible : S → S → Prop) (a : Γ) : Γ → ℝ → Prop
  | nil : ActualCostChain label entropy accessible a a 0
  | step {b c : Γ} {r : ℝ} {x y : S} :
      ActualCostChain label entropy accessible a b r →
      label x = b → label y = c → accessible x y →
      ActualCostChain label entropy accessible a c (r + (entropy y - entropy x))

/-- Parallel composition realizes a chain's total entropy change. The common
extra label avoids assuming cancellation in the label monoid. -/
theorem ActualCostChain.aggregate {label : S →+ Γ} {entropy : S →+ ℝ}
    {accessible : S → S → Prop}
    (hrefl : ∀ x, accessible x x)
    (hadd : ∀ {x y u v}, accessible x y → accessible u v → accessible (x + u) (y + v))
    {a b : Γ} {r : ℝ} (h : ActualCostChain label entropy accessible a b r)
    (anchor : S) (hanchor : label anchor = a) :
    ∃ x y z, accessible x y ∧ label x = a + z ∧ label y = b + z ∧
      entropy y - entropy x = r := by
  induction h with
  | nil => exact ⟨anchor, anchor, 0, hrefl anchor, by simpa using hanchor,
      by simpa using hanchor, sub_self _⟩
  | @step b c r u v _ hu hv huv ih =>
    obtain ⟨x, y, z, hxy, hx, hy, hcost⟩ := ih
    refine ⟨x + u, y + v, z + b, hadd hxy huv, ?_, ?_, ?_⟩
    · rw [map_add, hx, hu, add_assoc]
    · rw [map_add, hy, hv]
      ac_rfl
    · rw [map_add, map_add]
      linarith

/-- An actual cycle has nonnegative entropy cost using only monotonicity of
equal-label transformations. -/
theorem ActualCostChain.cycle_nonneg {label : S →+ Γ} {entropy : S →+ ℝ}
    {accessible : S → S → Prop}
    (hrefl : ∀ x, accessible x x)
    (hadd : ∀ {x y u v}, accessible x y → accessible u v → accessible (x + u) (y + v))
    (hmono : ∀ {x y}, accessible x y → label x = label y → entropy x ≤ entropy y)
    {a : Γ} {r : ℝ} (h : ActualCostChain label entropy accessible a a r)
    (anchor : S) (hanchor : label anchor = a) : 0 ≤ r := by
  obtain ⟨x, y, z, hxy, hx, hy, hcost⟩ := h.aggregate hrefl hadd anchor hanchor
  rw [← hcost]
  exact sub_nonneg.mpr (hmono hxy (hx.trans hy.symm))

/-- Direct transition costs for fibers of an additive raw-state label map. -/
noncomputable def calibratedDirectCost (label : S →+ Γ) (entropy : S →+ ℝ)
    (accessible : S → S → Prop) : Γ → Γ → EReal :=
  directCost (fun a => {x : S // label x = a}) (fun _ x => entropy x.val)
    (fun x y => accessible x.2.val y.2.val)

private theorem real_upper_bounds_of_add_lt {a b : EReal} {t : ℝ}
    (ha : a < ⊤) (hb : b < ⊤) (h : a + b < (t : EReal)) :
    ∃ u v : ℝ, a < u ∧ b < v ∧ u + v < t := by
  by_cases habot : a = ⊥
  · obtain ⟨v, hv, _⟩ := EReal.exists_between_coe_real hb
    refine ⟨t - v - 1, v, ?_, hv, by linarith⟩
    rw [habot]
    exact EReal.bot_lt_coe _
  by_cases hbbot : b = ⊥
  · obtain ⟨u, hu, _⟩ := EReal.exists_between_coe_real ha
    refine ⟨u, t - u - 1, hu, ?_, by linarith⟩
    rw [hbbot]
    exact EReal.bot_lt_coe _
  have hae := EReal.coe_toReal ha.ne habot
  have hbe := EReal.coe_toReal hb.ne hbbot
  rw [← hae, ← hbe, ← EReal.coe_add, EReal.coe_lt_coe_iff] at h
  refine ⟨a.toReal + (t - a.toReal - b.toReal) / 3,
    b.toReal + (t - a.toReal - b.toReal) / 3, ?_, ?_, ?_⟩
  · rw [← hae, EReal.coe_lt_coe_iff]
    simp only [EReal.toReal_coe]
    linarith
  · rw [← hbe, EReal.coe_lt_coe_iff]
    simp only [EReal.toReal_coe]
    linarith
  · linarith

/-- Every strict real upper bound on a chain of infimum costs can be realized
by a chain of actual transitions. -/
theorem CostChain.exists_actual_lt {label : S →+ Γ} {entropy : S →+ ℝ}
    {accessible : S → S → Prop} {a b : Γ} {r : EReal}
    (h : CostChain (calibratedDirectCost label entropy accessible) a b r) :
    ∀ t : ℝ, r < (t : EReal) →
      ∃ c : ℝ, ActualCostChain label entropy accessible a b c ∧ c < t := by
  induction h with
  | nil =>
    intro t ht
    exact ⟨0, ActualCostChain.nil, EReal.coe_lt_coe_iff.mp ht⟩
  | @step b c r hchain hedge ih =>
    intro t ht
    obtain ⟨u, v, hu, hv, huv⟩ := real_upper_bounds_of_add_lt hchain.finite hedge ht
    obtain ⟨r', hr', hru⟩ := ih u hu
    obtain ⟨cost, ⟨x, y, hxy, rfl⟩, hcost⟩ := sInf_lt_iff.mp hv
    have hreal : entropy y.val - entropy x.val < v := EReal.coe_lt_coe_iff.mp hcost
    exact ⟨r' + (entropy y.val - entropy x.val),
      ActualCostChain.step hr' x.property y.property hxy,
      (add_lt_add hru hreal).trans huv⟩

/-- Cycle consistency of infimum transition costs follows from calibrated
equal-label entropy monotonicity on the raw composite states. -/
theorem calibratedDirectCost_cycle_nonneg
    (label : S →+ Γ) (entropy : S →+ ℝ) (accessible : S → S → Prop)
    (hlabel : Function.Surjective label)
    (hrefl : ∀ x, accessible x x)
    (hadd : ∀ {x y u v}, accessible x y → accessible u v → accessible (x + u) (y + v))
    (hmono : ∀ {x y}, accessible x y → label x = label y → entropy x ≤ entropy y)
    (a : Γ) (r : EReal)
    (h : CostChain (calibratedDirectCost label entropy accessible) a a r) : 0 ≤ r := by
  by_contra hnonneg
  obtain ⟨t, hrt, ht⟩ := EReal.exists_between_coe_real (lt_of_not_ge hnonneg)
  obtain ⟨c, hc, hct⟩ := h.exists_actual_lt t hrt
  obtain ⟨anchor, hanchor⟩ := hlabel a
  have hcpos := hc.cycle_nonneg hrefl hadd hmono anchor hanchor
  have htneg : t < 0 := EReal.coe_lt_coe_iff.mp ht
  linarith

/-- Catalysts cannot create a negative self-cost in a calibrated state model. -/
theorem calibratedCatalystCost_self
    (label : S →+ Γ) (entropy : S →+ ℝ) (accessible : S → S → Prop)
    (hlabel : Function.Surjective label)
    (hrefl : ∀ x, accessible x x)
    (hadd : ∀ {x y u v}, accessible x y → accessible u v → accessible (x + u) (y + v))
    (hmono : ∀ {x y}, accessible x y → label x = label y → entropy x ≤ entropy y)
    (a : Γ) : catalystCost (calibratedDirectCost label entropy accessible) a a = 0 :=
  catalystCost_self _ (calibratedDirectCost_cycle_nonneg label entropy accessible
    hlabel hrefl hadd hmono) a

end ProjectAInos.Thermodynamics.Reactions
