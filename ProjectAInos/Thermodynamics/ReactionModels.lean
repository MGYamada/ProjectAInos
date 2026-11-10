module

public import ProjectAInos.Thermodynamics.Reactions

/-!
# Unreachable reaction sectors

An equality-only system model has zero transition cost within each label and
infinite cost between distinct labels. Finite chains and catalysts preserve
this obstruction when system composition is cancellative.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Thermodynamics.Reactions

variable {Γ : Type*}

/-- A system label with a single state and no changes of label. -/
def equalityDirectCost (a b : Γ) : EReal :=
  directCost (fun _ : Γ => Unit) (fun _ _ => 0)
    (fun x y => x.1 = y.1) a b

@[simp] theorem equalityDirectCost_self (a : Γ) : equalityDirectCost a a = 0 :=
  directCost_self _ _ _ a (fun _ => rfl) (fun _ _ _ => le_rfl)

theorem equalityDirectCost_eq_top {a b : Γ} (h : a ≠ b) :
    equalityDirectCost a b = ⊤ := by
  apply top_unique
  apply le_sInf
  rintro r ⟨x, y, hxy, _⟩
  exact (h hxy).elim

theorem equalityDirectCost_lt_top_iff (a b : Γ) :
    equalityDirectCost a b < ⊤ ↔ a = b := by
  rw [equalityDirectCost, directCost_lt_top_iff]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨(), (), h⟩⟩

/-- Every finite chain in the equality model stays at its initial label. -/
theorem equalityCostChain_iff (a b : Γ) (r : EReal) :
    CostChain equalityDirectCost a b r ↔ a = b ∧ r = 0 := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨rfl, rfl⟩
    | @step b c r _ hstep ih =>
      have hbc := (equalityDirectCost_lt_top_iff b c).mp hstep
      subst c
      exact ⟨ih.1, by simp [ih.2]⟩
  · rintro ⟨rfl, rfl⟩
    exact CostChain.nil

@[simp] theorem equality_chainCost_self (a : Γ) :
    chainCost equalityDirectCost a a = 0 := by
  apply le_antisymm
  · exact sInf_le CostChain.nil
  · apply le_sInf
    intro r hr
    exact (equalityCostChain_iff a a r).mp hr |>.2 ▸ le_rfl

theorem equality_chainCost_eq_top {a b : Γ} (h : a ≠ b) :
    chainCost equalityDirectCost a b = ⊤ := by
  apply top_unique
  apply le_sInf
  intro r hr
  exact (h ((equalityCostChain_iff a b r).mp hr).1).elim

/-- A common catalyst cannot remove a conserved-label obstruction. -/
theorem equality_catalystCost_eq_top [AddCancelCommMonoid Γ] {a b : Γ} (h : a ≠ b) :
    catalystCost equalityDirectCost a b = ⊤ := by
  apply top_unique
  apply le_iInf
  intro z
  rw [equality_chainCost_eq_top (fun hz => h (add_right_cancel hz))]

@[simp] theorem equality_catalystCost_self [AddCommMonoid Γ] (a : Γ) :
    catalystCost equalityDirectCost a a = 0 := by
  simp [catalystCost]

/-- The equality model satisfies the absence of sinks, including unreachable pairs. -/
theorem equality_noSinks [AddCancelCommMonoid Γ] :
    NoSinks (equalityDirectCost (Γ := Γ)) := by
  intro a b hab
  obtain ⟨z, r, hr⟩ := hab
  have hab : a = b := add_right_cancel ((equalityCostChain_iff _ _ r).mp hr).1
  subst b
  exact ⟨0, 0, CostChain.nil⟩

end ProjectAInos.Thermodynamics.Reactions
