module

public import ProjectAInos.Thermodynamics.Conservation
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Stoichiometric conservation

A linear reaction map represents the columns of a stoichiometric matrix.
Its cokernel classifies linear conserved quantities at the composition level.
The water-formation example identifies this quotient with hydrogen and oxygen
amounts.
-/

@[expose] public section

namespace ProjectAInos.Thermodynamics.Stoichiometry

variable {R V E : Type*} [AddCommGroup R] [Module ℝ R]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup E] [Module ℝ E]

/-- A composition observable factors through the reaction quotient exactly when
every allowed reaction direction preserves it. -/
theorem conserved_iff_factors (B : R →ₗ[ℝ] V) (q : V →ₗ[ℝ] E) :
    (∃! φ : (V ⧸ LinearMap.range B) →ₗ[ℝ] E,
      φ.comp (LinearMap.range B).mkQ = q) ↔ q.comp B = 0 := by
  rw [existsUnique_conservation_factor_iff, LinearMap.range_le_ker_iff]

/-- Species are ordered as hydrogen gas, oxygen gas, and water. -/
def waterReaction : Fin 3 → ℝ := ![-2, -1, 2]

/-- The extent of the reaction multiplies its stoichiometric vector. -/
def waterReactionMap : ℝ →ₗ[ℝ] (Fin 3 → ℝ) :=
  LinearMap.toSpanSingleton ℝ _ waterReaction

/-- The two elemental amounts are the hydrogen and oxygen atom counts. -/
def elementAmounts : (Fin 3 → ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun x := (2 * x 0 + 2 * x 2, 2 * x 1 + x 2)
  map_add' x y := by ext <;> dsimp <;> ring
  map_smul' r x := by ext <;> dsimp <;> ring

/-- Water formation preserves both elemental amounts. -/
theorem waterReaction_conserved : elementAmounts waterReaction = 0 := by
  norm_num [elementAmounts, waterReaction]

/-- The reaction directions are exactly the changes preserving both elements. -/
theorem waterReaction_range : LinearMap.range waterReactionMap = LinearMap.ker elementAmounts := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    change elementAmounts (t • waterReaction) = 0
    rw [map_smul, waterReaction_conserved, smul_zero]
  · intro hx
    have hzero : elementAmounts x = 0 := hx
    have hH : 2 * x 0 + 2 * x 2 = 0 := congrArg Prod.fst hzero
    have hO : 2 * x 1 + x 2 = 0 := congrArg Prod.snd hzero
    refine ⟨x 2 / 2, ?_⟩
    ext i
    fin_cases i <;> dsimp [waterReactionMap, LinearMap.toSpanSingleton, waterReaction]
    all_goals linarith

/-- Every formal pair of elemental amounts has a representative composition. -/
theorem elementAmounts_surjective : Function.Surjective elementAmounts := by
  rintro ⟨h, o⟩
  refine ⟨![h / 2, o / 2, 0], ?_⟩
  ext <;> dsimp [elementAmounts] <;> ring

/-- The universal conservation quotient in this reaction has two coordinates. -/
noncomputable def waterConservationEquiv :
    ((Fin 3 → ℝ) ⧸ LinearMap.range waterReactionMap) ≃ₗ[ℝ] (ℝ × ℝ) :=
  (Submodule.quotEquivOfEq _ _ waterReaction_range).trans
    (elementAmounts.quotKerEquivOfSurjective elementAmounts_surjective)

end ProjectAInos.Thermodynamics.Stoichiometry
