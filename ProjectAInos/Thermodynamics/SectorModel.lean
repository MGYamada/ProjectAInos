module

public import ProjectAInos.Thermodynamics.Models
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Tactic.Linarith

/-!
# A model with a conserved coordinate

The first coordinate records entropy and the second records an extensive
conserved quantity. Accessibility compares entropy only within a fixed fiber.
-/

@[expose] public section

open Filter
open scoped NNReal Topology

namespace ProjectAInos.Thermodynamics

/-- Entropy and conserved amount, with a sectorwise accessibility order. -/
def SectorState := ℝ × ℝ

namespace SectorState

instance : AddCommGroup SectorState := inferInstanceAs (AddCommGroup (ℝ × ℝ))
instance : Module ℝ SectorState := inferInstanceAs (Module ℝ (ℝ × ℝ))

/-- The entropy coordinate. -/
def entropy (x : SectorState) : ℝ := x.1

/-- The conserved coordinate as an additive map. -/
def amount : SectorState →+ ℝ where
  toFun x := x.2
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem amount_smul (a : ℝ≥0) (x : SectorState) :
    amount (a • x) = (a : ℝ) * amount x := rfl

@[simp] theorem entropy_add (x y : SectorState) :
    entropy (x + y) = entropy x + entropy y := rfl

@[simp] theorem entropy_smul (a : ℝ≥0) (x : SectorState) :
    entropy (a • x) = (a : ℝ) * entropy x := rfl

instance : PartialOrder SectorState where
  le x y := amount x = amount y ∧ entropy x ≤ entropy y
  le_refl _ := ⟨rfl, le_rfl⟩
  le_trans _ _ _ hxy hyz := ⟨hxy.1.trans hyz.1, hxy.2.trans hyz.2⟩
  le_antisymm _ _ hxy hyx := Prod.ext (le_antisymm hxy.2 hyx.2) hxy.1

instance : IsOrderedAddMonoid SectorState where
  add_le_add_left x y h z := by
    refine ⟨by simp only [map_add, h.1], ?_⟩
    change entropy x + entropy z ≤ entropy y + entropy z
    linarith [h.2]

instance : PosSMulMono ℝ≥0 SectorState where
  smul_le_smul_of_nonneg_left r hr x y h := by
    constructor
    · change (r : ℝ) * amount x = (r : ℝ) * amount y
      rw [h.1]
    · exact mul_le_mul_of_nonneg_left h.2 r.coe_nonneg

/-- The model satisfies stability by taking limits in both coordinates. -/
theorem stability : Stability SectorState := by
  intro x y z₀ z₁ ε _ hε h
  have lim (a b : ℝ) : Tendsto (fun n => a + (ε n : ℝ) * b) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.add ((NNReal.tendsto_coe.mpr hε).mul_const b)
  constructor
  · apply le_antisymm
    · exact le_of_tendsto_of_tendsto' (lim (amount x) (amount z₀))
        (lim (amount y) (amount z₁)) (fun n => (h n).1.le)
    · exact le_of_tendsto_of_tendsto' (lim (amount y) (amount z₁))
        (lim (amount x) (amount z₀)) (fun n => (h n).1.ge)
  · exact le_of_tendsto_of_tendsto' (lim (entropy x) (entropy z₀))
      (lim (entropy y) (entropy z₁)) (fun n => (h n).2)

/-- Every amount fiber is comparable, hence exchange comparison holds. -/
theorem exchangeComparison : ExchangeComparison SectorState := by
  apply exchangeComparison_of_sectors amount (fun {x y} (h : x ≤ y) => h.1)
  intro x y h
  rcases le_total (entropy x) (entropy y) with hle | hle
  · exact Or.inl ⟨h, hle⟩
  · exact Or.inr ⟨h.symm, hle⟩

/-- A larger entropy does not supply a transition between different amounts. -/
theorem different_amounts_incomparable :
    let x : SectorState := (0, 1)
    let y : SectorState := (1, 2)
    entropy x ≤ entropy y ∧ ¬ x ≤ y ∧ ¬ y ≤ x := by
  change (0 : ℝ) ≤ 1 ∧ ¬ ((1 : ℝ) = 2 ∧ (0 : ℝ) ≤ 1) ∧
    ¬ ((2 : ℝ) = 1 ∧ (1 : ℝ) ≤ 0)
  norm_num

end SectorState

end ProjectAInos.Thermodynamics
