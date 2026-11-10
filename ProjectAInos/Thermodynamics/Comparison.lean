module

public import ProjectAInos.Thermodynamics.Basic
public import Mathlib.Algebra.Order.Monoid.Defs

/-!
# Exchange comparison

Exchange comparison concerns the two composites obtained from two accessible
processes. Composition labels provide a sufficient physical interface when
accessibility preserves the labels and each label fiber is comparable.
-/

@[expose] public section

namespace ProjectAInos.Thermodynamics

/-- The exchange composites of any two accessible processes are comparable. -/
def ExchangeComparison (M : Type*) [AddCommMonoid M] [Preorder M] : Prop :=
  ∀ x y u v : M, x ≤ y → u ≤ v → x + v ≤ y + u ∨ y + u ≤ x + v

/-- Comparison on every composition sector implies exchange comparison. -/
theorem exchangeComparison_of_sectors {M D : Type*}
    [AddCommMonoid M] [Preorder M] [AddCommMonoid D]
    (label : M →+ D)
    (preserved : ∀ {x y}, x ≤ y → label x = label y)
    (comparable : ∀ {x y}, label x = label y → x ≤ y ∨ y ≤ x) :
    ExchangeComparison M := by
  intro x y u v hxy huv
  apply comparable
  simp only [map_add, preserved hxy, preserved huv]

/-- A total order supplies exchange comparison directly. -/
theorem exchangeComparison_of_linearOrder (M : Type*)
    [AddCommMonoid M] [LinearOrder M] : ExchangeComparison M :=
  fun _ _ _ _ _ _ => le_total _ _

end ProjectAInos.Thermodynamics
