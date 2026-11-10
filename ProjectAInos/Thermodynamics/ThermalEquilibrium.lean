module

public import ProjectAInos.Thermodynamics.PhysicalComparison

/-!
# Thermal equilibrium and scaling

The positive scaled-copy clause of T2 implies equilibrium with every positive
scaled copy. Together with symmetry and the zeroth law T3, this gives the
independent scaling invariance of LY Theorem 4.1. A separate typed interface
identifies the raw thermal relation with the equilibrium relation of a thermal
join; neither thermal splitting nor this identification is derived from contact.
-/

@[expose] public section

open scoped NNReal

namespace ProjectAInos.Thermodynamics.Physical

namespace Accessibility

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
variable {R : X → X → Prop}

/-- The positive scaled-copy clause of T2 gives equilibrium with any positive
multiple of a state, by splitting its `(1 + r)`-fold copy. -/
theorem ScaledCopyThermalEquilibrium.self_scale
    (hT2 : ScaledCopyThermalEquilibrium R) (x : X) {r : ℝ≥0} (hr : 0 < r) :
    R x (r • x) := by
  have hsum : 0 < 1 + r := by positivity
  have hlt : r / (1 + r) < 1 := (div_lt_one hsum).2 (by simp)
  have hleft : (1 - r / (1 + r)) * (1 + r) = 1 := by
    rw [tsub_mul, one_mul, div_mul_cancel₀ _ hsum.ne', add_tsub_cancel_right]
  have hright : r / (1 + r) * (1 + r) = r := div_mul_cancel₀ _ hsum.ne'
  simpa only [smul_smul, hleft, hright, one_smul] using
    hT2 ((1 + r) • x) (r / (1 + r)) (div_pos hr hsum) hlt

/-- LY Theorem 4.1: positive scaling of either system preserves thermal
equilibrium. T2, symmetry, and the zeroth law T3 are explicit premises. -/
theorem ScaledCopyThermalEquilibrium.scale_iff
    (hT2 : ScaledCopyThermalEquilibrium R) (hsymm : ∀ {x y}, R x y → R y x)
    (hT3 : ∀ {x y z}, R x y → R y z → R x z)
    (x y : X) {r s : ℝ≥0} (hr : 0 < r) (hs : 0 < s) :
    R x y ↔ R (r • x) (s • y) := by
  have hx := hT2.self_scale x hr
  have hy := hT2.self_scale y hs
  exact ⟨fun h => hT3 (hsymm hx) (hT3 h hy),
    fun h => hT3 hx (hT3 h (hsymm hy))⟩

/-- Diagnostic for an invalid empty-system extension: endpoint-inclusive
scaled-copy thermal equilibrium, symmetry, and T3 make the raw relation
universal when every zero-scaled state is the same empty state. This does not
assert any inconsistency in LY's typed, endpoint-inclusive adiabatic splitting
statement. The proof uses only the endpoint `t = 0`. -/
theorem thermal_relation_universal_of_endpoint_split
    (hzero : ∀ x : X, (0 : ℝ≥0) • x = 0)
    (hinclusive : ∀ (x : X) (t : ℝ≥0), t ≤ 1 →
      R ((1 - t) • x) (t • x))
    (hsymm : ∀ {x y}, R x y → R y x)
    (hT3 : ∀ {x y z}, R x y → R y z → R x z) :
    ∀ x y, R x y := by
  have hempty : ∀ x : X, R x 0 := by
    intro x
    simpa only [tsub_zero, one_smul, hzero] using hinclusive x 0 zero_le_one
  intro x y
  exact hT3 (hempty x) (hsymm (hempty y))

end Accessibility

namespace ThermalJoin

variable {X W₁ W₂ : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
variable {P : Accessibility X} {Γ₁ : Set (ℝ × W₁)} {Γ₂ : Set (ℝ × W₂)}
variable {represent₁ : Γ₁ → X} {represent₂ : Γ₂ → X}
variable (J : ThermalJoin P Γ₁ Γ₂ represent₁ represent₂)

/-- A raw thermal relation represents the thermal equilibrium of this typed
join exactly when it agrees with reversible thermal contact on its two domains.
This is a compatibility premise, independent of contact and splitting. -/
def RealizesThermalEquilibrium (R : X → X → Prop) : Prop :=
  ∀ x y, R (represent₁ x) (represent₂ y) ↔ J.Equilibrium x y

/-- The typed compatibility premise transfers LY Theorem 4.1 to this join. -/
theorem RealizesThermalEquilibrium.iff_scaled {R : X → X → Prop}
    (hR : J.RealizesThermalEquilibrium R)
    (hT2 : Accessibility.ScaledCopyThermalEquilibrium R)
    (hsymm : ∀ {x y}, R x y → R y x)
    (hT3 : ∀ {x y z}, R x y → R y z → R x z)
    (x : Γ₁) (y : Γ₂) {r s : ℝ≥0} (hr : 0 < r) (hs : 0 < s) :
    J.Equilibrium x y ↔ R (r • represent₁ x) (s • represent₂ y) :=
  (hR x y).symm.trans (hT2.scale_iff hsymm hT3 _ _ hr hs)

/-- Entropy completeness within a conserved label characterizes equilibrium by
equality between the joined entropy and the sum of the split entropies. -/
theorem equilibrium_iff_entropy_eq {L : Type*} (label : X → L)
    (preserved : ∀ {u v}, P.relation u v → label u = label v)
    (S : X →+ ℝ)
    (complete : ∀ u v, label u = label v → (P.relation u v ↔ S u ≤ S v))
    (x : Γ₁) (y : Γ₂) :
    J.Equilibrium x y ↔
      S (J.represent (joinedState x y)) = S (represent₁ x) + S (represent₂ y) := by
  have hlabel := preserved (J.contact x y)
  have hforward := (complete _ _ hlabel).1 (J.contact x y)
  change P.relation (J.represent (joinedState x y)) (represent₁ x + represent₂ y) ↔ _
  rw [complete _ _ hlabel.symm]
  simp only [map_add] at hforward ⊢
  exact ⟨fun h => le_antisymm h hforward, fun h => h.le⟩

/-- Under the typed compatibility premise, the raw thermal relation has the
same entropy characterization as equilibrium of the join. -/
theorem RealizesThermalEquilibrium.iff_entropy_eq {R : X → X → Prop}
    (hR : J.RealizesThermalEquilibrium R) {L : Type*} (label : X → L)
    (preserved : ∀ {u v}, P.relation u v → label u = label v)
    (S : X →+ ℝ)
    (complete : ∀ u v, label u = label v → (P.relation u v ↔ S u ≤ S v))
    (x : Γ₁) (y : Γ₂) :
    R (represent₁ x) (represent₂ y) ↔
      S (J.represent (joinedState x y)) = S (represent₁ x) + S (represent₂ y) :=
  (hR x y).trans (J.equilibrium_iff_entropy_eq label preserved S complete x y)

end ThermalJoin

end ProjectAInos.Thermodynamics.Physical
