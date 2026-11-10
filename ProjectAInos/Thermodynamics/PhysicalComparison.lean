module

public import ProjectAInos.Thermodynamics.Physical
public import ProjectAInos.Thermodynamics.Entropy
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.BigOperators.Field

/-!
# Composition labels and physical comparison interfaces

Labels evaluate finite composite expressions in a semimodule of amounts.
Comparison on common scaled products transfers to exchange comparison of
adiabatic classes. The common-product and comparison premises are explicit
until their physical realizations have been established.
-/

@[expose] public section

open scoped NNReal

namespace ProjectAInos.Thermodynamics.Physical

variable {A D : Type*} [AddCommMonoid D] [Module ℝ≥0 D]

/-- Evaluation of a composite's extensive composition label. -/
def Composite.label (label : A → D) : Composite A → D
  | .atom x => label x
  | .empty => 0
  | .compose x y => x.label label + y.label label
  | .scale a x => a • x.label label

/-- Structural identifications preserve extensive composition labels. -/
theorem StructuralEquiv.label_eq {x y : Composite A} (h : StructuralEquiv x y)
    (label : A → D) : x.label label = y.label label := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | compose _ _ ih₁ ih₂ => exact congrArg₂ (· + ·) ih₁ ih₂
  | scale a _ ih => exact congrArg (a • ·) ih
  | assoc => exact add_assoc _ _ _
  | comm => exact add_comm _ _
  | empty_left => exact zero_add _
  | empty_right => exact add_zero _
  | scale_one => exact one_smul _ _
  | scale_mul => exact mul_smul _ _ _
  | scale_compose => exact smul_add _ _ _
  | scale_empty => exact smul_zero _
  | scale_zero => exact zero_smul _ _

/-- Composition labels descend to the quotient by S0. -/
def CompositeState.label (label : A → D) : CompositeState A →+ D where
  toFun := Quotient.lift (Composite.label label) (fun _ _ h => h.label_eq label)
  map_zero' := rfl
  map_add' x y := Quotient.inductionOn₂ x y fun _ _ => rfl

@[simp] theorem CompositeState.label_mk (label : A → D) (x : Composite A) :
    CompositeState.label label (CompositeState.mk x) = x.label label := rfl

@[simp] theorem CompositeState.label_scale (label : A → D) (a : ℝ≥0)
    (x : CompositeState A) :
    CompositeState.label label (a • x) = a • CompositeState.label label x := by
  induction x using Quotient.inductionOn with
  | h x => rfl

namespace Accessibility

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
variable (P : Accessibility X)
variable {L : Type*} [AddCommMonoid L]

/-- A conserved composition label descends to adiabatic classes. -/
def sectorLabel (label : X →+ L)
    (preserved : ∀ {x y}, P.relation x y → label x = label y) : P.StateSpace →+ L where
  toFun := Quotient.lift label (fun _ _ h => preserved h.1)
  map_zero' := label.map_zero
  map_add' x y := Quotient.inductionOn₂ x y fun x y => label.map_add x y

@[simp] theorem sectorLabel_stateClass (label : X →+ L)
    (preserved : ∀ {x y}, P.relation x y → label x = label y) (x : X) :
    P.sectorLabel label preserved (P.stateClass x) = label x := rfl

/-- A realization in one comparable product transfers comparison to the original states. -/
theorem comparable_of_common_product {I : Type*} {Product : I → Type*}
    (realize : ∀ i, Product i → X)
    (comparison : ∀ i (u v : Product i),
      P.relation (realize i u) (realize i v) ∨ P.relation (realize i v) (realize i u))
    {x y : X}
    (common : ∃ i, ∃ u v : Product i,
      (P.relation x (realize i u) ∧ P.relation (realize i u) x) ∧
      (P.relation y (realize i v) ∧ P.relation (realize i v) y)) :
    P.relation x y ∨ P.relation y x := by
  obtain ⟨i, u, v, hx, hy⟩ := common
  rcases comparison i u v with h | h
  · exact Or.inl (P.trans hx.1 (P.trans h hy.2))
  · exact Or.inr (P.trans hy.1 (P.trans h hx.2))

/-- Sector preservation and common-product realizations give exchange comparison
on the physical adiabatic quotient. -/
theorem exchangeComparison_of_common_products (label : X →+ L)
    (preserved : ∀ {x y}, P.relation x y → label x = label y)
    {I : Type*} {Product : I → Type*} (realize : ∀ i, Product i → X)
    (comparison : ∀ i (u v : Product i),
      P.relation (realize i u) (realize i v) ∨ P.relation (realize i v) (realize i u))
    (common : ∀ x y, label x = label y → ∃ i, ∃ u v : Product i,
      (P.relation x (realize i u) ∧ P.relation (realize i u) x) ∧
      (P.relation y (realize i v) ∧ P.relation (realize i v) y)) :
    ExchangeComparison P.StateSpace := by
  apply exchangeComparison_of_sectors (P.sectorLabel label preserved)
  · intro x y
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y => exact preserved
  · intro x y
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        intro h
        exact P.comparable_of_common_product realize comparison (common x y h)

/-- The adiabatic projection respects composition. -/
def stateClassHom : X →+ P.StateSpace where
  toFun := P.stateClass
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Entropy existence on physical representatives, normalized by a strict process.
The conserved sector is the universal quotient of the completion. -/
theorem exists_physical_entropy (hECH : ExchangeComparison P.StateSpace)
    {x₀ x₁ : X} (hstrict : P.relation x₀ x₁ ∧ ¬ P.relation x₁ x₀) :
    ∃ S : X →+ ℝ,
      (∀ (a : ℝ≥0) x, S (a • x) = (a : ℝ) * S x) ∧
      (∀ x y, P.relation x y → S x ≤ S y) ∧ S x₁ - S x₀ = 1 ∧
      ∀ x y,
        (processSpan P.StateSpace).mkQ (Completion.of (P.stateClass x)) =
          (processSpan P.StateSpace).mkQ (Completion.of (P.stateClass y)) →
        (P.relation x y ↔ S x ≤ S y) := by
  have hstrict' : P.stateClass x₀ < P.stateClass x₁ :=
    lt_iff_le_not_ge.mpr hstrict
  obtain ⟨S, hmono, hunit, hsector⟩ := exists_normalized_entropy P.stability hECH hstrict'
  refine ⟨S.toAddMonoidHom.comp P.stateClassHom, ?_, ?_, hunit, ?_⟩
  · intro a x
    change S (a • P.stateClass x) = (a : ℝ) * S (P.stateClass x)
    rw [map_smul]
    rfl
  · intro x y h
    exact hmono h
  · intro x y h
    exact hsector (P.stateClass x) (P.stateClass y) h

/-- The forward set in one coordinate state space. -/
def forwardSector {E : Type*} (domain : Set E) (represent : E → X) (x : E) : Set E :=
  {y | y ∈ domain ∧ P.relation (represent x) (represent y)}

/-- A7, composition and splitting imply convexity of every forward sector. -/
theorem forwardSector_convex {E : Type*} [AddCommGroup E] [Module ℝ E]
    (domain : Set E) (represent : E → X) (hconvex : Convex ℝ domain)
    (mixing : ∀ x ∈ domain, ∀ y ∈ domain, ∀ a b : ℝ≥0, a + b = 1 →
      P.relation (a • represent x + b • represent y)
        (represent ((a : ℝ) • x + (b : ℝ) • y))) (x : E) :
    Convex ℝ (P.forwardSector domain represent x) := by
  intro y hy z hz a b ha hb hab
  refine ⟨hconvex hy.1 hz.1 ha hb hab, ?_⟩
  let a' : ℝ≥0 := ⟨a, ha⟩
  let b' : ℝ≥0 := ⟨b, hb⟩
  have hab' : a' + b' = 1 := NNReal.eq hab
  have hsplit : P.relation (represent x) (a' • represent x + b' • represent x) := by
    simpa only [hab', one_smul] using (P.split a' b' (represent x)).1
  exact P.trans hsplit (P.trans
    (P.add_mono (P.scale_mono a' hy.2) (P.scale_mono b' hz.2))
    (mixing y hy.1 z hz.1 a' b' hab'))

@[simp] theorem stateClass_sum {ι : Type*} (s : Finset ι) (x : ι → X) :
    P.stateClass (∑ i ∈ s, x i) = ∑ i ∈ s, P.stateClass (x i) :=
  map_sum P.stateClassHom x s

/-- LY Lemma 3.1. If an interior point of a segment can reach the far endpoint,
then the other endpoint can reach that interior point. -/
theorem collinear_accessibility {E : Type*} [AddCommGroup E] [Module ℝ E]
    (domain : Set E) (represent : E → X)
    (mixing : ∀ x ∈ domain, ∀ z ∈ domain, ∀ a b : ℝ≥0, a + b = 1 →
      P.relation (a • represent x + b • represent z)
        (represent ((a : ℝ) • x + (b : ℝ) • z)))
    {x y z : E} (hx : x ∈ domain) (hz : z ∈ domain)
    {a b : ℝ≥0} (ha : 0 < a) (hab : a + b = 1)
    (hy : y = (a : ℝ) • x + (b : ℝ) • z)
    (hyz : P.relation (represent y) (represent z)) :
    P.relation (represent x) (represent y) := by
  have hmix : P.relation (a • represent x + b • represent z) (represent y) := by
    simpa only [← hy] using mixing x hx z hz a b hab
  have hsplit : P.relation (represent y) (a • represent y + b • represent y) := by
    simpa only [hab, one_smul] using (P.split a b (represent y)).1
  have hraw := P.trans hmix (P.trans hsplit
    (P.add_mono (P.refl (a • represent y)) (P.scale_mono b hyz)))
  have hcancel : P.stateClass (a • represent x) ≤ P.stateClass (a • represent y) := by
    apply P.stability.le_of_add_le_add_right (z := P.stateClass (b • represent z))
    exact hraw
  have h := P.scale_mono a⁻¹ hcancel
  simpa only [smul_smul, inv_mul_cancel₀ ha.ne', one_smul] using h

/-- A common refinement of the amounts in two finite scaled products. -/
noncomputable def refinementWeight {ι κ : Type*} [Fintype ι] (a : ι → ℝ≥0) (b : κ → ℝ≥0)
    (i : ι) (j : κ) : ℝ≥0 := a i * b j / ∑ k, a k

theorem refinementWeight_pos {ι κ : Type*} [Fintype ι]
    (a : ι → ℝ≥0) (b : κ → ℝ≥0) (hT : 0 < ∑ k, a k)
    (i : ι) (j : κ) (ha : 0 < a i) (hb : 0 < b j) :
    0 < refinementWeight a b i j := div_pos (mul_pos ha hb) hT

theorem refinementWeight_row_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ≥0) (b : κ → ℝ≥0) (hT : 0 < ∑ k, a k)
    (hab : ∑ i, a i = ∑ j, b j) (i : ι) :
    ∑ j, refinementWeight a b i j = a i := by
  simp only [refinementWeight, ← Finset.sum_div, ← Finset.mul_sum, ← hab]
  exact mul_div_cancel_right₀ _ hT.ne'

theorem refinementWeight_column_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ≥0) (b : κ → ℝ≥0) (hT : 0 < ∑ k, a k) (j : κ) :
    ∑ i, refinementWeight a b i j = b j := by
  simp only [refinementWeight, ← Finset.sum_div, ← Finset.sum_mul]
  exact mul_div_cancel_left₀ _ hT.ne'

/-- Splitting realizes two finite composites with equal total amount using
exactly the same refined array of nonnegative amounts. -/
theorem common_refinement {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ≥0) (b : κ → ℝ≥0) (hT : 0 < ∑ k, a k)
    (hab : ∑ i, a i = ∑ j, b j) (x : ι → X) (y : κ → X) :
    P.stateClass (∑ i, a i • x i) =
      P.stateClass (∑ i, ∑ j, refinementWeight a b i j • x i) ∧
    P.stateClass (∑ j, b j • y j) =
      P.stateClass (∑ i, ∑ j, refinementWeight a b i j • y j) := by
  constructor
  · simp only [stateClass_sum, stateClass_scale, ← Finset.sum_smul,
      refinementWeight_row_sum a b hT hab]
  · simp only [stateClass_sum, stateClass_scale]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, refinementWeight_column_sum a b hT]

/-- The scaled-copy clause of thermal splitting T2 requires proportional copies
of a single state to be in thermal equilibrium. Both copies have positive amount:
the endpoint-inclusive adiabatic splitting law does not assert thermal equilibrium
with the empty state. -/
def ScaledCopyThermalEquilibrium (thermalEquilibrium : X → X → Prop) : Prop :=
  ∀ (x : X) (t : ℝ≥0), 0 < t → t < 1 →
    thermalEquilibrium ((1 - t) • x) (t • x)

end Accessibility

/-- The coordinate domain of the thermal join, with a single total energy. -/
def joinedDomain {W₁ W₂ : Type*} (Γ₁ : Set (ℝ × W₁)) (Γ₂ : Set (ℝ × W₂)) :
    Set (ℝ × W₁ × W₂) :=
  {z | ∃ U₁ U₂ : ℝ, (U₁, z.2.1) ∈ Γ₁ ∧ (U₂, z.2.2) ∈ Γ₂ ∧ z.1 = U₁ + U₂}

/-- Thermal joining preserves both work coordinates and sums the energies. -/
def joinedState {W₁ W₂ : Type*} {Γ₁ : Set (ℝ × W₁)} {Γ₂ : Set (ℝ × W₂)}
    (x : Γ₁) (y : Γ₂) : joinedDomain Γ₁ Γ₂ :=
  ⟨(x.val.1 + y.val.1, x.val.2, y.val.2),
    x.val.1, y.val.1, x.property, y.property, rfl⟩

/-- Coordinate and accessibility data for thermal contact and splitting.
The simple-system geometry of the join is a separate input to physical comparison.
The scaled-copy equilibrium clause is `ScaledCopyThermalEquilibrium`. -/
structure ThermalJoin {X W₁ W₂ : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    (P : Accessibility X) (Γ₁ : Set (ℝ × W₁)) (Γ₂ : Set (ℝ × W₂))
    (represent₁ : Γ₁ → X) (represent₂ : Γ₂ → X) where
  represent : joinedDomain Γ₁ Γ₂ → X
  contact : ∀ x y, P.relation (represent₁ x + represent₂ y) (represent (joinedState x y))
  splitting : ∀ z, ∃ x y, joinedState x y = z ∧
    P.relation (represent z) (represent₁ x + represent₂ y)

namespace ThermalJoin

variable {X W₁ W₂ : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
variable {P : Accessibility X} {Γ₁ : Set (ℝ × W₁)} {Γ₂ : Set (ℝ × W₂)}
variable {represent₁ : Γ₁ → X} {represent₂ : Γ₂ → X}
variable (J : ThermalJoin P Γ₁ Γ₂ represent₁ represent₂)

/-- A split is in thermal equilibrium when joining can be undone adiabatically. -/
def Equilibrium (x : Γ₁) (y : Γ₂) : Prop :=
  P.relation (J.represent (joinedState x y)) (represent₁ x + represent₂ y)

/-- Thermal contact and splitting realize the maximum of an additive monotone
entropy over the admissible energy allocations. -/
theorem entropy_maximum (S : X →+ ℝ)
    (hmono : ∀ x y, P.relation x y → S x ≤ S y) (z : joinedDomain Γ₁ Γ₂) :
    ∃ x y, joinedState x y = z ∧ J.Equilibrium x y ∧
      S (J.represent z) = S (represent₁ x) + S (represent₂ y) ∧
      ∀ u v, joinedState u v = z →
        S (represent₁ u) + S (represent₂ v) ≤ S (J.represent z) := by
  obtain ⟨x, y, hxy, hsplit⟩ := J.splitting z
  have hbound : ∀ u v, joinedState u v = z →
      S (represent₁ u) + S (represent₂ v) ≤ S (J.represent z) := by
    intro u v huv
    have h := hmono _ _ (J.contact u v)
    simpa only [huv, map_add] using h
  refine ⟨x, y, hxy, ?_, ?_, hbound⟩
  · simpa only [Equilibrium, hxy] using hsplit
  · apply le_antisymm
    · simpa only [map_add] using hmono _ _ hsplit
    · exact hbound x y hxy

end ThermalJoin
end ProjectAInos.Thermodynamics.Physical
