module

public import ProjectAInos.Thermodynamics.Basic
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Monoid.Defs

/-!
# Composite states and the adiabatic quotient

Finite expressions provide a strict composition and scaling interface after
quotienting by structural coherence. Splitting and recombination are additional
accessibility premises. They become scalar additivity only after quotienting by
mutual accessibility. The physical premises are fields of `Accessibility`.
-/

@[expose] public section

open scoped NNReal Topology

namespace ProjectAInos.Thermodynamics.Physical

/-- Formal finite composites of atomic equilibrium states. -/
inductive Composite (A : Type*) where
  | atom : A → Composite A
  | empty : Composite A
  | compose : Composite A → Composite A → Composite A
  | scale : ℝ≥0 → Composite A → Composite A

/-- Structural coherence of composition and scaling, before adiabatic equivalence. -/
inductive StructuralEquiv {A : Type*} : Composite A → Composite A → Prop where
  | refl (x) : StructuralEquiv x x
  | symm {x y} : StructuralEquiv x y → StructuralEquiv y x
  | trans {x y z} : StructuralEquiv x y → StructuralEquiv y z → StructuralEquiv x z
  | compose {x x' y y'} : StructuralEquiv x x' → StructuralEquiv y y' →
      StructuralEquiv (.compose x y) (.compose x' y')
  | scale (a) {x y} : StructuralEquiv x y → StructuralEquiv (.scale a x) (.scale a y)
  | assoc (x y z) : StructuralEquiv (.compose (.compose x y) z) (.compose x (.compose y z))
  | comm (x y) : StructuralEquiv (.compose x y) (.compose y x)
  | empty_left (x) : StructuralEquiv (.compose .empty x) x
  | empty_right (x) : StructuralEquiv (.compose x .empty) x
  | scale_one (x) : StructuralEquiv (.scale 1 x) x
  | scale_mul (a b) (x) : StructuralEquiv (.scale (a * b) x) (.scale a (.scale b x))
  | scale_compose (a) (x y) :
      StructuralEquiv (.scale a (.compose x y)) (.compose (.scale a x) (.scale a y))
  | scale_empty (a) : StructuralEquiv (.scale a .empty) .empty
  | scale_zero (x) : StructuralEquiv (.scale 0 x) .empty

/-- The equivalence relation used to impose structural coherence. -/
def structuralSetoid (A : Type*) : Setoid (Composite A) where
  r := StructuralEquiv
  iseqv := ⟨StructuralEquiv.refl, StructuralEquiv.symm, StructuralEquiv.trans⟩

/-- Composite states with reassociation, permutations and scaling coherence identified. -/
def CompositeState (A : Type*) := Quotient (structuralSetoid A)

namespace CompositeState

variable {A : Type*}

/-- The structural class of a finite expression. -/
def mk (x : Composite A) : CompositeState A := Quotient.mk _ x

instance : Zero (CompositeState A) := ⟨mk .empty⟩

instance : Add (CompositeState A) where
  add := Quotient.map₂ Composite.compose (fun _ _ hx _ _ hy => StructuralEquiv.compose hx hy)

instance : SMul ℝ≥0 (CompositeState A) where
  smul a := Quotient.map (Composite.scale a) (fun _ _ h => StructuralEquiv.scale a h)

instance : AddCommMonoid (CompositeState A) where
  add_assoc x y z := Quotient.inductionOn₃ x y z fun x y z =>
    Quotient.sound (StructuralEquiv.assoc x y z)
  zero_add x := Quotient.inductionOn x fun x => Quotient.sound (StructuralEquiv.empty_left x)
  add_zero x := Quotient.inductionOn x fun x => Quotient.sound (StructuralEquiv.empty_right x)
  add_comm x y := Quotient.inductionOn₂ x y fun x y => Quotient.sound (StructuralEquiv.comm x y)
  nsmul := nsmulRec

instance : DistribMulAction ℝ≥0 (CompositeState A) where
  one_smul x := Quotient.inductionOn x fun x => Quotient.sound (StructuralEquiv.scale_one x)
  mul_smul a b x := Quotient.inductionOn x fun x =>
    Quotient.sound (StructuralEquiv.scale_mul a b x)
  smul_zero a := Quotient.sound (StructuralEquiv.scale_empty a)
  smul_add a x y := Quotient.inductionOn₂ x y fun x y =>
    Quotient.sound (StructuralEquiv.scale_compose a x y)

@[simp] theorem zero_scale (x : CompositeState A) : (0 : ℝ≥0) • x = 0 := by
  induction x using Quotient.inductionOn with
  | h x => exact Quotient.sound (StructuralEquiv.scale_zero x)

end CompositeState

/-- The usual normalized splitting premise A5. -/
def NormalizedSplitting {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    (r : X → X → Prop) : Prop :=
  ∀ (t : ℝ≥0), 0 < t → t < 1 → ∀ x : X,
    r x (t • x + (1 - t) • x) ∧ r (t • x + (1 - t) • x) x

/-- Normalized splitting yields the homogeneous form used by `Accessibility`. -/
theorem splitting_of_normalized {X : Type*} [AddCommMonoid X]
    [DistribMulAction ℝ≥0 X] {r : X → X → Prop}
    (hrefl : ∀ x, r x x) (hzero : ∀ x : X, (0 : ℝ≥0) • x = 0)
    (hsplit : NormalizedSplitting r) (a b : ℝ≥0) (x : X) :
    r ((a + b) • x) (a • x + b • x) ∧ r (a • x + b • x) ((a + b) • x) := by
  by_cases ha : a = 0
  · simp only [ha, zero_add, hzero]
    exact ⟨hrefl _, hrefl _⟩
  by_cases hb : b = 0
  · simp only [hb, add_zero, hzero]
    exact ⟨hrefl _, hrefl _⟩
  have ha' : 0 < a := pos_iff_ne_zero.mpr ha
  have hb' : 0 < b := pos_iff_ne_zero.mpr hb
  have hab : 0 < a + b := add_pos ha' hb'
  have ht : a / (a + b) < 1 := (div_lt_one hab).2 (lt_add_of_pos_right a hb')
  have hfirst : a / (a + b) * (a + b) = a := div_mul_cancel₀ _ hab.ne'
  have hsecond : (1 - a / (a + b)) * (a + b) = b := by
    rw [tsub_mul, one_mul, hfirst, add_tsub_cancel_left]
  have h := hsplit (a / (a + b)) (div_pos ha' hab) ht ((a + b) • x)
  simpa only [smul_smul, hfirst, hsecond] using h

/-- A1–A6 on a coherent composition model. The splitting field includes zero
endpoints, whose identities are supplied by the formal empty system. -/
structure Accessibility (X : Type*) [AddCommMonoid X] [DistribMulAction ℝ≥0 X] where
  relation : X → X → Prop
  refl : ∀ x, relation x x
  trans : ∀ {x y z}, relation x y → relation y z → relation x z
  add_mono : ∀ {x y z w}, relation x y → relation z w → relation (x + z) (y + w)
  scale_mono : ∀ (a : ℝ≥0) {x y}, relation x y → relation (a • x) (a • y)
  zero_scale : ∀ x : X, (0 : ℝ≥0) • x = 0
  split : ∀ (a b : ℝ≥0) (x : X),
    relation ((a + b) • x) (a • x + b • x) ∧ relation (a • x + b • x) ((a + b) • x)
  stable : ∀ (x y z₀ z₁ : X) (ε : ℕ → ℝ≥0),
    (∀ n, 0 < ε n) → Filter.Tendsto ε Filter.atTop (nhds 0) →
    (∀ n, relation (x + ε n • z₀) (y + ε n • z₁)) → relation x y

namespace Accessibility

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
variable (P : Accessibility X)

/-- Mutual accessibility is an equivalence relation. -/
def adiabaticSetoid : Setoid X where
  r x y := P.relation x y ∧ P.relation y x
  iseqv := ⟨fun x => ⟨P.refl x, P.refl x⟩, fun h => ⟨h.2, h.1⟩,
    fun h g => ⟨P.trans h.1 g.1, P.trans g.2 h.2⟩⟩

/-- States modulo adiabatic equivalence. -/
def StateSpace := Quotient P.adiabaticSetoid

/-- Projection from a physical state to its adiabatic class. -/
def stateClass (x : X) : P.StateSpace := Quotient.mk _ x

instance : Zero P.StateSpace := ⟨P.stateClass 0⟩

instance : Add P.StateSpace where
  add := Quotient.map₂ (· + ·) (fun _ _ h _ _ g => ⟨P.add_mono h.1 g.1, P.add_mono h.2 g.2⟩)

instance : SMul ℝ≥0 P.StateSpace where
  smul a := Quotient.map (a • ·) (fun _ _ h => ⟨P.scale_mono a h.1, P.scale_mono a h.2⟩)

instance : AddCommMonoid P.StateSpace where
  add_assoc x y z := Quotient.inductionOn₃ x y z fun x y z => congrArg P.stateClass (add_assoc x y z)
  zero_add x := Quotient.inductionOn x fun x => congrArg P.stateClass (zero_add x)
  add_zero x := Quotient.inductionOn x fun x => congrArg P.stateClass (add_zero x)
  add_comm x y := Quotient.inductionOn₂ x y fun x y => congrArg P.stateClass (add_comm x y)
  nsmul := nsmulRec

instance : Module ℝ≥0 P.StateSpace where
  one_smul x := Quotient.inductionOn x fun x => congrArg P.stateClass (one_smul ℝ≥0 x)
  mul_smul a b x := Quotient.inductionOn x fun x => congrArg P.stateClass (mul_smul a b x)
  smul_zero a := congrArg P.stateClass (smul_zero a)
  smul_add a x y := Quotient.inductionOn₂ x y fun x y => congrArg P.stateClass (smul_add a x y)
  add_smul a b x := Quotient.inductionOn x fun x => Quotient.sound (P.split a b x)
  zero_smul x := Quotient.inductionOn x fun x => congrArg P.stateClass (P.zero_scale x)

instance : PartialOrder P.StateSpace where
  le := Quotient.lift₂ P.relation (fun _ _ _ _ h g =>
    propext ⟨fun hxy => P.trans h.2 (P.trans hxy g.1),
      fun hxy => P.trans h.1 (P.trans hxy g.2)⟩)
  le_refl x := Quotient.inductionOn x P.refl
  le_trans x y z := Quotient.inductionOn₃ x y z fun _ _ _ => P.trans
  le_antisymm x y := Quotient.inductionOn₂ x y fun _ _ h g => Quotient.sound ⟨h, g⟩

@[simp] theorem stateClass_le (x y : X) : P.stateClass x ≤ P.stateClass y ↔ P.relation x y := Iff.rfl

@[simp] theorem stateClass_eq (x y : X) :
    P.stateClass x = P.stateClass y ↔ P.relation x y ∧ P.relation y x := Quotient.eq

@[simp] theorem stateClass_zero : P.stateClass 0 = 0 := rfl

@[simp] theorem stateClass_add (x y : X) :
    P.stateClass (x + y) = P.stateClass x + P.stateClass y := rfl

@[simp] theorem stateClass_scale (a : ℝ≥0) (x : X) :
    P.stateClass (a • x) = a • P.stateClass x := rfl

instance : IsOrderedAddMonoid P.StateSpace where
  add_le_add_left x y h z := by
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        induction z using Quotient.inductionOn with
        | h z => exact P.add_mono h (P.refl z)

instance : PosSMulMono ℝ≥0 P.StateSpace where
  smul_le_smul_of_nonneg_left {a} _ {x y} h := by
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y => exact P.scale_mono a h

/-- A6 passes to the adiabatic quotient using fixed representatives. -/
theorem stability : Stability P.StateSpace := by
  intro x y z₀ z₁ ε hε hlim h
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      induction z₀ using Quotient.inductionOn with
      | h z₀ =>
        induction z₁ using Quotient.inductionOn with
        | h z₁ => exact P.stable x y z₀ z₁ ε hε hlim h

end Accessibility
end ProjectAInos.Thermodynamics.Physical
