module

public import ProjectAInos.Thermodynamics.Nonreactive
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Common scaled products for equal compositions

Finite composite expressions admit weighted-atom normal forms modulo adiabatic
splitting. Equal composition labels give a common refinement of their atom
amounts. Product comparison can therefore be transferred to arbitrary states
of equal composition without assuming a common-product realization.
-/

@[expose] public section

open scoped NNReal BigOperators

namespace ProjectAInos.Thermodynamics.Physical

namespace CompositeState

/-- The weighted multiset of atoms in a finite composite. Combining repeated
atoms here is interpreted by splitting only after passing to adiabatic classes. -/
noncomputable def atomAmounts (A : Type*) : CompositeState A →+ (A →₀ ℝ≥0) :=
  label (fun a => Finsupp.single a 1)

@[simp] theorem atomAmounts_scale {A : Type*} (r : ℝ≥0) (x : CompositeState A) :
    atomAmounts A (r • x) = r • atomAmounts A x := label_scale _ r x

/-- Every additive extensive evaluation is the finite linear combination of
its values on atomic states. -/
theorem eval_atomAmounts {A D : Type*} [AddCommMonoid D] [Module ℝ≥0 D]
    (f : CompositeState A →+ D)
    (hscale : ∀ (r : ℝ≥0) x, f (r • x) = r • f x) (x : CompositeState A) :
    f x = Finsupp.linearCombination ℝ≥0 (fun a => f (mk (.atom a))) (atomAmounts A x) := by
  induction x using Quotient.inductionOn with
  | h x =>
    induction x with
    | atom a =>
      change f (mk (.atom a)) = Finsupp.linearCombination ℝ≥0 _ (Finsupp.single a 1)
      simp
    | empty =>
      change f 0 = Finsupp.linearCombination ℝ≥0 _ 0
      simp
    | compose x y ihx ihy =>
      change f (mk x + mk y) = Finsupp.linearCombination ℝ≥0 _
        (atomAmounts A (mk x) + atomAmounts A (mk y))
      rw [map_add, map_add]
      exact congrArg₂ (· + ·) ihx ihy
    | scale r x ih =>
      change f (r • mk x) = Finsupp.linearCombination ℝ≥0 _ (r • atomAmounts A (mk x))
      rw [hscale, map_smul]
      exact congrArg (r • ·) ih

/-- A finite scaled-atom normal form, indexed by the nonzero atom amounts. -/
theorem eval_atomAmounts_sum {A D : Type*} [AddCommMonoid D] [Module ℝ≥0 D]
    (f : CompositeState A →+ D)
    (hscale : ∀ (r : ℝ≥0) x, f (r • x) = r • f x) (x : CompositeState A) :
    f x = ∑ a : (atomAmounts A x).support, atomAmounts A x a.val • f (mk (.atom a.val)) := by
  classical
  rw [eval_atomAmounts f hscale x, Finsupp.linearCombination_apply, Finsupp.sum]
  exact (Finset.sum_coe_sort _ _).symm

end CompositeState

namespace Nonreactive

variable {Γ : Type*} (State : Γ → Type*)

/-- A finite product shape, including zero amounts and the empty product. -/
structure ScaledProduct where
  count : ℕ
  system : Fin count → Γ
  amount : Fin count → ℝ≥0

/-- States in a fixed finite scaled product. -/
def ScaledProduct.States (p : ScaledProduct (Γ := Γ)) := ∀ i, State (p.system i)

/-- Realization of a fixed product as a coherent composite. -/
noncomputable def ScaledProduct.realize (p : ScaledProduct (Γ := Γ))
    (x : p.States State) : CompositeState (Σ g, State g) :=
  ∑ i, p.amount i • CompositeState.mk (.atom ⟨p.system i, x i⟩)

/-- Reindex any finite family as a product shape. -/
noncomputable def ScaledProduct.ofFamily {ι : Type*} [Fintype ι]
    (g : ι → Γ) (a : ι → ℝ≥0) : ScaledProduct (Γ := Γ) where
  count := Fintype.card ι
  system i := g ((Fintype.equivFin ι).symm i)
  amount i := a ((Fintype.equivFin ι).symm i)

noncomputable def ScaledProduct.statesOfFamily {ι : Type*} [Fintype ι]
    (g : ι → Γ) (a : ι → ℝ≥0) (x : ∀ i, State (g i)) :
    (ScaledProduct.ofFamily g a).States State :=
  fun i => x ((Fintype.equivFin ι).symm i)

theorem ScaledProduct.realize_ofFamily {ι : Type*} [Fintype ι]
    (g : ι → Γ) (a : ι → ℝ≥0) (x : ∀ i, State (g i)) :
    (ScaledProduct.ofFamily g a).realize State
      (ScaledProduct.statesOfFamily State g a x) =
        ∑ i, a i • CompositeState.mk (.atom ⟨g i, x i⟩) := by
  exact (Fintype.equivFin ι).symm.sum_comp
    (fun i => a i • CompositeState.mk (.atom (⟨g i, x i⟩ : Σ g, State g)))

/-- The total amount of one system type in an indexed weighted family. -/
noncomputable def typeAmount {ι : Type*} [Fintype ι]
    (system : ι → Γ) (amount : ι → ℝ≥0) (g : Γ) : ℝ≥0 := by
  classical
  exact ∑ i, if system i = g then amount i else 0

theorem typeAmount_pos {ι : Type*} [Fintype ι]
    (system : ι → Γ) (amount : ι → ℝ≥0) (i : ι) (hi : 0 < amount i) :
    0 < typeAmount system amount (system i) := by
  classical
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
    show (0 : ℝ≥0) ≤ if system j = system i then amount j else 0 from zero_le)
    (Finset.mem_univ i)
  exact hi.trans_le (by simpa [typeAmount] using h)

/-- Refinement pairs of different system types have zero amount. Pairs of
the same type share its total amount as denominator. -/
noncomputable def transportAmount {ι κ : Type*} [Fintype ι]
    (g : ι → Γ) (h : κ → Γ) (a : ι → ℝ≥0) (b : κ → ℝ≥0) (i : ι) (j : κ) : ℝ≥0 := by
  classical
  exact if h j = g i then a i * b j / typeAmount g a (g i) else 0

theorem transportAmount_row {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : ι → Γ) (h : κ → Γ) (a : ι → ℝ≥0) (b : κ → ℝ≥0)
    (ha : ∀ i, 0 < a i) (heq : ∀ k, typeAmount g a k = typeAmount h b k) (i : ι) :
    ∑ j, transportAmount g h a b i j = a i := by
  classical
  have hterm (j : κ) : transportAmount g h a b i j =
      a i * (if h j = g i then b j else 0) / typeAmount g a (g i) := by
    by_cases hij : h j = g i <;> simp [transportAmount, hij]
  simp_rw [hterm]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  change a i * typeAmount h b (g i) / typeAmount g a (g i) = a i
  rw [← heq]
  exact mul_div_cancel_right₀ _ (typeAmount_pos g a i (ha i)).ne'

theorem transportAmount_column {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : ι → Γ) (h : κ → Γ) (a : ι → ℝ≥0) (b : κ → ℝ≥0)
    (hb : ∀ j, 0 < b j) (heq : ∀ k, typeAmount g a k = typeAmount h b k) (j : κ) :
    ∑ i, transportAmount g h a b i j = b j := by
  classical
  have hterm (i : ι) : transportAmount g h a b i j =
      (if g i = h j then a i else 0) * b j / typeAmount h b (h j) := by
    by_cases hij : h j = g i
    · simp [transportAmount, hij, ← heq]
    · simp [transportAmount, hij, Ne.symm hij]
  simp_rw [hterm]
  rw [← Finset.sum_div, ← Finset.sum_mul]
  change typeAmount g a (h j) * b j / typeAmount h b (h j) = b j
  rw [heq]
  exact mul_div_cancel_left₀ _ (typeAmount_pos h b j (hb j)).ne'

/-- Transport a right-hand atomic state to the matching left-hand system type.
For unlike types the assigned amount is zero, so the left state can be used. -/
noncomputable def refinedRightState (u v : Σ g, State g) : State u.1 := by
  classical
  exact if h : v.1 = u.1 then h ▸ v.2 else u.2

theorem refinedRightState_atom (u v : Σ g, State g) (heq : v.1 = u.1) :
    (⟨u.1, refinedRightState State u v⟩ : Σ g, State g) = v := by
  rcases u with ⟨g, x⟩
  rcases v with ⟨k, y⟩
  dsimp at heq
  subst k
  simp [refinedRightState]

/-- Finite weighted families with equal amounts of each system have an actual
common scaled-product realization after splitting. -/
theorem common_product_of_typeAmounts
    (P : Accessibility (CompositeState (Σ g, State g)))
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ι → Σ g, State g) (v : κ → Σ g, State g)
    (a : ι → ℝ≥0) (b : κ → ℝ≥0) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (heq : ∀ k, typeAmount (fun i => (u i).1) a k = typeAmount (fun j => (v j).1) b k) :
    ∃ p : ScaledProduct (Γ := Γ), ∃ x y : p.States State,
      P.stateClass (∑ i, a i • CompositeState.mk (.atom (u i))) =
        P.stateClass (p.realize State x) ∧
      P.stateClass (∑ j, b j • CompositeState.mk (.atom (v j))) =
        P.stateClass (p.realize State y) := by
  classical
  let g (ij : ι × κ) := (u ij.1).1
  let c (ij : ι × κ) := transportAmount (fun i => (u i).1) (fun j => (v j).1) a b ij.1 ij.2
  let x (ij : ι × κ) : State (g ij) := (u ij.1).2
  let y (ij : ι × κ) : State (g ij) := refinedRightState State (u ij.1) (v ij.2)
  refine ⟨ScaledProduct.ofFamily g c, ScaledProduct.statesOfFamily State g c x,
    ScaledProduct.statesOfFamily State g c y, ?_, ?_⟩
  · rw [ScaledProduct.realize_ofFamily]
    simp only [Accessibility.stateClass_sum, Accessibility.stateClass_scale, Fintype.sum_prod_type]
    change (∑ i, a i • P.stateClass (CompositeState.mk (.atom (u i)))) =
      ∑ i, ∑ j, transportAmount (fun i => (u i).1) (fun j => (v j).1) a b i j •
        P.stateClass (CompositeState.mk (.atom (u i)))
    simp only [← Finset.sum_smul, transportAmount_row _ _ _ _ ha heq]
  · rw [ScaledProduct.realize_ofFamily]
    simp only [Accessibility.stateClass_sum, Accessibility.stateClass_scale, Fintype.sum_prod_type]
    have hterm (i : ι) (j : κ) :
        c (i, j) • P.stateClass (CompositeState.mk (.atom ⟨g (i, j), y (i, j)⟩)) =
          c (i, j) • P.stateClass (CompositeState.mk (.atom (v j))) := by
      by_cases hij : (v j).1 = (u i).1
      · change c (i, j) • P.stateClass (CompositeState.mk
          (.atom ⟨(u i).1, refinedRightState State (u i) (v j)⟩)) = _
        rw [refinedRightState_atom State (u i) (v j) hij]
      · have hc : c (i, j) = 0 := by simp [c, transportAmount, hij]
        rw [hc, zero_smul, zero_smul]
    simp_rw [hterm]
    rw [Finset.sum_comm]
    change (∑ j, b j • P.stateClass (CompositeState.mk (.atom (v j)))) =
      ∑ j, ∑ i, transportAmount (fun i => (u i).1) (fun j => (v j).1) a b i j •
        P.stateClass (CompositeState.mk (.atom (v j)))
    simp only [← Finset.sum_smul, transportAmount_column _ _ _ _ hb heq]

/-- Each composition coordinate is the sum of the normal-form atom amounts
belonging to that system. -/
theorem compositionLabel_eq_typeAmount (x : CompositeState (Σ g, State g)) (g : Γ) :
    compositionLabel State x g = typeAmount
      (fun a : (CompositeState.atomAmounts (Σ g, State g) x).support => a.val.1)
      (fun a => CompositeState.atomAmounts (Σ g, State g) x a.val) g := by
  classical
  have h := congrArg (fun f : Γ →₀ ℝ≥0 => f g)
    (CompositeState.eval_atomAmounts_sum (compositionLabel State)
      (compositionLabel_scale State) x)
  have hatom (a : Σ g, State g) :
      compositionLabel State (CompositeState.mk (.atom a)) = Finsupp.single a.1 1 := rfl
  simpa [typeAmount, Finsupp.finsetSum_apply, Finsupp.smul_apply, hatom,
    Finsupp.single_apply] using h

/-- The atom normal form is realized by physical nonnegative scalings and
composition, modulo the adiabatic splitting identifications. -/
theorem atom_normal_form (P : Accessibility (CompositeState (Σ g, State g)))
    (x : CompositeState (Σ g, State g)) :
    P.stateClass x = P.stateClass
      (∑ a : (CompositeState.atomAmounts (Σ g, State g) x).support,
        CompositeState.atomAmounts (Σ g, State g) x a.val •
          CompositeState.mk (.atom a.val)) := by
  classical
  have h := CompositeState.eval_atomAmounts_sum P.stateClassHom P.stateClass_scale x
  change P.stateClass x = ∑ a : (CompositeState.atomAmounts (Σ g, State g) x).support,
    CompositeState.atomAmounts (Σ g, State g) x a.val •
      P.stateClass (CompositeState.mk (.atom a.val)) at h
  simpa only [Accessibility.stateClass_sum, Accessibility.stateClass_scale] using h

/-- Equal composition labels admit a common scaled product. No comparison
assumption or conservation premise is needed for this realization theorem. -/
theorem common_product_of_equal_label
    (P : Accessibility (CompositeState (Σ g, State g)))
    (x y : CompositeState (Σ g, State g))
    (hxy : compositionLabel State x = compositionLabel State y) :
    ∃ p : ScaledProduct (Γ := Γ), ∃ u v : p.States State,
      P.stateClass x = P.stateClass (p.realize State u) ∧
      P.stateClass y = P.stateClass (p.realize State v) := by
  classical
  let a := CompositeState.atomAmounts (Σ g, State g) x
  let b := CompositeState.atomAmounts (Σ g, State g) y
  have ha (i : a.support) : 0 < a i.val :=
    pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp i.property)
  have hb (j : b.support) : 0 < b j.val :=
    pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp j.property)
  have heq (g : Γ) : typeAmount (fun i : a.support => i.val.1) (fun i => a i.val) g =
      typeAmount (fun j : b.support => j.val.1) (fun j => b j.val) g := by
    rw [← compositionLabel_eq_typeAmount State x, ← compositionLabel_eq_typeAmount State y, hxy]
  obtain ⟨p, u, v, hu, hv⟩ := common_product_of_typeAmounts State P
    (fun i : a.support => i.val) (fun j : b.support => j.val)
    (fun i => a i.val) (fun j => b j.val) ha hb heq
  exact ⟨p, u, v, (atom_normal_form State P x).trans hu,
    (atom_normal_form State P y).trans hv⟩

/-- Comparison on each fixed finite scaled product. Amounts may vanish. -/
def ProductComparison (P : Accessibility (CompositeState (Σ g, State g))) : Prop :=
  ∀ (p : ScaledProduct (Γ := Γ)) (u v : p.States State),
    P.relation (p.realize State u) (p.realize State v) ∨
      P.relation (p.realize State v) (p.realize State u)

/-- Comparison is needed only for nonempty products of positive amounts;
zero amounts can be removed and the empty product is reflexively comparable. -/
theorem productComparison_of_positive
    (P : Accessibility (CompositeState (Σ g, State g)))
    (hcompare : ∀ (p : ScaledProduct (Γ := Γ)), 0 < p.count →
      (∀ i, 0 < p.amount i) → ∀ u v : p.States State,
        P.relation (p.realize State u) (p.realize State v) ∨
          P.relation (p.realize State v) (p.realize State u)) : ProductComparison State P := by
  classical
  intro p u v
  let J := {i : Fin p.count // 0 < p.amount i}
  let g (i : J) := p.system i.val
  let a (i : J) := p.amount i.val
  have hremove (z : p.States State) :
      ∑ i : J, a i • CompositeState.mk (.atom (⟨g i, z i.val⟩ : Σ g, State g)) =
        p.realize State z := by
    have h := Fintype.sum_subtype_add_sum_subtype (fun i => 0 < p.amount i)
      (fun i => p.amount i • CompositeState.mk (.atom (⟨p.system i, z i⟩ : Σ g, State g)))
    have hz : ∑ i : {i : Fin p.count // ¬ 0 < p.amount i},
        p.amount i.val • CompositeState.mk (.atom (⟨p.system i.val, z i.val⟩ : Σ g, State g)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hi : p.amount i.val = 0 := le_antisymm (le_of_not_gt i.property) zero_le
      simp [hi]
    rw [hz, add_zero] at h
    exact h
  rcases isEmpty_or_nonempty J with hJ | hJ
  · let := hJ
    have hz (z : p.States State) : p.realize State z = 0 := by
      simpa using (hremove z).symm
    exact Or.inl (by rw [hz u, hz v]; exact P.refl 0)
  · let := hJ
    let q := ScaledProduct.ofFamily g a
    let u' := ScaledProduct.statesOfFamily State g a (fun i => u i.val)
    let v' := ScaledProduct.statesOfFamily State g a (fun i => v i.val)
    have hq : 0 < q.count := by
      change 0 < Fintype.card J
      exact Fintype.card_pos
    have hpos (i : Fin q.count) : 0 < q.amount i := ((Fintype.equivFin J).symm i).property
    have hu : q.realize State u' = p.realize State u :=
      (ScaledProduct.realize_ofFamily State g a (fun i => u i.val)).trans (hremove u)
    have hv : q.realize State v' = p.realize State v :=
      (ScaledProduct.realize_ofFamily State g a (fun i => v i.val)).trans (hremove v)
    simpa only [hu, hv] using hcompare q hq hpos u' v'

/-- Product CH implies comparison of arbitrary composites with equal labels,
using the explicitly constructed common product. -/
theorem sector_comparison_of_productComparison
    (P : Accessibility (CompositeState (Σ g, State g))) (hcompare : ProductComparison State P)
    {x y : CompositeState (Σ g, State g)}
    (hxy : compositionLabel State x = compositionLabel State y) :
    P.relation x y ∨ P.relation y x := by
  obtain ⟨p, u, v, hx, hy⟩ := common_product_of_equal_label State P x y hxy
  exact P.comparable_of_common_product (fun p : ScaledProduct (Γ := Γ) => p.realize State) hcompare
    ⟨p, u, v, (P.stateClass_eq _ _).mp hx, (P.stateClass_eq _ _).mp hy⟩

/-- Conservation and product CH give ECH; a common-product realization is a
proved consequence of the composite syntax, not a separate premise. -/
theorem exchangeComparison_of_productComparison
    (P : Accessibility (CompositeState (Σ g, State g)))
    (hpreserved : ∀ {x y}, P.relation x y → compositionLabel State x = compositionLabel State y)
    (hcompare : ProductComparison State P) : ExchangeComparison P.StateSpace := by
  apply P.exchangeComparison_of_common_products (compositionLabel State) hpreserved
    (fun p : ScaledProduct (Γ := Γ) => p.realize State) hcompare
  intro x y hxy
  obtain ⟨p, u, v, hx, hy⟩ := common_product_of_equal_label State P x y hxy
  exact ⟨p, u, v, (P.stateClass_eq _ _).mp hx, (P.stateClass_eq _ _).mp hy⟩

/-- For a generated nonreactive relation, only elementary conservation and
product CH remain premises; A6 conservation and common realization are proved. -/
theorem generated_exchangeComparison
    (elementary : CompositeState (Σ g, State g) → CompositeState (Σ g, State g) → Prop)
    (hbasic : ∀ {x y}, elementary x y → compositionLabel State x = compositionLabel State y)
    (hcompare : ProductComparison State (generatedAccessibility elementary CompositeState.zero_scale)) :
    ExchangeComparison (generatedAccessibility elementary CompositeState.zero_scale).StateSpace :=
  exchangeComparison_of_productComparison State _
    (Generated.label_eq (compositionLabel State) (compositionLabel_scale State) hbasic) hcompare

/-- The canonical within-system atomic model needs only product CH to yield ECH. -/
theorem atomic_exchangeComparison (elementary : ∀ g, State g → State g → Prop)
    (hcompare : ProductComparison State (accessibility State elementary)) :
    ExchangeComparison (accessibility State elementary).StateSpace :=
  exchangeComparison_of_productComparison State _ (accessibility_label_eq State elementary) hcompare

end Nonreactive

end ProjectAInos.Thermodynamics.Physical
