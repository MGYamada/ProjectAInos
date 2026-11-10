module

public import ProjectAInos.Thermodynamics.Basic
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Positivity

/-!
# A real coordinate for the thermodynamic process direction

Sequential order closedness and comparison on the process span imply that a
nonzero salient process cone has one real entropy coordinate. The coordinate
is constructed as a supremum, with its normalization fixed by a positive
generator. Mathlib's `PointedCone` contains zero, while `ConvexCone.Salient`
expresses the absence of nonzero reversible directions.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace ProjectAInos.Thermodynamics

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Closure along vanishing positive perturbations, without a topology on the
state space. Only the scalar sequence carries a topology. -/
def SequentialOrderClosed (P : PointedCone ℝ V) : Prop :=
  ∀ (v w : V) (ε : ℕ → ℝ≥0),
    (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      (∀ n, v + (ε n : ℝ) • w ∈ P) → v ∈ P

/-- Apply sequential order closedness along the fixed scales `1 / (n + 1)`. -/
theorem SequentialOrderClosed.of_reciprocalNatSucc {P : PointedCone ℝ V}
    (hSC : SequentialOrderClosed P) (v w : V)
    (h : ∀ n, v + (reciprocalNatSucc n : ℝ) • w ∈ P) : v ∈ P :=
  hSC v w reciprocalNatSucc reciprocalNatSucc_pos tendsto_reciprocalNatSucc h

/-- Every vector in the real process span has one of its signs in the cone. -/
def ConeTotalOnSpan (P : PointedCone ℝ V) : Prop :=
  ∀ w ∈ Submodule.span ℝ (P : Set V), w ∈ P ∨ -w ∈ P

/-- The lower cut defining the coordinate relative to a positive vector. -/
def entropyCut (P : PointedCone ℝ V) (e w : V) : Set ℝ :=
  {r | w - r • e ∈ P}

private theorem salient_eq_zero (P : PointedCone ℝ V)
    (hP : (P : ConvexCone ℝ V).Salient) {v : V}
    (hv : v ∈ P) (hnv : -v ∈ P) : v = 0 := by
  by_contra hne
  exact hP v hv hne hnv

/-- Sequential order closedness excludes positive infinitesimal directions
bounded above by one fixed vector. -/
theorem SequentialOrderClosed.archimedean (P : PointedCone ℝ V)
    (hSC : SequentialOrderClosed P) (v w : V)
    (h : ∀ n : ℕ, 0 < n → w - (n : ℝ) • v ∈ P) : -v ∈ P := by
  apply hSC.of_reciprocalNatSucc (-v) w
  intro n
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hscaled := P.smul_mem (show 0 ≤ 1 / ((n : ℝ) + 1) by positivity)
    (h (n + 1) (Nat.succ_pos n))
  simpa [reciprocalNatSucc, smul_sub, smul_smul, Nat.cast_add, Nat.cast_one, hn,
    sub_eq_add_neg, add_comm] using hscaled

/-- The cone induces a linear order on its span when exchange comparison
supplies totality. This is installed locally by callers. -/
@[instance_reducible]
noncomputable def coneSpanLinearOrder (P : PointedCone ℝ V)
    (hP : (P : ConvexCone ℝ V).Salient) (hTotal : ConeTotalOnSpan P) :
    LinearOrder (Submodule.span ℝ (P : Set V)) where
  le x y := (y : V) - x ∈ P
  le_refl x := by simp
  le_trans x y z hxy hyz := by
    have h := P.add_mem hxy hyz
    convert h using 1
    abel
  le_antisymm x y hxy hyx := by
    apply Subtype.ext
    have hneg : -((y : V) - x) ∈ P := by simpa using hyx
    exact (sub_eq_zero.mp (salient_eq_zero P hP hxy hneg)).symm
  le_total x y := by
    have h := hTotal ((y : V) - x) (Submodule.sub_mem _ y.property x.property)
    simpa only [neg_sub] using h
  toDecidableLE := Classical.decRel _

/-- Translation preserves the cone order on the process span. -/
theorem coneSpan_isOrderedAddMonoid (P : PointedCone ℝ V)
    (hP : (P : ConvexCone ℝ V).Salient) (hTotal : ConeTotalOnSpan P) :
    letI := coneSpanLinearOrder P hP hTotal
    IsOrderedAddMonoid (Submodule.span ℝ (P : Set V)) := by
  let := coneSpanLinearOrder P hP hTotal
  refine { add_le_add_left := ?_ }
  intro x y h z
  change (y : V) - x ∈ P at h
  change ((y : V) + z) - ((x : V) + z) ∈ P
  simpa only [add_sub_add_right_eq_sub] using h

/-- Nonnegative real scaling preserves the cone order on the process span. -/
theorem coneSpan_isOrderedModule (P : PointedCone ℝ V)
    (hP : (P : ConvexCone ℝ V).Salient) (hTotal : ConeTotalOnSpan P) :
    letI := coneSpanLinearOrder P hP hTotal
    IsOrderedModule ℝ (Submodule.span ℝ (P : Set V)) := by
  let := coneSpanLinearOrder P hP hTotal
  let := coneSpan_isOrderedAddMonoid P hP hTotal
  apply IsOrderedModule.of_smul_nonneg
  intro r hr w hw
  change (w : V) - 0 ∈ P at hw
  change r • (w : V) - 0 ∈ P
  simp only [sub_zero] at hw ⊢
  exact P.smul_mem hr hw

/-- The standard Archimedean typeclass on the linearly ordered process span
follows from the sequential closure hypothesis. -/
theorem coneSpan_archimedean (P : PointedCone ℝ V)
    (hSC : SequentialOrderClosed P) (hP : (P : ConvexCone ℝ V).Salient)
    (hTotal : ConeTotalOnSpan P) :
    letI := coneSpanLinearOrder P hP hTotal
    Archimedean (Submodule.span ℝ (P : Set V)) := by
  let := coneSpanLinearOrder P hP hTotal
  constructor
  intro x y hy
  by_contra hn
  push Not at hn
  have hnegative : -(y : V) ∈ P := hSC.archimedean P y x (by
    intro n _
    have hle : n • y ≤ x := (hn n).le
    change (x : V) - n • (y : V) ∈ P at hle
    simpa only [Nat.cast_smul_eq_nsmul] using hle)
  have hle : y ≤ 0 := by
    change (0 : V) - (y : V) ∈ P
    simpa using hnegative
  exact (not_le_of_gt hy) hle

theorem entropyCut_mono (P : PointedCone ℝ V) {e w : V} (he : e ∈ P)
    {r t : ℝ} (hrt : r ≤ t) (ht : t ∈ entropyCut P e w) :
    r ∈ entropyCut P e w := by
  have h := P.add_mem ht (P.smul_mem (sub_nonneg.mpr hrt) he)
  change w - r • e ∈ P
  convert h using 1
  module

theorem entropyCut_bddAbove (P : PointedCone ℝ V)
    (hSC : SequentialOrderClosed P) (hP : (P : ConvexCone ℝ V).Salient)
    {e : V} (he : e ∈ P) (hne : e ≠ 0) (w : V) :
    BddAbove (entropyCut P e w) := by
  by_contra hbound
  have hnat (n : ℕ) : w - ((n : ℝ) + 1) • e ∈ P := by
    obtain ⟨t, ht, hnt⟩ := not_bddAbove_iff.mp hbound ((n : ℝ) + 1)
    exact entropyCut_mono P he hnt.le ht
  have hneg : -e ∈ P := by
    apply hSC.of_reciprocalNatSucc (-e) w
    intro n
    have h := P.smul_mem (show 0 ≤ 1 / ((n : ℝ) + 1) by positivity) (hnat n)
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    simpa [reciprocalNatSucc, smul_sub, smul_smul, hn, sub_eq_add_neg, add_comm] using h
  exact hP e he hne hneg

theorem entropyCut_nonempty (P : PointedCone ℝ V)
    (hSC : SequentialOrderClosed P) (hP : (P : ConvexCone ℝ V).Salient)
    (hTotal : ConeTotalOnSpan P) {e w : V} (he : e ∈ P) (hne : e ≠ 0)
    (hw : w ∈ Submodule.span ℝ (P : Set V)) :
    (entropyCut P e w).Nonempty := by
  obtain ⟨b, hb⟩ := entropyCut_bddAbove P hSC hP he hne (-w)
  have hnot : -w - (b + 1) • e ∉ P := by
    intro h
    have := hb h
    linarith
  have hmem : -w - (b + 1) • e ∈ Submodule.span ℝ (P : Set V) :=
    Submodule.sub_mem _ (Submodule.neg_mem _ hw)
      (Submodule.smul_mem _ _ (Submodule.subset_span he))
  have h := (hTotal _ hmem).resolve_left hnot
  refine ⟨-(b + 1), ?_⟩
  change w - (-(b + 1)) • e ∈ P
  convert h using 1
  module

/-- Sequential closedness recovers a vector from its lower cut when only its
comparisons with the reference line are known. -/
theorem entropyCut_sSup_smul_of_comparable (P : PointedCone ℝ V)
    (hSC : SequentialOrderClosed P) (hP : (P : ConvexCone ℝ V).Salient)
    {e w : V} (he : e ∈ P) (hne : e ≠ 0)
    (hnonempty : (entropyCut P e w).Nonempty)
    (hcompare : ∀ r : ℝ, w - r • e ∈ P ∨ -(w - r • e) ∈ P) :
    sSup (entropyCut P e w) • e = w := by
  let α := sSup (entropyCut P e w)
  have hbound := entropyCut_bddAbove P hSC hP he hne w
  have hbelow {r : ℝ} (hr : r < α) : w - r • e ∈ P := by
    obtain ⟨t, ht, hrt⟩ := exists_lt_of_lt_csSup hnonempty hr
    exact entropyCut_mono P he hrt.le ht
  have habove {r : ℝ} (hr : α < r) : -(w - r • e) ∈ P := by
    exact (hcompare r).resolve_left (fun h =>
      (not_le_of_gt hr) (le_csSup hbound h))
  have hleft : w - α • e ∈ P := by
    apply hSC.of_reciprocalNatSucc (w - α • e) e
    intro n
    have h := hbelow (r := α - 1 / ((n : ℝ) + 1))
      (sub_lt_self _ (by positivity))
    convert h using 1
    simp only [reciprocalNatSucc, NNReal.coe_div, NNReal.coe_one, NNReal.coe_add, NNReal.coe_natCast]
    module
  have hright : -(w - α • e) ∈ P := by
    apply hSC.of_reciprocalNatSucc (-(w - α • e)) e
    intro n
    have h := habove (r := α + 1 / ((n : ℝ) + 1))
      (lt_add_of_pos_right _ (by positivity))
    convert h using 1
    simp only [reciprocalNatSucc, NNReal.coe_div, NNReal.coe_one, NNReal.coe_add, NNReal.coe_natCast]
    module
  exact (sub_eq_zero.mp (salient_eq_zero P hP hleft hright)).symm

/-- The supremum of the lower cut recovers the vector itself. -/
theorem entropyCut_sSup_smul (P : PointedCone ℝ V)
    (hSC : SequentialOrderClosed P) (hP : (P : ConvexCone ℝ V).Salient)
    (hTotal : ConeTotalOnSpan P) {e w : V} (he : e ∈ P) (hne : e ≠ 0)
    (hw : w ∈ Submodule.span ℝ (P : Set V)) :
    sSup (entropyCut P e w) • e = w :=
  entropyCut_sSup_smul_of_comparable P hSC hP he hne
    (entropyCut_nonempty P hSC hP hTotal he hne hw)
    (fun r => hTotal _ (Submodule.sub_mem _ hw
      (Submodule.smul_mem _ r (Submodule.subset_span he))))

/-- The normalized real entropy coordinate on the process span. -/
noncomputable def coneEntropyEquiv (P : PointedCone ℝ V)
    (hSC : SequentialOrderClosed P) (hP : (P : ConvexCone ℝ V).Salient)
    (hTotal : ConeTotalOnSpan P) (e : V) (he : e ∈ P) (hne : e ≠ 0) :
    Submodule.span ℝ (P : Set V) ≃ₗ[ℝ] ℝ where
  toFun w := sSup (entropyCut P e w)
  invFun r := ⟨r • e, Submodule.smul_mem _ _ (Submodule.subset_span he)⟩
  left_inv w := Subtype.ext (entropyCut_sSup_smul P hSC hP hTotal he hne w.property)
  right_inv r := smul_left_injective ℝ hne
    (entropyCut_sSup_smul P hSC hP hTotal he hne
      (Submodule.smul_mem _ r (Submodule.subset_span he)))
  map_add' u v := by
    apply smul_left_injective ℝ hne
    change sSup (entropyCut P e ((u : V) + v)) • e =
      (sSup (entropyCut P e u) + sSup (entropyCut P e v)) • e
    rw [add_smul]
    rw [entropyCut_sSup_smul P hSC hP hTotal he hne u.property,
      entropyCut_sSup_smul P hSC hP hTotal he hne v.property]
    exact entropyCut_sSup_smul P hSC hP hTotal he hne (u + v).property
  map_smul' r w := by
    apply smul_left_injective ℝ hne
    change sSup (entropyCut P e (r • (w : V))) • e =
      (r * sSup (entropyCut P e w)) • e
    rw [mul_smul, entropyCut_sSup_smul P hSC hP hTotal he hne w.property]
    exact entropyCut_sSup_smul P hSC hP hTotal he hne (r • w).property

theorem coneEntropyEquiv_nonneg_iff (P : PointedCone ℝ V)
    (hSC : SequentialOrderClosed P) (hP : (P : ConvexCone ℝ V).Salient)
    (hTotal : ConeTotalOnSpan P) (e : V) (he : e ∈ P) (hne : e ≠ 0)
    (w : Submodule.span ℝ (P : Set V)) :
    0 ≤ coneEntropyEquiv P hSC hP hTotal e he hne w ↔ (w : V) ∈ P := by
  let s := coneEntropyEquiv P hSC hP hTotal e he hne
  have hrepr : s w • e = (w : V) :=
    entropyCut_sSup_smul P hSC hP hTotal he hne w.property
  constructor
  · intro h
    rw [← hrepr]
    exact P.smul_mem h he
  · intro hw
    by_contra h
    have hneg : s w < 0 := lt_of_not_ge h
    have hminus := P.smul_mem (neg_nonneg.mpr hneg.le) he
    have hminus' : -(w : V) ∈ P := by simpa [neg_smul, hrepr] using hminus
    have hzero := salient_eq_zero P hP hw hminus'
    have hcoeff : s w = 0 := smul_eq_zero.mp (hrepr.trans hzero) |>.resolve_right hne
    exact (ne_of_lt hneg) hcoeff

@[simp]
theorem coneEntropyEquiv_generator (P : PointedCone ℝ V)
    (hSC : SequentialOrderClosed P) (hP : (P : ConvexCone ℝ V).Salient)
    (hTotal : ConeTotalOnSpan P) (e : V) (he : e ∈ P) (hne : e ≠ 0) :
    coneEntropyEquiv P hSC hP hTotal e he hne
      ⟨e, Submodule.subset_span he⟩ = 1 := by
  apply smul_left_injective ℝ hne
  change sSup (entropyCut P e e) • e = (1 : ℝ) • e
  simpa using entropyCut_sSup_smul P hSC hP hTotal he hne (Submodule.subset_span he)

/-- Any linear entropy coordinate differs by its value on the chosen generator. -/
theorem linearMap_eq_generator_mul_coneEntropyEquiv (P : PointedCone ℝ V)
    (hSC : SequentialOrderClosed P) (hP : (P : ConvexCone ℝ V).Salient)
    (hTotal : ConeTotalOnSpan P) (e : V) (he : e ∈ P) (hne : e ≠ 0)
    (f : Submodule.span ℝ (P : Set V) →ₗ[ℝ] ℝ)
    (w : Submodule.span ℝ (P : Set V)) :
    f w = f ⟨e, Submodule.subset_span he⟩ *
      coneEntropyEquiv P hSC hP hTotal e he hne w := by
  have hrepr : w = coneEntropyEquiv P hSC hP hTotal e he hne w •
      (⟨e, Submodule.subset_span he⟩ : Submodule.span ℝ (P : Set V)) :=
    Subtype.ext (entropyCut_sSup_smul P hSC hP hTotal he hne w.property).symm
  calc
    f w = f (coneEntropyEquiv P hSC hP hTotal e he hne w •
        (⟨e, Submodule.subset_span he⟩ : Submodule.span ℝ (P : Set V))) := congrArg f hrepr
    _ = _ := by rw [map_smul]; exact mul_comm _ _

/-- A second order-preserving linear equivalence changes the entropy unit by
one unique positive scalar. -/
theorem coneEntropyEquiv_unique_up_to_pos (P : PointedCone ℝ V)
    (hSC : SequentialOrderClosed P) (hP : (P : ConvexCone ℝ V).Salient)
    (hTotal : ConeTotalOnSpan P) (e : V) (he : e ∈ P) (hne : e ≠ 0)
    (f : Submodule.span ℝ (P : Set V) ≃ₗ[ℝ] ℝ)
    (hf : ∀ w, 0 ≤ f w ↔ (w : V) ∈ P) :
    ∃! a : ℝ, 0 < a ∧ ∀ w,
      f w = a * coneEntropyEquiv P hSC hP hTotal e he hne w := by
  let eW : Submodule.span ℝ (P : Set V) := ⟨e, Submodule.subset_span he⟩
  have heW : eW ≠ 0 := fun h => hne (congrArg Subtype.val h)
  have hfne : f eW ≠ 0 := fun h => heW (f.injective (h.trans f.map_zero.symm))
  have hpositive : 0 < f eW :=
    lt_of_le_of_ne ((hf eW).mpr he) hfne.symm
  refine ⟨f eW, ⟨hpositive, ?_⟩, ?_⟩
  · exact linearMap_eq_generator_mul_coneEntropyEquiv P hSC hP hTotal e he hne f.toLinearMap
  · intro a ha
    have := ha.2 eW
    simpa [eW] using this.symm

end ProjectAInos.Thermodynamics
