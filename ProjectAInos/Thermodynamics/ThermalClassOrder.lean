module

public import ProjectAInos.Thermodynamics.SupportingSlopes
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Analysis.Convex.Topology

/-!
# Ordering classes represented by intersecting intervals

The zeroth law makes interval intersection an equivalence relation. Each such
class then has a common point, which gives an injective real label for the
classes. Local ordering of these labels on a real interval extends globally.
The final lemma shows that a locally ordered label with transverse equal-label
endpoints is constant. These are the order-theoretic steps in LY Theorem 4.6.
-/

@[expose] public section

open Set
open scoped Topology

namespace ProjectAInos.Thermodynamics

/-- The supremum of the lower endpoints in an interval-intersection class. -/
noncomputable def intervalClassLabel {A : Type*} (R : A → A → Prop)
    (lower : A → ℝ) (x : A) : ℝ :=
  sSup {b | ∃ y, R x y ∧ b = lower y}

theorem intervalClassLabel_mem {A : Type*} {R : A → A → Prop}
    {lower upper : A → ℝ} (hrefl : ∀ x, R x x)
    (hinter : ∀ x y, R x y ↔ (Icc (lower x) (upper x) ∩
      Icc (lower y) (upper y)).Nonempty) (x : A) :
    intervalClassLabel R lower x ∈ Icc (lower x) (upper x) := by
  have hn : ({b | ∃ y, R x y ∧ b = lower y} : Set ℝ).Nonempty :=
    ⟨lower x, x, hrefl x, rfl⟩
  have hb : ∀ b ∈ ({b | ∃ y, R x y ∧ b = lower y} : Set ℝ), b ≤ upper x := by
    rintro b ⟨y, hxy, rfl⟩
    obtain ⟨c, hc, hd⟩ := (hinter x y).mp hxy
    exact hd.1.trans hc.2
  exact ⟨le_csSup ⟨upper x, hb⟩ ⟨x, hrefl x, rfl⟩, csSup_le hn hb⟩

theorem intervalClassLabel_eq_of_related {A : Type*} {R : A → A → Prop}
    {lower : A → ℝ} (hsymm : ∀ {x y}, R x y → R y x)
    (htrans : ∀ {x y z}, R x y → R y z → R x z)
    {x y : A} (hxy : R x y) : intervalClassLabel R lower x =
      intervalClassLabel R lower y := by
  unfold intervalClassLabel
  congr 1
  ext b
  constructor
  · rintro ⟨z, hxz, rfl⟩
    exact ⟨z, htrans (hsymm hxy) hxz, rfl⟩
  · rintro ⟨z, hyz, rfl⟩
    exact ⟨z, htrans hxy hyz, rfl⟩

/-- The common-point label distinguishes exactly the intersection classes. -/
theorem intervalClassLabel_eq_iff {A : Type*} {R : A → A → Prop}
    {lower upper : A → ℝ} (hrefl : ∀ x, R x x)
    (hsymm : ∀ {x y}, R x y → R y x)
    (htrans : ∀ {x y z}, R x y → R y z → R x z)
    (hinter : ∀ x y, R x y ↔ (Icc (lower x) (upper x) ∩
      Icc (lower y) (upper y)).Nonempty) (x y : A) :
    intervalClassLabel R lower x = intervalClassLabel R lower y ↔ R x y := by
  constructor
  · intro heq
    apply (hinter x y).mpr
    refine ⟨intervalClassLabel R lower x, intervalClassLabel_mem hrefl hinter x, ?_⟩
    rw [heq]
    exact intervalClassLabel_mem hrefl hinter y
  · intro hxy
    exact intervalClassLabel_eq_of_related (R := R) (lower := lower) hsymm htrans hxy

/-- Monotonicity on open neighborhoods globalizes on a real interval. The
codomain needs only a preorder; continuity of the function is not required. -/
theorem monotoneOn_of_open_local_monotone {B : Type*} [Preorder B]
    {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → B}
    (hlocal : ∀ x ∈ D, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧
      MonotoneOn f (D ∩ U)) : MonotoneOn f D := by
  classical
  intro a ha b hb hab
  choose U hU using fun x : D => hlocal x x.property
  let c (x : D) : Set (Icc a b) := Subtype.val ⁻¹' U x
  have hcopen : ∀ x, IsOpen (c x) := fun x =>
    (hU x).1.preimage continuous_subtype_val
  have hcover : (univ : Set (Icc a b)) ⊆ ⋃ x, c x := by
    intro t _
    have htD : (t : ℝ) ∈ D := hD.ordConnected.out ha hb t.property
    exact mem_iUnion.mpr ⟨⟨t, htD⟩, (hU ⟨t, htD⟩).2.1⟩
  obtain ⟨t, ht0, htmono, ⟨N, hN⟩, htcover⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hab hcopen hcover
  have hstep : ∀ k, f (t k) ≤ f (t (k + 1)) := by
    intro k
    obtain ⟨x, hx⟩ := htcover k
    have hle := htmono (Nat.le_succ k)
    exact (hU x).2.2
      ⟨hD.ordConnected.out ha hb (t k).property, hx ⟨le_rfl, hle⟩⟩
      ⟨hD.ordConnected.out ha hb (t (k + 1)).property, hx ⟨hle, le_rfl⟩⟩ hle
  have hall : ∀ k, f a ≤ f (t k) := by
    intro k
    induction k with
    | zero => simpa only [ht0] using (le_refl (f a))
    | succ k hk => exact hk.trans (hstep k)
  simpa only [hN N le_rfl] using hall N

/-- Transverse equal-label endpoints make a monotone label locally constant. -/
theorem locallyConstant_of_monotone_transverse {D : Set ℝ} {f : ℝ → ℝ}
    (hmono : MonotoneOn f D)
    (htransverse : ∀ x ∈ D, ∃ a ∈ D, ∃ b ∈ D, a < x ∧ x < b ∧ f a = f b) :
    IsLocallyConstant (fun x : D => f x) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  obtain ⟨a, ha, b, hb, hax, hxb, hab⟩ := htransverse x x.property
  refine ⟨Subtype.val ⁻¹' Ioo a b, isOpen_Ioo.preimage continuous_subtype_val,
    ⟨hax, hxb⟩, ?_⟩
  intro y hy
  have heq (z : D) (hz : (z : ℝ) ∈ Ioo a b) : f z = f a := by
    exact le_antisymm ((hmono z.property hb hz.2.le).trans_eq hab.symm)
      (hmono ha z.property hz.1.le)
  exact (heq y hy).trans (heq x ⟨hax, hxb⟩).symm

/-- A locally monotone real label on an interval is constant when every point
lies strictly between two points with equal label. -/
theorem constant_of_open_local_monotone_transverse {D : Set ℝ}
    (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hlocal : ∀ x ∈ D, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧
      MonotoneOn f (D ∩ U))
    (htransverse : ∀ x ∈ D, ∃ a ∈ D, ∃ b ∈ D, a < x ∧ x < b ∧ f a = f b)
    {x y : ℝ} (hx : x ∈ D) (hy : y ∈ D) : f x = f y := by
  let : PreconnectedSpace D := isPreconnected_iff_preconnectedSpace.mp hD.isPreconnected
  exact (locallyConstant_of_monotone_transverse
    (monotoneOn_of_open_local_monotone hD hlocal) htransverse).apply_eq_of_preconnectedSpace
      ⟨x, hx⟩ ⟨y, hy⟩

/-- On an open connected coordinate domain, a label that factors through a
continuous scalar coordinate inherits its local ordering from vertical lines.
Transverse equal-label endpoints then force the label to be constant. -/
theorem constant_of_vertical_order_transverse {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {D : Set (ℝ × V)} (hopen : IsOpen D) (hD : Convex ℝ D)
    {s : ℝ × V → ℝ} (hs : ContinuousOn s D)
    (hstrict : ∀ v, StrictMonoOn (fun u => s (u, v)) {u | (u, v) ∈ D})
    (q : D → ℝ)
    (hmono : ∀ x y : D, x.val.2 = y.val.2 → x.val.1 ≤ y.val.1 → q x ≤ q y)
    (hfiber : ∀ x y : D, s x = s y → q x = q y)
    (htransverse : ∀ x : D, ∃ a b : D, s a < s x ∧ s x < s b ∧ q a = q b)
    (x y : D) : q x = q y := by
  classical
  let J := s '' D
  let f : ℝ → ℝ := fun t => if h : t ∈ J then q ⟨h.choose, h.choose_spec.1⟩ else 0
  have hf (z : D) : f (s z) = q z := by
    have hz : s z ∈ J := ⟨z, z.property, rfl⟩
    dsimp only [f]
    rw [dite_eq_left hz]
    exact hfiber _ z hz.choose_spec.2
  have hJ : Convex ℝ J := (hD.isPreconnected.image s hs).convex
  have hlocal : ∀ t ∈ J, ∃ U : Set ℝ, IsOpen U ∧ t ∈ U ∧
      MonotoneOn f (J ∩ U) := by
    rintro t ⟨z, hz, rfl⟩
    let E : Set ℝ := {u | (u, z.2) ∈ D}
    have hE : IsOpen E := hopen.preimage (continuous_id.prodMk continuous_const)
    have hzE : z.1 ∈ E := by simpa only [E, mem_ofPred_eq, Prod.eta] using hz
    obtain ⟨l, r, ⟨hlz, hzr⟩, hlr⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp (hE.mem_nhds hzE)
    obtain ⟨a, hla, haz⟩ := exists_between hlz
    obtain ⟨b, hzb, hbr⟩ := exists_between hzr
    have hab : a ≤ b := haz.le.trans hzb.le
    have hsub : Icc a b ⊆ E := by
      intro u hu
      exact hlr ⟨hla.trans_le hu.1, hu.2.trans_lt hbr⟩
    have ha : (a, z.2) ∈ D := hsub (left_mem_Icc.mpr hab)
    have hb : (b, z.2) ∈ D := hsub (right_mem_Icc.mpr hab)
    have hcont : ContinuousOn (fun u => s (u, z.2)) (Icc a b) :=
      hs.comp (continuous_id.prodMk continuous_const).continuousOn hsub
    refine ⟨Ioo (s (a, z.2)) (s (b, z.2)), isOpen_Ioo, ?_, ?_⟩
    · exact ⟨by simpa only [Prod.eta] using hstrict z.2 ha hzE haz,
        by simpa only [Prod.eta] using hstrict z.2 hzE hb hzb⟩
    · intro u hu v hv huv
      obtain ⟨u', hu', hsu⟩ := intermediate_value_Icc hab hcont
        ⟨hu.2.1.le, hu.2.2.le⟩
      obtain ⟨v', hv', hsv⟩ := intermediate_value_Icc hab hcont
        ⟨hv.2.1.le, hv.2.2.le⟩
      have huv' : u' ≤ v' := by
        by_contra h
        have hlt := hstrict z.2 (hsub hv') (hsub hu') (lt_of_not_ge h)
        rw [hsu, hsv] at hlt
        exact (not_lt_of_ge huv) hlt
      rw [← hsu, ← hsv, hf ⟨(u', z.2), hsub hu'⟩, hf ⟨(v', z.2), hsub hv'⟩]
      exact hmono _ _ rfl huv'
  have htransverse' : ∀ t ∈ J, ∃ a ∈ J, ∃ b ∈ J,
      a < t ∧ t < b ∧ f a = f b := by
    rintro t ⟨z, hz, rfl⟩
    obtain ⟨a, b, ha, hb, hab⟩ := htransverse ⟨z, hz⟩
    exact ⟨s a, ⟨a, a.property, rfl⟩, s b, ⟨b, b.property, rfl⟩,
      ha, hb, (hf a).trans (hab.trans (hf b).symm)⟩
  have heq := constant_of_open_local_monotone_transverse hJ hlocal htransverse'
    (x := s x) (y := s y) ⟨x, x.property, rfl⟩ ⟨y, y.property, rfl⟩
  simpa only [hf] using heq

end ProjectAInos.Thermodynamics
