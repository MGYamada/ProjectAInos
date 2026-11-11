/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.RealSpectrum
public import ProjectAInos.SmoothAlgebra.Localization
public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Topology.Sheaves.Forget
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# The structure sheaf of a C∞-ring

Following Joyce, Definition 4.16, sections take values in point localizations
and locally are images of ring elements. The sheaf construction follows
mathlib's `AlgebraicGeometry.StructureSheaf` and reuses `LocalPredicate`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace ProjectAInos.SmoothGeometry

open SmoothAlgebra TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite TopCat
open scoped Topology

variable (A : Type u) [CommRing A] [Algebra ℝ A] [SmoothRing A]

namespace StructureSheaf

/-- The family of local C∞-rings over the real spectrum. -/
abbrev Localizations (x : RealSpectrum A) := PointLocalization x.hom

/-- Being represented by one element of `A` is stable under restriction. -/
def isRepresented : PrelocalPredicate (X := TopCat.of (RealSpectrum A)) (Localizations A) where
  pred s := ∃ a : A, ∀ x, s x = PointLocalization.of x.val.hom a
  res {U V} i s h := by
    obtain ⟨a, ha⟩ := h
    exact ⟨a, fun x => ha ⟨x.val, i.le x.property⟩⟩

/-- The local condition defining the structure sheaf. -/
def isLocallyRepresented : LocalPredicate (X := TopCat.of (RealSpectrum A)) (Localizations A) :=
  (isRepresented A).sheafify

/-- A neighbourhood-filter formulation of local representability. -/
theorem locallyRepresented_iff_eventually {U : Opens (RealSpectrum A)}
    (s : (x : U) → Localizations A x.val) :
    (isLocallyRepresented A).pred s ↔
      ∀ x : U, ∃ a : A, ∀ᶠ y : U in 𝓝 x, s y = PointLocalization.of y.val.hom a := by
  constructor
  · intro h x
    obtain ⟨V, hxV, iV, a, ha⟩ := h x
    refine ⟨a, ?_⟩
    have hV : ∀ᶠ y : U in 𝓝 x, y.val ∈ V :=
      continuous_subtype_val.continuousAt (V.isOpen.mem_nhds hxV)
    filter_upwards [hV] with y hy
    exact ha ⟨y.val, hy⟩
  · intro h x
    obtain ⟨a, ha⟩ := h x
    obtain ⟨W, hW, hWo, hxW⟩ := mem_nhds_iff.mp ha
    let V : Opens (RealSpectrum A) :=
      ⟨Subtype.val '' W, U.isOpen.isOpenMap_subtype_val W hWo⟩
    have hVU : V ≤ U := by rintro _ ⟨y, _, rfl⟩; exact y.property
    refine ⟨V, ⟨x, hxW, rfl⟩, homOfLE hVU, a, ?_⟩
    rintro ⟨y, z, hz, rfl⟩
    exact hW hz

theorem locally_op {U : Opens (RealSpectrum A)} {n : ℕ} (f : SmoothOperation n)
    (s : Fin n → (x : U) → Localizations A x.val)
    (hs : ∀ i, (isLocallyRepresented A).pred (s i)) :
    (isLocallyRepresented A).pred (fun x => SmoothRing.op f (fun i => s i x)) := by
  intro x
  choose V hV iV a ha using fun i => hs i x
  refine ⟨U ⊓ ⨅ i, V i, ⟨x.property, ?_⟩, homOfLE inf_le_left,
    SmoothRing.op f a, fun y => ?_⟩
  · rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr (fun i => hV i)
  · change SmoothRing.op f (fun i => s i ⟨y.val, y.property.1⟩) = _
    rw [(PointLocalization.of y.val.hom).map_op]
    congr 1
    funext i
    exact ha i ⟨y.val, (iInf_le V i) y.property.2⟩

/-- Locally represented sections form a real subalgebra of the product of local rings. -/
def sectionsSubalgebra (U : Opens (RealSpectrum A)) :
    Subalgebra ℝ ((x : U) → Localizations A x.val) where
  carrier := {s | (isLocallyRepresented A).pred s}
  add_mem' {s t} hs ht := by
    change (isLocallyRepresented A).pred (fun x => s x + t x)
    simpa using locally_op A SmoothOperation.addition ![s, t]
      (by intro i; fin_cases i <;> assumption)
  mul_mem' {s t} hs ht := by
    change (isLocallyRepresented A).pred (fun x => s x * t x)
    simpa using locally_op A SmoothOperation.multiplication ![s, t]
      (by intro i; fin_cases i <;> assumption)
  algebraMap_mem' r := (isRepresented A).sheafifyOf
    ⟨algebraMap ℝ A r, fun x => ((PointLocalization.of x.val.hom).map_algebraMap r).symm⟩

/-- Sections on an open subset of the real spectrum. -/
abbrev Sections (U : Opens (RealSpectrum A)) := sectionsSubalgebra A U

instance (U : Opens (RealSpectrum A)) : SmoothRing (Sections A U) where
  op f s := ⟨fun x => SmoothRing.op f (fun i => (s i).val x),
    locally_op A f _ (fun i => (s i).property)⟩
  op_proj i s := Subtype.ext (funext fun x => SmoothRing.op_proj i (fun j => (s j).val x))
  op_comp f g s := Subtype.ext (funext fun x => SmoothRing.op_comp f g (fun j => (s j).val x))
  op_nullary r s := Subtype.ext (funext fun x => SmoothRing.op_nullary r (fun j => (s j).val x))
  op_addition s := Subtype.ext (funext fun x => SmoothRing.op_addition (fun j => (s j).val x))
  op_multiplication s :=
    Subtype.ext (funext fun x => SmoothRing.op_multiplication (fun j => (s j).val x))

/-- Restriction of sections. -/
def restriction {U V : Opens (RealSpectrum A)} (i : U ⟶ V) :
    SmoothRingHom (Sections A V) (Sections A U) where
  toFun s := ⟨fun x => s.val ⟨x.val, i.le x.property⟩,
    (isLocallyRepresented A).res i s.val s.property⟩
  map_op' _ _ := rfl

/-- An element defines a section on any open subset. -/
def toOpen (U : Opens (RealSpectrum A)) : SmoothRingHom A (Sections A U) where
  toFun a := ⟨fun x => PointLocalization.of x.val.hom a,
    (isRepresented A).sheafifyOf ⟨a, fun _ => rfl⟩⟩
  map_op' f a := Subtype.ext (funext fun x => (PointLocalization.of x.val.hom).map_op f a)

/-- Evaluate a section in the local C∞-ring at a point. -/
def evaluation {U : Opens (RealSpectrum A)} (x : U) :
    SmoothRingHom (Sections A U) (Localizations A x.val) where
  toFun s := s.val x
  map_op' _ _ := rfl

/-- The underlying commutative-ring presheaf. -/
def presheaf : (TopCat.of (RealSpectrum A)).Presheaf CommRingCat where
  obj U := CommRingCat.of (Sections A U.unop)
  map i := CommRingCat.ofHom (restriction A i.unop).toAlgHom.toRingHom
  map_id _ := by ext s; rfl
  map_comp _ _ := by ext s; rfl

/-- Comparison with the sheaf constructed by mathlib's local-predicate machinery. -/
def presheafCompForget : presheaf A ⋙ forget CommRingCat ≅
    (subsheafToTypes (isLocallyRepresented A)).obj :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; ext s; rfl)

/-- The structure sheaf, with the gluing axiom proved. -/
def sheaf : (TopCat.of (RealSpectrum A)).Sheaf CommRingCat :=
  ⟨presheaf A, (TopCat.Presheaf.isSheaf_iff_isSheaf_comp _ _).mpr
    (TopCat.Presheaf.isSheaf_of_iso (presheafCompForget A).symm
      (subsheafToTypes (isLocallyRepresented A)).property)⟩

/-- Equality in a point localization persists on a neighbourhood. The finite
smooth congruence construction supplies this without a reducedness assumption. -/
theorem of_eq_locally {x : RealSpectrum A} {a b : A}
    (h : PointLocalization.of x.hom a = PointLocalization.of x.hom b) :
    ∀ᶠ y : RealSpectrum A in 𝓝 x,
      PointLocalization.of y.hom a = PointLocalization.of y.hom b := by
  have hr := (PointLocalization.of_eq_of x.hom a b).mp h
  clear h
  induction hr with
  | of h =>
    obtain ⟨s, hs, hab⟩ := h
    filter_upwards [(RealSpectrum.basicOpen s).isOpen.mem_nhds hs] with y hy
    exact (PointLocalization.of_eq_of y.hom _ _).mpr (.of ⟨s, hy, hab⟩)
  | refl => exact Filter.Eventually.of_forall fun _ => rfl
  | symm _ ih => exact ih.mono fun _ h => h.symm
  | trans _ _ ih₁ ih₂ => exact (ih₁.and ih₂).mono fun _ h => h.1.trans h.2
  | op f a b _ ih =>
    filter_upwards [Filter.eventually_all.mpr ih] with y hy
    simp only [(PointLocalization.of y.hom).map_op]
    congr 1
    funext i
    exact hy i

/-- Evaluation is a cocone over the system of neighbourhoods. -/
def evaluationCocone (x : RealSpectrum A) :
    Cocone ((OpenNhds.inclusion x).op ⋙ presheaf A) where
  pt := CommRingCat.of (Localizations A x)
  ι :=
    { app U := CommRingCat.ofHom (evaluation A ⟨x, U.unop.property⟩).toAlgHom.toRingHom
      naturality := by intros; ext s; rfl }

/-- Evaluation of germs, built using the actual colimit defining a stalk. -/
def stalkEvaluation (x : RealSpectrum A) :
    (presheaf A).stalk x ⟶ CommRingCat.of (Localizations A x) :=
  colimit.desc _ (evaluationCocone A x)

@[simp] theorem stalkEvaluation_germ (U : Opens (RealSpectrum A)) (x : RealSpectrum A)
    (hx : x ∈ U) (s : Sections A U) :
    stalkEvaluation A x ((presheaf A).germ U x hx s) = s.val ⟨x, hx⟩ := by
  exact congrArg (fun f : (presheaf A).obj (op U) ⟶ CommRingCat.of (Localizations A x) => f s)
    (colimit.ι_desc (evaluationCocone A x) (op ⟨U, hx⟩))

theorem stalkEvaluation_surjective (x : RealSpectrum A) :
    Function.Surjective (stalkEvaluation A x) := by
  intro a
  obtain ⟨a, rfl⟩ := PointLocalization.of_surjective x.hom a
  exact ⟨(presheaf A).germ ⊤ x trivial (toOpen A ⊤ a), stalkEvaluation_germ A ⊤ x trivial _⟩

theorem stalkEvaluation_injective (x : RealSpectrum A) :
    Function.Injective (stalkEvaluation A x) := by
  intro s t h
  obtain ⟨U, hxU, s, rfl⟩ := (presheaf A).exists_germ_eq s
  obtain ⟨V, hxV, t, rfl⟩ := (presheaf A).exists_germ_eq t
  rw [stalkEvaluation_germ, stalkEvaluation_germ] at h
  obtain ⟨U', hxU', iU, a, ha⟩ := s.property ⟨x, hxU⟩
  obtain ⟨V', hxV', iV, b, hb⟩ := t.property ⟨x, hxV⟩
  have hab : PointLocalization.of x.hom a = PointLocalization.of x.hom b :=
    (ha ⟨x, hxU'⟩).symm.trans (h.trans (hb ⟨x, hxV'⟩))
  obtain ⟨W, hW, hWo, hxW⟩ := mem_nhds_iff.mp (of_eq_locally A hab)
  let Z : Opens (RealSpectrum A) := U' ⊓ V' ⊓ ⟨W, hWo⟩
  have hxZ : x ∈ Z := ⟨⟨hxU', hxV'⟩, hxW⟩
  let jU : Z ⟶ U := homOfLE ((inf_le_left.trans inf_le_left).trans iU.le)
  let jV : Z ⟶ V := homOfLE ((inf_le_left.trans inf_le_right).trans iV.le)
  have heq : (presheaf A).map jU.op s = (presheaf A).map jV.op t := by
    apply Subtype.ext
    funext y
    exact (ha ⟨y.val, y.property.1.1⟩).trans
      ((hW y.property.2).trans (hb ⟨y.val, y.property.1.2⟩).symm)
  rw [← (presheaf A).germ_res_apply jU x hxZ s,
    ← (presheaf A).germ_res_apply jV x hxZ t, heq]

/-- The stalk is the C∞ localization at the corresponding real point,
as an isomorphism of underlying commutative rings. -/
def stalkIso (x : RealSpectrum A) : (presheaf A).stalk x ≅
    CommRingCat.of (Localizations A x) :=
  (RingEquiv.ofBijective (stalkEvaluation A x).hom
    ⟨stalkEvaluation_injective A x, stalkEvaluation_surjective A x⟩).toCommRingCatIso

end StructureSheaf
end ProjectAInos.SmoothGeometry
