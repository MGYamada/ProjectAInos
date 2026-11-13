/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Gluing
public import ProjectAInos.SmoothGeometry.Manifold.Euclidean

/-! # Gluing two open pieces of the affine smooth line -/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Set

namespace ProjectAInos.SmoothGeometry.GluingExample

/-- The smooth affine line, using its smooth-function sheaf. -/
def line : Scheme := Manifold.euclideanScheme 1

theorem continuous_coordinate : Continuous (fun x : line => x 0) := by
  change Continuous (fun x : Fin 1 → ℝ => x 0)
  exact continuous_apply 0

/-- Two open half-lines with a nonempty proper interval of overlap. -/
def pieceOpen : Bool → Opens line.carrier
  | false => ⟨{x | x 0 < 1}, isOpen_lt continuous_coordinate continuous_const⟩
  | true => ⟨{x | -1 < x 0}, isOpen_lt continuous_const continuous_coordinate⟩

def overlapOpen : Opens line.carrier := pieceOpen false ⊓ pieceOpen true

theorem overlap_nonempty : (overlapOpen : Set line).Nonempty := by
  refine ⟨fun _ => 0, ?_⟩
  change (0 : ℝ) < 1 ∧ -1 < (0 : ℝ)
  norm_num

theorem overlap_proper (i : Bool) : overlapOpen < pieceOpen i := by
  apply lt_of_le_of_ne
  · cases i
    · exact inf_le_left
    · exact inf_le_right
  · intro h
    cases i
    · have hx : (fun _ : Fin 1 => (-2 : ℝ)) ∈ pieceOpen false := by
        change (-2 : ℝ) < 1
        norm_num
      rw [← h] at hx
      change (-2 : ℝ) < 1 ∧ -1 < (-2 : ℝ) at hx
      norm_num at hx
    · have hx : (fun _ : Fin 1 => (2 : ℝ)) ∈ pieceOpen true := by
        change (-1 : ℝ) < 2
        norm_num
      rw [← h] at hx
      change (2 : ℝ) < 1 ∧ -1 < (2 : ℝ) at hx
      norm_num at hx

def piece (i : Bool) : Scheme := line.restrict (pieceOpen i).isOpenEmbedding

def overlap : Scheme := line.restrict overlapOpen.isOpenEmbedding

def pieceInclusion (i : Bool) : piece i ⟶ line := line.ofRestrict (pieceOpen i).isOpenEmbedding

def overlapInclusion : overlap ⟶ line := line.ofRestrict overlapOpen.isOpenEmbedding

instance (i : Bool) : Scheme.IsOpenImmersion (pieceInclusion i) :=
  Scheme.ofRestrict_isOpenImmersion line _

instance : Scheme.IsOpenImmersion overlapInclusion :=
  Scheme.ofRestrict_isOpenImmersion line _

theorem overlap_range_subset (i : Bool) :
    range overlapInclusion.toSmoothLRSHom.base ⊆ range (pieceInclusion i).toSmoothLRSHom.base := by
  rintro _ ⟨x, rfl⟩
  have hx : x.val ∈ pieceOpen i := by
    cases i
    · exact (show x.val ∈ pieceOpen false ∧ x.val ∈ pieceOpen true from x.property).1
    · exact (show x.val ∈ pieceOpen false ∧ x.val ∈ pieceOpen true from x.property).2
  exact ⟨⟨x.val, hx⟩, rfl⟩

def overlapToPiece (i : Bool) : overlap ⟶ piece i :=
  ⟨LocallyRingedSpace.IsOpenImmersion.lift (pieceInclusion i).toSmoothLRSHom
    overlapInclusion.toSmoothLRSHom (overlap_range_subset i)⟩

instance (i : Bool) : Scheme.IsOpenImmersion (overlapToPiece i) :=
  LocallyRingedSpace.IsOpenImmersion.lift_isOpenImmersion
    (pieceInclusion i).toSmoothLRSHom overlapInclusion.toSmoothLRSHom (overlap_range_subset i)

@[simp, reassoc]
theorem overlapToPiece_comp (i : Bool) :
    overlapToPiece i ≫ pieceInclusion i = overlapInclusion :=
  Scheme.Hom.ext (LocallyRingedSpace.IsOpenImmersion.lift_fac
    (pieceInclusion i).toSmoothLRSHom overlapInclusion.toSmoothLRSHom (overlap_range_subset i))

theorem no_three_distinct (i j k : Bool) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    False := by cases i <;> cases j <;> cases k <;> simp_all

/-- The off-diagonal entries are the same overlap, with identity transition. -/
def offDiagonal : CategoryTheory.GlueData' Scheme where
  J := Bool
  U := piece
  V _ _ _ := overlap
  f i _ _ := overlapToPiece i
  t _ _ _ := 𝟙 _
  t' i j k hij hik hjk := (no_three_distinct i j k hij hik hjk).elim
  t_fac i j k hij hik hjk := (no_three_distinct i j k hij hik hjk).elim
  t_inv _ _ _ := Category.id_comp _
  cocycle i j k hij hik hjk := (no_three_distinct i j k hij hik hjk).elim

/-- A concrete two-piece gluing datum in the category of smooth schemes. -/
def datum : Scheme.GlueData where
  toGlueData := CategoryTheory.GlueData.ofGlueData' offDiagonal
  f_open i j := by
    cases i <;> cases j <;>
      simp [CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', offDiagonal] <;>
      infer_instance

theorem piece_compatible (i j : datum.J) :
    datum.t i j ≫ datum.f j i ≫ pieceInclusion j = datum.f i j ≫ pieceInclusion i := by
  change (CategoryTheory.GlueData.ofGlueData' offDiagonal).t i j ≫
    (CategoryTheory.GlueData.ofGlueData' offDiagonal).f j i ≫ pieceInclusion j =
      (CategoryTheory.GlueData.ofGlueData' offDiagonal).f i j ≫ pieceInclusion i
  cases i <;> cases j <;>
    simp [CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', offDiagonal]

/-- The compatible inclusions descend to a morphism into the original line. -/
def toLine : datum.glued ⟶ line := datum.desc pieceInclusion piece_compatible

@[simp, reassoc]
theorem inclusion_toLine (i : datum.J) : datum.ι i ≫ toLine = pieceInclusion i :=
  datum.ι_desc pieceInclusion piece_compatible i

theorem toLine_surjective : Function.Surjective toLine.toSmoothLRSHom.base := by
  intro x
  have hx : x ∈ pieceOpen false ∨ x ∈ pieceOpen true := by
    change x 0 < 1 ∨ -1 < x 0
    by_cases h : x 0 < 1
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have fromPiece (i : datum.J) (hi : x ∈ pieceOpen i) : x ∈ range toLine.toSmoothLRSHom.base := by
    let y : datum.U i := ⟨x, hi⟩
    refine ⟨(datum.ι i).toSmoothLRSHom.base y, ?_⟩
    exact congrArg (fun f : datum.U i ⟶ line => f.toSmoothLRSHom.base y) (inclusion_toLine i)
  exact hx.elim (fromPiece false) (fromPiece true)

/-- The overlap inclusions give the actual categorical pullback over the line. -/
def overlapIsPullback : IsLimit
    (PullbackCone.mk (overlapToPiece false) (overlapToPiece true)
      ((overlapToPiece_comp false).trans (overlapToPiece_comp true).symm)) := by
  apply PullbackCone.isLimitAux'
  intro s
  have hr : range (s.fst ≫ pieceInclusion false).toSmoothLRSHom.base ⊆
      range overlapInclusion.toSmoothLRSHom.base := by
    rintro _ ⟨x, rfl⟩
    let y : piece false := s.fst.toSmoothLRSHom.base x
    let z : piece true := s.snd.toSmoothLRSHom.base x
    have h : y.val = z.val := congrArg
      (fun f : s.pt ⟶ line => f.toSmoothLRSHom.base x) s.condition
    exact ⟨⟨y.val, y.property, h ▸ z.property⟩, rfl⟩
  let l : s.pt ⟶ overlap :=
    ⟨LocallyRingedSpace.IsOpenImmersion.lift overlapInclusion.toSmoothLRSHom
      (s.fst ≫ pieceInclusion false).toSmoothLRSHom hr⟩
  have hl : l ≫ overlapInclusion = s.fst ≫ pieceInclusion false :=
    Scheme.Hom.ext (LocallyRingedSpace.IsOpenImmersion.lift_fac overlapInclusion.toSmoothLRSHom
      (s.fst ≫ pieceInclusion false).toSmoothLRSHom hr)
  have hleft : l ≫ overlapToPiece false = s.fst := by
    apply (cancel_mono (pieceInclusion false)).mp
    simpa only [Category.assoc, overlapToPiece_comp] using hl
  have hright : l ≫ overlapToPiece true = s.snd := by
    apply (cancel_mono (pieceInclusion true)).mp
    simpa only [Category.assoc, overlapToPiece_comp] using hl.trans s.condition
  exact ⟨l, hleft, hright, fun {_} hm _ => (cancel_mono (overlapToPiece false)).mp
    (hm.trans hleft.symm)⟩

/-- Descent acts on the entire smooth structure sheaf. -/
theorem toLine_map_op (U : Opens line.carrier) {n : ℕ}
    (op : SmoothAlgebra.SmoothOperation n) (a : Fin n → line.sections U) :
    toLine.app U (SmoothAlgebra.SmoothRing.op op a) =
      SmoothAlgebra.SmoothRing.op op (fun i => toLine.app U (a i)) :=
  (toLine.app U).map_op op a

end ProjectAInos.SmoothGeometry.GluingExample
