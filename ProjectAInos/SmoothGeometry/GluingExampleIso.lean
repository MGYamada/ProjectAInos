/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.GluingExample
public import ProjectAInos.SmoothGeometry.OpenCover

/-! # The two-piece gluing is the smooth affine line

The descent morphism `toLine` of `GluingExample` is an isomorphism of C∞
schemes. It is injective on points because the two copies of the overlap are
identified in the gluing, and it is an open immersion on each piece, so
`Scheme.GlueData.desc_isIso` applies.

The coordinate function is then followed through the gluing. Sections of the
line and of its open pieces are smooth real functions, so their values are
computed. The restrictions of the coordinate to the two pieces agree on the
overlap, and the section of the gluing that they determine corresponds to the
coordinate under the isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Set Opposite
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry

namespace Scheme

/-- Pulling a global section back along a composite. -/
theorem Γ_map_comp_apply {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (s : Z.sections ⊤) :
    Γ.map (f ≫ g).op s = Γ.map f.op (Γ.map g.op s) := rfl

theorem Γ_map_congr {X Y : Scheme} {f g : X ⟶ Y} (h : f = g) (s : Y.sections ⊤) :
    Γ.map f.op s = Γ.map g.op s := by rw [h]

end Scheme

namespace GluingExample

/-! ## The isomorphism -/

private theorem eqToHom_cancel_aux {C : Type*} [Category C] {V V' O P Q G : C} (p : V = O)
    (q : V = V') (r : V' = O) (a : O ⟶ P) (b : O ⟶ Q) (c : P ⟶ G) (d : Q ⟶ G)
    (h : eqToHom q ≫ (eqToHom r ≫ b) ≫ d = (eqToHom p ≫ a) ≫ c) : a ≫ c = b ≫ d := by
  subst q
  subst r
  simpa using h.symm

/-- The two inclusions of the overlap agree in the gluing. -/
theorem overlapToPiece_ι :
    overlapToPiece false ≫ datum.ι false = overlapToPiece true ≫ datum.ι true := by
  have h := datum.glue_condition false true
  change (CategoryTheory.GlueData.ofGlueData' offDiagonal).t false true ≫
    (CategoryTheory.GlueData.ofGlueData' offDiagonal).f true false ≫ datum.ι true =
      (CategoryTheory.GlueData.ofGlueData' offDiagonal).f false true ≫ datum.ι false at h
  simp only [CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', offDiagonal,
    Bool.false_eq_true, Bool.true_eq_false, ↓reduceDIte, Category.id_comp, Category.assoc,
    eqToHom_trans_assoc] at h
  exact eqToHom_cancel_aux _ _ _ (overlapToPiece false) (overlapToPiece true)
    (datum.ι false) (datum.ι true) h

/-- The inclusion of the overlap in a piece does not move the point of the line. -/
theorem overlapToPiece_val (i : Bool) (w : overlap) :
    ((overlapToPiece i).toSmoothLRSHom.base w).val = w.val :=
  congrArg (fun f : overlap ⟶ line => f.toSmoothLRSHom.base w) (overlapToPiece_comp i)

/-- On the image of a piece, `toLine` returns the point of the line. -/
theorem toLine_ι_apply (i : datum.J) (y : datum.U i) :
    toLine.toSmoothLRSHom.base ((datum.ι i).toSmoothLRSHom.base y) = y.val :=
  congrArg (fun f : datum.U i ⟶ line => f.toSmoothLRSHom.base y) (inclusion_toLine i)

/-- Points of two pieces over the same point of the line are equal in the gluing. -/
theorem ι_eq_of_val_eq : ∀ (i j : Bool) (y : piece i) (z : piece j), y.val = z.val →
    (datum.ι i).toSmoothLRSHom.base y = (datum.ι j).toSmoothLRSHom.base z
  | false, false, y, z, h => by rw [Subtype.ext h]
  | true, true, y, z, h => by rw [Subtype.ext h]
  | false, true, y, z, h => by
    let w : overlap := ⟨y.val, y.property, h ▸ z.property⟩
    have hy : (overlapToPiece false).toSmoothLRSHom.base w = y :=
      Subtype.ext (overlapToPiece_val false w)
    have hz : (overlapToPiece true).toSmoothLRSHom.base w = z :=
      Subtype.ext ((overlapToPiece_val true w).trans h)
    rw [← hy, ← hz]
    exact congrArg (fun f : overlap ⟶ datum.glued => f.toSmoothLRSHom.base w) overlapToPiece_ι
  | true, false, y, z, h => by
    let w : overlap := ⟨y.val, h ▸ z.property, y.property⟩
    have hy : (overlapToPiece true).toSmoothLRSHom.base w = y :=
      Subtype.ext (overlapToPiece_val true w)
    have hz : (overlapToPiece false).toSmoothLRSHom.base w = z :=
      Subtype.ext ((overlapToPiece_val false w).trans h)
    rw [← hy, ← hz]
    exact (congrArg (fun f : overlap ⟶ datum.glued => f.toSmoothLRSHom.base w)
      overlapToPiece_ι).symm

theorem toLine_injective : Function.Injective toLine.toSmoothLRSHom.base := by
  intro a b hab
  obtain ⟨i, y, rfl⟩ := datum.ι_jointly_surjective a
  obtain ⟨j, z, rfl⟩ := datum.ι_jointly_surjective b
  exact ι_eq_of_val_eq i j y z ((toLine_ι_apply i y).symm.trans (hab.trans (toLine_ι_apply j z)))

theorem toLine_bijective : Function.Bijective toLine.toSmoothLRSHom.base :=
  ⟨toLine_injective, toLine_surjective⟩

instance toLine_isOpenImmersion : Scheme.IsOpenImmersion toLine :=
  datum.desc_isOpenImmersion (H := fun _ => Scheme.ofRestrict_isOpenImmersion line _)
    pieceInclusion piece_compatible toLine_injective

/-- The descent morphism is an isomorphism of C∞ schemes. -/
instance toLine_isIso : IsIso toLine :=
  datum.desc_isIso (H := fun _ => Scheme.ofRestrict_isOpenImmersion line _)
    pieceInclusion piece_compatible toLine_bijective

/-- The gluing of the two half-lines is the smooth affine line. -/
def gluedIsoLine : datum.glued ≅ line := asIso toLine

@[simp] theorem gluedIsoLine_hom : gluedIsoLine.hom = toLine := rfl

/-- The inverse of `toLine`. -/
def fromLine : line ⟶ datum.glued := gluedIsoLine.inv

@[simp] theorem gluedIsoLine_inv : gluedIsoLine.inv = fromLine := rfl

@[reassoc (attr := simp)]
theorem toLine_fromLine : toLine ≫ fromLine = 𝟙 datum.glued := gluedIsoLine.hom_inv_id

@[reassoc (attr := simp)]
theorem fromLine_toLine : fromLine ≫ toLine = 𝟙 line := gluedIsoLine.inv_hom_id

/-- The inverse sends each open piece of the line to its copy in the gluing. -/
@[reassoc (attr := simp)]
theorem pieceInclusion_fromLine (i : datum.J) : pieceInclusion i ≫ fromLine = datum.ι i :=
  gluedIsoLine.comp_inv_eq.mpr (inclusion_toLine i).symm

/-- The stalk maps of `toLine` are isomorphisms of local rings. -/
theorem toLine_stalkMap_isIso (x : datum.glued) :
    IsIso (toLine.toSmoothLRSHom.toLRSHom.stalkMap x) :=
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.stalk_iso
    (H := toLine_isOpenImmersion) _ x

/-- A morphism out of the line is determined by its restrictions to the two pieces. -/
theorem line_hom_ext {X : Scheme} {f g : line ⟶ X}
    (h : ∀ i : datum.J, pieceInclusion i ≫ f = pieceInclusion i ≫ g) : f = g := by
  apply (cancel_epi toLine).mp
  apply datum.hom_ext
  intro i
  rw [inclusion_toLine_assoc, inclusion_toLine_assoc]
  exact h i

/-! ## The coordinate function -/

/-- Sections of the line are smooth real functions. This is the value at a point. -/
def sectionEval {U : Opens (Fin 1 → ℝ)} (s : line.sections U) (x : Fin 1 → ℝ) (hx : x ∈ U) :
    ℝ :=
  let f : C^∞⟮𝓘(ℝ, Fin 1 → ℝ), U; ℝ⟯ := s
  f ⟨x, hx⟩

theorem sectionEval_ext {U : Opens (Fin 1 → ℝ)} {s t : line.sections U}
    (h : ∀ (x : Fin 1 → ℝ) (hx : x ∈ U), sectionEval s x hx = sectionEval t x hx) : s = t := by
  let f : C^∞⟮𝓘(ℝ, Fin 1 → ℝ), U; ℝ⟯ := s
  let g : C^∞⟮𝓘(ℝ, Fin 1 → ℝ), U; ℝ⟯ := t
  change f = g
  ext ⟨x, hx⟩
  exact h x hx

/-- Smooth operations on sections of the line act on the values. -/
theorem sectionEval_op {U : Opens (Fin 1 → ℝ)} {n : ℕ} (g : SmoothAlgebra.SmoothOperation n)
    (a : Fin n → line.sections U) (x : Fin 1 → ℝ) (hx : x ∈ U) :
    sectionEval (SmoothAlgebra.SmoothRing.op g a) x hx = g fun k => sectionEval (a k) x hx :=
  rfl

/-- The coordinate function, as a global section of the line. -/
def coordinate : line.sections ⊤ :=
  let f : C^∞⟮𝓘(ℝ, Fin 1 → ℝ), (⊤ : Opens (Fin 1 → ℝ)); ℝ⟯ :=
    ⟨fun x => x.val 0,
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).contMDiff.comp
        contMDiff_subtype_val⟩
  f

@[simp] theorem sectionEval_coordinate (x : Fin 1 → ℝ) :
    sectionEval coordinate x trivial = x 0 := rfl

theorem coordinate_nonconstant :
    sectionEval coordinate (fun _ => 0) trivial ≠ sectionEval coordinate (fun _ => 1) trivial := by
  simp

/-- The value of a global section of a piece at a point of the piece. -/
def pieceEval (i : Bool) (s : (piece i).sections ⊤) (y : piece i) : ℝ :=
  sectionEval (U := (pieceOpen i).isOpenEmbedding.isOpenMap.functor.obj ⊤) s y.val
    ⟨y, trivial, rfl⟩

/-- Restriction to a piece does not change the values. -/
theorem pieceEval_restrict (i : Bool) (s : line.sections ⊤) (y : piece i) :
    pieceEval i (Scheme.Γ.map (pieceInclusion i).op s) y = sectionEval s y.val trivial := rfl

/-- The value of a global section of the overlap at a point of the overlap. -/
def overlapEval (s : overlap.sections ⊤) (w : overlap) : ℝ :=
  sectionEval (U := overlapOpen.isOpenEmbedding.isOpenMap.functor.obj ⊤) s w.val
    ⟨w, trivial, rfl⟩

theorem overlapEval_restrict (s : line.sections ⊤) (w : overlap) :
    overlapEval (Scheme.Γ.map overlapInclusion.op s) w = sectionEval s w.val trivial := rfl

/-- A global section of the line is determined by its restrictions to the two pieces. -/
theorem line_section_ext {s t : line.sections ⊤}
    (h : ∀ i : Bool, Scheme.Γ.map (pieceInclusion i).op s =
      Scheme.Γ.map (pieceInclusion i).op t) : s = t := by
  apply sectionEval_ext
  intro x _
  rcases lt_or_ge (x 0) 1 with hx | hx
  · exact congrArg (fun u => pieceEval false u ⟨x, hx⟩) (h false)
  · have hx' : -1 < x 0 := by linarith
    exact congrArg (fun u => pieceEval true u ⟨x, hx'⟩) (h true)

/-- The coordinate restricted to a piece. -/
def pieceCoordinate (i : Bool) : (piece i).sections ⊤ :=
  Scheme.Γ.map (pieceInclusion i).op coordinate

@[simp] theorem pieceEval_pieceCoordinate (i : Bool) (y : piece i) :
    pieceEval i (pieceCoordinate i) y = y.val 0 := rfl

/-- Restricted to the overlap, the coordinate of either piece is that of the line. -/
theorem overlapToPiece_pieceCoordinate (i : Bool) :
    Scheme.Γ.map (overlapToPiece i).op (pieceCoordinate i) =
      Scheme.Γ.map overlapInclusion.op coordinate :=
  (Scheme.Γ_map_comp_apply (overlapToPiece i) (pieceInclusion i) coordinate).symm.trans
    (Scheme.Γ_map_congr (overlapToPiece_comp i) coordinate)

/-- The coordinates of the two pieces agree on the overlap. -/
theorem pieceCoordinate_overlap :
    Scheme.Γ.map (overlapToPiece false).op (pieceCoordinate false) =
      Scheme.Γ.map (overlapToPiece true).op (pieceCoordinate true) :=
  (overlapToPiece_pieceCoordinate false).trans (overlapToPiece_pieceCoordinate true).symm

/-- On the overlap both restrictions take the value of the coordinate. -/
theorem overlapEval_pieceCoordinate (i : Bool) (w : overlap) :
    overlapEval (Scheme.Γ.map (overlapToPiece i).op (pieceCoordinate i)) w = w.val 0 := by
  rw [overlapToPiece_pieceCoordinate, overlapEval_restrict]
  exact sectionEval_coordinate w.val

/-- The section of the gluing descended from the coordinates of the pieces. -/
def gluedCoordinate : datum.glued.sections ⊤ := Scheme.Γ.map toLine.op coordinate

/-- The descended section restricts to the coordinate of each piece. -/
theorem ι_gluedCoordinate (i : datum.J) :
    Scheme.Γ.map (datum.ι i).op gluedCoordinate = pieceCoordinate i :=
  (Scheme.Γ_map_comp_apply (datum.ι i) toLine coordinate).symm.trans
    (Scheme.Γ_map_congr (inclusion_toLine i) coordinate)

/-- Under the isomorphism the descended section is the coordinate of the line. -/
theorem fromLine_gluedCoordinate : Scheme.Γ.map fromLine.op gluedCoordinate = coordinate :=
  (Scheme.Γ_map_comp_apply fromLine toLine coordinate).symm.trans
    (Scheme.Γ_map_congr fromLine_toLine coordinate)

/-- A global section of the gluing is determined by its restrictions to the pieces. -/
theorem glued_section_ext {s t : datum.glued.sections ⊤}
    (h : ∀ i : datum.J, Scheme.Γ.map (datum.ι i).op s = Scheme.Γ.map (datum.ι i).op t) :
    s = t := by
  have hline : Scheme.Γ.map fromLine.op s = Scheme.Γ.map fromLine.op t := by
    apply line_section_ext
    intro i
    have e (u : datum.glued.sections ⊤) :
        Scheme.Γ.map (pieceInclusion i).op (Scheme.Γ.map fromLine.op u) =
          Scheme.Γ.map (datum.ι i).op u :=
      (Scheme.Γ_map_comp_apply (pieceInclusion i) fromLine u).symm.trans
        (Scheme.Γ_map_congr (pieceInclusion_fromLine i) u)
    rw [e s, e t]
    exact h i
  have e (u : datum.glued.sections ⊤) :
      Scheme.Γ.map toLine.op (Scheme.Γ.map fromLine.op u) = u :=
    (Scheme.Γ_map_comp_apply toLine fromLine u).symm.trans (Scheme.Γ_map_congr toLine_fromLine u)
  rw [← e s, ← e t, hline]

/-- The descended section is the only one that restricts to the coordinates of the pieces. -/
theorem gluedCoordinate_unique {s : datum.glued.sections ⊤}
    (h : ∀ i : datum.J, Scheme.Γ.map (datum.ι i).op s = pieceCoordinate i) :
    s = gluedCoordinate :=
  glued_section_ext fun i => (h i).trans (ι_gluedCoordinate i).symm

/-- A smooth operation applied to the descended section is computed on each piece. -/
theorem pieceEval_op_gluedCoordinate (g : SmoothAlgebra.SmoothOperation 1) (i : Bool)
    (y : piece i) :
    pieceEval i (Scheme.Γ.map (datum.ι i).op
      (SmoothAlgebra.SmoothRing.op g fun _ => gluedCoordinate)) y = g fun _ => y.val 0 :=
  (congrArg (fun u => pieceEval i u y)
    ((ConcreteCategory.hom (Scheme.Γ.map (datum.ι i).op)).map_op g fun _ => gluedCoordinate)).trans
    (congrArg (fun u : (piece i).sections ⊤ =>
      pieceEval i (SmoothAlgebra.SmoothRing.op g fun _ => u) y) (ι_gluedCoordinate i))

end GluingExample
end ProjectAInos.SmoothGeometry
