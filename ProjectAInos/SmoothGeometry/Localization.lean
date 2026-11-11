/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.RealSpectrumTopology
public import ProjectAInos.SmoothAlgebra.LocalizationComparison
public import ProjectAInos.SmoothGeometry.Spec
public import Mathlib.Geometry.RingedSpace.OpenImmersion

/-! # Spectra of C∞ localizations and principal open subspaces -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace ProjectAInos.SmoothGeometry

open SmoothAlgebra TopologicalSpace CategoryTheory Topology

variable {A : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]

namespace Localization

/-- The real points at which every element of the localized set is nonzero. -/
def locus (S : Set A) : Set (RealSpectrum A) := {x | ∀ s : S, x s.val ≠ 0}

/-- The universal property identifies points of a localization. -/
def pointsEquiv (S : Set A) : RealSpectrum (SmoothLocalization S) ≃ locus S where
  toFun y := ⟨RealSpectrum.comap (SmoothLocalization.of S) y,
    fun s => ((SmoothLocalization.isUnit_of S s).map y.hom.toAlgHom.toRingHom).ne_zero⟩
  invFun x := SmoothLocalization.lift S x.val.hom (fun s => isUnit_iff_ne_zero.mpr (x.property s))
  left_inv y := by
    apply SmoothLocalization.hom_ext
    intro a
    exact SmoothLocalization.lift_of S _ _ a
  right_inv x := by
    apply Subtype.ext
    apply SmoothRingHom.ext
    intro a
    exact SmoothLocalization.lift_of S _ _ a

theorem continuous_pointsEquiv_symm (S : Set A) : Continuous (pointsEquiv S).symm := by
  apply (RealSpectrum.continuous_iff_eval _).mpr
  intro a
  induction a using SmoothLocalization.induction_on with
  | hOf a =>
    have h : Continuous (fun x : locus S => x.val a) :=
      (RealSpectrum.continuous_eval a).comp continuous_subtype_val
    exact h.congr (fun x => (SmoothLocalization.lift_of S x.val.hom _ a).symm)
  | hInv s =>
    have h := ((RealSpectrum.continuous_eval s.val).comp continuous_subtype_val).inv₀
      (fun x : locus S => x.property s)
    apply h.congr
    intro x
    change (x.val s.val)⁻¹ = SmoothLocalization.lift S x.val.hom _ (SmoothLocalization.inv S s)
    rw [SmoothLocalization.lift_inv, Units.val_inv_eq_inv_val, IsUnit.unit_spec]
    rfl
  | hOp f a ha =>
    have h := f.contMDiff.continuous.comp (continuous_pi ha)
    apply h.congr
    intro x
    exact ((pointsEquiv S).symm x).hom.map_op f a |>.symm

/-- For arbitrary sets the spectrum is the corresponding subspace; it need not be open. -/
def homeomorph (S : Set A) : RealSpectrum (SmoothLocalization S) ≃ₜ locus S where
  toEquiv := pointsEquiv S
  continuous_toFun := (RealSpectrum.continuous_comap (SmoothLocalization.of S)).subtype_mk _
  continuous_invFun := continuous_pointsEquiv_symm S

theorem locus_singleton (a : A) : locus ({a} : Set A) = (RealSpectrum.basicOpen a : Set _) := by
  ext x
  change (∀ s : ({a} : Set A), x s.val ≠ 0) ↔ x a ≠ 0
  constructor
  · intro h
    exact h ⟨a, Set.mem_singleton a⟩
  · intro h s
    have hs : s.val = a := s.property
    simpa only [hs] using h

/-- The spectrum of localization away from one element is its principal open set. -/
def awayHomeomorph (a : A) : RealSpectrum (SmoothLocalization ({a} : Set A)) ≃ₜ
    RealSpectrum.basicOpen a :=
  (homeomorph {a}).trans (Homeomorph.setCongr (locus_singleton a))

theorem away_range (a : A) :
    Set.range (RealSpectrum.comap (SmoothLocalization.of ({a} : Set A))) =
      (RealSpectrum.basicOpen a : Set _) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (awayHomeomorph a y).property
  · intro hx
    obtain ⟨y, hy⟩ := (awayHomeomorph a).surjective ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩

theorem away_isOpenEmbedding (a : A) :
    IsOpenEmbedding (RealSpectrum.comap (SmoothLocalization.of ({a} : Set A))) :=
  (RealSpectrum.basicOpen a).isOpenEmbedding'.comp (awayHomeomorph a).isOpenEmbedding

/-- Localizing induces an isomorphism on every surviving stalk. -/
instance stalkMap_isIso (S : Set A) (y : RealSpectrum (SmoothLocalization S)) :
    IsIso ((Spec.locallyRingedSpaceMap (A := SmoothRingCat.of A)
      (B := SmoothRingCat.of (SmoothLocalization S)) (SmoothLocalization.of S)).toLRSHom.stalkMap y) := by
  let e := StructureSheaf.stalkIso (SmoothLocalization S) y
  let d := StructureSheaf.stalkIso A (RealSpectrum.comap (SmoothLocalization.of S) y)
  let q := (SmoothLocalization.pointRingEquiv S y.hom).toCommRingCatIso
  have h : (Spec.locallyRingedSpaceMap (A := SmoothRingCat.of A)
      (B := SmoothRingCat.of (SmoothLocalization S)) (SmoothLocalization.of S)).toLRSHom.stalkMap y ≫
      e.hom = d.hom ≫ q.hom := by
    ext a
    exact Spec.stalkMap_evaluation (A := SmoothRingCat.of A)
      (B := SmoothRingCat.of (SmoothLocalization S)) (SmoothLocalization.of S) y a
  have heq : (Spec.locallyRingedSpaceMap (A := SmoothRingCat.of A)
      (B := SmoothRingCat.of (SmoothLocalization S)) (SmoothLocalization.of S)).toLRSHom.stalkMap y =
      d.hom ≫ q.hom ≫ e.inv := by
    apply (cancel_mono e.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h
  rw [heq]
  infer_instance

/-- Principal localizations give actual open immersions of locally ringed spaces. -/
instance away_isOpenImmersion (a : A) :
    AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (Spec.locallyRingedSpaceMap (A := SmoothRingCat.of A)
        (B := SmoothRingCat.of (SmoothLocalization ({a} : Set A)))
        (SmoothLocalization.of ({a} : Set A))).toLRSHom := by
  apply AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_stalk_iso
  exact away_isOpenEmbedding a

end Localization
end ProjectAInos.SmoothGeometry
