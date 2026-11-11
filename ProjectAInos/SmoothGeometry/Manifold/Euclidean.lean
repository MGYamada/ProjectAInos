/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Manifold.Germs
public import ProjectAInos.SmoothGeometry.Scheme
public import ProjectAInos.SmoothGeometry.OpenImmersion

/-! # The Euclidean affine C∞ scheme -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.Manifold

open SmoothAlgebra TopologicalSpace CategoryTheory Opposite Filter

/-- The point map in the Euclidean comparison. -/
def euclideanToSpec (n : ℕ) : TopCat.of (Fin n → ℝ) ⟶
    Spec.topObj (SmoothRingCat.of (SmoothOperation n)) :=
  TopCat.ofHom ⟨(RealSpectrum.euclideanHomeomorph n).symm,
    (RealSpectrum.euclideanHomeomorph n).symm.continuous⟩

/-- Pull an open subset of the real spectrum back to Euclidean space. -/
abbrev euclideanOpen {n : ℕ} (U : Opens (RealSpectrum (SmoothOperation n))) :
    Opens (Fin n → ℝ) := (Opens.map (euclideanToSpec n)).obj U

/-- Take real residues of a locally represented section. -/
def sectionFunction {n : ℕ} {U : Opens (RealSpectrum (SmoothOperation n))}
    (s : StructureSheaf.Sections (SmoothOperation n) U) (x : euclideanOpen U) : ℝ :=
  PointLocalization.residue (SmoothOperation.eval x.val)
    (s.val ⟨euclideanToSpec n x.val, x.property⟩)

theorem sectionFunction_contMDiff {n : ℕ} {U : Opens (RealSpectrum (SmoothOperation n))}
    (s : StructureSheaf.Sections (SmoothOperation n) U) :
    ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ (sectionFunction s) := by
  intro x
  obtain ⟨V, hxV, iV, a, ha⟩ := s.property ⟨euclideanToSpec n x.val, x.property⟩
  have hV : ∀ᶠ y : euclideanOpen U in 𝓝 x, euclideanToSpec n y.val ∈ V :=
    ((euclideanToSpec n).hom.continuous.comp continuous_subtype_val).continuousAt
      (V.isOpen.mem_nhds hxV)
  apply (a.contMDiff.comp contMDiff_subtype_val).contMDiffAt.congr_of_eventuallyEq
  filter_upwards [hV] with y hy
  exact congrArg (PointLocalization.residue (SmoothOperation.eval y.val))
    (ha ⟨euclideanToSpec n y.val, hy⟩)

/-- The comparison on sections is a morphism of C∞-rings. -/
def euclideanComap {n : ℕ} (U : Opens (RealSpectrum (SmoothOperation n))) :
    SmoothRingHom (StructureSheaf.Sections (SmoothOperation n) U)
      C^∞⟮𝓘(ℝ, Fin n → ℝ), euclideanOpen U; ℝ⟯ where
  toFun s := ⟨sectionFunction s, sectionFunction_contMDiff s⟩
  map_op' f a := by
    apply Subtype.ext
    funext x
    exact (PointLocalization.residue (SmoothOperation.eval x.val)).map_op f _

theorem euclideanComap_injective {n : ℕ} (U : Opens (RealSpectrum (SmoothOperation n))) :
    Function.Injective (euclideanComap U) := by
  intro s t h
  apply Subtype.ext
  funext x
  rcases x with ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := (RealSpectrum.euclideanHomeomorph n).symm.surjective x
  obtain ⟨V, hyV, iV, a, ha⟩ := s.property ⟨euclideanToSpec n y, hx⟩
  obtain ⟨W, hyW, iW, b, hb⟩ := t.property ⟨euclideanToSpec n y, hx⟩
  refine (ha ⟨euclideanToSpec n y, hyV⟩).trans
    (Eq.trans ?_ (hb ⟨euclideanToSpec n y, hyW⟩).symm)
  apply (euclidean_of_eq_iff y a b).mpr
  have hV := (euclideanToSpec n).hom.continuous.continuousAt (V.isOpen.mem_nhds hyV)
  have hW := (euclideanToSpec n).hom.continuous.continuousAt (W.isOpen.mem_nhds hyW)
  filter_upwards [hV, hW] with z hzV hzW
  have hz := congrArg (fun q : C^∞⟮𝓘(ℝ, Fin n → ℝ), euclideanOpen U; ℝ⟯ =>
    q ⟨z, iV.le hzV⟩) h
  exact (congrArg (PointLocalization.residue (SmoothOperation.eval z))
    (ha ⟨euclideanToSpec n z, hzV⟩)).symm.trans
      (hz.trans (congrArg (PointLocalization.residue (SmoothOperation.eval z))
        (hb ⟨euclideanToSpec n z, hzW⟩)))

/-- The point-local value of a smooth function on an open set. -/
def euclideanGerm {n : ℕ} {V : Opens (Fin n → ℝ)}
    (f : C^∞⟮𝓘(ℝ, Fin n → ℝ), V; ℝ⟯) (x : V) :
    PointLocalization (SmoothOperation.eval x.val) :=
  PointLocalization.of (SmoothOperation.eval x.val)
    (exists_global_representative f x).choose

theorem euclideanGerm_eq {n : ℕ} {V : Opens (Fin n → ℝ)}
    (f : C^∞⟮𝓘(ℝ, Fin n → ℝ), V; ℝ⟯) (x : V) (a : SmoothOperation n)
    (ha : ∀ᶠ y : V in 𝓝 x, a y = f y) :
    euclideanGerm f x = PointLocalization.of (SmoothOperation.eval x.val) a := by
  apply (euclidean_of_eq_iff x.val _ a).mpr
  rw [← V.isOpenEmbedding'.map_nhds_eq x]
  change ∀ᶠ y : V in 𝓝 x, (exists_global_representative f x).choose y = a y
  filter_upwards [(exists_global_representative f x).choose_spec, ha] with y hy hy'
  exact hy.trans hy'.symm

@[simp] theorem euclideanGerm_residue {n : ℕ} {V : Opens (Fin n → ℝ)}
    (f : C^∞⟮𝓘(ℝ, Fin n → ℝ), V; ℝ⟯) (x : V) :
    PointLocalization.residue (SmoothOperation.eval x.val) (euclideanGerm f x) = f x :=
  Filter.EventuallyEq.eq_of_nhds (exists_global_representative f x).choose_spec

/-- The Euclidean point homeomorphism restricted to an open set. -/
def euclideanOpenHomeomorph {n : ℕ} (U : Opens (RealSpectrum (SmoothOperation n))) :
    euclideanOpen U ≃ₜ U :=
  (RealSpectrum.euclideanHomeomorph n).symm.subtype (fun _ => Iff.rfl)

/-- Reindex the germ along the Euclidean point homeomorphism. -/
def euclideanGermAt {n : ℕ} {U : Opens (RealSpectrum (SmoothOperation n))}
    (f : C^∞⟮𝓘(ℝ, Fin n → ℝ), euclideanOpen U; ℝ⟯) (x : U) :
    PointLocalization x.val.hom :=
  cast (congrArg (fun z : RealSpectrum (SmoothOperation n) => PointLocalization z.hom)
    (congrArg Subtype.val ((euclideanOpenHomeomorph U).apply_symm_apply x)))
    (euclideanGerm f ((euclideanOpenHomeomorph U).symm x))

@[simp] theorem euclideanGermAt_apply {n : ℕ} {U : Opens (RealSpectrum (SmoothOperation n))}
    (f : C^∞⟮𝓘(ℝ, Fin n → ℝ), euclideanOpen U; ℝ⟯) (x : euclideanOpen U) :
    euclideanGermAt f (euclideanOpenHomeomorph U x) = euclideanGerm f x := rfl

/-- Smooth Euclidean functions supply locally represented spectrum sections. -/
def euclideanSection {n : ℕ} {U : Opens (RealSpectrum (SmoothOperation n))}
    (f : C^∞⟮𝓘(ℝ, Fin n → ℝ), euclideanOpen U; ℝ⟯) :
    StructureSheaf.Sections (SmoothOperation n) U :=
  ⟨euclideanGermAt f, by
    apply (StructureSheaf.locallyRepresented_iff_eventually _ _).mpr
    intro x
    obtain ⟨y, rfl⟩ := (euclideanOpenHomeomorph U).surjective x
    let a := (exists_global_representative f y).choose
    have ha : ∀ᶠ z : euclideanOpen U in 𝓝 y, ∀ᶠ w : euclideanOpen U in 𝓝 z, a w = f w :=
      Filter.Eventually.eventually_nhds (exists_global_representative f y).choose_spec
    refine ⟨a, ?_⟩
    rw [← (euclideanOpenHomeomorph U).map_nhds_eq y]
    change ∀ᶠ z : euclideanOpen U in 𝓝 y,
      euclideanGermAt f (euclideanOpenHomeomorph U z) =
        PointLocalization.of (SmoothOperation.eval z.val) a
    filter_upwards [ha] with z hz
    exact euclideanGerm_eq f z a hz⟩

@[simp] theorem euclideanComap_section {n : ℕ} {U : Opens (RealSpectrum (SmoothOperation n))}
    (f : C^∞⟮𝓘(ℝ, Fin n → ℝ), euclideanOpen U; ℝ⟯) :
    euclideanComap U (euclideanSection f) = f := by
  apply Subtype.ext
  funext x
  exact euclideanGerm_residue f x

theorem euclideanComap_surjective {n : ℕ} (U : Opens (RealSpectrum (SmoothOperation n))) :
    Function.Surjective (euclideanComap U) :=
  fun f => ⟨euclideanSection f, euclideanComap_section f⟩

/-- The comparison on the actual presheaves, including restriction maps. -/
def euclideanPresheafMap (n : ℕ) :
    (locallyRingedSpace 𝓘(ℝ, Fin n → ℝ) (Fin n → ℝ)).toPresheafedSpace ⟶
      (Spec.locallyRingedSpaceObj (SmoothRingCat.of (SmoothOperation n))).toPresheafedSpace where
  base := euclideanToSpec n
  c :=
    { app U := CommRingCat.ofHom (euclideanComap U.unop).toAlgHom.toRingHom
      naturality := by intros; ext f; rfl }

instance euclideanPresheafMap_isIso (n : ℕ) : IsIso (euclideanPresheafMap n) := by
  have : IsIso (euclideanPresheafMap n).base :=
    (TopCat.isoOfHomeo (X := TopCat.of (Fin n → ℝ))
      (Y := TopCat.of (RealSpectrum (SmoothOperation n)))
      (RealSpectrum.euclideanHomeomorph n).symm).isIso_hom
  have hApp (U) : IsIso ((euclideanPresheafMap n).c.app U) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact ⟨euclideanComap_injective U.unop, euclideanComap_surjective U.unop⟩
  have : IsIso (euclideanPresheafMap n).c := NatIso.isIso_of_isIso_app _
  exact AlgebraicGeometry.PresheafedSpace.isIso_of_components _

/-- The comparison is an isomorphism of underlying locally ringed spaces. -/
def euclideanUnderlyingIso (n : ℕ) :
    (locallyRingedSpace 𝓘(ℝ, Fin n → ℝ) (Fin n → ℝ)).toLocallyRingedSpace ≅
      (Spec.locallyRingedSpaceObj (SmoothRingCat.of (SmoothOperation n))).toLocallyRingedSpace :=
  AlgebraicGeometry.LocallyRingedSpace.isoOfSheafedSpaceIso
    (AlgebraicGeometry.SheafedSpace.fullyFaithfulForgetToPresheafedSpace.preimageIso
      (asIso (euclideanPresheafMap n)))

/-- The Euclidean comparison preserves every C∞ operation on sections. -/
def euclideanMap (n : ℕ) :
    locallyRingedSpace 𝓘(ℝ, Fin n → ℝ) (Fin n → ℝ) ⟶
      Spec.locallyRingedSpaceObj (SmoothRingCat.of (SmoothOperation n)) where
  toLRSHom := (euclideanUnderlyingIso n).hom
  map_op U := (euclideanComap U.unop).map_op

/-- Euclidean space with its smooth-function sheaf is the C∞ spectrum of its
free C∞-ring, as a smooth locally ringed space. -/
def euclideanIso (n : ℕ) :
    locallyRingedSpace 𝓘(ℝ, Fin n → ℝ) (Fin n → ℝ) ≅
      Spec.locallyRingedSpaceObj (SmoothRingCat.of (SmoothOperation n)) :=
  let : IsIso (LocallyRingedSpace.forgetToLocallyRingedSpace.map (euclideanMap n)) :=
    (euclideanUnderlyingIso n).isIso_hom
  LocallyRingedSpace.isoOfUnderlying (euclideanMap n)

/-- Euclidean space as a C∞ scheme, using its actual smooth-function sheaf. -/
def euclideanScheme (n : ℕ) : Scheme where
  toSmoothLocallyRingedSpace := locallyRingedSpace 𝓘(ℝ, Fin n → ℝ) (Fin n → ℝ)
  local_affine _ := ⟨⟨⊤, trivial⟩, SmoothRingCat.of (SmoothOperation n),
    ⟨(locallyRingedSpace 𝓘(ℝ, Fin n → ℝ) (Fin n → ℝ)).restrictTopIso ≪≫ euclideanIso n⟩⟩

end ProjectAInos.SmoothGeometry.Manifold
