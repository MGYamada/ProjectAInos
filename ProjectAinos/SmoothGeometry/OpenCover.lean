/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Gluing

/-! # Morphisms that are open immersions on an open cover

A morphism of local C∞-ringed spaces that restricts to an open immersion on
each member of a jointly surjective family of open immersions has
isomorphisms on stalks and is an open map. If it is injective on points it
is an open immersion, and if it is bijective on points it is an isomorphism.
The descent morphism of a gluing is the main case.
-/

@[expose] public section

noncomputable section

universe u

namespace ProjectAinos.SmoothGeometry

open CategoryTheory Topology

namespace LocallyRingedSpace

variable {ι : Type*} {X Y : LocallyRingedSpace.{u}} {U : ι → LocallyRingedSpace.{u}}
  (g : ∀ i, U i ⟶ Y) (h : Y ⟶ X)

/-- The stalk maps are isomorphisms, since they are so on each piece. -/
theorem stalkMap_isIso_of_cover [∀ i, IsOpenImmersion (g i)]
    [H : ∀ i, IsOpenImmersion (g i ≫ h)]
    (hg : ∀ y : Y, ∃ (i : ι) (z : U i), (g i).base z = y) (y : Y) :
    IsIso (h.toLRSHom.stalkMap y) := by
  obtain ⟨i, z, rfl⟩ := hg y
  have e := AlgebraicGeometry.LocallyRingedSpace.stalkMap_comp (g i).toLRSHom h.toLRSHom z
  have hc : IsIso ((g i ≫ h).toLRSHom.stalkMap z) :=
    AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.stalk_iso (H := H i) _ z
  have hc' : IsIso (h.toLRSHom.stalkMap ((g i).base z) ≫ (g i).toLRSHom.stalkMap z) :=
    e ▸ hc
  exact IsIso.of_isIso_comp_right _ ((g i).toLRSHom.stalkMap z)

/-- The image of an open set is the union of its images through the pieces. -/
theorem isOpenMap_of_cover [∀ i, IsOpenImmersion (g i)] [H : ∀ i, IsOpenImmersion (g i ≫ h)]
    (hg : ∀ y : Y, ∃ (i : ι) (z : U i), (g i).base z = y) : IsOpenMap h.base := by
  intro V hV
  have hV' : h.base '' V = ⋃ i, (g i ≫ h).base '' ((g i).base ⁻¹' V) := by
    ext x
    simp only [Set.mem_image, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨i, z, rfl⟩ := hg y
      exact ⟨i, z, hy, rfl⟩
    · rintro ⟨i, z, hz, rfl⟩
      exact ⟨(g i).base z, hz, rfl⟩
  rw [hV']
  exact isOpen_iUnion fun i =>
    (H i).base_open.isOpenMap _ (hV.preimage (g i).base.hom.continuous)

/-- A morphism that is an open immersion on an open cover and injective on
points is an open immersion. -/
theorem isOpenImmersion_of_cover [∀ i, IsOpenImmersion (g i)]
    [∀ i, IsOpenImmersion (g i ≫ h)]
    (hg : ∀ y : Y, ∃ (i : ι) (z : U i), (g i).base z = y)
    (hinj : Function.Injective h.base) : IsOpenImmersion h := by
  have : ∀ y : Y, IsIso (h.toLRSHom.stalkMap y) := stalkMap_isIso_of_cover g h hg
  exact AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_stalk_iso h.toLRSHom
    (.of_continuous_injective_isOpenMap h.base.hom.continuous hinj (isOpenMap_of_cover g h hg))

/-- A morphism that is an open immersion on an open cover and bijective on
points is an isomorphism of local C∞-ringed spaces. -/
theorem isIso_of_cover [∀ i, IsOpenImmersion (g i)] [∀ i, IsOpenImmersion (g i ≫ h)]
    (hg : ∀ y : Y, ∃ (i : ι) (z : U i), (g i).base z = y)
    (hbij : Function.Bijective h.base) : IsIso h := by
  have ho : IsOpenImmersion h := isOpenImmersion_of_cover g h hg hbij.injective
  have : Epi h.toLRSHom.base := (TopCat.epi_iff_surjective _).mpr hbij.surjective
  have : IsIso (forgetToLocallyRingedSpace.map h) :=
    AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.to_iso (H := ho) h.toLRSHom
  exact isIso_of_reflects_iso h forgetToLocallyRingedSpace

end LocallyRingedSpace

namespace Scheme

variable {ι : Type*} {X Y : Scheme.{u}} {U : ι → Scheme.{u}} (g : ∀ i, U i ⟶ Y) (h : Y ⟶ X)

/-- The scheme form of `LocallyRingedSpace.isOpenImmersion_of_cover`. -/
theorem isOpenImmersion_of_cover [∀ i, IsOpenImmersion (g i)]
    [H : ∀ i, IsOpenImmersion (g i ≫ h)]
    (hg : ∀ y : Y, ∃ (i : ι) (z : U i), (g i).toSmoothLRSHom.base z = y)
    (hinj : Function.Injective h.toSmoothLRSHom.base) : IsOpenImmersion h :=
  have : ∀ i, LocallyRingedSpace.IsOpenImmersion ((g i).toSmoothLRSHom ≫ h.toSmoothLRSHom) := H
  LocallyRingedSpace.isOpenImmersion_of_cover (fun i => (g i).toSmoothLRSHom)
    h.toSmoothLRSHom hg hinj

/-- A morphism of C∞ schemes that is an open immersion on an open cover and
bijective on points is an isomorphism. -/
theorem isIso_of_cover [∀ i, IsOpenImmersion (g i)] [H : ∀ i, IsOpenImmersion (g i ≫ h)]
    (hg : ∀ y : Y, ∃ (i : ι) (z : U i), (g i).toSmoothLRSHom.base z = y)
    (hbij : Function.Bijective h.toSmoothLRSHom.base) : IsIso h := by
  have : ∀ i, LocallyRingedSpace.IsOpenImmersion ((g i).toSmoothLRSHom ≫ h.toSmoothLRSHom) := H
  have : IsIso (forgetToLocallyRingedSpace.map h) :=
    LocallyRingedSpace.isIso_of_cover (fun i => (g i).toSmoothLRSHom) h.toSmoothLRSHom hg hbij
  exact isIso_of_fully_faithful forgetToLocallyRingedSpace h

namespace GlueData

variable (D : GlueData.{u}) {X : Scheme.{u}} (f : ∀ i, D.U i ⟶ X)
  (hf : ∀ i j, D.t i j ≫ D.f j i ≫ f j = D.f i j ≫ f i)

/-- Descent of open immersions is an open immersion when it is injective on points. -/
theorem desc_isOpenImmersion [H : ∀ i, IsOpenImmersion (f i)]
    (hinj : Function.Injective (D.desc f hf).toSmoothLRSHom.base) :
    IsOpenImmersion (D.desc f hf) :=
  have : ∀ i, IsOpenImmersion (D.ι i ≫ D.desc f hf) := fun i => by
    rw [D.ι_desc f hf i]
    exact H i
  isOpenImmersion_of_cover D.ι (D.desc f hf) D.ι_jointly_surjective hinj

/-- Descent of open immersions is an isomorphism when it is bijective on points:
a scheme is the gluing of an open cover along its overlaps. -/
theorem desc_isIso [H : ∀ i, IsOpenImmersion (f i)]
    (hbij : Function.Bijective (D.desc f hf).toSmoothLRSHom.base) : IsIso (D.desc f hf) :=
  have : ∀ i, IsOpenImmersion (D.ι i ≫ D.desc f hf) := fun i => by
    rw [D.ι_desc f hf i]
    exact H i
  isIso_of_cover D.ι (D.desc f hf) D.ι_jointly_surjective hbij

end GlueData
end Scheme
end ProjectAinos.SmoothGeometry
