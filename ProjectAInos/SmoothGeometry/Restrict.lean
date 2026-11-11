/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Scheme
public import ProjectAInos.SmoothGeometry.SmoothPresheaf
public import ProjectAInos.SmoothGeometry.Localization

/-! # Open C∞ subschemes -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace ProjectAInos.SmoothGeometry

open SmoothAlgebra CategoryTheory TopologicalSpace Opposite Topology

namespace LocallyRingedSpace.IsOpenImmersion

/-- An actual affine open cover supplies the local-affine property. -/
def scheme (X : LocallyRingedSpace.{u})
    (h : ∀ x : X, ∃ (A : SmoothRingCat.{u}) (f : Spec.locallyRingedSpaceObj A ⟶ X),
      x ∈ Set.range f.base ∧ IsOpenImmersion f) : Scheme where
  toSmoothLocallyRingedSpace := X
  local_affine x := by
    obtain ⟨A, f, hx, hf⟩ := h x
    let U : Opens X.carrier := ⟨Set.range f.base, hf.base_open.isOpen_range⟩
    let : IsOpenImmersion f := hf
    exact ⟨⟨U, hx⟩, A, ⟨isoOfRangeEq (X.ofRestrict U.isOpenEmbedding) f
      (Subtype.range_coe_subtype)⟩⟩

end LocallyRingedSpace.IsOpenImmersion

namespace Scheme

/-- Every point of a C∞ scheme is in the image of an affine open immersion. -/
theorem exists_affine_open (X : Scheme.{u}) (x : X) :
    ∃ (A : SmoothRingCat.{u}) (f : Spec.locallyRingedSpaceObj A ⟶ X.toSmoothLocallyRingedSpace),
      x ∈ Set.range f.base ∧ LocallyRingedSpace.IsOpenImmersion f := by
  obtain ⟨U, A, ⟨e⟩⟩ := X.local_affine x
  refine ⟨A, e.inv ≫ X.toSmoothLocallyRingedSpace.ofRestrict U.isOpenEmbedding, ?_, inferInstance⟩
  let y : U.val := ⟨x, U.property⟩
  refine ⟨e.hom.base y, ?_⟩
  have he := congrArg (fun f : X.toSmoothLocallyRingedSpace.restrict U.isOpenEmbedding ⟶
    X.toSmoothLocallyRingedSpace.restrict U.isOpenEmbedding => f.base y) e.hom_inv_id
  exact congrArg Subtype.val he

/-- An open subspace of a C∞ scheme is a C∞ scheme. Principal localizations
provide the smaller affine neighbourhoods required by the definition. -/
def ofOpenImmersion {X : LocallyRingedSpace.{u}} (Y : Scheme.{u})
    (f : X ⟶ Y.toSmoothLocallyRingedSpace) [H : LocallyRingedSpace.IsOpenImmersion f] :
    Scheme.{u} := LocallyRingedSpace.IsOpenImmersion.scheme X fun x => by
  obtain ⟨A, g, ⟨y, hy⟩, hg⟩ := Y.exists_affine_open (f.base x)
  let : LocallyRingedSpace.IsOpenImmersion g := hg
  have hy' : y ∈ g.base ⁻¹' Set.range f.base := by rw [Set.mem_preimage, hy]; exact ⟨x, rfl⟩
  have ho : IsOpen (g.base ⁻¹' Set.range f.base) :=
    H.base_open.isOpen_range.preimage g.base.hom.continuous
  obtain ⟨_, ⟨a, rfl⟩, hya, ha⟩ :=
    RealSpectrum.isTopologicalBasis_basicOpen.exists_subset_of_mem_open hy' ho
  let B := SmoothRingCat.of (SmoothLocalization ({a} : Set A))
  let l : Spec.locallyRingedSpaceObj B ⟶ Spec.locallyRingedSpaceObj A :=
    Spec.locallyRingedSpaceMap (SmoothLocalization.of ({a} : Set A))
  let : LocallyRingedSpace.IsOpenImmersion l := Localization.away_isOpenImmersion a
  have hr : Set.range (l ≫ g).base ⊆ Set.range f.base := by
    rintro _ ⟨z, rfl⟩
    exact ha ((Localization.awayHomeomorph a z).property)
  let k := LocallyRingedSpace.IsOpenImmersion.lift f (l ≫ g) hr
  refine ⟨B, k, ?_, inferInstance⟩
  have hyRange : y ∈ Set.range (RealSpectrum.comap (SmoothLocalization.of ({a} : Set A))) := by
    rw [Localization.away_range]
    exact hya
  obtain ⟨z, hz⟩ := hyRange
  refine ⟨z, H.base_open.injective ?_⟩
  have hk := congrArg (fun q : Spec.locallyRingedSpaceObj B ⟶ Y.toSmoothLocallyRingedSpace =>
    q.base z) (LocallyRingedSpace.IsOpenImmersion.lift_fac f (l ≫ g) hr)
  exact hk.trans ((congrArg g.base hz).trans hy)

/-- Restriction of a scheme along an arbitrary topological open embedding. -/
def restrict (X : Scheme.{u}) {U : TopCat.{u}} {f : U ⟶ X.carrier}
    (h : IsOpenEmbedding f) : Scheme.{u} :=
  ofOpenImmersion X (X.toSmoothLocallyRingedSpace.ofRestrict h)

/-- The inclusion of an open C∞ subscheme. -/
def ofRestrict (X : Scheme.{u}) {U : TopCat.{u}} {f : U ⟶ X.carrier}
    (h : IsOpenEmbedding f) : X.restrict h ⟶ X :=
  ⟨X.toSmoothLocallyRingedSpace.ofRestrict h⟩

/-- The scheme condition is local for open covers by already constructed schemes. -/
def ofOpenCover (X : LocallyRingedSpace.{u})
    (h : ∀ x : X, ∃ (Y : Scheme.{u}) (f : Y.toSmoothLocallyRingedSpace ⟶ X),
      x ∈ Set.range f.base ∧ LocallyRingedSpace.IsOpenImmersion f) : Scheme.{u} :=
  LocallyRingedSpace.IsOpenImmersion.scheme X fun x => by
    obtain ⟨Y, f, ⟨y, rfl⟩, hf⟩ := h x
    let : LocallyRingedSpace.IsOpenImmersion f := hf
    obtain ⟨A, g, ⟨z, hz⟩, hg⟩ := Y.exists_affine_open y
    let : LocallyRingedSpace.IsOpenImmersion g := hg
    exact ⟨A, g ≫ f, ⟨z, congrArg f.base hz⟩, inferInstance⟩

end Scheme
end ProjectAInos.SmoothGeometry
