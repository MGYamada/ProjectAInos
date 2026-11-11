/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.SmoothPresheaf

/-! # Pullbacks along smooth open immersions -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace ProjectAInos.SmoothGeometry

open SmoothAlgebra CategoryTheory CategoryTheory.Limits TopologicalSpace

/-- A square of open subspaces is a pullback when its second projection has
the expected inverse-image range. This is independent of the presheaf values. -/
def presheafOpenPullbackIsLimit {C : Type*} [Category* C]
    {X Y Z : AlgebraicGeometry.PresheafedSpace C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (c : PullbackCone f g) [AlgebraicGeometry.PresheafedSpace.IsOpenImmersion f]
    [AlgebraicGeometry.PresheafedSpace.IsOpenImmersion c.snd]
    (hr : Set.range c.snd.base = g.base ⁻¹' Set.range f.base) : IsLimit c :=
  PullbackCone.isLimitAux' c fun s => by
    have hs : Set.range s.snd.base ⊆ Set.range c.snd.base := by
      rw [hr]
      rintro _ ⟨x, rfl⟩
      exact ⟨s.fst.base x, congrArg (fun q => q.base x) s.condition⟩
    let k := AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift c.snd s.snd hs
    have hk := AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift_fac c.snd s.snd hs
    refine ⟨k, ?_, hk, ?_⟩
    · apply (cancel_mono f).mp
      rw [Category.assoc, c.condition, ← Category.assoc, hk, s.condition]
    · intro m _ hm
      exact (cancel_mono c.snd).mp (hm.trans hk.symm)

namespace LocallyRingedSpace.IsOpenImmersion

variable {X Y Z : LocallyRingedSpace} (f : X ⟶ Z) [H : IsOpenImmersion f] (g : Y ⟶ Z)

/-- The open inverse image of the image of `f`. -/
def pullbackOpen : Opens Y.carrier :=
  ⟨g.base ⁻¹' Set.range f.base, H.base_open.isOpen_range.preimage g.base.hom.continuous⟩

/-- The pullback along an open immersion is a restriction of the other space. -/
def pullbackCone : PullbackCone f g :=
  let i := Y.ofRestrict (pullbackOpen f g).isOpenEmbedding
  let h : Set.range (i ≫ g).base ⊆ Set.range f.base := by
    rintro _ ⟨x, rfl⟩
    exact x.property
  PullbackCone.mk (lift f (i ≫ g) h) i (lift_fac f (i ≫ g) h)

instance pullbackCone_snd_open : IsOpenImmersion (pullbackCone f g).snd :=
  inferInstanceAs (IsOpenImmersion (Y.ofRestrict (pullbackOpen f g).isOpenEmbedding))

theorem pullbackCone_range : Set.range (pullbackCone f g).snd.base =
    g.base ⁻¹' Set.range f.base := Subtype.range_coe_subtype

/-- The smooth locally ringed space pullback has the universal property. -/
def pullbackConeIsLimit : IsLimit (pullbackCone f g) :=
  PullbackCone.isLimitAux' _ fun s => by
    have hs : Set.range s.snd.base ⊆ Set.range (pullbackCone f g).snd.base := by
      rw [pullbackCone_range]
      rintro _ ⟨x, rfl⟩
      exact ⟨s.fst.base x, congrArg (fun q => q.base x) s.condition⟩
    let k := lift (pullbackCone f g).snd s.snd hs
    have hk := lift_fac (pullbackCone f g).snd s.snd hs
    refine ⟨k, ?_, hk, ?_⟩
    · apply (cancel_mono f).mp
      rw [Category.assoc, (pullbackCone f g).condition, ← Category.assoc, hk, s.condition]
    · intro m _ hm
      exact (cancel_mono (pullbackCone f g).snd).mp (hm.trans hk.symm)

instance hasPullback_of_left : HasPullback f g := ⟨⟨⟨_, pullbackConeIsLimit f g⟩⟩⟩

instance smoothPresheaf_preservesPullback :
    PreservesLimit (cospan f g) forgetToSmoothPresheafedSpace :=
  preservesLimit_of_preserves_limit_cone (pullbackConeIsLimit f g) <| by
    apply (PullbackCone.isLimitMapConeEquiv _ forgetToSmoothPresheafedSpace).symm.toFun
    let : AlgebraicGeometry.PresheafedSpace.IsOpenImmersion
        ((pullbackCone f g).map forgetToSmoothPresheafedSpace).snd :=
      smoothPresheafMap_isOpenImmersion (pullbackCone f g).snd
    apply presheafOpenPullbackIsLimit
    exact pullbackCone_range f g

end LocallyRingedSpace.IsOpenImmersion
end ProjectAInos.SmoothGeometry
