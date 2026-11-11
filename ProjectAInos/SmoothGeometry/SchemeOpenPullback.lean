/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Restrict
public import ProjectAInos.SmoothGeometry.SmoothSheaf

/-! # Open immersions and their pullbacks in C∞ schemes -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace ProjectAInos.SmoothGeometry.Scheme

open CategoryTheory CategoryTheory.Limits

variable {X Y Z : Scheme}

/-- A scheme open immersion is an open immersion of smooth locally ringed spaces. -/
abbrev IsOpenImmersion (f : X ⟶ Y) := LocallyRingedSpace.IsOpenImmersion f.toSmoothLRSHom

instance IsOpenImmersion.of_isIso (f : X ⟶ Y) [IsIso f] : IsOpenImmersion f :=
  inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (forgetToLocallyRingedSpace.map f))

instance IsOpenImmersion.comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] : IsOpenImmersion (f ≫ g) :=
  LocallyRingedSpace.IsOpenImmersion.comp f.toSmoothLRSHom g.toSmoothLRSHom

instance ofRestrict_isOpenImmersion (X : Scheme) {U : TopCat}
    {f : U ⟶ X.carrier} (h : Topology.IsOpenEmbedding f) : IsOpenImmersion (X.ofRestrict h) :=
  LocallyRingedSpace.ofRestrict_isOpenImmersion X.toSmoothLocallyRingedSpace h

instance openImmersion_mono (f : X ⟶ Y) [H : IsOpenImmersion f] : Mono f := by
  let : LocallyRingedSpace.IsOpenImmersion (forgetToLocallyRingedSpace.map f) := H
  exact forgetToLocallyRingedSpace.mono_of_mono_map
    (show Mono (forgetToLocallyRingedSpace.map f) from inferInstance)

namespace IsOpenImmersion

variable (f : X ⟶ Z) [H : IsOpenImmersion f] (g : Y ⟶ Z)

/-- Construct the pullback scheme as an open restriction of `Y`. -/
def pullbackCone : PullbackCone f g :=
  let c := LocallyRingedSpace.IsOpenImmersion.pullbackCone f.toSmoothLRSHom g.toSmoothLRSHom
  PullbackCone.mk
    (W := Y.restrict (LocallyRingedSpace.IsOpenImmersion.pullbackOpen
      f.toSmoothLRSHom g.toSmoothLRSHom).isOpenEmbedding)
    ⟨c.fst⟩ ⟨c.snd⟩ (Hom.ext c.condition)

/-- The constructed open subscheme is the categorical pullback. -/
def pullbackConeIsLimit : IsLimit (pullbackCone f g) :=
  isLimitOfReflects forgetToLocallyRingedSpace <| by
    apply (PullbackCone.isLimitMapConeEquiv _ forgetToLocallyRingedSpace).symm.toFun
    exact LocallyRingedSpace.IsOpenImmersion.pullbackConeIsLimit f.toSmoothLRSHom g.toSmoothLRSHom

instance hasPullback_of_left : HasPullback f g := ⟨⟨⟨_, pullbackConeIsLimit f g⟩⟩⟩

instance forget_preservesPullback : PreservesLimit (cospan f g) forgetToLocallyRingedSpace :=
  preservesLimit_of_preserves_limit_cone (pullbackConeIsLimit f g) <| by
    apply (PullbackCone.isLimitMapConeEquiv _ forgetToLocallyRingedSpace).symm.toFun
    exact LocallyRingedSpace.IsOpenImmersion.pullbackConeIsLimit f.toSmoothLRSHom g.toSmoothLRSHom

end IsOpenImmersion
end ProjectAInos.SmoothGeometry.Scheme
