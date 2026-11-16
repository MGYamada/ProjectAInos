/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAInos.SmoothGeometry.GluingExampleIso
import ProjectAInos.SmoothGeometry.DifferentialForm.NativeCoordinates
import ProjectAInos.SmoothGeometry.DifferentialForm.NativeGluing
import ProjectAInos.SmoothGeometry.DifferentialForm.NativeExteriorExamples
import ProjectAInos.SmoothGeometry.DifferentialForm.NativeWedgeExamples
import ProjectAInos.SmoothGeometry.DifferentialForm.InteriorDerivative
import ProjectAInos.SmoothGeometry.DifferentialForm.TwoForm
import ProjectAInos.SmoothGeometry.Tensor.CovariantDerivative

/-! External API regressions: use the public definitions with default elaborator
options, without unfolding morphism wrappers or adding local instances. -/

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open ProjectAInos.SmoothGeometry

noncomputable section

universe u

section OpenImmersions

variable {X Y Z : Scheme.{u}}

example : Scheme.IsOpenImmersion (𝟙 X) := inferInstance

example (f : X ⟶ Y) [IsIso f] : Scheme.IsOpenImmersion f := inferInstance

example (f : X ⟶ Y) (g : Y ⟶ Z) [Scheme.IsOpenImmersion f] [Scheme.IsOpenImmersion g] :
    Scheme.IsOpenImmersion (f ≫ g) := inferInstance

example (U : Opens X.carrier) : Scheme.IsOpenImmersion (X.ofRestrict U.isOpenEmbedding) :=
  inferInstance

example (U : Opens X.carrier) (f : Y ⟶ X) :
    HasPullback (X.ofRestrict U.isOpenEmbedding) f := inferInstance

example (U : Opens X.carrier) (e : X ≅ Y) (f : Z ⟶ Y) :
    HasPullback (X.ofRestrict U.isOpenEmbedding ≫ e.hom) f := inferInstance

end OpenImmersions

section ConcreteGluing

open GluingExample

example : (overlapOpen : Set line).Nonempty := overlap_nonempty

example (i : Bool) : overlapOpen < pieceOpen i := overlap_proper i

example (i : datum.J) : Scheme.IsOpenImmersion (datum.ι i) := inferInstance

example (i : datum.J) : datum.ι i ≫ toLine = pieceInclusion i := inclusion_toLine i

example : Function.Surjective toLine.toSmoothLRSHom.base := toLine_surjective

example : IsLimit
    (PullbackCone.mk (overlapToPiece false) (overlapToPiece true)
      ((overlapToPiece_comp false).trans (overlapToPiece_comp true).symm)) :=
  overlapIsPullback

example : overlapToPiece false ≫ datum.ι false = overlapToPiece true ≫ datum.ι true :=
  overlapToPiece_ι

example (i : Bool) (w : overlap) :
    ((overlapToPiece i).toSmoothLRSHom.base w).val = w.val := overlapToPiece_val i w

example (i : datum.J) (y : datum.U i) :
    toLine.toSmoothLRSHom.base ((datum.ι i).toSmoothLRSHom.base y) = y.val :=
  toLine_ι_apply i y

example (i j : Bool) (y : piece i) (z : piece j) (h : y.val = z.val) :
    (datum.ι i).toSmoothLRSHom.base y = (datum.ι j).toSmoothLRSHom.base z :=
  ι_eq_of_val_eq i j y z h

example : Function.Injective toLine.toSmoothLRSHom.base := toLine_injective

example : Function.Bijective toLine.toSmoothLRSHom.base := toLine_bijective

example : Scheme.IsOpenImmersion toLine := inferInstance

example : IsIso toLine := inferInstance

example : datum.glued ≅ line := gluedIsoLine

example : gluedIsoLine.hom = toLine := gluedIsoLine_hom

example : gluedIsoLine.inv = fromLine := gluedIsoLine_inv

example : toLine ≫ fromLine = 𝟙 datum.glued := toLine_fromLine

example : fromLine ≫ toLine = 𝟙 line := fromLine_toLine

example (i : datum.J) : pieceInclusion i ≫ fromLine = datum.ι i := pieceInclusion_fromLine i

example (x : datum.glued) : IsIso (toLine.toSmoothLRSHom.toLRSHom.stalkMap x) :=
  toLine_stalkMap_isIso x

example {X : Scheme} {f g : line ⟶ X}
    (h : ∀ i : datum.J, pieceInclusion i ≫ f = pieceInclusion i ≫ g) : f = g :=
  line_hom_ext h

end ConcreteGluing

section CoordinateSection

open GluingExample ProjectAInos.SmoothAlgebra

example {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (s : Z.sections ⊤) :
    Scheme.Γ.map (f ≫ g).op s = Scheme.Γ.map f.op (Scheme.Γ.map g.op s) :=
  Scheme.Γ_map_comp_apply f g s

example {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (s : Y.sections ⊤) :
    Scheme.Γ.map f.op s = Scheme.Γ.map g.op s := Scheme.Γ_map_congr h s

example {U : Opens (Fin 1 → ℝ)} {s t : line.sections U}
    (h : ∀ (x : Fin 1 → ℝ) (hx : x ∈ U), sectionEval s x hx = sectionEval t x hx) : s = t :=
  sectionEval_ext h

example {U : Opens (Fin 1 → ℝ)} {n : ℕ} (g : SmoothOperation n)
    (a : Fin n → line.sections U) (x : Fin 1 → ℝ) (hx : x ∈ U) :
    sectionEval (SmoothRing.op g a) x hx = g fun k => sectionEval (a k) x hx :=
  sectionEval_op g a x hx

example (x : Fin 1 → ℝ) : sectionEval coordinate x trivial = x 0 := sectionEval_coordinate x

example :
    sectionEval coordinate (fun _ => 0) trivial ≠ sectionEval coordinate (fun _ => 1) trivial :=
  coordinate_nonconstant

example (i : Bool) (s : line.sections ⊤) (y : piece i) :
    pieceEval i (Scheme.Γ.map (pieceInclusion i).op s) y = sectionEval s y.val trivial :=
  pieceEval_restrict i s y

example (s : line.sections ⊤) (w : overlap) :
    overlapEval (Scheme.Γ.map overlapInclusion.op s) w = sectionEval s w.val trivial :=
  overlapEval_restrict s w

example {s t : line.sections ⊤}
    (h : ∀ i : Bool, Scheme.Γ.map (pieceInclusion i).op s =
      Scheme.Γ.map (pieceInclusion i).op t) : s = t :=
  line_section_ext h

example (i : Bool) (y : piece i) : pieceEval i (pieceCoordinate i) y = y.val 0 :=
  pieceEval_pieceCoordinate i y

example (i : Bool) :
    Scheme.Γ.map (overlapToPiece i).op (pieceCoordinate i) =
      Scheme.Γ.map overlapInclusion.op coordinate :=
  overlapToPiece_pieceCoordinate i

example :
    Scheme.Γ.map (overlapToPiece false).op (pieceCoordinate false) =
      Scheme.Γ.map (overlapToPiece true).op (pieceCoordinate true) :=
  pieceCoordinate_overlap

example (i : Bool) (w : overlap) :
    overlapEval (Scheme.Γ.map (overlapToPiece i).op (pieceCoordinate i)) w = w.val 0 :=
  overlapEval_pieceCoordinate i w

example (i : datum.J) : Scheme.Γ.map (datum.ι i).op gluedCoordinate = pieceCoordinate i :=
  ι_gluedCoordinate i

example : Scheme.Γ.map fromLine.op gluedCoordinate = coordinate := fromLine_gluedCoordinate

example {s t : datum.glued.sections ⊤}
    (h : ∀ i : datum.J, Scheme.Γ.map (datum.ι i).op s = Scheme.Γ.map (datum.ι i).op t) :
    s = t :=
  glued_section_ext h

example {s : datum.glued.sections ⊤}
    (h : ∀ i : datum.J, Scheme.Γ.map (datum.ι i).op s = pieceCoordinate i) :
    s = gluedCoordinate :=
  gluedCoordinate_unique h

example (g : SmoothOperation 1) (i : Bool) (y : piece i) :
    pieceEval i (Scheme.Γ.map (datum.ι i).op
      (SmoothRing.op g fun _ => gluedCoordinate)) y = g fun _ => y.val 0 :=
  pieceEval_op_gluedCoordinate g i y

end CoordinateSection

section OpenCovers

example {ι : Type*} {X Y : LocallyRingedSpace.{u}} {U : ι → LocallyRingedSpace.{u}}
    (g : ∀ i, U i ⟶ Y) (h : Y ⟶ X) [∀ i, LocallyRingedSpace.IsOpenImmersion (g i)]
    [∀ i, LocallyRingedSpace.IsOpenImmersion (g i ≫ h)]
    (hg : ∀ y : Y, ∃ (i : ι) (z : U i), (g i).base z = y) (y : Y) :
    IsIso (h.toLRSHom.stalkMap y) :=
  LocallyRingedSpace.stalkMap_isIso_of_cover g h hg y

example {ι : Type*} {X Y : LocallyRingedSpace.{u}} {U : ι → LocallyRingedSpace.{u}}
    (g : ∀ i, U i ⟶ Y) (h : Y ⟶ X) [∀ i, LocallyRingedSpace.IsOpenImmersion (g i)]
    [∀ i, LocallyRingedSpace.IsOpenImmersion (g i ≫ h)]
    (hg : ∀ y : Y, ∃ (i : ι) (z : U i), (g i).base z = y) : IsOpenMap h.base :=
  LocallyRingedSpace.isOpenMap_of_cover g h hg

example {ι : Type*} {X Y : LocallyRingedSpace.{u}} {U : ι → LocallyRingedSpace.{u}}
    (g : ∀ i, U i ⟶ Y) (h : Y ⟶ X) [∀ i, LocallyRingedSpace.IsOpenImmersion (g i)]
    [∀ i, LocallyRingedSpace.IsOpenImmersion (g i ≫ h)]
    (hg : ∀ y : Y, ∃ (i : ι) (z : U i), (g i).base z = y)
    (hinj : Function.Injective h.base) : LocallyRingedSpace.IsOpenImmersion h :=
  LocallyRingedSpace.isOpenImmersion_of_cover g h hg hinj

example {ι : Type*} {X Y : LocallyRingedSpace.{u}} {U : ι → LocallyRingedSpace.{u}}
    (g : ∀ i, U i ⟶ Y) (h : Y ⟶ X) [∀ i, LocallyRingedSpace.IsOpenImmersion (g i)]
    [∀ i, LocallyRingedSpace.IsOpenImmersion (g i ≫ h)]
    (hg : ∀ y : Y, ∃ (i : ι) (z : U i), (g i).base z = y)
    (hbij : Function.Bijective h.base) : IsIso h :=
  LocallyRingedSpace.isIso_of_cover g h hg hbij

example {ι : Type*} {X Y : Scheme.{u}} {U : ι → Scheme.{u}} (g : ∀ i, U i ⟶ Y) (h : Y ⟶ X)
    [∀ i, Scheme.IsOpenImmersion (g i)] [∀ i, Scheme.IsOpenImmersion (g i ≫ h)]
    (hg : ∀ y : Y, ∃ (i : ι) (z : U i), (g i).toSmoothLRSHom.base z = y)
    (hinj : Function.Injective h.toSmoothLRSHom.base) : Scheme.IsOpenImmersion h :=
  Scheme.isOpenImmersion_of_cover g h hg hinj

example {ι : Type*} {X Y : Scheme.{u}} {U : ι → Scheme.{u}} (g : ∀ i, U i ⟶ Y) (h : Y ⟶ X)
    [∀ i, Scheme.IsOpenImmersion (g i)] [∀ i, Scheme.IsOpenImmersion (g i ≫ h)]
    (hg : ∀ y : Y, ∃ (i : ι) (z : U i), (g i).toSmoothLRSHom.base z = y)
    (hbij : Function.Bijective h.toSmoothLRSHom.base) : IsIso h :=
  Scheme.isIso_of_cover g h hg hbij

example (D : Scheme.GlueData.{u}) {X : Scheme.{u}} (f : ∀ i, D.U i ⟶ X)
    (hf : ∀ i j, D.t i j ≫ D.f j i ≫ f j = D.f i j ≫ f i)
    [∀ i, Scheme.IsOpenImmersion (f i)]
    (hinj : Function.Injective (D.desc f hf).toSmoothLRSHom.base) :
    Scheme.IsOpenImmersion (D.desc f hf) :=
  D.desc_isOpenImmersion f hf hinj

example (D : Scheme.GlueData.{u}) {X : Scheme.{u}} (f : ∀ i, D.U i ⟶ X)
    (hf : ∀ i j, D.t i j ≫ D.f j i ≫ f j = D.f i j ≫ f i)
    [∀ i, Scheme.IsOpenImmersion (f i)]
    (hbij : Function.Bijective (D.desc f hf).toSmoothLRSHom.base) : IsIso (D.desc f hf) :=
  D.desc_isIso f hf hbij

end OpenCovers

section LocallyRingedGluing

variable (D : LocallyRingedSpace.GlueData.{u})

example : HasMulticoequalizer D.toGlueData.diagram := inferInstance

example : D.glued = D.toGlueData.glued := rfl

example (i : D.J) : D.ι i = Multicoequalizer.π D.toGlueData.diagram i := rfl

example (i : D.J) : LocallyRingedSpace.IsOpenImmersion (D.toGlueData.ι i) := inferInstance

example (i j : D.J) : PullbackCone (D.ι i) (D.ι j) := D.toGlueData.vPullbackCone i j

example (X : LocallyRingedSpace.{u}) (f : ∀ i, D.U i ⟶ X)
    (h : ∀ p, D.toGlueData.diagram.fst p ≫ f p.1 = D.toGlueData.diagram.snd p ≫ f p.2)
    (i : D.J) : D.ι i ≫ Multicoequalizer.desc D.toGlueData.diagram X f h = f i :=
  Multicoequalizer.π_desc D.toGlueData.diagram X f h i

end LocallyRingedGluing

section SchemeGluing

variable (D : Scheme.GlueData.{u})

example : HasMulticoequalizer D.toGlueData.diagram := inferInstance

example : D.glued = D.toGlueData.glued := rfl

example (i : D.J) : D.ι i = Multicoequalizer.π D.toGlueData.diagram i := rfl

example (i : D.J) : Scheme.IsOpenImmersion (D.toGlueData.ι i) := inferInstance

example (i j : D.J) : PullbackCone (D.ι i) (D.ι j) := D.toGlueData.vPullbackCone i j

example (X : Scheme.{u}) (f : ∀ i, D.U i ⟶ X)
    (h : ∀ p, D.toGlueData.diagram.fst p ≫ f p.1 = D.toGlueData.diagram.snd p ≫ f p.2)
    (i : D.J) : D.ι i ≫ Multicoequalizer.desc D.toGlueData.diagram X f h = f i :=
  Multicoequalizer.π_desc D.toGlueData.diagram X f h i

end SchemeGluing


section NativeDifferentialForms

open Bundle DifferentialForm
open scoped Manifold ContDiff

variable {E H M F H' N G H'' P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  (J : ModelWithCorners ℝ F H') [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H'']
  (K : ModelWithCorners ℝ G H'') [TopologicalSpace P] [ChartedSpace H'' P]
  [IsManifold K ∞ P]

example (k : ℕ) : ContMDiffVectorBundle ∞ (E [⋀^Fin k]→L[ℝ] ℝ)
    (fun x : M => TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) I := inferInstance

example {k : ℕ} (f : C^∞⟮I, M; J, N⟯) (α : SmoothForm J N k)
    (x : M) (v : Fin k → TangentSpace I x) :
    smoothPullback I J f α x v = α (f x) (fun i => mfderiv I J f x (v i)) :=
  smoothPullback_apply I J f α x v

example {k : ℕ} (α : SmoothForm I M k) :
    smoothPullback I I (ContMDiffMap.id : C^∞⟮I, M; I, M⟯) α = α := smoothPullback_id I α

example {k : ℕ} (f : C^∞⟮I, M; J, N⟯) (g : C^∞⟮J, N; K, P⟯)
    (α : SmoothForm K P k) :
    smoothPullback I K (g.comp f) α = smoothPullback I J f (smoothPullback J K g α) :=
  smoothPullback_comp I J K f g α

example (k : ℕ) (y : N) (α : SmoothForm J N (k + 1)) :
    smoothPullback I J (ContMDiffMap.const y : C^∞⟮I, M; J, N⟯) α = 0 :=
  smoothPullback_const I J k y α

example {k : ℕ} (e e' : Trivialization E (π E (fun x : M => TangentSpace I x)))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] (α : NativeForm I M k)
    {x : M} (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet) :
    coefficients I e' α x = (coefficients I e α x).compContinuousLinearMap
      (e'.coordChangeL ℝ e x).toContinuousLinearMap := coefficients_change I e e' α hx hx'

example {k : ℕ} (α : SmoothForm I M k)
    (e : Trivialization E (π E (fun x : M => TangentSpace I x)))
    [MemTrivializationAtlas e] {x : M} (hx : x ∈ e.baseSet) :
    ContMDiffAt I 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ) ∞
      (coefficients I e (fun y => α y)) x := α.contMDiffAt_coefficients I e hx

example {k : ℕ} {ι : Type*} (U : ι → Set M) (hopen : ∀ i, IsOpen (U i))
    (hU : ∀ x, ∃ i, x ∈ U i) (α : ι → NativeForm I M k)
    (hsmooth : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ) x (α i x)) (U i))
    (hα : ∀ i j x, x ∈ U i ∩ U j → α i x = α j x) {i : ι} {x : M} (hx : x ∈ U i) :
    smoothGlue I U hopen hU α hsmooth hα x = α i x :=
  smoothGlue_apply I U hopen hU α hsmooth hα hx

example {k : ℕ} (f : E → F) (α : Form F k) :
    nativePullback 𝓘(ℝ, E) 𝓘(ℝ, F) f α = pullback f α := nativePullback_flat f α

example (p v : LorentzianCharts.Plane) :
    smoothPullback 𝓘(ℝ, LorentzianCharts.Plane) 𝓘(ℝ, LorentzianCharts.Plane)
      LorentzianCharts.shearDiffeomorph.toContMDiffMap NativeExamples.spatial p ![v] =
        v 1 + 2 * p 0 * v 0 := NativeExamples.spatial_shear p v

end NativeDifferentialForms


section NativeExteriorCalculus

open Bundle DifferentialForm
open scoped Manifold ContDiff Topology

variable {E M F N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N] {k : ℕ}

example {f : M → N} {α : NativeForm 𝓘(ℝ, F) N k} {x : M}
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x)
    (hα : ContMDiffAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun y => TotalSpace.mk' (F [⋀^Fin k]→L[ℝ] ℝ) y (α y)) (f x)) :
    ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun y => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ) y
        (nativePullback 𝓘(ℝ, E) 𝓘(ℝ, F) f α y)) x :=
  contMDiffAt_nativePullback 𝓘(ℝ, E) 𝓘(ℝ, F) hf hα

example (α : SmoothForm 𝓘(ℝ, E) M k) :
    smoothExteriorDerivative (smoothExteriorDerivative α) = 0 := smoothExteriorDerivative_squared α

example (f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯) (α : SmoothForm 𝓘(ℝ, F) N k) :
    smoothExteriorDerivative (smoothPullback 𝓘(ℝ, E) 𝓘(ℝ, F) f α) =
      smoothPullback 𝓘(ℝ, E) 𝓘(ℝ, F) f (smoothExteriorDerivative α) :=
  smoothExteriorDerivative_pullback f α

example (α : SmoothForm 𝓘(ℝ, E) M k) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {x : M} (hx : x ∈ e.source) :
    nativeExteriorDerivative (fun y => α y) x =
      chartLift e (extDeriv (chartCoefficients e (fun y => α y))) x :=
  nativeExteriorDerivative_eq_chart α he hx

example (α : SmoothForm 𝓘(ℝ, E) M k) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {y : E} (hy : y ∈ e.target) :
    chartCoefficients e (fun x => smoothExteriorDerivative α x) y =
      extDeriv (chartCoefficients e (fun x => α x)) y :=
  chartCoefficients_smoothExteriorDerivative α he hy

example : SmoothForm 𝓘(ℝ, E) M k →ₗ[ℝ] SmoothForm 𝓘(ℝ, E) M (k + 1) :=
  smoothExteriorDerivativeLinear

example {α β : SmoothForm 𝓘(ℝ, E) M k} {x : M} (h : ∀ᶠ y in 𝓝 x, α y = β y) :
    smoothExteriorDerivative α x = smoothExteriorDerivative β x := smoothExteriorDerivative_local h

example (α : Form E k) (hα : ContDiff ℝ ∞ α) :
    (fun x => smoothExteriorDerivative (ofFlat α hα) x) = exteriorDerivative α :=
  smoothExteriorDerivative_flat α hα

example : smoothExteriorDerivative NativeExamples.potential = NativeExamples.area :=
  NativeExamples.potential_exteriorDerivative

example : smoothExteriorDerivative NativeExamples.area = 0 := NativeExamples.area_closed

end NativeExteriorCalculus

section NativeExteriorProduct

open DifferentialForm
open scoped Manifold ContDiff

variable {n m k l q : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M] [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]
  [TopologicalSpace N] [ChartedSpace (Fin m → ℝ) N] [IsManifold 𝓘(ℝ, Fin m → ℝ) ∞ N]

example (α : SmoothForm 𝓘(ℝ, Fin n → ℝ) M k) (β : SmoothForm 𝓘(ℝ, Fin n → ℝ) M l) :
    SmoothForm 𝓘(ℝ, Fin n → ℝ) M (k + l) := smoothWedge α β

example : SmoothForm 𝓘(ℝ, Fin n → ℝ) M k →ₗ[ℝ]
    SmoothForm 𝓘(ℝ, Fin n → ℝ) M l →ₗ[ℝ] SmoothForm 𝓘(ℝ, Fin n → ℝ) M (k + l) :=
  smoothWedgeLinear

example (α : NativeForm 𝓘(ℝ, Fin n → ℝ) M k) (β : NativeForm 𝓘(ℝ, Fin n → ℝ) M l)
    {e : OpenPartialHomeomorph M (Fin n → ℝ)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin n → ℝ) ∞ M) {x : M} (hx : x ∈ e.source) :
    nativeWedge α β x = chartLift e (wedge (chartCoefficients e α) (chartCoefficients e β)) x :=
  nativeWedge_eq_chart α β he hx

example (α : SmoothForm 𝓘(ℝ, Fin n → ℝ) M k) (β : SmoothForm 𝓘(ℝ, Fin n → ℝ) M l)
    {e : OpenPartialHomeomorph M (Fin n → ℝ)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin n → ℝ) ∞ M) {y : Fin n → ℝ} (hy : y ∈ e.target) :
    chartCoefficients e (fun x => smoothWedge α β x) y =
      wedge (chartCoefficients e (fun x => α x)) (chartCoefficients e (fun x => β x)) y :=
  chartCoefficients_smoothWedge α β he hy

example (f : C^∞⟮𝓘(ℝ, Fin n → ℝ), M; 𝓘(ℝ, Fin m → ℝ), N⟯)
    (α : SmoothForm 𝓘(ℝ, Fin m → ℝ) N k) (β : SmoothForm 𝓘(ℝ, Fin m → ℝ) N l) :
    smoothPullback 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin m → ℝ) f (smoothWedge α β) =
      smoothWedge (smoothPullback 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin m → ℝ) f α)
        (smoothPullback 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin m → ℝ) f β) := smoothPullback_wedge f α β

example (α : SmoothForm 𝓘(ℝ, Fin n → ℝ) M k) (β : SmoothForm 𝓘(ℝ, Fin n → ℝ) M l)
    (γ : SmoothForm 𝓘(ℝ, Fin n → ℝ) M q) :
    smoothDegreeCast (Nat.add_assoc k l q) (smoothWedge (smoothWedge α β) γ) =
      smoothWedge α (smoothWedge β γ) := smoothWedge_assoc α β γ

example (α : SmoothForm 𝓘(ℝ, Fin n → ℝ) M k) (β : SmoothForm 𝓘(ℝ, Fin n → ℝ) M l) :
    smoothWedge α β = (-1 : ℝ) ^ (k * l) •
      smoothDegreeCast (Nat.add_comm l k) (smoothWedge β α) := smoothWedge_comm α β

example (α : SmoothForm 𝓘(ℝ, Fin n → ℝ) M k) :
    smoothDegreeCast (Nat.zero_add k) (smoothWedge smoothOne α) = α := smoothWedge_one_left α

example (α : SmoothForm 𝓘(ℝ, Fin n → ℝ) M k) :
    smoothWedge α smoothOne = α := smoothWedge_one_right α

example : smoothExteriorDerivative (smoothOne : SmoothForm 𝓘(ℝ, Fin n → ℝ) M 0) = 0 :=
  smoothExteriorDerivative_one

example (α : SmoothForm 𝓘(ℝ, Fin n → ℝ) M k) (β : SmoothForm 𝓘(ℝ, Fin n → ℝ) M l) :
    smoothExteriorDerivative (smoothWedge α β) =
      smoothDegreeCast (by omega : (k + 1) + l = (k + l) + 1)
        (smoothWedge (smoothExteriorDerivative α) β) +
      (-1 : ℝ) ^ k • smoothDegreeCast (Nat.add_assoc k l 1).symm
        (smoothWedge α (smoothExteriorDerivative β)) := smoothExteriorDerivative_wedge α β

example (α : Form (Fin n → ℝ) k) (β : Form (Fin n → ℝ) l)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β) :
    (fun x => smoothWedge (ofFlat α hα) (ofFlat β hβ) x) = wedge α β := smoothWedge_flat α β hα hβ

example (f : (Fin m → ℝ) → (Fin n → ℝ))
    (α : Form (Fin n → ℝ) k) (β : Form (Fin n → ℝ) l) :
    pullback f (wedge α β) = wedge (pullback f α) (pullback f β) := pullback_wedge f α β

example : smoothWedge NativeExamples.temporal NativeExamples.spatial = NativeExamples.area :=
  NativeExamples.temporal_wedge_spatial

example : smoothExteriorDerivative (smoothWedge NativeExamples.axisZero NativeExamples.secondPotential) =
    -NativeExamples.standardVolume := NativeExamples.negative_leibniz_example

end NativeExteriorProduct

section NativeInterior

open DifferentialForm
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] {k : ℕ}

example (v : V) (α : V [⋀^Fin (k + 1)]→L[ℝ] ℝ) (w : Fin k → V) :
    DifferentialForm.interior v α w = α (Matrix.vecCons v w) := interior_apply v α w

example (L : V →L[ℝ] W) (v : V) (α : W [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    DifferentialForm.interior v (α.compContinuousLinearMap L) =
      (DifferentialForm.interior (L v) α).compContinuousLinearMap L := interior_comp L v α

example {V : (Fin 4 → ℝ) → (Fin 4 → ℝ)} {x : Fin 4 → ℝ} (hV : DifferentiableAt ℝ V x) :
    extDeriv (fun y => DifferentialForm.interior (V y) (coordinateForm id)) x =
      (∑ i : Fin 4, fderiv ℝ V x (Pi.single i 1) i) • coordinateForm id :=
  extDeriv_interior_volume_four hV

end NativeInterior

section NativeBilinearDerivative

open scoped Manifold ContDiff
variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (connection : CovariantDerivative I E (TangentSpace I (M := M)))
  (B : Tensor.SmoothBilinear (I := I) (M := M))

example {X Y : ∀ x : M, TangentSpace I x} {x : M}
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% X) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Y) x) (u : TangentSpace I x) :
    Tensor.bilinearCovariantDerivative connection B x (X x) (Y x) u =
      mvfderiv I (fun y => B y (X y) (Y y)) x u -
        B x (connection X x u) (Y x) - B x (X x) (connection Y x u) :=
  Tensor.bilinearCovariantDerivative_apply connection B hX hY u

example (F : DifferentialForm.SmoothForm I M 2) (x : M) (v w : TangentSpace I x) :
    DifferentialForm.smoothTwoFormBilinear F x v w = F x ![v, w] :=
  DifferentialForm.smoothTwoFormBilinear_apply F x v w

end NativeBilinearDerivative
