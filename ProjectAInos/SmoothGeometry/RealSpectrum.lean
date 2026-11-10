/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Category
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Category.TopCat.Basic

/-! # Joyce's real spectrum and its basic open sets -/

@[expose] public section

noncomputable section

namespace ProjectAInos.SmoothGeometry

open SmoothAlgebra TopologicalSpace CategoryTheory

/-- The points of Joyce's spectrum are smooth-ring morphisms to ℝ. -/
def RealSpectrum (A : Type*) [CommRing A] [Algebra ℝ A] [SmoothRing A] := SmoothRingHom A ℝ

namespace RealSpectrum

variable {A B C : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]
  [CommRing B] [Algebra ℝ B] [SmoothRing B]
  [CommRing C] [Algebra ℝ C] [SmoothRing C]

instance : CoeFun (RealSpectrum A) (fun _ => A → ℝ) := ⟨fun x => SmoothRingHom.toFun x⟩

/-- The underlying smooth morphism. -/
abbrev hom (x : RealSpectrum A) : SmoothRingHom A ℝ := x

/-- The nonvanishing locus of a smooth-ring element. -/
def basicOpenSet (a : A) : Set (RealSpectrum A) := {x | x a ≠ 0}

instance : TopologicalSpace (RealSpectrum A) :=
  TopologicalSpace.generateFrom (Set.range (basicOpenSet (A := A)))

/-- A basic open subset of the real spectrum. -/
def basicOpen (a : A) : Opens (RealSpectrum A) :=
  ⟨basicOpenSet a, TopologicalSpace.isOpen_generateFrom_of_mem ⟨a, rfl⟩⟩

@[simp] theorem mem_basicOpen (x : RealSpectrum A) (a : A) : x ∈ basicOpen a ↔ x a ≠ 0 := Iff.rfl

@[simp] theorem basicOpen_one : basicOpen (1 : A) = ⊤ := by
  ext x
  change x.hom 1 ≠ 0 ↔ True
  simp

@[simp] theorem basicOpen_zero : basicOpen (0 : A) = ⊥ := by
  ext x
  change x.hom 0 ≠ 0 ↔ False
  simp

@[simp] theorem basicOpen_mul (a b : A) : basicOpen (a * b) = basicOpen a ⊓ basicOpen b := by
  ext x
  change x.hom (a * b) ≠ 0 ↔ x.hom a ≠ 0 ∧ x.hom b ≠ 0
  rw [x.hom.map_mul, mul_ne_zero_iff]

theorem isTopologicalBasis_basicOpen :
    IsTopologicalBasis (Set.range (fun a : A => (basicOpen a : Set (RealSpectrum A)))) := by
  have hb := isTopologicalBasis_of_subbasis_of_inter
    (r := Set.range (basicOpenSet (A := A))) rfl (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact ⟨a * b, congrArg SetLike.coe (basicOpen_mul a b)⟩)
  have htop : Set.univ ∈ Set.range (basicOpenSet (A := A)) :=
    ⟨1, congrArg SetLike.coe basicOpen_one⟩
  change IsTopologicalBasis (Set.range (basicOpenSet (A := A)))
  simpa only [Set.insert_eq_of_mem htop] using hb

/-- Precomposition, reversing the direction of a smooth-ring morphism. -/
def comap (f : SmoothRingHom A B) (x : RealSpectrum B) : RealSpectrum A := x.hom.comp f

@[simp] theorem comap_apply (f : SmoothRingHom A B) (x : RealSpectrum B) (a : A) :
    comap f x a = x (f a) := rfl

theorem continuous_comap (f : SmoothRingHom A B) : Continuous (comap f) := by
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨a, rfl⟩
  exact (basicOpen (f a)).isOpen

@[simp] theorem comap_id : comap (SmoothRingHom.id A) = id := rfl

@[simp] theorem comap_comp (f : SmoothRingHom A B) (g : SmoothRingHom B C) :
    comap (g.comp f) = comap f ∘ comap g := rfl

end RealSpectrum
end ProjectAInos.SmoothGeometry
