/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.IdealQuotient
public import ProjectAInos.SmoothAlgebra.Poisson.Hom
public import ProjectAInos.SmoothAlgebra.Poisson.Ideal
import Mathlib.Tactic.Abel

/-!
# Quotients and reductions of Poisson C-infinity rings

A Poisson structure descends along a surjective morphism when the bracket
respects its fibres (`PoissonStructure.ofSurjective`). With the quotient of a
C-infinity ring by an ideal this gives:

* the quotient `P/I` by a Poisson ideal is a Poisson C-infinity ring
  (`PoissonStructure.quotient`);
* the normalizer `N(I)` of an ideal is a Poisson C-infinity ring, the elements
  of `I` in it form a Poisson ideal, and the quotient is the reduced ring
  (`PoissonStructure.Reduction`, `PoissonStructure.reduction`). For a
  coisotropic ideal, `I ⊆ N(I)` and the reduced ring is `N(I)/I`.

A reduced ring is identified with a model `Q` by a Poisson morphism
`σ : Q → P` with values in `N(I)` and a retraction `r : P → Q` that vanishes
on `I`, such that `f − σ (r f) ∈ I` for every `f ∈ N(I)`
(`PoissonStructure.toReduction_bijective`,
`PoissonStructure.isPoissonHom_toReduction`).
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.SmoothAlgebra

open SmoothRing SmoothOperation

/-- A real subalgebra that is closed under the smooth operations is a
C-infinity ring. -/
@[reducible] def SmoothRing.ofSubalgebra {A : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]
    (S : Subalgebra ℝ A)
    (h : ∀ {n : ℕ} (f : SmoothOperation n) (c : Fin n → A), (∀ i, c i ∈ S) → op f c ∈ S) :
    SmoothRing S where
  op f a := ⟨op f fun i => (a i).val, h f _ fun i => (a i).property⟩
  op_proj i a := Subtype.ext (op_proj i fun k => (a k).val)
  op_comp f g a := Subtype.ext (op_comp f g fun k => (a k).val)
  op_nullary r a := Subtype.ext (op_nullary r fun k => (a k).val)
  op_addition a := Subtype.ext (op_addition fun k => (a k).val)
  op_multiplication a := Subtype.ext (op_multiplication fun k => (a k).val)

namespace PoissonStructure

variable {P Q : Type*} [CommRing P] [Algebra ℝ P] [SmoothRing P]
  [CommRing Q] [Algebra ℝ Q] [SmoothRing Q] (π : PoissonStructure P)

/-! ### Descent along a surjective morphism -/

/-- A Poisson structure descends along a surjective morphism when the bracket
respects its fibres. -/
def ofSurjective (φ : SmoothRingHom P Q) (hφ : Function.Surjective φ)
    (h : ∀ f f' g g', φ f = φ f' → φ g = φ g' → φ (π.bracket f g) = φ (π.bracket f' g')) :
    PoissonStructure Q where
  bracket a b := φ (π.bracket (Function.surjInv hφ a) (Function.surjInv hφ b))
  antisymm a b := by rw [π.antisymm, SmoothRingHom.map_neg]
  chain f c k := by
    have hc : (fun i => φ (Function.surjInv hφ (c i))) = c :=
      funext fun i => Function.surjInv_eq hφ (c i)
    have h1 : φ (π.bracket (Function.surjInv hφ (op f c)) (Function.surjInv hφ k)) =
        φ (π.bracket (op f fun i => Function.surjInv hφ (c i)) (Function.surjInv hφ k)) :=
      h _ _ _ _ ((Function.surjInv_eq hφ (op f c)).trans
        (by rw [SmoothRingHom.map_op, hc])) rfl
    rw [h1, π.chain, SmoothRingHom.map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SmoothRingHom.map_mul, SmoothRingHom.map_op, hc]
  jacobi a b c := by
    have key (x y z : Q) :
        φ (π.bracket (Function.surjInv hφ
            (φ (π.bracket (Function.surjInv hφ x) (Function.surjInv hφ y))))
          (Function.surjInv hφ z)) =
        φ (π.bracket (π.bracket (Function.surjInv hφ x) (Function.surjInv hφ y))
          (Function.surjInv hφ z)) :=
      h _ _ _ _ (Function.surjInv_eq hφ _) rfl
    rw [key, key, key, ← SmoothRingHom.map_add, ← SmoothRingHom.map_add, π.jacobi,
      SmoothRingHom.map_zero]

/-- The descended bracket of two images is the image of the bracket. -/
theorem ofSurjective_bracket (φ : SmoothRingHom P Q) (hφ : Function.Surjective φ)
    (h : ∀ f f' g g', φ f = φ f' → φ g = φ g' → φ (π.bracket f g) = φ (π.bracket f' g'))
    (f g : P) : (π.ofSurjective φ hφ h).bracket (φ f) (φ g) = φ (π.bracket f g) :=
  h _ _ _ _ (Function.surjInv_eq hφ _) (Function.surjInv_eq hφ _)

/-- The morphism is a Poisson morphism to the descended structure. -/
theorem isPoissonHom_ofSurjective (φ : SmoothRingHom P Q) (hφ : Function.Surjective φ)
    (h : ∀ f f' g g', φ f = φ f' → φ g = φ g' → φ (π.bracket f g) = φ (π.bracket f' g')) :
    IsPoissonHom π.toAlmostPoissonStructure (π.ofSurjective φ hφ h).toAlmostPoissonStructure φ :=
  fun f g => (π.ofSurjective_bracket φ hφ h f g).symm

/-! ### The quotient by a Poisson ideal -/

/-- The quotient of a Poisson C-infinity ring by a Poisson ideal is a Poisson
C-infinity ring. -/
def quotient (I : Ideal P) (hI : π.IsPoissonIdeal I) :
    PoissonStructure (SmoothRingCon.ofIdeal I).Quotient :=
  π.ofSurjective (SmoothRingCon.ofIdeal I).projection
    (SmoothRingCon.ofIdeal I).projection_surjective fun f f' g g' hf hg => by
      rw [SmoothRingCon.ofIdeal_projection_eq_iff] at hf hg ⊢
      have h : π.bracket f g - π.bracket f' g' =
          π.bracket (f - f') g - π.bracket (g - g') f' := by
        rw [π.toAlmostPoissonStructure.bracket_sub_left,
          π.toAlmostPoissonStructure.bracket_sub_left, π.antisymm g f', π.antisymm g' f']
        abel
      rw [h]
      exact sub_mem (hI _ hf g) (hI _ hg f')

/-- The bracket of two classes is the class of the bracket. -/
theorem quotient_bracket (I : Ideal P) (hI : π.IsPoissonIdeal I) (f g : P) :
    (π.quotient I hI).bracket ((SmoothRingCon.ofIdeal I).projection f)
        ((SmoothRingCon.ofIdeal I).projection g) =
      (SmoothRingCon.ofIdeal I).projection (π.bracket f g) :=
  π.ofSurjective_bracket _ _ _ f g

/-- The projection to the quotient by a Poisson ideal is a Poisson morphism. -/
theorem isPoissonHom_projection (I : Ideal P) (hI : π.IsPoissonIdeal I) :
    IsPoissonHom π.toAlmostPoissonStructure (π.quotient I hI).toAlmostPoissonStructure
      (SmoothRingCon.ofIdeal I).projection :=
  π.isPoissonHom_ofSurjective _ _ _

/-! ### The normalizer as a Poisson C-infinity ring -/

instance (I : Ideal P) : SmoothRing (π.normalizer I) :=
  SmoothRing.ofSubalgebra _ fun f _ hc => op_mem_normalizer f hc

/-- The inclusion of the normalizer. -/
def normalizerInclusion (I : Ideal P) : SmoothRingHom (π.normalizer I) P where
  toFun := Subtype.val
  map_op' _ _ := rfl

@[simp] theorem normalizerInclusion_apply (I : Ideal P) (f : π.normalizer I) :
    π.normalizerInclusion I f = f.val := rfl

/-- The bracket of `P` restricted to the normalizer of an ideal. -/
def restrictNormalizer (I : Ideal P) : PoissonStructure (π.normalizer I) where
  bracket f g := ⟨π.bracket f.val g.val, bracket_mem_normalizer f.property g.property⟩
  antisymm f g := Subtype.ext (π.antisymm f.val g.val)
  chain f c h := Subtype.ext <| by
    have hsum := (π.normalizerInclusion I).map_sum Finset.univ fun i =>
      op (partialDeriv i f) c *
        (⟨π.bracket (c i).val h.val, bracket_mem_normalizer (c i).property h.property⟩ :
          π.normalizer I)
    exact (π.chain f (fun i => (c i).val) h.val).trans hsum.symm
  jacobi f g h := Subtype.ext (π.jacobi f.val g.val h.val)

@[simp] theorem restrictNormalizer_bracket_val (I : Ideal P) (f g : π.normalizer I) :
    ((π.restrictNormalizer I).bracket f g).val = π.bracket f.val g.val := rfl

/-- The inclusion of the normalizer is a Poisson morphism. -/
theorem isPoissonHom_normalizerInclusion (I : Ideal P) :
    IsPoissonHom (π.restrictNormalizer I).toAlmostPoissonStructure π.toAlmostPoissonStructure
      (π.normalizerInclusion I) := fun _ _ => rfl

/-! ### Reduction -/

/-- The elements of the ideal in its normalizer, as an ideal of the
normalizer. For a coisotropic ideal these are all the elements of the ideal. -/
def normalizerIdeal (I : Ideal P) : Ideal (π.normalizer I) := I.comap (π.normalizer I).val

theorem mem_normalizerIdeal {I : Ideal P} {f : π.normalizer I} :
    f ∈ π.normalizerIdeal I ↔ f.val ∈ I := Iff.rfl

/-- In the normalizer the ideal is a Poisson ideal. -/
theorem isPoissonIdeal_normalizerIdeal (I : Ideal P) :
    (π.restrictNormalizer I).IsPoissonIdeal (π.normalizerIdeal I) :=
  fun _ hf g => bracket_mem_of_mem_normalizer (π := π) (I := I) hf g.property

/-- The reduced ring `N(I)/I` of an ideal. -/
abbrev Reduction (I : Ideal P) : Type _ := (SmoothRingCon.ofIdeal (π.normalizerIdeal I)).Quotient

/-- Coisotropic reduction: the reduced ring `N(I)/I` is a Poisson C-infinity
ring. -/
def reduction (I : Ideal P) : PoissonStructure (π.Reduction I) :=
  (π.restrictNormalizer I).quotient _ (π.isPoissonIdeal_normalizerIdeal I)

/-- The class in the reduced ring of an element of the normalizer. -/
def reductionMap (I : Ideal P) : SmoothRingHom (π.normalizer I) (π.Reduction I) :=
  (SmoothRingCon.ofIdeal (π.normalizerIdeal I)).projection

theorem reductionMap_surjective (I : Ideal P) : Function.Surjective (π.reductionMap I) :=
  (SmoothRingCon.ofIdeal (π.normalizerIdeal I)).projection_surjective

/-- Two elements of the normalizer have the same class when their difference
is in the ideal. -/
theorem reductionMap_eq_iff {I : Ideal P} {f g : π.normalizer I} :
    π.reductionMap I f = π.reductionMap I g ↔ f.val - g.val ∈ I :=
  SmoothRingCon.ofIdeal_projection_eq_iff

/-- The reduced bracket of two classes is the class of the bracket. -/
theorem reduction_bracket (I : Ideal P) (f g : π.normalizer I) :
    (π.reduction I).bracket (π.reductionMap I f) (π.reductionMap I g) =
      π.reductionMap I ((π.restrictNormalizer I).bracket f g) :=
  (π.restrictNormalizer I).quotient_bracket _ _ f g

/-- The projection of the normalizer to the reduced ring is a Poisson
morphism. -/
theorem isPoissonHom_reductionMap (I : Ideal P) :
    IsPoissonHom (π.restrictNormalizer I).toAlmostPoissonStructure
      (π.reduction I).toAlmostPoissonStructure (π.reductionMap I) :=
  (π.restrictNormalizer I).isPoissonHom_projection _ _

/-! ### A model of the reduced ring -/

variable {π} {I : Ideal P} {ρ : PoissonStructure Q}

/-- A morphism into `P` with values in the normalizer, as a morphism into the
normalizer. -/
def toNormalizer (σ : SmoothRingHom Q P) (hσ : ∀ g, σ g ∈ π.normalizer I) :
    SmoothRingHom Q (π.normalizer I) where
  toFun g := ⟨σ g, hσ g⟩
  map_op' f c := Subtype.ext (σ.map_op f c)

/-- The morphism to the reduced ring of a morphism with values in the
normalizer. -/
def toReduction (σ : SmoothRingHom Q P) (hσ : ∀ g, σ g ∈ π.normalizer I) :
    SmoothRingHom Q (π.Reduction I) :=
  (π.reductionMap I).comp (toNormalizer σ hσ)

theorem toReduction_apply (σ : SmoothRingHom Q P) (hσ : ∀ g, σ g ∈ π.normalizer I) (g : Q) :
    toReduction σ hσ g = π.reductionMap I ⟨σ g, hσ g⟩ := rfl

/-- A Poisson morphism with values in the normalizer gives a Poisson morphism
to the reduced ring. -/
theorem isPoissonHom_toReduction {σ : SmoothRingHom Q P} (hσ : ∀ g, σ g ∈ π.normalizer I)
    (hP : IsPoissonHom ρ.toAlmostPoissonStructure π.toAlmostPoissonStructure σ) :
    IsPoissonHom ρ.toAlmostPoissonStructure (π.reduction I).toAlmostPoissonStructure
      (toReduction σ hσ) := fun f g => by
  rw [toReduction_apply, toReduction_apply, toReduction_apply, reduction_bracket]
  exact congrArg (π.reductionMap I) (Subtype.ext (hP f g))

/-- The class of an element `f` of the normalizer is the image of `r f`, when
`f − σ (r f)` is in the ideal. -/
theorem toReduction_apply_eq {σ : SmoothRingHom Q P} (hσ : ∀ g, σ g ∈ π.normalizer I)
    (r : SmoothRingHom P Q) {f : P} (hf : f ∈ π.normalizer I) (h : f - σ (r f) ∈ I) :
    toReduction σ hσ (r f) = π.reductionMap I ⟨f, hf⟩ := by
  rw [toReduction_apply, reductionMap_eq_iff, ← neg_sub]
  exact neg_mem h

/-- The morphism to the reduced ring is injective when a retraction vanishes on
the ideal. -/
theorem toReduction_injective {σ : SmoothRingHom Q P} (hσ : ∀ g, σ g ∈ π.normalizer I)
    {r : SmoothRingHom P Q} (hrσ : ∀ g, r (σ g) = g) (hr : ∀ j ∈ I, r j = 0) :
    Function.Injective (toReduction σ hσ) := fun g g' h => by
  rw [toReduction_apply, toReduction_apply, reductionMap_eq_iff] at h
  have h0 := hr _ h
  rwa [SmoothRingHom.map_sub, hrσ, hrσ, sub_eq_zero] at h0

/-- The morphism to the reduced ring is surjective when every element of the
normalizer agrees modulo the ideal with an element of the model. -/
theorem toReduction_surjective {σ : SmoothRingHom Q P} (hσ : ∀ g, σ g ∈ π.normalizer I)
    {r : SmoothRingHom P Q} (h : ∀ f ∈ π.normalizer I, f - σ (r f) ∈ I) :
    Function.Surjective (toReduction σ hσ) := fun x => by
  obtain ⟨f, rfl⟩ := π.reductionMap_surjective I x
  exact ⟨r f.val, toReduction_apply_eq hσ r f.property (h _ f.property)⟩

/-- The reduced ring is the model `Q`: the morphism to the reduced ring is a
bijection. -/
theorem toReduction_bijective {σ : SmoothRingHom Q P} (hσ : ∀ g, σ g ∈ π.normalizer I)
    {r : SmoothRingHom P Q} (hrσ : ∀ g, r (σ g) = g) (hr : ∀ j ∈ I, r j = 0)
    (h : ∀ f ∈ π.normalizer I, f - σ (r f) ∈ I) : Function.Bijective (toReduction σ hσ) :=
  ⟨toReduction_injective hσ hrσ hr, toReduction_surjective hσ h⟩

end PoissonStructure

end ProjectAInos.SmoothAlgebra
