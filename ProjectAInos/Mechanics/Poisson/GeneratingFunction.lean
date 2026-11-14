/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.FreeChainRule
public import ProjectAInos.SmoothAlgebra.Poisson.Canonical
public import ProjectAInos.SmoothAlgebra.Poisson.Hom
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Canonical transformations from a generating function

Landau–Lifshitz §45. A generating function `F(q, Q)` of the old and the new
positions defines the transformation `p = ∂F/∂q`, `P = −∂F/∂Q`. In the
language of rings, `F` is an element of the free C-infinity ring on `q` and
`Q`, and there are two morphisms from a phase space to this ring:

* `oldMap F`: `qᵢ ↦ qᵢ`, `pᵢ ↦ ∂F/∂qᵢ`;
* `newMap F`: `Qᵢ ↦ Qᵢ`, `Pᵢ ↦ −∂F/∂Qᵢ`.

The generating function is free when `oldMap F` has an inverse morphism `G`,
that is, when `(q, p)` and `(q, Q)` are co-ordinates of the same space. The
transformation is then `transformation F G = G ∘ newMap F`, which expresses a
function of the new variables `(Q, P)` in the old variables `(q, p)`.

* `IsFree.inverseMixed_mul_mixedHessian`: the matrix `∂²F/∂qₖ∂Qₗ` is
  invertible.
* `IsFree.oldMap_bracket`: the canonical bracket in the co-ordinates `(q, Q)`.
* `IsFree.isPoissonHom_transformation`: the transformation is canonical.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.GeneratingFunction

open SmoothAlgebra SmoothRing FreeSmoothRing Matrix

/-- The ring of functions of the old positions `q` and the new positions
`Q`. -/
abbrev PositionPair (ι : Type*) := FreeSmoothRing (ι ⊕ ι)

variable {ι : Type*}

/-- The old position `qᵢ`. -/
def oldPosition (i : ι) : PositionPair ι := generator (Sum.inl i)

/-- The new position `Qᵢ`. -/
def newPosition (i : ι) : PositionPair ι := generator (Sum.inr i)

variable [DecidableEq ι]

/-- The gradient with respect to the old positions. -/
def gradOld (x : PositionPair ι) : ι → PositionPair ι :=
  fun k => partialDerivation (Sum.inl k) x

/-- The gradient with respect to the new positions. -/
def gradNew (x : PositionPair ι) : ι → PositionPair ι :=
  fun l => partialDerivation (Sum.inr l) x

theorem gradOld_neg (x : PositionPair ι) : gradOld (-x) = -gradOld x :=
  funext fun _ => map_neg _ _

theorem gradNew_neg (x : PositionPair ι) : gradNew (-x) = -gradNew x :=
  funext fun _ => map_neg _ _

theorem gradOld_newPosition (i : ι) : gradOld (newPosition i) = 0 :=
  funext fun k => partialDerivation_generator_of_ne (by simp)

theorem gradNew_newPosition (i : ι) : gradNew (newPosition i) = Pi.single i 1 := by
  funext l
  rw [gradNew, newPosition, partialDerivation_generator, Pi.single_apply]
  simp only [Sum.inr.injEq, eq_comm]

/-- The second derivatives with respect to the new positions are symmetric. -/
theorem gradNew_gradNew_comm (F : PositionPair ι) (i j : ι) :
    gradNew (gradNew F j) i = gradNew (gradNew F i) j :=
  partialDerivation_comm _ _ _

/-- The morphism of the old phase space: `qᵢ ↦ qᵢ`, `pᵢ ↦ ∂F/∂qᵢ`. -/
def oldMap (F : PositionPair ι) : SmoothRingHom (PhaseSpace ι) (PositionPair ι) :=
  FreeSmoothRing.lift (Sum.elim oldPosition (gradOld F))

/-- The morphism of the new phase space: `Qᵢ ↦ Qᵢ`, `Pᵢ ↦ −∂F/∂Qᵢ`. -/
def newMap (F : PositionPair ι) : SmoothRingHom (PhaseSpace ι) (PositionPair ι) :=
  FreeSmoothRing.lift (Sum.elim newPosition fun i => -gradNew F i)

@[simp] theorem oldMap_q (F : PositionPair ι) (i : ι) :
    oldMap F (PhaseSpace.q i) = oldPosition i := by
  rw [oldMap, PhaseSpace.q, lift_generator, Sum.elim_inl]

@[simp] theorem oldMap_p (F : PositionPair ι) (i : ι) :
    oldMap F (PhaseSpace.p i) = gradOld F i := by
  rw [oldMap, PhaseSpace.p, lift_generator, Sum.elim_inr]

@[simp] theorem newMap_q (F : PositionPair ι) (i : ι) :
    newMap F (PhaseSpace.q i) = newPosition i := by
  rw [newMap, PhaseSpace.q, lift_generator, Sum.elim_inl]

@[simp] theorem newMap_p (F : PositionPair ι) (i : ι) :
    newMap F (PhaseSpace.p i) = -gradNew F i := by
  rw [newMap, PhaseSpace.p, lift_generator, Sum.elim_inr]

variable [Fintype ι]

/-- The mixed matrix `∂²F/∂qₖ∂Qₗ`. -/
def mixedHessian (F : PositionPair ι) : Matrix ι ι (PositionPair ι) :=
  Matrix.of fun k l => gradNew (gradOld F k) l

/-- The matrix `∂²F/∂qₖ∂qₗ`. -/
def oldHessian (F : PositionPair ι) : Matrix ι ι (PositionPair ι) :=
  Matrix.of fun k l => gradOld (gradOld F k) l

omit [Fintype ι] in
theorem oldHessian_transpose (F : PositionPair ι) : (oldHessian F)ᵀ = oldHessian F :=
  Matrix.ext fun _ _ => partialDerivation_comm _ _ _

omit [Fintype ι] in
/-- `∂(∂F/∂Qⱼ)/∂qₖ = ∂²F/∂qₖ∂Qⱼ`. -/
theorem gradOld_gradNew (F : PositionPair ι) (j k : ι) :
    gradOld (gradNew F j) k = mixedHessian F k j :=
  partialDerivation_comm _ _ _

/-- The chain rule for `oldMap`. -/
theorem apply_oldMap (F : PositionPair ι)
    (E : SmoothDerivation (PositionPair ι) (PositionPair ι)) (s : PhaseSpace ι) :
    E (oldMap F s) =
      ∑ i, oldMap F (partialDerivation (Sum.inl i) s) * E (oldPosition i) +
        ∑ i, oldMap F (partialDerivation (Sum.inr i) s) * E (gradOld F i) := by
  rw [oldMap, derivation_lift_mul, Fintype.sum_sum_type]
  rfl

theorem gradNew_oldMap (F : PositionPair ι) (s : PhaseSpace ι) :
    gradNew (oldMap F s) =
      (fun k => oldMap F (partialDerivation (Sum.inr k) s)) ᵥ* mixedHessian F := by
  funext l
  rw [gradNew, apply_oldMap, Finset.sum_eq_zero, zero_add]
  · rfl
  · intro i _
    rw [oldPosition, partialDerivation_generator_of_ne (by simp), mul_zero]

theorem gradOld_oldMap (F : PositionPair ι) (s : PhaseSpace ι) :
    gradOld (oldMap F s) =
      (fun k => oldMap F (partialDerivation (Sum.inl k) s)) +
        (fun k => oldMap F (partialDerivation (Sum.inr k) s)) ᵥ* oldHessian F := by
  funext l
  rw [gradOld, apply_oldMap, Finset.sum_eq_single l]
  · rw [oldPosition, partialDerivation_generator_self, mul_one]
    rfl
  · intro i _ hi
    rw [oldPosition, partialDerivation_generator_of_ne (fun h => hi (Sum.inl.inj h)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ l) h

/-- `F` is a free generating function, with the inverse `G` of `oldMap F`:
the pairs `(q, p)` and `(q, Q)` are co-ordinates of the same space. -/
structure IsFree (F : PositionPair ι) (G : SmoothRingHom (PositionPair ι) (PhaseSpace ι)) :
    Prop where
  left_inv : G.comp (oldMap F) = SmoothRingHom.id (PhaseSpace ι)
  right_inv : (oldMap F).comp G = SmoothRingHom.id (PositionPair ι)

/-- The transformation generated by `F`: a function of the new variables
`(Q, P)` is expressed in the old variables `(q, p)`. -/
def transformation (F : PositionPair ι) (G : SmoothRingHom (PositionPair ι) (PhaseSpace ι)) :
    SmoothRingHom (PhaseSpace ι) (PhaseSpace ι) :=
  G.comp (newMap F)

/-- The derivatives `∂(G x)/∂pₖ`, read in the co-ordinates `(q, Q)`. -/
def momentumPart (F : PositionPair ι) (G : SmoothRingHom (PositionPair ι) (PhaseSpace ι))
    (x : PositionPair ι) : ι → PositionPair ι :=
  fun k => oldMap F (partialDerivation (Sum.inr k) (G x))

/-- The derivatives `∂(G x)/∂qₖ`, read in the co-ordinates `(q, Q)`. -/
def positionPart (F : PositionPair ι) (G : SmoothRingHom (PositionPair ι) (PhaseSpace ι))
    (x : PositionPair ι) : ι → PositionPair ι :=
  fun k => oldMap F (partialDerivation (Sum.inl k) (G x))

/-- The matrix `∂Qⱼ/∂pₖ`, the inverse of the mixed matrix `∂²F/∂qₖ∂Qₗ`. -/
def inverseMixed (F : PositionPair ι) (G : SmoothRingHom (PositionPair ι) (PhaseSpace ι)) :
    Matrix ι ι (PositionPair ι) :=
  Matrix.of fun j k => momentumPart F G (newPosition j) k

namespace IsFree

variable {F : PositionPair ι} {G : SmoothRingHom (PositionPair ι) (PhaseSpace ι)}

omit [Fintype ι] in
theorem apply_oldMap (h : IsFree F G) (s : PhaseSpace ι) : G (oldMap F s) = s :=
  congrArg (fun φ : SmoothRingHom (PhaseSpace ι) (PhaseSpace ι) => φ s) h.left_inv

omit [Fintype ι] in
theorem oldMap_apply (h : IsFree F G) (x : PositionPair ι) : oldMap F (G x) = x :=
  congrArg (fun φ : SmoothRingHom (PositionPair ι) (PositionPair ι) => φ x) h.right_inv

/-- `∂x/∂Q = (∂(G x)/∂p) · ∂²F/∂q∂Q`. -/
theorem gradNew_eq (h : IsFree F G) (x : PositionPair ι) :
    gradNew x = momentumPart F G x ᵥ* mixedHessian F := by
  have h1 := gradNew_oldMap F (G x)
  rwa [h.oldMap_apply] at h1

/-- `∂x/∂q = ∂(G x)/∂q + (∂(G x)/∂p) · ∂²F/∂q∂q`. -/
theorem gradOld_eq (h : IsFree F G) (x : PositionPair ι) :
    gradOld x = positionPart F G x + momentumPart F G x ᵥ* oldHessian F := by
  have h1 := gradOld_oldMap F (G x)
  rwa [h.oldMap_apply] at h1

theorem positionPart_eq (h : IsFree F G) (x : PositionPair ι) :
    positionPart F G x = gradOld x - momentumPart F G x ᵥ* oldHessian F :=
  eq_sub_of_add_eq (h.gradOld_eq x).symm

/-- The mixed matrix `∂²F/∂qₖ∂Qₗ` of a free generating function is
invertible. -/
theorem inverseMixed_mul_mixedHessian (h : IsFree F G) :
    inverseMixed F G * mixedHessian F = 1 := by
  refine Matrix.ext fun j l => ?_
  have h1 := congrFun (h.gradNew_eq (newPosition j)) l
  rw [gradNew_newPosition, Pi.single_apply] at h1
  rw [Matrix.one_apply]
  by_cases hjl : j = l
  · subst hjl
    simp only [↓reduceIte] at h1 ⊢
    exact h1.symm
  · simp only [hjl, Ne.symm hjl, ↓reduceIte] at h1 ⊢
    exact h1.symm

theorem mixedHessian_mul_inverseMixed (h : IsFree F G) :
    mixedHessian F * inverseMixed F G = 1 :=
  mul_eq_one_comm.mp h.inverseMixed_mul_mixedHessian

/-- `∂(G x)/∂p = (∂x/∂Q) · (∂²F/∂q∂Q)⁻¹`. -/
theorem momentumPart_eq (h : IsFree F G) (x : PositionPair ι) :
    momentumPart F G x = gradNew x ᵥ* inverseMixed F G := by
  rw [h.gradNew_eq x, Matrix.vecMul_vecMul, h.mixedHessian_mul_inverseMixed, Matrix.vecMul_one]

theorem momentumPart_neg (h : IsFree F G) (x : PositionPair ι) :
    momentumPart F G (-x) = -momentumPart F G x := by
  rw [h.momentumPart_eq, h.momentumPart_eq, gradNew_neg, Matrix.neg_vecMul]

/-- `(∂²F/∂q∂Q)⁻¹` applied to the column `∂²F/∂qₖ∂Qᵢ` of the mixed matrix. -/
theorem inverseMixed_mulVec_gradOld_gradNew (h : IsFree F G) (i : ι) :
    inverseMixed F G *ᵥ gradOld (gradNew F i) = Pi.single i 1 := by
  funext l
  have h1 := congrFun (congrFun h.inverseMixed_mul_mixedHessian l) i
  rw [Matrix.one_apply] at h1
  rw [Pi.single_apply]
  refine Eq.trans ?_ h1
  exact Finset.sum_congr rfl fun k _ => by rw [gradOld_gradNew]

/-- The canonical bracket in the co-ordinates `(q, Q)`:
`{x, y} = ∂x/∂q · (∂y/∂Q · B) − (∂x/∂Q · B) · ∂y/∂q` with
`B = (∂²F/∂q∂Q)⁻¹`. -/
theorem oldMap_bracket (h : IsFree F G) (x y : PositionPair ι) :
    oldMap F ((PhaseSpace.canonical ι).bracket (G x) (G y)) =
      gradOld x ⬝ᵥ (gradNew y ᵥ* inverseMixed F G) -
        (gradNew x ᵥ* inverseMixed F G) ⬝ᵥ gradOld y := by
  have hsymm : (momentumPart F G x ᵥ* oldHessian F) ⬝ᵥ momentumPart F G y =
      momentumPart F G x ⬝ᵥ (momentumPart F G y ᵥ* oldHessian F) := by
    rw [← Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, oldHessian_transpose]
  have h0 : oldMap F ((PhaseSpace.canonical ι).bracket (G x) (G y)) =
      positionPart F G x ⬝ᵥ momentumPart F G y -
        momentumPart F G x ⬝ᵥ positionPart F G y := by
    rw [PhaseSpace.canonical_bracket, SmoothRingHom.map_sum, dotProduct, dotProduct,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [SmoothRingHom.map_sub, SmoothRingHom.map_mul, SmoothRingHom.map_mul]
    rfl
  rw [h0, h.positionPart_eq x, h.positionPart_eq y, sub_dotProduct, dotProduct_sub, hsymm,
    ← h.momentumPart_eq x, ← h.momentumPart_eq y]
  ring

/-- The bracket of two functions of `(q, p)` that are given in the
co-ordinates `(q, Q)`. -/
theorem bracket_apply (h : IsFree F G) (x y : PositionPair ι) :
    (PhaseSpace.canonical ι).bracket (G x) (G y) =
      G (gradOld x ⬝ᵥ momentumPart F G y - momentumPart F G x ⬝ᵥ gradOld y) := by
  rw [h.momentumPart_eq x, h.momentumPart_eq y, ← h.oldMap_bracket, h.apply_oldMap]

/-- `(∂(G x)/∂p) · (∂²F/∂q∂Qᵢ) = ∂x/∂Qᵢ`. -/
theorem momentumPart_dotProduct_gradOld_gradNew (h : IsFree F G) (x : PositionPair ι) (i : ι) :
    momentumPart F G x ⬝ᵥ gradOld (gradNew F i) = gradNew x i := by
  rw [h.momentumPart_eq, ← Matrix.dotProduct_mulVec, h.inverseMixed_mulVec_gradOld_gradNew,
    dotProduct_single_one]

/-- `{Qᵢ, Qⱼ} = 0`. -/
theorem bracket_newPosition_newPosition (h : IsFree F G) (i j : ι) :
    (PhaseSpace.canonical ι).bracket (G (newPosition i)) (G (newPosition j)) = 0 := by
  rw [h.bracket_apply, gradOld_newPosition, gradOld_newPosition, zero_dotProduct,
    dotProduct_zero, sub_zero, SmoothRingHom.map_zero]

/-- `{Qᵢ, ∂F/∂Qⱼ} = −δᵢⱼ`. -/
theorem bracket_newPosition_gradNew (h : IsFree F G) (i j : ι) :
    (PhaseSpace.canonical ι).bracket (G (newPosition i)) (G (gradNew F j)) =
      if i = j then -1 else 0 := by
  rw [h.bracket_apply, gradOld_newPosition, zero_dotProduct, zero_sub,
    h.momentumPart_dotProduct_gradOld_gradNew, gradNew_newPosition, Pi.single_apply]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte, SmoothRingHom.map_neg, SmoothRingHom.map_one]
  · simp only [hij, Ne.symm hij, ↓reduceIte, neg_zero, SmoothRingHom.map_zero]

/-- `{∂F/∂Qᵢ, ∂F/∂Qⱼ} = 0`. -/
theorem bracket_gradNew_gradNew (h : IsFree F G) (i j : ι) :
    (PhaseSpace.canonical ι).bracket (G (gradNew F i)) (G (gradNew F j)) = 0 := by
  rw [h.bracket_apply, dotProduct_comm (gradOld (gradNew F i)),
    h.momentumPart_dotProduct_gradOld_gradNew, h.momentumPart_dotProduct_gradOld_gradNew,
    gradNew_gradNew_comm F i j, sub_self, SmoothRingHom.map_zero]

end IsFree

omit [Fintype ι] in
theorem transformation_q (F : PositionPair ι) (G : SmoothRingHom (PositionPair ι) (PhaseSpace ι))
    (i : ι) : transformation F G (PhaseSpace.q i) = G (newPosition i) := by
  rw [transformation, SmoothRingHom.comp_apply, newMap_q]

omit [Fintype ι] in
theorem transformation_p (F : PositionPair ι) (G : SmoothRingHom (PositionPair ι) (PhaseSpace ι))
    (i : ι) : transformation F G (PhaseSpace.p i) = -G (gradNew F i) := by
  rw [transformation, SmoothRingHom.comp_apply, newMap_p, SmoothRingHom.map_neg]

namespace IsFree

variable {F : PositionPair ι} {G : SmoothRingHom (PositionPair ι) (PhaseSpace ι)}

/-- The transformation generated by a free generating function is canonical
(Landau–Lifshitz §45). -/
theorem isPoissonHom_transformation (h : IsFree F G) :
    IsPoissonHom (PhaseSpace.canonical ι).toAlmostPoissonStructure
      (PhaseSpace.canonical ι).toAlmostPoissonStructure (transformation F G) :=
  FreeSmoothRing.isPoissonHom_of_generators fun a b => by
    rcases a with i | i <;> rcases b with j | j
    · change transformation F G
          ((PhaseSpace.canonical ι).bracket (PhaseSpace.q i) (PhaseSpace.q j)) =
        (PhaseSpace.canonical ι).bracket (transformation F G (PhaseSpace.q i))
          (transformation F G (PhaseSpace.q j))
      rw [PhaseSpace.canonical_q_q, SmoothRingHom.map_zero, transformation_q, transformation_q,
        h.bracket_newPosition_newPosition]
    · change transformation F G
          ((PhaseSpace.canonical ι).bracket (PhaseSpace.q i) (PhaseSpace.p j)) =
        (PhaseSpace.canonical ι).bracket (transformation F G (PhaseSpace.q i))
          (transformation F G (PhaseSpace.p j))
      rw [PhaseSpace.canonical_q_p, transformation_q, transformation_p,
        AlmostPoissonStructure.bracket_neg_right, h.bracket_newPosition_gradNew]
      split_ifs
      · rw [SmoothRingHom.map_one, neg_neg]
      · rw [SmoothRingHom.map_zero, neg_zero]
    · change transformation F G
          ((PhaseSpace.canonical ι).bracket (PhaseSpace.p i) (PhaseSpace.q j)) =
        (PhaseSpace.canonical ι).bracket (transformation F G (PhaseSpace.p i))
          (transformation F G (PhaseSpace.q j))
      rw [PhaseSpace.canonical_p_q, transformation_q, transformation_p,
        AlmostPoissonStructure.bracket_neg_left,
        (PhaseSpace.canonical ι).antisymm (G (gradNew F i)) (G (newPosition j)),
        h.bracket_newPosition_gradNew, neg_neg]
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte, SmoothRingHom.map_neg, SmoothRingHom.map_one]
      · simp only [hij, Ne.symm hij, ↓reduceIte, SmoothRingHom.map_zero]
    · change transformation F G
          ((PhaseSpace.canonical ι).bracket (PhaseSpace.p i) (PhaseSpace.p j)) =
        (PhaseSpace.canonical ι).bracket (transformation F G (PhaseSpace.p i))
          (transformation F G (PhaseSpace.p j))
      rw [PhaseSpace.canonical_p_p, SmoothRingHom.map_zero, transformation_p, transformation_p,
        AlmostPoissonStructure.bracket_neg_left, AlmostPoissonStructure.bracket_neg_right,
        neg_neg, h.bracket_gradNew_gradNew]

omit [Fintype ι] in
/-- If `newMap F` also has an inverse `G'`, the transformation is invertible,
with the inverse `G' ∘ oldMap F`. -/
theorem transformation_comp_inverse (h : IsFree F G)
    {G' : SmoothRingHom (PositionPair ι) (PhaseSpace ι)}
    (hr : (newMap F).comp G' = SmoothRingHom.id (PositionPair ι)) :
    (transformation F G).comp (G'.comp (oldMap F)) = SmoothRingHom.id (PhaseSpace ι) := by
  refine SmoothRingHom.ext fun s => ?_
  have h1 : newMap F (G' (oldMap F s)) = oldMap F s :=
    congrArg (fun φ : SmoothRingHom (PositionPair ι) (PositionPair ι) => φ (oldMap F s)) hr
  rw [SmoothRingHom.comp_apply, SmoothRingHom.comp_apply, transformation,
    SmoothRingHom.comp_apply, h1, h.apply_oldMap, SmoothRingHom.id_apply]

omit [Fintype ι] in
theorem inverse_comp_transformation (h : IsFree F G)
    {G' : SmoothRingHom (PositionPair ι) (PhaseSpace ι)}
    (hl : G'.comp (newMap F) = SmoothRingHom.id (PhaseSpace ι)) :
    (G'.comp (oldMap F)).comp (transformation F G) = SmoothRingHom.id (PhaseSpace ι) := by
  refine SmoothRingHom.ext fun s => ?_
  have h1 : G' (newMap F s) = s :=
    congrArg (fun φ : SmoothRingHom (PhaseSpace ι) (PhaseSpace ι) => φ s) hl
  rw [SmoothRingHom.comp_apply, SmoothRingHom.comp_apply, transformation,
    SmoothRingHom.comp_apply, h.oldMap_apply, h1, SmoothRingHom.id_apply]

end IsFree

/-! ### The exchange of the co-ordinates and the momenta -/

/-- The generating function `Σ qᵢ Qᵢ`. -/
def exchange : PositionPair ι := ∑ k, oldPosition k * newPosition k

theorem gradOld_exchange (i : ι) : gradOld (exchange (ι := ι)) i = newPosition i := by
  have hterm (k : ι) : partialDerivation (Sum.inl i) (oldPosition k * newPosition k) =
      if k = i then newPosition k else 0 := by
    rw [SmoothDerivation.map_mul, oldPosition, newPosition, partialDerivation_generator,
      partialDerivation_generator]
    simp only [Sum.inl.injEq, reduceCtorEq, ↓reduceIte, zero_add, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
  rw [gradOld, exchange, map_sum]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem gradNew_exchange (i : ι) : gradNew (exchange (ι := ι)) i = oldPosition i := by
  have hterm (k : ι) : partialDerivation (Sum.inr i) (oldPosition k * newPosition k) =
      if k = i then oldPosition k else 0 := by
    rw [SmoothDerivation.map_mul, oldPosition, newPosition, partialDerivation_generator,
      partialDerivation_generator]
    simp only [Sum.inr.injEq, reduceCtorEq, ↓reduceIte, add_zero, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
  rw [gradNew, exchange, map_sum]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem oldMap_exchange : oldMap (exchange (ι := ι)) = SmoothRingHom.id (PhaseSpace ι) :=
  FreeSmoothRing.hom_ext fun a => by
    rw [SmoothRingHom.id_apply]
    rcases a with i | i
    · exact oldMap_q exchange i
    · exact (oldMap_p exchange i).trans (gradOld_exchange i)

/-- `Σ qᵢ Qᵢ` is a free generating function. -/
theorem isFree_exchange : IsFree (exchange (ι := ι)) (SmoothRingHom.id (PhaseSpace ι)) where
  left_inv := by
    rw [oldMap_exchange]
    rfl
  right_inv := by
    rw [oldMap_exchange]
    rfl

/-- The transformation generated by `Σ qᵢ Qᵢ` is `Qᵢ = pᵢ`, `Pᵢ = −qᵢ`
(Landau–Lifshitz §45). -/
theorem transformation_exchange_q (i : ι) :
    transformation (exchange (ι := ι)) (SmoothRingHom.id (PhaseSpace ι)) (PhaseSpace.q i) =
      PhaseSpace.p i := by
  rw [transformation_q]
  rfl

theorem transformation_exchange_p (i : ι) :
    transformation (exchange (ι := ι)) (SmoothRingHom.id (PhaseSpace ι)) (PhaseSpace.p i) =
      -PhaseSpace.q i := by
  rw [transformation_p, gradNew_exchange]
  rfl

end ProjectAInos.Mechanics.GeneratingFunction
