/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.DualNumber
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Derivations of C-infinity rings

A C-infinity derivation `d : A → M` satisfies the chain rule for every finite
smooth operation. That single law implies additivity, the Leibniz rule,
vanishing on constants and real linearity, so a C-infinity derivation is an
ordinary derivation of the real algebra. The converse fails in general: an
ordinary derivation need not satisfy `d (exp a) = exp a • d a`.

Vector fields are the derivations of `A` into itself. They form a Lie ring under
the commutator and correspond to the morphisms `A → A[ε]` that reduce to the
identity at `ε = 0`. On the free ring `C∞(ℝⁿ)` a derivation is determined by
its values on the coordinates, which may be prescribed arbitrarily.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.SmoothAlgebra

open SmoothRing SmoothOperation

/-- A map into a module satisfying the chain rule for every smooth operation.
Linearity and the Leibniz rule are consequences, not fields. -/
structure SmoothDerivation (A M : Type*) [CommRing A] [Algebra ℝ A] [SmoothRing A]
    [AddCommGroup M] [Module A M] where
  /-- The underlying function. Use the function coercion instead. -/
  toFun : A → M
  /-- The chain rule for every finite smooth operation. -/
  chain' : ∀ {n} (f : SmoothOperation n) (a : Fin n → A),
    toFun (op f a) = ∑ i, op (partialDeriv i f) a • toFun (a i)

namespace SmoothDerivation

section Module

variable {A M : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A] [AddCommGroup M] [Module A M]

instance : FunLike (SmoothDerivation A M) A M where
  coe := SmoothDerivation.toFun
  coe_injective d e h := by
    cases d
    cases e
    cases h
    rfl

@[ext] theorem ext {d e : SmoothDerivation A M} (h : ∀ a, d a = e a) : d = e :=
  DFunLike.ext _ _ h

/-- The chain rule for every finite smooth operation. -/
theorem chain (d : SmoothDerivation A M) {n : ℕ} (f : SmoothOperation n) (a : Fin n → A) :
    d (op f a) = ∑ i, op (partialDeriv i f) a • d (a i) := d.chain' f a

/-- Real constants have zero derivative: the chain rule for a nullary operation. -/
@[simp] theorem map_algebraMap (d : SmoothDerivation A M) (r : ℝ) :
    d (algebraMap ℝ A r) = 0 := by
  simpa using d.chain (const 0 r) (Fin.elim0 : Fin 0 → A)

@[simp] protected theorem map_zero (d : SmoothDerivation A M) : d 0 = 0 := by
  simpa using d.map_algebraMap 0

@[simp] theorem map_one (d : SmoothDerivation A M) : d 1 = 0 := by
  simpa using d.map_algebraMap 1

/-- Additivity is the chain rule for binary addition. -/
@[simp] protected theorem map_add (d : SmoothDerivation A M) (a b : A) :
    d (a + b) = d a + d b := by
  simpa [partialDeriv_addition, Fin.sum_univ_two] using d.chain addition ![a, b]

/-- The Leibniz rule is the chain rule for binary multiplication. -/
theorem map_mul (d : SmoothDerivation A M) (a b : A) : d (a * b) = a • d b + b • d a := by
  have h := d.chain multiplication ![a, b]
  simp only [op_multiplication, Fin.sum_univ_two, partialDeriv_multiplication_zero,
    partialDeriv_multiplication_one, op_proj, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [h, add_comm]

instance : AddMonoidHomClass (SmoothDerivation A M) A M where
  map_add := SmoothDerivation.map_add
  map_zero := SmoothDerivation.map_zero

/-- Real constants pass through a C-infinity derivation. -/
theorem map_algebraMap_mul (d : SmoothDerivation A M) (r : ℝ) (a : A) :
    d (algebraMap ℝ A r * a) = algebraMap ℝ A r • d a := by
  rw [map_mul, map_algebraMap, smul_zero, add_zero]

/-- Real linearity, when the module carries a compatible real action. -/
protected theorem map_smul [Module ℝ M] [IsScalarTower ℝ A M] (d : SmoothDerivation A M)
    (r : ℝ) (a : A) : d (r • a) = r • d a := by
  rw [Algebra.smul_def, map_algebraMap_mul, algebraMap_smul]

/-- A nonpolynomial instance of the chain rule, false for general ordinary
derivations of the underlying real algebra. -/
theorem map_exp (d : SmoothDerivation A M) (a : A) : d (exp a) = exp a • d a := by
  simpa [exp, partialDeriv_exponential] using d.chain exponential ![a]

/-- A C-infinity derivation is an ordinary derivation of the real algebra. -/
def toDerivation [Module ℝ M] [IsScalarTower ℝ A M] (d : SmoothDerivation A M) :
    Derivation ℝ A M where
  toFun := d
  map_add' := d.map_add
  map_smul' r a := d.map_smul r a
  map_one_eq_zero' := d.map_one
  leibniz' := d.map_mul

@[simp] theorem toDerivation_apply [Module ℝ M] [IsScalarTower ℝ A M]
    (d : SmoothDerivation A M) (a : A) : d.toDerivation a = d a := rfl

instance : Zero (SmoothDerivation A M) := ⟨⟨fun _ => 0, fun _ _ => by simp⟩⟩

instance : Add (SmoothDerivation A M) :=
  ⟨fun d e => ⟨fun a => d a + e a, fun f a => by
    simp only [d.chain, e.chain, smul_add, Finset.sum_add_distrib]⟩⟩

instance : Neg (SmoothDerivation A M) :=
  ⟨fun d => ⟨fun a => -d a, fun f a => by
    simp only [d.chain, smul_neg, Finset.sum_neg_distrib]⟩⟩

instance : Sub (SmoothDerivation A M) :=
  ⟨fun d e => ⟨fun a => d a - e a, fun f a => by
    simp only [d.chain, e.chain, smul_sub, Finset.sum_sub_distrib]⟩⟩

/-- Scalars commuting with the ring act on derivations. This covers the ring
itself, natural and integer multiples, and compatible real scalars. -/
instance {S : Type*} [Monoid S] [DistribMulAction S M] [SMulCommClass S A M] :
    SMul S (SmoothDerivation A M) :=
  ⟨fun c d => ⟨fun a => c • d a, fun f a => by
    rw [d.chain, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _⟩⟩

@[simp] theorem zero_apply (a : A) : (0 : SmoothDerivation A M) a = 0 := rfl
@[simp] theorem add_apply (d e : SmoothDerivation A M) (a : A) : (d + e) a = d a + e a := rfl
@[simp] theorem neg_apply (d : SmoothDerivation A M) (a : A) : (-d) a = -d a := rfl
@[simp] theorem sub_apply (d e : SmoothDerivation A M) (a : A) : (d - e) a = d a - e a := rfl
@[simp] theorem smul_apply {S : Type*} [Monoid S] [DistribMulAction S M] [SMulCommClass S A M]
    (c : S) (d : SmoothDerivation A M) (a : A) : (c • d) a = c • d a := rfl

instance : AddCommGroup (SmoothDerivation A M) :=
  DFunLike.coe_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- The coercion to functions, as an additive homomorphism. -/
def coeFnAddMonoidHom : SmoothDerivation A M →+ A → M where
  toFun d := d
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Derivations form a module over the ring, and over any commuting scalars. -/
instance {S : Type*} [Semiring S] [Module S M] [SMulCommClass S A M] :
    Module S (SmoothDerivation A M) :=
  Function.Injective.module S coeFnAddMonoidHom DFunLike.coe_injective fun _ _ => rfl

/-- A finite sum of derivations is evaluated termwise. -/
theorem sum_apply {ι : Type*} (s : Finset ι) (d : ι → SmoothDerivation A M) (a : A) :
    (∑ i ∈ s, d i) a = ∑ i ∈ s, d i a := by
  have h := congrFun (map_sum (coeFnAddMonoidHom (A := A) (M := M)) d s) a
  rw [Finset.sum_apply] at h
  exact h

end Module

section VectorField

variable {A : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]

/-- The second-order expansion used for the commutator. -/
private theorem apply_apply_op (ξ η : SmoothDerivation A A) {n : ℕ} (f : SmoothOperation n)
    (a : Fin n → A) :
    ξ (η (op f a)) = ∑ i, op (partialDeriv i f) a * ξ (η (a i)) +
      ∑ i, ∑ j, op (partialDeriv j (partialDeriv i f)) a * (ξ (a j) * η (a i)) := by
  rw [η.chain, map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, map_mul, ξ.chain, smul_eq_mul, smul_eq_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_eq_mul]
  ring

/-- The commutator of two vector fields satisfies the chain rule. The
second-order terms cancel because partial derivatives commute. -/
theorem commutator_chain (ξ η : SmoothDerivation A A) {n : ℕ} (f : SmoothOperation n)
    (a : Fin n → A) :
    ξ (η (op f a)) - η (ξ (op f a)) =
      ∑ i, op (partialDeriv i f) a * (ξ (η (a i)) - η (ξ (a i))) := by
  have hswap : ∑ i, ∑ j, op (partialDeriv j (partialDeriv i f)) a * (η (a j) * ξ (a i)) =
      ∑ i, ∑ j, op (partialDeriv j (partialDeriv i f)) a * (ξ (a j) * η (a i)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [partialDeriv_comm i j f, mul_comm (η (a i))]
  rw [apply_apply_op ξ η, apply_apply_op η ξ, hswap]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- Vector fields are closed under the commutator. -/
instance : Bracket (SmoothDerivation A A) (SmoothDerivation A A) :=
  ⟨fun ξ η => ⟨fun a => ξ (η a) - η (ξ a), fun f a => by
    simpa only [smul_eq_mul] using commutator_chain ξ η f a⟩⟩

theorem commutator_apply (ξ η : SmoothDerivation A A) (a : A) :
    ⁅ξ, η⁆ a = ξ (η a) - η (ξ a) := rfl

/-- Vector fields form a Lie ring under the commutator. -/
instance : LieRing (SmoothDerivation A A) where
  add_lie ξ η ζ := by
    ext a
    simp only [commutator_apply, add_apply, map_add]
    abel
  lie_add ξ η ζ := by
    ext a
    simp only [commutator_apply, add_apply, map_add]
    abel
  lie_self ξ := by
    ext a
    simp only [commutator_apply, sub_self, zero_apply]
  leibniz_lie ξ η ζ := by
    ext a
    simp only [commutator_apply, add_apply, map_sub]
    abel

/-- A vector field as an infinitesimal automorphism `a ↦ a + ε ξ(a)`. -/
def toInfinitesimalAut (ξ : SmoothDerivation A A) : SmoothRingHom A (DualNumber A) where
  toFun a := TrivSqZeroExt.inl a + TrivSqZeroExt.inr (ξ a)
  map_op' f a := by
    apply TrivSqZeroExt.ext
    · simp
    · simp [ξ.chain]

@[simp] theorem fst_toInfinitesimalAut (ξ : SmoothDerivation A A) (a : A) :
    (ξ.toInfinitesimalAut a).fst = a := by
  change (TrivSqZeroExt.inl a + TrivSqZeroExt.inr (ξ a) : DualNumber A).fst = a
  simp

@[simp] theorem snd_toInfinitesimalAut (ξ : SmoothDerivation A A) (a : A) :
    (ξ.toInfinitesimalAut a).snd = ξ a := by
  change (TrivSqZeroExt.inl a + TrivSqZeroExt.inr (ξ a) : DualNumber A).snd = ξ a
  simp

/-- An infinitesimal automorphism reduces to the identity at `ε = 0`. -/
@[simp] theorem fstHom_comp_toInfinitesimalAut (ξ : SmoothDerivation A A) :
    DualNumber.fstHom.comp ξ.toInfinitesimalAut = SmoothRingHom.id A :=
  SmoothRingHom.ext fun a => ξ.fst_toInfinitesimalAut a

/-- The infinitesimal part of a morphism `A → A[ε]` lifting the identity. -/
def ofInfinitesimalAut (φ : SmoothRingHom A (DualNumber A)) (hφ : ∀ a, (φ a).fst = a) :
    SmoothDerivation A A where
  toFun a := (φ a).snd
  chain' f a := by
    rw [φ.map_op, DualNumber.snd_op]
    simp only [hφ, smul_eq_mul]

@[simp] theorem ofInfinitesimalAut_apply (φ : SmoothRingHom A (DualNumber A))
    (hφ : ∀ a, (φ a).fst = a) (a : A) : ofInfinitesimalAut φ hφ a = (φ a).snd := rfl

/-- Vector fields are exactly the infinitesimal automorphisms: the morphisms
`A → A[ε]` that reduce to the identity at `ε = 0`. -/
def equivInfinitesimalAut :
    SmoothDerivation A A ≃ {φ : SmoothRingHom A (DualNumber A) // ∀ a, (φ a).fst = a} where
  toFun ξ := ⟨ξ.toInfinitesimalAut, ξ.fst_toInfinitesimalAut⟩
  invFun φ := ofInfinitesimalAut φ.1 φ.2
  left_inv ξ := by
    ext a
    simp
  right_inv φ := by
    apply Subtype.ext
    apply SmoothRingHom.ext
    intro a
    apply TrivSqZeroExt.ext
    · simp [φ.2 a]
    · simp

end VectorField

section Free

variable {n : ℕ}

/-- The coordinate vector fields on `C∞(ℝⁿ)`. -/
def partialDerivation (i : Fin n) :
    SmoothDerivation (SmoothOperation n) (SmoothOperation n) where
  toFun := partialDeriv i
  chain' f g := by
    simp only [function_op, partialDeriv_comp, smul_eq_mul]

@[simp] theorem partialDerivation_apply (i : Fin n) (f : SmoothOperation n) :
    partialDerivation i f = partialDeriv i f := rfl

variable {M : Type*} [AddCommGroup M] [Module (SmoothOperation n) M]

/-- On the free ring a derivation is determined by its values on the coordinates. -/
theorem apply_eq_sum_partialDeriv (d : SmoothDerivation (SmoothOperation n) M)
    (f : SmoothOperation n) : d f = ∑ i, partialDeriv i f • d (proj i) := by
  simpa only [function_op, comp_proj] using d.chain f proj

/-- The derivation of the free ring with prescribed values on the coordinates. -/
def ofCoordinates (v : Fin n → M) : SmoothDerivation (SmoothOperation n) M where
  toFun f := ∑ i, partialDeriv i f • v i
  chain' f g := by
    simp only [function_op, partialDeriv_comp, Finset.sum_smul, Finset.smul_sum, mul_smul]
    rw [Finset.sum_comm]

@[simp] theorem ofCoordinates_apply (v : Fin n → M) (f : SmoothOperation n) :
    ofCoordinates v f = ∑ i, partialDeriv i f • v i := rfl

@[simp] theorem ofCoordinates_proj (v : Fin n → M) (i : Fin n) :
    ofCoordinates v (proj i) = v i := by
  simp [partialDeriv_proj, ite_smul]

/-- Derivations of `C∞(ℝⁿ)` are free on the coordinates: they correspond to
arbitrary tuples of values on the projections. -/
def equivCoordinates : SmoothDerivation (SmoothOperation n) M ≃ (Fin n → M) where
  toFun d i := d (proj i)
  invFun := ofCoordinates
  left_inv d := by
    ext f
    exact (d.apply_eq_sum_partialDeriv f).symm
  right_inv v := funext fun i => ofCoordinates_proj v i

/-- The coordinate vector fields are the derivations dual to the coordinates. -/
theorem partialDerivation_proj (i j : Fin n) :
    partialDerivation i (proj j) = if i = j then 1 else 0 := partialDeriv_proj i j

/-- Coordinate vector fields commute. -/
theorem lie_partialDerivation (i j : Fin n) :
    ⁅partialDerivation i, partialDerivation j⁆ = 0 := by
  refine SmoothDerivation.ext fun f => ?_
  simp only [commutator_apply, partialDerivation_apply, partialDeriv_comm i j f, sub_self,
    zero_apply]

/-- The commutator is not trivial: `[∂ᵢ, xⱼ ∂ₖ] = δᵢⱼ ∂ₖ`. -/
theorem lie_partialDerivation_proj_smul (i j k : Fin n) :
    ⁅partialDerivation i, proj j • partialDerivation k⁆ =
      (if i = j then (1 : SmoothOperation n) else 0) • partialDerivation k := by
  refine SmoothDerivation.ext fun f => ?_
  simp only [commutator_apply, smul_apply, partialDerivation_apply, smul_eq_mul,
    partialDeriv_mul, partialDeriv_proj, partialDeriv_comm i k f]
  ring

end Free

end SmoothDerivation

end ProjectAInos.SmoothAlgebra
