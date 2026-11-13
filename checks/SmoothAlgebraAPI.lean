/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAInos

/-! Public consumers of the differential part of the smooth-algebra API. Default
elaborator options are intentional: these checks must not rely on the
implementation's transparency settings. Every statement is pinned with its type. -/
noncomputable section
open ProjectAInos.SmoothAlgebra ProjectAInos.SmoothAlgebra.SmoothRing
open ProjectAInos.SmoothAlgebra.SmoothOperation

variable {n m : ℕ}

section PartialDerivative

example (f : SmoothOperation n) (x v : Fin n → ℝ) :
    fderiv ℝ f x v = ∑ i, v i * partialDeriv i f x := fderiv_apply_eq_sum_partialDeriv f x v

example (i j : Fin n) : partialDeriv i (proj j) = if i = j then 1 else 0 :=
  partialDeriv_proj i j

example (i : Fin n) (f g : SmoothOperation n) :
    partialDeriv i (f * g) = partialDeriv i f * g + f * partialDeriv i g :=
  partialDeriv_mul i f g

example (f : SmoothOperation n) (g : Fin n → SmoothOperation m) (j : Fin m) :
    partialDeriv j (comp f g) = ∑ i, comp (partialDeriv i f) g * partialDeriv j (g i) :=
  partialDeriv_comp f g j

example (i j : Fin n) (f : SmoothOperation n) :
    partialDeriv i (partialDeriv j f) = partialDeriv j (partialDeriv i f) :=
  partialDeriv_comm i j f

example : partialDeriv 0 exponential = exponential := partialDeriv_exponential

example (x v : Fin n → ℝ) (g : SmoothOperation n) :
    directionalEvaluation x v g = ∑ i, v i * partialDeriv i g x :=
  directionalEvaluation_eq_sum x v g

end PartialDerivative

section DualNumber

variable {A : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]

example : SmoothRing (DualNumber A) := inferInstance

example (f : SmoothOperation n) (c : Fin n → DualNumber A) :
    (op f c).fst = op f fun i => (c i).fst := DualNumber.fst_op f c

example (f : SmoothOperation n) (c : Fin n → DualNumber A) :
    (op f c).snd = ∑ i, op (partialDeriv i f) (fun k => (c k).fst) * (c i).snd :=
  DualNumber.snd_op f c

example : (DualNumber.fstHom (A := A)).comp DualNumber.inlHom = SmoothRingHom.id A :=
  DualNumber.fstHom_comp_inlHom

example (a b : A) :
    exp (TrivSqZeroExt.inl a + TrivSqZeroExt.inr b : DualNumber A) =
      TrivSqZeroExt.inl (exp a) + TrivSqZeroExt.inr (exp a * b) :=
  DualNumber.exp_inl_add_inr a b

example (a b : ℝ) :
    exp (TrivSqZeroExt.inl a + TrivSqZeroExt.inr b : DualNumber ℝ) =
      TrivSqZeroExt.inl (Real.exp a) + TrivSqZeroExt.inr (Real.exp a * b) :=
  DualNumber.exp_real a b

end DualNumber

section Derivation

variable {A M : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A] [AddCommGroup M] [Module A M]

example (d : SmoothDerivation A M) (f : SmoothOperation n) (a : Fin n → A) :
    d (op f a) = ∑ i, op (partialDeriv i f) a • d (a i) := d.chain f a

example (d : SmoothDerivation A M) (a b : A) : d (a + b) = d a + d b := d.map_add a b

example (d : SmoothDerivation A M) (a b : A) : d (a * b) = a • d b + b • d a := d.map_mul a b

example (d : SmoothDerivation A M) (r : ℝ) : d (algebraMap ℝ A r) = 0 := d.map_algebraMap r

example (d : SmoothDerivation A M) (a : A) : d (exp a) = exp a • d a := d.map_exp a

example [Module ℝ M] [IsScalarTower ℝ A M] (d : SmoothDerivation A M) (r : ℝ) (a : A) :
    d (r • a) = r • d a := d.map_smul r a

example [Module ℝ M] [IsScalarTower ℝ A M] (d : SmoothDerivation A M) (a : A) :
    (d.toDerivation : Derivation ℝ A M) a = d a := d.toDerivation_apply a

example : Module A (SmoothDerivation A M) := inferInstance

example (c : A) (d : SmoothDerivation A M) (a : A) : (c • d) a = c • d a :=
  SmoothDerivation.smul_apply c d a

example : LieRing (SmoothDerivation A A) := inferInstance

example (ξ η : SmoothDerivation A A) (a : A) : ⁅ξ, η⁆ a = ξ (η a) - η (ξ a) :=
  SmoothDerivation.commutator_apply ξ η a

example (ξ η : SmoothDerivation A A) (f : SmoothOperation n) (a : Fin n → A) :
    ξ (η (op f a)) - η (ξ (op f a)) =
      ∑ i, op (partialDeriv i f) a * (ξ (η (a i)) - η (ξ (a i))) :=
  SmoothDerivation.commutator_chain ξ η f a

example : SmoothDerivation A A ≃
    {φ : SmoothRingHom A (DualNumber A) // ∀ a, (φ a).fst = a} :=
  SmoothDerivation.equivInfinitesimalAut

example (ξ : SmoothDerivation A A) (a : A) :
    ((SmoothDerivation.equivInfinitesimalAut ξ).1 a).snd = ξ a := ξ.snd_toInfinitesimalAut a

example (φ : {φ : SmoothRingHom A (DualNumber A) // ∀ a, (φ a).fst = a}) (a : A) :
    SmoothDerivation.equivInfinitesimalAut.symm φ a = (φ.1 a).snd := rfl

end Derivation

section Free

variable {M : Type*} [AddCommGroup M] [Module (SmoothOperation n) M]

example (d : SmoothDerivation (SmoothOperation n) M) (f : SmoothOperation n) :
    d f = ∑ i, partialDeriv i f • d (proj i) := d.apply_eq_sum_partialDeriv f

example (d : SmoothDerivation (SmoothOperation n) M) (i : Fin n) :
    SmoothDerivation.equivCoordinates d i = d (proj i) := rfl

example (v : Fin n → M) (i : Fin n) :
    SmoothDerivation.equivCoordinates.symm v (proj i) = v i :=
  SmoothDerivation.ofCoordinates_proj v i

example (i j : Fin n) :
    SmoothDerivation.partialDerivation i (proj j) = if i = j then 1 else 0 :=
  SmoothDerivation.partialDerivation_proj i j

example (i j : Fin n) :
    ⁅SmoothDerivation.partialDerivation i, SmoothDerivation.partialDerivation j⁆ = 0 :=
  SmoothDerivation.lie_partialDerivation i j

example (i j k : Fin n) :
    ⁅SmoothDerivation.partialDerivation i, proj j • SmoothDerivation.partialDerivation k⁆ =
      (if i = j then (1 : SmoothOperation n) else 0) • SmoothDerivation.partialDerivation k :=
  SmoothDerivation.lie_partialDerivation_proj_smul i j k

end Free
