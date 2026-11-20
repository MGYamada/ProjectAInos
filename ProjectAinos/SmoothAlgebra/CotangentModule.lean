/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothAlgebra.Differential
public import ProjectAinos.SmoothAlgebra.FreeDerivation
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Tactic.Ring

/-!
# The universal C-infinity cotangent module

The cotangent module `Ω_A` of a C-infinity ring `A` is the free `A`-module on
symbols `da`, one for each `a : A`, modulo the chain rule

  `d(Φ_f(a₁, …, aₙ)) = Σᵢ Φ_{∂ᵢ f}(a₁, …, aₙ) daᵢ`

for every smooth operation `f` and every family `a`. Additivity, the Leibniz
rule and the vanishing on real constants are the instances `f = x₁ + x₂`,
`f = x₁ x₂` and `f = r`, so no further relations are imposed. The symbol map
`d : A → Ω_A` is a `SmoothDerivation`, and it is universal: every
`SmoothDerivation A M` factors uniquely through an `A`-linear map `Ω_A → M`.

A morphism `φ : A → B` induces the pullback `Ω_A → Ω_B`, `c da ↦ φ(c) d(φ a)`.
It is semilinear over `φ`, so no module structure of `Ω_B` over `A` is chosen.

For the model `C∞(ℝⁿ)` the module is free on `dx₁, …, dxₙ`, with the
coefficients of `df` the partial derivatives of `f`. Evaluation at a point `x`
sends `df` to the Fréchet derivative of `f` at `x`; it is surjective onto the
dual of the tangent space, its kernel is `𝔪ₓ Ω`, and it turns the pullback
along a smooth map into the transpose of its derivative. The free ring on any
set of generators has the basis `d(generator i)` as well.
-/

@[expose] public section

noncomputable section

universe u

namespace ProjectAinos.SmoothAlgebra

open SmoothRing SmoothOperation

namespace SmoothDerivation

variable {A M N : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- A derivation followed by a linear map is a derivation. -/
def compLinearMap (D : SmoothDerivation A M) (φ : M →ₗ[A] N) : SmoothDerivation A N where
  toFun a := φ (D a)
  chain' f a := by
    rw [D.chain, map_sum]
    simp only [map_smul]

/-- A composite derivation is evaluated by applying the linear map. -/
@[simp] theorem compLinearMap_apply (D : SmoothDerivation A M) (φ : M →ₗ[A] N) (a : A) :
    D.compLinearMap φ a = φ (D a) := rfl

end SmoothDerivation

namespace CotangentModule

section Relations

variable {A : Type u} [CommRing A] [Algebra ℝ A] [SmoothRing A]

/-- The defect of the chain rule for one operation and one family, in the free
module on the symbols: `[Φ_f(a)] − Σᵢ Φ_{∂ᵢ f}(a) [aᵢ]`. -/
def chainDefect {n : ℕ} (f : SmoothOperation n) (a : Fin n → A) : A →₀ A :=
  Finsupp.single (op f a) 1 - ∑ i, op (partialDeriv i f) a • Finsupp.single (a i) 1

variable (A) in
/-- The relations of the cotangent module: the span of all chain-rule defects. -/
def relations : Submodule A (A →₀ A) :=
  Submodule.span A
    {x | ∃ (n : ℕ) (f : SmoothOperation n) (a : Fin n → A), chainDefect f a = x}

/-- Each chain-rule defect is a relation. -/
theorem chainDefect_mem {n : ℕ} (f : SmoothOperation n) (a : Fin n → A) :
    chainDefect f a ∈ relations A :=
  Submodule.subset_span ⟨n, f, a, rfl⟩

end Relations

end CotangentModule

/-- The universal C-infinity cotangent module: the free module on symbols `da`
modulo the chain rule for every smooth operation. -/
def CotangentModule (A : Type u) [CommRing A] [Algebra ℝ A] [SmoothRing A] : Type u :=
  (A →₀ A) ⧸ CotangentModule.relations A

namespace CotangentModule

section Construction

variable (A : Type u) [CommRing A] [Algebra ℝ A] [SmoothRing A]

/-- The additive group of the quotient. -/
instance : AddCommGroup (CotangentModule A) :=
  inferInstanceAs (AddCommGroup ((A →₀ A) ⧸ relations A))

/-- The module structure over the ring itself. -/
instance : Module A (CotangentModule A) :=
  inferInstanceAs (Module A ((A →₀ A) ⧸ relations A))

/-- The real module structure, through the real algebra. -/
instance : Module ℝ (CotangentModule A) :=
  inferInstanceAs (Module ℝ ((A →₀ A) ⧸ relations A))

/-- Real scalars act through the ring. -/
instance : IsScalarTower ℝ A (CotangentModule A) :=
  inferInstanceAs (IsScalarTower ℝ A ((A →₀ A) ⧸ relations A))

/-- The quotient map from the free module on the symbols. -/
def mk : (A →₀ A) →ₗ[A] CotangentModule A := (relations A).mkQ

/-- Every element of the cotangent module is represented in the free module. -/
theorem mk_surjective : Function.Surjective (mk A) := (relations A).mkQ_surjective

variable {A} in
/-- The chain-rule defects vanish in the cotangent module. -/
theorem mk_chainDefect {n : ℕ} (f : SmoothOperation n) (a : Fin n → A) :
    mk A (chainDefect f a) = 0 := by
  change (relations A).mkQ _ = 0
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  exact chainDefect_mem f a

/-- The universal derivation `a ↦ da`. -/
def d : SmoothDerivation A (CotangentModule A) where
  toFun a := mk A (Finsupp.single a 1)
  chain' f a := by
    have h := mk_chainDefect f a
    rw [chainDefect, map_sub, map_sum, sub_eq_zero] at h
    simpa only [map_smul] using h

variable {A}

/-- The differential of `a` is the class of the symbol `[a]`. -/
theorem d_def (a : A) : d A a = mk A (Finsupp.single a 1) := rfl

/-- A symbol with a coefficient is the coefficient times the differential. -/
theorem mk_single (a c : A) : mk A (Finsupp.single a c) = c • d A a := by
  rw [← Finsupp.smul_single_one, map_smul, d_def]

/-- The defining relation: the chain rule for every smooth operation. -/
theorem d_op {n : ℕ} (f : SmoothOperation n) (a : Fin n → A) :
    d A (op f a) = ∑ i, op (partialDeriv i f) a • d A (a i) :=
  (d A).chain f a

/-- Additivity is the chain rule for `f = x₁ + x₂`. -/
theorem d_add (a b : A) : d A (a + b) = d A a + d A b := (d A).map_add a b

/-- The Leibniz rule is the chain rule for `f = x₁ x₂`. -/
theorem d_mul (a b : A) : d A (a * b) = a • d A b + b • d A a := (d A).map_mul a b

/-- Real constants are closed: the chain rule for a nullary operation. -/
theorem d_algebraMap (r : ℝ) : d A (algebraMap ℝ A r) = 0 := (d A).map_algebraMap r

/-- A nonpolynomial instance of the defining relation. -/
theorem d_exp (a : A) : d A (exp a) = exp a • d A a := (d A).map_exp a

/-- An induction principle: every element is a finite sum of terms `c • da`. -/
@[elab_as_elim]
theorem induction_on {P : CotangentModule A → Prop} (θ : CotangentModule A) (zero : P 0)
    (add : ∀ x y, P x → P y → P (x + y)) (smul_d : ∀ c a : A, P (c • d A a)) : P θ := by
  obtain ⟨x, rfl⟩ := mk_surjective A θ
  induction x using Finsupp.induction_linear with
  | zero => simpa using zero
  | add x y hx hy => simpa only [map_add] using add _ _ hx hy
  | single a c => simpa only [mk_single] using smul_d c a

/-- The differentials span the cotangent module. -/
theorem span_range_d : Submodule.span A (Set.range (d A)) = ⊤ := by
  rw [eq_top_iff]
  rintro θ -
  induction θ using induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | smul_d c a => exact Submodule.smul_mem _ c (Submodule.subset_span ⟨a, rfl⟩)

end Construction

section FreeLift

variable {A B N : Type*} [CommRing A] [Ring B] [AddCommGroup N] [Module B N]

/-- The map on the free module `Σ cₐ [a] ↦ Σ σ(cₐ) • D a`, semilinear over `σ`. -/
def freeLift (σ : A →+* B) (D : A → N) : (A →₀ A) →ₛₗ[σ] N where
  toFun x := x.sum fun a c => σ c • D a
  map_add' x y := Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul])
  map_smul' c x := by
    rw [Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.smul_sum]
    simp only [smul_eq_mul, map_mul, mul_smul]

/-- The free lift on a single symbol. -/
theorem freeLift_single (σ : A →+* B) (D : A → N) (a c : A) :
    freeLift σ D (Finsupp.single a c) = σ c • D a := by
  change (Finsupp.single a c).sum (fun a c => σ c • D a) = σ c • D a
  exact Finsupp.sum_single_index (by simp)

end FreeLift

section Lift

variable {A : Type u} [CommRing A] [Algebra ℝ A] [SmoothRing A]
variable {B N : Type*} [Ring B] [AddCommGroup N] [Module B N]

/-- A function satisfying the chain rule twisted by a ring morphism `σ` factors
through the cotangent module as a `σ`-semilinear map. -/
def liftₛₗ (σ : A →+* B) (D : A → N)
    (hD : ∀ {n : ℕ} (f : SmoothOperation n) (a : Fin n → A),
      D (op f a) = ∑ i, σ (op (partialDeriv i f) a) • D (a i)) :
    CotangentModule A →ₛₗ[σ] N :=
  (relations A).liftQ (freeLift σ D) (Submodule.span_le.mpr (by
    rintro _ ⟨n, f, a, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, chainDefect, map_sub, map_sum,
      LinearMap.map_smulₛₗ, freeLift_single, map_one, one_smul, hD, sub_self]))

/-- The semilinear lift sends `da` to `D a`. -/
@[simp] theorem liftₛₗ_d (σ : A →+* B) (D : A → N)
    (hD : ∀ {n : ℕ} (f : SmoothOperation n) (a : Fin n → A),
      D (op f a) = ∑ i, σ (op (partialDeriv i f) a) • D (a i)) (a : A) :
    liftₛₗ σ D hD (d A a) = D a := by
  change freeLift σ D (Finsupp.single a 1) = D a
  rw [freeLift_single, map_one, one_smul]

/-- Semilinear maps out of the cotangent module agree when they agree on the
differentials. -/
theorem hom_ext {σ : A →+* B} {φ ψ : CotangentModule A →ₛₗ[σ] N}
    (h : ∀ a, φ (d A a) = ψ (d A a)) : φ = ψ := by
  refine LinearMap.ext fun θ => ?_
  induction θ using induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul_d c a => simp only [LinearMap.map_smulₛₗ, h a]

variable {M : Type*} [AddCommGroup M] [Module A M]

/-- The linear map out of the cotangent module induced by a derivation. -/
def lift (D : SmoothDerivation A M) : CotangentModule A →ₗ[A] M :=
  liftₛₗ (RingHom.id A) D (fun f a => by simpa only [RingHom.id_apply] using D.chain f a)

/-- The induced linear map sends `da` to `D a`. -/
@[simp] theorem lift_d (D : SmoothDerivation A M) (a : A) : lift D (d A a) = D a :=
  liftₛₗ_d _ _ _ a

/-- The universal property: derivations into `M` are the linear maps `Ω_A → M`,
by composition with the universal derivation. -/
def liftEquiv : SmoothDerivation A M ≃ₗ[A] (CotangentModule A →ₗ[A] M) where
  toFun := lift
  map_add' D E := hom_ext fun a => by
    simp only [lift_d, SmoothDerivation.add_apply, LinearMap.add_apply]
  map_smul' c D := hom_ext fun a => by
    simp only [lift_d, SmoothDerivation.smul_apply, LinearMap.smul_apply, RingHom.id_apply]
  invFun φ := (d A).compLinearMap φ
  left_inv D := SmoothDerivation.ext fun a => lift_d D a
  right_inv φ := hom_ext fun a => lift_d _ a

/-- The universal property sends a derivation to its induced linear map. -/
@[simp] theorem liftEquiv_apply (D : SmoothDerivation A M) : liftEquiv D = lift D := rfl

/-- The inverse of the universal property composes with the universal derivation. -/
@[simp] theorem liftEquiv_symm_apply (φ : CotangentModule A →ₗ[A] M) (a : A) :
    liftEquiv.symm φ a = φ (d A a) := rfl

/-- Uniqueness in the universal property. -/
theorem lift_unique (D : SmoothDerivation A M) (φ : CotangentModule A →ₗ[A] M)
    (h : ∀ a, φ (d A a) = D a) : φ = lift D :=
  hom_ext fun a => by rw [h, lift_d]

end Lift

section Map

variable {A B C : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]
  [CommRing B] [Algebra ℝ B] [SmoothRing B] [CommRing C] [Algebra ℝ C] [SmoothRing C]

/-- The pullback of differentials along a morphism, `c • da ↦ φ c • d(φ a)`.
It is semilinear over `φ`. -/
def map (φ : SmoothRingHom A B) :
    CotangentModule A →ₛₗ[φ.toAlgHom.toRingHom] CotangentModule B :=
  liftₛₗ φ.toAlgHom.toRingHom (fun a => d B (φ a)) (fun f a => by
    rw [φ.map_op, d_op]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, SmoothRingHom.toAlgHom_apply,
      SmoothRingHom.map_op])

/-- Pullback of a differential: `φ^*(da) = d(φ a)`. -/
@[simp] theorem map_d (φ : SmoothRingHom A B) (a : A) : map φ (d A a) = d B (φ a) :=
  liftₛₗ_d _ _ _ a

/-- The pullback is semilinear over the morphism. -/
theorem map_apply_smul (φ : SmoothRingHom A B) (c : A) (θ : CotangentModule A) :
    map φ (c • θ) = φ c • map φ θ :=
  LinearMap.map_smulₛₗ (map φ) c θ

/-- Pullback along the identity is the identity. -/
@[simp] theorem map_id_apply (θ : CotangentModule A) : map (SmoothRingHom.id A) θ = θ := by
  induction θ using induction_on with
  | zero => exact _root_.map_zero _
  | add x y hx hy => rw [map_add, hx, hy]
  | smul_d c a => rw [map_apply_smul, map_d, SmoothRingHom.id_apply, SmoothRingHom.id_apply]

/-- Pullback is functorial. -/
theorem map_comp_apply (ψ : SmoothRingHom B C) (φ : SmoothRingHom A B)
    (θ : CotangentModule A) : map (ψ.comp φ) θ = map ψ (map φ θ) := by
  induction θ using induction_on with
  | zero => rw [_root_.map_zero, _root_.map_zero, _root_.map_zero]
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
  | smul_d c a =>
    rw [map_apply_smul, map_d, map_apply_smul, map_d, map_apply_smul, map_d,
      SmoothRingHom.comp_apply, SmoothRingHom.comp_apply]

/-- Pullback is functorial, as an identity of functions. -/
theorem map_comp (ψ : SmoothRingHom B C) (φ : SmoothRingHom A B) :
    ⇑(map (ψ.comp φ)) = ⇑(map ψ) ∘ ⇑(map φ) :=
  funext (map_comp_apply ψ φ)

end Map

section Coordinates

variable (n : ℕ)

/-- All partial derivatives at once, as a derivation of `C∞(ℝⁿ)` into `n`-tuples. -/
def gradient : SmoothDerivation (SmoothOperation n) (Fin n → SmoothOperation n) where
  toFun f i := partialDeriv i f
  chain' f g := by
    funext j
    simp only [function_op, partialDeriv_comp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The components of the gradient are the partial derivatives. -/
@[simp] theorem gradient_apply (f : SmoothOperation n) (i : Fin n) :
    gradient n f i = partialDeriv i f := rfl

/-- The coefficients of a covector of `C∞(ℝⁿ)` in the coordinate differentials. -/
def coordinates : CotangentModule (SmoothOperation n) →ₗ[SmoothOperation n]
    (Fin n → SmoothOperation n) :=
  lift (gradient n)

variable {n}

/-- The coefficients of `df` are the partial derivatives of `f`. -/
@[simp] theorem coordinates_d (f : SmoothOperation n) :
    coordinates n (d _ f) = fun i => partialDeriv i f :=
  lift_d _ f

/-- The differential of a smooth function is the sum of its partial derivatives
times the coordinate differentials. -/
theorem d_eq_sum (f : SmoothOperation n) :
    d (SmoothOperation n) f = ∑ i, partialDeriv i f • d (SmoothOperation n) (proj i) :=
  (d _).apply_eq_sum_partialDeriv f

variable (n)

/-- The combination of the coordinate differentials with given coefficients. -/
def ofCoordinates : (Fin n → SmoothOperation n) →ₗ[SmoothOperation n]
    CotangentModule (SmoothOperation n) :=
  ∑ i, (LinearMap.proj i).smulRight (d (SmoothOperation n) (proj i))

variable {n}

/-- The combination with coefficients `c` is `Σᵢ cᵢ • dxᵢ`. -/
@[simp] theorem ofCoordinates_apply (c : Fin n → SmoothOperation n) :
    ofCoordinates n c = ∑ i, c i • d (SmoothOperation n) (proj i) := by
  simp [ofCoordinates, LinearMap.sum_apply]

variable (n)

/-- The cotangent module of `C∞(ℝⁿ)` is free on the coordinate differentials. -/
def coordinateEquiv : CotangentModule (SmoothOperation n) ≃ₗ[SmoothOperation n]
    (Fin n → SmoothOperation n) :=
  LinearEquiv.ofLinearMap (coordinates n) (ofCoordinates n)
    (LinearMap.ext fun c => by
      funext j
      simp [partialDeriv_proj])
    (hom_ext fun f => by
      simp only [LinearMap.comp_apply, coordinates_d, ofCoordinates_apply, LinearMap.id_apply]
      exact (d_eq_sum f).symm)

/-- The basis `dx₁, …, dxₙ` of the cotangent module of `C∞(ℝⁿ)`. -/
def coordinateBasis :
    Module.Basis (Fin n) (SmoothOperation n) (CotangentModule (SmoothOperation n)) :=
  Module.Basis.ofEquivFun (coordinateEquiv n)

variable {n}

/-- The basis vectors are the coordinate differentials `dxᵢ`. -/
@[simp] theorem coordinateBasis_apply (i : Fin n) :
    coordinateBasis n i = d (SmoothOperation n) (proj i) := by
  classical
  rw [coordinateBasis, Module.Basis.coe_ofEquivFun]
  change ofCoordinates n (Pi.single i 1) = _
  rw [ofCoordinates_apply]
  simp [Pi.single_apply]

/-- The coordinates in the basis are the coefficients. -/
@[simp] theorem coordinateBasis_repr (θ : CotangentModule (SmoothOperation n)) (i : Fin n) :
    (coordinateBasis n).repr θ i = coordinates n θ i := rfl

/-- The coefficients of `df` in the basis are the partial derivatives of `f`. -/
theorem coordinateBasis_repr_d (f : SmoothOperation n) (i : Fin n) :
    (coordinateBasis n).repr (d _ f) i = partialDeriv i f := by
  simp

/-- Every covector is the combination of the coordinate differentials with its
coefficients. -/
theorem eq_sum_coordinates (θ : CotangentModule (SmoothOperation n)) :
    θ = ∑ i, coordinates n θ i • d (SmoothOperation n) (proj i) := by
  have h := (coordinateEquiv n).symm_apply_apply θ
  exact h.symm.trans (ofCoordinates_apply _)

end Coordinates

section Evaluation

variable {n m : ℕ}

/-- The chain rule of ordinary calculus at a point, in the form of the defining
relation twisted by evaluation. -/
theorem fderiv_op (f : SmoothOperation m) (g : Fin m → SmoothOperation n) (x : Fin n → ℝ) :
    fderiv ℝ (⇑(op f g : SmoothOperation n)) x =
      ∑ i, (eval x).toAlgHom.toRingHom (op (partialDeriv i f) g) • fderiv ℝ (g i) x := by
  ext v
  have h := directionalEvaluation_op f g x v
  simp only [directionalEvaluation, eval_apply] at h
  rw [h, fderiv_apply_eq_sum_partialDeriv]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    SmoothRingHom.toAlgHom_apply, eval_apply, function_op, comp_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Evaluation of covectors at a point: `c • df ↦ c(x) • Df(x)`, a semilinear map
into the dual of the tangent space, over evaluation at `x`. -/
def evalAt (x : Fin n → ℝ) :
    CotangentModule (SmoothOperation n) →ₛₗ[(eval x).toAlgHom.toRingHom]
      ((Fin n → ℝ) →L[ℝ] ℝ) :=
  liftₛₗ _ (fun f => fderiv ℝ f x) (fun f g => fderiv_op f g x)

/-- The value of a differential at a point is the Fréchet derivative. -/
@[simp] theorem evalAt_d (x : Fin n → ℝ) (f : SmoothOperation n) :
    evalAt x (d _ f) = fderiv ℝ f x :=
  liftₛₗ_d _ _ _ f

/-- Evaluation at a point is semilinear over evaluation of the coefficients. -/
@[simp] theorem evalAt_smul (x : Fin n → ℝ) (c : SmoothOperation n)
    (θ : CotangentModule (SmoothOperation n)) : evalAt x (c • θ) = c x • evalAt x θ :=
  LinearMap.map_smulₛₗ (evalAt x) c θ

/-- The coordinate differentials evaluate to the coordinate functionals. -/
theorem evalAt_d_proj (x : Fin n → ℝ) (i : Fin n) :
    evalAt x (d _ (proj i)) = ContinuousLinearMap.proj i := by
  rw [evalAt_d]
  exact (hasFDerivAt_apply i x).fderiv

/-- A covector at a point, in coordinates. -/
theorem evalAt_eq_sum (x : Fin n → ℝ) (θ : CotangentModule (SmoothOperation n)) :
    evalAt x θ = ∑ i, coordinates n θ i x • ContinuousLinearMap.proj i := by
  conv_lhs => rw [eq_sum_coordinates θ]
  simp only [map_sum, evalAt_smul, evalAt_d_proj]

/-- A covector at a point applied to a tangent vector, in coordinates. -/
theorem evalAt_apply (x : Fin n → ℝ) (θ : CotangentModule (SmoothOperation n))
    (v : Fin n → ℝ) : evalAt x θ v = ∑ i, coordinates n θ i x * v i := by
  rw [evalAt_eq_sum]
  simp

/-- The `i`-th coefficient at `x` is the value on the `i`-th coordinate vector. -/
theorem evalAt_single (x : Fin n → ℝ) (θ : CotangentModule (SmoothOperation n)) (i : Fin n) :
    evalAt x θ (Pi.single i 1) = coordinates n θ i x := by
  classical
  rw [evalAt_apply]
  simp [Pi.single_apply]

/-- A covector at a point as the differential of a linear function: every
element of the dual is attained. -/
theorem evalAt_d_ofContinuousLinearMap (x : Fin n → ℝ) (α : (Fin n → ℝ) →L[ℝ] ℝ) :
    evalAt x (d _ (ofContDiff α α.contDiff)) = α := by
  rw [evalAt_d]
  exact α.fderiv

/-- Evaluation at a point is onto the dual of the tangent space. -/
theorem evalAt_surjective (x : Fin n → ℝ) : Function.Surjective (evalAt x) :=
  fun α => ⟨_, evalAt_d_ofContinuousLinearMap x α⟩

/-- The kernel of evaluation at `x` is `𝔪ₓ Ω`, for the ideal `𝔪ₓ` of functions
vanishing at `x`. With surjectivity, the fibre `Ω / 𝔪ₓ Ω` is the dual of the
tangent space. -/
theorem ker_evalAt (x : Fin n → ℝ) :
    LinearMap.ker (evalAt x) = RingHom.ker (eval x).toAlgHom.toRingHom • ⊤ := by
  apply le_antisymm
  · intro θ hθ
    rw [LinearMap.mem_ker] at hθ
    rw [eq_sum_coordinates θ]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, SmoothRingHom.toAlgHom_apply,
      eval_apply, ← evalAt_single, hθ]
    rfl
  · refine Submodule.smul_le.mpr fun c hc θ _ => ?_
    rw [LinearMap.mem_ker, LinearMap.map_smulₛₗ, RingHom.mem_ker.mp hc, zero_smul]

/-- A covector field on `ℝⁿ` is determined by its values at all points. -/
theorem ext_evalAt {θ θ' : CotangentModule (SmoothOperation n)}
    (h : ∀ x, evalAt x θ = evalAt x θ') : θ = θ' :=
  (coordinateEquiv n).injective <| funext fun i => SmoothOperation.ext fun x => by
    change coordinates n θ i x = coordinates n θ' i x
    rw [← evalAt_single, ← evalAt_single, h]

/-- Pulling a covector back along a smooth map and evaluating it at `x` is the
transpose of the derivative applied to its value at the image point. -/
theorem evalAt_map_pullback (g : Fin n → SmoothOperation m) (x : Fin m → ℝ)
    (θ : CotangentModule (SmoothOperation n)) :
    evalAt x (map (pullback g) θ) =
      (evalAt (fun i => g i x) θ).comp (fderiv ℝ (fun y i => g i y) x) := by
  induction θ using induction_on with
  | zero => rw [_root_.map_zero, _root_.map_zero, _root_.map_zero, ContinuousLinearMap.zero_comp]
  | add a b ha hb => rw [_root_.map_add, _root_.map_add, ha, hb, _root_.map_add,
      ContinuousLinearMap.add_comp]
  | smul_d c f =>
    rw [map_apply_smul, map_d, evalAt_smul, evalAt_smul, evalAt_d, evalAt_d,
      ContinuousLinearMap.smul_comp, pullback_apply, pullback_apply, comp_apply]
    congr 1
    exact fderiv_comp x (f.differentiableAt _)
      (differentiableAt_pi.mpr fun i => (g i).differentiableAt x)

/-- The pullback of functions along a continuous linear map `ℝᵐ → ℝⁿ`. -/
def linearPullback (T : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) :
    SmoothRingHom (SmoothOperation n) (SmoothOperation m) :=
  pullback fun i => ofContDiff (fun y => T y i)
    ((contDiff_apply ℝ (fun _ => ℝ) i).comp T.contDiff)

/-- The linear pullback of `f` is `f ∘ T`. -/
@[simp] theorem linearPullback_apply (T : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ))
    (f : SmoothOperation n) (y : Fin m → ℝ) : linearPullback T f y = f (T y) := rfl

/-- Pullback of covectors along a linear map is the dual (transpose) action. -/
theorem evalAt_map_linearPullback (T : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ))
    (x : Fin m → ℝ) (θ : CotangentModule (SmoothOperation n)) :
    evalAt x (map (linearPullback T) θ) = (evalAt (T x) θ).comp T := by
  rw [linearPullback, evalAt_map_pullback]
  exact congrArg _ T.fderiv

end Evaluation

section Free

open FreeSmoothRing

variable (ι : Type*)

/-- The differentials of the generators of a free ring are linearly independent:
the coordinate vector fields detect each coefficient. -/
theorem linearIndependent_d_generator :
    LinearIndependent (FreeSmoothRing ι) fun i => d (FreeSmoothRing ι) (generator i) := by
  classical
  rw [linearIndependent_iff']
  intro s c hc i hi
  have h := congrArg (lift (partialDerivation i)) hc
  simp only [map_sum, map_smul, lift_d, partialDerivation_generator, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', map_zero] at h
  simpa [hi] using h

/-- The differentials of the generators of a free ring span its cotangent module:
the defining relation expands the differential of a presented element. -/
theorem span_range_d_generator :
    Submodule.span (FreeSmoothRing ι) (Set.range fun i => d (FreeSmoothRing ι) (generator i)) =
      ⊤ := by
  rw [eq_top_iff]
  rintro θ -
  induction θ using induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | smul_d c s =>
    refine Submodule.smul_mem _ c ?_
    rw [presentation_eq s, d_op]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- The basis `d(generator i)` of the cotangent module of a free ring. -/
def basisFree : Module.Basis ι (FreeSmoothRing ι) (CotangentModule (FreeSmoothRing ι)) :=
  Module.Basis.mk (linearIndependent_d_generator ι) (span_range_d_generator ι).ge

variable {ι}

/-- The basis vectors are the differentials of the generators. -/
@[simp] theorem basisFree_apply (i : ι) : basisFree ι i = d (FreeSmoothRing ι) (generator i) :=
  Module.Basis.mk_apply _ _ i

/-- The coefficients of a free covector are the values of the coordinate vector
fields. -/
theorem basisFree_coord [DecidableEq ι] (c : ι) :
    (basisFree ι).coord c = lift (partialDerivation c) :=
  (basisFree ι).ext fun i => by
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, basisFree_apply, lift_d,
      partialDerivation_generator, Finsupp.single_apply]

/-- The coefficients of `ds` are the coordinate derivatives of `s`. -/
theorem basisFree_repr_d [DecidableEq ι] (s : FreeSmoothRing ι) (c : ι) :
    (basisFree ι).repr (d _ s) c = partialDerivation c s := by
  rw [← Module.Basis.coord_apply, basisFree_coord, lift_d]

/-- On finitely many generators, `ds = Σᵢ ∂ᵢs • d(generator i)`. -/
theorem d_eq_sum_generator [Fintype ι] [DecidableEq ι] (s : FreeSmoothRing ι) :
    d (FreeSmoothRing ι) s =
      ∑ i, partialDerivation i s • d (FreeSmoothRing ι) (generator i) := by
  conv_lhs => rw [← (basisFree ι).sum_repr (d _ s)]
  simp only [basisFree_repr_d, basisFree_apply]

end Free

end CotangentModule

end ProjectAinos.SmoothAlgebra
