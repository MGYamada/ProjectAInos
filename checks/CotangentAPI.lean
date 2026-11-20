/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothAlgebra.CotangentModule
import ProjectAinos.SpecialRelativity.Cotangent

/-! Public consumers of the universal cotangent module (Landau–Lifshitz §6, SR-F2): the module
`Ω_A` of a C∞-ring with the universal derivation and its full chain rule, the universal property,
functoriality along smooth ring homomorphisms, the bases `dxᵢ` of free rings and of `C∞(ℝⁿ)`,
evaluation at a point with its kernel and its surjectivity, pullback as the transpose of the
derivative; and the comparison with covectors of space-time through `flat` and `sharp`, with
Lorentz covariance. Default elaborator options are intentional: these checks must not rely on the
implementation's transparency settings. Every statement is pinned with its type. -/

noncomputable section

section CotangentModule

namespace ProjectAinos.SmoothAlgebra

open SmoothRing SmoothOperation

namespace SmoothDerivation

variable {A M N : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

example (D : SmoothDerivation A M) (φ : M →ₗ[A] N) :
    SmoothDerivation A N :=
  compLinearMap D φ

example (D : SmoothDerivation A M) (φ : M →ₗ[A] N) (a : A) :
    D.compLinearMap φ a = φ (D a) :=
  compLinearMap_apply D φ a

end SmoothDerivation

namespace CotangentModule

section Relations

variable {A : Type u} [CommRing A] [Algebra ℝ A] [SmoothRing A]

example {n : ℕ} (f : SmoothOperation n) (a : Fin n → A) :
    A →₀ A :=
  chainDefect f a

example :
    Submodule A (A →₀ A) :=
  relations A

example {n : ℕ} (f : SmoothOperation n) (a : Fin n → A) :
    chainDefect f a ∈ relations A :=
  chainDefect_mem f a

end Relations

end CotangentModule

example (A : Type u) [CommRing A] [Algebra ℝ A] [SmoothRing A] :
    Type u :=
  CotangentModule A

namespace CotangentModule

section Construction

variable (A : Type u) [CommRing A] [Algebra ℝ A] [SmoothRing A]

example :
    (A →₀ A) →ₗ[A] CotangentModule A :=
  mk A

example :
    Function.Surjective (mk A) :=
  mk_surjective A

example {n : ℕ} (f : SmoothOperation n) (a : Fin n → A) :
    mk A (chainDefect f a) = 0 :=
  mk_chainDefect f a

example :
    SmoothDerivation A (CotangentModule A) :=
  d A

variable {A}

example (a : A) :
    d A a = mk A (Finsupp.single a 1) :=
  d_def a

example (a c : A) :
    mk A (Finsupp.single a c) = c • d A a :=
  mk_single a c

example {n : ℕ} (f : SmoothOperation n) (a : Fin n → A) :
    d A (op f a) = ∑ i, op (partialDeriv i f) a • d A (a i) :=
  d_op f a

example (a b : A) :
    d A (a + b) = d A a + d A b :=
  d_add a b

example (a b : A) :
    d A (a * b) = a • d A b + b • d A a :=
  d_mul a b

example (r : ℝ) :
    d A (algebraMap ℝ A r) = 0 :=
  d_algebraMap r

example (a : A) :
    d A (exp a) = exp a • d A a :=
  d_exp a

example {P : CotangentModule A → Prop} (θ : CotangentModule A) (zero : P 0)
    (add : ∀ x y, P x → P y → P (x + y)) (smul_d : ∀ c a : A, P (c • d A a)) :
    P θ :=
  induction_on θ zero add smul_d

example :
    Submodule.span A (Set.range (d A)) = ⊤ :=
  span_range_d

end Construction

section FreeLift

variable {A B N : Type*} [CommRing A] [Ring B] [AddCommGroup N] [Module B N]

example (σ : A →+* B) (D : A → N) :
    (A →₀ A) →ₛₗ[σ] N :=
  freeLift σ D

example (σ : A →+* B) (D : A → N) (a c : A) :
    freeLift σ D (Finsupp.single a c) = σ c • D a :=
  freeLift_single σ D a c

end FreeLift

section Lift

variable {A : Type u} [CommRing A] [Algebra ℝ A] [SmoothRing A]

variable {B N : Type*} [Ring B] [AddCommGroup N] [Module B N]

example (σ : A →+* B) (D : A → N)
    (hD : ∀ {n : ℕ} (f : SmoothOperation n) (a : Fin n → A),
      D (op f a) = ∑ i, σ (op (partialDeriv i f) a) • D (a i)) :
    CotangentModule A →ₛₗ[σ] N :=
  liftₛₗ σ D hD

example (σ : A →+* B) (D : A → N)
    (hD : ∀ {n : ℕ} (f : SmoothOperation n) (a : Fin n → A),
      D (op f a) = ∑ i, σ (op (partialDeriv i f) a) • D (a i))
    (a : A) :
    liftₛₗ σ D hD (d A a) = D a :=
  liftₛₗ_d σ D hD a

example {σ : A →+* B} {φ ψ : CotangentModule A →ₛₗ[σ] N} (h : ∀ a, φ (d A a) = ψ (d A a)) :
    φ = ψ :=
  hom_ext h

variable {M : Type*} [AddCommGroup M] [Module A M]

example (D : SmoothDerivation A M) :
    CotangentModule A →ₗ[A] M :=
  lift D

example (D : SmoothDerivation A M) (a : A) :
    lift D (d A a) = D a :=
  lift_d D a

example :
    SmoothDerivation A M ≃ₗ[A] (CotangentModule A →ₗ[A] M) :=
  liftEquiv

example (D : SmoothDerivation A M) :
    liftEquiv D = lift D :=
  liftEquiv_apply D

example (φ : CotangentModule A →ₗ[A] M) (a : A) :
    liftEquiv.symm φ a = φ (d A a) :=
  liftEquiv_symm_apply φ a

example (D : SmoothDerivation A M) (φ : CotangentModule A →ₗ[A] M) (h : ∀ a, φ (d A a) = D a) :
    φ = lift D :=
  lift_unique D φ h

end Lift

section Map

variable {A B C : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]
  [CommRing B] [Algebra ℝ B] [SmoothRing B] [CommRing C] [Algebra ℝ C] [SmoothRing C]

example (φ : SmoothRingHom A B) :
    CotangentModule A →ₛₗ[φ.toAlgHom.toRingHom] CotangentModule B :=
  map φ

example (φ : SmoothRingHom A B) (a : A) :
    map φ (d A a) = d B (φ a) :=
  map_d φ a

example (φ : SmoothRingHom A B) (c : A) (θ : CotangentModule A) :
    map φ (c • θ) = φ c • map φ θ :=
  map_apply_smul φ c θ

example (θ : CotangentModule A) :
    map (SmoothRingHom.id A) θ = θ :=
  map_id_apply θ

example (ψ : SmoothRingHom B C) (φ : SmoothRingHom A B) (θ : CotangentModule A) :
    map (ψ.comp φ) θ = map ψ (map φ θ) :=
  map_comp_apply ψ φ θ

example (ψ : SmoothRingHom B C) (φ : SmoothRingHom A B) :
    ⇑(map (ψ.comp φ)) = ⇑(map ψ) ∘ ⇑(map φ) :=
  map_comp ψ φ

end Map

section Coordinates

variable (n : ℕ)

example :
    SmoothDerivation (SmoothOperation n) (Fin n → SmoothOperation n) :=
  gradient n

example (f : SmoothOperation n) (i : Fin n) :
    gradient n f i = partialDeriv i f :=
  gradient_apply n f i

example :
    CotangentModule (SmoothOperation n) →ₗ[SmoothOperation n]
    (Fin n → SmoothOperation n) :=
  coordinates n

variable {n}

example (f : SmoothOperation n) :
    coordinates n (d _ f) = fun i => partialDeriv i f :=
  coordinates_d f

example (f : SmoothOperation n) :
    d (SmoothOperation n) f = ∑ i, partialDeriv i f • d (SmoothOperation n) (proj i) :=
  d_eq_sum f

variable (n)

example :
    (Fin n → SmoothOperation n) →ₗ[SmoothOperation n]
    CotangentModule (SmoothOperation n) :=
  ofCoordinates n

variable {n}

example (c : Fin n → SmoothOperation n) :
    ofCoordinates n c = ∑ i, c i • d (SmoothOperation n) (proj i) :=
  ofCoordinates_apply c

variable (n)

example :
    CotangentModule (SmoothOperation n) ≃ₗ[SmoothOperation n]
    (Fin n → SmoothOperation n) :=
  coordinateEquiv n

example :
    Module.Basis (Fin n) (SmoothOperation n) (CotangentModule (SmoothOperation n)) :=
  coordinateBasis n

variable {n}

example (i : Fin n) :
    coordinateBasis n i = d (SmoothOperation n) (proj i) :=
  coordinateBasis_apply i

example (θ : CotangentModule (SmoothOperation n)) (i : Fin n) :
    (coordinateBasis n).repr θ i = coordinates n θ i :=
  coordinateBasis_repr θ i

example (f : SmoothOperation n) (i : Fin n) :
    (coordinateBasis n).repr (d _ f) i = partialDeriv i f :=
  coordinateBasis_repr_d f i

example (θ : CotangentModule (SmoothOperation n)) :
    θ = ∑ i, coordinates n θ i • d (SmoothOperation n) (proj i) :=
  eq_sum_coordinates θ

end Coordinates

section Evaluation

variable {n m : ℕ}

example (f : SmoothOperation m) (g : Fin m → SmoothOperation n) (x : Fin n → ℝ) :
    fderiv ℝ (⇑(op f g : SmoothOperation n)) x =
      ∑ i, (eval x).toAlgHom.toRingHom (op (partialDeriv i f) g) • fderiv ℝ (g i) x :=
  fderiv_op f g x

example (x : Fin n → ℝ) :
    CotangentModule (SmoothOperation n) →ₛₗ[(eval x).toAlgHom.toRingHom]
      ((Fin n → ℝ) →L[ℝ] ℝ) :=
  evalAt x

example (x : Fin n → ℝ) (f : SmoothOperation n) :
    evalAt x (d _ f) = fderiv ℝ f x :=
  evalAt_d x f

example (x : Fin n → ℝ) (c : SmoothOperation n) (θ : CotangentModule (SmoothOperation n)) :
    evalAt x (c • θ) = c x • evalAt x θ :=
  evalAt_smul x c θ

example (x : Fin n → ℝ) (i : Fin n) :
    evalAt x (d _ (proj i)) = ContinuousLinearMap.proj i :=
  evalAt_d_proj x i

example (x : Fin n → ℝ) (θ : CotangentModule (SmoothOperation n)) :
    evalAt x θ = ∑ i, coordinates n θ i x • ContinuousLinearMap.proj i :=
  evalAt_eq_sum x θ

example (x : Fin n → ℝ) (θ : CotangentModule (SmoothOperation n)) (v : Fin n → ℝ) :
    evalAt x θ v = ∑ i, coordinates n θ i x * v i :=
  evalAt_apply x θ v

example (x : Fin n → ℝ) (θ : CotangentModule (SmoothOperation n)) (i : Fin n) :
    evalAt x θ (Pi.single i 1) = coordinates n θ i x :=
  evalAt_single x θ i

example (x : Fin n → ℝ) (α : (Fin n → ℝ) →L[ℝ] ℝ) :
    evalAt x (d _ (ofContDiff α α.contDiff)) = α :=
  evalAt_d_ofContinuousLinearMap x α

example (x : Fin n → ℝ) :
    Function.Surjective (evalAt x) :=
  evalAt_surjective x

example (x : Fin n → ℝ) :
    LinearMap.ker (evalAt x) = RingHom.ker (eval x).toAlgHom.toRingHom • ⊤ :=
  ker_evalAt x

example {θ θ' : CotangentModule (SmoothOperation n)} (h : ∀ x, evalAt x θ = evalAt x θ') :
    θ = θ' :=
  ext_evalAt h

example (g : Fin n → SmoothOperation m) (x : Fin m → ℝ) (θ : CotangentModule (SmoothOperation n)) :
    evalAt x (map (pullback g) θ) =
      (evalAt (fun i => g i x) θ).comp (fderiv ℝ (fun y i => g i y) x) :=
  evalAt_map_pullback g x θ

example (T : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) :
    SmoothRingHom (SmoothOperation n) (SmoothOperation m) :=
  linearPullback T

example (T : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) (f : SmoothOperation n) (y : Fin m → ℝ) :
    linearPullback T f y = f (T y) :=
  linearPullback_apply T f y

example (T : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) (x : Fin m → ℝ)
    (θ : CotangentModule (SmoothOperation n)) :
    evalAt x (map (linearPullback T) θ) = (evalAt (T x) θ).comp T :=
  evalAt_map_linearPullback T x θ

end Evaluation

section Free

open FreeSmoothRing

variable (ι : Type*)

example :
    LinearIndependent (FreeSmoothRing ι) fun i => d (FreeSmoothRing ι) (generator i) :=
  linearIndependent_d_generator ι

example :
    Submodule.span (FreeSmoothRing ι) (Set.range fun i => d (FreeSmoothRing ι) (generator i)) =
      ⊤ :=
  span_range_d_generator ι

example :
    Module.Basis ι (FreeSmoothRing ι) (CotangentModule (FreeSmoothRing ι)) :=
  basisFree ι

variable {ι}

example (i : ι) :
    basisFree ι i = d (FreeSmoothRing ι) (generator i) :=
  basisFree_apply i

example [DecidableEq ι] (c : ι) :
    (basisFree ι).coord c = lift (partialDerivation c) :=
  basisFree_coord c

example [DecidableEq ι] (s : FreeSmoothRing ι) (c : ι) :
    (basisFree ι).repr (d _ s) c = partialDerivation c s :=
  basisFree_repr_d s c

example [Fintype ι] [DecidableEq ι] (s : FreeSmoothRing ι) :
    d (FreeSmoothRing ι) s =
      ∑ i, partialDerivation i s • d (FreeSmoothRing ι) (generator i) :=
  d_eq_sum_generator s

end Free

end CotangentModule

end ProjectAinos.SmoothAlgebra

end CotangentModule

section Cotangent

namespace ProjectAinos.SpecialRelativity

open SmoothAlgebra SmoothAlgebra.SmoothOperation SmoothAlgebra.CotangentModule SmoothGeometry
  SmoothGeometry.Minkowski

variable (σ : LorentzConvention) (d : ℕ)

example :
    (Fin (d + 1) → SmoothOperation (d + 1)) ≃ₗ[SmoothOperation (d + 1)]
    (Fin (d + 1) → SmoothOperation (d + 1)) :=
  lowerIndex σ d

variable {σ d}

example (v : Fin (d + 1) → SmoothOperation (d + 1)) (μ : Fin (d + 1)) :
    lowerIndex σ d v μ = lorentzSign σ μ • v μ :=
  lowerIndex_apply v μ

example (v : Fin (d + 1) → SmoothOperation (d + 1)) (μ : Fin (d + 1)) :
    (lowerIndex σ d).symm v μ = lorentzSign σ μ • v μ :=
  lowerIndex_symm_apply v μ

variable (σ d)

example :
    (Fin (d + 1) → SmoothOperation (d + 1)) ≃ₗ[SmoothOperation (d + 1)]
    CotangentModule (SmoothOperation (d + 1)) :=
  musical σ d

variable {σ d}

example (v : Fin (d + 1) → SmoothOperation (d + 1)) :
    musical σ d v = ∑ μ, (lorentzSign σ μ • v μ) •
      CotangentModule.d (SmoothOperation (d + 1)) (proj μ) :=
  musical_apply v

example (v : Fin (d + 1) → SmoothOperation (d + 1)) :
    coordinates (d + 1) (musical σ d v) = lowerIndex σ d v :=
  coordinates_musical v

example (θ : CotangentModule (SmoothOperation (d + 1))) (μ : Fin (d + 1)) :
    (musical σ d).symm θ μ = lorentzSign σ μ • coordinates (d + 1) θ μ :=
  musical_symm_apply θ μ

example (v : Fin (d + 1) → SmoothOperation (d + 1)) (x : MinkowskiModel d) :
    evalAt x (musical σ d v) = flat σ (fun μ => v μ x) :=
  cotangent_flat v x

example (θ : CotangentModule (SmoothOperation (d + 1))) (x : MinkowskiModel d) :
    sharp σ (evalAt x θ) = fun μ => (musical σ d).symm θ μ x :=
  cotangent_sharp θ x

example (v : Fin (d + 1) → SmoothOperation (d + 1))
    (θ : CotangentModule (SmoothOperation (d + 1))) :
    musical σ d v = θ ↔ ∀ x : MinkowskiModel d, evalAt x θ = flat σ (fun μ => v μ x) :=
  musical_eq_iff v θ

example (L : LorentzGroup d) :
    SmoothRingHom (SmoothOperation (d + 1)) (SmoothOperation (d + 1)) :=
  lorentzFunctionPullback L

example (L : LorentzGroup d) (f : SmoothOperation (d + 1)) (x : MinkowskiModel d) :
    lorentzFunctionPullback L f x = f (L.val x) :=
  lorentzFunctionPullback_apply L f x

example (L : LorentzGroup d) (θ : CotangentModule (SmoothOperation (d + 1)))
    (x : MinkowskiModel d) :
    evalAt x (map (lorentzFunctionPullback L) θ) =
      (evalAt (L.val x) θ).comp
        (LorentzGroup.toContinuousLinearEquiv L : MinkowskiModel d →L[ℝ] MinkowskiModel d) :=
  cotangent_map_lorentz L θ x

example (L : LorentzGroup d) (v : Fin (d + 1) → SmoothOperation (d + 1)) (x : MinkowskiModel d) :
    evalAt x (map (lorentzFunctionPullback L) (musical σ d v)) =
      flat σ (L.val.symm (fun μ => v μ (L.val x))) :=
  cotangent_flat_lorentz L v x

example (L : LorentzGroup d) (v : Fin (d + 1) → SmoothOperation (d + 1)) :
    Fin (d + 1) → SmoothOperation (d + 1) :=
  lorentzPushforward L v

example (L : LorentzGroup d) (v : Fin (d + 1) → SmoothOperation (d + 1)) (x : MinkowskiModel d) :
    (fun μ => lorentzPushforward L v μ x) = L.val.symm (fun ν => v ν (L.val x)) :=
  lorentzPushforward_apply L v x

example (L : LorentzGroup d) (v : Fin (d + 1) → SmoothOperation (d + 1)) :
    map (lorentzFunctionPullback L) (musical σ d v) = musical σ d (lorentzPushforward L v) :=
  map_lorentzFunctionPullback_musical L v

example (v : Fin 4 → SmoothOperation 4) (x w : Spacetime) :
    evalAt x (musical .timeNegative 3 v) w = metric (fun μ => v μ x) w :=
  cotangent_metric v x w

end ProjectAinos.SpecialRelativity

end Cotangent
