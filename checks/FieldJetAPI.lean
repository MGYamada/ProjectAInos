/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.Variational.FieldJet.Noether
import ProjectAinos.Variational.FieldJet.Standard

/-! Public consumers of the jet rings of fields: iterated partial derivatives of a smooth
function, the total derivatives and their commutation, the Euler operators with the statement
that a total derivative is a null Lagrangian, Noether's identities for a Lagrangian of the
first order with the canonical stress tensor, and the standard jet ring with the prolongation
of a field.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section

namespace ProjectAinos.SmoothAlgebra.SmoothOperation

variable {n : ℕ}

example (f : SmoothOperation n) : iterPartialDeriv 0 f = f :=
  iterPartialDeriv_zero f

example (i : Fin n) (K : Multiset (Fin n)) (f : SmoothOperation n) :
    iterPartialDeriv (i ::ₘ K) f = partialDeriv i (iterPartialDeriv K f) :=
  iterPartialDeriv_cons i K f

end ProjectAinos.SmoothAlgebra.SmoothOperation

namespace ProjectAinos.Variational

open SmoothAlgebra SmoothRing SmoothOperation

namespace FieldJetRing

variable {ι κ J : Type*} [CommRing J] [Algebra ℝ J] [SmoothRing J] (R : FieldJetRing ι κ J)

variable {R}

example {F : J} {S T : Finset (Multiset ι)} (h : R.SupportIn F S) (hST : S ⊆ T) :
    R.SupportIn F T :=
  SupportIn.mono h hST

example {F : J} {S : Finset (Multiset ι)} (h : R.SupportIn F S) (b : κ)
    (L : Multiset ι) : R.SupportIn (R.d b L F) S :=
  SupportIn.d h b L

example {F : J} {S : Finset (Multiset ι)} (h : R.SupportIn F S) (μ : ι) :
    R.SupportIn (R.dx μ F) S :=
  SupportIn.dx h μ

example {F G : J} {S : Finset (Multiset ι)} (hF : R.SupportIn F S)
    (hG : R.SupportIn G S) : R.SupportIn (F + G) S :=
  SupportIn.add hF hG

example {F G : J} {S : Finset (Multiset ι)} (hF : R.SupportIn F S)
    (hG : R.SupportIn G S) : R.SupportIn (F * G) S :=
  SupportIn.mul hF hG

example {α : Type*} {s : Finset α} {F : α → J} {S : Finset (Multiset ι)}
    (h : ∀ c ∈ s, R.SupportIn (F c) S) : R.SupportIn (∑ c ∈ s, F c) S :=
  SupportIn.sum h

example {n : ℕ} {x : Fin n → J} {S : Finset (Multiset ι)}
    (h : ∀ j, R.SupportIn (x j) S) (f : SmoothOperation n) : R.SupportIn (op f x) S :=
  SupportIn.op h f

example [DecidableEq ι] (a : κ) (K : Multiset ι) : R.SupportIn (R.u a K) {K} :=
  supportIn_u a K

variable (R)

example (F : J) : ∃ S, R.SupportIn F S :=
  exists_supportIn R F

example [DecidableEq ι] {n : ℕ} (x : Fin n → J) :
    ∃ S, ∀ j, R.SupportIn (x j) S :=
  exists_supportIn_fin R x

variable [Fintype κ]

variable {R} in
example (μ : ι) {F : J} {S : Finset (Multiset ι)} (h : R.SupportIn F S) :
    R.totalDerivFun μ F = R.dx μ F + ∑ K ∈ S, ∑ a, R.u a (μ ::ₘ K) * R.d a K F :=
  totalDerivFun_eq_sum μ h

example [DecidableEq ι] (μ : ι) {n : ℕ} (f : SmoothOperation n)
    (x : Fin n → J) :
    R.totalDerivFun μ (op f x) = ∑ j, op (partialDeriv j f) x * R.totalDerivFun μ (x j) :=
  totalDerivFun_op R μ f x

variable [DecidableEq ι]

variable {R}

example (μ : ι) {F : J} {S : Finset (Multiset ι)} (h : R.SupportIn F S) :
    R.totalDeriv μ F = R.dx μ F + ∑ K ∈ S, ∑ a, R.u a (μ ::ₘ K) * R.d a K F :=
  totalDeriv_eq_sum μ h

example (δ : SmoothDerivation J J) (hδx : ∀ ν F, δ (R.dx ν F) = R.dx ν (δ F))
    (hδd : ∀ a K F, δ (R.d a K F) = R.d a K (δ F)) (μ : ι) {F : J} {S : Finset (Multiset ι)}
    (h : R.SupportIn F S) :
    δ (R.totalDeriv μ F) = R.totalDeriv μ (δ F) +
      ∑ K ∈ S, ∑ a, δ (R.u a (μ ::ₘ K)) * R.d a K F :=
  apply_totalDeriv δ hδx hδd μ h

example (ν μ : ι) (F : J) :
    R.dx ν (R.totalDeriv μ F) = R.totalDeriv μ (R.dx ν F) :=
  dx_totalDeriv ν μ F

example (μ : ι) (a : κ) (K : Multiset ι) :
    R.totalDeriv μ (R.u a K) = R.u a (μ ::ₘ K) :=
  totalDeriv_u μ a K

example (b : κ) (L : Multiset ι) (μ : ι) (F : J) :
    R.d b L (R.totalDeriv μ F) =
      R.totalDeriv μ (R.d b L F) + if μ ∈ L then R.d b (L.erase μ) F else 0 :=
  d_totalDeriv b L μ F

example (μ ν : ι) (F : J) :
    R.totalDeriv μ (R.totalDeriv ν F) = R.totalDeriv ν (R.totalDeriv μ F) :=
  totalDeriv_comm μ ν F

end FieldJetRing

end ProjectAinos.Variational

namespace ProjectAinos.Variational.FieldJetRing

open SmoothAlgebra

variable {ι κ J : Type*} [CommRing J] [Algebra ℝ J] [SmoothRing J] [Fintype κ] [DecidableEq ι]
  (R : FieldJetRing ι κ J)

variable {R}

example (F : J) : R.iterTotalDeriv 0 F = F :=
  iterTotalDeriv_zero F

example (μ : ι) (K : Multiset ι) (F : J) :
    R.iterTotalDeriv (μ ::ₘ K) F = R.totalDeriv μ (R.iterTotalDeriv K F) :=
  iterTotalDeriv_cons μ K F

example (K : Multiset ι) (μ : ι) (F : J) :
    R.iterTotalDeriv K (R.totalDeriv μ F) = R.totalDeriv μ (R.iterTotalDeriv K F) :=
  iterTotalDeriv_totalDeriv K μ F

example (K : Multiset ι) (F G : J) :
    R.iterTotalDeriv K (F + G) = R.iterTotalDeriv K F + R.iterTotalDeriv K G :=
  iterTotalDeriv_add K F G

example (K : Multiset ι) : R.iterTotalDeriv K (0 : J) = 0 :=
  iterTotalDeriv_map_zero K

example {F : J} {S : Finset (Multiset ι)} (h : R.SupportIn F S) (μ : ι) :
    R.SupportIn (R.totalDeriv μ F) (S ∪ S.image (μ ::ₘ ·)) :=
  SupportIn.totalDeriv h μ

variable (R)

variable {R}

example {F : J} {S : Finset (Multiset ι)} (h : R.SupportIn F S) (a : κ) :
    R.euler a F = ∑ K ∈ S, (-1 : J) ^ Multiset.card K * R.iterTotalDeriv K (R.d a K F) :=
  euler_eq_sum h a

example (a : κ) (μ : ι) (F : J) : R.euler a (R.totalDeriv μ F) = 0 :=
  euler_totalDeriv a μ F

example (a : κ) (μ : ι) (L F : J) :
    R.euler a (L + R.totalDeriv μ F) = R.euler a L :=
  euler_add_totalDeriv a μ L F

end ProjectAinos.Variational.FieldJetRing

namespace ProjectAinos.Variational.FieldJetRing

open SmoothAlgebra

variable {ι κ J : Type*} [CommRing J] [Algebra ℝ J] [SmoothRing J] [Fintype κ] [Fintype ι]
  [DecidableEq ι] (R : FieldJetRing ι κ J)

variable {R}

example {M : Type*} [AddCommMonoid M] (f : Multiset ι → M) :
    ∑ K ∈ firstOrderIndices ι, f K = f 0 + ∑ μ, f {μ} :=
  sum_firstOrderIndices f

omit [Fintype ι] in
example (μ : ι) (F : J) :
    R.iterTotalDeriv {μ} F = R.totalDeriv μ F :=
  iterTotalDeriv_singleton μ F

example {L : J} (hL : R.FirstOrder L) (a : κ) :
    R.euler a L = R.d a 0 L - R.divergence (R.momentum L a) :=
  euler_of_firstOrder hL a

example {L : J} (hL : R.FirstOrder L) (ν : ι) :
    R.totalDeriv ν L = R.dx ν L + ∑ a, R.u a {ν} * R.d a 0 L +
      ∑ μ, ∑ a, R.u a (ν ::ₘ {μ}) * R.momentum L a μ :=
  totalDeriv_of_firstOrder hL ν

example {L : J} (hL : R.FirstOrder L) (ξ : κ → J) :
    R.prolong ξ L = ∑ a, ξ a * R.d a 0 L +
      ∑ μ, ∑ a, R.totalDeriv μ (ξ a) * R.momentum L a μ :=
  prolong_of_firstOrder hL ξ

example (L : J) (ξ : κ → J) :
    R.divergence (fun μ => ∑ a, ξ a * R.momentum L a μ) =
      ∑ a, ξ a * R.divergence (R.momentum L a) +
        ∑ μ, ∑ a, R.totalDeriv μ (ξ a) * R.momentum L a μ :=
  divergence_sum_mul_momentum L ξ

example {L : J} (hL : R.FirstOrder L) (ξ : κ → J) :
    R.prolong ξ L = ∑ a, ξ a * R.euler a L +
      R.divergence (fun μ => ∑ a, ξ a * R.momentum L a μ) :=
  prolong_eq_euler_add_divergence hL ξ

example {L : J} (hL : R.FirstOrder L) (ξ : κ → J) {F : ι → J}
    (h : R.prolong ξ L = R.divergence F) :
    R.divergence (fun μ => ∑ a, ξ a * R.momentum L a μ - F μ) = -∑ a, ξ a * R.euler a L :=
  divergence_noetherCurrent hL ξ h

example {L : J} (hL : R.FirstOrder L) (ν : ι) :
    R.divergence (fun μ => R.stress L μ ν) = -∑ a, R.u a {ν} * R.euler a L - R.dx ν L :=
  divergence_stress hL ν

variable (R)

variable {R}

omit [Fintype ι] in
example (L : J) (a : κ) : R.euler a L ∈ R.eulerLagrangeIdeal L :=
  euler_mem L a

omit [Fintype ι] in
example (L : J) (ξ : κ → J) :
    ∑ a, ξ a * R.euler a L ∈ R.eulerLagrangeIdeal L :=
  sum_mul_euler_mem L ξ

example {L : J} (hL : R.FirstOrder L) (ξ : κ → J) {F : ι → J}
    (h : R.prolong ξ L = R.divergence F) :
    R.Conserved L fun μ => ∑ a, ξ a * R.momentum L a μ - F μ :=
  conserved_noetherCurrent hL ξ h

example {L : J} (hL : R.FirstOrder L) (ν : ι) (hx : R.dx ν L = 0) :
    R.Conserved L fun μ => R.stress L μ ν :=
  conserved_stress hL ν hx

end ProjectAinos.Variational.FieldJetRing

namespace ProjectAinos.Variational

open SmoothAlgebra SmoothRing

namespace StandardFieldJet

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

variable [Fintype κ]

example (μ ν : ι) :
    (jetRing ι κ).totalDeriv μ (x ν) = if ν = μ then 1 else 0 :=
  totalDeriv_x μ ν

end StandardFieldJet

namespace StandardFieldJet

variable {n : ℕ} {κ : Type*}

example (φ : κ → SmoothOperation n) (μ : Fin n) :
    prolongation φ (x μ) = SmoothOperation.proj μ :=
  prolongation_x φ μ

variable [DecidableEq κ]

example (φ : κ → SmoothOperation n) (a : κ) (K : Multiset (Fin n)) :
    prolongation φ ((jetRing (Fin n) κ).u a K) = SmoothOperation.iterPartialDeriv K (φ a) :=
  prolongation_u φ a K

variable [Fintype κ]

example (φ : κ → SmoothOperation n) (μ : Fin n)
    (F : StandardFieldJet (Fin n) κ) :
    prolongation φ ((jetRing (Fin n) κ).totalDeriv μ F) =
      SmoothOperation.partialDeriv μ (prolongation φ F) :=
  prolongation_totalDeriv φ μ F

example (L F : StandardFieldJet (Fin n) κ) (μ : Fin n)
    (φ : κ → SmoothOperation n) :
    IsSolution (L + (jetRing (Fin n) κ).totalDeriv μ F) φ ↔ IsSolution L φ :=
  isSolution_add_totalDeriv L F μ φ

end StandardFieldJet

end ProjectAinos.Variational
