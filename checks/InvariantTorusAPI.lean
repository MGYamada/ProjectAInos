/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAInos.Mechanics.Poisson.OscillatorTorus

/-! Typed contracts for the invariant tori of commuting flows: commuting
fields and their flows, the joint flow as an action of `ℝ^ι`, its smoothness,
the period lattice on a compact connected set, the level sets of a submersion,
the invariant tori of integrals in involution, and a system of oscillators.
These examples use default elaborator options. -/

open ProjectAInos ProjectAInos.Mechanics ProjectAInos.SmoothGeometry.NonlinearODE
open ProjectAInos.SmoothAlgebra ProjectAInos.SmoothAlgebra.FreeSmoothRing
open Set Filter Module
open scoped Topology ContDiff

noncomputable section

section CommutingFlows

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] {X : ι → E → E} {M : Set E}
variable {A B : E → E} {t : ℝ} {x : E}

example {c r T : ℝ} (hr : r ∈ uIcc 0 T) :
    c * r ∈ uIcc 0 (c * T) :=
  const_mul_mem_uIcc hr

example (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    (hAB : ∀ y, fderiv ℝ A y (B y) = fderiv ℝ B y (A y)) (h : (t, x) ∈ flowDomain A) :
    fderiv ℝ (fun y => flow A (t, y)) x (B x) = B (flow A (t, x)) :=
  fderiv_flow_apply_of_commute hA hB hAB h

example (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    (hAB : ∀ y, fderiv ℝ A y (B y) = fderiv ℝ B y (A y)) {T : ℝ}
    (hBdom : ∀ r ∈ uIcc 0 T, (r, x) ∈ flowDomain B)
    (hAdom : ∀ r ∈ uIcc 0 T, (r, flow B (r, x)) ∈ flowDomain A) :
    (T, x) ∈ flowDomain (fun y => A y + B y) ∧
      flow (fun y => A y + B y) (T, x) = flow A (T, flow B (T, x)) :=
  flow_add_of_commute hA hB hAB hBdom hAdom

example (hA : ContDiff ℝ ∞ A) (c : ℝ) {T : ℝ}
    (h : (c * T, x) ∈ flowDomain A) :
    (T, x) ∈ flowDomain (fun y => c • A y) ∧
      flow (fun y => c • A y) (T, x) = flow A (c * T, x) :=
  flow_smul_field hA c h

end CommutingFlows

section JointFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] {X : ι → E → E} {M : Set E}
variable (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hc : PairwiseCommute X) (hM : IsInvariantSet X M)

example (X : ι → E → E) (t : ι → ℝ) (y : E) :
    jointField X t y =
      ∑ i, t i • X i y := rfl

example (X : ι → E → E) (t : ι → ℝ) (x : E) :
    jointFlow X t x =
      flow (jointField X t) (1, x) := rfl

example (X : ι → E → E) :
    PairwiseCommute X =
      ∀ i j y, fderiv ℝ (X i) y (X j y) = fderiv ℝ (X j) y (X i y) := rfl

example (hX : ∀ i, ContDiff ℝ ∞ (X i)) (t : ι → ℝ) :
    ContDiff ℝ ∞ (jointField X t) :=
  contDiff_jointField hX t

example (t s : ι → ℝ) :
    jointField X (t + s) = fun y => jointField X t y + jointField X s y :=
  jointField_add t s

example (c : ℝ) (t : ι → ℝ) :
    jointField X (c • t) = fun y => c • jointField X t y :=
  jointField_smul c t

example (hX : ∀ i, ContDiff ℝ ∞ (X i)) (t : ι → ℝ) (y : E) :
    fderiv ℝ (jointField X t) y = ∑ i, t i • fderiv ℝ (X i) y :=
  fderiv_jointField hX t y

example (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hc : PairwiseCommute X)
    (t s : ι → ℝ) (y : E) :
    fderiv ℝ (jointField X t) y (jointField X s y) =
      fderiv ℝ (jointField X s) y (jointField X t y) :=
  jointField_commute hX hc t s y

example (h : IsInvariantSet X M) (t : ι → ℝ) (r : ℝ) {x : E} (hx : x ∈ M) :
    (r, x) ∈ flowDomain (jointField X t) := h.mem_flowDomain t r x hx

example (h : IsInvariantSet X M) (t : ι → ℝ) (r : ℝ) {x : E} (hx : x ∈ M) :
    flow (jointField X t) (r, x) ∈ M := h.flow_mem t r x hx

example (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hM : IsCompact M)
    (hinv : ∀ (t : ι → ℝ) (r : ℝ) (x : E), x ∈ M → (r, x) ∈ flowDomain (jointField X t) →
      flow (jointField X t) (r, x) ∈ M) :
    IsInvariantSet X M :=
  isInvariantSet_of_isCompact hX hM hinv

example (h : ∀ t : ι → ℝ, flowDomain (jointField X t) = univ) :
    IsInvariantSet X univ :=
  isInvariantSet_univ h

example (hM : IsInvariantSet X M) (t : ι → ℝ) {x : E} (hx : x ∈ M) :
    jointFlow X t x ∈ M :=
  jointFlow_mem hM t hx

example (t s : ι → ℝ) {x : E} (hx : x ∈ M) :
    jointFlow X (t + s) x = jointFlow X t (jointFlow X s x) :=
  jointFlow_add hX hc hM t s hx

example (r : ℝ) (t : ι → ℝ) {x : E} (hx : x ∈ M) :
    jointFlow X (r • t) x = flow (jointField X t) (r, x) :=
  jointFlow_smul hX hM r t hx

example {x : E} (hx : x ∈ M) :
    jointFlow X 0 x = x :=
  jointFlow_zero hX hM hx

example (t : ι → ℝ) {x : E} (hx : x ∈ M) :
    jointFlow X (-t) (jointFlow X t x) = x :=
  jointFlow_neg hX hc hM t hx

example (t s : ι → ℝ) {x : E} (hx : x ∈ M) :
    jointFlow X t (jointFlow X s x) = jointFlow X s (jointFlow X t x) :=
  jointFlow_comm hX hc hM t s hx

example (t : ι → ℝ) {x : E} (hx : x ∈ M) (r : ℝ) :
    HasDerivAt (fun r : ℝ => jointFlow X (r • t) x)
      (jointField X t (jointFlow X (r • t) x)) r :=
  hasDerivAt_jointFlow_smul hX hM t hx r

end JointFlow

section JointFlowSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] {X : ι → E → E} {M : Set E}

example (X : ι → E → E) (p : (ι → ℝ) × E) :
    extendedJointField X p =
      (0, jointField X p.1 p.2) := rfl

example (hX : ∀ i, ContDiff ℝ ∞ (X i)) :
    ContDiff ℝ ∞ (extendedJointField X) :=
  contDiff_extendedJointField hX

example (hX : ∀ i, ContDiff ℝ ∞ (X i)) {t : ι → ℝ} {x : E} {r : ℝ}
    (h : (r, x) ∈ flowDomain (jointField X t)) :
    (r, (t, x)) ∈ flowDomain (extendedJointField X) ∧
      flow (extendedJointField X) (r, (t, x)) = (t, flow (jointField X t) (r, x)) :=
  flow_extendedJointField hX h

example (hX : ∀ i, ContDiff ℝ ∞ (X i)) {t : ι → ℝ}
    {x : E} {r : ℝ} (h : (r, (t, x)) ∈ flowDomain (extendedJointField X)) :
    (r, x) ∈ flowDomain (jointField X t) :=
  mem_flowDomain_jointField_of_extended hX h

example (hX : ∀ i, ContDiff ℝ ∞ (X i)) {t : ι → ℝ} {x : E}
    (h : (1, x) ∈ flowDomain (jointField X t)) :
    ContDiffAt ℝ ∞ (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2) (t, x) :=
  contDiffAt_jointFlow hX h

example (X : ι → E → E) (y : E) :
    ((1 : ℝ), y) ∈ flowDomain (jointField X 0) ∧ flow (jointField X 0) ((1 : ℝ), y) = y :=
  one_mem_flowDomain_jointField_zero X y

example (X : ι → E → E) (y : E) :
    jointFlow X 0 y = y :=
  jointFlow_zero_apply X y

example (hX : ∀ i, ContDiff ℝ ∞ (X i)) (x : E) :
    ∃ D : (ι → ℝ) × E →L[ℝ] E, (∀ (τ : ι → ℝ) (v : E), D (τ, v) = jointField X τ x + v) ∧
      HasStrictFDerivAt (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2) D (0, x) :=
  hasFDerivAt_jointFlow_zero hX x

end JointFlowSmooth

section PeriodLattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] {X : ι → E → E} {M : Set E}
variable (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hc : PairwiseCommute X) (hM : IsInvariantSet X M)

example (h : IsLocallyFree X M) {x : E} (hx : x ∈ M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ι → ℝ, ‖t‖ < δ → jointFlow X t x = x → t = 0 := h.injective x hx

example (h : IsLocallyFree X M) {x : E} (hx : x ∈ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧
      ∀ y ∈ M ∩ W, ∃ t : ι → ℝ, ‖t‖ < ε ∧ jointFlow X t x = y := h.open_orbit x hx ε hε

example (hloc : IsLocallyFree X M) (hconn : IsPreconnected M) {x y : E}
    (hx : x ∈ M) (hy : y ∈ M) :
    ∃ t : ι → ℝ, jointFlow X t x = y :=
  exists_jointFlow_eq hX hc hM hloc hconn hx hy

example {x : E} (hx : x ∈ M) :
    ((periods hX hc hM hx : AddSubgroup (ι → ℝ)) : Set (ι → ℝ)) = {t | jointFlow X t x = x} :=
  rfl

example {x : E} (hx : x ∈ M) {t : ι → ℝ} :
    t ∈ periods hX hc hM hx ↔ jointFlow X t x = x :=
  mem_periods hX hc hM hx

example {x : E} (hx : x ∈ M) (t s : ι → ℝ) :
    jointFlow X t x = jointFlow X s x ↔ t - s ∈ periods hX hc hM hx :=
  jointFlow_eq_iff hX hc hM hx t s

example (hloc : IsLocallyFree X M) (hconn : IsPreconnected M) {x y : E}
    (hx : x ∈ M) (hy : y ∈ M) :
    periods hX hc hM hx = periods hX hc hM hy :=
  periods_eq hX hc hM hloc hconn hx hy

example (hloc : IsLocallyFree X M) {x : E} (hx : x ∈ M) :
    DiscreteTopology (AddSubgroup.toIntSubmodule (periods hX hc hM hx)) :=
  discreteTopology_periods hX hc hM hloc hx

example (hloc : IsLocallyFree X M)
    (hconn : IsPreconnected M) (hcomp : IsCompact M) {x : E} (hx : x ∈ M) :
    ∃ K : Set (ι → ℝ), IsCompact K ∧
      ∀ t : ι → ℝ, ∃ k ∈ K, t - k ∈ periods hX hc hM hx :=
  exists_isCompact_forall_exists_sub_mem hX hc hM hloc hconn hcomp hx

example (hloc : IsLocallyFree X M) (hconn : IsPreconnected M)
    (hcomp : IsCompact M) {x : E} (hx : x ∈ M) :
    Submodule.span ℝ (periods hX hc hM hx : Set (ι → ℝ)) = ⊤ :=
  span_periods_eq_top hX hc hM hloc hconn hcomp hx

example (hloc : IsLocallyFree X M) (hconn : IsPreconnected M)
    (hcomp : IsCompact M) {x : E} (hx : x ∈ M) :
    ∃ b : Basis ι ℝ (ι → ℝ), Submodule.span ℤ (Set.range b) =
      AddSubgroup.toIntSubmodule (periods hX hc hM hx) :=
  exists_basis_periods hX hc hM hloc hconn hcomp hx

example (hloc : IsLocallyFree X M) (hconn : IsPreconnected M)
    (hcomp : IsCompact M) :
    ∃ b : Basis ι ℝ (ι → ℝ), ∀ x ∈ M,
      (∀ y ∈ M, ∃ θ : ι → ℝ, jointFlow X (∑ i, θ i • b i) x = y) ∧
      (∀ θ θ' : ι → ℝ, jointFlow X (∑ i, θ i • b i) x = jointFlow X (∑ i, θ' i • b i) x ↔
        ∀ i, ∃ n : ℤ, θ i - θ' i = n) ∧
      ∀ (s : ι → ℝ) (r : ℝ) (θ : ι → ℝ),
        flow (jointField X s) (r, jointFlow X (∑ i, θ i • b i) x) =
          jointFlow X (∑ i, (θ i + r * b.repr s i) • b i) x :=
  exists_torus_chart hX hc hM hloc hconn hcomp

end PeriodLattice

section LevelSetFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] {X : ι → E → E} {M : Set E}
variable {F : E → κ → ℝ} {c : κ → ℝ} [FiniteDimensional ℝ E]

example (htan : ∀ i y, fderiv ℝ F y (X i y) = 0) (t : ι → ℝ) (y : E) :
    fderiv ℝ F y (jointField X t y) = 0 :=
  fderiv_apply_jointField htan t y

example (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hF : ContDiff ℝ ∞ F)
    (htan : ∀ i y, fderiv ℝ F y (X i y) = 0) (t : ι → ℝ) {r : ℝ} {x : E}
    (h : (r, x) ∈ flowDomain (jointField X t)) :
    F (flow (jointField X t) (r, x)) = F x :=
  flow_jointField_levelSet hX hF htan t h

example (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hF : ContDiff ℝ ∞ F)
    (htan : ∀ i y, fderiv ℝ F y (X i y) = 0) (hcomp : IsCompact (F ⁻¹' {c})) :
    IsInvariantSet X (F ⁻¹' {c}) :=
  isInvariantSet_levelSet hX hF htan hcomp

example (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hF : ContDiff ℝ ∞ F)
    (htan : ∀ i y, fderiv ℝ F y (X i y) = 0) {x : E} (hx : F x = c)
    (hind : LinearIndependent ℝ fun i => X i x) (hsurj : Function.Surjective (fderiv ℝ F x))
    (hdim : finrank ℝ E = Fintype.card ι + Fintype.card κ) :
    ∃ (e : OpenPartialHomeomorph ((ι → ℝ) × (κ → ℝ)) E) (L : (κ → ℝ) →L[ℝ] E),
      ((0 : ι → ℝ), (0 : κ → ℝ)) ∈ e.source ∧
      (∀ p, e p = jointFlow X p.1 (x + L p.2)) ∧
      ∀ p ∈ e.source, F (e p) = c → p.2 = 0 :=
  exists_levelSet_chart hX hF htan hx hind hsurj hdim

example (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hF : ContDiff ℝ ∞ F)
    (htan : ∀ i y, fderiv ℝ F y (X i y) = 0)
    (hind : ∀ x ∈ F ⁻¹' {c}, LinearIndependent ℝ fun i => X i x)
    (hsurj : ∀ x ∈ F ⁻¹' {c}, Function.Surjective (fderiv ℝ F x))
    (hdim : finrank ℝ E = Fintype.card ι + Fintype.card κ) :
    IsLocallyFree X (F ⁻¹' {c}) :=
  isLocallyFree_levelSet hX hF htan hind hsurj hdim

example (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hc : PairwiseCommute X)
    (hF : ContDiff ℝ ∞ F) (htan : ∀ i y, fderiv ℝ F y (X i y) = 0)
    (hind : ∀ x ∈ F ⁻¹' {c}, LinearIndependent ℝ fun i => X i x)
    (hsurj : ∀ x ∈ F ⁻¹' {c}, Function.Surjective (fderiv ℝ F x))
    (hdim : finrank ℝ E = Fintype.card ι + Fintype.card κ) (hcomp : IsCompact (F ⁻¹' {c}))
    (hconn : IsPreconnected (F ⁻¹' {c})) :
    ∃ b : Basis ι ℝ (ι → ℝ), ∀ x ∈ F ⁻¹' {c},
      (∀ y ∈ F ⁻¹' {c}, ∃ θ : ι → ℝ, jointFlow X (∑ i, θ i • b i) x = y) ∧
      (∀ θ θ' : ι → ℝ, jointFlow X (∑ i, θ i • b i) x = jointFlow X (∑ i, θ' i • b i) x ↔
        ∀ i, ∃ n : ℤ, θ i - θ' i = n) ∧
      ∀ (s : ι → ℝ) (r : ℝ) (θ : ι → ℝ),
        flow (jointField X s) (r, jointFlow X (∑ i, θ i • b i) x) =
          jointFlow X (∑ i, (θ i + r * b.repr s i) • b i) x :=
  exists_torus_chart_levelSet hX hc hF htan hind hsurj hdim hcomp hconn

end LevelSetFlow

section InvariantTorus

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

example (F : ι → PhaseSpace ι) (z : ι ⊕ ι → ℝ) :
    integralMap F z =
      fun i => (F i).val z := rfl

example (F : ι → PhaseSpace ι) :
    ContDiff ℝ ∞ (integralMap F) :=
  contDiff_integralMap F

example (F : ι → PhaseSpace ι) (z w : ι ⊕ ι → ℝ) (i : ι) :
    fderiv ℝ (integralMap F) z w i = fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) z w :=
  fderiv_integralMap_apply F z w i

example (G H : PhaseSpace ι) (z : ι ⊕ ι → ℝ) :
    fderiv ℝ (G.val : (ι ⊕ ι → ℝ) → ℝ) z (hamiltonianField H z) =
      ((PhaseSpace.canonical ι).bracket G H).val z :=
  fderiv_val_hamiltonianField G H z

example {F : ι → PhaseSpace ι}
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) (i : ι) (z : ι ⊕ ι → ℝ) :
    fderiv ℝ (integralMap F) z (hamiltonianField (F i) z) = 0 :=
  fderiv_integralMap_hamiltonianField hF i z

example {F : ι → PhaseSpace ι}
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) :
    PairwiseCommute fun i => hamiltonianField (F i) :=
  pairwiseCommute_hamiltonianField hF

example {F : ι → PhaseSpace ι} {z : ι ⊕ ι → ℝ}
    (hind : LinearIndependent ℝ fun i => fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) z) :
    LinearIndependent ℝ fun i => hamiltonianField (F i) z :=
  linearIndependent_hamiltonianField hind

example {F : ι → PhaseSpace ι} {z : ι ⊕ ι → ℝ}
    (hind : LinearIndependent ℝ fun i => fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) z) :
    Function.Surjective (fderiv ℝ (integralMap F) z) :=
  surjective_fderiv_integralMap hind

example {F : ι → PhaseSpace ι}
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {c : ι → ℝ}
    (hind : ∀ z ∈ integralMap F ⁻¹' {c},
      LinearIndependent ℝ fun i => fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) z)
    (hcomp : IsCompact (integralMap F ⁻¹' {c}))
    (hconn : IsPreconnected (integralMap F ⁻¹' {c})) :
    ∃ b : Basis ι ℝ (ι → ℝ), ∀ z ∈ integralMap F ⁻¹' {c},
      (∀ y ∈ integralMap F ⁻¹' {c}, ∃ θ : ι → ℝ,
        jointFlow (fun i => hamiltonianField (F i)) (∑ i, θ i • b i) z = y) ∧
      (∀ θ θ' : ι → ℝ,
        jointFlow (fun i => hamiltonianField (F i)) (∑ i, θ i • b i) z =
          jointFlow (fun i => hamiltonianField (F i)) (∑ i, θ' i • b i) z ↔
        ∀ i, ∃ n : ℤ, θ i - θ' i = n) ∧
      ∀ (s : ι → ℝ) (r : ℝ) (θ : ι → ℝ),
        flow (jointField (fun i => hamiltonianField (F i)) s)
            (r, jointFlow (fun i => hamiltonianField (F i)) (∑ i, θ i • b i) z) =
          jointFlow (fun i => hamiltonianField (F i))
            (∑ i, (θ i + r * b.repr s i) • b i) z :=
  exists_torus_chart_of_involution hF hind hcomp hconn

example (i : ι) :
    oscillatorEnergy i =
      algebraMap ℝ (PhaseSpace ι) (1 / 2) *
      (PhaseSpace.q i * PhaseSpace.q i + PhaseSpace.p i * PhaseSpace.p i) := rfl

example (i : ι) (z : ι ⊕ ι → ℝ) :
    (oscillatorEnergy i).val z = (z (Sum.inl i) ^ 2 + z (Sum.inr i) ^ 2) / 2 :=
  oscillatorEnergy_val i z

example (i : ι) (z w : ι ⊕ ι → ℝ) :
    fderiv ℝ ((oscillatorEnergy i).val : (ι ⊕ ι → ℝ) → ℝ) z w =
      z (Sum.inl i) * w (Sum.inl i) + z (Sum.inr i) * w (Sum.inr i) :=
  fderiv_oscillatorEnergy_apply i z w

example (b : ι ⊕ ι) (i : ι) (z : ι ⊕ ι → ℝ) :
    (partialDerivation b (oscillatorEnergy i)).val z =
      z (Sum.inl i) * (Pi.single b (1 : ℝ) : ι ⊕ ι → ℝ) (Sum.inl i) +
        z (Sum.inr i) * (Pi.single b (1 : ℝ) : ι ⊕ ι → ℝ) (Sum.inr i) :=
  partialDerivation_oscillatorEnergy_val b i z

example (i j : ι) :
    (PhaseSpace.canonical ι).bracket (oscillatorEnergy i) (oscillatorEnergy j) = 0 :=
  bracket_oscillatorEnergy i j

example {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {z : ι ⊕ ι → ℝ} (hz : z ∈ integralMap (oscillatorEnergy (ι := ι)) ⁻¹' {c}) :
    LinearIndependent ℝ fun i =>
      fderiv ℝ ((oscillatorEnergy i).val : (ι ⊕ ι → ℝ) → ℝ) z :=
  linearIndependent_fderiv_oscillatorEnergy hc hz

example (c : ι → ℝ) :
    IsCompact (integralMap (oscillatorEnergy (ι := ι)) ⁻¹' {c}) :=
  isCompact_oscillator_levelSet c

example {c : ι → ℝ} (hc : ∀ i, 0 < c i) :
    IsPreconnected (integralMap (oscillatorEnergy (ι := ι)) ⁻¹' {c}) :=
  isPreconnected_oscillator_levelSet hc

example {c : ι → ℝ} (hc : ∀ i, 0 < c i) :
    ∃ b : Basis ι ℝ (ι → ℝ), ∀ z ∈ integralMap (oscillatorEnergy (ι := ι)) ⁻¹' {c},
      (∀ y ∈ integralMap (oscillatorEnergy (ι := ι)) ⁻¹' {c}, ∃ θ : ι → ℝ,
        jointFlow (fun i => hamiltonianField (oscillatorEnergy i)) (∑ i, θ i • b i) z = y) ∧
      (∀ θ θ' : ι → ℝ,
        jointFlow (fun i => hamiltonianField (oscillatorEnergy i)) (∑ i, θ i • b i) z =
          jointFlow (fun i => hamiltonianField (oscillatorEnergy i)) (∑ i, θ' i • b i) z ↔
        ∀ i, ∃ n : ℤ, θ i - θ' i = n) ∧
      ∀ (s : ι → ℝ) (r : ℝ) (θ : ι → ℝ),
        flow (jointField (fun i => hamiltonianField (oscillatorEnergy i)) s)
            (r, jointFlow (fun i => hamiltonianField (oscillatorEnergy i)) (∑ i, θ i • b i) z) =
          jointFlow (fun i => hamiltonianField (oscillatorEnergy i))
            (∑ i, (θ i + r * b.repr s i) • b i) z :=
  exists_torus_chart_oscillators hc

end InvariantTorus
