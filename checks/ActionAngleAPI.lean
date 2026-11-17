/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.Mechanics.Poisson.ActionAngle

/-! Typed contracts for the action–angle variables near an invariant torus:
the neighbourhood of a compact level set on which the flows are complete, the
smooth family of periods, the first variation of the integral of a one-form,
the symplectic form in the co-ordinates of the joint flow, the Lagrangian
transversal, the chart of periods, the angle map, the action integrals over
the cycles, and the theorem of Liouville and Arnold with a system of
oscillators as its instance. These examples use default elaborator options. -/

open ProjectAinos ProjectAinos.Mechanics ProjectAinos.SmoothGeometry
open ProjectAinos.SmoothGeometry.NonlinearODE ProjectAinos.Variational
open ProjectAinos.SmoothAlgebra ProjectAinos.SmoothAlgebra.FreeSmoothRing
open Set Filter Module
open scoped Topology ContDiff Real

noncomputable section

section LevelSetTube

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {ι κ : Type*} [Fintype ι] [Fintype κ] {X : ι → E → E} {M : Set E}
  {F : E → κ → ℝ} {c : κ → ℝ}

example (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hF : ContDiff ℝ ∞ F)
    (htan : ∀ i y, fderiv ℝ F y (X i y) = 0) (hcomp : IsCompact (F ⁻¹' {c})) :
    ∃ (U : Set E) (B : Set (κ → ℝ)), IsOpen U ∧ IsOpen B ∧ F ⁻¹' {c} ⊆ U ∧ c ∈ B ∧
      IsCompact (closure U) ∧ IsInvariantSet X (F ⁻¹' B ∩ U) :=
  exists_isInvariantSet_tube hX hF htan hcomp

example (hX : ∀ i, ContDiff ℝ ∞ (X i))
    (hF : ContDiff ℝ ∞ F) (htan : ∀ i y, fderiv ℝ F y (X i y) = 0) {x : E}
    (hind : LinearIndependent ℝ fun i => X i x)
    (hdim : finrank ℝ E = Fintype.card ι + Fintype.card κ) (L : (κ → ℝ) →L[ℝ] E)
    (N : (κ → ℝ) ≃L[ℝ] (κ → ℝ)) (hFL : ∀ s, fderiv ℝ F x (L s) = N s) :
    ∃ (e : OpenPartialHomeomorph ((ι → ℝ) × (κ → ℝ)) E) (S₀ : Set (κ → ℝ)),
      ((0 : ι → ℝ), (0 : κ → ℝ)) ∈ e.source ∧
      (∀ p, e p = jointFlow X p.1 (x + L p.2)) ∧ IsOpen S₀ ∧ (0 : κ → ℝ) ∈ S₀ ∧
      InjOn (fun s => F (x + L s)) S₀ ∧
      (∀ p ∈ e.source, p.2 ∈ S₀ ∧ F (e p) = F (x + L p.2)) ∧
      ContDiffAt ℝ ∞ e.symm x :=
  exists_levelSet_chart_of_transversal hX hF htan hind hdim L N hFL

example (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hc : PairwiseCommute X)
    (hM : IsInvariantSet X M) (t : ι → ℝ) {y : E} (hy : y ∈ M) :
    ∃ D : (ι → ℝ) × E →L[ℝ] E,
      (∀ (τ : ι → ℝ) (v : E), D (τ, v) =
        jointField X τ (jointFlow X t y) + fderiv ℝ (fun z => jointFlow X t z) y v) ∧
      HasFDerivAt (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2) D (t, y) :=
  hasFDerivAt_jointFlow hX hc hM t hy

example (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hc : PairwiseCommute X)
    (hF : ContDiff ℝ ∞ F) (htan : ∀ i y, fderiv ℝ F y (X i y) = 0)
    (hM : IsInvariantSet X M) (hMo : IsOpen M) {x : E} (hx : x ∈ M)
    (hind : LinearIndependent ℝ fun i => X i x)
    (hdim : finrank ℝ E = Fintype.card ι + Fintype.card κ) (L : (κ → ℝ) →L[ℝ] E)
    (N : (κ → ℝ) ≃L[ℝ] (κ → ℝ)) (hFL : ∀ s, fderiv ℝ F x (L s) = N s) {b : ι → ℝ}
    (hb : jointFlow X b x = x) :
    ∃ (S : Set (κ → ℝ)) (e : (κ → ℝ) → ι → ℝ), IsOpen S ∧ (0 : κ → ℝ) ∈ S ∧ e 0 = b ∧
      ContDiffAt ℝ ∞ e 0 ∧
      ∀ s ∈ S, x + L s ∈ M ∧ jointFlow X (e s) (x + L s) = x + L s :=
  exists_period_family hX hc hF htan hM hMo hx hind hdim L N hFL hb

end LevelSetTube

section PeriodicInjective

variable {X : Type*} [TopologicalSpace X] [T2Space X] {ι : Type*} [Fintype ι]

example {Ψ : (ι → ℝ) × (ι → ℝ) → X} {B : Set (ι → ℝ)} {J₀ : ι → ℝ}
    {T : ℝ} (hT : 0 < T) (hB : IsOpen B) (hJ₀ : J₀ ∈ B)
    (hcont : ∀ φ : ι → ℝ, ContinuousAt Ψ (J₀, φ))
    (hloc : ∀ φ : ι → ℝ, ∃ U ∈ 𝓝 ((J₀, φ) : (ι → ℝ) × (ι → ℝ)), InjOn Ψ U)
    (hper : ∀ J ∈ B, ∀ (φ : ι → ℝ) (n : ι → ℤ), Ψ (J, fun k => φ k + T * n k) = Ψ (J, φ))
    (heq : ∀ φ φ' : ι → ℝ, Ψ (J₀, φ) = Ψ (J₀, φ') → ∀ k, ∃ n : ℤ, φ k - φ' k = T * n) :
    ∃ B' : Set (ι → ℝ), B' ⊆ B ∧ IsOpen B' ∧ J₀ ∈ B' ∧
      ∀ J ∈ B', ∀ J' ∈ B', ∀ φ φ' : ι → ℝ, Ψ (J, φ) = Ψ (J', φ') →
        J = J' ∧ ∀ k, ∃ n : ℤ, φ k - φ' k = T * n :=
  exists_injOn_modPeriod hT hB hJ₀ hcont hloc hper heq

end PeriodicInjective

section LineDerivative

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

example {f : E → G} {f' : E →L[ℝ] G} {s : E} (hf : HasFDerivAt f f' s)
    (a : E) :
    HasDerivAt (fun ε : ℝ => f (s + ε • a)) (f' a) 0 :=
  hasDerivAt_line hf a

example {f : E → G} {f' : E →L[ℝ] G} {s : E} (hf : HasFDerivAt f f' s)
    (a : E) (r : ℝ) :
    HasDerivAt (fun t : ℝ => f (s + (t - r) • a)) (f' a) r :=
  hasDerivAt_line_sub hf a r

example {f : E → G} {A : E → E →L[ℝ] G} {S : Set E}
    (hS : IsOpen S) (hf : ∀ s ∈ S, ∀ a, HasDerivAt (fun ε : ℝ => f (s + ε • a)) (A s a) 0)
    (hA : ContinuousOn A S) {s : E} (hs : s ∈ S) :
    HasFDerivAt f (A s) s :=
  hasFDerivAt_of_hasDerivAt_line hS hf hA hs

example (θ : E →L[ℝ] E →L[ℝ] ℝ) {γ : ℝ × ℝ → E} {ε₀ a b : ℝ}
    (hγ : ∀ r ∈ uIcc a b, ContDiffAt ℝ 2 γ (ε₀, r)) :
    HasDerivAt (fun ε => ∫ r in a..b, θ (γ (ε, r)) (deriv (fun t => γ (ε, t)) r))
      (θ (γ (ε₀, b)) (fderiv ℝ γ (ε₀, b) (1, 0)) -
          θ (γ (ε₀, a)) (fderiv ℝ γ (ε₀, a) (1, 0)) +
        ∫ r in a..b, (θ (fderiv ℝ γ (ε₀, r) (1, 0)) (fderiv ℝ γ (ε₀, r) (0, 1)) -
          θ (fderiv ℝ γ (ε₀, r) (0, 1)) (fderiv ℝ γ (ε₀, r) (1, 0)))) ε₀ :=
  hasDerivAt_lineIntegral θ hγ

end LineDerivative

section JointFlowSymplectic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : ι → PhaseSpace ι} {x₀ : ι ⊕ ι → ℝ}
  {M : Set (ι ⊕ ι → ℝ)} {S : Set (ι → ℝ)} {e : ι → (ι → ℝ) → ι → ℝ}

example (H : PhaseSpace ι) (z w : ι ⊕ ι → ℝ) :
    symplecticForm ι (hamiltonianField H z) w =
      fderiv ℝ (H.val : (ι ⊕ ι → ℝ) → ℝ) z w :=
  symplecticForm_hamiltonianField H z w

example (F : ι → PhaseSpace ι) (t : ι → ℝ) :
    jointField (fun i => hamiltonianField (F i)) t = hamiltonianField (∑ i, t i • F i) :=
  jointField_hamiltonianField F t

example (X : ι → (ι ⊕ ι → ℝ) → ι ⊕ ι → ℝ) (i : ι) :
    jointField X (Pi.single i 1) = X i :=
  jointField_single X i

example (F : ι → PhaseSpace ι) {t : ι → ℝ}
    {y : ι ⊕ ι → ℝ}
    (h : ((1 : ℝ), y) ∈ flowDomain (jointField (fun i => hamiltonianField (F i)) t))
    (u v : ι ⊕ ι → ℝ) :
    symplecticForm ι
        (fderiv ℝ (fun z => jointFlow (fun i => hamiltonianField (F i)) t z) y u)
        (fderiv ℝ (fun z => jointFlow (fun i => hamiltonianField (F i)) t z) y v) =
      symplecticForm ι u v :=
  symplecticForm_fderiv_jointFlow F h u v

example {F : ι → PhaseSpace ι}
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {t : ι → ℝ}
    {y : ι ⊕ ι → ℝ}
    (h : ((1 : ℝ), y) ∈ flowDomain (jointField (fun i => hamiltonianField (F i)) t)) (i : ι) :
    fderiv ℝ (fun z => jointFlow (fun i => hamiltonianField (F i)) t z) y
        (hamiltonianField (F i) y) =
      hamiltonianField (F i) (jointFlow (fun i => hamiltonianField (F i)) t y) :=
  fderiv_jointFlow_hamiltonianField hF h i

example {F : ι → PhaseSpace ι}
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) (i j : ι)
    (z : ι ⊕ ι → ℝ) :
    symplecticForm ι (hamiltonianField (F i) z) (hamiltonianField (F j) z) = 0 :=
  symplecticForm_hamiltonianField_hamiltonianField hF i j z

example {F : ι → PhaseSpace ι}
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {t : ι → ℝ}
    {y : ι ⊕ ι → ℝ}
    (h : ((1 : ℝ), y) ∈ flowDomain (jointField (fun i => hamiltonianField (F i)) t))
    (τ τ' : ι → ℝ) (v v' : ι ⊕ ι → ℝ) :
    symplecticForm ι
        (jointField (fun i => hamiltonianField (F i)) τ
            (jointFlow (fun i => hamiltonianField (F i)) t y) +
          fderiv ℝ (fun z => jointFlow (fun i => hamiltonianField (F i)) t z) y v)
        (jointField (fun i => hamiltonianField (F i)) τ'
            (jointFlow (fun i => hamiltonianField (F i)) t y) +
          fderiv ℝ (fun z => jointFlow (fun i => hamiltonianField (F i)) t z) y v') =
      symplecticForm ι v v' +
        ∑ i, (τ i * fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) y v' -
          τ' i * fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) y v) :=
  symplecticForm_jointFlow hF h τ τ' v v'

example (G H : PhaseSpace ι) (z : ι ⊕ ι → ℝ) :
    ((PhaseSpace.canonical ι).bracket G H).val z =
      ∑ i, ((partialDerivation (Sum.inl i) G).val z * (partialDerivation (Sum.inr i) H).val z -
        (partialDerivation (Sum.inr i) G).val z * (partialDerivation (Sum.inl i) H).val z) :=
  canonical_bracket_val G H z

example (F : ι → PhaseSpace ι) (x : ι ⊕ ι → ℝ) (k : ι) (a : ι ⊕ ι) :
    gradient F x k a = (partialDerivation a (F k)).val x := rfl

example (F : ι → PhaseSpace ι) (x : ι ⊕ ι → ℝ) (a : ι → ℝ) :
    gradientMap F x a = ∑ k, a k • gradient F x k := rfl

example (F : ι → PhaseSpace ι) (x : ι ⊕ ι → ℝ) (a : ι → ℝ) :
    gradientMap F x a = ∑ k, a k • gradient F x k :=
  gradientMap_apply F x a

example (F : ι → PhaseSpace ι) (x : ι ⊕ ι → ℝ) (a : ι → ℝ)
    (b : ι ⊕ ι) :
    gradientMap F x a b = ∑ k, a k * gradient F x k b :=
  gradientMap_apply_apply F x a b

example (F : ι → PhaseSpace ι) (x w : ι ⊕ ι → ℝ) (j : ι) :
    fderiv ℝ ((F j).val : (ι ⊕ ι → ℝ) → ℝ) x w = ∑ b, gradient F x j b * w b :=
  fderiv_val_eq_sum_gradient F x w j

example {F : ι → PhaseSpace ι}
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) (x : ι ⊕ ι → ℝ) (j k : ι) :
    symplecticForm ι (gradient F x j) (gradient F x k) = 0 :=
  symplecticForm_gradient hF x j k

example {F : ι → PhaseSpace ι}
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) (x : ι ⊕ ι → ℝ)
    (a a' : ι → ℝ) :
    symplecticForm ι (gradientMap F x a) (gradientMap F x a') = 0 :=
  symplecticForm_gradientMap hF x a a'

example {F : ι → PhaseSpace ι} {x : ι ⊕ ι → ℝ}
    (hind : LinearIndependent ℝ fun i => fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) x) :
    ∃ N : (ι → ℝ) ≃L[ℝ] (ι → ℝ),
      ∀ a, fderiv ℝ (integralMap F) x (gradientMap F x a) = N a :=
  exists_gram_equiv hind

end JointFlowSymplectic

section PeriodChart

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : ι → PhaseSpace ι} {x₀ : ι ⊕ ι → ℝ}
  {M : Set (ι ⊕ ι → ℝ)} {S : Set (ι → ℝ)} {e : ι → (ι → ℝ) → ι → ℝ}

example (F : ι → PhaseSpace ι) : hamFields F = fun i => hamiltonianField (F i) := rfl

example (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (s : ι → ℝ) :
    sectionPoint F x₀ s = x₀ + gradientMap F x₀ s := rfl

example (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (p : (ι → ℝ) × (ι → ℝ)) :
    torusMap F x₀ p = jointFlow (hamFields F) p.2 (sectionPoint F x₀ p.1) := rfl

example (F : ι → PhaseSpace ι) (i : ι) :
    ContDiff ℝ ∞ (hamFields F i) :=
  contDiff_hamFields F i

example (h : IsPeriodChart F x₀ M S e) : IsInvariantSet (hamFields F) M := h.invariant

example (h : IsPeriodChart F x₀ M S e) : IsOpen M := h.isOpen_set

example (h : IsPeriodChart F x₀ M S e) : IsOpen S := h.isOpen

example (h : IsPeriodChart F x₀ M S e) : (0 : ι → ℝ) ∈ S := h.zero_mem

example (h : IsPeriodChart F x₀ M S e) {s : ι → ℝ} (hs : s ∈ S) :
    sectionPoint F x₀ s ∈ M := h.mem s hs

example (h : IsPeriodChart F x₀ M S e) (k : ι) {s : ι → ℝ} (hs : s ∈ S) :
    jointFlow (hamFields F) (e k s) (sectionPoint F x₀ s) = sectionPoint F x₀ s :=
  h.period k s hs

example (h : IsPeriodChart F x₀ M S e) (k : ι) {s : ι → ℝ} (hs : s ∈ S) :
    ContDiffAt ℝ 2 (e k) s := h.contDiffAt k s hs

example {F : ι → PhaseSpace ι}
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {c : ι → ℝ}
    (hind : ∀ z ∈ integralMap F ⁻¹' {c},
      LinearIndependent ℝ fun i => fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) z)
    (hcomp : IsCompact (integralMap F ⁻¹' {c}))
    (hconn : IsPreconnected (integralMap F ⁻¹' {c})) {x₀ : ι ⊕ ι → ℝ}
    (hx₀ : x₀ ∈ integralMap F ⁻¹' {c}) :
    ∃ (b : Basis ι ℝ (ι → ℝ)) (M : Set (ι ⊕ ι → ℝ)) (S : Set (ι → ℝ))
      (e : ι → (ι → ℝ) → ι → ℝ), IsPeriodChart F x₀ M S e ∧ (∀ k, e k 0 = b k) ∧
      (∀ y ∈ integralMap F ⁻¹' {c}, ∃ θ : ι → ℝ,
        jointFlow (hamFields F) (∑ i, θ i • b i) x₀ = y) ∧
      ∀ θ θ' : ι → ℝ, jointFlow (hamFields F) (∑ i, θ i • b i) x₀ =
          jointFlow (hamFields F) (∑ i, θ' i • b i) x₀ ↔ ∀ i, ∃ n : ℤ, θ i - θ' i = n :=
  exists_isPeriodChart hF hind hcomp hconn hx₀

example (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (s : ι → ℝ) :
    sectionIntegral F x₀ s = integralMap F (sectionPoint F x₀ s) := rfl

example (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (s : ι → ℝ) :
    sectionDeriv F x₀ s =
      (fderiv ℝ (integralMap F) (sectionPoint F x₀ s)).comp (gradientMap F x₀) := rfl

example (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (s a : ι → ℝ) (i : ι) :
    sectionDeriv F x₀ s a i =
      fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) (sectionPoint F x₀ s) (gradientMap F x₀ a) :=
  sectionDeriv_apply F x₀ s a i

example (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (s : ι → ℝ) :
    HasFDerivAt (sectionPoint F x₀) (gradientMap F x₀) s :=
  hasFDerivAt_sectionPoint F x₀ s

example (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) :
    ContDiff ℝ ∞ (sectionPoint F x₀) :=
  contDiff_sectionPoint F x₀

example (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (s : ι → ℝ) :
    HasFDerivAt (sectionIntegral F x₀) (sectionDeriv F x₀ s) s :=
  hasFDerivAt_sectionIntegral F x₀ s

example (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) :
    Continuous (sectionDeriv F x₀) :=
  continuous_sectionDeriv F x₀

example (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {s : ι → ℝ} (hs : s ∈ S)
    (t : ι → ℝ) :
    integralMap F (torusMap F x₀ (s, t)) = sectionIntegral F x₀ s :=
  IsPeriodChart.integralMap_torusMap h hF hs t

example (h : IsPeriodChart F x₀ M S e) {s : ι → ℝ} (hs : s ∈ S)
    (t : ι → ℝ) :
    torusMap F x₀ (s, t) ∈ M :=
  IsPeriodChart.torusMap_mem h hs t

example (h : IsPeriodChart F x₀ M S e) {s : ι → ℝ}
    (hs : s ∈ S) (t : ι → ℝ) :
    ContDiffAt ℝ ∞ (torusMap F x₀) (s, t) :=
  IsPeriodChart.contDiffAt_torusMap h hs t

example (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {s : ι → ℝ} (hs : s ∈ S)
    (t a τ : ι → ℝ) :
    fderiv ℝ (torusMap F x₀) (s, t) (a, τ) =
      jointField (hamFields F) τ (torusMap F x₀ (s, t)) +
        fderiv ℝ (fun z => jointFlow (hamFields F) t z) (sectionPoint F x₀ s)
          (gradientMap F x₀ a) :=
  IsPeriodChart.fderiv_torusMap h hF hs t a τ

example (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {s : ι → ℝ} (hs : s ∈ S)
    (t a τ a' τ' : ι → ℝ) :
    symplecticForm ι (fderiv ℝ (torusMap F x₀) (s, t) (a, τ))
        (fderiv ℝ (torusMap F x₀) (s, t) (a', τ')) =
      ∑ i, (τ i * sectionDeriv F x₀ s a' i - τ' i * sectionDeriv F x₀ s a i) :=
  IsPeriodChart.symplecticForm_torusMap h hF hs t a τ a' τ'

example (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) (k : ι) {s : ι → ℝ}
    (hs : s ∈ S) (a a' : ι → ℝ) :
    ∑ i, (fderiv ℝ (e k) s a i * sectionDeriv F x₀ s a' i -
      fderiv ℝ (e k) s a' i * sectionDeriv F x₀ s a i) = 0 :=
  IsPeriodChart.sum_fderiv_period_symm h hF k hs a a'

example (e : ι → (ι → ℝ) → ι → ℝ) (s φ : ι → ℝ) :
    angleTime e s φ = ∑ k, (φ k / (2 * π)) • e k s := rfl

example (e : ι → (ι → ℝ) → ι → ℝ) (s φ : ι → ℝ) (i : ι) :
    angleTime e s φ i = ∑ k, φ k / (2 * π) * e k s i :=
  angleTime_apply e s φ i

example (e : ι → (ι → ℝ) → ι → ℝ) (s φ ψ : ι → ℝ) :
    angleTime e s (φ + ψ) = angleTime e s φ + angleTime e s ψ :=
  angleTime_add e s φ ψ

example (e : ι → (ι → ℝ) → ι → ℝ) (s : ι → ℝ) (c : ℝ) (φ : ι → ℝ) :
    angleTime e s (c • φ) = c • angleTime e s φ :=
  angleTime_smul e s c φ

example (e : ι → (ι → ℝ) → ι → ℝ) (s α v : ι → ℝ) :
    ∑ i, angleTime e s α i * v i = ∑ k, α k * ((2 * π)⁻¹ * ∑ i, e k s i * v i) :=
  sum_angleTime_mul e s α v

example (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (e : ι → (ι → ℝ) → ι → ℝ)
    (p : (ι → ℝ) × (ι → ℝ)) :
    angleMap F x₀ e p = torusMap F x₀ (p.1, angleTime e p.1 p.2) := rfl

example (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (e : ι → (ι → ℝ) → ι → ℝ) (s a : ι → ℝ)
    (k : ι) :
    actionForm F x₀ e s a k = (2 * π)⁻¹ * ∑ i, e k s i * sectionDeriv F x₀ s a i := rfl

example (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ)
    (e : ι → (ι → ℝ) → ι → ℝ) (s a : ι → ℝ) (k : ι) :
    actionForm F x₀ e s a k = (2 * π)⁻¹ * ∑ i, e k s i * sectionDeriv F x₀ s a i :=
  actionForm_apply F x₀ e s a k

example (h : IsPeriodChart F x₀ M S e) {s : ι → ℝ} (hs : s ∈ S)
    (φ : ι → ℝ) :
    angleMap F x₀ e (s, φ) ∈ M :=
  IsPeriodChart.angleMap_mem h hs φ

example (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {s : ι → ℝ} (hs : s ∈ S)
    (φ : ι → ℝ) :
    integralMap F (angleMap F x₀ e (s, φ)) = sectionIntegral F x₀ s :=
  IsPeriodChart.integralMap_angleMap h hF hs φ

example (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {s : ι → ℝ} (hs : s ∈ S)
    (φ : ι → ℝ) (n : ι → ℤ) :
    angleMap F x₀ e (s, fun k => φ k + 2 * π * n k) = angleMap F x₀ e (s, φ) :=
  IsPeriodChart.angleMap_add_period h hF hs φ n

example (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {s : ι → ℝ} (hs : s ∈ S)
    (φ : ι → ℝ) {ν c : ι → ℝ} (hν : angleTime e s ν = c) (r : ℝ) :
    flow (jointField (hamFields F) c) (r, angleMap F x₀ e (s, φ)) =
      angleMap F x₀ e (s, φ + r • ν) :=
  IsPeriodChart.flow_angleMap h hF hs φ hν r

example (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {s : ι → ℝ} (hs : s ∈ S)
    (φ : ι → ℝ) {ν : ι → ℝ} (i : ι) (hν : angleTime e s ν = Pi.single i 1) (r : ℝ) :
    flow (hamiltonianField (F i)) (r, angleMap F x₀ e (s, φ)) =
      angleMap F x₀ e (s, φ + r • ν) :=
  IsPeriodChart.flow_hamiltonianField_angleMap h hF hs φ i hν r

example (h : IsPeriodChart F x₀ M S e) {s : ι → ℝ}
    (hs : s ∈ S) (φ : ι → ℝ) :
    ContDiffAt ℝ 2 (fun p : (ι → ℝ) × (ι → ℝ) => angleTime e p.1 p.2) (s, φ) :=
  IsPeriodChart.contDiffAt_angleTime h hs φ

example (h : IsPeriodChart F x₀ M S e) {s : ι → ℝ}
    (hs : s ∈ S) (φ : ι → ℝ) :
    ContDiffAt ℝ 2 (angleMap F x₀ e) (s, φ) :=
  IsPeriodChart.contDiffAt_angleMap h hs φ

example (h : IsPeriodChart F x₀ M S e) {s : ι → ℝ}
    (hs : s ∈ S) (φ a α : ι → ℝ) :
    fderiv ℝ (fun p : (ι → ℝ) × (ι → ℝ) => angleTime e p.1 p.2) (s, φ) (a, α) =
      angleTime e s α + ∑ k, (φ k / (2 * π)) • fderiv ℝ (e k) s a :=
  IsPeriodChart.fderiv_angleTime h hs φ a α

example (h : IsPeriodChart F x₀ M S e) {s : ι → ℝ}
    (hs : s ∈ S) (φ a α : ι → ℝ) :
    fderiv ℝ (angleMap F x₀ e) (s, φ) (a, α) =
      fderiv ℝ (torusMap F x₀) (s, angleTime e s φ)
        (a, angleTime e s α + ∑ k, (φ k / (2 * π)) • fderiv ℝ (e k) s a) :=
  IsPeriodChart.fderiv_angleMap h hs φ a α

example (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {s : ι → ℝ} (hs : s ∈ S)
    (φ a α a' α' : ι → ℝ) :
    symplecticForm ι (fderiv ℝ (angleMap F x₀ e) (s, φ) (a, α))
        (fderiv ℝ (angleMap F x₀ e) (s, φ) (a', α')) =
      ∑ k, (α k * actionForm F x₀ e s a' k - α' k * actionForm F x₀ e s a k) :=
  IsPeriodChart.symplecticForm_angleMap h hF hs φ a α a' α'

example (k : ι) (φ : ι → ℝ) (r : ℝ) :
    cycleAngle k φ r = φ + (2 * π * r) • Pi.single k (1 : ℝ) := rfl

example (k : ι) (φ : ι → ℝ) :
    cycleAngle k φ 0 = φ :=
  cycleAngle_zero k φ

example (k : ι) (φ : ι → ℝ) :
    cycleAngle k φ 1 = fun j => φ j + 2 * π * ((Pi.single k (1 : ℤ) : ι → ℤ) j : ℝ) :=
  cycleAngle_one k φ

example (k : ι) (φ ψ : ι → ℝ) (r : ℝ) :
    cycleAngle k (φ + ψ) r = cycleAngle k φ r + ψ :=
  cycleAngle_add k φ ψ r

example (k : ι) (φ : ι → ℝ) (r t : ℝ) :
    cycleAngle k φ t = cycleAngle k φ r + (t - r) • ((2 * π) • Pi.single k (1 : ℝ)) :=
  cycleAngle_eq_add k φ r t

example (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (e : ι → (ι → ℝ) → ι → ℝ) (k : ι)
    (p : (ι → ℝ) × (ι → ℝ)) :
    loopAction F x₀ e k p = (2 * π)⁻¹ * ∫ r in (0 : ℝ)..1,
      liouvilleForm ι (angleMap F x₀ e (p.1, cycleAngle k p.2 r))
        (deriv (fun t => angleMap F x₀ e (p.1, cycleAngle k p.2 t)) r) := rfl

example (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (e : ι → (ι → ℝ) → ι → ℝ) (s : ι → ℝ)
    (k : ι) : actionMap F x₀ e s k = loopAction F x₀ e k (s, 0) := rfl

example (u w : ι ⊕ ι → ℝ) :
    symplecticForm ι u w = liouvilleForm ι w u - liouvilleForm ι u w :=
  symplecticForm_eq_liouvilleForm_sub u w

example (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (e : ι → (ι → ℝ) → ι → ℝ) (k : ι)
    (s a φ α : ι → ℝ) (p : ℝ × ℝ) :
    cycleFamily F x₀ e k s a φ α p =
      angleMap F x₀ e (s + p.1 • a, cycleAngle k (φ + p.1 • α) p.2) := rfl

example (h : IsPeriodChart F x₀ M S e) (k : ι)
    {s : ι → ℝ} (hs : s ∈ S) (a φ α : ι → ℝ) (r : ℝ) :
    ContDiffAt ℝ 2 (cycleFamily F x₀ e k s a φ α) (0, r) :=
  IsPeriodChart.contDiffAt_cycleFamily h k hs a φ α r

example (h : IsPeriodChart F x₀ M S e) (k : ι)
    {s : ι → ℝ} (hs : s ∈ S) (a φ α : ι → ℝ) (r : ℝ) :
    fderiv ℝ (cycleFamily F x₀ e k s a φ α) (0, r) (1, 0) =
      fderiv ℝ (angleMap F x₀ e) (s, cycleAngle k φ r) (a, α) :=
  IsPeriodChart.fderiv_cycleFamily_parameter h k hs a φ α r

example (h : IsPeriodChart F x₀ M S e) (k : ι)
    {s : ι → ℝ} (hs : s ∈ S) (a φ α : ι → ℝ) (r : ℝ) :
    fderiv ℝ (cycleFamily F x₀ e k s a φ α) (0, r) (0, 1) =
      fderiv ℝ (angleMap F x₀ e) (s, cycleAngle k φ r)
        (0, (2 * π) • Pi.single k (1 : ℝ)) :=
  IsPeriodChart.fderiv_cycleFamily_time h k hs a φ α r

example (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) (k : ι) {s : ι → ℝ}
    (hs : s ∈ S) (ψ a α : ι → ℝ) :
    liouvilleForm ι (fderiv ℝ (angleMap F x₀ e) (s, ψ) (a, α))
        (fderiv ℝ (angleMap F x₀ e) (s, ψ) (0, (2 * π) • Pi.single k (1 : ℝ))) -
      liouvilleForm ι (fderiv ℝ (angleMap F x₀ e) (s, ψ) (0, (2 * π) • Pi.single k (1 : ℝ)))
        (fderiv ℝ (angleMap F x₀ e) (s, ψ) (a, α)) =
      2 * π * actionForm F x₀ e s a k :=
  IsPeriodChart.liouvilleForm_cycle_sub h hF k hs ψ a α

example (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) (k : ι) {s a : ι → ℝ}
    (φ α : ι → ℝ) {ε : ℝ} (hε : s + ε • a ∈ S) :
    cycleFamily F x₀ e k s a φ α (ε, 1) = cycleFamily F x₀ e k s a φ α (ε, 0) :=
  IsPeriodChart.cycleFamily_one h hF k φ α hε

example (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) (k : ι) {s : ι → ℝ}
    (hs : s ∈ S) (φ a α : ι → ℝ) :
    HasDerivAt (fun ε : ℝ => loopAction F x₀ e k (s + ε • a, φ + ε • α))
      (actionForm F x₀ e s a k) 0 :=
  IsPeriodChart.hasDerivAt_loopAction h hF k hs φ a α

example (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) (k : ι) {s : ι → ℝ}
    (hs : s ∈ S) (φ : ι → ℝ) :
    loopAction F x₀ e k (s, φ) = loopAction F x₀ e k (s, 0) :=
  IsPeriodChart.loopAction_eq h hF k hs φ

example (h : IsPeriodChart F x₀ M S e) :
    ContinuousOn (actionForm F x₀ e) S :=
  IsPeriodChart.continuousOn_actionForm h

example (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {s : ι → ℝ} (hs : s ∈ S) :
    HasFDerivAt (actionMap F x₀ e) (actionForm F x₀ e s) s :=
  IsPeriodChart.hasFDerivAt_actionMap h hF hs

end PeriodChart

section ActionAngle

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : ι → PhaseSpace ι} {x₀ : ι ⊕ ι → ℝ}
  {M : Set (ι ⊕ ι → ℝ)} {S : Set (ι → ℝ)} {e : ι → (ι → ℝ) → ι → ℝ}
variable {c : ι → ℝ} {B : Set (ι → ℝ)} {J₀ : ι → ℝ} {Ψ : (ι → ℝ) × (ι → ℝ) → ι ⊕ ι → ℝ}
  {H : (ι → ℝ) → ι → ℝ} {ν : (ι → ℝ) → ι → ι → ℝ}

example (h : IsActionAngle F c B J₀ Ψ H ν) : IsOpen B := h.isOpen

example (h : IsActionAngle F c B J₀ Ψ H ν) : J₀ ∈ B := h.mem

example (h : IsActionAngle F c B J₀ Ψ H ν) {J : ι → ℝ} (hJ : J ∈ B) (φ : ι → ℝ) :
    ContDiffAt ℝ 1 Ψ (J, φ) := h.contDiffAt J hJ φ

example (h : IsActionAngle F c B J₀ Ψ H ν) {J : ι → ℝ} (hJ : J ∈ B) (φ a α a' α' : ι → ℝ) :
    symplecticForm ι (fderiv ℝ Ψ (J, φ) (a, α)) (fderiv ℝ Ψ (J, φ) (a', α')) =
      ∑ k, (α k * a' k - α' k * a k) := h.canonical J hJ φ a α a' α'

example (h : IsActionAngle F c B J₀ Ψ H ν) {J : ι → ℝ} (hJ : J ∈ B) (φ : ι → ℝ) (n : ι → ℤ) :
    Ψ (J, fun k => φ k + 2 * π * n k) = Ψ (J, φ) := h.periodic J hJ φ n

example (h : IsActionAngle F c B J₀ Ψ H ν) {J : ι → ℝ} (hJ : J ∈ B) (φ : ι → ℝ) :
    integralMap F (Ψ (J, φ)) = H J := h.integral J hJ φ

example (h : IsActionAngle F c B J₀ Ψ H ν) {J : ι → ℝ} (hJ : J ∈ B) :
    DifferentiableAt ℝ H J := h.differentiableAt_integral J hJ

example (h : IsActionAngle F c B J₀ Ψ H ν) {J : ι → ℝ} (hJ : J ∈ B) (a : ι → ℝ) (i : ι) :
    fderiv ℝ H J a i = ∑ k, ν J i k * a k := h.fderiv_integral J hJ a i

example (h : IsActionAngle F c B J₀ Ψ H ν) {J : ι → ℝ} (hJ : J ∈ B) (φ : ι → ℝ) (i : ι) (r : ℝ) :
    flow (hamiltonianField (F i)) (r, Ψ (J, φ)) = Ψ (J, φ + r • ν J i) :=
  h.flow J hJ φ i r

example (h : IsActionAngle F c B J₀ Ψ H ν) {J : ι → ℝ} (hJ : J ∈ B) (φ : ι → ℝ) (k : ι) :
    (2 * π)⁻¹ * ∫ r in (0 : ℝ)..1, liouvilleForm ι (Ψ (J, cycleAngle k φ r))
      (deriv (fun t => Ψ (J, cycleAngle k φ t)) r) = J k := h.action J hJ φ k

example (h : IsActionAngle F c B J₀ Ψ H ν) (y : ι ⊕ ι → ℝ) :
    integralMap F y = c ↔ ∃ φ : ι → ℝ, Ψ (J₀, φ) = y := h.torus y

example (h : IsActionAngle F c B J₀ Ψ H ν) (φ φ' : ι → ℝ) :
    Ψ (J₀, φ) = Ψ (J₀, φ') ↔ ∀ k, ∃ n : ℤ, φ k - φ' k = 2 * π * n := h.torus_eq φ φ'

example (b : Basis ι ℝ (ι → ℝ)) {v : ι → ℝ}
    (h : ∀ k, ∑ i, b k i * v i = 0) :
    v = 0 :=
  eq_zero_of_basis_dot_eq_zero b h

example (T : (ι → ℝ) →L[ℝ] (ι → ℝ)) (a : ι → ℝ) (i : ι) :
    T a i = ∑ k, T (Pi.single k 1) i * a k :=
  clm_apply_eq_sum T a i

example {s : ι → ℝ} (A' : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    (hA' : (A' : (ι → ℝ) →L[ℝ] (ι → ℝ)) = actionForm F x₀ e s) (i : ι) :
    angleTime e s (fun k => sectionDeriv F x₀ s (A'.symm (Pi.single k 1)) i) =
      Pi.single i 1 :=
  angleTime_frequency A' hA' i

example (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {s : ι → ℝ} (hs : s ∈ S) :
    ContDiffAt ℝ 1 (actionMap F x₀ e) s :=
  IsPeriodChart.contDiffAt_actionMap h hF hs

example (b : Basis ι ℝ (ι → ℝ)) (hb : ∀ k, e k 0 = b k)
    (hind : LinearIndependent ℝ fun i => fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) x₀) :
    ∃ A₀ : (ι → ℝ) ≃L[ℝ] (ι → ℝ),
      (A₀ : (ι → ℝ) →L[ℝ] (ι → ℝ)) = actionForm F x₀ e 0 :=
  exists_actionForm_equiv b hb hind

example (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0)
    (A₀ : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    (hA₀ : (A₀ : (ι → ℝ) →L[ℝ] (ι → ℝ)) = actionForm F x₀ e 0) :
    ∃ (B : Set (ι → ℝ)) (sOf : (ι → ℝ) → ι → ℝ), IsOpen B ∧ actionMap F x₀ e 0 ∈ B ∧
      sOf (actionMap F x₀ e 0) = 0 ∧
      ∀ J ∈ B, sOf J ∈ S ∧ actionMap F x₀ e (sOf J) = J ∧
        ∃ A' : (ι → ℝ) ≃L[ℝ] (ι → ℝ),
          (A' : (ι → ℝ) →L[ℝ] (ι → ℝ)) = actionForm F x₀ e (sOf J) ∧
          HasFDerivAt sOf (A'.symm : (ι → ℝ) →L[ℝ] (ι → ℝ)) J ∧ ContDiffAt ℝ 1 sOf J :=
  IsPeriodChart.exists_action_inverse h hF A₀ hA₀

example (h : IsPeriodChart F x₀ M S e)
    {sOf : (ι → ℝ) → ι → ℝ} {J : ι → ℝ} (hs : sOf J ∈ S) {D : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hD : HasFDerivAt sOf D J) (φ a α : ι → ℝ) :
    fderiv ℝ (fun p : (ι → ℝ) × (ι → ℝ) => angleMap F x₀ e (sOf p.1, p.2)) (J, φ) (a, α) =
      fderiv ℝ (angleMap F x₀ e) (sOf J, φ) (D a, α) :=
  IsPeriodChart.fderiv_angleMap_comp h hs hD φ a α

example (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {c : ι → ℝ}
    (hx₀ : integralMap F x₀ = c)
    (hind : LinearIndependent ℝ fun i => fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) x₀)
    (b : Basis ι ℝ (ι → ℝ)) (hb : ∀ k, e k 0 = b k)
    (honto : ∀ y ∈ integralMap F ⁻¹' {c}, ∃ θ : ι → ℝ,
      jointFlow (hamFields F) (∑ i, θ i • b i) x₀ = y)
    (hiff : ∀ θ θ' : ι → ℝ, jointFlow (hamFields F) (∑ i, θ i • b i) x₀ =
      jointFlow (hamFields F) (∑ i, θ' i • b i) x₀ ↔ ∀ i, ∃ n : ℤ, θ i - θ' i = n) :
    ∃ (B : Set (ι → ℝ)) (J₀ : ι → ℝ) (Ψ : (ι → ℝ) × (ι → ℝ) → ι ⊕ ι → ℝ)
      (H : (ι → ℝ) → ι → ℝ) (ν : (ι → ℝ) → ι → ι → ℝ), IsActionAngle F c B J₀ Ψ H ν :=
  IsPeriodChart.exists_isActionAngle h hF hx₀ hind b hb honto hiff

example (h : IsActionAngle F c B J₀ Ψ H ν) {J : ι → ℝ}
    (hJ : J ∈ B) (φ : ι → ℝ) :
    Function.Injective (fderiv ℝ Ψ (J, φ)) :=
  IsActionAngle.injective_fderiv h hJ φ

example (h : IsActionAngle F c B J₀ Ψ H ν) {J : ι → ℝ}
    (hJ : J ∈ B) (φ : ι → ℝ) :
    ∃ D : ((ι → ℝ) × (ι → ℝ)) ≃L[ℝ] (ι ⊕ ι → ℝ),
      (D : (ι → ℝ) × (ι → ℝ) →L[ℝ] (ι ⊕ ι → ℝ)) = fderiv ℝ Ψ (J, φ) :=
  IsActionAngle.exists_fderiv_equiv h hJ φ

example (h : IsActionAngle F c B J₀ Ψ H ν) {J : ι → ℝ}
    (hJ : J ∈ B) (φ : ι → ℝ) :
    ∃ U ∈ 𝓝 ((J, φ) : (ι → ℝ) × (ι → ℝ)), InjOn Ψ U :=
  IsActionAngle.exists_injOn_nhds h hJ φ

example (h : IsActionAngle F c B J₀ Ψ H ν) :
    IsOpen (Ψ '' (B ×ˢ (univ : Set (ι → ℝ)))) :=
  IsActionAngle.isOpen_image h

example (h : IsActionAngle F c B J₀ Ψ H ν) :
    integralMap F ⁻¹' {c} ⊆ Ψ '' (B ×ˢ (univ : Set (ι → ℝ))) :=
  IsActionAngle.levelSet_subset_image h

example (h : IsActionAngle F c B J₀ Ψ H ν) {J : ι → ℝ}
    (hJ : J ∈ B) (φ : ι → ℝ) (i : ι) :
    fderiv ℝ Ψ (J, φ) (0, ν J i) = hamiltonianField (F i) (Ψ (J, φ)) :=
  IsActionAngle.fderiv_frequency h hJ φ i

example (h : IsActionAngle F c B J₀ Ψ H ν) (K : PhaseSpace ι)
    (w : (ι → ℝ) → ι → ℝ)
    (hK : ∀ z, hamiltonianField K z = ∑ i, w (integralMap F z) i • hamiltonianField (F i) z)
    {J : ι → ℝ} (hJ : J ∈ B) (φ : ι → ℝ) (r : ℝ) :
    NonlinearODE.flow (hamiltonianField K) (r, Ψ (J, φ)) =
      Ψ (J, φ + r • ∑ i, w (H J) i • ν J i) :=
  IsActionAngle.flow_of_field h K w hK hJ φ r

example (h : IsActionAngle F c B J₀ Ψ H ν) (a : ι → ℝ) {J : ι → ℝ}
    (hJ : J ∈ B) (φ : ι → ℝ) (r : ℝ) :
    NonlinearODE.flow (hamiltonianField (∑ i, a i • F i)) (r, Ψ (J, φ)) =
      Ψ (J, φ + r • ∑ i, a i • ν J i) :=
  IsActionAngle.flow_sum h a hJ φ r

example (h : IsActionAngle F c B J₀ Ψ H ν) :
    ∃ B' : Set (ι → ℝ), B' ⊆ B ∧ IsActionAngle F c B' J₀ Ψ H ν ∧
      ∀ J ∈ B', ∀ J' ∈ B', ∀ φ φ' : ι → ℝ, Ψ (J, φ) = Ψ (J', φ') →
        J = J' ∧ ∀ k, ∃ n : ℤ, φ k - φ' k = 2 * π * n :=
  IsActionAngle.exists_injective h

example {F : ι → PhaseSpace ι}
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {c : ι → ℝ}
    (hind : ∀ z ∈ integralMap F ⁻¹' {c},
      LinearIndependent ℝ fun i => fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) z)
    (hcomp : IsCompact (integralMap F ⁻¹' {c}))
    (hconn : IsPreconnected (integralMap F ⁻¹' {c}))
    (hne : (integralMap F ⁻¹' {c}).Nonempty) :
    ∃ (B : Set (ι → ℝ)) (J₀ : ι → ℝ) (Ψ : (ι → ℝ) × (ι → ℝ) → ι ⊕ ι → ℝ)
      (H : (ι → ℝ) → ι → ℝ) (ν : (ι → ℝ) → ι → ι → ℝ), IsActionAngle F c B J₀ Ψ H ν ∧
      ∀ J ∈ B, ∀ J' ∈ B, ∀ φ φ' : ι → ℝ, Ψ (J, φ) = Ψ (J', φ') →
        J = J' ∧ ∀ k, ∃ n : ℤ, φ k - φ' k = 2 * π * n :=
  exists_isActionAngle hF hind hcomp hconn hne

example {c : ι → ℝ} (hc : ∀ i, 0 < c i) :
    (integralMap (oscillatorEnergy (ι := ι)) ⁻¹' {c}).Nonempty :=
  nonempty_oscillator_levelSet hc

example {c : ι → ℝ} (hc : ∀ i, 0 < c i) :
    ∃ (B : Set (ι → ℝ)) (J₀ : ι → ℝ) (Ψ : (ι → ℝ) × (ι → ℝ) → ι ⊕ ι → ℝ)
      (H : (ι → ℝ) → ι → ℝ) (ν : (ι → ℝ) → ι → ι → ℝ),
      IsActionAngle (oscillatorEnergy (ι := ι)) c B J₀ Ψ H ν ∧
      ∀ J ∈ B, ∀ J' ∈ B, ∀ φ φ' : ι → ℝ, Ψ (J, φ) = Ψ (J', φ') →
        J = J' ∧ ∀ k, ∃ n : ℤ, φ k - φ' k = 2 * π * n :=
  exists_isActionAngle_oscillators hc

end ActionAngle
