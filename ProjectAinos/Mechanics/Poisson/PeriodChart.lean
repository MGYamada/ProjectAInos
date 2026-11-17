/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Poisson.LagrangianSection
public import ProjectAinos.SmoothGeometry.ODE.PeriodFamily

/-!
# The chart of the joint flow near an invariant torus

For integrals `Fᵢ` in involution and a point `x₀` of a compact connected
regular level set:

* `sectionPoint F x₀ s = x₀ + Σₖ sₖ ∇Fₖ(x₀)` is a Lagrangian transversal, and
  `torusMap F x₀ (s, t) = g^t (sectionPoint F x₀ s)`.
* `IsPeriodChart F x₀ M S e`: on an open invariant set `M` and for `s` in an open
  set `S`, the points of the transversal are in `M` and `e k s` are periods of
  them, twice continuously differentiable in `s`. `exists_isPeriodChart`: such
  a chart exists, with `e k 0` a basis of the periods of `x₀`.
* `symplecticForm_torusMap`: in the co-ordinates `(s, t)` the symplectic form is
  `Σᵢ dtᵢ ∧ d(Fᵢ ∘ sectionPoint)`.
* `sum_fderiv_period_mul_symm`: the symmetry
  `Σᵢ (Deₖ a)ᵢ dFᵢ(L a′) = Σᵢ (Deₖ a′)ᵢ dFᵢ(L a)`, from the periodicity of the
  torus map.
-/

@[expose] public section
noncomputable section

open Set Module Filter
open scoped ContDiff Topology

namespace ProjectAinos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing
open SmoothGeometry SmoothGeometry.NonlinearODE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Hamiltonian fields of the integrals. -/
abbrev hamFields (F : ι → PhaseSpace ι) : ι → (ι ⊕ ι → ℝ) → ι ⊕ ι → ℝ :=
  fun i => hamiltonianField (F i)

/-- The point `x₀ + Σₖ sₖ ∇Fₖ(x₀)` of the Lagrangian transversal. -/
def sectionPoint (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (s : ι → ℝ) : ι ⊕ ι → ℝ :=
  x₀ + gradientMap F x₀ s

/-- The joint flow from the transversal: `(s, t) ↦ g^t (sectionPoint s)`. -/
def torusMap (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (p : (ι → ℝ) × (ι → ℝ)) :
    ι ⊕ ι → ℝ :=
  jointFlow (hamFields F) p.2 (sectionPoint F x₀ p.1)

theorem contDiff_hamFields (F : ι → PhaseSpace ι) (i : ι) : ContDiff ℝ ∞ (hamFields F i) :=
  contDiff_hamiltonianField (F i)

/-- A chart of periods near a point: an open invariant set `M`, an open set `S`
of parameters of the transversal, and periods `e k s` of the points of the
transversal. -/
structure IsPeriodChart (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (M : Set (ι ⊕ ι → ℝ))
    (S : Set (ι → ℝ)) (e : ι → (ι → ℝ) → ι → ℝ) : Prop where
  /-- The flows are complete on `M` and preserve it. -/
  invariant : IsInvariantSet (hamFields F) M
  isOpen_set : IsOpen M
  isOpen : IsOpen S
  zero_mem : (0 : ι → ℝ) ∈ S
  /-- The transversal over `S` is in `M`. -/
  mem : ∀ s ∈ S, sectionPoint F x₀ s ∈ M
  /-- `e k s` is a period of the point of the transversal. -/
  period : ∀ k, ∀ s ∈ S,
    jointFlow (hamFields F) (e k s) (sectionPoint F x₀ s) = sectionPoint F x₀ s
  contDiffAt : ∀ k, ∀ s ∈ S, ContDiffAt ℝ 2 (e k) s

/-- Near a point of a compact connected level set of integrals in involution
with independent differentials there is a chart of periods, whose periods at
the point are a basis of the lattice of the invariant torus. -/
theorem exists_isPeriodChart {F : ι → PhaseSpace ι}
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
          jointFlow (hamFields F) (∑ i, θ' i • b i) x₀ ↔ ∀ i, ∃ n : ℤ, θ i - θ' i = n := by
  have hX : ∀ i, ContDiff ℝ ∞ (hamFields F i) := contDiff_hamFields F
  have hc := pairwiseCommute_hamiltonianField hF
  have hFs := contDiff_integralMap F
  have htan : ∀ i z, fderiv ℝ (integralMap F) z (hamFields F i z) = 0 := fun i z =>
    fderiv_integralMap_hamiltonianField hF i z
  have hdim : finrank ℝ (ι ⊕ ι → ℝ) = Fintype.card ι + Fintype.card ι := by
    rw [finrank_fintype_fun_eq_card, Fintype.card_sum]
  obtain ⟨b, hb⟩ := exists_torus_chart_of_involution hF hind hcomp hconn
  obtain ⟨hbonto, hbiff, -⟩ := hb x₀ hx₀
  -- the basis vectors are periods
  have hbper : ∀ k, jointFlow (hamFields F) (b k) x₀ = x₀ := by
    intro k
    have h1 := (hbiff (Pi.single k 1) 0).mpr fun i => by
      by_cases hik : i = k
      · subst hik
        exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Pi.single_eq_of_ne hik]⟩
    have e1 : ∑ i, (Pi.single k (1 : ℝ) : ι → ℝ) i • b i = b k := by
      rw [Finset.sum_eq_single k]
      · rw [Pi.single_eq_same, one_smul]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, zero_smul]
      · intro h
        exact absurd (Finset.mem_univ k) h
    have e2 : ∑ i, (0 : ι → ℝ) i • b i = 0 := by simp
    rw [e1, e2, jointFlow_zero_apply] at h1
    exact h1
  -- the invariant neighbourhood
  obtain ⟨U, B, hUo, hBo, hMU, hcB, -, hinv⟩ := exists_isInvariantSet_tube hX hFs htan hcomp
  have hMo : IsOpen (integralMap F ⁻¹' B ∩ U) := (hBo.preimage hFs.continuous).inter hUo
  have hx₀M : x₀ ∈ integralMap F ⁻¹' B ∩ U := by
    refine ⟨?_, hMU hx₀⟩
    have h : integralMap F x₀ = c := hx₀
    change integralMap F x₀ ∈ B
    rw [h]
    exact hcB
  obtain ⟨N, hN⟩ := exists_gram_equiv (hind x₀ hx₀)
  have hindX := linearIndependent_hamiltonianField (hind x₀ hx₀)
  have hfam : ∀ k, ∃ (S : Set (ι → ℝ)) (e : (ι → ℝ) → ι → ℝ), IsOpen S ∧ (0 : ι → ℝ) ∈ S ∧
      e 0 = b k ∧ ContDiffAt ℝ ∞ e 0 ∧ ∀ s ∈ S, x₀ + gradientMap F x₀ s ∈
        integralMap F ⁻¹' B ∩ U ∧
        jointFlow (hamFields F) (e s) (x₀ + gradientMap F x₀ s) = x₀ + gradientMap F x₀ s :=
    fun k => exists_period_family hX hc hFs htan hinv hMo hx₀M hindX hdim (gradientMap F x₀) N hN
      (hbper k)
  choose Sk e hSo h0S he0 hsm hper using hfam
  have hTo : ∀ k, IsOpen {s : ι → ℝ | ContDiffAt ℝ 2 (e k) s} := fun k =>
    isOpen_iff_mem_nhds.mpr fun s hs =>
      (show ContDiffAt ℝ 2 (e k) s from hs).eventually (by norm_num)
  have h0T : ∀ k, (0 : ι → ℝ) ∈ {s : ι → ℝ | ContDiffAt ℝ 2 (e k) s} := fun k =>
    show ContDiffAt ℝ 2 (e k) 0 from (hsm k).of_le (by simp)
  refine ⟨b, integralMap F ⁻¹' B ∩ U, ⋂ k, (Sk k ∩ {s : ι → ℝ | ContDiffAt ℝ 2 (e k) s}), e,
    ⟨hinv, hMo, isOpen_iInter_of_finite fun k => (hSo k).inter (hTo k),
      mem_iInter.mpr fun k => ⟨h0S k, h0T k⟩, ?_, ?_, ?_⟩, he0, hbonto, hbiff⟩
  · intro s hs
    rcases isEmpty_or_nonempty ι with hne | ⟨⟨k⟩⟩
    · have hs0 : s = 0 := Subsingleton.elim _ _
      rw [sectionPoint, hs0, map_zero, add_zero]
      exact hx₀M
    · exact (hper k s (mem_iInter.mp hs k).1).1
  · intro k s hs
    exact (hper k s (mem_iInter.mp hs k).1).2
  · intro k s hs
    exact (mem_iInter.mp hs k).2

/-! ### The integrals on the transversal -/

/-- The values of the integrals on the transversal. -/
def sectionIntegral (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (s : ι → ℝ) : ι → ℝ :=
  integralMap F (sectionPoint F x₀ s)

/-- The derivative of the integrals along the transversal. -/
def sectionDeriv (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (s : ι → ℝ) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  (fderiv ℝ (integralMap F) (sectionPoint F x₀ s)).comp (gradientMap F x₀)

theorem sectionDeriv_apply (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (s a : ι → ℝ) (i : ι) :
    sectionDeriv F x₀ s a i =
      fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) (sectionPoint F x₀ s) (gradientMap F x₀ a) :=
  fderiv_integralMap_apply F _ _ i

theorem hasFDerivAt_sectionPoint (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (s : ι → ℝ) :
    HasFDerivAt (sectionPoint F x₀) (gradientMap F x₀) s :=
  (gradientMap F x₀).hasFDerivAt.const_add x₀

theorem contDiff_sectionPoint (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) :
    ContDiff ℝ ∞ (sectionPoint F x₀) :=
  contDiff_const.add (gradientMap F x₀).contDiff

theorem hasFDerivAt_sectionIntegral (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (s : ι → ℝ) :
    HasFDerivAt (sectionIntegral F x₀) (sectionDeriv F x₀ s) s :=
  ((contDiff_integralMap F).differentiable (by simp) _).hasFDerivAt.comp s
    (hasFDerivAt_sectionPoint F x₀ s)

theorem continuous_sectionDeriv (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) :
    Continuous (sectionDeriv F x₀) :=
  (((contDiff_integralMap F).continuous_fderiv (by simp)).comp
    (contDiff_sectionPoint F x₀).continuous).clm_comp continuous_const

/-! ### The torus map -/

section TorusMap

variable {F : ι → PhaseSpace ι} {x₀ : ι ⊕ ι → ℝ} {M : Set (ι ⊕ ι → ℝ)} {S : Set (ι → ℝ)}
  {e : ι → (ι → ℝ) → ι → ℝ}

/-- The integrals are constant on the image of the torus map over a point of
the transversal. -/
theorem IsPeriodChart.integralMap_torusMap (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {s : ι → ℝ} (hs : s ∈ S)
    (t : ι → ℝ) : integralMap F (torusMap F x₀ (s, t)) = sectionIntegral F x₀ s :=
  flow_jointField_levelSet (contDiff_hamFields F) (contDiff_integralMap F)
    (fun i z => fderiv_integralMap_hamiltonianField hF i z) t
    (h.invariant.mem_flowDomain t 1 _ (h.mem s hs))

theorem IsPeriodChart.torusMap_mem (h : IsPeriodChart F x₀ M S e) {s : ι → ℝ} (hs : s ∈ S)
    (t : ι → ℝ) : torusMap F x₀ (s, t) ∈ M :=
  jointFlow_mem h.invariant t (h.mem s hs)

theorem IsPeriodChart.contDiffAt_torusMap (h : IsPeriodChart F x₀ M S e) {s : ι → ℝ}
    (hs : s ∈ S) (t : ι → ℝ) : ContDiffAt ℝ ∞ (torusMap F x₀) (s, t) := by
  have h1 := contDiffAt_jointFlow (contDiff_hamFields F)
    (h.invariant.mem_flowDomain t 1 _ (h.mem s hs))
  exact ContDiffAt.comp (s, t)
    (g := fun p : (ι → ℝ) × (ι ⊕ ι → ℝ) => jointFlow (hamFields F) p.1 p.2)
    (f := fun p : (ι → ℝ) × (ι → ℝ) => (p.2, sectionPoint F x₀ p.1)) h1
    (contDiffAt_snd.prodMk ((contDiff_sectionPoint F x₀).contDiffAt.comp _ contDiffAt_fst))

/-- The derivative of the torus map: `(a, τ) ↦ Σᵢ τᵢ Xᵢ + D g^t (L a)`. -/
theorem IsPeriodChart.fderiv_torusMap (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {s : ι → ℝ} (hs : s ∈ S)
    (t a τ : ι → ℝ) :
    fderiv ℝ (torusMap F x₀) (s, t) (a, τ) =
      jointField (hamFields F) τ (torusMap F x₀ (s, t)) +
        fderiv ℝ (fun z => jointFlow (hamFields F) t z) (sectionPoint F x₀ s)
          (gradientMap F x₀ a) := by
  obtain ⟨D, hD, hDd⟩ := hasFDerivAt_jointFlow (contDiff_hamFields F)
    (pairwiseCommute_hamiltonianField hF) h.invariant t (h.mem s hs)
  have hsec : HasFDerivAt (fun p : (ι → ℝ) × (ι → ℝ) => sectionPoint F x₀ p.1)
      ((gradientMap F x₀).comp (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))) (s, t) :=
    HasFDerivAt.comp (s, t) (g := sectionPoint F x₀)
      (f := fun p : (ι → ℝ) × (ι → ℝ) => p.1) (hasFDerivAt_sectionPoint F x₀ s) hasFDerivAt_fst
  have hin : HasFDerivAt (fun p : (ι → ℝ) × (ι → ℝ) => (p.2, sectionPoint F x₀ p.1))
      ((ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)).prod
        ((gradientMap F x₀).comp (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)))) (s, t) :=
    hasFDerivAt_snd.prodMk hsec
  have hc := HasFDerivAt.comp (s, t)
    (g := fun p : (ι → ℝ) × (ι ⊕ ι → ℝ) => jointFlow (hamFields F) p.1 p.2)
    (f := fun p : (ι → ℝ) × (ι → ℝ) => (p.2, sectionPoint F x₀ p.1)) hDd hin
  have e1 : torusMap F x₀ =
      (fun p : (ι → ℝ) × (ι ⊕ ι → ℝ) => jointFlow (hamFields F) p.1 p.2) ∘
        fun p : (ι → ℝ) × (ι → ℝ) => (p.2, sectionPoint F x₀ p.1) := rfl
  rw [e1, hc.fderiv]
  exact hD τ (gradientMap F x₀ a)

/-- The symplectic form in the co-ordinates of the torus map: the times of the
joint flow are conjugate to the values of the integrals. -/
theorem IsPeriodChart.symplecticForm_torusMap (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {s : ι → ℝ} (hs : s ∈ S)
    (t a τ a' τ' : ι → ℝ) :
    symplecticForm ι (fderiv ℝ (torusMap F x₀) (s, t) (a, τ))
        (fderiv ℝ (torusMap F x₀) (s, t) (a', τ')) =
      ∑ i, (τ i * sectionDeriv F x₀ s a' i - τ' i * sectionDeriv F x₀ s a i) := by
  rw [h.fderiv_torusMap hF hs, h.fderiv_torusMap hF hs]
  have h1 := symplecticForm_jointFlow hF (h.invariant.mem_flowDomain t 1 _ (h.mem s hs)) τ τ'
    (gradientMap F x₀ a) (gradientMap F x₀ a')
  rw [symplecticForm_gradientMap hF, zero_add] at h1
  simp only [sectionDeriv_apply]
  exact h1

/-- The derivatives of a period are symmetric against the derivatives of the
integrals: the one-form `Σᵢ (eₖ)ᵢ dGᵢ` on the transversal is closed. -/
theorem IsPeriodChart.sum_fderiv_period_symm (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) (k : ι) {s : ι → ℝ}
    (hs : s ∈ S) (a a' : ι → ℝ) :
    ∑ i, (fderiv ℝ (e k) s a i * sectionDeriv F x₀ s a' i -
      fderiv ℝ (e k) s a' i * sectionDeriv F x₀ s a i) = 0 := by
  have hed : HasFDerivAt (e k) (fderiv ℝ (e k) s) s :=
    ((h.contDiffAt k s hs).differentiableAt (by simp)).hasFDerivAt
  have hT := ((h.contDiffAt_torusMap hs (e k s)).differentiableAt (by simp)).hasFDerivAt
  have hin : HasFDerivAt (fun s' : ι → ℝ => (s', e k s'))
      ((ContinuousLinearMap.id ℝ (ι → ℝ)).prod (fderiv ℝ (e k) s)) s :=
    (hasFDerivAt_id s).prodMk hed
  have hc := HasFDerivAt.comp s (g := torusMap F x₀) (f := fun s' : ι → ℝ => (s', e k s'))
    hT hin
  have heq : sectionPoint F x₀ =ᶠ[𝓝 s]
      torusMap F x₀ ∘ fun s' : ι → ℝ => (s', e k s') := by
    filter_upwards [h.isOpen.mem_nhds hs] with s' hs'
    exact (h.period k s' hs').symm
  have huniq := (hc.congr_of_eventuallyEq heq).unique (hasFDerivAt_sectionPoint F x₀ s)
  have hval : ∀ b : ι → ℝ, fderiv ℝ (torusMap F x₀) (s, e k s) (b, fderiv ℝ (e k) s b) =
      gradientMap F x₀ b := fun b =>
    congrArg (fun T : (ι → ℝ) →L[ℝ] (ι ⊕ ι → ℝ) => T b) huniq
  have h1 := h.symplecticForm_torusMap hF hs (e k s) a (fderiv ℝ (e k) s a) a'
    (fderiv ℝ (e k) s a')
  rw [hval, hval, symplecticForm_gradientMap hF] at h1
  exact h1.symm

end TorusMap

end ProjectAinos.Mechanics
