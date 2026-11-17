/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Poisson.LoopAction
public import ProjectAInos.Mechanics.Poisson.OscillatorTorus
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import ProjectAInos.SmoothGeometry.PeriodicInjective

/-!
# Action–angle variables near an invariant torus

The second half of the theorem of Liouville and Arnold (Landau–Lifshitz §52) on
the canonical phase space. Let `Fᵢ` be integrals in involution and let the
level set `F = c` be compact and connected with linearly independent
differentials. `exists_isActionAngle`: there are an open set `B` of values of
the action variables, a point `J₀` of it and a map `Ψ(J, φ)` to the phase
space such that (`IsActionAngle`)

* `Ψ` is continuously differentiable and canonical: the symplectic form is
  `Σₖ dφₖ ∧ dJₖ` in the co-ordinates `(J, φ)`;
* `Ψ` has the period `2π` in each angle;
* the integrals are functions of the actions, `Fᵢ(Ψ(J, φ)) = Hᵢ(J)`;
* the flow of `Fᵢ` is the uniform motion `φ ↦ φ + r ν` of the angles with the
  frequencies `νₖ = ∂Hᵢ/∂Jₖ`;
* `Jₖ = (1/2π) ∮ p dq` over the `k`-th cycle `r ↦ Ψ(J, φ + 2π r 1ₖ)`;
* `φ ↦ Ψ(J₀, φ)` maps onto the level set `F = c`, and two angles give the same
  point exactly when they differ by multiples of `2π`.

`IsActionAngle.flow_of_field`: the flow of a Hamiltonian whose field is
`Σᵢ wᵢ(F) X_{Fᵢ}`, as for a function of the integrals, is the uniform motion of
the angles with the velocities `Σᵢ wᵢ(H(J)) ν J i`; `flow_sum` is the case of a
linear combination.

The image of the chart is an open set that contains the level set
(`IsActionAngle.isOpen_image`, `levelSet_subset_image`), and for the chart of
the theorem `Ψ(J, φ) = Ψ(J′, φ′)` only when `J = J′` and the angles differ by
multiples of `2π` (`IsActionAngle.exists_injective`): the actions and the
angles modulo `2π` are co-ordinates on a neighbourhood of the torus.

The actions are the integrals `actionMap` on a transversal, whose derivative
`actionForm` is invertible at the torus; the inverse function theorem makes
them co-ordinates. `exists_isActionAngle_oscillators` is the instance of a
system of oscillators.
-/

@[expose] public section
noncomputable section

open Set Module Filter
open scoped ContDiff Topology Real

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing
open SmoothGeometry SmoothGeometry.NonlinearODE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Action–angle variables for the integrals `F` near the level set `F = c`:
the actions `J` in the open set `B`, the angles `φ`, the map `Ψ` to the phase
space, the integrals `H` as functions of the actions and the frequencies `ν`. -/
structure IsActionAngle (F : ι → PhaseSpace ι) (c : ι → ℝ) (B : Set (ι → ℝ)) (J₀ : ι → ℝ)
    (Ψ : (ι → ℝ) × (ι → ℝ) → ι ⊕ ι → ℝ) (H : (ι → ℝ) → ι → ℝ)
    (ν : (ι → ℝ) → ι → ι → ℝ) : Prop where
  isOpen : IsOpen B
  mem : J₀ ∈ B
  contDiffAt : ∀ J ∈ B, ∀ φ : ι → ℝ, ContDiffAt ℝ 1 Ψ (J, φ)
  /-- The symplectic form is `Σₖ dφₖ ∧ dJₖ`. -/
  canonical : ∀ J ∈ B, ∀ φ a α a' α' : ι → ℝ,
    symplecticForm ι (fderiv ℝ Ψ (J, φ) (a, α)) (fderiv ℝ Ψ (J, φ) (a', α')) =
      ∑ k, (α k * a' k - α' k * a k)
  /-- The period `2π` in each angle. -/
  periodic : ∀ J ∈ B, ∀ (φ : ι → ℝ) (n : ι → ℤ),
    Ψ (J, fun k => φ k + 2 * π * n k) = Ψ (J, φ)
  /-- The integrals are functions of the actions. -/
  integral : ∀ J ∈ B, ∀ φ : ι → ℝ, integralMap F (Ψ (J, φ)) = H J
  differentiableAt_integral : ∀ J ∈ B, DifferentiableAt ℝ H J
  /-- The frequencies are the derivatives of the integrals in the actions. -/
  fderiv_integral : ∀ J ∈ B, ∀ (a : ι → ℝ) (i : ι), fderiv ℝ H J a i = ∑ k, ν J i k * a k
  /-- The flow of an integral is a uniform motion of the angles. -/
  flow : ∀ J ∈ B, ∀ (φ : ι → ℝ) (i : ι) (r : ℝ),
    flow (hamiltonianField (F i)) (r, Ψ (J, φ)) = Ψ (J, φ + r • ν J i)
  /-- The actions are the integrals of `p dq` over the cycles, divided by `2π`. -/
  action : ∀ J ∈ B, ∀ (φ : ι → ℝ) (k : ι),
    (2 * π)⁻¹ * ∫ r in (0 : ℝ)..1, liouvilleForm ι (Ψ (J, cycleAngle k φ r))
      (deriv (fun t => Ψ (J, cycleAngle k φ t)) r) = J k
  /-- The torus `F = c` is the image of the angles at `J₀`. -/
  torus : ∀ y : ι ⊕ ι → ℝ, integralMap F y = c ↔ ∃ φ : ι → ℝ, Ψ (J₀, φ) = y
  torus_eq : ∀ φ φ' : ι → ℝ, Ψ (J₀, φ) = Ψ (J₀, φ') ↔ ∀ k, ∃ n : ℤ, φ k - φ' k = 2 * π * n

/-! ### Linear algebra -/

omit [DecidableEq ι] in
/-- A vector that is orthogonal to the vectors of a basis is zero. -/
theorem eq_zero_of_basis_dot_eq_zero (b : Basis ι ℝ (ι → ℝ)) {v : ι → ℝ}
    (h : ∀ k, ∑ i, b k i * v i = 0) : v = 0 := by
  have e1 : ∀ i, v i = ∑ k, b.repr v k * b k i := fun i => by
    have h1 := congrFun (b.sum_repr v) i
    rw [Finset.sum_apply] at h1
    exact h1.symm
  have hsq : ∑ i, v i * v i = 0 := by
    calc ∑ i, v i * v i = ∑ i, (∑ k, b.repr v k * b k i) * v i :=
          Finset.sum_congr rfl fun i _ => by rw [← e1 i]
      _ = ∑ k, b.repr v k * ∑ i, b k i * v i := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := Finset.sum_eq_zero fun k _ => by rw [h k, mul_zero]
  funext i
  exact mul_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    mul_self_nonneg (v i)).mp hsq i (Finset.mem_univ i))

/-- A linear map of `ℝ^ι` through its values on the unit vectors. -/
theorem clm_apply_eq_sum (T : (ι → ℝ) →L[ℝ] (ι → ℝ)) (a : ι → ℝ) (i : ι) :
    T a i = ∑ k, T (Pi.single k 1) i * a k := by
  have ha : a = ∑ k, a k • Pi.single k (1 : ℝ) := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · intro k _ hk
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hk), smul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  conv_lhs => rw [ha]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

section Chart

variable {F : ι → PhaseSpace ι} {x₀ : ι ⊕ ι → ℝ} {M : Set (ι ⊕ ι → ℝ)} {S : Set (ι → ℝ)}
  {e : ι → (ι → ℝ) → ι → ℝ}

/-- The frequencies: the times of the joint flow for the angular velocities
`∂Gᵢ/∂Jₖ` are the unit vector of the integral `Fᵢ`. -/
theorem angleTime_frequency {s : ι → ℝ} (A' : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    (hA' : (A' : (ι → ℝ) →L[ℝ] (ι → ℝ)) = actionForm F x₀ e s) (i : ι) :
    angleTime e s (fun k => sectionDeriv F x₀ s (A'.symm (Pi.single k 1)) i) =
      Pi.single i 1 := by
  have hAa : ∀ (a : ι → ℝ) (k : ι),
      A' a k = (2 * π)⁻¹ * ∑ j, e k s j * sectionDeriv F x₀ s a j := fun a k =>
    congrArg (fun T : (ι → ℝ) →L[ℝ] (ι → ℝ) => T a k) hA'
  have hinj : Function.Injective (sectionDeriv F x₀ s : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have ha' : sectionDeriv F x₀ s a = 0 := ha
    refine A'.injective ((funext fun k => ?_).trans (map_zero A').symm)
    rw [hAa, ha']
    simp
  obtain ⟨a, ha⟩ := (LinearMap.injective_iff_surjective.mp hinj)
    (angleTime e s (fun k => sectionDeriv F x₀ s (A'.symm (Pi.single k 1)) i) -
      Pi.single i 1)
  have ha' : sectionDeriv F x₀ s a =
      angleTime e s (fun k => sectionDeriv F x₀ s (A'.symm (Pi.single k 1)) i) -
        Pi.single i 1 := ha
  -- the pairing with the derivatives of the integrals
  have hpair : ∑ j, angleTime e s (fun k => sectionDeriv F x₀ s (A'.symm (Pi.single k 1)) i) j *
      sectionDeriv F x₀ s a j = sectionDeriv F x₀ s a i := by
    rw [sum_angleTime_mul]
    have h1 := clm_apply_eq_sum ((sectionDeriv F x₀ s).comp
      (A'.symm : (ι → ℝ) →L[ℝ] (ι → ℝ))) (A' a) i
    have h2 : ((sectionDeriv F x₀ s).comp (A'.symm : (ι → ℝ) →L[ℝ] (ι → ℝ))) (A' a) i =
        sectionDeriv F x₀ s a i := by
      change sectionDeriv F x₀ s (A'.symm (A' a)) i = _
      rw [A'.symm_apply_apply]
    rw [h2] at h1
    rw [h1]
    exact Finset.sum_congr rfl fun k _ => by rw [← hAa]; rfl
  have hunit : ∑ j, (Pi.single i (1 : ℝ) : ι → ℝ) j * sectionDeriv F x₀ s a j =
      sectionDeriv F x₀ s a i := by
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, one_mul]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hsq : ∑ j, sectionDeriv F x₀ s a j * sectionDeriv F x₀ s a j = 0 := by
    have h1 : ∀ j, sectionDeriv F x₀ s a j * sectionDeriv F x₀ s a j =
        angleTime e s (fun k => sectionDeriv F x₀ s (A'.symm (Pi.single k 1)) i) j *
            sectionDeriv F x₀ s a j -
          (Pi.single i (1 : ℝ) : ι → ℝ) j * sectionDeriv F x₀ s a j := fun j => by
      rw [← sub_mul]
      congr 1
      exact congrFun ha' j
    rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_sub_distrib, hpair, hunit, sub_self]
  have hzero : sectionDeriv F x₀ s a = 0 := funext fun j =>
    mul_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      mul_self_nonneg (sectionDeriv F x₀ s a j)).mp hsq j (Finset.mem_univ j))
  rw [hzero] at ha'
  exact (sub_eq_zero.mp ha'.symm)

theorem IsPeriodChart.contDiffAt_actionMap (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {s : ι → ℝ} (hs : s ∈ S) :
    ContDiffAt ℝ 1 (actionMap F x₀ e) s := by
  rw [contDiffAt_one_iff]
  exact ⟨actionForm F x₀ e, S, h.isOpen.mem_nhds hs, h.continuousOn_actionForm,
    fun s' hs' => h.hasFDerivAt_actionMap hF hs'⟩

/-- At the torus the differentials of the actions are linearly independent. -/
theorem exists_actionForm_equiv (b : Basis ι ℝ (ι → ℝ)) (hb : ∀ k, e k 0 = b k)
    (hind : LinearIndependent ℝ fun i => fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) x₀) :
    ∃ A₀ : (ι → ℝ) ≃L[ℝ] (ι → ℝ),
      (A₀ : (ι → ℝ) →L[ℝ] (ι → ℝ)) = actionForm F x₀ e 0 := by
  obtain ⟨N, hN⟩ := exists_gram_equiv hind
  have hsec : sectionPoint F x₀ 0 = x₀ := by rw [sectionPoint, map_zero, add_zero]
  have hDN : ∀ a, sectionDeriv F x₀ 0 a = N a := fun a => by
    rw [← hN a]
    change fderiv ℝ (integralMap F) (sectionPoint F x₀ 0) (gradientMap F x₀ a) = _
    rw [hsec]
  have hinj : Function.Injective (actionForm F x₀ e 0 : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hv : sectionDeriv F x₀ 0 a = 0 := by
      refine eq_zero_of_basis_dot_eq_zero b fun k => ?_
      have hk : (2 * π)⁻¹ * ∑ i, e k 0 i * sectionDeriv F x₀ 0 a i = 0 := congrFun ha k
      rw [← hb k]
      exact (mul_eq_zero.mp hk).resolve_left (inv_ne_zero (by positivity))
    rw [hDN] at hv
    exact N.injective (hv.trans (map_zero N).symm)
  exact ⟨(LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv,
    ContinuousLinearMap.ext fun a => rfl⟩

/-- The actions are co-ordinates near the torus: the inverse of `actionMap`. -/
theorem IsPeriodChart.exists_action_inverse (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0)
    (A₀ : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    (hA₀ : (A₀ : (ι → ℝ) →L[ℝ] (ι → ℝ)) = actionForm F x₀ e 0) :
    ∃ (B : Set (ι → ℝ)) (sOf : (ι → ℝ) → ι → ℝ), IsOpen B ∧ actionMap F x₀ e 0 ∈ B ∧
      sOf (actionMap F x₀ e 0) = 0 ∧
      ∀ J ∈ B, sOf J ∈ S ∧ actionMap F x₀ e (sOf J) = J ∧
        ∃ A' : (ι → ℝ) ≃L[ℝ] (ι → ℝ),
          (A' : (ι → ℝ) →L[ℝ] (ι → ℝ)) = actionForm F x₀ e (sOf J) ∧
          HasFDerivAt sOf (A'.symm : (ι → ℝ) →L[ℝ] (ι → ℝ)) J ∧ ContDiffAt ℝ 1 sOf J := by
  have hstrict : HasStrictFDerivAt (actionMap F x₀ e) (A₀ : (ι → ℝ) →L[ℝ] (ι → ℝ)) 0 := by
    rw [hA₀]
    refine hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt ?_
      (h.continuousOn_actionForm.continuousAt (h.isOpen.mem_nhds h.zero_mem))
    filter_upwards [h.isOpen.mem_nhds h.zero_mem] with s hs
    exact h.hasFDerivAt_actionMap hF hs
  obtain ⟨Ih, hIh⟩ : ∃ Ih : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ),
      Ih = hstrict.toOpenPartialHomeomorph (actionMap F x₀ e) := ⟨_, rfl⟩
  have hcoe : ⇑Ih = actionMap F x₀ e := by
    rw [hIh]
    exact hstrict.toOpenPartialHomeomorph_coe
  have h0src : (0 : ι → ℝ) ∈ Ih.source := by
    rw [hIh]
    exact hstrict.mem_toOpenPartialHomeomorph_source
  obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Set (ι → ℝ), S₁ = S ∩ actionForm F x₀ e ⁻¹'
      range ((↑) : ((ι → ℝ) ≃L[ℝ] (ι → ℝ)) → (ι → ℝ) →L[ℝ] (ι → ℝ)) := ⟨_, rfl⟩
  have hS₁o : IsOpen S₁ := by
    rw [hS₁]
    exact h.continuousOn_actionForm.isOpen_inter_preimage h.isOpen ContinuousLinearEquiv.isOpen
  have h0S₁ : (0 : ι → ℝ) ∈ S₁ := by
    rw [hS₁]
    exact ⟨h.zero_mem, A₀, hA₀⟩
  have hl : Ih.symm (actionMap F x₀ e 0) = 0 := by
    have h1 := Ih.left_inv h0src
    rwa [hcoe] at h1
  refine ⟨Ih.target ∩ Ih.symm ⁻¹' S₁, Ih.symm, Ih.isOpen_inter_preimage_symm hS₁o, ⟨?_, ?_⟩,
    hl, ?_⟩
  · have h1 := Ih.map_source h0src
    rwa [hcoe] at h1
  · change Ih.symm (actionMap F x₀ e 0) ∈ S₁
    rw [hl]
    exact h0S₁
  · intro J hJ
    have hsS₁ : Ih.symm J ∈ S₁ := hJ.2
    rw [hS₁] at hsS₁
    obtain ⟨hsS, A', hA'⟩ := hsS₁
    have hr := Ih.right_inv hJ.1
    rw [hcoe] at hr
    have hder : HasFDerivAt Ih (A' : (ι → ℝ) →L[ℝ] (ι → ℝ)) (Ih.symm J) := by
      rw [hcoe, hA']
      exact h.hasFDerivAt_actionMap hF hsS
    refine ⟨hsS, hr, A', hA', Ih.hasFDerivAt_symm hJ.1 hder, Ih.contDiffAt_symm hJ.1 hder ?_⟩
    rw [hcoe]
    exact h.contDiffAt_actionMap hF hsS

/-- The derivative of the angle map in the co-ordinates of the actions. -/
theorem IsPeriodChart.fderiv_angleMap_comp (h : IsPeriodChart F x₀ M S e)
    {sOf : (ι → ℝ) → ι → ℝ} {J : ι → ℝ} (hs : sOf J ∈ S) {D : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hD : HasFDerivAt sOf D J) (φ a α : ι → ℝ) :
    fderiv ℝ (fun p : (ι → ℝ) × (ι → ℝ) => angleMap F x₀ e (sOf p.1, p.2)) (J, φ) (a, α) =
      fderiv ℝ (angleMap F x₀ e) (sOf J, φ) (D a, α) := by
  have hA := ((h.contDiffAt_angleMap hs φ).differentiableAt (by simp)).hasFDerivAt
  have h1 : HasFDerivAt (fun p : (ι → ℝ) × (ι → ℝ) => sOf p.1)
      (D.comp (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))) (J, φ) :=
    HasFDerivAt.comp (J, φ) (g := sOf) (f := fun p : (ι → ℝ) × (ι → ℝ) => p.1) hD
      hasFDerivAt_fst
  have hin : HasFDerivAt (fun p : (ι → ℝ) × (ι → ℝ) => (sOf p.1, p.2))
      ((D.comp (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))).prod
        (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))) (J, φ) :=
    h1.prodMk hasFDerivAt_snd
  have hc := HasFDerivAt.comp (J, φ) (g := angleMap F x₀ e)
    (f := fun p : (ι → ℝ) × (ι → ℝ) => (sOf p.1, p.2)) hA hin
  have e1 : (fun p : (ι → ℝ) × (ι → ℝ) => angleMap F x₀ e (sOf p.1, p.2)) =
      angleMap F x₀ e ∘ fun p : (ι → ℝ) × (ι → ℝ) => (sOf p.1, p.2) := rfl
  rw [e1, hc.fderiv]
  rfl

/-- A chart of periods that are, at the base point, a basis of the lattice of
the torus gives action–angle variables. -/
theorem IsPeriodChart.exists_isActionAngle (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {c : ι → ℝ}
    (hx₀ : integralMap F x₀ = c)
    (hind : LinearIndependent ℝ fun i => fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) x₀)
    (b : Basis ι ℝ (ι → ℝ)) (hb : ∀ k, e k 0 = b k)
    (honto : ∀ y ∈ integralMap F ⁻¹' {c}, ∃ θ : ι → ℝ,
      jointFlow (hamFields F) (∑ i, θ i • b i) x₀ = y)
    (hiff : ∀ θ θ' : ι → ℝ, jointFlow (hamFields F) (∑ i, θ i • b i) x₀ =
      jointFlow (hamFields F) (∑ i, θ' i • b i) x₀ ↔ ∀ i, ∃ n : ℤ, θ i - θ' i = n) :
    ∃ (B : Set (ι → ℝ)) (J₀ : ι → ℝ) (Ψ : (ι → ℝ) × (ι → ℝ) → ι ⊕ ι → ℝ)
      (H : (ι → ℝ) → ι → ℝ) (ν : (ι → ℝ) → ι → ι → ℝ), IsActionAngle F c B J₀ Ψ H ν := by
  have hπ : (2 * π) ≠ 0 := by positivity
  obtain ⟨A₀, hA₀⟩ := exists_actionForm_equiv b hb hind
  obtain ⟨B, sOf, hBo, hJ₀, hs₀, hB⟩ := h.exists_action_inverse hF A₀ hA₀
  have hsec : sectionPoint F x₀ 0 = x₀ := by rw [sectionPoint, map_zero, add_zero]
  have hcentral : ∀ φ : ι → ℝ, angleMap F x₀ e (sOf (actionMap F x₀ e 0), φ) =
      jointFlow (hamFields F) (∑ k, (φ k / (2 * π)) • b k) x₀ := by
    intro φ
    rw [hs₀]
    change jointFlow (hamFields F) (angleTime e 0 φ) (sectionPoint F x₀ 0) = _
    rw [hsec, angleTime]
    simp only [hb]
  have hinv : ∀ (J : ι → ℝ) (A' : (ι → ℝ) ≃L[ℝ] (ι → ℝ)),
      (A' : (ι → ℝ) →L[ℝ] (ι → ℝ)) = actionForm F x₀ e (sOf J) →
      (actionForm F x₀ e (sOf J)).inverse = (A'.symm : (ι → ℝ) →L[ℝ] (ι → ℝ)) :=
    fun J A' hA' => by rw [← hA', ContinuousLinearMap.inverse_equiv]
  have hH : ∀ (J : ι → ℝ) (A' : (ι → ℝ) ≃L[ℝ] (ι → ℝ)),
      HasFDerivAt sOf (A'.symm : (ι → ℝ) →L[ℝ] (ι → ℝ)) J →
      HasFDerivAt (fun J => sectionIntegral F x₀ (sOf J))
        ((sectionDeriv F x₀ (sOf J)).comp (A'.symm : (ι → ℝ) →L[ℝ] (ι → ℝ))) J :=
    fun J A' hder => HasFDerivAt.comp J (g := sectionIntegral F x₀) (f := sOf)
      (hasFDerivAt_sectionIntegral F x₀ (sOf J)) hder
  refine ⟨B, actionMap F x₀ e 0, fun p => angleMap F x₀ e (sOf p.1, p.2),
    fun J => sectionIntegral F x₀ (sOf J),
    fun J i k => sectionDeriv F x₀ (sOf J)
      ((actionForm F x₀ e (sOf J)).inverse (Pi.single k 1)) i,
    { isOpen := hBo, mem := hJ₀, contDiffAt := ?_, canonical := ?_, periodic := ?_,
      integral := ?_, differentiableAt_integral := ?_, fderiv_integral := ?_, flow := ?_,
      action := ?_, torus := ?_, torus_eq := ?_ }⟩
  · intro J hJ φ
    obtain ⟨hs, -, A', -, -, hsm⟩ := hB J hJ
    exact ContDiffAt.comp (J, φ) (g := angleMap F x₀ e)
      (f := fun p : (ι → ℝ) × (ι → ℝ) => (sOf p.1, p.2))
      ((h.contDiffAt_angleMap hs φ).of_le (by norm_num))
      ((ContDiffAt.comp (J, φ) (g := sOf) (f := fun p : (ι → ℝ) × (ι → ℝ) => p.1) hsm
        contDiffAt_fst).prodMk contDiffAt_snd)
  · intro J hJ φ a α a' α'
    obtain ⟨hs, -, A', hA', hder, -⟩ := hB J hJ
    rw [h.fderiv_angleMap_comp hs hder, h.fderiv_angleMap_comp hs hder,
      h.symplecticForm_angleMap hF hs]
    have hAA : ∀ v : ι → ℝ,
        actionForm F x₀ e (sOf J) ((A'.symm : (ι → ℝ) →L[ℝ] (ι → ℝ)) v) = v := fun v => by
      rw [← hA']
      exact A'.apply_symm_apply v
    rw [hAA, hAA]
  · exact fun J hJ φ n => h.angleMap_add_period hF (hB J hJ).1 φ n
  · exact fun J hJ φ => h.integralMap_angleMap hF (hB J hJ).1 φ
  · intro J hJ
    obtain ⟨-, -, A', -, hder, -⟩ := hB J hJ
    exact (hH J A' hder).differentiableAt
  · intro J hJ a i
    obtain ⟨-, -, A', hA', hder, -⟩ := hB J hJ
    rw [(hH J A' hder).fderiv, clm_apply_eq_sum ((sectionDeriv F x₀ (sOf J)).comp
      (A'.symm : (ι → ℝ) →L[ℝ] (ι → ℝ))) a i, hinv J A' hA']
    rfl
  · intro J hJ φ i r
    obtain ⟨hs, -, A', hA', -, -⟩ := hB J hJ
    have hν := angleTime_frequency (F := F) (x₀ := x₀) (e := e) A' hA' i
    have h1 := h.flow_hamiltonianField_angleMap hF hs φ i hν r
    change NonlinearODE.flow (hamiltonianField (F i)) (r, angleMap F x₀ e (sOf J, φ)) =
      angleMap F x₀ e (sOf J, φ + r • fun k => sectionDeriv F x₀ (sOf J)
        ((actionForm F x₀ e (sOf J)).inverse (Pi.single k 1)) i)
    rw [hinv J A' hA']
    exact h1
  · intro J hJ φ k
    obtain ⟨hs, hI, -⟩ := hB J hJ
    have h1 := h.loopAction_eq hF k hs φ
    have h2 : loopAction F x₀ e k (sOf J, 0) = J k := congrFun hI k
    exact h1.trans h2
  · intro y
    constructor
    · intro hy
      obtain ⟨θ, hθ⟩ := honto y hy
      refine ⟨fun k => 2 * π * θ k, ?_⟩
      change angleMap F x₀ e (sOf (actionMap F x₀ e 0), fun k => 2 * π * θ k) = y
      rw [hcentral, ← hθ]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_div_cancel_left₀ _ hπ]
    · rintro ⟨φ, rfl⟩
      refine (h.integralMap_angleMap hF (hB _ hJ₀).1 φ).trans ?_
      rw [hs₀]
      change integralMap F (sectionPoint F x₀ 0) = c
      rw [hsec]
      exact hx₀
  · intro φ φ'
    change angleMap F x₀ e (sOf (actionMap F x₀ e 0), φ) =
      angleMap F x₀ e (sOf (actionMap F x₀ e 0), φ') ↔ _
    rw [hcentral, hcentral, hiff]
    refine forall_congr' fun k => exists_congr fun n => ?_
    rw [← sub_div, div_eq_iff hπ, mul_comm (n : ℝ)]

end Chart

/-! ### The chart of the action–angle variables -/

section General

variable {F : ι → PhaseSpace ι} {c : ι → ℝ} {B : Set (ι → ℝ)} {J₀ : ι → ℝ}
  {Ψ : (ι → ℝ) × (ι → ℝ) → ι ⊕ ι → ℝ} {H : (ι → ℝ) → ι → ℝ} {ν : (ι → ℝ) → ι → ι → ℝ}

/-- The derivative of the canonical map `Ψ` is injective. -/
theorem IsActionAngle.injective_fderiv (h : IsActionAngle F c B J₀ Ψ H ν) {J : ι → ℝ}
    (hJ : J ∈ B) (φ : ι → ℝ) : Function.Injective (fderiv ℝ Ψ (J, φ)) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨a, α⟩ hz
  have h1 := h.canonical J hJ φ a α α 0
  have h2 := h.canonical J hJ φ a α 0 a
  rw [hz, map_zero, _root_.zero_apply] at h1 h2
  have hα : α = 0 := by
    have hs : ∑ k, α k * α k = 0 := by
      have h3 := h1.symm
      simpa using h3
    exact funext fun k => mul_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
      mul_self_nonneg (α k)).mp hs k (Finset.mem_univ k))
  have ha : a = 0 := by
    have hs : ∑ k, a k * a k = 0 := by
      have h3 := h2.symm
      rw [hα] at h3
      simpa using h3
    exact funext fun k => mul_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
      mul_self_nonneg (a k)).mp hs k (Finset.mem_univ k))
  rw [ha, hα]
  rfl

/-- The derivative of `Ψ` is invertible. -/
theorem IsActionAngle.exists_fderiv_equiv (h : IsActionAngle F c B J₀ Ψ H ν) {J : ι → ℝ}
    (hJ : J ∈ B) (φ : ι → ℝ) :
    ∃ D : ((ι → ℝ) × (ι → ℝ)) ≃L[ℝ] (ι ⊕ ι → ℝ),
      (D : (ι → ℝ) × (ι → ℝ) →L[ℝ] (ι ⊕ ι → ℝ)) = fderiv ℝ Ψ (J, φ) := by
  have hdim : finrank ℝ ((ι → ℝ) × (ι → ℝ)) = finrank ℝ (ι ⊕ ι → ℝ) := by
    rw [finrank_prod, finrank_fintype_fun_eq_card, finrank_fintype_fun_eq_card,
      Fintype.card_sum]
  exact ⟨(LinearMap.linearEquivOfInjective
    (fderiv ℝ Ψ (J, φ) : (ι → ℝ) × (ι → ℝ) →ₗ[ℝ] (ι ⊕ ι → ℝ)) (h.injective_fderiv hJ φ)
    hdim).toContinuousLinearEquiv, ContinuousLinearMap.ext fun v => rfl⟩

/-- `Ψ` is injective near every point. -/
theorem IsActionAngle.exists_injOn_nhds (h : IsActionAngle F c B J₀ Ψ H ν) {J : ι → ℝ}
    (hJ : J ∈ B) (φ : ι → ℝ) :
    ∃ U ∈ 𝓝 ((J, φ) : (ι → ℝ) × (ι → ℝ)), InjOn Ψ U := by
  obtain ⟨D, hD⟩ := h.exists_fderiv_equiv hJ φ
  have hstrict : HasStrictFDerivAt Ψ (D : (ι → ℝ) × (ι → ℝ) →L[ℝ] (ι ⊕ ι → ℝ)) (J, φ) := by
    rw [hD]
    exact (h.contDiffAt J hJ φ).hasStrictFDerivAt (by simp)
  refine ⟨(hstrict.toOpenPartialHomeomorph Ψ).source,
    (hstrict.toOpenPartialHomeomorph Ψ).open_source.mem_nhds
      hstrict.mem_toOpenPartialHomeomorph_source, ?_⟩
  have hinj := (hstrict.toOpenPartialHomeomorph Ψ).injOn
  rwa [hstrict.toOpenPartialHomeomorph_coe] at hinj

/-- The image of the chart is open. -/
theorem IsActionAngle.isOpen_image (h : IsActionAngle F c B J₀ Ψ H ν) :
    IsOpen (Ψ '' (B ×ˢ (univ : Set (ι → ℝ)))) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨⟨J, φ⟩, ⟨hJ, -⟩, rfl⟩
  obtain ⟨D, hD⟩ := h.exists_fderiv_equiv hJ φ
  have hstrict : HasStrictFDerivAt Ψ (D : (ι → ℝ) × (ι → ℝ) →L[ℝ] (ι ⊕ ι → ℝ)) (J, φ) := by
    rw [hD]
    exact (h.contDiffAt J hJ φ).hasStrictFDerivAt (by simp)
  rw [← hstrict.map_nhds_eq_of_equiv]
  exact Filter.image_mem_map ((h.isOpen.prod isOpen_univ).mem_nhds ⟨hJ, mem_univ φ⟩)

/-- The image of the chart contains the level set. -/
theorem IsActionAngle.levelSet_subset_image (h : IsActionAngle F c B J₀ Ψ H ν) :
    integralMap F ⁻¹' {c} ⊆ Ψ '' (B ×ˢ (univ : Set (ι → ℝ))) := fun y hy => by
  obtain ⟨φ, hφ⟩ := (h.torus y).mp hy
  exact ⟨(J₀, φ), ⟨h.mem, mem_univ φ⟩, hφ⟩

/-- The field of `Fᵢ` in the co-ordinates of the chart: the velocity `ν J i` of
the angles. -/
theorem IsActionAngle.fderiv_frequency (h : IsActionAngle F c B J₀ Ψ H ν) {J : ι → ℝ}
    (hJ : J ∈ B) (φ : ι → ℝ) (i : ι) :
    fderiv ℝ Ψ (J, φ) (0, ν J i) = hamiltonianField (F i) (Ψ (J, φ)) := by
  have hΨ := ((h.contDiffAt J hJ φ).differentiableAt (by simp)).hasFDerivAt
  have h1 := Variational.hasDerivAt_line hΨ ((0 : ι → ℝ), ν J i)
  have h2 := hasDerivAt_flow (contDiff_hamiltonianField (F i))
    (zero_mem_flowDomain (hamiltonianField (F i)) (Ψ (J, φ)))
  rw [flow_zero] at h2
  have e1 : (fun r : ℝ => Ψ ((J, φ) + r • ((0 : ι → ℝ), ν J i))) =
      fun r : ℝ => NonlinearODE.flow (hamiltonianField (F i)) (r, Ψ (J, φ)) := by
    funext r
    rw [h.flow J hJ φ i r, Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero]
  rw [e1] at h1
  exact h1.unique h2

/-- The flow of a Hamiltonian `K` that is a function of the integrals, in the
sense that its field is `Σᵢ wᵢ(F) X_{Fᵢ}`: a uniform motion of the angles with
the velocities `Σᵢ wᵢ(H(J)) ν J i`. -/
theorem IsActionAngle.flow_of_field (h : IsActionAngle F c B J₀ Ψ H ν) (K : PhaseSpace ι)
    (w : (ι → ℝ) → ι → ℝ)
    (hK : ∀ z, hamiltonianField K z = ∑ i, w (integralMap F z) i • hamiltonianField (F i) z)
    {J : ι → ℝ} (hJ : J ∈ B) (φ : ι → ℝ) (r : ℝ) :
    NonlinearODE.flow (hamiltonianField K) (r, Ψ (J, φ)) =
      Ψ (J, φ + r • ∑ i, w (H J) i • ν J i) := by
  obtain ⟨ν', hν'⟩ : ∃ ν' : ι → ℝ, ν' = ∑ i, w (H J) i • ν J i := ⟨_, rfl⟩
  rw [← hν']
  have hcurve : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Ψ (J, φ + t • ν'))
      (hamiltonianField K (Ψ (J, φ + t • ν'))) t := by
    intro t
    have hΨ := ((h.contDiffAt J hJ (φ + t • ν')).differentiableAt (by simp)).hasFDerivAt
    have h1 := Variational.hasDerivAt_line_sub hΨ ((0 : ι → ℝ), ν') t
    have e1 : (fun t' : ℝ => Ψ ((J, φ + t • ν') + (t' - t) • ((0 : ι → ℝ), ν'))) =
        fun t' : ℝ => Ψ (J, φ + t' • ν') := by
      funext t'
      rw [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero, add_assoc, ← add_smul,
        add_sub_cancel]
    rw [e1] at h1
    refine h1.congr_deriv ?_
    rw [hK, h.integral J hJ]
    have e2 : ((0 : ι → ℝ), ν') = ∑ i, w (H J) i • ((0 : ι → ℝ), ν J i) := by
      rw [hν']
      refine Prod.ext ?_ ?_
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum]
    rw [e2, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, h.fderiv_frequency hJ]
  exact flow_eq_of_hasDerivWithinAt (X := hamiltonianField K) (x := Ψ (J, φ)) (t := r)
    ((contDiff_hamiltonianField K).of_le (by simp)) (y := fun t => Ψ (J, φ + t • ν'))
    (by simp) (fun t _ => (hcurve t).hasDerivWithinAt)

/-- The flow of a linear combination of the integrals: an instance of the
hypothesis of `flow_of_field`. -/
theorem IsActionAngle.flow_sum (h : IsActionAngle F c B J₀ Ψ H ν) (a : ι → ℝ) {J : ι → ℝ}
    (hJ : J ∈ B) (φ : ι → ℝ) (r : ℝ) :
    NonlinearODE.flow (hamiltonianField (∑ i, a i • F i)) (r, Ψ (J, φ)) =
      Ψ (J, φ + r • ∑ i, a i • ν J i) :=
  h.flow_of_field (∑ i, a i • F i) (fun _ => a)
    (fun z => by
      rw [← jointField_hamiltonianField]
      rfl) hJ φ r

/-- On a smaller set of actions the chart is injective up to the periods of
the angles: the actions and the angles modulo `2π` are functions of the point. -/
theorem IsActionAngle.exists_injective (h : IsActionAngle F c B J₀ Ψ H ν) :
    ∃ B' : Set (ι → ℝ), B' ⊆ B ∧ IsActionAngle F c B' J₀ Ψ H ν ∧
      ∀ J ∈ B', ∀ J' ∈ B', ∀ φ φ' : ι → ℝ, Ψ (J, φ) = Ψ (J', φ') →
        J = J' ∧ ∀ k, ∃ n : ℤ, φ k - φ' k = 2 * π * n := by
  obtain ⟨B', hsub, hB'o, hJ₀', hinj⟩ := exists_injOn_modPeriod (T := 2 * π) (by positivity)
    h.isOpen h.mem (fun φ => (h.contDiffAt J₀ h.mem φ).continuousAt)
    (fun φ => h.exists_injOn_nhds h.mem φ) h.periodic (fun φ φ' => (h.torus_eq φ φ').mp)
  exact ⟨B', hsub,
    { isOpen := hB'o
      mem := hJ₀'
      contDiffAt := fun J hJ => h.contDiffAt J (hsub hJ)
      canonical := fun J hJ => h.canonical J (hsub hJ)
      periodic := fun J hJ => h.periodic J (hsub hJ)
      integral := fun J hJ => h.integral J (hsub hJ)
      differentiableAt_integral := fun J hJ => h.differentiableAt_integral J (hsub hJ)
      fderiv_integral := fun J hJ => h.fderiv_integral J (hsub hJ)
      flow := fun J hJ => h.flow J (hsub hJ)
      action := fun J hJ => h.action J (hsub hJ)
      torus := h.torus
      torus_eq := h.torus_eq }, hinj⟩

end General

/-- Landau–Lifshitz §52, the theorem of Liouville and Arnold: near a compact
connected level set of integrals in involution with linearly independent
differentials there are action–angle variables. The chart `Ψ` is injective up
to the periods of the angles. -/
theorem exists_isActionAngle {F : ι → PhaseSpace ι}
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {c : ι → ℝ}
    (hind : ∀ z ∈ integralMap F ⁻¹' {c},
      LinearIndependent ℝ fun i => fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) z)
    (hcomp : IsCompact (integralMap F ⁻¹' {c}))
    (hconn : IsPreconnected (integralMap F ⁻¹' {c}))
    (hne : (integralMap F ⁻¹' {c}).Nonempty) :
    ∃ (B : Set (ι → ℝ)) (J₀ : ι → ℝ) (Ψ : (ι → ℝ) × (ι → ℝ) → ι ⊕ ι → ℝ)
      (H : (ι → ℝ) → ι → ℝ) (ν : (ι → ℝ) → ι → ι → ℝ), IsActionAngle F c B J₀ Ψ H ν ∧
      ∀ J ∈ B, ∀ J' ∈ B, ∀ φ φ' : ι → ℝ, Ψ (J, φ) = Ψ (J', φ') →
        J = J' ∧ ∀ k, ∃ n : ℤ, φ k - φ' k = 2 * π * n := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨b, M, S, e, h, hb, honto, hiff⟩ := exists_isPeriodChart hF hind hcomp hconn hx₀
  obtain ⟨B, J₀, Ψ, H, ν, hAA⟩ :=
    h.exists_isActionAngle hF hx₀ (hind x₀ hx₀) b hb honto hiff
  obtain ⟨B', -, hAA', hinj⟩ := hAA.exists_injective
  exact ⟨B', J₀, Ψ, H, ν, hAA', hinj⟩

omit [Fintype ι] [DecidableEq ι] in
/-- The level set of the energies of a system of oscillators is not empty. -/
theorem nonempty_oscillator_levelSet {c : ι → ℝ} (hc : ∀ i, 0 < c i) :
    (integralMap (oscillatorEnergy (ι := ι)) ⁻¹' {c}).Nonempty := by
  refine ⟨fun a => Sum.elim (fun i => √(2 * c i)) (fun _ => 0) a, funext fun i => ?_⟩
  change (oscillatorEnergy i).val _ = c i
  rw [oscillatorEnergy_val]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [Real.sq_sqrt (by have := hc i; positivity)]
  ring

/-- Action–angle variables of a system of oscillators with positive energies:
an instance of all the hypotheses. -/
theorem exists_isActionAngle_oscillators {c : ι → ℝ} (hc : ∀ i, 0 < c i) :
    ∃ (B : Set (ι → ℝ)) (J₀ : ι → ℝ) (Ψ : (ι → ℝ) × (ι → ℝ) → ι ⊕ ι → ℝ)
      (H : (ι → ℝ) → ι → ℝ) (ν : (ι → ℝ) → ι → ι → ℝ),
      IsActionAngle (oscillatorEnergy (ι := ι)) c B J₀ Ψ H ν ∧
      ∀ J ∈ B, ∀ J' ∈ B, ∀ φ φ' : ι → ℝ, Ψ (J, φ) = Ψ (J', φ') →
        J = J' ∧ ∀ k, ∃ n : ℤ, φ k - φ' k = 2 * π * n :=
  exists_isActionAngle bracket_oscillatorEnergy
    (fun _ hz => linearIndependent_fderiv_oscillatorEnergy hc hz)
    (isCompact_oscillator_levelSet c) (isPreconnected_oscillator_levelSet hc)
    (nonempty_oscillator_levelSet hc)

end ProjectAInos.Mechanics
