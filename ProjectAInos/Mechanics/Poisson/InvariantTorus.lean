/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Poisson.HamiltonianField
public import ProjectAInos.SmoothGeometry.ODE.LevelSetFlow

/-!
# Invariant tori of commuting integrals

Landau–Lifshitz §52, the first half of the theorem of Liouville and Arnold on
the canonical phase space `ι ⊕ ι → ℝ`. Let `Fᵢ`, `i ∈ ι`, be elements of the
phase space ring with `{Fᵢ, Fⱼ} = 0`.

* `fderiv_val_hamiltonianField`: the derivative of `G` along the Hamiltonian
  field of `H` is the value of `{G, H}`.
* `pairwiseCommute_hamiltonianField`: the Hamiltonian fields of the `Fᵢ`
  commute, by the Jacobi identity. `fderiv_integralMap_hamiltonianField`: they
  are tangent to the level sets of `F = (Fᵢ)`.
* `exists_torus_chart_of_involution`: a compact connected level set of `F` on
  which the differentials `dFᵢ` are linearly independent carries angles `θ`
  with the periods `1`: every point of the level set is `g^{Σ θᵢ bᵢ} z`, two
  angles give the same point exactly when they differ by integers, and the
  flow of the Hamiltonian `Σᵢ sᵢ Fᵢ` is a uniform motion of the angles. The
  motion is conditionally periodic.
-/

@[expose] public section
noncomputable section

open Set Module
open scoped ContDiff

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing
open SmoothGeometry SmoothGeometry.NonlinearODE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The integrals as a map from the phase space to `ℝ^ι`. -/
def integralMap (F : ι → PhaseSpace ι) (z : ι ⊕ ι → ℝ) : ι → ℝ := fun i => (F i).val z

omit [DecidableEq ι] in
theorem contDiff_integralMap (F : ι → PhaseSpace ι) : ContDiff ℝ ∞ (integralMap F) :=
  contDiff_pi.mpr fun i => contDiff_val (F i)

omit [DecidableEq ι] in
theorem fderiv_integralMap_apply (F : ι → PhaseSpace ι) (z w : ι ⊕ ι → ℝ) (i : ι) :
    fderiv ℝ (integralMap F) z w i = fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) z w := by
  have hd : DifferentiableAt ℝ (integralMap F) z :=
    (contDiff_integralMap F).differentiable (by simp) z
  have hcomp := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).hasFDerivAt.comp z
    hd.hasFDerivAt
  exact (congrArg (fun L : (ι ⊕ ι → ℝ) →L[ℝ] ℝ => L w) hcomp.fderiv).symm

/-- The derivative of `G` along the Hamiltonian field of `H` is `{G, H}`. -/
theorem fderiv_val_hamiltonianField (G H : PhaseSpace ι) (z : ι ⊕ ι → ℝ) :
    fderiv ℝ (G.val : (ι ⊕ ι → ℝ) → ℝ) z (hamiltonianField H z) =
      ((PhaseSpace.canonical ι).bracket G H).val z := by
  rw [fderiv_val_apply, Fintype.sum_sum_type, PhaseSpace.canonical_bracket]
  simp only [hamiltonianField_inl, hamiltonianField_inr]
  rw [← Finset.sum_add_distrib]
  have hsum : ∀ (f : ι → PhaseSpace ι) (z : ι ⊕ ι → ℝ), (∑ i, f i).val z = ∑ i, (f i).val z :=
    fun f z => by
      rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change _ = (partialDerivation (Sum.inl i) G).val z * (partialDerivation (Sum.inr i) H).val z -
    (partialDerivation (Sum.inr i) G).val z * (partialDerivation (Sum.inl i) H).val z
  ring

/-- The Hamiltonian fields of commuting integrals are tangent to the level sets
of the integrals. -/
theorem fderiv_integralMap_hamiltonianField {F : ι → PhaseSpace ι}
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) (i : ι) (z : ι ⊕ ι → ℝ) :
    fderiv ℝ (integralMap F) z (hamiltonianField (F i) z) = 0 := by
  funext j
  rw [fderiv_integralMap_apply, fderiv_val_hamiltonianField, hF j i]
  rfl

/-- The Hamiltonian fields of commuting integrals commute. -/
theorem pairwiseCommute_hamiltonianField {F : ι → PhaseSpace ι}
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) :
    PairwiseCommute fun i => hamiltonianField (F i) := by
  intro i j z
  funext a
  have key : ∀ (i j : ι), fderiv ℝ (hamiltonianField (F i)) z (hamiltonianField (F j) z) a =
      ((PhaseSpace.canonical ι).bracket
        ((PhaseSpace.canonical ι).bracket (generator a) (F i)) (F j)).val z := fun i j => by
    rw [hamiltonianField, fderiv_realField_apply, ← fderiv_val_apply]
    exact fderiv_val_hamiltonianField _ (F j) z
  rw [key i j, key j i, (PhaseSpace.canonical ι).bracket_bracket (generator a) (F i) (F j), hF i j,
    (PhaseSpace.canonical ι).toAlmostPoissonStructure.bracket_zero_right, add_zero]

/-- Independent differentials give independent Hamiltonian fields. -/
theorem linearIndependent_hamiltonianField {F : ι → PhaseSpace ι} {z : ι ⊕ ι → ℝ}
    (hind : LinearIndependent ℝ fun i => fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) z) :
    LinearIndependent ℝ fun i => hamiltonianField (F i) z := by
  rw [Fintype.linearIndependent_iff] at hind ⊢
  intro τ hτ
  apply hind τ
  have hcomp : ∀ b : ι ⊕ ι, ∑ i, τ i * (partialDerivation b (F i)).val z = 0 := by
    intro b
    rcases b with k | k
    · have h := congrFun hτ (Sum.inr k)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hamiltonianField_inr, mul_neg,
        Finset.sum_neg_distrib, Pi.zero_apply, neg_eq_zero] at h
      exact h
    · have h := congrFun hτ (Sum.inl k)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hamiltonianField_inl,
        Pi.zero_apply] at h
      exact h
  refine ContinuousLinearMap.ext fun w => ?_
  have hw : (∑ i, τ i • fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) z) w =
      ∑ i, τ i * fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) z w := by
    change ContinuousLinearMap.apply ℝ ℝ w
      (∑ i, τ i • fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) z) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    rfl
  rw [hw]
  simp only [fderiv_val_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  have e : ∀ b : ι ⊕ ι, ∑ i, τ i * ((partialDerivation b (F i)).val z * w b) =
      (∑ i, τ i * (partialDerivation b (F i)).val z) * w b := fun b => by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
  simp only [e, hcomp, zero_mul, Finset.sum_const_zero]
  rfl

/-- Independent differentials make the derivative of the integrals onto. -/
theorem surjective_fderiv_integralMap {F : ι → PhaseSpace ι} {z : ι ⊕ ι → ℝ}
    (hind : LinearIndependent ℝ fun i => fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) z) :
    Function.Surjective (fderiv ℝ (integralMap F) z) := by
  by_contra hns
  have hlt : LinearMap.range (fderiv ℝ (integralMap F) z : (ι ⊕ ι → ℝ) →ₗ[ℝ] ι → ℝ) < ⊤ :=
    lt_top_iff_ne_top.mpr fun h => hns (LinearMap.range_eq_top.mp h)
  obtain ⟨f, hf0, hfker⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  apply hf0
  have hzero : ∑ i, f (Pi.single i 1) • fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) z = 0 := by
    refine ContinuousLinearMap.ext fun w => ?_
    have hw : (∑ i, f (Pi.single i 1) • fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) z) w =
        ∑ i, f (Pi.single i 1) * fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) z w := by
      change ContinuousLinearMap.apply ℝ ℝ w
        (∑ i, f (Pi.single i 1) • fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) z) = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]
      rfl
    have hT : f (fderiv ℝ (integralMap F) z w) = 0 :=
      hfker (LinearMap.mem_range_self _ w)
    have hdec : fderiv ℝ (integralMap F) z w =
        ∑ i, fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) z w • (Pi.single i (1 : ℝ) : ι → ℝ) := by
      funext j
      rw [Finset.sum_apply, fderiv_integralMap_apply]
      simp [Pi.single_apply]
    rw [hdec, map_sum] at hT
    rw [hw]
    simp only [map_smul, smul_eq_mul] at hT
    exact (Finset.sum_congr rfl fun i _ => mul_comm _ _).trans hT
  have hfi := Fintype.linearIndependent_iff.mp hind (fun i => f (Pi.single i 1)) hzero
  refine LinearMap.pi_ext fun i x => ?_
  have e : (Pi.single i x : ι → ℝ) = x • (Pi.single i (1 : ℝ) : ι → ℝ) := by
    funext j
    simp [Pi.single_apply]
  rw [e, map_smul, hfi i, smul_zero, LinearMap.zero_apply]

/-- The theorem of Liouville and Arnold, the invariant tori. A compact connected
level set of commuting integrals with linearly independent differentials is
the image of `θ ↦ g^{Σ θᵢ bᵢ} z` for a basis `b` of `ℝ^ι`; two angles give the
same point exactly when they differ by integers, and the flow of the field
`Σᵢ sᵢ X_{Fᵢ}`, which is the Hamiltonian field of `Σᵢ sᵢ Fᵢ`, moves the angles
uniformly. -/
theorem exists_torus_chart_of_involution {F : ι → PhaseSpace ι}
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
  exists_torus_chart_levelSet (fun i => contDiff_hamiltonianField (F i))
    (pairwiseCommute_hamiltonianField hF) (contDiff_integralMap F)
    (fun i z => fderiv_integralMap_hamiltonianField hF i z)
    (fun z hz => linearIndependent_hamiltonianField (hind z hz))
    (fun z hz => surjective_fderiv_integralMap (hind z hz))
    (by rw [finrank_fintype_fun_eq_card, Fintype.card_sum]) hcomp hconn

end ProjectAInos.Mechanics
