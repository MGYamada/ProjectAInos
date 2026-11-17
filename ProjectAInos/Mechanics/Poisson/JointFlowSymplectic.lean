/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Poisson.InvariantTorus
public import ProjectAInos.Mechanics.Poisson.SymplecticFlow

/-!
# The symplectic form in the co-ordinates of the joint flow

For integrals `Fᵢ` in involution with the Hamiltonian fields `Xᵢ` and the
joint flow `g^t`:

* `symplecticForm_hamiltonianField`: `ω(X_H(z), w) = dH(z) w`.
* `jointField_hamiltonianField`: `Σᵢ tᵢ Xᵢ` is the Hamiltonian field of
  `Σᵢ tᵢ Fᵢ`, so the joint flow preserves the symplectic form
  (`symplecticForm_fderiv_jointFlow`).
* `symplecticForm_jointFlow`: for the derivatives `Σᵢ τᵢ Xᵢ(g^t y) + D_y g^t(y) v`
  of `(t, y) ↦ g^t y` (`SmoothGeometry.NonlinearODE.hasFDerivAt_jointFlow`),
  `ω(Σ τᵢ Xᵢ + Dg v, Σ τ′ᵢ Xᵢ + Dg v′) = ω(v, v′) + Σᵢ (τᵢ dFᵢ(y) v′ − τ′ᵢ dFᵢ(y) v)`.
  The times of the joint flow and the values of the integrals are conjugate
  co-ordinates.
-/

@[expose] public section
noncomputable section

open Set Module
open scoped ContDiff

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing
open SmoothGeometry SmoothGeometry.NonlinearODE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `ω(X_H(z), w) = dH(z) w`. -/
theorem symplecticForm_hamiltonianField (H : PhaseSpace ι) (z w : ι ⊕ ι → ℝ) :
    symplecticForm ι (hamiltonianField H z) w =
      fderiv ℝ (H.val : (ι ⊕ ι → ℝ) → ℝ) z w := by
  rw [symplecticForm_apply, fderiv_val_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hamiltonianField_inl, hamiltonianField_inr]
  ring

/-- `Σᵢ tᵢ Xᵢ` is the Hamiltonian field of `Σᵢ tᵢ Fᵢ`. -/
theorem jointField_hamiltonianField (F : ι → PhaseSpace ι) (t : ι → ℝ) :
    jointField (fun i => hamiltonianField (F i)) t = hamiltonianField (∑ i, t i • F i) := by
  funext z a
  have hval : ∀ (f : ι → PhaseSpace ι) (z : ι ⊕ ι → ℝ), (∑ i, f i).val z = ∑ i, (f i).val z :=
    fun f z => by
      rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  have hbr : hamiltonianField (∑ i, t i • F i) z a =
      ∑ i, t i * hamiltonianField (F i) z a := by
    change ((PhaseSpace.canonical ι).bracket (generator a) (∑ i, t i • F i)).val z = _
    rw [(PhaseSpace.canonical ι).toAlmostPoissonStructure.bracket_sum_right, hval]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(PhaseSpace.canonical ι).toAlmostPoissonStructure.bracket_smul_right]
    rfl
  rw [hbr, jointField, Finset.sum_apply]
  rfl

theorem jointField_single (X : ι → (ι ⊕ ι → ℝ) → ι ⊕ ι → ℝ) (i : ι) :
    jointField X (Pi.single i 1) = X i := by
  funext z
  rw [jointField, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, one_smul]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The joint flow of Hamiltonian fields preserves the symplectic form. -/
theorem symplecticForm_fderiv_jointFlow (F : ι → PhaseSpace ι) {t : ι → ℝ}
    {y : ι ⊕ ι → ℝ}
    (h : ((1 : ℝ), y) ∈ flowDomain (jointField (fun i => hamiltonianField (F i)) t))
    (u v : ι ⊕ ι → ℝ) :
    symplecticForm ι
        (fderiv ℝ (fun z => jointFlow (fun i => hamiltonianField (F i)) t z) y u)
        (fderiv ℝ (fun z => jointFlow (fun i => hamiltonianField (F i)) t z) y v) =
      symplecticForm ι u v := by
  have e := jointField_hamiltonianField F t
  rw [e] at h
  have h1 := symplecticForm_fderiv_flow (∑ i, t i • F i) h u v
  have e2 : (fun z => jointFlow (fun i => hamiltonianField (F i)) t z) =
      fun z => flow (hamiltonianField (∑ i, t i • F i)) ((1 : ℝ), z) := by
    funext z
    rw [jointFlow, e]
  rw [e2]
  exact h1

/-- The joint flow carries each of the commuting fields into itself. -/
theorem fderiv_jointFlow_hamiltonianField {F : ι → PhaseSpace ι}
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {t : ι → ℝ}
    {y : ι ⊕ ι → ℝ}
    (h : ((1 : ℝ), y) ∈ flowDomain (jointField (fun i => hamiltonianField (F i)) t)) (i : ι) :
    fderiv ℝ (fun z => jointFlow (fun i => hamiltonianField (F i)) t z) y
        (hamiltonianField (F i) y) =
      hamiltonianField (F i) (jointFlow (fun i => hamiltonianField (F i)) t y) := by
  have hX : ∀ i, ContDiff ℝ ∞ (hamiltonianField (F i)) := fun i => contDiff_hamiltonianField _
  have hc := jointField_commute hX (pairwiseCommute_hamiltonianField hF) t (Pi.single i 1)
  rw [jointField_single] at hc
  exact fderiv_flow_apply_of_commute (contDiff_jointField hX t) (hX i) hc h

/-- `ω(Xᵢ, Xⱼ) = 0` for integrals in involution. -/
theorem symplecticForm_hamiltonianField_hamiltonianField {F : ι → PhaseSpace ι}
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) (i j : ι)
    (z : ι ⊕ ι → ℝ) :
    symplecticForm ι (hamiltonianField (F i) z) (hamiltonianField (F j) z) = 0 := by
  rw [symplecticForm_hamiltonianField, fderiv_val_hamiltonianField, hF i j]
  rfl

/-- The symplectic form in the co-ordinates of the joint flow: the times and
the values of the integrals are conjugate. -/
theorem symplecticForm_jointFlow {F : ι → PhaseSpace ι}
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
          τ' i * fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) y v) := by
  obtain ⟨g, hg⟩ : ∃ g : (ι ⊕ ι → ℝ) → ι ⊕ ι → ℝ,
      g = fun z => jointFlow (fun i => hamiltonianField (F i)) t z := ⟨_, rfl⟩
  have hgy : jointFlow (fun i => hamiltonianField (F i)) t y = g y := by rw [hg]
  rw [← hg, hgy]
  -- the field of a direction against a transported vector
  have hAB : ∀ (σ : ι → ℝ) (w : ι ⊕ ι → ℝ),
      symplecticForm ι (fderiv ℝ g y w)
          (jointField (fun i => hamiltonianField (F i)) σ (g y)) =
        -∑ i, σ i * fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) y w := by
    intro σ w
    rw [jointField, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := fderiv_jointFlow_hamiltonianField hF h i
    rw [← hg, hgy] at h1
    have h2 := symplecticForm_fderiv_jointFlow F h w (hamiltonianField (F i) y)
    rw [← hg] at h2
    rw [map_smul, smul_eq_mul, ← h1, h2, symplecticForm_swap, symplecticForm_hamiltonianField]
    ring
  have hXA : ∀ (i : ι) (σ' : ι → ℝ), symplecticForm ι (hamiltonianField (F i) (g y))
      (jointField (fun i => hamiltonianField (F i)) σ' (g y)) = 0 := by
    intro i σ'
    rw [jointField, map_sum]
    exact Finset.sum_eq_zero fun j _ => by
      rw [map_smul, symplecticForm_hamiltonianField_hamiltonianField hF, smul_zero]
  have hAA : ∀ σ σ' : ι → ℝ,
      symplecticForm ι (jointField (fun i => hamiltonianField (F i)) σ (g y))
        (jointField (fun i => hamiltonianField (F i)) σ' (g y)) = 0 := by
    intro σ σ'
    have e : jointField (fun i => hamiltonianField (F i)) σ (g y) =
        ∑ i, σ i • hamiltonianField (F i) (g y) := rfl
    rw [symplecticForm_swap, e, map_sum, neg_eq_zero]
    exact Finset.sum_eq_zero fun i _ => by
      rw [map_smul, symplecticForm_swap, hXA, neg_zero, smul_zero]
  have hadd : ∀ a b c : ι ⊕ ι → ℝ, symplecticForm ι (a + b) c =
      symplecticForm ι a c + symplecticForm ι b c := fun a b c => by
    rw [symplecticForm_swap, map_add, symplecticForm_swap c a, symplecticForm_swap c b]
    ring
  have hBB := symplecticForm_fderiv_jointFlow F h v v'
  rw [← hg] at hBB
  have hBA : symplecticForm ι (jointField (fun i => hamiltonianField (F i)) τ (g y))
      (fderiv ℝ g y v') = ∑ i, τ i * fderiv ℝ ((F i).val : (ι ⊕ ι → ℝ) → ℝ) y v' := by
    rw [symplecticForm_swap, hAB, neg_neg]
  rw [hadd, map_add, map_add, hAA, hBA, hAB, hBB, Finset.sum_sub_distrib]
  ring

end ProjectAInos.Mechanics
