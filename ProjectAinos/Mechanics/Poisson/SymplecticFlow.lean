/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Poisson.PhaseAction

/-!
# The flow of a Hamiltonian preserves the symplectic form

`symplecticForm ι` is the form `ω = Σᵢ dqᵢ ∧ dpᵢ` on the phase space. The
derivative of a Hamiltonian field is infinitesimally symplectic,
`ω(DX u, v) + ω(u, DX v) = 0`, because it is the Hessian of the Hamiltonian
composed with the canonical matrix and the Hessian is symmetric. By the
variational equation `M′ = DX(Φ) M` for the derivative `M = D_z Φ(t, z)` of the
flow, `ω(M u, M v)` is constant in the time, so

`ω(D_z Φ(t, z) u, D_z Φ(t, z) v) = ω(u, v)`:

the map of the flow at every time is a canonical transformation (the second
statement of Proposition 49 of the plan).
-/

@[expose] public section
noncomputable section

open Set
open scoped ContDiff

namespace ProjectAinos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace
open SmoothGeometry SmoothGeometry.LinearODE SmoothGeometry.NonlinearODE

variable {ι : Type*} [Fintype ι]

/-- The symplectic form `ω = Σᵢ dqᵢ ∧ dpᵢ`, as a bilinear form:
`ω(u, v) = Σᵢ (u(qᵢ) v(pᵢ) − u(pᵢ) v(qᵢ))`. -/
def symplecticForm (ι : Type*) [Fintype ι] : (ι ⊕ ι → ℝ) →L[ℝ] (ι ⊕ ι → ℝ) →L[ℝ] ℝ :=
  (liouvilleForm ι).flip - liouvilleForm ι

theorem symplecticForm_apply (u v : ι ⊕ ι → ℝ) :
    symplecticForm ι u v =
      ∑ i, (u (Sum.inl i) * v (Sum.inr i) - u (Sum.inr i) * v (Sum.inl i)) := by
  rw [symplecticForm, _root_.sub_apply, _root_.sub_apply, ContinuousLinearMap.flip_apply,
    liouvilleForm_apply, liouvilleForm_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem symplecticForm_swap (u v : ι ⊕ ι → ℝ) :
    symplecticForm ι u v = -symplecticForm ι v u := by
  rw [symplecticForm_apply, symplecticForm_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

variable [DecidableEq ι]

/-- The Hessian of an element of the phase space, as a bilinear expression. -/
def hessianForm (H : PhaseSpace ι) (z u v : ι ⊕ ι → ℝ) : ℝ :=
  ∑ a, ∑ b, (partialDerivation b (partialDerivation a H)).val z * u b * v a

/-- The Hessian is symmetric. -/
theorem hessianForm_comm (H : PhaseSpace ι) (z u v : ι ⊕ ι → ℝ) :
    hessianForm H z u v = hessianForm H z v u := by
  rw [hessianForm, hessianForm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [partialDerivation_comm a b H]
  ring

theorem fderiv_hamiltonianField_inl (H : PhaseSpace ι) (z u : ι ⊕ ι → ℝ) (i : ι) :
    fderiv ℝ (hamiltonianField H) z u (Sum.inl i) =
      ∑ b, (partialDerivation b (partialDerivation (Sum.inr i) H)).val z * u b := by
  rw [hamiltonianField, fderiv_realField_apply]
  have h : (PhaseSpace.canonical ι).hamiltonian H (generator (Sum.inl i)) =
      partialDerivation (Sum.inr i) H := PhaseSpace.canonical_q_bracket i H
  rw [h]

theorem fderiv_hamiltonianField_inr (H : PhaseSpace ι) (z u : ι ⊕ ι → ℝ) (i : ι) :
    fderiv ℝ (hamiltonianField H) z u (Sum.inr i) =
      -∑ b, (partialDerivation b (partialDerivation (Sum.inl i) H)).val z * u b := by
  rw [hamiltonianField, fderiv_realField_apply]
  have h : (PhaseSpace.canonical ι).hamiltonian H (generator (Sum.inr i)) =
      -partialDerivation (Sum.inl i) H := PhaseSpace.canonical_p_bracket i H
  rw [h, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_neg]
  change -((partialDerivation b (partialDerivation (Sum.inl i) H)).val z) * u b = _
  ring

/-- The derivative of a Hamiltonian field, paired with the symplectic form, is
the Hessian of the Hamiltonian. -/
theorem symplecticForm_fderiv_hamiltonianField (H : PhaseSpace ι) (z u v : ι ⊕ ι → ℝ) :
    symplecticForm ι (fderiv ℝ (hamiltonianField H) z u) v = hessianForm H z u v := by
  rw [symplecticForm_apply, hessianForm, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_hamiltonianField_inl, fderiv_hamiltonianField_inr, neg_mul, sub_neg_eq_add,
    Finset.sum_mul, Finset.sum_mul, add_comm]

/-- The derivative of a Hamiltonian field is infinitesimally symplectic. -/
theorem symplecticForm_fderiv_hamiltonianField_add (H : PhaseSpace ι) (z u v : ι ⊕ ι → ℝ) :
    symplecticForm ι (fderiv ℝ (hamiltonianField H) z u) v +
      symplecticForm ι u (fderiv ℝ (hamiltonianField H) z v) = 0 := by
  rw [symplecticForm_swap u, symplecticForm_fderiv_hamiltonianField,
    symplecticForm_fderiv_hamiltonianField, hessianForm_comm H z u v, add_neg_cancel]

/-- The flow of a Hamiltonian preserves the symplectic form: the map of the flow
at every time is a canonical transformation. -/
theorem symplecticForm_fderiv_flow (H : PhaseSpace ι) {t : ℝ} {z : ι ⊕ ι → ℝ}
    (h : (t, z) ∈ flowDomain (hamiltonianField H)) (u v : ι ⊕ ι → ℝ) :
    symplecticForm ι (fderiv ℝ (fun y => flow (hamiltonianField H) (t, y)) z u)
        (fderiv ℝ (fun y => flow (hamiltonianField H) (t, y)) z v) =
      symplecticForm ι u v := by
  have hX := contDiff_hamiltonianField H
  have hflow := isLocalFlowOn_flow hX
  have hd : ∀ r ∈ uIcc 0 t, HasDerivAt
      (fun s => symplecticForm ι (fderiv ℝ (fun y => flow (hamiltonianField H) (s, y)) z u)
        (fderiv ℝ (fun y => flow (hamiltonianField H) (s, y)) z v)) 0 r := by
    intro r hr
    have hM := hflow.hasDerivAt_fderiv (hX.of_le (by simp)) (mem_flowDomain_of_mem_uIcc h hr)
    have hu := hM.clm_apply (hasDerivAt_const r u)
    have hv := hM.clm_apply (hasDerivAt_const r v)
    have hpair := hu.prodMk hv
    have hb := (symplecticForm ι).isBoundedBilinearMap.hasFDerivAt
      (fderiv ℝ (fun y => flow (hamiltonianField H) (r, y)) z u,
        fderiv ℝ (fun y => flow (hamiltonianField H) (r, y)) z v)
    have hc := hb.comp_hasDerivAt r hpair
    refine hc.congr_deriv ?_
    rw [IsBoundedBilinearMap.deriv_apply]
    simp only [ContinuousLinearMap.comp_apply, map_zero, add_zero]
    rw [add_comm]
    exact symplecticForm_fderiv_hamiltonianField_add H _ _ _
  have hc := eq_of_hasDerivAt_zero hd
  rw [hflow.fderiv_zero (zero_mem_flowDomain _ z)] at hc
  simpa using hc

end ProjectAinos.Mechanics
