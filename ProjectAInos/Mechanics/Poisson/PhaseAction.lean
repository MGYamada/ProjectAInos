/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Poisson.HamiltonianField
public import ProjectAInos.Mechanics.EndpointAction
public import ProjectAInos.SmoothGeometry.ODE.FlowInvariant
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
# The action along the flow of a Hamiltonian

The action in the phase space is the integral of `Σᵢ pᵢ q̇ᵢ − H` along a curve
`z(t) = (q(t), p(t))`. Its Lagrangian `phaseLagrangian H` is a function of the
point and the velocity of the phase space, and its Euler–Lagrange equations are
Hamilton's equations. Its momentum is the canonical one-form `θ = Σᵢ pᵢ dqᵢ`
(`liouvilleForm`) and its energy is `H`.

* `hamiltonian_flow_eq`: the Hamiltonian is constant along its flow.
* `hasDerivAt_action_hamiltonianFlow`: Proposition 49 of the plan
  (Landau–Lifshitz §43). For a curve of initial points `z₀(s)` and moving times
  `a(s)`, `b(s)`, the derivative of the action of the solutions
  `t ↦ Φ(t, z₀(s))` between those times is

  `[θ(d/ds Φ(b, z₀)) − H b′] − [θ(d/ds Φ(a, z₀)) − H a′]`,

  that is, `dS = p dq − H dt` at the two ends. The solutions are those of the
  flow; nothing is assumed about them.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing
open SmoothGeometry SmoothGeometry.LinearODE SmoothGeometry.NonlinearODE

variable {ι : Type*} [Fintype ι]

/-- The canonical one-form `θ = Σᵢ pᵢ dqᵢ`: at the point `z` it takes the vector
`w` to `Σᵢ pᵢ(z) wᵢ`, with the components of `w` along the positions. -/
def liouvilleForm (ι : Type*) [Fintype ι] : (ι ⊕ ι → ℝ) →L[ℝ] (ι ⊕ ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ⊕ ι => ℝ) (Sum.inr i)).smulRight
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ⊕ ι => ℝ) (Sum.inl i))

theorem liouvilleForm_apply (z w : ι ⊕ ι → ℝ) :
    liouvilleForm ι z w = ∑ i, z (Sum.inr i) * w (Sum.inl i) := by
  simp [liouvilleForm]

/-- The Lagrangian `Σᵢ pᵢ q̇ᵢ − H` of the phase space. -/
def phaseLagrangian (H : PhaseSpace ι) : Lagrangian (ι ⊕ ι → ℝ) :=
  fun _ zv => liouvilleForm ι zv.1 zv.2 - H.val zv.1

theorem contDiff_phaseLagrangian (H : PhaseSpace ι) :
    ContDiff ℝ ∞ (Function.uncurry (phaseLagrangian H)) := by
  have hB : ContDiff ℝ ∞ fun p : ℝ × ((ι ⊕ ι → ℝ) × (ι ⊕ ι → ℝ)) =>
      liouvilleForm ι p.2.1 p.2.2 :=
    ((liouvilleForm ι).contDiff.comp (contDiff_fst.comp contDiff_snd)).clm_apply
      (contDiff_snd.comp contDiff_snd)
  exact hB.sub ((contDiff_val H).comp (contDiff_fst.comp contDiff_snd))

theorem hasFDerivAt_phaseLagrangian (H : PhaseSpace ι) (t : ℝ)
    (zv : (ι ⊕ ι → ℝ) × (ι ⊕ ι → ℝ)) :
    HasFDerivAt (phaseLagrangian H t)
      ((liouvilleForm ι).isBoundedBilinearMap.deriv zv -
        (fderiv ℝ (H.val : (ι ⊕ ι → ℝ) → ℝ) zv.1).comp
          (ContinuousLinearMap.fst ℝ (ι ⊕ ι → ℝ) (ι ⊕ ι → ℝ))) zv := by
  have h1 := (liouvilleForm ι).isBoundedBilinearMap.hasFDerivAt zv
  have h2 := ((contDiff_val H).differentiable (by simp) zv.1).hasFDerivAt.comp zv
    (hasFDerivAt_fst (𝕜 := ℝ) (p := zv))
  exact h1.sub h2

/-- The momentum of the phase-space Lagrangian is the canonical one-form. -/
theorem momentum_phaseLagrangian (H : PhaseSpace ι) (z : ℝ → ι ⊕ ι → ℝ) (t : ℝ) :
    momentum (phaseLagrangian H) z t = liouvilleForm ι (z t) := by
  ext w
  rw [momentum, (hasFDerivAt_phaseLagrangian H t _).fderiv]
  simp [IsBoundedBilinearMap.deriv_apply]

theorem force_phaseLagrangian_apply (H : PhaseSpace ι) (z : ℝ → ι ⊕ ι → ℝ) (t : ℝ)
    (w : ι ⊕ ι → ℝ) :
    force (phaseLagrangian H) z t w =
      liouvilleForm ι w (deriv z t) - fderiv ℝ (H.val : (ι ⊕ ι → ℝ) → ℝ) (z t) w := by
  rw [force, (hasFDerivAt_phaseLagrangian H t _).fderiv]
  simp [IsBoundedBilinearMap.deriv_apply]

/-- The energy of the phase-space Lagrangian is the Hamiltonian. -/
theorem pathEnergy_phaseLagrangian (H : PhaseSpace ι) (z : ℝ → ι ⊕ ι → ℝ) (t : ℝ) :
    pathEnergy (phaseLagrangian H) z t = H.val (z t) := by
  rw [pathEnergy, momentum_phaseLagrangian]
  simp [phaseLagrangian]

variable [DecidableEq ι]

/-- The Euler–Lagrange equations of the phase-space Lagrangian hold along a
solution of Hamilton's equations. -/
theorem eulerLagrange_phaseLagrangian (H : PhaseSpace ι) {z : ℝ → ι ⊕ ι → ℝ} {t : ℝ}
    (hz : HasDerivAt z (hamiltonianField H (z t)) t) :
    eulerLagrange (phaseLagrangian H) z t = 0 := by
  have hm : momentum (phaseLagrangian H) z = fun s => liouvilleForm ι (z s) :=
    funext (momentum_phaseLagrangian H z)
  have hd : HasDerivAt (fun s => liouvilleForm ι (z s))
      (liouvilleForm ι (hamiltonianField H (z t))) t :=
    (liouvilleForm ι).hasFDerivAt.comp_hasDerivAt t hz
  ext w
  rw [eulerLagrange, hm, hd.deriv, _root_.sub_apply,
    force_phaseLagrangian_apply, hz.deriv, liouvilleForm_apply, liouvilleForm_apply,
    fderiv_val_apply, Fintype.sum_sum_type, _root_.zero_apply]
  simp only [hamiltonianField_inl, hamiltonianField_inr]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_eq_zero fun i _ => by ring

/-- The Hamiltonian has derivative zero along a solution of Hamilton's
equations. -/
theorem hasDerivAt_hamiltonian_comp (H : PhaseSpace ι) {z : ℝ → ι ⊕ ι → ℝ} {t : ℝ}
    (hz : HasDerivAt z (hamiltonianField H (z t)) t) :
    HasDerivAt (fun s => H.val (z s)) 0 t := by
  have h := ((contDiff_val H).differentiable (by simp) (z t)).hasFDerivAt.comp_hasDerivAt t hz
  refine h.congr_deriv ?_
  rw [fderiv_val_apply, Fintype.sum_sum_type]
  simp only [hamiltonianField_inl, hamiltonianField_inr]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun i _ => by ring

/-- The Hamiltonian is constant along its flow. -/
theorem hamiltonian_flow_eq (H : PhaseSpace ι) {t : ℝ} {z : ι ⊕ ι → ℝ}
    (h : (t, z) ∈ flowDomain (hamiltonianField H)) :
    H.val (flow (hamiltonianField H) (t, z)) = H.val z :=
  flow_invariant (contDiff_hamiltonianField H) (f := fun y => H.val y)
    (fun hy => hasDerivAt_hamiltonian_comp H hy) h

/-- Proposition 49 (Landau–Lifshitz §43): the derivative of the action of the
solutions of Hamilton's equations, for a curve of initial points and moving
times, is `p dq − H dt` taken between the two ends. -/
theorem hasDerivAt_action_hamiltonianFlow (H : PhaseSpace ι) {z₀ : ℝ → ι ⊕ ι → ℝ}
    {V : Set ℝ} (hV : IsOpen V) (hz₀ : ContDiffOn ℝ ∞ z₀ V) {a b : ℝ → ℝ} {s₀ a' b' : ℝ}
    (hs₀ : s₀ ∈ V) (ha : HasDerivAt a a' s₀) (hb : HasDerivAt b b' s₀)
    (hmem : ∀ t ∈ uIcc (a s₀) (b s₀), (t, z₀ s₀) ∈ flowDomain (hamiltonianField H)) :
    HasDerivAt
      (fun s => action (a s) (b s) (phaseLagrangian H)
        fun t => flow (hamiltonianField H) (t, z₀ s))
      (liouvilleForm ι (flow (hamiltonianField H) (b s₀, z₀ s₀))
            (deriv (fun s => flow (hamiltonianField H) (b s, z₀ s)) s₀) -
          H.val (flow (hamiltonianField H) (b s₀, z₀ s₀)) * b' -
        (liouvilleForm ι (flow (hamiltonianField H) (a s₀, z₀ s₀))
            (deriv (fun s => flow (hamiltonianField H) (a s, z₀ s)) s₀) -
          H.val (flow (hamiltonianField H) (a s₀, z₀ s₀)) * a')) s₀ := by
  have hX := contDiff_hamiltonianField H
  have hU : IsOpen ((Prod.fst ⁻¹' V : Set (ℝ × ℝ)) ∩
      (fun p : ℝ × ℝ => (p.2, z₀ p.1)) ⁻¹' flowDomain (hamiltonianField H)) := by
    refine ContinuousOn.isOpen_inter_preimage ?_ (hV.preimage continuous_fst)
      (isOpen_flowDomain hX)
    exact continuousOn_snd.prodMk (hz₀.continuousOn.comp continuousOn_fst fun p hp => hp)
  have hm : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (p.2, z₀ p.1))
      ((Prod.fst ⁻¹' V : Set (ℝ × ℝ)) ∩
        (fun p : ℝ × ℝ => (p.2, z₀ p.1)) ⁻¹' flowDomain (hamiltonianField H)) :=
    contDiffOn_snd.prodMk (hz₀.comp contDiffOn_fst fun p hp => hp.1)
  have hq : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => flow (hamiltonianField H) (p.2, z₀ p.1))
      ((Prod.fst ⁻¹' V : Set (ℝ × ℝ)) ∩
        (fun p : ℝ × ℝ => (p.2, z₀ p.1)) ⁻¹' flowDomain (hamiltonianField H)) :=
    (contDiffOn_flow hX).comp hm fun p hp => hp.2
  have h := hasDerivAt_action_movingEndpoints_on (L := phaseLagrangian H) isOpen_univ
    (contDiff_phaseLagrangian H).contDiffOn hU hq ha hb
    (fun t ht => ⟨hs₀, hmem t ht⟩) (fun _ _ => mem_univ _)
    (fun t ht => eulerLagrange_phaseLagrangian H (hasDerivAt_flow hX (hmem t ht)))
  refine h.congr_deriv ?_
  simp only [momentum_phaseLagrangian, pathEnergy_phaseLagrangian]

end ProjectAInos.Mechanics
