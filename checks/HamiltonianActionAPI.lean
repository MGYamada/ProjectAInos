/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAInos.Mechanics.Poisson.LocalAction
import ProjectAInos.Mechanics.Poisson.SymplecticFlow

/-! Typed contracts for the action along the flow of a Hamiltonian: quantities
that are constant along a flow, the end-point formula `dS = p dq − H dt`, the
preservation of the symplectic form, and the action as a differentiable
function of the time and the end point away from conjugate points. These
examples use default elaborator options. -/

open ProjectAInos ProjectAInos.Mechanics
open ProjectAInos.SmoothAlgebra ProjectAInos.SmoothAlgebra.SmoothRing
open ProjectAInos.SmoothAlgebra.FreeSmoothRing ProjectAInos.SmoothAlgebra.PhaseSpace
open ProjectAInos.SmoothGeometry ProjectAInos.SmoothGeometry.LinearODE
open ProjectAInos.SmoothGeometry.NonlinearODE
open Set Filter
open scoped Topology ContDiff

noncomputable section

section FlowInvariant

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {X : E → E} {t : ℝ} {x : E}

example {g : ℝ → F} {s t : ℝ}
    (hg : ∀ r ∈ uIcc s t, HasDerivAt g 0 r) :
    g t = g s :=
  eq_of_hasDerivAt_zero hg

example (hX : ContDiff ℝ (⊤ : ℕ∞) X) {f : E → F}
    (hf : ∀ {y : ℝ → E} {r : ℝ}, HasDerivAt y (X (y r)) r → HasDerivAt (fun s => f (y s)) 0 r)
    (h : (t, x) ∈ flowDomain X) :
    f (flow X (t, x)) = f x :=
  flow_invariant hX hf h


end FlowInvariant

section LineDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Derivatives along all lines assemble to the Fréchet derivative. -/
example {f : E → ℝ} {ℓ : E → E →L[ℝ] ℝ} {x : E}
    (h : ∀ᶠ y in 𝓝 x, ∀ v : E, HasDerivAt (fun s : ℝ => f (y + s • v)) (ℓ y v) 0)
    (hℓ : ContinuousAt ℓ x) :
    HasFDerivAt f (ℓ x) x :=
  hasFDerivAt_of_hasDerivAt_line h hℓ


end LineDerivative

section PhaseAction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

example (z w : ι ⊕ ι → ℝ) :
    liouvilleForm ι z w = ∑ i, z (Sum.inr i) * w (Sum.inl i) := liouvilleForm_apply z w

example (z w : ι ⊕ ι → ℝ) :
    liouvilleForm ι z w = ∑ i, z (Sum.inr i) * w (Sum.inl i) :=
  liouvilleForm_apply z w

example (H : PhaseSpace ι) (t : ℝ) (zv : (ι ⊕ ι → ℝ) × (ι ⊕ ι → ℝ)) :
    phaseLagrangian H t zv = liouvilleForm ι zv.1 zv.2 - H.val zv.1 := rfl

example (H : PhaseSpace ι) :
    ContDiff ℝ ∞ (Function.uncurry (phaseLagrangian H)) :=
  contDiff_phaseLagrangian H

example (H : PhaseSpace ι) (t : ℝ)
    (zv : (ι ⊕ ι → ℝ) × (ι ⊕ ι → ℝ)) :
    HasFDerivAt (phaseLagrangian H t)
      ((liouvilleForm ι).isBoundedBilinearMap.deriv zv -
        (fderiv ℝ (H.val : (ι ⊕ ι → ℝ) → ℝ) zv.1).comp
          (ContinuousLinearMap.fst ℝ (ι ⊕ ι → ℝ) (ι ⊕ ι → ℝ))) zv :=
  hasFDerivAt_phaseLagrangian H t zv

example (H : PhaseSpace ι) (z : ℝ → ι ⊕ ι → ℝ) (t : ℝ) :
    momentum (phaseLagrangian H) z t = liouvilleForm ι (z t) :=
  momentum_phaseLagrangian H z t

example (H : PhaseSpace ι) (z : ℝ → ι ⊕ ι → ℝ) (t : ℝ)
    (w : ι ⊕ ι → ℝ) :
    force (phaseLagrangian H) z t w =
      liouvilleForm ι w (deriv z t) - fderiv ℝ (H.val : (ι ⊕ ι → ℝ) → ℝ) (z t) w :=
  force_phaseLagrangian_apply H z t w

example (H : PhaseSpace ι) (z : ℝ → ι ⊕ ι → ℝ) (t : ℝ) :
    pathEnergy (phaseLagrangian H) z t = H.val (z t) :=
  pathEnergy_phaseLagrangian H z t

example (H : PhaseSpace ι) {z : ℝ → ι ⊕ ι → ℝ} {t : ℝ}
    (hz : HasDerivAt z (hamiltonianField H (z t)) t) :
    eulerLagrange (phaseLagrangian H) z t = 0 :=
  eulerLagrange_phaseLagrangian H hz

example (H : PhaseSpace ι) {z : ℝ → ι ⊕ ι → ℝ} {t : ℝ}
    (hz : HasDerivAt z (hamiltonianField H (z t)) t) :
    HasDerivAt (fun s => H.val (z s)) 0 t :=
  hasDerivAt_hamiltonian_comp H hz

example (H : PhaseSpace ι) {t : ℝ} {z : ι ⊕ ι → ℝ}
    (h : (t, z) ∈ flowDomain (hamiltonianField H)) :
    H.val (flow (hamiltonianField H) (t, z)) = H.val z :=
  hamiltonian_flow_eq H h

example (H : PhaseSpace ι) {z₀ : ℝ → ι ⊕ ι → ℝ}
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
          H.val (flow (hamiltonianField H) (a s₀, z₀ s₀)) * a')) s₀ :=
  hasDerivAt_action_hamiltonianFlow H hV hz₀ hs₀ ha hb hmem


end PhaseAction

section SymplecticFlow

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

example : symplecticForm ι = (liouvilleForm ι).flip - liouvilleForm ι := rfl

example (u v : ι ⊕ ι → ℝ) :
    symplecticForm ι u v =
      ∑ i, (u (Sum.inl i) * v (Sum.inr i) - u (Sum.inr i) * v (Sum.inl i)) :=
  symplecticForm_apply u v

example (u v : ι ⊕ ι → ℝ) :
    symplecticForm ι u v = -symplecticForm ι v u :=
  symplecticForm_swap u v

example (H : PhaseSpace ι) (z u v : ι ⊕ ι → ℝ) :
    hessianForm H z u v =
      ∑ a, ∑ b, (partialDerivation b (partialDerivation a H)).val z * u b * v a := rfl

example (H : PhaseSpace ι) (z u v : ι ⊕ ι → ℝ) :
    hessianForm H z u v = hessianForm H z v u :=
  hessianForm_comm H z u v

example (H : PhaseSpace ι) (z u : ι ⊕ ι → ℝ) (i : ι) :
    fderiv ℝ (hamiltonianField H) z u (Sum.inl i) =
      ∑ b, (partialDerivation b (partialDerivation (Sum.inr i) H)).val z * u b :=
  fderiv_hamiltonianField_inl H z u i

example (H : PhaseSpace ι) (z u : ι ⊕ ι → ℝ) (i : ι) :
    fderiv ℝ (hamiltonianField H) z u (Sum.inr i) =
      -∑ b, (partialDerivation b (partialDerivation (Sum.inl i) H)).val z * u b :=
  fderiv_hamiltonianField_inr H z u i

example (H : PhaseSpace ι) (z u v : ι ⊕ ι → ℝ) :
    symplecticForm ι (fderiv ℝ (hamiltonianField H) z u) v = hessianForm H z u v :=
  symplecticForm_fderiv_hamiltonianField H z u v

example (H : PhaseSpace ι) (z u v : ι ⊕ ι → ℝ) :
    symplecticForm ι (fderiv ℝ (hamiltonianField H) z u) v +
      symplecticForm ι u (fderiv ℝ (hamiltonianField H) z v) = 0 :=
  symplecticForm_fderiv_hamiltonianField_add H z u v

example (H : PhaseSpace ι) {t : ℝ} {z : ι ⊕ ι → ℝ}
    (h : (t, z) ∈ flowDomain (hamiltonianField H)) (u v : ι ⊕ ι → ℝ) :
    symplecticForm ι (fderiv ℝ (fun y => flow (hamiltonianField H) (t, y)) z u)
        (fderiv ℝ (fun y => flow (hamiltonianField H) (t, y)) z v) =
      symplecticForm ι u v :=
  symplecticForm_fderiv_flow H h u v


end SymplecticFlow

section LocalAction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

example (q₀ : ι → ℝ) :
    ContDiff ℝ ∞ fun p : ι → ℝ => (Sum.elim q₀ p : ι ⊕ ι → ℝ) :=
  contDiff_elim_right q₀

example :
    ContDiff ℝ ∞ fun x : (ι → ℝ) × (ι → ℝ) => (Sum.elim x.1 x.2 : ι ⊕ ι → ℝ) :=
  contDiff_elim

example (H : PhaseSpace ι) (q₀ : ι → ℝ) :
    startDomain H q₀ = {x | (x.1, Sum.elim q₀ x.2) ∈ flowDomain (hamiltonianField H)} := rfl

example (H : PhaseSpace ι) (q₀ : ι → ℝ) (x : ℝ × (ι → ℝ)) (i : ι) :
    endPosition H q₀ x i = flow (hamiltonianField H) (x.1, Sum.elim q₀ x.2) (Sum.inl i) := rfl

example (H : PhaseSpace ι) (q₀ : ι → ℝ) (x : ℝ × (ι → ℝ)) (i : ι) :
    endMomentum H q₀ x i = flow (hamiltonianField H) (x.1, Sum.elim q₀ x.2) (Sum.inr i) := rfl

example (H : PhaseSpace ι) (q₀ : ι → ℝ) (x : ℝ × (ι → ℝ)) :
    Sum.elim (endPosition H q₀ x) (endMomentum H q₀ x) =
      flow (hamiltonianField H) (x.1, Sum.elim q₀ x.2) :=
  elim_endPosition_endMomentum H q₀ x

example (q₀ : ι → ℝ) :
    ContDiff ℝ ∞ fun x : ℝ × (ι → ℝ) => (x.1, (Sum.elim q₀ x.2 : ι ⊕ ι → ℝ)) :=
  contDiff_startPoint q₀

example (H : PhaseSpace ι) (q₀ : ι → ℝ) :
    IsOpen (startDomain H q₀) :=
  isOpen_startDomain H q₀

example (H : PhaseSpace ι) (q₀ : ι → ℝ) :
    ContDiffOn ℝ ∞ (fun x : ℝ × (ι → ℝ) => flow (hamiltonianField H) (x.1, Sum.elim q₀ x.2))
      (startDomain H q₀) :=
  contDiffOn_flow_startPoint H q₀

example (H : PhaseSpace ι) (q₀ : ι → ℝ) :
    ContDiffOn ℝ ∞ (endPosition H q₀) (startDomain H q₀) :=
  contDiffOn_endPosition H q₀

example (H : PhaseSpace ι) (q₀ : ι → ℝ) :
    ContDiffOn ℝ ∞ (endMomentum H q₀) (startDomain H q₀) :=
  contDiffOn_endMomentum H q₀

example (H : PhaseSpace ι) (q₀ : ι → ℝ) {x₀ : ℝ × (ι → ℝ)}
    (hx₀ : x₀ ∈ startDomain H q₀)
    (hinv : (fderiv ℝ (fun p => endPosition H q₀ (x₀.1, p)) x₀.2).IsInvertible) :
    ∃ (W : Set (ℝ × (ι → ℝ))) (P₀ : ℝ × (ι → ℝ) → ι → ℝ), IsOpen W ∧
      (x₀.1, endPosition H q₀ x₀) ∈ W ∧ P₀ (x₀.1, endPosition H q₀ x₀) = x₀.2 ∧
      ContDiffOn ℝ ∞ P₀ W ∧
      ∀ y ∈ W, (y.1, P₀ y) ∈ startDomain H q₀ ∧ endPosition H q₀ (y.1, P₀ y) = y.2 :=
  exists_initialMomentum H q₀ hx₀ hinv

example (H : PhaseSpace ι) (q₀ : ι → ℝ) (P₀ : ℝ × (ι → ℝ) → ι → ℝ) (y : ℝ × (ι → ℝ)) :
    localAction H q₀ P₀ y = action 0 y.1 (phaseLagrangian H)
      fun t => flow (hamiltonianField H) (t, Sum.elim q₀ (P₀ y)) := rfl

example (P : ι → ℝ) (E : ℝ) (v : ℝ × (ι → ℝ)) :
    actionDifferential P E v = ∑ i, P i * v.2 i - E * v.1 := actionDifferential_apply P E v

example (P : ι → ℝ) (E : ℝ) (v : ℝ × (ι → ℝ)) :
    actionDifferential P E v = ∑ i, P i * v.2 i - E * v.1 :=
  actionDifferential_apply P E v

example :
    Continuous fun x : (ι → ℝ) × ℝ => actionDifferential x.1 x.2 :=
  continuous_actionDifferential

example (H : PhaseSpace ι) (q₀ : ι → ℝ)
    {W : Set (ℝ × (ι → ℝ))} {P₀ : ℝ × (ι → ℝ) → ι → ℝ} (hW : IsOpen W)
    (hP₀ : ContDiffOn ℝ ∞ P₀ W)
    (hsol : ∀ y ∈ W, (y.1, P₀ y) ∈ startDomain H q₀ ∧ endPosition H q₀ (y.1, P₀ y) = y.2)
    {y : ℝ × (ι → ℝ)} (hy : y ∈ W) (v : ℝ × (ι → ℝ)) :
    HasDerivAt (fun s : ℝ => localAction H q₀ P₀ (y + s • v))
      (actionDifferential (endMomentum H q₀ (y.1, P₀ y))
        (H.val (Sum.elim y.2 (endMomentum H q₀ (y.1, P₀ y)))) v) 0 :=
  hasDerivAt_localAction_line H q₀ hW hP₀ hsol hy v

example (H : PhaseSpace ι) (q₀ : ι → ℝ) {x₀ : ℝ × (ι → ℝ)}
    (hx₀ : x₀ ∈ startDomain H q₀)
    (hinv : (fderiv ℝ (fun p => endPosition H q₀ (x₀.1, p)) x₀.2).IsInvertible) :
    ∃ (W : Set (ℝ × (ι → ℝ))) (P₀ : ℝ × (ι → ℝ) → ι → ℝ), IsOpen W ∧
      (x₀.1, endPosition H q₀ x₀) ∈ W ∧ P₀ (x₀.1, endPosition H q₀ x₀) = x₀.2 ∧
      ContDiffOn ℝ ∞ P₀ W ∧
      (∀ y ∈ W, (y.1, P₀ y) ∈ startDomain H q₀ ∧ endPosition H q₀ (y.1, P₀ y) = y.2) ∧
      ∀ y ∈ W, HasFDerivAt (localAction H q₀ P₀)
        (actionDifferential (endMomentum H q₀ (y.1, P₀ y))
          (H.val (Sum.elim y.2 (endMomentum H q₀ (y.1, P₀ y))))) y :=
  exists_localAction H q₀ hx₀ hinv

example (H : PhaseSpace ι) {S : ℝ × (ι → ℝ) → ℝ} {P : ι → ℝ}
    {y : ℝ × (ι → ℝ)}
    (hS : HasFDerivAt S (actionDifferential P (H.val (Sum.elim y.2 P))) y) :
    fderiv ℝ S y (1, 0) +
      H.val (Sum.elim y.2 fun i => fderiv ℝ S y (0, Pi.single i 1)) = 0 :=
  localAction_hamiltonJacobi H hS

example (m : ι → ℝ) (z : ι ⊕ ι → ℝ) (i : ι) :
    hamiltonianField (kineticEnergy m) z (Sum.inl i) = (m i)⁻¹ * z (Sum.inr i) :=
  hamiltonianField_kineticEnergy_inl m z i

example (m : ι → ℝ) (z : ι ⊕ ι → ℝ) (i : ι) :
    hamiltonianField (kineticEnergy m) z (Sum.inr i) = 0 :=
  hamiltonianField_kineticEnergy_inr m z i

example (m : ι → ℝ) (t : ℝ) (z : ι ⊕ ι → ℝ) :
    (t, z) ∈ flowDomain (hamiltonianField (kineticEnergy m)) ∧
      flow (hamiltonianField (kineticEnergy m)) (t, z) =
        Sum.elim (fun i => z (Sum.inl i) + t * ((m i)⁻¹ * z (Sum.inr i)))
          (fun i => z (Sum.inr i)) :=
  flow_kineticEnergy m t z

example (m : ι → ℝ) (q₀ : ι → ℝ) (x : ℝ × (ι → ℝ)) :
    endPosition (kineticEnergy m) q₀ x = fun i => q₀ i + x.1 * ((m i)⁻¹ * x.2 i) :=
  endPosition_kineticEnergy m q₀ x

example {m : ι → ℝ} (hm : ∀ i, m i ≠ 0)
    {T : ℝ} (hT : T ≠ 0) (q₀ p : ι → ℝ) :
    (fderiv ℝ (fun p => endPosition (kineticEnergy m) q₀ (T, p)) p).IsInvertible :=
  isInvertible_fderiv_endPosition_kineticEnergy hm hT q₀ p

example {m : ι → ℝ} (hm : ∀ i, m i ≠ 0) {T : ℝ}
    (hT : T ≠ 0) (q₀ p₀ : ι → ℝ) :
    ∃ (W : Set (ℝ × (ι → ℝ))) (P₀ : ℝ × (ι → ℝ) → ι → ℝ), IsOpen W ∧
      (T, endPosition (kineticEnergy m) q₀ (T, p₀)) ∈ W ∧
      P₀ (T, endPosition (kineticEnergy m) q₀ (T, p₀)) = p₀ ∧ ContDiffOn ℝ ∞ P₀ W ∧
      (∀ y ∈ W, (y.1, P₀ y) ∈ startDomain (kineticEnergy m) q₀ ∧
        endPosition (kineticEnergy m) q₀ (y.1, P₀ y) = y.2) ∧
      ∀ y ∈ W, HasFDerivAt (localAction (kineticEnergy m) q₀ P₀)
        (actionDifferential (endMomentum (kineticEnergy m) q₀ (y.1, P₀ y))
          ((kineticEnergy m).val
            (Sum.elim y.2 (endMomentum (kineticEnergy m) q₀ (y.1, P₀ y))))) y :=
  exists_localAction_kineticEnergy hm hT q₀ p₀


end LocalAction
