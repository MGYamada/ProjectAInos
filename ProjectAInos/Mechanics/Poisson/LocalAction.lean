/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Poisson.PhaseAction
public import ProjectAInos.SmoothAlgebra.LineDerivative

/-!
# The action as a function of the co-ordinates and the time

Fix an initial position `q₀`. The solution of Hamilton's equations that starts
at `q₀` with the momentum `p` reaches, at the time `T`, the position
`endPosition H q₀ (T, p)`. If the derivative of this position in `p` is
invertible at `(T₀, p₀)`, that is, if the end point is not conjugate to `q₀`
along the solution, then near `(T₀, q₁)` with `q₁` the position reached:

* the initial momentum is a smooth function `P₀(T, q)` of the time and the end
  point (`exists_initialMomentum`);
* the action `S(T, q)` of the solution from `q₀` to `q` in the time `T`
  (`localAction`) is differentiable, with

  `dS = Σᵢ pᵢ dqᵢ − H dT`,

  where `p` is the momentum at the end point (`exists_localAction`);
* hence `∂S/∂T + H(q, ∂S/∂q) = 0`, the Hamilton–Jacobi equation
  (`localAction_hamiltonJacobi`).

This is Landau–Lifshitz §43. The action function is defined on an open set of
times and end points, not on the whole space, so it is not an element of a
free C∞-ring.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing
open SmoothGeometry SmoothGeometry.LinearODE SmoothGeometry.NonlinearODE

variable {ι : Type*} [Fintype ι]

/-! ### The point of the phase space with a given position and momentum -/

theorem contDiff_elim_right (q₀ : ι → ℝ) :
    ContDiff ℝ ∞ fun p : ι → ℝ => (Sum.elim q₀ p : ι ⊕ ι → ℝ) := by
  refine contDiff_pi.mpr fun a => ?_
  rcases a with i | i
  · exact contDiff_const
  · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).contDiff

theorem contDiff_elim :
    ContDiff ℝ ∞ fun x : (ι → ℝ) × (ι → ℝ) => (Sum.elim x.1 x.2 : ι ⊕ ι → ℝ) := by
  refine contDiff_pi.mpr fun a => ?_
  rcases a with i | i
  · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).contDiff.comp contDiff_fst
  · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).contDiff.comp contDiff_snd

variable [DecidableEq ι]

/-! ### The end point of the solution from a fixed position -/

/-- The times and initial momenta for which the solution from `q₀` exists. -/
def startDomain (H : PhaseSpace ι) (q₀ : ι → ℝ) : Set (ℝ × (ι → ℝ)) :=
  {x | (x.1, Sum.elim q₀ x.2) ∈ flowDomain (hamiltonianField H)}

/-- The position at the time `x.1` of the solution that starts at `q₀` with the
momentum `x.2`. -/
def endPosition (H : PhaseSpace ι) (q₀ : ι → ℝ) (x : ℝ × (ι → ℝ)) : ι → ℝ :=
  fun i => flow (hamiltonianField H) (x.1, Sum.elim q₀ x.2) (Sum.inl i)

/-- The momentum at the time `x.1` of the solution that starts at `q₀` with the
momentum `x.2`. -/
def endMomentum (H : PhaseSpace ι) (q₀ : ι → ℝ) (x : ℝ × (ι → ℝ)) : ι → ℝ :=
  fun i => flow (hamiltonianField H) (x.1, Sum.elim q₀ x.2) (Sum.inr i)

theorem elim_endPosition_endMomentum (H : PhaseSpace ι) (q₀ : ι → ℝ) (x : ℝ × (ι → ℝ)) :
    Sum.elim (endPosition H q₀ x) (endMomentum H q₀ x) =
      flow (hamiltonianField H) (x.1, Sum.elim q₀ x.2) := by
  funext a
  rcases a with i | i <;> rfl

omit [DecidableEq ι] in
theorem contDiff_startPoint (q₀ : ι → ℝ) :
    ContDiff ℝ ∞ fun x : ℝ × (ι → ℝ) => (x.1, (Sum.elim q₀ x.2 : ι ⊕ ι → ℝ)) :=
  contDiff_fst.prodMk ((contDiff_elim_right q₀).comp contDiff_snd)

theorem isOpen_startDomain (H : PhaseSpace ι) (q₀ : ι → ℝ) : IsOpen (startDomain H q₀) :=
  (isOpen_flowDomain (contDiff_hamiltonianField H)).preimage (contDiff_startPoint q₀).continuous

theorem contDiffOn_flow_startPoint (H : PhaseSpace ι) (q₀ : ι → ℝ) :
    ContDiffOn ℝ ∞ (fun x : ℝ × (ι → ℝ) => flow (hamiltonianField H) (x.1, Sum.elim q₀ x.2))
      (startDomain H q₀) :=
  (contDiffOn_flow (contDiff_hamiltonianField H)).comp (contDiff_startPoint q₀).contDiffOn
    fun _ hx => hx

theorem contDiffOn_endPosition (H : PhaseSpace ι) (q₀ : ι → ℝ) :
    ContDiffOn ℝ ∞ (endPosition H q₀) (startDomain H q₀) :=
  contDiffOn_pi.mpr fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ⊕ ι => ℝ)
      (Sum.inl i)).contDiff.comp_contDiffOn (contDiffOn_flow_startPoint H q₀)

theorem contDiffOn_endMomentum (H : PhaseSpace ι) (q₀ : ι → ℝ) :
    ContDiffOn ℝ ∞ (endMomentum H q₀) (startDomain H q₀) :=
  contDiffOn_pi.mpr fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ⊕ ι => ℝ)
      (Sum.inr i)).contDiff.comp_contDiffOn (contDiffOn_flow_startPoint H q₀)

/-! ### The initial momentum as a function of the time and the end point -/

/-- Away from conjugate points the initial momentum is a smooth function of the
time and the end point. -/
theorem exists_initialMomentum (H : PhaseSpace ι) (q₀ : ι → ℝ) {x₀ : ℝ × (ι → ℝ)}
    (hx₀ : x₀ ∈ startDomain H q₀)
    (hinv : (fderiv ℝ (fun p => endPosition H q₀ (x₀.1, p)) x₀.2).IsInvertible) :
    ∃ (W : Set (ℝ × (ι → ℝ))) (P₀ : ℝ × (ι → ℝ) → ι → ℝ), IsOpen W ∧
      (x₀.1, endPosition H q₀ x₀) ∈ W ∧ P₀ (x₀.1, endPosition H q₀ x₀) = x₀.2 ∧
      ContDiffOn ℝ ∞ P₀ W ∧
      ∀ y ∈ W, (y.1, P₀ y) ∈ startDomain H q₀ ∧ endPosition H q₀ (y.1, P₀ y) = y.2 := by
  let f : (ℝ × (ι → ℝ)) × (ι → ℝ) → ι → ℝ := fun v => endPosition H q₀ (v.1.1, v.2) - v.1.2
  let W₀ : Set ((ℝ × (ι → ℝ)) × (ι → ℝ)) := {v | (v.1.1, v.2) ∈ startDomain H q₀}
  have hmap : ContDiff ℝ ∞ fun v : (ℝ × (ι → ℝ)) × (ι → ℝ) => (v.1.1, v.2) :=
    (contDiff_fst.comp contDiff_fst).prodMk contDiff_snd
  have hW₀ : IsOpen W₀ := (isOpen_startDomain H q₀).preimage hmap.continuous
  have hf : ContDiffOn ℝ ∞ f W₀ :=
    ((contDiffOn_endPosition H q₀).comp hmap.contDiffOn fun _ hv => hv).sub
      (contDiff_snd.comp contDiff_fst).contDiffOn
  have hG : ContinuousOn (fun v => fderiv ℝ f v ∘L
      ContinuousLinearMap.inr ℝ (ℝ × (ι → ℝ)) (ι → ℝ)) W₀ :=
    (hf.continuousOn_fderiv_of_isOpen hW₀ (by simp)).clm_comp continuousOn_const
  have hW₁ : IsOpen (W₀ ∩ (fun v => fderiv ℝ f v ∘L
      ContinuousLinearMap.inr ℝ (ℝ × (ι → ℝ)) (ι → ℝ)) ⁻¹'
        {T : (ι → ℝ) →L[ℝ] (ι → ℝ) | T.IsInvertible}) :=
    hG.isOpen_inter_preimage hW₀ ContinuousLinearMap.isOpen_setOfPred_isInvertible
  -- the partial derivative at the base point
  have hu₀ : ((x₀.1, endPosition H q₀ x₀), x₀.2) ∈ W₀ := hx₀
  have hfd : DifferentiableAt ℝ f ((x₀.1, endPosition H q₀ x₀), x₀.2) :=
    (hf.contDiffAt (hW₀.mem_nhds hu₀)).differentiableAt (by simp)
  have hpart : fderiv ℝ f ((x₀.1, endPosition H q₀ x₀), x₀.2) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × (ι → ℝ)) (ι → ℝ) =
      fderiv ℝ (fun p => endPosition H q₀ (x₀.1, p)) x₀.2 := by
    have hc := hfd.hasFDerivAt.comp x₀.2
      (hasFDerivAt_prodMk_right (x₀.1, endPosition H q₀ x₀) x₀.2)
    have hfun : (f ∘ fun p => ((x₀.1, endPosition H q₀ x₀), p)) =
        fun p => endPosition H q₀ (x₀.1, p) - endPosition H q₀ x₀ := rfl
    rw [hfun] at hc
    rw [← hc.fderiv, fderiv_sub_const]
  obtain ⟨V, ψ, hV, huV, hψu, hψ, hsol⟩ := exists_contDiffOn_implicitFunction (f := f)
    hW₁ (hf.mono inter_subset_left) (fun v hv => hv.2)
    (u := ((x₀.1, endPosition H q₀ x₀), x₀.2)) ⟨hu₀, by
      change (fderiv ℝ f ((x₀.1, endPosition H q₀ x₀), x₀.2) ∘L
        ContinuousLinearMap.inr ℝ (ℝ × (ι → ℝ)) (ι → ℝ)).IsInvertible
      rw [hpart]
      exact hinv⟩
  refine ⟨V, ψ, hV, huV, hψu, hψ, fun y hy => ⟨(hsol y hy).1.1, ?_⟩⟩
  have h0 := (hsol y hy).2
  change endPosition H q₀ (y.1, ψ y) - y.2 = endPosition H q₀ (x₀.1, x₀.2) - endPosition H q₀ x₀
    at h0
  rw [sub_self, sub_eq_zero] at h0
  exact h0

/-! ### The action of the solution to a given end point -/

/-- The action of the solution from `q₀`, in the time `y.1`, with the initial
momentum `P₀ y`. -/
def localAction (H : PhaseSpace ι) (q₀ : ι → ℝ) (P₀ : ℝ × (ι → ℝ) → ι → ℝ)
    (y : ℝ × (ι → ℝ)) : ℝ :=
  action 0 y.1 (phaseLagrangian H) fun t => flow (hamiltonianField H) (t, Sum.elim q₀ (P₀ y))

/-- The differential `Σᵢ Pᵢ dqᵢ − E dt`, as a linear form of the time and the
position. -/
def actionDifferential (P : ι → ℝ) (E : ℝ) : ℝ × (ι → ℝ) →L[ℝ] ℝ :=
  (∑ i, P i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).comp
      (ContinuousLinearMap.snd ℝ ℝ (ι → ℝ)) -
    E • ContinuousLinearMap.fst ℝ ℝ (ι → ℝ)

omit [DecidableEq ι] in
theorem actionDifferential_apply (P : ι → ℝ) (E : ℝ) (v : ℝ × (ι → ℝ)) :
    actionDifferential P E v = ∑ i, P i * v.2 i - E * v.1 := by
  simp [actionDifferential]

omit [DecidableEq ι] in
theorem continuous_actionDifferential :
    Continuous fun x : (ι → ℝ) × ℝ => actionDifferential x.1 x.2 := by
  unfold actionDifferential
  refine Continuous.sub ?_ (continuous_snd.smul continuous_const)
  refine Continuous.clm_comp ?_ continuous_const
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp continuous_fst).smul continuous_const

/-- The derivative of the action along a line in the space of times and end
points. -/
theorem hasDerivAt_localAction_line (H : PhaseSpace ι) (q₀ : ι → ℝ)
    {W : Set (ℝ × (ι → ℝ))} {P₀ : ℝ × (ι → ℝ) → ι → ℝ} (hW : IsOpen W)
    (hP₀ : ContDiffOn ℝ ∞ P₀ W)
    (hsol : ∀ y ∈ W, (y.1, P₀ y) ∈ startDomain H q₀ ∧ endPosition H q₀ (y.1, P₀ y) = y.2)
    {y : ℝ × (ι → ℝ)} (hy : y ∈ W) (v : ℝ × (ι → ℝ)) :
    HasDerivAt (fun s : ℝ => localAction H q₀ P₀ (y + s • v))
      (actionDifferential (endMomentum H q₀ (y.1, P₀ y))
        (H.val (Sum.elim y.2 (endMomentum H q₀ (y.1, P₀ y)))) v) 0 := by
  have hX := contDiff_hamiltonianField H
  -- the line and the curve of initial points
  have hline : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have hlinec : ContDiff ℝ ∞ fun s : ℝ => y + s • v :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hline0 : y + (0 : ℝ) • v = y := by simp
  have hV : IsOpen ((fun s : ℝ => y + s • v) ⁻¹' W) := hW.preimage hlinec.continuous
  have h0V : (0 : ℝ) ∈ (fun s : ℝ => y + s • v) ⁻¹' W := by
    change y + (0 : ℝ) • v ∈ W
    rwa [hline0]
  have hz₀ : ContDiffOn ℝ ∞ (fun s : ℝ => (Sum.elim q₀ (P₀ (y + s • v)) : ι ⊕ ι → ℝ))
      ((fun s : ℝ => y + s • v) ⁻¹' W) :=
    (contDiff_elim_right q₀).comp_contDiffOn (hP₀.comp hlinec.contDiffOn fun _ hs => hs)
  have ha : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 0 := hasDerivAt_const 0 0
  have hb : HasDerivAt (fun s : ℝ => (y + s • v).1) v.1 0 :=
    (ContinuousLinearMap.fst ℝ ℝ (ι → ℝ)).hasFDerivAt.comp_hasDerivAt 0 hline
  have hyD : (y.1, Sum.elim q₀ (P₀ y)) ∈ flowDomain (hamiltonianField H) := (hsol y hy).1
  have hmem : ∀ t ∈ uIcc ((fun _ : ℝ => (0 : ℝ)) 0) ((fun s : ℝ => (y + s • v).1) 0),
      (t, (fun s : ℝ => (Sum.elim q₀ (P₀ (y + s • v)) : ι ⊕ ι → ℝ)) 0) ∈
        flowDomain (hamiltonianField H) := by
    intro t ht
    change t ∈ uIcc 0 (y + (0 : ℝ) • v).1 at ht
    change (t, Sum.elim q₀ (P₀ (y + (0 : ℝ) • v))) ∈ flowDomain (hamiltonianField H)
    rw [hline0] at ht ⊢
    exact mem_flowDomain_of_mem_uIcc hyD ht
  have hmain := hasDerivAt_action_hamiltonianFlow H hV hz₀ h0V ha hb hmem
  -- the end point of the solution of the parameter `0`
  have hend : flow (hamiltonianField H) ((y + (0 : ℝ) • v).1,
      Sum.elim q₀ (P₀ (y + (0 : ℝ) • v))) =
      Sum.elim y.2 (endMomentum H q₀ (y.1, P₀ y)) := by
    rw [hline0, ← (hsol y hy).2]
    exact (elim_endPosition_endMomentum H q₀ (y.1, P₀ y)).symm
  -- the displacement of the end point
  have hF : DifferentiableAt ℝ (fun s : ℝ => flow (hamiltonianField H)
      ((y + s • v).1, Sum.elim q₀ (P₀ (y + s • v)))) 0 := by
    have hpair : DifferentiableAt ℝ (fun s : ℝ =>
        ((y + s • v).1, (Sum.elim q₀ (P₀ (y + s • v)) : ι ⊕ ι → ℝ))) 0 :=
      (hb.differentiableAt).prodMk
        ((hz₀.contDiffAt (hV.mem_nhds h0V)).differentiableAt (by simp))
    have hfl : DifferentiableAt ℝ (flow (hamiltonianField H))
        ((y + (0 : ℝ) • v).1, Sum.elim q₀ (P₀ (y + (0 : ℝ) • v))) := by
      rw [hline0]
      exact (contDiffAt_flow hX hyD).differentiableAt (by simp)
    exact DifferentiableAt.comp (g := flow (hamiltonianField H))
      (f := fun s : ℝ => ((y + s • v).1, (Sum.elim q₀ (P₀ (y + s • v)) : ι ⊕ ι → ℝ)))
      (0 : ℝ) hfl hpair
  have hendq : ∀ i, deriv (fun s : ℝ => flow (hamiltonianField H)
      ((y + s • v).1, Sum.elim q₀ (P₀ (y + s • v)))) 0 (Sum.inl i) = v.2 i := by
    intro i
    have h1 := (hasDerivAt_pi.mp hF.hasDerivAt) (Sum.inl i)
    have h2 : HasDerivAt (fun s : ℝ => y.2 i + s * v.2 i) (v.2 i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v.2 i)).const_add (y.2 i)
    have hev : (fun s : ℝ => flow (hamiltonianField H)
        ((y + s • v).1, Sum.elim q₀ (P₀ (y + s • v))) (Sum.inl i)) =ᶠ[𝓝 0]
        fun s : ℝ => y.2 i + s * v.2 i := by
      filter_upwards [hV.mem_nhds h0V] with s hs
      have he := congrFun (hsol (y + s • v) hs).2 i
      exact he
    exact h1.unique (h2.congr_of_eventuallyEq hev)
  -- the initial point does not move in the positions
  have hz₀d : DifferentiableAt ℝ (fun s : ℝ => flow (hamiltonianField H)
      ((fun _ : ℝ => (0 : ℝ)) s, Sum.elim q₀ (P₀ (y + s • v)))) 0 := by
    have he : (fun s : ℝ => flow (hamiltonianField H)
        ((fun _ : ℝ => (0 : ℝ)) s, Sum.elim q₀ (P₀ (y + s • v)))) =
        fun s : ℝ => (Sum.elim q₀ (P₀ (y + s • v)) : ι ⊕ ι → ℝ) := by
      funext s
      exact flow_zero _ _
    rw [he]
    exact (hz₀.contDiffAt (hV.mem_nhds h0V)).differentiableAt (by simp)
  have hstartq : ∀ i, deriv (fun s : ℝ => flow (hamiltonianField H)
      ((fun _ : ℝ => (0 : ℝ)) s, Sum.elim q₀ (P₀ (y + s • v)))) 0 (Sum.inl i) = 0 := by
    intro i
    have h1 := (hasDerivAt_pi.mp hz₀d.hasDerivAt) (Sum.inl i)
    have hfun : (fun s : ℝ => flow (hamiltonianField H)
        ((fun _ : ℝ => (0 : ℝ)) s, Sum.elim q₀ (P₀ (y + s • v))) (Sum.inl i)) =
        fun _ : ℝ => q₀ i := by
      funext s
      change flow (hamiltonianField H) (0, Sum.elim q₀ (P₀ (y + s • v))) (Sum.inl i) = q₀ i
      rw [flow_zero]
      rfl
    rw [hfun] at h1
    exact h1.unique (hasDerivAt_const 0 (q₀ i))
  refine hmain.congr_deriv ?_
  change liouvilleForm ι (flow (hamiltonianField H)
        ((y + (0 : ℝ) • v).1, Sum.elim q₀ (P₀ (y + (0 : ℝ) • v))))
        (deriv (fun s : ℝ => flow (hamiltonianField H)
          ((y + s • v).1, Sum.elim q₀ (P₀ (y + s • v)))) 0) -
      H.val (flow (hamiltonianField H)
        ((y + (0 : ℝ) • v).1, Sum.elim q₀ (P₀ (y + (0 : ℝ) • v)))) * v.1 -
      (liouvilleForm ι (flow (hamiltonianField H)
        ((0 : ℝ), Sum.elim q₀ (P₀ (y + (0 : ℝ) • v))))
        (deriv (fun s : ℝ => flow (hamiltonianField H)
          ((fun _ : ℝ => (0 : ℝ)) s, Sum.elim q₀ (P₀ (y + s • v)))) 0) -
      H.val (flow (hamiltonianField H)
        ((0 : ℝ), Sum.elim q₀ (P₀ (y + (0 : ℝ) • v)))) * 0) = _
  rw [hend, liouvilleForm_apply, liouvilleForm_apply, actionDifferential_apply]
  simp only [hendq, hstartq, Sum.elim_inr, mul_zero, Finset.sum_const_zero, sub_zero]

/-- Landau–Lifshitz §43: away from conjugate points the action of the solution
from `q₀` is a differentiable function of the time and the end point, with
`dS = Σᵢ pᵢ dqᵢ − H dT`. -/
theorem exists_localAction (H : PhaseSpace ι) (q₀ : ι → ℝ) {x₀ : ℝ × (ι → ℝ)}
    (hx₀ : x₀ ∈ startDomain H q₀)
    (hinv : (fderiv ℝ (fun p => endPosition H q₀ (x₀.1, p)) x₀.2).IsInvertible) :
    ∃ (W : Set (ℝ × (ι → ℝ))) (P₀ : ℝ × (ι → ℝ) → ι → ℝ), IsOpen W ∧
      (x₀.1, endPosition H q₀ x₀) ∈ W ∧ P₀ (x₀.1, endPosition H q₀ x₀) = x₀.2 ∧
      ContDiffOn ℝ ∞ P₀ W ∧
      (∀ y ∈ W, (y.1, P₀ y) ∈ startDomain H q₀ ∧ endPosition H q₀ (y.1, P₀ y) = y.2) ∧
      ∀ y ∈ W, HasFDerivAt (localAction H q₀ P₀)
        (actionDifferential (endMomentum H q₀ (y.1, P₀ y))
          (H.val (Sum.elim y.2 (endMomentum H q₀ (y.1, P₀ y))))) y := by
  obtain ⟨W, P₀, hW, hmem, hP₀x, hP₀, hsol⟩ := exists_initialMomentum H q₀ hx₀ hinv
  refine ⟨W, P₀, hW, hmem, hP₀x, hP₀, hsol, fun y hy => ?_⟩
  have hpair : ContDiffOn ℝ ∞ (fun w : ℝ × (ι → ℝ) => (w.1, P₀ w)) W :=
    contDiffOn_fst.prodMk hP₀
  have hP : ContinuousOn (fun w : ℝ × (ι → ℝ) => endMomentum H q₀ (w.1, P₀ w)) W :=
    (ContDiffOn.comp (g := endMomentum H q₀) (f := fun w : ℝ × (ι → ℝ) => (w.1, P₀ w))
      (contDiffOn_endMomentum H q₀) hpair fun w hw => (hsol w hw).1).continuousOn
  have hel : ContinuousOn (fun w : ℝ × (ι → ℝ) =>
      (Sum.elim w.2 (endMomentum H q₀ (w.1, P₀ w)) : ι ⊕ ι → ℝ)) W :=
    Continuous.comp_continuousOn
      (g := fun x : (ι → ℝ) × (ι → ℝ) => (Sum.elim x.1 x.2 : ι ⊕ ι → ℝ))
      (f := fun w : ℝ × (ι → ℝ) => (w.2, endMomentum H q₀ (w.1, P₀ w)))
      contDiff_elim.continuous (continuousOn_snd.prodMk hP)
  have hE : ContinuousOn (fun w : ℝ × (ι → ℝ) =>
      H.val (Sum.elim w.2 (endMomentum H q₀ (w.1, P₀ w)))) W :=
    Continuous.comp_continuousOn (g := (H.val : (ι ⊕ ι → ℝ) → ℝ))
      (f := fun w : ℝ × (ι → ℝ) =>
        (Sum.elim w.2 (endMomentum H q₀ (w.1, P₀ w)) : ι ⊕ ι → ℝ))
      (contDiff_val H).continuous hel
  have hℓ : ContinuousOn (fun w : ℝ × (ι → ℝ) =>
      actionDifferential (endMomentum H q₀ (w.1, P₀ w))
        (H.val (Sum.elim w.2 (endMomentum H q₀ (w.1, P₀ w))))) W :=
    Continuous.comp_continuousOn (g := fun x : (ι → ℝ) × ℝ => actionDifferential x.1 x.2)
      (f := fun w : ℝ × (ι → ℝ) => (endMomentum H q₀ (w.1, P₀ w),
        H.val (Sum.elim w.2 (endMomentum H q₀ (w.1, P₀ w)))))
      continuous_actionDifferential (hP.prodMk hE)
  have hline : ∀ᶠ w in 𝓝 y, ∀ v : ℝ × (ι → ℝ),
      HasDerivAt (fun s : ℝ => localAction H q₀ P₀ (w + s • v))
        ((fun w : ℝ × (ι → ℝ) => actionDifferential (endMomentum H q₀ (w.1, P₀ w))
          (H.val (Sum.elim w.2 (endMomentum H q₀ (w.1, P₀ w))))) w v) 0 :=
    Filter.eventually_of_mem (hW.mem_nhds hy) fun w hw v =>
      hasDerivAt_localAction_line H q₀ hW hP₀ hsol hw v
  exact hasFDerivAt_of_hasDerivAt_line hline (hℓ.continuousAt (hW.mem_nhds hy))

/-- The Hamilton–Jacobi equation `∂S/∂T + H(q, ∂S/∂q) = 0` for a function whose
differential is `Σᵢ pᵢ dqᵢ − H(q, p) dT`. -/
theorem localAction_hamiltonJacobi (H : PhaseSpace ι) {S : ℝ × (ι → ℝ) → ℝ} {P : ι → ℝ}
    {y : ℝ × (ι → ℝ)}
    (hS : HasFDerivAt S (actionDifferential P (H.val (Sum.elim y.2 P))) y) :
    fderiv ℝ S y (1, 0) +
      H.val (Sum.elim y.2 fun i => fderiv ℝ S y (0, Pi.single i 1)) = 0 := by
  have hP : (fun i => fderiv ℝ S y (0, Pi.single i 1)) = P := by
    funext i
    rw [hS.fderiv, actionDifferential_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hP, hS.fderiv, actionDifferential_apply]
  simp

/-! ### The free particle -/

open PhaseSpace

theorem hamiltonianField_kineticEnergy_inl (m : ι → ℝ) (z : ι ⊕ ι → ℝ) (i : ι) :
    hamiltonianField (kineticEnergy m) z (Sum.inl i) = (m i)⁻¹ * z (Sum.inr i) := by
  rw [hamiltonianField_inl, partialDerivation_inr_kineticEnergy]
  rfl

theorem hamiltonianField_kineticEnergy_inr (m : ι → ℝ) (z : ι ⊕ ι → ℝ) (i : ι) :
    hamiltonianField (kineticEnergy m) z (Sum.inr i) = 0 := by
  rw [hamiltonianField_inr, partialDerivation_inl_kineticEnergy]
  simp

/-- The flow of a free particle: uniform motion. -/
theorem flow_kineticEnergy (m : ι → ℝ) (t : ℝ) (z : ι ⊕ ι → ℝ) :
    (t, z) ∈ flowDomain (hamiltonianField (kineticEnergy m)) ∧
      flow (hamiltonianField (kineticEnergy m)) (t, z) =
        Sum.elim (fun i => z (Sum.inl i) + t * ((m i)⁻¹ * z (Sum.inr i)))
          (fun i => z (Sum.inr i)) := by
  have hy : ∀ r : ℝ, HasDerivAt
      (fun s : ℝ => (Sum.elim (fun i => z (Sum.inl i) + s * ((m i)⁻¹ * z (Sum.inr i)))
        (fun i => z (Sum.inr i)) : ι ⊕ ι → ℝ))
      (hamiltonianField (kineticEnergy m)
        (Sum.elim (fun i => z (Sum.inl i) + r * ((m i)⁻¹ * z (Sum.inr i)))
          (fun i => z (Sum.inr i)))) r := by
    intro r
    rw [hasDerivAt_pi]
    intro a
    rcases a with i | i
    · rw [hamiltonianField_kineticEnergy_inl]
      simpa using ((hasDerivAt_id r).mul_const ((m i)⁻¹ * z (Sum.inr i))).const_add
        (z (Sum.inl i))
    · rw [hamiltonianField_kineticEnergy_inr]
      exact hasDerivAt_const r (z (Sum.inr i))
  have h0 : (fun s : ℝ => (Sum.elim (fun i => z (Sum.inl i) + s * ((m i)⁻¹ * z (Sum.inr i)))
      (fun i => z (Sum.inr i)) : ι ⊕ ι → ℝ)) 0 = z := by
    funext a
    rcases a with i | i <;> simp
  exact ⟨mem_flowDomain_of_hasDerivWithinAt (contDiff_hamiltonianField _).continuous h0
      fun r _ => (hy r).hasDerivWithinAt,
    flow_eq_of_hasDerivWithinAt ((contDiff_hamiltonianField _).of_le (by simp)) h0
      fun r _ => (hy r).hasDerivWithinAt⟩

theorem endPosition_kineticEnergy (m : ι → ℝ) (q₀ : ι → ℝ) (x : ℝ × (ι → ℝ)) :
    endPosition (kineticEnergy m) q₀ x = fun i => q₀ i + x.1 * ((m i)⁻¹ * x.2 i) := by
  funext i
  rw [endPosition, (flow_kineticEnergy m x.1 (Sum.elim q₀ x.2)).2]
  rfl

/-- For a free particle no time other than zero is conjugate: the end point
determines the initial momentum. -/
theorem isInvertible_fderiv_endPosition_kineticEnergy {m : ι → ℝ} (hm : ∀ i, m i ≠ 0)
    {T : ℝ} (hT : T ≠ 0) (q₀ p : ι → ℝ) :
    (fderiv ℝ (fun p => endPosition (kineticEnergy m) q₀ (T, p)) p).IsInvertible := by
  let L : (ι → ℝ) →L[ℝ] (ι → ℝ) := ContinuousLinearMap.pi fun i =>
    (T * (m i)⁻¹) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i
  let L' : (ι → ℝ) →L[ℝ] (ι → ℝ) := ContinuousLinearMap.pi fun i =>
    (T * (m i)⁻¹)⁻¹ • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i
  have hne : ∀ i, T * (m i)⁻¹ ≠ 0 := fun i => mul_ne_zero hT (inv_ne_zero (hm i))
  have hfun : (fun p => endPosition (kineticEnergy m) q₀ (T, p)) = fun p => q₀ + L p := by
    funext p i
    rw [endPosition_kineticEnergy]
    simp [L]
    ring
  have hd : fderiv ℝ (fun p => endPosition (kineticEnergy m) q₀ (T, p)) p = L := by
    rw [hfun]
    exact (L.hasFDerivAt.const_add q₀).fderiv
  rw [hd]
  refine ContinuousLinearMap.IsInvertible.of_inverse (g := L') ?_ ?_
  · ext v i
    have hmi := hm i
    simp [L, L']
    field_simp
  · ext v i
    have hmi := hm i
    simp [L, L']
    field_simp

/-- The action of a free particle is a differentiable function of the time and
the end point near every end point reached in a time other than zero, with
`dS = Σᵢ pᵢ dqᵢ − H dT`. The hypotheses of `exists_localAction` hold. -/
theorem exists_localAction_kineticEnergy {m : ι → ℝ} (hm : ∀ i, m i ≠ 0) {T : ℝ}
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
  exists_localAction (kineticEnergy m) q₀ (x₀ := (T, p₀))
    (flow_kineticEnergy m T (Sum.elim q₀ p₀)).1
    (isInvertible_fderiv_endPosition_kineticEnergy hm hT q₀ p₀)

end ProjectAInos.Mechanics
