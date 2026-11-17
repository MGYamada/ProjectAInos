/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Poisson.Liouville
public import ProjectAinos.Mechanics.Poisson.Trajectory
public import ProjectAinos.SmoothAlgebra.FreeCalculus
public import ProjectAinos.SmoothGeometry.ODE.FlowComplete

/-!
# Hamiltonian vector fields in the analytic model, and Liouville's theorem

A derivation of a free C∞-ring on finitely many generators is a smooth vector
field on `κ → ℝ` (`FreeSmoothRing.realField`). This file connects the algebraic
statements with the flow of that field.

* `isTrajectory_iff_hasDerivAt`: a family of smooth functions of time is a
  trajectory of a Hamiltonian if and only if the real curve of its values
  solves the differential equation of the field.
* `traceCLM_fderiv_realField`: the trace of the derivative of the field is the
  value of the divergence `Σₐ ∂ₐ (D xₐ)`.
* `hamiltonianField H` is the field of the canonical bracket,
  `(∂H/∂p, −∂H/∂q)`. Its divergence is zero, so its flow preserves the Lebesgue
  measure of the phase space (Liouville's theorem, Landau–Lifshitz §46):
  `volume_image_hamiltonianFlow` for a measurable set in the domain of the
  flow at the time `t`, and `measurePreserving_hamiltonianFlow` for a flow
  defined for all times and points.
* A trajectory is a line of the flow (`IsTrajectory.flow_eq`), and when the flow
  is defined for all times and points there is a trajectory through every
  point (`exists_isTrajectory`).
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace ProjectAinos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing
open SmoothGeometry SmoothGeometry.LinearODE SmoothGeometry.NonlinearODE

/-! ### Curves of time functions as real curves -/

section RealCurve

variable {κ : Type*}

/-- The real curve of a family of smooth functions of time. -/
def realCurve (c : κ → TimeFunction) (t : ℝ) : κ → ℝ := fun a => c a fun _ => t

@[simp] theorem realCurve_apply (c : κ → TimeFunction) (t : ℝ) (a : κ) :
    realCurve c t a = c a fun _ => t := rfl

/-- The value of an observable along a curve, at a time, is its value at the
point of the real curve. -/
theorem lift_apply_const (c : κ → TimeFunction) (s : FreeSmoothRing κ) (t : ℝ) :
    FreeSmoothRing.lift c s (fun _ => t) = s.val (realCurve c t) := by
  rw [lift_curve_apply, lift_real]
  rfl

variable [Fintype κ]

omit [Fintype κ] in
/-- The velocity of the real curve. -/
theorem hasDerivAt_realCurve (c : κ → TimeFunction) (t : ℝ) :
    HasDerivAt (realCurve c) (fun a => timeDerivative (c a) fun _ => t) t := by
  rw [hasDerivAt_pi]
  intro a
  rw [TimeFunction.timeDerivative_apply]
  exact (((c a).contDiff_apply_const).differentiable (by simp) t).hasDerivAt

/-- A family of smooth functions of time is an integral curve of a derivation if
and only if its real curve solves the differential equation of the field. -/
theorem isIntegralCurve_iff_hasDerivAt
    (D : SmoothDerivation (FreeSmoothRing κ) (FreeSmoothRing κ)) (c : κ → TimeFunction) :
    IsIntegralCurve D c ↔ ∀ t, HasDerivAt (realCurve c) (realField D (realCurve c t)) t := by
  constructor
  · intro h t
    refine (hasDerivAt_realCurve c t).congr_deriv (funext fun a => ?_)
    rw [h a, lift_apply_const]
    rfl
  · intro h a
    refine TimeFunction.ext_apply_const fun t => ?_
    have h1 := congrFun ((hasDerivAt_realCurve c t).unique (h t)) a
    rw [lift_apply_const]
    exact h1

/-- A family of smooth functions of time is a trajectory if and only if its real
curve solves the differential equation of the Hamiltonian vector field. -/
theorem isTrajectory_iff_hasDerivAt (π : PoissonStructure (FreeSmoothRing κ))
    (H : FreeSmoothRing κ) (c : κ → TimeFunction) :
    IsTrajectory π H c ↔
      ∀ t, HasDerivAt (realCurve c) (realField (π.hamiltonian H) (realCurve c t)) t := by
  rw [← isIntegralCurve_hamiltonian_iff, isIntegralCurve_iff_hasDerivAt]

end RealCurve

/-! ### The divergence -/

section Divergence

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The trace of the derivative of the vector field of a derivation is the value
of its divergence. -/
theorem traceCLM_fderiv_realField
    (D : SmoothDerivation (FreeSmoothRing κ) (FreeSmoothRing κ)) (z : κ → ℝ) :
    traceCLM (fderiv ℝ (realField D) z) = (divergence D).val z := by
  rw [traceCLM_apply, LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ κ), Matrix.trace]
  have hdiag : ∀ a, Matrix.diag (LinearMap.toMatrix (Pi.basisFun ℝ κ) (Pi.basisFun ℝ κ)
      (fderiv ℝ (realField D) z : (κ → ℝ) →ₗ[ℝ] κ → ℝ)) a =
      (partialDerivation a (D (generator a))).val z := by
    intro a
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply]
    change fderiv ℝ (realField D) z (Pi.single a 1) a = _
    rw [fderiv_realField_apply, Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  simp only [hdiag]
  have hsum : (divergence D).val z = ∑ a, (partialDerivation a (D (generator a))).val z := by
    rw [divergence]
    change ((∑ a, partialDerivation a (D (generator a)) : FreeSmoothRing κ) :
      (κ → ℝ) → ℝ) z = _
    rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  rw [hsum]

end Divergence

/-! ### The Hamiltonian field of the canonical bracket -/

section Canonical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Hamiltonian vector field `(∂H/∂p, −∂H/∂q)` on the phase space. -/
def hamiltonianField (H : PhaseSpace ι) : (ι ⊕ ι → ℝ) → ι ⊕ ι → ℝ :=
  realField ((PhaseSpace.canonical ι).hamiltonian H)

theorem hamiltonianField_inl (H : PhaseSpace ι) (z : ι ⊕ ι → ℝ) (i : ι) :
    hamiltonianField H z (Sum.inl i) = (partialDerivation (Sum.inr i) H).val z := by
  change ((PhaseSpace.canonical ι).bracket (PhaseSpace.q i) H).val z = _
  rw [PhaseSpace.canonical_q_bracket]

theorem hamiltonianField_inr (H : PhaseSpace ι) (z : ι ⊕ ι → ℝ) (i : ι) :
    hamiltonianField H z (Sum.inr i) = -(partialDerivation (Sum.inl i) H).val z := by
  change ((PhaseSpace.canonical ι).bracket (PhaseSpace.p i) H).val z = _
  rw [PhaseSpace.canonical_p_bracket]
  rfl

theorem contDiff_hamiltonianField (H : PhaseSpace ι) : ContDiff ℝ ∞ (hamiltonianField H) :=
  contDiff_realField _

/-- Hamilton's equations for the real curve. -/
theorem isTrajectory_canonical_iff_hasDerivAt (H : PhaseSpace ι)
    (c : ι ⊕ ι → TimeFunction) :
    IsTrajectory (PhaseSpace.canonical ι) H c ↔
      ∀ t, HasDerivAt (realCurve c) (hamiltonianField H (realCurve c t)) t :=
  isTrajectory_iff_hasDerivAt _ H c

/-- The Hamiltonian field has divergence zero. -/
theorem traceCLM_fderiv_hamiltonianField (H : PhaseSpace ι) (z : ι ⊕ ι → ℝ) :
    traceCLM (fderiv ℝ (hamiltonianField H) z) = 0 := by
  rw [hamiltonianField, traceCLM_fderiv_realField, divergence_hamiltonian]
  rfl

/-- Liouville's theorem: the flow of a Hamiltonian preserves the Lebesgue measure
of every measurable set of the phase space that lies in its domain at the time
`t`. -/
theorem volume_image_hamiltonianFlow (H : PhaseSpace ι) {t : ℝ} {A : Set (ι ⊕ ι → ℝ)}
    (hA : MeasurableSet A) (hAD : ∀ z ∈ A, (t, z) ∈ flowDomain (hamiltonianField H)) :
    volume ((fun z => flow (hamiltonianField H) (t, z)) '' A) = volume A :=
  (isLocalFlowOn_flow (contDiff_hamiltonianField H)).measure_image volume
    ((contDiff_hamiltonianField H).of_le (by simp)) (traceCLM_fderiv_hamiltonianField H) hA hAD

/-- Liouville's theorem for a flow defined for all times and points. -/
theorem measurePreserving_hamiltonianFlow (H : PhaseSpace ι)
    (hc : flowDomain (hamiltonianField H) = univ) (t : ℝ) :
    MeasurePreserving (fun z => flow (hamiltonianField H) (t, z)) volume volume :=
  (isLocalFlowOn_flow (contDiff_hamiltonianField H)).measurePreserving volume
    ((contDiff_hamiltonianField H).of_le (by simp)) (traceCLM_fderiv_hamiltonianField H) hc t

/-- A trajectory is a line of the flow. -/
theorem IsTrajectory.flow_eq {H : PhaseSpace ι} {c : ι ⊕ ι → TimeFunction}
    (h : IsTrajectory (PhaseSpace.canonical ι) H c) (t : ℝ) :
    (t, realCurve c 0) ∈ flowDomain (hamiltonianField H) ∧
      flow (hamiltonianField H) (t, realCurve c 0) = realCurve c t := by
  have hd := (isTrajectory_canonical_iff_hasDerivAt H c).mp h
  exact ⟨mem_flowDomain_of_hasDerivWithinAt (contDiff_hamiltonianField H).continuous rfl
      fun r _ => (hd r).hasDerivWithinAt,
    flow_eq_of_hasDerivWithinAt ((contDiff_hamiltonianField H).of_le (by simp)) rfl
      fun r _ => (hd r).hasDerivWithinAt⟩

/-- When the flow is defined for all times and points, there is a trajectory
through every point of the phase space. -/
theorem exists_isTrajectory (H : PhaseSpace ι) (hc : flowDomain (hamiltonianField H) = univ)
    (z₀ : ι ⊕ ι → ℝ) :
    ∃ c : ι ⊕ ι → TimeFunction, IsTrajectory (PhaseSpace.canonical ι) H c ∧
      realCurve c 0 = z₀ := by
  have hmem : ∀ p : ℝ × (ι ⊕ ι → ℝ), p ∈ flowDomain (hamiltonianField H) := fun p =>
    hc ▸ mem_univ p
  have hflow : ContDiff ℝ ∞ (flow (hamiltonianField H)) :=
    contDiff_iff_contDiffAt.mpr fun p =>
      contDiffAt_flow (contDiff_hamiltonianField H) (hmem p)
  have hcomp : ∀ a : ι ⊕ ι, ContDiff ℝ ∞ fun s : Fin 1 → ℝ =>
      flow (hamiltonianField H) (s 0, z₀) a := by
    intro a
    have h1 : ContDiff ℝ ∞ fun s : Fin 1 → ℝ => (s 0, z₀) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).contDiff.prodMk
        contDiff_const
    have h2 : ContDiff ℝ ∞ fun y : ι ⊕ ι → ℝ => y a :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ⊕ ι => ℝ) a).contDiff
    exact h2.comp (hflow.comp h1)
  refine ⟨fun a => SmoothOperation.ofContDiff _ (hcomp a), ?_, ?_⟩
  · rw [isTrajectory_canonical_iff_hasDerivAt]
    intro t
    exact hasDerivAt_flow (contDiff_hamiltonianField H) (hmem (t, z₀))
  · funext a
    change flow (hamiltonianField H) (0, z₀) a = z₀ a
    rw [flow_zero]

end Canonical

end ProjectAinos.Mechanics
