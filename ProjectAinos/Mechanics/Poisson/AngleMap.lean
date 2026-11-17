/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Poisson.PeriodChart
public import ProjectAinos.Mechanics.LineIntegral
public import ProjectAinos.Variational.LineDerivative

/-!
# The angles of a chart of periods and the action integrals

For a chart of periods `eₖ(s)` of integrals in involution (`IsPeriodChart`):

* `angleMap F x₀ e (s, φ) = g^{Σₖ (φₖ/2π) eₖ(s)} (sectionPoint s)`: the angles
  `φ` on the torus through the point `s` of the transversal. It has the period
  `2π` in each angle (`angleMap_add_period`) and the flow of `Σᵢ cᵢ X_{Fᵢ}` is a
  uniform motion of the angles (`flow_angleMap`).
* `actionForm F x₀ e s a k = (1/2π) Σᵢ eₖ(s)ᵢ dGᵢ(s) a`, with `G` the integrals
  on the transversal. `symplecticForm_angleMap`: in the co-ordinates `(s, φ)`
  the symplectic form is `Σₖ dφₖ ∧ (actionForm)ₖ`.
* `loopAction F x₀ e k (s, φ)` is `(1/2π) ∮ p dq` over the `k`-th cycle through
  the point with the angles `φ`. `hasDerivAt_loopAction`: its derivative in a
  direction `(a, α)` is `actionForm s a k`. So it does not depend on the angles
  (`loopAction_eq`), and `actionMap` has the derivative `actionForm`
  (`hasFDerivAt_actionMap`): the forms `actionForm` are the differentials of the
  action variables.
-/

@[expose] public section
noncomputable section

open Set Module Filter
open scoped ContDiff Topology Real

namespace ProjectAinos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing
open SmoothGeometry SmoothGeometry.NonlinearODE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The times of the joint flow as functions of the angles -/

/-- The times of the joint flow for the angles `φ`: `Σₖ (φₖ/2π) eₖ(s)`. -/
def angleTime (e : ι → (ι → ℝ) → ι → ℝ) (s φ : ι → ℝ) : ι → ℝ :=
  ∑ k, (φ k / (2 * π)) • e k s

omit [DecidableEq ι] in
theorem angleTime_apply (e : ι → (ι → ℝ) → ι → ℝ) (s φ : ι → ℝ) (i : ι) :
    angleTime e s φ i = ∑ k, φ k / (2 * π) * e k s i := by
  rw [angleTime, Finset.sum_apply]
  rfl

omit [DecidableEq ι] in
theorem angleTime_add (e : ι → (ι → ℝ) → ι → ℝ) (s φ ψ : ι → ℝ) :
    angleTime e s (φ + ψ) = angleTime e s φ + angleTime e s ψ := by
  simp only [angleTime, Pi.add_apply, add_div, add_smul, Finset.sum_add_distrib]

omit [DecidableEq ι] in
theorem angleTime_smul (e : ι → (ι → ℝ) → ι → ℝ) (s : ι → ℝ) (c : ℝ) (φ : ι → ℝ) :
    angleTime e s (c • φ) = c • angleTime e s φ := by
  simp only [angleTime, Pi.smul_apply, smul_eq_mul, mul_div_assoc, mul_smul, Finset.smul_sum]

omit [DecidableEq ι] in
/-- The pairing of the times with a vector, through the angles. -/
theorem sum_angleTime_mul (e : ι → (ι → ℝ) → ι → ℝ) (s α v : ι → ℝ) :
    ∑ i, angleTime e s α i * v i = ∑ k, α k * ((2 * π)⁻¹ * ∑ i, e k s i * v i) := by
  simp only [angleTime_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [div_eq_mul_inv]
  ring

/-- The angles on the tori: `(s, φ) ↦ g^{Σₖ (φₖ/2π) eₖ(s)} (sectionPoint s)`. -/
def angleMap (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (e : ι → (ι → ℝ) → ι → ℝ)
    (p : (ι → ℝ) × (ι → ℝ)) : ι ⊕ ι → ℝ :=
  torusMap F x₀ (p.1, angleTime e p.1 p.2)

/-- The differentials of the action variables on the transversal:
`(1/2π) Σᵢ eₖ(s)ᵢ dGᵢ(s) a`. -/
def actionForm (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (e : ι → (ι → ℝ) → ι → ℝ)
    (s : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a k => (2 * π)⁻¹ * ∑ i, e k s i * sectionDeriv F x₀ s a i
      map_add' := fun a b => by
        funext k
        simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        funext k
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring }

theorem actionForm_apply (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ)
    (e : ι → (ι → ℝ) → ι → ℝ) (s a : ι → ℝ) (k : ι) :
    actionForm F x₀ e s a k = (2 * π)⁻¹ * ∑ i, e k s i * sectionDeriv F x₀ s a i := rfl

section Chart

variable {F : ι → PhaseSpace ι} {x₀ : ι ⊕ ι → ℝ} {M : Set (ι ⊕ ι → ℝ)} {S : Set (ι → ℝ)}
  {e : ι → (ι → ℝ) → ι → ℝ}

theorem IsPeriodChart.angleMap_mem (h : IsPeriodChart F x₀ M S e) {s : ι → ℝ} (hs : s ∈ S)
    (φ : ι → ℝ) : angleMap F x₀ e (s, φ) ∈ M :=
  h.torusMap_mem hs _

/-- The integrals depend on the point of the transversal only. -/
theorem IsPeriodChart.integralMap_angleMap (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {s : ι → ℝ} (hs : s ∈ S)
    (φ : ι → ℝ) : integralMap F (angleMap F x₀ e (s, φ)) = sectionIntegral F x₀ s :=
  h.integralMap_torusMap hF hs _

/-- The angle map has the period `2π` in each angle. -/
theorem IsPeriodChart.angleMap_add_period (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {s : ι → ℝ} (hs : s ∈ S)
    (φ : ι → ℝ) (n : ι → ℤ) :
    angleMap F x₀ e (s, fun k => φ k + 2 * π * n k) = angleMap F x₀ e (s, φ) := by
  have hX := contDiff_hamFields F
  have hc := pairwiseCommute_hamiltonianField hF
  have hσ := h.mem s hs
  have hper : ∑ k, (n k : ℝ) • e k s ∈ periods hX hc h.invariant hσ := by
    refine AddSubgroup.sum_mem _ fun k _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact AddSubgroup.zsmul_mem _ ((mem_periods hX hc h.invariant hσ).mpr (h.period k s hs)) _
  have hπ : (2 * π) ≠ 0 := by positivity
  have eT : angleTime e s (fun k => φ k + 2 * π * n k) =
      angleTime e s φ + ∑ k, (n k : ℝ) • e k s := by
    simp only [angleTime]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← add_smul]
    congr 1
    field_simp
  change jointFlow (hamFields F) (angleTime e s fun k => φ k + 2 * π * n k)
    (sectionPoint F x₀ s) = jointFlow (hamFields F) (angleTime e s φ) (sectionPoint F x₀ s)
  rw [eT, jointFlow_add hX hc h.invariant _ _ hσ,
    (mem_periods hX hc h.invariant hσ).mp hper]

/-- The flow of `Σᵢ cᵢ X_{Fᵢ}` moves the angles uniformly, with the velocities
`ν` for which `Σₖ (νₖ/2π) eₖ(s) = c`. -/
theorem IsPeriodChart.flow_angleMap (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {s : ι → ℝ} (hs : s ∈ S)
    (φ : ι → ℝ) {ν c : ι → ℝ} (hν : angleTime e s ν = c) (r : ℝ) :
    flow (jointField (hamFields F) c) (r, angleMap F x₀ e (s, φ)) =
      angleMap F x₀ e (s, φ + r • ν) := by
  have hX := contDiff_hamFields F
  have hc := pairwiseCommute_hamiltonianField hF
  have hσ := h.mem s hs
  rw [← jointFlow_smul hX h.invariant r c (h.angleMap_mem hs φ)]
  change jointFlow (hamFields F) (r • c)
      (jointFlow (hamFields F) (angleTime e s φ) (sectionPoint F x₀ s)) =
    jointFlow (hamFields F) (angleTime e s (φ + r • ν)) (sectionPoint F x₀ s)
  rw [← jointFlow_add hX hc h.invariant _ _ hσ, angleTime_add, angleTime_smul, hν, add_comm]

/-- The flow of one integral. -/
theorem IsPeriodChart.flow_hamiltonianField_angleMap (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {s : ι → ℝ} (hs : s ∈ S)
    (φ : ι → ℝ) {ν : ι → ℝ} (i : ι) (hν : angleTime e s ν = Pi.single i 1) (r : ℝ) :
    flow (hamiltonianField (F i)) (r, angleMap F x₀ e (s, φ)) =
      angleMap F x₀ e (s, φ + r • ν) := by
  have h1 := h.flow_angleMap hF hs φ hν r
  rwa [jointField_single] at h1

/-! ### The derivative of the angle map -/

theorem IsPeriodChart.contDiffAt_angleTime (h : IsPeriodChart F x₀ M S e) {s : ι → ℝ}
    (hs : s ∈ S) (φ : ι → ℝ) :
    ContDiffAt ℝ 2 (fun p : (ι → ℝ) × (ι → ℝ) => angleTime e p.1 p.2) (s, φ) := by
  have hk : ∀ k, ContDiffAt ℝ 2
      (fun p : (ι → ℝ) × (ι → ℝ) => (p.2 k / (2 * π)) • e k p.1) (s, φ) := by
    intro k
    have h1 : ContDiffAt ℝ 2 (fun p : (ι → ℝ) × (ι → ℝ) => p.2 k / (2 * π)) (s, φ) :=
      (by fun_prop : ContDiff ℝ 2 fun p : (ι → ℝ) × (ι → ℝ) => p.2 k / (2 * π)).contDiffAt
    have h2 : ContDiffAt ℝ 2 (fun p : (ι → ℝ) × (ι → ℝ) => e k p.1) (s, φ) :=
      ContDiffAt.comp (s, φ) (g := e k) (f := fun p : (ι → ℝ) × (ι → ℝ) => p.1)
        (h.contDiffAt k s hs) contDiffAt_fst
    exact h1.smul h2
  exact ContDiffAt.sum fun k _ => hk k

theorem IsPeriodChart.contDiffAt_angleMap (h : IsPeriodChart F x₀ M S e) {s : ι → ℝ}
    (hs : s ∈ S) (φ : ι → ℝ) : ContDiffAt ℝ 2 (angleMap F x₀ e) (s, φ) := by
  have h1 : ContDiffAt ℝ 2 (torusMap F x₀) (s, angleTime e s φ) :=
    (h.contDiffAt_torusMap hs _).of_le (by simp)
  exact ContDiffAt.comp (s, φ) (g := torusMap F x₀)
    (f := fun p : (ι → ℝ) × (ι → ℝ) => (p.1, angleTime e p.1 p.2)) h1
    (contDiffAt_fst.prodMk (h.contDiffAt_angleTime hs φ))

/-- The derivative of the times in the point of the transversal and the angles. -/
theorem IsPeriodChart.fderiv_angleTime (h : IsPeriodChart F x₀ M S e) {s : ι → ℝ}
    (hs : s ∈ S) (φ a α : ι → ℝ) :
    fderiv ℝ (fun p : (ι → ℝ) × (ι → ℝ) => angleTime e p.1 p.2) (s, φ) (a, α) =
      angleTime e s α + ∑ k, (φ k / (2 * π)) • fderiv ℝ (e k) s a := by
  have hT := ((h.contDiffAt_angleTime hs φ).differentiableAt (by simp)).hasFDerivAt
  have h1 : HasDerivAt (fun ε : ℝ => angleTime e (s + ε • a) (φ + ε • α))
      (fderiv ℝ (fun p : (ι → ℝ) × (ι → ℝ) => angleTime e p.1 p.2) (s, φ) (a, α)) 0 :=
    Variational.hasDerivAt_line hT (a, α)
  have hk : ∀ k, HasDerivAt (fun ε : ℝ => ((φ + ε • α) k / (2 * π)) • e k (s + ε • a))
      ((φ k / (2 * π)) • fderiv ℝ (e k) s a + (α k / (2 * π)) • e k s) 0 := by
    intro k
    have hc : HasDerivAt (fun ε : ℝ => (φ + ε • α) k / (2 * π)) (α k / (2 * π)) 0 := by
      have h0 := (((hasDerivAt_id (0 : ℝ)).mul_const (α k)).const_add (φ k)).div_const (2 * π)
      rw [one_mul] at h0
      exact h0
    have hf := Variational.hasDerivAt_line
      ((h.contDiffAt k s hs).differentiableAt (by simp)).hasFDerivAt a
    exact (hc.smul hf).congr_deriv (by simp)
  have hsum := HasDerivAt.fun_sum fun k (_ : k ∈ Finset.univ) => hk k
  have h2 := h1.unique hsum
  rw [h2, Finset.sum_add_distrib, add_comm]
  rfl

/-- The derivative of the angle map through that of the torus map. -/
theorem IsPeriodChart.fderiv_angleMap (h : IsPeriodChart F x₀ M S e) {s : ι → ℝ}
    (hs : s ∈ S) (φ a α : ι → ℝ) :
    fderiv ℝ (angleMap F x₀ e) (s, φ) (a, α) =
      fderiv ℝ (torusMap F x₀) (s, angleTime e s φ)
        (a, angleTime e s α + ∑ k, (φ k / (2 * π)) • fderiv ℝ (e k) s a) := by
  have hT := ((h.contDiffAt_angleTime hs φ).differentiableAt (by simp)).hasFDerivAt
  have hΦ := ((h.contDiffAt_torusMap hs (angleTime e s φ)).differentiableAt
    (by simp)).hasFDerivAt
  have hin : HasFDerivAt (fun p : (ι → ℝ) × (ι → ℝ) => (p.1, angleTime e p.1 p.2))
      ((ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).prod
        (fderiv ℝ (fun p : (ι → ℝ) × (ι → ℝ) => angleTime e p.1 p.2) (s, φ))) (s, φ) :=
    hasFDerivAt_fst.prodMk hT
  have hc := HasFDerivAt.comp (s, φ) (g := torusMap F x₀)
    (f := fun p : (ι → ℝ) × (ι → ℝ) => (p.1, angleTime e p.1 p.2)) hΦ hin
  have e1 : angleMap F x₀ e =
      torusMap F x₀ ∘ fun p : (ι → ℝ) × (ι → ℝ) => (p.1, angleTime e p.1 p.2) := rfl
  rw [e1, hc.fderiv, ← h.fderiv_angleTime hs φ a α]
  rfl

/-- The symplectic form in the co-ordinates `(s, φ)`: the angles are conjugate
to the forms `actionForm`. -/
theorem IsPeriodChart.symplecticForm_angleMap (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {s : ι → ℝ} (hs : s ∈ S)
    (φ a α a' α' : ι → ℝ) :
    symplecticForm ι (fderiv ℝ (angleMap F x₀ e) (s, φ) (a, α))
        (fderiv ℝ (angleMap F x₀ e) (s, φ) (a', α')) =
      ∑ k, (α k * actionForm F x₀ e s a' k - α' k * actionForm F x₀ e s a k) := by
  rw [h.fderiv_angleMap hs, h.fderiv_angleMap hs, h.symplecticForm_torusMap hF hs]
  have hterm : ∀ i, (∑ k, (φ k / (2 * π)) • fderiv ℝ (e k) s a) i * sectionDeriv F x₀ s a' i -
      (∑ k, (φ k / (2 * π)) • fderiv ℝ (e k) s a') i * sectionDeriv F x₀ s a i =
      ∑ k, φ k / (2 * π) * (fderiv ℝ (e k) s a i * sectionDeriv F x₀ s a' i -
        fderiv ℝ (e k) s a' i * sectionDeriv F x₀ s a i) := by
    intro i
    rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_mul, Finset.sum_mul,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hsym : ∑ i, ((∑ k, (φ k / (2 * π)) • fderiv ℝ (e k) s a) i * sectionDeriv F x₀ s a' i -
      (∑ k, (φ k / (2 * π)) • fderiv ℝ (e k) s a') i * sectionDeriv F x₀ s a i) = 0 := by
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← Finset.mul_sum, h.sum_fderiv_period_symm hF k hs, mul_zero]
  have hsplit : ∀ T T' P P' D D' : ι → ℝ, ∑ i, ((T + P) i * D' i - (T' + P') i * D i) =
      ∑ i, (T i * D' i - T' i * D i) + ∑ i, (P i * D' i - P' i * D i) := by
    intro T T' P P' D D'
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [Pi.add_apply]
      ring
  rw [hsplit, hsym, add_zero, Finset.sum_sub_distrib, sum_angleTime_mul, sum_angleTime_mul,
    ← Finset.sum_sub_distrib]
  rfl

end Chart

end ProjectAinos.Mechanics
