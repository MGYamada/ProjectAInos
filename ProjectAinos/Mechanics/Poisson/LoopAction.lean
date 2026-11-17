/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Poisson.AngleMap

/-!
# The action variables as integrals over the cycles of the tori

For a chart of periods of integrals in involution (`IsPeriodChart`):

* `loopAction F x₀ e k (s, φ)` is `(1/2π) ∮ p dq` over the `k`-th cycle
  `r ↦ angleMap (s, φ + 2π r 1ₖ)` through the point with the angles `φ` of the
  torus over the point `s` of the transversal.
* `hasDerivAt_loopAction`: its derivative in a direction `(a, α)` is
  `actionForm s a k`. The variation of the integral of `p dq` is the integral
  of the symplectic form on the velocity of the cycle and the variation, the
  cycles are closed, and the angles are conjugate to the forms `actionForm`.
* `loopAction_eq`: the integral does not depend on the angles `φ`.
* `hasFDerivAt_actionMap`: the action variables `actionMap F x₀ e s` have the
  derivative `actionForm F x₀ e s`.
-/

@[expose] public section
noncomputable section

open Set Module Filter
open scoped ContDiff Topology Real

namespace ProjectAinos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing
open SmoothGeometry SmoothGeometry.NonlinearODE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The angles along the `k`-th cycle through the angles `φ`: `r ↦ φ + 2π r 1ₖ`. -/
def cycleAngle (k : ι) (φ : ι → ℝ) (r : ℝ) : ι → ℝ := φ + (2 * π * r) • Pi.single k (1 : ℝ)

omit [Fintype ι] in
theorem cycleAngle_zero (k : ι) (φ : ι → ℝ) : cycleAngle k φ 0 = φ := by
  simp [cycleAngle]

omit [Fintype ι] in
theorem cycleAngle_one (k : ι) (φ : ι → ℝ) :
    cycleAngle k φ 1 = fun j => φ j + 2 * π * ((Pi.single k (1 : ℤ) : ι → ℤ) j : ℝ) := by
  funext j
  by_cases hj : j = k
  · subst hj
    simp [cycleAngle]
  · simp [cycleAngle, Pi.single_eq_of_ne hj]

omit [Fintype ι] in
theorem cycleAngle_add (k : ι) (φ ψ : ι → ℝ) (r : ℝ) :
    cycleAngle k (φ + ψ) r = cycleAngle k φ r + ψ := by
  rw [cycleAngle, cycleAngle, add_right_comm]

omit [Fintype ι] in
theorem cycleAngle_eq_add (k : ι) (φ : ι → ℝ) (r t : ℝ) :
    cycleAngle k φ t = cycleAngle k φ r + (t - r) • ((2 * π) • Pi.single k (1 : ℝ)) := by
  rw [cycleAngle, cycleAngle, smul_smul, add_assoc, ← add_smul]
  congr 2
  ring

/-- `(1/2π) ∮ p dq` over the `k`-th cycle through the point with the angles
`p.2` of the torus over the point `p.1` of the transversal. -/
def loopAction (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (e : ι → (ι → ℝ) → ι → ℝ) (k : ι)
    (p : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  (2 * π)⁻¹ * ∫ r in (0 : ℝ)..1, liouvilleForm ι (angleMap F x₀ e (p.1, cycleAngle k p.2 r))
    (deriv (fun t => angleMap F x₀ e (p.1, cycleAngle k p.2 t)) r)

/-- The action variables on the transversal: the integrals over the cycles
through the points of the transversal. -/
def actionMap (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (e : ι → (ι → ℝ) → ι → ℝ)
    (s : ι → ℝ) : ι → ℝ :=
  fun k => loopAction F x₀ e k (s, 0)

omit [DecidableEq ι] in
theorem symplecticForm_eq_liouvilleForm_sub (u w : ι ⊕ ι → ℝ) :
    symplecticForm ι u w = liouvilleForm ι w u - liouvilleForm ι u w := rfl

section Chart

variable {F : ι → PhaseSpace ι} {x₀ : ι ⊕ ι → ℝ} {M : Set (ι ⊕ ι → ℝ)} {S : Set (ι → ℝ)}
  {e : ι → (ι → ℝ) → ι → ℝ}

/-- The family of the cycles through the points with the co-ordinates
`(s + ε a, φ + ε α)`, as a function of `(ε, r)`. -/
def cycleFamily (F : ι → PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (e : ι → (ι → ℝ) → ι → ℝ) (k : ι)
    (s a φ α : ι → ℝ) (p : ℝ × ℝ) : ι ⊕ ι → ℝ :=
  angleMap F x₀ e (s + p.1 • a, cycleAngle k (φ + p.1 • α) p.2)

theorem IsPeriodChart.contDiffAt_cycleFamily (h : IsPeriodChart F x₀ M S e) (k : ι)
    {s : ι → ℝ} (hs : s ∈ S) (a φ α : ι → ℝ) (r : ℝ) :
    ContDiffAt ℝ 2 (cycleFamily F x₀ e k s a φ α) (0, r) := by
  have hs0 : s + (0 : ℝ) • a ∈ S := by
    rw [zero_smul, add_zero]
    exact hs
  have h1 : ContDiff ℝ 2 (fun p : ℝ × ℝ => s + p.1 • a) :=
    contDiff_const.add (contDiff_fst.smul contDiff_const)
  have h2 : ContDiff ℝ 2 (fun p : ℝ × ℝ => cycleAngle k (φ + p.1 • α) p.2) :=
    (contDiff_const.add (contDiff_fst.smul contDiff_const)).add
      ((contDiff_const.mul contDiff_snd).smul contDiff_const)
  exact ContDiffAt.comp (0, r) (g := angleMap F x₀ e)
    (f := fun p : ℝ × ℝ => (s + p.1 • a, cycleAngle k (φ + p.1 • α) p.2))
    (h.contDiffAt_angleMap hs0 _) (h1.prodMk h2).contDiffAt

/-- The variation of the family of cycles. -/
theorem IsPeriodChart.fderiv_cycleFamily_parameter (h : IsPeriodChart F x₀ M S e) (k : ι)
    {s : ι → ℝ} (hs : s ∈ S) (a φ α : ι → ℝ) (r : ℝ) :
    fderiv ℝ (cycleFamily F x₀ e k s a φ α) (0, r) (1, 0) =
      fderiv ℝ (angleMap F x₀ e) (s, cycleAngle k φ r) (a, α) := by
  have hA := ((h.contDiffAt_angleMap hs (cycleAngle k φ r)).differentiableAt
    (by simp)).hasFDerivAt
  have h1 := hasDerivAt_family_parameter
    ((h.contDiffAt_cycleFamily k hs a φ α r).differentiableAt (by simp))
  have h2 : HasDerivAt
      (fun ε : ℝ => angleMap F x₀ e (s + ε • a, cycleAngle k φ r + ε • α))
      (fderiv ℝ (angleMap F x₀ e) (s, cycleAngle k φ r) (a, α)) 0 :=
    Variational.hasDerivAt_line hA (a, α)
  have e1 : (fun ε : ℝ => cycleFamily F x₀ e k s a φ α (ε, r)) =
      fun ε : ℝ => angleMap F x₀ e (s + ε • a, cycleAngle k φ r + ε • α) := by
    funext ε
    change angleMap F x₀ e (s + ε • a, cycleAngle k (φ + ε • α) r) = _
    rw [cycleAngle_add]
  rw [e1] at h1
  exact h1.unique h2

/-- The velocity of the cycles of the family. -/
theorem IsPeriodChart.fderiv_cycleFamily_time (h : IsPeriodChart F x₀ M S e) (k : ι)
    {s : ι → ℝ} (hs : s ∈ S) (a φ α : ι → ℝ) (r : ℝ) :
    fderiv ℝ (cycleFamily F x₀ e k s a φ α) (0, r) (0, 1) =
      fderiv ℝ (angleMap F x₀ e) (s, cycleAngle k φ r)
        (0, (2 * π) • Pi.single k (1 : ℝ)) := by
  have hA := ((h.contDiffAt_angleMap hs (cycleAngle k φ r)).differentiableAt
    (by simp)).hasFDerivAt
  have h1 := hasDerivAt_family_time
    ((h.contDiffAt_cycleFamily k hs a φ α r).differentiableAt (by simp))
  have h3 := Variational.hasDerivAt_line_sub hA
    ((0 : ι → ℝ), (2 * π) • Pi.single k (1 : ℝ)) r
  have e1 : (fun t : ℝ => cycleFamily F x₀ e k s a φ α (0, t)) =
      fun t : ℝ => angleMap F x₀ e ((s, cycleAngle k φ r) +
        (t - r) • ((0 : ι → ℝ), (2 * π) • Pi.single k (1 : ℝ))) := by
    funext t
    have e2 : ((s, cycleAngle k φ r) +
        (t - r) • ((0 : ι → ℝ), (2 * π) • Pi.single k (1 : ℝ)) : (ι → ℝ) × (ι → ℝ)) =
        (s + (0 : ℝ) • a, cycleAngle k (φ + (0 : ℝ) • α) t) := by
      rw [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero, zero_smul, zero_smul, add_zero,
        add_zero, ← cycleAngle_eq_add]
    rw [e2]
    rfl
  rw [e1] at h1
  exact h1.unique h3

/-- The symplectic form on the velocity of a cycle and a variation of it. -/
theorem IsPeriodChart.liouvilleForm_cycle_sub (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) (k : ι) {s : ι → ℝ}
    (hs : s ∈ S) (ψ a α : ι → ℝ) :
    liouvilleForm ι (fderiv ℝ (angleMap F x₀ e) (s, ψ) (a, α))
        (fderiv ℝ (angleMap F x₀ e) (s, ψ) (0, (2 * π) • Pi.single k (1 : ℝ))) -
      liouvilleForm ι (fderiv ℝ (angleMap F x₀ e) (s, ψ) (0, (2 * π) • Pi.single k (1 : ℝ)))
        (fderiv ℝ (angleMap F x₀ e) (s, ψ) (a, α)) =
      2 * π * actionForm F x₀ e s a k := by
  have hω := h.symplecticForm_angleMap hF hs ψ 0 ((2 * π) • Pi.single k (1 : ℝ)) a α
  rw [symplecticForm_eq_liouvilleForm_sub] at hω
  have hsum : ∑ j, (((2 * π) • Pi.single k (1 : ℝ) : ι → ℝ) j * actionForm F x₀ e s a j -
      α j * actionForm F x₀ e s 0 j) = 2 * π * actionForm F x₀ e s a k := by
    rw [Finset.sum_eq_single k]
    · rw [map_zero, Pi.zero_apply, mul_zero, sub_zero, Pi.smul_apply, Pi.single_eq_same,
        smul_eq_mul, mul_one]
    · intro j _ hj
      rw [map_zero, Pi.zero_apply, mul_zero, sub_zero, Pi.smul_apply,
        Pi.single_eq_of_ne hj, smul_zero, zero_mul]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  exact hω.trans hsum

/-- The cycles of the family are closed. -/
theorem IsPeriodChart.cycleFamily_one (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) (k : ι) {s a : ι → ℝ}
    (φ α : ι → ℝ) {ε : ℝ} (hε : s + ε • a ∈ S) :
    cycleFamily F x₀ e k s a φ α (ε, 1) = cycleFamily F x₀ e k s a φ α (ε, 0) := by
  change angleMap F x₀ e (s + ε • a, cycleAngle k (φ + ε • α) 1) =
    angleMap F x₀ e (s + ε • a, cycleAngle k (φ + ε • α) 0)
  rw [cycleAngle_one, cycleAngle_zero]
  exact h.angleMap_add_period hF hε _ _

/-- The derivative of the action integral over a cycle, in the point of the
transversal and the angles of the base point. -/
theorem IsPeriodChart.hasDerivAt_loopAction (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) (k : ι) {s : ι → ℝ}
    (hs : s ∈ S) (φ a α : ι → ℝ) :
    HasDerivAt (fun ε : ℝ => loopAction F x₀ e k (s + ε • a, φ + ε • α))
      (actionForm F x₀ e s a k) 0 := by
  have hπ : (2 * π) ≠ 0 := by positivity
  have hs0 : s + (0 : ℝ) • a ∈ S := by
    rw [zero_smul, add_zero]
    exact hs
  have hγ : ∀ r ∈ uIcc (0 : ℝ) 1, ContDiffAt ℝ 2 (cycleFamily F x₀ e k s a φ α) (0, r) :=
    fun r _ => h.contDiffAt_cycleFamily k hs a φ α r
  have hvar := hasDerivAt_lineIntegral (liouvilleForm ι) hγ
  refine (hvar.const_mul (2 * π)⁻¹).congr_deriv ?_
  have hη : fderiv ℝ (cycleFamily F x₀ e k s a φ α) (0, 1) (1, 0) =
      fderiv ℝ (cycleFamily F x₀ e k s a φ α) (0, 0) (1, 0) := by
    have h1 := (hasDerivAt_family_parameter
      ((hγ 1 right_mem_uIcc).differentiableAt (by simp))).deriv
    have h0 := (hasDerivAt_family_parameter
      ((hγ 0 left_mem_uIcc).differentiableAt (by simp))).deriv
    rw [← h1, ← h0]
    refine Filter.EventuallyEq.deriv_eq ?_
    have hcont : ContinuousAt (fun ε : ℝ => s + ε • a) 0 :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
    filter_upwards [hcont.preimage_mem_nhds (h.isOpen.mem_nhds hs0)] with ε hε
    exact h.cycleFamily_one hF k φ α hε
  have hb : liouvilleForm ι (cycleFamily F x₀ e k s a φ α (0, 1))
        (fderiv ℝ (cycleFamily F x₀ e k s a φ α) (0, 1) (1, 0)) -
      liouvilleForm ι (cycleFamily F x₀ e k s a φ α (0, 0))
        (fderiv ℝ (cycleFamily F x₀ e k s a φ α) (0, 0) (1, 0)) = 0 := by
    rw [h.cycleFamily_one hF k φ α hs0, hη]
    exact sub_self _
  have hI : ∫ r in (0 : ℝ)..1,
      (liouvilleForm ι (fderiv ℝ (cycleFamily F x₀ e k s a φ α) (0, r) (1, 0))
          (fderiv ℝ (cycleFamily F x₀ e k s a φ α) (0, r) (0, 1)) -
        liouvilleForm ι (fderiv ℝ (cycleFamily F x₀ e k s a φ α) (0, r) (0, 1))
          (fderiv ℝ (cycleFamily F x₀ e k s a φ α) (0, r) (1, 0))) =
      2 * π * actionForm F x₀ e s a k := by
    have hint : ∀ r ∈ uIcc (0 : ℝ) 1,
        liouvilleForm ι (fderiv ℝ (cycleFamily F x₀ e k s a φ α) (0, r) (1, 0))
            (fderiv ℝ (cycleFamily F x₀ e k s a φ α) (0, r) (0, 1)) -
          liouvilleForm ι (fderiv ℝ (cycleFamily F x₀ e k s a φ α) (0, r) (0, 1))
            (fderiv ℝ (cycleFamily F x₀ e k s a φ α) (0, r) (1, 0)) =
          2 * π * actionForm F x₀ e s a k := fun r _ => by
      rw [h.fderiv_cycleFamily_parameter k hs, h.fderiv_cycleFamily_time k hs]
      exact h.liouvilleForm_cycle_sub hF k hs _ a α
    rw [intervalIntegral.integral_congr (g := fun _ => 2 * π * actionForm F x₀ e s a k) hint,
      intervalIntegral.integral_const, sub_zero, one_smul]
  rw [hb, zero_add, hI]
  exact inv_mul_cancel_left₀ hπ _

/-- The action integral over a cycle does not depend on the angles of the
base point. -/
theorem IsPeriodChart.loopAction_eq (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) (k : ι) {s : ι → ℝ}
    (hs : s ∈ S) (φ : ι → ℝ) :
    loopAction F x₀ e k (s, φ) = loopAction F x₀ e k (s, 0) := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => loopAction F x₀ e k (s, t • φ)) 0 t := by
    intro t
    have h0 : HasDerivAt
        (fun ε : ℝ => loopAction F x₀ e k (s + ε • (0 : ι → ℝ), t • φ + ε • φ))
        (actionForm F x₀ e s 0 k) (t - t) := by
      rw [sub_self]
      exact h.hasDerivAt_loopAction hF k hs (t • φ) 0 φ
    have h1 := HasDerivAt.comp t
      (h₂ := fun ε : ℝ => loopAction F x₀ e k (s + ε • (0 : ι → ℝ), t • φ + ε • φ))
      (h := fun t' : ℝ => t' - t) h0 ((hasDerivAt_id t).sub_const t)
    rw [map_zero, Pi.zero_apply, zero_mul] at h1
    have e1 : ((fun ε : ℝ => loopAction F x₀ e k (s + ε • (0 : ι → ℝ), t • φ + ε • φ)) ∘
        fun t' : ℝ => t' - t) = fun t' : ℝ => loopAction F x₀ e k (s, t' • φ) := by
      funext t'
      change loopAction F x₀ e k (s + (t' - t) • (0 : ι → ℝ), t • φ + (t' - t) • φ) = _
      rw [smul_zero, add_zero, ← add_smul, add_sub_cancel]
    rwa [e1] at h1
  have hconst := is_const_of_deriv_eq_zero (fun t => (hderiv t).differentiableAt)
    (fun t => (hderiv t).deriv) 1 0
  simpa using hconst

theorem IsPeriodChart.continuousOn_actionForm (h : IsPeriodChart F x₀ M S e) :
    ContinuousOn (actionForm F x₀ e) S := by
  rw [continuousOn_clm_apply]
  intro a
  refine continuousOn_pi.mpr fun k => ?_
  change ContinuousOn (fun s => (2 * π)⁻¹ * ∑ i, e k s i * sectionDeriv F x₀ s a i) S
  refine continuousOn_const.mul (continuousOn_finsetSum _ fun i _ => ContinuousOn.mul ?_ ?_)
  · exact (continuous_apply i).comp_continuousOn fun s hs =>
      (h.contDiffAt k s hs).continuousAt.continuousWithinAt
  · exact ((continuous_apply i).comp
      ((continuous_sectionDeriv F x₀).clm_apply continuous_const)).continuousOn

/-- The forms `actionForm` are the differentials of the action variables. -/
theorem IsPeriodChart.hasFDerivAt_actionMap (h : IsPeriodChart F x₀ M S e)
    (hF : ∀ i j, (PhaseSpace.canonical ι).bracket (F i) (F j) = 0) {s : ι → ℝ} (hs : s ∈ S) :
    HasFDerivAt (actionMap F x₀ e) (actionForm F x₀ e s) s := by
  refine Variational.hasFDerivAt_of_hasDerivAt_line h.isOpen (fun s' hs' a => ?_)
    h.continuousOn_actionForm hs
  refine hasDerivAt_pi.mpr fun k => ?_
  have h1 := h.hasDerivAt_loopAction hF k hs' 0 a 0
  have e1 : (fun ε : ℝ => loopAction F x₀ e k (s' + ε • a, (0 : ι → ℝ) + ε • (0 : ι → ℝ))) =
      fun ε : ℝ => actionMap F x₀ e (s' + ε • a) k := by
    funext ε
    rw [smul_zero, add_zero]
    rfl
  rwa [e1] at h1

end Chart

end ProjectAinos.Mechanics
