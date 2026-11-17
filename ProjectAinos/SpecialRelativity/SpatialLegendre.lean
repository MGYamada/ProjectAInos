/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialRelativity.Hamiltonian
public import ProjectAinos.SpecialRelativity.FreeMotion
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The Lagrangian of a free particle in the time of an observer, and its Legendre transformation

In the time of an inertial observer the Lagrangian of a free particle of mass `m` is
`FreeParticle.lagrangian d m = −m √(1 − Σ vᵢ²)`, a function on the ball `Σ vᵢ² < 1` of
velocities (Landau–Lifshitz, *The Classical Theory of Fields*, §§8–9). The units have `c = 1`.

**The Legendre transformation.** `legendre m v = m γ v` with `γ = 1/√(1 − Σ vᵢ²)` is the
momentum of the velocity `v`, and `velocityOfMomentum m p = p/√(m² + Σ pᵢ²)` is the velocity
of the momentum `p`. For `m > 0` they are inverse bijections between the ball and all momenta
(`velocityOfMomentum_legendre`, `legendre_velocityOfMomentum`), and the energy is
`Σ pᵢ vᵢ − L = √(m² + Σ pᵢ²)` (`energy_eq_relEnergy`).

**Lagrange's equations.** `hasFDerivAt_lagrangian` gives the momentum covector, and for a `C²`
curve with speed less than one on `[a, b]`, `a < b` and `m > 0`:
`stationary_iff_deriv_const` shows that the action is stationary if and only if the velocity
is constant on `[a, b]`.

**Hamilton's equations.** `isTrajectory_iff_legendre`: a curve in the phase space is a
trajectory of the Hamiltonian `√(m² + Σ pᵢ²)` if and only if, at every time, its speed is less
than one, its momentum is the Legendre transform of its velocity, and the momentum has zero
derivative.

**The action of space-time.** In three space dimensions the graph `t ↦ (t, x(t))` of a curve
has `freeLagrangian m` equal to this Lagrangian (`freeLagrangian_graph`), and
`free_stationary_graph_iff` shows that the action of space-time is stationary on the graph if
and only if the action in the time of the observer is stationary on the curve.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Topology
open scoped ContDiff

namespace ProjectAinos.SpecialRelativity.FreeParticle

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace Mechanics
open SmoothGeometry SmoothGeometry.Minkowski

variable {d : ℕ} {m : ℝ}

/-! ### The Legendre transformation on the ball of velocities -/

/-- The factor `γ = 1/√(1 − Σ vᵢ²)`. -/
def gamma (v : Fin d → ℝ) : ℝ := (Real.sqrt (1 - ∑ i, v i ^ 2))⁻¹

/-- The momentum `m γ v` of the velocity `v`. -/
def legendre (m : ℝ) (v : Fin d → ℝ) : Fin d → ℝ := fun i => m * gamma v * v i

/-- The velocity `p/√(m² + Σ pᵢ²)` of the momentum `p`. -/
def velocityOfMomentum (m : ℝ) (p : Fin d → ℝ) : Fin d → ℝ := fun i => relEnergyInv m p * p i

theorem sqrt_one_sub_pos {v : Fin d → ℝ} (hv : ∑ i, v i ^ 2 < 1) :
    0 < Real.sqrt (1 - ∑ i, v i ^ 2) :=
  Real.sqrt_pos.mpr (by linarith)

theorem gamma_pos {v : Fin d → ℝ} (hv : ∑ i, v i ^ 2 < 1) : 0 < gamma v :=
  inv_pos.mpr (sqrt_one_sub_pos hv)

/-- `γ² (1 − Σ vᵢ²) = 1`. -/
theorem gamma_sq_mul {v : Fin d → ℝ} (hv : ∑ i, v i ^ 2 < 1) :
    gamma v ^ 2 * (1 - ∑ i, v i ^ 2) = 1 := by
  have h : Real.sqrt (1 - ∑ i, v i ^ 2) ^ 2 = 1 - ∑ i, v i ^ 2 := Real.sq_sqrt (by linarith)
  rw [gamma, inv_pow, h, inv_mul_cancel₀ (by linarith)]

/-- The velocity of a momentum is inside the ball. -/
theorem sum_sq_velocityOfMomentum_lt_one (hm : m ≠ 0) (p : Fin d → ℝ) :
    ∑ i, velocityOfMomentum m p i ^ 2 < 1 :=
  sum_sq_relEnergyInv_mul_lt_one hm p

/-- The energy of the momentum of a velocity is `m γ`. -/
theorem relEnergy_legendre (hm : 0 < m) {v : Fin d → ℝ} (hv : ∑ i, v i ^ 2 < 1) :
    relEnergy m (legendre m v) = m * gamma v := by
  have hg := gamma_sq_mul hv
  have hgp := gamma_pos hv
  rw [relEnergy_real hm]
  have hsum : ∑ i, legendre m v i ^ 2 = (m * gamma v) ^ 2 * ∑ i, v i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [legendre, mul_pow]
  have hsq : m ^ 2 + ∑ i, legendre m v i ^ 2 = (m * gamma v) ^ 2 := by
    rw [hsum]
    linear_combination (-m ^ 2) * hg
  rw [hsq, Real.sqrt_sq (mul_pos hm hgp).le]

/-- The velocity of the momentum of a velocity is that velocity. -/
theorem velocityOfMomentum_legendre (hm : 0 < m) {v : Fin d → ℝ} (hv : ∑ i, v i ^ 2 < 1) :
    velocityOfMomentum m (legendre m v) = v := by
  funext i
  have hgp := gamma_pos hv
  rw [velocityOfMomentum, relEnergyInv_real hm.ne', relEnergy_legendre hm hv, legendre]
  field_simp

/-- The factor `γ` of the velocity of a momentum is `E/m`. -/
theorem gamma_velocityOfMomentum (hm : 0 < m) (p : Fin d → ℝ) :
    gamma (velocityOfMomentum m p) = relEnergy m p * m⁻¹ := by
  have hE := relEnergy_real_pos hm p
  have hinv := relEnergyInv_real hm.ne' p
  have hsq : ∑ i, p i ^ 2 = relEnergy m p ^ 2 - m ^ 2 := by
    have h : relEnergy m p * relEnergy m p = m ^ 2 + ∑ i, p i * p i :=
      relEnergy_mul_self hm.ne' p
    simp only [pow_two]
    linarith
  have hsum : ∑ i, velocityOfMomentum m p i ^ 2 = (relEnergy m p)⁻¹ ^ 2 * ∑ i, p i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [velocityOfMomentum, hinv, mul_pow]
  have hone : 1 - ∑ i, velocityOfMomentum m p i ^ 2 = (m * (relEnergy m p)⁻¹) ^ 2 := by
    rw [hsum, hsq]
    field_simp
    ring
  rw [gamma, hone, Real.sqrt_sq (mul_pos hm (inv_pos.mpr hE)).le, mul_inv, inv_inv, mul_comm]

/-- The momentum of the velocity of a momentum is that momentum. -/
theorem legendre_velocityOfMomentum (hm : 0 < m) (p : Fin d → ℝ) :
    legendre m (velocityOfMomentum m p) = p := by
  funext i
  have hE := relEnergy_real_pos hm p
  rw [legendre, gamma_velocityOfMomentum hm, velocityOfMomentum, relEnergyInv_real hm.ne']
  field_simp

/-- The momentum determines the velocity on the ball. -/
theorem legendre_eq_iff (hm : 0 < m) {v w : Fin d → ℝ} (hv : ∑ i, v i ^ 2 < 1)
    (hw : ∑ i, w i ^ 2 < 1) : legendre m v = legendre m w ↔ v = w := by
  constructor
  · intro h
    rw [← velocityOfMomentum_legendre hm hv, h, velocityOfMomentum_legendre hm hw]
  · intro h
    rw [h]

/-- The energy `Σ pᵢ vᵢ − L` of a velocity is `√(m² + Σ pᵢ²)` of its momentum. -/
theorem energy_eq_relEnergy (hm : 0 < m) {v : Fin d → ℝ} (hv : ∑ i, v i ^ 2 < 1) :
    ∑ i, legendre m v i * v i - -m * Real.sqrt (1 - ∑ i, v i ^ 2) =
      relEnergy m (legendre m v) := by
  have hs := sqrt_one_sub_pos hv
  have hs2 : Real.sqrt (1 - ∑ i, v i ^ 2) ^ 2 = 1 - ∑ i, v i ^ 2 := Real.sq_sqrt (by linarith)
  have hsum : ∑ i, legendre m v i * v i = m * gamma v * ∑ i, v i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [legendre]; ring
  rw [relEnergy_legendre hm hv, hsum, gamma]
  field_simp
  linarith

/-! ### The Lagrangian and its momentum -/

/-- The covector `w ↦ Σ aᵢ wᵢ`. -/
def dotCovector (a : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ i, a i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i

theorem dotCovector_apply (a w : Fin d → ℝ) : dotCovector a w = ∑ i, a i * w i := by
  simp only [dotCovector, _root_.sum_apply, smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]

theorem dotCovector_smul (r : ℝ) (a : Fin d → ℝ) : dotCovector (r • a) = r • dotCovector a := by
  ext w
  simp only [dotCovector_apply, Pi.smul_apply, smul_eq_mul, smul_apply, Finset.mul_sum,
    mul_assoc]

theorem dotCovector_injective : Function.Injective (dotCovector (d := d)) := by
  intro a b h
  funext i
  have hi := congrArg (fun L : (Fin d → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) h
  simpa [dotCovector_apply, Pi.single_apply] using hi

/-- The Lagrangian `−m √(1 − Σ vᵢ²)` in the time of an inertial observer. -/
def lagrangian (d : ℕ) (m : ℝ) : Lagrangian (Fin d → ℝ) :=
  fun _ z => -m * Real.sqrt (1 - ∑ i, z.2 i ^ 2)

/-- The jets of the curves with speed less than one. -/
def subluminalJets (d : ℕ) : Set (ℝ × ((Fin d → ℝ) × (Fin d → ℝ))) :=
  {z | ∑ i, z.2.2 i ^ 2 < 1}

theorem contDiff_sum_sq {n : ℕ∞ω} : ContDiff ℝ n fun v : Fin d → ℝ => ∑ i, v i ^ 2 :=
  ContDiff.sum fun i _ => (contDiff_apply ℝ (fun _ : Fin d => ℝ) i).pow 2

theorem isOpen_ball : IsOpen {v : Fin d → ℝ | ∑ i, v i ^ 2 < 1} :=
  isOpen_lt (contDiff_sum_sq (n := 0)).continuous continuous_const

theorem isOpen_subluminalJets : IsOpen (subluminalJets d) :=
  isOpen_lt ((contDiff_sum_sq (n := 0)).continuous.comp (continuous_snd.comp continuous_snd))
    continuous_const

theorem lagrangian_contDiffOn (m : ℝ) :
    ContDiffOn ℝ 2 (Function.uncurry (lagrangian d m)) (subluminalJets d) := by
  intro z hz
  have hne : 1 - ∑ i, z.2.2 i ^ 2 ≠ 0 := by
    have h : ∑ i, z.2.2 i ^ 2 < 1 := hz
    linarith
  have hsum : ContDiffAt ℝ 2 (fun z : ℝ × ((Fin d → ℝ) × (Fin d → ℝ)) =>
      1 - ∑ i, z.2.2 i ^ 2) z :=
    contDiffAt_const.sub ((contDiff_sum_sq.comp (contDiff_snd.comp contDiff_snd)).contDiffAt)
  exact (contDiffAt_const.mul (hsum.sqrt hne)).contDiffWithinAt

/-- The derivative of `√(1 − Σ vᵢ²)` is `−γ Σ vᵢ dvᵢ`. -/
theorem hasFDerivAt_sqrt_one_sub {v : Fin d → ℝ} (hv : ∑ i, v i ^ 2 < 1) :
    HasFDerivAt (fun w : Fin d → ℝ => Real.sqrt (1 - ∑ i, w i ^ 2))
      (-gamma v • dotCovector v) v := by
  have hj (j : Fin d) : HasFDerivAt (fun w : Fin d → ℝ => w j ^ 2)
      ((2 * v j) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j)) v := by
    simpa using ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j).hasFDerivAt
      (x := v)).pow 2
  have hg : HasFDerivAt (fun w : Fin d → ℝ => 1 - ∑ j, w j ^ 2)
      (-∑ j, (2 * v j) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j)) v :=
    (HasFDerivAt.fun_sum fun j _ => hj j).const_sub 1
  have hs := hg.sqrt (by linarith : (1 - ∑ i, v i ^ 2) ≠ 0)
  have hpos := sqrt_one_sub_pos hv
  refine hs.congr_fderiv ?_
  ext w
  simp only [smul_apply, neg_apply, _root_.sum_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, dotCovector_apply, gamma, Finset.mul_sum]
  rw [← Finset.sum_neg_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

/-- The derivative of the Lagrangian: the momentum covector is `Σ (m γ vᵢ) dvᵢ`. -/
theorem hasFDerivAt_lagrangian (m : ℝ) {z : (Fin d → ℝ) × (Fin d → ℝ)}
    (hz : ∑ i, z.2 i ^ 2 < 1) (t : ℝ) :
    HasFDerivAt (lagrangian d m t)
      ((dotCovector (legendre m z.2)).comp
        (ContinuousLinearMap.snd ℝ (Fin d → ℝ) (Fin d → ℝ))) z := by
  have h := ((hasFDerivAt_sqrt_one_sub hz).comp z hasFDerivAt_snd).const_mul (-m)
  have he : (dotCovector (legendre m z.2)).comp
      (ContinuousLinearMap.snd ℝ (Fin d → ℝ) (Fin d → ℝ)) =
      -m • ((-gamma z.2 • dotCovector z.2).comp
        (ContinuousLinearMap.snd ℝ (Fin d → ℝ) (Fin d → ℝ))) := by
    have hl : legendre m z.2 = (m * gamma z.2) • z.2 := rfl
    rw [hl, dotCovector_smul, ContinuousLinearMap.smul_comp, ContinuousLinearMap.smul_comp,
      smul_smul]
    congr 1
    ring
  rw [he]
  exact h

theorem force_lagrangian (m : ℝ) {x : ℝ → Fin d → ℝ} {t : ℝ}
    (hv : ∑ i, deriv x t i ^ 2 < 1) : force (lagrangian d m) x t = 0 := by
  rw [force, (hasFDerivAt_lagrangian m (z := (x t, deriv x t)) hv t).fderiv]
  ext w
  simp

/-- The momentum of the Lagrangian along a curve is `m γ ẋ`. -/
theorem momentum_lagrangian (m : ℝ) {x : ℝ → Fin d → ℝ} {t : ℝ}
    (hv : ∑ i, deriv x t i ^ 2 < 1) :
    momentum (lagrangian d m) x t = dotCovector (legendre m (deriv x t)) := by
  rw [momentum, (hasFDerivAt_lagrangian m (z := (x t, deriv x t)) hv t).fderiv]
  ext w
  simp

/-! ### Lagrange's equations -/

variable {x : ℝ → Fin d → ℝ} {a b : ℝ}

/-- A speed less than one stays less than one near the time `t`. -/
theorem eventually_subluminal (hx : ContDiff ℝ 2 x) {t : ℝ} (hv : ∑ i, deriv x t i ^ 2 < 1) :
    ∀ᶠ s in 𝓝 t, ∑ i, deriv x s i ^ 2 < 1 :=
  (hx.continuous_deriv (by norm_num)).continuousAt.eventually (isOpen_ball.mem_nhds hv)

theorem differentiableAt_gamma {v : Fin d → ℝ} (hv : ∑ i, v i ^ 2 < 1) :
    DifferentiableAt ℝ (gamma (d := d)) v :=
  (hasFDerivAt_sqrt_one_sub hv).differentiableAt.inv (sqrt_one_sub_pos hv).ne'

theorem differentiableAt_legendre (m : ℝ) {v : Fin d → ℝ} (hv : ∑ i, v i ^ 2 < 1) :
    DifferentiableAt ℝ (legendre (d := d) m) v :=
  differentiableAt_pi.mpr fun i =>
    ((differentiableAt_const m).mul (differentiableAt_gamma hv)).mul
      (differentiableAt_apply i v)

theorem differentiableAt_dotCovector_legendre (m : ℝ) (hx : ContDiff ℝ 2 x) {t : ℝ}
    (hv : ∑ i, deriv x t i ^ 2 < 1) :
    DifferentiableAt ℝ (fun s => dotCovector (legendre m (deriv x s))) t := by
  have hl : DifferentiableAt ℝ (fun s => legendre m (deriv x s)) t :=
    (differentiableAt_legendre m hv).comp t (hx.differentiable_deriv_two t)
  unfold dotCovector
  exact DifferentiableAt.fun_sum fun i _ => ((differentiableAt_pi.mp hl) i).smul_const _

/-- Where the speed is less than one, the Euler–Lagrange covector is minus the derivative of
the momentum. -/
theorem eulerLagrange_lagrangian (m : ℝ) (hx : ContDiff ℝ 2 x) {t : ℝ}
    (hv : ∑ i, deriv x t i ^ 2 < 1) :
    eulerLagrange (lagrangian d m) x t =
      -deriv (fun s => dotCovector (legendre m (deriv x s))) t := by
  have h : momentum (lagrangian d m) x =ᶠ[𝓝 t] fun s => dotCovector (legendre m (deriv x s)) :=
    (eventually_subluminal hx hv).mono fun s hs => momentum_lagrangian m hs
  rw [eulerLagrange, force_lagrangian m hv, zero_sub, h.deriv_eq]

/-- The action is stationary if and only if the momentum has zero derivative. -/
theorem stationary_iff_deriv_legendre (m : ℝ) (hab : a < b) (hx : ContDiff ℝ 2 x)
    (hv : ∀ t ∈ Icc a b, ∑ i, deriv x t i ^ 2 < 1) :
    Stationary a b (lagrangian d m) x ↔
      ∀ t ∈ Ioo a b, deriv (fun s => dotCovector (legendre m (deriv x s))) t = 0 := by
  rw [stationary_iff_eulerLagrange_on hab hx isOpen_subluminalJets (lagrangian_contDiffOn m)
    fun t ht => hv t ht]
  refine forall₂_congr fun t ht => ?_
  rw [eulerLagrange_lagrangian m hx (hv t (Ioo_subset_Icc_self ht)), neg_eq_zero]

/-- The action is stationary if and only if the momentum is constant. -/
theorem stationary_iff_legendre_const (m : ℝ) (hab : a < b) (hx : ContDiff ℝ 2 x)
    (hv : ∀ t ∈ Icc a b, ∑ i, deriv x t i ^ 2 < 1) :
    Stationary a b (lagrangian d m) x ↔
      ∀ t ∈ Icc a b, legendre m (deriv x t) = legendre m (deriv x a) := by
  rw [stationary_iff_deriv_legendre m hab hx hv]
  constructor
  · intro h t ht
    refine dotCovector_injective (eq_of_hasDerivAt_zero_Ioo
      (f := fun s => dotCovector (legendre m (deriv x s)))
      (fun s hs => (differentiableAt_dotCovector_legendre m hx (hv s hs)).continuousAt
        |>.continuousWithinAt) (fun s hs => ?_) ht)
    have hd := (differentiableAt_dotCovector_legendre m hx
      (hv s (Ioo_subset_Icc_self hs))).hasDerivAt
    rwa [h s hs] at hd
  · intro h t ht
    have heq : (fun s => dotCovector (legendre m (deriv x s))) =ᶠ[𝓝 t]
        fun _ => dotCovector (legendre m (deriv x a)) :=
      Filter.eventuallyEq_of_mem (Icc_mem_nhds ht.1 ht.2) fun s hs =>
        congrArg dotCovector (h s hs)
    rw [heq.deriv_eq, deriv_const]

/-- For a positive mass the action is stationary if and only if the velocity is constant: the
motion is uniform and in a straight line. -/
theorem stationary_iff_deriv_const (hm : 0 < m) (hab : a < b) (hx : ContDiff ℝ 2 x)
    (hv : ∀ t ∈ Icc a b, ∑ i, deriv x t i ^ 2 < 1) :
    Stationary a b (lagrangian d m) x ↔ ∀ t ∈ Icc a b, deriv x t = deriv x a := by
  rw [stationary_iff_legendre_const m hab hx hv]
  exact forall₂_congr fun t ht =>
    legendre_eq_iff hm (hv t ht) (hv a (left_mem_Icc.mpr hab.le))

/-! ### Hamilton's equations -/

/-- A curve in the phase space is a trajectory of the Hamiltonian `√(m² + Σ pᵢ²)` if and only
if at every time its speed is less than one, its momentum is the Legendre transform of its
velocity, and the momentum has zero derivative. -/
theorem isTrajectory_iff_legendre (hm : 0 < m) (c : Fin d ⊕ Fin d → TimeFunction) :
    IsTrajectory (canonical (Fin d)) (hamiltonian d m) c ↔
      ∀ t : ℝ,
        (∑ i, deriv (fun s => realCurve c s (Sum.inl i)) t ^ 2 < 1) ∧
        (fun i => realCurve c t (Sum.inr i)) =
          legendre m (fun i => deriv (fun s => realCurve c s (Sum.inl i)) t) ∧
        ∀ i, deriv (fun s => realCurve c s (Sum.inr i)) t = 0 := by
  rw [isTrajectory_canonical_iff_hasDerivAt]
  have hq (t : ℝ) (i : Fin d) : HasDerivAt (fun s => realCurve c s (Sum.inl i))
      (deriv (fun s => realCurve c s (Sum.inl i)) t) t :=
    (hasDerivAt_pi.mp (hasDerivAt_realCurve c t) (Sum.inl i)).differentiableAt.hasDerivAt
  have hp (t : ℝ) (i : Fin d) : HasDerivAt (fun s => realCurve c s (Sum.inr i))
      (deriv (fun s => realCurve c s (Sum.inr i)) t) t :=
    (hasDerivAt_pi.mp (hasDerivAt_realCurve c t) (Sum.inr i)).differentiableAt.hasDerivAt
  constructor
  · intro h t
    have ht := hasDerivAt_pi.mp (h t)
    have hvel (i : Fin d) : deriv (fun s => realCurve c s (Sum.inl i)) t =
        velocityOfMomentum m (fun j => realCurve c t (Sum.inr j)) i := by
      have h1 := (ht (Sum.inl i)).deriv
      rw [hamiltonianField_inl hm.ne'] at h1
      exact h1
    have hveq : (fun i => deriv (fun s => realCurve c s (Sum.inl i)) t) =
        velocityOfMomentum m fun j => realCurve c t (Sum.inr j) := funext hvel
    refine ⟨?_, ?_, fun i => ?_⟩
    · rw [show (∑ i, deriv (fun s => realCurve c s (Sum.inl i)) t ^ 2) =
          ∑ i, velocityOfMomentum m (fun j => realCurve c t (Sum.inr j)) i ^ 2 from
        Finset.sum_congr rfl fun i _ => by rw [hvel i]]
      exact sum_sq_velocityOfMomentum_lt_one hm.ne' _
    · rw [hveq, legendre_velocityOfMomentum hm]
    · have h1 := (ht (Sum.inr i)).deriv
      rw [hamiltonianField_inr hm.ne'] at h1
      exact h1
  · intro h t
    obtain ⟨hlt, hleg, hzero⟩ := h t
    rw [hasDerivAt_pi]
    rintro (i | i)
    · rw [hamiltonianField_inl hm.ne']
      have hvel : velocityOfMomentum m (fun j => realCurve c t (Sum.inr j)) =
          fun i => deriv (fun s => realCurve c s (Sum.inl i)) t := by
        rw [hleg, velocityOfMomentum_legendre hm hlt]
      have hi := congrFun hvel i
      change relEnergyInv m (fun j => realCurve c t (Sum.inr j)) * realCurve c t (Sum.inr i) =
        deriv (fun s => realCurve c s (Sum.inl i)) t at hi
      rw [hi]
      exact hq t i
    · rw [hamiltonianField_inr hm.ne', ← hzero i]
      exact hp t i

/-! ### The action of space-time on a graph -/

/-- The quadratic form of the vector with the time `τ` and the space part `w`. -/
theorem intervalQuadratic_cons (τ : ℝ) (w : Fin d → ℝ) :
    intervalQuadratic (Fin.cons τ w : MinkowskiModel d) = τ ^ 2 - ∑ i, w i ^ 2 := by
  rw [intervalQuadratic_apply, pair, minkowskiForm_apply, Fin.sum_univ_succ]
  simp only [lorentzSign, LorentzConvention.timeSign_timePositive, Fin.cons_zero, Fin.cons_succ,
    Fin.succ_ne_zero, ↓reduceIte, one_mul, mul_neg, mul_one, neg_mul, Finset.sum_neg_distrib,
    pow_two]
  ring

/-- The graph `t ↦ (t, x(t))` in space-time of a curve in space. -/
def graph (x : ℝ → Fin 3 → ℝ) : ℝ → Spacetime := fun t => Fin.cons t (x t)

theorem hasDerivAt_graph {x : ℝ → Fin 3 → ℝ} {t : ℝ} (hx : DifferentiableAt ℝ x t) :
    HasDerivAt (graph x) (Fin.cons 1 (deriv x t)) t := by
  rw [hasDerivAt_pi]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hasDerivAt_id t
  · exact hasDerivAt_pi.mp hx.hasDerivAt j

theorem deriv_graph {x : ℝ → Fin 3 → ℝ} {t : ℝ} (hx : DifferentiableAt ℝ x t) :
    deriv (graph x) t = Fin.cons 1 (deriv x t) :=
  (hasDerivAt_graph hx).deriv

theorem contDiff_graph {x : ℝ → Fin 3 → ℝ} (hx : ContDiff ℝ 2 x) : ContDiff ℝ 2 (graph x) := by
  rw [contDiff_pi]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact contDiff_id
  · exact contDiff_pi.mp hx j

/-- The velocity of the graph is timelike if and only if the speed is less than one. -/
theorem timelike_cons_one (w : Fin 3 → ℝ) :
    Timelike (Fin.cons 1 w : Spacetime) ↔ ∑ i, w i ^ 2 < 1 := by
  rw [Timelike, intervalQuadratic_cons]
  constructor <;> intro h <;> linarith

theorem properSpeed_cons_one (w : Fin 3 → ℝ) :
    properSpeed (Fin.cons 1 w : Spacetime) = Real.sqrt (1 - ∑ i, w i ^ 2) := by
  rw [properSpeed, intervalQuadratic_cons, one_pow]

/-- On a graph the Lagrangian of space-time is the Lagrangian in the time of the observer. -/
theorem freeLagrangian_graph (m : ℝ) {x : ℝ → Fin 3 → ℝ} {t : ℝ}
    (hx : DifferentiableAt ℝ x t) :
    freeLagrangian m t (graph x t, deriv (graph x) t) = lagrangian 3 m t (x t, deriv x t) := by
  rw [freeLagrangian, deriv_graph hx, properSpeed_cons_one]
  rfl

/-- The unit four-velocity of a graph is `γ (1, v)`. -/
theorem fourVelocity_cons_one (w : Fin 3 → ℝ) :
    fourVelocity (Fin.cons 1 w : Spacetime) = gamma w • (Fin.cons 1 w : Spacetime) := by
  rw [fourVelocity, properSpeed_cons_one, gamma]

theorem fourVelocity_cons_one_eq_iff (v : Fin 3 → ℝ) {w : Fin 3 → ℝ}
    (hw : ∑ i, w i ^ 2 < 1) :
    fourVelocity (Fin.cons 1 v : Spacetime) = fourVelocity (Fin.cons 1 w : Spacetime) ↔
      v = w := by
  rw [fourVelocity_cons_one, fourVelocity_cons_one]
  constructor
  · intro h
    have h0 := congrFun h 0
    simp only [Pi.smul_apply, Fin.cons_zero, smul_eq_mul, mul_one] at h0
    funext i
    have hi := congrFun h i.succ
    simp only [Pi.smul_apply, Fin.cons_succ, smul_eq_mul] at hi
    rw [h0] at hi
    exact mul_left_cancel₀ (gamma_pos hw).ne' hi
  · intro h
    rw [h]

/-- The action of space-time is stationary on the graph of a curve if and only if the action
in the time of the observer is stationary on the curve. -/
theorem free_stationary_graph_iff (hm : 0 < m) (hab : a < b) {x : ℝ → Fin 3 → ℝ}
    (hx : ContDiff ℝ 2 x) (hv : ∀ t ∈ Icc a b, ∑ i, deriv x t i ^ 2 < 1) :
    Stationary a b (freeLagrangian m) (graph x) ↔ Stationary a b (lagrangian 3 m) x := by
  have hdiff (t : ℝ) : DifferentiableAt ℝ x t := hx.differentiable (by norm_num) t
  have htl : ∀ t ∈ Icc a b, Timelike (deriv (graph x) t) := fun t ht => by
    rw [deriv_graph (hdiff t)]
    exact (timelike_cons_one _).mpr (hv t ht)
  rw [free_stationary_iff_fourVelocity_const hm.ne' hab (contDiff_graph hx) htl,
    stationary_iff_deriv_const hm hab hx hv]
  refine forall₂_congr fun t ht => ?_
  rw [deriv_graph (hdiff t), deriv_graph (hdiff a)]
  exact fourVelocity_cons_one_eq_iff _ (hv a (left_mem_Icc.mpr hab.le))

end ProjectAinos.SpecialRelativity.FreeParticle
