/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Hamiltonian
public import ProjectAinos.Electrodynamics.LorentzForce
public import ProjectAinos.Electrodynamics.Components
public import ProjectAinos.SpecialRelativity.SpatialLegendre
public import ProjectAinos.SpecialRelativity.FreeMotion
public import ProjectAinos.SpecialRelativity.MassShellReduction
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# A charge in a static field: the action of space-time and Hamilton's equations

For static potentials `φ` and `a` on space, `staticPotential φ a` is the potential
`A = −φ dt + a · dx` of space-time (Landau–Lifshitz, *The Classical Theory of Fields*,
§§16–19).

* `fieldTensor_staticPotential`: its field has the electric part `Eᵢ = −∂ᵢφ` and the magnetic
  part `Fᵢⱼ = ∂ᵢaⱼ − ∂ⱼaᵢ`.
* `lorentzForce_staticPotential_succ`, `lorentzForce_staticPotential_zero`: on the velocity
  `(1, u)` the force has the space components `e (Eᵢ + Σⱼ Fᵢⱼ uⱼ)` and the time component
  `e Σᵢ Eᵢ uᵢ`, the power.
* `stationary_graph_iff_lorentzForce`: the action `−m ∫ ds + e ∫ A` is stationary on the graph
  `t ↦ (t, x(t))` of a curve with a speed less than one if and only if
  `d/dt (m γ ẋᵢ) = e (Eᵢ + Σⱼ Fᵢⱼ ẋⱼ)`. The time component of the equation of space-time
  follows from the space components, because the force and the acceleration are orthogonal to
  the velocity.
* `stationary_graph_iff_hamilton`: equivalently, the curve `(x, m γ ẋ + e a(x))` in the phase
  space solves Hamilton's equations of `ChargedParticle.hamiltonian m e φ a`.
* `stationary_graph_of_isTrajectory`: the graph of the positions of a trajectory of the
  Hamiltonian is stationary on every interval.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics.ChargedParticle

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace Mechanics
open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity SpecialRelativity.FreeParticle

variable {m e : ℝ} (φ : FreeSmoothRing (Fin 3)) (a : Fin 3 → FreeSmoothRing (Fin 3))

/-! ### The potential of space-time -/

/-- The space co-ordinates of an event. -/
def spaceCoordinates : Spacetime →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ

@[simp] theorem spaceCoordinates_apply (x : Spacetime) (i : Fin 3) :
    spaceCoordinates x i = x i.succ := rfl

@[simp] theorem spaceCoordinates_cons (τ : ℝ) (w : Fin 3 → ℝ) :
    spaceCoordinates (Fin.cons τ w : Spacetime) = w := rfl

/-- The potential `A = −φ dt + a · dx` of space-time of static potentials. -/
def staticPotential : Potential :=
  potentialOf (fun x => φ.val (spaceCoordinates x)) fun x i => (a i).val (spaceCoordinates x)

theorem staticPotential_apply (x w : Spacetime) :
    oneCovector (staticPotential φ a x) w =
      -φ.val (spaceCoordinates x) * w 0 + ∑ i, (a i).val (spaceCoordinates x) * w i.succ :=
  potentialOf_apply _ _ x w

theorem contDiff_staticPotential : ContDiff ℝ ∞ (staticPotential φ a) := by
  have hφ : ContDiff ℝ ∞ fun x : Spacetime => φ.val (spaceCoordinates x) :=
    (contDiff_val φ).comp spaceCoordinates.contDiff
  have ha (i : Fin 3) : ContDiff ℝ ∞ fun x : Spacetime => (a i).val (spaceCoordinates x) :=
    (contDiff_val (a i)).comp spaceCoordinates.contDiff
  unfold staticPotential potentialOf
  exact oneCovector.symm.contDiff.comp
    ((hφ.neg.smul contDiff_const).add (ContDiff.sum fun i _ => (ha i).smul contDiff_const))

/-- The derivative of a function of the position along a vector of space-time. -/
def spaceDerivative (f : FreeSmoothRing (Fin 3)) (x v : Spacetime) : ℝ :=
  ∑ j, (partialDerivation j f).val (spaceCoordinates x) * v j.succ

theorem hasFDerivAt_val_spaceCoordinates (f : FreeSmoothRing (Fin 3)) (x : Spacetime) :
    HasFDerivAt (fun y : Spacetime => f.val (spaceCoordinates y))
      ((fderiv ℝ (f.val : (Fin 3 → ℝ) → ℝ) (spaceCoordinates x)).comp spaceCoordinates) x :=
  (((contDiff_val f).differentiable (by simp) _).hasFDerivAt).comp x
    spaceCoordinates.hasFDerivAt

theorem comp_spaceCoordinates_apply (f : FreeSmoothRing (Fin 3)) (x v : Spacetime) :
    ((fderiv ℝ (f.val : (Fin 3 → ℝ) → ℝ) (spaceCoordinates x)).comp spaceCoordinates) v =
      spaceDerivative f x v := by
  rw [ContinuousLinearMap.comp_apply, fderiv_val_apply]
  rfl

/-- The pairing of the derivative of a potential with a vector is the derivative of the
pairing. -/
theorem oneCovector_fderiv_apply {A : Potential} {x : Spacetime} (hA : DifferentiableAt ℝ A x)
    (v w : Spacetime) :
    oneCovector (fderiv ℝ A x v) w = fderiv ℝ (fun y => oneCovector (A y) w) x v := by
  let ev : OneForm →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ w).comp oneCovector.toContinuousLinearMap
  have hd : HasFDerivAt (fun y => oneCovector (A y) w) (ev.comp (fderiv ℝ A x)) x :=
    ev.hasFDerivAt.comp x hA.hasFDerivAt
  rw [hd.fderiv]
  rfl

/-- The derivative of the static potential. -/
theorem fderiv_staticPotential_apply (x v w : Spacetime) :
    oneCovector (fderiv ℝ (staticPotential φ a) x v) w =
      -(w 0 * spaceDerivative φ x v) + ∑ i, w i.succ * spaceDerivative (a i) x v := by
  rw [oneCovector_fderiv_apply ((contDiff_staticPotential φ a).differentiable (by simp) x)]
  have hfun : (fun y => oneCovector (staticPotential φ a y) w) = fun y =>
      -φ.val (spaceCoordinates y) * w 0 + ∑ i, (a i).val (spaceCoordinates y) * w i.succ :=
    funext fun y => staticPotential_apply φ a y w
  have hd : HasFDerivAt (fun y : Spacetime =>
      -φ.val (spaceCoordinates y) * w 0 + ∑ i, (a i).val (spaceCoordinates y) * w i.succ)
      (w 0 • -((fderiv ℝ (φ.val : (Fin 3 → ℝ) → ℝ) (spaceCoordinates x)).comp
          spaceCoordinates) +
        ∑ i, w i.succ • ((fderiv ℝ ((a i).val : (Fin 3 → ℝ) → ℝ) (spaceCoordinates x)).comp
          spaceCoordinates)) x :=
    ((hasFDerivAt_val_spaceCoordinates φ x).neg.mul_const (w 0)).add
      (HasFDerivAt.fun_sum fun i _ => (hasFDerivAt_val_spaceCoordinates (a i) x).mul_const _)
  rw [hfun, hd.fderiv]
  simp only [add_apply, smul_apply, neg_apply, _root_.sum_apply, comp_spaceCoordinates_apply,
    smul_eq_mul, mul_neg]

/-- The field of static potentials: the electric part `Eᵢ = −∂ᵢφ` and the magnetic part
`Fᵢⱼ = ∂ᵢaⱼ − ∂ⱼaᵢ`. -/
theorem fieldTensor_staticPotential (x v w : Spacetime) :
    fieldTensor (staticPotential φ a) x ![v, w] =
      v 0 * spaceDerivative φ x w - w 0 * spaceDerivative φ x v +
        ∑ i, (w i.succ * spaceDerivative (a i) x v - v i.succ * spaceDerivative (a i) x w) := by
  rw [fieldTensor_apply, fderiv_staticPotential_apply, fderiv_staticPotential_apply,
    Finset.sum_sub_distrib]
  ring

/-! ### The force on a graph -/

theorem spaceDerivative_single_succ (f : FreeSmoothRing (Fin 3)) (x : Spacetime) (k : Fin 3) :
    spaceDerivative f x (Pi.single k.succ 1) =
      (partialDerivation k f).val (spaceCoordinates x) := by
  rw [spaceDerivative, Finset.sum_eq_single k]
  · rw [Pi.single_eq_same, mul_one]
  · intro j _ hj
    rw [Pi.single_eq_of_ne (fun h => hj (Fin.succ_injective _ h)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem spaceDerivative_single_zero (f : FreeSmoothRing (Fin 3)) (x : Spacetime) :
    spaceDerivative f x (Pi.single 0 1) = 0 := by
  rw [spaceDerivative]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Pi.single_eq_of_ne (Fin.succ_ne_zero j), mul_zero]

theorem spaceDerivative_cons (f : FreeSmoothRing (Fin 3)) (x : Spacetime) (τ : ℝ)
    (u : Fin 3 → ℝ) :
    spaceDerivative f x (Fin.cons τ u) =
      ∑ j, (partialDerivation j f).val (spaceCoordinates x) * u j := rfl

/-- A space component of the force is minus the charge times the field on the velocity and
the axis. -/
theorem lorentzForce_succ (e : ℝ) (F : TwoForm) (v : Spacetime) (k : Fin 3) :
    lorentzForce e F v k.succ = -e * F ![v, Pi.single k.succ 1] := by
  rw [← lorentzForce_lowered, minkowskiForm_apply, Finset.sum_eq_single k.succ]
  · rw [Pi.single_eq_same, mul_one, MassShell.lorentzSign_timeNegative_succ, one_mul]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, mul_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The time component of the force is the charge times the field on the velocity and the
axis of the time. -/
theorem lorentzForce_zero (e : ℝ) (F : TwoForm) (v : Spacetime) :
    lorentzForce e F v 0 = e * F ![v, Pi.single 0 1] := by
  have h := lorentzForce_lowered e F v (Pi.single 0 1)
  rw [minkowskiForm_apply, Finset.sum_eq_single 0] at h
  · rw [Pi.single_eq_same, mul_one, MassShell.lorentzSign_timeNegative_zero] at h
    linarith
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, mul_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem val_electricField (k : Fin 3) (y : Fin 3 → ℝ) :
    (electricField φ k).val y = -(partialDerivation k φ).val y := by
  rw [← lift_real, electricField, SmoothRingHom.map_neg, lift_real]

theorem val_magneticTensor (k j : Fin 3) (y : Fin 3 → ℝ) :
    (magneticTensor a k j).val y =
      (partialDerivation k (a j)).val y - (partialDerivation j (a k)).val y := by
  rw [← lift_real, magneticTensor, SmoothRingHom.map_sub, lift_real, lift_real]

/-- On the velocity `(1, u)` the space components of the force are `e (Eᵢ + Σⱼ Fᵢⱼ uⱼ)`. -/
theorem lorentzForce_staticPotential_succ (e : ℝ) (x : Spacetime) (u : Fin 3 → ℝ) (k : Fin 3) :
    lorentzForce e (fieldTensor (staticPotential φ a) x) (Fin.cons 1 u) k.succ =
      e * ((electricField φ k).val (spaceCoordinates x) +
        ∑ j, (magneticTensor a k j).val (spaceCoordinates x) * u j) := by
  have hsum : ∑ i, ((Pi.single k.succ 1 : Spacetime) i.succ *
        spaceDerivative (a i) x (Fin.cons 1 u) -
      (Fin.cons 1 u : Spacetime) i.succ * spaceDerivative (a i) x (Pi.single k.succ 1)) =
      -∑ j, (magneticTensor a k j).val (spaceCoordinates x) * u j := by
    rw [Finset.sum_sub_distrib, Finset.sum_eq_single k]
    · rw [Pi.single_eq_same, one_mul, spaceDerivative_cons, ← Finset.sum_sub_distrib,
        ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [spaceDerivative_single_succ, val_magneticTensor, Fin.cons_succ]
      ring
    · intro i _ hi
      rw [Pi.single_eq_of_ne (fun h => hi (Fin.succ_injective _ h)), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ k) h
  rw [lorentzForce_succ, fieldTensor_staticPotential, hsum, spaceDerivative_single_succ,
    val_electricField, Pi.single_eq_of_ne (Fin.succ_ne_zero k).symm, Fin.cons_zero]
  ring

/-- On the velocity `(1, u)` the time component of the force is the power `e Σᵢ Eᵢ uᵢ`. -/
theorem lorentzForce_staticPotential_zero (e : ℝ) (x : Spacetime) (u : Fin 3 → ℝ) :
    lorentzForce e (fieldTensor (staticPotential φ a) x) (Fin.cons 1 u) 0 =
      e * ∑ j, (electricField φ j).val (spaceCoordinates x) * u j := by
  have hsum : ∑ i, ((Pi.single 0 1 : Spacetime) i.succ *
        spaceDerivative (a i) x (Fin.cons 1 u) -
      (Fin.cons 1 u : Spacetime) i.succ * spaceDerivative (a i) x (Pi.single 0 1)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Pi.single_eq_of_ne (Fin.succ_ne_zero i), spaceDerivative_single_zero, zero_mul,
      mul_zero, sub_zero]
  have hE : ∑ j, (electricField φ j).val (spaceCoordinates x) * u j =
      -spaceDerivative φ x (Fin.cons 1 u) := by
    rw [spaceDerivative_cons, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [val_electricField]
    ring
  rw [lorentzForce_zero, fieldTensor_staticPotential, hsum, spaceDerivative_single_zero, hE,
    Pi.single_eq_same]
  ring

/-! ### The action on a graph -/

/-- A vector that is orthogonal to `(1, u)` has the time component `Σ wᵢ uᵢ`. -/
theorem time_eq_of_minkowskiForm_cons_eq_zero {w : Spacetime} {u : Fin 3 → ℝ}
    (h : minkowskiForm .timeNegative 3 w (Fin.cons 1 u) = 0) : w 0 = ∑ k, w k.succ * u k := by
  rw [minkowskiForm_apply, Fin.sum_univ_succ] at h
  simp only [MassShell.lorentzSign_timeNegative_zero, MassShell.lorentzSign_timeNegative_succ,
    Fin.cons_zero, Fin.cons_succ, one_mul, mul_one] at h
  linarith

variable {x : ℝ → Fin 3 → ℝ} {t₀ t₁ : ℝ}

/-- The mass times the unit four-velocity of a graph has the Legendre transform of the
velocity as its space part. -/
theorem mul_fourVelocity_graph_succ (m : ℝ) (hx : Differentiable ℝ x) (s : ℝ) (k : Fin 3) :
    m * fourVelocity (deriv (graph x) s) k.succ = legendre m (deriv x s) k := by
  rw [deriv_graph (hx s), fourVelocity_cons_one, Pi.smul_apply, Fin.cons_succ, smul_eq_mul,
    legendre]
  ring

/-- The action of space-time of a charge in a static field is stationary on the graph of a
curve if and only if the curve satisfies the equation of the Lorentz force
`d/dt (m γ ẋᵢ) = e (Eᵢ + Σⱼ Fᵢⱼ ẋⱼ)`. -/
theorem stationary_graph_iff_lorentzForce (m e : ℝ) (h01 : t₀ < t₁) (hx : ContDiff ℝ 2 x)
    (hv : ∀ t ∈ Icc t₀ t₁, ∑ i, deriv x t i ^ 2 < 1) :
    Stationary t₀ t₁ (chargedLagrangian m e (staticPotential φ a)) (graph x) ↔
      ∀ t ∈ Ioo t₀ t₁, ∀ k, deriv (fun s => legendre m (deriv x s) k) t =
        e * ((electricField φ k).val (x t) +
          ∑ j, (magneticTensor a k j).val (x t) * deriv x t j) := by
  have hdiff : Differentiable ℝ x := hx.differentiable (by norm_num)
  have htl : ∀ t ∈ Icc t₀ t₁, Timelike (deriv (graph x) t) := fun t ht => by
    rw [deriv_graph (hdiff t)]
    exact (timelike_cons_one _).mpr (hv t ht)
  rw [stationary_iff_lorentzForce m e h01 (contDiff_graph hx) isOpen_univ
    ((contDiff_staticPotential φ a).of_le (by simp)).contDiffOn (fun _ _ => mem_univ _) htl]
  refine forall₂_congr fun t ht => ?_
  have htI := Ioo_subset_Icc_self ht
  have hUd : HasDerivAt (fun s => fourVelocity (deriv (graph x) s))
      (deriv (fun s => fourVelocity (deriv (graph x) s)) t) t :=
    (((contDiffAt_fourVelocity (htl t htI) (n := 1)).differentiableAt (by norm_num)).comp t
      ((contDiff_graph hx).differentiable_deriv_two t)).hasDerivAt
  have hsucc (k : Fin 3) : m * deriv (fun s => fourVelocity (deriv (graph x) s)) t k.succ =
      deriv (fun s => legendre m (deriv x s) k) t := by
    have hfun : (fun s => legendre m (deriv x s) k) =
        fun s => m * fourVelocity (deriv (graph x) s) k.succ :=
      funext fun s => (mul_fourVelocity_graph_succ m hdiff s k).symm
    rw [hfun, ((hasDerivAt_pi.mp hUd k.succ).const_mul m).deriv]
  have hforce (k : Fin 3) :
      lorentzForce e (fieldTensor (staticPotential φ a) (graph x t)) (deriv (graph x) t) k.succ =
        e * ((electricField φ k).val (x t) +
          ∑ j, (magneticTensor a k j).val (x t) * deriv x t j) := by
    rw [deriv_graph (hdiff t), lorentzForce_staticPotential_succ]
    rfl
  constructor
  · intro h k
    rw [← hsucc k, ← hforce k, ← h]
    rfl
  · intro h
    have hs : ∀ k : Fin 3, m * deriv (fun s => fourVelocity (deriv (graph x) s)) t k.succ =
        lorentzForce e (fieldTensor (staticPotential φ a) (graph x t)) (deriv (graph x) t)
          k.succ := fun k => by
      rw [hsucc k, hforce k]
      exact h k
    have hpair : pair (deriv (fun s => fourVelocity (deriv (graph x) s)) t)
        (Fin.cons 1 (deriv x t) : Spacetime) = 0 := by
      have h2 := pair_fourVelocity_deriv (contDiff_graph hx) (htl t htI)
      have hps := properSpeed_smul_fourVelocity_of_timelike (htl t htI)
      rw [deriv_graph (hdiff t)] at hps h2
      rw [← hps, map_smul, smul_eq_mul, Minkowski.pair_comm, h2, mul_zero]
    have hU0 := time_eq_of_minkowskiForm_cons_eq_zero
      (w := deriv (fun s => fourVelocity (deriv (graph x) s)) t) (u := deriv x t)
      (by rw [metric_eq, hpair, mul_zero])
    have hf0 := time_eq_of_minkowskiForm_cons_eq_zero
      (w := lorentzForce e (fieldTensor (staticPotential φ a) (graph x t))
        (deriv (graph x) t)) (u := deriv x t)
      (by
        have h1 := lorentzForce_orthogonal e (fieldTensor (staticPotential φ a) (graph x t))
          (deriv (graph x) t)
        rw [deriv_graph (hdiff t)] at h1 ⊢
        exact h1)
    funext μ
    refine Fin.cases ?_ (fun k => ?_) μ
    · rw [Pi.smul_apply, smul_eq_mul, hU0, hf0, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hs k]
      ring
    · rw [Pi.smul_apply, smul_eq_mul]
      exact hs k

/-! ### Hamilton's equations -/

/-- The curve in the phase space of a curve of positions, with the momentum
`m γ ẋ + e a(x)`. -/
def phaseCurve (m e : ℝ) (a : Fin 3 → FreeSmoothRing (Fin 3)) (x : ℝ → Fin 3 → ℝ) (s : ℝ) :
    Fin 3 ⊕ Fin 3 → ℝ :=
  Sum.elim (x s) fun i => legendre m (deriv x s) i + e * (a i).val (x s)

theorem realKineticMomentum_phaseCurve (m e : ℝ) (x : ℝ → Fin 3 → ℝ) (s : ℝ) :
    realKineticMomentum e a (phaseCurve m e a x s) = legendre m (deriv x s) := by
  funext i
  change legendre m (deriv x s) i + e * (a i).val (x s) - e * (a i).val (x s) = _
  ring

/-- The derivative of a function of the position along a curve. -/
theorem hasDerivAt_val_comp (f : FreeSmoothRing (Fin 3)) (hx : Differentiable ℝ x) (t : ℝ) :
    HasDerivAt (fun s => f.val (x s))
      (∑ j, (partialDerivation j f).val (x t) * deriv x t j) t := by
  have h := (((contDiff_val f).differentiable (by simp) (x t)).hasFDerivAt).comp_hasDerivAt t
    (hx t).hasDerivAt
  rw [fderiv_val_apply] at h
  exact h

/-- The action of space-time of a charge in a static field is stationary on the graph of a
curve if and only if the curve `(x, m γ ẋ + e a(x))` in the phase space solves Hamilton's
equations. -/
theorem stationary_graph_iff_hamilton (hm : 0 < m) (e : ℝ) (h01 : t₀ < t₁)
    (hx : ContDiff ℝ 2 x) (hv : ∀ t ∈ Icc t₀ t₁, ∑ i, deriv x t i ^ 2 < 1) :
    Stationary t₀ t₁ (chargedLagrangian m e (staticPotential φ a)) (graph x) ↔
      ∀ t ∈ Ioo t₀ t₁, HasDerivAt (phaseCurve m e a x)
        (hamiltonianField (hamiltonian m e φ a) (phaseCurve m e a x t)) t := by
  have hdiff : Differentiable ℝ x := hx.differentiable (by norm_num)
  rw [stationary_graph_iff_lorentzForce φ a m e h01 hx hv]
  refine forall₂_congr fun t ht => ?_
  have hvt := hv t (Ioo_subset_Icc_self ht)
  have hπ := realKineticMomentum_phaseCurve a m e x t
  have hvel (i : Fin 3) :
      hamiltonianField (hamiltonian m e φ a) (phaseCurve m e a x t) (Sum.inl i) =
        deriv x t i := by
    rw [hamiltonianField_inl e φ a hm.ne', hπ]
    exact congrFun (velocityOfMomentum_legendre hm hvt) i
  have hleg (i : Fin 3) : HasDerivAt (fun s => legendre m (deriv x s) i)
      (deriv (fun s => legendre m (deriv x s) i) t) t :=
    (differentiableAt_pi.mp ((differentiableAt_legendre m hvt).comp t
      (hx.differentiable_deriv_two t)) i).hasDerivAt
  have hmom (i : Fin 3) : HasDerivAt (fun s => phaseCurve m e a x s (Sum.inr i))
      (deriv (fun s => legendre m (deriv x s) i) t +
        e * ∑ j, (partialDerivation j (a i)).val (x t) * deriv x t j) t :=
    (hleg i).add ((hasDerivAt_val_comp (a i) hdiff t).const_mul e)
  have hfield (i : Fin 3) :
      hamiltonianField (hamiltonian m e φ a) (phaseCurve m e a x t) (Sum.inr i) =
        e * ((electricField φ i).val (x t) +
            ∑ j, (magneticTensor a i j).val (x t) * deriv x t j) +
          e * ∑ j, (partialDerivation j (a i)).val (x t) * deriv x t j := by
    rw [hamiltonianField_inr e φ a hm.ne']
    simp only [hvel]
    change e * (∑ j, (partialDerivation i (a j)).val (x t) * deriv x t j -
      (partialDerivation i φ).val (x t)) = _
    have hsum : ∑ j, (magneticTensor a i j).val (x t) * deriv x t j =
        ∑ j, (partialDerivation i (a j)).val (x t) * deriv x t j -
          ∑ j, (partialDerivation j (a i)).val (x t) * deriv x t j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by
        rw [val_magneticTensor]
        ring
    rw [hsum, val_electricField]
    ring
  rw [hasDerivAt_pi]
  constructor
  · intro h s
    rcases s with i | i
    · rw [hvel i]
      exact hasDerivAt_pi.mp (hdiff t).hasDerivAt i
    · rw [hfield i, ← h i]
      exact hmom i
  · intro h k
    have h1 := (hmom k).unique (h (Sum.inr k))
    rw [hfield k] at h1
    linarith

/-- The graph of the positions of a trajectory of the Hamiltonian is a stationary curve of
the action of space-time, on every interval. -/
theorem stationary_graph_of_isTrajectory (hm : 0 < m) (e : ℝ)
    {c : Fin 3 ⊕ Fin 3 → TimeFunction}
    (h : IsTrajectory (canonical (Fin 3)) (hamiltonian m e φ a) c) (h01 : t₀ < t₁) :
    Stationary t₀ t₁ (chargedLagrangian m e (staticPotential φ a))
      (graph fun s i => realCurve c s (Sum.inl i)) := by
  have hd := (isTrajectory_canonical_iff_hasDerivAt _ c).mp h
  obtain ⟨x, hx⟩ : ∃ x : ℝ → Fin 3 → ℝ, x = fun s i => realCurve c s (Sum.inl i) := ⟨_, rfl⟩
  rw [← hx]
  have hxs (s : ℝ) : (fun j => realCurve c s (Sum.inl j)) = x s := (congrFun hx s).symm
  have hxc : ContDiff ℝ 2 x := by
    rw [hx]
    exact contDiff_pi.mpr fun i => ((c (Sum.inl i)).contDiff_apply_const).of_le (by simp)
  have hxd (s : ℝ) : HasDerivAt x
      (fun i => hamiltonianField (hamiltonian m e φ a) (realCurve c s) (Sum.inl i)) s := by
    rw [hx]
    exact hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mp (hd s) (Sum.inl i)
  have hvel (s : ℝ) :
      deriv x s = velocityOfMomentum m (realKineticMomentum e a (realCurve c s)) := by
    rw [(hxd s).deriv]
    funext i
    rw [hamiltonianField_inl e φ a hm.ne']
    rfl
  have hv (s : ℝ) : ∑ i, deriv x s i ^ 2 < 1 := by
    rw [hvel s]
    exact sum_sq_velocityOfMomentum_lt_one hm.ne' _
  have hphase : realCurve c = phaseCurve m e a x := by
    funext s b
    rcases b with i | i
    · exact (congrFun (hxs s) i)
    · have hleg : legendre m (deriv x s) = realKineticMomentum e a (realCurve c s) := by
        rw [hvel s, legendre_velocityOfMomentum hm]
      change realCurve c s (Sum.inr i) = legendre m (deriv x s) i + e * (a i).val (x s)
      rw [hleg, ← hxs s]
      simp only [realKineticMomentum]
      ring
  refine (stationary_graph_iff_hamilton φ a hm e h01 hxc fun t _ => hv t).mpr fun t _ => ?_
  rw [← hphase]
  exact hd t

end ProjectAinos.Electrodynamics.ChargedParticle
