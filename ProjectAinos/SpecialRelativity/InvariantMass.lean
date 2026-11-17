/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialRelativity.ObserverEnergy
public import ProjectAinos.SpecialRelativity.MaximalProperTime
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The invariant mass of a system of particles

The invariant mass of a momentum `p` is `invariantMass p = √Q(p)` (Landau–Lifshitz, *The
Classical Theory of Fields*, §§9, 11). For momenta of the closed future cone:

* `invariantMass_add_le`: `M(p) + M(q) ≤ M(p + q)`: the mass of a system is at least the sum of
  the masses of its parts;
* `intervalQuadratic_add_eq_zero_iff`: the sum of two momenta is null if and only if both are
  null and parallel;
* `centreOfMomentum P hP` is the observer in whose rest space a future timelike total momentum
  `P` has no momentum (`observerMomentum_centreOfMomentum`); its energy there is the invariant
  mass (`observerEnergy_centreOfMomentum`), and it is the only such observer
  (`eq_centreOfMomentum`);
* `not_exists_observer_of_null`: a nonzero null total momentum has no such observer.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.SpecialRelativity

open SmoothGeometry SmoothGeometry.Minkowski

variable {d : ℕ} {p q : MinkowskiModel d}

/-- The invariant mass `√Q(p)` of a momentum. -/
def invariantMass (p : MinkowskiModel d) : ℝ := properSpeed p

theorem invariantMass_nonneg (p : MinkowskiModel d) : 0 ≤ invariantMass p :=
  Real.sqrt_nonneg _

theorem invariantMass_sq (hp : FutureCausal p) : invariantMass p ^ 2 = intervalQuadratic p :=
  Real.sq_sqrt ((futureCausal_iff p).mp hp).1

/-- The invariant mass does not depend on the inertial frame. -/
theorem invariantMass_lorentz (L : LorentzGroup d) (p : MinkowskiModel d) :
    invariantMass (L.val p) = invariantMass p :=
  congrArg Real.sqrt (LorentzGroup.preserves_interval L p)

/-- The mass of a system is at least the sum of the masses of its parts. -/
theorem invariantMass_add_le (hp : FutureCausal p) (hq : FutureCausal q) :
    invariantMass p + invariantMass q ≤ invariantMass (p + q) :=
  sqrt_add_sqrt_le hp hq

/-- Two null vectors of the future cone with zero pairing are parallel. -/
theorem exists_smul_of_pair_eq_zero (hp : FutureCausal p) (hq : FutureCausal q) (hp0 : p ≠ 0)
    (hQp : intervalQuadratic p = 0) (hQq : intervalQuadratic q = 0) (hpq : pair p q = 0) :
    ∃ c : ℝ, 0 ≤ c ∧ q = c • p := by
  have htp : 0 < time p := time_pos_of_futureCausal_ne_zero hp hp0
  have htq : 0 ≤ time q := ((futureCausal_iff q).mp hq).2
  have hnp : ‖space p‖ = time p := by
    rw [intervalQuadratic_coordinates] at hQp
    have h : ‖space p‖ ^ 2 = time p ^ 2 := by linarith
    exact (sq_eq_sq₀ (norm_nonneg _) htp.le).mp h
  have hnq : ‖space q‖ = time q := by
    rw [intervalQuadratic_coordinates] at hQq
    have h : ‖space q‖ ^ 2 = time q ^ 2 := by linarith
    exact (sq_eq_sq₀ (norm_nonneg _) htq).mp h
  have hinner : inner ℝ (space p) (space q) = ‖space p‖ * ‖space q‖ := by
    rw [pair_apply] at hpq
    rw [hnp, hnq]
    linarith
  have hpar := inner_eq_norm_mul_iff_real.mp hinner
  rw [hnp, hnq] at hpar
  refine ⟨time q / time p, div_nonneg htq htp.le, ?_⟩
  have hspace : space q = (time q / time p) • space p := by
    rw [div_eq_inv_mul, ← smul_smul, hpar, smul_smul, inv_mul_cancel₀ htp.ne', one_smul]
  have htime : time q = time q / time p * time p := by
    rw [div_mul_cancel₀ _ htp.ne']
  rw [← vector_time_space q, ← vector_time_space p]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using htime
  · have hj := congrFun (congrArg (fun x : Space d => (x : Fin d → ℝ)) hspace) j
    simpa using hj

/-- The sum of two momenta of the future cone is null if and only if both are null and
parallel. -/
theorem intervalQuadratic_add_eq_zero_iff (hp : FutureCausal p) (hq : FutureCausal q)
    (hp0 : p ≠ 0) :
    intervalQuadratic (p + q) = 0 ↔ intervalQuadratic p = 0 ∧ ∃ c : ℝ, 0 ≤ c ∧ q = c • p := by
  have hQp : 0 ≤ intervalQuadratic p := ((futureCausal_iff p).mp hp).1
  have hQq : 0 ≤ intervalQuadratic q := ((futureCausal_iff q).mp hq).1
  have hpair : 0 ≤ pair p q := pair_nonneg_of_futureCausal hp hq
  constructor
  · intro h
    rw [intervalQuadratic_add] at h
    have h1 : intervalQuadratic p = 0 := by linarith
    have h2 : intervalQuadratic q = 0 := by linarith
    have h3 : pair p q = 0 := by linarith
    exact ⟨h1, exists_smul_of_pair_eq_zero hp hq hp0 h1 h2 h3⟩
  · rintro ⟨h1, c, -, rfl⟩
    have hsum : p + c • p = (1 + c) • p := by rw [add_smul, one_smul]
    rw [hsum, QuadraticMap.map_smul, h1, smul_zero]

/-- The observer of the centre of momentum of a future timelike total momentum. -/
def centreOfMomentum (P : MinkowskiModel d) (hP : FutureTimelike P) : Observer d :=
  fourVelocityObserver P hP

/-- In the frame of the centre of momentum the energy is the invariant mass. -/
theorem observerEnergy_centreOfMomentum {P : MinkowskiModel d} (hP : FutureTimelike P) :
    observerEnergy (centreOfMomentum P hP) P = invariantMass P :=
  clock_fourVelocityObserver hP

/-- In the frame of the centre of momentum the total momentum is zero. -/
theorem observerMomentum_centreOfMomentum {P : MinkowskiModel d} (hP : FutureTimelike P) :
    observerMomentum (centreOfMomentum P hP) P = 0 := by
  apply Subtype.ext
  have hE := observerEnergy_centreOfMomentum hP
  have hvel : (centreOfMomentum P hP).velocity = fourVelocity P := rfl
  change P - (centreOfMomentum P hP).clock P • (centreOfMomentum P hP).velocity = 0
  have hclock : (centreOfMomentum P hP).clock P = properSpeed P := hE
  rw [hclock, hvel, properSpeed_smul_fourVelocity hP, sub_self]

/-- The observer of the centre of momentum is the only observer for whom the total momentum
is zero. -/
theorem eq_centreOfMomentum {P : MinkowskiModel d} (hP : FutureTimelike P) (u : Observer d)
    (h : observerMomentum u P = 0) : u = centreOfMomentum P hP := by
  have hdec := observerEnergy_smul_add_observerMomentum u P
  rw [h] at hdec
  have hP' : observerEnergy u P • u.velocity = P := by simpa using hdec
  have hE : 0 < observerEnergy u P := observerEnergy_pos u hP
  have hspeed : properSpeed P = observerEnergy u P := by
    have h1 : properSpeed (observerEnergy u P • u.velocity) = observerEnergy u P := by
      rw [properSpeed_smul, abs_of_pos hE, properSpeed, u.unit, Real.sqrt_one, mul_one]
    rwa [hP'] at h1
  have hvel : (observerEnergy u P)⁻¹ • P = u.velocity :=
    (congrArg (fun w : MinkowskiModel d => (observerEnergy u P)⁻¹ • w) hP'.symm).trans
      (by rw [smul_smul, inv_mul_cancel₀ hE.ne', one_smul])
  apply Observer.ext
  change u.velocity = fourVelocity P
  rw [fourVelocity, hspeed]
  exact hvel.symm

/-- A nonzero null total momentum has no frame of the centre of momentum. -/
theorem not_exists_observer_of_null {P : MinkowskiModel d} (hP0 : P ≠ 0)
    (hQ : intervalQuadratic P = 0) : ¬∃ u : Observer d, observerMomentum u P = 0 := by
  rintro ⟨u, h⟩
  have hdec := observerEnergy_smul_add_observerMomentum u P
  rw [h] at hdec
  have hP' : observerEnergy u P • u.velocity = P := by simpa using hdec
  have hE0 : observerEnergy u P = 0 := by
    have hsq := observerEnergy_sq u P
    rw [hQ, h] at hsq
    simpa using hsq
  rw [hE0, zero_smul] at hP'
  exact hP0 hP'.symm

end ProjectAinos.SpecialRelativity
