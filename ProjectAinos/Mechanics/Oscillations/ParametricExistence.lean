/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Oscillations.Parametric
public import ProjectAinos.SmoothGeometry.ODE.Propagator

/-!
# Existence of solutions of `ẍ + p(t) x = 0`

For every smooth coefficient `p` the equation `ẍ + p x = 0` has a solution
with a given position and velocity at time zero, defined and smooth for all
time, and only one. It is the first component of the propagator of the
first-order system `(x, v)' = (v, −p x)`. In particular every coefficient has
a fundamental system, and only one, so the monodromy matrix of a periodic
coefficient is defined without further data (Landau–Lifshitz §27).
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.Mechanics.Parametric

open SmoothAlgebra SmoothGeometry.LinearODE

/-- The constant part `(x, v) ↦ (v, 0)` of the first-order system. -/
def velocityMap : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).prod 0

/-- The part `(x, v) ↦ (0, −x)` that the coefficient multiplies. -/
def forceMap : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (-ContinuousLinearMap.fst ℝ ℝ ℝ)

open scoped ContDiff in
theorem contDiff_hillCoefficient (p : TimeFunction) :
    ContDiff ℝ ∞ fun t : ℝ => velocityMap + (p fun _ => t) • forceMap :=
  contDiff_const.add (p.contDiff_apply_const.smul contDiff_const)

/-- The coefficient `(x, v) ↦ (v, −p(t) x)` of the first-order system. -/
def hillCoefficient (p : TimeFunction) : C(ℝ, (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) :=
  ⟨fun t => velocityMap + (p fun _ => t) • forceMap, (contDiff_hillCoefficient p).continuous⟩

@[simp] theorem hillCoefficient_apply (p : TimeFunction) (t : ℝ) (z : ℝ × ℝ) :
    hillCoefficient p t z = (z.2, -((p fun _ => t) * z.1)) := by
  change (velocityMap + (p fun _ => t) • forceMap) z = _
  simp [velocityMap, forceMap]

/-- The state `(x(t), ẋ(t))` of the solution with the state `(x₀, v₀)` at time zero. -/
def hillState (p : TimeFunction) (x₀ v₀ t : ℝ) : ℝ × ℝ :=
  propagator (hillCoefficient p) t 0 (x₀, v₀)

open scoped ContDiff in
theorem contDiff_hillState (p : TimeFunction) (x₀ v₀ : ℝ) :
    ContDiff ℝ ∞ (hillState p x₀ v₀) := by
  have hA : ContDiff ℝ ∞ (hillCoefficient p) := contDiff_hillCoefficient p
  have h := (propagator_contDiff_of_contDiff hA).comp
    ((contDiff_id (E := ℝ)).prodMk (contDiff_const (c := (0 : ℝ))))
  exact h.clm_apply contDiff_const

theorem hasDerivAt_hillState (p : TimeFunction) (x₀ v₀ t : ℝ) :
    HasDerivAt (hillState p x₀ v₀)
      ((hillState p x₀ v₀ t).2, -((p fun _ => t) * (hillState p x₀ v₀ t).1)) t := by
  have h := hasDerivAt_propagator_apply (hillCoefficient p) t 0 (x₀, v₀)
  rw [hillCoefficient_apply] at h
  exact h

@[simp] theorem hillState_zero (p : TimeFunction) (x₀ v₀ : ℝ) :
    hillState p x₀ v₀ 0 = (x₀, v₀) := by
  simp [hillState]

/-- The solution of `ẍ + p x = 0` with position `x₀` and velocity `v₀` at time zero. -/
def hillSolution (p : TimeFunction) (x₀ v₀ : ℝ) : TimeFunction :=
  SmoothOperation.ofContDiff (fun τ => (hillState p x₀ v₀ (τ 0)).1)
    (contDiff_fst.comp ((contDiff_hillState p x₀ v₀).comp (contDiff_apply ℝ (fun _ => ℝ) 0)))

/-- Its velocity, as a function of time. -/
def hillVelocity (p : TimeFunction) (x₀ v₀ : ℝ) : TimeFunction :=
  SmoothOperation.ofContDiff (fun τ => (hillState p x₀ v₀ (τ 0)).2)
    (contDiff_snd.comp ((contDiff_hillState p x₀ v₀).comp (contDiff_apply ℝ (fun _ => ℝ) 0)))

theorem hillSolution_apply (p : TimeFunction) (x₀ v₀ t : ℝ) :
    hillSolution p x₀ v₀ (fun _ => t) = (hillState p x₀ v₀ t).1 := rfl

theorem hillVelocity_apply (p : TimeFunction) (x₀ v₀ t : ℝ) :
    hillVelocity p x₀ v₀ (fun _ => t) = (hillState p x₀ v₀ t).2 := rfl

theorem timeDerivative_hillSolution (p : TimeFunction) (x₀ v₀ : ℝ) :
    timeDerivative (hillSolution p x₀ v₀) = hillVelocity p x₀ v₀ := by
  refine TimeFunction.ext_apply_const fun t => ?_
  rw [TimeFunction.timeDerivative_apply]
  exact ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_hillState p x₀ v₀ t)).deriv

theorem timeDerivative_hillVelocity (p : TimeFunction) (x₀ v₀ : ℝ) :
    timeDerivative (hillVelocity p x₀ v₀) = -(p * hillSolution p x₀ v₀) := by
  refine TimeFunction.ext_apply_const fun t => ?_
  rw [TimeFunction.timeDerivative_apply]
  exact ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_hillState p x₀ v₀ t)).deriv

/-- The constructed function solves the equation. -/
theorem isHill_hillSolution (p : TimeFunction) (x₀ v₀ : ℝ) : IsHill p (hillSolution p x₀ v₀) := by
  unfold IsHill
  rw [timeDerivative_hillSolution, timeDerivative_hillVelocity]

@[simp] theorem hillSolution_zero (p : TimeFunction) (x₀ v₀ : ℝ) :
    hillSolution p x₀ v₀ (fun _ => 0) = x₀ := by
  rw [hillSolution_apply, hillState_zero]

@[simp] theorem timeDerivative_hillSolution_zero (p : TimeFunction) (x₀ v₀ : ℝ) :
    timeDerivative (hillSolution p x₀ v₀) (fun _ => 0) = v₀ := by
  rw [timeDerivative_hillSolution, hillVelocity_apply, hillState_zero]

/-- The fundamental system of an arbitrary smooth coefficient. -/
def FundamentalSystem.ofCoefficient (p : TimeFunction) : FundamentalSystem p where
  x₁ := hillSolution p 1 0
  x₂ := hillSolution p 0 1
  isHill₁ := isHill_hillSolution p 1 0
  isHill₂ := isHill_hillSolution p 0 1
  x₁_zero := hillSolution_zero p 1 0
  dx₁_zero := timeDerivative_hillSolution_zero p 1 0
  x₂_zero := hillSolution_zero p 0 1
  dx₂_zero := timeDerivative_hillSolution_zero p 0 1

/-- Every smooth coefficient has a fundamental system. -/
theorem FundamentalSystem.nonempty (p : TimeFunction) : Nonempty (FundamentalSystem p) :=
  ⟨FundamentalSystem.ofCoefficient p⟩

instance (p : TimeFunction) : Inhabited (FundamentalSystem p) :=
  ⟨FundamentalSystem.ofCoefficient p⟩

/-- A solution is determined by its position and velocity at time zero. -/
theorem IsHill.eq_of_initial {p x y : TimeFunction} (hx : IsHill p x) (hy : IsHill p y)
    (h0 : x (fun _ => 0) = y fun _ => 0)
    (h1 : timeDerivative x (fun _ => 0) = timeDerivative y fun _ => 0) : x = y := by
  rw [(FundamentalSystem.ofCoefficient p).eq_combination hx,
    (FundamentalSystem.ofCoefficient p).eq_combination hy, h0, h1]

/-- Existence of the solution with given initial data, for all time. -/
theorem exists_isHill (p : TimeFunction) (x₀ v₀ : ℝ) :
    ∃ x, IsHill p x ∧ x (fun _ => 0) = x₀ ∧ timeDerivative x (fun _ => 0) = v₀ :=
  ⟨hillSolution p x₀ v₀, isHill_hillSolution p x₀ v₀, hillSolution_zero p x₀ v₀,
    timeDerivative_hillSolution_zero p x₀ v₀⟩

/-- Existence and uniqueness of the solution with given initial data. -/
theorem existsUnique_isHill (p : TimeFunction) (x₀ v₀ : ℝ) :
    ∃! x, IsHill p x ∧ x (fun _ => 0) = x₀ ∧ timeDerivative x (fun _ => 0) = v₀ := by
  obtain ⟨x, hx, h0, h1⟩ := exists_isHill p x₀ v₀
  exact ⟨x, ⟨hx, h0, h1⟩, fun y hy => hy.1.eq_of_initial hx (hy.2.1.trans h0.symm)
    (hy.2.2.trans h1.symm)⟩

/-- A coefficient has only one fundamental system. -/
instance (p : TimeFunction) : Subsingleton (FundamentalSystem p) where
  allEq Φ Ψ := by
    have h1 : Φ.x₁ = Ψ.x₁ := Φ.isHill₁.eq_of_initial Ψ.isHill₁
      (Φ.x₁_zero.trans Ψ.x₁_zero.symm) (Φ.dx₁_zero.trans Ψ.dx₁_zero.symm)
    have h2 : Φ.x₂ = Ψ.x₂ := Φ.isHill₂.eq_of_initial Ψ.isHill₂
      (Φ.x₂_zero.trans Ψ.x₂_zero.symm) (Φ.dx₂_zero.trans Ψ.dx₂_zero.symm)
    cases Φ
    cases Ψ
    simp only at h1 h2
    subst h1
    subst h2
    rfl

/-- For a constant frequency the constructed fundamental system is `cos ωt`, `sin ωt / ω`. -/
theorem FundamentalSystem.ofCoefficient_harmonic {ω : ℝ} (hω : ω ≠ 0) :
    FundamentalSystem.ofCoefficient (algebraMap ℝ TimeFunction (ω ^ 2)) =
      FundamentalSystem.harmonic hω :=
  Subsingleton.elim _ _

/-- The monodromy matrix of a coefficient: the matrix of its fundamental system
at the time `T`. -/
def monodromy (p : TimeFunction) (T : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (FundamentalSystem.ofCoefficient p).matrix T

theorem FundamentalSystem.matrix_eq_monodromy {p : TimeFunction} (Φ : FundamentalSystem p)
    (T : ℝ) : Φ.matrix T = monodromy p T := by
  rw [Subsingleton.elim Φ (FundamentalSystem.ofCoefficient p)]
  rfl

theorem det_monodromy (p : TimeFunction) (T : ℝ) : (monodromy p T).det = 1 :=
  (FundamentalSystem.ofCoefficient p).det_matrix T

/-- The trace of the monodromy matrix of the oscillator is `2 cos ωT`. -/
theorem trace_monodromy_harmonic {ω : ℝ} (hω : ω ≠ 0) (T : ℝ) :
    (monodromy (algebraMap ℝ TimeFunction (ω ^ 2)) T).trace = 2 * Real.cos (ω * T) := by
  rw [← (FundamentalSystem.harmonic hω).matrix_eq_monodromy]
  exact FundamentalSystem.trace_matrix_harmonic hω T

end ProjectAinos.Mechanics.Parametric
