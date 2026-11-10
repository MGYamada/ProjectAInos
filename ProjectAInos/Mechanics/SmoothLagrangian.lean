module

public import ProjectAInos.Mechanics.EulerLagrange
public import ProjectAInos.SmoothAlgebra.Differential
import Mathlib.Tactic.NormNum

/-!
# Mechanical Lagrangians from the shared C∞-ring

The coordinates of a smooth operation are time, the `n` positions and the `n`
velocities, in that order. Evaluation uses the smooth-ring morphisms from the
shared algebraic layer. The construction includes the zero-coordinate system.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff

namespace ProjectAInos.Mechanics

open SmoothAlgebra

/-- Evaluate a smooth observable in time, position and velocity coordinates. -/
def ofSmoothOperation {n : ℕ} (f : SmoothOperation (n + n + 1)) :
    Lagrangian (Fin n → ℝ) :=
  fun t z => SmoothOperation.eval (Fin.cons t (Fin.append z.1 z.2)) f

@[simp] theorem ofSmoothOperation_apply {n : ℕ} (f : SmoothOperation (n + n + 1))
    (t : ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    ofSmoothOperation f t z = f (Fin.cons t (Fin.append z.1 z.2)) := rfl

/-- Smooth substitution of observables agrees with pointwise substitution of
mechanical Lagrangians, because evaluation is a C∞-ring morphism. -/
theorem ofSmoothOperation_op {n k : ℕ} (f : SmoothOperation k)
    (g : Fin k → SmoothOperation (n + n + 1)) (t : ℝ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    ofSmoothOperation (SmoothRing.op f g) t z = f (fun i => ofSmoothOperation (g i) t z) :=
  (SmoothOperation.eval (Fin.cons t (Fin.append z.1 z.2))).map_op f g

/-- A bundled C∞ operation supplies the joint regularity required for mechanics. -/
theorem contDiff_ofSmoothOperation {n : ℕ} (f : SmoothOperation (n + n + 1)) :
    ContDiff ℝ ∞ (Function.uncurry (ofSmoothOperation f)) := by
  apply f.contMDiff.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using
      (contDiff_fst : ContDiff ℝ ∞ (fun p : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => p.1))
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa only [Fin.cons_succ, Fin.append_left, Function.comp_def] using
        (contDiff_apply ℝ (fun _ : Fin n => ℝ) k).comp (contDiff_fst.comp contDiff_snd)
    · simpa only [Fin.cons_succ, Fin.append_right, Function.comp_def] using
        (contDiff_apply ℝ (fun _ : Fin n => ℝ) k).comp (contDiff_snd.comp contDiff_snd)

/-- The fixed-endpoint Euler–Lagrange theorem for the shared smooth-function ring.
No separate smoothness assumption on `f` is necessary. -/
theorem stationary_ofSmoothOperation_iff {n : ℕ} {a b : ℝ}
    (f : SmoothOperation (n + n + 1)) {q : ℝ → Fin n → ℝ}
    (hab : a < b) (hq : ContDiff ℝ 2 q) :
    Stationary a b (ofSmoothOperation f) q ↔
      ∀ t ∈ Ioo a b, deriv (momentum (ofSmoothOperation f) q) t =
        force (ofSmoothOperation f) q t :=
  stationary_iff_momentum_equation hab ((contDiff_ofSmoothOperation f).of_le (by norm_num)) hq

end ProjectAInos.Mechanics
