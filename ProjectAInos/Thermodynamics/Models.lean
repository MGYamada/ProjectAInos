module

public import ProjectAInos.Thermodynamics.Comparison
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Tactic.NormNum

/-!
# Stable models and failure of exchange comparison

The coordinatewise product model satisfies stability while its two independent
positive directions violate exchange comparison.
-/

@[expose] public section

open Filter
open scoped NNReal Topology

namespace ProjectAInos.Thermodynamics

/-- The ordinary order on nonnegative real numbers satisfies A6. -/
theorem nnreal_stability : Stability ℝ≥0 := by
  intro x y z₀ z₁ ε _ hε h
  have left : Tendsto (fun n => x + ε n * z₀) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.add (hε.mul_const z₀)
  have right : Tendsto (fun n => y + ε n * z₁) atTop (𝓝 y) := by
    simpa using tendsto_const_nhds.add (hε.mul_const z₁)
  exact le_of_tendsto_of_tendsto' left right h

/-- Stability is preserved by coordinatewise products. -/
theorem Stability.prod {M N : Type*}
    [AddCommMonoid M] [PartialOrder M] [Module ℝ≥0 M]
    [AddCommMonoid N] [PartialOrder N] [Module ℝ≥0 N]
    (hM : Stability M) (hN : Stability N) : Stability (M × N) := by
  intro x y z₀ z₁ ε hpos hlim h
  exact ⟨hM x.1 y.1 z₀.1 z₁.1 ε hpos hlim (fun n => (h n).1),
    hN x.2 y.2 z₀.2 z₁.2 ε hpos hlim (fun n => (h n).2)⟩

/-- The nonnegative real model is exchange comparable. -/
theorem nnreal_exchangeComparison : ExchangeComparison ℝ≥0 :=
  exchangeComparison_of_linearOrder ℝ≥0

/-- Two independent nonnegative coordinates are stable. -/
theorem nnreal_prod_stability : Stability (ℝ≥0 × ℝ≥0) :=
  nnreal_stability.prod nnreal_stability

/-- Stability alone permits two independent, incomparable process directions. -/
theorem nnreal_prod_not_exchangeComparison : ¬ ExchangeComparison (ℝ≥0 × ℝ≥0) := by
  intro h
  have hbad := h (0, 0) (1, 0) (0, 0) (0, 1) (by norm_num) (by norm_num)
  norm_num [Prod.le_def] at hbad

end ProjectAInos.Thermodynamics
