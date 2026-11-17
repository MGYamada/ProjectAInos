/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialRelativity.ShellMeasure
public import ProjectAinos.SpecialRelativity.ElasticScattering
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The invariant flux and the covariance of a cross-section

For two incoming particles with the momenta `p₁`, `p₂` the invariant flux factor is
`fluxFactor p₁ p₂ = √(⟨p₁, p₂⟩² − Q(p₁) Q(p₂))` (Landau–Lifshitz, *The Classical Theory of
Fields*, §12).

* `fluxFactor_lorentz`: it is a Lorentz scalar.
* `fluxFactor_sq`: for momenta of the future cone, `F² = λ(s, m₁², m₂²)/4` with Källén's
  function.
* `fluxFactor_target_at_rest`: if the second particle is at rest for the observer `u`, then
  `F = m₂ |𝐩₁|`.

**Final states.** `measurePreserving_action_prod`: the product of the invariant measures of
two mass shells is invariant under a Lorentz transformation of both momenta. This is the
measure of the final states of two particles without the conservation of the momentum.

**The cross-section.** For a measure `ν` on the final states and a transition weight `W`,
`crossSection ν W F S = (1/4F) ∫_S W dν`. `crossSection_covariant`: it is unchanged under a
transformation of the final states that preserves `ν` and the weight. These are the two
hypotheses. The measure of the final states on the set where the momentum is conserved is not
constructed, and special relativity does not determine the weight.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace ProjectAinos.SpecialRelativity

open SmoothGeometry SmoothGeometry.Minkowski

variable {d : ℕ} {p₁ p₂ : MinkowskiModel d}

/-- The invariant flux factor `√(⟨p₁, p₂⟩² − Q(p₁) Q(p₂))` of two incoming particles. -/
def fluxFactor (p₁ p₂ : MinkowskiModel d) : ℝ :=
  Real.sqrt (pair p₁ p₂ ^ 2 - intervalQuadratic p₁ * intervalQuadratic p₂)

/-- The flux factor is a Lorentz scalar. -/
theorem fluxFactor_lorentz (L : LorentzGroup d) (p₁ p₂ : MinkowskiModel d) :
    fluxFactor (L.val p₁) (L.val p₂) = fluxFactor p₁ p₂ := by
  rw [fluxFactor, fluxFactor, LorentzGroup.preserves_pair, LorentzGroup.preserves_interval,
    LorentzGroup.preserves_interval]

theorem fluxFactor_sq_eq (hp₁ : FutureCausal p₁) (hp₂ : FutureCausal p₂) :
    fluxFactor p₁ p₂ ^ 2 = pair p₁ p₂ ^ 2 - intervalQuadratic p₁ * intervalQuadratic p₂ :=
  Real.sq_sqrt (sub_nonneg.mpr (intervalQuadratic_mul_le_pair_sq hp₁ hp₂))

/-- `F² = λ(s, m₁², m₂²)/4`. -/
theorem fluxFactor_sq (hp₁ : FutureCausal p₁) (hp₂ : FutureCausal p₂) :
    fluxFactor p₁ p₂ ^ 2 =
      kallen (mandelstamS p₁ p₂) (intervalQuadratic p₁) (intervalQuadratic p₂) / 4 := by
  rw [fluxFactor_sq_eq hp₁ hp₂, mandelstamS, intervalQuadratic_add, kallen]
  ring

/-- If the second particle is at rest for the observer `u`, the flux factor is `m₂ |𝐩₁|`. -/
theorem fluxFactor_target_at_rest (u : Observer d) (p₁ : MinkowskiModel d) {m₂ : ℝ}
    (hm₂ : 0 ≤ m₂) :
    fluxFactor p₁ (m₂ • u.velocity) =
      m₂ * Real.sqrt (u.restForm (observerMomentum u p₁) (observerMomentum u p₁)) := by
  have hpair : pair p₁ u.velocity = observerEnergy u p₁ := pair_comm _ _
  have hsq := observerEnergy_sq u p₁
  have harg : pair p₁ (m₂ • u.velocity) ^ 2 -
      intervalQuadratic p₁ * intervalQuadratic (m₂ • u.velocity) =
      m₂ ^ 2 * u.restForm (observerMomentum u p₁) (observerMomentum u p₁) := by
    rw [map_smul, hpair, QuadraticMap.map_smul, u.unit]
    simp only [smul_eq_mul]
    linear_combination m₂ ^ 2 * hsq
  rw [fluxFactor, harg, Real.sqrt_mul (sq_nonneg m₂), Real.sqrt_sq hm₂]

/-! ### Final states of two particles -/

instance (d : ℕ) (m : ℝ) : SFinite (FutureShell.measure d m) := by
  unfold FutureShell.measure
  infer_instance

/-- The product of the invariant measures of two mass shells is invariant under a Lorentz
transformation of both momenta. -/
theorem measurePreserving_action_prod (m₃ m₄ : ℝ) (L : orthochronousLorentzGroup d) :
    MeasurePreserving (Prod.map (FutureShell.action m₃ L) (FutureShell.action m₄ L))
      ((FutureShell.measure d m₃).prod (FutureShell.measure d m₄))
      ((FutureShell.measure d m₃).prod (FutureShell.measure d m₄)) :=
  (FutureShell.measurePreserving_action L).prod (FutureShell.measurePreserving_action L)

/-! ### The cross-section -/

/-- The cross-section of a set `S` of final states, for a measure `ν` on the final states, a
transition weight `W` and the flux factor `F`: `(1/4F) ∫_S W dν`. -/
def crossSection {α : Type*} [MeasurableSpace α] (ν : Measure α) (W : α → ℝ) (F : ℝ)
    (S : Set α) : ℝ :=
  (4 * F)⁻¹ * ∫ y in S, W y ∂ν

/-- The cross-section is unchanged under a transformation of the final states that preserves
their measure and the transition weight. -/
theorem crossSection_covariant {α : Type*} [MeasurableSpace α] {ν : Measure α} {φ : α → α}
    (hφ : MeasurePreserving φ ν ν) (hemb : MeasurableEmbedding φ) {W W' : α → ℝ}
    (hW : ∀ y, W' (φ y) = W y) (F : ℝ) (S : Set α) :
    crossSection ν W' F (φ '' S) = crossSection ν W F S := by
  rw [crossSection, crossSection, hφ.setIntegral_image_emb hemb]
  simp only [hW]

end ProjectAinos.SpecialRelativity
