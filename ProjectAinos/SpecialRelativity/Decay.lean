/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialRelativity.InvariantMass
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The decay of a particle into two particles

A particle of mass `M > 0` and momentum `P` decays into two particles with the momenta `p₁`,
`p₂` and the masses `m₁`, `m₂` (Landau–Lifshitz, *The Classical Theory of Fields*, §11).
`TwoBodyDecay P p₁ p₂ M m₁ m₂` holds the conservation `P = p₁ + p₂` and the three mass shells.
In the rest frame of the parent, which is the frame of the centre of momentum:

* `TwoBodyDecay.energy_first`, `energy_second`:
  `E₁ = (M² + m₁² − m₂²)/2M` and `E₂ = (M² + m₂² − m₁²)/2M`;
* `TwoBodyDecay.momentum_add`: the momenta of the daughters are opposite;
* `TwoBodyDecay.momentum_sq_first`, `momentum_sq_second`:
  `|𝐩₁|² = |𝐩₂|² = λ(M², m₁², m₂²)/4M²` with Källén's function `kallen`;
* `TwoBodyDecay.mass_add_le`: for daughters of the future cone, `m₁ + m₂ ≤ M`;
* `TwoBodyDecay.eq_smul_of_threshold`: at the threshold `M = m₁ + m₂` the daughters are at
  rest, `pᵢ = mᵢ u`. A daughter of mass zero then has the momentum zero, which is not a
  particle;
* `exists_twoBodyDecay`: for `m₁ + m₂ ≤ M` and every unit vector `n` of the rest space, there
  is a decay with `𝐩₁ = (√λ/2M) n`, and both daughters are in the future cone.

The conditions are those of the conservation laws. They do not select a direction of the
decay.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.SpecialRelativity

open SmoothGeometry SmoothGeometry.Minkowski

variable {d : ℕ}

/-- Källén's function `λ(a, b, c) = a² + b² + c² − 2ab − 2ac − 2bc`. -/
def kallen (a b c : ℝ) : ℝ := a ^ 2 + b ^ 2 + c ^ 2 - 2 * a * b - 2 * a * c - 2 * b * c

theorem kallen_sq (M m₁ m₂ : ℝ) :
    kallen (M ^ 2) (m₁ ^ 2) (m₂ ^ 2) = (M ^ 2 - (m₁ + m₂) ^ 2) * (M ^ 2 - (m₁ - m₂) ^ 2) := by
  unfold kallen
  ring

/-- Källén's function of the squares of the masses is not negative above the threshold. -/
theorem kallen_sq_nonneg {M m₁ m₂ : ℝ} (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (h : m₁ + m₂ ≤ M) :
    0 ≤ kallen (M ^ 2) (m₁ ^ 2) (m₂ ^ 2) := by
  rw [kallen_sq]
  have h1 : (m₁ + m₂) ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (add_nonneg hm₁ hm₂) h 2
  have h2 : (m₁ - m₂) ^ 2 ≤ M ^ 2 := by nlinarith
  exact mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)

/-- The conservation of the momentum and the mass shells in the decay of a particle of mass
`M > 0` into two particles. -/
structure TwoBodyDecay (P p₁ p₂ : MinkowskiModel d) (M m₁ m₂ : ℝ) : Prop where
  conservation : P = p₁ + p₂
  parent : intervalQuadratic P = M ^ 2
  first : intervalQuadratic p₁ = m₁ ^ 2
  second : intervalQuadratic p₂ = m₂ ^ 2
  mass_pos : 0 < M
  future : FutureTimelike P

namespace TwoBodyDecay

variable {P p₁ p₂ : MinkowskiModel d} {M m₁ m₂ : ℝ} (h : TwoBodyDecay P p₁ p₂ M m₁ m₂)

include h in
/-- The pairing of the momenta of the daughters. -/
theorem pair_eq : pair p₁ p₂ = (M ^ 2 - m₁ ^ 2 - m₂ ^ 2) / 2 := by
  have hQ := intervalQuadratic_add p₁ p₂
  rw [← h.conservation, h.parent, h.first, h.second] at hQ
  linarith

include h in
/-- The invariant mass of the parent is its mass. -/
theorem properSpeed_eq : properSpeed P = M := by
  rw [properSpeed, h.parent, Real.sqrt_sq h.mass_pos.le]

/-- The rest frame of the parent. -/
def restFrame : Observer d := centreOfMomentum P h.future

/-- An energy in the rest frame of the parent is the pairing with `P` divided by `M`. -/
theorem observerEnergy_restFrame (w : MinkowskiModel d) :
    observerEnergy h.restFrame w = M⁻¹ * pair P w := by
  change pair (fourVelocity P) w = M⁻¹ * pair P w
  rw [fourVelocity, h.properSpeed_eq, map_smul, smul_apply, smul_eq_mul]

/-- The energy of the first daughter: `E₁ = (M² + m₁² − m₂²)/2M`. -/
theorem energy_first :
    observerEnergy h.restFrame p₁ = (M ^ 2 + m₁ ^ 2 - m₂ ^ 2) / (2 * M) := by
  have hM := h.mass_pos.ne'
  have hpair : pair P p₁ = m₁ ^ 2 + (M ^ 2 - m₁ ^ 2 - m₂ ^ 2) / 2 := by
    rw [h.conservation, map_add, add_apply, pair_comm p₂ p₁, h.pair_eq]
    have h1 : pair p₁ p₁ = intervalQuadratic p₁ := rfl
    rw [h1, h.first]
  rw [h.observerEnergy_restFrame, hpair]
  field_simp
  ring

/-- The energy of the second daughter: `E₂ = (M² + m₂² − m₁²)/2M`. -/
theorem energy_second :
    observerEnergy h.restFrame p₂ = (M ^ 2 + m₂ ^ 2 - m₁ ^ 2) / (2 * M) := by
  have hM := h.mass_pos.ne'
  have hpair : pair P p₂ = m₂ ^ 2 + (M ^ 2 - m₁ ^ 2 - m₂ ^ 2) / 2 := by
    rw [h.conservation, map_add, add_apply, h.pair_eq]
    have h1 : pair p₂ p₂ = intervalQuadratic p₂ := rfl
    rw [h1, h.second]
    ring
  rw [h.observerEnergy_restFrame, hpair]
  field_simp
  ring

/-- The energies of the daughters add up to the mass of the parent. -/
theorem energy_add : observerEnergy h.restFrame p₁ + observerEnergy h.restFrame p₂ = M := by
  have hM := h.mass_pos.ne'
  rw [h.energy_first, h.energy_second]
  field_simp
  ring

/-- The momenta of the daughters in the rest frame of the parent are opposite. -/
theorem momentum_add :
    observerMomentum h.restFrame p₁ + observerMomentum h.restFrame p₂ = 0 := by
  have hP := observerMomentum_centreOfMomentum h.future
  have hsum : observerMomentum h.restFrame p₁ + observerMomentum h.restFrame p₂ =
      observerMomentum h.restFrame (p₁ + p₂) := (map_add h.restFrame.project p₁ p₂).symm
  rw [hsum, ← h.conservation]
  exact hP

/-- The momentum of the first daughter: `|𝐩₁|² = λ(M², m₁², m₂²)/4M²`. -/
theorem momentum_sq_first :
    h.restFrame.restForm (observerMomentum h.restFrame p₁) (observerMomentum h.restFrame p₁) =
      kallen (M ^ 2) (m₁ ^ 2) (m₂ ^ 2) / (4 * M ^ 2) := by
  have hM := h.mass_pos.ne'
  have hsq := observerEnergy_sq_of_mass h.restFrame h.first
  rw [h.energy_first] at hsq
  have hval : h.restFrame.restForm (observerMomentum h.restFrame p₁)
      (observerMomentum h.restFrame p₁) =
      ((M ^ 2 + m₁ ^ 2 - m₂ ^ 2) / (2 * M)) ^ 2 - m₁ ^ 2 := by linarith
  rw [hval, kallen]
  field_simp
  ring

/-- The momentum of the second daughter: `|𝐩₂|² = λ(M², m₁², m₂²)/4M²`. -/
theorem momentum_sq_second :
    h.restFrame.restForm (observerMomentum h.restFrame p₂) (observerMomentum h.restFrame p₂) =
      kallen (M ^ 2) (m₁ ^ 2) (m₂ ^ 2) / (4 * M ^ 2) := by
  have hM := h.mass_pos.ne'
  have hsq := observerEnergy_sq_of_mass h.restFrame h.second
  rw [h.energy_second] at hsq
  have hval : h.restFrame.restForm (observerMomentum h.restFrame p₂)
      (observerMomentum h.restFrame p₂) =
      ((M ^ 2 + m₂ ^ 2 - m₁ ^ 2) / (2 * M)) ^ 2 - m₂ ^ 2 := by linarith
  rw [hval, kallen]
  field_simp
  ring

include h in
/-- The masses of daughters of the future cone add up to at most the mass of the parent. -/
theorem mass_add_le (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (hp₁ : FutureCausal p₁)
    (hp₂ : FutureCausal p₂) : m₁ + m₂ ≤ M := by
  have hle := invariantMass_add_le hp₁ hp₂
  rw [← h.conservation] at hle
  have h1 : invariantMass p₁ = m₁ := by
    rw [invariantMass, properSpeed, h.first, Real.sqrt_sq hm₁]
  have h2 : invariantMass p₂ = m₂ := by
    rw [invariantMass, properSpeed, h.second, Real.sqrt_sq hm₂]
  have h3 : invariantMass P = M := h.properSpeed_eq
  rw [h1, h2, h3] at hle
  exact hle

/-- At the threshold `M = m₁ + m₂` the daughters are at rest in the rest frame of the parent:
`pᵢ = mᵢ u`. -/
theorem eq_smul_of_threshold (hM : M = m₁ + m₂) :
    p₁ = m₁ • h.restFrame.velocity ∧ p₂ = m₂ • h.restFrame.velocity := by
  have hMpos := h.mass_pos
  have hk : kallen (M ^ 2) (m₁ ^ 2) (m₂ ^ 2) = 0 := by
    rw [kallen_sq, hM, sub_self, zero_mul]
  have hzero (p : MinkowskiModel d) (hp : h.restFrame.restForm (observerMomentum h.restFrame p)
      (observerMomentum h.restFrame p) = 0) : observerMomentum h.restFrame p = 0 := by
    by_contra hne
    exact (h.restFrame.restForm_posDef _ hne).ne' hp
  have h1 := hzero p₁ (by rw [h.momentum_sq_first, hk, zero_div])
  have h2 := hzero p₂ (by rw [h.momentum_sq_second, hk, zero_div])
  have hne : m₁ + m₂ ≠ 0 := hM ▸ hMpos.ne'
  have hE1 : observerEnergy h.restFrame p₁ = m₁ := by
    rw [h.energy_first, hM]
    field_simp
    ring
  have hE2 : observerEnergy h.restFrame p₂ = m₂ := by
    rw [h.energy_second, hM]
    field_simp
    ring
  have hd1 := observerEnergy_smul_add_observerMomentum h.restFrame p₁
  have hd2 := observerEnergy_smul_add_observerMomentum h.restFrame p₂
  rw [h1, hE1] at hd1
  rw [h2, hE2] at hd2
  exact ⟨by simpa using hd1.symm, by simpa using hd2.symm⟩

end TwoBodyDecay

/-- For masses with `m₁ + m₂ ≤ M` and every unit vector `n` of the rest space of the parent,
there is a decay in which the first daughter has the momentum `(√λ/2M) n`. Both daughters are
in the closed future cone. -/
theorem exists_twoBodyDecay (u : Observer d) {M m₁ m₂ : ℝ} (hM : 0 < M) (hm₁ : 0 ≤ m₁)
    (hm₂ : 0 ≤ m₂) (hle : m₁ + m₂ ≤ M) (n : u.restSpace) (hn : u.restForm n n = 1) :
    ∃ p₁ p₂ : MinkowskiModel d, TwoBodyDecay (M • u.velocity) p₁ p₂ M m₁ m₂ ∧
      FutureCausal p₁ ∧ FutureCausal p₂ ∧
      (u.project p₁ : MinkowskiModel d) =
        (Real.sqrt (kallen (M ^ 2) (m₁ ^ 2) (m₂ ^ 2)) / (2 * M)) • (n : MinkowskiModel d) := by
  have hk := kallen_sq_nonneg hm₁ hm₂ hle
  have hunit : pair u.velocity u.velocity = 1 := u.unit
  have hun : pair u.velocity (n : MinkowskiModel d) = 0 := u.clock_rest n
  have hnu : pair (n : MinkowskiModel d) u.velocity = 0 := by rw [pair_comm]; exact hun
  have hnn : pair (n : MinkowskiModel d) (n : MinkowskiModel d) = -1 := by
    have h1 : u.restForm n n = -pair (n : MinkowskiModel d) (n : MinkowskiModel d) := rfl
    linarith
  have hksq : Real.sqrt (kallen (M ^ 2) (m₁ ^ 2) (m₂ ^ 2)) ^ 2 =
      kallen (M ^ 2) (m₁ ^ 2) (m₂ ^ 2) := Real.sq_sqrt hk
  have hQ (E k : ℝ) : intervalQuadratic (E • u.velocity + k • (n : MinkowskiModel d)) =
      E ^ 2 - k ^ 2 := by
    rw [intervalQuadratic_apply]
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hunit, hun, hnu, hnn]
    ring
  have hclock (E k : ℝ) : pair u.velocity (E • u.velocity + k • (n : MinkowskiModel d)) = E := by
    simp only [map_add, map_smul, smul_eq_mul, hunit, hun]
    ring
  have hE₁ : 0 ≤ (M ^ 2 + m₁ ^ 2 - m₂ ^ 2) / (2 * M) := by
    have h2 : m₂ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hm₂ (by linarith) 2
    exact div_nonneg (by nlinarith [sq_nonneg m₁]) (by linarith)
  have hE₂ : 0 ≤ (M ^ 2 + m₂ ^ 2 - m₁ ^ 2) / (2 * M) := by
    have h2 : m₁ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hm₁ (by linarith) 2
    exact div_nonneg (by nlinarith [sq_nonneg m₂]) (by linarith)
  have hsq₁ : ((M ^ 2 + m₁ ^ 2 - m₂ ^ 2) / (2 * M)) ^ 2 -
      (Real.sqrt (kallen (M ^ 2) (m₁ ^ 2) (m₂ ^ 2)) / (2 * M)) ^ 2 = m₁ ^ 2 := by
    rw [div_pow, div_pow, hksq, kallen]
    field_simp
    ring
  have hsq₂ : ((M ^ 2 + m₂ ^ 2 - m₁ ^ 2) / (2 * M)) ^ 2 -
      (-(Real.sqrt (kallen (M ^ 2) (m₁ ^ 2) (m₂ ^ 2)) / (2 * M))) ^ 2 = m₂ ^ 2 := by
    rw [neg_sq, div_pow, div_pow, hksq, kallen]
    field_simp
    ring
  refine ⟨((M ^ 2 + m₁ ^ 2 - m₂ ^ 2) / (2 * M)) • u.velocity +
      (Real.sqrt (kallen (M ^ 2) (m₁ ^ 2) (m₂ ^ 2)) / (2 * M)) • (n : MinkowskiModel d),
    ((M ^ 2 + m₂ ^ 2 - m₁ ^ 2) / (2 * M)) • u.velocity +
      (-(Real.sqrt (kallen (M ^ 2) (m₁ ^ 2) (m₂ ^ 2)) / (2 * M))) • (n : MinkowskiModel d),
    ⟨?_, ?_, ?_, ?_, hM, ?_⟩, ?_, ?_, ?_⟩
  · have hsum : (M ^ 2 + m₁ ^ 2 - m₂ ^ 2) / (2 * M) + (M ^ 2 + m₂ ^ 2 - m₁ ^ 2) / (2 * M) = M := by
      field_simp
      ring
    rw [add_add_add_comm, ← add_smul, ← add_smul, hsum, add_neg_cancel, zero_smul, add_zero]
  · rw [QuadraticMap.map_smul, u.unit, smul_eq_mul, mul_one, pow_two]
  · rw [hQ, hsq₁]
  · rw [hQ, hsq₂]
  · have hfut : FutureTimelike (M • u.velocity) := by
      have hu := u.futureTimelike
      rw [FutureTimelike] at hu ⊢
      rw [map_smul, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hM, smul_eq_mul]
      exact mul_lt_mul_of_pos_left hu hM
    exact hfut
  · refine futureCausal_of_pair_nonneg u.futureTimelike ?_ ?_
    · change 0 ≤ intervalQuadratic _
      rw [hQ, hsq₁]
      exact sq_nonneg m₁
    · rw [hclock]
      exact hE₁
  · refine futureCausal_of_pair_nonneg u.futureTimelike ?_ ?_
    · change 0 ≤ intervalQuadratic _
      rw [hQ, hsq₂]
      exact sq_nonneg m₂
    · rw [hclock]
      exact hE₂
  · rw [Observer.project_coe]
    have hc : u.clock (((M ^ 2 + m₁ ^ 2 - m₂ ^ 2) / (2 * M)) • u.velocity +
        (Real.sqrt (kallen (M ^ 2) (m₁ ^ 2) (m₂ ^ 2)) / (2 * M)) • (n : MinkowskiModel d)) =
        (M ^ 2 + m₁ ^ 2 - m₂ ^ 2) / (2 * M) := hclock _ _
    rw [hc, add_sub_cancel_left]

end ProjectAinos.SpecialRelativity
