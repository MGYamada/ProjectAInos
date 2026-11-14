/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAInos

/-! Public consumers of the oscillation API: the general solution of
`ẍ + ω² x = 0`, amplitude and phase, the energy and the period, the oscillator
as a Lagrangian and as a Hamiltonian system with its flow, the linearization
at an equilibrium, damped oscillations, and the dissipative function. Default
elaborator options are intentional: these checks must not rely on the
implementation's transparency settings. Every statement is pinned with its
type. -/
noncomputable section
open ProjectAInos.SmoothAlgebra ProjectAInos.SmoothAlgebra.SmoothRing
open ProjectAInos.SmoothAlgebra.FreeSmoothRing ProjectAInos.SmoothAlgebra.PhaseSpace
open ProjectAInos.Mechanics
open Matrix

section Harmonic

example (ω : ℝ) (x : TimeFunction) :
    IsHarmonic ω x ↔
      timeDerivative (timeDerivative x) = -(algebraMap ℝ TimeFunction (ω ^ 2) * x) :=
  Iff.rfl

example (ω : ℝ) (t : ℝ) : TimeFunction.cosMul ω (fun _ => t) = Real.cos (ω * t) := rfl

example (ω : ℝ) (t : ℝ) : TimeFunction.sinMul ω (fun _ => t) = Real.sin (ω * t) := rfl

example (ω : ℝ) :
    timeDerivative (TimeFunction.cosMul ω) =
      -(algebraMap ℝ TimeFunction ω * TimeFunction.sinMul ω) :=
  TimeFunction.timeDerivative_cosMul ω

example (ω : ℝ) :
    timeDerivative (TimeFunction.sinMul ω) = algebraMap ℝ TimeFunction ω * TimeFunction.cosMul ω :=
  TimeFunction.timeDerivative_sinMul ω

/-- The general solution (Landau–Lifshitz (21.7)). -/
example {ω : ℝ} {x : TimeFunction} (h : IsHarmonic ω x) (hω : ω ≠ 0) :
    x = algebraMap ℝ TimeFunction (x fun _ => 0) * TimeFunction.cosMul ω +
      algebraMap ℝ TimeFunction (timeDerivative x (fun _ => 0) / ω) * TimeFunction.sinMul ω :=
  h.eq_cos_add_sin hω

example {ω : ℝ} {x : TimeFunction} (hω : ω ≠ 0) :
    IsHarmonic ω x ↔ ∃ c₁ c₂ : ℝ, x = algebraMap ℝ TimeFunction c₁ * TimeFunction.cosMul ω +
      algebraMap ℝ TimeFunction c₂ * TimeFunction.sinMul ω :=
  isHarmonic_iff hω

/-- A free oscillation is determined by its initial position and velocity. -/
example {ω : ℝ} {x y : TimeFunction} (hx : IsHarmonic ω x) (hy : IsHarmonic ω y) (hω : ω ≠ 0)
    (h0 : x (fun _ => 0) = y fun _ => 0)
    (h1 : timeDerivative x (fun _ => 0) = timeDerivative y fun _ => 0) : x = y :=
  hx.eq_of_initial hy hω h0 h1

example (c₁ c₂ : ℝ) : amplitude c₁ c₂ = Real.sqrt (c₁ ^ 2 + c₂ ^ 2) := rfl

example (c₁ c₂ θ : ℝ) :
    amplitude c₁ c₂ * Real.cos (θ + phase c₁ c₂) = c₁ * Real.cos θ + c₂ * Real.sin θ :=
  amplitude_mul_cos_add c₁ c₂ θ

/-- Amplitude and phase (Landau–Lifshitz (21.8)). -/
example {ω : ℝ} {x : TimeFunction} (h : IsHarmonic ω x) (hω : ω ≠ 0) (t : ℝ) :
    x (fun _ => t) =
      amplitude (x fun _ => 0) (timeDerivative x (fun _ => 0) / ω) *
        Real.cos (ω * t + phase (x fun _ => 0) (timeDerivative x (fun _ => 0) / ω)) :=
  h.apply_eq_amplitude_mul_cos hω t

/-- The period does not depend on the amplitude. -/
example {ω : ℝ} {x : TimeFunction} (h : IsHarmonic ω x) (hω : ω ≠ 0) (t : ℝ) :
    x (fun _ => t + 2 * Real.pi / ω) = x fun _ => t :=
  h.apply_add_period hω t

/-- The energy (Landau–Lifshitz (21.11)). -/
example {ω : ℝ} {x : TimeFunction} (h : IsHarmonic ω x) (hω : ω ≠ 0) (m t : ℝ) :
    m / 2 * (timeDerivative x (fun _ => t) ^ 2 + ω ^ 2 * x (fun _ => t) ^ 2) =
      m / 2 * ω ^ 2 * amplitude (x fun _ => 0) (timeDerivative x (fun _ => 0) / ω) ^ 2 :=
  h.energy_eq_amplitude hω m t

end Harmonic

section Oscillator

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The Lagrangian side (Landau–Lifshitz (21.3), (21.5)). -/
example {m ω : ι → ℝ} {k : ℝ} (hm : ∀ i, m i ≠ 0) (hk : ∀ i, k = m i * ω i ^ 2)
    (γ : ι → TimeFunction) :
    StandardJet.IsSolution
        ((StandardJet.jetRing ι).naturalLagrangian m (StandardJet.oscillatorPotential k)) γ ↔
      ∀ i, IsHarmonic (ω i) (γ i) :=
  StandardJet.isSolution_oscillator_iff_isHarmonic hm hk γ

example (m : ι → ℝ) (k : ℝ) :
    Oscillator.hamiltonian m k = kineticEnergy m + oscillatorPotential k := rfl

/-- The Hamiltonian side. -/
example {m ω : ι → ℝ} {k : ℝ} (hm : ∀ i, m i ≠ 0) (hk : ∀ i, k = m i * ω i ^ 2)
    (c : ι ⊕ ι → TimeFunction) :
    IsTrajectory (canonical ι) (Oscillator.hamiltonian m k) c ↔
      ∀ i, IsHarmonic (ω i) (c (Sum.inl i)) ∧
        c (Sum.inr i) = algebraMap ℝ TimeFunction (m i) * timeDerivative (c (Sum.inl i)) :=
  Oscillator.isTrajectory_iff_isHarmonic hm hk c

example (m ω t : ℝ) :
    Oscillator.flowMatrix m ω t =
      !![Real.cos (ω * t), Real.sin (ω * t) / (m * ω);
        -(m * ω * Real.sin (ω * t)), Real.cos (ω * t)] := rfl

example (m ω : ℝ) : Oscillator.flowMatrix m ω 0 = 1 := Oscillator.flowMatrix_zero m ω

/-- The flow is a one-parameter group. -/
example {m ω : ℝ} (hm : m ≠ 0) (hω : ω ≠ 0) (s t : ℝ) :
    Oscillator.flowMatrix m ω (s + t) = Oscillator.flowMatrix m ω s * Oscillator.flowMatrix m ω t :=
  Oscillator.flowMatrix_add hm hω s t

/-- The flow preserves the area of the phase plane. -/
example {m ω : ℝ} (hm : m ≠ 0) (hω : ω ≠ 0) (t : ℝ) : (Oscillator.flowMatrix m ω t).det = 1 :=
  Oscillator.det_flowMatrix hm hω t

/-- Every trajectory is the flow of its initial point. -/
example {m ω : ι → ℝ} {k : ℝ} (hm : ∀ i, m i ≠ 0) (hω : ∀ i, ω i ≠ 0)
    (hk : ∀ i, k = m i * ω i ^ 2) {c : ι ⊕ ι → TimeFunction}
    (h : IsTrajectory (canonical ι) (Oscillator.hamiltonian m k) c) (i : ι) (t : ℝ) :
    ![c (Sum.inl i) fun _ => t, c (Sum.inr i) fun _ => t] =
      Oscillator.flowMatrix (m i) (ω i) t *ᵥ
        ![c (Sum.inl i) fun _ => 0, c (Sum.inr i) fun _ => 0] :=
  Oscillator.apply_eq_flowMatrix_mulVec hm hω hk h i t

/-- Every point lies on a trajectory. -/
example {m ω : ι → ℝ} {k : ℝ} (hm : ∀ i, m i ≠ 0) (hω : ∀ i, ω i ≠ 0)
    (hk : ∀ i, k = m i * ω i ^ 2) (q₀ p₀ : ι → ℝ) :
    IsTrajectory (canonical ι) (Oscillator.hamiltonian m k) (Oscillator.flowCurve m ω q₀ p₀) :=
  Oscillator.isTrajectory_flowCurve hm hω hk q₀ p₀

example (m ω q₀ p₀ : ι → ℝ) (i : ι) :
    Oscillator.flowCurve m ω q₀ p₀ (Sum.inl i) (fun _ => 0) = q₀ i :=
  Oscillator.flowCurve_inl_apply_zero m ω q₀ p₀ i

example (m ω q₀ p₀ : ι → ℝ) (i : ι) :
    Oscillator.flowCurve m ω q₀ p₀ (Sum.inr i) (fun _ => 0) = p₀ i :=
  Oscillator.flowCurve_inr_apply_zero m ω q₀ p₀ i

end Oscillator

section Linearization

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- Equilibria of the canonical bracket are critical points. -/
example (H : PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) :
    IsTrajectory (canonical ι) H (fun a => algebraMap ℝ TimeFunction (x₀ a)) ↔
      ∀ a, FreeSmoothRing.lift x₀ (partialDerivation a H) = 0 :=
  isTrajectory_canonical_const_iff H x₀

example (H : PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (a b : ι ⊕ ι) :
    hessian H x₀ a b = FreeSmoothRing.lift x₀ (partialDerivation a (partialDerivation b H)) :=
  rfl

example (H : PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (a c : ι ⊕ ι) :
    linearization (canonical ι) H x₀ a c =
      FreeSmoothRing.lift x₀ (partialDerivation c ((canonical ι).bracket (generator a) H)) :=
  rfl

example (H : PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) :
    quadraticPart H x₀ =
      ∑ a, ∑ b, algebraMap ℝ (PhaseSpace ι) (hessian H x₀ a b / 2) *
        (displacement x₀ a * displacement x₀ b) := rfl

/-- The Hamiltonian vector field of the quadratic part is the linearization. -/
example (H : PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (a : ι ⊕ ι) :
    (canonical ι).bracket (generator a) (quadraticPart H x₀) =
      ∑ c, algebraMap ℝ (PhaseSpace ι) (linearization (canonical ι) H x₀ a c) *
        displacement x₀ c :=
  canonical_bracket_quadraticPart H x₀ a

example (H : PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (a c : ι ⊕ ι) :
    linearization (canonical ι) (quadraticPart H x₀) x₀ a c =
      linearization (canonical ι) H x₀ a c :=
  linearization_quadraticPart H x₀ a c

example (H : PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (c : ι ⊕ ι → TimeFunction) :
    IsTrajectory (canonical ι) (quadraticPart H x₀) c ↔
      ∀ a, timeDerivative (c a) =
        ∑ b, algebraMap ℝ TimeFunction (linearization (canonical ι) H x₀ a b) *
          (c b - algebraMap ℝ TimeFunction (x₀ b)) :=
  isTrajectory_quadraticPart_iff H x₀ c

/-- Rest at `q₀` is an equilibrium exactly at a critical point of the potential. -/
example (b U : SmoothOperation 1) (q₀ : ℝ) :
    IsTrajectory (canonical (Fin 1)) (naturalHamiltonian b U)
        (fun a => algebraMap ℝ TimeFunction (restPoint q₀ a)) ↔
      SmoothOperation.partialDeriv 0 U (fun _ => q₀) = 0 :=
  isTrajectory_restPoint_iff b U q₀

/-- Small oscillations at a non-degenerate minimum (Landau–Lifshitz (21.6)). -/
example (b U : SmoothOperation 1) (q₀ : ℝ) (hb : 0 < b fun _ => q₀)
    (hk : 0 < SmoothOperation.partialDeriv 0 (SmoothOperation.partialDeriv 0 U) fun _ => q₀)
    {c : Fin 1 ⊕ Fin 1 → TimeFunction}
    (h : IsTrajectory (canonical (Fin 1))
      (quadraticPart (naturalHamiltonian b U) (restPoint q₀)) c) :
    IsHarmonic
      (Real.sqrt (b (fun _ => q₀) *
        SmoothOperation.partialDeriv 0 (SmoothOperation.partialDeriv 0 U) fun _ => q₀))
      (c (Sum.inl 0) - algebraMap ℝ TimeFunction q₀) :=
  isHarmonic_sqrt_of_isTrajectory_quadraticPart b U q₀ hb hk h

/-- The pendulum: `ω² = g/l`. -/
example {m l g ω : ℝ} (hm : m ≠ 0) (hl : l ≠ 0) (hω : ω ^ 2 = g / l)
    {c : Fin 1 ⊕ Fin 1 → TimeFunction}
    (h : IsTrajectory (canonical (Fin 1))
      (quadraticPart (pendulumHamiltonian m l g) (restPoint 0)) c) :
    IsHarmonic ω (c (Sum.inl 0)) :=
  isHarmonic_pendulum hm hl hω h

example (m l g : ℝ) :
    IsTrajectory (canonical (Fin 1)) (pendulumHamiltonian m l g)
      fun a => algebraMap ℝ TimeFunction (restPoint 0 a) :=
  isTrajectory_pendulum_restPoint m l g

end Linearization

section Damped

example (γ ω₀ : ℝ) (x : TimeFunction) :
    IsDamped γ ω₀ x ↔
      timeDerivative (timeDerivative x) =
        -(algebraMap ℝ TimeFunction (2 * γ) * timeDerivative x) -
          algebraMap ℝ TimeFunction (ω₀ ^ 2) * x :=
  Iff.rfl

example {ω₀ : ℝ} {x : TimeFunction} : IsDamped 0 ω₀ x ↔ IsHarmonic ω₀ x := isDamped_zero_iff

example (a t : ℝ) : TimeFunction.expMul a (fun _ => t) = Real.exp (a * t) := rfl

/-- The substitution `y = e^{γt} x` removes the first-order term. -/
example (γ ω₀ : ℝ) (x : TimeFunction) :
    IsDamped γ ω₀ x ↔
      timeDerivative (timeDerivative (TimeFunction.expMul γ * x)) =
        -(algebraMap ℝ TimeFunction (ω₀ ^ 2 - γ ^ 2) * (TimeFunction.expMul γ * x)) :=
  isDamped_iff_expMul_mul γ ω₀ x

example {γ ω₀ ω : ℝ} (hω : ω ^ 2 = ω₀ ^ 2 - γ ^ 2) (x : TimeFunction) :
    IsDamped γ ω₀ x ↔ IsHarmonic ω (TimeFunction.expMul γ * x) :=
  isDamped_iff_isHarmonic hω x

/-- Weak damping (Landau–Lifshitz (25.4)). -/
example {γ ω₀ ω : ℝ} {x : TimeFunction} (h : IsDamped γ ω₀ x) (hω : ω ^ 2 = ω₀ ^ 2 - γ ^ 2)
    (hω0 : ω ≠ 0) (t : ℝ) :
    x (fun _ => t) =
      amplitude (x fun _ => 0) ((timeDerivative x (fun _ => 0) + γ * x fun _ => 0) / ω) *
        Real.exp (-γ * t) *
        Real.cos (ω * t +
          phase (x fun _ => 0) ((timeDerivative x (fun _ => 0) + γ * x fun _ => 0) / ω)) :=
  h.apply_eq_amplitude_mul_exp_mul_cos hω hω0 t

/-- The envelope of a weakly damped oscillation. -/
example {γ ω₀ ω : ℝ} {x : TimeFunction} (h : IsDamped γ ω₀ x) (hω : ω ^ 2 = ω₀ ^ 2 - γ ^ 2)
    (hω0 : ω ≠ 0) (t : ℝ) :
    |x fun _ => t| ≤
      amplitude (x fun _ => 0) ((timeDerivative x (fun _ => 0) + γ * x fun _ => 0) / ω) *
        Real.exp (-γ * t) :=
  h.abs_apply_le hω hω0 t

/-- Critical damping (Landau–Lifshitz (25.7)). -/
example {γ ω₀ : ℝ} {x : TimeFunction} (h : IsDamped γ ω₀ x) (hc : ω₀ ^ 2 = γ ^ 2) (t : ℝ) :
    x (fun _ => t) = Real.exp (-γ * t) *
      (x (fun _ => 0) + (timeDerivative x (fun _ => 0) + γ * x fun _ => 0) * t) :=
  h.apply_eq_critical hc t

/-- Strong damping (Landau–Lifshitz (25.6)). -/
example {γ ω₀ β : ℝ} {x : TimeFunction} (h : IsDamped γ ω₀ x) (hβ : β ^ 2 = γ ^ 2 - ω₀ ^ 2)
    (hβ0 : β ≠ 0) (t : ℝ) :
    x (fun _ => t) =
      ((γ + β) * x (fun _ => 0) + timeDerivative x fun _ => 0) / (2 * β) *
          Real.exp (-(γ - β) * t) -
        ((γ - β) * x (fun _ => 0) + timeDerivative x fun _ => 0) / (2 * β) *
          Real.exp (-(γ + β) * t) :=
  h.apply_eq_overdamped hβ hβ0 t

/-- Uniqueness for all real `γ` and `ω₀`. -/
example {γ ω₀ : ℝ} {x y : TimeFunction} (hx : IsDamped γ ω₀ x) (hy : IsDamped γ ω₀ y)
    (h0 : x (fun _ => 0) = y fun _ => 0)
    (h1 : timeDerivative x (fun _ => 0) = timeDerivative y fun _ => 0) : x = y :=
  hx.eq_of_initial hy h0 h1

/-- Existence: exponentials of the characteristic roots. -/
example {γ ω₀ r : ℝ} (hr : r ^ 2 + 2 * γ * r + ω₀ ^ 2 = 0) :
    IsDamped γ ω₀ (TimeFunction.expMul r) :=
  isDamped_expMul hr

example {γ ω₀ : ℝ} (hc : ω₀ ^ 2 = γ ^ 2) :
    IsDamped γ ω₀ (TimeFunction.time * TimeFunction.expMul (-γ)) :=
  isDamped_time_mul_expMul hc

example {γ ω₀ ω : ℝ} {y : TimeFunction} (hy : IsHarmonic ω y) (hω : ω ^ 2 = ω₀ ^ 2 - γ ^ 2) :
    IsDamped γ ω₀ (TimeFunction.expMul (-γ) * y) :=
  hy.isDamped_expMul_neg_mul hω

/-- The rate of loss of energy. -/
example {γ ω₀ : ℝ} {x : TimeFunction} (h : IsDamped γ ω₀ x) :
    timeDerivative (timeDerivative x * timeDerivative x +
        algebraMap ℝ TimeFunction (ω₀ ^ 2) * (x * x)) =
      -(algebraMap ℝ TimeFunction (4 * γ) * (timeDerivative x * timeDerivative x)) :=
  h.timeDerivative_energy

example {γ ω₀ : ℝ} {x : TimeFunction} (h : IsDamped γ ω₀ x) (hγ : 0 ≤ γ) :
    Antitone fun t : ℝ => timeDerivative x (fun _ => t) ^ 2 + ω₀ ^ 2 * x (fun _ => t) ^ 2 :=
  h.energy_antitone hγ

end Damped

section Dissipation

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

example {κ : Type*} (X : SmoothDerivation (FreeSmoothRing κ) (FreeSmoothRing κ))
    (c : κ → TimeFunction) :
    IsIntegralCurve X c ↔
      ∀ a, timeDerivative (c a) = FreeSmoothRing.lift c (X (generator a)) :=
  Iff.rfl

example {κ : Type*} (π : PoissonStructure (FreeSmoothRing κ)) (H : FreeSmoothRing κ)
    (c : κ → TimeFunction) : IsIntegralCurve (π.hamiltonian H) c ↔ IsTrajectory π H c :=
  isIntegralCurve_hamiltonian_iff π H c

example (H : PhaseSpace ι) (i : ι) : velocity H i = partialDerivation (Sum.inr i) H := rfl

example (α : Matrix ι ι ℝ) (H : PhaseSpace ι) :
    dissipativeFunction α H =
      ∑ i, ∑ k, algebraMap ℝ (PhaseSpace ι) (α i k / 2) * (velocity H i * velocity H k) := rfl

example (α : Matrix ι ι ℝ) (H f : PhaseSpace ι) :
    dissipativeField α H f =
      (canonical ι).bracket f H - ∑ i, frictionalForce α H i * partialDerivation (Sum.inr i) f :=
  dissipativeField_apply α H f

example (α : Matrix ι ι ℝ) (H : PhaseSpace ι) (i : ι) :
    dissipativeField α H (p i) = -partialDerivation (Sum.inl i) H - frictionalForce α H i :=
  dissipativeField_p α H i

/-- The rate of loss of energy (Landau–Lifshitz (25.13)). -/
example (α : Matrix ι ι ℝ) (H : PhaseSpace ι) :
    dissipativeField α H H = -(2 * dissipativeFunction α H) :=
  dissipativeField_self α H

example {α : Matrix ι ι ℝ} (hα : ∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ α *ᵥ v) (H : PhaseSpace ι)
    (x₀ : ι ⊕ ι → ℝ) : 0 ≤ FreeSmoothRing.lift x₀ (dissipativeFunction α H) :=
  lift_dissipativeFunction_nonneg hα H x₀

/-- The energy does not increase along a motion with friction. -/
example {α : Matrix ι ι ℝ} (hα : ∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ α *ᵥ v) {H : PhaseSpace ι}
    {c : ι ⊕ ι → TimeFunction} (h : IsIntegralCurve (dissipativeField α H) c) :
    Antitone fun t : ℝ => FreeSmoothRing.lift c H fun _ => t :=
  h.energy_antitone hα

/-- The oscillator with friction is the damped oscillator (Landau–Lifshitz (25.1)). -/
example {m a γ ω₀ : ι → ℝ} {k : ℝ} (hm : ∀ i, m i ≠ 0) (hk : ∀ i, k = m i * ω₀ i ^ 2)
    (ha : ∀ i, a i = 2 * m i * γ i) (c : ι ⊕ ι → TimeFunction) :
    IsIntegralCurve (dissipativeField (Matrix.diagonal a) (Oscillator.hamiltonian m k)) c ↔
      ∀ i, IsDamped (γ i) (ω₀ i) (c (Sum.inl i)) ∧
        c (Sum.inr i) = algebraMap ℝ TimeFunction (m i) * timeDerivative (c (Sum.inl i)) :=
  Oscillator.isIntegralCurve_dissipativeField_iff_isDamped hm hk ha c

end Dissipation
