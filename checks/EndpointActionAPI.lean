/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.Mechanics.EndpointAction

/-! Typed contracts for the action as a function of its end points: Leibniz's
rule with moving limits and the formula `dS = p dq − E dt`. These examples use
default elaborator options. -/

open ProjectAinos ProjectAinos.Mechanics
open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

section MovingLimits

/-- Leibniz's rule with moving limits. -/
example {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {D : ℝ → ℝ} {a b : ℝ → ℝ} {s₀ a' b' : ℝ}
    (ha : HasDerivAt a a' s₀) (hb : HasDerivAt b b' s₀)
    (hD : ∀ t ∈ uIcc (a s₀) (b s₀), HasDerivAt (fun s => F (s, t)) (D t) s₀) :
    HasDerivAt (fun s => ∫ t in a s..b s, F (s, t))
      ((∫ t in a s₀..b s₀, D t) + F (s₀, b s₀) * b' - F (s₀, a s₀) * a') s₀ :=
  Variational.hasDerivAt_intervalIntegral_moving hF ha hb hD

example {a b : ℝ → ℝ} {s₀ : ℝ} (ha : ContinuousAt a s₀) (hb : ContinuousAt b s₀)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V) (h : ∀ t ∈ uIcc (a s₀) (b s₀), (s₀, t) ∈ V) :
    ∀ᶠ s in 𝓝 s₀, ∀ t ∈ uIcc (a s) (b s), (s, t) ∈ V :=
  Variational.eventually_uIcc_mem_open ha hb hV h

/-- The rule for an integrand that is smooth near the reference segment. -/
example {F : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    {D : ℝ → ℝ} {a b : ℝ → ℝ} {s₀ a' b' : ℝ} (ha : HasDerivAt a a' s₀)
    (hb : HasDerivAt b b' s₀) (hK : ∀ t ∈ uIcc (a s₀) (b s₀), (s₀, t) ∈ U)
    (hD : ∀ t ∈ uIcc (a s₀) (b s₀), HasDerivAt (fun s => F (s, t)) (D t) s₀) :
    HasDerivAt (fun s => ∫ t in a s..b s, F (s, t))
      ((∫ t in a s₀..b s₀, D t) + F (s₀, b s₀) * b' - F (s₀, a s₀) * a') s₀ :=
  Variational.hasDerivAt_intervalIntegral_moving_on hU hF ha hb hK hD

end MovingLimits

section Family

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

example (L : Lagrangian Q) (q : ℝ → Q) (t : ℝ) :
    pathEnergy L q t = momentum L q t (deriv q t) - L t (q t, deriv q t) := rfl

example {q : ℝ × ℝ → Q} {p : ℝ × ℝ} (hq : DifferentiableAt ℝ q p) :
    deriv (fun t => q (p.1, t)) p.2 = fderiv ℝ q p (0, 1) := deriv_family_time hq

example {g : ℝ × ℝ → Q} {s₀ t : ℝ} (hg : DifferentiableAt ℝ g (s₀, t)) :
    HasDerivAt (fun s => g (s, t)) (fderiv ℝ g (s₀, t) (1, 0)) s₀ :=
  hasDerivAt_family_parameter hg

example {g : ℝ × ℝ → Q} {s₀ t : ℝ} (hg : DifferentiableAt ℝ g (s₀, t)) :
    HasDerivAt (fun r => g (s₀, r)) (fderiv ℝ g (s₀, t) (0, 1)) t :=
  hasDerivAt_family_time hg

/-- The derivative of the Lagrangian along a family, in the parameter. -/
example {q : ℝ × ℝ → Q} {L : Lagrangian Q} {s₀ t : ℝ} (hq : ContDiffAt ℝ 2 q (s₀, t))
    (hL : DifferentiableAt ℝ (L t) (q (s₀, t), deriv (fun r => q (s₀, r)) t)) :
    HasDerivAt (fun s => L t (q (s, t), deriv (fun r => q (s, r)) t))
      (force L (fun r => q (s₀, r)) t (fderiv ℝ q (s₀, t) (1, 0)) +
        momentum L (fun r => q (s₀, r)) t
          (deriv (fun r => fderiv ℝ q (s₀, r) (1, 0)) t)) s₀ :=
  hasDerivAt_density_family hq hL

example {q : ℝ × ℝ → Q} {s₀ : ℝ} {c : ℝ → ℝ} {c' : ℝ} (hc : HasDerivAt c c' s₀)
    (hq : DifferentiableAt ℝ q (s₀, c s₀)) :
    deriv (fun s => q (s, c s)) s₀ =
      fderiv ℝ q (s₀, c s₀) (1, 0) + c' • deriv (fun r => q (s₀, r)) (c s₀) :=
  deriv_family_endpoint hc hq

example {L : Lagrangian Q} {q : ℝ → Q} {t : ℝ}
    (hL : ContDiffAt ℝ 2 (Function.uncurry L) (pathJet q t)) (hq : ContDiffAt ℝ 2 q t) :
    ContDiffAt ℝ 1 (momentum L q) t :=
  contDiffAt_momentum hL hq

end Family

section EndpointAction

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- `dS = p dq − E dt` at both ends, for a family and a Lagrangian that are
smooth on open sets. -/
example {L : Lagrangian Q} {W : Set (ℝ × (Q × Q))} (hW : IsOpen W)
    (hL : ContDiffOn ℝ ∞ (Function.uncurry L) W) {q : ℝ × ℝ → Q} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U) {a b : ℝ → ℝ} {s₀ a' b' : ℝ}
    (ha : HasDerivAt a a' s₀) (hb : HasDerivAt b b' s₀)
    (hqU : ∀ t ∈ uIcc (a s₀) (b s₀), (s₀, t) ∈ U)
    (hqW : ∀ t ∈ uIcc (a s₀) (b s₀), pathJet (fun t => q (s₀, t)) t ∈ W)
    (hEL : ∀ t ∈ uIcc (a s₀) (b s₀), eulerLagrange L (fun t => q (s₀, t)) t = 0) :
    HasDerivAt (fun s => action (a s) (b s) L fun t => q (s, t))
      (momentum L (fun t => q (s₀, t)) (b s₀) (deriv (fun s => q (s, b s)) s₀) -
          pathEnergy L (fun t => q (s₀, t)) (b s₀) * b' -
        (momentum L (fun t => q (s₀, t)) (a s₀) (deriv (fun s => q (s, a s)) s₀) -
          pathEnergy L (fun t => q (s₀, t)) (a s₀) * a')) s₀ :=
  hasDerivAt_action_movingEndpoints_on hW hL hU hq ha hb hqU hqW hEL

example {L : Lagrangian Q} (hL : ContDiff ℝ ∞ (Function.uncurry L)) {q : ℝ × ℝ → Q}
    (hq : ContDiff ℝ ∞ q) {a b : ℝ → ℝ} {s₀ a' b' : ℝ} (ha : HasDerivAt a a' s₀)
    (hb : HasDerivAt b b' s₀)
    (hEL : ∀ t ∈ uIcc (a s₀) (b s₀), eulerLagrange L (fun t => q (s₀, t)) t = 0) :
    HasDerivAt (fun s => action (a s) (b s) L fun t => q (s, t))
      (momentum L (fun t => q (s₀, t)) (b s₀) (deriv (fun s => q (s, b s)) s₀) -
          pathEnergy L (fun t => q (s₀, t)) (b s₀) * b' -
        (momentum L (fun t => q (s₀, t)) (a s₀) (deriv (fun s => q (s, a s)) s₀) -
          pathEnergy L (fun t => q (s₀, t)) (a s₀) * a')) s₀ :=
  hasDerivAt_action_movingEndpoints hL hq ha hb hEL

end EndpointAction

section Potential

example (m : ℝ) {V : ℝ → ℝ} {n : WithTop ℕ∞} (hV : ContDiff ℝ n V) :
    ContDiff ℝ n (Function.uncurry (natural m V)) := contDiff_natural_of_contDiff m hV

example (m : ℝ) {V : ℝ → ℝ} (hV : Differentiable ℝ V) {q : ℝ → ℝ} {t : ℝ}
    (hq : DifferentiableAt ℝ (deriv q) t) :
    eulerLagrange (natural m V) q t =
      (-deriv V (q t) - m * deriv (deriv q) t) • ContinuousLinearMap.id ℝ ℝ :=
  eulerLagrange_natural_of_differentiableAt m hV hq

example (m : ℝ) {V : ℝ → ℝ} (hV : Differentiable ℝ V) (q : ℝ → ℝ) (t : ℝ) :
    pathEnergy (natural m V) q t = m / 2 * deriv q t ^ 2 + V (q t) :=
  pathEnergy_natural m hV q t

/-- The formula for a particle in a potential. -/
example {m : ℝ} {V : ℝ → ℝ} (hV : ContDiff ℝ ∞ V) {q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U) {a b : ℝ → ℝ} {s₀ a' b' : ℝ}
    (ha : HasDerivAt a a' s₀) (hb : HasDerivAt b b' s₀)
    (hqU : ∀ t ∈ uIcc (a s₀) (b s₀), (s₀, t) ∈ U)
    (hN : ∀ t ∈ uIcc (a s₀) (b s₀),
      m * deriv (deriv fun t => q (s₀, t)) t = -deriv V (q (s₀, t))) :
    HasDerivAt (fun s => action (a s) (b s) (natural m V) fun t => q (s, t))
      (m * deriv (fun t => q (s₀, t)) (b s₀) * deriv (fun s => q (s, b s)) s₀ -
          (m / 2 * deriv (fun t => q (s₀, t)) (b s₀) ^ 2 + V (q (s₀, b s₀))) * b' -
        (m * deriv (fun t => q (s₀, t)) (a s₀) * deriv (fun s => q (s, a s)) s₀ -
          (m / 2 * deriv (fun t => q (s₀, t)) (a s₀) ^ 2 + V (q (s₀, a s₀))) * a')) s₀ :=
  hasDerivAt_action_natural_movingEndpoints_on hV hU hq ha hb hqU hN

/-- The action of a free particle as a function of the end point and of the time
of arrival: `dS = p dx − E dT` with `p = m x / T` and `E = m x² / 2T²`. -/
example (m x ξ T τ : ℝ) (hT : T ≠ 0) :
    HasDerivAt (fun s => action 0 (T + s * τ) (natural m fun _ => 0)
        fun t => (x + s * ξ) * t / (T + s * τ))
      (m * x / T * ξ - m * x ^ 2 / (2 * T ^ 2) * τ) 0 :=
  hasDerivAt_action_free_endpoint m x ξ T τ hT

/-- A family of motions of the harmonic oscillator. -/
example (m k A B α β T τ : ℝ) :
    HasDerivAt (fun s => action 0 (T + s * τ) (natural m fun x => m * k ^ 2 / 2 * x ^ 2)
        fun t => (A + s * α) * Real.cos (k * t) + (B + s * β) * Real.sin (k * t))
      (m * (k * (B * Real.cos (k * T) - A * Real.sin (k * T))) *
            (α * Real.cos (k * T) + β * Real.sin (k * T)) +
          (m / 2 * (k * (B * Real.cos (k * T) - A * Real.sin (k * T))) ^ 2 -
            m * k ^ 2 / 2 * (A * Real.cos (k * T) + B * Real.sin (k * T)) ^ 2) * τ -
        m * (k * B) * α) 0 :=
  hasDerivAt_action_oscillator_family m k A B α β T τ

/-- The action of the oscillator as a function of the end point and of the time of
arrival, when the end point is not conjugate to the origin. -/
example (m k x ξ T τ : ℝ) (hT : Real.sin (k * T) ≠ 0) :
    HasDerivAt (fun s => action 0 (T + s * τ) (natural m fun y => m * k ^ 2 / 2 * y ^ 2)
        fun t => (x + s * ξ) * Real.sin (k * t) / Real.sin (k * (T + s * τ)))
      (m * k * x * Real.cos (k * T) / Real.sin (k * T) * ξ -
        m * k ^ 2 * x ^ 2 / (2 * Real.sin (k * T) ^ 2) * τ) 0 :=
  hasDerivAt_action_oscillator_endpoint m k x ξ T τ hT

end Potential
