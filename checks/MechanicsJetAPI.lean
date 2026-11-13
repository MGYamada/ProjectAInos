/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAInos

/-! Public consumers of the jet-ring API of mechanics. Default elaborator options
are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section
open ProjectAInos.SmoothAlgebra ProjectAInos.SmoothAlgebra.SmoothRing ProjectAInos.Mechanics
open Matrix

section FreeDerivation

variable {ι : Type*}

example (w : ι → FreeSmoothRing ι) (i : ι) :
    FreeSmoothRing.derivation w (FreeSmoothRing.generator i) = w i :=
  FreeSmoothRing.derivation_generator w i

example {M : Type*} [AddCommGroup M] [Module (FreeSmoothRing ι) M]
    {d e : SmoothDerivation (FreeSmoothRing ι) M}
    (h : ∀ i, d (FreeSmoothRing.generator i) = e (FreeSmoothRing.generator i)) : d = e :=
  FreeSmoothRing.derivation_ext h

example (d : SmoothDerivation (FreeSmoothRing ι) (FreeSmoothRing ι)) (i : ι) :
    FreeSmoothRing.derivationEquiv d i = d (FreeSmoothRing.generator i) := rfl

example [DecidableEq ι] (c c' : ι) (s : FreeSmoothRing ι) :
    FreeSmoothRing.partialDerivation c (FreeSmoothRing.partialDerivation c' s) =
      FreeSmoothRing.partialDerivation c' (FreeSmoothRing.partialDerivation c s) :=
  FreeSmoothRing.partialDerivation_comm c c' s

end FreeDerivation

section Abstract

variable {ι J : Type*} [CommRing J] [Algebra ℝ J] [SmoothRing J] [Fintype ι] (R : JetRing ι J)

example (F : J) {N : ℕ} (h : R.OrderLE F N) :
    R.totalDeriv F =
      R.dt F + ∑ k ∈ Finset.range (N + 1), ∑ i, R.q i (k + 1) * R.d i k F :=
  JetRing.totalDeriv_eq_sum h

example {n : ℕ} (f : SmoothOperation n) (a : Fin n → J) :
    R.totalDeriv (op f a) = ∑ j, op (SmoothOperation.partialDeriv j f) a • R.totalDeriv (a j) :=
  R.totalDeriv.chain f a

example (i : ι) (k : ℕ) : R.totalDeriv (R.q i k) = R.q i (k + 1) := JetRing.totalDeriv_q i k

example (F : J) : R.dt (R.totalDeriv F) = R.totalDeriv (R.dt F) := JetRing.dt_totalDeriv F

example (j : ι) (F : J) : R.d j 0 (R.totalDeriv F) = R.totalDeriv (R.d j 0 F) :=
  JetRing.d_zero_totalDeriv j F

example (j : ι) (m : ℕ) (F : J) :
    R.d j (m + 1) (R.totalDeriv F) = R.totalDeriv (R.d j (m + 1) F) + R.d j m F :=
  JetRing.d_succ_totalDeriv j m F

example {F : J} {N : ℕ} (h : R.OrderLE F N) : R.OrderLE (R.totalDeriv F) (N + 1) := h.totalDeriv

example {F : J} {N : ℕ} (h : R.OrderLE F N) (i : ι) :
    R.euler i F =
      ∑ k ∈ Finset.range (N + 1), (-1 : J) ^ k * (R.totalDeriv^[k]) (R.d i k F) :=
  JetRing.euler_eq_sum h i

example (i : ι) (F : J) : R.euler i (R.totalDeriv F) = 0 := JetRing.euler_totalDeriv i F

example (i : ι) (L F : J) : R.euler i (L + R.totalDeriv F) = R.euler i L :=
  JetRing.euler_add_totalDeriv i L F

example {L x : J} (hx : x ∈ R.eulerLagrangeIdeal L) : R.totalDeriv x ∈ R.eulerLagrangeIdeal L :=
  JetRing.totalDeriv_mem_eulerLagrangeIdeal hx

example (L F : J) : R.Conserved L F ↔ R.totalDeriv F ∈ R.eulerLagrangeIdeal L := Iff.rfl

example {L : J} (hL : R.OrderLE L 1) (i : ι) :
    R.euler i L = R.d i 0 L - R.totalDeriv (R.momentum L i) :=
  JetRing.euler_of_orderLE_one hL i

example {L : J} (hL : R.OrderLE L 1) :
    R.totalDeriv (R.energy L) = -∑ i, R.q i 1 * R.euler i L - R.dt L :=
  JetRing.totalDeriv_energy hL

example {L : J} (hL : R.OrderLE L 1) (ξ : ι → J) :
    R.prolong ξ L = ∑ i, (ξ i * R.d i 0 L + R.totalDeriv (ξ i) * R.momentum L i) :=
  JetRing.prolong_of_orderLE_one hL ξ

example {L : J} (hL : R.OrderLE L 1) (ξ : ι → J) :
    R.prolong ξ L =
      ∑ i, ξ i * R.euler i L + R.totalDeriv (∑ i, ξ i * R.momentum L i) :=
  JetRing.prolong_eq_euler_add_totalDeriv hL ξ

example (L : J) (i : ι) : R.momentum L i = R.d i 1 L := rfl

example (L : J) : R.energy L = ∑ i, R.q i 1 * R.momentum L i - L := rfl

example {L F : J} (hL : R.OrderLE L 1) (ξ : ι → J) (h : R.prolong ξ L = R.totalDeriv F) :
    R.Conserved L (∑ i, ξ i * R.momentum L i - F) := JetRing.conserved_noetherCharge hL ξ h

example {L : J} (hL : R.OrderLE L 1) (ht : R.dt L = 0) : R.Conserved L (R.energy L) :=
  JetRing.conserved_energy hL ht

example (m : ι → ℝ) {U : J} (hU : R.OrderLE U 0) (j : ι) :
    R.euler j (R.naturalLagrangian m U) = -R.d j 0 U - algebraMap ℝ J (m j) * R.q j 2 :=
  JetRing.euler_naturalLagrangian m hU j

example (m : ι → ℝ) {U : J} (hU : R.OrderLE U 0) (ht : R.dt U = 0) :
    R.Conserved (R.naturalLagrangian m U)
      (∑ i, algebraMap ℝ J (m i / 2) * (R.q i 1 * R.q i 1) + U) :=
  JetRing.conserved_energy_naturalLagrangian m hU ht

example (m : ι → ℝ) {U : J} (hU : R.OrderLE U 0) (u : ι → ℝ)
    (hinv : ∑ i, algebraMap ℝ J (u i) * R.d i 0 U = 0) :
    R.Conserved (R.naturalLagrangian m U)
      (∑ i, algebraMap ℝ J (u i) * (algebraMap ℝ J (m i) * R.q i 1)) :=
  JetRing.conserved_momentum m hU u hinv

example (m : ι → ℝ) {U : J} (hU : R.OrderLE U 0) {τ : J} (hτt : R.dt τ = 1)
    (hτq : ∀ i k, R.d i k τ = 0) (u : ι → ℝ)
    (hinv : ∑ i, algebraMap ℝ J (u i) * R.d i 0 U = 0) :
    R.Conserved (R.naturalLagrangian m U)
      (∑ i, τ * algebraMap ℝ J (u i) * (algebraMap ℝ J (m i) * R.q i 1) -
        ∑ i, algebraMap ℝ J (u i) * (algebraMap ℝ J (m i) * R.q i 0)) :=
  JetRing.conserved_boost m hU hτt hτq u hinv

example (m : ι → ℝ) {U : J} (hU : R.OrderLE U 0) (A : ι → ι → ℝ)
    (hA : ∀ i j, m i * A i j + m j * A j i = 0)
    (hinv : ∑ i, (∑ j, algebraMap ℝ J (A i j) * R.q j 0) * R.d i 0 U = 0) :
    R.Conserved (R.naturalLagrangian m U)
      (∑ i, (∑ j, algebraMap ℝ J (A i j) * R.q j 0) * (algebraMap ℝ J (m i) * R.q i 1)) :=
  JetRing.conserved_linear m hU A hA hinv

end Abstract

section AngularMomentum

variable {κ J : Type*} [CommRing J] [Algebra ℝ J] [SmoothRing J] [Fintype κ]
  (R : JetRing (κ × Fin 3) J)

example (M : κ → ℝ) {U : J} (hU : R.OrderLE U 0) (n : Fin 3 → ℝ)
    (hinv : ∑ a, ∑ r, (JetRing.axis J n ⨯₃ R.position a) r * R.d (a, r) 0 U = 0) :
    R.Conserved (R.naturalLagrangian (fun i => M i.1) U)
      (∑ a, ∑ r, (JetRing.axis J n ⨯₃ R.position a) r *
        (algebraMap ℝ J (M a) * R.velocity a r)) :=
  JetRing.conserved_angularMomentum M hU n hinv

example (n : Fin 3 → ℝ) (x p : Fin 3 → J) :
    ∑ r, (JetRing.axis J n ⨯₃ x) r * p r = JetRing.axis J n ⬝ᵥ (x ⨯₃ p) :=
  JetRing.axis_cross_dotProduct n x p

end AngularMomentum

section Standard

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

example : JetRing ι (StandardJet ι) := StandardJet.jetRing ι

example : (StandardJet.jetRing ι).totalDeriv (StandardJet.time ι) = 1 :=
  StandardJet.totalDeriv_time

example (i : ι) :
    (StandardJet.jetRing ι).euler i
        ((StandardJet.jetRing ι).q i 0 * (StandardJet.jetRing ι).q i 2) =
      2 * (StandardJet.jetRing ι).q i 2 :=
  StandardJet.euler_q_mul_acceleration i

example (i : ι) :
    (StandardJet.jetRing ι).euler i
        ((StandardJet.jetRing ι).q i 1 * (StandardJet.jetRing ι).q i 1) =
      -(2 * (StandardJet.jetRing ι).q i 2) :=
  StandardJet.euler_velocity_sq i

example (m : ι → ℝ) (k : ℝ) (j : ι) :
    (StandardJet.jetRing ι).d j 2 ((StandardJet.jetRing ι).euler j
        ((StandardJet.jetRing ι).naturalLagrangian m (StandardJet.oscillatorPotential k))) =
      -algebraMap ℝ (StandardJet ι) (m j) :=
  StandardJet.d_two_euler_oscillator m k j

example (m : ι → ℝ) (k : ℝ) :
    (StandardJet.jetRing ι).Conserved
      ((StandardJet.jetRing ι).naturalLagrangian m (StandardJet.oscillatorPotential k))
      (∑ i, algebraMap ℝ (StandardJet ι) (m i / 2) *
          ((StandardJet.jetRing ι).q i 1 * (StandardJet.jetRing ι).q i 1) +
        StandardJet.oscillatorPotential k) :=
  StandardJet.conserved_energy_oscillator m k

end Standard

section Prolongation

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

example (γ : ι → TimeFunction) (i : ι) (k : ℕ) :
    StandardJet.prolongation γ ((StandardJet.jetRing ι).q i k) = (timeDerivative^[k]) (γ i) :=
  StandardJet.prolongation_q γ i k

example (f : TimeFunction) : timeDerivative f = SmoothOperation.partialDeriv 0 f := rfl

/-- The prolongation turns the total derivative into `d/dt`. -/
example (γ : ι → TimeFunction) (F : StandardJet ι) :
    StandardJet.prolongation γ ((StandardJet.jetRing ι).totalDeriv F) =
      timeDerivative (StandardJet.prolongation γ F) :=
  StandardJet.prolongation_totalDeriv γ F

/-- A solution is a path whose prolongation kills the Euler–Lagrange expressions. -/
example (L : StandardJet ι) (γ : ι → TimeFunction) :
    StandardJet.IsSolution L γ ↔
      ∀ i, StandardJet.prolongation γ ((StandardJet.jetRing ι).euler i L) = 0 :=
  Iff.rfl

/-- Conservation along trajectories. -/
example {L F : StandardJet ι} {γ : ι → TimeFunction} (h : StandardJet.IsSolution L γ)
    (hF : (StandardJet.jetRing ι).Conserved L F) (s t : Fin 1 → ℝ) :
    StandardJet.prolongation γ F s = StandardJet.prolongation γ F t :=
  StandardJet.prolongation_eq_of_conserved h hF s t

/-- Solutions of a natural Lagrangian are solutions of Newton's equations. -/
example (m : ι → ℝ) (k : ℝ) (γ : ι → TimeFunction) :
    StandardJet.IsSolution
        ((StandardJet.jetRing ι).naturalLagrangian m (StandardJet.oscillatorPotential k)) γ ↔
      ∀ i, algebraMap ℝ TimeFunction (m i) * (timeDerivative^[2]) (γ i) =
        -(algebraMap ℝ TimeFunction k * γ i) :=
  StandardJet.isSolution_oscillator_iff m k γ

/-- Conservation of energy along trajectories. -/
example (m : ι → ℝ) {U : StandardJet ι} (hU : (StandardJet.jetRing ι).OrderLE U 0)
    (ht : (StandardJet.jetRing ι).dt U = 0) {γ : ι → TimeFunction}
    (h : StandardJet.IsSolution ((StandardJet.jetRing ι).naturalLagrangian m U) γ)
    (s t : Fin 1 → ℝ) :
    (∑ i, algebraMap ℝ TimeFunction (m i / 2) * (timeDerivative (γ i) * timeDerivative (γ i)) +
        StandardJet.prolongation γ U) s =
      (∑ i, algebraMap ℝ TimeFunction (m i / 2) *
          (timeDerivative (γ i) * timeDerivative (γ i)) + StandardJet.prolongation γ U) t :=
  StandardJet.energy_eq_of_isSolution m hU ht h s t

/-- Solutions exist: uniform motion solves the free equations. -/
example (m a b : ι → ℝ) :
    StandardJet.IsSolution ((StandardJet.jetRing ι).naturalLagrangian m 0)
      (StandardJet.uniformMotion a b) :=
  StandardJet.isSolution_uniformMotion m a b

example (a b : ι → ℝ) (i : ι) (t : Fin 1 → ℝ) :
    StandardJet.uniformMotion a b i t = a i + b i * t 0 := rfl

/-- `timeDerivative` is the ordinary derivative of a function of a real variable. -/
example (f : TimeFunction) (t : ℝ) :
    timeDerivative f (fun _ => t) = deriv (fun s : ℝ => f (fun _ => s)) t :=
  TimeFunction.timeDerivative_apply f t

end Prolongation
