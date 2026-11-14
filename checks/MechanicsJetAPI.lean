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

section Analytic

variable {n : ℕ}

example (f : SmoothOperation (n + n + 1)) :
    StandardJet.firstOrder f = op f (StandardJet.firstOrderCoordinates n) := rfl

example (γ : Fin n → TimeFunction) (t : ℝ) (i : Fin n) :
    StandardJet.realPath γ t i = γ i (fun _ => t) := rfl

/-- The prolonged Lagrangian is the analytic Lagrangian along the path. -/
example (f : SmoothOperation (n + n + 1)) (γ : Fin n → TimeFunction) (t : ℝ) :
    StandardJet.prolongation γ (StandardJet.firstOrder f) (fun _ => t) =
      ofSmoothOperation f t (StandardJet.realPath γ t, deriv (StandardJet.realPath γ) t) :=
  StandardJet.prolongation_firstOrder_apply f γ t

/-- The prolonged Euler operator is the analytic Euler–Lagrange residual. -/
example (f : SmoothOperation (n + n + 1)) (γ : Fin n → TimeFunction) (i : Fin n) (t : ℝ) :
    StandardJet.prolongation γ
        ((StandardJet.jetRing (Fin n)).euler i (StandardJet.firstOrder f)) (fun _ => t) =
      eulerLagrange (ofSmoothOperation f) (StandardJet.realPath γ) t (Pi.single i 1) :=
  StandardJet.prolongation_euler_firstOrder_apply f γ i t

/-- Solutions in the jet ring are the stationary paths of the action. -/
example (f : SmoothOperation (n + n + 1)) (γ : Fin n → TimeFunction) :
    StandardJet.IsSolution (StandardJet.firstOrder f) γ ↔
      ∀ a b : ℝ, a < b →
        Stationary a b (ofSmoothOperation f) (StandardJet.realPath γ) :=
  StandardJet.isSolution_firstOrder_iff_stationary f γ

/-- Conserved elements are constant along stationary paths. -/
example {f : SmoothOperation (n + n + 1)} {F : StandardJet (Fin n)} {γ : Fin n → TimeFunction}
    (h : ∀ a b : ℝ, a < b →
      Stationary a b (ofSmoothOperation f) (StandardJet.realPath γ))
    (hF : (StandardJet.jetRing (Fin n)).Conserved (StandardJet.firstOrder f) F)
    (s t : Fin 1 → ℝ) :
    StandardJet.prolongation γ F s = StandardJet.prolongation γ F t :=
  StandardJet.prolongation_eq_of_stationary h hF s t

/-- Conservation of energy along stationary paths of a time-independent Lagrangian. -/
example {f : SmoothOperation (n + n + 1)} (hf : SmoothOperation.partialDeriv 0 f = 0)
    {γ : Fin n → TimeFunction}
    (h : ∀ a b : ℝ, a < b →
      Stationary a b (ofSmoothOperation f) (StandardJet.realPath γ)) (s t : ℝ) :
    ∑ i, deriv (StandardJet.realPath γ) s i *
          SmoothOperation.partialDeriv (StandardJet.velocityIndex i) f
            (StandardJet.realJet γ s) - f (StandardJet.realJet γ s) =
      ∑ i, deriv (StandardJet.realPath γ) t i *
          SmoothOperation.partialDeriv (StandardJet.velocityIndex i) f
            (StandardJet.realJet γ t) - f (StandardJet.realJet γ t) :=
  StandardJet.energy_eq_of_stationary hf h s t

example (γ : Fin n → TimeFunction) (t : ℝ) :
    StandardJet.realJet γ t =
      Fin.cons t (Fin.append (StandardJet.realPath γ t) (deriv (StandardJet.realPath γ) t)) :=
  rfl

end Analytic

section KineticForm

variable {ι J : Type*} [CommRing J] [Algebra ℝ J] [SmoothRing J] [Fintype ι] [DecidableEq ι]
  (R : JetRing ι J) {a : ι → ι → J} {U : J}

example (a : ι → ι → J) (U : J) :
    R.metricLagrangian a U =
      algebraMap ℝ J (1 / 2) * (∑ i, ∑ k, a i k * (R.q i 1 * R.q k 1)) - U := rfl

/-- The momenta `pⱼ = Σₖ aⱼₖ vₖ`. -/
example (ha : ∀ i k, R.OrderLE (a i k) 0) (hsymm : ∀ i k, a i k = a k i)
    (hU : R.OrderLE U 0) (j : ι) :
    R.momentum (R.metricLagrangian a U) j = ∑ k, a j k * R.q k 1 :=
  JetRing.momentum_metricLagrangian ha hsymm hU j

/-- Lagrange's equations. -/
example (ha : ∀ i k, R.OrderLE (a i k) 0) (hsymm : ∀ i k, a i k = a k i)
    (hU : R.OrderLE U 0) (i : ι) :
    R.euler i (R.metricLagrangian a U) =
      -(∑ k, a i k * R.q k 2) -
          ∑ j, ∑ k, (R.d j 0 (a i k) - algebraMap ℝ J (1 / 2) * R.d i 0 (a j k)) *
            (R.q j 1 * R.q k 1) -
        ∑ k, R.dt (a i k) * R.q k 1 - R.d i 0 U :=
  JetRing.euler_metricLagrangian_eq ha hsymm hU i

/-- The energy is `½ Σ a v v + U`, and it is conserved. -/
example (ha : ∀ i k, R.OrderLE (a i k) 0) (hsymm : ∀ i k, a i k = a k i)
    (hU : R.OrderLE U 0) (hat : ∀ i k, R.dt (a i k) = 0) (hUt : R.dt U = 0) :
    R.energy (R.metricLagrangian a U) = algebraMap ℝ J (1 / 2) * R.kineticForm a + U ∧
      R.Conserved (R.metricLagrangian a U) (algebraMap ℝ J (1 / 2) * R.kineticForm a + U) :=
  ⟨JetRing.energy_metricLagrangian ha hsymm hU,
    JetRing.conserved_energy_metricLagrangian ha hsymm hU hat hUt⟩

/-- The energy in the momenta, for an inverse `b` of `a`. -/
example (ha : ∀ i k, R.OrderLE (a i k) 0) (hsymm : ∀ i k, a i k = a k i)
    (hU : R.OrderLE U 0) (b : ι → ι → J)
    (hb : ∀ i l, ∑ j, b i j * a j l = if i = l then 1 else 0) :
    R.energy (R.metricLagrangian a U) =
      algebraMap ℝ J (1 / 2) *
          ∑ i, ∑ j, b i j *
            (R.momentum (R.metricLagrangian a U) i * R.momentum (R.metricLagrangian a U) j) +
        U :=
  JetRing.energy_metricLagrangian_eq_inverse ha hsymm hU b hb

/-- Constant masses are the diagonal case. -/
example (m : ι → ℝ) (U : J) :
    R.metricLagrangian (fun i k => if i = k then algebraMap ℝ J (m i) else 0) U =
      R.naturalLagrangian m U :=
  JetRing.metricLagrangian_diagonal m U

/-- A cyclic co-ordinate has a conserved momentum. -/
example {L : J} (hL : R.OrderLE L 1) (i : ι) (h : R.d i 0 L = 0) :
    R.Conserved L (R.momentum L i) :=
  JetRing.conserved_momentum_of_cyclic hL i h

end KineticForm

section Polar

open StandardJet

example :
    Polar.metric = ![![1, 0], ![0, (jetRing (Fin 2)).q 0 0 * (jetRing (Fin 2)).q 0 0]] := rfl

/-- The radial equation has the centrifugal term. -/
example {U : StandardJet (Fin 2)} (hU : (jetRing (Fin 2)).OrderLE U 0) :
    (jetRing (Fin 2)).euler 0 (Polar.lagrangian U) =
      -(jetRing (Fin 2)).q 0 2 +
          Polar.radius * ((jetRing (Fin 2)).q 1 1 * (jetRing (Fin 2)).q 1 1) -
        (jetRing (Fin 2)).d 0 0 U :=
  Polar.euler_radial hU

example {U : StandardJet (Fin 2)} (hU : (jetRing (Fin 2)).OrderLE U 0) :
    (jetRing (Fin 2)).euler 1 (Polar.lagrangian U) =
      -(Polar.radius * Polar.radius * (jetRing (Fin 2)).q 1 2 +
          2 * Polar.radius * ((jetRing (Fin 2)).q 0 1 * (jetRing (Fin 2)).q 1 1)) -
        (jetRing (Fin 2)).d 1 0 U :=
  Polar.euler_angular hU

/-- Conservation of the angular momentum `r² φ̇`. -/
example {U : StandardJet (Fin 2)} (hU : (jetRing (Fin 2)).OrderLE U 0)
    (hφ : (jetRing (Fin 2)).d 1 0 U = 0) :
    (jetRing (Fin 2)).Conserved (Polar.lagrangian U)
      (Polar.radius * Polar.radius * (jetRing (Fin 2)).q 1 1) :=
  Polar.conserved_angularMomentum hU hφ

end Polar

section FreeParticle

open StandardJet

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- A vector field is a finite combination of the coordinate vector fields. -/
example {κ M : Type*} [DecidableEq κ] [AddCommGroup M] [Module (FreeSmoothRing κ) M]
    (E : SmoothDerivation (FreeSmoothRing κ) M) (s : FreeSmoothRing κ) :
    E s = ∑ a ∈ Finset.univ.image (FreeSmoothRing.presentation s).indices,
      FreeSmoothRing.partialDerivation a s • E (FreeSmoothRing.generator a) :=
  FreeSmoothRing.apply_eq_sum_partialDerivation E s

/-- An element of a free ring with vanishing partial derivatives is a constant. -/
example {κ : Type*} [DecidableEq κ] {s : FreeSmoothRing κ}
    (h : ∀ a, FreeSmoothRing.partialDerivation a s = 0) (x y : κ → ℝ) :
    FreeSmoothRing.lift x s = FreeSmoothRing.lift y s :=
  lift_eq_of_partialDerivation_eq_zero h x y

example {κ : Type*} [DecidableEq κ] {s : FreeSmoothRing κ}
    (h : ∀ a, FreeSmoothRing.partialDerivation a s = 0) (x₀ : κ → ℝ) :
    s = algebraMap ℝ (FreeSmoothRing κ) (FreeSmoothRing.lift x₀ s) :=
  eq_algebraMap_of_partialDerivation_eq_zero h x₀

example (L : StandardJet ι) :
    DependsOnVelocities L ↔
      (jetRing ι).dt L = 0 ∧ ∀ i k, k ≠ 1 → (jetRing ι).d i k L = 0 :=
  Iff.rfl

example (u : ι → ℝ) (L : StandardJet ι) :
    boost u L =
      (jetRing ι).prolong (fun i => time ι * algebraMap ℝ (StandardJet ι) (u i)) L :=
  rfl

example (L : StandardJet ι) :
    IsBoostQuasiInvariant L ↔
      ∀ u : ι → ℝ, ∃ F, (jetRing ι).OrderLE F 0 ∧ boost u L = (jetRing ι).totalDeriv F :=
  Iff.rfl

/-- On a function of the velocities the boost is `Σ uᵢ ∂/∂vᵢ`. -/
example {L : StandardJet ι} (hL : DependsOnVelocities L) (u : ι → ℝ) :
    boost u L = ∑ i, algebraMap ℝ (StandardJet ι) (u i) * (jetRing ι).d i 1 L :=
  boost_eq hL u

example (m : Matrix ι ι ℝ) (b : ι → ℝ) (c : ℝ) :
    velocityPolynomial m b c =
      ∑ i, ∑ j, algebraMap ℝ (StandardJet ι) (m i j / 2) *
          ((jetRing ι).q i 1 * (jetRing ι).q j 1) +
        ∑ i, algebraMap ℝ (StandardJet ι) (b i) * (jetRing ι).q i 1 +
          algebraMap ℝ (StandardJet ι) c :=
  rfl

/-- Landau–Lifshitz §4 (Theorem 66): quasi-invariance under boosts is being a
polynomial of degree at most two in the velocities. -/
example {L : StandardJet ι} (hL : DependsOnVelocities L) :
    IsBoostQuasiInvariant L ↔
      ∃ (m : Matrix ι ι ℝ) (b : ι → ℝ) (c : ℝ), m.IsSymm ∧ L = velocityPolynomial m b c :=
  isBoostQuasiInvariant_iff hL

/-- The terms of degree at most one are a total derivative. -/
example (m : Matrix ι ι ℝ) (b : ι → ℝ) (c : ℝ) :
    velocityPolynomial m b c =
      ∑ i, ∑ j, algebraMap ℝ (StandardJet ι) (m i j / 2) *
          ((jetRing ι).q i 1 * (jetRing ι).q j 1) +
        (jetRing ι).totalDeriv (∑ i, algebraMap ℝ (StandardJet ι) (b i) * (jetRing ι).q i 0 +
          algebraMap ℝ (StandardJet ι) c * time ι) :=
  velocityPolynomial_eq_add_totalDeriv m b c

example (L : StandardJet ι) (w : ι → ℝ) :
    velocityValue L w = FreeSmoothRing.lift (velocityPoint w) L := rfl

example (m : Matrix ι ι ℝ) (b : ι → ℝ) (c : ℝ) (w : ι → ℝ) :
    velocityValue (velocityPolynomial m b c) w = w ⬝ᵥ m *ᵥ w / 2 + b ⬝ᵥ w + c :=
  velocityValue_velocityPolynomial m b c w

example (L : StandardJet ι) :
    IsIsotropic L ↔
      ∀ A : Matrix ι ι ℝ, Aᵀ * A = 1 →
        ∀ w : ι → ℝ, velocityValue L (A *ᵥ w) = velocityValue L w :=
  Iff.rfl

example {m : Matrix ι ι ℝ} (hm : m.IsSymm) {b : ι → ℝ} {c : ℝ}
    (h : IsIsotropic (velocityPolynomial m b c)) :
    (∃ μ : ℝ, m = μ • (1 : Matrix ι ι ℝ)) ∧ b = 0 :=
  eq_smul_one_of_isIsotropic hm h

/-- Landau–Lifshitz §4: a function of the velocities that is quasi-invariant
under boosts and isotropic is `½ μ |v|² + c`. -/
example {L : StandardJet ι} (hL : DependsOnVelocities L) (hq : IsBoostQuasiInvariant L)
    (hiso : IsIsotropic L) :
    ∃ μ c : ℝ,
      L = (jetRing ι).naturalLagrangian (fun _ => μ) 0 + algebraMap ℝ (StandardJet ι) c :=
  exists_eq_of_isIsotropic hL hq hiso

/-- The finite boost of the free Lagrangian (Landau–Lifshitz (4.2)). -/
example (μ : ℝ) (u : ι → ℝ) :
    ∑ i, algebraMap ℝ (StandardJet ι) (μ / 2) *
          (((jetRing ι).q i 1 + algebraMap ℝ (StandardJet ι) (u i)) *
            ((jetRing ι).q i 1 + algebraMap ℝ (StandardJet ι) (u i))) -
        ∑ i, algebraMap ℝ (StandardJet ι) (μ / 2) * ((jetRing ι).q i 1 * (jetRing ι).q i 1) =
      (jetRing ι).totalDeriv
        (∑ i, algebraMap ℝ (StandardJet ι) (μ * u i) * (jetRing ι).q i 0 +
          algebraMap ℝ (StandardJet ι) (∑ i, μ / 2 * (u i * u i)) * time ι) :=
  freeLagrangian_boost μ u

end FreeParticle
