/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAInos.Mechanics.JacobiMetric

/-! Typed contracts for Maupertuis' principle: the Jacobi length and its
derivative on the energy surface, the stationarity of the abbreviated action,
the change of the parameter for a Lagrangian that is homogeneous of degree one
in the velocity, the geodesics of the Jacobi metric, the existence of the
parameters, and a free particle. These examples use default elaborator
options. -/

open ProjectAInos ProjectAInos.Mechanics ProjectAInos.Mechanics.Maupertuis
open Set Filter MeasureTheory
open ContinuousLinearMap (inl inr fst snd)
open scoped Topology ContDiff

noncomputable section

section Parameter

example {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (c : ℝ) :
    ContDiff ℝ 2 (fun x => ∫ y in c..x, f y) ∧
      ∀ x, HasDerivAt (fun x => ∫ y in c..x, f y) (f x) x :=
  Variational.contDiff_primitive hf c

end Parameter

section Maupertuis

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  {T : Q × Q → ℝ} {U : Q → ℝ} {E : ℝ}
variable {z : Q × Q} {T' : Q × Q →L[ℝ] ℝ} {U' : Q →L[ℝ] ℝ} {q : ℝ → Q} {a b t : ℝ}

example (T : Q × Q → ℝ) (U : Q → ℝ) :
    naturalLagrangian T U =
      fun _ z => T z - U z.1 := rfl

example (T : Q × Q → ℝ) (U : Q → ℝ) (E : ℝ) (z : Q × Q) :
    radicand T U E z =
      (E - U z.1) * T z := rfl

example (T : Q × Q → ℝ) (U : Q → ℝ) (E : ℝ) :
    jacobiLength T U E =
      fun _ z => 2 * √(radicand T U E z) := rfl

example (T : Q × Q → ℝ) (U : Q → ℝ) (E : ℝ) :
    jacobiEnergy T U E =
      fun _ z => 2 * radicand T U E z := rfl

example (hT : ContDiff ℝ 2 T) (hU : ContDiff ℝ 2 U) :
    ContDiff ℝ 2 (radicand T U E) :=
  contDiff_radicand hT hU

example (hT : HasFDerivAt T T' z) (hU : HasFDerivAt U U' z.1) :
    HasFDerivAt (radicand T U E) ((E - U z.1) • T' - T z • U'.comp (fst ℝ Q Q)) z :=
  hasFDerivAt_radicand hT hU

example (hT : HasFDerivAt T T' z) (hU : HasFDerivAt U U' z.1)
    (hpos : 0 < radicand T U E z) (t : ℝ) :
    HasFDerivAt (jacobiLength T U E t)
      ((1 / √(radicand T U E z)) • ((E - U z.1) • T' - T z • U'.comp (fst ℝ Q Q))) z :=
  hasFDerivAt_jacobiLength hT hU hpos t

example (hE : T z + U z.1 = E) :
    radicand T U E z = (E - U z.1) ^ 2 :=
  radicand_eq_sq hE

example (hE : T z + U z.1 = E) (hlt : U z.1 < E) :
    0 < radicand T U E z :=
  radicand_pos hE hlt

example (hT : HasFDerivAt T T' z) (hU : HasFDerivAt U U' z.1)
    (hE : T z + U z.1 = E) (hlt : U z.1 < E) (t : ℝ) :
    HasFDerivAt (jacobiLength T U E t) (T' - U'.comp (fst ℝ Q Q)) z :=
  hasFDerivAt_jacobiLength_shell hT hU hE hlt t

example (hT : HasFDerivAt T T' z) (hU : HasFDerivAt U U' z.1)
    (t : ℝ) :
    HasFDerivAt (naturalLagrangian T U t) (T' - U'.comp (fst ℝ Q Q)) z :=
  hasFDerivAt_naturalLagrangian hT hU t

example (hT : DifferentiableAt ℝ T z) (hU : DifferentiableAt ℝ U z.1)
    (hE : T z + U z.1 = E) (hlt : U z.1 < E) (t : ℝ) :
    fderiv ℝ (jacobiLength T U E t) z = fderiv ℝ (naturalLagrangian T U t) z :=
  fderiv_jacobiLength_eq hT hU hE hlt t

example (hE : T z + U z.1 = E) (hlt : U z.1 < E) (t : ℝ) :
    jacobiLength T U E t z = 2 * T z :=
  jacobiLength_eq_two_mul hE hlt t

example (hT : Differentiable ℝ T) (hU : Differentiable ℝ U)
    (hE : ∀ᶠ s in 𝓝 t, T (q s, deriv q s) + U (q s) = E ∧ U (q s) < E) :
    eulerLagrange (jacobiLength T U E) q t = eulerLagrange (naturalLagrangian T U) q t :=
  eulerLagrange_jacobiLength_eq hT hU hE

example (hE : ∀ t ∈ uIcc a b, T (q t, deriv q t) + U (q t) = E ∧ U (q t) < E) :
    action a b (jacobiLength T U E) q = ∫ t in a..b, 2 * T (q t, deriv q t) :=
  action_jacobiLength hE

example [FiniteDimensional ℝ Q] (hab : a < b)
    (hT : ContDiff ℝ 2 T) (hU : ContDiff ℝ 2 U) (hq : ContDiff ℝ 2 q)
    (hE : ∀ t ∈ Icc a b, T (q t, deriv q t) + U (q t) = E ∧ U (q t) < E) :
    Stationary a b (jacobiLength T U E) q ↔
      ∀ t ∈ Ioo a b, eulerLagrange (naturalLagrangian T U) q t = 0 :=
  stationary_jacobiLength_iff hab hT hU hq hE

example (T : Q × Q → ℝ) :
    IsHomogeneousTwo T =
      ∀ (q w : Q) (c : ℝ), T (q, c • w) = c ^ 2 * T (q, w) := rfl

example (hT : IsHomogeneousTwo T) {q w : Q}
    (hd : DifferentiableAt ℝ T (q, w)) :
    fderiv ℝ T (q, w) (0, w) = 2 * T (q, w) :=
  IsHomogeneousTwo.fderiv_velocity hT hd

example (hT : IsHomogeneousTwo T) (hd : Differentiable ℝ T)
    (hU : Differentiable ℝ U) (t : ℝ) :
    momentum (naturalLagrangian T U) q t (deriv q t) = 2 * T (q t, deriv q t) :=
  momentum_naturalLagrangian_apply hT hd hU t

example (hT : IsHomogeneousTwo T)
    (hd : Differentiable ℝ T) (hU : Differentiable ℝ U)
    (hE : ∀ t ∈ uIcc a b, T (q t, deriv q t) + U (q t) = E ∧ U (q t) < E) :
    action a b (jacobiLength T U E) q =
      ∫ t in a..b, momentum (naturalLagrangian T U) q t (deriv q t) :=
  action_jacobiLength_eq_integral_momentum hT hd hU hE

end Maupertuis

section JacobiMetric

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  {T : Q × Q → ℝ} {U : Q → ℝ} {E : ℝ}
variable {z : Q × Q} {T' : Q × Q →L[ℝ] ℝ} {U' : Q →L[ℝ] ℝ} {q γ : ℝ → Q} {σ : ℝ → ℝ} {t : ℝ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

example (Λ : Q × Q → ℝ) :
    IsHomogeneousOne Λ =
      ∀ (q w : Q) (c : ℝ), 0 < c → Λ (q, c • w) = c * Λ (q, w) := rfl

example {Λ : Q × Q → ℝ} (hΛ : IsHomogeneousOne Λ) {q w : Q}
    {c : ℝ} (hc : 0 < c) (hd : DifferentiableAt ℝ Λ (q, c • w)) :
    (fderiv ℝ Λ (q, c • w)).comp (inl ℝ Q Q) = c • (fderiv ℝ Λ (q, w)).comp (inl ℝ Q Q) ∧
      (fderiv ℝ Λ (q, c • w)).comp (inr ℝ Q Q) = (fderiv ℝ Λ (q, w)).comp (inr ℝ Q Q) :=
  IsHomogeneousOne.fderiv_smul hΛ hc hd

example {L : Lagrangian Q} {q₁ q₂ : ℝ → Q} {t : ℝ}
    (h : q₁ =ᶠ[𝓝 t] q₂) :
    eulerLagrange L q₁ t = eulerLagrange L q₂ t :=
  eulerLagrange_congr h

example {Λ : Q × Q → ℝ} (hΛ : IsHomogeneousOne Λ) {γ : ℝ → Q}
    {σ : ℝ → ℝ} {t : ℝ} (hpos : ∀ᶠ s in 𝓝 t, 0 < deriv σ s)
    (hγ : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ γ (σ s))
    (hd : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ Λ (γ (σ s), deriv σ s • deriv γ (σ s)))
    (hm : DifferentiableAt ℝ (momentum (fun _ => Λ) γ) (σ t)) :
    eulerLagrange (fun _ => Λ) (γ ∘ σ) t =
      deriv σ t • eulerLagrange (fun _ => Λ) γ (σ t) :=
  eulerLagrange_comp hΛ hpos hγ hd hm

example (hT : IsHomogeneousTwo T) (t : ℝ) :
    IsHomogeneousOne (jacobiLength T U E t) :=
  isHomogeneousOne_jacobiLength hT t

example (hT : HasFDerivAt T T' z) (hU : HasFDerivAt U U' z.1)
    (t : ℝ) :
    HasFDerivAt (jacobiEnergy T U E t)
      ((2 : ℝ) • ((E - U z.1) • T' - T z • U'.comp (fst ℝ Q Q))) z :=
  hasFDerivAt_jacobiEnergy hT hU t

example (hT : DifferentiableAt ℝ T z) (hU : DifferentiableAt ℝ U z.1)
    (hpos : 0 < radicand T U E z) (t : ℝ) :
    fderiv ℝ (jacobiEnergy T U E t) z =
      jacobiLength T U E t z • fderiv ℝ (jacobiLength T U E t) z :=
  fderiv_jacobiEnergy_eq hT hU hpos t

example (hT : Differentiable ℝ T) (hU : Differentiable ℝ U)
    {γ : ℝ → Q} {x ℓ₀ : ℝ}
    (hℓ : ∀ᶠ y in 𝓝 x, 0 < radicand T U E (γ y, deriv γ y) ∧
      jacobiLength T U E y (γ y, deriv γ y) = ℓ₀)
    (hm : DifferentiableAt ℝ (momentum (jacobiLength T U E) γ) x) :
    eulerLagrange (jacobiEnergy T U E) γ x =
      ℓ₀ • eulerLagrange (jacobiLength T U E) γ x :=
  eulerLagrange_jacobiEnergy_eq hT hU hℓ hm

example {z : Q × Q} {t : ℝ}
    (h : jacobiLength T U E t z = 1) :
    0 < radicand T U E z :=
  radicand_pos_of_jacobiLength_eq_one h

example (hT2 : IsHomogeneousTwo T) (hU : Continuous U)
    (hqc : ContinuousAt q t)
    (hE : ∀ᶠ s in 𝓝 t, T (q s, deriv q s) + U (q s) = E ∧ U (q s) < E)
    (hσ : ∀ᶠ s in 𝓝 t, HasDerivAt σ (2 * (E - U (q s))) s)
    (hqγ : ∀ᶠ s in 𝓝 t, q s = γ (σ s))
    (hγ : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ γ (σ s)) :
    ∀ᶠ x in 𝓝 (σ t), jacobiLength T U E x (γ x, deriv γ x) = 1 :=
  eventually_jacobiLength_eq_one hT2 hU hqc hE hσ hqγ hγ

example (hT2 : IsHomogeneousTwo T) (hT : Differentiable ℝ T)
    (hU : Differentiable ℝ U) (hqc : ContinuousAt q t)
    (hE : ∀ᶠ s in 𝓝 t, T (q s, deriv q s) + U (q s) = E ∧ U (q s) < E)
    (hσ : ∀ᶠ s in 𝓝 t, HasDerivAt σ (2 * (E - U (q s))) s)
    (hqγ : ∀ᶠ s in 𝓝 t, q s = γ (σ s))
    (hγ : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ γ (σ s))
    (hm : DifferentiableAt ℝ (momentum (jacobiLength T U E) γ) (σ t)) :
    eulerLagrange (naturalLagrangian T U) q t =
      (2 * (E - U (q t))) • eulerLagrange (jacobiEnergy T U E) γ (σ t) :=
  eulerLagrange_eq_smul_jacobiEnergy hT2 hT hU hqc hE hσ hqγ hγ hm

example (hT : ContDiff ℝ 2 T) (hU : ContDiff ℝ 2 U)
    {γ : ℝ → Q} {x : ℝ} (hγ : ContDiffAt ℝ 2 γ x)
    (hpos : 0 < radicand T U E (γ x, deriv γ x)) :
    DifferentiableAt ℝ (momentum (jacobiLength T U E) γ) x :=
  differentiableAt_momentum_jacobiLength hT hU hγ hpos

example (hT2 : IsHomogeneousTwo T) (hT : ContDiff ℝ 2 T)
    (hU : ContDiff ℝ 2 U) {q : ℝ → Q} (hq : ContDiff ℝ 2 q) {a b : ℝ}
    (hE : ∀ t ∈ Ioo a b, T (q t, deriv q t) + U (q t) = E ∧ U (q t) < E) :
    ∃ (σ : ℝ → ℝ) (γ : ℝ → Q), (∀ t ∈ Ioo a b, HasDerivAt σ (2 * (E - U (q t))) t) ∧
      (∀ t ∈ Ioo a b, γ (σ t) = q t) ∧
      (∀ t ∈ Ioo a b, ∀ᶠ x in 𝓝 (σ t), jacobiLength T U E x (γ x, deriv γ x) = 1) ∧
      ∀ t ∈ Ioo a b, eulerLagrange (naturalLagrangian T U) q t =
        (2 * (E - U (q t))) • eulerLagrange (jacobiEnergy T U E) γ (σ t) :=
  exists_jacobi_parameter hT2 hT hU hq hE

example (hT2 : IsHomogeneousTwo T) (hT : ContDiff ℝ 2 T)
    (hU : ContDiff ℝ 2 U) {γ : ℝ → Q} (hγ : ContDiff ℝ 2 γ) {c d : ℝ}
    (hunit : ∀ x ∈ Ioo c d, jacobiLength T U E x (γ x, deriv γ x) = 1 ∧ U (γ x) < E) :
    ∃ (τ : ℝ → ℝ) (q : ℝ → Q),
      (∀ x ∈ Ioo c d, HasDerivAt τ (1 / (2 * (E - U (γ x)))) x) ∧
      (∀ x ∈ Ioo c d, q (τ x) = γ x) ∧
      (∀ x ∈ Ioo c d, ∀ᶠ s in 𝓝 (τ x), T (q s, deriv q s) + U (q s) = E ∧ U (q s) < E) ∧
      ∀ x ∈ Ioo c d, eulerLagrange (naturalLagrangian T U) q (τ x) =
        (2 * (E - U (γ x))) • eulerLagrange (jacobiEnergy T U E) γ x :=
  exists_motion_of_jacobi_geodesic hT2 hT hU hγ hunit

example (m : ℝ) (z : V × V) :
    kineticEnergy m z =
      m / 2 * ‖z.2‖ ^ 2 := rfl

example (m : ℝ) :
    ContDiff ℝ 2 (kineticEnergy (V := V) m) :=
  contDiff_kineticEnergy m

example (m : ℝ) :
    IsHomogeneousTwo (kineticEnergy (V := V) m) :=
  isHomogeneousTwo_kineticEnergy m

example (x₀ v : V) (s : ℝ) :
    deriv (fun s : ℝ => x₀ + s • v) s = v :=
  deriv_line x₀ v s

example (m : ℝ) (x₀ v : V) (t : ℝ) :
    eulerLagrange (naturalLagrangian (kineticEnergy m) fun _ => 0)
      (fun s : ℝ => x₀ + s • v) t = 0 :=
  eulerLagrange_line m x₀ v t

example [FiniteDimensional ℝ V] {m : ℝ} (hm : 0 < m) (x₀ : V)
    {v : V} (hv : v ≠ 0) {a b : ℝ} (hab : a < b) :
    Stationary a b (jacobiLength (kineticEnergy m) (fun _ => 0) (m / 2 * ‖v‖ ^ 2))
      fun s : ℝ => x₀ + s • v :=
  stationary_jacobiLength_line hm x₀ hv hab

end JacobiMetric
