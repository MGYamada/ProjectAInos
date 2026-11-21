/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.Mechanics.Poisson.AsymmetricTop

/-! Typed contracts for the flow of a positive bounded field on the line,
Jacobi's elliptic functions, and the solution of Euler's equations for the
asymmetrical top by elliptic functions. These examples use default elaborator
options. -/

open ProjectAinos ProjectAinos.Mechanics ProjectAinos.Mechanics.RigidBody
open ProjectAinos.SmoothAlgebra ProjectAinos.SmoothAlgebra.FreeSmoothRing
open ProjectAinos.SmoothGeometry ProjectAinos.SmoothGeometry.NonlinearODE
open ProjectAinos.SmoothGeometry.JacobiElliptic
open Set MeasureTheory
open scoped Real ContDiff

noncomputable section

-- Existing clients can use the historical names together with the shared implementation.
example (k u : ℝ) : ProjectAinos.SmoothGeometry.JacobiElliptic.sn k u =
    ProjectAinos.SpecialFunctions.JacobiElliptic.sn k u := rfl

example (A B C p k : ℝ) : ProjectAinos.Mechanics.RigidBody.jacobiCurve A B C p k =
    ProjectAinos.SpecialFunctions.JacobiElliptic.jacobiCurve A B C p k := rfl

section ScalarFlow

variable {g : ℝ → ℝ}

example (hg : ContDiff ℝ ∞ g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    flowDomain g = univ :=
  flowDomain_eq_univ_of_abs_le hg hC

example (g : ℝ → ℝ) (φ : ℝ) :
    scalarTime g φ =
      ∫ s in (0 : ℝ)..φ, (g s)⁻¹ := rfl

example (hg : Continuous g) (hpos : ∀ x, 0 < g x) (φ : ℝ) :
    HasDerivAt (scalarTime g) (g φ)⁻¹ φ :=
  hasDerivAt_scalarTime hg hpos φ

example (hg : Continuous g) (hpos : ∀ x, 0 < g x) :
    StrictMono (scalarTime g) :=
  strictMono_scalarTime hg hpos

example (g : ℝ → ℝ) :
    scalarTime g 0 = 0 :=
  scalarTime_zero g

example (hg : ContDiff ℝ ∞ g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) (u : ℝ) :
    HasDerivAt (fun u => flow g (u, 0)) (g (flow g (u, 0))) u :=
  hasDerivAt_flow_zero hg hC u

example (hg : ContDiff ℝ ∞ g) (hpos : ∀ x, 0 < g x) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) (u : ℝ) :
    scalarTime g (flow g (u, 0)) = u :=
  scalarTime_flow hg hpos hC u

example (hg : ContDiff ℝ ∞ g) (hpos : ∀ x, 0 < g x) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) (φ : ℝ) :
    flow g (scalarTime g φ, 0) = φ :=
  flow_scalarTime hg hpos hC φ

example (hg : ContDiff ℝ ∞ g) (hpos : ∀ x, 0 < g x) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) :
    StrictMono fun u => flow g (u, 0) :=
  strictMono_flow_zero hg hpos hC

example (hg : Continuous g) (hpos : ∀ x, 0 < g x) {P : ℝ}
    (hP : ∀ x, g (x + P) = g x) (φ : ℝ) :
    scalarTime g (φ + P) = scalarTime g φ + scalarTime g P :=
  scalarTime_add_of_periodic hg hpos hP φ

example (hg : ContDiff ℝ ∞ g) (hpos : ∀ x, 0 < g x) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) {P : ℝ} (hP : ∀ x, g (x + P) = g x) (u : ℝ) :
    flow g (u + scalarTime g P, 0) = flow g (u, 0) + P :=
  flow_add_scalarTime_of_periodic hg hpos hC hP u

end ScalarFlow

section JacobiElliptic

variable {k : ℝ}

example (k φ : ℝ) :
    amplitudeField k φ =
      √(1 - k ^ 2 * Real.sin φ ^ 2) := rfl

example (hk : k ^ 2 < 1) (φ : ℝ) :
    0 < 1 - k ^ 2 * Real.sin φ ^ 2 :=
  one_sub_pos hk φ

example (hk : k ^ 2 < 1) (φ : ℝ) :
    0 < amplitudeField k φ :=
  amplitudeField_pos hk φ

example (hk : k ^ 2 < 1) (φ : ℝ) :
    amplitudeField k φ ^ 2 = 1 - k ^ 2 * Real.sin φ ^ 2 :=
  amplitudeField_sq hk φ

example (k φ : ℝ) :
    |amplitudeField k φ| ≤ 1 :=
  abs_amplitudeField_le k φ

example (k φ : ℝ) :
    amplitudeField k (φ + π) = amplitudeField k φ :=
  amplitudeField_add_pi k φ

example (hk : k ^ 2 < 1) :
    ContDiff ℝ ∞ (amplitudeField k) :=
  contDiff_amplitudeField hk

example (hk : k ^ 2 < 1) (φ : ℝ) :
    HasDerivAt (amplitudeField k)
      (-(k ^ 2 * Real.sin φ * Real.cos φ) / amplitudeField k φ) φ :=
  hasDerivAt_amplitudeField hk φ

example (k u : ℝ) :
    am k u =
      flow (amplitudeField k) (u, 0) := rfl

example (k u : ℝ) :
    sn k u =
      Real.sin (am k u) := rfl

example (k u : ℝ) :
    cn k u =
      Real.cos (am k u) := rfl

example (k u : ℝ) :
    dn k u =
      amplitudeField k (am k u) := rfl

example (k : ℝ) :
    halfPeriod k =
      scalarTime (amplitudeField k) π := rfl

example (k : ℝ) :
    am k 0 = 0 :=
  am_zero k

example (k : ℝ) :
    sn k 0 = 0 :=
  sn_zero k

example (k : ℝ) :
    cn k 0 = 1 :=
  cn_zero k

example (k : ℝ) :
    dn k 0 = 1 :=
  dn_zero k

example (k u : ℝ) :
    sn k u ^ 2 + cn k u ^ 2 = 1 :=
  sn_sq_add_cn_sq k u

example (hk : k ^ 2 < 1) (u : ℝ) :
    dn k u ^ 2 = 1 - k ^ 2 * sn k u ^ 2 :=
  dn_sq hk u

example (hk : k ^ 2 < 1) (u : ℝ) :
    0 < dn k u :=
  dn_pos hk u

example (hk : k ^ 2 < 1) (u : ℝ) :
    HasDerivAt (am k) (dn k u) u :=
  hasDerivAt_am hk u

example (hk : k ^ 2 < 1) (u : ℝ) :
    HasDerivAt (sn k) (cn k u * dn k u) u :=
  hasDerivAt_sn hk u

example (hk : k ^ 2 < 1) (u : ℝ) :
    HasDerivAt (cn k) (-(sn k u * dn k u)) u :=
  hasDerivAt_cn hk u

example (hk : k ^ 2 < 1) (u : ℝ) :
    HasDerivAt (dn k) (-(k ^ 2 * sn k u * cn k u)) u :=
  hasDerivAt_dn hk u

example (hk : k ^ 2 < 1) :
    ContDiff ℝ ∞ (am k) :=
  contDiff_am hk

example (hk : k ^ 2 < 1) :
    ContDiff ℝ ∞ (sn k) :=
  contDiff_sn hk

example (hk : k ^ 2 < 1) :
    ContDiff ℝ ∞ (cn k) :=
  contDiff_cn hk

example (hk : k ^ 2 < 1) :
    ContDiff ℝ ∞ (dn k) :=
  contDiff_dn hk

example (hk : k ^ 2 < 1) :
    Function.Surjective (am k) :=
  am_surjective hk

example (hk : k ^ 2 < 1) :
    StrictMono (am k) :=
  strictMono_am hk

example (hk : k ^ 2 < 1) :
    0 < halfPeriod k :=
  halfPeriod_pos hk

example (hk : k ^ 2 < 1) (u : ℝ) :
    am k (u + halfPeriod k) = am k u + π :=
  am_add_halfPeriod hk u

example (hk : k ^ 2 < 1) (u : ℝ) :
    sn k (u + halfPeriod k) = -sn k u :=
  sn_add_halfPeriod hk u

example (hk : k ^ 2 < 1) (u : ℝ) :
    cn k (u + halfPeriod k) = -cn k u :=
  cn_add_halfPeriod hk u

example (hk : k ^ 2 < 1) (u : ℝ) :
    dn k (u + halfPeriod k) = dn k u :=
  dn_add_halfPeriod hk u

end JacobiElliptic

section AsymmetricTop

variable {I : Fin 3 → ℝ}

example (I : Fin 3 → ℝ) :
    eulerField I =
      realField (poisson.hamiltonian (kineticEnergy I)) := rfl

example (I : Fin 3 → ℝ) :
    ContDiff ℝ ∞ (eulerField I) :=
  contDiff_eulerField I

example (I : Fin 3 → ℝ) (L : Fin 3 → ℝ) :
    eulerField I L 0 = ((I 2)⁻¹ - (I 1)⁻¹) * (L 1 * L 2) :=
  eulerField_zero I L

example (I : Fin 3 → ℝ) (L : Fin 3 → ℝ) :
    eulerField I L 1 = ((I 0)⁻¹ - (I 2)⁻¹) * (L 2 * L 0) :=
  eulerField_one I L

example (I : Fin 3 → ℝ) (L : Fin 3 → ℝ) :
    eulerField I L 2 = ((I 1)⁻¹ - (I 0)⁻¹) * (L 0 * L 1) :=
  eulerField_two I L

example (A B C p k t : ℝ) :
    jacobiCurve A B C p k t =
      ![A * cn k (p * t), B * sn k (p * t), C * dn k (p * t)] := rfl

example (A B C p k : ℝ) :
    jacobiCurve A B C p k 0 = ![A, 0, C] :=
  jacobiCurve_zero A B C p k

example {k : ℝ} (hk : k ^ 2 < 1) {a₀ a₁ a₂ A B C p : ℝ}
    (h0 : -(A * p) = a₀ * (B * C)) (h1 : B * p = a₁ * (C * A))
    (h2 : -(C * p * k ^ 2) = a₂ * (A * B)) (t : ℝ) :
    HasDerivAt (jacobiCurve A B C p k)
      ![a₀ * (jacobiCurve A B C p k t 1 * jacobiCurve A B C p k t 2),
        a₁ * (jacobiCurve A B C p k t 2 * jacobiCurve A B C p k t 0),
        a₂ * (jacobiCurve A B C p k t 0 * jacobiCurve A B C p k t 1)] t :=
  hasDerivAt_jacobiCurve hk h0 h1 h2 t

example (A B C p k t : ℝ) :
    jacobiCurve' A B C p k t =
      ![A * dn k (p * t), B * sn k (p * t), C * cn k (p * t)] := rfl

example (A B C p k : ℝ) :
    jacobiCurve' A B C p k 0 = ![A, 0, C] :=
  jacobiCurve'_zero A B C p k

example {k : ℝ} (hk : k ^ 2 < 1) {a₀ a₁ a₂ A B C p : ℝ}
    (h0 : -(A * p * k ^ 2) = a₀ * (B * C)) (h1 : B * p = a₁ * (C * A))
    (h2 : -(C * p) = a₂ * (A * B)) (t : ℝ) :
    HasDerivAt (jacobiCurve' A B C p k)
      ![a₀ * (jacobiCurve' A B C p k t 1 * jacobiCurve' A B C p k t 2),
        a₁ * (jacobiCurve' A B C p k t 2 * jacobiCurve' A B C p k t 0),
        a₂ * (jacobiCurve' A B C p k t 0 * jacobiCurve' A B C p k t 1)] t :=
  hasDerivAt_jacobiCurve' hk h0 h1 h2 t

example (I : Fin 3 → ℝ) (A C : ℝ) :
    topModulus I A C =
      √(((I 1)⁻¹ - (I 0)⁻¹) / ((I 2)⁻¹ - (I 1)⁻¹)) * A / C := rfl

example (I : Fin 3 → ℝ) :
    topRate I =
      √(-(((I 2)⁻¹ - (I 1)⁻¹) * ((I 0)⁻¹ - (I 2)⁻¹))) := rfl

example (I : Fin 3 → ℝ) (A C t : ℝ) :
    ellipticMotion I A C t =
      jacobiCurve A (((I 0)⁻¹ - (I 2)⁻¹) * A / topRate I) C (C * topRate I)
        (topModulus I A C) t := rfl

example (I : Fin 3 → ℝ) (A C : ℝ) :
    ellipticMotion I A C 0 = ![A, 0, C] :=
  ellipticMotion_zero I A C

example (h0 : (I 2)⁻¹ - (I 1)⁻¹ < 0) (h1 : 0 < (I 0)⁻¹ - (I 2)⁻¹) :
    topRate I ^ 2 = -(((I 2)⁻¹ - (I 1)⁻¹) * ((I 0)⁻¹ - (I 2)⁻¹)) :=
  topRate_sq h0 h1

example (h0 : (I 2)⁻¹ - (I 1)⁻¹ < 0) (h1 : 0 < (I 0)⁻¹ - (I 2)⁻¹) :
    0 < topRate I :=
  topRate_pos h0 h1

example (h0 : (I 2)⁻¹ - (I 1)⁻¹ < 0) (h2 : (I 1)⁻¹ - (I 0)⁻¹ ≤ 0) (A C : ℝ) :
    topModulus I A C ^ 2 =
      ((I 1)⁻¹ - (I 0)⁻¹) / ((I 2)⁻¹ - (I 1)⁻¹) * A ^ 2 / C ^ 2 :=
  topModulus_sq h0 h2 A C

example (h0 : (I 2)⁻¹ - (I 1)⁻¹ < 0) (h1 : 0 < (I 0)⁻¹ - (I 2)⁻¹)
    (h2 : (I 1)⁻¹ - (I 0)⁻¹ ≤ 0) {A C : ℝ} (hC : C ≠ 0) (hk : topModulus I A C ^ 2 < 1)
    (t : ℝ) :
    HasDerivAt (ellipticMotion I A C) (eulerField I (ellipticMotion I A C t)) t :=
  hasDerivAt_ellipticMotion h0 h1 h2 hC hk t

example (h0 : (I 2)⁻¹ - (I 1)⁻¹ < 0)
    (h1 : 0 < (I 0)⁻¹ - (I 2)⁻¹) (h2 : (I 1)⁻¹ - (I 0)⁻¹ ≤ 0) {A C : ℝ} (hC : C ≠ 0)
    (hk : topModulus I A C ^ 2 < 1) (t : ℝ) :
    (t, ![A, 0, C]) ∈ flowDomain (eulerField I) ∧
      flow (eulerField I) (t, ![A, 0, C]) = ellipticMotion I A C t :=
  flow_eulerField_ellipticMotion h0 h1 h2 hC hk t

example (h0 : (I 2)⁻¹ - (I 1)⁻¹ < 0) (h1 : 0 < (I 0)⁻¹ - (I 2)⁻¹)
    {A C : ℝ} (hC : C ≠ 0) (hk : topModulus I A C ^ 2 < 1) (t : ℝ) :
    ellipticMotion I A C (t + 2 * halfPeriod (topModulus I A C) / (C * topRate I)) =
      ellipticMotion I A C t :=
  ellipticMotion_add_period h0 h1 hC hk t

example (I : Fin 3 → ℝ) (A C t : ℝ) :
    ellipticMotion' I A C t =
      jacobiCurve' A (((I 0)⁻¹ - (I 2)⁻¹) * C /
      √(-(((I 0)⁻¹ - (I 2)⁻¹) * ((I 1)⁻¹ - (I 0)⁻¹)))) C
      (A * √(-(((I 0)⁻¹ - (I 2)⁻¹) * ((I 1)⁻¹ - (I 0)⁻¹))))
      (√(((I 2)⁻¹ - (I 1)⁻¹) / ((I 1)⁻¹ - (I 0)⁻¹)) * C / A) t := rfl

example (I : Fin 3 → ℝ) (A C : ℝ) :
    ellipticMotion' I A C 0 = ![A, 0, C] :=
  ellipticMotion'_zero I A C

example (h0 : (I 2)⁻¹ - (I 1)⁻¹ ≤ 0) (h1 : 0 < (I 0)⁻¹ - (I 2)⁻¹)
    (h2 : (I 1)⁻¹ - (I 0)⁻¹ < 0) {A C : ℝ} (hA : A ≠ 0)
    (hk : (√(((I 2)⁻¹ - (I 1)⁻¹) / ((I 1)⁻¹ - (I 0)⁻¹)) * C / A) ^ 2 < 1) (t : ℝ) :
    HasDerivAt (ellipticMotion' I A C) (eulerField I (ellipticMotion' I A C t)) t :=
  hasDerivAt_ellipticMotion' h0 h1 h2 hA hk t

example {u w : ℝ} (h : u ^ 2 + w ^ 2 = 1) :
    ∃ φ : ℝ, Real.cos φ = u ∧ Real.sin φ = w :=
  exists_cos_sin_eq h

example {a b c : ℝ} (ha : a < 0) (hb : 0 < b) (hc : c < 0)
    {x y z : ℝ} (hreg : a * z ^ 2 < c * x ^ 2) :
    ∃ A C t₀ : ℝ, C ≠ 0 ∧ (√(c / a) * A / C) ^ 2 < 1 ∧
      jacobiCurve A (b * A / √(-(a * b))) C (C * √(-(a * b))) (√(c / a) * A / C) t₀ =
        ![x, y, z] :=
  exists_jacobiCurve_eq ha hb hc hreg

example (h0 : (I 2)⁻¹ - (I 1)⁻¹ < 0) (h1 : 0 < (I 0)⁻¹ - (I 2)⁻¹)
    (h2 : (I 1)⁻¹ - (I 0)⁻¹ < 0) {L₀ : Fin 3 → ℝ}
    (hreg : ((I 2)⁻¹ - (I 1)⁻¹) * L₀ 2 ^ 2 < ((I 1)⁻¹ - (I 0)⁻¹) * L₀ 0 ^ 2) :
    ∃ A C t₀ : ℝ, C ≠ 0 ∧ topModulus I A C ^ 2 < 1 ∧ ellipticMotion I A C t₀ = L₀ :=
  exists_ellipticMotion_eq h0 h1 h2 hreg

example (h0 : (I 2)⁻¹ - (I 1)⁻¹ < 0)
    (h1 : 0 < (I 0)⁻¹ - (I 2)⁻¹) (h2 : (I 1)⁻¹ - (I 0)⁻¹ < 0) {y : ℝ → Fin 3 → ℝ}
    (hy : ∀ t, HasDerivAt y (eulerField I (y t)) t)
    (hreg : ((I 2)⁻¹ - (I 1)⁻¹) * y 0 2 ^ 2 < ((I 1)⁻¹ - (I 0)⁻¹) * y 0 0 ^ 2) :
    ∃ A C t₀ : ℝ, C ≠ 0 ∧ topModulus I A C ^ 2 < 1 ∧
      ∀ t, y t = ellipticMotion I A C (t + t₀) :=
  eq_ellipticMotion_of_hasDerivAt h0 h1 h2 hy hreg

example (A B C p k t : ℝ) :
    jacobiCurve' A B C p k t =
      ![jacobiCurve C B A p k t 2, jacobiCurve C B A p k t 1, jacobiCurve C B A p k t 0] :=
  jacobiCurve'_eq A B C p k t

example (h0 : (I 2)⁻¹ - (I 1)⁻¹ < 0) (h1 : 0 < (I 0)⁻¹ - (I 2)⁻¹)
    (h2 : (I 1)⁻¹ - (I 0)⁻¹ < 0) {L₀ : Fin 3 → ℝ}
    (hreg : ((I 1)⁻¹ - (I 0)⁻¹) * L₀ 0 ^ 2 < ((I 2)⁻¹ - (I 1)⁻¹) * L₀ 2 ^ 2) :
    ∃ A C t₀ : ℝ, A ≠ 0 ∧
      (√(((I 2)⁻¹ - (I 1)⁻¹) / ((I 1)⁻¹ - (I 0)⁻¹)) * C / A) ^ 2 < 1 ∧
      ellipticMotion' I A C t₀ = L₀ :=
  exists_ellipticMotion'_eq h0 h1 h2 hreg

example (h0 : (I 2)⁻¹ - (I 1)⁻¹ < 0)
    (h1 : 0 < (I 0)⁻¹ - (I 2)⁻¹) (h2 : (I 1)⁻¹ - (I 0)⁻¹ < 0) {y : ℝ → Fin 3 → ℝ}
    (hy : ∀ t, HasDerivAt y (eulerField I (y t)) t)
    (hreg : ((I 1)⁻¹ - (I 0)⁻¹) * y 0 0 ^ 2 < ((I 2)⁻¹ - (I 1)⁻¹) * y 0 2 ^ 2) :
    ∃ A C t₀ : ℝ, A ≠ 0 ∧
      (√(((I 2)⁻¹ - (I 1)⁻¹) / ((I 1)⁻¹ - (I 0)⁻¹)) * C / A) ^ 2 < 1 ∧
      ∀ t, y t = ellipticMotion' I A C (t + t₀) :=
  eq_ellipticMotion'_of_hasDerivAt h0 h1 h2 hy hreg

example (I : Fin 3 → ℝ) (A C : ℝ) (hk : topModulus I A C ^ 2 < 1) :
    ellipticTrajectory I A C hk =
      fun i =>
      SmoothOperation.ofContDiff (fun s : Fin 1 → ℝ => ellipticMotion I A C (s 0) i) (by
      have hlin : ContDiff ℝ ∞ fun s : Fin 1 → ℝ => C * topRate I * s 0 :=
      contDiff_const.mul (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).contDiff
      fin_cases i
      · exact contDiff_const.mul ((contDiff_cn hk).comp hlin)
      · exact contDiff_const.mul ((contDiff_sn hk).comp hlin)
      · exact contDiff_const.mul ((contDiff_dn hk).comp hlin)) := rfl

example (h0 : (I 2)⁻¹ - (I 1)⁻¹ < 0)
    (h1 : 0 < (I 0)⁻¹ - (I 2)⁻¹) (h2 : (I 1)⁻¹ - (I 0)⁻¹ ≤ 0) {A C : ℝ} (hC : C ≠ 0)
    (hk : topModulus I A C ^ 2 < 1) :
    IsTrajectory poisson (kineticEnergy I) (ellipticTrajectory I A C hk) :=
  isTrajectory_ellipticTrajectory h0 h1 h2 hC hk

end AsymmetricTop
