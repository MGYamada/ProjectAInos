/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.Mechanics.OneDimension.AdiabaticInvariant
import ProjectAinos.Mechanics.Oscillations.AdiabaticOscillator

/-! Typed contracts for adiabatic invariance: parametric integrals of functions
that are smooth on an open set, the estimate from a corrector of the first
order, families of wells with a parameter and the derivative of the area, the
action variable of one degree of freedom with its corrector and the adiabatic
theorem, and the theorem for the oscillator. These examples use default
elaborator options. -/

open ProjectAinos ProjectAinos.Mechanics ProjectAinos.Mechanics.OneDim
open ProjectAinos.SmoothGeometry.NonlinearODE
open Set Filter MeasureTheory
open scoped Real Topology

noncomputable section

section ParametricIntegral

open Variational
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

example {f : E × ℝ → ℝ} {U : Set (E × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {a b : ℝ} {x₀ : E}
    (h : ∀ t ∈ uIcc a b, (x₀, t) ∈ U) :
    ContDiffAt ℝ ∞ (fun x => ∫ t in a..b, f (x, t)) x₀ :=
  contDiffAt_parametric_intervalIntegral hU hf h

example {f : E × ℝ → ℝ} {U : Set (E × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {a b : ℝ} {S : Set E}
    (h : ∀ x ∈ S, ∀ t ∈ uIcc a b, (x, t) ∈ U) :
    ContDiffOn ℝ ∞ (fun x => ∫ t in a..b, f (x, t)) S :=
  contDiffOn_parametric_intervalIntegral hU hf h

end ParametricIntegral

section SlowParameter

open SmoothGeometry.SlowParameter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

example {X : E × ℝ → E} {I G : E × ℝ → ℝ}
    {I' G' : E × ℝ → (E × ℝ →L[ℝ] ℝ)} {S : Set (E × ℝ)} {Λ Λ' Λ'' : ℝ → ℝ}
    {T ε L₁ L₂ M₀ M₁ : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (hI : ∀ w ∈ S, HasFDerivAt I (I' w) w) (hG : ∀ w ∈ S, HasFDerivAt G (G' w) w)
    (hinv : ∀ w ∈ S, I' w (X w, 0) = 0)
    (hhom : ∀ w ∈ S, I' w (0, 1) = G' w (X w, 0))
    (hΛ : ∀ τ ∈ Icc 0 T, HasDerivAt Λ (Λ' τ) τ)
    (hΛ' : ∀ τ ∈ Icc 0 T, HasDerivAt Λ' (Λ'' τ) τ)
    (hL₁ : ∀ τ ∈ Icc 0 T, |Λ' τ| ≤ L₁) (hL₂ : ∀ τ ∈ Icc 0 T, |Λ'' τ| ≤ L₂)
    (hM₀ : ∀ w ∈ S, |G w| ≤ M₀) (hM₁ : ∀ w ∈ S, |G' w (0, 1)| ≤ M₁)
    {z : ℝ → E} (hz : ∀ t ∈ Icc 0 (T / ε), HasDerivAt z (X (z t, Λ (ε * t))) t)
    (hS : ∀ t ∈ Icc 0 (T / ε), (z t, Λ (ε * t)) ∈ S) :
    ∀ t ∈ Icc 0 (T / ε),
      |I (z t, Λ (ε * t)) - I (z 0, Λ 0)| ≤
        ε * (T * (L₂ * M₀ + L₁ ^ 2 * M₁) + 2 * L₁ * M₀) :=
  abs_sub_le_of_corrector hε hT hI hG hinv hhom hΛ hΛ' hL₁ hL₂ hM₀ hM₁ hz hS

end SlowParameter

section WellFamily

open scoped ContDiff

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {V : P × ℝ → ℝ} {ℰ : P → ℝ} {J : Set P} {α β : P → ℝ} {m : ℝ}

example (V : P × ℝ → ℝ) (w : P × ℝ) :
    slopeOf V w =
      fderiv ℝ V w (0, 1) := rfl

example (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (slopeOf V) :=
  contDiff_slopeOf hV

example (hV : ContDiff ℝ ∞ V) (s : P) (x : ℝ) :
    HasDerivAt (fun y => V (s, y)) (slopeOf V (s, x)) x :=
  hasDerivAt_slice hV s x

example (hV : ContDiff ℝ ∞ V) (s : P) :
    deriv (fun y => V (s, y)) = fun x => slopeOf V (s, x) :=
  deriv_slice hV s

example (hV : ContDiff ℝ ∞ V) (s : P) :
    deriv (deriv (fun y => V (s, y))) = fun x => slopeOf (slopeOf V) (s, x) :=
  deriv_deriv_slice hV s

example (hV : ContDiff ℝ ∞ V) (s : P) :
    ContDiff ℝ ∞ fun y => V (s, y) :=
  contDiff_slice hV s

example (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ fun r : P × ℝ × ℝ × ℝ =>
      wellFactor (fun y => V (r.1, y)) r.2.1 r.2.2.1 r.2.2.2 :=
  contDiff_wellFactor_family hV

example (hV : ContDiff ℝ ∞ V) {ℰ : P → ℝ} (hℰ : ContDiff ℝ ∞ ℰ)
    {s₀ : P} {x₀ : ℝ} (hx₀ : V (s₀, x₀) = ℰ s₀) (hd : slopeOf V (s₀, x₀) ≠ 0) :
    ∃ (J : Set P) (ξ : P → ℝ), IsOpen J ∧ s₀ ∈ J ∧ ξ s₀ = x₀ ∧ ContDiffOn ℝ ∞ ξ J ∧
      ∀ s ∈ J, V (s, ξ s) = ℰ s :=
  exists_level_point_family hV hℰ hx₀ hd

example (hV : ContDiff ℝ ∞ V) {ℰ : P → ℝ} (hℰ : ContDiff ℝ ∞ ℰ)
    {s₀ : P} {a₀ b₀ : ℝ} (h : IsWell (fun y => V (s₀, y)) (ℰ s₀) a₀ b₀) :
    ∃ (J : Set P) (α β : P → ℝ), IsOpen J ∧ s₀ ∈ J ∧ α s₀ = a₀ ∧ β s₀ = b₀ ∧
      ContDiffOn ℝ ∞ α J ∧ ContDiffOn ℝ ∞ β J ∧
        ∀ s ∈ J, IsWell (fun y => V (s, y)) (ℰ s) (α s) (β s) :=
  IsWell.exists_family_param hV hℰ h

example (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J) :
    ContDiffOn ℝ ∞ (fun p : P × ℝ => orbitPosition (α p.1) (β p.1) p.2) (Prod.fst ⁻¹' J) :=
  contDiffOn_orbitPosition_family hα hβ

example (hV : ContDiff ℝ ∞ V) (hα : ContDiffOn ℝ ∞ α J)
    (hβ : ContDiffOn ℝ ∞ β J) :
    ContDiffOn ℝ ∞ (fun p : P × ℝ => wellFactor (fun y => V (p.1, y)) (α p.1) (β p.1)
      (orbitPosition (α p.1) (β p.1) p.2)) (Prod.fst ⁻¹' J) :=
  contDiffOn_wellFactor_orbit hV hα hβ

example (hV : ContDiff ℝ ∞ V) (m : ℝ)
    (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ s ∈ J, IsWell (fun y => V (s, y)) (ℰ s) (α s) (β s)) :
    ContDiffOn ℝ ∞ (fun p : P × ℝ =>
      orbitMomentum m (fun y => V (p.1, y)) (α p.1) (β p.1) p.2) (Prod.fst ⁻¹' J) :=
  contDiffOn_orbitMomentum_family_param hV m hα hβ hw

example (hV : ContDiff ℝ ∞ V) (m : ℝ)
    (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ s ∈ J, IsWell (fun y => V (s, y)) (ℰ s) (α s) (β s)) :
    ContDiffOn ℝ ∞ (fun p : P × ℝ =>
      orbitRate m (fun y => V (p.1, y)) (α p.1) (β p.1) p.2) (Prod.fst ⁻¹' J) :=
  contDiffOn_orbitRate_family hV m hα hβ hw

example (hV : ContDiff ℝ ∞ V) (m : ℝ) (hJ : IsOpen J)
    (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ s ∈ J, IsWell (fun y => V (s, y)) (ℰ s) (α s) (β s)) {g : P × ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) :
    ContDiffOn ℝ ∞ (fun s => ∫ θ in (0 : ℝ)..2 * π,
      orbitRate m (fun y => V (s, y)) (α s) (β s) θ *
        g (s, orbitPosition (α s) (β s) θ)) J :=
  contDiffOn_integral_orbitRate_mul hV m hJ hα hβ hw hg

example (hV : ContDiff ℝ ∞ V) (m : ℝ) (hJ : IsOpen J)
    (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ s ∈ J, IsWell (fun y => V (s, y)) (ℰ s) (α s) (β s)) :
    ContDiffOn ℝ ∞ (fun s => orbitPeriod m (fun y => V (s, y)) (α s) (β s)) J :=
  contDiffOn_orbitPeriod_family hV m hJ hα hβ hw

example (hV : ContDiff ℝ ∞ V) (m : ℝ) (hJ : IsOpen J)
    (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ s ∈ J, IsWell (fun y => V (s, y)) (ℰ s) (α s) (β s)) :
    ContDiffOn ℝ ∞ (fun s => orbitArea m (fun y => V (s, y)) (α s) (β s)) J :=
  contDiffOn_orbitArea_family hV m hJ hα hβ hw

example (s₀ u : P) :
    HasDerivAt (fun r : ℝ => s₀ + r • u) u 0 :=
  hasDerivAt_line s₀ u

example (hV : ContDiff ℝ ∞ V) (hm : 0 < m) (hJ : IsOpen J)
    (hℰ : ContDiff ℝ ∞ ℰ) (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ s ∈ J, IsWell (fun y => V (s, y)) (ℰ s) (α s) (β s)) {s₀ : P} (hs₀ : s₀ ∈ J)
    (u : P) :
    HasDerivAt (fun r : ℝ => orbitArea m (fun y => V (s₀ + r • u, y)) (α (s₀ + r • u))
        (β (s₀ + r • u)))
      (∫ θ in (0 : ℝ)..2 * π, orbitRate m (fun y => V (s₀, y)) (α s₀) (β s₀) θ *
        (fderiv ℝ ℰ s₀ u - fderiv ℝ V (s₀, orbitPosition (α s₀) (β s₀) θ) (u, 0))) 0 :=
  hasDerivAt_orbitArea_line hV hm hJ hℰ hα hβ hw hs₀ u

example (hV : ContDiff ℝ ∞ V) (hm : 0 < m) (hJ : IsOpen J)
    (hℰ : ContDiff ℝ ∞ ℰ) (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ s ∈ J, IsWell (fun y => V (s, y)) (ℰ s) (α s) (β s)) {s₀ : P} (hs₀ : s₀ ∈ J)
    (u : P) :
    fderiv ℝ (fun s => orbitArea m (fun y => V (s, y)) (α s) (β s)) s₀ u =
      ∫ θ in (0 : ℝ)..2 * π, orbitRate m (fun y => V (s₀, y)) (α s₀) (β s₀) θ *
        (fderiv ℝ ℰ s₀ u - fderiv ℝ V (s₀, orbitPosition (α s₀) (β s₀) θ) (u, 0)) :=
  fderiv_orbitArea_family hV hm hJ hℰ hα hβ hw hs₀ u

end WellFamily

section RealParameter

open scoped ContDiff

variable {V : ℝ × ℝ → ℝ} {m : ℝ} {J : Set ℝ} {ℰ α β : ℝ → ℝ}

example (hV : ContDiff ℝ ∞ V) (hm : 0 < m) (hJ : IsOpen J)
    (hw : ∀ r ∈ J, IsWell (fun y => V (r, y)) (ℰ r) (α r) (β r)) {r₀ : ℝ} (hr₀ : r₀ ∈ J)
    {ℰ' α' β' PE : ℝ} (hℰ : HasDerivAt ℰ ℰ' r₀) (hα : HasDerivAt α α' r₀)
    (hβ : HasDerivAt β β' r₀) {θ : ℝ}
    (hPE : HasDerivAt (fun r => orbitMomentum m (fun y => V (r, y)) (α r) (β r) θ) PE r₀) :
    orbitMomentum m (fun y => V (r₀, y)) (α r₀) (β r₀) θ * PE / m +
      (slopeOf V (r₀, orbitPosition (α r₀) (β r₀) θ) *
          ((α' + β') / 2 - (β' - α') / 2 * Real.cos θ) +
        fderiv ℝ V (r₀, orbitPosition (α r₀) (β r₀) θ) (1, 0)) = ℰ' :=
  orbitMomentum_mul_deriv_param hV hm hJ hw hr₀ hℰ hα hβ hPE

example (hV : ContDiff ℝ ∞ V) (hm : 0 < m) (hJ : IsOpen J)
    (hℰ : ContDiffOn ℝ ∞ ℰ J) (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ r ∈ J, IsWell (fun y => V (r, y)) (ℰ r) (α r) (β r)) {r₀ : ℝ} (hr₀ : r₀ ∈ J) :
    HasDerivAt (fun r => orbitArea m (fun y => V (r, y)) (α r) (β r))
      (∫ θ in (0 : ℝ)..2 * π, orbitRate m (fun y => V (r₀, y)) (α r₀) (β r₀) θ *
        (deriv ℰ r₀ - fderiv ℝ V (r₀, orbitPosition (α r₀) (β r₀) θ) (1, 0))) r₀ :=
  hasDerivAt_orbitArea_family hV hm hJ hℰ hα hβ hw hr₀

end RealParameter

section AdiabaticInvariant

open Adiabatic
open scoped ContDiff

variable {V : ℝ × ℝ → ℝ} {J : Set (ℝ × ℝ)} {α β : ℝ × ℝ → ℝ} {m : ℝ}

example (V : ℝ × ℝ → ℝ) (r : (ℝ × ℝ) × ℝ) :
    lift V r =
      V (r.1.2, r.2) := rfl

example (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (lift V) :=
  contDiff_lift hV

example (hF : IsWellFamily V J α β) : IsOpen J := hF.isOpen

example (hF : IsWellFamily V J α β) : ContDiffOn ℝ ∞ α J := hF.contDiffOn_left

example (hF : IsWellFamily V J α β) : ContDiffOn ℝ ∞ β J := hF.contDiffOn_right

example (hF : IsWellFamily V J α β) (s : ℝ × ℝ) (hs : s ∈ J) :
    IsWell (fun y => V (s.2, y)) s.1 (α s) (β s) := hF.isWell s hs

example (hV : ContDiff ℝ ∞ V) {E₀ lam₀ a₀ b₀ : ℝ}
    (h : IsWell (fun y => V (lam₀, y)) E₀ a₀ b₀) :
    ∃ (J : Set (ℝ × ℝ)) (α β : ℝ × ℝ → ℝ), IsWellFamily V J α β ∧ (E₀, lam₀) ∈ J ∧
      α (E₀, lam₀) = a₀ ∧ β (E₀, lam₀) = b₀ :=
  exists_isWellFamily hV h

example (m : ℝ) (V : ℝ × ℝ → ℝ) (α β : ℝ × ℝ → ℝ) (s : ℝ × ℝ) :
    period m V α β s =
      orbitPeriod m (fun y => V (s.2, y)) (α s) (β s) := rfl

example (m : ℝ) (V : ℝ × ℝ → ℝ) (α β : ℝ × ℝ → ℝ) (s : ℝ × ℝ) :
    area m V α β s =
      orbitArea m (fun y => V (s.2, y)) (α s) (β s) := rfl

example (m : ℝ) (V : ℝ × ℝ → ℝ) (α β : ℝ × ℝ → ℝ) (s : ℝ × ℝ) :
    parameterForce m V α β s =
      ∫ θ in (0 : ℝ)..2 * π, orbitRate m (fun y => V (s.2, y)) (α s) (β s) θ *
      fderiv ℝ V (s.2, orbitPosition (α s) (β s) θ) (1, 0) := rfl

example (hV : ContDiff ℝ ∞ V) (m : ℝ) (hF : IsWellFamily V J α β) :
    ContDiffOn ℝ ∞ (period m V α β) J :=
  contDiffOn_period hV m hF

example (hV : ContDiff ℝ ∞ V) (m : ℝ) (hF : IsWellFamily V J α β) :
    ContDiffOn ℝ ∞ (area m V α β) J :=
  contDiffOn_area hV m hF

example (hV : ContDiff ℝ ∞ V) (m : ℝ) (hF : IsWellFamily V J α β) :
    ContDiffOn ℝ ∞ (parameterForce m V α β) J :=
  contDiffOn_parameterForce hV m hF

example (hV : ContDiff ℝ ∞ V) (s : ℝ × ℝ) (x : ℝ) (u : ℝ × ℝ) :
    fderiv ℝ (lift V) (s, x) (u, 0) = u.2 * fderiv ℝ V (s.2, x) (1, 0) :=
  fderiv_lift hV s x u

example (hV : ContDiff ℝ ∞ V) (hm : 0 < m) (hF : IsWellFamily V J α β)
    {s : ℝ × ℝ} (hs : s ∈ J) (u : ℝ × ℝ) :
    fderiv ℝ (area m V α β) s u =
      u.1 * period m V α β s - u.2 * parameterForce m V α β s :=
  fderiv_area hV hm hF hs u

example (m : ℝ) (V : ℝ × ℝ → ℝ) (w : (ℝ × ℝ) × ℝ) :
    energyAt m V w =
      w.1.2 ^ 2 / (2 * m) + V (w.2, w.1.1) := rfl

example (m : ℝ) (V : ℝ × ℝ → ℝ) (w : (ℝ × ℝ) × ℝ) :
    level m V w =
      (energyAt m V w, w.2) := rfl

example (m : ℝ) (V : ℝ × ℝ → ℝ) (w : (ℝ × ℝ) × ℝ) :
    frozenField m V w =
      (w.1.2 / m, -fderiv ℝ V (w.2, w.1.1) (0, 1)) := rfl

example (m : ℝ) (V : ℝ × ℝ → ℝ) (z : ℝ × ℝ) (lam : ℝ) :
    energyAt m V (z, lam) = energy m (fun y => V (lam, y)) z :=
  energyAt_eq m V z lam

example (hV : ContDiff ℝ ∞ V) (m : ℝ) (z : ℝ × ℝ) (lam : ℝ) :
    frozenField m V (z, lam) = field m (fun y => V (lam, y)) z :=
  frozenField_eq hV m z lam

example (hV : ContDiff ℝ ∞ V) (m : ℝ) :
    ContDiff ℝ ∞ (energyAt m V) :=
  contDiff_energyAt hV m

example (hV : ContDiff ℝ ∞ V) (m : ℝ) :
    ContDiff ℝ ∞ (level m V) :=
  contDiff_level hV m

example (hV : ContDiff ℝ ∞ V) (m : ℝ) (w u : (ℝ × ℝ) × ℝ) :
    HasDerivAt (fun r : ℝ => energyAt m V (w + r • u))
      (w.1.2 * u.1.2 / m + fderiv ℝ V (w.2, w.1.1) (u.2, u.1.1)) 0 :=
  hasDerivAt_energyAt_line hV m w u

example (hV : ContDiff ℝ ∞ V) (m : ℝ) (w u : (ℝ × ℝ) × ℝ) :
    fderiv ℝ (energyAt m V) w u =
      w.1.2 * u.1.2 / m + fderiv ℝ V (w.2, w.1.1) (u.2, u.1.1) :=
  fderiv_energyAt hV m w u

example (hV : ContDiff ℝ ∞ V) (m : ℝ) (w : (ℝ × ℝ) × ℝ) :
    fderiv ℝ (energyAt m V) w (frozenField m V w, 0) = 0 :=
  fderiv_energyAt_frozenField hV m w

example (hV : ContDiff ℝ ∞ V) (m : ℝ) (w : (ℝ × ℝ) × ℝ) :
    fderiv ℝ (energyAt m V) w (0, 1) = fderiv ℝ V (w.2, w.1.1) (1, 0) :=
  fderiv_energyAt_parameter hV m w

example (hV : ContDiff ℝ ∞ V) (m : ℝ) (w u : (ℝ × ℝ) × ℝ) :
    fderiv ℝ (level m V) w u = (fderiv ℝ (energyAt m V) w u, u.2) :=
  fderiv_level hV m w u

example (m : ℝ) (V : ℝ × ℝ → ℝ) (α β : ℝ × ℝ → ℝ) (w : (ℝ × ℝ) × ℝ) :
    invariant m V α β w =
      area m V α β (level m V w) / (2 * π) := rfl

example (m : ℝ) (V : ℝ × ℝ → ℝ) (α β : ℝ × ℝ → ℝ) (w : (ℝ × ℝ) × ℝ) :
    invariantDeriv m V α β w =
      (period m V α β (level m V w) * fderiv ℝ V (w.2, w.1.1) (1, 0) -
      parameterForce m V α β (level m V w)) / (2 * π) := rfl

example (m : ℝ) (V : ℝ × ℝ → ℝ) (α β : ℝ × ℝ → ℝ) :
    invariant m V α β = fun w => (area m V α β ∘ level m V) w * (2 * π)⁻¹ :=
  invariant_eq m V α β

example (hV : ContDiff ℝ ∞ V) (m : ℝ) (hF : IsWellFamily V J α β)
    {w : (ℝ × ℝ) × ℝ} (hw : level m V w ∈ J) :
    DifferentiableAt ℝ (invariant m V α β) w :=
  differentiableAt_invariant hV m hF hw

example (hV : ContDiff ℝ ∞ V) (hm : 0 < m) (hF : IsWellFamily V J α β)
    {w : (ℝ × ℝ) × ℝ} (hw : level m V w ∈ J) (u : (ℝ × ℝ) × ℝ) :
    fderiv ℝ (invariant m V α β) w u =
      (fderiv ℝ (energyAt m V) w u * period m V α β (level m V w) -
        u.2 * parameterForce m V α β (level m V w)) / (2 * π) :=
  fderiv_invariant hV hm hF hw u

example (hV : ContDiff ℝ ∞ V) (hm : 0 < m)
    (hF : IsWellFamily V J α β) {w : (ℝ × ℝ) × ℝ} (hw : level m V w ∈ J) :
    fderiv ℝ (invariant m V α β) w (frozenField m V w, 0) = 0 :=
  fderiv_invariant_frozenField hV hm hF hw

example (hV : ContDiff ℝ ∞ V) (hm : 0 < m)
    (hF : IsWellFamily V J α β) {w : (ℝ × ℝ) × ℝ} (hw : level m V w ∈ J) :
    fderiv ℝ (invariant m V α β) w (0, 1) = invariantDeriv m V α β w :=
  fderiv_invariant_parameter hV hm hF hw

example (m : ℝ) (V : ℝ × ℝ → ℝ) (J : Set (ℝ × ℝ)) (α β : ℝ × ℝ → ℝ) :
    wellRegion m V J α β =
      {w | level m V w ∈ J ∧ w.1.1 ∈ Icc (α (level m V w)) (β (level m V w))} := rfl

example (hV : ContDiff ℝ ∞ V) (hm : 0 < m) (hF : IsWellFamily V J α β)
    {w : (ℝ × ℝ) × ℝ} (hw : w ∈ wellRegion m V J α β) :
    ∃ y : ℝ → ℝ × ℝ, y 0 = w.1 ∧
      (∀ s, HasDerivAt y (frozenField m V (y s, w.2)) s) ∧
      (∀ s, level m V (y s, w.2) = level m V w) ∧
      (∀ s, (y s, w.2) ∈ wellRegion m V J α β) ∧
      (∀ s, y (s + period m V α β (level m V w)) = y s) ∧
      (∫ s in (0 : ℝ)..period m V α β (level m V w), fderiv ℝ V (w.2, (y s).1) (1, 0)) =
        parameterForce m V α β (level m V w) :=
  exists_orbit hV hm hF hw

example (m : ℝ) (V : ℝ × ℝ → ℝ) (w : (ℝ × ℝ) × ℝ) :
    extendedField m V w =
      (frozenField m V w, 0) := rfl

example (hV : ContDiff ℝ ∞ V) (m : ℝ) :
    ContDiff ℝ ∞ (extendedField m V) :=
  contDiff_extendedField hV m

example (hV : ContDiff ℝ ∞ V) (m : ℝ) {y : ℝ → ℝ × ℝ} {lam : ℝ}
    (hy : ∀ s, HasDerivAt y (frozenField m V (y s, lam)) s) (t : ℝ) :
    (t, (y 0, lam)) ∈ flowDomain (extendedField m V) ∧
      flow (extendedField m V) (t, (y 0, lam)) = (y t, lam) :=
  flow_extendedField hV m hy t

example {φ : ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hφ : Continuous φ)
    (hper : Function.Periodic φ T) (hmean : ∫ s in (0 : ℝ)..T, φ s = 0) :
    HasDerivAt (fun r : ℝ => T * ∫ σ in (0 : ℝ)..1, σ * φ (T * σ + r)) (φ 0) 0 :=
  hasDerivAt_weighted_shift hT hφ hper hmean

example (m : ℝ) (V : ℝ × ℝ → ℝ) (α β : ℝ × ℝ → ℝ) (w : (ℝ × ℝ) × ℝ) :
    corrector m V α β w =
      period m V α β (level m V w) * ∫ σ in (0 : ℝ)..1,
      σ * ((period m V α β (level m V w) *
      fderiv ℝ V (w.2, (flow (extendedField m V)
      (period m V α β (level m V w) * σ, w)).1.1) (1, 0) -
      parameterForce m V α β (level m V w)) / (2 * π)) := rfl

example (hV : ContDiff ℝ ∞ V) (m : ℝ) (α β : ℝ × ℝ → ℝ) {w : (ℝ × ℝ) × ℝ}
    {y : ℝ → ℝ × ℝ} (hy : ∀ s, HasDerivAt y (frozenField m V (y s, w.2)) s)
    (hlevel : ∀ s, level m V (y s, w.2) = level m V w) (r : ℝ) :
    corrector m V α β (y r, w.2) =
      period m V α β (level m V w) * ∫ σ in (0 : ℝ)..1,
        σ * ((period m V α β (level m V w) *
            fderiv ℝ V (w.2, (y (period m V α β (level m V w) * σ + r)).1) (1, 0) -
          parameterForce m V α β (level m V w)) / (2 * π)) :=
  corrector_orbit hV m α β hy hlevel r

example (hV : ContDiff ℝ ∞ V) (hm : 0 < m) (hF : IsWellFamily V J α β)
    {w₀ : (ℝ × ℝ) × ℝ} (hw₀ : w₀ ∈ wellRegion m V J α β) :
    ContDiffAt ℝ ∞ (corrector m V α β) w₀ :=
  contDiffAt_corrector hV hm hF hw₀

example (hV : ContDiff ℝ ∞ V) (hm : 0 < m)
    (hF : IsWellFamily V J α β) {w : (ℝ × ℝ) × ℝ} (hw : w ∈ wellRegion m V J α β) :
    fderiv ℝ (corrector m V α β) w (frozenField m V w, 0) = invariantDeriv m V α β w :=
  fderiv_corrector_frozenField hV hm hF hw

example (hV : ContDiff ℝ ∞ V) (hm : 0 < m)
    (hF : IsWellFamily V J α β) {K : Set ((ℝ × ℝ) × ℝ)} (hK : IsCompact K)
    (hKw : K ⊆ wellRegion m V J α β) {Λ : ℝ → ℝ} (hΛ : ContDiff ℝ 2 Λ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ z : ℝ → ℝ × ℝ,
      (∀ t ∈ Icc 0 (T / ε), HasDerivAt z (frozenField m V (z t, Λ (ε * t))) t) →
      (∀ t ∈ Icc 0 (T / ε), (z t, Λ (ε * t)) ∈ K) →
      ∀ t ∈ Icc 0 (T / ε),
        |invariant m V α β (z t, Λ (ε * t)) - invariant m V α β (z 0, Λ 0)| ≤ C * ε :=
  exists_forall_abs_invariant_sub_le hV hm hF hK hKw hΛ hT

example (r : ℝ × ℝ) :
    oscillatorPotential r =
      r.1 / 2 * r.2 ^ 2 := rfl

example :
    ContDiff ℝ ∞ oscillatorPotential :=
  contDiff_oscillatorPotential

example :
    IsWellFamily oscillatorPotential {s : ℝ × ℝ | 0 < s.1 ∧ 0 < s.2}
      (fun s => -√(2 * s.1 / s.2)) (fun s => √(2 * s.1 / s.2)) :=
  isWellFamily_oscillator

example (hm : 0 < m) {w : (ℝ × ℝ) × ℝ} (hk : 0 < w.2)
    (hE : 0 < energyAt m oscillatorPotential w) :
    invariant m oscillatorPotential (fun s => -√(2 * s.1 / s.2)) (fun s => √(2 * s.1 / s.2)) w =
      energyAt m oscillatorPotential w * √(m / w.2) :=
  invariant_oscillator hm hk hE

end AdiabaticInvariant

section AdiabaticOscillator

open AdiabaticOscillator

variable {Ω x v : ℝ → ℝ} {ε L : ℝ}

example (ω x v : ℝ) :
    action ω x v =
      (v ^ 2 + ω ^ 2 * x ^ 2) / (2 * ω) := rfl

example {ω : ℝ} (hω : 0 < ω) (x v : ℝ) :
    0 ≤ action ω x v :=
  action_nonneg hω x v

example {ω : ℝ} (hω : 0 < ω) (x v : ℝ) :
    |x * v| ≤ action ω x v :=
  abs_mul_le_action hω x v

example {ω : ℝ} (hω : 0 < ω) (x v : ℝ) :
    |ω ^ 2 * x ^ 2 - v ^ 2| ≤ 2 * ω * action ω x v :=
  abs_sub_le_action hω x v

example {Ω : ℝ → ℝ} (hΩ : ContDiff ℝ 2 Ω) :
    ContDiff ℝ 1 (deriv Ω) :=
  contDiff_deriv hΩ

example (Ω : ℝ → ℝ) (τ : ℝ) :
    coefficient Ω τ =
      deriv Ω τ / (2 * Ω τ ^ 2) := rfl

example (Ω : ℝ → ℝ) (τ : ℝ) :
    coefficientDeriv Ω τ =
      (deriv (deriv Ω) τ * (2 * Ω τ ^ 2) - deriv Ω τ * (4 * Ω τ * deriv Ω τ)) /
        (2 * Ω τ ^ 2) ^ 2 := rfl

example {Ω : ℝ → ℝ} (hΩ : ContDiff ℝ 2 Ω) {τ : ℝ} (hτ : Ω τ ≠ 0) :
    HasDerivAt (coefficient Ω) (coefficientDeriv Ω τ) τ :=
  hasDerivAt_coefficient hΩ hτ

example (hΩ : ContDiff ℝ 2 Ω) {t : ℝ} (hpos : Ω (ε * t) ≠ 0)
    (hx : HasDerivAt x (v t) t) (hv : HasDerivAt v (-(Ω (ε * t)) ^ 2 * x t) t) :
    HasDerivAt (fun s => action (Ω (ε * s)) (x s) (v s))
      (ε * coefficient Ω (ε * t) * (Ω (ε * t) ^ 2 * x t ^ 2 - v t ^ 2)) t :=
  hasDerivAt_action hΩ hpos hx hv

example (hΩ : ContDiff ℝ 2 Ω) {t : ℝ} (hpos : Ω (ε * t) ≠ 0)
    (hx : HasDerivAt x (v t) t) (hv : HasDerivAt v (-(Ω (ε * t)) ^ 2 * x t) t) :
    HasDerivAt
      (fun s => action (Ω (ε * s)) (x s) (v s) + ε * coefficient Ω (ε * s) * (x s * v s))
      (ε ^ 2 * coefficientDeriv Ω (ε * t) * (x t * v t)) t :=
  hasDerivAt_correctedAction hΩ hpos hx hv

example {Ω : ℝ → ℝ} (hΩ : ContDiff ℝ 2 Ω) {T : ℝ}
    (hT : 0 ≤ T) (hpos : ∀ τ ∈ Icc 0 T, 0 < Ω τ) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ x v : ℝ → ℝ,
      (∀ t ∈ Icc 0 (T / ε), HasDerivAt x (v t) t) →
      (∀ t ∈ Icc 0 (T / ε), HasDerivAt v (-(Ω (ε * t)) ^ 2 * x t) t) →
      ∀ t ∈ Icc 0 (T / ε),
        |action (Ω (ε * t)) (x t) (v t) - action (Ω 0) (x 0) (v 0)| ≤
          C * ε * action (Ω 0) (x 0) (v 0) :=
  exists_forall_abs_action_sub_le hΩ hT hpos

example {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ x v : ℝ → ℝ,
      (∀ t ∈ Icc 0 (T / ε), HasDerivAt x (v t) t) →
      (∀ t ∈ Icc 0 (T / ε), HasDerivAt v (-(Real.exp (ε * t)) ^ 2 * x t) t) →
      ∀ t ∈ Icc 0 (T / ε),
        |action (Real.exp (ε * t)) (x t) (v t) - action (Real.exp 0) (x 0) (v 0)| ≤
          C * ε * action (Real.exp 0) (x 0) (v 0) :=
  exists_forall_abs_action_sub_le_exp hT

example {ω₀ L : ℝ} {x v : ℝ → ℝ}
    (hx : ∀ t ∈ Icc 0 L, HasDerivAt x (v t) t)
    (hv : ∀ t ∈ Icc 0 L, HasDerivAt v (-ω₀ ^ 2 * x t) t) {t : ℝ} (ht : t ∈ Icc 0 L) :
    action ω₀ (x t) (v t) = action ω₀ (x 0) (v 0) :=
  action_eq_of_const hx hv ht

end AdiabaticOscillator
