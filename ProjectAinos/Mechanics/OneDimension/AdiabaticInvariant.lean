/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.OneDimension.WellFamily
public import ProjectAinos.SmoothGeometry.ODE.SlowParameter
public import ProjectAinos.Mechanics.OneDimension.Oscillator
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The adiabatic invariant of one degree of freedom

Landau–Lifshitz §49 for `H = p²/2m + V(λ, x)` with a slowly varying parameter
`λ = Λ(εt)`.

* `IsWellFamily V J α β`: a smooth family of wells of the potentials
  `V(λ, ·)` over an open set `J` of pairs `(E, λ)`; `exists_isWellFamily`
  extends one well to a family.
* `period`, `area`, `parameterForce`: the period, the area `∮ p dx` and
  `∮ ∂V/∂λ dt` of the level curve, as smooth functions of `(E, λ)`, with
  `dA = T dE − (∮ ∂V/∂λ dt) dλ` (`fderiv_area`).
* `invariant` is the action variable `I = A(H, λ)/2π` as a function of the
  point of the phase space and the parameter. It is invariant under the motion
  with a fixed parameter (`fderiv_invariant_frozenField`), and its derivative in
  the parameter is `invariantDeriv` (`fderiv_invariant_parameter`).
* `corrector` is a weighted mean of `invariantDeriv` over a period of the motion
  with a fixed parameter. It is smooth at the points of the level curves
  (`contDiffAt_corrector`), and its derivative along that motion is
  `invariantDeriv` (`fderiv_corrector_frozenField`), because the mean of
  `invariantDeriv` over a period is zero.
* `exists_forall_abs_invariant_sub_le`: the adiabatic theorem,
  `|I(t) − I(0)| ≤ C ε` for `0 ≤ t ≤ T/ε`, for a motion that stays in a compact
  set of points of the level curves.
* `isWellFamily_oscillator`, `invariant_oscillator`: the oscillator with a
  variable stiffness `k` is a family over all positive energies and
  stiffnesses, with `I = E √(m/k)`.
-/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory
open scoped Real ContDiff Topology

namespace ProjectAinos.Mechanics.OneDim.Adiabatic

open SmoothGeometry.NonlinearODE

variable {V : ℝ × ℝ → ℝ} {J : Set (ℝ × ℝ)} {α β : ℝ × ℝ → ℝ} {m : ℝ}

/-- The potential `V(λ, x)` as a function of the pair `(E, λ)` and `x`. -/
def lift (V : ℝ × ℝ → ℝ) (r : (ℝ × ℝ) × ℝ) : ℝ := V (r.1.2, r.2)

theorem contDiff_lift (hV : ContDiff ℝ ∞ V) : ContDiff ℝ ∞ (lift V) :=
  hV.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)

/-- A smooth family of wells of the potentials `V(λ, ·)` over an open set of
pairs `(E, λ)`, with the turning points `α(E, λ) < β(E, λ)`. -/
structure IsWellFamily (V : ℝ × ℝ → ℝ) (J : Set (ℝ × ℝ)) (α β : ℝ × ℝ → ℝ) : Prop where
  /-- The set of pairs is open. -/
  isOpen : IsOpen J
  /-- The left turning point is smooth. -/
  contDiffOn_left : ContDiffOn ℝ ∞ α J
  /-- The right turning point is smooth. -/
  contDiffOn_right : ContDiffOn ℝ ∞ β J
  /-- Each pair has a well. -/
  isWell : ∀ s ∈ J, IsWell (fun y => V (s.2, y)) s.1 (α s) (β s)

/-- A well of one potential of a smooth family extends to a family of wells. -/
theorem exists_isWellFamily (hV : ContDiff ℝ ∞ V) {E₀ lam₀ a₀ b₀ : ℝ}
    (h : IsWell (fun y => V (lam₀, y)) E₀ a₀ b₀) :
    ∃ (J : Set (ℝ × ℝ)) (α β : ℝ × ℝ → ℝ), IsWellFamily V J α β ∧ (E₀, lam₀) ∈ J ∧
      α (E₀, lam₀) = a₀ ∧ β (E₀, lam₀) = b₀ := by
  obtain ⟨J, α, β, hJ, hs, hα₀, hβ₀, hα, hβ, hw⟩ := IsWell.exists_family_param
    (V := lift V) (contDiff_lift hV) (ℰ := Prod.fst) contDiff_fst (s₀ := (E₀, lam₀)) h
  exact ⟨J, α, β, ⟨hJ, hα, hβ, hw⟩, hs, hα₀, hβ₀⟩

/-! ### Functions of the energy and the parameter -/

/-- The period of the level curve of the pair `s = (E, λ)`. -/
def period (m : ℝ) (V : ℝ × ℝ → ℝ) (α β : ℝ × ℝ → ℝ) (s : ℝ × ℝ) : ℝ :=
  orbitPeriod m (fun y => V (s.2, y)) (α s) (β s)

/-- The area `∮ p dx` of the level curve of the pair `s = (E, λ)`. -/
def area (m : ℝ) (V : ℝ × ℝ → ℝ) (α β : ℝ × ℝ → ℝ) (s : ℝ × ℝ) : ℝ :=
  orbitArea m (fun y => V (s.2, y)) (α s) (β s)

/-- The integral `∮ ∂V/∂λ dt` over the level curve of the pair `s = (E, λ)`. -/
def parameterForce (m : ℝ) (V : ℝ × ℝ → ℝ) (α β : ℝ × ℝ → ℝ) (s : ℝ × ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..2 * π, orbitRate m (fun y => V (s.2, y)) (α s) (β s) θ *
    fderiv ℝ V (s.2, orbitPosition (α s) (β s) θ) (1, 0)

theorem contDiffOn_period (hV : ContDiff ℝ ∞ V) (m : ℝ) (hF : IsWellFamily V J α β) :
    ContDiffOn ℝ ∞ (period m V α β) J :=
  contDiffOn_orbitPeriod_family (V := lift V) (ℰ := Prod.fst) (contDiff_lift hV) m hF.isOpen
    hF.contDiffOn_left hF.contDiffOn_right hF.isWell

theorem contDiffOn_area (hV : ContDiff ℝ ∞ V) (m : ℝ) (hF : IsWellFamily V J α β) :
    ContDiffOn ℝ ∞ (area m V α β) J :=
  contDiffOn_orbitArea_family (V := lift V) (ℰ := Prod.fst) (contDiff_lift hV) m hF.isOpen
    hF.contDiffOn_left hF.contDiffOn_right hF.isWell

theorem contDiffOn_parameterForce (hV : ContDiff ℝ ∞ V) (m : ℝ) (hF : IsWellFamily V J α β) :
    ContDiffOn ℝ ∞ (parameterForce m V α β) J := by
  have hg : ContDiff ℝ ∞ fun q : (ℝ × ℝ) × ℝ => fderiv ℝ V (q.1.2, q.2) (1, 0) :=
    ((hV.fderiv_right (m := ∞) (by simp)).comp
      ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)).clm_apply contDiff_const
  exact contDiffOn_integral_orbitRate_mul (V := lift V) (ℰ := Prod.fst) (contDiff_lift hV) m
    hF.isOpen hF.contDiffOn_left hF.contDiffOn_right hF.isWell hg

theorem fderiv_lift (hV : ContDiff ℝ ∞ V) (s : ℝ × ℝ) (x : ℝ) (u : ℝ × ℝ) :
    fderiv ℝ (lift V) (s, x) (u, 0) = u.2 * fderiv ℝ V (s.2, x) (1, 0) := by
  have h1 : HasDerivAt (fun r : ℝ => (((s + r • u, x) : (ℝ × ℝ) × ℝ))) (u, (0 : ℝ)) 0 :=
    (hasDerivAt_line s u).prodMk (hasDerivAt_const (0 : ℝ) x)
  have h2 : HasFDerivAt (lift V) (fderiv ℝ (lift V) (s, x)) (s + (0 : ℝ) • u, x) := by
    simpa using ((contDiff_lift hV).differentiable (by simp) (s, x)).hasFDerivAt
  have h3 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h2 h1
  have h4 : HasDerivAt (fun r : ℝ => ((s.2 + r * u.2, x) : ℝ × ℝ)) (u.2, (0 : ℝ)) 0 := by
    have h5 : HasDerivAt (fun r : ℝ => s.2 + r * u.2) u.2 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const u.2).const_add s.2
    exact h5.prodMk (hasDerivAt_const (0 : ℝ) x)
  have h6 : HasFDerivAt V (fderiv ℝ V (s.2, x)) (s.2 + (0 : ℝ) * u.2, x) := by
    simpa using (hV.differentiable (by simp) (s.2, x)).hasFDerivAt
  have h7 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h6 h4
  have hfun : (lift V ∘ fun r : ℝ => (((s + r • u, x) : (ℝ × ℝ) × ℝ))) =
      (V ∘ fun r : ℝ => ((s.2 + r * u.2, x) : ℝ × ℝ)) := by
    funext r
    simp [lift]
  rw [hfun] at h3
  have h8 := h3.unique h7
  rw [h8]
  have e : ((u.2, (0 : ℝ)) : ℝ × ℝ) = u.2 • ((1 : ℝ), (0 : ℝ)) := by simp
  rw [e, map_smul, smul_eq_mul]

/-- The derivative of the area: `dA = T dE − (∮ ∂V/∂λ dt) dλ`. -/
theorem fderiv_area (hV : ContDiff ℝ ∞ V) (hm : 0 < m) (hF : IsWellFamily V J α β)
    {s : ℝ × ℝ} (hs : s ∈ J) (u : ℝ × ℝ) :
    fderiv ℝ (area m V α β) s u =
      u.1 * period m V α β s - u.2 * parameterForce m V α β s := by
  have h := fderiv_orbitArea_family (V := lift V) (ℰ := Prod.fst) (contDiff_lift hV) hm
    hF.isOpen contDiff_fst hF.contDiffOn_left hF.contDiffOn_right hF.isWell hs u
  have hw := hF.isWell s hs
  have hU := contDiff_slice (contDiff_lift hV) s
  have hcrate : Continuous (orbitRate m (fun y => V (s.2, y)) (α s) (β s)) :=
    (hw.contDiff_orbitRate hU m).continuous
  have hcDV : Continuous fun θ => fderiv ℝ V (s.2, orbitPosition (α s) (β s) θ) (1, 0) :=
    ((hV.continuous_fderiv (by simp)).comp
      (continuous_const.prodMk (contDiff_orbitPosition _ _).continuous)).clm_apply
        continuous_const
  have hpt : ∀ θ : ℝ, orbitRate m (fun y => lift V (s, y)) (α s) (β s) θ *
      (fderiv ℝ Prod.fst s u - fderiv ℝ (lift V) (s, orbitPosition (α s) (β s) θ) (u, 0)) =
      u.1 * orbitRate m (fun y => V (s.2, y)) (α s) (β s) θ -
        u.2 * (orbitRate m (fun y => V (s.2, y)) (α s) (β s) θ *
          fderiv ℝ V (s.2, orbitPosition (α s) (β s) θ) (1, 0)) := by
    intro θ
    rw [fderiv_lift hV, fderiv_fst]
    simp only [ContinuousLinearMap.coe_fst']
    change orbitRate m (fun y => V (s.2, y)) (α s) (β s) θ * _ = _
    ring
  have hc1 : Continuous fun θ => u.1 * orbitRate m (fun y => V (s.2, y)) (α s) (β s) θ :=
    continuous_const.mul hcrate
  have hc2 : Continuous fun θ => u.2 * (orbitRate m (fun y => V (s.2, y)) (α s) (β s) θ *
      fderiv ℝ V (s.2, orbitPosition (α s) (β s) θ) (1, 0)) :=
    continuous_const.mul (hcrate.mul hcDV)
  change fderiv ℝ (fun s => orbitArea m (fun y => lift V (s, y)) (α s) (β s)) s u = _
  rw [h, intervalIntegral.integral_congr fun θ _ => hpt θ,
    intervalIntegral.integral_sub
      (f := fun θ => u.1 * orbitRate m (fun y => V (s.2, y)) (α s) (β s) θ)
      (g := fun θ => u.2 * (orbitRate m (fun y => V (s.2, y)) (α s) (β s) θ *
        fderiv ℝ V (s.2, orbitPosition (α s) (β s) θ) (1, 0)))
      (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rfl

/-! ### Functions on the phase space with the parameter -/

/-- The energy `p²/2m + V(λ, x)` at the point `w = ((x, p), λ)`. -/
def energyAt (m : ℝ) (V : ℝ × ℝ → ℝ) (w : (ℝ × ℝ) × ℝ) : ℝ :=
  w.1.2 ^ 2 / (2 * m) + V (w.2, w.1.1)

/-- The pair `(E, λ)` of a point of the phase space with the parameter. -/
def level (m : ℝ) (V : ℝ × ℝ → ℝ) (w : (ℝ × ℝ) × ℝ) : ℝ × ℝ := (energyAt m V w, w.2)

/-- The Hamiltonian field at a fixed parameter. -/
def frozenField (m : ℝ) (V : ℝ × ℝ → ℝ) (w : (ℝ × ℝ) × ℝ) : ℝ × ℝ :=
  (w.1.2 / m, -fderiv ℝ V (w.2, w.1.1) (0, 1))

theorem energyAt_eq (m : ℝ) (V : ℝ × ℝ → ℝ) (z : ℝ × ℝ) (lam : ℝ) :
    energyAt m V (z, lam) = energy m (fun y => V (lam, y)) z :=
  rfl

theorem frozenField_eq (hV : ContDiff ℝ ∞ V) (m : ℝ) (z : ℝ × ℝ) (lam : ℝ) :
    frozenField m V (z, lam) = field m (fun y => V (lam, y)) z := by
  rw [frozenField, field, deriv_slice hV lam]
  rfl

theorem contDiff_energyAt (hV : ContDiff ℝ ∞ V) (m : ℝ) : ContDiff ℝ ∞ (energyAt m V) :=
  (((contDiff_snd.comp contDiff_fst).pow 2).div_const _).add
    (hV.comp (contDiff_snd.prodMk (contDiff_fst.comp contDiff_fst)))

theorem contDiff_level (hV : ContDiff ℝ ∞ V) (m : ℝ) : ContDiff ℝ ∞ (level m V) :=
  (contDiff_energyAt hV m).prodMk contDiff_snd

theorem hasDerivAt_energyAt_line (hV : ContDiff ℝ ∞ V) (m : ℝ) (w u : (ℝ × ℝ) × ℝ) :
    HasDerivAt (fun r : ℝ => energyAt m V (w + r • u))
      (w.1.2 * u.1.2 / m + fderiv ℝ V (w.2, w.1.1) (u.2, u.1.1)) 0 := by
  have hfun : (fun r : ℝ => energyAt m V (w + r • u)) = fun r =>
      (w.1.2 + r * u.1.2) ^ 2 / (2 * m) + V (w.2 + r * u.2, w.1.1 + r * u.1.1) := by
    funext r
    simp [energyAt]
  have hp : HasDerivAt (fun r : ℝ => w.1.2 + r * u.1.2) u.1.2 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const u.1.2).const_add w.1.2
  have h1 : HasDerivAt (fun r : ℝ => (w.1.2 + r * u.1.2) ^ 2 / (2 * m))
      (2 * (w.1.2 + 0 * u.1.2) * u.1.2 / (2 * m)) 0 := by
    refine ((hp.pow 2).div_const (2 * m)).congr_deriv ?_
    norm_num
  have hl : HasDerivAt (fun r : ℝ => w.2 + r * u.2) u.2 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const u.2).const_add w.2
  have hx : HasDerivAt (fun r : ℝ => w.1.1 + r * u.1.1) u.1.1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const u.1.1).const_add w.1.1
  have h2 : HasFDerivAt V (fderiv ℝ V (w.2, w.1.1)) (w.2 + (0 : ℝ) * u.2, w.1.1 + 0 * u.1.1) := by
    simpa using (hV.differentiable (by simp) (w.2, w.1.1)).hasFDerivAt
  have h3 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h2 (hl.prodMk hx)
  rw [hfun]
  refine (h1.add h3).congr_deriv ?_
  rw [zero_mul, add_zero]
  ring

theorem fderiv_energyAt (hV : ContDiff ℝ ∞ V) (m : ℝ) (w u : (ℝ × ℝ) × ℝ) :
    fderiv ℝ (energyAt m V) w u =
      w.1.2 * u.1.2 / m + fderiv ℝ V (w.2, w.1.1) (u.2, u.1.1) := by
  have h1 : HasFDerivAt (energyAt m V) (fderiv ℝ (energyAt m V) w) (w + (0 : ℝ) • u) := by
    simpa using ((contDiff_energyAt hV m).differentiable (by simp) w).hasFDerivAt
  have h2 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h1 (hasDerivAt_line w u)
  exact h2.unique (hasDerivAt_energyAt_line hV m w u)

/-- The energy is constant along the field with a fixed parameter. -/
theorem fderiv_energyAt_frozenField (hV : ContDiff ℝ ∞ V) (m : ℝ) (w : (ℝ × ℝ) × ℝ) :
    fderiv ℝ (energyAt m V) w (frozenField m V w, 0) = 0 := by
  rw [fderiv_energyAt hV]
  have e : (((0 : ℝ), w.1.2 / m) : ℝ × ℝ) = (w.1.2 / m) • ((0 : ℝ), (1 : ℝ)) := by simp
  simp only [frozenField]
  rw [e, map_smul, smul_eq_mul]
  ring

theorem fderiv_energyAt_parameter (hV : ContDiff ℝ ∞ V) (m : ℝ) (w : (ℝ × ℝ) × ℝ) :
    fderiv ℝ (energyAt m V) w (0, 1) = fderiv ℝ V (w.2, w.1.1) (1, 0) := by
  rw [fderiv_energyAt hV]
  simp

theorem fderiv_level (hV : ContDiff ℝ ∞ V) (m : ℝ) (w u : (ℝ × ℝ) × ℝ) :
    fderiv ℝ (level m V) w u = (fderiv ℝ (energyAt m V) w u, u.2) := by
  have h1 : HasFDerivAt (level m V)
      ((fderiv ℝ (energyAt m V) w).prod (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ)) w :=
    ((contDiff_energyAt hV m).differentiable (by simp) w).hasFDerivAt.prodMk hasFDerivAt_snd
  rw [h1.fderiv]
  rfl

/-- The action variable `I = A(H, λ)/2π`, as a function of the point of the
phase space and the parameter. -/
def invariant (m : ℝ) (V : ℝ × ℝ → ℝ) (α β : ℝ × ℝ → ℝ) (w : (ℝ × ℝ) × ℝ) : ℝ :=
  area m V α β (level m V w) / (2 * π)

/-- The derivative of the action variable in the parameter, at a fixed point of
the phase space: `(T ∂V/∂λ − ∮ ∂V/∂λ dt)/2π`. -/
def invariantDeriv (m : ℝ) (V : ℝ × ℝ → ℝ) (α β : ℝ × ℝ → ℝ) (w : (ℝ × ℝ) × ℝ) : ℝ :=
  (period m V α β (level m V w) * fderiv ℝ V (w.2, w.1.1) (1, 0) -
    parameterForce m V α β (level m V w)) / (2 * π)

theorem invariant_eq (m : ℝ) (V : ℝ × ℝ → ℝ) (α β : ℝ × ℝ → ℝ) :
    invariant m V α β = fun w => (area m V α β ∘ level m V) w * (2 * π)⁻¹ := by
  funext w
  rw [invariant, div_eq_mul_inv]
  rfl

theorem differentiableAt_invariant (hV : ContDiff ℝ ∞ V) (m : ℝ) (hF : IsWellFamily V J α β)
    {w : (ℝ × ℝ) × ℝ} (hw : level m V w ∈ J) : DifferentiableAt ℝ (invariant m V α β) w := by
  have hA : DifferentiableAt ℝ (area m V α β) (level m V w) :=
    ((contDiffOn_area hV m hF).contDiffAt (hF.isOpen.mem_nhds hw)).differentiableAt (by simp)
  have hL : DifferentiableAt ℝ (level m V) w := (contDiff_level hV m).differentiable (by simp) w
  rw [invariant_eq]
  exact (hA.comp w hL).mul_const _

theorem fderiv_invariant (hV : ContDiff ℝ ∞ V) (hm : 0 < m) (hF : IsWellFamily V J α β)
    {w : (ℝ × ℝ) × ℝ} (hw : level m V w ∈ J) (u : (ℝ × ℝ) × ℝ) :
    fderiv ℝ (invariant m V α β) w u =
      (fderiv ℝ (energyAt m V) w u * period m V α β (level m V w) -
        u.2 * parameterForce m V α β (level m V w)) / (2 * π) := by
  have hA : DifferentiableAt ℝ (area m V α β) (level m V w) :=
    ((contDiffOn_area hV m hF).contDiffAt (hF.isOpen.mem_nhds hw)).differentiableAt (by simp)
  have hL := ((contDiff_level hV m).differentiable (by simp) w).hasFDerivAt
  have h1 := (hA.hasFDerivAt.comp w hL).mul_const (2 * π)⁻¹
  rw [invariant_eq, h1.fderiv]
  change (2 * π)⁻¹ * fderiv ℝ (area m V α β) (level m V w) (fderiv ℝ (level m V) w u) = _
  rw [fderiv_level hV, fderiv_area hV hm hF hw]
  ring

/-- The action variable is invariant under the motion with a fixed parameter. -/
theorem fderiv_invariant_frozenField (hV : ContDiff ℝ ∞ V) (hm : 0 < m)
    (hF : IsWellFamily V J α β) {w : (ℝ × ℝ) × ℝ} (hw : level m V w ∈ J) :
    fderiv ℝ (invariant m V α β) w (frozenField m V w, 0) = 0 := by
  rw [fderiv_invariant hV hm hF hw, fderiv_energyAt_frozenField hV]
  simp

/-- The derivative of the action variable in the parameter. -/
theorem fderiv_invariant_parameter (hV : ContDiff ℝ ∞ V) (hm : 0 < m)
    (hF : IsWellFamily V J α β) {w : (ℝ × ℝ) × ℝ} (hw : level m V w ∈ J) :
    fderiv ℝ (invariant m V α β) w (0, 1) = invariantDeriv m V α β w := by
  rw [fderiv_invariant hV hm hF hw, fderiv_energyAt_parameter hV, invariantDeriv]
  ring

/-! ### The motion with a fixed parameter -/

/-- The points of the phase space with the parameter that lie on a level curve
of the family. -/
def wellRegion (m : ℝ) (V : ℝ × ℝ → ℝ) (J : Set (ℝ × ℝ)) (α β : ℝ × ℝ → ℝ) :
    Set ((ℝ × ℝ) × ℝ) :=
  {w | level m V w ∈ J ∧ w.1.1 ∈ Icc (α (level m V w)) (β (level m V w))}

/-- Through a point of the region there is a motion with the fixed parameter:
it stays on the level curve, has the period of the curve, and the integral of
`∂V/∂λ` along a period is `parameterForce`. -/
theorem exists_orbit (hV : ContDiff ℝ ∞ V) (hm : 0 < m) (hF : IsWellFamily V J α β)
    {w : (ℝ × ℝ) × ℝ} (hw : w ∈ wellRegion m V J α β) :
    ∃ y : ℝ → ℝ × ℝ, y 0 = w.1 ∧
      (∀ s, HasDerivAt y (frozenField m V (y s, w.2)) s) ∧
      (∀ s, level m V (y s, w.2) = level m V w) ∧
      (∀ s, (y s, w.2) ∈ wellRegion m V J α β) ∧
      (∀ s, y (s + period m V α β (level m V w)) = y s) ∧
      (∫ s in (0 : ℝ)..period m V α β (level m V w), fderiv ℝ V (w.2, (y s).1) (1, 0)) =
        parameterForce m V α β (level m V w) := by
  obtain ⟨U, hUdef⟩ : ∃ U : ℝ → ℝ, U = fun y => V (w.2, y) := ⟨_, rfl⟩
  have hU : ContDiff ℝ ∞ U := hUdef ▸ contDiff_slice hV w.2
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = α (level m V w) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = β (level m V w) := ⟨_, rfl⟩
  have hwell : IsWell U (energyAt m V w) a b := by
    rw [hUdef, ha, hb]
    exact hF.isWell (level m V w) hw.1
  have hE : energy m U w.1 = energyAt m V w := by
    rw [hUdef]
    rfl
  obtain ⟨t₀, ht₀⟩ := hwell.exists_wellMotion_eq hU hm (z := w.1) (by rw [ha, hb]; exact hw.2) hE
  have hper : period m V α β (level m V w) = orbitPeriod m U a b := by
    rw [hUdef, ha, hb]
    rfl
  have hlevel : ∀ s, level m V (wellMotion m U a b (s + t₀), w.2) = level m V w := by
    intro s
    have h1 : energyAt m V (wellMotion m U a b (s + t₀), w.2) = energyAt m V w := by
      rw [energyAt_eq, ← hUdef]
      exact hwell.energy_wellMotion hU hm _
    exact Prod.ext h1 rfl
  have hy0 : wellMotion m U a b (0 + t₀) = w.1 := by rw [zero_add, ht₀]
  refine ⟨fun s => wellMotion m U a b (s + t₀), hy0, fun s => ?_, hlevel,
    fun s => ⟨?_, ?_⟩, fun s => ?_, ?_⟩
  · rw [frozenField_eq hV, ← hUdef]
    exact (hwell.hasDerivAt_wellMotion hU hm (s + t₀)).comp_add_const s t₀
  · rw [hlevel s]
    exact hw.1
  · rw [hlevel s, ← ha, ← hb]
    exact orbitPosition_mem_Icc hwell.lt.le _
  · rw [hper]
    have e : s + orbitPeriod m U a b + t₀ = s + t₀ + orbitPeriod m U a b := by ring
    change wellMotion m U a b (s + orbitPeriod m U a b + t₀) = wellMotion m U a b (s + t₀)
    rw [e, hwell.wellMotion_add_period hU hm]
  · obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun s => fderiv ℝ V (w.2, (wellMotion m U a b s).1) (1, 0) :=
      ⟨_, rfl⟩
    have hcw : Continuous (wellMotion m U a b) :=
      continuous_iff_continuousAt.mpr fun s => (hwell.hasDerivAt_wellMotion hU hm s).continuousAt
    have hgc : Continuous g := by
      rw [hg]
      exact ((hV.continuous_fderiv (by simp)).comp
        (continuous_const.prodMk (continuous_fst.comp hcw))).clm_apply continuous_const
    have hgper : Function.Periodic g (orbitPeriod m U a b) := by
      intro s
      rw [hg]
      change fderiv ℝ V (w.2, (wellMotion m U a b (s + orbitPeriod m U a b)).1) (1, 0) = _
      rw [hwell.wellMotion_add_period hU hm]
    have h1 : (∫ s in (0 : ℝ)..period m V α β (level m V w),
        fderiv ℝ V (w.2, (wellMotion m U a b (s + t₀)).1) (1, 0)) =
        ∫ s in (0 : ℝ)..orbitPeriod m U a b, g s := by
      rw [hper]
      have h2 := intervalIntegral.integral_comp_add_right (a := 0) (b := orbitPeriod m U a b) g t₀
      rw [hg] at h2 ⊢
      rw [h2, zero_add, add_comm (orbitPeriod m U a b) t₀]
      have h3 := hgper.intervalIntegral_add_eq t₀ 0
      rw [hg, zero_add] at h3
      exact h3
    rw [h1]
    -- the substitution of the time by the angle
    have hsub := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := 2 * π)
      (f := orbitTime m U a b) (f' := orbitRate m U a b) (g := g)
      (fun θ _ => hwell.hasDerivAt_orbitTime hU m θ)
      (hwell.contDiff_orbitRate hU m).continuous.continuousOn hgc
    have h0 : orbitTime m U a b 0 = 0 := by simp [orbitTime]
    have hT : orbitTime m U a b (2 * π) = orbitPeriod m U a b := rfl
    rw [h0, hT] at hsub
    rw [← hsub, parameterForce]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hpos : (wellMotion m U a b (orbitTime m U a b θ)).1 = orbitPosition a b θ := by
      rw [wellMotion, hwell.orbitAngle_orbitTime hU hm θ]
      rfl
    change (g ∘ orbitTime m U a b) θ * orbitRate m U a b θ = _
    rw [Function.comp_apply, hg]
    change fderiv ℝ V (w.2, (wellMotion m U a b (orbitTime m U a b θ)).1) (1, 0) * _ = _
    rw [hpos, mul_comm, hUdef, ha, hb]
    rfl

/-- The field of the phase space with the parameter, which is constant. -/
def extendedField (m : ℝ) (V : ℝ × ℝ → ℝ) (w : (ℝ × ℝ) × ℝ) : (ℝ × ℝ) × ℝ :=
  (frozenField m V w, 0)

theorem contDiff_extendedField (hV : ContDiff ℝ ∞ V) (m : ℝ) :
    ContDiff ℝ ∞ (extendedField m V) := by
  have h1 : ContDiff ℝ ∞ fun w : (ℝ × ℝ) × ℝ => fderiv ℝ V (w.2, w.1.1) (0, 1) :=
    ((hV.fderiv_right (m := ∞) (by simp)).comp
      (contDiff_snd.prodMk (contDiff_fst.comp contDiff_fst))).clm_apply contDiff_const
  exact (((contDiff_snd.comp contDiff_fst).div_const m).prodMk h1.neg).prodMk contDiff_const

/-- A motion with a fixed parameter is a line of the flow of the extended
field. -/
theorem flow_extendedField (hV : ContDiff ℝ ∞ V) (m : ℝ) {y : ℝ → ℝ × ℝ} {lam : ℝ}
    (hy : ∀ s, HasDerivAt y (frozenField m V (y s, lam)) s) (t : ℝ) :
    (t, (y 0, lam)) ∈ flowDomain (extendedField m V) ∧
      flow (extendedField m V) (t, (y 0, lam)) = (y t, lam) := by
  have hc : ∀ r ∈ uIcc 0 t, HasDerivWithinAt (fun s => ((y s, lam) : (ℝ × ℝ) × ℝ))
      (extendedField m V (y r, lam)) (uIcc 0 t) r := fun r _ =>
    ((hy r).prodMk (hasDerivAt_const r lam)).hasDerivWithinAt
  exact ⟨mem_flowDomain_of_hasDerivWithinAt (contDiff_extendedField hV m).continuous
      (y := fun s => ((y s, lam) : (ℝ × ℝ) × ℝ)) rfl hc,
    flow_eq_of_hasDerivWithinAt ((contDiff_extendedField hV m).of_le (by simp))
      (y := fun s => ((y s, lam) : (ℝ × ℝ) × ℝ)) rfl hc⟩

/-! ### The corrector -/

/-- A weighted mean over a period of a periodic function of mean zero, as a
function of the shift: its derivative at zero is the value at zero. -/
theorem hasDerivAt_weighted_shift {φ : ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hφ : Continuous φ)
    (hper : Function.Periodic φ T) (hmean : ∫ s in (0 : ℝ)..T, φ s = 0) :
    HasDerivAt (fun r : ℝ => T * ∫ σ in (0 : ℝ)..1, σ * φ (T * σ + r)) (φ 0) 0 := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℝ → ℝ, Ψ = fun x => ∫ v in (0 : ℝ)..x, v * φ v := ⟨_, rfl⟩
  have hvc : Continuous fun v : ℝ => v * φ v := continuous_id.mul hφ
  have hΨd : ∀ x : ℝ, HasDerivAt Ψ (x * φ x) x := by
    intro x
    rw [hΨ]
    exact intervalIntegral.integral_hasDerivAt_right (hvc.intervalIntegrable _ _)
      (hvc.stronglyMeasurableAtFilter _ _) hvc.continuousAt
  have hK : ∀ r : ℝ, T * ∫ σ in (0 : ℝ)..1, σ * φ (T * σ + r) = (Ψ (r + T) - Ψ r) / T := by
    intro r
    have h1 : ∀ σ : ℝ, σ * φ (T * σ + r) =
        (fun v : ℝ => (v - r) / T * φ v) (T * σ + r) := by
      intro σ
      simp only
      rw [add_sub_cancel_right, mul_div_cancel_left₀ σ hT.ne']
    have h2 := intervalIntegral.integral_comp_mul_add (a := 0) (b := 1)
      (f := fun v : ℝ => (v - r) / T * φ v) hT.ne' r
    rw [mul_zero, zero_add, mul_one, smul_eq_mul, add_comm T r] at h2
    have h3 : (∫ v in r..r + T, (v - r) / T * φ v) =
        ((∫ v in r..r + T, v * φ v) - r * ∫ v in r..r + T, φ v) / T := by
      have e : ∀ v : ℝ, (v - r) / T * φ v = (v * φ v - r * φ v) / T := fun v => by ring
      simp_rw [e]
      have hrc : Continuous fun v : ℝ => r * φ v := continuous_const.mul hφ
      rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
        (f := fun v : ℝ => v * φ v) (g := fun v : ℝ => r * φ v)
        (hvc.intervalIntegrable _ _) (hrc.intervalIntegrable _ _),
        intervalIntegral.integral_const_mul]
    have h4 : (∫ v in r..r + T, φ v) = 0 := by
      rw [hper.intervalIntegral_add_eq r 0, zero_add, hmean]
    have h5 : (∫ v in r..r + T, v * φ v) = Ψ (r + T) - Ψ r := by
      rw [hΨ]
      exact (intervalIntegral.integral_interval_sub_left (hvc.intervalIntegrable _ _)
        (hvc.intervalIntegrable _ _)).symm
    rw [intervalIntegral.integral_congr fun σ _ => h1 σ, h2, h3, h4, h5, mul_zero, sub_zero]
    field_simp
  have hd : HasDerivAt (fun r : ℝ => (Ψ (r + T) - Ψ r) / T)
      (((0 + T) * φ (0 + T) - 0 * φ 0) / T) 0 :=
    (((hΨd (0 + T)).comp_add_const 0 T).sub (hΨd 0)).div_const T
  have hfun : (fun r : ℝ => T * ∫ σ in (0 : ℝ)..1, σ * φ (T * σ + r)) =
      fun r => (Ψ (r + T) - Ψ r) / T := funext hK
  rw [hfun]
  refine hd.congr_deriv ?_
  rw [hper 0]
  field_simp
  ring

/-- The corrector of the first order of the action variable: a weighted mean
of `∂I/∂λ` over the period of the motion with a fixed parameter. -/
def corrector (m : ℝ) (V : ℝ × ℝ → ℝ) (α β : ℝ × ℝ → ℝ) (w : (ℝ × ℝ) × ℝ) : ℝ :=
  period m V α β (level m V w) * ∫ σ in (0 : ℝ)..1,
    σ * ((period m V α β (level m V w) *
        fderiv ℝ V (w.2, (flow (extendedField m V)
          (period m V α β (level m V w) * σ, w)).1.1) (1, 0) -
      parameterForce m V α β (level m V w)) / (2 * π))

/-- The corrector along a motion with a fixed parameter. -/
theorem corrector_orbit (hV : ContDiff ℝ ∞ V) (m : ℝ) (α β : ℝ × ℝ → ℝ) {w : (ℝ × ℝ) × ℝ}
    {y : ℝ → ℝ × ℝ} (hy : ∀ s, HasDerivAt y (frozenField m V (y s, w.2)) s)
    (hlevel : ∀ s, level m V (y s, w.2) = level m V w) (r : ℝ) :
    corrector m V α β (y r, w.2) =
      period m V α β (level m V w) * ∫ σ in (0 : ℝ)..1,
        σ * ((period m V α β (level m V w) *
            fderiv ℝ V (w.2, (y (period m V α β (level m V w) * σ + r)).1) (1, 0) -
          parameterForce m V α β (level m V w)) / (2 * π)) := by
  have hyr : ∀ s, HasDerivAt (fun s => y (s + r)) (frozenField m V (y (s + r), w.2)) s :=
    fun s => (hy (s + r)).comp_add_const s r
  have hflow : ∀ t : ℝ, flow (extendedField m V) (t, (y r, w.2)) = (y (t + r), w.2) := by
    intro t
    have h := (flow_extendedField hV m hyr t).2
    simp only [zero_add] at h
    exact h
  rw [corrector, hlevel r]
  congr 1
  refine intervalIntegral.integral_congr fun σ _ => ?_
  simp only [hflow]

/-- The corrector is smooth at the points of the region. -/
theorem contDiffAt_corrector (hV : ContDiff ℝ ∞ V) (hm : 0 < m) (hF : IsWellFamily V J α β)
    {w₀ : (ℝ × ℝ) × ℝ} (hw₀ : w₀ ∈ wellRegion m V J α β) :
    ContDiffAt ℝ ∞ (corrector m V α β) w₀ := by
  have hY := contDiff_extendedField hV m
  have hO₁ : IsOpen (level m V ⁻¹' J) := hF.isOpen.preimage (contDiff_level hV m).continuous
  have hτ : ContDiffOn ℝ ∞ (fun w => period m V α β (level m V w)) (level m V ⁻¹' J) :=
    (contDiffOn_period hV m hF).comp (contDiff_level hV m).contDiffOn fun w hw => hw
  have hPF : ContDiffOn ℝ ∞ (fun w => parameterForce m V α β (level m V w))
      (level m V ⁻¹' J) :=
    (contDiffOn_parameterForce hV m hF).comp (contDiff_level hV m).contDiffOn fun w hw => hw
  obtain ⟨U₁, hU₁def⟩ : ∃ U₁ : Set (((ℝ × ℝ) × ℝ) × ℝ),
      U₁ = Prod.fst ⁻¹' (level m V ⁻¹' J) := ⟨_, rfl⟩
  have hU₁ : IsOpen U₁ := hU₁def ▸ hO₁.preimage continuous_fst
  have hτ' : ContDiffOn ℝ ∞
      (fun q : ((ℝ × ℝ) × ℝ) × ℝ => period m V α β (level m V q.1)) U₁ :=
    hτ.comp contDiffOn_fst fun q hq => by rw [hU₁def] at hq; exact hq
  have hPF' : ContDiffOn ℝ ∞
      (fun q : ((ℝ × ℝ) × ℝ) × ℝ => parameterForce m V α β (level m V q.1)) U₁ :=
    hPF.comp contDiffOn_fst fun q hq => by rw [hU₁def] at hq; exact hq
  have hκ : ContDiffOn ℝ ∞ (fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
      ((period m V α β (level m V q.1) * q.2, q.1) : ℝ × ((ℝ × ℝ) × ℝ))) U₁ :=
    (hτ'.mul contDiffOn_snd).prodMk contDiffOn_fst
  obtain ⟨U, hUdef⟩ : ∃ U : Set (((ℝ × ℝ) × ℝ) × ℝ),
      U = U₁ ∩ (fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
        ((period m V α β (level m V q.1) * q.2, q.1) : ℝ × ((ℝ × ℝ) × ℝ))) ⁻¹'
          flowDomain (extendedField m V) := ⟨_, rfl⟩
  have hU : IsOpen U := hUdef ▸ hκ.continuousOn.isOpen_inter_preimage hU₁ (isOpen_flowDomain hY)
  have hUsub : U ⊆ U₁ := hUdef ▸ inter_subset_left
  have hflow : ContDiffOn ℝ ∞ (fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
      flow (extendedField m V) (period m V α β (level m V q.1) * q.2, q.1)) U :=
    (contDiffOn_flow hY).comp (hκ.mono hUsub) fun q hq => by
      rw [hUdef] at hq
      exact hq.2
  have hDV : ContDiff ℝ ∞ fun p : ℝ × ℝ => fderiv ℝ V p (1, 0) :=
    (hV.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hx : ContDiffOn ℝ ∞ (fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
      ((q.1.2, (flow (extendedField m V)
        (period m V α β (level m V q.1) * q.2, q.1)).1.1) : ℝ × ℝ)) U :=
    (contDiff_snd.comp contDiff_fst).contDiffOn.prodMk
      ((contDiff_fst.comp contDiff_fst).comp_contDiffOn hflow)
  have hg : ContDiffOn ℝ ∞ (fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
      q.2 * ((period m V α β (level m V q.1) *
          fderiv ℝ V (q.1.2, (flow (extendedField m V)
            (period m V α β (level m V q.1) * q.2, q.1)).1.1) (1, 0) -
        parameterForce m V α β (level m V q.1)) / (2 * π))) U :=
    contDiffOn_snd.mul ((((hτ'.mono hUsub).mul (hDV.comp_contDiffOn hx)).sub
      (hPF'.mono hUsub)).div_const _)
  obtain ⟨y, hy0, hy, -, -, -, -⟩ := exists_orbit hV hm hF hw₀
  have hseg : ∀ σ ∈ uIcc (0 : ℝ) 1, (w₀, σ) ∈ U := by
    intro σ _
    rw [hUdef, hU₁def]
    refine ⟨hw₀.1, ?_⟩
    have h := (flow_extendedField hV m hy (period m V α β (level m V w₀) * σ)).1
    rw [hy0] at h
    exact h
  have hint := Variational.contDiffAt_parametric_intervalIntegral hU hg hseg
  have hτat : ContDiffAt ℝ ∞ (fun w => period m V α β (level m V w)) w₀ :=
    hτ.contDiffAt (hO₁.mem_nhds hw₀.1)
  exact hτat.mul hint

/-- The homological equation of the corrector: its derivative along the motion
with a fixed parameter is the derivative of the action variable in the
parameter. -/
theorem fderiv_corrector_frozenField (hV : ContDiff ℝ ∞ V) (hm : 0 < m)
    (hF : IsWellFamily V J α β) {w : (ℝ × ℝ) × ℝ} (hw : w ∈ wellRegion m V J α β) :
    fderiv ℝ (corrector m V α β) w (frozenField m V w, 0) = invariantDeriv m V α β w := by
  obtain ⟨y, hy0, hy, hlevel, -, hper, hint⟩ := exists_orbit hV hm hF hw
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = period m V α β (level m V w) := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = parameterForce m V α β (level m V w) := ⟨_, rfl⟩
  rw [← hTdef] at hper hint
  rw [← hSdef] at hint
  have hTpos : 0 < T := by
    rw [hTdef]
    exact (hF.isWell _ hw.1).orbitPeriod_pos (contDiff_slice hV _) hm
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun s => fderiv ℝ V (w.2, (y s).1) (1, 0) := ⟨_, rfl⟩
  have hyc : Continuous y := continuous_iff_continuousAt.mpr fun s => (hy s).continuousAt
  have hgc : Continuous g := by
    rw [hg]
    exact ((hV.continuous_fderiv (by simp)).comp
      (continuous_const.prodMk (continuous_fst.comp hyc))).clm_apply continuous_const
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → ℝ, φ = fun s => (T * g s - S) / (2 * π) := ⟨_, rfl⟩
  have hφc : Continuous φ := by
    rw [hφ]
    exact ((continuous_const.mul hgc).sub continuous_const).div_const _
  have hφper : Function.Periodic φ T := by
    intro s
    rw [hφ, hg]
    simp only [hper s]
  have hgint : ∫ s in (0 : ℝ)..T, g s = S := by
    rw [hg]
    exact hint
  have hmean : ∫ s in (0 : ℝ)..T, φ s = 0 := by
    have hTg : Continuous fun s : ℝ => T * g s := continuous_const.mul hgc
    rw [hφ, intervalIntegral.integral_div, intervalIntegral.integral_sub
      (f := fun s : ℝ => T * g s) (g := fun _ : ℝ => S)
      (hTg.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, hgint, intervalIntegral.integral_const]
    simp
  have hK := hasDerivAt_weighted_shift hTpos hφc hφper hmean
  have hcorr : (fun r : ℝ => corrector m V α β (y r, w.2)) =
      fun r => T * ∫ σ in (0 : ℝ)..1, σ * φ (T * σ + r) := by
    funext r
    rw [corrector_orbit hV m α β hy hlevel r, ← hTdef, ← hSdef, hφ, hg]
  rw [← hcorr] at hK
  have hc : HasDerivAt (fun r : ℝ => ((y r, w.2) : (ℝ × ℝ) × ℝ))
      (frozenField m V (y 0, w.2), (0 : ℝ)) 0 :=
    (hy 0).prodMk (hasDerivAt_const (0 : ℝ) w.2)
  rw [hy0] at hc
  have hdiff : HasFDerivAt (corrector m V α β) (fderiv ℝ (corrector m V α β) w) (y 0, w.2) := by
    rw [hy0]
    exact ((contDiffAt_corrector hV hm hF hw).differentiableAt (by simp)).hasFDerivAt
  have hchain := HasFDerivAt.comp_hasDerivAt (0 : ℝ) hdiff hc
  have hval := hchain.unique hK
  rw [hval, hφ, hg, invariantDeriv, ← hTdef, ← hSdef]
  simp only [hy0]

/-! ### The adiabatic theorem -/

/-- **The adiabatic theorem for one degree of freedom** (Landau–Lifshitz §49).
For `H = p²/2m + V(λ, x)` with `λ = Λ(εt)`, and a compact set `K` of points on
the level curves of a family of wells, there is a constant `C` such that for
every `ε > 0` the action variable of a motion that stays in `K` changes by at
most `C ε` up to the time `T/ε`. -/
theorem exists_forall_abs_invariant_sub_le (hV : ContDiff ℝ ∞ V) (hm : 0 < m)
    (hF : IsWellFamily V J α β) {K : Set ((ℝ × ℝ) × ℝ)} (hK : IsCompact K)
    (hKw : K ⊆ wellRegion m V J α β) {Λ : ℝ → ℝ} (hΛ : ContDiff ℝ 2 Λ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ z : ℝ → ℝ × ℝ,
      (∀ t ∈ Icc 0 (T / ε), HasDerivAt z (frozenField m V (z t, Λ (ε * t))) t) →
      (∀ t ∈ Icc 0 (T / ε), (z t, Λ (ε * t)) ∈ K) →
      ∀ t ∈ Icc 0 (T / ε),
        |invariant m V α β (z t, Λ (ε * t)) - invariant m V α β (z 0, Λ 0)| ≤ C * ε := by
  have hΛ1 : ContDiff ℝ 1 (deriv Λ) := by
    have h2 : ContDiff ℝ (1 + 1) Λ := by
      rw [one_add_one_eq_two]
      exact hΛ
    exact h2.deriv'
  have hΛd : ∀ τ : ℝ, HasDerivAt Λ (deriv Λ τ) τ := fun τ =>
    (hΛ.differentiable (by norm_num) τ).hasDerivAt
  have hΛd' : ∀ τ : ℝ, HasDerivAt (deriv Λ) (deriv (deriv Λ) τ) τ := fun τ =>
    (hΛ1.differentiable one_ne_zero τ).hasDerivAt
  obtain ⟨L₁, hL₁⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 T)
    (f := deriv Λ) hΛ1.continuous.continuousOn
  obtain ⟨L₂, hL₂⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 T)
    (f := deriv (deriv Λ)) (hΛ1.continuous_deriv le_rfl).continuousOn
  have hGat : ∀ w ∈ K, ContDiffAt ℝ ∞ (corrector m V α β) w := fun w hw =>
    contDiffAt_corrector hV hm hF (hKw hw)
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn (f := corrector m V α β)
    fun w hw => (hGat w hw).continuousAt.continuousWithinAt
  obtain ⟨M₁, hM₁⟩ := hK.exists_bound_of_continuousOn
    (f := fun w => fderiv ℝ (corrector m V α β) w (0, 1))
    fun w hw => (((hGat w hw).continuousAt_fderiv (by simp)).clm_apply
      continuousAt_const).continuousWithinAt
  refine ⟨T * (L₂ * M₀ + L₁ ^ 2 * M₁) + 2 * L₁ * M₀, fun ε hε z hz hzK t ht => ?_⟩
  have h := SmoothGeometry.SlowParameter.abs_sub_le_of_corrector (X := frozenField m V)
    (I := invariant m V α β) (G := corrector m V α β)
    (I' := fderiv ℝ (invariant m V α β)) (G' := fderiv ℝ (corrector m V α β)) (S := K)
    (Λ := Λ) (Λ' := deriv Λ) (Λ'' := deriv (deriv Λ)) hε hT
    (fun w hw => (differentiableAt_invariant hV m hF (hKw hw).1).hasFDerivAt)
    (fun w hw => ((hGat w hw).differentiableAt (by simp)).hasFDerivAt)
    (fun w hw => fderiv_invariant_frozenField hV hm hF (hKw hw).1)
    (fun w hw => by
      rw [fderiv_invariant_parameter hV hm hF (hKw hw).1,
        fderiv_corrector_frozenField hV hm hF (hKw hw)])
    (fun τ _ => hΛd τ) (fun τ _ => hΛd' τ)
    (fun τ hτ => by simpa using hL₁ τ hτ) (fun τ hτ => by simpa using hL₂ τ hτ)
    (fun w hw => by simpa using hM₀ w hw) (fun w hw => by simpa using hM₁ w hw) hz hzK t ht
  exact h.trans (le_of_eq (mul_comm _ _))

/-! ### The oscillator -/

/-- The potential `k x²/2` of the oscillator, with the stiffness `k` as the
parameter. -/
def oscillatorPotential (r : ℝ × ℝ) : ℝ := r.1 / 2 * r.2 ^ 2

theorem contDiff_oscillatorPotential : ContDiff ℝ ∞ oscillatorPotential :=
  (contDiff_fst.div_const 2).mul (contDiff_snd.pow 2)

/-- The oscillators of all positive stiffnesses, at all positive energies, form
a family of wells. -/
theorem isWellFamily_oscillator :
    IsWellFamily oscillatorPotential {s : ℝ × ℝ | 0 < s.1 ∧ 0 < s.2}
      (fun s => -√(2 * s.1 / s.2)) (fun s => √(2 * s.1 / s.2)) := by
  have hsqrt : ContDiffOn ℝ ∞ (fun s : ℝ × ℝ => √(2 * s.1 / s.2))
      {s : ℝ × ℝ | 0 < s.1 ∧ 0 < s.2} :=
    ((contDiffOn_const.mul contDiffOn_fst).div contDiffOn_snd fun s hs => hs.2.ne').sqrt
      fun s hs => (div_pos (mul_pos two_pos hs.1) hs.2).ne'
  exact ⟨(isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_const continuous_snd), hsqrt.neg, hsqrt,
    fun s hs => isWell_oscillator hs.2 hs.1⟩

/-- The action variable of the oscillator is `E √(m/k)`, the energy over the
frequency. -/
theorem invariant_oscillator (hm : 0 < m) {w : (ℝ × ℝ) × ℝ} (hk : 0 < w.2)
    (hE : 0 < energyAt m oscillatorPotential w) :
    invariant m oscillatorPotential (fun s => -√(2 * s.1 / s.2)) (fun s => √(2 * s.1 / s.2)) w =
      energyAt m oscillatorPotential w * √(m / w.2) :=
  orbitAction_oscillator hk hm hE

end ProjectAinos.Mechanics.OneDim.Adiabatic
