/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialRelativity.FreeMotion
public import ProjectAinos.SpecialRelativity.ObserverEnergy
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The momentum and the angular momentum of a system of particles

A particle at the event `x` with the momentum vector `p` has the orbital moment `x ∧ p`
(Landau–Lifshitz, *The Classical Theory of Fields*, §14). It is written here as a function of
two covectors, `orbitalMoment x p α β = α(x) β(p) − α(p) β(x)`; its components are the values
on the co-ordinate covectors, `x^μ p^ν − x^ν p^μ` (`orbitalMoment_proj`).

**One particle.** The moment is unchanged along the line of the particle
(`orbitalMoment_add_smul`), and it is a tensor: under a Lorentz transformation the covectors
are pulled back (`orbitalMoment_lorentz`). A shift of the origin by `c` adds `c ∧ p`
(`orbitalMoment_add_left`).

**Noether's charges.** For two covectors, `lorentzGenerator σ α β` is the infinitesimal Lorentz
transformation `x ↦ α(x) β♯ − β(x) α♯`. The momentum covector applied to this field is the
orbital moment (`flat_lorentzGenerator`), so the moment is the charge that Noether's theorem
assigns to the Lorentz transformations. In three space dimensions it is constant along a
stationary curve of the free action (`orbitalMoment_eq_of_stationary`).

**A system.** For finitely many particles, `totalMomentum p` and `totalMoment x p` are the sums.
They do not change when each particle moves freely (`totalMoment_freeMotion`), and at a
collision in one event the moment is conserved if the momentum is
(`sum_orbitalMoment_same_event`). The total moment is a tensor, and a shift of the origin by
`c` adds `c ∧ P` (`totalMoment_add_const`).

**The centre of energy.** For an observer `u` and events that are simultaneous for `u`,
`centreOfEnergy u x p = Σ Eₐ xₐ / Σ Eₐ`. If the total moment is the same at two times, the
centre has moved by `(t′ − t) P / E`: it moves uniformly with the velocity `P/E`
(`centreOfEnergy_sub`, `centreOfEnergy_freeMotion`).
-/

@[expose] public section

noncomputable section

open Set

namespace ProjectAinos.SpecialRelativity

open SmoothGeometry SmoothGeometry.Minkowski Mechanics

variable {d : ℕ}

/-! ### One particle -/

/-- The orbital moment `x ∧ p`, as a function of two covectors. -/
def orbitalMoment (x p : MinkowskiModel d) (α β : MinkowskiModel d →L[ℝ] ℝ) : ℝ :=
  α x * β p - α p * β x

/-- The components `x^μ p^ν − x^ν p^μ`. -/
theorem orbitalMoment_proj (x p : MinkowskiModel d) (μ ν : Fin (d + 1)) :
    orbitalMoment x p (ContinuousLinearMap.proj μ) (ContinuousLinearMap.proj ν) =
      x μ * p ν - p μ * x ν := rfl

theorem orbitalMoment_antisymm (x p : MinkowskiModel d) (α β : MinkowskiModel d →L[ℝ] ℝ) :
    orbitalMoment x p α β = -orbitalMoment x p β α := by
  unfold orbitalMoment
  ring

theorem orbitalMoment_self (p : MinkowskiModel d) (α β : MinkowskiModel d →L[ℝ] ℝ) :
    orbitalMoment p p α β = 0 := by
  unfold orbitalMoment
  ring

/-- A shift of the origin by `c` adds `c ∧ p`. -/
theorem orbitalMoment_add_left (x c p : MinkowskiModel d) (α β : MinkowskiModel d →L[ℝ] ℝ) :
    orbitalMoment (x + c) p α β = orbitalMoment x p α β + orbitalMoment c p α β := by
  simp only [orbitalMoment, map_add]
  ring

theorem orbitalMoment_add_right (x p q : MinkowskiModel d) (α β : MinkowskiModel d →L[ℝ] ℝ) :
    orbitalMoment x (p + q) α β = orbitalMoment x p α β + orbitalMoment x q α β := by
  simp only [orbitalMoment, map_add]
  ring

theorem orbitalMoment_smul_left (s : ℝ) (x p : MinkowskiModel d)
    (α β : MinkowskiModel d →L[ℝ] ℝ) :
    orbitalMoment (s • x) p α β = s * orbitalMoment x p α β := by
  simp only [orbitalMoment, map_smul, smul_eq_mul]
  ring

/-- The moment is unchanged along the line of the particle. -/
theorem orbitalMoment_add_smul (x p : MinkowskiModel d) (s : ℝ)
    (α β : MinkowskiModel d →L[ℝ] ℝ) :
    orbitalMoment (x + s • p) p α β = orbitalMoment x p α β := by
  rw [orbitalMoment_add_left, orbitalMoment_smul_left, orbitalMoment_self, mul_zero, add_zero]

/-- The moment is a tensor: a Lorentz transformation of the event and the momentum is the
pullback of the covectors. -/
theorem orbitalMoment_lorentz (L : LorentzGroup d) (x p : MinkowskiModel d)
    (α β : MinkowskiModel d →L[ℝ] ℝ) :
    orbitalMoment (L.val x) (L.val p) α β =
      orbitalMoment x p (α.comp (LorentzGroup.toContinuousLinearEquiv L).toContinuousLinearMap)
        (β.comp (LorentzGroup.toContinuousLinearEquiv L).toContinuousLinearMap) := rfl

/-! ### Noether's charges -/

/-- The infinitesimal Lorentz transformation `x ↦ α(x) β♯ − β(x) α♯` of two covectors. -/
def lorentzGenerator (σ : LorentzConvention) (α β : MinkowskiModel d →L[ℝ] ℝ) :
    MinkowskiModel d →L[ℝ] MinkowskiModel d :=
  α.smulRight (sharp σ β) - β.smulRight (sharp σ α)

theorem minkowskiForm_sharp (σ : LorentzConvention) (β : MinkowskiModel d →L[ℝ] ℝ)
    (w : MinkowskiModel d) : minkowskiForm σ d (sharp σ β) w = β w := by
  rw [← flat_apply]
  exact congrArg (fun γ : MinkowskiModel d →L[ℝ] ℝ => γ w) ((flat σ).apply_symm_apply β)

/-- The generator is antisymmetric for the metric: it is an infinitesimal isometry. -/
theorem minkowskiForm_lorentzGenerator (σ : LorentzConvention)
    (α β : MinkowskiModel d →L[ℝ] ℝ) (v w : MinkowskiModel d) :
    minkowskiForm σ d (lorentzGenerator σ α β v) w +
      minkowskiForm σ d v (lorentzGenerator σ α β w) = 0 := by
  have h1 := minkowskiForm_sharp σ α
  have h2 := minkowskiForm_sharp σ β
  have hsymm (a b : MinkowskiModel d) : minkowskiForm σ d a b = minkowskiForm σ d b a :=
    minkowskiForm_symmetric σ a b
  simp only [lorentzGenerator, sub_apply, ContinuousLinearMap.smulRight_apply, map_sub, map_smul,
    smul_apply, smul_eq_mul, h1, h2, hsymm v (sharp σ β), hsymm v (sharp σ α)]
  ring

/-- The momentum covector applied to the generator is the orbital moment: the moment is the
charge of the Lorentz transformations. -/
theorem flat_lorentzGenerator (σ : LorentzConvention) (α β : MinkowskiModel d →L[ℝ] ℝ)
    (x p : MinkowskiModel d) :
    flat σ p (lorentzGenerator σ α β x) = orbitalMoment x p α β := by
  have hsymm (a b : MinkowskiModel d) : minkowskiForm σ d a b = minkowskiForm σ d b a :=
    minkowskiForm_symmetric σ a b
  simp only [flat_apply, lorentzGenerator, sub_apply, ContinuousLinearMap.smulRight_apply,
    map_sub, map_smul, smul_eq_mul, hsymm p (sharp σ β), hsymm p (sharp σ α),
    minkowskiForm_sharp, orbitalMoment]
  ring

/-- The momentum covector of the free action applied to the generator is the orbital moment
of the momentum vector `m U`. -/
theorem kineticMomentum_lorentzGenerator (m : ℝ) (v x : Spacetime)
    (α β : Spacetime →L[ℝ] ℝ) :
    kineticMomentum m v (lorentzGenerator .timeNegative α β x) =
      orbitalMoment x (m • fourVelocity v) α β := by
  rw [← flat_lorentzGenerator .timeNegative α β x (m • fourVelocity v), map_smul]
  rfl

/-- Along a stationary curve of the free action with a nonzero mass the orbital moment is
constant. -/
theorem orbitalMoment_eq_of_stationary {m : ℝ} (hm : m ≠ 0) {γ : ℝ → Spacetime} {a b : ℝ}
    (hab : a < b) (hγ : ContDiff ℝ 2 γ) (hv : ∀ t ∈ Icc a b, Timelike (deriv γ t))
    (h : Stationary a b (freeLagrangian m) γ) {t : ℝ} (ht : t ∈ Icc a b)
    (α β : Spacetime →L[ℝ] ℝ) :
    orbitalMoment (γ t) (m • fourVelocity (deriv γ t)) α β =
      orbitalMoment (γ a) (m • fourVelocity (deriv γ a)) α β := by
  have hU := (free_stationary_iff_fourVelocity_const hm hab hγ hv).mp h t ht
  have hline := (free_stationary_iff_inertial hm hab hγ hv).mp h t ht
  have hsmul : properTime γ a t • fourVelocity (deriv γ a) =
      (properTime γ a t * m⁻¹) • (m • fourVelocity (deriv γ a)) := by
    rw [smul_smul, mul_assoc, inv_mul_cancel₀ hm, mul_one]
  rw [hU, hline, hsmul, orbitalMoment_add_smul]

/-! ### A system of particles -/

variable {ι : Type*} [Fintype ι]

/-- The total momentum of a system. -/
def totalMomentum (p : ι → MinkowskiModel d) : MinkowskiModel d := ∑ a, p a

/-- The total orbital moment of a system. -/
def totalMoment (x p : ι → MinkowskiModel d) (α β : MinkowskiModel d →L[ℝ] ℝ) : ℝ :=
  ∑ a, orbitalMoment (x a) (p a) α β

/-- The total momentum is a vector. -/
theorem totalMomentum_lorentz (L : LorentzGroup d) (p : ι → MinkowskiModel d) :
    totalMomentum (fun a => L.val (p a)) = L.val (totalMomentum p) :=
  (map_sum L.val p Finset.univ).symm

/-- The total moment is a tensor. -/
theorem totalMoment_lorentz (L : LorentzGroup d) (x p : ι → MinkowskiModel d)
    (α β : MinkowskiModel d →L[ℝ] ℝ) :
    totalMoment (fun a => L.val (x a)) (fun a => L.val (p a)) α β =
      totalMoment x p (α.comp (LorentzGroup.toContinuousLinearEquiv L).toContinuousLinearMap)
        (β.comp (LorentzGroup.toContinuousLinearEquiv L).toContinuousLinearMap) := rfl

/-- The total moment does not change when each particle moves along its line. -/
theorem totalMoment_freeMotion (x p : ι → MinkowskiModel d) (s : ι → ℝ)
    (α β : MinkowskiModel d →L[ℝ] ℝ) :
    totalMoment (fun a => x a + s a • p a) p α β = totalMoment x p α β :=
  Finset.sum_congr rfl fun a _ => orbitalMoment_add_smul (x a) (p a) (s a) α β

/-- A shift of the origin by `c` adds `c ∧ P`. -/
theorem totalMoment_add_const (x p : ι → MinkowskiModel d) (c : MinkowskiModel d)
    (α β : MinkowskiModel d →L[ℝ] ℝ) :
    totalMoment (fun a => x a + c) p α β =
      totalMoment x p α β + orbitalMoment c (totalMomentum p) α β := by
  have hsum : orbitalMoment c (totalMomentum p) α β = ∑ a, orbitalMoment c (p a) α β := by
    simp only [orbitalMoment, totalMomentum, map_sum, Finset.mul_sum, Finset.sum_mul,
      Finset.sum_sub_distrib]
  rw [totalMoment, totalMoment, hsum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => orbitalMoment_add_left (x a) c (p a) α β

/-- The moment of particles that are at one event is the moment of their total momentum. At a
collision in one event the moment is therefore conserved if the momentum is. -/
theorem sum_orbitalMoment_same_event (y : MinkowskiModel d) (p : ι → MinkowskiModel d)
    (α β : MinkowskiModel d →L[ℝ] ℝ) :
    ∑ a, orbitalMoment y (p a) α β = orbitalMoment y (totalMomentum p) α β := by
  simp only [orbitalMoment, totalMomentum, map_sum, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_sub_distrib]

/-! ### The centre of energy -/

/-- The centre of energy `Σ Eₐ xₐ / Σ Eₐ` of a system for the observer `u`. -/
def centreOfEnergy (u : Observer d) (x p : ι → MinkowskiModel d) : MinkowskiModel d :=
  (∑ a, observerEnergy u (p a))⁻¹ • ∑ a, observerEnergy u (p a) • x a

/-- For events that are simultaneous for `u` at the time `t`, the mixed part of the moment is
`t P − Σ Eₐ xₐ`. -/
theorem totalMoment_clock (u : Observer d) (x p : ι → MinkowskiModel d) {t : ℝ}
    (hsim : ∀ a, u.clock (x a) = t) (β : MinkowskiModel d →L[ℝ] ℝ) :
    totalMoment x p u.clock β =
      t * β (totalMomentum p) - β (∑ a, observerEnergy u (p a) • x a) := by
  simp only [totalMoment, orbitalMoment, totalMomentum, map_sum, map_smul, smul_eq_mul, hsim,
    Finset.mul_sum, Finset.sum_sub_distrib]
  rfl

/-- If the total moment is the same for two simultaneous configurations at the times `t` and
`t′`, the centre of energy has moved by `(t′ − t) P / E`. -/
theorem centreOfEnergy_sub (u : Observer d) (x x' p : ι → MinkowskiModel d) {t t' : ℝ}
    (hsim : ∀ a, u.clock (x a) = t) (hsim' : ∀ a, u.clock (x' a) = t')
    (hJ : ∀ β : MinkowskiModel d →L[ℝ] ℝ,
      totalMoment x' p u.clock β = totalMoment x p u.clock β) :
    centreOfEnergy u x' p - centreOfEnergy u x p =
      ((t' - t) / ∑ a, observerEnergy u (p a)) • totalMomentum p := by
  have hvec : ∑ a, observerEnergy u (p a) • x' a - ∑ a, observerEnergy u (p a) • x a =
      (t' - t) • totalMomentum p := by
    funext μ
    have h := hJ (ContinuousLinearMap.proj μ)
    rw [totalMoment_clock u x' p hsim', totalMoment_clock u x p hsim] at h
    simp only [ContinuousLinearMap.proj_apply] at h
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  rw [centreOfEnergy, centreOfEnergy, ← smul_sub, hvec, smul_smul, div_eq_inv_mul]

/-- The centre of energy of freely moving particles moves uniformly with the velocity
`P / E`: after the time `s` of the observer it has moved by `s P / E`. -/
theorem centreOfEnergy_freeMotion (u : Observer d) (x p : ι → MinkowskiModel d) {t : ℝ} (s : ℝ)
    (hsim : ∀ a, u.clock (x a) = t) (hEa : ∀ a, observerEnergy u (p a) ≠ 0) :
    centreOfEnergy u (fun a => x a + (s / observerEnergy u (p a)) • p a) p -
        centreOfEnergy u x p =
      (s / ∑ a, observerEnergy u (p a)) • totalMomentum p := by
  have hsim' : ∀ a, u.clock (x a + (s / observerEnergy u (p a)) • p a) = t + s := by
    intro a
    rw [map_add, map_smul, hsim a, smul_eq_mul]
    change t + s / observerEnergy u (p a) * observerEnergy u (p a) = t + s
    rw [div_mul_cancel₀ _ (hEa a)]
  have h := centreOfEnergy_sub u x (fun a => x a + (s / observerEnergy u (p a)) • p a) p hsim
    hsim' (fun β => totalMoment_freeMotion x p _ u.clock β)
  rwa [add_sub_cancel_left] at h

end ProjectAinos.SpecialRelativity
