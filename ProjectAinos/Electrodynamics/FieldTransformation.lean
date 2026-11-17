/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Covariance
public import ProjectAinos.SpecialRelativity.Factorization
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The transformation of the electric and the magnetic field

In the frame of the co-ordinates a field `F` has the electric components `Eᵢ = F(eᵢ, e₀)` and
the magnetic components `B₁ = F₂₃`, `B₂ = F₃₁`, `B₃ = F₁₂` (Landau–Lifshitz, *The Classical
Theory of Fields*, §§23–25).

* `twoForm_apply_vectors`: `F(v, w)` in terms of `E` and `B`.
* `electric_restObserver_apply`, `magnetic_restObserver_apply`: `E` and `B` are the components
  of the electric and the magnetic covector of the observer at rest.
* `scalarInvariant_vectors`, `pseudoscalarInvariant_vectors`: the invariants are
  `Σ Bᵢ² − Σ Eᵢ²` and `Σ Eᵢ Bᵢ`.
* `boost_axisVelocity_apply`: the boost with the velocity `V` along the first axis is
  `t ↦ γ (t − V x)`, `x ↦ γ (x − V t)`.
* `electricVector_boost`, `magneticVector_boost`: the components of the pullback of `F` by
  this boost are `E₁`, `γ (E₂ + V B₃)`, `γ (E₃ − V B₂)` and `B₁`, `γ (B₂ − V E₃)`,
  `γ (B₃ + V E₂)`.
* `electricVector_moving`, `magneticVector_moving`: the pullback by the inverse boost has the
  components that the observer with the velocity `V` measures
  (`electric_observer_apply`, `magnetic_observer_apply`): `E₁`, `γ (E₂ − V B₃)`,
  `γ (E₃ + V B₂)` and `B₁`, `γ (B₂ + V E₃)`, `γ (B₃ − V E₂)`.

The boost `boost β` maps the four-velocity of the observer with the velocity `β` to the axis
of the time, so the components of a tensor for this observer are those of its pullback by the
inverse of the boost.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

/-! ### The components -/

/-- The electric components `Eᵢ = F(eᵢ, e₀)` in the frame of the co-ordinates. -/
def electricVector (F : TwoForm) : Fin 3 → ℝ :=
  ![component F 1 0, component F 2 0, component F 3 0]

/-- The magnetic components `B₁ = F₂₃`, `B₂ = F₃₁`, `B₃ = F₁₂` in the frame of the
co-ordinates. -/
def magneticVector (F : TwoForm) : Fin 3 → ℝ :=
  ![component F 2 3, component F 3 1, component F 1 2]

theorem component_swap (F : TwoForm) (μ ν : Fin 4) : component F μ ν = -component F ν μ :=
  twoForm_swap F _ _

/-- A two-form on two vectors, in its six components. -/
theorem twoForm_apply (F : TwoForm) (v w : Spacetime) :
    F ![v, w] = component F 0 1 * (v 0 * w 1 - v 1 * w 0) +
      component F 0 2 * (v 0 * w 2 - v 2 * w 0) + component F 0 3 * (v 0 * w 3 - v 3 * w 0) +
      component F 1 2 * (v 1 * w 2 - v 2 * w 1) + component F 1 3 * (v 1 * w 3 - v 3 * w 1) +
      component F 2 3 * (v 2 * w 3 - v 3 * w 2) := by
  conv_lhs => rw [twoForm_expansion F]
  simp [twoFormExpansion, coordinateForm_apply, Matrix.det_fin_two]

/-- A two-form on two vectors, in terms of the electric and the magnetic components. -/
theorem twoForm_apply_vectors (F : TwoForm) (v w : Spacetime) :
    F ![v, w] = electricVector F 0 * (v 1 * w 0 - v 0 * w 1) +
      electricVector F 1 * (v 2 * w 0 - v 0 * w 2) +
      electricVector F 2 * (v 3 * w 0 - v 0 * w 3) +
      magneticVector F 0 * (v 2 * w 3 - v 3 * w 2) +
      magneticVector F 1 * (v 3 * w 1 - v 1 * w 3) +
      magneticVector F 2 * (v 1 * w 2 - v 2 * w 1) := by
  have h1 := component_swap F 1 0
  have h2 := component_swap F 2 0
  have h3 := component_swap F 3 0
  have h4 := component_swap F 3 1
  rw [twoForm_apply F v w]
  simp only [electricVector, magneticVector, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [h1, h2, h3, h4]
  ring

/-- The pullback by a Lorentz transformation on two vectors. -/
theorem lorentzPullback_apply (L : LorentzGroup 3) (F : TwoForm) (v w : Spacetime) :
    lorentzPullback L F ![v, w] = F ![L.val v, L.val w] := by
  rw [lorentzPullback, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem component_lorentzPullback (L : LorentzGroup 3) (F : TwoForm) (μ ν : Fin 4) :
    component (lorentzPullback L F) μ ν = F ![L.val (Pi.single μ 1), L.val (Pi.single ν 1)] :=
  lorentzPullback_apply L F _ _

/-! ### The boost along the first axis -/

/-- The velocity `V` along the first axis of space. -/
def axisVelocity (V : ℝ) (hV : |V| < 1) : Velocity 3 :=
  ⟨EuclideanSpace.single 0 V, by simpa [PiLp.norm_single] using hV⟩

theorem axisVelocity_gamma_identity (V : ℝ) (hV : |V| < 1) :
    (axisVelocity V hV).gamma ^ 2 * (1 - V ^ 2) = 1 := by
  have h := (axisVelocity V hV).gamma_identity
  simpa [axisVelocity, PiLp.norm_single] using h

/-- The boost with the velocity `V` along the first axis, in co-ordinates. -/
theorem boost_axisVelocity_apply (V : ℝ) (hV : |V| < 1) (v : Spacetime) :
    (boost (axisVelocity V hV)).val v =
      ![(axisVelocity V hV).gamma * (v 0 - V * v 1),
        (axisVelocity V hV).gamma * (v 1 - V * v 0), v 2, v 3] := by
  have hg := axisVelocity_gamma_identity V hV
  have hgp := (axisVelocity V hV).gamma_pos
  have hin : inner ℝ (axisVelocity V hV).val (space v) = V * v 1 := by
    simp [axisVelocity, EuclideanSpace.inner_single_left]
  have ht := boost_time (axisVelocity V hV) v
  have hs := boost_space (axisVelocity V hV) v
  rw [hin] at ht hs
  have hcomp (k : Fin 3) : (boost (axisVelocity V hV)).val v k.succ = v k.succ +
      ((axisVelocity V hV).gamma ^ 2 / (1 + (axisVelocity V hV).gamma) * (V * v 1) -
        (axisVelocity V hV).gamma * v 0) * (axisVelocity V hV).val k := by
    have h1 := congrArg (fun x : Space 3 => x k) hs
    simp only [space_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h1
    exact h1
  have hβ0 : (axisVelocity V hV).val 0 = V := by simp [axisVelocity]
  have hβ1 : (axisVelocity V hV).val 1 = 0 := by simp [axisVelocity]
  have hβ2 : (axisVelocity V hV).val 2 = 0 := by simp [axisVelocity]
  ext μ
  fin_cases μ
  · exact ht
  · have h1 := hcomp 0
    rw [hβ0] at h1
    refine h1.trans ?_
    change v 1 + ((axisVelocity V hV).gamma ^ 2 / (1 + (axisVelocity V hV).gamma) * (V * v 1) -
      (axisVelocity V hV).gamma * v 0) * V = (axisVelocity V hV).gamma * (v 1 - V * v 0)
    have hne : 1 + (axisVelocity V hV).gamma ≠ 0 := by positivity
    field_simp
    linear_combination (-(v 1)) * hg
  · have h1 := hcomp 1
    rw [hβ1, mul_zero, add_zero] at h1
    exact h1
  · have h1 := hcomp 2
    rw [hβ2, mul_zero, add_zero] at h1
    exact h1

/-! ### The transformation of the components -/

section Boost

variable (V : ℝ) (hV : |V| < 1)

theorem boost_axisVelocity_single_zero :
    (boost (axisVelocity V hV)).val (Pi.single 0 1) =
      ![(axisVelocity V hV).gamma, -((axisVelocity V hV).gamma * V), 0, 0] := by
  rw [boost_axisVelocity_apply]
  simp

theorem boost_axisVelocity_single_one :
    (boost (axisVelocity V hV)).val (Pi.single 1 1) =
      ![-((axisVelocity V hV).gamma * V), (axisVelocity V hV).gamma, 0, 0] := by
  rw [boost_axisVelocity_apply]
  simp

theorem boost_axisVelocity_single_two :
    (boost (axisVelocity V hV)).val (Pi.single 2 1) = ![0, 0, 1, 0] := by
  rw [boost_axisVelocity_apply]
  simp

theorem boost_axisVelocity_single_three :
    (boost (axisVelocity V hV)).val (Pi.single 3 1) = ![0, 0, 0, 1] := by
  rw [boost_axisVelocity_apply]
  simp

/-- The electric components of the pullback of a field by the boost with the velocity `V`
along the first axis. -/
theorem electricVector_boost (F : TwoForm) :
    electricVector (lorentzPullback (boost (axisVelocity V hV)) F) =
      ![electricVector F 0,
        (axisVelocity V hV).gamma * (electricVector F 1 + V * magneticVector F 2),
        (axisVelocity V hV).gamma * (electricVector F 2 - V * magneticVector F 1)] := by
  have hg := axisVelocity_gamma_identity V hV
  funext i
  fin_cases i
  · change component (lorentzPullback (boost (axisVelocity V hV)) F) 1 0 = electricVector F 0
    rw [component_lorentzPullback, boost_axisVelocity_single_one, boost_axisVelocity_single_zero,
      twoForm_apply_vectors F]
    simp only [Matrix.cons_val]
    linear_combination electricVector F 0 * hg
  · change component (lorentzPullback (boost (axisVelocity V hV)) F) 2 0 =
      (axisVelocity V hV).gamma * (electricVector F 1 + V * magneticVector F 2)
    rw [component_lorentzPullback, boost_axisVelocity_single_two, boost_axisVelocity_single_zero,
      twoForm_apply_vectors F]
    simp only [Matrix.cons_val]
    ring
  · change component (lorentzPullback (boost (axisVelocity V hV)) F) 3 0 =
      (axisVelocity V hV).gamma * (electricVector F 2 - V * magneticVector F 1)
    rw [component_lorentzPullback, boost_axisVelocity_single_three,
      boost_axisVelocity_single_zero, twoForm_apply_vectors F]
    simp only [Matrix.cons_val]
    ring

/-- The magnetic components of the pullback of a field by the boost with the velocity `V`
along the first axis. -/
theorem magneticVector_boost (F : TwoForm) :
    magneticVector (lorentzPullback (boost (axisVelocity V hV)) F) =
      ![magneticVector F 0,
        (axisVelocity V hV).gamma * (magneticVector F 1 - V * electricVector F 2),
        (axisVelocity V hV).gamma * (magneticVector F 2 + V * electricVector F 1)] := by
  funext i
  fin_cases i
  · change component (lorentzPullback (boost (axisVelocity V hV)) F) 2 3 = magneticVector F 0
    rw [component_lorentzPullback, boost_axisVelocity_single_two,
      boost_axisVelocity_single_three, twoForm_apply_vectors F]
    simp only [Matrix.cons_val]
    ring
  · change component (lorentzPullback (boost (axisVelocity V hV)) F) 3 1 =
      (axisVelocity V hV).gamma * (magneticVector F 1 - V * electricVector F 2)
    rw [component_lorentzPullback, boost_axisVelocity_single_three,
      boost_axisVelocity_single_one, twoForm_apply_vectors F]
    simp only [Matrix.cons_val]
    ring
  · change component (lorentzPullback (boost (axisVelocity V hV)) F) 1 2 =
      (axisVelocity V hV).gamma * (magneticVector F 2 + V * electricVector F 1)
    rw [component_lorentzPullback, boost_axisVelocity_single_one, boost_axisVelocity_single_two,
      twoForm_apply_vectors F]
    simp only [Matrix.cons_val]
    ring

end Boost

/-! ### The observer at rest and the invariants -/

theorem timeAxis_eq_single : timeAxis 3 = Pi.single 0 1 := by
  ext i
  fin_cases i <;> rfl

theorem electricVector_apply (F : TwoForm) (i : Fin 3) :
    electricVector F i = component F i.succ 0 := by
  fin_cases i <;> rfl

/-- The components of the Hodge dual. -/
theorem component_star (F : TwoForm) (μ ν : Fin 4) :
    component (star F) μ ν =
      -component F 0 1 * ((Pi.single μ 1 : Spacetime) 2 * (Pi.single ν 1 : Spacetime) 3 -
          (Pi.single μ 1 : Spacetime) 3 * (Pi.single ν 1 : Spacetime) 2) +
        component F 0 2 * ((Pi.single μ 1 : Spacetime) 1 * (Pi.single ν 1 : Spacetime) 3 -
          (Pi.single μ 1 : Spacetime) 3 * (Pi.single ν 1 : Spacetime) 1) -
        component F 0 3 * ((Pi.single μ 1 : Spacetime) 1 * (Pi.single ν 1 : Spacetime) 2 -
          (Pi.single μ 1 : Spacetime) 2 * (Pi.single ν 1 : Spacetime) 1) +
        component F 1 2 * ((Pi.single μ 1 : Spacetime) 0 * (Pi.single ν 1 : Spacetime) 3 -
          (Pi.single μ 1 : Spacetime) 3 * (Pi.single ν 1 : Spacetime) 0) -
        component F 1 3 * ((Pi.single μ 1 : Spacetime) 0 * (Pi.single ν 1 : Spacetime) 2 -
          (Pi.single μ 1 : Spacetime) 2 * (Pi.single ν 1 : Spacetime) 0) +
        component F 2 3 * ((Pi.single μ 1 : Spacetime) 0 * (Pi.single ν 1 : Spacetime) 1 -
          (Pi.single μ 1 : Spacetime) 1 * (Pi.single ν 1 : Spacetime) 0) :=
  hodgeTwo_apply .timeNegative F _ _

/-- The magnetic components are the components `(⋆F)(e₀, eᵢ)` of the Hodge dual. -/
theorem component_star_zero_succ (F : TwoForm) (i : Fin 3) :
    component (star F) 0 i.succ = magneticVector F i := by
  have h := component_swap F 3 1
  rw [component_star]
  fin_cases i <;> simp [magneticVector]
  linarith

/-- The electric components are the components of the electric covector of the observer at
rest. -/
theorem electric_restObserver_single (F : TwoForm) (i : Fin 3) :
    oneCovector (electric (restObserver 3) F) (Pi.single i.succ 1) = electricVector F i := by
  rw [electric_apply, electricVector_apply]
  change -F ![timeAxis 3, Pi.single i.succ 1] = component F i.succ 0
  rw [timeAxis_eq_single]
  exact (component_swap F i.succ 0).symm

/-- The magnetic components are the components of the magnetic covector of the observer at
rest. -/
theorem magnetic_restObserver_single (F : TwoForm) (i : Fin 3) :
    oneCovector (magnetic (restObserver 3) F) (Pi.single i.succ 1) = magneticVector F i := by
  rw [magnetic_apply, ← component_star_zero_succ]
  change star F ![timeAxis 3, Pi.single i.succ 1] = component (star F) 0 i.succ
  rw [timeAxis_eq_single]
  rfl

/-- The scalar invariant is `Σ Bᵢ² − Σ Eᵢ²`. -/
theorem scalarInvariant_vectors (F : TwoForm) :
    scalarInvariant F = ∑ i, magneticVector F i ^ 2 - ∑ i, electricVector F i ^ 2 := by
  have h1 := component_swap F 1 0
  have h2 := component_swap F 2 0
  have h3 := component_swap F 3 0
  have h4 := component_swap F 3 1
  rw [scalarInvariant, tensorContraction_coordinates]
  simp only [electricVector, magneticVector, Fin.sum_univ_three, Matrix.cons_val]
  rw [h1, h2, h3, h4]
  ring

/-- The pseudoscalar invariant is `Σ Eᵢ Bᵢ`. -/
theorem pseudoscalarInvariant_vectors (F : TwoForm) :
    pseudoscalarInvariant F = ∑ i, electricVector F i * magneticVector F i := by
  have h1 := component_swap F 1 0
  have h2 := component_swap F 2 0
  have h3 := component_swap F 3 0
  have h4 := component_swap F 3 1
  rw [pseudoscalarInvariant, tensorContraction_coordinates]
  simp only [component_star]
  simp only [electricVector, magneticVector, Fin.sum_univ_three, Matrix.cons_val]
  rw [h1, h2, h3, h4]
  simp
  ring

/-! ### A moving observer -/

/-- The boost with the opposite velocity maps the axis of the time to the four-velocity of the
observer. -/
theorem boost_neg_single_zero (β : Velocity 3) :
    (boost β.neg).val (Pi.single 0 1) = β.observer.velocity := by
  have h : ((boost β)⁻¹ * boost β).val β.observer.velocity = β.observer.velocity := by
    rw [inv_mul_cancel]
    rfl
  rw [boost_neg_inverse, ← timeAxis_eq_single, ← boost_observer β]
  exact h

/-- The electric covector of the observer with the velocity `β`, on the axes of this observer,
has the components of the pullback of the field by the boost with the opposite velocity. -/
theorem electric_observer_apply (β : Velocity 3) (F : TwoForm) (i : Fin 3) :
    oneCovector (electric β.observer F) ((boost β.neg).val (Pi.single i.succ 1)) =
      electricVector (lorentzPullback (boost β.neg) F) i := by
  rw [electric_apply, electricVector_apply, component_lorentzPullback, boost_neg_single_zero]
  exact (twoForm_swap F _ _).symm

/-- The magnetic covector of the observer with the velocity `β`, on the axes of this observer,
has the components of the pullback of the field by the boost with the opposite velocity. -/
theorem magnetic_observer_apply (β : Velocity 3) (F : TwoForm) (i : Fin 3) :
    oneCovector (magnetic β.observer F) ((boost β.neg).val (Pi.single i.succ 1)) =
      magneticVector (lorentzPullback (boost β.neg) F) i := by
  have hstar := star_properLorentz
    ⟨boost β.neg, (boostProperOrthochronous β.neg).property.1⟩ F
  rw [magnetic_apply, ← component_star_zero_succ]
  change star F ![β.observer.velocity, (boost β.neg).val (Pi.single i.succ 1)] =
    component (star (lorentzPullback (boost β.neg) F)) 0 i.succ
  rw [hstar, component_lorentzPullback, boost_neg_single_zero]

section Moving

variable (V : ℝ) (hV : |V| < 1)

theorem axisVelocity_neg :
    (axisVelocity V hV).neg = axisVelocity (-V) (by rwa [abs_neg]) := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [axisVelocity]

theorem gamma_axisVelocity_neg :
    (axisVelocity (-V) (by rwa [abs_neg])).gamma = (axisVelocity V hV).gamma := by
  simp [Velocity.gamma, axisVelocity]

/-- The electric components that the observer with the velocity `V` along the first axis
measures: `E₁`, `γ (E₂ − V B₃)`, `γ (E₃ + V B₂)`. -/
theorem electricVector_moving (F : TwoForm) :
    electricVector (lorentzPullback (boost (axisVelocity V hV).neg) F) =
      ![electricVector F 0,
        (axisVelocity V hV).gamma * (electricVector F 1 - V * magneticVector F 2),
        (axisVelocity V hV).gamma * (electricVector F 2 + V * magneticVector F 1)] := by
  rw [axisVelocity_neg, electricVector_boost, gamma_axisVelocity_neg V hV]
  simp only [neg_mul, sub_neg_eq_add, ← sub_eq_add_neg]

/-- The magnetic components that the observer with the velocity `V` along the first axis
measures: `B₁`, `γ (B₂ + V E₃)`, `γ (B₃ − V E₂)`. -/
theorem magneticVector_moving (F : TwoForm) :
    magneticVector (lorentzPullback (boost (axisVelocity V hV).neg) F) =
      ![magneticVector F 0,
        (axisVelocity V hV).gamma * (magneticVector F 1 + V * electricVector F 2),
        (axisVelocity V hV).gamma * (magneticVector F 2 - V * electricVector F 1)] := by
  rw [axisVelocity_neg, magneticVector_boost, gamma_axisVelocity_neg V hV]
  simp only [neg_mul, sub_neg_eq_add, ← sub_eq_add_neg]

end Moving

end ProjectAinos.Electrodynamics
