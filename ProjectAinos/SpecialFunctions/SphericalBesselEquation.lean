/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.SphericalBesselRecurrence
import Mathlib.Tactic

/-! # Regular and singular spherical Bessel solutions

The order recurrence preserves both derivative ladders and the Wronskian. Starting with
the cardinal sine and negative cardinal cosine gives independent solutions with Wronskian
`1/z²`. Their complex linear combinations are the outgoing and incoming spherical waves.
-/

@[expose] public section
noncomputable section

open Complex
namespace ProjectAinos.SpecialFunctions.Bessel

/-- Spherical Bessel function of the second kind, with `y₀(z) = −cos(z)/z`. -/
def sphericalY : ℕ → ℂ → ℂ
  | 0, z => -cos z / z
  | 1, z => -cos z / z ^ 2 - sin z / z
  | n + 2, z => (2 * (n : ℂ) + 3) / z * sphericalY (n + 1) z - sphericalY n z

/-- Spherical Hankel function of the first kind (outgoing). -/
def sphericalHankel₁ (n : ℕ) (z : ℂ) : ℂ := sphericalJ n z + I * sphericalY n z

/-- Spherical Hankel function of the second kind (incoming). -/
def sphericalHankel₂ (n : ℕ) (z : ℂ) : ℂ := sphericalJ n z - I * sphericalY n z

private abbrev Recurs (f : ℕ → ℂ → ℂ) :=
  ∀ n z, z ≠ 0 → f (n + 2) z = (2 * (n : ℂ) + 3) / z * f (n + 1) z - f n z

private theorem jrec : Recurs sphericalJ := by
  intro n z hz
  field_simp
  linear_combination sphericalJ_recurrence z n

private theorem yrec : Recurs sphericalY := fun _ _ _ => rfl

private abbrev Ladders (f : ℕ → ℂ → ℂ) (n : ℕ) (z : ℂ) :=
  HasDerivAt (f n) (n / z * f n z - f (n + 1) z) z ∧
    HasDerivAt (f (n + 1)) (f n z - (n + 2 : ℂ) / z * f (n + 1) z) z

private theorem ladders {f : ℕ → ℂ → ℂ} (h : Recurs f) {z : ℂ} (hz : z ≠ 0)
    (hbase : Ladders f 0 z) (n : ℕ) : Ladders f n z := by
  induction n with
  | zero => exact hbase
  | succ n ih =>
    have he := ((((hasDerivAt_const z (2 * (n : ℂ) + 3)).div (hasDerivAt_id z) hz).mul
      ih.2).sub ih.1)
    have hl : f (n + 2) =ᶠ[nhds z] fun t => (2 * (n : ℂ) + 3) / t * f (n + 1) t - f n t :=
      Filter.eventually_of_mem (isOpen_ne.mem_nhds hz) fun t ht => h n t ht
    constructor
    · apply ih.2.congr_deriv
      rw [h n z hz]
      push_cast
      ring
    · apply (he.congr_of_eventuallyEq hl).congr_deriv
      rw [h n z hz]
      simp only [Pi.div_apply, id_eq, Nat.cast_succ]
      field_simp
      ring

private theorem jladders {z : ℂ} (hz : z ≠ 0) (n : ℕ) : Ladders sphericalJ n z := by
  apply ladders jrec hz _ n
  have h₀ : sphericalJ 0 =ᶠ[nhds z] fun t => sin t / t :=
    Filter.eventually_of_mem (isOpen_ne.mem_nhds hz) fun _ ht => sphericalJ_zero_order ht
  have h₁ : sphericalJ 1 =ᶠ[nhds z] fun t => sin t / t ^ 2 - cos t / t :=
    Filter.eventually_of_mem (isOpen_ne.mem_nhds hz) fun _ ht => sphericalJ_one_order ht
  have d₀ := (hasDerivAt_sin z).div (hasDerivAt_id z) hz
  have d₁ := ((hasDerivAt_sin z).div ((hasDerivAt_id z).pow 2) (pow_ne_zero _ hz)).sub
    ((hasDerivAt_cos z).div (hasDerivAt_id z) hz)
  constructor
  · apply (d₀.congr_of_eventuallyEq h₀).congr_deriv
    simp [sphericalJ_one_order hz]
    field_simp
  · apply (d₁.congr_of_eventuallyEq h₁).congr_deriv
    simp [sphericalJ_one_order hz, sphericalJ_zero_order hz]
    field_simp
    ring

private theorem yladders {z : ℂ} (hz : z ≠ 0) (n : ℕ) : Ladders sphericalY n z := by
  apply ladders yrec hz _ n
  have d₀ := (hasDerivAt_cos z).neg.div (hasDerivAt_id z) hz
  have d₁ := ((hasDerivAt_cos z).neg.div ((hasDerivAt_id z).pow 2) (pow_ne_zero _ hz)).sub
    ((hasDerivAt_sin z).div (hasDerivAt_id z) hz)
  constructor
  · apply d₀.congr_deriv
    simp [sphericalY]
    field_simp
    ring
  · apply d₁.congr_deriv
    simp [sphericalY]
    field_simp
    ring

/-- Differentiation of a regular spherical mode in terms of the next degree. -/
theorem hasDerivAt_sphericalJ (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (sphericalJ n) (n / z * sphericalJ n z - sphericalJ (n + 1) z) z :=
  (jladders hz n).1

/-- Differentiation of a singular spherical mode in terms of the next degree. -/
theorem hasDerivAt_sphericalY (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (sphericalY n) (n / z * sphericalY n z - sphericalY (n + 1) z) z :=
  (yladders hz n).1

private def SphericalEquation (n : ℕ) (f : ℂ → ℂ) (z : ℂ) : Prop :=
  z ^ 2 * deriv (deriv f) z + 2 * z * deriv f z +
    (z ^ 2 - n * (n + 1 : ℂ)) * f z = 0

private theorem equation_of_ladders {f : ℕ → ℂ → ℂ} (n : ℕ) {z : ℂ} (hz : z ≠ 0)
    (h : ∀ t : ℂ, t ≠ 0 → Ladders f n t) : SphericalEquation n (f n) z := by
  obtain ⟨d₀, d₁⟩ := h z hz
  have he := ((((hasDerivAt_const z (n : ℂ)).div (hasDerivAt_id z) hz).mul d₀).sub d₁)
  have hl : deriv (f n) =ᶠ[nhds z] fun t => n / t * f n t - f (n + 1) t :=
    Filter.eventually_of_mem (isOpen_ne.mem_nhds hz) fun t ht => (h t ht).1.deriv
  unfold SphericalEquation
  rw [(he.congr_of_eventuallyEq hl).deriv, d₀.deriv]
  simp only [Pi.div_apply, id_eq]
  field_simp
  ring

/-- Radial Helmholtz equation for the regular spherical Bessel function. -/
theorem sphericalJ_equation (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    z ^ 2 * deriv (deriv (sphericalJ n)) z + 2 * z * deriv (sphericalJ n) z +
      (z ^ 2 - n * (n + 1 : ℂ)) * sphericalJ n z = 0 :=
  equation_of_ladders n hz fun _ ht => jladders ht n

/-- Radial Helmholtz equation for the singular spherical Bessel function. -/
theorem sphericalY_equation (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    z ^ 2 * deriv (deriv (sphericalY n)) z + 2 * z * deriv (sphericalY n) z +
      (z ^ 2 - n * (n + 1 : ℂ)) * sphericalY n z = 0 :=
  equation_of_ladders n hz fun _ ht => yladders ht n

private theorem hankel_equation (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    SphericalEquation n (fun t => sphericalJ n t + a * sphericalY n t) z := by
  apply equation_of_ladders (f := fun j t => sphericalJ j t + a * sphericalY j t) n hz
  intro t ht
  obtain ⟨d₀, d₁⟩ := jladders ht n
  obtain ⟨e₀, e₁⟩ := yladders ht n
  constructor
  · apply (d₀.add (e₀.const_mul a)).congr_deriv
    ring
  · apply (d₁.add (e₁.const_mul a)).congr_deriv
    ring

/-- The outgoing and incoming spherical waves both satisfy the radial Helmholtz equation. -/
theorem sphericalHankel_equations (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ∀ f ∈ ({sphericalHankel₁ n, sphericalHankel₂ n} : Set (ℂ → ℂ)),
      z ^ 2 * deriv (deriv f) z + 2 * z * deriv f z + (z ^ 2 - n * (n + 1 : ℂ)) * f z = 0 := by
  intro f hf
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl
  · exact hankel_equation I n hz
  · have he : sphericalHankel₂ n = fun t => sphericalJ n t + -I * sphericalY n t := by
      funext t
      simp [sphericalHankel₂, sub_eq_add_neg]
    rw [he]
    exact hankel_equation (-I) n hz

/-- Exact Wronskian: the regular and singular modes are independent at every nonzero argument. -/
theorem spherical_wronskian (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    sphericalJ n z * deriv (sphericalY n) z - deriv (sphericalJ n) z * sphericalY n z =
      1 / z ^ 2 := by
  rw [(hasDerivAt_sphericalJ n hz).deriv, (hasDerivAt_sphericalY n hz).deriv]
  suffices h : sphericalJ (n + 1) z * sphericalY n z -
      sphericalJ n z * sphericalY (n + 1) z = 1 / z ^ 2 by linear_combination h
  induction n with
  | zero =>
    rw [sphericalJ_zero_order hz, sphericalJ_one_order hz]
    simp only [sphericalY]
    field_simp
    linear_combination z * Complex.sin_sq_add_cos_sq z
  | succ n ih =>
    rw [jrec n z hz, yrec n z hz]
    linear_combination ih

end ProjectAinos.SpecialFunctions.Bessel
