/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.Kasner
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateFrame
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The oscillating regime: one transition between Kasner epochs

Landau–Lifshitz, §118, in the co-ordinates `(τ, x, y, z) = (x 0, x 1, x 2, x 3)`, the signature
`(−+++)` and `c = 1`. The scope is one exact transition between two Kasner epochs, in the vacuum
model of Bianchi type II; the infinite sequence of eras of type IX and the generic oscillatory
approach to the singularity (the BKL conjecture) are not formalised.

**The transition law** (with `Kasner.kasnerExponents u`, `p₁ = −u/(1 + u + u²)`,
`p₂ = (1 + u)/(1 + u + u²)`, `p₃ = u(1 + u)/(1 + u + u²)`, and `Kasner.sum_kasnerExponents`,
`Kasner.sum_sq_kasnerExponents` for `Σp = Σp² = 1`):

* `bounce`, `sum_bounce`, `sum_sq_bounce`: the law
  `p ↦ (−p₁/(1 + 2p₁), (p₂ + 2p₁)/(1 + 2p₁), (p₃ + 2p₁)/(1 + 2p₁))` preserves the Kasner
  conditions.
* `bounce_kasnerExponents`: it maps `p(u)` to `(p₂, p₁, p₃)(u − 1)` (the next epoch);
  `bounce_kasnerExponents_era`: for `u ≠ 1` this is `(p₃, p₁, p₂)(1/(u − 1))` (a new era).
* `bklMap`, `one_le_bklMap`, `exists_bounce_eq_comp`: the map `u ↦ u − 1` for `u ≥ 2`,
  `u ↦ 1/(u − 1)` for `u < 2` sends `u > 1` to a parameter `≥ 1`, and the exponents after the
  bounce are a permutation of `p(bklMap u)`.

**The model of type II** (`TypeII.Data`: an open set `I` of times and the logarithms
`α = ln a`, `β = ln b`, `γ = ln c`, smooth on `I`):

* `TypeII.Data.metric`: `ds² = −(abc)² dτ² + a² (dx − z dy)² + b² dy² + c² dz²` on `τ ∈ I`,
  with the lapse `N = abc` (`dt = abc dτ`); it is diagonal in the invariant coframe
  `(dx − z dy, dy, dz)` of the Heisenberg group (`[∂_z, ∂_y + z ∂_x] = ∂_x`) but not in the
  co-ordinates.
* The Ricci tensor is computed in the orthonormal frame `E₀ = N⁻¹ ∂_τ`, `E₁ = a⁻¹ ∂_x`,
  `E₂ = b⁻¹ (∂_y + z ∂_x)`, `E₃ = c⁻¹ ∂_z` (`frameField`, `frame`) with the frame tools of
  `CoordinateFrame.lean` (`ricci_orthonormalFrameOf`): `commutator_frame` gives the commutator
  coefficients `λ_{k0k} = −α_k'/N`, `λ_{123} = −a/(bc)` (`lam`), `ricci_frame` the frame
  components `frameRicci`, and `frameRicci_eq` evaluates them:
  `R₀₀ = (2(α'β' + α'γ' + β'γ') − (α'' + β'' + γ''))/N²`, `R₁₁ = (α'' + a⁴/2)/N²`,
  `R₂₂ = (β'' − a⁴/2)/N²`, `R₃₃ = (γ'' − a⁴/2)/N²`, the others zero (`ricciDiag`).
* `TypeII.Data.isVacuum_iff`: **the vacuum equations are the one-wall system** (`OneWall`)
  `α'' = −a⁴/2`, `β'' = γ'' = a⁴/2`, `α'β' + α'γ' + β'γ' = a⁴/4` on `I`;
  `isEinstein_of_isVacuum`: then the co-ordinate vacuum Einstein equations hold.
* `TypeII.Data.exponents`: the logarithmic rates `p_k = (ln a_k)'/(ln abc)'`, `Σp = 1`.

**The exact transition** (`TypeII.solution u`, the solution of Taub):
`a² = 2u/cosh 2uτ`, `b² = e^{2τ} cosh 2uτ`, `c² = e^{2u²τ} cosh 2uτ`.

* `TypeII.isVacuum_solution`, `TypeII.isEinstein_solution`: it is a vacuum solution for `u > 0`.
* `TypeII.abs_exponents_sub_le_atTop`, `TypeII.abs_exponents_sub_le_atBot`,
  `TypeII.abs_exponents_sub_le`: for every `τ`, `|p_k(τ) − p_k(u)| ≤ 8u/(1 + u²) e^{−4uτ}` and
  `|p_k(τ) − q_k| ≤ 8u/(1 + u²) e^{4uτ}` with `q = (p₂, p₁, p₃)(u − 1)`; hence the bound
  `8u/(1 + u²) e^{−4uτ₀}` on `τ ≥ τ₀` and on `τ ≤ −τ₀`.
* `TypeII.tendsto_exponents`: **the BKL transition**: the exponents tend to `p(u)` as `τ → +∞`
  and to `(p₂, p₁, p₃)(u − 1) = bounce (p(u))` as `τ → −∞` (`tendsto_exponents_atBot_bounce`).
  Toward the singularity (`τ` decreasing) the negative exponent of `a` becomes positive and `b`
  takes the negative exponent (`kasnerExponents_zero_neg_and_pos`,
  `kasnerExponents_sub_one_zero_nonpos`);
  `tendsto_exponents_atBot_era`: for `u ≠ 1` the limit is `(p₃, p₁, p₂)(1/(u − 1))`, the change
  of era when `1 < u < 2`.
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap Set TopologicalSpace Filter
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.BKL

open Kasner (kasnerExponents kasnerDenom_pos)

/-! ### The transition law of the exponents -/

/-- **The transition law of a bounce off the wall of `a`** (Landau–Lifshitz, §118): the exponents
`(p_a, p_b, p_c)` of the epoch before the bounce become
`(−p_a/(1 + 2p_a), (p_b + 2p_a)/(1 + 2p_a), (p_c + 2p_a)/(1 + 2p_a))`. -/
def bounce (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![-p 0 / (1 + 2 * p 0), (p 1 + 2 * p 0) / (1 + 2 * p 0), (p 2 + 2 * p 0) / (1 + 2 * p 0)]

/-- The transition law preserves `Σp = 1`. -/
theorem sum_bounce {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) (hp : 1 + 2 * p 0 ≠ 0) :
    ∑ α, bounce p α = 1 := by
  rw [Fin.sum_univ_three] at h1
  simp only [Fin.sum_univ_three, bounce, Fin.isValue, Matrix.cons_val]
  rw [← add_div, ← add_div, div_eq_one_iff_eq hp]
  linear_combination h1

/-- The transition law preserves `Σp² = 1` on the solutions of `Σp = 1`. -/
theorem sum_sq_bounce {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1)
    (hp : 1 + 2 * p 0 ≠ 0) : ∑ α, bounce p α ^ 2 = 1 := by
  rw [Fin.sum_univ_three] at h1 h2
  simp only [Fin.sum_univ_three, bounce, Fin.isValue, Matrix.cons_val, div_pow]
  rw [← add_div, ← add_div, div_eq_one_iff_eq (pow_ne_zero 2 hp)]
  linear_combination h2 + 4 * p 0 * h1

/-- `1 + 2p₁(u) = (1 + (u − 1) + (u − 1)²)/(1 + u + u²)`. -/
theorem one_add_two_mul_kasnerExponents (u : ℝ) :
    1 + 2 * kasnerExponents u 0 = (1 + (u - 1) + (u - 1) ^ 2) / (1 + u + u ^ 2) := by
  have h := (kasnerDenom_pos u).ne'
  simp only [kasnerExponents, Fin.isValue, Matrix.cons_val_zero]
  field_simp
  ring

/-- **The next Kasner epoch** (Landau–Lifshitz, §118): the transition law maps the exponents
`p(u)` to `p(u − 1)`, the first two exchanged: the negative exponent `p₁(u)` of `a` becomes the
positive `p₂(u − 1)`, and `b` takes the negative exponent `p₁(u − 1)`. -/
theorem bounce_kasnerExponents (u : ℝ) :
    bounce (kasnerExponents u) =
      ![kasnerExponents (u - 1) 1, kasnerExponents (u - 1) 0, kasnerExponents (u - 1) 2] := by
  have h := (kasnerDenom_pos u).ne'
  have h' := (kasnerDenom_pos (u - 1)).ne'
  have hd := one_add_two_mul_kasnerExponents u
  funext i
  fin_cases i <;>
    simp only [bounce, hd, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val] <;>
    simp only [kasnerExponents, Fin.isValue, Matrix.cons_val] <;>
    field_simp <;> ring

/-- **A new era** (Landau–Lifshitz, §118): for `u ≠ 1` the exponents after the bounce are
`p(1/(u − 1))` permuted: `a` takes the largest exponent `p₃`, `b` the negative `p₁`. -/
theorem bounce_kasnerExponents_era {u : ℝ} (hu : u ≠ 1) :
    bounce (kasnerExponents u) =
      ![kasnerExponents (u - 1)⁻¹ 2, kasnerExponents (u - 1)⁻¹ 0, kasnerExponents (u - 1)⁻¹ 1] := by
  rw [bounce_kasnerExponents, Kasner.kasnerExponents_inv (sub_ne_zero.mpr hu)]
  simp

/-- **The BKL map** `u ↦ u − 1` for `u ≥ 2` (the next epoch of the same era) and
`u ↦ 1/(u − 1)` for `u < 2` (the first epoch of a new era). -/
def bklMap (u : ℝ) : ℝ := if 2 ≤ u then u - 1 else (u - 1)⁻¹

/-- Within an era: `bklMap u = u − 1` for `u ≥ 2`. -/
theorem bklMap_of_two_le {u : ℝ} (hu : 2 ≤ u) : bklMap u = u - 1 := by simp [bklMap, hu]

/-- A change of era: `bklMap u = 1/(u − 1)` for `u < 2`. -/
theorem bklMap_of_lt_two {u : ℝ} (hu : u < 2) : bklMap u = (u - 1)⁻¹ := by
  simp [bklMap, not_le.mpr hu]

/-- The BKL map sends `u > 1` to a parameter `≥ 1` of an ordered Kasner epoch. -/
theorem one_le_bklMap {u : ℝ} (hu : 1 < u) : 1 ≤ bklMap u := by
  rcases le_or_gt 2 u with h | h
  · rw [bklMap_of_two_le h]
    linarith
  · rw [bklMap_of_lt_two h, one_le_inv₀ (by linarith)]
    linarith

/-- **The exponents after a bounce are a permutation of `p(bklMap u)`** for `u ≠ 1`. -/
theorem exists_bounce_eq_comp {u : ℝ} (hu : u ≠ 1) :
    ∃ σ : Equiv.Perm (Fin 3), bounce (kasnerExponents u) = kasnerExponents (bklMap u) ∘ σ := by
  rcases le_or_gt 2 u with h | h
  · refine ⟨Equiv.swap 0 1, ?_⟩
    rw [bounce_kasnerExponents, bklMap_of_two_le h]
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  · refine ⟨Equiv.swap 0 1 * Equiv.swap 0 2, ?_⟩
    rw [bounce_kasnerExponents_era hu, bklMap_of_lt_two h]
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]

/-- The signs of the exchange: for `u > 0` the exponent `p₁(u)` of `a` before the bounce is
negative and its exponent `p₂(u − 1)` after the bounce is positive. -/
theorem kasnerExponents_zero_neg_and_pos {u : ℝ} (hu : 0 < u) :
    kasnerExponents u 0 < 0 ∧ 0 < kasnerExponents (u - 1) 1 := by
  simp only [kasnerExponents, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · exact div_neg_of_neg_of_pos (by linarith) (kasnerDenom_pos u)
  · exact div_pos (by linarith) (kasnerDenom_pos (u - 1))

/-- For `u ≥ 1`, `b` takes the exponent `p₁(u − 1) ≤ 0` after the bounce (negative for
`u > 1`). -/
theorem kasnerExponents_sub_one_zero_nonpos {u : ℝ} (hu : 1 ≤ u) :
    kasnerExponents (u - 1) 0 ≤ 0 := by
  simp only [kasnerExponents, Fin.isValue, Matrix.cons_val_zero]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (kasnerDenom_pos (u - 1)).le

/-! ## The vacuum model of type II -/

namespace TypeII

open SmoothGeometry CoordinateMetric LorentzMetric

local notation "E" => MinkowskiModel 3

/-- **The data of a diagonal model of type II** with the lapse `N = abc` (Landau–Lifshitz, §118,
with `dt = abc dτ`): an open set `I` of times `τ` and the logarithms `α = ln a`, `β = ln b`,
`γ = ln c` of the three scale factors, smooth on `I`. -/
structure Data where
  /-- The open set of the times `τ`. -/
  I : Set ℝ
  /-- The set of times is open. -/
  isOpen_I : IsOpen I
  /-- `α = ln a`. -/
  α : ℝ → ℝ
  /-- `β = ln b`. -/
  β : ℝ → ℝ
  /-- `γ = ln c`. -/
  γ : ℝ → ℝ
  /-- `α` is smooth on `I`. -/
  contDiffOn_α : ContDiffOn ℝ ∞ α I
  /-- `β` is smooth on `I`. -/
  contDiffOn_β : ContDiffOn ℝ ∞ β I
  /-- `γ` is smooth on `I`. -/
  contDiffOn_γ : ContDiffOn ℝ ∞ γ I

namespace Data

variable (D : Data)

/-- The logarithms `(α, β, γ)` of the scale factors as a triple. -/
def w : Fin 3 → ℝ → ℝ := ![D.α, D.β, D.γ]

@[simp] theorem w_zero : D.w 0 = D.α := rfl

@[simp] theorem w_one : D.w 1 = D.β := rfl

@[simp] theorem w_two : D.w 2 = D.γ := rfl

/-- The logarithms are smooth on `I`. -/
theorem contDiffOn_w (k : Fin 3) : ContDiffOn ℝ ∞ (D.w k) D.I := by
  fin_cases k
  · exact D.contDiffOn_α
  · exact D.contDiffOn_β
  · exact D.contDiffOn_γ

/-- The scale factor `a = e^α`. -/
def a (τ : ℝ) : ℝ := Real.exp (D.α τ)

/-- The scale factor `b = e^β`. -/
def b (τ : ℝ) : ℝ := Real.exp (D.β τ)

/-- The scale factor `c = e^γ`. -/
def c (τ : ℝ) : ℝ := Real.exp (D.γ τ)

/-- The lapse `N = abc`. -/
def lapse (τ : ℝ) : ℝ := D.a τ * D.b τ * D.c τ

/-- The logarithmic rate of the volume, `(ln abc)' = α' + β' + γ'`. -/
def expansion (τ : ℝ) : ℝ := deriv D.α τ + deriv D.β τ + deriv D.γ τ

theorem a_pos (τ : ℝ) : 0 < D.a τ := Real.exp_pos _

theorem b_pos (τ : ℝ) : 0 < D.b τ := Real.exp_pos _

theorem c_pos (τ : ℝ) : 0 < D.c τ := Real.exp_pos _

/-- The lapse is positive. -/
theorem lapse_pos (τ : ℝ) : 0 < D.lapse τ :=
  mul_pos (mul_pos (D.a_pos τ) (D.b_pos τ)) (D.c_pos τ)

variable {D}

theorem hasDerivAt_w (k : Fin 3) {τ : ℝ} (hτ : τ ∈ D.I) :
    HasDerivAt (D.w k) (deriv (D.w k) τ) τ :=
  FLRW.hasDerivAt_of_contDiffOn D.isOpen_I (D.contDiffOn_w k) hτ

theorem hasDerivAt_deriv_w (k : Fin 3) {τ : ℝ} (hτ : τ ∈ D.I) :
    HasDerivAt (deriv (D.w k)) (deriv (deriv (D.w k)) τ) τ :=
  FLRW.hasDerivAt_of_contDiffOn D.isOpen_I
    (FLRW.contDiffOn_deriv_of_contDiffOn D.isOpen_I (D.contDiffOn_w k)) hτ

theorem hasDerivAt_a {τ : ℝ} (hτ : τ ∈ D.I) : HasDerivAt D.a (D.a τ * deriv D.α τ) τ :=
  (hasDerivAt_w 0 hτ).exp

theorem hasDerivAt_b {τ : ℝ} (hτ : τ ∈ D.I) : HasDerivAt D.b (D.b τ * deriv D.β τ) τ :=
  (hasDerivAt_w 1 hτ).exp

theorem hasDerivAt_c {τ : ℝ} (hτ : τ ∈ D.I) : HasDerivAt D.c (D.c τ * deriv D.γ τ) τ :=
  (hasDerivAt_w 2 hτ).exp

/-- `N' = N (α' + β' + γ')`. -/
theorem hasDerivAt_lapse {τ : ℝ} (hτ : τ ∈ D.I) :
    HasDerivAt D.lapse (D.lapse τ * D.expansion τ) τ := by
  refine (((hasDerivAt_a hτ).fun_mul (hasDerivAt_b hτ)).fun_mul (hasDerivAt_c hτ)).congr_deriv ?_
  simp only [lapse, expansion]
  ring

variable (D)

theorem contDiffOn_a : ContDiffOn ℝ ∞ D.a D.I := Real.contDiff_exp.comp_contDiffOn D.contDiffOn_α

theorem contDiffOn_b : ContDiffOn ℝ ∞ D.b D.I := Real.contDiff_exp.comp_contDiffOn D.contDiffOn_β

theorem contDiffOn_c : ContDiffOn ℝ ∞ D.c D.I := Real.contDiff_exp.comp_contDiffOn D.contDiffOn_γ

theorem contDiffOn_lapse : ContDiffOn ℝ ∞ D.lapse D.I :=
  (D.contDiffOn_a.mul D.contDiffOn_b).mul D.contDiffOn_c

/-! ### The domain and the metric -/

/-- The domain `τ ∈ I` of the co-ordinates `(τ, x, y, z) = (x 0, x 1, x 2, x 3)`. -/
def domain : Opens E :=
  ⟨{x | x 0 ∈ D.I}, D.isOpen_I.preimage (continuous_apply 0)⟩

variable {D}

theorem time_mem {x : E} (hx : x ∈ D.domain) : x 0 ∈ D.I := hx

/-- The point `(τ, 0, 0, 0)` lies in the domain for every `τ ∈ I`. -/
theorem timeAxis_mem {τ : ℝ} (hτ : τ ∈ D.I) : FLRW.timeAxis τ ∈ D.domain := by
  simpa [domain] using hτ

/-- A smooth function of the time is smooth on the domain. -/
theorem contDiffOn_time {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f D.I) :
    ContDiffOn ℝ ∞ (fun z : E => f (z 0)) D.domain :=
  hf.comp (contDiff_apply ℝ (fun _ => ℝ) 0).contDiffOn fun _ hz => time_mem hz

variable (D)

/-- The invariant one-form `ω¹ = dx − z dy` at the point `x`. -/
def omega (x : E) : E →L[ℝ] ℝ := (proj 1 : E →L[ℝ] ℝ) - x 3 • (proj 2 : E →L[ℝ] ℝ)

/-- The form `−N² dτ² + a² (dx − z dy)² + b² dy² + c² dz²` at the point `x`. -/
def form (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (-(D.lapse (x 0) ^ 2)) • (proj 0 : E →L[ℝ] ℝ).smulRight (proj 0 : E →L[ℝ] ℝ) +
    (D.a (x 0) ^ 2) • (omega x).smulRight (omega x) +
    (D.b (x 0) ^ 2) • (proj 2 : E →L[ℝ] ℝ).smulRight (proj 2 : E →L[ℝ] ℝ) +
    (D.c (x 0) ^ 2) • (proj 3 : E →L[ℝ] ℝ).smulRight (proj 3 : E →L[ℝ] ℝ)

theorem form_apply (x v u : E) :
    D.form x v u = -(D.lapse (x 0) ^ 2) * (v 0 * u 0) +
      D.a (x 0) ^ 2 * ((v 1 - x 3 * v 2) * (u 1 - x 3 * u 2)) + D.b (x 0) ^ 2 * (v 2 * u 2) +
      D.c (x 0) ^ 2 * (v 3 * u 3) := by
  simp only [form, omega, add_apply, smul_apply, smulRight_apply, sub_apply, proj_apply,
    smul_eq_mul]

theorem form_symm (x v u : E) : D.form x v u = D.form x u v := by
  rw [form_apply, form_apply]
  ring

theorem contDiffOn_form : ContDiffOn ℝ ∞ D.form D.domain := by
  refine contDiffOn_clm_apply.mpr fun v => contDiffOn_clm_apply.mpr fun u => ?_
  simp only [form_apply]
  have h3 : ContDiffOn ℝ ∞ (fun x : E => x 3) D.domain :=
    (contDiff_apply ℝ (fun _ => ℝ) 3).contDiffOn
  have hω (q : E) : ContDiffOn ℝ ∞ (fun x : E => q 1 - x 3 * q 2) D.domain :=
    contDiffOn_const.sub (h3.mul contDiffOn_const)
  exact (((((contDiffOn_time D.contDiffOn_lapse).pow 2).neg.mul contDiffOn_const).add
    (((contDiffOn_time D.contDiffOn_a).pow 2).mul ((hω v).mul (hω u)))).add
    (((contDiffOn_time D.contDiffOn_b).pow 2).mul contDiffOn_const)).add
    (((contDiffOn_time D.contDiffOn_c).pow 2).mul contDiffOn_const)

/-- **The metric of the type II model** `ds² = −(abc)² dτ² + a² (dx − z dy)² + b² dy² + c² dz²`
on the domain (Landau–Lifshitz, §118, with `dt = abc dτ`). It is diagonal in the invariant
coframe `(dx − z dy, dy, dz)` but not in the co-ordinates. -/
def metric : CoordinateMetric .timeNegative 3 D.domain :=
  ofCriterion D.form D.contDiffOn_form (fun x _ v u => D.form_symm x v u)
    (fun x _ => by
      rw [form_apply, LorentzConvention.timeSign_timeNegative]
      have := pow_pos (D.lapse_pos (x 0)) 2
      simp only [Fin.cons_zero, mul_one]
      have h1 : (Fin.cons 1 (0 : Fin 3 → ℝ) : E) 1 = 0 := rfl
      have h2 : (Fin.cons 1 (0 : Fin 3 → ℝ) : E) 2 = 0 := rfl
      have h3 : (Fin.cons 1 (0 : Fin 3 → ℝ) : E) 3 = 0 := rfl
      rw [h1, h2, h3]
      linarith)
    (fun x _ v hv => by
      rw [form_apply, LorentzConvention.timeSign_timeNegative]
      have h0 : (Fin.cons 0 v : E) 0 = 0 := rfl
      have h1 : (Fin.cons 0 v : E) 1 = v 0 := rfl
      have h2 : (Fin.cons 0 v : E) 2 = v 1 := rfl
      have h3 : (Fin.cons 0 v : E) 3 = v 2 := rfl
      rw [h0, h1, h2, h3]
      have ha := pow_pos (D.a_pos (x 0)) 2
      have hb := pow_pos (D.b_pos (x 0)) 2
      have hc := pow_pos (D.c_pos (x 0)) 2
      have q1 := mul_nonneg ha.le (mul_self_nonneg (v 0 - x 3 * v 1))
      have q2 := mul_nonneg hb.le (mul_self_nonneg (v 1))
      have q3 := mul_nonneg hc.le (mul_self_nonneg (v 2))
      by_contra hle
      apply hv
      have z2 : v 1 * v 1 = 0 :=
        (mul_eq_zero.mp (le_antisymm (by nlinarith) q2)).resolve_left hb.ne'
      have z3 : v 2 * v 2 = 0 :=
        (mul_eq_zero.mp (le_antisymm (by nlinarith) q3)).resolve_left hc.ne'
      have z1 : (v 0 - x 3 * v 1) * (v 0 - x 3 * v 1) = 0 :=
        (mul_eq_zero.mp (le_antisymm (by nlinarith) q1)).resolve_left ha.ne'
      have e2 := mul_self_eq_zero.mp z2
      have e3 := mul_self_eq_zero.mp z3
      have e1 := mul_self_eq_zero.mp z1
      rw [e2, mul_zero, sub_zero] at e1
      funext i
      fin_cases i
      · exact e1
      · exact e2
      · exact e3)

@[simp] theorem metric_form : (metric D).form = D.form := rfl

/-! ### The orthonormal frame -/

/-- The co-ordinate unit vector `e_k`. -/
def unit (k : Fin 4) : E := Pi.single k 1

@[simp] theorem unit_apply (k j : Fin 4) : unit k j = if j = k then 1 else 0 := by
  simp [unit, Pi.single_apply]

/-- The components of the orthonormal frame `E₀ = N⁻¹ ∂_τ`, `E₁ = a⁻¹ ∂_x`,
`E₂ = b⁻¹ (∂_y + z ∂_x)`, `E₃ = c⁻¹ ∂_z`, dual to the coframe
`(N dτ, a (dx − z dy), b dy, c dz)`. -/
def frameField (p : Fin 4) (x : E) : E :=
  ![(D.lapse (x 0))⁻¹ • unit 0, (D.a (x 0))⁻¹ • unit 1,
    (D.b (x 0))⁻¹ • unit 2 + (x 3 * (D.b (x 0))⁻¹) • unit 1, (D.c (x 0))⁻¹ • unit 3] p

/-- The time component of a frame field: `E_p⁰ = δ_{p0} N⁻¹`. -/
theorem frameField_apply_zero (p : Fin 4) (x : E) :
    D.frameField p x 0 = if p = 0 then (D.lapse (x 0))⁻¹ else 0 := by
  fin_cases p <;> simp [frameField]

/-- **The frame is orthonormal**: `g(E_p, E_q) = η_{pq}`. -/
theorem form_frameField (x : E) (p q : Fin 4) :
    D.form x (D.frameField p x) (D.frameField q x) =
      if p = q then lorentzSign .timeNegative p else 0 := by
  have hN := (D.lapse_pos (x 0)).ne'
  have ha := (D.a_pos (x 0)).ne'
  have hb := (D.b_pos (x 0)).ne'
  have hc := (D.c_pos (x 0)).ne'
  fin_cases p <;> fin_cases q <;>
    simp [form_apply, frameField, lorentzSign, LorentzConvention.timeSign_timeNegative, ha] <;>
    field_simp
  -- the case `(p, q) = (2, 1)`
  ring

theorem contDiffOn_frameField (p : Fin 4) : ContDiffOn ℝ ∞ (D.frameField p) D.domain := by
  have hinv {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f D.I) (hpos : ∀ τ, 0 < f τ) :
      ContDiffOn ℝ ∞ (fun x : E => (f (x 0))⁻¹) D.domain :=
    (contDiffOn_time hf).inv fun x _ => (hpos (x 0)).ne'
  have h3 : ContDiffOn ℝ ∞ (fun x : E => x 3) D.domain :=
    (contDiff_apply ℝ (fun _ => ℝ) 3).contDiffOn
  fin_cases p
  · exact (hinv D.contDiffOn_lapse D.lapse_pos).smul contDiffOn_const
  · exact (hinv D.contDiffOn_a D.a_pos).smul contDiffOn_const
  · exact ((hinv D.contDiffOn_b D.b_pos).smul contDiffOn_const).add
      ((h3.mul (hinv D.contDiffOn_b D.b_pos)).smul contDiffOn_const)
  · exact (hinv D.contDiffOn_c D.c_pos).smul contDiffOn_const

/-! ### Derivatives of the frame -/

variable {D}

/-- The derivative of `1/f` for `f' = f r`. -/
private theorem hasDerivAt_inv_of_log {f : ℝ → ℝ} {r τ : ℝ} (hf : HasDerivAt f (f τ * r) τ)
    (h : f τ ≠ 0) : HasDerivAt (fun s => (f s)⁻¹) (-r / f τ) τ :=
  (hf.inv h).congr_deriv (by field_simp)

variable (D) in
/-- The derivatives of the frame fields along `v`, in closed form. -/
def frameDeriv (p : Fin 4) (y v : E) : E :=
  ![(-D.expansion (y 0) / D.lapse (y 0) * v 0) • unit 0,
    (-deriv D.α (y 0) / D.a (y 0) * v 0) • unit 1,
    (-deriv D.β (y 0) / D.b (y 0) * v 0) • unit 2 +
      (-deriv D.β (y 0) / D.b (y 0) * v 0 * y 3 + (D.b (y 0))⁻¹ * v 3) • unit 1,
    (-deriv D.γ (y 0) / D.c (y 0) * v 0) • unit 3] p

theorem fderiv_frameField_zero {y : E} (hy : y ∈ D.domain) (v : E) :
    fderiv ℝ (D.frameField 0) y v = D.frameDeriv 0 y v := by
  have h := (FLRW.hasFDerivAt_time (hasDerivAt_inv_of_log (hasDerivAt_lapse (time_mem hy))
    (D.lapse_pos (y 0)).ne')).smul_const (unit 0)
  rw [show D.frameField 0 = fun x : E => (D.lapse (x 0))⁻¹ • unit 0 from rfl, h.fderiv]
  simp [frameDeriv]

theorem fderiv_frameField_one {y : E} (hy : y ∈ D.domain) (v : E) :
    fderiv ℝ (D.frameField 1) y v = D.frameDeriv 1 y v := by
  have h := (FLRW.hasFDerivAt_time (hasDerivAt_inv_of_log (hasDerivAt_a (time_mem hy))
    (D.a_pos (y 0)).ne')).smul_const (unit 1)
  rw [show D.frameField 1 = fun x : E => (D.a (x 0))⁻¹ • unit 1 from rfl, h.fderiv]
  simp [frameDeriv]

theorem fderiv_frameField_two {y : E} (hy : y ∈ D.domain) (v : E) :
    fderiv ℝ (D.frameField 2) y v = D.frameDeriv 2 y v := by
  have hb := FLRW.hasFDerivAt_time (hasDerivAt_inv_of_log (hasDerivAt_b (time_mem hy))
    (D.b_pos (y 0)).ne')
  have h := (hb.smul_const (unit 2)).fun_add (((hasFDerivAt_apply 3 y).fun_mul hb).smul_const
    (unit 1))
  rw [show D.frameField 2 = fun x : E =>
    (D.b (x 0))⁻¹ • unit 2 + (x 3 * (D.b (x 0))⁻¹) • unit 1 from rfl, h.fderiv]
  simp only [frameDeriv]
  ext j
  simp
  ring_nf

theorem fderiv_frameField_three {y : E} (hy : y ∈ D.domain) (v : E) :
    fderiv ℝ (D.frameField 3) y v = D.frameDeriv 3 y v := by
  have h := (FLRW.hasFDerivAt_time (hasDerivAt_inv_of_log (hasDerivAt_c (time_mem hy))
    (D.c_pos (y 0)).ne')).smul_const (unit 3)
  rw [show D.frameField 3 = fun x : E => (D.c (x 0))⁻¹ • unit 3 from rfl, h.fderiv]
  simp [frameDeriv]

/-- **The derivatives of the frame fields.** -/
theorem fderiv_frameField {y : E} (hy : y ∈ D.domain) (p : Fin 4) (v : E) :
    fderiv ℝ (D.frameField p) y v = D.frameDeriv p y v := by
  fin_cases p
  · exact fderiv_frameField_zero hy v
  · exact fderiv_frameField_one hy v
  · exact fderiv_frameField_two hy v
  · exact fderiv_frameField_three hy v

/-! ### The commutator coefficients -/

variable (D)

/-- The rate `h_k = (ln a_k)'/N` of the scale factor `a_k` in the proper time. -/
def rate (k : Fin 3) (τ : ℝ) : ℝ := deriv (D.w k) τ / D.lapse τ

/-- The time derivative of the rate: `((ln a_k)'' − (ln a_k)' (ln abc)')/N`. -/
def rateDeriv (k : Fin 3) (τ : ℝ) : ℝ :=
  (deriv (deriv (D.w k)) τ - deriv (D.w k) τ * D.expansion τ) / D.lapse τ

/-- The wall coefficient `m = a/(bc)`: `[E₂, E₃] = −m E₁`. -/
def wall (τ : ℝ) : ℝ := D.a τ / (D.b τ * D.c τ)

/-- The time derivative of the wall coefficient: `(α' − β' − γ') m`. -/
def wallDeriv (τ : ℝ) : ℝ := (deriv D.α τ - deriv D.β τ - deriv D.γ τ) * D.wall τ

/-- The signs `λ_{kij}/m` of the spatial commutator coefficients: `−1` for `(k, i, j) = (0, 1, 2)`,
`1` for `(0, 2, 1)`, `0` otherwise. -/
def wallSign (k i j : Fin 3) : ℝ :=
  if k = 0 ∧ i = 1 ∧ j = 2 then -1 else if k = 0 ∧ i = 2 ∧ j = 1 then 1 else 0

/-- **The commutator coefficients** `λ_{pqr} = g(E_p, [E_q, E_r])`, functions of the time:
`λ_{k0k} = −h_k`, `λ_{kk0} = h_k`, `λ_{123} = −m`, `λ_{132} = m` (frame indices `1, 2, 3`),
all others zero. -/
def lam (τ : ℝ) (p q r : Fin 4) : ℝ :=
  Matrix.vecCons 0 (fun k => Matrix.vecCons
    (Matrix.vecCons 0 (fun j => (if k = j then -1 else 0) * D.rate k τ) r)
    (fun i => Matrix.vecCons (-((if k = i then -1 else 0) * D.rate k τ))
      (fun j => wallSign k i j * D.wall τ) r) q) p

/-- The time derivatives of the commutator coefficients in closed form. -/
def lamDeriv (τ : ℝ) (p q r : Fin 4) : ℝ :=
  Matrix.vecCons 0 (fun k => Matrix.vecCons
    (Matrix.vecCons 0 (fun j => (if k = j then -1 else 0) * D.rateDeriv k τ) r)
    (fun i => Matrix.vecCons (-((if k = i then -1 else 0) * D.rateDeriv k τ))
      (fun j => wallSign k i j * D.wallDeriv τ) r) q) p

variable {D}

/-- **The commutator coefficients of the frame** at a point of the domain are `lam` at its
time. -/
theorem commutator_frame {y : E} (hy : y ∈ D.domain) (p q r : Fin 4) :
    D.form y (D.frameField p y) (lieBracketOf (D.frameField q) (D.frameField r) y) =
      D.lam (y 0) p q r := by
  have hN := (D.lapse_pos (y 0)).ne'
  have ha := (D.a_pos (y 0)).ne'
  have hb := (D.b_pos (y 0)).ne'
  have hc := (D.c_pos (y 0)).ne'
  rw [lieBracketOf, fderiv_frameField hy, fderiv_frameField hy]
  fin_cases p <;> fin_cases q <;> fin_cases r <;>
    simp [form_apply, frameField, frameDeriv, lam, wallSign, rate, wall, hN, ha, hb, hc] <;>
    field_simp <;> ring_nf
  -- the case `(p, q, r) = (2, 0, 1)`
  simp

/-! ### Derivatives and smoothness of the commutator coefficients -/

theorem hasDerivAt_rate (k : Fin 3) {τ : ℝ} (hτ : τ ∈ D.I) :
    HasDerivAt (D.rate k) (D.rateDeriv k τ) τ := by
  have hN := (D.lapse_pos τ).ne'
  refine ((hasDerivAt_deriv_w k hτ).fun_div (hasDerivAt_lapse hτ) hN).congr_deriv ?_
  simp only [rateDeriv]
  field_simp

theorem hasDerivAt_wall {τ : ℝ} (hτ : τ ∈ D.I) : HasDerivAt D.wall (D.wallDeriv τ) τ := by
  have hb := (D.b_pos τ).ne'
  have hc := (D.c_pos τ).ne'
  refine ((hasDerivAt_a hτ).fun_div ((hasDerivAt_b hτ).fun_mul (hasDerivAt_c hτ))
    (mul_ne_zero hb hc)).congr_deriv ?_
  simp only [wallDeriv, wall]
  field_simp
  ring

/-- The commutator coefficients have the derivatives `lamDeriv`. -/
theorem hasDerivAt_lam {τ : ℝ} (hτ : τ ∈ D.I) (p q r : Fin 4) :
    HasDerivAt (fun s => D.lam s p q r) (D.lamDeriv τ p q r) τ := by
  refine Fin.cases ?_ (fun k => ?_) p
  · exact hasDerivAt_const τ (0 : ℝ)
  · refine Fin.cases ?_ (fun i => ?_) q <;> refine Fin.cases ?_ (fun j => ?_) r
    · exact hasDerivAt_const τ (0 : ℝ)
    · exact (hasDerivAt_rate k hτ).const_mul _
    · exact ((hasDerivAt_rate k hτ).const_mul _).fun_neg
    · exact (hasDerivAt_wall hτ).const_mul _

variable (D)

theorem contDiffOn_rate (k : Fin 3) : ContDiffOn ℝ ∞ (D.rate k) D.I :=
  (FLRW.contDiffOn_deriv_of_contDiffOn D.isOpen_I (D.contDiffOn_w k)).div D.contDiffOn_lapse
    fun τ _ => (D.lapse_pos τ).ne'

theorem contDiffOn_wall : ContDiffOn ℝ ∞ D.wall D.I :=
  D.contDiffOn_a.div (D.contDiffOn_b.mul D.contDiffOn_c)
    fun τ _ => (mul_pos (D.b_pos τ) (D.c_pos τ)).ne'

/-- The commutator coefficients are smooth functions of the time on `I`. -/
theorem contDiffOn_lam (p q r : Fin 4) : ContDiffOn ℝ ∞ (fun τ => D.lam τ p q r) D.I := by
  refine Fin.cases ?_ (fun k => ?_) p
  · exact contDiffOn_const
  · refine Fin.cases ?_ (fun i => ?_) q <;> refine Fin.cases ?_ (fun j => ?_) r
    · exact contDiffOn_const
    · exact contDiffOn_const.mul (D.contDiffOn_rate k)
    · exact (contDiffOn_const.mul (D.contDiffOn_rate k)).neg
    · exact contDiffOn_const.mul D.contDiffOn_wall

/-! ### The Ricci tensor in the frame -/

/-- The rotation coefficients `γ_{pqr} = ½ (λ_{pqr} + λ_{qrp} − λ_{rpq})` at the time `τ`. -/
def rot (τ : ℝ) (p q r : Fin 4) : ℝ := (D.lam τ p q r + D.lam τ q r p - D.lam τ r p q) / 2

/-- The time derivatives of the rotation coefficients in closed form. -/
def rotDeriv (τ : ℝ) (p q r : Fin 4) : ℝ :=
  (D.lamDeriv τ p q r + D.lamDeriv τ q r p - D.lamDeriv τ r p q) / 2

/-- **The frame components of the Ricci tensor at the time `τ`**:
`R_{bk} = Σ_i η_{ii} (δ_{i0} γ̇_{kib}/N − δ_{b0} γ̇_{kii}/N −
Σ_f η_{ff} (γ_{kfb} γ_{ifi} − γ_{kfi} γ_{ifb} + λ_{fib} γ_{kif}))`, the dot being `d/dτ`; the
factor `1/N` is the derivative along `E₀ = N⁻¹ ∂_τ`. -/
def frameRicci (τ : ℝ) (b k : Fin 4) : ℝ :=
  ∑ i, lorentzSign .timeNegative i *
    ((if i = 0 then D.rotDeriv τ k i b / D.lapse τ else 0) -
      (if b = 0 then D.rotDeriv τ k i i / D.lapse τ else 0) -
      ∑ f, lorentzSign .timeNegative f * (D.rot τ k f b * D.rot τ i f i -
        D.rot τ k f i * D.rot τ i f b + D.lam τ f i b * D.rot τ k i f))

/-- **The orthonormal frame** `E₀ = N⁻¹ ∂_τ`, `E₁ = a⁻¹ ∂_x`, `E₂ = b⁻¹ (∂_y + z ∂_x)`,
`E₃ = c⁻¹ ∂_z` of the metric, on the whole domain (the base point only fixes the chart of the
components). -/
def frame (y : D.domain) : (metric D).toLorentzMetric.OrthonormalFrame (univ : Set D.domain) :=
  orthonormalFrameOf (metric D) y D.frameField D.contDiffOn_frameField
    fun z _ p q => D.form_frameField z p q

variable {D}

theorem hasDerivAt_rot {τ : ℝ} (hτ : τ ∈ D.I) (p q r : Fin 4) :
    HasDerivAt (fun s => D.rot s p q r) (D.rotDeriv τ p q r) τ :=
  (((hasDerivAt_lam hτ p q r).fun_add (hasDerivAt_lam hτ q r p)).fun_sub
    (hasDerivAt_lam hτ r p q)).div_const 2

/-- The derivative of a rotation coefficient, a function of the time, along `v`. -/
theorem fderiv_rotationOf {z : E} (hz : z ∈ D.domain) (p q r : Fin 4) (v : E) :
    fderiv ℝ (rotationOf (fun p q r (y : E) => D.lam (y 0) p q r) p q r) z v =
      D.rotDeriv (z 0) p q r * v 0 := by
  have h := FLRW.hasFDerivAt_time (hasDerivAt_rot (time_mem hz) p q r)
  rw [show rotationOf (fun p q r (y : E) => D.lam (y 0) p q r) p q r =
    fun y : E => D.rot (y 0) p q r from rfl, h.fderiv]
  simp [smul_eq_mul]

/-- **The reduction of the Ricci tensor**: its components in the frame at a point of the domain
are `frameRicci` at the time of the point. -/
theorem ricci_frame (y : D.domain) (b k : Fin 4) :
    (metric D).toLorentzMetric.ricci y ((frame D y).field b y) ((frame D y).field k y) =
      D.frameRicci ((y : E) 0) b k := by
  have hΛ (p q r : Fin 4) : ContDiffOn ℝ ∞ (fun z : E => D.lam (z 0) p q r) D.domain :=
    contDiffOn_time (D.contDiffOn_lam p q r)
  have hcomm : ∀ z ∈ D.domain, ∀ p q r, (metric D).form z (D.frameField p z)
      (lieBracketOf (D.frameField q) (D.frameField r) z) = D.lam (z 0) p q r :=
    fun z hz p q r => commutator_frame hz p q r
  refine (ricci_orthonormalFrameOf (metric D) y (ξ := D.frameField) D.contDiffOn_frameField
    (fun z _ p q => D.form_frameField z p q) hΛ hcomm y b k).trans ?_
  rw [ricciOfFrame, frameRicci]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_rotationOf y.property, fderiv_rotationOf y.property, frameField_apply_zero,
    frameField_apply_zero]
  simp only [mul_ite, mul_zero, div_eq_mul_inv]
  rfl

/-- **The vacuum equations reduce to ordinary differential equations**: the Ricci tensor
vanishes on the domain if and only if `frameRicci τ b k = 0` for all `τ ∈ I`. -/
theorem ricci_eq_zero_iff :
    (∀ y : D.domain, (metric D).toLorentzMetric.ricci y = 0) ↔
      ∀ τ ∈ D.I, ∀ b k, D.frameRicci τ b k = 0 := by
  constructor
  · intro h τ hτ b k
    have h' := ricci_frame ⟨FLRW.timeAxis τ, timeAxis_mem hτ⟩ b k
    rw [h ⟨_, timeAxis_mem hτ⟩, zero_apply, zero_apply] at h'
    simpa using h'.symm
  · intro h y
    refine (frame D y).bilinear_ext (mem_univ y) fun b k => ?_
    rw [ricci_frame]
    exact h _ (time_mem y.property) b k

variable (D) in
/-- The diagonal frame components of the Ricci tensor in closed form:
`R₀₀ = (2(α'β' + α'γ' + β'γ') − (α'' + β'' + γ''))/N²`, `R₁₁ = (α'' + a⁴/2)/N²`,
`R₂₂ = (β'' − a⁴/2)/N²`, `R₃₃ = (γ'' − a⁴/2)/N²`. -/
def ricciDiag (τ : ℝ) : Fin 4 → ℝ :=
  ![(2 * (deriv D.α τ * deriv D.β τ + deriv D.α τ * deriv D.γ τ + deriv D.β τ * deriv D.γ τ) -
      (deriv (deriv D.α) τ + deriv (deriv D.β) τ + deriv (deriv D.γ) τ)) / D.lapse τ ^ 2,
    (deriv (deriv D.α) τ + D.a τ ^ 4 / 2) / D.lapse τ ^ 2,
    (deriv (deriv D.β) τ - D.a τ ^ 4 / 2) / D.lapse τ ^ 2,
    (deriv (deriv D.γ) τ - D.a τ ^ 4 / 2) / D.lapse τ ^ 2]

/-- The diagonal frame component `R₀₀`. -/
theorem frameRicci_zero_zero (τ : ℝ) : D.frameRicci τ 0 0 = D.ricciDiag τ 0 := by
  have ha := (D.a_pos τ).ne'
  have hb := (D.b_pos τ).ne'
  have hc := (D.c_pos τ).ne'
  simp [frameRicci, ricciDiag, Fin.sum_univ_four, rot, rotDeriv, lam, lamDeriv, wallSign, rate,
    rateDeriv, wall, wallDeriv, expansion, lapse, lorentzSign]
  field_simp
  ring

/-- The diagonal frame component `R₁₁`. -/
theorem frameRicci_one_one (τ : ℝ) : D.frameRicci τ 1 1 = D.ricciDiag τ 1 := by
  have ha := (D.a_pos τ).ne'
  have hb := (D.b_pos τ).ne'
  have hc := (D.c_pos τ).ne'
  simp [frameRicci, ricciDiag, Fin.sum_univ_four, rot, rotDeriv, lam, lamDeriv, wallSign, rate,
    rateDeriv, wall, wallDeriv, expansion, lapse, lorentzSign]
  field_simp
  ring

/-- The diagonal frame component `R₂₂`. -/
theorem frameRicci_two_two (τ : ℝ) : D.frameRicci τ 2 2 = D.ricciDiag τ 2 := by
  have ha := (D.a_pos τ).ne'
  have hb := (D.b_pos τ).ne'
  have hc := (D.c_pos τ).ne'
  simp [frameRicci, ricciDiag, Fin.sum_univ_four, rot, rotDeriv, lam, lamDeriv, wallSign, rate,
    rateDeriv, wall, wallDeriv, expansion, lapse, lorentzSign]
  field_simp
  ring

/-- The diagonal frame component `R₃₃`. -/
theorem frameRicci_three_three (τ : ℝ) : D.frameRicci τ 3 3 = D.ricciDiag τ 3 := by
  have ha := (D.a_pos τ).ne'
  have hb := (D.b_pos τ).ne'
  have hc := (D.c_pos τ).ne'
  simp [frameRicci, ricciDiag, Fin.sum_univ_four, rot, rotDeriv, lam, lamDeriv, wallSign, rate,
    rateDeriv, wall, wallDeriv, expansion, lapse, lorentzSign]
  field_simp
  ring

/-- The off-diagonal frame component `R_{01}` vanishes. -/
theorem frameRicci_zero_one (τ : ℝ) : D.frameRicci τ 0 1 = 0 := by
  simp [frameRicci, Fin.sum_univ_four, rot, rotDeriv, lam, lamDeriv, wallSign, rate,
    rateDeriv, wall, wallDeriv, expansion, lapse, lorentzSign]

/-- The off-diagonal frame component `R_{02}` vanishes. -/
theorem frameRicci_zero_two (τ : ℝ) : D.frameRicci τ 0 2 = 0 := by
  simp [frameRicci, Fin.sum_univ_four, rot, rotDeriv, lam, lamDeriv, wallSign, rate,
    rateDeriv, wall, wallDeriv, expansion, lapse, lorentzSign]

/-- The off-diagonal frame component `R_{03}` vanishes. -/
theorem frameRicci_zero_three (τ : ℝ) : D.frameRicci τ 0 3 = 0 := by
  simp [frameRicci, Fin.sum_univ_four, rot, rotDeriv, lam, lamDeriv, wallSign, rate,
    rateDeriv, wall, wallDeriv, expansion, lapse, lorentzSign]

/-- The off-diagonal frame component `R_{10}` vanishes. -/
theorem frameRicci_one_zero (τ : ℝ) : D.frameRicci τ 1 0 = 0 := by
  simp [frameRicci, Fin.sum_univ_four, rot, rotDeriv, lam, lamDeriv, wallSign, rate,
    rateDeriv, wall, wallDeriv, expansion, lapse, lorentzSign]

/-- The off-diagonal frame component `R_{12}` vanishes. -/
theorem frameRicci_one_two (τ : ℝ) : D.frameRicci τ 1 2 = 0 := by
  simp [frameRicci, Fin.sum_univ_four, rot, rotDeriv, lam, lamDeriv, wallSign, rate,
    rateDeriv, wall, wallDeriv, expansion, lapse, lorentzSign]

/-- The off-diagonal frame component `R_{13}` vanishes. -/
theorem frameRicci_one_three (τ : ℝ) : D.frameRicci τ 1 3 = 0 := by
  simp [frameRicci, Fin.sum_univ_four, rot, rotDeriv, lam, lamDeriv, wallSign, rate,
    rateDeriv, wall, wallDeriv, expansion, lapse, lorentzSign]

/-- The off-diagonal frame component `R_{20}` vanishes. -/
theorem frameRicci_two_zero (τ : ℝ) : D.frameRicci τ 2 0 = 0 := by
  simp [frameRicci, Fin.sum_univ_four, rot, rotDeriv, lam, lamDeriv, wallSign, rate,
    rateDeriv, wall, wallDeriv, expansion, lapse, lorentzSign]

/-- The off-diagonal frame component `R_{21}` vanishes. -/
theorem frameRicci_two_one (τ : ℝ) : D.frameRicci τ 2 1 = 0 := by
  simp [frameRicci, Fin.sum_univ_four, rot, rotDeriv, lam, lamDeriv, wallSign, rate,
    rateDeriv, wall, wallDeriv, expansion, lapse, lorentzSign]

/-- The off-diagonal frame component `R_{23}` vanishes. -/
theorem frameRicci_two_three (τ : ℝ) : D.frameRicci τ 2 3 = 0 := by
  simp [frameRicci, Fin.sum_univ_four, rot, rotDeriv, lam, lamDeriv, wallSign, rate,
    rateDeriv, wall, wallDeriv, expansion, lapse, lorentzSign]

/-- The off-diagonal frame component `R_{30}` vanishes. -/
theorem frameRicci_three_zero (τ : ℝ) : D.frameRicci τ 3 0 = 0 := by
  simp [frameRicci, Fin.sum_univ_four, rot, rotDeriv, lam, lamDeriv, wallSign, rate,
    rateDeriv, wall, wallDeriv, expansion, lapse, lorentzSign]

/-- The off-diagonal frame component `R_{31}` vanishes. -/
theorem frameRicci_three_one (τ : ℝ) : D.frameRicci τ 3 1 = 0 := by
  simp [frameRicci, Fin.sum_univ_four, rot, rotDeriv, lam, lamDeriv, wallSign, rate,
    rateDeriv, wall, wallDeriv, expansion, lapse, lorentzSign]

/-- The off-diagonal frame component `R_{32}` vanishes. -/
theorem frameRicci_three_two (τ : ℝ) : D.frameRicci τ 3 2 = 0 := by
  simp [frameRicci, Fin.sum_univ_four, rot, rotDeriv, lam, lamDeriv, wallSign, rate,
    rateDeriv, wall, wallDeriv, expansion, lapse, lorentzSign]

/-- **The Ricci tensor in the orthonormal frame** (Landau–Lifshitz, §118, the equations of type
IX with the walls of `b` and `c` removed): it is diagonal, with the components `ricciDiag`. -/
theorem frameRicci_eq (τ : ℝ) (b k : Fin 4) :
    D.frameRicci τ b k = if b = k then D.ricciDiag τ b else 0 := by
  fin_cases b <;> fin_cases k
  · exact frameRicci_zero_zero τ
  · exact frameRicci_zero_one τ
  · exact frameRicci_zero_two τ
  · exact frameRicci_zero_three τ
  · exact frameRicci_one_zero τ
  · exact frameRicci_one_one τ
  · exact frameRicci_one_two τ
  · exact frameRicci_one_three τ
  · exact frameRicci_two_zero τ
  · exact frameRicci_two_one τ
  · exact frameRicci_two_two τ
  · exact frameRicci_two_three τ
  · exact frameRicci_three_zero τ
  · exact frameRicci_three_one τ
  · exact frameRicci_three_two τ
  · exact frameRicci_three_three τ

variable (D) in
/-- **The vacuum condition**: the Ricci tensor vanishes on the whole domain. -/
def IsVacuum : Prop := ∀ y : D.domain, (metric D).toLorentzMetric.ricci y = 0

variable (D) in
/-- **The one-wall system** (Landau–Lifshitz, §118, with `α = ln a`, `β = ln b`, `γ = ln c` and
`dt = abc dτ`): `α'' = −a⁴/2`, `β'' = γ'' = a⁴/2`, with the first integral
`α'β' + α'γ' + β'γ' = a⁴/4`. These are the equations of type IX with only the wall of `a`. -/
def OneWall (τ : ℝ) : Prop :=
  deriv (deriv D.α) τ = -(D.a τ ^ 4 / 2) ∧ deriv (deriv D.β) τ = D.a τ ^ 4 / 2 ∧
    deriv (deriv D.γ) τ = D.a τ ^ 4 / 2 ∧
    deriv D.α τ * deriv D.β τ + deriv D.α τ * deriv D.γ τ + deriv D.β τ * deriv D.γ τ =
      D.a τ ^ 4 / 4

/-- At a time, the frame components of the Ricci tensor vanish exactly when the one-wall system
holds. -/
theorem frameRicci_eq_zero_iff (τ : ℝ) : (∀ b k, D.frameRicci τ b k = 0) ↔ D.OneWall τ := by
  have hN := pow_ne_zero 2 (D.lapse_pos τ).ne'
  simp only [frameRicci_eq]
  constructor
  · intro h
    have h0 := h 0 0
    have h1 := h 1 1
    have h2 := h 2 2
    have h3 := h 3 3
    simp only [ricciDiag, ite_true, Fin.isValue, Matrix.cons_val, div_eq_zero_iff, hN,
      or_false] at h0 h1 h2 h3
    refine ⟨by linear_combination h1, by linear_combination h2, by linear_combination h3, ?_⟩
    linear_combination h0 / 2 + h1 / 2 + h2 / 2 + h3 / 2
  · rintro ⟨h1, h2, h3, h4⟩ b k
    split_ifs
    · fin_cases b
      · simp only [ricciDiag, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, h1, h2, h3]
        rw [div_eq_zero_iff]
        left
        linear_combination 2 * h4
      · simp [ricciDiag, h1]
      · simp [ricciDiag, h2]
      · simp [ricciDiag, h3]
    · rfl

/-- **The vacuum equations of the type II model are the one-wall system**: the metric
`−(abc)² dτ² + a² (dx − z dy)² + b² dy² + c² dz²` is Ricci flat on its domain if and only if
`α'' = −a⁴/2`, `β'' = γ'' = a⁴/2` and `α'β' + α'γ' + β'γ' = a⁴/4` on `I` (Landau–Lifshitz,
§118). -/
theorem isVacuum_iff : D.IsVacuum ↔ ∀ τ ∈ D.I, D.OneWall τ := by
  rw [IsVacuum, ricci_eq_zero_iff]
  exact forall₂_congr fun τ _ => frameRicci_eq_zero_iff τ

/-- The co-ordinate Ricci tensor of a vacuum model vanishes on the domain. -/
theorem ricciOf_eq_zero_of_isVacuum (h : D.IsVacuum) {x : E} (hx : x ∈ D.domain) (j k : Fin 4) :
    ricciOf (metric D).coefficient x j k = 0 := by
  rw [← (metric D).toLorentzMetric_ricci_chartField ⟨x, hx⟩ ⟨x, hx⟩, h ⟨x, hx⟩]
  rfl

/-- A vacuum model solves the co-ordinate vacuum Einstein equations for every coupling. -/
theorem isEinstein_of_isVacuum (h : D.IsVacuum) (κ : ℝ) : (metric D).IsEinstein κ 0 0 := by
  intro z hz i k
  simp [einsteinOf, scalarOf, ricciOf_eq_zero_of_isVacuum h hz]

variable (D) in
/-- **The Kasner exponents of the model at the time `τ`**: the logarithmic rates
`p_k = (ln a_k)'/(ln abc)'`. In a Kasner epoch `a_k ∝ t^{p_k}` with `abc ∝ t`, so these are the
exponents of the epoch. -/
def exponents (τ : ℝ) (k : Fin 3) : ℝ := deriv (D.w k) τ / D.expansion τ

/-- The exponents of the model satisfy `Σ_k p_k = 1` where `(ln abc)' ≠ 0`. -/
theorem sum_exponents {τ : ℝ} (h : D.expansion τ ≠ 0) : ∑ k, D.exponents τ k = 1 := by
  simp only [exponents, Fin.sum_univ_three, w_zero, w_one, w_two]
  rw [← add_div, ← add_div, div_eq_one_iff_eq h]
  rfl

end Data

/-! ### The exact one-bounce solution -/

/-- `ln cosh(2uτ)`. -/
def logCosh (u τ : ℝ) : ℝ := Real.log (Real.cosh (2 * u * τ))

theorem contDiff_logCosh (u : ℝ) : ContDiff ℝ ∞ (logCosh u) :=
  (Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)).log fun _ => (Real.cosh_pos _).ne'

/-- `(ln cosh 2uτ)' = 2u tanh 2uτ`. -/
theorem hasDerivAt_logCosh (u τ : ℝ) :
    HasDerivAt (logCosh u) (2 * u * Real.tanh (2 * u * τ)) τ := by
  have h := (((hasDerivAt_id' τ).const_mul (2 * u)).cosh).log (Real.cosh_pos _).ne'
  refine h.congr_deriv ?_
  rw [Real.tanh_eq_sinh_div_cosh]
  ring

/-- `(tanh 2uτ)' = 2u/cosh² 2uτ`. -/
theorem hasDerivAt_tanh (u τ : ℝ) :
    HasDerivAt (fun s => Real.tanh (2 * u * s)) (2 * u / Real.cosh (2 * u * τ) ^ 2) τ := by
  have hc := (Real.cosh_pos (2 * u * τ)).ne'
  have h := (((hasDerivAt_id' τ).const_mul (2 * u)).sinh).fun_div
    (((hasDerivAt_id' τ).const_mul (2 * u)).cosh) hc
  have he : (fun s => Real.tanh (2 * u * s)) =
      fun s => Real.sinh (2 * u * s) / Real.cosh (2 * u * s) :=
    funext fun s => Real.tanh_eq_sinh_div_cosh _
  rw [he]
  refine h.congr_deriv ?_
  field_simp
  linear_combination u * Real.cosh_sq (2 * u * τ)

/-- `1 − tanh² x = 1/cosh² x`. -/
theorem one_sub_tanh_sq (x : ℝ) : 1 - Real.tanh x ^ 2 = 1 / Real.cosh x ^ 2 := by
  have hc := (Real.cosh_pos x).ne'
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  linear_combination Real.cosh_sq x

/-- **The exact one-bounce solution of type II** (Taub): for `u > 0`, the logarithms
`α = ½ ln(2u/cosh 2uτ)`, `β = ½ ln cosh 2uτ + τ`, `γ = ½ ln cosh 2uτ + u²τ`, that is
`a² = 2u/cosh 2uτ`, `b² = e^{2τ} cosh 2uτ`, `c² = e^{2u²τ} cosh 2uτ`, at all times. The rates are
`α' = −u tanh 2uτ`, `β' = 1 + u tanh 2uτ`, `γ' = u² + u tanh 2uτ`: the epoch `p(u)` as
`τ → +∞` and the epoch `p(u − 1)` with the first two exponents exchanged as `τ → −∞`
(`tendsto_exponents`). The rates are normalised by `α' + β' + γ' → 1 + u + u²` as `τ → +∞`. -/
def solution (u : ℝ) : Data where
  I := univ
  isOpen_I := isOpen_univ
  α τ := (Real.log (2 * u) - logCosh u τ) / 2
  β τ := logCosh u τ / 2 + τ
  γ τ := logCosh u τ / 2 + u ^ 2 * τ
  contDiffOn_α := ((contDiff_const.sub (contDiff_logCosh u)).div_const 2).contDiffOn
  contDiffOn_β := (((contDiff_logCosh u).div_const 2).add contDiff_id).contDiffOn
  contDiffOn_γ :=
    (((contDiff_logCosh u).div_const 2).add (contDiff_const.mul contDiff_id)).contDiffOn

variable {u : ℝ}

@[simp] theorem solution_I (u : ℝ) : (solution u).I = univ := rfl

theorem hasDerivAt_solution_α (u τ : ℝ) :
    HasDerivAt (solution u).α (-(u * Real.tanh (2 * u * τ))) τ :=
  (((hasDerivAt_logCosh u τ).const_sub (Real.log (2 * u))).div_const 2).congr_deriv (by ring)

theorem hasDerivAt_solution_β (u τ : ℝ) :
    HasDerivAt (solution u).β (u * Real.tanh (2 * u * τ) + 1) τ :=
  (((hasDerivAt_logCosh u τ).div_const 2).fun_add (hasDerivAt_id' τ)).congr_deriv (by ring)

theorem hasDerivAt_solution_γ (u τ : ℝ) :
    HasDerivAt (solution u).γ (u * Real.tanh (2 * u * τ) + u ^ 2) τ :=
  (((hasDerivAt_logCosh u τ).div_const 2).fun_add
    ((hasDerivAt_id' τ).const_mul (u ^ 2))).congr_deriv (by ring)

theorem deriv_solution_α (u : ℝ) :
    deriv (solution u).α = fun τ => -(u * Real.tanh (2 * u * τ)) :=
  funext fun τ => (hasDerivAt_solution_α u τ).deriv

theorem deriv_solution_β (u : ℝ) :
    deriv (solution u).β = fun τ => u * Real.tanh (2 * u * τ) + 1 :=
  funext fun τ => (hasDerivAt_solution_β u τ).deriv

theorem deriv_solution_γ (u : ℝ) :
    deriv (solution u).γ = fun τ => u * Real.tanh (2 * u * τ) + u ^ 2 :=
  funext fun τ => (hasDerivAt_solution_γ u τ).deriv

theorem deriv_deriv_solution_α (u τ : ℝ) :
    deriv (deriv (solution u).α) τ = -(2 * u ^ 2 / Real.cosh (2 * u * τ) ^ 2) := by
  rw [deriv_solution_α]
  exact (((hasDerivAt_tanh u τ).const_mul u).fun_neg.congr_deriv (by ring)).deriv

theorem deriv_deriv_solution_β (u τ : ℝ) :
    deriv (deriv (solution u).β) τ = 2 * u ^ 2 / Real.cosh (2 * u * τ) ^ 2 := by
  rw [deriv_solution_β]
  exact ((((hasDerivAt_tanh u τ).const_mul u).add_const 1).congr_deriv (by ring)).deriv

theorem deriv_deriv_solution_γ (u τ : ℝ) :
    deriv (deriv (solution u).γ) τ = 2 * u ^ 2 / Real.cosh (2 * u * τ) ^ 2 := by
  rw [deriv_solution_γ]
  exact ((((hasDerivAt_tanh u τ).const_mul u).add_const (u ^ 2)).congr_deriv (by ring)).deriv

/-- The wall term of the solution: `a⁴ = 4u²/cosh² 2uτ`. -/
theorem a_solution_pow_four (hu : 0 < u) (τ : ℝ) :
    (solution u).a τ ^ 4 = 4 * u ^ 2 / Real.cosh (2 * u * τ) ^ 2 := by
  have h2 : (solution u).a τ ^ 2 = 2 * u / Real.cosh (2 * u * τ) := by
    rw [sq, Data.a, ← Real.exp_add]
    change Real.exp ((Real.log (2 * u) - logCosh u τ) / 2 + (Real.log (2 * u) - logCosh u τ) / 2)
      = _
    rw [show (Real.log (2 * u) - logCosh u τ) / 2 + (Real.log (2 * u) - logCosh u τ) / 2 =
      Real.log (2 * u) - logCosh u τ by ring, Real.exp_sub, logCosh,
      Real.exp_log (by positivity), Real.exp_log (Real.cosh_pos _)]
  rw [show (solution u).a τ ^ 4 = ((solution u).a τ ^ 2) ^ 2 by ring, h2]
  ring

/-- **The one-bounce solution is a vacuum solution** of type II for every `u > 0`. -/
theorem isVacuum_solution (hu : 0 < u) : (solution u).IsVacuum := by
  refine Data.isVacuum_iff.mpr fun τ _ => ?_
  have hc := (Real.cosh_pos (2 * u * τ)).ne'
  have ha := a_solution_pow_four hu τ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [deriv_deriv_solution_α, ha]
    ring
  · rw [deriv_deriv_solution_β, ha]
    ring
  · rw [deriv_deriv_solution_γ, ha]
    ring
  · rw [deriv_solution_α, deriv_solution_β, deriv_solution_γ, ha]
    dsimp only
    linear_combination u ^ 2 * one_sub_tanh_sq (2 * u * τ)

/-- The one-bounce solution solves the co-ordinate vacuum Einstein equations. -/
theorem isEinstein_solution (hu : 0 < u) (κ : ℝ) : (solution u).metric.IsEinstein κ 0 0 :=
  Data.isEinstein_of_isVacuum (isVacuum_solution hu) κ

/-! ### The transition between the two Kasner epochs -/

/-- `(ln abc)' = u tanh 2uτ + (1 + u²)` for the solution. -/
theorem expansion_solution (u τ : ℝ) :
    (solution u).expansion τ = u * Real.tanh (2 * u * τ) + (1 + u ^ 2) := by
  simp only [Data.expansion, deriv_solution_α, deriv_solution_β, deriv_solution_γ]
  ring

/-- The exponents of the solution in closed form:
`(−u T, 1 + u T, u² + u T)/(1 + u² + u T)` with `T = tanh 2uτ`. -/
theorem exponents_solution (u τ : ℝ) (k : Fin 3) :
    (solution u).exponents τ k =
      ![-(u * Real.tanh (2 * u * τ)), u * Real.tanh (2 * u * τ) + 1,
        u * Real.tanh (2 * u * τ) + u ^ 2] k / (u * Real.tanh (2 * u * τ) + (1 + u ^ 2)) := by
  rw [Data.exponents, expansion_solution]
  fin_cases k <;> simp [deriv_solution_α, deriv_solution_β, deriv_solution_γ]

/-- `1 − tanh x ≤ 2 e^{−2x}`. -/
theorem one_sub_tanh_le (x : ℝ) : 1 - Real.tanh x ≤ 2 * Real.exp (-(2 * x)) := by
  have hc := Real.cosh_pos x
  rw [Real.tanh_eq_sinh_div_cosh, one_sub_div hc.ne', Real.cosh_sub_sinh, div_le_iff₀ hc,
    Real.cosh_eq]
  have h1 : Real.exp (-(2 * x)) * Real.exp x = Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (-(2 * x)) * Real.exp (-x) = Real.exp (-(3 * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : 2 * Real.exp (-(2 * x)) * ((Real.exp x + Real.exp (-x)) / 2) =
      Real.exp (-(2 * x)) * Real.exp x + Real.exp (-(2 * x)) * Real.exp (-x) := by ring
  rw [h3, h1, h2]
  linarith [Real.exp_pos (-(3 * x))]

/-- `1 + tanh x ≤ 2 e^{2x}`. -/
theorem one_add_tanh_le (x : ℝ) : 1 + Real.tanh x ≤ 2 * Real.exp (2 * x) := by
  have h := one_sub_tanh_le (-x)
  rwa [Real.tanh_neg, sub_neg_eq_add, show -(2 * -x) = 2 * x by ring] at h

/-- A difference of two quotients with a factored cross difference. -/
private theorem div_sub_div_of_eq {A B d₁ d₂ c e : ℝ} (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0)
    (h : A * d₂ - d₁ * B = c * e) : A / d₁ - B / d₂ = c * e / (d₁ * d₂) := by
  rw [div_sub_div _ _ h₁ h₂, h]

/-- The estimate of a difference `c e/(d₁ d₂)` with `|c| ≤ u(1 + u²)` and both denominators at
least `(1 + u²)/2`. -/
private theorem abs_div_le {u c d₁ d₂ e : ℝ} (hu : 0 < u) (hc : |c| ≤ u * (1 + u ^ 2)) (he : 0 ≤ e)
    (h₁ : (1 + u ^ 2) / 2 ≤ d₁) (h₂ : (1 + u ^ 2) / 2 ≤ d₂) :
    |c * e / (d₁ * d₂)| ≤ 4 * u / (1 + u ^ 2) * e := by
  have hq : 0 < (1 + u ^ 2) / 2 := by positivity
  have hd : 0 < d₁ * d₂ := mul_pos (hq.trans_le h₁) (hq.trans_le h₂)
  rw [abs_div, abs_mul, abs_of_nonneg he, abs_of_pos hd]
  calc |c| * e / (d₁ * d₂) ≤ u * (1 + u ^ 2) * e / ((1 + u ^ 2) / 2 * ((1 + u ^ 2) / 2)) :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hc he) (mul_pos hq hq)
          (mul_le_mul h₁ h₂ hq.le (hq.le.trans h₁))
    _ = 4 * u / (1 + u ^ 2) * e := by
        field_simp
        ring

/-- The exponents `p(u − 1)` in closed form, with `1 + (u − 1) + (u − 1)² = 1 − u + u²`. -/
theorem kasnerExponents_sub_one (u : ℝ) (k : Fin 3) :
    kasnerExponents (u - 1) k = ![-(u - 1), u, u * (u - 1)] k / (1 - u + u ^ 2) := by
  have h : 1 + (u - 1) + (u - 1) ^ 2 = 1 - u + u ^ 2 := by ring
  fin_cases k <;> simp only [kasnerExponents, Fin.isValue, Matrix.cons_val, Fin.zero_eta,
    Fin.mk_one, Fin.reduceFinMk, h] <;> ring

/-- **The epoch before the bounce, with an explicit rate**: for `u > 0` and every time `τ`,
`|p_k(τ) − p_k(u)| ≤ 8u/(1 + u²) e^{−4uτ}`. -/
theorem abs_exponents_sub_le_atTop (hu : 0 < u) (τ : ℝ) (k : Fin 3) :
    |(solution u).exponents τ k - kasnerExponents u k| ≤
      8 * u / (1 + u ^ 2) * Real.exp (-(4 * u * τ)) := by
  rw [exponents_solution]
  set T := Real.tanh (2 * u * τ) with hT
  obtain ⟨hTl, hTu⟩ := abs_lt.mp (Real.abs_tanh_lt_one (2 * u * τ))
  rw [← hT] at hTl hTu
  have hD : (1 + u ^ 2) / 2 ≤ u * T + (1 + u ^ 2) := by
    nlinarith [sq_nonneg (u - 1), mul_lt_mul_of_pos_left hTl hu]
  have hD1 : (1 + u ^ 2) / 2 ≤ 1 + u + u ^ 2 := by nlinarith
  have hq : 0 < (1 + u ^ 2) / 2 := by positivity
  have hDne := (hq.trans_le hD).ne'
  have hD1ne := (kasnerDenom_pos u).ne'
  have he : 0 ≤ 1 - T := by linarith
  have hrate : 1 - T ≤ 2 * Real.exp (-(4 * u * τ)) := by
    have h := one_sub_tanh_le (2 * u * τ)
    rwa [show -(2 * (2 * u * τ)) = -(4 * u * τ) by ring] at h
  have key (c : ℝ) (hc : |c| ≤ u * (1 + u ^ 2)) :
      |c * (1 - T) / ((u * T + (1 + u ^ 2)) * (1 + u + u ^ 2))| ≤
        8 * u / (1 + u ^ 2) * Real.exp (-(4 * u * τ)) := by
    refine (abs_div_le hu hc he hD hD1).trans ?_
    calc 4 * u / (1 + u ^ 2) * (1 - T) ≤ 4 * u / (1 + u ^ 2) * (2 * Real.exp (-(4 * u * τ))) :=
          mul_le_mul_of_nonneg_left hrate (by positivity)
      _ = 8 * u / (1 + u ^ 2) * Real.exp (-(4 * u * τ)) := by ring
  fin_cases k
  · simp only [kasnerExponents, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [div_sub_div_of_eq hDne hD1ne (c := u * (1 + u ^ 2)) (e := 1 - T) (by ring)]
    exact key _ (by rw [abs_of_pos (by positivity)])
  · simp only [kasnerExponents, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    rw [div_sub_div_of_eq hDne hD1ne (c := -u ^ 3) (e := 1 - T) (by ring)]
    exact key _ (by rw [abs_neg, abs_of_pos (by positivity)]; nlinarith)
  · simp only [kasnerExponents, Fin.reduceFinMk, Matrix.cons_val]
    rw [div_sub_div_of_eq hDne hD1ne (c := -u) (e := 1 - T) (by ring)]
    exact key _ (by rw [abs_neg, abs_of_pos hu]; nlinarith)

/-- **The epoch after the bounce, with an explicit rate**: for `u > 0` and every time `τ`,
`|p_k(τ) − q_k| ≤ 8u/(1 + u²) e^{4uτ}`, where `q = (p₂(u − 1), p₁(u − 1), p₃(u − 1))`. -/
theorem abs_exponents_sub_le_atBot (hu : 0 < u) (τ : ℝ) (k : Fin 3) :
    |(solution u).exponents τ k -
        ![kasnerExponents (u - 1) 1, kasnerExponents (u - 1) 0, kasnerExponents (u - 1) 2] k| ≤
      8 * u / (1 + u ^ 2) * Real.exp (4 * u * τ) := by
  rw [exponents_solution]
  set T := Real.tanh (2 * u * τ) with hT
  obtain ⟨hTl, hTu⟩ := abs_lt.mp (Real.abs_tanh_lt_one (2 * u * τ))
  rw [← hT] at hTl hTu
  have hD : (1 + u ^ 2) / 2 ≤ u * T + (1 + u ^ 2) := by
    nlinarith [sq_nonneg (u - 1), mul_lt_mul_of_pos_left hTl hu]
  have hD1 : (1 + u ^ 2) / 2 ≤ 1 - u + u ^ 2 := by nlinarith [sq_nonneg (u - 1)]
  have hq : 0 < (1 + u ^ 2) / 2 := by positivity
  have hDne := (hq.trans_le hD).ne'
  have hD1ne := (hq.trans_le hD1).ne'
  have he : 0 ≤ 1 + T := by linarith
  have hrate : 1 + T ≤ 2 * Real.exp (4 * u * τ) := by
    have h := one_add_tanh_le (2 * u * τ)
    rwa [show 2 * (2 * u * τ) = 4 * u * τ by ring] at h
  have key (c : ℝ) (hc : |c| ≤ u * (1 + u ^ 2)) :
      |c * (1 + T) / ((u * T + (1 + u ^ 2)) * (1 - u + u ^ 2))| ≤
        8 * u / (1 + u ^ 2) * Real.exp (4 * u * τ) := by
    refine (abs_div_le hu hc he hD hD1).trans ?_
    calc 4 * u / (1 + u ^ 2) * (1 + T) ≤ 4 * u / (1 + u ^ 2) * (2 * Real.exp (4 * u * τ)) :=
          mul_le_mul_of_nonneg_left hrate (by positivity)
      _ = 8 * u / (1 + u ^ 2) * Real.exp (4 * u * τ) := by ring
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, kasnerExponents_sub_one,
      Matrix.cons_val_one]
    rw [div_sub_div_of_eq hDne hD1ne (c := -(u * (1 + u ^ 2))) (e := 1 + T) (by ring)]
    exact key _ (by rw [abs_neg, abs_of_pos (by positivity)])
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
      kasnerExponents_sub_one]
    rw [div_sub_div_of_eq hDne hD1ne (c := u ^ 3) (e := 1 + T) (by ring)]
    exact key _ (by rw [abs_of_pos (by positivity)]; nlinarith)
  · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val, kasnerExponents_sub_one]
    rw [div_sub_div_of_eq hDne hD1ne (c := u) (e := 1 + T) (by ring)]
    exact key _ (by rw [abs_of_pos hu]; nlinarith)

/-- **The two epochs on the intervals `|τ| ≥ τ₀`** (Landau–Lifshitz, §118): for `u > 0`, the
exponents of the solution are within `8u/(1 + u²) e^{−4uτ₀}` of `p(u)` for `τ ≥ τ₀` and of
`(p₂(u − 1), p₁(u − 1), p₃(u − 1))` for `τ ≤ −τ₀`. -/
theorem abs_exponents_sub_le (hu : 0 < u) {τ₀ τ : ℝ} (k : Fin 3) :
    (τ₀ ≤ τ → |(solution u).exponents τ k - kasnerExponents u k| ≤
        8 * u / (1 + u ^ 2) * Real.exp (-(4 * u * τ₀))) ∧
      (τ ≤ -τ₀ → |(solution u).exponents τ k -
          ![kasnerExponents (u - 1) 1, kasnerExponents (u - 1) 0, kasnerExponents (u - 1) 2] k| ≤
        8 * u / (1 + u ^ 2) * Real.exp (-(4 * u * τ₀))) := by
  have hK : 0 ≤ 8 * u / (1 + u ^ 2) := by positivity
  refine ⟨fun h => (abs_exponents_sub_le_atTop hu τ k).trans ?_,
    fun h => (abs_exponents_sub_le_atBot hu τ k).trans ?_⟩
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hK
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hK

/-- The bound `8u/(1 + u²) e^{−4u s}` tends to `0` as `s → +∞`. -/
private theorem tendsto_bound (hu : 0 < u) :
    Tendsto (fun s : ℝ => 8 * u / (1 + u ^ 2) * Real.exp (-(4 * u * s))) atTop (𝓝 0) := by
  have h : Tendsto (fun s : ℝ => -(4 * u * s)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp (Tendsto.const_mul_atTop (by positivity) tendsto_id)
  simpa using (Real.tendsto_exp_atBot.comp h).const_mul (8 * u / (1 + u ^ 2))

/-- **As `τ → +∞` the exponents tend to the Kasner exponents `p(u)`**. -/
theorem tendsto_exponents_atTop (hu : 0 < u) :
    Tendsto (solution u).exponents atTop (𝓝 (kasnerExponents u)) := by
  refine tendsto_pi_nhds.mpr fun k => ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun τ => by rw [Real.norm_eq_abs]; exact abs_exponents_sub_le_atTop hu τ k) (tendsto_bound hu)

/-- **As `τ → −∞` the exponents tend to `p(u − 1)` with the first two exchanged**. -/
theorem tendsto_exponents_atBot (hu : 0 < u) :
    Tendsto (solution u).exponents atBot
      (𝓝 ![kasnerExponents (u - 1) 1, kasnerExponents (u - 1) 0, kasnerExponents (u - 1) 2]) := by
  refine tendsto_pi_nhds.mpr fun k => ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := (tendsto_bound hu).comp tendsto_neg_atBot_atTop
  refine squeeze_zero (fun _ => norm_nonneg _) (fun τ => ?_) h
  rw [Real.norm_eq_abs, Function.comp_apply, show -(4 * u * -τ) = 4 * u * τ by ring]
  exact abs_exponents_sub_le_atBot hu τ k

/-- **The BKL transition in the exact solution** (Landau–Lifshitz, §118): for `u > 0` the
exponents of the one-bounce solution tend to `p(u)` as `τ → +∞` and to
`(p₂(u − 1), p₁(u − 1), p₃(u − 1))` as `τ → −∞`. Toward the singularity (`τ` decreasing,
`dt = abc dτ`) the negative exponent `p₁(u)` of `a` becomes the positive `p₂(u − 1)` and the
negative exponent passes to `b`. -/
theorem tendsto_exponents (hu : 0 < u) :
    Tendsto (solution u).exponents atTop (𝓝 (kasnerExponents u)) ∧
      Tendsto (solution u).exponents atBot
        (𝓝 ![kasnerExponents (u - 1) 1, kasnerExponents (u - 1) 0, kasnerExponents (u - 1) 2]) :=
  ⟨tendsto_exponents_atTop hu, tendsto_exponents_atBot hu⟩

/-- The limit as `τ → −∞` is the transition law `bounce` applied to `p(u)`. -/
theorem tendsto_exponents_atBot_bounce (hu : 0 < u) :
    Tendsto (solution u).exponents atBot (𝓝 (bounce (kasnerExponents u))) := by
  rw [bounce_kasnerExponents]
  exact tendsto_exponents_atBot hu

/-- **A change of era in the exact solution**: for `u > 0`, `u ≠ 1`, the limit as `τ → −∞` is
`(p₃, p₁, p₂)(1/(u − 1))`; for `1 < u < 2` this is an ordered epoch of the new era with the
parameter `1/(u − 1) > 1`. -/
theorem tendsto_exponents_atBot_era (hu : 0 < u) (hu1 : u ≠ 1) :
    Tendsto (solution u).exponents atBot
      (𝓝 ![kasnerExponents (u - 1)⁻¹ 2, kasnerExponents (u - 1)⁻¹ 0,
        kasnerExponents (u - 1)⁻¹ 1]) := by
  rw [← bounce_kasnerExponents_era hu1]
  exact tendsto_exponents_atBot_bounce hu

end TypeII

end ProjectAinos.GeneralRelativity.BKL
