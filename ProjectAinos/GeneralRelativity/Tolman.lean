/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.SphericalAnsatz
public import ProjectAinos.GeneralRelativity.EddingtonFinkelstein
public import ProjectAinos.SmoothGeometry.Lorentzian.Synchronous
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateConservation
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Gravitational collapse of a dustlike sphere

Landau–Lifshitz, §103: the solution of Tolman (Lemaître–Tolman–Bondi) in the co-ordinates
`(τ, R, θ, φ) = (x 0, x 1, x 2, x 3)`, the signature `(−+++)` and `c = 1`. The dust is at rest in a
synchronous frame, `τ` is the proper time of the dust and `R` labels its shells. The data
(`Data`) are an open set `S` of `(τ, R)` and two functions `r(τ, R)`, `λ(τ, R)` smooth on `S`
with `r > 0` and `r′ = ∂r/∂R > 0` (no shell crossing); the metric is
`ds² = −dτ² + e^λ dR² + r² (dθ² + sin²θ dφ²)` on the domain `(τ, R) ∈ S`, `0 < θ < π`
(`metric`, L&L (103.1)); it is synchronous (`isSynchronous`). Partial derivatives are
`SphericalAnsatz.partialT` (`ṙ`) and `SphericalAnsatz.partialR` (`r′`).

* `christoffelOf_eq`, `ricciOf_eq`, `einsteinOf_eq`: the Christoffel symbols, the Ricci tensor and
  the Einstein tensor are the tables `christoffel`, `ricci`, `einstein`, computed by the library
  from the coefficients. With `f = e^{−λ} r′² − 1` (`energyOf`) and `F = r(ṙ² − f)` (`massOf`):
  `G₀₁ = (λ̇ r′ − 2ṙ′)/r`, `G₁₁ = −e^λ(2r r̈ + ṙ² − f)/r²` (`einstein_one_one_eq`) and
  `G₀₀ r² r′ = ∂_R F + r ṙ (λ̇ r′ − 2ṙ′)` (`einstein_zero_zero_mul`).
* `dustStress`: the dust `T_{ik} = ε u_i u_k`, `u = ∂_τ`; `isEinstein_at_iff`: the Einstein
  equations at a point are `G₀₀ = κε`, `G₀₁ = G₁₁ = G₂₂ = 0`.
* `Equations`: `e^λ = r′²/(1 + f(R))`, `ṙ² = f(R) + F(R)/r`, `r̈ = −F(R)/(2r²)` and
  `κε = F′(R)/(r′r²)` on `S` (L&L (103.3)–(103.5)). **`isEinstein_iff`**: when the slices
  `{τ | (τ, R) ∈ S}` are preconnected, `G_{ik} = κ T_{ik}` with the dust holds on the domain if and
  only if `Equations` holds for some `f`, `F`; then `f > −1` (`Equations.one_add_pos`). The
  converse direction `Equations.isEinstein` needs no connectedness: `G₂₂ = 0` follows from the
  derivatives of the other equations. `accel_of_energy`: the equation of motion follows from the
  first integral where `ṙ ≠ 0`; where `ṙ = 0` on an open set it is an independent condition.
  `satisfiesEinstein_iff` is the native form, and `divergence_dust_eq_zero` the conservation
  `∇^a T_{ab} = 0` from the contracted Bianchi identity; `Equations.hasDerivAt_restMass`: the rest
  mass `ε r′ r²` of every shell is constant in time.
* `Equations.density_nonneg_iff`: for `κ > 0`, `ε ≥ 0` if and only if `F′ ≥ 0`.
* The parabolic solution `f = 0` (L&L (103.8)): `parabolicRadius`,
  `r = (9F(τ₀ − τ)²/4)^{1/3} = (9F/4)^{1/3}(τ₀ − τ)^{2/3}` (`parabolicRadius_eq`), with the data
  `ParabolicData` (`F > 0`, `F′ ≥ 0`, `τ₀′ ≥ 0`, `F′ + τ₀′ > 0` on an open set of shells), the
  frame `ParabolicData.toData` with `e^λ = r′²` and the density `ParabolicData.density`;
  **`solution_parabolic`** proves `Equations`, and `isEinstein_parabolic` the Einstein equations.
  `tendsto_radius_zero`: `r → 0` as `τ → τ₀(R)⁻`.
* The elliptic (`f < 0`) and hyperbolic (`f > 0`) solutions (L&L (103.9), (103.10)) in the
  parameter `η`: `solution_elliptic`, `solution_hyperbolic` prove `ṙ² = f + F/r` and
  `r̈ = −F/(2r²)` for `ṙ = r_η/τ_η` along the curves `η ↦ (τ(η), r(η))`, and `tendsto_elliptic`,
  `tendsto_hyperbolic`, `ellipticTime_lt`, `hyperbolicTime_lt`: `(τ, r) → (τ₀, 0)` as `η → 0⁺`
  with `τ < τ₀`.
* The exterior: **`matching`**: at a falling shell with `f = 0` and `F = r_g > 0`, the map
  `eddingtonMap` (`v = τ + r − 2√(r_g r) + 2r_g log(1 + √(r/r_g))`) pulls the Schwarzschild metric
  in the Eddington–Finkelstein co-ordinates back to the metric of the frame, through the horizon;
  `matching_exterior`: if `f = 0` and `F = r_g` for all `R > R_b`, the shells `R > R_b` are the
  vacuum Schwarzschild field. **`lemaitre_eq`**: there a parabolic collapse with `τ₀(R) = R` is the
  Schwarzschild metric in the co-ordinates of Lemaître, `ds² = −dτ² + (r_g/r) dR² + r² dΩ²`
  (`lemaitreForm`, L&L (102.3)); `ParabolicData.isEinstein_lemaitre`: it is a vacuum solution.
* The instance `ParabolicData.dustBall`: `F = r_g σ(R/R_b)` with Mathlib's smooth transition `σ`
  and `τ₀(R) = R`; `dustBall_exterior`: the ball is a smooth dust solution whose exterior `R > R_b`
  is the Schwarzschild field.

The scope: the domain before shell crossing (`r′ > 0`), the chart `0 < θ < π` of the sphere, the
three signs of `f` (the elliptic and hyperbolic solutions in the parametric form); shell crossing,
the regularity at the centre and the global structure are not treated.
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap Set TopologicalSpace Filter
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.Tolman

open SmoothGeometry CoordinateMetric
open SphericalAnsatz (partialT partialR hasDerivAt_partialT hasDerivAt_partialR
  contDiffOn_partialT contDiffOn_partialR partialR_partialT hasFDerivAt_timeRadius
  hasFDerivAt_div gamma233 gamma323 fderiv_gamma233 sum_four)

local notation "E" => MinkowskiModel 3

/-! ### The data -/

/-- **The data of the comoving synchronous frame of a dust sphere** (Landau–Lifshitz, (103.1)):
an open set `S` of co-ordinates `(τ, R)` and two functions `r(τ, R)`, `λ(τ, R)` smooth on `S`,
with `r > 0` and `r′ = ∂r/∂R > 0` on `S`; the condition `r′ > 0` excludes shell crossing. -/
structure Data where
  /-- The open set of co-ordinates `(τ, R)`. -/
  S : Set (ℝ × ℝ)
  /-- The radius `r(τ, R)` of the shell `R` at the proper time `τ`. -/
  r : ℝ → ℝ → ℝ
  /-- The exponent `λ(τ, R)`, with `g_{RR} = e^λ`. -/
  lam : ℝ → ℝ → ℝ
  /-- The set of co-ordinates is open. -/
  isOpen_S : IsOpen S
  /-- `r` is smooth on `S`. -/
  contDiffOn_r : ContDiffOn ℝ ∞ (Function.uncurry r) S
  /-- `λ` is smooth on `S`. -/
  contDiffOn_lam : ContDiffOn ℝ ∞ (Function.uncurry lam) S
  /-- The radius is positive on `S`. -/
  r_pos : ∀ p ∈ S, 0 < r p.1 p.2
  /-- No shell crossing: `r′ > 0` on `S`. -/
  partialR_r_pos : ∀ p ∈ S, 0 < partialR r p.1 p.2

variable (D : Data)

/-- The domain `(τ, R) ∈ S`, `0 < θ < π` in the co-ordinates `(τ, R, θ, φ)`. -/
def domain : Opens E :=
  ⟨{x | (x 0, x 1) ∈ D.S ∧ 0 < x 2 ∧ x 2 < Real.pi},
    (D.isOpen_S.preimage ((continuous_apply 0).prodMk (continuous_apply 1))).inter
      ((isOpen_lt continuous_const (continuous_apply 2)).inter
        (isOpen_lt (continuous_apply 2) continuous_const))⟩

variable {D} {x : E}

/-- The co-ordinates `(τ, R)` of a point of the domain lie in `S`. -/
theorem mem_S (hx : x ∈ domain D) : (x 0, x 1) ∈ D.S := hx.1

/-- The radius is positive on the domain. -/
theorem r_pos_of_mem (hx : x ∈ domain D) : 0 < D.r (x 0) (x 1) := D.r_pos _ hx.1

/-- `r′ > 0` on the domain. -/
theorem partialR_r_pos_of_mem (hx : x ∈ domain D) : 0 < partialR D.r (x 0) (x 1) :=
  D.partialR_r_pos _ hx.1

/-- `sin θ > 0` on the domain. -/
theorem sin_pos_of_mem (hx : x ∈ domain D) : 0 < Real.sin (x 2) :=
  Real.sin_pos_of_pos_of_lt_pi hx.2.1 hx.2.2

/-- The point `(τ, R, π/2, 0)` of the equator. -/
def point (τ R : ℝ) : E := ![τ, R, Real.pi / 2, 0]

/-- The point `(τ, R, π/2, 0)` lies in the domain for every `(τ, R) ∈ S`. -/
theorem point_mem {τ R : ℝ} (h : (τ, R) ∈ D.S) : point τ R ∈ domain D :=
  ⟨by simpa [point] using h, by simp [point, Real.pi_pos], by simp [point]; linarith [Real.pi_pos]⟩

@[simp] theorem point_zero (τ R : ℝ) : point τ R 0 = τ := rfl

@[simp] theorem point_one (τ R : ℝ) : point τ R 1 = R := rfl

/-! ### Smooth functions of `(τ, R)` -/

/-- `∂f/∂τ` is smooth on `S` when `f` is. -/
theorem contDiffOn_dt {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) D.S) :
    ContDiffOn ℝ ∞ (Function.uncurry (partialT f)) D.S :=
  contDiffOn_partialT D.isOpen_S hf

/-- `∂f/∂R` is smooth on `S` when `f` is. -/
theorem contDiffOn_dR {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) D.S) :
    ContDiffOn ℝ ∞ (Function.uncurry (partialR f)) D.S :=
  contDiffOn_partialR D.isOpen_S hf

/-- A smooth function of `(τ, R)` on `S` is smooth on the domain. -/
theorem contDiffOn_lift {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) D.S) :
    ContDiffOn ℝ ∞ (fun z : E => f (z 0) (z 1)) (domain D) := by
  have hπ : ContDiff ℝ ∞ fun z : E => ((z 0, z 1) : ℝ × ℝ) :=
    (contDiff_apply ℝ (fun _ => ℝ) 0).prodMk (contDiff_apply ℝ (fun _ => ℝ) 1)
  exact hf.comp hπ.contDiffOn fun z hz => mem_S hz

/-- The derivative `∂_τ f v⁰ + ∂_R f v¹` of a function of `(τ, R)` along `v`. -/
def along (f : ℝ → ℝ → ℝ) (x v : E) : ℝ :=
  partialT f (x 0) (x 1) * v 0 + partialR f (x 0) (x 1) * v 1

/-- The chain rule for a smooth function of `(τ, R)` at a point of the domain. -/
theorem hasFDerivAt_lift {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) D.S)
    (hx : x ∈ domain D) :
    HasFDerivAt (fun z : E => f (z 0) (z 1))
      (partialT f (x 0) (x 1) • (proj 0 : E →L[ℝ] ℝ) +
        partialR f (x 0) (x 1) • (proj 1 : E →L[ℝ] ℝ)) x :=
  hasFDerivAt_timeRadius D.isOpen_S hf (mem_S hx)

/-- The derivative of a smooth function of `(τ, R)` along `v`. -/
theorem fderiv_lift {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) D.S)
    (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (fun z : E => f (z 0) (z 1)) x v = along f x v := by
  rw [(hasFDerivAt_lift hf hx).fderiv]
  simp [along]

/-- The mixed partial derivatives commute on `S`: `∂_τ ∂_R f = ∂_R ∂_τ f`. -/
theorem partialT_partialR {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) D.S)
    {τ R : ℝ} (h : (τ, R) ∈ D.S) : partialT (partialR f) τ R = partialR (partialT f) τ R :=
  (partialR_partialT D.isOpen_S hf h).symm

/-! ### The metric -/

variable (D) in
/-- The diagonal coefficients `(−1, e^λ, r², r² sin²θ)`. -/
def coefficients (x : E) : Fin 4 → ℝ :=
  ![-1, Real.exp (D.lam (x 0) (x 1)), D.r (x 0) (x 1) ^ 2,
    D.r (x 0) (x 1) ^ 2 * Real.sin (x 2) ^ 2]

/-- The coefficients are smooth on the domain. -/
theorem contDiffOn_coefficients (i : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => coefficients D x i) (domain D) := by
  have hθ : ContDiff ℝ ∞ fun x : E => x 2 := contDiff_apply ℝ (fun _ => ℝ) 2
  fin_cases i
  · exact contDiffOn_const
  · exact (contDiffOn_lift D.contDiffOn_lam).exp
  · exact (contDiffOn_lift D.contDiffOn_r).pow 2
  · exact ((contDiffOn_lift D.contDiffOn_r).pow 2).mul (hθ.sin.pow 2).contDiffOn

variable (D) in
/-- **The metric of the comoving frame of the dust** (Landau–Lifshitz, (103.1)),
`ds² = −dτ² + e^{λ(τ,R)} dR² + r(τ, R)² (dθ² + sin²θ dφ²)` on the domain. -/
def metric : CoordinateMetric .timeNegative 3 (domain D) :=
  ofDiagonal (coefficients D) contDiffOn_coefficients
    (fun x _ => by
      simp only [coefficients, LorentzConvention.timeSign_timeNegative, Matrix.cons_val_zero]
      norm_num)
    (fun x hx α => by
      fin_cases α
      · simp [coefficients, Real.exp_pos]
      · simpa [coefficients] using pow_pos (r_pos_of_mem hx) 2
      · simpa [coefficients] using
          mul_pos (pow_pos (r_pos_of_mem hx) 2) (pow_pos (sin_pos_of_mem hx) 2))

/-- The matrix of coefficients of the metric is `diag(−1, e^λ, r², r² sin²θ)`. -/
theorem coefficient_metric (y : E) :
    (metric D).coefficient y = Matrix.diagonal (coefficients D y) :=
  coefficient_ofDiagonal _ _ _ _ y

/-- The form of the metric: `g(v, w) = −v⁰w⁰ + e^λ v¹w¹ + r² v²w² + r² sin²θ v³w³`. -/
theorem metric_form_apply (y v w : E) :
    (metric D).form y v w = -(v 0 * w 0) + Real.exp (D.lam (y 0) (y 1)) * (v 1 * w 1) +
      D.r (y 0) (y 1) ^ 2 * (v 2 * w 2) +
        D.r (y 0) (y 1) ^ 2 * Real.sin (y 2) ^ 2 * (v 3 * w 3) := by
  simp only [metric, ofDiagonal_form, diagonalForm_apply, sum_four, coefficients]
  simp
  ring

/-- **The frame is synchronous**: `g₀₀ = −1` and `g₀α = 0` (Landau–Lifshitz, §97). -/
theorem isSynchronous : (metric D).IsSynchronous := by
  intro z _
  refine ⟨?_, fun α => ?_⟩
  · rw [coefficient_metric, Matrix.diagonal_apply_eq]
    rfl
  · rw [coefficient_metric, Matrix.diagonal_apply_ne _ (Fin.succ_ne_zero α).symm]

/-- No coefficient vanishes on the domain. -/
theorem coefficients_ne_zero (hx : x ∈ domain D) (i : Fin 4) : coefficients D x i ≠ 0 := by
  fin_cases i
  · simp [coefficients]
  · simp [coefficients, Real.exp_ne_zero]
  · simpa [coefficients] using (r_pos_of_mem hx).ne'
  · simpa [coefficients] using ⟨(r_pos_of_mem hx).ne', (sin_pos_of_mem hx).ne'⟩

/-! ### The derivatives of the coefficients -/

/-- The derivatives of the four coefficients along a vector `v`. -/
theorem fderiv_coefficients (hx : x ∈ domain D) (k : Fin 4) (v : E) :
    fderiv ℝ (fun z => coefficients D z k) x v =
      ![0, Real.exp (D.lam (x 0) (x 1)) * along D.lam x v,
        2 * D.r (x 0) (x 1) * along D.r x v,
        2 * D.r (x 0) (x 1) * Real.sin (x 2) ^ 2 * along D.r x v +
          D.r (x 0) (x 1) ^ 2 * (2 * Real.sin (x 2) * Real.cos (x 2)) * v 2] k := by
  have hr := hasFDerivAt_lift D.contDiffOn_r hx
  have hl := hasFDerivAt_lift D.contDiffOn_lam hx
  fin_cases k
  · simp [coefficients]
  · simp only [coefficients, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [hl.exp.fderiv]
    simp [along]
    ring
  · simp only [coefficients, Fin.reduceFinMk, Matrix.cons_val]
    rw [(hr.pow 2).fderiv]
    simp [along]
    ring
  · simp only [coefficients, Fin.reduceFinMk, Matrix.cons_val]
    rw [((hr.pow 2).fun_mul ((hasFDerivAt_apply 2 x).sin.pow 2)).fderiv]
    simp [along]
    ring

/-! ### The Christoffel symbols -/

variable (D) in
/-- `Γ⁰₁₁ = λ̇ e^λ/2`. -/
def gamma011 (x : E) : ℝ := partialT D.lam (x 0) (x 1) * Real.exp (D.lam (x 0) (x 1)) / 2

variable (D) in
/-- `Γ⁰₂₂ = r ṙ`. -/
def gamma022 (x : E) : ℝ := D.r (x 0) (x 1) * partialT D.r (x 0) (x 1)

variable (D) in
/-- `Γ⁰₃₃ = r ṙ sin²θ`. -/
def gamma033 (x : E) : ℝ := D.r (x 0) (x 1) * partialT D.r (x 0) (x 1) * Real.sin (x 2) ^ 2

variable (D) in
/-- `Γ¹₀₁ = λ̇/2`. -/
def gamma101 (x : E) : ℝ := partialT D.lam (x 0) (x 1) / 2

variable (D) in
/-- `Γ¹₁₁ = λ′/2`. -/
def gamma111 (x : E) : ℝ := partialR D.lam (x 0) (x 1) / 2

variable (D) in
/-- `Γ¹₂₂ = −r r′ e^{−λ}`. -/
def gamma122 (x : E) : ℝ :=
  -(D.r (x 0) (x 1) * partialR D.r (x 0) (x 1)) / Real.exp (D.lam (x 0) (x 1))

variable (D) in
/-- `Γ¹₃₃ = −r r′ sin²θ e^{−λ}`. -/
def gamma133 (x : E) : ℝ :=
  -(D.r (x 0) (x 1) * partialR D.r (x 0) (x 1)) * Real.sin (x 2) ^ 2 /
    Real.exp (D.lam (x 0) (x 1))

variable (D) in
/-- `Γ²₀₂ = Γ³₀₃ = ṙ/r`. -/
def gamma202 (x : E) : ℝ := partialT D.r (x 0) (x 1) / D.r (x 0) (x 1)

variable (D) in
/-- `Γ²₁₂ = Γ³₁₃ = r′/r`. -/
def gamma212 (x : E) : ℝ := partialR D.r (x 0) (x 1) / D.r (x 0) (x 1)

variable (D) in
/-- **The Christoffel symbols of the comoving frame**: the table `Γ^k_{ij}`, indexed
`christoffel D x k i j`, with the nonzero entries `Γ⁰₁₁ = λ̇ e^λ/2`, `Γ⁰₂₂ = r ṙ`,
`Γ⁰₃₃ = r ṙ sin²θ`, `Γ¹₀₁ = λ̇/2`, `Γ¹₁₁ = λ′/2`, `Γ¹₂₂ = −r r′ e^{−λ}`,
`Γ¹₃₃ = −r r′ sin²θ e^{−λ}`, `Γ²₀₂ = Γ³₀₃ = ṙ/r`, `Γ²₁₂ = Γ³₁₃ = r′/r`, `Γ²₃₃ = −sin θ cos θ`,
`Γ³₂₃ = cot θ` and their transposes in the lower indices. -/
def christoffel (x : E) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![![![0, 0, 0, 0], ![0, gamma011 D x, 0, 0], ![0, 0, gamma022 D x, 0],
      ![0, 0, 0, gamma033 D x]],
    ![![0, gamma101 D x, 0, 0], ![gamma101 D x, gamma111 D x, 0, 0],
      ![0, 0, gamma122 D x, 0], ![0, 0, 0, gamma133 D x]],
    ![![0, 0, gamma202 D x, 0], ![0, 0, gamma212 D x, 0], ![gamma202 D x, gamma212 D x, 0, 0],
      ![0, 0, 0, gamma233 x]],
    ![![0, 0, 0, gamma202 D x], ![0, 0, 0, gamma212 D x], ![0, 0, 0, gamma323 x],
      ![gamma202 D x, gamma212 D x, gamma323 x, 0]]]

/-- **The table is the table of Christoffel symbols** of the metric on its domain. -/
theorem christoffelOf_eq (hx : x ∈ domain D) (k i j : Fin 4) :
    christoffelOf (metric D).coefficient x k i j = christoffel D x k i j := by
  have he := (Real.exp_pos (D.lam (x 0) (x 1))).ne'
  have hr := (r_pos_of_mem hx).ne'
  have hs := (sin_pos_of_mem hx).ne'
  rw [metric, christoffelOf_ofDiagonal _ _ _ _ x (coefficients_ne_zero hx)]
  simp only [fderiv_coefficients hx]
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [christoffel, gamma011, gamma022, gamma033, gamma101, gamma111, gamma122, gamma133,
      gamma202, gamma212, gamma233, gamma323, coefficients, along] <;>
    field_simp

/-- The table agrees with the Christoffel symbols near every point of the domain. -/
theorem eventually_christoffelOf_eq (hx : x ∈ domain D) :
    ∀ᶠ z in 𝓝 x, ∀ k i j, christoffelOf (metric D).coefficient z k i j = christoffel D z k i j := by
  filter_upwards [(domain D).isOpen.mem_nhds hx] with z hz using christoffelOf_eq hz


/-! ### Derivatives of the Christoffel symbols -/

/-- The derivative of `Γ⁰₁₁ = λ̇ e^λ/2` along `v`. -/
theorem fderiv_gamma011 (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (gamma011 D) x v =
      (along (partialT D.lam) x v * Real.exp (D.lam (x 0) (x 1)) +
        partialT D.lam (x 0) (x 1) * Real.exp (D.lam (x 0) (x 1)) * along D.lam x v) / 2 := by
  rw [show gamma011 D = fun z => partialT D.lam (z 0) (z 1) * Real.exp (D.lam (z 0) (z 1)) / 2
    from rfl, (hasFDerivAt_div ((hasFDerivAt_lift (contDiffOn_dt D.contDiffOn_lam) hx).fun_mul
      (hasFDerivAt_lift D.contDiffOn_lam hx).exp) (hasFDerivAt_const (2 : ℝ) x)
      two_ne_zero).fderiv]
  simp [along]
  ring

/-- The derivative of `Γ⁰₂₂ = r ṙ` along `v`. -/
theorem fderiv_gamma022 (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (gamma022 D) x v =
      along D.r x v * partialT D.r (x 0) (x 1) + D.r (x 0) (x 1) * along (partialT D.r) x v := by
  rw [show gamma022 D = fun z => D.r (z 0) (z 1) * partialT D.r (z 0) (z 1) from rfl,
    ((hasFDerivAt_lift D.contDiffOn_r hx).fun_mul
      (hasFDerivAt_lift (contDiffOn_dt D.contDiffOn_r) hx)).fderiv]
  simp [along]
  ring

/-- The derivative of `Γ⁰₃₃ = r ṙ sin²θ` along `v`. -/
theorem fderiv_gamma033 (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (gamma033 D) x v =
      (along D.r x v * partialT D.r (x 0) (x 1) + D.r (x 0) (x 1) * along (partialT D.r) x v) *
          Real.sin (x 2) ^ 2 +
        D.r (x 0) (x 1) * partialT D.r (x 0) (x 1) *
          (2 * Real.sin (x 2) * Real.cos (x 2) * v 2) := by
  rw [show gamma033 D = fun z => D.r (z 0) (z 1) * partialT D.r (z 0) (z 1) * Real.sin (z 2) ^ 2
    from rfl, (((hasFDerivAt_lift D.contDiffOn_r hx).fun_mul
      (hasFDerivAt_lift (contDiffOn_dt D.contDiffOn_r) hx)).fun_mul
        ((hasFDerivAt_apply 2 x).sin.pow 2)).fderiv]
  simp [along]
  ring

/-- The derivative of `Γ¹₀₁ = λ̇/2` along `v`. -/
theorem fderiv_gamma101 (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (gamma101 D) x v = along (partialT D.lam) x v / 2 := by
  rw [show gamma101 D = fun z => partialT D.lam (z 0) (z 1) / 2 from rfl,
    (hasFDerivAt_div (hasFDerivAt_lift (contDiffOn_dt D.contDiffOn_lam) hx)
      (hasFDerivAt_const (2 : ℝ) x) two_ne_zero).fderiv]
  simp [along]
  ring

/-- The derivative of `Γ¹₁₁ = λ′/2` along `v`. -/
theorem fderiv_gamma111 (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (gamma111 D) x v = along (partialR D.lam) x v / 2 := by
  rw [show gamma111 D = fun z => partialR D.lam (z 0) (z 1) / 2 from rfl,
    (hasFDerivAt_div (hasFDerivAt_lift (contDiffOn_dR D.contDiffOn_lam) hx)
      (hasFDerivAt_const (2 : ℝ) x) two_ne_zero).fderiv]
  simp [along]
  ring

/-- The derivative of `Γ¹₂₂ = −r r′ e^{−λ}` along `v`. -/
theorem fderiv_gamma122 (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (gamma122 D) x v =
      (-(along D.r x v * partialR D.r (x 0) (x 1) + D.r (x 0) (x 1) * along (partialR D.r) x v) +
        D.r (x 0) (x 1) * partialR D.r (x 0) (x 1) * along D.lam x v) /
        Real.exp (D.lam (x 0) (x 1)) := by
  have he := (Real.exp_pos (D.lam (x 0) (x 1))).ne'
  rw [show gamma122 D = fun z => -(D.r (z 0) (z 1) * partialR D.r (z 0) (z 1)) /
      Real.exp (D.lam (z 0) (z 1)) from rfl,
    (hasFDerivAt_div ((hasFDerivAt_lift D.contDiffOn_r hx).fun_mul
      (hasFDerivAt_lift (contDiffOn_dR D.contDiffOn_r) hx)).fun_neg
      (hasFDerivAt_lift D.contDiffOn_lam hx).exp he).fderiv]
  simp [along]
  field_simp
  ring

/-- The derivative of `Γ¹₃₃ = −r r′ sin²θ e^{−λ}` along `v`. -/
theorem fderiv_gamma133 (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (gamma133 D) x v =
      (-(along D.r x v * partialR D.r (x 0) (x 1) + D.r (x 0) (x 1) * along (partialR D.r) x v) *
          Real.sin (x 2) ^ 2 -
        D.r (x 0) (x 1) * partialR D.r (x 0) (x 1) *
          (2 * Real.sin (x 2) * Real.cos (x 2) * v 2) +
        D.r (x 0) (x 1) * partialR D.r (x 0) (x 1) * Real.sin (x 2) ^ 2 * along D.lam x v) /
        Real.exp (D.lam (x 0) (x 1)) := by
  have he := (Real.exp_pos (D.lam (x 0) (x 1))).ne'
  rw [show gamma133 D = fun z => -(D.r (z 0) (z 1) * partialR D.r (z 0) (z 1)) *
      Real.sin (z 2) ^ 2 / Real.exp (D.lam (z 0) (z 1)) from rfl,
    (hasFDerivAt_div (((hasFDerivAt_lift D.contDiffOn_r hx).fun_mul
      (hasFDerivAt_lift (contDiffOn_dR D.contDiffOn_r) hx)).fun_neg.fun_mul
        ((hasFDerivAt_apply 2 x).sin.pow 2))
      (hasFDerivAt_lift D.contDiffOn_lam hx).exp he).fderiv]
  simp [along]
  field_simp
  ring

/-- The derivative of `Γ²₀₂ = ṙ/r` along `v`. -/
theorem fderiv_gamma202 (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (gamma202 D) x v =
      (along (partialT D.r) x v * D.r (x 0) (x 1) - partialT D.r (x 0) (x 1) * along D.r x v) /
        D.r (x 0) (x 1) ^ 2 := by
  have hr := (r_pos_of_mem hx).ne'
  rw [show gamma202 D = fun z => partialT D.r (z 0) (z 1) / D.r (z 0) (z 1) from rfl,
    (hasFDerivAt_div (hasFDerivAt_lift (contDiffOn_dt D.contDiffOn_r) hx)
      (hasFDerivAt_lift D.contDiffOn_r hx) hr).fderiv]
  simp [along]
  field_simp

/-- The derivative of `Γ²₁₂ = r′/r` along `v`. -/
theorem fderiv_gamma212 (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (gamma212 D) x v =
      (along (partialR D.r) x v * D.r (x 0) (x 1) - partialR D.r (x 0) (x 1) * along D.r x v) /
        D.r (x 0) (x 1) ^ 2 := by
  have hr := (r_pos_of_mem hx).ne'
  rw [show gamma212 D = fun z => partialR D.r (z 0) (z 1) / D.r (z 0) (z 1) from rfl,
    (hasFDerivAt_div (hasFDerivAt_lift (contDiffOn_dR D.contDiffOn_r) hx)
      (hasFDerivAt_lift D.contDiffOn_r hx) hr).fderiv]
  simp [along]
  field_simp

/-- The derivative of `Γ³₂₃ = cot θ` along `v` is `−v²/sin²θ`. -/
theorem fderiv_gamma323 (hx : x ∈ domain D) (v : E) :
    fderiv ℝ gamma323 x v = -v 2 / Real.sin (x 2) ^ 2 := by
  have hs := (sin_pos_of_mem hx).ne'
  rw [show gamma323 = fun z => Real.cos (z 2) / Real.sin (z 2) from rfl,
    (hasFDerivAt_div (hasFDerivAt_apply 2 x).cos (hasFDerivAt_apply 2 x).sin hs).fderiv]
  simp only [sub_apply, smul_apply, proj_apply, smul_eq_mul]
  field_simp
  linear_combination -v 2 * Real.sin_sq_add_cos_sq (x 2)

/-! ### The Ricci tensor -/

variable (D) in
/-- The table of the Ricci tensor of the comoving frame: `R₀₀ = −λ̇²/4 − λ̈/2 − 2r̈/r`,
`R₀₁ = R₁₀ = (λ̇ r′ − 2ṙ′)/r`, `R₁₁ = e^λ(λ̇²/4 + λ̈/2 + λ̇ṙ/r) + (λ′r′ − 2r″)/r`,
`R₂₂ = rλ̇ṙ/2 + r r̈ + e^{−λ}(r λ′ r′/2 − r r″ − r′²) + ṙ² + 1` and `R₃₃ = sin²θ R₂₂`; the other
components vanish. Here `ṙ′ = ∂_R ∂_τ r`. -/
def ricci (x : E) : Fin 4 → Fin 4 → ℝ :=
  ![![-(partialT D.lam (x 0) (x 1) ^ 2) / 4 - partialT (partialT D.lam) (x 0) (x 1) / 2 -
        2 * partialT (partialT D.r) (x 0) (x 1) / D.r (x 0) (x 1),
      (partialT D.lam (x 0) (x 1) * partialR D.r (x 0) (x 1) -
        2 * partialR (partialT D.r) (x 0) (x 1)) / D.r (x 0) (x 1), 0, 0],
    ![(partialT D.lam (x 0) (x 1) * partialR D.r (x 0) (x 1) -
        2 * partialR (partialT D.r) (x 0) (x 1)) / D.r (x 0) (x 1),
      Real.exp (D.lam (x 0) (x 1)) * (partialT D.lam (x 0) (x 1) ^ 2 / 4 +
          partialT (partialT D.lam) (x 0) (x 1) / 2 +
          partialT D.lam (x 0) (x 1) * partialT D.r (x 0) (x 1) / D.r (x 0) (x 1)) +
        (partialR D.lam (x 0) (x 1) * partialR D.r (x 0) (x 1) -
          2 * partialR (partialR D.r) (x 0) (x 1)) / D.r (x 0) (x 1), 0, 0],
    ![0, 0, D.r (x 0) (x 1) * partialT D.lam (x 0) (x 1) * partialT D.r (x 0) (x 1) / 2 +
        D.r (x 0) (x 1) * partialT (partialT D.r) (x 0) (x 1) +
        (D.r (x 0) (x 1) * partialR D.lam (x 0) (x 1) * partialR D.r (x 0) (x 1) / 2 -
          D.r (x 0) (x 1) * partialR (partialR D.r) (x 0) (x 1) -
          partialR D.r (x 0) (x 1) ^ 2) / Real.exp (D.lam (x 0) (x 1)) +
        partialT D.r (x 0) (x 1) ^ 2 + 1, 0],
    ![0, 0, 0, Real.sin (x 2) ^ 2 *
      (D.r (x 0) (x 1) * partialT D.lam (x 0) (x 1) * partialT D.r (x 0) (x 1) / 2 +
        D.r (x 0) (x 1) * partialT (partialT D.r) (x 0) (x 1) +
        (D.r (x 0) (x 1) * partialR D.lam (x 0) (x 1) * partialR D.r (x 0) (x 1) / 2 -
          D.r (x 0) (x 1) * partialR (partialR D.r) (x 0) (x 1) -
          partialR D.r (x 0) (x 1) ^ 2) / Real.exp (D.lam (x 0) (x 1)) +
        partialT D.r (x 0) (x 1) ^ 2 + 1)]]

/-- **The Ricci tensor of the comoving frame** at every point of the domain is the table
`ricci`. -/
theorem ricciOf_eq (hx : x ∈ domain D) (j k : Fin 4) :
    ricciOf (metric D).coefficient x j k = ricci D x j k := by
  have he := (Real.exp_pos (D.lam (x 0) (x 1))).ne'
  have hr := (r_pos_of_mem hx).ne'
  have hs := (sin_pos_of_mem hx).ne'
  have hsr := partialT_partialR D.contDiffOn_r (mem_S hx)
  have hsl := partialT_partialR D.contDiffOn_lam (mem_S hx)
  rw [ricciOf_eq_ricciOfChristoffel (eventually_christoffelOf_eq hx)]
  fin_cases j <;> fin_cases k <;>
  · simp only [ricciOfChristoffel, sum_four, christoffel, ricci, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    simp only [fderiv_gamma011 hx, fderiv_gamma022 hx, fderiv_gamma033 hx, fderiv_gamma101 hx,
      fderiv_gamma111 hx, fderiv_gamma122 hx, fderiv_gamma133 hx, fderiv_gamma202 hx,
      fderiv_gamma212 hx, fderiv_gamma233, fderiv_gamma323 hx, fderiv_const_apply, zero_apply]
    simp [gamma011, gamma022, gamma033, gamma101, gamma111, gamma122, gamma133,
      gamma202, gamma212, gamma233, gamma323, along, hsr, hsl]
    try field_simp
    try simp only [Real.cos_sq']
    try ring


/-! ### The Einstein tensor -/

/-- The inverse of the matrix of coefficients is `diag(1/c)`. -/
theorem coefficient_metric_inv (hx : x ∈ domain D) :
    ((metric D).coefficient x)⁻¹ = Matrix.diagonal fun l => (coefficients D x l)⁻¹ := by
  rw [coefficient_metric]
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one with l
  exact inv_mul_cancel₀ (coefficients_ne_zero hx l)

/-- The scalar curvature `R = ∑ₐ R_{aa}/c_a`. -/
theorem scalarOf_eq (hx : x ∈ domain D) :
    scalarOf (metric D).coefficient x = ∑ a, ricci D x a a / coefficients D x a := by
  rw [scalarOf, coefficient_metric_inv hx]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a (fun c _ hc => by simp [Matrix.diagonal_apply_ne _ (Ne.symm hc)])
    (fun h => absurd (Finset.mem_univ a) h), Matrix.diagonal_apply_eq, ricciOf_eq hx,
    div_eq_mul_inv]

variable (D) in
/-- The table of the Einstein tensor `G_{ik} = R_{ik} − ½ R g_{ik}` of the comoving frame, the
left-hand sides of Landau–Lifshitz (103.2) in covariant form:
`G₀₀ = λ̇ṙ/r + e^{−λ}(λ′r′ − 2r″)/r + (ṙ² + 1)/r² − e^{−λ} r′²/r²`,
`G₀₁ = G₁₀ = (λ̇ r′ − 2ṙ′)/r`, `G₁₁ = −e^λ(2r r̈ + ṙ² + 1)/r² + r′²/r²`,
`G₂₂ = −r²(λ̇²/4 + λ̈/2) − rλ̇ṙ/2 − r r̈ + r e^{−λ}(r″ − λ′r′/2)` and `G₃₃ = sin²θ G₂₂`; the other
components vanish. -/
def einstein (x : E) : Fin 4 → Fin 4 → ℝ :=
  ![![partialT D.lam (x 0) (x 1) * partialT D.r (x 0) (x 1) / D.r (x 0) (x 1) +
        (partialR D.lam (x 0) (x 1) * partialR D.r (x 0) (x 1) -
          2 * partialR (partialR D.r) (x 0) (x 1)) /
          (Real.exp (D.lam (x 0) (x 1)) * D.r (x 0) (x 1)) +
        (partialT D.r (x 0) (x 1) ^ 2 + 1) / D.r (x 0) (x 1) ^ 2 -
        partialR D.r (x 0) (x 1) ^ 2 / (Real.exp (D.lam (x 0) (x 1)) * D.r (x 0) (x 1) ^ 2),
      (partialT D.lam (x 0) (x 1) * partialR D.r (x 0) (x 1) -
        2 * partialR (partialT D.r) (x 0) (x 1)) / D.r (x 0) (x 1), 0, 0],
    ![(partialT D.lam (x 0) (x 1) * partialR D.r (x 0) (x 1) -
        2 * partialR (partialT D.r) (x 0) (x 1)) / D.r (x 0) (x 1),
      -(Real.exp (D.lam (x 0) (x 1)) * (2 * D.r (x 0) (x 1) * partialT (partialT D.r) (x 0) (x 1) +
          partialT D.r (x 0) (x 1) ^ 2 + 1)) / D.r (x 0) (x 1) ^ 2 +
        partialR D.r (x 0) (x 1) ^ 2 / D.r (x 0) (x 1) ^ 2, 0, 0],
    ![0, 0, -(D.r (x 0) (x 1) ^ 2 * (partialT D.lam (x 0) (x 1) ^ 2 / 4 +
          partialT (partialT D.lam) (x 0) (x 1) / 2)) -
        D.r (x 0) (x 1) * partialT D.lam (x 0) (x 1) * partialT D.r (x 0) (x 1) / 2 -
        D.r (x 0) (x 1) * partialT (partialT D.r) (x 0) (x 1) +
        D.r (x 0) (x 1) * (partialR (partialR D.r) (x 0) (x 1) -
          partialR D.lam (x 0) (x 1) * partialR D.r (x 0) (x 1) / 2) /
          Real.exp (D.lam (x 0) (x 1)), 0],
    ![0, 0, 0, Real.sin (x 2) ^ 2 *
      (-(D.r (x 0) (x 1) ^ 2 * (partialT D.lam (x 0) (x 1) ^ 2 / 4 +
          partialT (partialT D.lam) (x 0) (x 1) / 2)) -
        D.r (x 0) (x 1) * partialT D.lam (x 0) (x 1) * partialT D.r (x 0) (x 1) / 2 -
        D.r (x 0) (x 1) * partialT (partialT D.r) (x 0) (x 1) +
        D.r (x 0) (x 1) * (partialR (partialR D.r) (x 0) (x 1) -
          partialR D.lam (x 0) (x 1) * partialR D.r (x 0) (x 1) / 2) /
          Real.exp (D.lam (x 0) (x 1)))]]

/-- **The Einstein tensor of the comoving frame** at every point of the domain is the table
`einstein`. -/
theorem einsteinOf_eq (hx : x ∈ domain D) (i k : Fin 4) :
    einsteinOf (metric D).coefficient x i k = einstein D x i k := by
  have he := (Real.exp_pos (D.lam (x 0) (x 1))).ne'
  have hr := (r_pos_of_mem hx).ne'
  have hs := (sin_pos_of_mem hx).ne'
  rw [einsteinOf, ricciOf_eq hx, scalarOf_eq hx, coefficient_metric, sum_four]
  fin_cases i <;> fin_cases k <;>
  · simp [ricci, einstein, coefficients]
    try field_simp
    try ring


/-- `G₁₀ = G₀₁`. -/
theorem einstein_one_zero (y : E) : einstein D y 1 0 = einstein D y 0 1 := rfl

/-- `G₃₃ = sin²θ G₂₂`. -/
theorem einstein_three_three (y : E) :
    einstein D y 3 3 = Real.sin (y 2) ^ 2 * einstein D y 2 2 := rfl

/-! ### The functions `f` and `F` of a point -/

/-- `τ ↦ f(τ, R)` has the derivative `∂f/∂τ` on `S`. -/
theorem hasDerivAt_dt {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) D.S)
    {τ R : ℝ} (h : (τ, R) ∈ D.S) : HasDerivAt (fun s => f s R) (partialT f τ R) τ :=
  hasDerivAt_partialT D.isOpen_S hf h

/-- `R ↦ f(τ, R)` has the derivative `∂f/∂R` on `S`. -/
theorem hasDerivAt_dR {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) D.S)
    {τ R : ℝ} (h : (τ, R) ∈ D.S) : HasDerivAt (fun s => f τ s) (partialR f τ R) R :=
  hasDerivAt_partialR D.isOpen_S hf h

/-- The slice `{τ | (τ, R) ∈ S}` of the shell `R` is open. -/
theorem isOpen_slice (R : ℝ) : IsOpen {τ | (τ, R) ∈ D.S} :=
  D.isOpen_S.preimage (continuous_id.prodMk continuous_const)

/-- The set `{R' | (τ, R') ∈ S}` of the shells at the time `τ` is open. -/
theorem isOpen_shells (τ : ℝ) : IsOpen {R | (τ, R) ∈ D.S} :=
  D.isOpen_S.preimage (continuous_const.prodMk continuous_id)

variable (D) in
/-- The function `f = e^{−λ} r′² − 1` of the point (Landau–Lifshitz, (103.3)). -/
def energyOf (τ R : ℝ) : ℝ := partialR D.r τ R ^ 2 / Real.exp (D.lam τ R) - 1

variable (D) in
/-- The function `F = r(ṙ² − f)` of the point (Landau–Lifshitz, (103.4)); for `κ = 8π`
(`G = c = 1`) `F/2` is the mass inside the shell. -/
def massOf (τ R : ℝ) : ℝ := D.r τ R * (partialT D.r τ R ^ 2 - energyOf D τ R)

/-- `∂_τ f = r′(2ṙ′ − λ̇ r′) e^{−λ}`. -/
theorem hasDerivAt_energyOf_time {τ R : ℝ} (h : (τ, R) ∈ D.S) :
    HasDerivAt (fun s => energyOf D s R)
      (partialR D.r τ R * (2 * partialR (partialT D.r) τ R -
        partialT D.lam τ R * partialR D.r τ R) / Real.exp (D.lam τ R)) τ := by
  have he := (Real.exp_pos (D.lam τ R)).ne'
  have h1 := (((hasDerivAt_dt (contDiffOn_dR D.contDiffOn_r) h).fun_pow 2).fun_div
    (hasDerivAt_dt D.contDiffOn_lam h).exp he).sub_const 1
  refine h1.congr_deriv ?_
  rw [partialT_partialR D.contDiffOn_r h]
  field_simp
  push_cast
  ring

/-- `∂_R f = (2r′r″ − r′² λ′) e^{−λ}`. -/
theorem hasDerivAt_energyOf_radius {τ R : ℝ} (h : (τ, R) ∈ D.S) :
    HasDerivAt (fun s => energyOf D τ s)
      ((2 * partialR D.r τ R * partialR (partialR D.r) τ R -
        partialR D.r τ R ^ 2 * partialR D.lam τ R) / Real.exp (D.lam τ R)) R := by
  have he := (Real.exp_pos (D.lam τ R)).ne'
  have h1 := (((hasDerivAt_dR (contDiffOn_dR D.contDiffOn_r) h).fun_pow 2).fun_div
    (hasDerivAt_dR D.contDiffOn_lam h).exp he).sub_const 1
  refine h1.congr_deriv ?_
  field_simp
  push_cast
  ring

/-- `∂_τ F = ṙ(ṙ² − f + 2r r̈) − r ∂_τ f`. -/
theorem hasDerivAt_massOf_time {τ R : ℝ} (h : (τ, R) ∈ D.S) :
    HasDerivAt (fun s => massOf D s R)
      (partialT D.r τ R * (partialT D.r τ R ^ 2 - energyOf D τ R +
          2 * D.r τ R * partialT (partialT D.r) τ R) -
        D.r τ R * (partialR D.r τ R * (2 * partialR (partialT D.r) τ R -
          partialT D.lam τ R * partialR D.r τ R) / Real.exp (D.lam τ R))) τ := by
  have h1 := (hasDerivAt_dt D.contDiffOn_r h).fun_mul
    (((hasDerivAt_dt (contDiffOn_dt D.contDiffOn_r) h).fun_pow 2).fun_sub
      (hasDerivAt_energyOf_time h))
  refine h1.congr_deriv ?_
  push_cast
  ring

/-- `∂_R F = r′(ṙ² − f) + r(2ṙṙ′ − ∂_R f)`. -/
theorem hasDerivAt_massOf_radius {τ R : ℝ} (h : (τ, R) ∈ D.S) :
    HasDerivAt (fun s => massOf D τ s)
      (partialR D.r τ R * (partialT D.r τ R ^ 2 - energyOf D τ R) +
        D.r τ R * (2 * partialT D.r τ R * partialR (partialT D.r) τ R -
          (2 * partialR D.r τ R * partialR (partialR D.r) τ R -
            partialR D.r τ R ^ 2 * partialR D.lam τ R) / Real.exp (D.lam τ R))) R := by
  have h1 := (hasDerivAt_dR D.contDiffOn_r h).fun_mul
    (((hasDerivAt_dR (contDiffOn_dt D.contDiffOn_r) h).fun_pow 2).fun_sub
      (hasDerivAt_energyOf_radius h))
  refine h1.congr_deriv ?_
  push_cast
  ring

/-- **The time component and the mass function**: `G₀₀ r² r′ = ∂_R F + r ṙ (λ̇ r′ − 2ṙ′)`. -/
theorem einstein_zero_zero_mul (hx : x ∈ domain D) :
    einstein D x 0 0 * (D.r (x 0) (x 1) ^ 2 * partialR D.r (x 0) (x 1)) =
      (partialR D.r (x 0) (x 1) * (partialT D.r (x 0) (x 1) ^ 2 - energyOf D (x 0) (x 1)) +
        D.r (x 0) (x 1) * (2 * partialT D.r (x 0) (x 1) * partialR (partialT D.r) (x 0) (x 1) -
          (2 * partialR D.r (x 0) (x 1) * partialR (partialR D.r) (x 0) (x 1) -
            partialR D.r (x 0) (x 1) ^ 2 * partialR D.lam (x 0) (x 1)) /
              Real.exp (D.lam (x 0) (x 1)))) +
        D.r (x 0) (x 1) * partialT D.r (x 0) (x 1) * (partialT D.lam (x 0) (x 1) *
          partialR D.r (x 0) (x 1) - 2 * partialR (partialT D.r) (x 0) (x 1)) := by
  have he := (Real.exp_pos (D.lam (x 0) (x 1))).ne'
  have hr := (r_pos_of_mem hx).ne'
  simp only [einstein, energyOf, Matrix.cons_val_zero]
  field_simp
  ring

/-- **The radial component and the energy function**: `G₁₁ = −e^λ (2r r̈ + ṙ² − f)/r²`. -/
theorem einstein_one_one_eq (hx : x ∈ domain D) :
    einstein D x 1 1 = -(Real.exp (D.lam (x 0) (x 1)) *
      (2 * D.r (x 0) (x 1) * partialT (partialT D.r) (x 0) (x 1) + partialT D.r (x 0) (x 1) ^ 2 -
        energyOf D (x 0) (x 1))) / D.r (x 0) (x 1) ^ 2 := by
  have he := (Real.exp_pos (D.lam (x 0) (x 1))).ne'
  have hr := (r_pos_of_mem hx).ne'
  simp only [einstein, energyOf, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring


/-! ### The dust -/

/-- The covector `u_μ = (−1, 0, 0, 0)` of the four-velocity `u = ∂_τ` of the dust. -/
def fluidCovector : Fin 4 → ℝ := ![-1, 0, 0, 0]

/-- **The stress of the dust** at rest in the frame, `T_{μν} = ε u_μ u_ν` with the energy density
`ε(τ, R)` and `u = ∂_τ` (Landau–Lifshitz, §103: dustlike matter, `p = 0`). -/
def dustStress (ε : ℝ → ℝ → ℝ) (x : E) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => ε (x 0) (x 1) * fluidCovector i * fluidCovector j

/-- The stress of the dust is smooth on the domain when the density is smooth on `S`. -/
theorem contDiffOn_dustStress {ε : ℝ → ℝ → ℝ} (hε : ContDiffOn ℝ ∞ (Function.uncurry ε) D.S)
    (i k : Fin 4) : ContDiffOn ℝ ∞ (fun x => dustStress ε x i k) (domain D) :=
  ((contDiffOn_lift hε).mul contDiffOn_const).mul contDiffOn_const

/-- **The Einstein equations with the dust at a point** are the four equations
`G₀₀ = κε`, `G₀₁ = 0`, `G₁₁ = 0`, `G₂₂ = 0`: the components off the diagonal and the `(τ, R)`
block vanish identically, and `G₃₃ = sin²θ G₂₂`. -/
theorem isEinstein_at_iff (hx : x ∈ domain D) (κ : ℝ) (ε : ℝ → ℝ → ℝ) :
    (∀ i k, einsteinOf (metric D).coefficient x i k + 0 * (metric D).coefficient x i k =
      κ * dustStress ε x i k) ↔
      einstein D x 0 0 = κ * ε (x 0) (x 1) ∧ einstein D x 0 1 = 0 ∧ einstein D x 1 1 = 0 ∧
        einstein D x 2 2 = 0 := by
  simp only [zero_mul, add_zero, einsteinOf_eq hx]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [dustStress, fluidCovector] using h 0 0
    · simpa [dustStress, fluidCovector] using h 0 1
    · simpa [dustStress, fluidCovector] using h 1 1
    · simpa [dustStress, fluidCovector] using h 2 2
  · rintro ⟨h00, h01, h11, h22⟩ i k
    fin_cases i <;> fin_cases k
    · simpa [dustStress, fluidCovector] using h00
    · simpa [dustStress, fluidCovector] using h01
    · simp [einstein, dustStress, fluidCovector]
    · simp [einstein, dustStress, fluidCovector]
    · simpa [dustStress, fluidCovector, einstein_one_zero] using h01
    · simpa [dustStress, fluidCovector] using h11
    · simp [einstein, dustStress, fluidCovector]
    · simp [einstein, dustStress, fluidCovector]
    · simp [einstein, dustStress, fluidCovector]
    · simp [einstein, dustStress, fluidCovector]
    · simpa [dustStress, fluidCovector] using h22
    · simp [einstein, dustStress, fluidCovector]
    · simp [einstein, dustStress, fluidCovector]
    · simp [einstein, dustStress, fluidCovector]
    · simp [einstein, dustStress, fluidCovector]
    · simpa [dustStress, fluidCovector, einstein_three_three] using Or.inr h22

/-! ### The equations of the dust sphere -/

variable (D) in
/-- **The equations of the dust sphere** (Landau–Lifshitz, (103.3)–(103.5)) with two functions
`f(R)` and `F(R)` of the shell, at every point of `S`: `e^λ = r′²/(1 + f)`, the first integral
`ṙ² = f + F/r`, the equation of motion `r̈ = −F/(2r²)` of the shell, and `κε = F′/(r′r²)`. The
equation of motion follows from the first integral where `ṙ ≠ 0` (`accel_of_energy`). -/
structure Equations (κ : ℝ) (ε : ℝ → ℝ → ℝ) (f F : ℝ → ℝ) : Prop where
  /-- `e^λ = r′²/(1 + f)` (L&L (103.3)). -/
  exp_lam : ∀ τ R, (τ, R) ∈ D.S → Real.exp (D.lam τ R) = partialR D.r τ R ^ 2 / (1 + f R)
  /-- `ṙ² = f + F/r` (L&L (103.4)). -/
  energy : ∀ τ R, (τ, R) ∈ D.S → partialT D.r τ R ^ 2 = f R + F R / D.r τ R
  /-- `r̈ = −F/(2r²)`. -/
  accel : ∀ τ R, (τ, R) ∈ D.S → partialT (partialT D.r) τ R = -F R / (2 * D.r τ R ^ 2)
  /-- `κε = F′/(r′r²)` (L&L (103.5)). -/
  density : ∀ τ R, (τ, R) ∈ D.S →
    κ * ε τ R = deriv F R / (partialR D.r τ R * D.r τ R ^ 2)

namespace Equations

variable {κ : ℝ} {ε : ℝ → ℝ → ℝ} {f F : ℝ → ℝ} (h : Equations D κ ε f F) {τ R : ℝ}
include h

/-- The function `f` of the equations is the function `e^{−λ} r′² − 1` of the point. -/
theorem energyOf_eq (hp : (τ, R) ∈ D.S) : energyOf D τ R = f R := by
  have he := Real.exp_pos (D.lam τ R)
  have hR := (D.partialR_r_pos _ hp).ne'
  have h1 := h.exp_lam τ R hp
  have hf : 1 + f R ≠ 0 := by
    intro h0
    rw [h0, div_zero] at h1
    exact he.ne' h1
  rw [energyOf, h1]
  field_simp
  ring

/-- `f > −1`. -/
theorem one_add_pos (hp : (τ, R) ∈ D.S) : 0 < 1 + f R := by
  have h1 := h.energyOf_eq hp
  rw [energyOf] at h1
  have : 0 < partialR D.r τ R ^ 2 / Real.exp (D.lam τ R) :=
    div_pos (pow_pos (D.partialR_r_pos _ hp) 2) (Real.exp_pos _)
  linarith

/-- The function `F` of the equations is the function `r(ṙ² − f)` of the point. -/
theorem massOf_eq (hp : (τ, R) ∈ D.S) : massOf D τ R = F R := by
  have hr := (D.r_pos _ hp).ne'
  rw [massOf, h.energyOf_eq hp, h.energy τ R hp]
  field_simp
  ring

/-- `F` is differentiable, with `F′ = r′(ṙ² − f) + r(2ṙṙ′ − ∂_R f)` at every point of `S`. -/
theorem hasDerivAt_mass (hp : (τ, R) ∈ D.S) :
    HasDerivAt F
      (partialR D.r τ R * (partialT D.r τ R ^ 2 - energyOf D τ R) +
        D.r τ R * (2 * partialT D.r τ R * partialR (partialT D.r) τ R -
          (2 * partialR D.r τ R * partialR (partialR D.r) τ R -
            partialR D.r τ R ^ 2 * partialR D.lam τ R) / Real.exp (D.lam τ R))) R := by
  refine (hasDerivAt_massOf_radius hp).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_shells τ).mem_nhds hp] with R' hR' using (h.massOf_eq hR').symm


/-- **The momentum constraint** `λ̇ r′ = 2ṙ′`: the function `f` does not depend on the time. -/
theorem momentum (hp : (τ, R) ∈ D.S) :
    partialT D.lam τ R * partialR D.r τ R = 2 * partialR (partialT D.r) τ R := by
  have he := (Real.exp_pos (D.lam τ R)).ne'
  have hR := (D.partialR_r_pos _ hp).ne'
  have hc : (fun s => energyOf D s R) =ᶠ[𝓝 τ] fun _ => f R := by
    filter_upwards [(isOpen_slice R).mem_nhds hp] with s hs using h.energyOf_eq hs
  have h0 := (hasDerivAt_energyOf_time hp).unique
    ((hasDerivAt_const τ (f R)).congr_of_eventuallyEq hc)
  rw [div_eq_zero_iff, mul_eq_zero] at h0
  rcases h0 with (h0 | h0) | h0
  · exact absurd h0 hR
  · linarith
  · exact absurd h0 he

/-- The time derivative of the momentum constraint: `λ̈ r′ + λ̇ ṙ′ = 2 ∂_R r̈`. -/
theorem momentum_time (hp : (τ, R) ∈ D.S) :
    partialT (partialT D.lam) τ R * partialR D.r τ R +
        partialT D.lam τ R * partialR (partialT D.r) τ R =
      2 * partialR (partialT (partialT D.r)) τ R := by
  have h1 := ((hasDerivAt_dt (contDiffOn_dt D.contDiffOn_lam) hp).fun_mul
    (hasDerivAt_dt (contDiffOn_dR D.contDiffOn_r) hp)).fun_sub
      ((hasDerivAt_dt (contDiffOn_dR (contDiffOn_dt D.contDiffOn_r)) hp).const_mul 2)
  have hc : (fun s => partialT D.lam s R * partialR D.r s R -
      2 * partialR (partialT D.r) s R) =ᶠ[𝓝 τ] fun _ => 0 := by
    filter_upwards [(isOpen_slice R).mem_nhds hp] with s hs
    rw [h.momentum hs, sub_self]
  have h0 := h1.unique ((hasDerivAt_const τ (0 : ℝ)).congr_of_eventuallyEq hc)
  rw [partialT_partialR D.contDiffOn_r hp,
    partialT_partialR (contDiffOn_dt D.contDiffOn_r) hp] at h0
  linarith

/-- The radial derivative of the equation of motion: `∂_R r̈ = −F′/(2r²) + F r′/r³`. -/
theorem accel_radius (hp : (τ, R) ∈ D.S) :
    partialR (partialT (partialT D.r)) τ R =
      -(partialR D.r τ R * (partialT D.r τ R ^ 2 - energyOf D τ R) +
        D.r τ R * (2 * partialT D.r τ R * partialR (partialT D.r) τ R -
          (2 * partialR D.r τ R * partialR (partialR D.r) τ R -
            partialR D.r τ R ^ 2 * partialR D.lam τ R) / Real.exp (D.lam τ R))) /
          (2 * D.r τ R ^ 2) + F R * partialR D.r τ R / D.r τ R ^ 3 := by
  have hr := (D.r_pos _ hp).ne'
  have h1 := (hasDerivAt_dR (contDiffOn_dt (contDiffOn_dt D.contDiffOn_r)) hp)
  have h2 := (h.hasDerivAt_mass hp).fun_neg.fun_div
    (((hasDerivAt_dR D.contDiffOn_r hp).fun_pow 2).const_mul 2)
    (mul_ne_zero two_ne_zero (pow_ne_zero 2 hr))
  have hc : (fun s => partialT (partialT D.r) τ s) =ᶠ[𝓝 R]
      fun s => -F s / (2 * D.r τ s ^ 2) := by
    filter_upwards [(isOpen_shells τ).mem_nhds hp] with s hs using h.accel τ s hs
  rw [h1.unique (h2.congr_of_eventuallyEq hc)]
  field_simp
  push_cast
  ring

/-- The time component of the Einstein equations: `G₀₀ = κε`. -/
theorem einstein_zero_zero (hx : x ∈ domain D) :
    einstein D x 0 0 = κ * ε (x 0) (x 1) := by
  have hp := mem_S hx
  have hr := (r_pos_of_mem hx).ne'
  have hR := (partialR_r_pos_of_mem hx).ne'
  have h1 := einstein_zero_zero_mul hx
  rw [← (h.hasDerivAt_mass hp).deriv, h.momentum hp, sub_self, mul_zero, add_zero] at h1
  rw [h.density _ _ hp, ← h1]
  field_simp

/-- The mixed component of the Einstein equations: `G₀₁ = 0`. -/
theorem einstein_zero_one (hx : x ∈ domain D) : einstein D x 0 1 = 0 := by
  simp only [einstein, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h.momentum (mem_S hx), sub_self, zero_div]

/-- The radial component of the Einstein equations: `G₁₁ = 0`. -/
theorem einstein_one_one (hx : x ∈ domain D) : einstein D x 1 1 = 0 := by
  have hp := mem_S hx
  have hr := (r_pos_of_mem hx).ne'
  rw [einstein_one_one_eq hx, h.accel _ _ hp, h.energyOf_eq hp, h.energy _ _ hp]
  field_simp
  ring

/-- The angular component of the Einstein equations: `G₂₂ = 0`. -/
theorem einstein_two_two (hx : x ∈ domain D) : einstein D x 2 2 = 0 := by
  have hp := mem_S hx
  have he := (Real.exp_pos (D.lam (x 0) (x 1))).ne'
  have hr := (r_pos_of_mem hx).ne'
  have hR := (partialR_r_pos_of_mem hx).ne'
  have e1 : partialT D.lam (x 0) (x 1) =
      2 * partialR (partialT D.r) (x 0) (x 1) / partialR D.r (x 0) (x 1) := by
    field_simp
    linear_combination h.momentum hp
  have e2 : partialT (partialT D.lam) (x 0) (x 1) =
      (2 * partialR (partialT (partialT D.r)) (x 0) (x 1) -
        partialT D.lam (x 0) (x 1) * partialR (partialT D.r) (x 0) (x 1)) /
        partialR D.r (x 0) (x 1) := by
    field_simp
    linear_combination h.momentum_time hp
  have hm := h.massOf_eq hp
  simp only [einstein, Matrix.cons_val]
  rw [e2, h.accel_radius hp, e1, h.accel _ _ hp]
  rw [massOf, h.energyOf_eq hp] at hm
  rw [← hm]
  rw [h.energyOf_eq hp]
  field_simp
  ring

/-- **The equations of the dust sphere give the Einstein equations** with the dust, at every
point of the domain. -/
theorem isEinstein : (metric D).IsEinstein κ 0 (dustStress ε) := by
  intro x hx
  exact (isEinstein_at_iff hx κ ε).mpr ⟨h.einstein_zero_zero hx, h.einstein_zero_one hx,
    h.einstein_one_one hx, h.einstein_two_two hx⟩

end Equations


/-- **The equation of motion follows from the first integral** where `ṙ ≠ 0`: if
`ṙ² = f + F/r` on `S`, then `r̈ = −F/(2r²)` at every point of `S` with `ṙ ≠ 0`. -/
theorem accel_of_energy {f F : ℝ → ℝ}
    (he : ∀ τ R, (τ, R) ∈ D.S → partialT D.r τ R ^ 2 = f R + F R / D.r τ R) {τ R : ℝ}
    (hp : (τ, R) ∈ D.S) (h0 : partialT D.r τ R ≠ 0) :
    partialT (partialT D.r) τ R = -F R / (2 * D.r τ R ^ 2) := by
  have hr : D.r τ R ≠ 0 := (D.r_pos _ hp).ne'
  have h1 := (hasDerivAt_dt (contDiffOn_dt D.contDiffOn_r) hp).fun_pow 2
  have h2 := ((hasDerivAt_const τ (F R)).fun_div (hasDerivAt_dt D.contDiffOn_r hp) hr).const_add
    (f R)
  have heq : (fun s => partialT D.r s R ^ 2) =ᶠ[𝓝 τ] fun s => f R + F R / D.r s R := by
    filter_upwards [(isOpen_slice R).mem_nhds hp] with s hs using he s R hs
  have h3 := h1.unique (h2.congr_of_eventuallyEq heq)
  have h4 : partialT D.r τ R * (2 * partialT (partialT D.r) τ R * D.r τ R ^ 2 + F R) = 0 := by
    field_simp at h3
    push_cast at h3
    linear_combination h3
  rcases mul_eq_zero.mp h4 with h5 | h5
  · exact absurd h5 h0
  · field_simp
    linear_combination h5


/-! ### The Einstein equations give the equations of the dust sphere -/

variable (D) in
/-- The value of `g(·, R)` at a point of the slice `{τ | (τ, R) ∈ S}` of the shell `R`, zero when
the slice is empty. For a function that does not depend on the time on the slice it is the
function of the shell (`sliceValue_eq`). -/
def sliceValue (g : ℝ → ℝ → ℝ) (R : ℝ) : ℝ := by
  classical
  exact if h : ∃ τ, (τ, R) ∈ D.S then g h.choose R else 0

/-- A function with `∂_τ g = 0` on a preconnected slice is the function `sliceValue D g` of the
shell there. -/
theorem sliceValue_eq {g : ℝ → ℝ → ℝ} {R : ℝ} (hS : IsPreconnected {τ | (τ, R) ∈ D.S})
    (hg : ∀ τ, (τ, R) ∈ D.S → HasDerivAt (fun s => g s R) 0 τ) {τ : ℝ} (h : (τ, R) ∈ D.S) :
    g τ R = sliceValue D g R := by
  have hex : ∃ τ, (τ, R) ∈ D.S := ⟨τ, h⟩
  rw [sliceValue, dite_eq_left hex]
  exact (isOpen_slice R).is_const_of_deriv_eq_zero hS
    (fun s hs => (hg s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hg s hs).deriv) h hex.choose_spec

/-- **The Einstein equations with the dust give the equations of the dust sphere**, when every
slice `{τ | (τ, R) ∈ S}` is preconnected, with `f` and `F` the values of `e^{−λ}r′² − 1` and
`r(ṙ² − f)` on the slices: the momentum constraint `G₀₁ = 0` makes `f` independent of the time,
and `G₁₁ = 0` makes `F` independent of the time. -/
theorem equations_of_isEinstein (hS : ∀ R, IsPreconnected {τ | (τ, R) ∈ D.S}) {κ : ℝ}
    {ε : ℝ → ℝ → ℝ} (h : (metric D).IsEinstein κ 0 (dustStress ε)) :
    Equations D κ ε (sliceValue D (energyOf D)) (sliceValue D (massOf D)) := by
  have hc : ∀ τ R, (τ, R) ∈ D.S → einstein D (point τ R) 0 0 = κ * ε τ R ∧
      einstein D (point τ R) 0 1 = 0 ∧ einstein D (point τ R) 1 1 = 0 := by
    intro τ R hp
    have h1 := (isEinstein_at_iff (point_mem hp) κ ε).mp (h _ (point_mem hp))
    exact ⟨by simpa using h1.1, h1.2.1, h1.2.2.1⟩
  have hmom : ∀ τ R, (τ, R) ∈ D.S →
      partialT D.lam τ R * partialR D.r τ R = 2 * partialR (partialT D.r) τ R := by
    intro τ R hp
    have h01 := (hc τ R hp).2.1
    simp only [einstein, Matrix.cons_val_zero, Matrix.cons_val_one, point_zero,
      point_one] at h01
    rcases div_eq_zero_iff.mp h01 with h01 | h01
    · linarith
    · exact absurd h01 (D.r_pos _ hp).ne'
  have hrad : ∀ τ R, (τ, R) ∈ D.S →
      2 * D.r τ R * partialT (partialT D.r) τ R + partialT D.r τ R ^ 2 - energyOf D τ R = 0 := by
    intro τ R hp
    have h11 := (hc τ R hp).2.2
    rw [einstein_one_one_eq (point_mem hp)] at h11
    simp only [point_zero, point_one] at h11
    rcases div_eq_zero_iff.mp h11 with h11 | h11
    · rcases mul_eq_zero.mp (neg_eq_zero.mp h11) with h11 | h11
      · exact absurd h11 (Real.exp_pos _).ne'
      · exact h11
    · exact absurd h11 (pow_ne_zero 2 (D.r_pos _ hp).ne')
  have hf : ∀ τ R, (τ, R) ∈ D.S → energyOf D τ R = sliceValue D (energyOf D) R :=
    fun τ R hp => sliceValue_eq (hS R) (fun s hs => (hasDerivAt_energyOf_time hs).congr_deriv
      (by rw [hmom s R hs, sub_self, mul_zero, zero_div])) hp
  have hF : ∀ τ R, (τ, R) ∈ D.S → massOf D τ R = sliceValue D (massOf D) R :=
    fun τ R hp => sliceValue_eq (hS R) (fun s hs => (hasDerivAt_massOf_time hs).congr_deriv
      (by
        rw [hmom s R hs, sub_self, mul_zero, zero_div, mul_zero, sub_zero]
        linear_combination partialT D.r s R * hrad s R hs)) hp
  refine ⟨fun τ R hp => ?_, fun τ R hp => ?_, fun τ R hp => ?_, fun τ R hp => ?_⟩
  · have he := (Real.exp_pos (D.lam τ R)).ne'
    have hR := (D.partialR_r_pos _ hp).ne'
    rw [← hf τ R hp, energyOf]
    field_simp
    ring
  · have hr := (D.r_pos _ hp).ne'
    rw [← hf τ R hp, ← hF τ R hp, massOf]
    field_simp
    ring
  · have hr := (D.r_pos _ hp).ne'
    rw [← hF τ R hp, massOf]
    field_simp
    linear_combination hrad τ R hp
  · have hr := (D.r_pos _ hp).ne'
    have hR := (D.partialR_r_pos _ hp).ne'
    have hd := (hasDerivAt_massOf_radius hp).congr_of_eventuallyEq
      (f₁ := sliceValue D (massOf D)) (by
        filter_upwards [(isOpen_shells τ).mem_nhds hp] with s hs using (hF τ s hs).symm)
    have h1 := einstein_zero_zero_mul (point_mem hp)
    simp only [point_zero, point_one] at h1
    rw [hmom τ R hp, sub_self, mul_zero, add_zero] at h1
    rw [hd.deriv, ← (hc τ R hp).1, ← h1]
    field_simp

/-- **The Einstein equations of the dust sphere** (Landau–Lifshitz, §103). When every slice
`{τ | (τ, R) ∈ S}` is preconnected, the metric `−dτ² + e^λ dR² + r² dΩ²` with the dust
`T = ε u ⊗ u`, `u = ∂_τ`, satisfies `G_{ik} = κ T_{ik}` on the domain if and only if there are
functions `f`, `F` of the shell with `e^λ = r′²/(1 + f)`, `ṙ² = f + F/r`, `r̈ = −F/(2r²)` and
`κε = F′/(r′r²)` on `S` (`Equations`). Then `f > −1` (`Equations.one_add_pos`), and `f`, `F`
are the functions `e^{−λ}r′² − 1` and `r(ṙ² − f)` of the point (`Equations.energyOf_eq`,
`Equations.massOf_eq`). -/
theorem isEinstein_iff (hS : ∀ R, IsPreconnected {τ | (τ, R) ∈ D.S}) (κ : ℝ)
    (ε : ℝ → ℝ → ℝ) :
    (metric D).IsEinstein κ 0 (dustStress ε) ↔ ∃ f F : ℝ → ℝ, Equations D κ ε f F :=
  ⟨fun h => ⟨_, _, equations_of_isEinstein hS h⟩, fun ⟨_, _, h⟩ => h.isEinstein⟩

/-- **The native Einstein equations of the dust sphere**, for a density smooth on `S`. -/
theorem satisfiesEinstein_iff (hS : ∀ R, IsPreconnected {τ | (τ, R) ∈ D.S}) (κ : ℝ)
    {ε : ℝ → ℝ → ℝ} (hε : ContDiffOn ℝ ∞ (Function.uncurry ε) D.S) :
    (metric D).toLorentzMetric.SatisfiesEinstein κ 0
        (bilinearOf (dustStress ε) (contDiffOn_dustStress hε)) ↔
      ∃ f F : ℝ → ℝ, Equations D κ ε f F :=
  (satisfiesEinstein_bilinearOf_iff _ κ 0).trans (isEinstein_iff hS κ ε)

/-- **The dust is conserved**: for `κ ≠ 0` and a density smooth on `S`, the Einstein equations
give `∇^a T_{ab} = 0` on the domain, from the contracted Bianchi identity. -/
theorem divergence_dust_eq_zero {κ : ℝ} (hκ : κ ≠ 0) {ε : ℝ → ℝ → ℝ}
    (hε : ContDiffOn ℝ ∞ (Function.uncurry ε) D.S)
    (h : (metric D).IsEinstein κ 0 (dustStress ε)) (y : domain D) (b : Fin 4) :
    (metric D).divergenceOf (dustStress ε) y b = 0 := by
  have hn := (satisfiesEinstein_bilinearOf_iff (contDiffOn_dustStress hε) κ 0).mpr h
  rw [← bilinearDivergence_bilinearOf (g := metric D) (contDiffOn_dustStress hε) y b,
    hn.divergence_eq_zero hκ y]
  rfl


/-! ### The sign of the density and the conservation of the rest mass -/

namespace Equations

variable {κ : ℝ} {ε : ℝ → ℝ → ℝ} {f F : ℝ → ℝ} (h : Equations D κ ε f F) {τ R : ℝ}
include h

/-- **The density is nonnegative exactly where `F` does not decrease** (Landau–Lifshitz, (103.5)):
for `κ > 0`, before shell crossing (`r′ > 0` on `S`), `ε ≥ 0` at a point of `S` if and only if
`F′ ≥ 0` at its shell. -/
theorem density_nonneg_iff (hκ : 0 < κ) (hp : (τ, R) ∈ D.S) : 0 ≤ ε τ R ↔ 0 ≤ deriv F R := by
  have hpos : 0 < partialR D.r τ R * D.r τ R ^ 2 :=
    mul_pos (D.partialR_r_pos _ hp) (pow_pos (D.r_pos _ hp) 2)
  have h1 : ε τ R = deriv F R / (κ * (partialR D.r τ R * D.r τ R ^ 2)) := by
    rw [mul_comm κ, ← div_div, ← h.density τ R hp]
    field_simp
  rw [h1, le_div_iff₀ (mul_pos hκ hpos), zero_mul]

/-- **The rest mass of every shell is conserved** (for `κ ≠ 0`): `ε r′ r² = F′/κ` does not depend
on the time, so `∂_τ (ε r′ r²) = 0`. -/
theorem hasDerivAt_restMass (hκ : κ ≠ 0) (hp : (τ, R) ∈ D.S) :
    HasDerivAt (fun s => ε s R * (partialR D.r s R * D.r s R ^ 2)) 0 τ := by
  refine (hasDerivAt_const τ (deriv F R / κ)).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_slice R).mem_nhds hp] with s hs
  have hpos : partialR D.r s R * D.r s R ^ 2 ≠ 0 :=
    (mul_pos (D.partialR_r_pos _ hs) (pow_pos (D.r_pos _ hs) 2)).ne'
  have h1 := h.density s R hs
  rw [eq_div_iff hpos] at h1
  rw [eq_div_iff hκ]
  linear_combination h1

end Equations

/-! ### The parabolic solution -/

/-- `(y^{1/3})³ = y` for `y ≥ 0`. -/
theorem rpow_third_pow_three {y : ℝ} (hy : 0 ≤ y) : (y ^ (1 / 3 : ℝ)) ^ 3 = y := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
  norm_num

/-- The derivative of `y ↦ y^{1/3}` at `y > 0` is `1/(3 (y^{1/3})²)`. -/
theorem hasDerivAt_rpow_third {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => t ^ (1 / 3 : ℝ)) (1 / (3 * (y ^ (1 / 3 : ℝ)) ^ 2)) y := by
  have h := Real.hasDerivAt_rpow_const (p := 1 / 3) (Or.inl hy.ne')
  refine h.congr_deriv ?_
  have h1 : y ^ ((1 : ℝ) / 3 - 1) = ((y ^ (1 / 3 : ℝ)) ^ 2)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le, ← Real.rpow_neg hy.le]
    norm_num
  have h2 : 0 < y ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hy _
  rw [h1]
  field_simp

/-- The radius `r = (9F(τ₀ − τ)²/4)^{1/3}` of the parabolic solution `f = 0`, that is
`r = (9F/4)^{1/3} (τ₀ − τ)^{2/3}` (Landau–Lifshitz, (103.8); `parabolicRadius_eq`). -/
def parabolicRadius (F τ₀ : ℝ → ℝ) (τ R : ℝ) : ℝ :=
  (9 * F R * (τ₀ R - τ) ^ 2 / 4) ^ (1 / 3 : ℝ)

/-- The form `r = (9F/4)^{1/3} (τ₀ − τ)^{2/3}` of Landau–Lifshitz, (103.8). -/
theorem parabolicRadius_eq {F τ₀ : ℝ → ℝ} {τ R : ℝ} (hF : 0 ≤ F R) (hτ : τ ≤ τ₀ R) :
    parabolicRadius F τ₀ τ R = (9 * F R / 4) ^ (1 / 3 : ℝ) * (τ₀ R - τ) ^ (2 / 3 : ℝ) := by
  have hu : 0 ≤ τ₀ R - τ := sub_nonneg.mpr hτ
  rw [parabolicRadius, mul_div_right_comm, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_mul hu]
  norm_num

/-- The cube of the parabolic radius: `r³ = 9F(τ₀ − τ)²/4`. -/
theorem parabolicRadius_cube {F τ₀ : ℝ → ℝ} {τ R : ℝ} (hF : 0 ≤ F R) :
    parabolicRadius F τ₀ τ R ^ 3 = 9 * F R * (τ₀ R - τ) ^ 2 / 4 :=
  rpow_third_pow_three (by positivity)

/-- The parabolic radius is positive before the collapse. -/
theorem parabolicRadius_pos {F τ₀ : ℝ → ℝ} {τ R : ℝ} (hF : 0 < F R) (hτ : τ < τ₀ R) :
    0 < parabolicRadius F τ₀ τ R := by
  have : 0 < τ₀ R - τ := sub_pos.mpr hτ
  exact Real.rpow_pos_of_pos (by positivity) _

/-- **The collapse at the finite time `τ₀(R)`**: `r(τ, R) → 0` as `τ → τ₀(R)⁻`. -/
theorem tendsto_radius_zero (F τ₀ : ℝ → ℝ) (R : ℝ) :
    Tendsto (fun τ => parabolicRadius F τ₀ τ R) (𝓝[<] (τ₀ R)) (𝓝 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds ?_
  have hc : Continuous fun τ => 9 * F R * (τ₀ R - τ) ^ 2 / 4 := by fun_prop
  have h := ((Real.continuousAt_rpow_const _ (1 / 3 : ℝ) (Or.inr (by norm_num))).comp
    (hc.continuousAt (x := τ₀ R))).tendsto
  simpa [Function.comp_def, parabolicRadius, Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0)]
    using h

/-- The derivative of the parabolic radius in the time: `ṙ = −3F(τ₀ − τ)/(2r²)`. -/
theorem hasDerivAt_parabolicRadius_time {F τ₀ : ℝ → ℝ} {τ R : ℝ} (hF : 0 < F R)
    (hτ : τ < τ₀ R) :
    HasDerivAt (fun s => parabolicRadius F τ₀ s R)
      (-3 * F R * (τ₀ R - τ) / (2 * parabolicRadius F τ₀ τ R ^ 2)) τ := by
  have hu : 0 < τ₀ R - τ := sub_pos.mpr hτ
  have hX : 0 < 9 * F R * (τ₀ R - τ) ^ 2 / 4 := by positivity
  have h1 : HasDerivAt (fun s => 9 * F R * (τ₀ R - s) ^ 2 / 4)
      (9 * F R * (2 * (τ₀ R - τ) * (-1)) / 4) τ := by
    have := (((hasDerivAt_id τ).const_sub (τ₀ R)).fun_pow 2).const_mul (9 * F R)
    refine (this.div_const 4).congr_deriv ?_
    simp
  refine ((hasDerivAt_rpow_third hX).comp τ h1).congr_deriv ?_
  have hr := parabolicRadius_pos (τ₀ := τ₀) hF hτ
  rw [show (9 * F R * (τ₀ R - τ) ^ 2 / 4) ^ (1 / 3 : ℝ) = parabolicRadius F τ₀ τ R from rfl]
  field_simp
  ring


/-- The derivative of the parabolic radius in the shell:
`r′ = 3(F′(τ₀ − τ)² + 2F(τ₀ − τ)τ₀′)/(4r²)`. -/
theorem hasDerivAt_parabolicRadius_radius {F τ₀ : ℝ → ℝ} {τ R F' τ₀' : ℝ}
    (hF' : HasDerivAt F F' R) (hτ₀' : HasDerivAt τ₀ τ₀' R) (hF : 0 < F R) (hτ : τ < τ₀ R) :
    HasDerivAt (fun s => parabolicRadius F τ₀ τ s)
      (3 * (F' * (τ₀ R - τ) ^ 2 + 2 * F R * (τ₀ R - τ) * τ₀') /
        (4 * parabolicRadius F τ₀ τ R ^ 2)) R := by
  have hu : 0 < τ₀ R - τ := sub_pos.mpr hτ
  have hX : 0 < 9 * F R * (τ₀ R - τ) ^ 2 / 4 := by positivity
  have h1 : HasDerivAt (fun s => 9 * F s * (τ₀ s - τ) ^ 2 / 4)
      (9 * (F' * (τ₀ R - τ) ^ 2 + F R * (2 * (τ₀ R - τ) * τ₀')) / 4) R := by
    have := ((hF'.const_mul 9).fun_mul ((hτ₀'.sub_const τ).fun_pow 2)).div_const 4
    refine this.congr_deriv ?_
    push_cast
    ring
  refine ((hasDerivAt_rpow_third hX).comp R h1).congr_deriv ?_
  have hr := parabolicRadius_pos (τ₀ := τ₀) hF hτ
  rw [show (9 * F R * (τ₀ R - τ) ^ 2 / 4) ^ (1 / 3 : ℝ) = parabolicRadius F τ₀ τ R from rfl]
  field_simp
  ring

/-- The second derivative in the time: `s ↦ −3F(τ₀ − s)/(2r²)` has the derivative `−F/(2r²)`. -/
theorem hasDerivAt_parabolicRate {F τ₀ : ℝ → ℝ} {τ R : ℝ} (hF : 0 < F R) (hτ : τ < τ₀ R) :
    HasDerivAt (fun s => -3 * F R * (τ₀ R - s) / (2 * parabolicRadius F τ₀ s R ^ 2))
      (-F R / (2 * parabolicRadius F τ₀ τ R ^ 2)) τ := by
  have hr := parabolicRadius_pos (τ₀ := τ₀) hF hτ
  have hc := parabolicRadius_cube (τ₀ := τ₀) (τ := τ) hF.le
  have h1 : HasDerivAt (fun s => -3 * F R * (τ₀ R - s)) (3 * F R) τ := by
    have := ((hasDerivAt_id τ).const_sub (τ₀ R)).const_mul (-3 * F R)
    refine this.congr_deriv ?_
    simp
  have h2 := ((hasDerivAt_parabolicRadius_time hF hτ).fun_pow 2).const_mul 2
  refine (h1.fun_div h2 (by positivity)).congr_deriv ?_
  have hu : 0 < τ₀ R - τ := sub_pos.mpr hτ
  have hFe : F R = 4 * parabolicRadius F τ₀ τ R ^ 3 / (9 * (τ₀ R - τ) ^ 2) := by
    rw [hc]
    field_simp
  rw [hFe]
  field_simp
  push_cast
  ring

/-- **The data of a parabolic collapse** (`f = 0`, Landau–Lifshitz (103.8)): an open set `J` of
shells with smooth functions `F > 0` and `τ₀` on `J` such that `F′ ≥ 0`, `τ₀′ ≥ 0` and
`F′ + τ₀′ > 0`; these conditions exclude shell crossing for all `τ < τ₀(R)`. -/
structure ParabolicData where
  /-- The open set of shells. -/
  J : Set ℝ
  /-- The function `F(R)`. -/
  F : ℝ → ℝ
  /-- The time `τ₀(R)` of the arrival of the shell `R` at the centre. -/
  τ₀ : ℝ → ℝ
  /-- The set of shells is open. -/
  isOpen_J : IsOpen J
  /-- `F` is smooth on `J`. -/
  contDiffOn_F : ContDiffOn ℝ ∞ F J
  /-- `τ₀` is smooth on `J`. -/
  contDiffOn_τ₀ : ContDiffOn ℝ ∞ τ₀ J
  /-- `F > 0` on `J`. -/
  F_pos : ∀ R ∈ J, 0 < F R
  /-- `F′ ≥ 0` on `J`. -/
  deriv_F_nonneg : ∀ R ∈ J, 0 ≤ deriv F R
  /-- `τ₀′ ≥ 0` on `J`. -/
  deriv_τ₀_nonneg : ∀ R ∈ J, 0 ≤ deriv τ₀ R
  /-- `F′ + τ₀′ > 0` on `J`. -/
  deriv_add_pos : ∀ R ∈ J, 0 < deriv F R + deriv τ₀ R

namespace ParabolicData

variable (P : ParabolicData) {τ R : ℝ}

/-- The set `R ∈ J`, `τ < τ₀(R)` of the co-ordinates before the collapse. -/
def S : Set (ℝ × ℝ) := {p | p.2 ∈ P.J ∧ p.1 < P.τ₀ p.2}

/-- The set of the co-ordinates before the collapse is open. -/
theorem isOpen_S : IsOpen P.S := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => p.1 - P.τ₀ p.2) (Prod.snd ⁻¹' P.J) :=
    continuous_fst.continuousOn.sub
      (P.contDiffOn_τ₀.continuousOn.comp continuous_snd.continuousOn fun _ hp => hp)
  have h := hc.isOpen_inter_preimage (P.isOpen_J.preimage continuous_snd) (isOpen_Iio (a := 0))
  convert h using 1
  ext p
  simp [S, sub_neg]

/-- `F` is differentiable on `J`. -/
theorem hasDerivAt_F (hR : R ∈ P.J) : HasDerivAt P.F (deriv P.F R) R :=
  ((P.contDiffOn_F.differentiableOn (by simp)).differentiableAt
    (P.isOpen_J.mem_nhds hR)).hasDerivAt

/-- `τ₀` is differentiable on `J`. -/
theorem hasDerivAt_τ₀ (hR : R ∈ P.J) : HasDerivAt P.τ₀ (deriv P.τ₀ R) R :=
  ((P.contDiffOn_τ₀.differentiableOn (by simp)).differentiableAt
    (P.isOpen_J.mem_nhds hR)).hasDerivAt

/-- `ṙ = −3F(τ₀ − τ)/(2r²)`. -/
theorem partialT_radius (hp : (τ, R) ∈ P.S) :
    partialT (parabolicRadius P.F P.τ₀) τ R =
      -3 * P.F R * (P.τ₀ R - τ) / (2 * parabolicRadius P.F P.τ₀ τ R ^ 2) :=
  (hasDerivAt_parabolicRadius_time (P.F_pos _ hp.1) hp.2).deriv

/-- `r′ = 3(F′(τ₀ − τ)² + 2F(τ₀ − τ)τ₀′)/(4r²)`. -/
theorem partialR_radius (hp : (τ, R) ∈ P.S) :
    partialR (parabolicRadius P.F P.τ₀) τ R =
      3 * (deriv P.F R * (P.τ₀ R - τ) ^ 2 + 2 * P.F R * (P.τ₀ R - τ) * deriv P.τ₀ R) /
        (4 * parabolicRadius P.F P.τ₀ τ R ^ 2) :=
  (hasDerivAt_parabolicRadius_radius (P.hasDerivAt_F hp.1) (P.hasDerivAt_τ₀ hp.1)
    (P.F_pos _ hp.1) hp.2).deriv

/-- No shell crossing before the collapse: `r′ > 0`. -/
theorem partialR_radius_pos (hp : (τ, R) ∈ P.S) :
    0 < partialR (parabolicRadius P.F P.τ₀) τ R := by
  rw [P.partialR_radius hp]
  have hu : 0 < P.τ₀ R - τ := sub_pos.mpr hp.2
  have hF := P.F_pos _ hp.1
  have h1 := P.deriv_F_nonneg _ hp.1
  have h2 := P.deriv_τ₀_nonneg _ hp.1
  have h3 := P.deriv_add_pos _ hp.1
  have hr := parabolicRadius_pos (τ₀ := P.τ₀) hF hp.2
  refine div_pos (mul_pos (by norm_num) ?_) (by positivity)
  rcases lt_or_eq_of_le h1 with h1 | h1
  · have : 0 < deriv P.F R * (P.τ₀ R - τ) ^ 2 := by positivity
    have : 0 ≤ 2 * P.F R * (P.τ₀ R - τ) * deriv P.τ₀ R := by positivity
    linarith
  · have h4 : 0 < deriv P.τ₀ R := by linarith
    have : 0 < 2 * P.F R * (P.τ₀ R - τ) * deriv P.τ₀ R := by positivity
    rw [← h1]
    linarith

/-- `r̈ = −F/(2r²)`. -/
theorem partialT_partialT_radius (hp : (τ, R) ∈ P.S) :
    partialT (partialT (parabolicRadius P.F P.τ₀)) τ R =
      -P.F R / (2 * parabolicRadius P.F P.τ₀ τ R ^ 2) := by
  have hc : (fun s => partialT (parabolicRadius P.F P.τ₀) s R) =ᶠ[𝓝 τ]
      fun s => -3 * P.F R * (P.τ₀ R - s) / (2 * parabolicRadius P.F P.τ₀ s R ^ 2) := by
    filter_upwards [isOpen_Iio.mem_nhds hp.2] with s hs using P.partialT_radius ⟨hp.1, hs⟩
  change deriv (fun s => partialT (parabolicRadius P.F P.τ₀) s R) τ = _
  rw [hc.deriv_eq]
  exact (hasDerivAt_parabolicRate (P.F_pos _ hp.1) hp.2).deriv

/-- The parabolic radius is smooth on `S`. -/
theorem contDiffOn_radius : ContDiffOn ℝ ∞ (Function.uncurry (parabolicRadius P.F P.τ₀)) P.S := by
  have hF : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => P.F p.2) P.S :=
    P.contDiffOn_F.comp contDiff_snd.contDiffOn fun _ hp => hp.1
  have hτ : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => P.τ₀ p.2) P.S :=
    P.contDiffOn_τ₀.comp contDiff_snd.contDiffOn fun _ hp => hp.1
  have hX : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => 9 * P.F p.2 * (P.τ₀ p.2 - p.1) ^ 2 / 4) P.S :=
    ((contDiffOn_const.mul hF).mul ((hτ.sub contDiff_fst.contDiffOn).pow 2)).div_const 4
  refine hX.rpow_const_of_ne fun p hp => ?_
  have : 0 < P.τ₀ p.2 - p.1 := sub_pos.mpr hp.2
  have := P.F_pos _ hp.1
  positivity

/-- **The parabolic collapse as data of the comoving frame**, with `r` the parabolic radius and
`e^λ = r′²`. -/
def toData : Data where
  S := P.S
  r := parabolicRadius P.F P.τ₀
  lam τ R := Real.log (partialR (parabolicRadius P.F P.τ₀) τ R ^ 2)
  isOpen_S := P.isOpen_S
  contDiffOn_r := P.contDiffOn_radius
  contDiffOn_lam := ((contDiffOn_partialR P.isOpen_S P.contDiffOn_radius).pow 2).log
    fun p hp => (pow_pos (P.partialR_radius_pos (τ := p.1) (R := p.2) hp) 2).ne'
  r_pos _ hp := parabolicRadius_pos (P.F_pos _ hp.1) hp.2
  partialR_r_pos p hp := P.partialR_radius_pos (τ := p.1) (R := p.2) hp

/-- The co-ordinates of the frame of a parabolic collapse. -/
@[simp] theorem toData_S : P.toData.S = P.S := rfl

/-- The radius of the frame of a parabolic collapse. -/
@[simp] theorem toData_r : P.toData.r = parabolicRadius P.F P.τ₀ := rfl

/-- The exponent `λ = log r′²` of the frame of a parabolic collapse. -/
theorem toData_lam (τ R : ℝ) :
    P.toData.lam τ R = Real.log (partialR (parabolicRadius P.F P.τ₀) τ R ^ 2) := rfl

/-- The density `ε = F′/(κ r′ r²)` of the parabolic collapse. -/
def density (κ τ R : ℝ) : ℝ :=
  deriv P.F R / (κ * (partialR (parabolicRadius P.F P.τ₀) τ R * parabolicRadius P.F P.τ₀ τ R ^ 2))

/-- The density of the parabolic collapse is `κε = 4F′/(3(τ₀ − τ)(F′(τ₀ − τ) + 2Fτ₀′))`. -/
theorem density_eq {κ : ℝ} (hκ : κ ≠ 0) (hp : (τ, R) ∈ P.S) :
    κ * P.density κ τ R = 4 * deriv P.F R /
      (3 * (P.τ₀ R - τ) * (deriv P.F R * (P.τ₀ R - τ) + 2 * P.F R * deriv P.τ₀ R)) := by
  have hr := (parabolicRadius_pos (τ₀ := P.τ₀) (P.F_pos _ hp.1) hp.2).ne'
  have hR := (P.partialR_radius_pos hp).ne'
  have hu : P.τ₀ R - τ ≠ 0 := (sub_pos.mpr hp.2).ne'
  have hR' := hR
  rw [P.partialR_radius hp] at hR'
  have hw : deriv P.F R * (P.τ₀ R - τ) + 2 * P.F R * deriv P.τ₀ R ≠ 0 := by
    intro h0
    apply hR'
    have : deriv P.F R * (P.τ₀ R - τ) ^ 2 + 2 * P.F R * (P.τ₀ R - τ) * deriv P.τ₀ R =
        (P.τ₀ R - τ) * (deriv P.F R * (P.τ₀ R - τ) + 2 * P.F R * deriv P.τ₀ R) := by ring
    rw [this, h0]
    simp
  rw [density, P.partialR_radius hp]
  field_simp

end ParabolicData

/-- **The parabolic solution** (Landau–Lifshitz, (103.8)): for `κ ≠ 0` the parabolic collapse
`r = (9F(τ₀ − τ)²/4)^{1/3}`, `e^λ = r′²` with the density `ε = F′/(κr′r²)` solves the equations of
the dust sphere with `f = 0`. -/
theorem solution_parabolic (P : ParabolicData) {κ : ℝ} (hκ : κ ≠ 0) :
    Equations P.toData κ (P.density κ) 0 P.F where
  exp_lam τ R hp := by
    rw [ParabolicData.toData_lam, ParabolicData.toData_r, Real.exp_log
      (pow_pos (P.partialR_radius_pos hp) 2), Pi.zero_apply, add_zero, div_one]
  energy τ R hp := by
    have hp' : (τ, R) ∈ P.S := hp
    have hF := P.F_pos _ hp'.1
    have hr := parabolicRadius_pos (τ₀ := P.τ₀) hF hp'.2
    have hu : 0 < P.τ₀ R - τ := sub_pos.mpr hp'.2
    have hFe : P.F R = 4 * parabolicRadius P.F P.τ₀ τ R ^ 3 / (9 * (P.τ₀ R - τ) ^ 2) := by
      rw [parabolicRadius_cube hF.le]
      field_simp
    rw [ParabolicData.toData_r, P.partialT_radius hp', Pi.zero_apply, zero_add, hFe]
    field_simp
    ring
  accel τ R hp := by
    rw [ParabolicData.toData_r]
    exact P.partialT_partialT_radius hp
  density τ R hp := by
    have hr := (parabolicRadius_pos (τ₀ := P.τ₀) (P.F_pos _ hp.1) hp.2).ne'
    have hR := (P.partialR_radius_pos hp).ne'
    rw [ParabolicData.toData_r, ParabolicData.density]
    field_simp

/-- **The parabolic collapse satisfies the Einstein equations** with the dust. -/
theorem isEinstein_parabolic (P : ParabolicData) {κ : ℝ} (hκ : κ ≠ 0) :
    (metric P.toData).IsEinstein κ 0 (dustStress (P.density κ)) :=
  (solution_parabolic P hκ).isEinstein


/-! ### The elliptic and hyperbolic solutions in parametric form -/

/-- The radius `r = F/(2(−f)) (1 − cos η)` of the elliptic solution `f < 0`, in the parameter `η`
(Landau–Lifshitz, (103.9)). -/
def ellipticRadius (f F η : ℝ) : ℝ := F / (2 * -f) * (1 - Real.cos η)

/-- The time `τ = τ₀ − F/(2(−f)^{3/2}) (η − sin η)` of the elliptic solution (Landau–Lifshitz,
(103.9)). -/
def ellipticTime (f F τ₀ η : ℝ) : ℝ := τ₀ - F / (2 * -f * Real.sqrt (-f)) * (η - Real.sin η)

/-- The radius `r = F/(2f) (cosh η − 1)` of the hyperbolic solution `f > 0`, in the parameter `η`
(Landau–Lifshitz, (103.10)). -/
def hyperbolicRadius (f F η : ℝ) : ℝ := F / (2 * f) * (Real.cosh η - 1)

/-- The time `τ = τ₀ − F/(2f^{3/2}) (sinh η − η)` of the hyperbolic solution (Landau–Lifshitz,
(103.10)). -/
def hyperbolicTime (f F τ₀ η : ℝ) : ℝ := τ₀ - F / (2 * f * Real.sqrt f) * (Real.sinh η - η)

/-- `dr/dη = F/(2(−f)) sin η`. -/
theorem hasDerivAt_ellipticRadius (f F η : ℝ) :
    HasDerivAt (ellipticRadius f F) (F / (2 * -f) * Real.sin η) η := by
  have := ((Real.hasDerivAt_cos η).const_sub 1).const_mul (F / (2 * -f))
  exact this.congr_deriv (by ring)

/-- `dτ/dη = −F/(2(−f)^{3/2}) (1 − cos η)`. -/
theorem hasDerivAt_ellipticTime (f F τ₀ η : ℝ) :
    HasDerivAt (ellipticTime f F τ₀) (-(F / (2 * -f * Real.sqrt (-f))) * (1 - Real.cos η)) η := by
  have := (((hasDerivAt_id η).sub (Real.hasDerivAt_sin η)).const_mul
    (F / (2 * -f * Real.sqrt (-f)))).const_sub τ₀
  exact this.congr_deriv (by simp)

/-- `dr/dη = F/(2f) sinh η`. -/
theorem hasDerivAt_hyperbolicRadius (f F η : ℝ) :
    HasDerivAt (hyperbolicRadius f F) (F / (2 * f) * Real.sinh η) η :=
  ((Real.hasDerivAt_cosh η).sub_const 1).const_mul (F / (2 * f))

/-- `dτ/dη = −F/(2f^{3/2}) (cosh η − 1)`. -/
theorem hasDerivAt_hyperbolicTime (f F τ₀ η : ℝ) :
    HasDerivAt (hyperbolicTime f F τ₀) (-(F / (2 * f * Real.sqrt f)) * (Real.cosh η - 1)) η := by
  have := (((Real.hasDerivAt_sinh η).sub (hasDerivAt_id η)).const_mul
    (F / (2 * f * Real.sqrt f))).const_sub τ₀
  exact this.congr_deriv (by simp)

/-- The derivative of the elliptic radius as a function. -/
theorem deriv_ellipticRadius (f F : ℝ) :
    deriv (ellipticRadius f F) = fun η => F / (2 * -f) * Real.sin η :=
  funext fun η => (hasDerivAt_ellipticRadius f F η).deriv

/-- The derivative of the elliptic time as a function. -/
theorem deriv_ellipticTime (f F τ₀ : ℝ) :
    deriv (ellipticTime f F τ₀) = fun η => -(F / (2 * -f * Real.sqrt (-f))) * (1 - Real.cos η) :=
  funext fun η => (hasDerivAt_ellipticTime f F τ₀ η).deriv

/-- The derivative of the hyperbolic radius as a function. -/
theorem deriv_hyperbolicRadius (f F : ℝ) :
    deriv (hyperbolicRadius f F) = fun η => F / (2 * f) * Real.sinh η :=
  funext fun η => (hasDerivAt_hyperbolicRadius f F η).deriv

/-- The derivative of the hyperbolic time as a function. -/
theorem deriv_hyperbolicTime (f F τ₀ : ℝ) :
    deriv (hyperbolicTime f F τ₀) = fun η => -(F / (2 * f * Real.sqrt f)) * (Real.cosh η - 1) :=
  funext fun η => (hasDerivAt_hyperbolicTime f F τ₀ η).deriv

/-- **The elliptic solution** (Landau–Lifshitz, (103.9)): for `f < 0`, `F > 0` and
`0 < η < 2π`, the curve `η ↦ (τ(η), r(η))` has `r > 0` and `dτ/dη < 0`, and the velocity
`ṙ = (dr/dη)/(dτ/dη)` and the acceleration `r̈ = (r_ηη τ_η − r_η τ_ηη)/τ_η³` satisfy
`ṙ² = f + F/r` and `r̈ = −F/(2r²)`. -/
theorem solution_elliptic {f F : ℝ} (hf : f < 0) (hF : 0 < F) (τ₀ : ℝ) {η : ℝ} (h0 : 0 < η)
    (h2 : η < 2 * Real.pi) :
    0 < ellipticRadius f F η ∧ deriv (ellipticTime f F τ₀) η < 0 ∧
      (deriv (ellipticRadius f F) η / deriv (ellipticTime f F τ₀) η) ^ 2 =
        f + F / ellipticRadius f F η ∧
      (deriv (deriv (ellipticRadius f F)) η * deriv (ellipticTime f F τ₀) η -
          deriv (ellipticRadius f F) η * deriv (deriv (ellipticTime f F τ₀)) η) /
          deriv (ellipticTime f F τ₀) η ^ 3 = -F / (2 * ellipticRadius f F η ^ 2) := by
  obtain ⟨q, hq, rfl⟩ : ∃ q, 0 < q ∧ f = -q ^ 2 :=
    ⟨Real.sqrt (-f), Real.sqrt_pos.mpr (by linarith), by
      rw [Real.sq_sqrt (by linarith)]; ring⟩
  have hsq : Real.sqrt (-(-q ^ 2)) = q := by rw [neg_neg, Real.sqrt_sq hq.le]
  have hsq2 : Real.sqrt (q ^ 2) = q := Real.sqrt_sq hq.le
  have hc : Real.cos η < 1 := lt_of_le_of_ne (Real.cos_le_one η) fun h => by
    have := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith) h2).mp h
    linarith
  have hc' : 0 < 1 - Real.cos η := by linarith
  have hd2 : deriv (deriv (ellipticRadius (-q ^ 2) F)) η = F / (2 * q ^ 2) * Real.cos η := by
    rw [deriv_ellipticRadius]
    have := (Real.hasDerivAt_sin η).const_mul (F / (2 * -(-q ^ 2)))
    rw [this.deriv, neg_neg]
  have hd2' : deriv (deriv (ellipticTime (-q ^ 2) F τ₀)) η =
      -(F / (2 * q ^ 2 * q)) * Real.sin η := by
    rw [deriv_ellipticTime]
    have := ((Real.hasDerivAt_cos η).const_sub 1).const_mul
      (-(F / (2 * -(-q ^ 2) * Real.sqrt (-(-q ^ 2)))))
    rw [this.deriv, hsq, neg_neg]
    ring
  have hs : Real.sin η ^ 2 = (1 - Real.cos η) * (1 + Real.cos η) := by
    linear_combination Real.sin_sq_add_cos_sq η
  have hN : F / (2 * q ^ 2) * Real.cos η * (-(F / (2 * q ^ 2 * q)) * (1 - Real.cos η)) -
      F / (2 * q ^ 2) * Real.sin η * (-(F / (2 * q ^ 2 * q)) * Real.sin η) =
      F / (2 * q ^ 2) * (F / (2 * q ^ 2 * q)) * (1 - Real.cos η) := by
    linear_combination F / (2 * q ^ 2) * (F / (2 * q ^ 2 * q)) * Real.sin_sq_add_cos_sq η
  rw [hd2, hd2', deriv_ellipticRadius, deriv_ellipticTime]
  simp only [ellipticRadius, neg_neg, hsq2]
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · have : 0 < F / (2 * q ^ 2 * q) * (1 - Real.cos η) := by positivity
    linarith
  · rw [div_pow, mul_pow, hs]
    field_simp
    ring
  · rw [hN]
    field_simp

/-- **The hyperbolic solution** (Landau–Lifshitz, (103.10)): for `f > 0`, `F > 0` and `η > 0`,
the curve `η ↦ (τ(η), r(η))` has `r > 0` and `dτ/dη < 0`, and `ṙ = (dr/dη)/(dτ/dη)`,
`r̈ = (r_ηη τ_η − r_η τ_ηη)/τ_η³` satisfy `ṙ² = f + F/r` and `r̈ = −F/(2r²)`. -/
theorem solution_hyperbolic {f F : ℝ} (hf : 0 < f) (hF : 0 < F) (τ₀ : ℝ) {η : ℝ} (h0 : 0 < η) :
    0 < hyperbolicRadius f F η ∧ deriv (hyperbolicTime f F τ₀) η < 0 ∧
      (deriv (hyperbolicRadius f F) η / deriv (hyperbolicTime f F τ₀) η) ^ 2 =
        f + F / hyperbolicRadius f F η ∧
      (deriv (deriv (hyperbolicRadius f F)) η * deriv (hyperbolicTime f F τ₀) η -
          deriv (hyperbolicRadius f F) η * deriv (deriv (hyperbolicTime f F τ₀)) η) /
          deriv (hyperbolicTime f F τ₀) η ^ 3 = -F / (2 * hyperbolicRadius f F η ^ 2) := by
  obtain ⟨q, hq, rfl⟩ : ∃ q, 0 < q ∧ f = q ^ 2 :=
    ⟨Real.sqrt f, Real.sqrt_pos.mpr hf, (Real.sq_sqrt hf.le).symm⟩
  have hsq : Real.sqrt (q ^ 2) = q := Real.sqrt_sq hq.le
  have hc' : 0 < Real.cosh η - 1 := by linarith [Real.one_lt_cosh.mpr h0.ne']
  have hd2 : deriv (deriv (hyperbolicRadius (q ^ 2) F)) η = F / (2 * q ^ 2) * Real.cosh η := by
    rw [deriv_hyperbolicRadius]
    exact ((Real.hasDerivAt_sinh η).const_mul (F / (2 * q ^ 2))).deriv
  have hd2' : deriv (deriv (hyperbolicTime (q ^ 2) F τ₀)) η =
      -(F / (2 * q ^ 2 * q)) * Real.sinh η := by
    rw [deriv_hyperbolicTime]
    have := ((Real.hasDerivAt_cosh η).sub_const 1).const_mul
      (-(F / (2 * q ^ 2 * Real.sqrt (q ^ 2))))
    rw [this.deriv, hsq]
  have hs : Real.sinh η ^ 2 = (Real.cosh η - 1) * (Real.cosh η + 1) := by
    linear_combination -Real.cosh_sq_sub_sinh_sq η
  have hN : F / (2 * q ^ 2) * Real.cosh η * (-(F / (2 * q ^ 2 * q)) * (Real.cosh η - 1)) -
      F / (2 * q ^ 2) * Real.sinh η * (-(F / (2 * q ^ 2 * q)) * Real.sinh η) =
      F / (2 * q ^ 2) * (F / (2 * q ^ 2 * q)) * (Real.cosh η - 1) := by
    linear_combination -(F / (2 * q ^ 2) * (F / (2 * q ^ 2 * q))) * Real.cosh_sq_sub_sinh_sq η
  rw [hd2, hd2', deriv_hyperbolicRadius, deriv_hyperbolicTime]
  simp only [hyperbolicRadius, hsq]
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · have : 0 < F / (2 * q ^ 2 * q) * (Real.cosh η - 1) := by positivity
    linarith
  · rw [div_pow, mul_pow, hs]
    field_simp
    ring
  · rw [hN]
    field_simp

/-- **The elliptic collapse at the finite time `τ₀`**: as `η → 0⁺`, `(τ, r) → (τ₀, 0)`, and
`τ < τ₀` for `η > 0`. -/
theorem tendsto_elliptic (f F τ₀ : ℝ) :
    Tendsto (fun η => (ellipticTime f F τ₀ η, ellipticRadius f F η)) (𝓝[>] 0) (𝓝 (τ₀, 0)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds ?_
  have hc : Continuous fun η => (ellipticTime f F τ₀ η, ellipticRadius f F η) := by
    unfold ellipticTime ellipticRadius
    fun_prop
  simpa [ellipticTime, ellipticRadius] using hc.tendsto 0

/-- The elliptic curve lies before the collapse: `τ < τ₀` for `η > 0`. -/
theorem ellipticTime_lt {f F : ℝ} (hf : f < 0) (hF : 0 < F) (τ₀ : ℝ) {η : ℝ} (h0 : 0 < η) :
    ellipticTime f F τ₀ η < τ₀ := by
  have h1 : 0 < η - Real.sin η := sub_pos.mpr (Real.sin_lt h0)
  have h2 : 0 < Real.sqrt (-f) := Real.sqrt_pos.mpr (by linarith)
  have h3 : 0 < -f := by linarith
  have : 0 < F / (2 * -f * Real.sqrt (-f)) * (η - Real.sin η) := by positivity
  unfold ellipticTime
  linarith

/-- **The hyperbolic collapse at the finite time `τ₀`**: as `η → 0⁺`, `(τ, r) → (τ₀, 0)`, and
`τ < τ₀` for `η > 0`. -/
theorem tendsto_hyperbolic (f F τ₀ : ℝ) :
    Tendsto (fun η => (hyperbolicTime f F τ₀ η, hyperbolicRadius f F η)) (𝓝[>] 0)
      (𝓝 (τ₀, 0)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds ?_
  have hc : Continuous fun η => (hyperbolicTime f F τ₀ η, hyperbolicRadius f F η) := by
    unfold hyperbolicTime hyperbolicRadius
    fun_prop
  simpa [hyperbolicTime, hyperbolicRadius] using hc.tendsto 0

/-- The hyperbolic curve lies before the collapse: `τ < τ₀` for `η > 0`. -/
theorem hyperbolicTime_lt {f F : ℝ} (hf : 0 < f) (hF : 0 < F) (τ₀ : ℝ) {η : ℝ} (h0 : 0 < η) :
    hyperbolicTime f F τ₀ η < τ₀ := by
  have h1 : 0 < Real.sinh η - η := sub_pos.mpr (Real.self_lt_sinh_iff.mpr h0)
  have h2 : 0 < Real.sqrt f := Real.sqrt_pos.mpr hf
  have : 0 < F / (2 * f * Real.sqrt f) * (Real.sinh η - η) := by positivity
  unfold hyperbolicTime
  linarith


/-! ### The exterior of the dust: the Schwarzschild field -/

/-- The shift `v − τ = r − 2√(r_g r) + 2r_g log(1 + √(r/r_g))` from the proper time of the
freely falling shells to the advanced time `v` of Eddington and Finkelstein. -/
def eddingtonShift (rg r : ℝ) : ℝ :=
  r - 2 * Real.sqrt rg * Real.sqrt r + 2 * rg * Real.log (1 + Real.sqrt r / Real.sqrt rg)

/-- `d(v − τ)/dr = √r/(√r + √r_g) = 1/(1 + √(r_g/r))`, regular through the horizon. -/
theorem hasDerivAt_eddingtonShift {rg r : ℝ} (hrg : 0 < rg) (hr : 0 < r) :
    HasDerivAt (eddingtonShift rg) (Real.sqrt r / (Real.sqrt r + Real.sqrt rg)) r := by
  have hs := Real.sqrt_pos.mpr hr
  have hg := Real.sqrt_pos.mpr hrg
  have h1 := Real.hasDerivAt_sqrt hr.ne'
  have hl : 0 < 1 + Real.sqrt r / Real.sqrt rg := by positivity
  have h2 := ((h1.div_const (Real.sqrt rg)).const_add 1).log hl.ne'
  have h3 := ((hasDerivAt_id r).sub (h1.const_mul (2 * Real.sqrt rg))).add
    (h2.const_mul (2 * rg))
  refine h3.congr_deriv ?_
  have kg := (Real.mul_self_sqrt hrg.le).symm
  generalize Real.sqrt rg = g at *
  generalize Real.sqrt r = q at *
  subst kg
  have hqg : q + g ≠ 0 := by positivity
  field_simp
  ring

variable (D) in
/-- The map `(τ, R, θ, φ) ↦ (v, r, θ, φ)` from the comoving frame to the ingoing
Eddington–Finkelstein co-ordinates of a field with the gravitational radius `r_g`, with
`r = r(τ, R)` and `v = τ + r − 2√(r_g r) + 2r_g log(1 + √(r/r_g))`. -/
def eddingtonMap (rg : ℝ) (x : E) : E :=
  ![x 0 + eddingtonShift rg (D.r (x 0) (x 1)), D.r (x 0) (x 1), x 2, x 3]

variable (D) in
/-- The Jacobian `w ↦ (w⁰ + c dr(w), dr(w), w², w³)` of `eddingtonMap`, with `dr(w) = ṙw⁰ + r′w¹`
and `c = √r/(√r + √r_g)`. -/
def eddingtonLinear (rg : ℝ) (x : E) : E →ₗ[ℝ] E where
  toFun v := ![v 0 + Real.sqrt (D.r (x 0) (x 1)) / (Real.sqrt (D.r (x 0) (x 1)) + Real.sqrt rg) *
    along D.r x v, along D.r x v, v 2, v 3]
  map_add' v w := by
    funext i
    fin_cases i <;> simp [along] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> simp [along] <;> ring

variable (D) in
/-- The Jacobian of `eddingtonMap` as a continuous linear map. -/
def eddingtonJacobian (rg : ℝ) (x : E) : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap (eddingtonLinear D rg x)

/-- The value of the Jacobian of `eddingtonMap`. -/
theorem eddingtonJacobian_apply (rg : ℝ) (x v : E) :
    eddingtonJacobian D rg x v = ![v 0 + Real.sqrt (D.r (x 0) (x 1)) /
      (Real.sqrt (D.r (x 0) (x 1)) + Real.sqrt rg) * along D.r x v, along D.r x v, v 2, v 3] :=
  rfl

/-- The map sends the domain into the domain `r > 0`, `0 < θ < π` of the Eddington–Finkelstein
co-ordinates. -/
theorem eddingtonMap_mem (rg : ℝ) (hx : x ∈ domain D) :
    eddingtonMap D rg x ∈ EddingtonFinkelstein.domain :=
  ⟨r_pos_of_mem hx, hx.2.1, hx.2.2⟩

/-- The derivative of `eddingtonMap` at a point of the domain is `eddingtonJacobian`. -/
theorem hasFDerivAt_eddingtonMap {rg : ℝ} (hrg : 0 < rg) (hx : x ∈ domain D) :
    HasFDerivAt (eddingtonMap D rg) (eddingtonJacobian D rg x) x := by
  have hr := hasFDerivAt_lift D.contDiffOn_r hx
  refine hasFDerivAt_pi'' fun i => ?_
  fin_cases i
  · refine ((hasFDerivAt_apply 0 x).add
      ((hasDerivAt_eddingtonShift hrg (r_pos_of_mem hx)).comp_hasFDerivAt x hr)).congr_fderiv ?_
    ext w
    simp [eddingtonJacobian_apply, along]
    ring
  · refine hr.congr_fderiv ?_
    ext w
    simp [eddingtonJacobian_apply, along]
  · refine (hasFDerivAt_apply 2 x).congr_fderiv ?_
    ext w
    simp [eddingtonJacobian_apply]
  · refine (hasFDerivAt_apply 3 x).congr_fderiv ?_
    ext w
    simp [eddingtonJacobian_apply]

/-- The algebra of the pullback: with `r = s²`, `r_g = g²`, `ṙ = −g/s` and `e^λ = r′²`, the
Eddington–Finkelstein form on the Jacobian is the form of the comoving frame. -/
theorem eddington_pullback_algebra {r s g rt rR e θ : ℝ} (hs : 0 < s) (hg : 0 < g)
    (hr : r = s ^ 2) (hrt : rt = -g / s) (he : e = rR ^ 2) (v w : E) :
    -(1 - 2 * (g ^ 2 / 2) / r) * ((v 0 + s / (s + g) * (rt * v 0 + rR * v 1)) *
        (w 0 + s / (s + g) * (rt * w 0 + rR * w 1))) +
      (v 0 + s / (s + g) * (rt * v 0 + rR * v 1)) * (rt * w 0 + rR * w 1) +
      (rt * v 0 + rR * v 1) * (w 0 + s / (s + g) * (rt * w 0 + rR * w 1)) +
      r ^ 2 * (v 2 * w 2) + r ^ 2 * Real.sin θ ^ 2 * (v 3 * w 3) =
    -(v 0 * w 0) + e * (v 1 * w 1) + r ^ 2 * (v 2 * w 2) +
      r ^ 2 * Real.sin θ ^ 2 * (v 3 * w 3) := by
  subst hr hrt he
  have : s + g ≠ 0 := by positivity
  field_simp
  ring

/-- **The exterior is the Schwarzschild field** (Landau–Lifshitz, §§102–103). At a point of the
domain whose shell has `f = 0` and `F = r_g > 0` and falls, `ṙ < 0`, the map `eddingtonMap` pulls
the Schwarzschild metric `−(1 − r_g/r) dv² + 2 dv dr + r² dΩ²` of `EddingtonFinkelstein` (with
`2M = r_g`) back to the metric of the comoving frame, through the horizon `r = r_g`. -/
theorem matching {κ : ℝ} {ε : ℝ → ℝ → ℝ} {f F : ℝ → ℝ} (h : Equations D κ ε f F) {rg : ℝ}
    (hrg : 0 < rg) (hx : x ∈ domain D) (hf : f (x 1) = 0) (hF : F (x 1) = rg)
    (hc : partialT D.r (x 0) (x 1) < 0) (v w : E) :
    EddingtonFinkelstein.form (rg / 2) (eddingtonMap D rg x) (eddingtonJacobian D rg x v)
        (eddingtonJacobian D rg x w) = (metric D).form x v w := by
  have hp := mem_S hx
  have hr := r_pos_of_mem hx
  have hs := Real.sqrt_pos.mpr hr
  obtain ⟨g, hg, rfl⟩ : ∃ g, 0 < g ∧ rg = g ^ 2 :=
    ⟨Real.sqrt rg, Real.sqrt_pos.mpr hrg, (Real.sq_sqrt hrg.le).symm⟩
  have hsg : Real.sqrt (g ^ 2) = g := Real.sqrt_sq hg.le
  have hr2 : D.r (x 0) (x 1) = Real.sqrt (D.r (x 0) (x 1)) ^ 2 := (Real.sq_sqrt hr.le).symm
  have he : Real.exp (D.lam (x 0) (x 1)) = partialR D.r (x 0) (x 1) ^ 2 := by
    rw [h.exp_lam _ _ hp, hf, add_zero, div_one]
  have hrt : partialT D.r (x 0) (x 1) = -g / Real.sqrt (D.r (x 0) (x 1)) := by
    have h1 := h.energy _ _ hp
    rw [hf, hF, zero_add] at h1
    have h2 : (partialT D.r (x 0) (x 1) + g / Real.sqrt (D.r (x 0) (x 1))) *
        (partialT D.r (x 0) (x 1) - g / Real.sqrt (D.r (x 0) (x 1))) = 0 := by
      rw [← sq_sub_sq, h1, div_pow, ← hr2, sub_self]
    have h3 : partialT D.r (x 0) (x 1) - g / Real.sqrt (D.r (x 0) (x 1)) < 0 := by
      have : 0 < g / Real.sqrt (D.r (x 0) (x 1)) := by positivity
      linarith
    have h4 := (mul_eq_zero.mp h2).resolve_right h3.ne
    rw [neg_div]
    linarith
  rw [EddingtonFinkelstein.form_apply, metric_form_apply, eddingtonJacobian_apply,
    eddingtonJacobian_apply, hsg]
  simp only [eddingtonMap, along, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  exact eddington_pullback_algebra hs hg hr2 hrt he v w

/-- **The dust ball matches the exterior field** (Landau–Lifshitz, §103). If `f = 0` and
`F = r_g > 0` on the shells `R > R_b` and the shells fall, then on `R > R_b` the metric of the
comoving frame is the Schwarzschild metric pulled back by `eddingtonMap`, and for `κ ≠ 0` the
density vanishes there: the ball `R ≤ R_b` is surrounded by vacuum with the gravitational radius
`r_g = F(R_b)`. -/
theorem matching_exterior {κ : ℝ} {ε : ℝ → ℝ → ℝ} {f F : ℝ → ℝ} (h : Equations D κ ε f F)
    {rg Rb : ℝ} (hrg : 0 < rg) (hf : ∀ R, Rb < R → f R = 0) (hF : ∀ R, Rb < R → F R = rg)
    (hc : ∀ τ R, (τ, R) ∈ D.S → Rb < R → partialT D.r τ R < 0) (hx : x ∈ domain D)
    (hb : Rb < x 1) :
    (∀ v w, EddingtonFinkelstein.form (rg / 2) (eddingtonMap D rg x) (eddingtonJacobian D rg x v)
        (eddingtonJacobian D rg x w) = (metric D).form x v w) ∧
      (κ ≠ 0 → ε (x 0) (x 1) = 0) := by
  refine ⟨matching h hrg hx (hf _ hb) (hF _ hb) (hc _ _ (mem_S hx) hb), fun hκ => ?_⟩
  have hd : deriv F (x 1) = 0 := by
    have hc' : F =ᶠ[𝓝 (x 1)] fun _ => rg := by
      filter_upwards [isOpen_Ioi.mem_nhds hb] with R hR using hF R hR
    rw [hc'.deriv_eq, deriv_const]
  have h1 := h.density _ _ (mem_S hx)
  rw [hd, zero_div] at h1
  exact (mul_eq_zero.mp h1).resolve_left hκ


/-! ### The co-ordinates of Lemaître and a dust ball -/

namespace ParabolicData

/-- The density of a parabolic collapse is nonnegative for `κ > 0`. -/
theorem density_nonneg (P : ParabolicData) {κ τ R : ℝ} (hκ : 0 < κ) (hp : (τ, R) ∈ P.S) :
    0 ≤ P.density κ τ R := by
  have hr := parabolicRadius_pos (τ₀ := P.τ₀) (P.F_pos _ hp.1) hp.2
  have hR := P.partialR_radius_pos hp
  have := P.deriv_F_nonneg _ hp.1
  unfold density
  positivity

/-- A parabolic collapse falls: `ṙ < 0`. -/
theorem partialT_radius_neg (P : ParabolicData) {τ R : ℝ} (hp : (τ, R) ∈ P.S) :
    partialT (parabolicRadius P.F P.τ₀) τ R < 0 := by
  rw [P.partialT_radius hp]
  have hr := parabolicRadius_pos (τ₀ := P.τ₀) (P.F_pos _ hp.1) hp.2
  have hu : 0 < P.τ₀ R - τ := sub_pos.mpr hp.2
  have := P.F_pos _ hp.1
  have : 0 < 3 * P.F R * (P.τ₀ R - τ) / (2 * parabolicRadius P.F P.τ₀ τ R ^ 2) := by positivity
  rw [neg_mul, neg_mul, neg_div]
  linarith

/-- **The data of Lemaître** (Landau–Lifshitz, §102): the parabolic collapse with `F = r_g`
constant and `τ₀(R) = R` on all shells. -/
def lemaitre (rg : ℝ) (hrg : 0 < rg) : ParabolicData where
  J := univ
  F _ := rg
  τ₀ R := R
  isOpen_J := isOpen_univ
  contDiffOn_F := contDiffOn_const
  contDiffOn_τ₀ := contDiffOn_id
  F_pos _ _ := hrg
  deriv_F_nonneg _ _ := by simp
  deriv_τ₀_nonneg _ _ := by simp
  deriv_add_pos _ _ := by simp

/-- The density of the data of Lemaître vanishes: they are a vacuum. -/
theorem density_lemaitre (rg : ℝ) (hrg : 0 < rg) (κ : ℝ) :
    (lemaitre rg hrg).density κ = fun _ _ => 0 := by
  funext τ R
  simp [density, lemaitre]

/-- The slices of a parabolic collapse are the intervals `τ < τ₀(R)`, hence preconnected: the
hypothesis of `isEinstein_iff` holds. -/
theorem isPreconnected_slice (P : ParabolicData) (R : ℝ) :
    IsPreconnected {τ | (τ, R) ∈ P.toData.S} := by
  by_cases hR : R ∈ P.J
  · have : {τ | (τ, R) ∈ P.toData.S} = Iio (P.τ₀ R) := by
      ext τ
      simp [toData_S, S, hR]
    rw [this]
    exact isPreconnected_Iio
  · have : {τ | (τ, R) ∈ P.toData.S} = ∅ := by
      ext τ
      simp [toData_S, S, hR]
    rw [this]
    exact isPreconnected_empty

/-- **The Schwarzschild field in the co-ordinates of Lemaître is a vacuum solution.** -/
theorem isEinstein_lemaitre (rg : ℝ) (hrg : 0 < rg) {κ : ℝ} (hκ : κ ≠ 0) :
    (metric (lemaitre rg hrg).toData).IsEinstein κ 0 (dustStress fun _ _ => 0) := by
  rw [← density_lemaitre rg hrg κ]
  exact isEinstein_parabolic _ hκ

/-- **A dust ball in parabolic collapse**: `F(R) = r_g σ(R/R_b)` with the smooth transition `σ`
of Mathlib (`σ = 0` for `R ≤ 0`, `σ = 1` for `R ≥ R_b`, nondecreasing) and `τ₀(R) = R`, on the
shells `R > 0`. -/
def dustBall (rg Rb : ℝ) (hrg : 0 < rg) (hRb : 0 < Rb) : ParabolicData where
  J := Ioi 0
  F R := rg * Real.smoothTransition (R / Rb)
  τ₀ R := R
  isOpen_J := isOpen_Ioi
  contDiffOn_F := (contDiff_const.mul (Real.smoothTransition.contDiff.comp
    (contDiff_id.div_const Rb))).contDiffOn
  contDiffOn_τ₀ := contDiffOn_id
  F_pos _ hR := mul_pos hrg (Real.smoothTransition.pos_of_pos (div_pos hR hRb))
  deriv_F_nonneg _ _ := Monotone.deriv_nonneg ((Real.smoothTransition.monotone.comp
    fun _ _ h => div_le_div_of_nonneg_right h hRb.le).const_mul hrg.le)
  deriv_τ₀_nonneg _ _ := by simp
  deriv_add_pos R _ := by
    have : 0 ≤ deriv (fun R => rg * Real.smoothTransition (R / Rb)) R :=
      Monotone.deriv_nonneg ((Real.smoothTransition.monotone.comp
        fun _ _ h => div_le_div_of_nonneg_right h hRb.le).const_mul hrg.le)
    simp only [deriv_id'']
    linarith

/-- Outside the ball the function `F` is the gravitational radius: `F(R) = r_g` for `R ≥ R_b`. -/
theorem dustBall_F {rg Rb : ℝ} (hrg : 0 < rg) (hRb : 0 < Rb) {R : ℝ} (hR : Rb ≤ R) :
    (dustBall rg Rb hrg hRb).F R = rg := by
  change rg * Real.smoothTransition (R / Rb) = rg
  rw [Real.smoothTransition.one_of_one_le ((one_le_div hRb).mpr hR), mul_one]

end ParabolicData

/-- The radius `r = (9r_g(R − τ)²/4)^{1/3} = (3(R − τ)/2)^{2/3} r_g^{1/3}` of the co-ordinates of
Lemaître (Landau–Lifshitz, (102.2)). -/
def lemaitreRadius (rg τ R : ℝ) : ℝ := parabolicRadius (fun _ => rg) id τ R

/-- **The Schwarzschild metric in the co-ordinates of Lemaître** (Landau–Lifshitz, (102.3)):
`ds² = −dτ² + (r_g/r) dR² + r² dΩ²` with `r = lemaitreRadius r_g τ R`. -/
def lemaitreForm (rg : ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  diagonalForm (fun y => ![-1, rg / lemaitreRadius rg (y 0) (y 1),
    lemaitreRadius rg (y 0) (y 1) ^ 2, lemaitreRadius rg (y 0) (y 1) ^ 2 * Real.sin (y 2) ^ 2]) x

/-- **A parabolic collapse with `F = r_g` and `τ₀(R) = R` near a shell is the Schwarzschild field
in the co-ordinates of Lemaître** there (Landau–Lifshitz, (102.3)): `e^λ = r′² = r_g/r`. -/
theorem lemaitre_eq (P : ParabolicData) {rg : ℝ} (hx : x ∈ domain P.toData)
    (hF : P.F (x 1) = rg) (hF' : deriv P.F (x 1) = 0) (hτ : P.τ₀ (x 1) = x 1)
    (hτ' : deriv P.τ₀ (x 1) = 1) : (metric P.toData).form x = lemaitreForm rg x := by
  have hp : (x 0, x 1) ∈ P.S := mem_S hx
  have hrg : 0 < rg := hF ▸ P.F_pos _ hp.1
  have hrad : parabolicRadius P.F P.τ₀ (x 0) (x 1) = lemaitreRadius rg (x 0) (x 1) := by
    simp only [lemaitreRadius, parabolicRadius, hF, hτ, id]
  have hL := parabolicRadius_pos (τ₀ := P.τ₀) (P.F_pos _ hp.1) hp.2
  rw [hrad] at hL
  have hu : 0 < x 1 - x 0 := by
    have := hp.2
    rw [hτ] at this
    linarith
  have hcube : lemaitreRadius rg (x 0) (x 1) ^ 3 = 9 * rg * (x 1 - x 0) ^ 2 / 4 :=
    parabolicRadius_cube hrg.le
  have hR := P.partialR_radius hp
  rw [hF', hτ', hF, hτ, hrad] at hR
  have hcoef : partialR (parabolicRadius P.F P.τ₀) (x 0) (x 1) ^ 2 =
      rg / lemaitreRadius rg (x 0) (x 1) := by
    rw [hR]
    calc (3 * (0 * (x 1 - x 0) ^ 2 + 2 * rg * (x 1 - x 0) * 1) /
          (4 * lemaitreRadius rg (x 0) (x 1) ^ 2)) ^ 2 =
        rg * (9 * rg * (x 1 - x 0) ^ 2 / 4) / lemaitreRadius rg (x 0) (x 1) ^ 4 := by
          field_simp
          ring
      _ = rg * lemaitreRadius rg (x 0) (x 1) ^ 3 / lemaitreRadius rg (x 0) (x 1) ^ 4 := by
          rw [hcube]
      _ = rg / lemaitreRadius rg (x 0) (x 1) := by
          field_simp
  ext v w
  rw [metric_form_apply, lemaitreForm, diagonalForm_apply, sum_four, ParabolicData.toData_lam,
    ParabolicData.toData_r, Real.exp_log (pow_pos (P.partialR_radius_pos hp) 2), hcoef, hrad]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- **The dust ball is surrounded by the Schwarzschild field.** For the ball
`ParabolicData.dustBall` and `κ ≠ 0`, on the shells `R > R_b` the density vanishes, the metric is
the Schwarzschild metric in the co-ordinates of Lemaître, and it is the pullback of the
Eddington–Finkelstein metric of the gravitational radius `r_g` by `eddingtonMap`; the metric is
smooth across `R = R_b`. -/
theorem dustBall_exterior {rg Rb κ : ℝ} (hrg : 0 < rg) (hRb : 0 < Rb) (hκ : κ ≠ 0)
    (hx : x ∈ domain (ParabolicData.dustBall rg Rb hrg hRb).toData) (hb : Rb < x 1) :
    (ParabolicData.dustBall rg Rb hrg hRb).density κ (x 0) (x 1) = 0 ∧
      (metric (ParabolicData.dustBall rg Rb hrg hRb).toData).form x = lemaitreForm rg x ∧
      ∀ v w, EddingtonFinkelstein.form (rg / 2)
          (eddingtonMap (ParabolicData.dustBall rg Rb hrg hRb).toData rg x)
          (eddingtonJacobian (ParabolicData.dustBall rg Rb hrg hRb).toData rg x v)
          (eddingtonJacobian (ParabolicData.dustBall rg Rb hrg hRb).toData rg x w) =
        (metric (ParabolicData.dustBall rg Rb hrg hRb).toData).form x v w := by
  set P := ParabolicData.dustBall rg Rb hrg hRb
  have h := solution_parabolic P hκ
  have hF : ∀ R, Rb < R → P.F R = rg := fun R hR => ParabolicData.dustBall_F hrg hRb hR.le
  have hm := matching_exterior h hrg (fun _ _ => rfl) hF
    (fun τ R hp _ => P.partialT_radius_neg hp) hx hb
  have hF' : deriv P.F (x 1) = 0 := by
    have hc : P.F =ᶠ[𝓝 (x 1)] fun _ => rg := by
      filter_upwards [isOpen_Ioi.mem_nhds hb] with R hR using hF R hR
    rw [hc.deriv_eq, deriv_const]
  refine ⟨hm.2 hκ, lemaitre_eq P hx (hF _ hb) hF' rfl (by simp [P, ParabolicData.dustBall]),
    hm.1⟩

end ProjectAinos.GeneralRelativity.Tolman
