/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.DiagonalMetric
public import ProjectAinos.SmoothGeometry.Lorentzian.ChristoffelCertificate
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateEinsteinHilbert
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The centrally symmetric field

In the co-ordinates `(t, r, θ, φ) = (x 0, x 1, x 2, x 3)` the centrally symmetric metric of
Landau–Lifshitz §100, (100.1)–(100.2), is
`ds² = −A(t, r) dt² + B(t, r) dr² + r² (dθ² + sin²θ dφ²)`, in the signature `(−+++)` with
`G = c = 1`; Landau–Lifshitz write `A = e^ν`, `B = e^λ`. The data (`Data`) are two positive
smooth functions on a product `I × J` of open sets of times and positive radii; the metric is the
diagonal coordinate metric on the domain `t ∈ I`, `r ∈ J`, `0 < θ < π` (`metric`).

The partial derivatives of a function `f t r` are `partialT f = ∂f/∂t` and
`partialR f = ∂f/∂r`, one-variable derivatives in each argument; the second partials are the
iterates, such as `partialR (partialR A) = A_rr`, and the mixed ones commute
(`partialR_partialT`). The chain rule on the model is `hasFDerivAt_timeRadius`, and
`fderiv_single_zero`, `fderiv_single_one` read `∂_t`, `∂_r` of `f(x⁰, x¹)` as these partials.

* `christoffelOf_eq`: the Christoffel symbols are the table `christoffel` (L&L (100.3)), with
  the nonzero entries `Γ⁰₀₀ = A_t/(2A)`, `Γ⁰₀₁ = A_r/(2A)`, `Γ⁰₁₁ = B_t/(2A)`, `Γ¹₀₀ = A_r/(2B)`,
  `Γ¹₀₁ = B_t/(2B)`, `Γ¹₁₁ = B_r/(2B)`, `Γ¹₂₂ = −r/B`, `Γ¹₃₃ = −r sin²θ/B`,
  `Γ²₁₂ = Γ³₁₃ = 1/r`, `Γ²₃₃ = −sin θ cos θ`, `Γ³₂₃ = cot θ`.
* `ricciOf_eq` and `ricci_zero_zero`, …, `ricci_three_two`: the sixteen components of the Ricci
  tensor; `R₀₁ = B_t/(rB)`, `R₃₃ = sin²θ R₂₂`, and the components off the `(t, r)` block and the
  diagonal vanish.
* `einsteinOf_eq` and `einstein_zero_zero`, …, `einstein_three_two`: the Einstein tensor
  `G_{ik} = R_{ik} − ½ R g_{ik}`, the left-hand sides of (100.4)–(100.6) in covariant form:
  `G₀₀ = A/r² (1 − 1/B + r B_r/B²)`, `G₀₁ = B_t/(rB)`, `G₁₁ = A_r/(rA) − (B − 1)/r²`, `G₂₂`,
  `G₃₃ = sin²θ G₂₂`.
* `einstein_zero_zero_div_add_one_one_div`: `G₀₀/A + G₁₁/B = ∂_r(AB)/(r A B²)`, the combination
  behind Birkhoff's theorem.
* `ricciOf_flat`, `einsteinOf_flat`: flat space in spherical co-ordinates (`Data.flat`,
  `A = B = 1`) has vanishing Ricci and Einstein tensors.
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap Set TopologicalSpace Filter
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.SphericalAnsatz

open SmoothGeometry CoordinateMetric

/-! ### Partial derivatives of functions of `(t, r)` -/

/-- The partial derivative `∂f/∂t` of a function `f t r` of the time and the radius. -/
def partialT (f : ℝ → ℝ → ℝ) (t r : ℝ) : ℝ := deriv (fun s => f s r) t

/-- The partial derivative `∂f/∂r` of a function `f t r` of the time and the radius. -/
def partialR (f : ℝ → ℝ → ℝ) (t r : ℝ) : ℝ := deriv (fun s => f t s) r

variable {S : Set (ℝ × ℝ)} {f : ℝ → ℝ → ℝ}

/-- On an open set where `f` is smooth, `∂f/∂t` is the derivative of `f` along `(1, 0)`. -/
theorem hasDerivAt_uncurry_time (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) S)
    {t r : ℝ} (h : (t, r) ∈ S) :
    HasDerivAt (fun s => f s r) (fderiv ℝ (Function.uncurry f) (t, r) (1, 0)) t := by
  have hd : DifferentiableAt ℝ (Function.uncurry f) (t, r) :=
    (hf.contDiffAt (hS.mem_nhds h)).differentiableAt (by simp)
  exact hd.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t r))

/-- On an open set where `f` is smooth, `∂f/∂r` is the derivative of `f` along `(0, 1)`. -/
theorem hasDerivAt_uncurry_radius (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) S)
    {t r : ℝ} (h : (t, r) ∈ S) :
    HasDerivAt (fun s => f t s) (fderiv ℝ (Function.uncurry f) (t, r) (0, 1)) r := by
  have hd : DifferentiableAt ℝ (Function.uncurry f) (t, r) :=
    (hf.contDiffAt (hS.mem_nhds h)).differentiableAt (by simp)
  exact hd.hasFDerivAt.comp_hasDerivAt r ((hasDerivAt_const r t).prodMk (hasDerivAt_id r))

/-- `∂f/∂t` is the Fréchet derivative of `f` along `(1, 0)` where `f` is smooth. -/
theorem partialT_eq_fderiv (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) S)
    {t r : ℝ} (h : (t, r) ∈ S) :
    partialT f t r = fderiv ℝ (Function.uncurry f) (t, r) (1, 0) :=
  (hasDerivAt_uncurry_time hS hf h).deriv

/-- `∂f/∂r` is the Fréchet derivative of `f` along `(0, 1)` where `f` is smooth. -/
theorem partialR_eq_fderiv (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) S)
    {t r : ℝ} (h : (t, r) ∈ S) :
    partialR f t r = fderiv ℝ (Function.uncurry f) (t, r) (0, 1) :=
  (hasDerivAt_uncurry_radius hS hf h).deriv

/-- `t ↦ f(t, r)` has the derivative `∂f/∂t` where `f` is smooth. -/
theorem hasDerivAt_partialT (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) S)
    {t r : ℝ} (h : (t, r) ∈ S) : HasDerivAt (fun s => f s r) (partialT f t r) t := by
  rw [partialT_eq_fderiv hS hf h]
  exact hasDerivAt_uncurry_time hS hf h

/-- `r ↦ f(t, r)` has the derivative `∂f/∂r` where `f` is smooth. -/
theorem hasDerivAt_partialR (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) S)
    {t r : ℝ} (h : (t, r) ∈ S) : HasDerivAt (fun s => f t s) (partialR f t r) r := by
  rw [partialR_eq_fderiv hS hf h]
  exact hasDerivAt_uncurry_radius hS hf h

/-- `∂f/∂t` is smooth on an open set where `f` is. -/
theorem contDiffOn_partialT (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) S) :
    ContDiffOn ℝ ∞ (Function.uncurry (partialT f)) S := by
  refine ((hf.fderiv_of_isOpen hS (by simp)).clm_apply
    (contDiffOn_const (c := ((1 : ℝ), (0 : ℝ))))).congr fun p hp => ?_
  obtain ⟨t, r⟩ := p
  exact partialT_eq_fderiv hS hf hp

/-- `∂f/∂r` is smooth on an open set where `f` is. -/
theorem contDiffOn_partialR (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) S) :
    ContDiffOn ℝ ∞ (Function.uncurry (partialR f)) S := by
  refine ((hf.fderiv_of_isOpen hS (by simp)).clm_apply
    (contDiffOn_const (c := ((0 : ℝ), (1 : ℝ))))).congr fun p hp => ?_
  obtain ⟨t, r⟩ := p
  exact partialR_eq_fderiv hS hf hp

/-- **The mixed partial derivatives commute**: `∂_r ∂_t f = ∂_t ∂_r f` where `f` is smooth. -/
theorem partialR_partialT (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) S)
    {t r : ℝ} (h : (t, r) ∈ S) : partialR (partialT f) t r = partialT (partialR f) t r := by
  have hn : S ∈ 𝓝 (t, r) := hS.mem_nhds h
  have e1 : Function.uncurry (partialT f) =ᶠ[𝓝 (t, r)]
      fun p => fderiv ℝ (Function.uncurry f) p (1, 0) := by
    filter_upwards [hn] with p hp
    obtain ⟨a, b⟩ := p
    exact partialT_eq_fderiv hS hf hp
  have e2 : Function.uncurry (partialR f) =ᶠ[𝓝 (t, r)]
      fun p => fderiv ℝ (Function.uncurry f) p (0, 1) := by
    filter_upwards [hn] with p hp
    obtain ⟨a, b⟩ := p
    exact partialR_eq_fderiv hS hf hp
  have hd2 : DifferentiableAt ℝ (fderiv ℝ (Function.uncurry f)) (t, r) :=
    ((hf.fderiv_of_isOpen (m := 1) hS (by simp)).contDiffAt hn).differentiableAt (by simp)
  rw [partialR_eq_fderiv hS (contDiffOn_partialT hS hf) h,
    partialT_eq_fderiv hS (contDiffOn_partialR hS hf) h, e1.fderiv_eq, e2.fderiv_eq,
    fderiv_clm_apply hd2 (differentiableAt_const _),
    fderiv_clm_apply hd2 (differentiableAt_const _)]
  simp only [fderiv_const_apply, comp_zero, zero_add, flip_apply]
  exact (hf.contDiffAt hn).isSymmSndFDerivAt (by simp) _ _

/-- The chain rule for `z ↦ f(z₀, z₁)` on the model: its derivative is
`∂_t f dz⁰ + ∂_r f dz¹`. -/
theorem hasFDerivAt_timeRadius (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) S)
    {x : MinkowskiModel 3} (hx : (x 0, x 1) ∈ S) :
    HasFDerivAt (fun z : MinkowskiModel 3 => f (z 0) (z 1))
      (partialT f (x 0) (x 1) • (proj 0 : MinkowskiModel 3 →L[ℝ] ℝ) +
        partialR f (x 0) (x 1) • (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ)) x := by
  have hd : DifferentiableAt ℝ (Function.uncurry f) (x 0, x 1) :=
    (hf.contDiffAt (hS.mem_nhds hx)).differentiableAt (by simp)
  let π : MinkowskiModel 3 →L[ℝ] ℝ × ℝ :=
    (proj 0 : MinkowskiModel 3 →L[ℝ] ℝ).prod (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ)
  have h := hd.hasFDerivAt.comp x π.hasFDerivAt
  refine h.congr_fderiv ?_
  ext v
  have hv : ((v 0, v 1) : ℝ × ℝ) = v 0 • ((1 : ℝ), (0 : ℝ)) + v 1 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  simp only [ContinuousLinearMap.comp_apply, π, ContinuousLinearMap.prod_apply, proj_apply,
    add_apply, smul_apply, smul_eq_mul]
  rw [hv, map_add, map_smul, map_smul, partialT_eq_fderiv hS hf hx,
    partialR_eq_fderiv hS hf hx, smul_eq_mul, smul_eq_mul]
  ring

/-- The quotient rule for real functions on the model. -/
theorem hasFDerivAt_div {c d : MinkowskiModel 3 → ℝ}
    {c' d' : MinkowskiModel 3 →L[ℝ] ℝ} {x : MinkowskiModel 3} (hc : HasFDerivAt c c' x)
    (hd : HasFDerivAt d d' x) (h : d x ≠ 0) :
    HasFDerivAt (fun z => c z / d z) ((d x)⁻¹ • c' - (c x / d x ^ 2) • d') x := by
  have hinv := (hasDerivAt_inv h).comp_hasFDerivAt x hd
  refine ((hc.fun_mul hinv).congr_fderiv ?_).congr_of_eventuallyEq ?_
  · ext v
    simp only [add_apply, smul_apply, sub_apply, smul_eq_mul, Function.comp_apply]
    field_simp
    ring
  · exact Eventually.of_forall fun z => div_eq_mul_inv (c z) (d z)

/-! ### The data of the ansatz -/

/-- **The centrally symmetric ansatz** (Landau–Lifshitz, (100.1)–(100.2)): two positive smooth
functions `A(t, r)`, `B(t, r)` on a product `I × J` of open sets of times and radii,
`J ⊆ (0, ∞)`, for the metric `ds² = −A dt² + B dr² + r² (dθ² + sin²θ dφ²)`. -/
structure Data where
  /-- The open set of times. -/
  I : Set ℝ
  /-- The open set of radii. -/
  J : Set ℝ
  /-- The coefficient `A(t, r) = −g₀₀`. -/
  A : ℝ → ℝ → ℝ
  /-- The coefficient `B(t, r) = g₁₁`. -/
  B : ℝ → ℝ → ℝ
  /-- The set of times is open. -/
  isOpen_I : IsOpen I
  /-- The set of radii is open. -/
  isOpen_J : IsOpen J
  /-- The radii are positive. -/
  J_pos : J ⊆ Ioi 0
  /-- `A` is smooth on `I × J`. -/
  contDiffOn_A : ContDiffOn ℝ ∞ (Function.uncurry A) (I ×ˢ J)
  /-- `B` is smooth on `I × J`. -/
  contDiffOn_B : ContDiffOn ℝ ∞ (Function.uncurry B) (I ×ˢ J)
  /-- `A` is positive on `I × J`: the time direction is timelike. -/
  A_pos : ∀ t ∈ I, ∀ r ∈ J, 0 < A t r
  /-- `B` is positive on `I × J`: the radial direction is spacelike. -/
  B_pos : ∀ t ∈ I, ∀ r ∈ J, 0 < B t r

namespace Data

/-- Flat space in spherical co-ordinates, `A = B = 1`, for all times and all radii `r > 0`. -/
def flat : Data where
  I := univ
  J := Ioi 0
  A := fun _ _ => 1
  B := fun _ _ => 1
  isOpen_I := isOpen_univ
  isOpen_J := isOpen_Ioi
  J_pos := subset_rfl
  contDiffOn_A := contDiffOn_const
  contDiffOn_B := contDiffOn_const
  A_pos := fun _ _ _ _ => one_pos
  B_pos := fun _ _ _ _ => one_pos

end Data

variable (D : Data)

/-- The set `I × J` of times and radii is open. -/
theorem isOpen_timeRadius : IsOpen (D.I ×ˢ D.J) := D.isOpen_I.prod D.isOpen_J

/-- The domain `t ∈ I`, `r ∈ J`, `0 < θ < π` in the co-ordinates `(t, r, θ, φ)`. -/
def domain : Opens (MinkowskiModel 3) :=
  ⟨{x | x 0 ∈ D.I ∧ x 1 ∈ D.J ∧ 0 < x 2 ∧ x 2 < Real.pi},
    (D.isOpen_I.preimage (continuous_apply 0)).inter
      ((D.isOpen_J.preimage (continuous_apply 1)).inter
        ((isOpen_lt continuous_const (continuous_apply 2)).inter
          (isOpen_lt (continuous_apply 2) continuous_const)))⟩

variable {D} {x : MinkowskiModel 3}

/-- The time and the radius of a point of the domain lie in `I × J`. -/
theorem mem_timeRadius (hx : x ∈ domain D) : (x 0, x 1) ∈ D.I ×ˢ D.J := ⟨hx.1, hx.2.1⟩

/-- The radius is positive on the domain. -/
theorem radius_pos (hx : x ∈ domain D) : 0 < x 1 := D.J_pos hx.2.1

/-- `sin θ > 0` on the domain. -/
theorem sin_pos_of_mem (hx : x ∈ domain D) : 0 < Real.sin (x 2) :=
  Real.sin_pos_of_pos_of_lt_pi hx.2.2.1 hx.2.2.2

/-- `A > 0` on the domain. -/
theorem A_pos_of_mem (hx : x ∈ domain D) : 0 < D.A (x 0) (x 1) := D.A_pos _ hx.1 _ hx.2.1

/-- `B > 0` on the domain. -/
theorem B_pos_of_mem (hx : x ∈ domain D) : 0 < D.B (x 0) (x 1) := D.B_pos _ hx.1 _ hx.2.1

variable (D) in
/-- The diagonal coefficients `(−A, B, r², r² sin²θ)` of the ansatz. -/
def coefficients (x : MinkowskiModel 3) : Fin 4 → ℝ :=
  ![-D.A (x 0) (x 1), D.B (x 0) (x 1), x 1 ^ 2, x 1 ^ 2 * Real.sin (x 2) ^ 2]

/-- A smooth function of `(t, r)` on `I × J` is smooth on the domain. -/
theorem contDiffOn_timeRadius {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (D.I ×ˢ D.J)) :
    ContDiffOn ℝ ∞ (fun z : MinkowskiModel 3 => f (z 0) (z 1)) (domain D) := by
  have hπ : ContDiff ℝ ∞ fun z : MinkowskiModel 3 => ((z 0, z 1) : ℝ × ℝ) :=
    (contDiff_apply ℝ (fun _ => ℝ) 0).prodMk (contDiff_apply ℝ (fun _ => ℝ) 1)
  exact hf.comp hπ.contDiffOn fun z hz => mem_timeRadius hz

/-- The coefficients are smooth on the domain. -/
theorem contDiffOn_coefficients (i : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => coefficients D x i) (domain D) := by
  have hr : ContDiff ℝ ∞ fun x : MinkowskiModel 3 => x 1 := contDiff_apply ℝ (fun _ => ℝ) 1
  have hθ : ContDiff ℝ ∞ fun x : MinkowskiModel 3 => x 2 := contDiff_apply ℝ (fun _ => ℝ) 2
  fin_cases i
  · exact (contDiffOn_timeRadius D.contDiffOn_A).neg
  · exact contDiffOn_timeRadius D.contDiffOn_B
  · exact (hr.pow 2).contDiffOn
  · exact ((hr.pow 2).mul (hθ.sin.pow 2)).contDiffOn

variable (D) in
/-- **The centrally symmetric metric** `ds² = −A dt² + B dr² + r² dθ² + r² sin²θ dφ²` on the
domain (Landau–Lifshitz, (100.2)). -/
def metric : CoordinateMetric .timeNegative 3 (domain D) :=
  ofDiagonal (coefficients D) contDiffOn_coefficients
    (fun x hx => by
      simp only [coefficients, LorentzConvention.timeSign_timeNegative, Matrix.cons_val_zero]
      linarith [A_pos_of_mem hx])
    (fun x hx α => by
      fin_cases α
      · simpa [coefficients] using B_pos_of_mem hx
      · simpa [coefficients] using pow_pos (radius_pos hx) 2
      · simpa [coefficients] using
          mul_pos (pow_pos (radius_pos hx) 2) (pow_pos (sin_pos_of_mem hx) 2))

/-- The matrix of coefficients of the metric is `diag(−A, B, r², r² sin²θ)`. -/
theorem coefficient_metric (y : MinkowskiModel 3) :
    (metric D).coefficient y = Matrix.diagonal (coefficients D y) :=
  coefficient_ofDiagonal _ _ _ _ y

/-- No coefficient vanishes on the domain. -/
theorem coefficients_ne_zero (hx : x ∈ domain D) (i : Fin 4) : coefficients D x i ≠ 0 := by
  fin_cases i
  · simpa [coefficients] using (A_pos_of_mem hx).ne'
  · simpa [coefficients] using (B_pos_of_mem hx).ne'
  · simpa [coefficients] using (radius_pos hx).ne'
  · simpa [coefficients] using ⟨(radius_pos hx).ne', (sin_pos_of_mem hx).ne'⟩

/-! ### Partial derivatives on the domain -/

/-- The chain rule for a smooth function of `(t, r)` at a point of the domain. -/
theorem hasFDerivAt_timeRadius_domain {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (D.I ×ˢ D.J)) (hx : x ∈ domain D) :
    HasFDerivAt (fun z : MinkowskiModel 3 => f (z 0) (z 1))
      (partialT f (x 0) (x 1) • (proj 0 : MinkowskiModel 3 →L[ℝ] ℝ) +
        partialR f (x 0) (x 1) • (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ)) x :=
  hasFDerivAt_timeRadius (isOpen_timeRadius D) hf (mem_timeRadius hx)

/-- The derivative of `f(t, r)` along `∂_t` is `∂f/∂t`. -/
theorem fderiv_single_zero {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (D.I ×ˢ D.J)) (hx : x ∈ domain D) :
    fderiv ℝ (fun z : MinkowskiModel 3 => f (z 0) (z 1)) x (Pi.single 0 1) =
      partialT f (x 0) (x 1) := by
  rw [(hasFDerivAt_timeRadius_domain hf hx).fderiv]
  simp

/-- The derivative of `f(t, r)` along `∂_r` is `∂f/∂r`. -/
theorem fderiv_single_one {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (D.I ×ˢ D.J)) (hx : x ∈ domain D) :
    fderiv ℝ (fun z : MinkowskiModel 3 => f (z 0) (z 1)) x (Pi.single 1 1) =
      partialR f (x 0) (x 1) := by
  rw [(hasFDerivAt_timeRadius_domain hf hx).fderiv]
  simp

/-- The derivative of `g₀₀ = −A` along `v` is `−(A_t v⁰ + A_r v¹)`. -/
theorem fderiv_coefficients_zero (hx : x ∈ domain D) (v : MinkowskiModel 3) :
    fderiv ℝ (fun z => coefficients D z 0) x v =
      -(partialT D.A (x 0) (x 1) * v 0 + partialR D.A (x 0) (x 1) * v 1) := by
  simp only [coefficients, Matrix.cons_val_zero]
  rw [(hasFDerivAt_timeRadius_domain D.contDiffOn_A hx).fun_neg.fderiv]
  simp

/-- The derivative of `g₁₁ = B` along `v` is `B_t v⁰ + B_r v¹`. -/
theorem fderiv_coefficients_one (hx : x ∈ domain D) (v : MinkowskiModel 3) :
    fderiv ℝ (fun z => coefficients D z 1) x v =
      partialT D.B (x 0) (x 1) * v 0 + partialR D.B (x 0) (x 1) * v 1 := by
  simp only [coefficients, Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [(hasFDerivAt_timeRadius_domain D.contDiffOn_B hx).fderiv]
  simp

/-- The derivative of `g₂₂ = r²` along `v` is `2r v¹`. -/
theorem fderiv_coefficients_two (v : MinkowskiModel 3) :
    fderiv ℝ (fun z => coefficients D z 2) x v = 2 * x 1 * v 1 := by
  simp only [coefficients, Matrix.cons_val]
  rw [((hasFDerivAt_apply 1 x).pow 2).fderiv]
  simp

/-- The derivative of `g₃₃ = r² sin²θ` along `v` is `2r sin²θ v¹ + 2r² sin θ cos θ v²`. -/
theorem fderiv_coefficients_three (v : MinkowskiModel 3) :
    fderiv ℝ (fun z => coefficients D z 3) x v =
      2 * x 1 * Real.sin (x 2) ^ 2 * v 1 +
        x 1 ^ 2 * (2 * Real.sin (x 2) * Real.cos (x 2)) * v 2 := by
  simp only [coefficients, Matrix.cons_val]
  rw [(((hasFDerivAt_apply 1 x).pow 2).fun_mul ((hasFDerivAt_apply 2 x).sin.pow 2)).fderiv]
  simp
  ring

/-- The derivatives of the four coefficients along a vector `v`. -/
theorem fderiv_coefficients (hx : x ∈ domain D) (k : Fin 4) (v : MinkowskiModel 3) :
    fderiv ℝ (fun z => coefficients D z k) x v =
      ![-(partialT D.A (x 0) (x 1) * v 0 + partialR D.A (x 0) (x 1) * v 1),
        partialT D.B (x 0) (x 1) * v 0 + partialR D.B (x 0) (x 1) * v 1, 2 * x 1 * v 1,
        2 * x 1 * Real.sin (x 2) ^ 2 * v 1 +
          x 1 ^ 2 * (2 * Real.sin (x 2) * Real.cos (x 2)) * v 2] k := by
  fin_cases k
  · exact fderiv_coefficients_zero hx v
  · exact fderiv_coefficients_one hx v
  · exact fderiv_coefficients_two v
  · exact fderiv_coefficients_three v

/-! ### The Christoffel symbols -/

/-- The derivative of a quotient `P/(2Q)` of two smooth functions of `(t, r)`. -/
theorem fderiv_div_two {P Q : ℝ → ℝ → ℝ}
    (hP : ContDiffOn ℝ ∞ (Function.uncurry P) (D.I ×ˢ D.J))
    (hQ : ContDiffOn ℝ ∞ (Function.uncurry Q) (D.I ×ˢ D.J)) (hx : x ∈ domain D)
    (hQ0 : Q (x 0) (x 1) ≠ 0) (v : MinkowskiModel 3) :
    fderiv ℝ (fun z : MinkowskiModel 3 => P (z 0) (z 1) / (2 * Q (z 0) (z 1))) x v =
      ((partialT P (x 0) (x 1) * v 0 + partialR P (x 0) (x 1) * v 1) * Q (x 0) (x 1) -
        P (x 0) (x 1) * (partialT Q (x 0) (x 1) * v 0 + partialR Q (x 0) (x 1) * v 1)) /
        (2 * Q (x 0) (x 1) ^ 2) := by
  rw [(hasFDerivAt_div (hasFDerivAt_timeRadius_domain hP hx)
    ((hasFDerivAt_timeRadius_domain hQ hx).const_mul 2) (mul_ne_zero two_ne_zero hQ0)).fderiv]
  simp only [sub_apply, smul_apply, add_apply, proj_apply, smul_eq_mul]
  field_simp

variable (D) in
/-- `Γ⁰₀₀ = A_t/(2A)`. -/
def gamma000 (x : MinkowskiModel 3) : ℝ := partialT D.A (x 0) (x 1) / (2 * D.A (x 0) (x 1))

variable (D) in
/-- `Γ⁰₀₁ = A_r/(2A)`. -/
def gamma001 (x : MinkowskiModel 3) : ℝ := partialR D.A (x 0) (x 1) / (2 * D.A (x 0) (x 1))

variable (D) in
/-- `Γ⁰₁₁ = B_t/(2A)`. -/
def gamma011 (x : MinkowskiModel 3) : ℝ := partialT D.B (x 0) (x 1) / (2 * D.A (x 0) (x 1))

variable (D) in
/-- `Γ¹₀₀ = A_r/(2B)`. -/
def gamma100 (x : MinkowskiModel 3) : ℝ := partialR D.A (x 0) (x 1) / (2 * D.B (x 0) (x 1))

variable (D) in
/-- `Γ¹₀₁ = B_t/(2B)`. -/
def gamma101 (x : MinkowskiModel 3) : ℝ := partialT D.B (x 0) (x 1) / (2 * D.B (x 0) (x 1))

variable (D) in
/-- `Γ¹₁₁ = B_r/(2B)`. -/
def gamma111 (x : MinkowskiModel 3) : ℝ := partialR D.B (x 0) (x 1) / (2 * D.B (x 0) (x 1))

variable (D) in
/-- `Γ¹₂₂ = −r/B`. -/
def gamma122 (x : MinkowskiModel 3) : ℝ := -x 1 / D.B (x 0) (x 1)

variable (D) in
/-- `Γ¹₃₃ = −r sin²θ/B`. -/
def gamma133 (x : MinkowskiModel 3) : ℝ := -x 1 * Real.sin (x 2) ^ 2 / D.B (x 0) (x 1)

/-- `Γ²₁₂ = Γ³₁₃ = 1/r`. -/
def gamma212 (x : MinkowskiModel 3) : ℝ := 1 / x 1

/-- `Γ²₃₃ = −sin θ cos θ`. -/
def gamma233 (x : MinkowskiModel 3) : ℝ := -(Real.sin (x 2) * Real.cos (x 2))

/-- `Γ³₂₃ = cos θ/sin θ`. -/
def gamma323 (x : MinkowskiModel 3) : ℝ := Real.cos (x 2) / Real.sin (x 2)

variable (D) in
/-- **The Christoffel symbols of the ansatz** (Landau–Lifshitz, (100.3)): the table `Γ^k_{ij}`,
indexed `christoffel D x k i j`, with the nonzero entries `Γ⁰₀₀ = A_t/(2A)`,
`Γ⁰₀₁ = A_r/(2A)`, `Γ⁰₁₁ = B_t/(2A)`, `Γ¹₀₀ = A_r/(2B)`, `Γ¹₀₁ = B_t/(2B)`,
`Γ¹₁₁ = B_r/(2B)`, `Γ¹₂₂ = −r/B`, `Γ¹₃₃ = −r sin²θ/B`, `Γ²₁₂ = Γ³₁₃ = 1/r`,
`Γ²₃₃ = −sin θ cos θ`, `Γ³₂₃ = cot θ` and their transposes in the lower indices. -/
def christoffel (x : MinkowskiModel 3) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![![![gamma000 D x, gamma001 D x, 0, 0], ![gamma001 D x, gamma011 D x, 0, 0],
      ![0, 0, 0, 0], ![0, 0, 0, 0]],
    ![![gamma100 D x, gamma101 D x, 0, 0], ![gamma101 D x, gamma111 D x, 0, 0],
      ![0, 0, gamma122 D x, 0], ![0, 0, 0, gamma133 D x]],
    ![![0, 0, 0, 0], ![0, 0, gamma212 x, 0], ![0, gamma212 x, 0, 0],
      ![0, 0, 0, gamma233 x]],
    ![![0, 0, 0, 0], ![0, 0, 0, gamma212 x], ![0, 0, 0, gamma323 x],
      ![0, gamma212 x, gamma323 x, 0]]]

/-- The table is symmetric in the lower indices. -/
theorem christoffel_symm (y : MinkowskiModel 3) (k i j : Fin 4) :
    christoffel D y k i j = christoffel D y k j i := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;> rfl

/-- **The table is the table of Christoffel symbols** of the ansatz on its domain. -/
theorem christoffelOf_eq (hx : x ∈ domain D) (k i j : Fin 4) :
    christoffelOf (metric D).coefficient x k i j = christoffel D x k i j := by
  have hA := (A_pos_of_mem hx).ne'
  have hB := (B_pos_of_mem hx).ne'
  have hr := (radius_pos hx).ne'
  have hs := (sin_pos_of_mem hx).ne'
  rw [metric, christoffelOf_ofDiagonal _ _ _ _ x (coefficients_ne_zero hx)]
  simp only [fderiv_coefficients hx]
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [christoffel, gamma000, gamma001, gamma011, gamma100, gamma101,
      gamma111, gamma122, gamma133, gamma212, gamma233, gamma323, coefficients] <;>
    field_simp

/-- The table agrees with the Christoffel symbols near every point of the domain. -/
theorem eventually_christoffelOf_eq (hx : x ∈ domain D) :
    ∀ᶠ z in 𝓝 x, ∀ k i j, christoffelOf (metric D).coefficient z k i j = christoffel D z k i j := by
  filter_upwards [(domain D).isOpen.mem_nhds hx] with z hz using christoffelOf_eq hz

/-! ### Derivatives of the Christoffel symbols -/

/-- The derivative of `Γ⁰₀₀ = A_t/(2A)` along `v`. -/
theorem fderiv_gamma000 (hx : x ∈ domain D) (v : MinkowskiModel 3) :
    fderiv ℝ (gamma000 D) x v =
      ((partialT (partialT D.A) (x 0) (x 1) * v 0 + partialR (partialT D.A) (x 0) (x 1) * v 1) *
          D.A (x 0) (x 1) -
        partialT D.A (x 0) (x 1) *
          (partialT D.A (x 0) (x 1) * v 0 + partialR D.A (x 0) (x 1) * v 1)) /
        (2 * D.A (x 0) (x 1) ^ 2) :=
  fderiv_div_two (contDiffOn_partialT (isOpen_timeRadius D) D.contDiffOn_A) D.contDiffOn_A hx
    (A_pos_of_mem hx).ne' v

/-- The derivative of `Γ⁰₀₁ = A_r/(2A)` along `v`. -/
theorem fderiv_gamma001 (hx : x ∈ domain D) (v : MinkowskiModel 3) :
    fderiv ℝ (gamma001 D) x v =
      ((partialT (partialR D.A) (x 0) (x 1) * v 0 + partialR (partialR D.A) (x 0) (x 1) * v 1) *
          D.A (x 0) (x 1) -
        partialR D.A (x 0) (x 1) *
          (partialT D.A (x 0) (x 1) * v 0 + partialR D.A (x 0) (x 1) * v 1)) /
        (2 * D.A (x 0) (x 1) ^ 2) :=
  fderiv_div_two (contDiffOn_partialR (isOpen_timeRadius D) D.contDiffOn_A) D.contDiffOn_A hx
    (A_pos_of_mem hx).ne' v

/-- The derivative of `Γ⁰₁₁ = B_t/(2A)` along `v`. -/
theorem fderiv_gamma011 (hx : x ∈ domain D) (v : MinkowskiModel 3) :
    fderiv ℝ (gamma011 D) x v =
      ((partialT (partialT D.B) (x 0) (x 1) * v 0 + partialR (partialT D.B) (x 0) (x 1) * v 1) *
          D.A (x 0) (x 1) -
        partialT D.B (x 0) (x 1) *
          (partialT D.A (x 0) (x 1) * v 0 + partialR D.A (x 0) (x 1) * v 1)) /
        (2 * D.A (x 0) (x 1) ^ 2) :=
  fderiv_div_two (contDiffOn_partialT (isOpen_timeRadius D) D.contDiffOn_B) D.contDiffOn_A hx
    (A_pos_of_mem hx).ne' v

/-- The derivative of `Γ¹₀₀ = A_r/(2B)` along `v`. -/
theorem fderiv_gamma100 (hx : x ∈ domain D) (v : MinkowskiModel 3) :
    fderiv ℝ (gamma100 D) x v =
      ((partialT (partialR D.A) (x 0) (x 1) * v 0 + partialR (partialR D.A) (x 0) (x 1) * v 1) *
          D.B (x 0) (x 1) -
        partialR D.A (x 0) (x 1) *
          (partialT D.B (x 0) (x 1) * v 0 + partialR D.B (x 0) (x 1) * v 1)) /
        (2 * D.B (x 0) (x 1) ^ 2) :=
  fderiv_div_two (contDiffOn_partialR (isOpen_timeRadius D) D.contDiffOn_A) D.contDiffOn_B hx
    (B_pos_of_mem hx).ne' v

/-- The derivative of `Γ¹₀₁ = B_t/(2B)` along `v`. -/
theorem fderiv_gamma101 (hx : x ∈ domain D) (v : MinkowskiModel 3) :
    fderiv ℝ (gamma101 D) x v =
      ((partialT (partialT D.B) (x 0) (x 1) * v 0 + partialR (partialT D.B) (x 0) (x 1) * v 1) *
          D.B (x 0) (x 1) -
        partialT D.B (x 0) (x 1) *
          (partialT D.B (x 0) (x 1) * v 0 + partialR D.B (x 0) (x 1) * v 1)) /
        (2 * D.B (x 0) (x 1) ^ 2) :=
  fderiv_div_two (contDiffOn_partialT (isOpen_timeRadius D) D.contDiffOn_B) D.contDiffOn_B hx
    (B_pos_of_mem hx).ne' v

/-- The derivative of `Γ¹₁₁ = B_r/(2B)` along `v`. -/
theorem fderiv_gamma111 (hx : x ∈ domain D) (v : MinkowskiModel 3) :
    fderiv ℝ (gamma111 D) x v =
      ((partialT (partialR D.B) (x 0) (x 1) * v 0 + partialR (partialR D.B) (x 0) (x 1) * v 1) *
          D.B (x 0) (x 1) -
        partialR D.B (x 0) (x 1) *
          (partialT D.B (x 0) (x 1) * v 0 + partialR D.B (x 0) (x 1) * v 1)) /
        (2 * D.B (x 0) (x 1) ^ 2) :=
  fderiv_div_two (contDiffOn_partialR (isOpen_timeRadius D) D.contDiffOn_B) D.contDiffOn_B hx
    (B_pos_of_mem hx).ne' v

/-- The derivative of `Γ¹₂₂ = −r/B` along `v`. -/
theorem fderiv_gamma122 (hx : x ∈ domain D) (v : MinkowskiModel 3) :
    fderiv ℝ (gamma122 D) x v =
      (-v 1 * D.B (x 0) (x 1) +
        x 1 * (partialT D.B (x 0) (x 1) * v 0 + partialR D.B (x 0) (x 1) * v 1)) /
        D.B (x 0) (x 1) ^ 2 := by
  have hB := (B_pos_of_mem hx).ne'
  rw [show gamma122 D = fun z => -z 1 / D.B (z 0) (z 1) from rfl,
    (hasFDerivAt_div (hasFDerivAt_apply 1 x).fun_neg
      (hasFDerivAt_timeRadius_domain D.contDiffOn_B hx) hB).fderiv]
  simp only [sub_apply, smul_apply, add_apply, neg_apply, proj_apply, smul_eq_mul]
  field_simp
  ring

/-- The derivative of `Γ¹₃₃ = −r sin²θ/B` along `v`. -/
theorem fderiv_gamma133 (hx : x ∈ domain D) (v : MinkowskiModel 3) :
    fderiv ℝ (gamma133 D) x v =
      ((-v 1 * Real.sin (x 2) ^ 2 - x 1 * (2 * Real.sin (x 2) * Real.cos (x 2)) * v 2) *
          D.B (x 0) (x 1) +
        x 1 * Real.sin (x 2) ^ 2 *
          (partialT D.B (x 0) (x 1) * v 0 + partialR D.B (x 0) (x 1) * v 1)) /
        D.B (x 0) (x 1) ^ 2 := by
  have hB := (B_pos_of_mem hx).ne'
  rw [show gamma133 D = fun z => -z 1 * Real.sin (z 2) ^ 2 / D.B (z 0) (z 1) from rfl,
    (hasFDerivAt_div ((hasFDerivAt_apply 1 x).fun_neg.fun_mul
      ((hasFDerivAt_apply 2 x).sin.pow 2)) (hasFDerivAt_timeRadius_domain D.contDiffOn_B hx)
      hB).fderiv]
  simp only [sub_apply, smul_apply, add_apply, neg_apply, proj_apply, smul_eq_mul]
  field_simp
  ring

/-- The derivative of `Γ²₁₂ = 1/r` along `v` is `−v¹/r²`. -/
theorem fderiv_gamma212 (hx : x ∈ domain D) (v : MinkowskiModel 3) :
    fderiv ℝ gamma212 x v = -v 1 / x 1 ^ 2 := by
  have hr := (radius_pos hx).ne'
  rw [show gamma212 = fun z => 1 / z 1 from rfl,
    (hasFDerivAt_div (hasFDerivAt_const (1 : ℝ) x) (hasFDerivAt_apply 1 x) hr).fderiv]
  simp only [sub_apply, smul_apply, zero_apply, proj_apply, smul_eq_mul]
  field_simp
  ring

/-- The derivative of `Γ²₃₃ = −sin θ cos θ` along `v` is `−(cos²θ − sin²θ) v²`. -/
theorem fderiv_gamma233 (v : MinkowskiModel 3) :
    fderiv ℝ gamma233 x v = -(Real.cos (x 2) ^ 2 - Real.sin (x 2) ^ 2) * v 2 := by
  rw [show gamma233 = fun z => -(Real.sin (z 2) * Real.cos (z 2)) from rfl,
    ((hasFDerivAt_apply 2 x).sin.fun_mul (hasFDerivAt_apply 2 x).cos).fun_neg.fderiv]
  simp only [neg_apply, add_apply, smul_apply, proj_apply, smul_eq_mul]
  ring

/-- The derivative of `Γ³₂₃ = cot θ` along `v` is `−v²/sin²θ`. -/
theorem fderiv_gamma323 (hx : x ∈ domain D) (v : MinkowskiModel 3) :
    fderiv ℝ gamma323 x v = -v 2 / Real.sin (x 2) ^ 2 := by
  have hs := (sin_pos_of_mem hx).ne'
  rw [show gamma323 = fun z => Real.cos (z 2) / Real.sin (z 2) from rfl,
    (hasFDerivAt_div (hasFDerivAt_apply 2 x).cos (hasFDerivAt_apply 2 x).sin hs).fderiv]
  simp only [sub_apply, smul_apply, proj_apply, smul_eq_mul]
  field_simp
  linear_combination -v 2 * Real.sin_sq_add_cos_sq (x 2)

/-! ### The Ricci tensor -/

/-- A sum over the four indices of space-time. -/
theorem sum_four (g : Fin (3 + 1) → ℝ) : ∑ i, g i = g 0 + g 1 + g 2 + g 3 :=
  Fin.sum_univ_four g

variable (D) in
/-- The table of the Ricci tensor of the ansatz: `R₀₀`, `R₀₁ = R₁₀ = B_t/(rB)`, `R₁₁`,
`R₂₂ = r B_r/(2B²) − r A_r/(2AB) + 1 − 1/B` and `R₃₃ = sin²θ R₂₂`; the other components
vanish. -/
def ricci (x : MinkowskiModel 3) : Fin 4 → Fin 4 → ℝ :=
  ![![(-(x 1) * D.A (x 0) (x 1) * (partialR D.A (x 0) (x 1) * partialR D.B (x 0) (x 1) -
          partialT D.B (x 0) (x 1) ^ 2) -
        x 1 * D.B (x 0) (x 1) * (partialR D.A (x 0) (x 1) ^ 2 -
          partialT D.A (x 0) (x 1) * partialT D.B (x 0) (x 1)) +
        2 * x 1 * D.A (x 0) (x 1) * D.B (x 0) (x 1) *
          (partialR (partialR D.A) (x 0) (x 1) - partialT (partialT D.B) (x 0) (x 1)) +
        4 * D.A (x 0) (x 1) * D.B (x 0) (x 1) * partialR D.A (x 0) (x 1)) /
        (4 * x 1 * D.A (x 0) (x 1) * D.B (x 0) (x 1) ^ 2),
      partialT D.B (x 0) (x 1) / (x 1 * D.B (x 0) (x 1)), 0, 0],
    ![partialT D.B (x 0) (x 1) / (x 1 * D.B (x 0) (x 1)),
      (x 1 * D.A (x 0) (x 1) * (partialR D.A (x 0) (x 1) * partialR D.B (x 0) (x 1) -
          partialT D.B (x 0) (x 1) ^ 2) +
        x 1 * D.B (x 0) (x 1) * (partialR D.A (x 0) (x 1) ^ 2 -
          partialT D.A (x 0) (x 1) * partialT D.B (x 0) (x 1)) -
        2 * x 1 * D.A (x 0) (x 1) * D.B (x 0) (x 1) *
          (partialR (partialR D.A) (x 0) (x 1) - partialT (partialT D.B) (x 0) (x 1)) +
        4 * D.A (x 0) (x 1) ^ 2 * partialR D.B (x 0) (x 1)) /
        (4 * x 1 * D.A (x 0) (x 1) ^ 2 * D.B (x 0) (x 1)), 0, 0],
    ![0, 0, x 1 * partialR D.B (x 0) (x 1) / (2 * D.B (x 0) (x 1) ^ 2) -
        x 1 * partialR D.A (x 0) (x 1) / (2 * D.A (x 0) (x 1) * D.B (x 0) (x 1)) + 1 -
        1 / D.B (x 0) (x 1), 0],
    ![0, 0, 0, Real.sin (x 2) ^ 2 *
      (x 1 * partialR D.B (x 0) (x 1) / (2 * D.B (x 0) (x 1) ^ 2) -
        x 1 * partialR D.A (x 0) (x 1) / (2 * D.A (x 0) (x 1) * D.B (x 0) (x 1)) + 1 -
        1 / D.B (x 0) (x 1))]]

/-- **The Ricci tensor of the ansatz** at every point of the domain is the table `ricci`. -/
theorem ricciOf_eq (hx : x ∈ domain D) (j k : Fin 4) :
    ricciOf (metric D).coefficient x j k = ricci D x j k := by
  have hA := (A_pos_of_mem hx).ne'
  have hB := (B_pos_of_mem hx).ne'
  have hr := (radius_pos hx).ne'
  have hs := (sin_pos_of_mem hx).ne'
  have hsymA := partialR_partialT (isOpen_timeRadius D) D.contDiffOn_A (mem_timeRadius hx)
  have hsymB := partialR_partialT (isOpen_timeRadius D) D.contDiffOn_B (mem_timeRadius hx)
  rw [ricciOf_eq_ricciOfChristoffel (eventually_christoffelOf_eq hx)]
  fin_cases j <;> fin_cases k <;>
  · simp only [ricciOfChristoffel, sum_four, christoffel, ricci, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    simp only [fderiv_gamma000 hx, fderiv_gamma001 hx, fderiv_gamma011 hx, fderiv_gamma100 hx,
      fderiv_gamma101 hx, fderiv_gamma111 hx, fderiv_gamma122 hx, fderiv_gamma133 hx,
      fderiv_gamma212 hx, fderiv_gamma233, fderiv_gamma323 hx, fderiv_const_apply, zero_apply,
      hsymA, hsymB]
    simp [gamma000, gamma001, gamma011, gamma100, gamma101,
      gamma111, gamma122, gamma133, gamma212, gamma233, gamma323]
    try field_simp
    try simp only [Real.cos_sq']
    try ring

/-- `R₀₀ = [−rA(A_r B_r − B_t²) − rB(A_r² − A_t B_t) + 2rAB(A_rr − B_tt) + 4AB A_r]/(4rAB²)`. -/
theorem ricci_zero_zero (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 0 0 =
      (-(x 1) * D.A (x 0) (x 1) * (partialR D.A (x 0) (x 1) * partialR D.B (x 0) (x 1) -
          partialT D.B (x 0) (x 1) ^ 2) -
        x 1 * D.B (x 0) (x 1) * (partialR D.A (x 0) (x 1) ^ 2 -
          partialT D.A (x 0) (x 1) * partialT D.B (x 0) (x 1)) +
        2 * x 1 * D.A (x 0) (x 1) * D.B (x 0) (x 1) *
          (partialR (partialR D.A) (x 0) (x 1) - partialT (partialT D.B) (x 0) (x 1)) +
        4 * D.A (x 0) (x 1) * D.B (x 0) (x 1) * partialR D.A (x 0) (x 1)) /
        (4 * x 1 * D.A (x 0) (x 1) * D.B (x 0) (x 1) ^ 2) :=
  ricciOf_eq hx 0 0

/-- `R₀₁ = B_t/(rB)`. -/
theorem ricci_zero_one (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 0 1 = partialT D.B (x 0) (x 1) / (x 1 * D.B (x 0) (x 1)) :=
  ricciOf_eq hx 0 1

/-- `R₁₀ = B_t/(rB)`. -/
theorem ricci_one_zero (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 1 0 = partialT D.B (x 0) (x 1) / (x 1 * D.B (x 0) (x 1)) :=
  ricciOf_eq hx 1 0

/-- `R₁₁ = [rA(A_r B_r − B_t²) + rB(A_r² − A_t B_t) − 2rAB(A_rr − B_tt) + 4A² B_r]/(4rA²B)`. -/
theorem ricci_one_one (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 1 1 =
      (x 1 * D.A (x 0) (x 1) * (partialR D.A (x 0) (x 1) * partialR D.B (x 0) (x 1) -
          partialT D.B (x 0) (x 1) ^ 2) +
        x 1 * D.B (x 0) (x 1) * (partialR D.A (x 0) (x 1) ^ 2 -
          partialT D.A (x 0) (x 1) * partialT D.B (x 0) (x 1)) -
        2 * x 1 * D.A (x 0) (x 1) * D.B (x 0) (x 1) *
          (partialR (partialR D.A) (x 0) (x 1) - partialT (partialT D.B) (x 0) (x 1)) +
        4 * D.A (x 0) (x 1) ^ 2 * partialR D.B (x 0) (x 1)) /
        (4 * x 1 * D.A (x 0) (x 1) ^ 2 * D.B (x 0) (x 1)) :=
  ricciOf_eq hx 1 1

/-- `R₂₂ = r B_r/(2B²) − r A_r/(2AB) + 1 − 1/B`. -/
theorem ricci_two_two (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 2 2 =
      x 1 * partialR D.B (x 0) (x 1) / (2 * D.B (x 0) (x 1) ^ 2) -
        x 1 * partialR D.A (x 0) (x 1) / (2 * D.A (x 0) (x 1) * D.B (x 0) (x 1)) + 1 -
        1 / D.B (x 0) (x 1) :=
  ricciOf_eq hx 2 2

/-- `R₃₃ = sin²θ R₂₂`. -/
theorem ricci_three_three (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 3 3 =
      Real.sin (x 2) ^ 2 * ricciOf (metric D).coefficient x 2 2 := by
  rw [ricciOf_eq hx 3 3, ricciOf_eq hx 2 2]
  rfl

/-- `R₀₂ = 0`. -/
theorem ricci_zero_two (hx : x ∈ domain D) : ricciOf (metric D).coefficient x 0 2 = 0 :=
  ricciOf_eq hx 0 2

/-- `R₂₀ = 0`. -/
theorem ricci_two_zero (hx : x ∈ domain D) : ricciOf (metric D).coefficient x 2 0 = 0 :=
  ricciOf_eq hx 2 0

/-- `R₀₃ = 0`. -/
theorem ricci_zero_three (hx : x ∈ domain D) : ricciOf (metric D).coefficient x 0 3 = 0 :=
  ricciOf_eq hx 0 3

/-- `R₃₀ = 0`. -/
theorem ricci_three_zero (hx : x ∈ domain D) : ricciOf (metric D).coefficient x 3 0 = 0 :=
  ricciOf_eq hx 3 0

/-- `R₁₂ = 0`. -/
theorem ricci_one_two (hx : x ∈ domain D) : ricciOf (metric D).coefficient x 1 2 = 0 :=
  ricciOf_eq hx 1 2

/-- `R₂₁ = 0`. -/
theorem ricci_two_one (hx : x ∈ domain D) : ricciOf (metric D).coefficient x 2 1 = 0 :=
  ricciOf_eq hx 2 1

/-- `R₁₃ = 0`. -/
theorem ricci_one_three (hx : x ∈ domain D) : ricciOf (metric D).coefficient x 1 3 = 0 :=
  ricciOf_eq hx 1 3

/-- `R₃₁ = 0`. -/
theorem ricci_three_one (hx : x ∈ domain D) : ricciOf (metric D).coefficient x 3 1 = 0 :=
  ricciOf_eq hx 3 1

/-- `R₂₃ = 0`. -/
theorem ricci_two_three (hx : x ∈ domain D) : ricciOf (metric D).coefficient x 2 3 = 0 :=
  ricciOf_eq hx 2 3

/-- `R₃₂ = 0`. -/
theorem ricci_three_two (hx : x ∈ domain D) : ricciOf (metric D).coefficient x 3 2 = 0 :=
  ricciOf_eq hx 3 2

/-! ### The Einstein tensor -/

/-- The inverse of the matrix of coefficients is `diag(1/c)`. -/
theorem coefficient_metric_inv (hx : x ∈ domain D) :
    ((metric D).coefficient x)⁻¹ = Matrix.diagonal fun l => (coefficients D x l)⁻¹ := by
  rw [coefficient_metric]
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one with l
  exact inv_mul_cancel₀ (coefficients_ne_zero hx l)

/-- The scalar curvature `R = ∑ₐ R_{aa}/c_a` of the ansatz. -/
theorem scalarOf_eq (hx : x ∈ domain D) :
    scalarOf (metric D).coefficient x = ∑ a, ricci D x a a / coefficients D x a := by
  rw [scalarOf, coefficient_metric_inv hx]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a (fun c _ hc => by simp [Matrix.diagonal_apply_ne _ (Ne.symm hc)])
    (fun h => absurd (Finset.mem_univ a) h), Matrix.diagonal_apply_eq, ricciOf_eq hx,
    div_eq_mul_inv]

variable (D) in
/-- The table of the Einstein tensor `G_{ik} = R_{ik} − ½ R g_{ik}` of the ansatz, the
left-hand sides of Landau–Lifshitz (100.4)–(100.6): `G₀₀ = A/r² (1 − 1/B + r B_r/B²)`,
`G₀₁ = B_t/(rB)`, `G₁₁ = A_r/(rA) − (B − 1)/r²`, `G₂₂`, `G₃₃ = sin²θ G₂₂`; the other
components vanish. -/
def einstein (x : MinkowskiModel 3) : Fin 4 → Fin 4 → ℝ :=
  ![![D.A (x 0) (x 1) / x 1 ^ 2 * (1 - 1 / D.B (x 0) (x 1) +
        x 1 * partialR D.B (x 0) (x 1) / D.B (x 0) (x 1) ^ 2),
      partialT D.B (x 0) (x 1) / (x 1 * D.B (x 0) (x 1)), 0, 0],
    ![partialT D.B (x 0) (x 1) / (x 1 * D.B (x 0) (x 1)),
      partialR D.A (x 0) (x 1) / (x 1 * D.A (x 0) (x 1)) - (D.B (x 0) (x 1) - 1) / x 1 ^ 2,
      0, 0],
    ![0, 0, x 1 / (4 * D.A (x 0) (x 1) ^ 2 * D.B (x 0) (x 1) ^ 2) *
      (2 * x 1 * D.A (x 0) (x 1) * D.B (x 0) (x 1) * partialR (partialR D.A) (x 0) (x 1) -
        2 * x 1 * D.A (x 0) (x 1) * D.B (x 0) (x 1) * partialT (partialT D.B) (x 0) (x 1) -
        x 1 * D.A (x 0) (x 1) * partialR D.A (x 0) (x 1) * partialR D.B (x 0) (x 1) +
        x 1 * D.A (x 0) (x 1) * partialT D.B (x 0) (x 1) ^ 2 -
        x 1 * D.B (x 0) (x 1) * partialR D.A (x 0) (x 1) ^ 2 +
        x 1 * D.B (x 0) (x 1) * partialT D.A (x 0) (x 1) * partialT D.B (x 0) (x 1) -
        2 * D.A (x 0) (x 1) ^ 2 * partialR D.B (x 0) (x 1) +
        2 * D.A (x 0) (x 1) * D.B (x 0) (x 1) * partialR D.A (x 0) (x 1)), 0],
    ![0, 0, 0, Real.sin (x 2) ^ 2 * (x 1 / (4 * D.A (x 0) (x 1) ^ 2 * D.B (x 0) (x 1) ^ 2) *
      (2 * x 1 * D.A (x 0) (x 1) * D.B (x 0) (x 1) * partialR (partialR D.A) (x 0) (x 1) -
        2 * x 1 * D.A (x 0) (x 1) * D.B (x 0) (x 1) * partialT (partialT D.B) (x 0) (x 1) -
        x 1 * D.A (x 0) (x 1) * partialR D.A (x 0) (x 1) * partialR D.B (x 0) (x 1) +
        x 1 * D.A (x 0) (x 1) * partialT D.B (x 0) (x 1) ^ 2 -
        x 1 * D.B (x 0) (x 1) * partialR D.A (x 0) (x 1) ^ 2 +
        x 1 * D.B (x 0) (x 1) * partialT D.A (x 0) (x 1) * partialT D.B (x 0) (x 1) -
        2 * D.A (x 0) (x 1) ^ 2 * partialR D.B (x 0) (x 1) +
        2 * D.A (x 0) (x 1) * D.B (x 0) (x 1) * partialR D.A (x 0) (x 1)))]]

/-- **The Einstein tensor of the ansatz** at every point of the domain is the table
`einstein`. -/
theorem einsteinOf_eq (hx : x ∈ domain D) (i k : Fin 4) :
    einsteinOf (metric D).coefficient x i k = einstein D x i k := by
  have hA := (A_pos_of_mem hx).ne'
  have hB := (B_pos_of_mem hx).ne'
  have hr := (radius_pos hx).ne'
  have hs := (sin_pos_of_mem hx).ne'
  rw [einsteinOf, ricciOf_eq hx, scalarOf_eq hx, coefficient_metric, sum_four]
  fin_cases i <;> fin_cases k <;>
  · simp [ricci, einstein, coefficients]
    try field_simp
    try ring

/-- `G₀₀ = A/r² (1 − 1/B + r B_r/B²)`. -/
theorem einstein_zero_zero (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 0 0 =
      D.A (x 0) (x 1) / x 1 ^ 2 * (1 - 1 / D.B (x 0) (x 1) +
        x 1 * partialR D.B (x 0) (x 1) / D.B (x 0) (x 1) ^ 2) :=
  einsteinOf_eq hx 0 0

/-- `G₀₁ = B_t/(rB)`. -/
theorem einstein_zero_one (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 0 1 =
      partialT D.B (x 0) (x 1) / (x 1 * D.B (x 0) (x 1)) :=
  einsteinOf_eq hx 0 1

/-- `G₁₀ = B_t/(rB)`. -/
theorem einstein_one_zero (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 1 0 =
      partialT D.B (x 0) (x 1) / (x 1 * D.B (x 0) (x 1)) :=
  einsteinOf_eq hx 1 0

/-- `G₁₁ = A_r/(rA) − (B − 1)/r²`. -/
theorem einstein_one_one (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 1 1 =
      partialR D.A (x 0) (x 1) / (x 1 * D.A (x 0) (x 1)) - (D.B (x 0) (x 1) - 1) / x 1 ^ 2 :=
  einsteinOf_eq hx 1 1

/-- `G₂₂ = r/(4A²B²) (2rAB A_rr − 2rAB B_tt − rA A_r B_r + rA B_t² − rB A_r² + rB A_t B_t −
2A² B_r + 2AB A_r)`. -/
theorem einstein_two_two (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 2 2 =
      x 1 / (4 * D.A (x 0) (x 1) ^ 2 * D.B (x 0) (x 1) ^ 2) *
        (2 * x 1 * D.A (x 0) (x 1) * D.B (x 0) (x 1) * partialR (partialR D.A) (x 0) (x 1) -
          2 * x 1 * D.A (x 0) (x 1) * D.B (x 0) (x 1) * partialT (partialT D.B) (x 0) (x 1) -
          x 1 * D.A (x 0) (x 1) * partialR D.A (x 0) (x 1) * partialR D.B (x 0) (x 1) +
          x 1 * D.A (x 0) (x 1) * partialT D.B (x 0) (x 1) ^ 2 -
          x 1 * D.B (x 0) (x 1) * partialR D.A (x 0) (x 1) ^ 2 +
          x 1 * D.B (x 0) (x 1) * partialT D.A (x 0) (x 1) * partialT D.B (x 0) (x 1) -
          2 * D.A (x 0) (x 1) ^ 2 * partialR D.B (x 0) (x 1) +
          2 * D.A (x 0) (x 1) * D.B (x 0) (x 1) * partialR D.A (x 0) (x 1)) :=
  einsteinOf_eq hx 2 2

/-- `G₃₃ = sin²θ G₂₂`. -/
theorem einstein_three_three (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 3 3 =
      Real.sin (x 2) ^ 2 * einsteinOf (metric D).coefficient x 2 2 := by
  rw [einsteinOf_eq hx 3 3, einsteinOf_eq hx 2 2]
  rfl

/-- `G₀₂ = 0`. -/
theorem einstein_zero_two (hx : x ∈ domain D) : einsteinOf (metric D).coefficient x 0 2 = 0 :=
  einsteinOf_eq hx 0 2

/-- `G₂₀ = 0`. -/
theorem einstein_two_zero (hx : x ∈ domain D) : einsteinOf (metric D).coefficient x 2 0 = 0 :=
  einsteinOf_eq hx 2 0

/-- `G₀₃ = 0`. -/
theorem einstein_zero_three (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 0 3 = 0 :=
  einsteinOf_eq hx 0 3

/-- `G₃₀ = 0`. -/
theorem einstein_three_zero (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 3 0 = 0 :=
  einsteinOf_eq hx 3 0

/-- `G₁₂ = 0`. -/
theorem einstein_one_two (hx : x ∈ domain D) : einsteinOf (metric D).coefficient x 1 2 = 0 :=
  einsteinOf_eq hx 1 2

/-- `G₂₁ = 0`. -/
theorem einstein_two_one (hx : x ∈ domain D) : einsteinOf (metric D).coefficient x 2 1 = 0 :=
  einsteinOf_eq hx 2 1

/-- `G₁₃ = 0`. -/
theorem einstein_one_three (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 1 3 = 0 :=
  einsteinOf_eq hx 1 3

/-- `G₃₁ = 0`. -/
theorem einstein_three_one (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 3 1 = 0 :=
  einsteinOf_eq hx 3 1

/-- `G₂₃ = 0`. -/
theorem einstein_two_three (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 2 3 = 0 :=
  einsteinOf_eq hx 2 3

/-- `G₃₂ = 0`. -/
theorem einstein_three_two (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 3 2 = 0 :=
  einsteinOf_eq hx 3 2

/-- The product rule `∂_r(AB) = A_r B + A B_r`. -/
theorem partialR_mul (hx : x ∈ domain D) :
    partialR (fun t r => D.A t r * D.B t r) (x 0) (x 1) =
      partialR D.A (x 0) (x 1) * D.B (x 0) (x 1) +
        D.A (x 0) (x 1) * partialR D.B (x 0) (x 1) :=
  ((hasDerivAt_partialR (isOpen_timeRadius D) D.contDiffOn_A (mem_timeRadius hx)).mul
    (hasDerivAt_partialR (isOpen_timeRadius D) D.contDiffOn_B (mem_timeRadius hx))).deriv

/-- **The combination used by Birkhoff's theorem**: `G₀₀/A + G₁₁/B = ∂_r(AB)/(r A B²)`, so
`G₀₀ = G₁₁ = 0` forces `AB` to be independent of `r`. -/
theorem einstein_zero_zero_div_add_one_one_div (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 0 0 / D.A (x 0) (x 1) +
        einsteinOf (metric D).coefficient x 1 1 / D.B (x 0) (x 1) =
      partialR (fun t r => D.A t r * D.B t r) (x 0) (x 1) /
        (x 1 * D.A (x 0) (x 1) * D.B (x 0) (x 1) ^ 2) := by
  have hA := (A_pos_of_mem hx).ne'
  have hB := (B_pos_of_mem hx).ne'
  have hr := (radius_pos hx).ne'
  rw [einstein_zero_zero hx, einstein_one_one hx, partialR_mul hx]
  field_simp
  ring

/-! ### Regression: flat space -/

/-- The partial derivative in `t` of a constant vanishes. -/
@[simp] theorem partialT_const (c : ℝ) : partialT (fun _ _ => c) = fun _ _ => 0 := by
  funext t r
  simp [partialT]

/-- The partial derivative in `r` of a constant vanishes. -/
@[simp] theorem partialR_const (c : ℝ) : partialR (fun _ _ => c) = fun _ _ => 0 := by
  funext t r
  simp [partialR]

/-- Flat space in spherical co-ordinates is Ricci flat. -/
theorem ricciOf_flat (hx : x ∈ domain Data.flat) (j k : Fin 4) :
    ricciOf (metric Data.flat).coefficient x j k = 0 := by
  rw [ricciOf_eq hx]
  fin_cases j <;> fin_cases k <;> simp [ricci, Data.flat]

/-- The Einstein tensor of flat space in spherical co-ordinates vanishes. -/
theorem einsteinOf_flat (hx : x ∈ domain Data.flat) (i k : Fin 4) :
    einsteinOf (metric Data.flat).coefficient x i k = 0 := by
  rw [einsteinOf_eq hx]
  fin_cases i <;> fin_cases k <;> simp [einstein, Data.flat]

end ProjectAinos.GeneralRelativity.SphericalAnsatz
