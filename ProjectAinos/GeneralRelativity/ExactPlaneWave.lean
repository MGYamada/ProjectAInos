/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.FLRW
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Strong gravitational waves

Landau–Lifshitz, §109, in the co-ordinates `(t, x, y, z) = (x 0, x 1, x 2, x 3)`, the signature
`(−+++)`, `c = 1` and the retarded time `u = t − z` (`retarded`). The data (`Data`) are an open
set `J` of retarded times and two transverse scale factors `a, b` smooth and positive on `J`;
the metric is the diagonal plane wave in the Rosen form
`ds² = −dt² + a(u)² dx² + b(u)² dy² + dz² = −du dv + a(u)² dx² + b(u)² dy²`, `v = t + z`, on the
strip `u ∈ J` (`metric`). Its gradient `ℓ = du = (1, 0, 0, −1)` (`nullCovector`) is null
(`nullCovector_isNull`).

* `christoffelOf_eq`: the Christoffel symbols are the table `christoffel`:
  `Γ⁰_{11} = Γ³_{11} = a a'`, `Γ⁰_{22} = Γ³_{22} = b b'`, `Γ¹_{01} = Γ¹_{10} = −Γ¹_{13} = −Γ¹_{31}
  = a'/a`, `Γ²_{02} = Γ²_{20} = −Γ²_{23} = −Γ²_{32} = b'/b`, all others zero.
* `ricciOf_eq`, `ricciOf_eq_null`: `R₀₀ = R₃₃ = −R₀₃ = −R₃₀ = −(a''/a + b''/b)`, all other
  components zero; that is `R_{ik} = −(a''/a + b''/b) ℓ_i ℓ_k` (`ricciFactor`).
* `ricciOf_eq_zero_iff`, `isEinstein_vacuum`: the metric is Ricci flat on the strip, and solves
  the vacuum equations, if and only if `a''/a + b''/b = 0` on `J`. This is an exact statement
  about the full nonlinear Ricci tensor, not its linearisation.
* `curvatureOf_christoffel_one`, `chartCurvature_one_zero_one_zero`, …: the curvature components
  `R¹_{010} = a''/a` and `R²_{020} = b''/b` (in the native chart curvature as well).
* Landau–Lifshitz's form (`LogData`, `LogData.toData`): `a = L e^{β}`, `b = L e^{−β}`, so that
  the transverse metric is `L² γ` with `det γ = 1`. Then `a''/a + b''/b = 2(L'' + β'² L)/L`
  (`ricciFactor_toData`), and the wave is a vacuum solution if and only if `L'' + β'² L = 0`
  on `J` (`ricciOf_toData_eq_zero_iff`).
* An explicit strong wave (`strong`): `L = cos u`, `β = u` on `|u| < π/2`. It is a vacuum
  solution (`ricciOf_strong`, `isEinstein_strong`) and it is curved:
  `R¹_{010} = −2 tan u` (`chartCurvature_strong`) is nonzero wherever `u ≠ 0`
  (`chartCurvature_strong_ne_zero`), for example at `u = π/4`
  (`exists_chartCurvature_strong_ne_zero`). At `u = ±π/2` the factor `L` vanishes and the Rosen
  co-ordinates break down: this is the focusing of Landau–Lifshitz, §109.
* The first order is not exact (`weak`): for `a = e^{εf(u)}`, `b = e^{−εf(u)}` (`L = 1`,
  `β = εf`), the exact Ricci tensor is `R_{ik} = −2ε² f'² ℓ_i ℓ_k` (`ricciOf_weak`,
  `ricci_zero_zero_weak`). Its first-order part in `ε` vanishes (`hasDerivAt_ricciOf_weak`): the
  linearised equations hold for every profile `f`. The exact residual does not: for `ε ≠ 0` and
  `f' ≠ 0` somewhere the metric is not Ricci flat (`not_ricciFlat_weak`, and
  `not_ricciFlat_weak_id` for `f = u`).
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap Set TopologicalSpace Filter
open scoped ContDiff Topology Real

namespace ProjectAinos.GeneralRelativity.ExactPlaneWave

open SmoothGeometry CoordinateMetric

local notation "E" => MinkowskiModel 3

/-! ### The retarded time -/

/-- The retarded time `u = t − z = x⁰ − x³` of a point. -/
def retarded (x : E) : ℝ := x 0 - x 3

/-- The retarded time is continuous. -/
theorem continuous_retarded : Continuous retarded :=
  (continuous_apply 0).sub (continuous_apply 3)

/-- The retarded time is smooth. -/
theorem contDiff_retarded : ContDiff ℝ ∞ retarded :=
  (contDiff_apply ℝ (fun _ => ℝ) 0).sub (contDiff_apply ℝ (fun _ => ℝ) 3)

/-- The retarded time has the derivative `v ↦ v⁰ − v³`. -/
theorem hasFDerivAt_retarded (x : E) :
    HasFDerivAt retarded ((proj 0 : E →L[ℝ] ℝ) - proj 3) x :=
  (hasFDerivAt_apply 0 x).sub (hasFDerivAt_apply 3 x)

/-- The chain rule for a function of the retarded time `z ↦ f(z⁰ − z³)`. -/
theorem hasFDerivAt_comp_retarded {f : ℝ → ℝ} {f' : ℝ} {x : E}
    (hf : HasDerivAt f f' (retarded x)) :
    HasFDerivAt (fun z : E => f (retarded z)) (f' • ((proj 0 : E →L[ℝ] ℝ) - proj 3)) x :=
  hf.comp_hasFDerivAt x (hasFDerivAt_retarded x)

/-- The retarded time of `(t, 0, 0, 0)` is `t`. -/
@[simp] theorem retarded_timeAxis (t : ℝ) : retarded (FLRW.timeAxis t) = t := by
  simp [retarded, FLRW.timeAxis]

/-- The derivative of a function smooth on an open set has its derivative there. -/
theorem hasDerivAt_deriv_of_contDiffOn {J : Set ℝ} {f : ℝ → ℝ} (hJ : IsOpen J)
    (hf : ContDiffOn ℝ ∞ f J) {u : ℝ} (hu : u ∈ J) :
    HasDerivAt (deriv f) (deriv (deriv f) u) u :=
  FLRW.hasDerivAt_of_contDiffOn hJ (FLRW.contDiffOn_deriv_of_contDiffOn hJ hf) hu

/-- The derivative of `z ↦ f(u)²` along `v` is `2 f f' (v⁰ − v³)`. -/
theorem fderiv_sq_retarded {J : Set ℝ} {f : ℝ → ℝ} (hJ : IsOpen J) (hf : ContDiffOn ℝ ∞ f J)
    {x : E} (hx : retarded x ∈ J) (v : E) :
    fderiv ℝ (fun z : E => f (retarded z) ^ 2) x v =
      2 * f (retarded x) * deriv f (retarded x) * (v 0 - v 3) := by
  rw [((hasFDerivAt_comp_retarded (FLRW.hasDerivAt_of_contDiffOn hJ hf hx)).pow 2).fderiv]
  simp only [smul_apply, sub_apply, proj_apply, smul_eq_mul]
  push_cast
  ring

/-- `f f'` at the retarded time: `Γ⁰_{11} = Γ³_{11} = a a'` for `f = a`. -/
def sqGamma (f : ℝ → ℝ) (x : E) : ℝ := f (retarded x) * deriv f (retarded x)

/-- `f'/f` at the retarded time: `Γ¹_{01} = −Γ¹_{13} = a'/a` for `f = a`. -/
def logGamma (f : ℝ → ℝ) (x : E) : ℝ := deriv f (retarded x) / f (retarded x)

/-- The derivative of `f f'` at the retarded time along `v` is `(f'² + f f'') (v⁰ − v³)`. -/
theorem fderiv_sqGamma {J : Set ℝ} {f : ℝ → ℝ} (hJ : IsOpen J) (hf : ContDiffOn ℝ ∞ f J)
    {x : E} (hx : retarded x ∈ J) (v : E) :
    fderiv ℝ (sqGamma f) x v =
      (deriv f (retarded x) ^ 2 + f (retarded x) * deriv (deriv f) (retarded x)) *
        (v 0 - v 3) := by
  have h := hasFDerivAt_comp_retarded ((FLRW.hasDerivAt_of_contDiffOn hJ hf hx).mul
    (hasDerivAt_deriv_of_contDiffOn hJ hf hx))
  rw [show sqGamma f = fun z : E => (f * deriv f) (retarded z) from rfl, h.fderiv]
  simp only [smul_apply, sub_apply, proj_apply, smul_eq_mul]
  ring

/-- The derivative of `f'/f` at the retarded time along `v` is
`(f'' f − f'²)/f² (v⁰ − v³)`. -/
theorem fderiv_logGamma {J : Set ℝ} {f : ℝ → ℝ} (hJ : IsOpen J) (hf : ContDiffOn ℝ ∞ f J)
    {x : E} (hx : retarded x ∈ J) (hf0 : f (retarded x) ≠ 0) (v : E) :
    fderiv ℝ (logGamma f) x v =
      (deriv (deriv f) (retarded x) * f (retarded x) - deriv f (retarded x) ^ 2) /
        f (retarded x) ^ 2 * (v 0 - v 3) := by
  have h := hasFDerivAt_comp_retarded ((hasDerivAt_deriv_of_contDiffOn hJ hf hx).div
    (FLRW.hasDerivAt_of_contDiffOn hJ hf hx) hf0)
  rw [show logGamma f = fun z : E => (deriv f / f) (retarded z) from rfl, h.fderiv]
  simp only [smul_apply, sub_apply, proj_apply, smul_eq_mul]
  ring

/-! ### The data -/

/-- **The data of a diagonal plane wave** (Landau–Lifshitz, §109): an open set `J` of retarded
times and two transverse scale factors `a, b`, smooth and positive on `J`. -/
structure Data where
  /-- The open set of retarded times. -/
  J : Set ℝ
  /-- The scale factor `a(u)`, with `g₁₁ = a²`. -/
  a : ℝ → ℝ
  /-- The scale factor `b(u)`, with `g₂₂ = b²`. -/
  b : ℝ → ℝ
  /-- The set of retarded times is open. -/
  isOpen_J : IsOpen J
  /-- The scale factor `a` is smooth on `J`. -/
  contDiffOn_a : ContDiffOn ℝ ∞ a J
  /-- The scale factor `b` is smooth on `J`. -/
  contDiffOn_b : ContDiffOn ℝ ∞ b J
  /-- The scale factor `a` is positive on `J`. -/
  a_pos : ∀ u ∈ J, 0 < a u
  /-- The scale factor `b` is positive on `J`. -/
  b_pos : ∀ u ∈ J, 0 < b u

variable {D : Data} {x : E}

variable (D) in
/-- The strip `u = t − z ∈ J` of the co-ordinates `(t, x, y, z)`. -/
def domain : Opens E :=
  ⟨{x | retarded x ∈ D.J}, D.isOpen_J.preimage continuous_retarded⟩

/-- The retarded time of a point of the domain lies in `J`. -/
theorem retarded_mem (hx : x ∈ domain D) : retarded x ∈ D.J := hx

/-- The scale factor `a` is positive on the domain. -/
theorem a_pos_of_mem (hx : x ∈ domain D) : 0 < D.a (retarded x) := D.a_pos _ hx

/-- The scale factor `b` is positive on the domain. -/
theorem b_pos_of_mem (hx : x ∈ domain D) : 0 < D.b (retarded x) := D.b_pos _ hx

/-- The point `(u, 0, 0, 0)` lies in the domain for every `u ∈ J`. -/
theorem timeAxis_mem {u : ℝ} (hu : u ∈ D.J) : FLRW.timeAxis u ∈ domain D := by
  simpa [domain] using hu

/-! ### The metric -/

variable (D) in
/-- The diagonal coefficients `(−1, a(u)², b(u)², 1)`. -/
def coefficients (x : E) : Fin 4 → ℝ :=
  ![-1, D.a (retarded x) ^ 2, D.b (retarded x) ^ 2, 1]

/-- A smooth function of the retarded time is smooth on the domain. -/
theorem contDiffOn_retarded {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f D.J) :
    ContDiffOn ℝ ∞ (fun z : E => f (retarded z)) (domain D) :=
  hf.comp contDiff_retarded.contDiffOn fun _ hz => retarded_mem hz

/-- The coefficients are smooth on the domain. -/
theorem contDiffOn_coefficients (i : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => coefficients D x i) (domain D) := by
  fin_cases i
  · exact contDiffOn_const
  · exact (contDiffOn_retarded D.contDiffOn_a).pow 2
  · exact (contDiffOn_retarded D.contDiffOn_b).pow 2
  · exact contDiffOn_const

variable (D) in
/-- **The diagonal plane wave** `ds² = −dt² + a(u)² dx² + b(u)² dy² + dz²`, `u = t − z`, on the
strip `u ∈ J` (Landau–Lifshitz, §109, with a diagonal transverse metric). -/
def metric : CoordinateMetric .timeNegative 3 (domain D) :=
  ofDiagonal (coefficients D) contDiffOn_coefficients
    (fun x _ => by
      simp only [coefficients, LorentzConvention.timeSign_timeNegative, Matrix.cons_val_zero]
      norm_num)
    (fun x hx α => by
      have ha := pow_pos (a_pos_of_mem hx) 2
      have hb := pow_pos (b_pos_of_mem hx) 2
      fin_cases α <;>
        simp [coefficients, LorentzConvention.timeSign_timeNegative, ha, hb])

/-- The matrix of coefficients of the metric is `diag(−1, a², b², 1)`. -/
theorem coefficient_metric (y : E) :
    (metric D).coefficient y = Matrix.diagonal (coefficients D y) :=
  coefficient_ofDiagonal _ _ _ _ y

/-- No coefficient vanishes on the domain. -/
theorem coefficients_ne_zero (hx : x ∈ domain D) (i : Fin 4) : coefficients D x i ≠ 0 := by
  have ha := (a_pos_of_mem hx).ne'
  have hb := (b_pos_of_mem hx).ne'
  fin_cases i <;> simp [coefficients, ha, hb]

/-- The gradient `ℓ = du = (1, 0, 0, −1)` of the retarded time. -/
def nullCovector : Fin 4 → ℝ := ![1, 0, 0, -1]

/-- **The gradient of the retarded time is null**: `g^{ik} ℓ_i ℓ_k = 0`. -/
theorem nullCovector_isNull (y : E) :
    ∑ i, nullCovector i ^ 2 / coefficients D y i = 0 := by
  simp [SphericalAnsatz.sum_four, nullCovector, coefficients]

/-! ### Derivatives of the coefficients -/

/-- The derivatives of the four coefficients along a vector `v`. -/
theorem fderiv_coefficients (hx : x ∈ domain D) (i : Fin 4) (v : E) :
    fderiv ℝ (fun z => coefficients D z i) x v =
      ![0, 2 * D.a (retarded x) * deriv D.a (retarded x) * (v 0 - v 3),
        2 * D.b (retarded x) * deriv D.b (retarded x) * (v 0 - v 3), 0] i := by
  fin_cases i
  · simp [coefficients]
  · exact fderiv_sq_retarded D.isOpen_J D.contDiffOn_a hx v
  · exact fderiv_sq_retarded D.isOpen_J D.contDiffOn_b hx v
  · simp [coefficients]

/-! ### The Christoffel symbols -/

variable (D) in
/-- **The Christoffel symbols of the plane wave**: the table `Γ^k_{ij}`, indexed
`christoffel D x k i j`, with `Γ⁰_{11} = Γ³_{11} = a a'`, `Γ⁰_{22} = Γ³_{22} = b b'`,
`Γ¹_{01} = Γ¹_{10} = −Γ¹_{13} = −Γ¹_{31} = a'/a`, `Γ²_{02} = Γ²_{20} = −Γ²_{23} = −Γ²_{32} = b'/b`
and all other symbols zero. -/
def christoffel (x : E) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![![![0, 0, 0, 0], ![0, sqGamma D.a x, 0, 0], ![0, 0, sqGamma D.b x, 0], ![0, 0, 0, 0]],
    ![![0, logGamma D.a x, 0, 0], ![logGamma D.a x, 0, 0, -logGamma D.a x], ![0, 0, 0, 0],
      ![0, -logGamma D.a x, 0, 0]],
    ![![0, 0, logGamma D.b x, 0], ![0, 0, 0, 0], ![logGamma D.b x, 0, 0, -logGamma D.b x],
      ![0, 0, -logGamma D.b x, 0]],
    ![![0, 0, 0, 0], ![0, sqGamma D.a x, 0, 0], ![0, 0, sqGamma D.b x, 0], ![0, 0, 0, 0]]]

/-- The table is symmetric in the lower indices. -/
theorem christoffel_symm (y : E) (k i j : Fin 4) :
    christoffel D y k i j = christoffel D y k j i := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;> rfl

/-- **The table is the table of Christoffel symbols** of the metric on its domain. -/
theorem christoffelOf_eq (hx : x ∈ domain D) (k i j : Fin 4) :
    christoffelOf (metric D).coefficient x k i j = christoffel D x k i j := by
  have ha := (a_pos_of_mem hx).ne'
  have hb := (b_pos_of_mem hx).ne'
  rw [metric, christoffelOf_ofDiagonal _ _ _ _ x (coefficients_ne_zero hx)]
  simp only [fderiv_coefficients hx]
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [christoffel, sqGamma, logGamma, coefficients] <;>
    field_simp

/-- The table agrees with the Christoffel symbols near every point of the domain. -/
theorem eventually_christoffelOf_eq (hx : x ∈ domain D) :
    ∀ᶠ z in 𝓝 x, ∀ k i j, christoffelOf (metric D).coefficient z k i j = christoffel D z k i j := by
  filter_upwards [(domain D).isOpen.mem_nhds hx] with z hz using christoffelOf_eq hz

/-! ### The Ricci tensor -/

variable (D) in
/-- `a''/a + b''/b` at the retarded time `u`: `R_{ik} = −(a''/a + b''/b) ℓ_i ℓ_k`. -/
def ricciFactor (u : ℝ) : ℝ := deriv (deriv D.a) u / D.a u + deriv (deriv D.b) u / D.b u

variable (D) in
/-- The table of the Ricci tensor: `R₀₀ = R₃₃ = −R₀₃ = −R₃₀ = −(a''/a + b''/b)`, the other
components zero. -/
def ricci (x : E) : Fin 4 → Fin 4 → ℝ :=
  ![![-ricciFactor D (retarded x), 0, 0, ricciFactor D (retarded x)], ![0, 0, 0, 0],
    ![0, 0, 0, 0], ![ricciFactor D (retarded x), 0, 0, -ricciFactor D (retarded x)]]

/-- **The Ricci tensor of the plane wave** at every point of the domain is the table `ricci`.
This is the exact Ricci tensor, not its first-order part. -/
theorem ricciOf_eq (hx : x ∈ domain D) (j k : Fin 4) :
    ricciOf (metric D).coefficient x j k = ricci D x j k := by
  have ha := (a_pos_of_mem hx).ne'
  have hb := (b_pos_of_mem hx).ne'
  rw [ricciOf_eq_ricciOfChristoffel (eventually_christoffelOf_eq hx)]
  fin_cases j <;> fin_cases k <;>
  · simp only [ricciOfChristoffel, SphericalAnsatz.sum_four, christoffel, ricci, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    simp only [fderiv_sqGamma D.isOpen_J D.contDiffOn_a hx,
      fderiv_sqGamma D.isOpen_J D.contDiffOn_b hx,
      fderiv_logGamma D.isOpen_J D.contDiffOn_a hx ha,
      fderiv_logGamma D.isOpen_J D.contDiffOn_b hx hb, fderiv_fun_neg, neg_apply,
      fderiv_const_apply, zero_apply]
    simp [sqGamma, logGamma, ricciFactor]
    try field_simp
    try ring

/-- **The Ricci tensor is null**: `R_{ik} = −(a''/a + b''/b) ℓ_i ℓ_k` with `ℓ = du`. -/
theorem ricciOf_eq_null (hx : x ∈ domain D) (j k : Fin 4) :
    ricciOf (metric D).coefficient x j k =
      -ricciFactor D (retarded x) * nullCovector j * nullCovector k := by
  rw [ricciOf_eq hx]
  fin_cases j <;> fin_cases k <;> simp [ricci, nullCovector]

/-- `R₀₀ = −(a''/a + b''/b)`. -/
theorem ricci_zero_zero (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 0 0 = -ricciFactor D (retarded x) :=
  ricciOf_eq hx 0 0

/-- `R₀₃ = a''/a + b''/b`. -/
theorem ricci_zero_three (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 0 3 = ricciFactor D (retarded x) :=
  ricciOf_eq hx 0 3

/-- `R₃₀ = a''/a + b''/b`. -/
theorem ricci_three_zero (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 3 0 = ricciFactor D (retarded x) :=
  ricciOf_eq hx 3 0

/-- `R₃₃ = −(a''/a + b''/b)`. -/
theorem ricci_three_three (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 3 3 = -ricciFactor D (retarded x) :=
  ricciOf_eq hx 3 3

/-- **The vacuum condition of the plane wave**: the metric is Ricci flat on the strip if and
only if `a''/a + b''/b = 0` on `J`. -/
theorem ricciOf_eq_zero_iff :
    (∀ x ∈ domain D, ∀ j k, ricciOf (metric D).coefficient x j k = 0) ↔
      ∀ u ∈ D.J, ricciFactor D u = 0 := by
  constructor
  · intro h u hu
    have h0 := h _ (timeAxis_mem hu) 0 0
    rw [ricci_zero_zero (timeAxis_mem hu), retarded_timeAxis, neg_eq_zero] at h0
    exact h0
  · intro h x hx j k
    rw [ricciOf_eq_null hx, h _ (retarded_mem hx)]
    simp

/-- **The vacuum plane waves solve the vacuum Einstein equations**: if `a''/a + b''/b = 0` on
`J`, then `G_{ik} = 0` on the strip for every coupling constant. -/
theorem isEinstein_vacuum (h : ∀ u ∈ D.J, ricciFactor D u = 0) (κ : ℝ) :
    (metric D).IsEinstein κ 0 0 := by
  intro z hz i k
  simp [einsteinOf, scalarOf, ricciOf_eq_zero_iff.mpr h z hz]

/-! ### The curvature -/

/-- `R¹_{010} = a''/a` from the table of Christoffel symbols. -/
theorem curvatureOf_christoffel_one (hx : x ∈ domain D) :
    curvatureOf (christoffel D) x 1 0 1 0 =
      deriv (deriv D.a) (retarded x) / D.a (retarded x) := by
  have ha := (a_pos_of_mem hx).ne'
  simp only [curvatureOf, SphericalAnsatz.sum_four, christoffel, Fin.isValue, Matrix.cons_val]
  simp only [fderiv_logGamma D.isOpen_J D.contDiffOn_a hx ha, fderiv_const_apply, zero_apply]
  simp [logGamma]
  field_simp
  ring

/-- `R²_{020} = b''/b` from the table of Christoffel symbols. -/
theorem curvatureOf_christoffel_two (hx : x ∈ domain D) :
    curvatureOf (christoffel D) x 2 0 2 0 =
      deriv (deriv D.b) (retarded x) / D.b (retarded x) := by
  have hb := (b_pos_of_mem hx).ne'
  simp only [curvatureOf, SphericalAnsatz.sum_four, christoffel, Fin.isValue, Matrix.cons_val]
  simp only [fderiv_logGamma D.isOpen_J D.contDiffOn_b hx hb, fderiv_const_apply, zero_apply]
  simp [logGamma]
  field_simp
  ring

/-- **The curvature component** `R¹_{010} = a''/a` of the Lorentz metric in the inclusion
chart. -/
theorem chartCurvature_one_zero_one_zero (x y : domain D) :
    (metric D).toLorentzMetric.chartCurvature (physicalChart x) y 1 0 1 0 =
      deriv (deriv D.a) (retarded y.1) / D.a (retarded y.1) := by
  rw [toLorentzMetric_chartCurvature_eq_curvatureOf (metric D) x y
    (eventually_christoffelOf_eq y.2), curvatureOf_christoffel_one y.2]

/-- **The curvature component** `R²_{020} = b''/b` of the Lorentz metric in the inclusion
chart. -/
theorem chartCurvature_two_zero_two_zero (x y : domain D) :
    (metric D).toLorentzMetric.chartCurvature (physicalChart x) y 2 0 2 0 =
      deriv (deriv D.b) (retarded y.1) / D.b (retarded y.1) := by
  rw [toLorentzMetric_chartCurvature_eq_curvatureOf (metric D) x y
    (eventually_christoffelOf_eq y.2), curvatureOf_christoffel_two y.2]

/-! ### Landau–Lifshitz's form -/

/-- **The data of a plane wave in Landau–Lifshitz's form** (§109): an open set `J` of retarded
times, a factor `L` smooth and positive on `J` and an anisotropy `β` smooth on `J`. The scale
factors are `a = L e^{β}` and `b = L e^{−β}`: the transverse metric is `L² γ` with
`γ = diag(e^{2β}, e^{−2β})`, `det γ = 1`. -/
structure LogData where
  /-- The open set of retarded times. -/
  J : Set ℝ
  /-- The factor `L(u)`; `L²` is the transverse area factor. -/
  L : ℝ → ℝ
  /-- The anisotropy `β(u)`. -/
  β : ℝ → ℝ
  /-- The set of retarded times is open. -/
  isOpen_J : IsOpen J
  /-- The factor `L` is smooth on `J`. -/
  contDiffOn_L : ContDiffOn ℝ ∞ L J
  /-- The anisotropy `β` is smooth on `J`. -/
  contDiffOn_β : ContDiffOn ℝ ∞ β J
  /-- The factor `L` is positive on `J`. -/
  L_pos : ∀ u ∈ J, 0 < L u

namespace LogData

variable (P : LogData)

/-- The scale factor `L e^{sβ}`: `a = L e^{β}` for `s = 1` and `b = L e^{−β}` for `s = −1`. -/
def scale (s u : ℝ) : ℝ := P.L u * Real.exp (s * P.β u)

/-- The scale factors are smooth on `J`. -/
theorem contDiffOn_scale (s : ℝ) : ContDiffOn ℝ ∞ (P.scale s) P.J :=
  P.contDiffOn_L.mul (contDiffOn_const.mul P.contDiffOn_β).exp

/-- The scale factors are positive on `J`. -/
theorem scale_pos (s : ℝ) {u : ℝ} (hu : u ∈ P.J) : 0 < P.scale s u :=
  mul_pos (P.L_pos u hu) (Real.exp_pos _)

/-- **The plane wave of the data** `a = L e^{β}`, `b = L e^{−β}`. -/
def toData : Data where
  J := P.J
  a := P.scale 1
  b := P.scale (-1)
  isOpen_J := P.isOpen_J
  contDiffOn_a := P.contDiffOn_scale 1
  contDiffOn_b := P.contDiffOn_scale (-1)
  a_pos _ hu := P.scale_pos 1 hu
  b_pos _ hu := P.scale_pos (-1) hu

/-- The retarded times of the plane wave are `J`. -/
@[simp] theorem toData_J : P.toData.J = P.J := rfl

/-- The scale factor `a` of the plane wave is `L e^{β}`. -/
@[simp] theorem toData_a : P.toData.a = P.scale 1 := rfl

/-- The scale factor `b` of the plane wave is `L e^{−β}`. -/
@[simp] theorem toData_b : P.toData.b = P.scale (-1) := rfl

variable {P}

/-- `(L e^{sβ})' = (L' + s β' L) e^{sβ}` on `J`. -/
theorem hasDerivAt_scale (s : ℝ) {u : ℝ} (hu : u ∈ P.J) :
    HasDerivAt (P.scale s)
      ((deriv P.L u + s * deriv P.β u * P.L u) * Real.exp (s * P.β u)) u := by
  have hL := FLRW.hasDerivAt_of_contDiffOn P.isOpen_J P.contDiffOn_L hu
  have hβ := FLRW.hasDerivAt_of_contDiffOn P.isOpen_J P.contDiffOn_β hu
  have h : HasDerivAt (fun v => P.L v * Real.exp (s * P.β v))
      (deriv P.L u * Real.exp (s * P.β u) +
        P.L u * (Real.exp (s * P.β u) * (s * deriv P.β u))) u :=
    hL.fun_mul (hβ.const_mul s).exp
  exact h.congr_deriv (by ring)

/-- `(L e^{sβ})'' = (L'' + 2s L'β' + s L β'' + s² L β'²) e^{sβ}` on `J`. -/
theorem deriv_deriv_scale (s : ℝ) {u : ℝ} (hu : u ∈ P.J) :
    deriv (deriv (P.scale s)) u =
      (deriv (deriv P.L) u + 2 * s * deriv P.L u * deriv P.β u +
        s * P.L u * deriv (deriv P.β) u + s ^ 2 * P.L u * deriv P.β u ^ 2) *
        Real.exp (s * P.β u) := by
  have he : deriv (P.scale s) =ᶠ[𝓝 u] fun v =>
      (deriv P.L v + s * deriv P.β v * P.L v) * Real.exp (s * P.β v) := by
    filter_upwards [P.isOpen_J.mem_nhds hu] with v hv using (hasDerivAt_scale s hv).deriv
  have hL := FLRW.hasDerivAt_of_contDiffOn P.isOpen_J P.contDiffOn_L hu
  have hβ := FLRW.hasDerivAt_of_contDiffOn P.isOpen_J P.contDiffOn_β hu
  have hL2 := hasDerivAt_deriv_of_contDiffOn P.isOpen_J P.contDiffOn_L hu
  have hβ2 := hasDerivAt_deriv_of_contDiffOn P.isOpen_J P.contDiffOn_β hu
  have h := (hL2.fun_add ((hβ2.const_mul s).fun_mul hL)).fun_mul (hβ.const_mul s).exp
  rw [he.deriv_eq, h.deriv]
  ring

/-- **The vacuum factor in Landau–Lifshitz's form**: `a''/a + b''/b = 2(L'' + β'² L)/L`. -/
theorem ricciFactor_toData {u : ℝ} (hu : u ∈ P.J) :
    ricciFactor P.toData u = 2 * (deriv (deriv P.L) u + deriv P.β u ^ 2 * P.L u) / P.L u := by
  have hL := (P.L_pos u hu).ne'
  have h1 := (Real.exp_pos (1 * P.β u)).ne'
  have h2 := (Real.exp_pos (-1 * P.β u)).ne'
  rw [ricciFactor, toData_a, toData_b, deriv_deriv_scale 1 hu, deriv_deriv_scale (-1) hu]
  simp only [scale]
  field_simp
  ring

/-- **The vacuum equation in Landau–Lifshitz's form** (§109): the plane wave with
`a = L e^{β}`, `b = L e^{−β}` is Ricci flat on the strip if and only if `L'' + β'² L = 0` on
`J`. -/
theorem ricciOf_toData_eq_zero_iff :
    (∀ x ∈ domain P.toData, ∀ j k, ricciOf (metric P.toData).coefficient x j k = 0) ↔
      ∀ u ∈ P.J, deriv (deriv P.L) u + deriv P.β u ^ 2 * P.L u = 0 := by
  rw [ricciOf_eq_zero_iff]
  refine forall₂_congr fun u hu => ?_
  have hL := (P.L_pos u hu).ne'
  rw [ricciFactor_toData hu]
  simp [hL]

end LogData

/-! ### An explicit strong wave -/

/-- **An explicit strong wave**: `L = cos u` and `β = u` on `|u| < π/2`, that is
`a = cos u e^{u}` and `b = cos u e^{−u}`. The factor `L` vanishes at `u = ±π/2`, where the
transverse metric degenerates and the Rosen co-ordinates break down: the focusing of
Landau–Lifshitz, §109. The theorems hold on the open strip. -/
def strong : LogData where
  J := Ioo (-(π / 2)) (π / 2)
  L := Real.cos
  β u := u
  isOpen_J := isOpen_Ioo
  contDiffOn_L := Real.contDiff_cos.contDiffOn
  contDiffOn_β := contDiff_id.contDiffOn
  L_pos _ hu := Real.cos_pos_of_mem_Ioo hu

/-- The retarded times of the strong wave are `|u| < π/2`. -/
@[simp] theorem strong_J : strong.J = Ioo (-(π / 2)) (π / 2) := rfl

/-- **The strong wave is a vacuum solution**: `L'' + β'² L = −cos u + cos u = 0`. -/
theorem ricciOf_strong :
    ∀ x ∈ domain strong.toData, ∀ j k, ricciOf (metric strong.toData).coefficient x j k = 0 :=
  LogData.ricciOf_toData_eq_zero_iff.mpr fun u _ => by simp [strong, Real.deriv_cos']

/-- The strong wave solves the vacuum Einstein equations for every coupling constant. -/
theorem isEinstein_strong (κ : ℝ) : (metric strong.toData).IsEinstein κ 0 0 :=
  isEinstein_vacuum (fun u hu =>
    ricciOf_eq_zero_iff.mp ricciOf_strong u hu) κ

/-- `a''/a = −2 tan u` for the strong wave. -/
theorem accel_strong {u : ℝ} (hu : u ∈ strong.J) :
    deriv (deriv strong.toData.a) u / strong.toData.a u = -2 * Real.tan u := by
  have hc := (Real.cos_pos_of_mem_Ioo hu).ne'
  rw [LogData.toData_a, LogData.deriv_deriv_scale 1 hu]
  simp [LogData.scale, strong, Real.deriv_cos', Real.tan_eq_sin_div_cos]
  field_simp

/-- **The curvature of the strong wave**: `R¹_{010} = −2 tan u`. -/
theorem chartCurvature_strong (x y : domain strong.toData) :
    (metric strong.toData).toLorentzMetric.chartCurvature (physicalChart x) y 1 0 1 0 =
      -2 * Real.tan (retarded y.1) := by
  rw [chartCurvature_one_zero_one_zero, accel_strong y.2]

/-- **The strong wave is curved**: `R¹_{010} = −2 tan u` is nonzero at every point with
`u ≠ 0`. It vanishes on the null hyperplane `u = 0`. -/
theorem chartCurvature_strong_ne_zero (x y : domain strong.toData) (hy : retarded y.1 ≠ 0) :
    (metric strong.toData).toLorentzMetric.chartCurvature (physicalChart x) y 1 0 1 0 ≠ 0 := by
  have hu : retarded y.1 ∈ Ioo (-(π / 2)) (π / 2) := y.2
  have hc := (Real.cos_pos_of_mem_Ioo hu).ne'
  have hs : Real.sin (retarded y.1) ≠ 0 := by
    rw [Ne, Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [hu.1, Real.pi_pos])
      (by linarith [hu.2, Real.pi_pos])]
    exact hy
  rw [chartCurvature_strong, Real.tan_eq_sin_div_cos]
  exact mul_ne_zero (by norm_num) (div_ne_zero hs hc)

/-- **The strong wave is not flat**: at the point `(π/4, 0, 0, 0)` of the strip the curvature
component `R¹_{010} = −2` does not vanish. -/
theorem exists_chartCurvature_strong_ne_zero :
    ∃ y : domain strong.toData,
      (metric strong.toData).toLorentzMetric.chartCurvature (physicalChart y) y 1 0 1 0 ≠ 0 := by
  have hm : FLRW.timeAxis (π / 4) ∈ domain strong.toData :=
    timeAxis_mem (by
      rw [LogData.toData_J, strong_J]
      constructor <;> linarith [Real.pi_pos])
  refine ⟨⟨_, hm⟩, chartCurvature_strong_ne_zero _ _ ?_⟩
  rw [retarded_timeAxis]
  positivity

/-! ### The first order is not exact -/

/-- **A weak wave and its exact metric**: for a profile `f` smooth on `ℝ` and an amplitude `ε`,
the data `L = 1`, `β = εf`, that is `a = e^{εf(u)}` and `b = e^{−εf(u)}` on all of space. To first
order in `ε` the metric is `η + ε h` with `h = diag(0, 2f, −2f, 0)`, a transverse traceless plane
wave of the linearised theory. -/
def weak (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (ε : ℝ) : LogData where
  J := univ
  L _ := 1
  β u := ε * f u
  isOpen_J := isOpen_univ
  contDiffOn_L := contDiffOn_const
  contDiffOn_β := (contDiff_const.mul hf).contDiffOn
  L_pos _ _ := one_pos

variable {f : ℝ → ℝ} {hf : ContDiff ℝ ∞ f} {ε : ℝ}

/-- Every point lies in the domain of the weak wave. -/
theorem mem_domain_weak (y : E) : y ∈ domain (weak f hf ε).toData := mem_univ (retarded y)

/-- `a''/a + b''/b = 2ε² f'²` for the weak wave. -/
theorem ricciFactor_weak (u : ℝ) :
    ricciFactor (weak f hf ε).toData u = 2 * ε ^ 2 * deriv f u ^ 2 := by
  rw [LogData.ricciFactor_toData (mem_univ u)]
  simp [weak, deriv_const_mul_field']
  ring

/-- **The exact Ricci tensor of the weak wave**: `R_{ik} = −2ε² f'(u)² ℓ_i ℓ_k`. -/
theorem ricciOf_weak (y : E) (j k : Fin 4) :
    ricciOf (metric (weak f hf ε).toData).coefficient y j k =
      -(2 * ε ^ 2 * deriv f (retarded y) ^ 2) * nullCovector j * nullCovector k := by
  rw [ricciOf_eq_null (mem_domain_weak y), ricciFactor_weak]

/-- **The exact residual** `R₀₀ = −2ε² f'(u)²` of the weak wave. -/
theorem ricci_zero_zero_weak (y : E) :
    ricciOf (metric (weak f hf ε).toData).coefficient y 0 0 =
      -2 * ε ^ 2 * deriv f (retarded y) ^ 2 := by
  rw [ricci_zero_zero (mem_domain_weak y), ricciFactor_weak]
  ring

/-- **The first-order part of the Ricci tensor vanishes**: at every point, every component of the
Ricci tensor of the weak wave has derivative `0` in `ε` at `ε = 0`, so the linearised vacuum
equations hold for every profile. -/
theorem hasDerivAt_ricciOf_weak (y : E) (j k : Fin 4) :
    HasDerivAt (fun ε => ricciOf (metric (weak f hf ε).toData).coefficient y j k) 0 0 := by
  set C := -(2 * deriv f (retarded y) ^ 2) * nullCovector j * nullCovector k
  have h : (fun ε => ricciOf (metric (weak f hf ε).toData).coefficient y j k) =
      fun ε => ε ^ 2 * C := by
    funext ε
    rw [ricciOf_weak]
    ring
  rw [h]
  simpa using (hasDerivAt_pow 2 (0 : ℝ)).mul_const C

/-- **The first order is not exact**: for `ε ≠ 0` and a profile with `f'(u) ≠ 0` at some `u`,
the weak wave is not Ricci flat; `R₀₀ = −2ε² f'(u)² ≠ 0` at `(u, 0, 0, 0)`. -/
theorem not_ricciFlat_weak (hε : ε ≠ 0) {u : ℝ} (hu : deriv f u ≠ 0) :
    ¬ ∀ y ∈ domain (weak f hf ε).toData, ∀ j k,
      ricciOf (metric (weak f hf ε).toData).coefficient y j k = 0 := by
  intro h
  have h0 := h _ (mem_domain_weak (FLRW.timeAxis u)) 0 0
  rw [ricci_zero_zero_weak, retarded_timeAxis] at h0
  simp [hε, hu] at h0

/-- **The linear profile** `f = u`: for every `ε ≠ 0` the metric
`−dt² + e^{2εu} dx² + e^{−2εu} dy² + dz²` solves the linearised vacuum equations but is not Ricci
flat, with `R₀₀ = −2ε²`. -/
theorem not_ricciFlat_weak_id (hε : ε ≠ 0) :
    ¬ ∀ y ∈ domain (weak (fun u => u) contDiff_id ε).toData, ∀ j k,
      ricciOf (metric (weak (fun u => u) contDiff_id ε).toData).coefficient y j k = 0 :=
  not_ricciFlat_weak (u := 0) hε (by simp)

end ProjectAinos.GeneralRelativity.ExactPlaneWave
