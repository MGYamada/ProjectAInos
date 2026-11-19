/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.SphericalAnsatz
public import ProjectAinos.GeneralRelativity.DeSitterSlicing
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateConservation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The isotropic cosmological model

Landau–Lifshitz, §§111–113, in the co-ordinates `(t, x¹, x², x³) = (x 0, x 1, x 2, x 3)`, the
signature `(−+++)` and `c = 1`. The data (`Data`) are an open set `I` of times, a lapse `N` and a
scale factor `a` smooth and positive on `I`, and a curvature constant `k`. With the conformal
factor `ψ_k(x) = 1 + (k/4)(x₁² + x₂² + x₃²)` (`psi`), the space `ψ_k⁻² (dx₁² + dx₂² + dx₃²)` has
constant curvature `k` (§111, in isotropic co-ordinates), and the metric is
`ds² = −N(t)² dt² + a(t)² ψ_k(x)⁻² (dx₁² + dx₂² + dx₃²)` on `t ∈ I`, `ψ_k(x) > 0` (`metric`).
With `N = 1` it is synchronous (`isSynchronous`).

* `christoffelOf_eq`: the Christoffel symbols are the table `christoffel`: `Γ⁰₀₀ = Ṅ/N`,
  `Γ⁰_{αβ} = aȧ/(N²ψ²) δ_{αβ}`, `Γ^α_{0β} = (ȧ/a) δ^α_β` and the spatial symbols
  `Γ^α_{βγ} = σ_β δ_{αγ} + σ_γ δ_{αβ} − σ_α δ_{βγ}` with `σ_i = −k xⁱ/(2ψ)`.
* `ricciOf_eq`, `ricci_zero_zero`, `ricci_zero_succ`, `ricci_succ_zero`, `ricci_succ_succ`:
  `R₀₀ = −3(ä/a − Ṅȧ/(Na))`, `R₀α = 0` and
  `R_{αβ} = ((aä + 2ȧ²)/N² − aȧṄ/N³ + 2k) ψ⁻² δ_{αβ}`; `scalarOf_eq`:
  `R = 6((aä + ȧ²)/N² − aȧṄ/N³ + k)/a²`.
* `einsteinOf_eq`, `einstein_zero_zero`, …, `einstein_succ_succ`:
  `G₀₀ = 3(ȧ²/a² + N²k/a²)`, `G₀α = 0` and
  `G_{αβ} = −((2aä + ȧ²)/N² − 2aȧṄ/N³ + k) ψ⁻² δ_{αβ}`.
* `perfectFluidStress`: the comoving perfect fluid `T_{μν} = (ρ + p) u_μ u_ν + p g_{μν}` with
  `u^μ = (1/N, 0, 0, 0)`, `u_μ = (−N, 0, 0, 0)` (`fluidCovector`, `fluidCovector_norm`) and a
  density `ρ(t)` and a pressure `p(t)`; it is `diag(ρN², p g_{αα})` (`perfectFluidStress_eq`).
* `divergenceOf_perfectFluidStress`, `comoving_divergence_iff`,
  `divergence_eq_zero_iff_continuity`: in the co-ordinates, `∇^μ T_{μ0} = −(ρ̇ + 3(ȧ/a)(ρ + p))`
  and `∇^μ T_{μα} = 0`, so the conservation of the fluid is the continuity equation
  `ρ̇ + 3(ȧ/a)(ρ + p) = 0` (`ContinuityEquation`).
* `isEinstein_iff_friedmann`, `satisfiesEinstein_iff_friedmann`: the Einstein equations
  `G_{ik} + Λ g_{ik} = κ T_{ik}` hold on the domain, in the co-ordinates or natively, if and only
  if on `I` the first Friedmann equation `(ȧ/a)² + N²k/a² = (κ/3)N²ρ + (Λ/3)N²`
  (`FirstFriedmann`, from `G₀₀`) and the second
  `(2ä/a + (ȧ/a)²)/N² − 2(ȧ/a)Ṅ/N³ + k/a² = −κp + Λ` (`SecondFriedmann`, from `G_{αβ}`) hold;
  for `N = 1` they are `H² + k/a² = κρ/3 + Λ/3` and `2ä/a + ȧ²/a² + k/a² = −κp + Λ`
  (`firstFriedmann_iff_of_lapse_eq_one`, `secondFriedmann_iff_of_lapse_eq_one`).
* `continuity_of_friedmann`: for `κ ≠ 0`, the first equation on `I` and the second at `t` give
  the continuity equation at `t`, without division by the Hubble rate (`friedmann_identity`);
  `second_of_first_of_continuity`: where `ȧ ≠ 0`, the first equation and the continuity
  equation give the second, and `not_secondFriedmann_static` shows that `ȧ ≠ 0` is needed.
* `curvature_eq`, `curvature_sign`: with `N = 1`, `Λ = 0` and `κ > 0`, `k = a²(κρ/3 − H²)`, so
  `k` has the sign of `ρ − 3H²/κ` (§§112–113: closed above the critical density, open below).
* Regressions: de Sitter space in the flat slicing (`Data.deSitter`) is
  `DeSitterSlicing.metric` (`coefficient_deSitter`), the table `ricci` reproduces
  `DeSitterSlicing.ricci_eq` (`ricci_deSitter`) and the vacuum equations with `Λ = 3` hold
  (`isEinstein_deSitter`); the Milne universe `a = t`, `k = −1` (`Data.milne`) is Ricci flat and
  solves the vacuum equations (`ricciOf_milne`, `isEinstein_milne`); de Sitter space in the
  closed slicing `a = cosh t`, `k = 1` (`Data.closedDeSitter`), with a turning point at `t = 0`,
  solves them with `Λ = 3` (`isEinstein_closedDeSitter`).
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap Set TopologicalSpace Filter
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.FLRW

open SmoothGeometry CoordinateMetric
open LorentzMetric (chartField)

local notation "E" => MinkowskiModel 3

/-! ### Functions of the time -/

/-- A function smooth on an open set of times has its derivative there. -/
theorem hasDerivAt_of_contDiffOn {I : Set ℝ} {f : ℝ → ℝ} (hI : IsOpen I)
    (hf : ContDiffOn ℝ ∞ f I) {t : ℝ} (ht : t ∈ I) : HasDerivAt f (deriv f t) t :=
  ((hf.contDiffAt (hI.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt

/-- The derivative of a function smooth on an open set of times is smooth there. -/
theorem contDiffOn_deriv_of_contDiffOn {I : Set ℝ} {f : ℝ → ℝ} (hI : IsOpen I)
    (hf : ContDiffOn ℝ ∞ f I) : ContDiffOn ℝ ∞ (deriv f) I :=
  hf.deriv_of_isOpen hI (by simp)

/-- The chain rule for a function of the time `z ↦ f(z⁰)` on the model. -/
theorem hasFDerivAt_time {f : ℝ → ℝ} {f' : ℝ} {x : E} (hf : HasDerivAt f f' (x 0)) :
    HasFDerivAt (fun z : E => f (z 0)) (f' • (proj 0 : E →L[ℝ] ℝ)) x :=
  hf.comp_hasFDerivAt x (hasFDerivAt_apply 0 x)

/-! ### The conformal factor of the spatial metric -/

/-- The conformal factor `ψ_k(x) = 1 + (k/4)(x₁² + x₂² + x₃²)` of the spatial metric
`ψ_k⁻² (dx₁² + dx₂² + dx₃²)` of constant curvature `k`. -/
def psi (k : ℝ) (x : E) : ℝ := 1 + k / 4 * (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2)

/-- The radial sum `x₁ v₁ + x₂ v₂ + x₃ v₃`. -/
def dotSpace (x v : E) : ℝ := x 1 * v 1 + x 2 * v 2 + x 3 * v 3

/-- The conformal factor is smooth. -/
theorem contDiff_psi (k : ℝ) : ContDiff ℝ ∞ (psi k) := by
  unfold psi
  fun_prop

/-- The derivative of the conformal factor: `dψ_k(v) = (k/2)(x₁ v₁ + x₂ v₂ + x₃ v₃)`. -/
theorem hasFDerivAt_psi (k : ℝ) (x : E) :
    HasFDerivAt (psi k) ((k / 2) • (x 1 • (proj 1 : E →L[ℝ] ℝ) + x 2 • (proj 2 : E →L[ℝ] ℝ) +
      x 3 • (proj 3 : E →L[ℝ] ℝ))) x := by
  have h1 : HasFDerivAt (fun z : E => z 1) (proj 1 : E →L[ℝ] ℝ) x := hasFDerivAt_apply 1 x
  have h2 : HasFDerivAt (fun z : E => z 2) (proj 2 : E →L[ℝ] ℝ) x := hasFDerivAt_apply 2 x
  have h3 : HasFDerivAt (fun z : E => z 3) (proj 3 : E →L[ℝ] ℝ) x := hasFDerivAt_apply 3 x
  have h := (((h1.pow 2).add (h2.pow 2)).add (h3.pow 2)).const_mul (k / 4)
  refine (h.const_add 1).congr_fderiv ?_
  ext v
  simp only [add_apply, smul_apply, proj_apply, smul_eq_mul]
  ring

/-- `dψ_k(v) = (k/2)(x₁ v₁ + x₂ v₂ + x₃ v₃)`. -/
theorem fderiv_psi (k : ℝ) (x v : E) : fderiv ℝ (psi k) x v = k / 2 * dotSpace x v := by
  rw [(hasFDerivAt_psi k x).fderiv]
  simp only [smul_apply, add_apply, proj_apply, smul_eq_mul, dotSpace]

/-! ### The data -/

/-- **The data of the isotropic cosmological model** (Landau–Lifshitz, §§111–112): an open set
`I` of times, the lapse `N` and the scale factor `a`, smooth and positive on `I`, and the
curvature constant `k` of the spatial sections. -/
structure Data where
  /-- The open set of times. -/
  I : Set ℝ
  /-- The lapse `N(t)`, with `g₀₀ = −N²`. -/
  N : ℝ → ℝ
  /-- The scale factor `a(t)`. -/
  a : ℝ → ℝ
  /-- The curvature constant of the spatial sections. -/
  k : ℝ
  /-- The set of times is open. -/
  isOpen_I : IsOpen I
  /-- The lapse is smooth on `I`. -/
  contDiffOn_N : ContDiffOn ℝ ∞ N I
  /-- The scale factor is smooth on `I`. -/
  contDiffOn_a : ContDiffOn ℝ ∞ a I
  /-- The lapse is positive on `I`. -/
  N_pos : ∀ t ∈ I, 0 < N t
  /-- The scale factor is positive on `I`. -/
  a_pos : ∀ t ∈ I, 0 < a t

namespace Data

/-- De Sitter space in the flat slicing: `N = 1`, `a = eᵗ`, `k = 0` for all times. -/
def deSitter : Data where
  I := univ
  N := fun _ => 1
  a := Real.exp
  k := 0
  isOpen_I := isOpen_univ
  contDiffOn_N := contDiffOn_const
  contDiffOn_a := Real.contDiff_exp.contDiffOn
  N_pos := fun _ _ => one_pos
  a_pos := fun t _ => Real.exp_pos t

/-- The empty Milne universe: `N = 1`, `a = t`, `k = −1` for the times `t > 0`. -/
def milne : Data where
  I := Ioi 0
  N := fun _ => 1
  a := fun t => t
  k := -1
  isOpen_I := isOpen_Ioi
  contDiffOn_N := contDiffOn_const
  contDiffOn_a := contDiffOn_id
  N_pos := fun _ _ => one_pos
  a_pos := fun _ ht => ht

end Data

variable {D : Data} {x : E}

/-- `t ↦ N(t)` has the derivative `Ṅ` on `I`. -/
theorem hasDerivAt_N {t : ℝ} (ht : t ∈ D.I) : HasDerivAt D.N (deriv D.N t) t :=
  hasDerivAt_of_contDiffOn D.isOpen_I D.contDiffOn_N ht

/-- `t ↦ Ṅ(t)` has the derivative `N̈` on `I`. -/
theorem hasDerivAt_deriv_N {t : ℝ} (ht : t ∈ D.I) :
    HasDerivAt (deriv D.N) (deriv (deriv D.N) t) t :=
  hasDerivAt_of_contDiffOn D.isOpen_I (contDiffOn_deriv_of_contDiffOn D.isOpen_I D.contDiffOn_N)
    ht

/-- `t ↦ a(t)` has the derivative `ȧ` on `I`. -/
theorem hasDerivAt_a {t : ℝ} (ht : t ∈ D.I) : HasDerivAt D.a (deriv D.a t) t :=
  hasDerivAt_of_contDiffOn D.isOpen_I D.contDiffOn_a ht

/-- `t ↦ ȧ(t)` has the derivative `ä` on `I`. -/
theorem hasDerivAt_deriv_a {t : ℝ} (ht : t ∈ D.I) :
    HasDerivAt (deriv D.a) (deriv (deriv D.a) t) t :=
  hasDerivAt_of_contDiffOn D.isOpen_I (contDiffOn_deriv_of_contDiffOn D.isOpen_I D.contDiffOn_a)
    ht

variable (D) in
/-- The domain `t ∈ I`, `ψ_k(x) > 0` of the co-ordinates `(t, x¹, x², x³)`. -/
def domain : Opens E :=
  ⟨{x | x 0 ∈ D.I ∧ 0 < psi D.k x},
    (D.isOpen_I.preimage (continuous_apply 0)).inter
      (isOpen_lt continuous_const (contDiff_psi D.k).continuous)⟩

/-- The time of a point of the domain lies in `I`. -/
theorem time_mem (hx : x ∈ domain D) : x 0 ∈ D.I := hx.1

/-- The conformal factor is positive on the domain. -/
theorem psi_pos (hx : x ∈ domain D) : 0 < psi D.k x := hx.2

/-- The lapse is positive on the domain. -/
theorem N_pos_of_mem (hx : x ∈ domain D) : 0 < D.N (x 0) := D.N_pos _ hx.1

/-- The scale factor is positive on the domain. -/
theorem a_pos_of_mem (hx : x ∈ domain D) : 0 < D.a (x 0) := D.a_pos _ hx.1

/-- The point `(t, 0, 0, 0)`. -/
def timeAxis (t : ℝ) : E := Pi.single 0 t

/-- The time of `(t, 0, 0, 0)` is `t`. -/
@[simp] theorem timeAxis_zero (t : ℝ) : timeAxis t 0 = t := by simp [timeAxis]

/-- The conformal factor is `1` on the time axis. -/
@[simp] theorem psi_timeAxis (k t : ℝ) : psi k (timeAxis t) = 1 := by
  simp [psi, timeAxis]

/-- The point `(t, 0, 0, 0)` lies in the domain for every `t ∈ I`. -/
theorem timeAxis_mem {t : ℝ} (ht : t ∈ D.I) : timeAxis t ∈ domain D :=
  ⟨by simpa using ht, by simp⟩

/-! ### The metric -/

variable (D) in
/-- The diagonal coefficients `(−N², a²/ψ², a²/ψ², a²/ψ²)`. -/
def coefficients (x : E) : Fin 4 → ℝ :=
  ![-(D.N (x 0) ^ 2), D.a (x 0) ^ 2 / psi D.k x ^ 2, D.a (x 0) ^ 2 / psi D.k x ^ 2,
    D.a (x 0) ^ 2 / psi D.k x ^ 2]

/-- A smooth function of the time is smooth on the domain. -/
theorem contDiffOn_time {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f D.I) :
    ContDiffOn ℝ ∞ (fun z : E => f (z 0)) (domain D) :=
  hf.comp (contDiff_apply ℝ (fun _ => ℝ) 0).contDiffOn fun _ hz => time_mem hz

/-- The spatial coefficient `a²/ψ²` is smooth on the domain. -/
theorem contDiffOn_spatialCoefficient :
    ContDiffOn ℝ ∞ (fun z : E => D.a (z 0) ^ 2 / psi D.k z ^ 2) (domain D) :=
  ((contDiffOn_time D.contDiffOn_a).pow 2).div ((contDiff_psi D.k).contDiffOn.pow 2)
    fun _ hz => (pow_pos (psi_pos hz) 2).ne'

/-- The coefficients are smooth on the domain. -/
theorem contDiffOn_coefficients (i : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => coefficients D x i) (domain D) := by
  fin_cases i
  · exact ((contDiffOn_time D.contDiffOn_N).pow 2).neg
  · exact contDiffOn_spatialCoefficient
  · exact contDiffOn_spatialCoefficient
  · exact contDiffOn_spatialCoefficient

variable (D) in
/-- **The isotropic cosmological metric** `ds² = −N(t)² dt² + a(t)² ψ_k(x)⁻² (dx₁² + dx₂² + dx₃²)`
on the domain (Landau–Lifshitz, (111.8), (112.2) with a lapse). -/
def metric : CoordinateMetric .timeNegative 3 (domain D) :=
  ofDiagonal (coefficients D) contDiffOn_coefficients
    (fun x hx => by
      simp only [coefficients, LorentzConvention.timeSign_timeNegative, Matrix.cons_val_zero]
      nlinarith [pow_pos (N_pos_of_mem hx) 2])
    (fun x hx α => by
      have h : 0 < D.a (x 0) ^ 2 / psi D.k x ^ 2 :=
        div_pos (pow_pos (a_pos_of_mem hx) 2) (pow_pos (psi_pos hx) 2)
      fin_cases α <;> simpa [coefficients] using h)

/-- The matrix of coefficients of the metric is `diag(−N², a²/ψ², a²/ψ², a²/ψ²)`. -/
theorem coefficient_metric (y : E) :
    (metric D).coefficient y = Matrix.diagonal (coefficients D y) :=
  coefficient_ofDiagonal _ _ _ _ y

/-- No coefficient vanishes on the domain. -/
theorem coefficients_ne_zero (hx : x ∈ domain D) (i : Fin 4) : coefficients D x i ≠ 0 := by
  have hN := (N_pos_of_mem hx).ne'
  have ha := (a_pos_of_mem hx).ne'
  have hψ := (psi_pos hx).ne'
  fin_cases i <;> simp [coefficients, hN, ha, hψ]

/-- **With unit lapse the metric is synchronous** (Landau–Lifshitz, §97): `g₀₀ = −1` and
`g₀α = 0`. -/
theorem isSynchronous (hN : ∀ t ∈ D.I, D.N t = 1) : (metric D).IsSynchronous := by
  intro z hz
  refine ⟨?_, fun α => ?_⟩
  · simp [coefficient_metric, coefficients, hN _ (time_mem hz)]
  · simp [coefficient_metric, Matrix.diagonal_apply_ne _ (Fin.succ_ne_zero α).symm]

/-! ### Derivatives of the coefficients -/

/-- The derivative of `g₀₀ = −N²` along `v` is `−2NṄ v⁰`. -/
theorem fderiv_coefficients_zero (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (fun z => coefficients D z 0) x v =
      -(2 * D.N (x 0) * deriv D.N (x 0) * v 0) := by
  simp only [coefficients, Matrix.cons_val_zero]
  rw [((hasFDerivAt_time (hasDerivAt_N (time_mem hx))).pow 2).fun_neg.fderiv]
  simp only [neg_apply, smul_apply, proj_apply, smul_eq_mul]
  push_cast
  ring

/-- The derivative of `a²/ψ²` along `v` is `(2aȧ v⁰ ψ − a² k (x·v))/ψ³`. -/
theorem fderiv_spatialCoefficient (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (fun z : E => D.a (z 0) ^ 2 / psi D.k z ^ 2) x v =
      (2 * D.a (x 0) * deriv D.a (x 0) * v 0 * psi D.k x -
        D.a (x 0) ^ 2 * D.k * dotSpace x v) / psi D.k x ^ 3 := by
  have hψ := (psi_pos hx).ne'
  rw [(SphericalAnsatz.hasFDerivAt_div ((hasFDerivAt_time (hasDerivAt_a (time_mem hx))).pow 2)
    ((hasFDerivAt_psi D.k x).pow 2) (pow_ne_zero 2 hψ)).fderiv]
  simp only [sub_apply, smul_apply, add_apply, proj_apply, smul_eq_mul, dotSpace]
  push_cast
  field_simp
  ring

/-- The derivatives of the four coefficients along a vector `v`. -/
theorem fderiv_coefficients (hx : x ∈ domain D) (i : Fin 4) (v : E) :
    fderiv ℝ (fun z => coefficients D z i) x v =
      ![-(2 * D.N (x 0) * deriv D.N (x 0) * v 0),
        (2 * D.a (x 0) * deriv D.a (x 0) * v 0 * psi D.k x -
          D.a (x 0) ^ 2 * D.k * dotSpace x v) / psi D.k x ^ 3,
        (2 * D.a (x 0) * deriv D.a (x 0) * v 0 * psi D.k x -
          D.a (x 0) ^ 2 * D.k * dotSpace x v) / psi D.k x ^ 3,
        (2 * D.a (x 0) * deriv D.a (x 0) * v 0 * psi D.k x -
          D.a (x 0) ^ 2 * D.k * dotSpace x v) / psi D.k x ^ 3] i := by
  fin_cases i
  · exact fderiv_coefficients_zero hx v
  · exact fderiv_spatialCoefficient hx v
  · exact fderiv_spatialCoefficient hx v
  · exact fderiv_spatialCoefficient hx v

/-! ### The Christoffel symbols -/

variable (D) in
/-- `Γ⁰₀₀ = Ṅ/N`. -/
def gammaLapse (x : E) : ℝ := deriv D.N (x 0) / D.N (x 0)

variable (D) in
/-- `Γ⁰_{αα} = aȧ/(N²ψ²)`. -/
def gammaSpatial (x : E) : ℝ :=
  D.a (x 0) * deriv D.a (x 0) / (D.N (x 0) ^ 2 * psi D.k x ^ 2)

variable (D) in
/-- `Γ^α_{0α} = ȧ/a`, the Hubble rate. -/
def gammaExpansion (x : E) : ℝ := deriv D.a (x 0) / D.a (x 0)

/-- `σ_i = −k xⁱ/(2ψ)`, the spatial Christoffel symbols
`Γ^α_{βγ} = σ_β δ_{αγ} + σ_γ δ_{αβ} − σ_α δ_{βγ}` of `ψ⁻² δ`. -/
def gammaConformal (k : ℝ) (i : Fin 4) (x : E) : ℝ := -(k * x i) / (2 * psi k x)

variable (D) in
/-- **The Christoffel symbols of the isotropic metric**: the table `Γ^k_{ij}`, indexed
`christoffel D x k i j`, with `Γ⁰₀₀ = Ṅ/N`, `Γ⁰_{αβ} = aȧ/(N²ψ²) δ_{αβ}`, `Γ^α_{0β} = ȧ/a δ^α_β`
and `Γ^α_{βγ} = σ_β δ_{αγ} + σ_γ δ_{αβ} − σ_α δ_{βγ}`, `σ_i = −k xⁱ/(2ψ)`. -/
def christoffel (x : E) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![![![gammaLapse D x, 0, 0, 0], ![0, gammaSpatial D x, 0, 0],
      ![0, 0, gammaSpatial D x, 0], ![0, 0, 0, gammaSpatial D x]],
    ![![0, gammaExpansion D x, 0, 0],
      ![gammaExpansion D x, gammaConformal D.k 1 x, gammaConformal D.k 2 x,
        gammaConformal D.k 3 x],
      ![0, gammaConformal D.k 2 x, -gammaConformal D.k 1 x, 0],
      ![0, gammaConformal D.k 3 x, 0, -gammaConformal D.k 1 x]],
    ![![0, 0, gammaExpansion D x, 0],
      ![0, -gammaConformal D.k 2 x, gammaConformal D.k 1 x, 0],
      ![gammaExpansion D x, gammaConformal D.k 1 x, gammaConformal D.k 2 x,
        gammaConformal D.k 3 x],
      ![0, 0, gammaConformal D.k 3 x, -gammaConformal D.k 2 x]],
    ![![0, 0, 0, gammaExpansion D x],
      ![0, -gammaConformal D.k 3 x, 0, gammaConformal D.k 1 x],
      ![0, 0, -gammaConformal D.k 3 x, gammaConformal D.k 2 x],
      ![gammaExpansion D x, gammaConformal D.k 1 x, gammaConformal D.k 2 x,
        gammaConformal D.k 3 x]]]

/-- The table is symmetric in the lower indices. -/
theorem christoffel_symm (y : E) (k i j : Fin 4) :
    christoffel D y k i j = christoffel D y k j i := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;> rfl

/-- **The table is the table of Christoffel symbols** of the metric on its domain. -/
theorem christoffelOf_eq (hx : x ∈ domain D) (k i j : Fin 4) :
    christoffelOf (metric D).coefficient x k i j = christoffel D x k i j := by
  have hN := (N_pos_of_mem hx).ne'
  have ha := (a_pos_of_mem hx).ne'
  have hψ := (psi_pos hx).ne'
  rw [metric, christoffelOf_ofDiagonal _ _ _ _ x (coefficients_ne_zero hx)]
  simp only [fderiv_coefficients hx]
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [christoffel, gammaLapse, gammaSpatial, gammaExpansion, gammaConformal, coefficients,
      dotSpace] <;>
    field_simp

/-- The table agrees with the Christoffel symbols near every point of the domain. -/
theorem eventually_christoffelOf_eq (hx : x ∈ domain D) :
    ∀ᶠ z in 𝓝 x, ∀ k i j, christoffelOf (metric D).coefficient z k i j = christoffel D z k i j := by
  filter_upwards [(domain D).isOpen.mem_nhds hx] with z hz using christoffelOf_eq hz

/-! ### Derivatives of the Christoffel symbols -/

/-- The derivative of `Γ⁰₀₀ = Ṅ/N` along `v` is `(N̈N − Ṅ²)/N² v⁰`. -/
theorem fderiv_gammaLapse (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (gammaLapse D) x v =
      (deriv (deriv D.N) (x 0) * D.N (x 0) - deriv D.N (x 0) ^ 2) / D.N (x 0) ^ 2 * v 0 := by
  have hN := (N_pos_of_mem hx).ne'
  have h := hasFDerivAt_time ((hasDerivAt_deriv_N (time_mem hx)).div
    (hasDerivAt_N (time_mem hx)) hN)
  rw [show gammaLapse D = fun z : E => (deriv D.N / D.N) (z 0) from rfl, h.fderiv]
  simp only [smul_apply, proj_apply, smul_eq_mul]
  ring

/-- The derivative of `Γ^α_{0α} = ȧ/a` along `v` is `(äa − ȧ²)/a² v⁰`. -/
theorem fderiv_gammaExpansion (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (gammaExpansion D) x v =
      (deriv (deriv D.a) (x 0) * D.a (x 0) - deriv D.a (x 0) ^ 2) / D.a (x 0) ^ 2 * v 0 := by
  have ha := (a_pos_of_mem hx).ne'
  have h := hasFDerivAt_time ((hasDerivAt_deriv_a (time_mem hx)).div
    (hasDerivAt_a (time_mem hx)) ha)
  rw [show gammaExpansion D = fun z : E => (deriv D.a / D.a) (z 0) from rfl, h.fderiv]
  simp only [smul_apply, proj_apply, smul_eq_mul]
  ring

/-- The derivative of `Γ⁰_{αα} = aȧ/(N²ψ²)` along `v`. -/
theorem fderiv_gammaSpatial (hx : x ∈ domain D) (v : E) :
    fderiv ℝ (gammaSpatial D) x v =
      ((deriv D.a (x 0) ^ 2 + D.a (x 0) * deriv (deriv D.a) (x 0)) * D.N (x 0) * psi D.k x * v 0 -
        2 * D.a (x 0) * deriv D.a (x 0) * deriv D.N (x 0) * psi D.k x * v 0 -
        D.a (x 0) * deriv D.a (x 0) * D.N (x 0) * D.k * dotSpace x v) /
        (D.N (x 0) ^ 3 * psi D.k x ^ 3) := by
  have hN := (N_pos_of_mem hx).ne'
  have hψ := (psi_pos hx).ne'
  have hnum := (hasFDerivAt_time (hasDerivAt_a (time_mem hx))).fun_mul
    (hasFDerivAt_time (hasDerivAt_deriv_a (time_mem hx)))
  have hden := ((hasFDerivAt_time (hasDerivAt_N (time_mem hx))).pow 2).fun_mul
    ((hasFDerivAt_psi D.k x).pow 2)
  rw [show gammaSpatial D = fun z : E =>
      D.a (z 0) * deriv D.a (z 0) / (D.N (z 0) ^ 2 * psi D.k z ^ 2) from rfl,
    (SphericalAnsatz.hasFDerivAt_div hnum hden (by positivity)).fderiv]
  simp only [sub_apply, smul_apply, add_apply, proj_apply, smul_eq_mul, dotSpace]
  push_cast
  field_simp
  ring

/-- The derivative of `σ_i = −k xⁱ/(2ψ)` along `v` is `(k² xⁱ (x·v) − 2k vⁱ ψ)/(4ψ²)`. -/
theorem fderiv_gammaConformal (k : ℝ) (i : Fin 4) {x : E} (hψ : psi k x ≠ 0) (v : E) :
    fderiv ℝ (gammaConformal k i) x v =
      (k ^ 2 * x i * dotSpace x v - 2 * k * v i * psi k x) / (4 * psi k x ^ 2) := by
  have hnum : HasFDerivAt (fun z : E => -(k * z i)) (-(k • (proj i : E →L[ℝ] ℝ))) x :=
    ((hasFDerivAt_apply i x).const_mul k).neg
  rw [show gammaConformal k i = fun z : E => -(k * z i) / (2 * psi k z) from rfl,
    (SphericalAnsatz.hasFDerivAt_div hnum ((hasFDerivAt_psi k x).const_mul 2)
      (mul_ne_zero two_ne_zero hψ)).fderiv]
  simp only [sub_apply, smul_apply, add_apply, neg_apply, proj_apply, smul_eq_mul, dotSpace]
  field_simp
  ring

/-! ### The Ricci tensor -/

variable (D) in
/-- `R₀₀ = −3(ä/a − Ṅȧ/(Na))`. -/
def ricciTime (x : E) : ℝ :=
  -3 * (deriv (deriv D.a) (x 0) / D.a (x 0) -
    deriv D.N (x 0) * deriv D.a (x 0) / (D.N (x 0) * D.a (x 0)))

variable (D) in
/-- `R_{αα} = ((aä + 2ȧ²)/N² − aȧṄ/N³ + 2k)/ψ²`. -/
def ricciSpace (x : E) : ℝ :=
  ((D.a (x 0) * deriv (deriv D.a) (x 0) + 2 * deriv D.a (x 0) ^ 2) / D.N (x 0) ^ 2 -
    D.a (x 0) * deriv D.a (x 0) * deriv D.N (x 0) / D.N (x 0) ^ 3 + 2 * D.k) / psi D.k x ^ 2

variable (D) in
/-- The table of the Ricci tensor: `R₀₀ = ricciTime`, `R_{αβ} = ricciSpace δ_{αβ}`, `R₀α = 0`. -/
def ricci (x : E) : Fin 4 → Fin 4 → ℝ :=
  ![![ricciTime D x, 0, 0, 0], ![0, ricciSpace D x, 0, 0], ![0, 0, ricciSpace D x, 0],
    ![0, 0, 0, ricciSpace D x]]

/-- **The Ricci tensor of the isotropic metric** at every point of the domain is the table
`ricci`. -/
theorem ricciOf_eq (hx : x ∈ domain D) (j k : Fin 4) :
    ricciOf (metric D).coefficient x j k = ricci D x j k := by
  have hN := (N_pos_of_mem hx).ne'
  have ha := (a_pos_of_mem hx).ne'
  have hψ := (psi_pos hx).ne'
  rw [ricciOf_eq_ricciOfChristoffel (eventually_christoffelOf_eq hx)]
  fin_cases j <;> fin_cases k <;>
  · simp only [ricciOfChristoffel, SphericalAnsatz.sum_four, christoffel, ricci, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    simp only [fderiv_gammaLapse hx, fderiv_gammaExpansion hx, fderiv_gammaSpatial hx,
      fderiv_gammaConformal D.k _ hψ, fderiv_fun_neg, fderiv_const_apply, zero_apply, neg_apply]
    simp [gammaLapse, gammaSpatial, gammaExpansion, gammaConformal, ricciTime, ricciSpace,
      dotSpace]
    try field_simp
    try unfold psi
    try ring

/-- `R₀₀ = −3(ä/a − Ṅȧ/(Na))`. -/
theorem ricci_zero_zero (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 0 0 =
      -3 * (deriv (deriv D.a) (x 0) / D.a (x 0) -
        deriv D.N (x 0) * deriv D.a (x 0) / (D.N (x 0) * D.a (x 0))) :=
  ricciOf_eq hx 0 0

/-- `R₀α = 0`. -/
theorem ricci_zero_succ (hx : x ∈ domain D) (α : Fin 3) :
    ricciOf (metric D).coefficient x 0 α.succ = 0 := by
  rw [ricciOf_eq hx]
  fin_cases α <;> rfl

/-- `R_α0 = 0`. -/
theorem ricci_succ_zero (hx : x ∈ domain D) (α : Fin 3) :
    ricciOf (metric D).coefficient x α.succ 0 = 0 := by
  rw [ricciOf_eq hx]
  fin_cases α <;> rfl

/-- `R_{αβ} = ((aä + 2ȧ²)/N² − aȧṄ/N³ + 2k) ψ⁻² δ_{αβ}`. -/
theorem ricci_succ_succ (hx : x ∈ domain D) (α β : Fin 3) :
    ricciOf (metric D).coefficient x α.succ β.succ =
      if α = β then
        ((D.a (x 0) * deriv (deriv D.a) (x 0) + 2 * deriv D.a (x 0) ^ 2) / D.N (x 0) ^ 2 -
          D.a (x 0) * deriv D.a (x 0) * deriv D.N (x 0) / D.N (x 0) ^ 3 + 2 * D.k) /
          psi D.k x ^ 2
      else 0 := by
  rw [ricciOf_eq hx]
  fin_cases α <;> fin_cases β <;> rfl

/-! ### The scalar curvature and the Einstein tensor -/

/-- The inverse of the matrix of coefficients is `diag(1/c)`. -/
theorem coefficient_metric_inv (hx : x ∈ domain D) :
    ((metric D).coefficient x)⁻¹ = Matrix.diagonal fun l => (coefficients D x l)⁻¹ := by
  rw [coefficient_metric]
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one with l
  exact inv_mul_cancel₀ (coefficients_ne_zero hx l)

/-- The scalar curvature `R = ∑ₐ R_{aa}/c_a`. -/
theorem scalarOf_eq_sum (hx : x ∈ domain D) :
    scalarOf (metric D).coefficient x = ∑ a, ricci D x a a / coefficients D x a := by
  rw [scalarOf, coefficient_metric_inv hx]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a (fun c _ hc => by simp [Matrix.diagonal_apply_ne _ (Ne.symm hc)])
    (fun h => absurd (Finset.mem_univ a) h), Matrix.diagonal_apply_eq, ricciOf_eq hx,
    div_eq_mul_inv]

/-- **The scalar curvature** `R = 6((aä + ȧ²)/N² − aȧṄ/N³ + k)/a²`. -/
theorem scalarOf_eq (hx : x ∈ domain D) :
    scalarOf (metric D).coefficient x =
      6 * ((D.a (x 0) * deriv (deriv D.a) (x 0) + deriv D.a (x 0) ^ 2) / D.N (x 0) ^ 2 -
        D.a (x 0) * deriv D.a (x 0) * deriv D.N (x 0) / D.N (x 0) ^ 3 + D.k) / D.a (x 0) ^ 2 := by
  have hN := (N_pos_of_mem hx).ne'
  have ha := (a_pos_of_mem hx).ne'
  have hψ := (psi_pos hx).ne'
  rw [scalarOf_eq_sum hx, SphericalAnsatz.sum_four]
  simp only [ricci, coefficients, ricciTime, ricciSpace, Fin.isValue, Matrix.cons_val]
  field_simp
  ring

variable (D) in
/-- `G₀₀ = 3(ȧ²/a² + N²k/a²)`. -/
def einsteinTime (x : E) : ℝ :=
  3 * ((deriv D.a (x 0) / D.a (x 0)) ^ 2 + D.N (x 0) ^ 2 * D.k / D.a (x 0) ^ 2)

variable (D) in
/-- `G_{αα} = −((2aä + ȧ²)/N² − 2aȧṄ/N³ + k)/ψ²`. -/
def einsteinSpace (x : E) : ℝ :=
  -((2 * D.a (x 0) * deriv (deriv D.a) (x 0) + deriv D.a (x 0) ^ 2) / D.N (x 0) ^ 2 -
    2 * D.a (x 0) * deriv D.a (x 0) * deriv D.N (x 0) / D.N (x 0) ^ 3 + D.k) / psi D.k x ^ 2

variable (D) in
/-- The table of the Einstein tensor: `G₀₀ = einsteinTime`, `G_{αβ} = einsteinSpace δ_{αβ}`,
`G₀α = 0`. -/
def einstein (x : E) : Fin 4 → Fin 4 → ℝ :=
  ![![einsteinTime D x, 0, 0, 0], ![0, einsteinSpace D x, 0, 0], ![0, 0, einsteinSpace D x, 0],
    ![0, 0, 0, einsteinSpace D x]]

/-- **The Einstein tensor of the isotropic metric** at every point of the domain is the table
`einstein`. -/
theorem einsteinOf_eq (hx : x ∈ domain D) (i k : Fin 4) :
    einsteinOf (metric D).coefficient x i k = einstein D x i k := by
  have hN := (N_pos_of_mem hx).ne'
  have ha := (a_pos_of_mem hx).ne'
  have hψ := (psi_pos hx).ne'
  rw [einsteinOf, ricciOf_eq hx, scalarOf_eq hx, coefficient_metric]
  fin_cases i <;> fin_cases k <;>
  · simp [ricci, einstein, coefficients, ricciTime, ricciSpace, einsteinTime, einsteinSpace]
    try field_simp
    try ring

/-- `G₀₀ = 3(ȧ²/a² + N²k/a²)`. -/
theorem einstein_zero_zero (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 0 0 =
      3 * ((deriv D.a (x 0) / D.a (x 0)) ^ 2 + D.N (x 0) ^ 2 * D.k / D.a (x 0) ^ 2) :=
  einsteinOf_eq hx 0 0

/-- `G₀α = 0`. -/
theorem einstein_zero_succ (hx : x ∈ domain D) (α : Fin 3) :
    einsteinOf (metric D).coefficient x 0 α.succ = 0 := by
  rw [einsteinOf_eq hx]
  fin_cases α <;> rfl

/-- `G_α0 = 0`. -/
theorem einstein_succ_zero (hx : x ∈ domain D) (α : Fin 3) :
    einsteinOf (metric D).coefficient x α.succ 0 = 0 := by
  rw [einsteinOf_eq hx]
  fin_cases α <;> rfl

/-- `G_{αβ} = −((2aä + ȧ²)/N² − 2aȧṄ/N³ + k) ψ⁻² δ_{αβ}`. -/
theorem einstein_succ_succ (hx : x ∈ domain D) (α β : Fin 3) :
    einsteinOf (metric D).coefficient x α.succ β.succ =
      if α = β then
        -((2 * D.a (x 0) * deriv (deriv D.a) (x 0) + deriv D.a (x 0) ^ 2) / D.N (x 0) ^ 2 -
          2 * D.a (x 0) * deriv D.a (x 0) * deriv D.N (x 0) / D.N (x 0) ^ 3 + D.k) /
          psi D.k x ^ 2
      else 0 := by
  rw [einsteinOf_eq hx]
  fin_cases α <;> fin_cases β <;> rfl

/-! ### The comoving perfect fluid -/

variable (D) in
/-- The covector `u_μ = g_{μν} u^ν = (−N, 0, 0, 0)` of the comoving four-velocity
`u^μ = (1/N, 0, 0, 0)`. -/
def fluidCovector (x : E) : Fin 4 → ℝ := ![-D.N (x 0), 0, 0, 0]

/-- The comoving four-velocity is a unit timelike vector: `g^{μν} u_μ u_ν = −1`. -/
theorem fluidCovector_norm (hx : x ∈ domain D) :
    ∑ i, ∑ j, ((metric D).coefficient x)⁻¹ i j * fluidCovector D x i * fluidCovector D x j =
      -1 := by
  have hN := (N_pos_of_mem hx).ne'
  rw [coefficient_metric_inv hx]
  simp [SphericalAnsatz.sum_four, fluidCovector, coefficients, Matrix.diagonal_apply]
  field_simp

variable (D) in
/-- **The stress of the comoving perfect fluid** `T_{μν} = (ρ + p) u_μ u_ν + p g_{μν}` with the
energy density `ρ(t)` and the pressure `p(t)` (Landau–Lifshitz, (94.9)). -/
def perfectFluidStress (ρ p : ℝ → ℝ) (x : E) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => (ρ (x 0) + p (x 0)) * fluidCovector D x i * fluidCovector D x j +
    p (x 0) * (metric D).coefficient x i j

variable (D) in
/-- The diagonal entries `(ρN², pa²/ψ², pa²/ψ², pa²/ψ²)` of the stress of the fluid. -/
def fluidDiagonal (ρ p : ℝ → ℝ) (x : E) : Fin 4 → ℝ :=
  ![ρ (x 0) * D.N (x 0) ^ 2, p (x 0) * (D.a (x 0) ^ 2 / psi D.k x ^ 2),
    p (x 0) * (D.a (x 0) ^ 2 / psi D.k x ^ 2), p (x 0) * (D.a (x 0) ^ 2 / psi D.k x ^ 2)]

/-- The stress of the comoving fluid is `diag(ρN², pa²/ψ², pa²/ψ², pa²/ψ²)` at every point. -/
theorem perfectFluidStress_eq (ρ p : ℝ → ℝ) (y : E) :
    perfectFluidStress D ρ p y = Matrix.diagonal (fluidDiagonal D ρ p y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [perfectFluidStress, fluidDiagonal, fluidCovector, coefficient_metric, coefficients]
  ring

/-- `T₀₀ = ρN²`. -/
theorem perfectFluidStress_zero_zero (ρ p : ℝ → ℝ) (y : E) :
    perfectFluidStress D ρ p y 0 0 = ρ (y 0) * D.N (y 0) ^ 2 := by
  rw [perfectFluidStress_eq]
  rfl

/-- `T_{αβ} = p g_{αβ}`. -/
theorem perfectFluidStress_succ_succ (ρ p : ℝ → ℝ) (y : E) (α β : Fin 3) :
    perfectFluidStress D ρ p y α.succ β.succ =
      p (y 0) * (metric D).coefficient y α.succ β.succ := by
  have hu (γ : Fin 3) : fluidCovector D y γ.succ = 0 := by fin_cases γ <;> rfl
  simp [perfectFluidStress, hu]

/-- The stress of the comoving fluid is smooth on the domain where `ρ` and `p` are smooth on the
times. -/
theorem contDiffOn_perfectFluidStress {ρ p : ℝ → ℝ} (hρ : ContDiffOn ℝ ∞ ρ D.I)
    (hp : ContDiffOn ℝ ∞ p D.I) (i j : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => perfectFluidStress D ρ p x i j) (domain D) := by
  have hu (l : Fin 4) : ContDiffOn ℝ ∞ (fun x => fluidCovector D x l) (domain D) := by
    fin_cases l
    · exact (contDiffOn_time D.contDiffOn_N).neg
    · exact contDiffOn_const
    · exact contDiffOn_const
    · exact contDiffOn_const
  exact ((((contDiffOn_time hρ).add (contDiffOn_time hp)).mul (hu i)).mul (hu j)).add
    ((contDiffOn_time hp).mul ((metric D).coefficient_contDiffOn i j))

/-! ### The conservation of the stress of the fluid -/

/-- The derivative of `T₀₀ = ρN²` along `v` is `(ρ̇N² + 2ρNṄ) v⁰`. -/
theorem fderiv_fluidDiagonal_zero {ρ p : ℝ → ℝ} (hx : x ∈ domain D)
    (hρ : DifferentiableAt ℝ ρ (x 0)) (v : E) :
    fderiv ℝ (fun z => fluidDiagonal D ρ p z 0) x v =
      (deriv ρ (x 0) * D.N (x 0) ^ 2 + 2 * ρ (x 0) * D.N (x 0) * deriv D.N (x 0)) * v 0 := by
  have h := hasFDerivAt_time (hρ.hasDerivAt.mul ((hasDerivAt_N (time_mem hx)).pow 2))
  rw [show (fun z => fluidDiagonal D ρ p z 0) = fun z : E => (ρ * D.N ^ 2) (z 0) from rfl,
    h.fderiv]
  simp only [smul_apply, proj_apply, smul_eq_mul, Pi.pow_apply]
  push_cast
  ring

/-- The derivative of `T_{αα} = pa²/ψ²` along `v`. -/
theorem fderiv_fluidSpace {p : ℝ → ℝ} (hx : x ∈ domain D) (hp : DifferentiableAt ℝ p (x 0))
    (v : E) :
    fderiv ℝ (fun z : E => p (z 0) * (D.a (z 0) ^ 2 / psi D.k z ^ 2)) x v =
      deriv p (x 0) * v 0 * (D.a (x 0) ^ 2 / psi D.k x ^ 2) +
        p (x 0) * ((2 * D.a (x 0) * deriv D.a (x 0) * v 0 * psi D.k x -
          D.a (x 0) ^ 2 * D.k * dotSpace x v) / psi D.k x ^ 3) := by
  have hψ := (psi_pos hx).ne'
  have hs := SphericalAnsatz.hasFDerivAt_div ((hasFDerivAt_time (hasDerivAt_a (time_mem hx))).pow 2)
    ((hasFDerivAt_psi D.k x).pow 2) (pow_ne_zero 2 hψ)
  rw [((hasFDerivAt_time hp.hasDerivAt).fun_mul hs).fderiv, ← fderiv_spatialCoefficient hx v,
    hs.fderiv]
  simp only [add_apply, smul_apply, proj_apply, smul_eq_mul]
  ring

/-- The derivatives of the diagonal entries of the stress along a vector `v`. -/
theorem fderiv_fluidDiagonal {ρ p : ℝ → ℝ} (hx : x ∈ domain D) (hρ : DifferentiableAt ℝ ρ (x 0))
    (hp : DifferentiableAt ℝ p (x 0)) (i : Fin 4) (v : E) :
    fderiv ℝ (fun z => fluidDiagonal D ρ p z i) x v =
      ![(deriv ρ (x 0) * D.N (x 0) ^ 2 + 2 * ρ (x 0) * D.N (x 0) * deriv D.N (x 0)) * v 0,
        deriv p (x 0) * v 0 * (D.a (x 0) ^ 2 / psi D.k x ^ 2) +
          p (x 0) * ((2 * D.a (x 0) * deriv D.a (x 0) * v 0 * psi D.k x -
            D.a (x 0) ^ 2 * D.k * dotSpace x v) / psi D.k x ^ 3),
        deriv p (x 0) * v 0 * (D.a (x 0) ^ 2 / psi D.k x ^ 2) +
          p (x 0) * ((2 * D.a (x 0) * deriv D.a (x 0) * v 0 * psi D.k x -
            D.a (x 0) ^ 2 * D.k * dotSpace x v) / psi D.k x ^ 3),
        deriv p (x 0) * v 0 * (D.a (x 0) ^ 2 / psi D.k x ^ 2) +
          p (x 0) * ((2 * D.a (x 0) * deriv D.a (x 0) * v 0 * psi D.k x -
            D.a (x 0) ^ 2 * D.k * dotSpace x v) / psi D.k x ^ 3)] i := by
  fin_cases i
  · exact fderiv_fluidDiagonal_zero hx hρ v
  · exact fderiv_fluidSpace hx hp v
  · exact fderiv_fluidSpace hx hp v
  · exact fderiv_fluidSpace hx hp v

/-- **The divergence of the stress of the comoving fluid**:
`∇^μ T_{μ0} = −(ρ̇ + 3(ȧ/a)(ρ + p))` and `∇^μ T_{μα} = 0` (Landau–Lifshitz, (112.4)). -/
theorem divergenceOf_perfectFluidStress {ρ p : ℝ → ℝ} (hx : x ∈ domain D)
    (hρ : DifferentiableAt ℝ ρ (x 0)) (hp : DifferentiableAt ℝ p (x 0)) (b : Fin 4) :
    (metric D).divergenceOf (perfectFluidStress D ρ p) x b =
      ![-(deriv ρ (x 0) + 3 * (deriv D.a (x 0) / D.a (x 0)) * (ρ (x 0) + p (x 0))), 0, 0, 0] b
      := by
  have hN := (N_pos_of_mem hx).ne'
  have ha := (a_pos_of_mem hx).ne'
  have hψ := (psi_pos hx).ne'
  have hT : (fun z => perfectFluidStress D ρ p z) =
      fun z => Matrix.diagonal (fluidDiagonal D ρ p z) :=
    funext (perfectFluidStress_eq ρ p)
  unfold divergenceOf
  simp only [hT, fderiv_diagonal_apply, fderiv_fluidDiagonal hx hρ hp, coefficient_metric_inv hx,
    christoffelOf_eq hx]
  fin_cases b <;>
    simp [SphericalAnsatz.sum_four, Matrix.diagonal_apply, christoffel, fluidDiagonal,
      coefficients, gammaLapse, gammaSpatial, gammaExpansion, gammaConformal, dotSpace] <;>
    field_simp
  · ring
  all_goals
    right
    ring

/-- **The conservation of the comoving fluid is the continuity equation**: at a point of the
domain, `∇^μ T_{μν} = 0` for every `ν` if and only if `ρ̇ + 3(ȧ/a)(ρ + p) = 0`. -/
theorem comoving_divergence_iff {ρ p : ℝ → ℝ} (hx : x ∈ domain D)
    (hρ : DifferentiableAt ℝ ρ (x 0)) (hp : DifferentiableAt ℝ p (x 0)) :
    (∀ b, (metric D).divergenceOf (perfectFluidStress D ρ p) x b = 0) ↔
      deriv ρ (x 0) + 3 * (deriv D.a (x 0) / D.a (x 0)) * (ρ (x 0) + p (x 0)) = 0 := by
  constructor
  · intro h
    have h0 := h 0
    rwa [divergenceOf_perfectFluidStress hx hρ hp, Matrix.cons_val_zero, neg_eq_zero] at h0
  · intro h b
    rw [divergenceOf_perfectFluidStress hx hρ hp]
    fin_cases b <;> simp [h]

/-- **The native divergence of the comoving fluid** on the co-ordinate fields, for a density and
a pressure smooth on the times: `∇^μ T_{μ0} = −(ρ̇ + 3(ȧ/a)(ρ + p))` and `∇^μ T_{μα} = 0`. -/
theorem bilinearDivergence_perfectFluidStress {ρ p : ℝ → ℝ} (hρ : ContDiffOn ℝ ∞ ρ D.I)
    (hp : ContDiffOn ℝ ∞ p D.I) (y : domain D) (b : Fin 4) :
    (metric D).toLorentzMetric.bilinearDivergenceCovector
        (bilinearOf (perfectFluidStress D ρ p) (contDiffOn_perfectFluidStress hρ hp)) y
        (chartField (physicalChart y) (Pi.single b 1) y) =
      ![-(deriv ρ (y.1 0) + 3 * (deriv D.a (y.1 0) / D.a (y.1 0)) * (ρ (y.1 0) + p (y.1 0))),
        0, 0, 0] b := by
  have ht := time_mem y.property
  rw [bilinearDivergence_bilinearOf, divergenceOf_perfectFluidStress y.property
    ((hρ.contDiffAt (D.isOpen_I.mem_nhds ht)).differentiableAt (by simp))
    ((hp.contDiffAt (D.isOpen_I.mem_nhds ht)).differentiableAt (by simp))]

/-! ### The Friedmann equations -/

variable (D) in
/-- The Hubble rate `H = ȧ/a`. -/
def hubble (t : ℝ) : ℝ := deriv D.a t / D.a t

variable (D) in
/-- **The first Friedmann equation** at the time `t`:
`(ȧ/a)² + N²k/a² = (κ/3) N² ρ + (Λ/3) N²`, the time component `G₀₀ + Λ g₀₀ = κ T₀₀`. -/
def FirstFriedmann (κ Λ : ℝ) (ρ : ℝ → ℝ) (t : ℝ) : Prop :=
  hubble D t ^ 2 + D.N t ^ 2 * D.k / D.a t ^ 2 = κ / 3 * D.N t ^ 2 * ρ t + Λ / 3 * D.N t ^ 2

variable (D) in
/-- **The second Friedmann equation** at the time `t`:
`(2ä/a + (ȧ/a)²)/N² − 2(ȧ/a)Ṅ/N³ + k/a² = −κp + Λ`, the spatial components of the Einstein
equations; for `N = 1` it is `2ä/a + ȧ²/a² + k/a² = −κp + Λ`
(`secondFriedmann_iff_of_lapse_eq_one`). -/
def SecondFriedmann (κ Λ : ℝ) (p : ℝ → ℝ) (t : ℝ) : Prop :=
  (2 * (deriv (deriv D.a) t / D.a t) + hubble D t ^ 2) / D.N t ^ 2 -
      2 * hubble D t * deriv D.N t / D.N t ^ 3 + D.k / D.a t ^ 2 = -κ * p t + Λ

variable (D) in
/-- **The continuity equation** `ρ̇ + 3(ȧ/a)(ρ + p) = 0` at the time `t`. -/
def ContinuityEquation (ρ p : ℝ → ℝ) (t : ℝ) : Prop :=
  deriv ρ t + 3 * hubble D t * (ρ t + p t) = 0

/-- The time component of the Einstein equations is three times the first Friedmann equation:
`G₀₀ + Λ g₀₀ − κ T₀₀ = 3 (H² + N²k/a² − (κ/3) N² ρ − (Λ/3) N²)`. -/
theorem einsteinEquation_zero_zero (hx : x ∈ domain D) (κ Λ : ℝ) (ρ p : ℝ → ℝ) :
    einsteinOf (metric D).coefficient x 0 0 + Λ * (metric D).coefficient x 0 0 -
        κ * perfectFluidStress D ρ p x 0 0 =
      3 * (hubble D (x 0) ^ 2 + D.N (x 0) ^ 2 * D.k / D.a (x 0) ^ 2 -
        (κ / 3 * D.N (x 0) ^ 2 * ρ (x 0) + Λ / 3 * D.N (x 0) ^ 2)) := by
  rw [einstein_zero_zero hx, perfectFluidStress_zero_zero, coefficient_metric]
  simp only [Matrix.diagonal_apply_eq, coefficients, Matrix.cons_val_zero, hubble]
  ring

/-- The diagonal spatial components of the Einstein equations are `−a²/ψ²` times the second
Friedmann equation. -/
theorem einsteinEquation_succ_succ (hx : x ∈ domain D) (κ Λ : ℝ) (ρ p : ℝ → ℝ) (α : Fin 3) :
    einsteinOf (metric D).coefficient x α.succ α.succ + Λ * (metric D).coefficient x α.succ α.succ -
        κ * perfectFluidStress D ρ p x α.succ α.succ =
      -(D.a (x 0) ^ 2 / psi D.k x ^ 2) *
        ((2 * (deriv (deriv D.a) (x 0) / D.a (x 0)) + hubble D (x 0) ^ 2) / D.N (x 0) ^ 2 -
          2 * hubble D (x 0) * deriv D.N (x 0) / D.N (x 0) ^ 3 + D.k / D.a (x 0) ^ 2 -
          (-κ * p (x 0) + Λ)) := by
  have hN := (N_pos_of_mem hx).ne'
  have ha := (a_pos_of_mem hx).ne'
  have hψ := (psi_pos hx).ne'
  have hc : (metric D).coefficient x α.succ α.succ = D.a (x 0) ^ 2 / psi D.k x ^ 2 := by
    rw [coefficient_metric, Matrix.diagonal_apply_eq]
    fin_cases α <;> rfl
  rw [einstein_succ_succ hx, perfectFluidStress_succ_succ, hc]
  simp only [↓reduceIte, hubble]
  field_simp
  ring

/-- **The Einstein equations at a point are the two Friedmann equations**: with the comoving
fluid, `G_{ik} + Λ g_{ik} = κ T_{ik}` at a point of the domain holds for all `i, k` if and only if
the two Friedmann equations hold at its time. -/
theorem isEinstein_at_iff (hx : x ∈ domain D) (κ Λ : ℝ) (ρ p : ℝ → ℝ) :
    (∀ i k, einsteinOf (metric D).coefficient x i k + Λ * (metric D).coefficient x i k =
      κ * perfectFluidStress D ρ p x i k) ↔
      FirstFriedmann D κ Λ ρ (x 0) ∧ SecondFriedmann D κ Λ p (x 0) := by
  have ha := (a_pos_of_mem hx).ne'
  have hψ := (psi_pos hx).ne'
  have hc : D.a (x 0) ^ 2 / psi D.k x ^ 2 ≠ 0 := div_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 hψ)
  constructor
  · intro h
    have h0 := einsteinEquation_zero_zero hx κ Λ ρ p
    have h1 := einsteinEquation_succ_succ hx κ Λ ρ p 0
    rw [h 0 0, sub_self] at h0
    rw [h (Fin.succ 0) (Fin.succ 0), sub_self] at h1
    refine ⟨sub_eq_zero.mp ?_, sub_eq_zero.mp ?_⟩
    · linarith
    · exact (mul_eq_zero.mp h1.symm).resolve_left (neg_ne_zero.mpr hc)
  · rintro ⟨h1, h2⟩ i k
    have e0 := einsteinEquation_zero_zero hx κ Λ ρ p
    have es (α : Fin 3) := einsteinEquation_succ_succ hx κ Λ ρ p α
    rw [sub_eq_zero.mpr h1, mul_zero] at e0
    simp only [sub_eq_zero.mpr h2, mul_zero] at es
    have hoff : i ≠ k → einsteinOf (metric D).coefficient x i k = 0 ∧
        (metric D).coefficient x i k = 0 ∧ perfectFluidStress D ρ p x i k = 0 := by
      intro hik
      rw [einsteinOf_eq hx, coefficient_metric, perfectFluidStress_eq,
        Matrix.diagonal_apply_ne _ hik, Matrix.diagonal_apply_ne _ hik]
      refine ⟨?_, rfl, rfl⟩
      fin_cases i <;> fin_cases k <;> simp_all [einstein]
    by_cases hik : i = k
    · subst hik
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨α, rfl⟩
      · exact sub_eq_zero.mp e0
      · exact sub_eq_zero.mp (es α)
    · obtain ⟨hG, hg, hT⟩ := hoff hik
      rw [hG, hg, hT]
      ring

/-- **The Einstein equations of the isotropic model are the Friedmann equations**: the metric
with the comoving perfect fluid satisfies `G_{ik} + Λ g_{ik} = κ T_{ik}` on the domain if and
only if both Friedmann equations hold at every time of `I`. -/
theorem isEinstein_iff_friedmann (κ Λ : ℝ) (ρ p : ℝ → ℝ) :
    (metric D).IsEinstein κ Λ (perfectFluidStress D ρ p) ↔
      ∀ t ∈ D.I, FirstFriedmann D κ Λ ρ t ∧ SecondFriedmann D κ Λ p t := by
  constructor
  · intro h t ht
    simpa using (isEinstein_at_iff (timeAxis_mem ht) κ Λ ρ p).mp (h _ (timeAxis_mem ht))
  · intro h x hx
    exact (isEinstein_at_iff hx κ Λ ρ p).mpr (h _ (time_mem hx))

/-- **The native Einstein equations are the Friedmann equations**, for a density and a pressure
smooth on the times. -/
theorem satisfiesEinstein_iff_friedmann {ρ p : ℝ → ℝ} (hρ : ContDiffOn ℝ ∞ ρ D.I)
    (hp : ContDiffOn ℝ ∞ p D.I) (κ Λ : ℝ) :
    (metric D).toLorentzMetric.SatisfiesEinstein κ Λ
        (bilinearOf (perfectFluidStress D ρ p) (contDiffOn_perfectFluidStress hρ hp)) ↔
      ∀ t ∈ D.I, FirstFriedmann D κ Λ ρ t ∧ SecondFriedmann D κ Λ p t :=
  (satisfiesEinstein_bilinearOf_iff _ κ Λ).trans (isEinstein_iff_friedmann κ Λ ρ p)

/-- **The conservation of the fluid on the domain is the continuity equation on `I`.** -/
theorem divergence_eq_zero_iff_continuity {ρ p : ℝ → ℝ} (hρ : DifferentiableOn ℝ ρ D.I)
    (hp : DifferentiableOn ℝ p D.I) :
    (∀ x ∈ domain D, ∀ b, (metric D).divergenceOf (perfectFluidStress D ρ p) x b = 0) ↔
      ∀ t ∈ D.I, ContinuityEquation D ρ p t := by
  have hρ' {t : ℝ} (ht : t ∈ D.I) := hρ.differentiableAt (D.isOpen_I.mem_nhds ht)
  have hp' {t : ℝ} (ht : t ∈ D.I) := hp.differentiableAt (D.isOpen_I.mem_nhds ht)
  constructor
  · intro h t ht
    have hx := timeAxis_mem (D := D) ht
    have := (comoving_divergence_iff hx (by simpa using hρ' ht) (by simpa using hp' ht)).mp
      (h _ hx)
    simpa [ContinuityEquation, hubble] using this
  · intro h x hx
    exact (comoving_divergence_iff hx (hρ' (time_mem hx)) (hp' (time_mem hx))).mpr
      (h _ (time_mem hx))

/-! ### Unit lapse -/

/-- With unit lapse on `I`, `Ṅ = 0` on `I`. -/
theorem deriv_N_eq_zero (hN : ∀ s ∈ D.I, D.N s = 1) {t : ℝ} (ht : t ∈ D.I) :
    deriv D.N t = 0 := by
  have h : D.N =ᶠ[𝓝 t] fun _ => 1 := by
    filter_upwards [D.isOpen_I.mem_nhds ht] with s hs using hN s hs
  rw [h.deriv_eq, deriv_const]

/-- With unit lapse the first Friedmann equation is `H² + k/a² = κρ/3 + Λ/3`. -/
theorem firstFriedmann_iff_of_lapse_eq_one (hN : ∀ s ∈ D.I, D.N s = 1) {t : ℝ} (ht : t ∈ D.I)
    (κ Λ : ℝ) (ρ : ℝ → ℝ) :
    FirstFriedmann D κ Λ ρ t ↔ hubble D t ^ 2 + D.k / D.a t ^ 2 = κ * ρ t / 3 + Λ / 3 := by
  unfold FirstFriedmann
  rw [hN t ht]
  constructor <;> intro h <;> linear_combination h

/-- **With unit lapse the second Friedmann equation is** `2ä/a + ȧ²/a² + k/a² = −κp + Λ`
(Landau–Lifshitz, §112). -/
theorem secondFriedmann_iff_of_lapse_eq_one (hN : ∀ s ∈ D.I, D.N s = 1) {t : ℝ}
    (ht : t ∈ D.I) (κ Λ : ℝ) (p : ℝ → ℝ) :
    SecondFriedmann D κ Λ p t ↔
      2 * (deriv (deriv D.a) t / D.a t) + (deriv D.a t / D.a t) ^ 2 + D.k / D.a t ^ 2 =
        -κ * p t + Λ := by
  unfold SecondFriedmann hubble
  rw [hN t ht, deriv_N_eq_zero hN ht]
  simp

/-! ### The continuity equation from the Friedmann equations -/

variable (D) in
/-- The first Friedmann equation without denominators: `ȧ² + kN² − (κρ + Λ) N² a²/3`. -/
def firstDefect (κ Λ : ℝ) (ρ : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv D.a t ^ 2 + D.k * D.N t ^ 2 - (κ * ρ t + Λ) * D.N t ^ 2 * D.a t ^ 2 / 3

variable (D) in
/-- The second Friedmann equation without denominators:
`(2aä + ȧ²) N − 2aȧṄ + kN³ − (−κp + Λ) a² N³`. -/
def secondDefect (κ Λ : ℝ) (p : ℝ → ℝ) (t : ℝ) : ℝ :=
  (2 * D.a t * deriv (deriv D.a) t + deriv D.a t ^ 2) * D.N t -
    2 * D.a t * deriv D.a t * deriv D.N t + D.k * D.N t ^ 3 - (-κ * p t + Λ) * D.a t ^ 2 * D.N t ^ 3

/-- The first Friedmann equation holds at `t ∈ I` if and only if its defect vanishes. -/
theorem firstFriedmann_iff_firstDefect {t : ℝ} (ht : t ∈ D.I) (κ Λ : ℝ) (ρ : ℝ → ℝ) :
    FirstFriedmann D κ Λ ρ t ↔ firstDefect D κ Λ ρ t = 0 := by
  have ha := (D.a_pos t ht).ne'
  have he : firstDefect D κ Λ ρ t = D.a t ^ 2 * (hubble D t ^ 2 + D.N t ^ 2 * D.k / D.a t ^ 2 -
      (κ / 3 * D.N t ^ 2 * ρ t + Λ / 3 * D.N t ^ 2)) := by
    unfold firstDefect hubble
    field_simp
  rw [he, mul_eq_zero, sub_eq_zero, FirstFriedmann]
  simp [ha]

/-- The second Friedmann equation holds at `t ∈ I` if and only if its defect vanishes. -/
theorem secondFriedmann_iff_secondDefect {t : ℝ} (ht : t ∈ D.I) (κ Λ : ℝ) (p : ℝ → ℝ) :
    SecondFriedmann D κ Λ p t ↔ secondDefect D κ Λ p t = 0 := by
  have ha := (D.a_pos t ht).ne'
  have hN := (D.N_pos t ht).ne'
  have he : secondDefect D κ Λ p t = D.a t ^ 2 * D.N t ^ 3 *
      ((2 * (deriv (deriv D.a) t / D.a t) + hubble D t ^ 2) / D.N t ^ 2 -
        2 * hubble D t * deriv D.N t / D.N t ^ 3 + D.k / D.a t ^ 2 - (-κ * p t + Λ)) := by
    unfold secondDefect hubble
    field_simp
  rw [he, mul_eq_zero, sub_eq_zero, SecondFriedmann]
  simp [ha, hN]

/-- The derivative of the defect of the first Friedmann equation:
`2ȧä + 2kNṄ − (κρ̇N²a² + (κρ + Λ)(2NṄa² + 2N²aȧ))/3`. -/
theorem hasDerivAt_firstDefect {t : ℝ} (ht : t ∈ D.I) (κ Λ : ℝ) {ρ : ℝ → ℝ}
    (hρ : DifferentiableAt ℝ ρ t) :
    HasDerivAt (firstDefect D κ Λ ρ)
      (2 * deriv D.a t * deriv (deriv D.a) t + 2 * D.k * D.N t * deriv D.N t -
        (κ * deriv ρ t * D.N t ^ 2 * D.a t ^ 2 + (κ * ρ t + Λ) *
          (2 * D.N t * deriv D.N t * D.a t ^ 2 + 2 * D.N t ^ 2 * D.a t * deriv D.a t)) / 3) t := by
  have h := (((hasDerivAt_deriv_a ht).pow 2).add ((hasDerivAt_N ht).pow 2 |>.const_mul D.k)).sub
    ((((hρ.hasDerivAt.const_mul κ).add_const Λ).mul ((hasDerivAt_N ht).pow 2)).mul
      ((hasDerivAt_a ht).pow 2) |>.div_const 3)
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.mul_apply]
  push_cast
  ring

variable (D) in
/-- The defect of the first Friedmann equation, differentiated, against the two defects and the
continuity equation: `aN f' = (2aṄ − ȧN) f + ȧ e − (κa²N³/3)(aρ̇ + 3ȧ(ρ + p))`. -/
theorem friedmann_identity (t κ Λ : ℝ) (ρ p : ℝ → ℝ) :
    D.a t * D.N t * (2 * deriv D.a t * deriv (deriv D.a) t + 2 * D.k * D.N t * deriv D.N t -
        (κ * deriv ρ t * D.N t ^ 2 * D.a t ^ 2 + (κ * ρ t + Λ) *
          (2 * D.N t * deriv D.N t * D.a t ^ 2 + 2 * D.N t ^ 2 * D.a t * deriv D.a t)) / 3) =
      (2 * D.a t * deriv D.N t - deriv D.a t * D.N t) * firstDefect D κ Λ ρ t +
        deriv D.a t * secondDefect D κ Λ p t -
        κ * D.a t ^ 2 * D.N t ^ 3 / 3 * (D.a t * deriv ρ t + 3 * deriv D.a t * (ρ t + p t)) := by
  unfold firstDefect secondDefect
  ring

/-- If the first Friedmann equation holds on `I`, its defect has derivative zero at `t ∈ I`. -/
theorem deriv_firstDefect_eq_zero {κ Λ : ℝ} {ρ : ℝ → ℝ} {t : ℝ} (ht : t ∈ D.I)
    (hρ : DifferentiableAt ℝ ρ t) (h1 : ∀ s ∈ D.I, FirstFriedmann D κ Λ ρ s) :
    2 * deriv D.a t * deriv (deriv D.a) t + 2 * D.k * D.N t * deriv D.N t -
        (κ * deriv ρ t * D.N t ^ 2 * D.a t ^ 2 + (κ * ρ t + Λ) *
          (2 * D.N t * deriv D.N t * D.a t ^ 2 + 2 * D.N t ^ 2 * D.a t * deriv D.a t)) / 3 = 0 := by
  have hzero : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 t] firstDefect D κ Λ ρ := by
    filter_upwards [D.isOpen_I.mem_nhds ht] with s hs
    exact ((firstFriedmann_iff_firstDefect hs κ Λ ρ).mp (h1 s hs)).symm
  exact ((hasDerivAt_const t (0 : ℝ)).unique
    ((hasDerivAt_firstDefect ht κ Λ hρ).congr_of_eventuallyEq hzero)).symm

/-- `a(ρ̇ + 3(ȧ/a)(ρ + p)) = aρ̇ + 3ȧ(ρ + p)`. -/
theorem mul_continuity {t : ℝ} (ht : t ∈ D.I) (ρ p : ℝ → ℝ) :
    D.a t * (deriv ρ t + 3 * hubble D t * (ρ t + p t)) =
      D.a t * deriv ρ t + 3 * deriv D.a t * (ρ t + p t) := by
  have ha := (D.a_pos t ht).ne'
  unfold hubble
  field_simp

/-- **The continuity equation follows from the Friedmann equations** (Landau–Lifshitz, §112):
if the first Friedmann equation holds on `I` and the second at `t ∈ I`, then
`ρ̇ + 3(ȧ/a)(ρ + p) = 0` at `t`, for `κ ≠ 0`. No division by the Hubble rate is made: the
derivative of the first equation minus `ȧ` times the second is
`−(κa²N³/3)(aρ̇ + 3ȧ(ρ + p))/(aN)`, so the statement holds at a turning point `ȧ = 0`. -/
theorem continuity_of_friedmann {κ Λ : ℝ} (hκ : κ ≠ 0) {ρ p : ℝ → ℝ} {t : ℝ} (ht : t ∈ D.I)
    (hρ : DifferentiableAt ℝ ρ t) (h1 : ∀ s ∈ D.I, FirstFriedmann D κ Λ ρ s)
    (h2 : SecondFriedmann D κ Λ p t) : ContinuityEquation D ρ p t := by
  have ha := (D.a_pos t ht).ne'
  have hN := (D.N_pos t ht).ne'
  have e1 := (firstFriedmann_iff_firstDefect ht κ Λ ρ).mp (h1 t ht)
  have e2 := (secondFriedmann_iff_secondDefect ht κ Λ p).mp h2
  have hd := deriv_firstDefect_eq_zero ht hρ h1
  have hid := friedmann_identity D t κ Λ ρ p
  rw [hd, mul_zero, e1, e2] at hid
  have hc : D.a t * deriv ρ t + 3 * deriv D.a t * (ρ t + p t) = 0 := by
    have hk : κ * D.a t ^ 2 * D.N t ^ 3 / 3 ≠ 0 := by positivity
    have h0 : κ * D.a t ^ 2 * D.N t ^ 3 / 3 *
        (D.a t * deriv ρ t + 3 * deriv D.a t * (ρ t + p t)) = 0 := by
      linear_combination hid
    exact (mul_eq_zero.mp h0).resolve_left hk
  have hm := mul_continuity ht ρ p
  rw [hc] at hm
  exact (mul_eq_zero.mp hm).resolve_left ha

/-- **The second Friedmann equation follows from the first and the continuity equation where
`ȧ ≠ 0`**: if the first equation holds on `I` and the continuity equation at `t ∈ I` with
`ȧ(t) ≠ 0`, then the second equation holds at `t`. At a turning point it can fail
(`not_secondFriedmann_static`). -/
theorem second_of_first_of_continuity {κ Λ : ℝ} {ρ p : ℝ → ℝ} {t : ℝ} (ht : t ∈ D.I)
    (hda : deriv D.a t ≠ 0) (hρ : DifferentiableAt ℝ ρ t)
    (h1 : ∀ s ∈ D.I, FirstFriedmann D κ Λ ρ s) (hc : ContinuityEquation D ρ p t) :
    SecondFriedmann D κ Λ p t := by
  have e1 := (firstFriedmann_iff_firstDefect ht κ Λ ρ).mp (h1 t ht)
  have hd := deriv_firstDefect_eq_zero ht hρ h1
  have hid := friedmann_identity D t κ Λ ρ p
  have hm := mul_continuity ht ρ p
  rw [show deriv ρ t + 3 * hubble D t * (ρ t + p t) = 0 from hc, mul_zero] at hm
  rw [hd, mul_zero, e1, ← hm] at hid
  refine (secondFriedmann_iff_secondDefect ht κ Λ p).mpr ?_
  have h0 : deriv D.a t * secondDefect D κ Λ p t = 0 := by linear_combination -hid
  exact (mul_eq_zero.mp h0).resolve_left hda

/-! ### The sign of the curvature -/

/-- With unit lapse and `Λ = 0` the first Friedmann equation gives `k = a²(κρ/3 − H²)`. -/
theorem curvature_eq {κ : ℝ} {ρ : ℝ → ℝ} {t : ℝ} (ht : t ∈ D.I) (hN : D.N t = 1)
    (h : FirstFriedmann D κ 0 ρ t) : D.k = D.a t ^ 2 * (κ * ρ t / 3 - hubble D t ^ 2) := by
  have ha := (D.a_pos t ht).ne'
  unfold FirstFriedmann at h
  rw [hN] at h
  field_simp at h ⊢
  linear_combination h

/-- **The sign of the curvature** (Landau–Lifshitz, §§112–113): with unit lapse, `Λ = 0` and
`κ > 0`, the curvature constant `k` has the sign of `ρ − 3H²/κ`, the excess of the density over
the critical density: the space is closed for `ρ > 3H²/κ`, flat at the critical density and
open below it. -/
theorem curvature_sign {κ : ℝ} (hκ : 0 < κ) {ρ : ℝ → ℝ} {t : ℝ} (ht : t ∈ D.I)
    (hN : D.N t = 1) (h : FirstFriedmann D κ 0 ρ t) :
    SignType.sign D.k = SignType.sign (ρ t - 3 * hubble D t ^ 2 / κ) := by
  have ha := D.a_pos t ht
  have he : D.a t ^ 2 * (κ * ρ t / 3 - hubble D t ^ 2) =
      D.a t ^ 2 * κ / 3 * (ρ t - 3 * hubble D t ^ 2 / κ) := by
    field_simp
  rw [curvature_eq ht hN h, he, sign_mul, sign_pos (by positivity), one_mul]

/-! ### Regression: de Sitter space -/

/-- The empty fluid has no stress. -/
@[simp] theorem perfectFluidStress_zero : perfectFluidStress D 0 0 = 0 := by
  funext y
  ext i j
  simp [perfectFluidStress]

/-- Every point of the model is in the domain of de Sitter space. -/
theorem mem_domain_deSitter (z : E) : z ∈ domain Data.deSitter :=
  ⟨mem_univ _, by simp [psi, Data.deSitter]⟩

/-- **De Sitter space in the flat slicing is the isotropic model** `N = 1`, `a = eᵗ`, `k = 0`:
the two matrices of coefficients agree at every point. -/
theorem coefficient_deSitter :
    (metric Data.deSitter).coefficient = DeSitterSlicing.metric.coefficient := by
  funext z
  rw [coefficient_metric, DeSitterSlicing.coefficient_eq]
  congr 1
  funext i
  have he : Real.exp (2 * z 0) = Real.exp (z 0) ^ 2 := by
    rw [show 2 * z 0 = z 0 + z 0 by ring, Real.exp_add]
    ring
  fin_cases i <;> simp [coefficients, DeSitterSlicing.coefficients, Data.deSitter, psi, he]

/-- **Regression: the formulas reproduce `Ric = 3g` for de Sitter space.** The table `ricci`
with `N = 1`, `a = eᵗ`, `k = 0` is the Ricci tensor `DeSitterSlicing.ricci_eq` computed from the
synchronous system. -/
theorem ricci_deSitter (z : E) (i j : Fin 4) :
    ricci Data.deSitter z i j = ricciOf DeSitterSlicing.metric.coefficient z i j := by
  rw [DeSitterSlicing.ricci_eq, DeSitterSlicing.coefficient_eq]
  have he : Real.exp (2 * z 0) = Real.exp (z 0) ^ 2 := by
    rw [show 2 * z 0 = z 0 + z 0 by ring, Real.exp_add]
    ring
  fin_cases i <;> fin_cases j <;>
    simp [ricci, ricciTime, ricciSpace, Data.deSitter, DeSitterSlicing.coefficients, psi,
      Real.deriv_exp, he] <;>
    ring

/-- De Sitter space as an isotropic model satisfies `Ric = 3g`. -/
theorem ricciOf_deSitter (z : E) (i j : Fin 4) :
    ricciOf (metric Data.deSitter).coefficient z i j =
      3 * (metric Data.deSitter).coefficient z i j := by
  rw [ricciOf_eq (mem_domain_deSitter z), ricci_deSitter, DeSitterSlicing.ricci_eq,
    coefficient_deSitter]

/-- De Sitter space satisfies the vacuum Einstein equations with `Λ = 3` for every coupling
constant: both Friedmann equations hold with `H = 1`, `ρ = p = 0`. -/
theorem isEinstein_deSitter (κ : ℝ) : (metric Data.deSitter).IsEinstein κ 3 0 := by
  rw [← perfectFluidStress_zero, isEinstein_iff_friedmann]
  intro t _
  simp [FirstFriedmann, SecondFriedmann, hubble, Data.deSitter, Real.deriv_exp]
  norm_num

/-! ### Regression: the Milne universe -/

/-- The Milne universe is Ricci flat: `ä = 0`, `ȧ = 1` and `k = −1` give `R_{ik} = 0`. -/
theorem ricciOf_milne {z : E} (hz : z ∈ domain Data.milne) (i j : Fin 4) :
    ricciOf (metric Data.milne).coefficient z i j = 0 := by
  rw [ricciOf_eq hz]
  fin_cases i <;> fin_cases j <;> simp [ricci, ricciTime, ricciSpace, Data.milne]

/-- **The empty Milne universe** `N = 1`, `a = t`, `k = −1` on `t > 0` satisfies the vacuum
Einstein equations: `H = 1/t` and `H² − 1/t² = 0`. -/
theorem isEinstein_milne (κ : ℝ) : (metric Data.milne).IsEinstein κ 0 0 := by
  rw [← perfectFluidStress_zero, isEinstein_iff_friedmann]
  intro t ht
  have h : t ≠ 0 := (show 0 < t from ht).ne'
  simp [FirstFriedmann, SecondFriedmann, hubble, Data.milne]
  ring

/-! ### Regression: a static model -/

/-- The static model `N = 1`, `a = 1`, `k = 0` for all times. -/
def Data.static : Data where
  I := univ
  N := fun _ => 1
  a := fun _ => 1
  k := 0
  isOpen_I := isOpen_univ
  contDiffOn_N := contDiffOn_const
  contDiffOn_a := contDiffOn_const
  N_pos := fun _ _ => one_pos
  a_pos := fun _ _ => one_pos

/-- **At a turning point the second equation does not follow**: in the static model with
`ρ = 0` and the pressure `p = 1`, the first Friedmann equation holds at all times and the
continuity equation holds, but the second equation fails for `κ ≠ 0`. The hypothesis `ȧ ≠ 0` of
`second_of_first_of_continuity` cannot be dropped. -/
theorem not_secondFriedmann_static {κ : ℝ} (hκ : κ ≠ 0) (t : ℝ) :
    (∀ s ∈ Data.static.I, FirstFriedmann Data.static κ 0 0 s) ∧
      ContinuityEquation Data.static 0 (fun _ => 1) t ∧
      ¬ SecondFriedmann Data.static κ 0 (fun _ => 1) t := by
  refine ⟨fun s _ => ?_, ?_, ?_⟩
  · simp [FirstFriedmann, hubble, Data.static]
  · simp [ContinuityEquation, hubble, Data.static]
  · simp [SecondFriedmann, hubble, Data.static, hκ]

/-! ### Regression: de Sitter space in the closed slicing -/

/-- De Sitter space in the closed slicing: `N = 1`, `a = cosh t`, `k = 1` for all times, with the
turning point `ȧ = 0` at `t = 0`. -/
def Data.closedDeSitter : Data where
  I := univ
  N := fun _ => 1
  a := Real.cosh
  k := 1
  isOpen_I := isOpen_univ
  contDiffOn_N := contDiffOn_const
  contDiffOn_a := Real.contDiff_cosh.contDiffOn
  N_pos := fun _ _ => one_pos
  a_pos := fun t _ => Real.cosh_pos t

/-- De Sitter space in the closed slicing satisfies the vacuum Einstein equations with `Λ = 3`:
`tanh²t + 1/cosh²t = 1`. -/
theorem isEinstein_closedDeSitter (κ : ℝ) : (metric Data.closedDeSitter).IsEinstein κ 3 0 := by
  rw [← perfectFluidStress_zero, isEinstein_iff_friedmann]
  intro t _
  have hc := (Real.cosh_pos t).ne'
  have hs := Real.cosh_sq t
  simp only [FirstFriedmann, SecondFriedmann, hubble, Data.closedDeSitter, Real.deriv_cosh,
    Real.deriv_sinh, Pi.zero_apply, deriv_const']
  constructor
  · field_simp
    linear_combination -3 * hs
  · field_simp
    linear_combination -hs

end ProjectAinos.GeneralRelativity.FLRW
