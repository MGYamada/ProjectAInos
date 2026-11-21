/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.FLRW
public import ProjectAinos.SmoothGeometry.Lorentzian.CurvedLinearization
public import ProjectAinos.SmoothGeometry.Lorentzian.Synchronous
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
# The gravitational stability of an isotropic universe

Landau–Lifshitz, §115, for the flat isotropic background in the synchronous reference system,
with the signature `(−+++)`, `c = 1`, a coupling constant `κ` (`G_{ik} = κ T_{ik}`) and `Λ = 0`.
A `Background` is an open set `I` of times and a scale factor `a`; its metric
`ds² = −dt² + a(t)² (dx₁² + dx₂² + dx₃²)` is `FLRW.metric` with unit lapse and `k = 0`
(`Background.toData`), with the domain `t ∈ I` (`mem_domain_iff`).

* **The linearization.** For a field `h_{αβ}` of symmetric spatial matrices, smooth on the domain
  (`IsPerturbation`), the family `γ_{αβ} = a² (δ_{αβ} + ε h_{αβ})` (`perturbedCoefficient`) keeps
  the metric synchronous (`perturbedCoefficient_synchronous`). The variation of the Christoffel
  symbols is the table `linChristoffel` (`curvedChristoffel_eq`, through the covariant first
  variation of `CurvedLinearization`), and `ricci_synchronous_deriv` gives the derivatives in `ε`
  at `0` of the Ricci tensor: `δR₀₀ = −½ ∂ₜ²h − (ȧ/a) ∂ₜh`,
  `δR₀α = ½ (∂_γ∂ₜh_{γα} − ∂ₜ∂_α h)` and
  `δR_{αβ} = δP_{αβ} + (2ȧ² + aä) h_{αβ} + (3/2) aȧ ∂ₜh_{αβ} + ½ a² ∂ₜ²h_{αβ} + ½ aȧ ∂ₜh δ_{αβ}`,
  with `h = h_γγ` and the variation `δP_{αβ}` of the Ricci tensor of the sections (`linRicci`,
  `hasDerivAt_ricciOf_perturbed`). The derivatives are `dh` and `ddh`.
* **The equations with dust.** The density `ρ(t)(1 + εδ)` and the covariant velocity
  `u = (−1, ε v_α)` give the trace-reversed source `ρ (u_i u_k + ½ g_{ik})` (`dustSource`).
  `LinearizedEinsteinDust` is `δR_{ik} = κ δS_{ik}` with the table `linDust`; it is the vanishing
  of the derivative at `ε = 0` of the residual `dustResidual` (`linearizedEinsteinDust_iff_deriv`,
  `hasDerivAt_dustResidual`), which vanishes at `ε = 0` on a background solution
  (`dustResidual_zero`, `dust_background`: `ȧ² = κρa²/3`, `aä = −κρa²/6`).
* **Plane waves.** For `h_{αβ} = F_{αβ}(t) k(n · x)` (`mode`) with `k'' = −k` (`IsProfile`:
  `cos`, `sin`), `δ = δ̂(t) k(n · x)` and `v_α = V_α(t) k'(n · x)`, the linearized equations are
  equivalent to ordinary differential equations for the amplitudes (`mode_iff`, with the
  amplitudes `modeTime`, `modeMixed`, `modeSpace`).
* **Scalar modes.** `scalarMode_iff`: for the mode
  `h_{αβ} = λ(t)(n_α n_β/n² − δ_{αβ}/3) cos(n · x) + μ(t)(δ_{αβ}/3) cos(n · x)` on a dust
  solution, with `δ = δ̂ cos(n · x)` and `v_α = w n_α sin(n · x)`, the equations are
  `λ̈ + 3Hλ̇ + n²(μ − λ)/(3a²) = 0`, `μ̈ + 3Hμ̇ + n²(μ − λ)/(3a²) = 0`, `κρδ̂ = −(μ̈ + 2Hμ̇)` and
  `μ̇ − λ̇ = −3κρw` (`scalar_decomp_eq_zero_iff` separates the two tensors).
* **The flat dust universe** `a = t^{2/3}`, `ρ = 4/(3κt²)` (`dustBackground`, `dustDensity`,
  `isEinstein_dustBackground`). `densityContrast_growing`: the comoving mode with
  `δ = c t^{2/3} cos(n · x)`; `densityContrast_decaying`: the comoving mode with
  `δ = c t⁻¹ cos(n · x)`. `gaugeMode`: the synchronous change of the time
  `t ↦ t + F cos(n · x)` (`gaugeField`) gives the mode `λ = 6F n² t^{−1/3}`,
  `μ = λ + 4F/t`, `δ = −2F t⁻¹ cos(n · x)`, `v_α = F n_α sin(n · x)`: a solution that is the
  derivative of the pulled-back background (`familyCoeffDeriv_pullback_gaugeField`,
  `coordinateLieMetric_gaugeField`, for any flat background with `P' = a⁻²`), not a physical
  perturbation. The second fictitious mode `λ = μ = const` is the change of the spatial
  co-ordinates along `spatialGaugeField` (`coordinateLieMetric_spatialGaugeField`,
  `spatialGaugeMode`).
* **Tensor and vector modes.** `tensorMode_iff`: for a symmetric, traceless, transverse
  polarization (`IsTensorPolarization`, `isTensorPolarization_plus`),
  `h_{αβ} = τ(t) e_{αβ} cos(n · x)` solves the equations if and only if
  `τ̈ + 3(ȧ/a) τ̇ + (n²/a²) τ = 0`. `vectorMode_iff`, `vectorMode_decay`: for
  `h_{αβ} = σ(t)(n_α e_β + n_β e_α) sin(n · x)` with `e · n = 0` and `v_α = w e_α cos(n · x)`,
  `σ̈ + 3(ȧ/a) σ̇ = 0` and `n² σ̇ = −2κρw`, so `σ̇ = C/a³` and `κρw = −n²C/(2a³)`;
  `vectorMode_dust` is the solution `σ = −c/t`, `w = −3n²c/8` on the dust universe.

The closed and open models (`k = ±1`) and the reduction of a general perturbation to plane waves
are not treated here.
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap Set TopologicalSpace Filter
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.CosmologicalPerturbation

open SmoothGeometry CoordinateMetric FLRW

local notation "E" => MinkowskiModel 3

/-! ### The flat background -/

/-- **The flat isotropic background**: an open set `I` of times and a scale factor `a`, smooth and
positive on `I`; the metric is `ds² = −dt² + a(t)² (dx₁² + dx₂² + dx₃²)`, the isotropic model of
`FLRW` with unit lapse and `k = 0` (`toData`). -/
structure Background where
  /-- The open set of times. -/
  I : Set ℝ
  /-- The scale factor `a(t)`. -/
  a : ℝ → ℝ
  /-- The set of times is open. -/
  isOpen_I : IsOpen I
  /-- The scale factor is smooth on `I`. -/
  contDiffOn_a : ContDiffOn ℝ ∞ a I
  /-- The scale factor is positive on `I`. -/
  a_pos : ∀ t ∈ I, 0 < a t

namespace Background

/-- The background as an isotropic model with unit lapse and flat sections. -/
def toData (B : Background) : Data where
  I := B.I
  N := fun _ => 1
  a := B.a
  k := 0
  isOpen_I := B.isOpen_I
  contDiffOn_N := contDiffOn_const
  contDiffOn_a := B.contDiffOn_a
  N_pos := fun _ _ => one_pos
  a_pos := B.a_pos

@[simp] theorem toData_I (B : Background) : B.toData.I = B.I := rfl

@[simp] theorem toData_N (B : Background) : B.toData.N = fun _ => 1 := rfl

@[simp] theorem toData_a (B : Background) : B.toData.a = B.a := rfl

@[simp] theorem toData_k (B : Background) : B.toData.k = 0 := rfl

end Background

variable {B : Background} {x z : E}

/-- A point lies in the domain if and only if its time lies in `I`. -/
theorem mem_domain_iff : z ∈ domain B.toData ↔ z 0 ∈ B.I := by
  change z 0 ∈ B.I ∧ 0 < psi 0 z ↔ _
  simp [psi]

theorem time_mem_I (hz : z ∈ domain B.toData) : z 0 ∈ B.I := mem_domain_iff.mp hz

theorem a_pos' (hz : z ∈ domain B.toData) : 0 < B.a (z 0) := B.a_pos _ (time_mem_I hz)

/-- The background is synchronous. -/
theorem isSynchronous_background : (metric B.toData).IsSynchronous :=
  isSynchronous fun _ _ => rfl

/-- The time row of the background coefficients. -/
theorem coefficient_zero_zero : (metric B.toData).coefficient z 0 0 = -1 := by
  simp [coefficient_metric, coefficients, Background.toData]

theorem coefficient_zero_succ (α : Fin 3) : (metric B.toData).coefficient z 0 α.succ = 0 := by
  simp [coefficient_metric, Matrix.diagonal_apply_ne _ (Fin.succ_ne_zero α).symm]

theorem coefficient_succ_zero (α : Fin 3) : (metric B.toData).coefficient z α.succ 0 = 0 := by
  simp [coefficient_metric]

/-- The spatial coefficients `a² δ_{αβ}`. -/
theorem coefficient_succ_succ (α β : Fin 3) :
    (metric B.toData).coefficient z α.succ β.succ = if α = β then B.a (z 0) ^ 2 else 0 := by
  rw [coefficient_metric]
  by_cases hab : α = β
  · subst hab
    simp only [Matrix.diagonal_apply_eq, ite_true]
    fin_cases α <;> simp [coefficients, Background.toData, psi]
  · rw [Matrix.diagonal_apply_ne _ (fun h => hab (Fin.succ_injective _ h))]
    simp [hab]

/-- The inverse coefficients: `g^{00} = −1`, `g^{0α} = 0` and `g^{αβ} = a⁻² δ^{αβ}`. -/
theorem inv_zero_zero (hz : z ∈ domain B.toData) :
    ((metric B.toData).coefficient z)⁻¹ 0 0 = -1 := by
  rw [coefficient_metric_inv hz, Matrix.diagonal_apply_eq]
  simp [coefficients, Background.toData]

theorem inv_zero_succ (hz : z ∈ domain B.toData) (α : Fin 3) :
    ((metric B.toData).coefficient z)⁻¹ 0 α.succ = 0 := by
  rw [coefficient_metric_inv hz, Matrix.diagonal_apply_ne _ (Fin.succ_ne_zero α).symm]

theorem inv_succ_zero (hz : z ∈ domain B.toData) (α : Fin 3) :
    ((metric B.toData).coefficient z)⁻¹ α.succ 0 = 0 := by
  rw [coefficient_metric_inv hz, Matrix.diagonal_apply_ne _ (Fin.succ_ne_zero α)]

theorem inv_succ_succ (hz : z ∈ domain B.toData) (α β : Fin 3) :
    ((metric B.toData).coefficient z)⁻¹ α.succ β.succ =
      if α = β then (B.a (z 0) ^ 2)⁻¹ else 0 := by
  rw [coefficient_metric_inv hz]
  by_cases hab : α = β
  · subst hab
    rw [Matrix.diagonal_apply_eq]
    fin_cases α <;> simp [coefficients, Background.toData, psi]
  · rw [Matrix.diagonal_apply_ne _ (fun h => hab (Fin.succ_injective _ h))]
    simp [hab]

/-! ### The Christoffel symbols of the background -/

/-- `Γ^k_{00} = 0`. -/
theorem bgΓ_zero_zero (hz : z ∈ domain B.toData) (k : Fin 4) :
    christoffelOf (metric B.toData).coefficient z k 0 0 = 0 :=
  isSynchronous_background.christoffel_zero_zero hz k

/-- `Γ^0_{0j} = 0`. -/
theorem bgΓ_zero_zero_left (hz : z ∈ domain B.toData) (j : Fin 4) :
    christoffelOf (metric B.toData).coefficient z 0 0 j = 0 :=
  isSynchronous_background.christoffel_zero_zero_succ hz j

/-- `Γ^0_{j0} = 0`. -/
theorem bgΓ_zero_left_zero (hz : z ∈ domain B.toData) (j : Fin 4) :
    christoffelOf (metric B.toData).coefficient z 0 j 0 = 0 :=
  isSynchronous_background.christoffel_zero_succ_zero hz j

/-- `Γ^0_{αβ} = a ȧ δ_{αβ}`. -/
theorem bgΓ_zero_succ_succ (hz : z ∈ domain B.toData) (α β : Fin 3) :
    christoffelOf (metric B.toData).coefficient z 0 α.succ β.succ =
      if α = β then B.a (z 0) * deriv B.a (z 0) else 0 := by
  rw [christoffelOf_eq hz]
  fin_cases α <;> fin_cases β <;>
    simp [christoffel, gammaSpatial, Background.toData, psi]

/-- `Γ^γ_{0β} = (ȧ/a) δ_{γβ}`. -/
theorem bgΓ_succ_zero_succ (hz : z ∈ domain B.toData) (γ β : Fin 3) :
    christoffelOf (metric B.toData).coefficient z γ.succ 0 β.succ =
      if γ = β then deriv B.a (z 0) / B.a (z 0) else 0 := by
  rw [christoffelOf_eq hz]
  fin_cases γ <;> fin_cases β <;>
    simp [christoffel, gammaExpansion, Background.toData]

/-- `Γ^γ_{β0} = (ȧ/a) δ_{γβ}`. -/
theorem bgΓ_succ_succ_zero (hz : z ∈ domain B.toData) (γ β : Fin 3) :
    christoffelOf (metric B.toData).coefficient z γ.succ β.succ 0 =
      if γ = β then deriv B.a (z 0) / B.a (z 0) else 0 := by
  rw [christoffelOf_eq hz]
  fin_cases γ <;> fin_cases β <;>
    simp [christoffel, gammaExpansion, Background.toData]

/-- `Γ^γ_{αβ} = 0`: the sections are flat. -/
theorem bgΓ_succ_succ_succ (hz : z ∈ domain B.toData) (γ α β : Fin 3) :
    christoffelOf (metric B.toData).coefficient z γ.succ α.succ β.succ = 0 := by
  rw [christoffelOf_eq hz]
  fin_cases γ <;> fin_cases α <;> fin_cases β <;>
    simp [christoffel, gammaConformal, Background.toData]

/-! ### Functions of the time -/

/-- The product rule for `w ↦ φ(w⁰) f(w)`. -/
theorem hasFDerivAt_time_mul {φ : ℝ → ℝ} {φ' : ℝ} (hφ : HasDerivAt φ φ' (z 0)) {f : E → ℝ}
    {f' : E →L[ℝ] ℝ} (hf : HasFDerivAt f f' z) :
    HasFDerivAt (fun w : E => φ (w 0) * f w) (φ (z 0) • f' + f z • (φ' • proj 0)) z :=
  (hasFDerivAt_time hφ).mul hf

theorem fderiv_time_mul {φ : ℝ → ℝ} {φ' : ℝ} (hφ : HasDerivAt φ φ' (z 0)) {f : E → ℝ}
    (hf : DifferentiableAt ℝ f z) (v : E) :
    fderiv ℝ (fun w : E => φ (w 0) * f w) z v = φ' * v 0 * f z + φ (z 0) * fderiv ℝ f z v := by
  rw [(hasFDerivAt_time_mul hφ hf.hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, proj_apply, smul_eq_mul]
  ring

/-- The derivative of a function of the time alone. -/
theorem fderiv_time {φ : ℝ → ℝ} {φ' : ℝ} (hφ : HasDerivAt φ φ' (z 0)) (v : E) :
    fderiv ℝ (fun w : E => φ (w 0)) z v = φ' * v 0 := by
  rw [(hasFDerivAt_time hφ).fderiv]
  simp only [smul_apply, proj_apply, smul_eq_mul]

theorem hasDerivAt_a' {t : ℝ} (ht : t ∈ B.I) : HasDerivAt B.a (deriv B.a t) t :=
  hasDerivAt_a (D := B.toData) ht

theorem hasDerivAt_deriv_a' {t : ℝ} (ht : t ∈ B.I) :
    HasDerivAt (deriv B.a) (deriv (deriv B.a) t) t :=
  hasDerivAt_deriv_a (D := B.toData) ht

/-- `(a²)˙ = 2aȧ`. -/
theorem hasDerivAt_a_sq {t : ℝ} (ht : t ∈ B.I) :
    HasDerivAt (fun s => B.a s ^ 2) (2 * B.a t * deriv B.a t) t := by
  have := (hasDerivAt_a' ht).pow 2
  convert this using 1
  push_cast
  ring

/-- `(aȧ)˙ = ȧ² + aä`. -/
theorem hasDerivAt_a_mul_deriv {t : ℝ} (ht : t ∈ B.I) :
    HasDerivAt (fun s => B.a s * deriv B.a s)
      (deriv B.a t ^ 2 + B.a t * deriv (deriv B.a) t) t := by
  have := (hasDerivAt_a' ht).fun_mul (hasDerivAt_deriv_a' ht)
  convert this using 1
  ring

/-! ### The perturbation -/

/-- The block `0 ⊕ f`: zero in the time row and column, `f_{αβ}` in the spatial block. -/
def spatialBlock (f : Fin 3 → Fin 3 → ℝ) (i j : Fin 4) : ℝ :=
  Fin.cases (motive := fun _ => ℝ) 0
    (fun α => Fin.cases (motive := fun _ => ℝ) 0 (fun β => f α β) j) i

@[simp] theorem spatialBlock_zero_left (f : Fin 3 → Fin 3 → ℝ) (j : Fin 4) :
    spatialBlock f 0 j = 0 := rfl

@[simp] theorem spatialBlock_zero_right (f : Fin 3 → Fin 3 → ℝ) (i : Fin 4) :
    spatialBlock f i 0 = 0 := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨α, rfl⟩ <;> rfl

@[simp] theorem spatialBlock_succ_succ (f : Fin 3 → Fin 3 → ℝ) (α β : Fin 3) :
    spatialBlock f α.succ β.succ = f α β := rfl

/-- `∂_c h_{αβ}`, the partial derivative of a field `h` of spatial matrices. -/
def dh (h : E → Fin 3 → Fin 3 → ℝ) (c : Fin 4) (z : E) (α β : Fin 3) : ℝ :=
  fderiv ℝ (fun w => h w α β) z (Pi.single c 1)

/-- `∂_c ∂_e h_{αβ}`, the second partial derivative. -/
def ddh (h : E → Fin 3 → Fin 3 → ℝ) (c e : Fin 4) (z : E) (α β : Fin 3) : ℝ :=
  fderiv ℝ (fun w => dh h e w α β) z (Pi.single c 1)

/-- A smooth symmetric perturbation of the spatial metric on the domain. -/
structure IsPerturbation (B : Background) (h : E → Fin 3 → Fin 3 → ℝ) : Prop where
  /-- The components are smooth on the domain. -/
  smooth : ∀ α β, ContDiffOn ℝ ∞ (fun z => h z α β) (domain B.toData)
  /-- The perturbation is symmetric. -/
  symm : ∀ z α β, h z α β = h z β α

variable (B) in
/-- **The metric perturbation** `δg_{00} = δg_{0α} = 0`, `δg_{αβ} = a² h_{αβ}`. -/
def metricPerturbation (h : E → Fin 3 → Fin 3 → ℝ) (z : E) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of (spatialBlock fun α β => B.a (z 0) ^ 2 * h z α β)

variable (B) in
/-- **The perturbed synchronous metric** `ds² = −dt² + a² (δ_{αβ} + ε h_{αβ}) dx^α dx^β`. -/
def perturbedCoefficient (h : E → Fin 3 → Fin 3 → ℝ) (ε : ℝ) (z : E) : Matrix (Fin 4) (Fin 4) ℝ :=
  (metric B.toData).coefficient z + ε • metricPerturbation B h z

/-- **The perturbation keeps the metric synchronous**: for every `ε`, `g₀₀ = −1`, `g₀α = 0`, and
`g_{αβ} = a² (δ_{αβ} + ε h_{αβ})`. -/
theorem perturbedCoefficient_synchronous (h : E → Fin 3 → Fin 3 → ℝ) (ε : ℝ) (z : E) :
    perturbedCoefficient B h ε z 0 0 = -1 ∧
      (∀ α : Fin 3, perturbedCoefficient B h ε z 0 α.succ = 0) ∧
      ∀ α β : Fin 3, perturbedCoefficient B h ε z α.succ β.succ =
        B.a (z 0) ^ 2 * ((if α = β then 1 else 0) + ε * h z α β) := by
  refine ⟨?_, fun α => ?_, fun α β => ?_⟩
  · simp [perturbedCoefficient, metricPerturbation, coefficient_zero_zero]
  · simp [perturbedCoefficient, metricPerturbation, coefficient_zero_succ]
  · simp only [perturbedCoefficient, metricPerturbation, Matrix.add_apply, Matrix.smul_apply,
    Matrix.of_apply, spatialBlock_succ_succ, coefficient_succ_succ, smul_eq_mul]
    split_ifs <;> ring

@[simp] theorem metricPerturbation_zero_left (h : E → Fin 3 → Fin 3 → ℝ) (z : E) (j : Fin 4) :
    metricPerturbation B h z 0 j = 0 := rfl

@[simp] theorem metricPerturbation_zero_right (h : E → Fin 3 → Fin 3 → ℝ) (z : E) (i : Fin 4) :
    metricPerturbation B h z i 0 = 0 := spatialBlock_zero_right _ i

@[simp] theorem metricPerturbation_succ_succ (h : E → Fin 3 → Fin 3 → ℝ) (z : E) (α β : Fin 3) :
    metricPerturbation B h z α.succ β.succ = B.a (z 0) ^ 2 * h z α β := rfl

theorem fderiv_metricPerturbation_zero_left (h : E → Fin 3 → Fin 3 → ℝ) (j : Fin 4) (v : E) :
    fderiv ℝ (fun w => metricPerturbation B h w 0 j) z v = 0 := by
  simp

theorem fderiv_metricPerturbation_zero_right (h : E → Fin 3 → Fin 3 → ℝ) (i : Fin 4) (v : E) :
    fderiv ℝ (fun w => metricPerturbation B h w i 0) z v = 0 := by
  simp

theorem fderiv_metricPerturbation_succ_succ {h : E → Fin 3 → Fin 3 → ℝ} (hz : z ∈ domain B.toData)
    {α β : Fin 3} (hh : DifferentiableAt ℝ (fun w => h w α β) z) (v : E) :
    fderiv ℝ (fun w => metricPerturbation B h w α.succ β.succ) z v =
      2 * B.a (z 0) * deriv B.a (z 0) * v 0 * h z α β +
        B.a (z 0) ^ 2 * fderiv ℝ (fun w => h w α β) z v := by
  simp only [metricPerturbation_succ_succ]
  exact fderiv_time_mul (hasDerivAt_a_sq (time_mem_I hz)) hh v

theorem IsPerturbation.differentiableAt {h : E → Fin 3 → Fin 3 → ℝ} (hP : IsPerturbation B h)
    (hz : z ∈ domain B.toData) (α β : Fin 3) : DifferentiableAt ℝ (fun w => h w α β) z :=
  ((hP.smooth α β).contDiffAt ((domain B.toData).isOpen.mem_nhds hz)).differentiableAt
    (by simp)

theorem IsPerturbation.dh_symm {h : E → Fin 3 → Fin 3 → ℝ} (hP : IsPerturbation B h) (c : Fin 4)
    (z : E) (α β : Fin 3) : dh h c z α β = dh h c z β α := by
  unfold dh
  congr 1
  rw [show (fun w => h w α β) = fun w => h w β α from funext fun w => hP.symm w α β]

theorem IsPerturbation.ddh_symm {h : E → Fin 3 → Fin 3 → ℝ} (hP : IsPerturbation B h)
    (c e : Fin 4) (z : E) (α β : Fin 3) : ddh h c e z α β = ddh h c e z β α := by
  unfold ddh
  congr 1
  rw [show (fun w => dh h e w α β) = fun w => dh h e w β α from
    funext fun w => hP.dh_symm e w α β]

theorem IsPerturbation.contDiffOn_metricPerturbation {h : E → Fin 3 → Fin 3 → ℝ}
    (hP : IsPerturbation B h) (i j : Fin 4) :
    ContDiffOn ℝ ∞ (fun z => metricPerturbation B h z i j) (domain B.toData) := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨α, rfl⟩
  · simpa using contDiffOn_const
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨β, rfl⟩
  · simpa using contDiffOn_const
  simp only [metricPerturbation_succ_succ]
  exact ((contDiffOn_time (D := B.toData) B.contDiffOn_a).pow 2).mul (hP.smooth α β)

theorem IsPerturbation.metricPerturbation_symm {h : E → Fin 3 → Fin 3 → ℝ}
    (hP : IsPerturbation B h) (z : E) (i j : Fin 4) :
    metricPerturbation B h z i j = metricPerturbation B h z j i := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨α, rfl⟩
  · simp
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨β, rfl⟩
  · simp
  simp [hP.symm z α β]

/-! ### The variation of the Christoffel symbols -/

variable (B) in
/-- **The variation of the Christoffel symbols** of the perturbed synchronous metric:
`δΓ⁰_{αβ} = aȧ h_{αβ} + ½ a² ∂ₜh_{αβ}`, `δΓ^γ_{0β} = ½ ∂ₜh_{γβ}`,
`δΓ^γ_{αβ} = ½ (∂_α h_{γβ} + ∂_β h_{γα} − ∂_γ h_{αβ})`, the others zero. -/
def linChristoffel (h : E → Fin 3 → Fin 3 → ℝ) (z : E) (k i j : Fin 4) : ℝ :=
  Fin.cases (motive := fun _ => ℝ)
    (spatialBlock (fun α β => B.a (z 0) * deriv B.a (z 0) * h z α β +
      B.a (z 0) ^ 2 * dh h 0 z α β / 2) i j)
    (fun γ => Fin.cases (motive := fun _ => ℝ)
      (Fin.cases (motive := fun _ => ℝ) 0 (fun β => dh h 0 z γ β / 2) j)
      (fun α => Fin.cases (motive := fun _ => ℝ) (dh h 0 z γ α / 2)
        (fun β => (dh h α.succ z γ β + dh h β.succ z γ α - dh h γ.succ z α β) / 2) j) i) k

section linChristoffel

variable (h : E → Fin 3 → Fin 3 → ℝ) (z : E)

@[simp] theorem linChristoffel_zero_zero (j : Fin 4) : linChristoffel B h z 0 0 j = 0 := rfl

@[simp] theorem linChristoffel_zero_succ_zero (α : Fin 3) :
    linChristoffel B h z 0 α.succ 0 = 0 := rfl

@[simp] theorem linChristoffel_zero_succ_succ (α β : Fin 3) :
    linChristoffel B h z 0 α.succ β.succ =
      B.a (z 0) * deriv B.a (z 0) * h z α β + B.a (z 0) ^ 2 * dh h 0 z α β / 2 := rfl

@[simp] theorem linChristoffel_succ_zero_zero (γ : Fin 3) :
    linChristoffel B h z γ.succ 0 0 = 0 := rfl

@[simp] theorem linChristoffel_succ_zero_succ (γ β : Fin 3) :
    linChristoffel B h z γ.succ 0 β.succ = dh h 0 z γ β / 2 := rfl

@[simp] theorem linChristoffel_succ_succ_zero (γ α : Fin 3) :
    linChristoffel B h z γ.succ α.succ 0 = dh h 0 z γ α / 2 := rfl

@[simp] theorem linChristoffel_succ_succ_succ (γ α β : Fin 3) :
    linChristoffel B h z γ.succ α.succ β.succ =
      (dh h α.succ z γ β + dh h β.succ z γ α - dh h γ.succ z α β) / 2 := rfl

end linChristoffel

@[simp] theorem single_zero_apply_zero : (Pi.single 0 1 : E) 0 = 1 := by simp

@[simp] theorem single_succ_apply_zero (α : Fin 3) : (Pi.single α.succ 1 : E) 0 = 0 := by
  simp [Fin.succ_ne_zero]

theorem fderiv_metricPerturbation_single {h : E → Fin 3 → Fin 3 → ℝ} (hz : z ∈ domain B.toData)
    {α β : Fin 3} (hh : DifferentiableAt ℝ (fun w => h w α β) z) (c : Fin 4) :
    fderiv ℝ (fun w => metricPerturbation B h w α.succ β.succ) z (Pi.single c 1) =
      2 * B.a (z 0) * deriv B.a (z 0) * (Pi.single c 1 : E) 0 * h z α β +
        B.a (z 0) ^ 2 * dh h c z α β :=
  fderiv_metricPerturbation_succ_succ hz hh _

/-- **The variation of the Christoffel symbols** (Landau–Lifshitz, §115): on the flat background,
the covariant first variation `½ g^{kl} (∇_i δg_{jl} + ∇_j δg_{li} − ∇_l δg_{ij})` of
`CurvedLinearization` is the table `linChristoffel`. -/
theorem curvedChristoffel_eq {h : E → Fin 3 → Fin 3 → ℝ} (hP : IsPerturbation B h)
    (hz : z ∈ domain B.toData) (k i j : Fin 4) :
    (metric B.toData).curvedChristoffel (metricPerturbation B h) z k i j =
      linChristoffel B h z k i j := by
  have hd := fun α β => hP.differentiableAt hz α β
  have ha := (a_pos' hz).ne'
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨γ, rfl⟩ <;>
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨α, rfl⟩ <;>
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨β, rfl⟩ <;>
  simp only [curvedChristoffel, covDerivTwo, Fin.sum_univ_succ (n := 3),
    fderiv_metricPerturbation_zero_left, fderiv_metricPerturbation_zero_right,
    fderiv_metricPerturbation_single hz (hd _ _)] <;>
  simp only [inv_zero_zero hz, inv_zero_succ hz, inv_succ_zero hz, inv_succ_succ hz,
    bgΓ_zero_zero hz, bgΓ_zero_zero_left hz, bgΓ_zero_left_zero hz, bgΓ_zero_succ_succ hz,
    bgΓ_succ_zero_succ hz, bgΓ_succ_succ_zero hz, bgΓ_succ_succ_succ hz,
    metricPerturbation_zero_left, metricPerturbation_zero_right, metricPerturbation_succ_succ,
    linChristoffel_zero_zero, linChristoffel_zero_succ_zero, linChristoffel_zero_succ_succ,
    linChristoffel_succ_zero_zero, linChristoffel_succ_zero_succ, linChristoffel_succ_succ_zero,
    linChristoffel_succ_succ_succ, single_zero_apply_zero, single_succ_apply_zero, mul_zero,
    zero_mul, add_zero, zero_add, sub_zero, zero_sub, ite_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero, zero_div, mul_one,
    neg_mul, one_mul, Finset.sum_add_distrib, ite_div]
  · rw [hP.symm z β α]; field_simp; ring
  · rw [hP.symm z β γ, hP.dh_symm 0 z β γ]; field_simp; ring
  · rw [hP.symm z α γ]; field_simp; ring
  · rw [hP.dh_symm α.succ z β γ]; field_simp

/-! ### The variation of the Ricci tensor -/

section Ricci

variable {h : E → Fin 3 → Fin 3 → ℝ}

theorem IsPerturbation.contDiffOn_dh (hP : IsPerturbation B h) (c : Fin 4) (α β : Fin 3) :
    ContDiffOn ℝ ∞ (fun w => dh h c w α β) (domain B.toData) :=
  contDiffOn_partial (hP.smooth α β) _

theorem IsPerturbation.differentiableAt_dh (hP : IsPerturbation B h) (hx : x ∈ domain B.toData)
    (c : Fin 4) (α β : Fin 3) : DifferentiableAt ℝ (fun w => dh h c w α β) x :=
  ((hP.contDiffOn_dh c α β).contDiffAt ((domain B.toData).isOpen.mem_nhds hx)).differentiableAt
    (by simp)

/-- The second partial derivatives commute. -/
theorem IsPerturbation.ddh_comm (hP : IsPerturbation B h) (hx : x ∈ domain B.toData)
    (a b : Fin 4) (α β : Fin 3) : ddh h a b x α β = ddh h b a x α β :=
  fderiv_fderiv_comm (hP.smooth α β) hx a b

variable (B h) in
/-- The family `ḡ + ε δg` of coefficients, as a function of `(ε, z)`. -/
abbrev family : ℝ × E → Matrix (Fin 4) (Fin 4) ℝ :=
  (metric B.toData).perturbationFamily (metricPerturbation B h)

theorem familyChristoffelDeriv_eq_lin (hP : IsPerturbation B h) (hz : z ∈ domain B.toData)
    (k i j : Fin 4) :
    familyChristoffelDeriv (family B h) z k i j = linChristoffel B h z k i j := by
  rw [familyChristoffelDeriv_eq hP.contDiffOn_metricPerturbation
    (fun z _ i j => hP.metricPerturbation_symm z i j) hz, curvedChristoffel_eq hP hz]

/-- The derivative of the Ricci tensor of the perturbed metric is the first variation of the
family. -/
theorem hasDerivAt_ricciOf_family (hP : IsPerturbation B h) (hx : x ∈ domain B.toData)
    (j k : Fin 4) :
    HasDerivAt (fun ε => ricciOf (perturbedCoefficient B h ε) x j k)
      (familyRicciDeriv (family B h) x j k) 0 := by
  rw [familyRicciDeriv_eq hP.contDiffOn_metricPerturbation
    (fun z _ i j => hP.metricPerturbation_symm z i j) hx]
  exact hasDerivAt_ricciOf_perturbation hP.contDiffOn_metricPerturbation
    (fun z _ i j => hP.metricPerturbation_symm z i j) hx j k

/-- The first variation of the Ricci tensor through the table `linChristoffel`. -/
theorem familyRicciDeriv_eq_lin (hP : IsPerturbation B h) (hx : x ∈ domain B.toData)
    (j k : Fin 4) :
    familyRicciDeriv (family B h) x j k =
      ∑ i, (fderiv ℝ (fun z => linChristoffel B h z i j k) x (Pi.single i 1) -
        fderiv ℝ (fun z => linChristoffel B h z i i k) x (Pi.single j 1) +
        ∑ a, ((linChristoffel B h x i i a * christoffelOf (metric B.toData).coefficient x a j k +
            christoffelOf (metric B.toData).coefficient x i i a * linChristoffel B h x a j k) -
          (linChristoffel B h x i j a * christoffelOf (metric B.toData).coefficient x a i k +
            christoffelOf (metric B.toData).coefficient x i j a *
              linChristoffel B h x a i k))) := by
  have hev (a b c : Fin 4) : (fun z => familyChristoffelDeriv (family B h) z a b c) =ᶠ[𝓝 x]
      fun z => linChristoffel B h z a b c :=
    eventually_of_mem ((domain B.toData).isOpen.mem_nhds hx) fun z hz =>
      familyChristoffelDeriv_eq_lin hP hz a b c
  have h0 (a b c : Fin 4) : familyChristoffel (family B h) (0, x) a b c =
      christoffelOf (metric B.toData).coefficient x a b c := by
    change christoffelOf (fun z => family B h (0, z)) x a b c = _
    rw [perturbationFamily_zero]
  unfold familyRicciDeriv
  simp only [(hev _ _ _).fderiv_eq, familyChristoffelDeriv_eq_lin hP hx, h0]

/-! #### Derivatives of the table -/

theorem differentiableAt_div_two {f : E → ℝ} (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun z => f z / 2) x := by
  simpa [div_eq_mul_inv] using hf.mul_const (2⁻¹ : ℝ)

theorem fderiv_div_two {f : E → ℝ} (hf : DifferentiableAt ℝ f x) (v : E) :
    fderiv ℝ (fun z => f z / 2) x v = fderiv ℝ f x v / 2 := by
  have e : (fun z => f z / 2) = fun z => f z * 2⁻¹ := funext fun z => div_eq_mul_inv _ _
  rw [e, fderiv_mul_const hf]
  simp only [smul_apply, smul_eq_mul]
  ring

theorem fderiv_lin_zero_zero (j : Fin 4) (v : E) :
    fderiv ℝ (fun z => linChristoffel B h z 0 0 j) x v = 0 := by
  simp

theorem fderiv_lin_zero_succ_zero (α : Fin 3) (v : E) :
    fderiv ℝ (fun z => linChristoffel B h z 0 α.succ 0) x v = 0 := by
  simp

theorem fderiv_lin_succ_zero_zero (γ : Fin 3) (v : E) :
    fderiv ℝ (fun z => linChristoffel B h z γ.succ 0 0) x v = 0 := by
  simp

theorem fderiv_lin_zero_succ_succ (hP : IsPerturbation B h) (hx : x ∈ domain B.toData)
    (α β : Fin 3) (c : Fin 4) :
    fderiv ℝ (fun z => linChristoffel B h z 0 α.succ β.succ) x (Pi.single c 1) =
      (deriv B.a (x 0) ^ 2 + B.a (x 0) * deriv (deriv B.a) (x 0)) * (Pi.single c 1 : E) 0 *
          h x α β + B.a (x 0) * deriv B.a (x 0) * dh h c x α β +
        B.a (x 0) * deriv B.a (x 0) * (Pi.single c 1 : E) 0 * dh h 0 x α β +
        B.a (x 0) ^ 2 / 2 * ddh h c 0 x α β := by
  have ht := time_mem_I hx
  have h1 : DifferentiableAt ℝ (fun z : E => B.a (z 0) * deriv B.a (z 0) * h z α β) x :=
    ((hasFDerivAt_time_mul (hasDerivAt_a_mul_deriv ht)
      (hP.differentiableAt hx α β).hasFDerivAt).differentiableAt)
  have h2 : DifferentiableAt ℝ (fun z : E => B.a (z 0) ^ 2 * dh h 0 z α β) x :=
    ((hasFDerivAt_time_mul (hasDerivAt_a_sq ht)
      (hP.differentiableAt_dh hx 0 α β).hasFDerivAt).differentiableAt)
  have e : (fun z => linChristoffel B h z 0 α.succ β.succ) = fun z : E =>
      B.a (z 0) * deriv B.a (z 0) * h z α β + B.a (z 0) ^ 2 * dh h 0 z α β / 2 := rfl
  rw [e, fderiv_fun_add h1 (differentiableAt_div_two h2), add_apply,
    fderiv_div_two h2,
    fderiv_time_mul (φ := fun s => B.a s * deriv B.a s) (hasDerivAt_a_mul_deriv ht)
      (hP.differentiableAt hx α β),
    fderiv_time_mul (φ := fun s => B.a s ^ 2) (hasDerivAt_a_sq ht)
      (hP.differentiableAt_dh hx 0 α β)]
  simp only [dh, ddh]
  ring

theorem fderiv_lin_succ_zero_succ (hP : IsPerturbation B h) (hx : x ∈ domain B.toData)
    (γ β : Fin 3) (c : Fin 4) :
    fderiv ℝ (fun z => linChristoffel B h z γ.succ 0 β.succ) x (Pi.single c 1) =
      ddh h c 0 x γ β / 2 := by
  have e : (fun z => linChristoffel B h z γ.succ 0 β.succ) = fun z : E => dh h 0 z γ β / 2 := rfl
  rw [e, fderiv_div_two (hP.differentiableAt_dh hx 0 γ β)]
  rfl

theorem fderiv_lin_succ_succ_zero (hP : IsPerturbation B h) (hx : x ∈ domain B.toData)
    (γ α : Fin 3) (c : Fin 4) :
    fderiv ℝ (fun z => linChristoffel B h z γ.succ α.succ 0) x (Pi.single c 1) =
      ddh h c 0 x γ α / 2 := by
  have e : (fun z => linChristoffel B h z γ.succ α.succ 0) = fun z : E => dh h 0 z γ α / 2 := rfl
  rw [e, fderiv_div_two (hP.differentiableAt_dh hx 0 γ α)]
  rfl

theorem fderiv_lin_succ_succ_succ (hP : IsPerturbation B h) (hx : x ∈ domain B.toData)
    (γ α β : Fin 3) (c : Fin 4) :
    fderiv ℝ (fun z => linChristoffel B h z γ.succ α.succ β.succ) x (Pi.single c 1) =
      (ddh h c α.succ x γ β + ddh h c β.succ x γ α - ddh h c γ.succ x α β) / 2 := by
  have e : (fun z => linChristoffel B h z γ.succ α.succ β.succ) = fun z : E =>
      (dh h α.succ z γ β + dh h β.succ z γ α - dh h γ.succ z α β) / 2 := rfl
  have h3 := ((hP.differentiableAt_dh hx α.succ γ β).fun_add
    (hP.differentiableAt_dh hx β.succ γ α)).fun_sub (hP.differentiableAt_dh hx γ.succ α β)
  rw [e, fderiv_div_two h3, fderiv_fun_sub ((hP.differentiableAt_dh hx _ _ _).fun_add
    (hP.differentiableAt_dh hx _ _ _)) (hP.differentiableAt_dh hx _ _ _),
    fderiv_fun_add (hP.differentiableAt_dh hx _ _ _) (hP.differentiableAt_dh hx _ _ _)]
  rfl

/-! #### The table of the variation of the Ricci tensor -/

variable (B) in
/-- `δR₀₀ = −½ ∂ₜ²h − (ȧ/a) ∂ₜh`, with `h = h_γγ` the trace. -/
def linRicciTime (h : E → Fin 3 → Fin 3 → ℝ) (z : E) : ℝ :=
  -(∑ γ, ddh h 0 0 z γ γ) / 2 - deriv B.a (z 0) / B.a (z 0) * ∑ γ, dh h 0 z γ γ

/-- `δR₀α = ½ (∂_γ ∂ₜ h_{γα} − ∂ₜ ∂_α h)`. -/
def linRicciMixed (h : E → Fin 3 → Fin 3 → ℝ) (z : E) (α : Fin 3) : ℝ :=
  (∑ γ, ddh h γ.succ 0 z γ α - ∑ γ, ddh h 0 α.succ z γ γ) / 2

variable (B) in
/-- `δR_{αβ} = δP_{αβ} + (2ȧ² + aä) h_{αβ} + (3/2) aȧ ∂ₜh_{αβ} + ½ a² ∂ₜ²h_{αβ}
+ ½ aȧ ∂ₜh δ_{αβ}`, with the variation
`δP_{αβ} = ½ (∂_γ∂_α h_{γβ} + ∂_γ∂_β h_{γα} − ∂_γ∂_γ h_{αβ} − ∂_α∂_β h)` of the Ricci tensor
of the sections. -/
def linRicciSpace (h : E → Fin 3 → Fin 3 → ℝ) (z : E) (α β : Fin 3) : ℝ :=
  (∑ γ, (ddh h γ.succ α.succ z γ β + ddh h γ.succ β.succ z γ α - ddh h γ.succ γ.succ z α β) -
      ∑ γ, ddh h α.succ β.succ z γ γ) / 2 +
    (2 * deriv B.a (z 0) ^ 2 + B.a (z 0) * deriv (deriv B.a) (z 0)) * h z α β +
    3 / 2 * (B.a (z 0) * deriv B.a (z 0)) * dh h 0 z α β + B.a (z 0) ^ 2 / 2 * ddh h 0 0 z α β +
    if α = β then B.a (z 0) * deriv B.a (z 0) / 2 * ∑ γ, dh h 0 z γ γ else 0

theorem familyRicciDeriv_zero_zero (hP : IsPerturbation B h) (hx : x ∈ domain B.toData) :
    familyRicciDeriv (family B h) x 0 0 = linRicciTime B h x := by
  rw [familyRicciDeriv_eq_lin hP hx]
  simp only [Fin.sum_univ_succ (n := 3), fderiv_lin_zero_zero, fderiv_lin_succ_zero_zero,
    fderiv_lin_succ_succ_zero hP hx]
  simp only [linChristoffel_zero_zero, linChristoffel_zero_succ_zero, linChristoffel_succ_zero_zero,
    linChristoffel_succ_zero_succ, linChristoffel_succ_succ_zero, linChristoffel_succ_succ_succ,
    bgΓ_zero_zero hx, bgΓ_zero_zero_left hx, bgΓ_zero_left_zero hx, bgΓ_succ_zero_succ hx,
    bgΓ_succ_succ_zero hx, bgΓ_succ_succ_succ hx, mul_zero, zero_mul, add_zero, zero_add, zero_sub,
    ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const_zero, sub_self, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  simp only [linRicciTime, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_div]
  ring

theorem familyRicciDeriv_zero_succ (hP : IsPerturbation B h) (hx : x ∈ domain B.toData)
    (β : Fin 3) : familyRicciDeriv (family B h) x 0 β.succ = linRicciMixed h x β := by
  rw [familyRicciDeriv_eq_lin hP hx]
  simp only [Fin.sum_univ_succ (n := 3), fderiv_lin_zero_zero, fderiv_lin_succ_zero_succ hP hx,
    fderiv_lin_succ_succ_succ hP hx]
  simp only [linChristoffel_zero_zero, linChristoffel_zero_succ_succ, linChristoffel_succ_zero_zero,
    linChristoffel_succ_zero_succ, linChristoffel_succ_succ_zero, linChristoffel_succ_succ_succ,
    bgΓ_zero_zero hx, bgΓ_zero_zero_left hx, bgΓ_zero_succ_succ hx, bgΓ_succ_zero_succ hx,
    bgΓ_succ_succ_zero hx, bgΓ_succ_succ_succ hx, mul_zero, zero_mul, add_zero, zero_add, zero_sub,
    ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const_zero, neg_zero, sub_self, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    Finset.sum_sub_distrib]
  simp only [linRicciMixed, add_div, sub_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_div]
  ring

theorem familyRicciDeriv_succ_zero (hP : IsPerturbation B h) (hx : x ∈ domain B.toData)
    (α : Fin 3) : familyRicciDeriv (family B h) x α.succ 0 = linRicciMixed h x α := by
  rw [familyRicciDeriv_eq_lin hP hx]
  simp only [Fin.sum_univ_succ (n := 3), fderiv_lin_zero_zero, fderiv_lin_zero_succ_zero,
    fderiv_lin_succ_succ_zero hP hx]
  simp only [linChristoffel_zero_zero, linChristoffel_zero_succ_zero, linChristoffel_zero_succ_succ,
    linChristoffel_succ_zero_zero, linChristoffel_succ_succ_zero, linChristoffel_succ_succ_succ,
    bgΓ_zero_zero hx, bgΓ_zero_zero_left hx, bgΓ_zero_left_zero hx, bgΓ_zero_succ_succ hx,
    bgΓ_succ_succ_zero hx, bgΓ_succ_succ_succ hx, mul_zero, zero_mul, add_zero, zero_add, sub_zero,
    mul_ite, Finset.sum_ite_eq', Finset.mem_univ, ite_true, sub_self, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  simp only [linRicciMixed, add_div, sub_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.sum_div]
  have e1 : ∑ i, ddh h α.succ 0 x i i = ∑ i, ddh h 0 α.succ x i i :=
    Finset.sum_congr rfl fun i _ => hP.ddh_comm hx _ _ _ _
  have e2 : ∑ i : Fin 3, dh h i.succ x α i = ∑ i, dh h i.succ x i α :=
    Finset.sum_congr rfl fun i _ => hP.dh_symm _ _ _ _
  rw [e1, e2]
  ring

theorem familyRicciDeriv_succ_succ (hP : IsPerturbation B h) (hx : x ∈ domain B.toData)
    (α β : Fin 3) : familyRicciDeriv (family B h) x α.succ β.succ = linRicciSpace B h x α β := by
  have ha := (a_pos' hx).ne'
  rw [familyRicciDeriv_eq_lin hP hx]
  by_cases hab : α = β
  · subst hab
    simp only [Fin.sum_univ_succ (n := 3), fderiv_lin_zero_zero, fderiv_lin_zero_succ_succ hP hx,
      fderiv_lin_succ_succ_succ hP hx]
    simp only [linChristoffel_zero_zero, linChristoffel_zero_succ_zero,
      linChristoffel_zero_succ_succ, linChristoffel_succ_zero_succ, linChristoffel_succ_succ_zero,
      linChristoffel_succ_succ_succ, bgΓ_zero_zero hx, bgΓ_zero_zero_left hx, bgΓ_zero_left_zero hx,
      bgΓ_zero_succ_succ hx, bgΓ_succ_zero_succ hx, bgΓ_succ_succ_zero hx, bgΓ_succ_succ_succ hx,
      single_zero_apply_zero, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, ite_mul,
      mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Finset.sum_const_zero, mul_one, sub_self, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_sub_distrib]
    simp only [linRicciSpace, add_div, sub_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul,
      ← Finset.sum_div, ite_true, Nat.cast_ofNat]
    field_simp
    ring
  · simp only [Fin.sum_univ_succ (n := 3), fderiv_lin_zero_zero, fderiv_lin_zero_succ_succ hP hx,
    fderiv_lin_succ_succ_succ hP hx]
    simp only [linChristoffel_zero_zero, linChristoffel_zero_succ_zero,
      linChristoffel_zero_succ_succ, linChristoffel_succ_zero_succ, linChristoffel_succ_succ_zero,
      linChristoffel_succ_succ_succ, bgΓ_zero_zero hx, bgΓ_zero_zero_left hx, bgΓ_zero_left_zero hx,
      bgΓ_zero_succ_succ hx, bgΓ_succ_zero_succ hx, bgΓ_succ_succ_zero hx, bgΓ_succ_succ_succ hx,
      single_zero_apply_zero, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, ite_mul,
      mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Finset.sum_const_zero, mul_one, sub_self, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_sub_distrib, hab, ite_false]
    simp only [linRicciSpace, add_div, sub_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div, hab,
      ite_false, Nat.cast_ofNat]
    rw [hP.dh_symm 0 x β α]
    field_simp
    ring

variable (B) in
/-- The table `δR_{jk}` of the variation of the Ricci tensor (`linRicciTime`, `linRicciMixed`,
`linRicciSpace`). -/
def linRicci (h : E → Fin 3 → Fin 3 → ℝ) (z : E) (j k : Fin 4) : ℝ :=
  Fin.cases (motive := fun _ => ℝ)
    (Fin.cases (motive := fun _ => ℝ) (linRicciTime B h z) (fun β => linRicciMixed h z β) k)
    (fun α => Fin.cases (motive := fun _ => ℝ) (linRicciMixed h z α)
      (fun β => linRicciSpace B h z α β) k) j

@[simp] theorem linRicci_zero_zero (z : E) : linRicci B h z 0 0 = linRicciTime B h z := rfl

@[simp] theorem linRicci_zero_succ (z : E) (β : Fin 3) :
    linRicci B h z 0 β.succ = linRicciMixed h z β := rfl

@[simp] theorem linRicci_succ_zero (z : E) (α : Fin 3) :
    linRicci B h z α.succ 0 = linRicciMixed h z α := rfl

@[simp] theorem linRicci_succ_succ (z : E) (α β : Fin 3) :
    linRicci B h z α.succ β.succ = linRicciSpace B h z α β := rfl

/-- The first variation of the Ricci tensor is the table `linRicci`. -/
theorem familyRicciDeriv_eq_linRicci (hP : IsPerturbation B h) (hx : x ∈ domain B.toData)
    (j k : Fin 4) : familyRicciDeriv (family B h) x j k = linRicci B h x j k := by
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨α, rfl⟩ <;>
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨β, rfl⟩
  · exact familyRicciDeriv_zero_zero hP hx
  · exact familyRicciDeriv_zero_succ hP hx β
  · exact familyRicciDeriv_succ_zero hP hx α
  · exact familyRicciDeriv_succ_succ hP hx α β

/-- The derivative in `ε` at `0` of the Ricci tensor of the perturbed metric is `linRicci`. -/
theorem hasDerivAt_ricciOf_perturbed (hP : IsPerturbation B h) (hx : x ∈ domain B.toData)
    (j k : Fin 4) :
    HasDerivAt (fun ε => ricciOf (perturbedCoefficient B h ε) x j k) (linRicci B h x j k) 0 := by
  rw [← familyRicciDeriv_eq_linRicci hP hx]
  exact hasDerivAt_ricciOf_family hP hx j k

/-- **The Ricci tensor of a perturbed synchronous metric** (Landau–Lifshitz, §115). For the flat
background `ds² = −dt² + a² δ_{αβ} dx^α dx^β` and the synchronous family
`γ_{αβ} = a² (δ_{αβ} + ε h_{αβ})` (`perturbedCoefficient`, which keeps `g₀₀ = −1` and `g₀α = 0`,
`perturbedCoefficient_synchronous`), with `h = h_γγ` the trace and `H = ȧ/a`, the derivatives in
`ε` at `0` of the co-ordinate Ricci tensor are
`δR₀₀ = −½ ∂ₜ²h − H ∂ₜh`,
`δR₀α = δR_α0 = ½ (∂_γ ∂ₜ h_{γα} − ∂ₜ ∂_α h)` and
`δR_{αβ} = ½ (∂_γ∂_α h_{γβ} + ∂_γ∂_β h_{γα} − ∂_γ∂_γ h_{αβ} − ∂_α∂_β h)
+ (2ȧ² + aä) h_{αβ} + (3/2) aȧ ∂ₜh_{αβ} + ½ a² ∂ₜ²h_{αβ} + ½ aȧ ∂ₜh δ_{αβ}`. -/
theorem ricci_synchronous_deriv (hP : IsPerturbation B h) (hx : x ∈ domain B.toData) :
    HasDerivAt (fun ε => ricciOf (perturbedCoefficient B h ε) x 0 0)
        (-(∑ γ, ddh h 0 0 x γ γ) / 2 - deriv B.a (x 0) / B.a (x 0) * ∑ γ, dh h 0 x γ γ) 0 ∧
      (∀ α : Fin 3, HasDerivAt (fun ε => ricciOf (perturbedCoefficient B h ε) x 0 α.succ)
        ((∑ γ, ddh h γ.succ 0 x γ α - ∑ γ, ddh h 0 α.succ x γ γ) / 2) 0) ∧
      (∀ α : Fin 3, HasDerivAt (fun ε => ricciOf (perturbedCoefficient B h ε) x α.succ 0)
        ((∑ γ, ddh h γ.succ 0 x γ α - ∑ γ, ddh h 0 α.succ x γ γ) / 2) 0) ∧
      ∀ α β : Fin 3, HasDerivAt (fun ε => ricciOf (perturbedCoefficient B h ε) x α.succ β.succ)
        ((∑ γ, (ddh h γ.succ α.succ x γ β + ddh h γ.succ β.succ x γ α -
              ddh h γ.succ γ.succ x α β) - ∑ γ, ddh h α.succ β.succ x γ γ) / 2 +
          (2 * deriv B.a (x 0) ^ 2 + B.a (x 0) * deriv (deriv B.a) (x 0)) * h x α β +
          3 / 2 * (B.a (x 0) * deriv B.a (x 0)) * dh h 0 x α β +
          B.a (x 0) ^ 2 / 2 * ddh h 0 0 x α β +
          if α = β then B.a (x 0) * deriv B.a (x 0) / 2 * ∑ γ, dh h 0 x γ γ else 0) 0 :=
  ⟨hasDerivAt_ricciOf_perturbed hP hx 0 0, fun α => hasDerivAt_ricciOf_perturbed hP hx 0 α.succ,
    fun α => hasDerivAt_ricciOf_perturbed hP hx α.succ 0,
    fun α β => hasDerivAt_ricciOf_perturbed hP hx α.succ β.succ⟩

end Ricci

/-! ### The linearized Einstein equations with dust -/

section Dust

variable {κ : ℝ} {ρ : ℝ → ℝ}

/-- **The background is a dust solution**: the Einstein equations `G_{ik} = κ T_{ik}` with the
comoving dust `p = 0` (`FLRW.isEinstein_iff_friedmann`) give `ȧ² = κρa²/3` and
`aä = −κρa²/6` on `I`. -/
theorem dust_background (hB : (metric B.toData).IsEinstein κ 0
      (perfectFluidStress B.toData ρ fun _ => 0)) {t : ℝ} (ht : t ∈ B.I) :
    deriv B.a t ^ 2 = κ * ρ t * B.a t ^ 2 / 3 ∧
      B.a t * deriv (deriv B.a) t = -(κ * ρ t * B.a t ^ 2) / 6 := by
  obtain ⟨h1, h2⟩ := (isEinstein_iff_friedmann κ 0 ρ _).mp hB t ht
  rw [firstFriedmann_iff_of_lapse_eq_one (fun _ _ => rfl) ht] at h1
  rw [secondFriedmann_iff_of_lapse_eq_one (fun _ _ => rfl) ht] at h2
  have ha := (B.a_pos t ht).ne'
  simp only [hubble, Background.toData, zero_div, add_zero, mul_zero] at h1 h2
  have e1 : deriv B.a t ^ 2 = κ * ρ t * B.a t ^ 2 / 3 := by
    field_simp at h1
    linarith
  refine ⟨e1, ?_⟩
  field_simp at h2
  nlinarith [e1]

/-- The covariant velocity `u = (−1, ε v_α)` of the perturbed dust. -/
def velocity (v : E → Fin 3 → ℝ) (ε : ℝ) (z : E) : Fin 4 → ℝ :=
  Fin.cons (-1) fun α => ε * v z α

variable (B) in
/-- **The source of the perturbed dust**: with the density `ρ(t)(1 + ε δ)` and the covariant
velocity `u = (−1, ε v_α)`, the trace-reversed stress `ρ (u_i u_k + ½ g_{ik})` of
`T_{ik} = ρ u_i u_k`, so that the Einstein equations `G_{ik} = κ T_{ik}` read
`R_{ik} = κ ρ (u_i u_k + ½ g_{ik})` (with `u^i u_i = −1` to first order in `ε`). -/
def dustSource (ρ : ℝ → ℝ) (h : E → Fin 3 → Fin 3 → ℝ) (δ : E → ℝ) (v : E → Fin 3 → ℝ)
    (ε : ℝ) (z : E) (i k : Fin 4) : ℝ :=
  ρ (z 0) * (1 + ε * δ z) *
    (velocity v ε z i * velocity v ε z k + perturbedCoefficient B h ε z i k / 2)

variable (B) in
/-- The residual `R_{ik} − κ ρ (u_i u_k + ½ g_{ik})` of the Einstein equations with dust along the
family. -/
def dustResidual (κ : ℝ) (ρ : ℝ → ℝ) (h : E → Fin 3 → Fin 3 → ℝ) (δ : E → ℝ)
    (v : E → Fin 3 → ℝ) (ε : ℝ) (z : E) (i k : Fin 4) : ℝ :=
  ricciOf (perturbedCoefficient B h ε) z i k - κ * dustSource B ρ h δ v ε z i k

variable (B) in
/-- **The linearized source of the dust**: `δS₀₀ = ½ ρδ`, `δS₀α = −ρ v_α` and
`δS_{αβ} = ½ ρ a² (δ δ_{αβ} + h_{αβ})`. -/
def linDust (ρ : ℝ → ℝ) (h : E → Fin 3 → Fin 3 → ℝ) (δ : E → ℝ) (v : E → Fin 3 → ℝ) (z : E)
    (i k : Fin 4) : ℝ :=
  Fin.cases (motive := fun _ => ℝ)
    (Fin.cases (motive := fun _ => ℝ) (ρ (z 0) * δ z / 2) (fun β => -(ρ (z 0) * v z β)) k)
    (fun α => Fin.cases (motive := fun _ => ℝ) (-(ρ (z 0) * v z α))
      (fun β => ρ (z 0) * B.a (z 0) ^ 2 * ((if α = β then δ z else 0) + h z α β) / 2) k) i

section linDust

variable (h : E → Fin 3 → Fin 3 → ℝ) (δ : E → ℝ) (v : E → Fin 3 → ℝ) (z : E)

@[simp] theorem linDust_zero_zero : linDust B ρ h δ v z 0 0 = ρ (z 0) * δ z / 2 := rfl

@[simp] theorem linDust_zero_succ (β : Fin 3) :
    linDust B ρ h δ v z 0 β.succ = -(ρ (z 0) * v z β) := rfl

@[simp] theorem linDust_succ_zero (α : Fin 3) :
    linDust B ρ h δ v z α.succ 0 = -(ρ (z 0) * v z α) := rfl

@[simp] theorem linDust_succ_succ (α β : Fin 3) :
    linDust B ρ h δ v z α.succ β.succ =
      ρ (z 0) * B.a (z 0) ^ 2 * ((if α = β then δ z else 0) + h z α β) / 2 := rfl

end linDust

theorem hasDerivAt_velocity (v : E → Fin 3 → ℝ) (z : E) (i : Fin 4) :
    HasDerivAt (fun ε => velocity v ε z i)
      (Fin.cons (α := fun _ => ℝ) 0 (fun α => v z α) i) 0 := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨α, rfl⟩
  · simpa [velocity] using hasDerivAt_const (0 : ℝ) (-1 : ℝ)
  · simpa [velocity] using (hasDerivAt_id (0 : ℝ)).mul_const (v z α)

/-- The derivative of the source of the dust is `linDust`. -/
theorem hasDerivAt_dustSource (h : E → Fin 3 → Fin 3 → ℝ) (δ : E → ℝ) (v : E → Fin 3 → ℝ)
    (z : E) (i k : Fin 4) :
    HasDerivAt (fun ε => dustSource B ρ h δ v ε z i k) (linDust B ρ h δ v z i k) 0 := by
  have h1 : HasDerivAt (fun ε : ℝ => ρ (z 0) * (1 + ε * δ z)) (ρ (z 0) * δ z) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const (δ z)).const_add 1).const_mul (ρ (z 0))
  have hC : HasDerivAt (fun ε => perturbedCoefficient B h ε z i k)
      (metricPerturbation B h z i k) 0 := by
    simpa [perturbedCoefficient] using ((hasDerivAt_id (0 : ℝ)).mul_const
      (metricPerturbation B h z i k)).const_add ((metric B.toData).coefficient z i k)
  have h2 := ((hasDerivAt_velocity v z i).fun_mul (hasDerivAt_velocity v z k)).fun_add
    (hC.div_const 2)
  have h3 := h1.fun_mul h2
  have e : (fun ε => dustSource B ρ h δ v ε z i k) = fun ε => ρ (z 0) * (1 + ε * δ z) *
      (velocity v ε z i * velocity v ε z k + perturbedCoefficient B h ε z i k / 2) := rfl
  rw [e]
  convert h3 using 1
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨α, rfl⟩ <;>
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨β, rfl⟩
  · simp [velocity, perturbedCoefficient, coefficient_zero_zero]
    ring
  · simp [velocity, perturbedCoefficient, coefficient_zero_succ]
  · simp [velocity, perturbedCoefficient, coefficient_succ_zero]
  · simp only [linDust_succ_succ, velocity, Fin.cons_succ, perturbedCoefficient,
    coefficient_succ_succ, metricPerturbation_succ_succ, zero_mul, mul_zero, zero_add, add_zero,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> ring

/-- **The derivative of the residual**: `d/dε (R_{ik} − κ ρ (u_i u_k + ½ g_{ik}))|₀ =
δR_{ik} − κ δS_{ik}`. -/
theorem hasDerivAt_dustResidual {h : E → Fin 3 → Fin 3 → ℝ} (hP : IsPerturbation B h)
    (δ : E → ℝ) (v : E → Fin 3 → ℝ) (hx : x ∈ domain B.toData) (i k : Fin 4) :
    HasDerivAt (fun ε => dustResidual B κ ρ h δ v ε x i k)
      (linRicci B h x i k - κ * linDust B ρ h δ v x i k) 0 :=
  (hasDerivAt_ricciOf_perturbed hP hx i k).sub ((hasDerivAt_dustSource h δ v x i k).const_mul κ)

/-- **The background solves the equations at `ε = 0`**: the residual vanishes on the domain. -/
theorem dustResidual_zero (hB : (metric B.toData).IsEinstein κ 0
      (perfectFluidStress B.toData ρ fun _ => 0)) (h : E → Fin 3 → Fin 3 → ℝ) (δ : E → ℝ)
    (v : E → Fin 3 → ℝ) (hx : x ∈ domain B.toData) (i k : Fin 4) :
    dustResidual B κ ρ h δ v 0 x i k = 0 := by
  have ht := time_mem_I hx
  have ha := (a_pos' hx).ne'
  obtain ⟨e1, e2⟩ := dust_background hB ht
  have hc : perturbedCoefficient B h 0 = (metric B.toData).coefficient := by
    funext z
    simp [perturbedCoefficient]
  unfold dustResidual dustSource
  rw [hc]
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨α, rfl⟩ <;>
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨β, rfl⟩
  · rw [FLRW.ricci_zero_zero hx, coefficient_zero_zero]
    simp only [velocity, Fin.cons_zero, Background.toData_a, Background.toData_N, deriv_const',
      zero_mul, zero_div, sub_zero, mul_one, add_zero]
    have e3 : deriv (deriv B.a) (x 0) = -(κ * ρ (x 0) * B.a (x 0)) / 6 :=
      mul_left_cancel₀ ha (by rw [e2]; ring)
    rw [e3]
    field_simp
    ring
  · rw [FLRW.ricci_zero_succ hx, coefficient_zero_succ]
    simp [velocity]
  · rw [FLRW.ricci_succ_zero hx, coefficient_succ_zero]
    simp [velocity]
  · rw [FLRW.ricci_succ_succ hx, coefficient_succ_succ]
    simp only [velocity, Fin.cons_succ, Background.toData_a, Background.toData_N,
      Background.toData_k, deriv_const', zero_mul, mul_zero, zero_add, add_zero, one_pow, div_one,
      sub_zero, psi, zero_div]
    split_ifs
    · field_simp
      nlinarith [e1, e2]
    · simp

variable (B) in
/-- **The linearized Einstein equations with dust** on the domain: `δR_{ik} = κ δS_{ik}`, that is
`δR₀₀ = ½ κρδ`, `δR₀α = −κρ v_α` and `δR_{αβ} = ½ κρa² (δ δ_{αβ} + h_{αβ})`. -/
def LinearizedEinsteinDust (κ : ℝ) (ρ : ℝ → ℝ) (h : E → Fin 3 → Fin 3 → ℝ) (δ : E → ℝ)
    (v : E → Fin 3 → ℝ) : Prop :=
  ∀ x ∈ domain B.toData, ∀ i k, linRicci B h x i k = κ * linDust B ρ h δ v x i k

/-- **The linearized equations are the first variation of the Einstein equations**: they hold if
and only if the derivative in `ε` at `0` of the residual vanishes on the domain. -/
theorem linearizedEinsteinDust_iff_deriv {h : E → Fin 3 → Fin 3 → ℝ} (hP : IsPerturbation B h)
    (δ : E → ℝ) (v : E → Fin 3 → ℝ) :
    LinearizedEinsteinDust B κ ρ h δ v ↔
      ∀ x ∈ domain B.toData, ∀ i k, deriv (fun ε => dustResidual B κ ρ h δ v ε x i k) 0 = 0 := by
  refine forall₂_congr fun x hx => forall₂_congr fun i k => ?_
  rw [(hasDerivAt_dustResidual hP δ v hx i k).deriv, sub_eq_zero]

end Dust

/-! ### Plane waves -/

section Wave

/-- The linear form `x ↦ n · x = n₁x¹ + n₂x² + n₃x³` of a wave vector `n`. -/
def phaseCLM (n : Fin 3 → ℝ) : E →L[ℝ] ℝ := ∑ γ, n γ • (proj γ.succ : E →L[ℝ] ℝ)

/-- The phase `n · x` of a plane wave. -/
def phase (n : Fin 3 → ℝ) (z : E) : ℝ := ∑ γ, n γ * z γ.succ

theorem phaseCLM_apply (n : Fin 3 → ℝ) (z : E) : phaseCLM n z = phase n z := by
  simp [phaseCLM, phase]

/-- `|n|² = n₁² + n₂² + n₃²`. -/
def nsq (n : Fin 3 → ℝ) : ℝ := ∑ γ, n γ ^ 2

theorem nsq_ne_zero {n : Fin 3 → ℝ} (hn : n ≠ 0) : nsq n ≠ 0 := by
  intro h0
  apply hn
  funext γ
  have hγ : n γ ^ 2 = 0 := by
    have hle := Finset.single_le_sum (f := fun γ => n γ ^ 2) (fun γ _ => sq_nonneg (n γ))
      (Finset.mem_univ γ)
    have : n γ ^ 2 ≤ 0 := by simpa [nsq] using hle.trans_eq h0
    exact le_antisymm this (sq_nonneg _)
  simpa using hγ

theorem hasFDerivAt_phase (n : Fin 3 → ℝ) (z : E) :
    HasFDerivAt (phase n) (phaseCLM n) z := by
  have e : phase n = phaseCLM n := funext fun w => (phaseCLM_apply n w).symm
  rw [e]
  exact (phaseCLM n).hasFDerivAt

@[simp] theorem phaseCLM_single_zero (n : Fin 3 → ℝ) : phaseCLM n (Pi.single 0 1) = 0 := by
  simp [phaseCLM_apply, phase, Fin.succ_ne_zero]

@[simp] theorem phaseCLM_single_succ (n : Fin 3 → ℝ) (δ : Fin 3) :
    phaseCLM n (Pi.single δ.succ 1) = n δ := by
  simp [phaseCLM_apply, phase, Pi.single_apply]

/-- The point `(t, s n/|n|²)`, of time `t` and phase `s`. -/
def wavePoint (n : Fin 3 → ℝ) (t s : ℝ) : E := Fin.cons t fun γ => s * n γ / nsq n

@[simp] theorem wavePoint_zero (n : Fin 3 → ℝ) (t s : ℝ) : wavePoint n t s 0 = t := rfl

theorem phase_wavePoint {n : Fin 3 → ℝ} (hn : nsq n ≠ 0) (t s : ℝ) :
    phase n (wavePoint n t s) = s := by
  simp only [phase, wavePoint, Fin.cons_succ]
  have : ∑ γ, n γ * (s * n γ / nsq n) = s * (∑ γ, n γ ^ 2) / nsq n := by
    rw [Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun γ _ => by ring
  rw [this, ← nsq]
  field_simp

theorem wavePoint_mem {n : Fin 3 → ℝ} {t : ℝ} (ht : t ∈ B.I) (s : ℝ) :
    wavePoint n t s ∈ domain B.toData := mem_domain_iff.mpr ht

/-- The derivative of `w ↦ f(w⁰) k(n · w)`. -/
theorem fderiv_wave {n : Fin 3 → ℝ} {f k : ℝ → ℝ} {f' k' : ℝ} (hf : HasDerivAt f f' (z 0))
    (hk : HasDerivAt k k' (phase n z)) (v : E) :
    fderiv ℝ (fun w => f (w 0) * k (phase n w)) z v =
      f' * v 0 * k (phase n z) + f (z 0) * k' * phaseCLM n v := by
  have hK : HasFDerivAt (fun w => k (phase n w)) (k' • phaseCLM n) z :=
    hk.comp_hasFDerivAt z (hasFDerivAt_phase n z)
  have hM : HasFDerivAt (fun w => f (w 0) * k (phase n w))
      (f (z 0) • (k' • phaseCLM n) + k (phase n z) • (f' • proj 0)) z :=
    (hasFDerivAt_time hf).mul hK
  rw [hM.fderiv]
  simp only [add_apply, smul_apply, proj_apply, smul_eq_mul]
  ring

theorem differentiableAt_wave {n : Fin 3 → ℝ} {f k : ℝ → ℝ} {f' k' : ℝ}
    (hf : HasDerivAt f f' (z 0)) (hk : HasDerivAt k k' (phase n z)) :
    DifferentiableAt ℝ (fun w => f (w 0) * k (phase n w)) z :=
  (HasFDerivAt.mul (hasFDerivAt_time hf)
    (hk.comp_hasFDerivAt z (hasFDerivAt_phase n z))).differentiableAt

/-- The first derivative `∂ₜF_{αβ}` of an amplitude. -/
def Fd (F : ℝ → Fin 3 → Fin 3 → ℝ) (t : ℝ) (α β : Fin 3) : ℝ := deriv (fun s => F s α β) t

/-- The second derivative `∂ₜ²F_{αβ}` of an amplitude. -/
def Fdd (F : ℝ → Fin 3 → Fin 3 → ℝ) (t : ℝ) (α β : Fin 3) : ℝ :=
  deriv (deriv fun s => F s α β) t

/-- **A plane-wave perturbation** `h_{αβ} = F_{αβ}(t) k(n · x)` with the profile `k`. -/
def mode (F : ℝ → Fin 3 → Fin 3 → ℝ) (k : ℝ → ℝ) (n : Fin 3 → ℝ) (z : E) (α β : Fin 3) : ℝ :=
  F (z 0) α β * k (phase n z)

/-- A smooth symmetric amplitude on the times. -/
structure IsAmplitude (B : Background) (F : ℝ → Fin 3 → Fin 3 → ℝ) : Prop where
  /-- The entries are smooth on the times. -/
  smooth : ∀ α β, ContDiffOn ℝ ∞ (fun t => F t α β) B.I
  /-- The amplitude is symmetric. -/
  symm : ∀ t α β, F t α β = F t β α

/-- A profile `k` with `k' = k₁` and `k₁' = −k`, such as `cos` and `sin`. -/
structure IsProfile (k k₁ : ℝ → ℝ) : Prop where
  /-- The profile is smooth. -/
  smooth : ContDiff ℝ ∞ k
  /-- `k' = k₁`. -/
  deriv : ∀ s, HasDerivAt k (k₁ s) s
  /-- `k₁' = −k`. -/
  deriv₁ : ∀ s, HasDerivAt k₁ (-k s) s

theorem isProfile_cos : IsProfile Real.cos fun s => -Real.sin s :=
  ⟨Real.contDiff_cos, fun s => Real.hasDerivAt_cos s, fun s => (Real.hasDerivAt_sin s).neg⟩

theorem isProfile_sin : IsProfile Real.sin Real.cos :=
  ⟨Real.contDiff_sin, fun s => Real.hasDerivAt_sin s, fun s => Real.hasDerivAt_cos s⟩

variable {F : ℝ → Fin 3 → Fin 3 → ℝ} {k k₁ : ℝ → ℝ} {n : Fin 3 → ℝ}

theorem IsAmplitude.hasDerivAt (hF : IsAmplitude B F) {t : ℝ} (ht : t ∈ B.I) (α β : Fin 3) :
    HasDerivAt (fun s => F s α β) (Fd F t α β) t :=
  hasDerivAt_of_contDiffOn B.isOpen_I (hF.smooth α β) ht

theorem IsAmplitude.hasDerivAt_Fd (hF : IsAmplitude B F) {t : ℝ} (ht : t ∈ B.I) (α β : Fin 3) :
    HasDerivAt (fun s => Fd F s α β) (Fdd F t α β) t :=
  hasDerivAt_of_contDiffOn B.isOpen_I
    (contDiffOn_deriv_of_contDiffOn B.isOpen_I (hF.smooth α β)) ht

/-- A plane wave with a smooth symmetric amplitude is a perturbation. -/
theorem IsAmplitude.isPerturbation (hF : IsAmplitude B F) (hk : IsProfile k k₁) :
    IsPerturbation B (mode F k n) where
  smooth α β := (contDiffOn_time (D := B.toData) (hF.smooth α β)).mul
    ((hk.smooth.comp (phaseCLM n).contDiff).contDiffOn.congr fun z _ => by
      simp [phaseCLM_apply])
  symm z α β := by simp only [mode, hF.symm (z 0) α β]

theorem dh_mode (hF : IsAmplitude B F) (hk : IsProfile k k₁) (hz : z ∈ domain B.toData)
    (c : Fin 4) (α β : Fin 3) :
    dh (mode F k n) c z α β =
      Fd F (z 0) α β * (Pi.single c 1 : E) 0 * k (phase n z) +
        F (z 0) α β * phaseCLM n (Pi.single c 1) * k₁ (phase n z) := by
  unfold dh mode
  rw [fderiv_wave (hF.hasDerivAt (time_mem_I hz) α β) (hk.deriv _)]
  ring

theorem ddh_mode (hF : IsAmplitude B F) (hk : IsProfile k k₁) (hx : x ∈ domain B.toData)
    (c' c : Fin 4) (α β : Fin 3) :
    ddh (mode F k n) c' c x α β =
      (Pi.single c 1 : E) 0 * (Pi.single c' 1 : E) 0 * Fdd F (x 0) α β * k (phase n x) +
        ((Pi.single c 1 : E) 0 * phaseCLM n (Pi.single c' 1) +
          phaseCLM n (Pi.single c 1) * (Pi.single c' 1 : E) 0) * Fd F (x 0) α β *
            k₁ (phase n x) -
        phaseCLM n (Pi.single c 1) * phaseCLM n (Pi.single c' 1) * F (x 0) α β *
          k (phase n x) := by
  have ht := time_mem_I hx
  have hev : (fun w => dh (mode F k n) c w α β) =ᶠ[𝓝 x] fun w =>
      (Pi.single c 1 : E) 0 * (Fd F (w 0) α β * k (phase n w)) +
        phaseCLM n (Pi.single c 1) * (F (w 0) α β * k₁ (phase n w)) :=
    eventually_of_mem ((domain B.toData).isOpen.mem_nhds hx) fun w hw => by
      simp only
      rw [dh_mode hF hk hw]
      ring
  have h1 := differentiableAt_wave (n := n) (hF.hasDerivAt_Fd ht α β) (hk.deriv (phase n x))
  have h2 := differentiableAt_wave (n := n) (hF.hasDerivAt ht α β) (hk.deriv₁ (phase n x))
  unfold ddh
  rw [hev.fderiv_eq, fderiv_fun_add (h1.const_mul _) (h2.const_mul _), add_apply,
    fderiv_const_mul h1, fderiv_const_mul h2, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul,
    fderiv_wave (hF.hasDerivAt_Fd ht α β) (hk.deriv (phase n x)),
    fderiv_wave (hF.hasDerivAt ht α β) (hk.deriv₁ (phase n x))]
  ring

/-! #### The equations of a plane wave -/

variable (B) in
/-- The amplitude of `δR₀₀` for a plane wave: `−½ ∂ₜ² F_γγ − H ∂ₜ F_γγ`. -/
def modeTime (F : ℝ → Fin 3 → Fin 3 → ℝ) (t : ℝ) : ℝ :=
  -(∑ γ, Fdd F t γ γ) / 2 - deriv B.a t / B.a t * ∑ γ, Fd F t γ γ

/-- The amplitude of `δR₀α` for a plane wave: `½ (n_γ ∂ₜF_{γα} − n_α ∂ₜF_γγ)`. -/
def modeMixed (F : ℝ → Fin 3 → Fin 3 → ℝ) (n : Fin 3 → ℝ) (t : ℝ) (α : Fin 3) : ℝ :=
  (∑ γ, n γ * Fd F t γ α - n α * ∑ γ, Fd F t γ γ) / 2

variable (B) in
/-- The amplitude of `δR_{αβ}` for a plane wave:
`½ (n² F_{αβ} + n_α n_β F_γγ − n_α n_γ F_{γβ} − n_β n_γ F_{γα}) + (2ȧ² + aä) F_{αβ}
+ (3/2) aȧ ∂ₜF_{αβ} + ½ a² ∂ₜ²F_{αβ} + ½ aȧ ∂ₜF_γγ δ_{αβ}`. -/
def modeSpace (F : ℝ → Fin 3 → Fin 3 → ℝ) (n : Fin 3 → ℝ) (t : ℝ) (α β : Fin 3) : ℝ :=
  (nsq n * F t α β + n α * n β * ∑ γ, F t γ γ - n α * ∑ γ, n γ * F t γ β -
      n β * ∑ γ, n γ * F t γ α) / 2 +
    (2 * deriv B.a t ^ 2 + B.a t * deriv (deriv B.a) t) * F t α β +
    3 / 2 * (B.a t * deriv B.a t) * Fd F t α β + B.a t ^ 2 / 2 * Fdd F t α β +
    if α = β then B.a t * deriv B.a t / 2 * ∑ γ, Fd F t γ γ else 0

theorem linRicciTime_mode (hF : IsAmplitude B F) (hk : IsProfile k k₁)
    (hx : x ∈ domain B.toData) :
    linRicciTime B (mode F k n) x = modeTime B F (x 0) * k (phase n x) := by
  unfold linRicciTime modeTime
  simp only [ddh_mode hF hk hx, dh_mode hF hk hx, single_zero_apply_zero, phaseCLM_single_zero,
    mul_zero, zero_mul, add_zero, sub_zero, mul_one, ← Finset.sum_mul]
  ring_nf

theorem linRicciMixed_mode (hF : IsAmplitude B F) (hk : IsProfile k k₁)
    (hx : x ∈ domain B.toData) (α : Fin 3) :
    linRicciMixed (mode F k n) x α = modeMixed F n (x 0) α * k₁ (phase n x) := by
  unfold linRicciMixed modeMixed
  simp only [ddh_mode hF hk hx, single_zero_apply_zero, single_succ_apply_zero,
    phaseCLM_single_zero, phaseCLM_single_succ, mul_zero, zero_mul, add_zero, zero_add, sub_zero,
    mul_one, one_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  ring_nf

theorem linRicciSpace_mode (hF : IsAmplitude B F) (hk : IsProfile k k₁)
    (hx : x ∈ domain B.toData) (α β : Fin 3) :
    linRicciSpace B (mode F k n) x α β = modeSpace B F n (x 0) α β * k (phase n x) := by
  unfold linRicciSpace modeSpace
  simp only [ddh_mode hF hk hx, dh_mode hF hk hx, single_zero_apply_zero, single_succ_apply_zero,
    phaseCLM_single_zero, phaseCLM_single_succ, mul_zero, zero_mul, add_zero, sub_zero, zero_sub,
    mul_one, one_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, mode]
  have e1 : ∑ i : Fin 3, n i * n i = nsq n := Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i : Fin 3, n α * n i * F (x 0) i β = n α * ∑ i, n i * F (x 0) i β := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ i : Fin 3, n β * n i * F (x 0) i α = n β * ∑ i, n i * F (x 0) i α := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, e3]
  split_ifs <;> ring

/-- **The linearized equations of a plane wave are ordinary differential equations.** For the
perturbation `h_{αβ} = F_{αβ}(t) k(n · x)`, the density contrast `δ = δ̂(t) k(n · x)` and the
velocity `v_α = V_α(t) k'(n · x)`, with `n ≠ 0` and a profile `k` with `k'' = −k` (`cos` or
`sin`), the linearized Einstein equations with dust hold on the domain if and only if on `I` the
amplitudes satisfy `modeTime = ½ κρδ̂`, `modeMixed = −κρ V` and
`modeSpace = ½ κρ a² (δ̂ δ + F)`. -/
theorem mode_iff {κ : ℝ} {ρ : ℝ → ℝ} (hF : IsAmplitude B F) (hk : IsProfile k k₁)
    (hn : nsq n ≠ 0) (hk0 : ∃ s, k s ≠ 0) (hk1 : ∃ s, k₁ s ≠ 0) (dc : ℝ → ℝ)
    (V : ℝ → Fin 3 → ℝ) :
    LinearizedEinsteinDust B κ ρ (mode F k n) (fun z => dc (z 0) * k (phase n z))
        (fun z α => V (z 0) α * k₁ (phase n z)) ↔
      ∀ t ∈ B.I, modeTime B F t = κ * (ρ t * dc t / 2) ∧
        (∀ α, modeMixed F n t α = κ * -(ρ t * V t α)) ∧
        ∀ α β, modeSpace B F n t α β =
          κ * (ρ t * B.a t ^ 2 * ((if α = β then dc t else 0) + F t α β) / 2) := by
  constructor
  · intro hL t ht
    obtain ⟨s₀, hs₀⟩ := hk0
    obtain ⟨s₁, hs₁⟩ := hk1
    have hx₀ := wavePoint_mem (B := B) (n := n) ht s₀
    have hx₁ := wavePoint_mem (B := B) (n := n) ht s₁
    refine ⟨?_, fun α => ?_, fun α β => ?_⟩
    · have e := hL _ hx₀ 0 0
      rw [linRicci_zero_zero, linRicciTime_mode hF hk hx₀, linDust_zero_zero] at e
      simp only [wavePoint_zero, phase_wavePoint hn] at e
      exact mul_right_cancel₀ hs₀ (by rw [e]; ring)
    · have e := hL _ hx₁ 0 α.succ
      rw [linRicci_zero_succ, linRicciMixed_mode hF hk hx₁, linDust_zero_succ] at e
      simp only [wavePoint_zero, phase_wavePoint hn] at e
      exact mul_right_cancel₀ hs₁ (by rw [e]; ring)
    · have e := hL _ hx₀ α.succ β.succ
      rw [linRicci_succ_succ, linRicciSpace_mode hF hk hx₀, linDust_succ_succ] at e
      simp only [wavePoint_zero, phase_wavePoint hn, mode] at e
      refine mul_right_cancel₀ hs₀ ?_
      rw [e]
      split_ifs <;> ring
  · intro h x hx i j
    have ht := time_mem_I hx
    obtain ⟨h0, h1, h2⟩ := h (x 0) ht
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨α, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨β, rfl⟩
    · rw [linRicci_zero_zero, linRicciTime_mode hF hk hx, linDust_zero_zero, h0]
      ring
    · rw [linRicci_zero_succ, linRicciMixed_mode hF hk hx, linDust_zero_succ, h1]
      ring
    · rw [linRicci_succ_zero, linRicciMixed_mode hF hk hx, linDust_succ_zero, h1]
      ring
    · rw [linRicci_succ_succ, linRicciSpace_mode hF hk hx, linDust_succ_succ, h2]
      simp only [mode]
      split_ifs <;> ring

end Wave

/-! ### The scalar perturbations -/

section Scalar

/-- The Kronecker symbol `δ_{αβ}`. -/
def kron (α β : Fin 3) : ℝ := if α = β then 1 else 0

/-- The traceless longitudinal tensor `n_α n_β/n² − δ_{αβ}/3`. -/
def longitudinal (n : Fin 3 → ℝ) (α β : Fin 3) : ℝ := n α * n β / nsq n - kron α β / 3

theorem sum_kron_mul (f : Fin 3 → ℝ) (β : Fin 3) : ∑ γ, f γ * kron γ β = f β := by
  simp [kron]

theorem sum_kron_diag : ∑ γ : Fin 3, kron γ γ = 3 := by
  simp [kron]

theorem sum_longitudinal_diag {n : Fin 3 → ℝ} (hn : nsq n ≠ 0) :
    ∑ γ, longitudinal n γ γ = 0 := by
  simp only [longitudinal, Finset.sum_sub_distrib, ← Finset.sum_div, sum_kron_diag]
  have : ∑ γ, n γ * n γ = nsq n := Finset.sum_congr rfl fun γ _ => by ring
  rw [this, div_self hn]
  norm_num

theorem sum_mul_longitudinal {n : Fin 3 → ℝ} (hn : nsq n ≠ 0) (β : Fin 3) :
    ∑ γ, n γ * longitudinal n γ β = 2 / 3 * n β := by
  have e : ∑ γ, n γ * longitudinal n γ β =
      (∑ γ, n γ * n γ) * n β / nsq n - (∑ γ, n γ * kron γ β) / 3 := by
    rw [Finset.sum_mul, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun γ _ => by unfold longitudinal; ring
  have : ∑ γ, n γ * n γ = nsq n := Finset.sum_congr rfl fun γ _ => by ring
  rw [e, this, sum_kron_mul]
  field_simp
  ring

theorem longitudinal_symm (n : Fin 3 → ℝ) (α β : Fin 3) :
    longitudinal n α β = longitudinal n β α := by
  unfold longitudinal kron
  by_cases h : α = β
  · subst h; rfl
  · simp only [h, Ne.symm h, ite_false]
    ring

theorem kron_symm (α β : Fin 3) : kron α β = kron β α := by
  unfold kron
  by_cases h : α = β
  · subst h; rfl
  · simp only [h, Ne.symm h, ite_false]

/-- **The decomposition of a symmetric tensor of the scalar sector**:
`A (n_α n_β/n² − δ_{αβ}/3) + C δ_{αβ}/3` vanishes for all `α, β` if and only if `A = C = 0`. -/
theorem scalar_decomp_eq_zero_iff {n : Fin 3 → ℝ} (hn : nsq n ≠ 0) (A C : ℝ) :
    (∀ α β, A * longitudinal n α β + C * (kron α β / 3) = 0) ↔ A = 0 ∧ C = 0 := by
  constructor
  · intro h
    have hC : C = 0 := by
      have htr : ∑ α, (A * longitudinal n α α + C * (kron α α / 3)) = 0 :=
        Finset.sum_eq_zero fun α _ => h α α
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_longitudinal_diag hn,
        ← Finset.sum_div, sum_kron_diag] at htr
      linarith
    refine ⟨?_, hC⟩
    have hnn : ∑ α, ∑ β, n α * n β * (A * longitudinal n α β + C * (kron α β / 3)) = 0 :=
      Finset.sum_eq_zero fun α _ => Finset.sum_eq_zero fun β _ => by rw [h α β, mul_zero]
    have e : ∑ α, ∑ β, n α * n β * (A * longitudinal n α β + C * (kron α β / 3)) =
        A * (2 / 3 * nsq n) := by
      simp only [hC, zero_mul, add_zero]
      have : ∀ α, ∑ β, n α * n β * (A * longitudinal n α β) =
          A * n α * ∑ β, n β * longitudinal n β α := fun α => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun β _ => by rw [longitudinal_symm]; ring
      simp only [this, sum_mul_longitudinal hn, nsq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun α _ => by ring
    rw [e] at hnn
    have h3 : (2 / 3 * nsq n) ≠ 0 := mul_ne_zero (by norm_num) hn
    exact (mul_eq_zero.mp hnn).resolve_right h3
  · rintro ⟨rfl, rfl⟩ α β
    ring

/-- The amplitude `λ(t) (n_α n_β/n² − δ_{αβ}/3) + μ(t) δ_{αβ}/3` of a scalar perturbation. -/
def scalarAmp (n : Fin 3 → ℝ) (lam mu : ℝ → ℝ) (t : ℝ) (α β : Fin 3) : ℝ :=
  lam t * longitudinal n α β + mu t * (kron α β / 3)

/-- **The scalar mode** `h_{αβ} = λ(t) (n_α n_β/n² − δ_{αβ}/3) cos(n · x)
+ μ(t) (δ_{αβ}/3) cos(n · x)` (Landau–Lifshitz, §115). -/
def scalarMode (n : Fin 3 → ℝ) (lam mu : ℝ → ℝ) : E → Fin 3 → Fin 3 → ℝ :=
  mode (scalarAmp n lam mu) Real.cos n

theorem scalarMode_apply (n : Fin 3 → ℝ) (lam mu : ℝ → ℝ) (z : E) (α β : Fin 3) :
    scalarMode n lam mu z α β =
      lam (z 0) * (n α * n β / nsq n - (if α = β then 1 else 0) / 3) * Real.cos (phase n z) +
        mu (z 0) * ((if α = β then 1 else 0) / 3) * Real.cos (phase n z) := by
  simp only [scalarMode, mode, scalarAmp, longitudinal, kron]
  ring

variable {lam mu : ℝ → ℝ} {n : Fin 3 → ℝ}

theorem isAmplitude_scalarAmp (hlam : ContDiffOn ℝ ∞ lam B.I) (hmu : ContDiffOn ℝ ∞ mu B.I) :
    IsAmplitude B (scalarAmp n lam mu) where
  smooth α β := (hlam.mul contDiffOn_const).add (hmu.mul contDiffOn_const)
  symm t α β := by simp only [scalarAmp, longitudinal_symm n α β, kron_symm α β]

/-- The scalar modes are perturbations. -/
theorem isPerturbation_scalarMode (hlam : ContDiffOn ℝ ∞ lam B.I) (hmu : ContDiffOn ℝ ∞ mu B.I) :
    IsPerturbation B (scalarMode n lam mu) :=
  (isAmplitude_scalarAmp hlam hmu).isPerturbation isProfile_cos

theorem Fd_scalarAmp (hlam : ContDiffOn ℝ ∞ lam B.I) (hmu : ContDiffOn ℝ ∞ mu B.I) {t : ℝ}
    (ht : t ∈ B.I) (α β : Fin 3) :
    Fd (scalarAmp n lam mu) t α β = scalarAmp n (deriv lam) (deriv mu) t α β := by
  unfold Fd scalarAmp
  have h1 := hasDerivAt_of_contDiffOn B.isOpen_I hlam ht
  have h2 := hasDerivAt_of_contDiffOn B.isOpen_I hmu ht
  exact ((h1.mul_const _).add (h2.mul_const _)).deriv

theorem Fdd_scalarAmp (hlam : ContDiffOn ℝ ∞ lam B.I) (hmu : ContDiffOn ℝ ∞ mu B.I) {t : ℝ}
    (ht : t ∈ B.I) (α β : Fin 3) :
    Fdd (scalarAmp n lam mu) t α β =
      scalarAmp n (deriv (deriv lam)) (deriv (deriv mu)) t α β := by
  have hev : (deriv fun s => scalarAmp n lam mu s α β) =ᶠ[𝓝 t]
      fun s => scalarAmp n (deriv lam) (deriv mu) s α β :=
    eventually_of_mem (B.isOpen_I.mem_nhds ht) fun s hs => Fd_scalarAmp hlam hmu hs α β
  unfold Fdd
  rw [hev.deriv_eq]
  unfold scalarAmp
  have h1 := hasDerivAt_of_contDiffOn B.isOpen_I
    (contDiffOn_deriv_of_contDiffOn B.isOpen_I hlam) ht
  have h2 := hasDerivAt_of_contDiffOn B.isOpen_I
    (contDiffOn_deriv_of_contDiffOn B.isOpen_I hmu) ht
  exact ((h1.mul_const _).add (h2.mul_const _)).deriv

theorem sum_scalarAmp_diag (hn : nsq n ≠ 0) (lam mu : ℝ → ℝ) (t : ℝ) :
    ∑ γ, scalarAmp n lam mu t γ γ = mu t := by
  simp only [scalarAmp, Finset.sum_add_distrib, ← Finset.mul_sum, sum_longitudinal_diag hn,
    ← Finset.sum_div, sum_kron_diag]
  ring

theorem sum_mul_scalarAmp (hn : nsq n ≠ 0) (lam mu : ℝ → ℝ) (t : ℝ) (β : Fin 3) :
    ∑ γ, n γ * scalarAmp n lam mu t γ β = (2 / 3 * lam t + mu t / 3) * n β := by
  have e : ∑ γ, n γ * scalarAmp n lam mu t γ β =
      lam t * ∑ γ, n γ * longitudinal n γ β + mu t / 3 * ∑ γ, n γ * kron γ β := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun γ _ => by unfold scalarAmp; ring
  rw [e, sum_mul_longitudinal hn, sum_kron_mul]
  ring

theorem modeTime_scalarAmp (hlam : ContDiffOn ℝ ∞ lam B.I) (hmu : ContDiffOn ℝ ∞ mu B.I)
    (hn : nsq n ≠ 0) {t : ℝ} (ht : t ∈ B.I) :
    modeTime B (scalarAmp n lam mu) t =
      -deriv (deriv mu) t / 2 - deriv B.a t / B.a t * deriv mu t := by
  unfold modeTime
  simp only [Fd_scalarAmp hlam hmu ht, Fdd_scalarAmp hlam hmu ht, sum_scalarAmp_diag hn]

theorem modeMixed_scalarAmp (hlam : ContDiffOn ℝ ∞ lam B.I) (hmu : ContDiffOn ℝ ∞ mu B.I)
    (hn : nsq n ≠ 0) {t : ℝ} (ht : t ∈ B.I) (α : Fin 3) :
    modeMixed (scalarAmp n lam mu) n t α = (deriv lam t - deriv mu t) * n α / 3 := by
  unfold modeMixed
  simp only [Fd_scalarAmp hlam hmu ht, sum_scalarAmp_diag hn, sum_mul_scalarAmp hn]
  ring

/-- The spatial equation of a scalar mode, decomposed on `n_α n_β/n² − δ_{αβ}/3` and `δ_{αβ}/3`,
on a background with `2ȧ² + aä = ½ κρa²`. -/
theorem modeSpace_scalarAmp {κ : ℝ} {ρ : ℝ → ℝ} (hlam : ContDiffOn ℝ ∞ lam B.I)
    (hmu : ContDiffOn ℝ ∞ mu B.I) (hn : nsq n ≠ 0) {t : ℝ} (ht : t ∈ B.I)
    (hbg : 2 * deriv B.a t ^ 2 + B.a t * deriv (deriv B.a) t = κ * ρ t * B.a t ^ 2 / 2)
    (dc : ℝ → ℝ) (α β : Fin 3) :
    modeSpace B (scalarAmp n lam mu) n t α β -
        κ * (ρ t * B.a t ^ 2 * ((if α = β then dc t else 0) + scalarAmp n lam mu t α β) / 2) =
      B.a t ^ 2 / 2 * (deriv (deriv lam) t + 3 * (deriv B.a t / B.a t) * deriv lam t +
          nsq n * (mu t - lam t) / (3 * B.a t ^ 2)) * longitudinal n α β +
        B.a t ^ 2 / 2 * (deriv (deriv mu) t + 6 * (deriv B.a t / B.a t) * deriv mu t +
          4 * nsq n * (mu t - lam t) / (3 * B.a t ^ 2) - 3 * κ * ρ t * dc t) *
          (kron α β / 3) := by
  have ha := (B.a_pos t ht).ne'
  unfold modeSpace
  rw [hbg]
  simp only [Fd_scalarAmp hlam hmu ht, Fdd_scalarAmp hlam hmu ht, sum_scalarAmp_diag hn,
    sum_mul_scalarAmp hn]
  unfold scalarAmp longitudinal kron
  split_ifs
  · field_simp
    ring
  · field_simp
    ring

/-- **The scalar perturbations reduce to ordinary differential equations** (Landau–Lifshitz,
§115). On a flat background that solves the Einstein equations with dust, for a wave vector
`n ≠ 0`, the scalar mode `h_{αβ} = λ(t) (n_α n_β/n² − δ_{αβ}/3) cos(n · x)
+ μ(t) (δ_{αβ}/3) cos(n · x)`, the density contrast `δ = δ̂(t) cos(n · x)` and the velocity
`v_α = w(t) n_α sin(n · x)` solve the linearized Einstein equations with dust if and only if on
`I`, with `H = ȧ/a`,
`λ̈ + 3Hλ̇ + n² (μ − λ)/(3a²) = 0`, `μ̈ + 3Hμ̇ + n² (μ − λ)/(3a²) = 0`,
`κρδ̂ = −(μ̈ + 2Hμ̇)` and `μ̇ − λ̇ = −3κρw`. -/
theorem scalarMode_iff {κ : ℝ} {ρ : ℝ → ℝ} (hB : (metric B.toData).IsEinstein κ 0
      (perfectFluidStress B.toData ρ fun _ => 0)) (hn : n ≠ 0)
    (hlam : ContDiffOn ℝ ∞ lam B.I) (hmu : ContDiffOn ℝ ∞ mu B.I) (dc w : ℝ → ℝ) :
    LinearizedEinsteinDust B κ ρ (scalarMode n lam mu) (fun z => dc (z 0) * Real.cos (phase n z))
        (fun z α => w (z 0) * n α * Real.sin (phase n z)) ↔
      ∀ t ∈ B.I,
        deriv (deriv lam) t + 3 * (deriv B.a t / B.a t) * deriv lam t +
            nsq n * (mu t - lam t) / (3 * B.a t ^ 2) = 0 ∧
        deriv (deriv mu) t + 3 * (deriv B.a t / B.a t) * deriv mu t +
            nsq n * (mu t - lam t) / (3 * B.a t ^ 2) = 0 ∧
        κ * ρ t * dc t = -(deriv (deriv mu) t + 2 * (deriv B.a t / B.a t) * deriv mu t) ∧
        deriv mu t - deriv lam t = -(3 * κ * ρ t * w t) := by
  have hn' := nsq_ne_zero hn
  obtain ⟨α₀, hα₀⟩ := Function.ne_iff.mp hn
  replace hα₀ : n α₀ ≠ 0 := by simpa using hα₀
  have hv : (fun z α => w (z 0) * n α * Real.sin (phase n z)) =
      fun z α => (fun t α => -(w t * n α)) (z 0) α * (fun s => -Real.sin s) (phase n z) := by
    funext z α
    ring
  rw [hv, scalarMode]
  refine (mode_iff (isAmplitude_scalarAmp hlam hmu) isProfile_cos hn' ⟨0, by simp⟩
    ⟨Real.pi / 2, by simp⟩ dc fun t α => -(w t * n α)).trans (forall₂_congr fun t ht => ?_)
  have ha := (B.a_pos t ht).ne'
  obtain ⟨e1, e2⟩ := dust_background hB ht
  have hbg : 2 * deriv B.a t ^ 2 + B.a t * deriv (deriv B.a) t = κ * ρ t * B.a t ^ 2 / 2 := by
    rw [e1, e2]; ring
  have hS : (∀ α β, modeSpace B (scalarAmp n lam mu) n t α β =
      κ * (ρ t * B.a t ^ 2 * ((if α = β then dc t else 0) + scalarAmp n lam mu t α β) / 2)) ↔
      (deriv (deriv lam) t + 3 * (deriv B.a t / B.a t) * deriv lam t +
          nsq n * (mu t - lam t) / (3 * B.a t ^ 2) = 0 ∧
        deriv (deriv mu) t + 6 * (deriv B.a t / B.a t) * deriv mu t +
          4 * nsq n * (mu t - lam t) / (3 * B.a t ^ 2) - 3 * κ * ρ t * dc t = 0) := by
    have ha2 : B.a t ^ 2 / 2 ≠ 0 := by positivity
    rw [show (∀ α β, modeSpace B (scalarAmp n lam mu) n t α β =
        κ * (ρ t * B.a t ^ 2 * ((if α = β then dc t else 0) + scalarAmp n lam mu t α β) / 2)) ↔
        ∀ α β, B.a t ^ 2 / 2 * (deriv (deriv lam) t + 3 * (deriv B.a t / B.a t) * deriv lam t +
          nsq n * (mu t - lam t) / (3 * B.a t ^ 2)) * longitudinal n α β +
        B.a t ^ 2 / 2 * (deriv (deriv mu) t + 6 * (deriv B.a t / B.a t) * deriv mu t +
          4 * nsq n * (mu t - lam t) / (3 * B.a t ^ 2) - 3 * κ * ρ t * dc t) *
          (kron α β / 3) = 0 from forall₂_congr fun α β => by
        rw [← sub_eq_zero, modeSpace_scalarAmp hlam hmu hn' ht hbg dc α β],
      scalar_decomp_eq_zero_iff hn']
    simp only [mul_eq_zero, ha2, false_or]
  have hM : (∀ α, modeMixed (scalarAmp n lam mu) n t α = κ * -(ρ t * -(w t * n α))) ↔
      deriv mu t - deriv lam t = -(3 * κ * ρ t * w t) := by
    simp only [modeMixed_scalarAmp hlam hmu hn' ht]
    constructor
    · intro h
      have := h α₀
      have h3 : (deriv lam t - deriv mu t) / 3 = κ * ρ t * w t :=
        mul_right_cancel₀ hα₀ (by rw [div_mul_eq_mul_div, this]; ring)
      linarith
    · intro h α
      have : deriv lam t - deriv mu t = 3 * κ * ρ t * w t := by linarith
      rw [this]
      ring
  rw [modeTime_scalarAmp hlam hmu hn' ht, hM, hS]
  constructor
  · rintro ⟨hT, hW, hA, hC⟩
    refine ⟨hA, ?_, ?_, hW⟩
    · have : κ * ρ t * dc t = -(deriv (deriv mu) t + 2 * (deriv B.a t / B.a t) * deriv mu t) := by
        linarith
      linear_combination (hC + 3 * this) / 4
    · linarith
  · rintro ⟨hA, hB', hC, hW⟩
    refine ⟨by linarith, hW, hA, ?_⟩
    linear_combination 4 * hB' - 3 * hC

end Scalar

/-! ### The flat dust universe -/

section DustUniverse

/-- `t^{k/3} = (t^{1/3})^k` for `t > 0`. -/
theorem rpow_div_three {t : ℝ} (ht : 0 < t) (k : ℤ) :
    t ^ ((k : ℝ) / 3) = (t ^ (1 / 3 : ℝ)) ^ k := by
  rw [← Real.rpow_intCast, ← Real.rpow_mul ht.le]
  congr 1
  ring

theorem cbrt_pos {t : ℝ} (ht : 0 < t) : 0 < t ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos ht _

theorem cbrt_cube {t : ℝ} (ht : 0 < t) : (t ^ (1 / 3 : ℝ)) ^ 3 = t := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  norm_num

/-- The power `s ↦ A s^{k/3} + K` has the derivative `A (k/3) t^{(k−3)/3}`. -/
theorem hasDerivAt_powThird (A K : ℝ) (k : ℤ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => A * s ^ ((k : ℝ) / 3) + K)
      (A * ((k : ℝ) / 3) * t ^ (((k - 3 : ℤ) : ℝ) / 3)) t := by
  have h :=
    ((Real.hasDerivAt_rpow_const (p := (k : ℝ) / 3) (Or.inl ht.ne')).const_mul A).add_const K
  convert h using 1
  push_cast
  ring_nf

theorem deriv_powThird (A K : ℝ) (k : ℤ) {t : ℝ} (ht : 0 < t) :
    deriv (fun s => A * s ^ ((k : ℝ) / 3) + K) t =
      A * ((k : ℝ) / 3) * (t ^ (1 / 3 : ℝ)) ^ (k - 3) := by
  rw [(hasDerivAt_powThird A K k ht).deriv, rpow_div_three ht]

theorem deriv_deriv_powThird (A K : ℝ) (k : ℤ) {t : ℝ} (ht : 0 < t) :
    deriv (deriv fun s => A * s ^ ((k : ℝ) / 3) + K) t =
      A * ((k : ℝ) / 3) * (((k - 3 : ℤ) : ℝ) / 3) * (t ^ (1 / 3 : ℝ)) ^ (k - 6) := by
  have hev : (deriv fun s => A * s ^ ((k : ℝ) / 3) + K) =ᶠ[𝓝 t]
      fun s => A * ((k : ℝ) / 3) * s ^ (((k - 3 : ℤ) : ℝ) / 3) + 0 :=
    eventually_of_mem (isOpen_Ioi.mem_nhds ht) fun s hs => by
      simp only [add_zero]
      exact (hasDerivAt_powThird A K k hs).deriv
  rw [hev.deriv_eq, deriv_powThird _ _ _ ht]
  congr 2
  ring

theorem contDiffOn_powThird (A K q : ℝ) :
    ContDiffOn ℝ ∞ (fun s : ℝ => A * s ^ q + K) (Ioi 0) := fun _ ht =>
  ((contDiffAt_const.mul (Real.contDiffAt_rpow_const_of_ne (ne_of_gt ht))).add
    contDiffAt_const).contDiffWithinAt

/-- The sum `s ↦ A s^{k/3} + C s^{m/3}` of two powers and its derivatives. -/
theorem hasDerivAt_powPair (A C : ℝ) (k m : ℤ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => A * s ^ ((k : ℝ) / 3) + C * s ^ ((m : ℝ) / 3))
      (A * ((k : ℝ) / 3) * t ^ (((k - 3 : ℤ) : ℝ) / 3) +
        C * ((m : ℝ) / 3) * t ^ (((m - 3 : ℤ) : ℝ) / 3)) t := by
  have h1 := hasDerivAt_powThird A 0 k ht
  have h2 := hasDerivAt_powThird C 0 m ht
  simp only [add_zero] at h1 h2
  exact h1.fun_add h2

theorem deriv_powPair (A C : ℝ) (k m : ℤ) {t : ℝ} (ht : 0 < t) :
    deriv (fun s => A * s ^ ((k : ℝ) / 3) + C * s ^ ((m : ℝ) / 3)) t =
      A * ((k : ℝ) / 3) * (t ^ (1 / 3 : ℝ)) ^ (k - 3) +
        C * ((m : ℝ) / 3) * (t ^ (1 / 3 : ℝ)) ^ (m - 3) := by
  rw [(hasDerivAt_powPair A C k m ht).deriv, rpow_div_three ht, rpow_div_three ht]

theorem deriv_deriv_powPair (A C : ℝ) (k m : ℤ) {t : ℝ} (ht : 0 < t) :
    deriv (deriv fun s => A * s ^ ((k : ℝ) / 3) + C * s ^ ((m : ℝ) / 3)) t =
      A * ((k : ℝ) / 3) * (((k - 3 : ℤ) : ℝ) / 3) * (t ^ (1 / 3 : ℝ)) ^ (k - 6) +
        C * ((m : ℝ) / 3) * (((m - 3 : ℤ) : ℝ) / 3) * (t ^ (1 / 3 : ℝ)) ^ (m - 6) := by
  have hev : (deriv fun s => A * s ^ ((k : ℝ) / 3) + C * s ^ ((m : ℝ) / 3)) =ᶠ[𝓝 t]
      fun s => A * ((k : ℝ) / 3) * s ^ (((k - 3 : ℤ) : ℝ) / 3) +
        C * ((m : ℝ) / 3) * s ^ (((m - 3 : ℤ) : ℝ) / 3) :=
    eventually_of_mem (isOpen_Ioi.mem_nhds ht) fun s hs => (hasDerivAt_powPair A C k m hs).deriv
  rw [hev.deriv_eq, deriv_powPair _ _ _ _ ht]
  congr 2 <;> ring_nf

theorem contDiffOn_powPair (A C q r : ℝ) :
    ContDiffOn ℝ ∞ (fun s : ℝ => A * s ^ q + C * s ^ r) (Ioi 0) := by
  have h := (contDiffOn_powThird A 0 q).add (contDiffOn_powThird C 0 r)
  simpa using h

/-- **The flat dust universe** `a(t) = t^{2/3}` on `t > 0` (Landau–Lifshitz, §112, the flat
model in the cosmic time). -/
def dustBackground : Background where
  I := Ioi 0
  a := fun t => t ^ (2 / 3 : ℝ)
  isOpen_I := isOpen_Ioi
  contDiffOn_a := by
    simpa using contDiffOn_powThird 1 0 (2 / 3)
  a_pos := fun t ht => Real.rpow_pos_of_pos ht _

/-- The density `ρ = 4/(3κt²)` of the flat dust universe. -/
def dustDensity (κ t : ℝ) : ℝ := 4 / (3 * κ * t ^ 2)

theorem dustBackground_a_eq : dustBackground.a = fun s => 1 * s ^ (((2 : ℤ) : ℝ) / 3) + 0 := by
  funext s
  simp [dustBackground]

theorem dustBackground_a {t : ℝ} (ht : 0 < t) : dustBackground.a t = (t ^ (1 / 3 : ℝ)) ^ 2 := by
  rw [dustBackground_a_eq]
  simpa using rpow_div_three ht 2

theorem deriv_dustBackground_a {t : ℝ} (ht : 0 < t) :
    deriv dustBackground.a t = 2 / 3 * (t ^ (1 / 3 : ℝ)) ^ (-1 : ℤ) := by
  rw [dustBackground_a_eq, deriv_powThird _ _ _ ht]
  norm_num

theorem deriv_deriv_dustBackground_a {t : ℝ} (ht : 0 < t) :
    deriv (deriv dustBackground.a) t = -(2 / 9) * (t ^ (1 / 3 : ℝ)) ^ (-4 : ℤ) := by
  rw [dustBackground_a_eq, deriv_deriv_powThird _ _ _ ht]
  norm_num

/-- **The flat dust universe solves the Einstein equations** with the comoving dust of density
`ρ = 4/(3κt²)`, for every `κ ≠ 0`. -/
theorem isEinstein_dustBackground {κ : ℝ} (hκ : κ ≠ 0) :
    (metric dustBackground.toData).IsEinstein κ 0
      (perfectFluidStress dustBackground.toData (dustDensity κ) fun _ => 0) := by
  rw [isEinstein_iff_friedmann]
  intro t ht
  have ht' : 0 < t := ht
  have hr := cbrt_pos ht'
  have hc := cbrt_cube ht'
  rw [firstFriedmann_iff_of_lapse_eq_one (fun _ _ => rfl) ht,
    secondFriedmann_iff_of_lapse_eq_one (fun _ _ => rfl) ht]
  simp only [hubble, Background.toData_a, Background.toData_k, zero_div, add_zero, mul_zero,
    dustDensity]
  rw [dustBackground_a ht', deriv_dustBackground_a ht', deriv_deriv_dustBackground_a ht']
  set r := t ^ (1 / 3 : ℝ)
  clear_value r
  subst hc
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- **The growing mode** (Landau–Lifshitz, §115): on the flat dust universe `a = t^{2/3}`, for
`n ≠ 0` and any amplitude `c`, the comoving (`v = 0`) scalar mode with
`μ = −2c t^{2/3}`, `λ = μ − 20c/(3n²)` solves the linearized Einstein equations with the density
contrast `δ = c t^{2/3} cos(n · x)`, which grows like `a ∝ t^{2/3}`. -/
theorem densityContrast_growing {κ : ℝ} (hκ : κ ≠ 0) {n : Fin 3 → ℝ} (hn : n ≠ 0) (c : ℝ) :
    LinearizedEinsteinDust dustBackground κ (dustDensity κ)
      (scalarMode n (fun t => -2 * c * t ^ (2 / 3 : ℝ) - 20 * c / (3 * nsq n))
        (fun t => -2 * c * t ^ (2 / 3 : ℝ)))
      (fun z => c * z 0 ^ (2 / 3 : ℝ) * Real.cos (phase n z)) fun _ _ => 0 := by
  have hn' := nsq_ne_zero hn
  have elam : (fun t : ℝ => -2 * c * t ^ (2 / 3 : ℝ) - 20 * c / (3 * nsq n)) =
      fun s => (-2 * c) * s ^ (((2 : ℤ) : ℝ) / 3) + -(20 * c / (3 * nsq n)) := by
    funext s; push_cast; ring
  have emu : (fun t : ℝ => -2 * c * t ^ (2 / 3 : ℝ)) =
      fun s => (-2 * c) * s ^ (((2 : ℤ) : ℝ) / 3) + 0 := by
    funext s; push_cast; ring
  have hv : (fun _ _ => (0 : ℝ)) =
      fun (z : E) (α : Fin 3) => (fun _ : ℝ => (0 : ℝ)) (z 0) * n α * Real.sin (phase n z) := by
    funext z α; simp
  rw [hv, elam, emu]
  refine (scalarMode_iff (isEinstein_dustBackground hκ) hn
    (contDiffOn_powThird _ _ _) (contDiffOn_powThird _ _ _) (fun t => c * t ^ (2 / 3 : ℝ))
    fun _ => 0).mpr fun t ht => ?_
  have ht' : 0 < t := ht
  simp only [deriv_powThird _ _ _ ht', deriv_deriv_powThird _ _ _ ht', dustBackground_a ht',
    deriv_dustBackground_a ht', dustDensity, rpow_div_three ht', mul_zero, neg_zero]
  rw [show (2 / 3 : ℝ) = ((2 : ℤ) : ℝ) / 3 by norm_num, rpow_div_three ht']
  have hr := cbrt_pos ht'
  have hc := cbrt_cube ht'
  set r := t ^ (1 / 3 : ℝ)
  clear_value r
  subst hc
  push_cast
  norm_num [zpow_neg]
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- **The decaying mode** (Landau–Lifshitz, §115): on the flat dust universe, the comoving
scalar mode with `λ = μ = −2c/t` solves the linearized Einstein equations with the density
contrast `δ = c t⁻¹ cos(n · x)`, which decays like `t⁻¹`. -/
theorem densityContrast_decaying {κ : ℝ} (hκ : κ ≠ 0) {n : Fin 3 → ℝ} (hn : n ≠ 0) (c : ℝ) :
    LinearizedEinsteinDust dustBackground κ (dustDensity κ)
      (scalarMode n (fun t => -2 * c * t ^ (-1 : ℝ)) (fun t => -2 * c * t ^ (-1 : ℝ)))
      (fun z => c * z 0 ^ (-1 : ℝ) * Real.cos (phase n z)) fun _ _ => 0 := by
  have hn' := nsq_ne_zero hn
  have e : (fun t : ℝ => -2 * c * t ^ (-1 : ℝ)) =
      fun s => (-2 * c) * s ^ (((-3 : ℤ) : ℝ) / 3) + 0 := by
    funext s; push_cast; norm_num
  have hv : (fun _ _ => (0 : ℝ)) =
      fun (z : E) (α : Fin 3) => (fun _ : ℝ => (0 : ℝ)) (z 0) * n α * Real.sin (phase n z) := by
    funext z α; simp
  rw [hv, e]
  refine (scalarMode_iff (isEinstein_dustBackground hκ) hn
    (contDiffOn_powThird _ _ _) (contDiffOn_powThird _ _ _) (fun t => c * t ^ (-1 : ℝ))
    fun _ => 0).mpr fun t ht => ?_
  have ht' : 0 < t := ht
  simp only [deriv_powThird _ _ _ ht', deriv_deriv_powThird _ _ _ ht', dustBackground_a ht',
    deriv_dustBackground_a ht', dustDensity, rpow_div_three ht', mul_zero, neg_zero]
  rw [show (-1 : ℝ) = ((-3 : ℤ) : ℝ) / 3 by norm_num, rpow_div_three ht']
  have hr := cbrt_pos ht'
  have hc := cbrt_cube ht'
  set r := t ^ (1 / 3 : ℝ)
  clear_value r
  subst hc
  push_cast
  norm_num [zpow_neg]
  constructor
  · field_simp
    ring
  · field_simp
    ring

end DustUniverse

/-! ### The fictitious mode: a synchronous change of the time -/

section Gauge

variable {P : ℝ → ℝ} {F : ℝ} {n : Fin 3 → ℝ}

/-- **The generator of a synchronous change of co-ordinates** `t ↦ t + F cos(n · x)`:
`ξ⁰ = F cos(n · x)` and `ξ^α = ∂_α ξ⁰ ∫ a⁻² dt = −F P(t) n_α sin(n · x)`, with `P' = a⁻²`
(Landau–Lifshitz, §97: the transformations that keep the reference system synchronous). -/
def gaugeField (P : ℝ → ℝ) (F : ℝ) (n : Fin 3 → ℝ) (z : E) : E :=
  Fin.cons (F * Real.cos (phase n z)) fun γ => -F * n γ * P (z 0) * Real.sin (phase n z)

theorem gaugeField_zero :
    (fun w => gaugeField P F n w 0) = fun w => (fun _ : ℝ => F) (w 0) * Real.cos (phase n w) := by
  funext w
  simp [gaugeField]

theorem gaugeField_succ (γ : Fin 3) :
    (fun w => gaugeField P F n w γ.succ) =
      fun w => (fun t => -F * n γ * P t) (w 0) * Real.sin (phase n w) := by
  funext w
  simp [gaugeField]

/-- `∂_v ξ⁰ = −F sin(n · x) (n · v)`. -/
theorem fderiv_gaugeField_zero (z v : E) :
    fderiv ℝ (fun w => gaugeField P F n w 0) z v =
      -(F * Real.sin (phase n z) * phaseCLM n v) := by
  rw [gaugeField_zero, fderiv_wave (hasDerivAt_const _ F) (Real.hasDerivAt_cos _)]
  ring

/-- `∂_v ξ^γ = −F n_γ (P' v⁰ sin(n · x) + P cos(n · x) (n · v))`. -/
theorem fderiv_gaugeField_succ {P' : ℝ} (hP : HasDerivAt P P' (z 0)) (γ : Fin 3) (v : E) :
    fderiv ℝ (fun w => gaugeField P F n w γ.succ) z v =
      -(F * n γ * (P' * v 0 * Real.sin (phase n z) +
        P (z 0) * Real.cos (phase n z) * phaseCLM n v)) := by
  rw [gaugeField_succ, fderiv_wave ((hP.const_mul (-F * n γ))) (Real.hasDerivAt_sin _)]
  ring

/-- The derivative of the spatial coefficients `a² δ_{αβ}` of the background. -/
theorem fderiv_coefficient_succ_succ (hz : z ∈ domain B.toData) (α β : Fin 3) (v : E) :
    fderiv ℝ (fun w => (metric B.toData).coefficient w α.succ β.succ) z v =
      if α = β then 2 * B.a (z 0) * deriv B.a (z 0) * v 0 else 0 := by
  have e : (fun w => (metric B.toData).coefficient w α.succ β.succ) =
      fun w => if α = β then B.a (w 0) ^ 2 else 0 := funext fun w => coefficient_succ_succ α β
  rw [e]
  split_ifs
  · rw [fderiv_time (φ := fun s => B.a s ^ 2) (hasDerivAt_a_sq (time_mem_I hz))]
  · simp

theorem fderiv_coefficient_zero_left (i : Fin 4) (v : E) :
    fderiv ℝ (fun w => (metric B.toData).coefficient w 0 i) z v = 0 := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨α, rfl⟩
  · simp [coefficient_zero_zero]
  · simp [coefficient_zero_succ]

theorem fderiv_coefficient_zero_right (i : Fin 4) (v : E) :
    fderiv ℝ (fun w => (metric B.toData).coefficient w i 0) z v = 0 := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨α, rfl⟩
  · simp [coefficient_zero_zero]
  · simp [coefficient_succ_zero]

/-- **The synchronous change of the time is a scalar mode** (Landau–Lifshitz, §115): for
`P' = a⁻²` on `I`, the Lie derivative `L_ξ g` of the background along `gaugeField` is the metric
perturbation of the scalar mode with `λ = −2F n² P` and `μ = −2F n² P + 6F ȧ/a`; in particular
`(L_ξ g)₀₀ = (L_ξ g)₀α = 0`, so the change keeps the system synchronous. -/
theorem coordinateLieMetric_gaugeField (hP : ∀ t ∈ B.I, HasDerivAt P (B.a t ^ 2)⁻¹ t)
    (hn : nsq n ≠ 0) (hz : z ∈ domain B.toData) :
    coordinateLieMetric (gaugeField P F n) (metric B.toData) z =
      metricPerturbation B (scalarMode n (fun t => -2 * F * nsq n * P t)
        (fun t => -2 * F * nsq n * P t + 6 * F * (deriv B.a t / B.a t))) z := by
  have ht := time_mem_I hz
  have ha := (a_pos' hz).ne'
  ext i j
  simp only [coordinateLieMetric, Matrix.of_apply, lieOf, Fin.sum_univ_succ (n := 3)]
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨α, rfl⟩ <;>
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨β, rfl⟩ <;>
  simp only [fderiv_coefficient_zero_left, fderiv_coefficient_zero_right,
    fderiv_coefficient_succ_succ hz, fderiv_gaugeField_zero, fderiv_gaugeField_succ (hP _ ht)] <;>
  simp only [coefficient_zero_zero, coefficient_zero_succ, coefficient_succ_zero,
    coefficient_succ_succ, single_zero_apply_zero, single_succ_apply_zero, phaseCLM_single_zero,
    phaseCLM_single_succ, metricPerturbation_zero_left, metricPerturbation_zero_right,
    metricPerturbation_succ_succ, ite_mul, zero_mul, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero, add_zero, zero_add,
    neg_zero, mul_one, neg_mul, one_mul]
  · field_simp
    ring
  · field_simp
    ring
  · simp only [gaugeField, Fin.cons_zero, scalarMode, mode, scalarAmp, longitudinal, kron]
    split_ifs
    · field_simp
      ring
    · field_simp
      ring

theorem contDiffOn_gaugeField (hP : ContDiffOn ℝ ∞ P B.I) :
    ContDiffOn ℝ ∞ (gaugeField P F n) (domain B.toData) := by
  have hφ : ContDiff ℝ ∞ (phase n) := by
    have e : phase n = phaseCLM n := funext fun w => (phaseCLM_apply n w).symm
    rw [e]
    exact (phaseCLM n).contDiff
  refine contDiffOn_pi.2 fun i => ?_
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨γ, rfl⟩
  · rw [gaugeField_zero]
    exact (contDiffOn_const.mul (Real.contDiff_cos.comp hφ).contDiffOn)
  · rw [gaugeField_succ]
    exact (contDiffOn_time (D := B.toData) (contDiffOn_const.mul hP)).mul
      (Real.contDiff_sin.comp hφ).contDiffOn

/-- **The fictitious mode is a change of co-ordinates**: the derivative at `ε = 0` of the pullback
of the background by `z ↦ z + ε ξ(z)`, `ξ = gaugeField`, is the metric perturbation of the
scalar mode with `λ = −2F n² P`, `μ = −2F n² P + 6F ȧ/a`. -/
theorem familyCoeffDeriv_pullback_gaugeField (hP : ∀ t ∈ B.I, HasDerivAt P (B.a t ^ 2)⁻¹ t)
    (hPs : ContDiffOn ℝ ∞ P B.I) (hn : nsq n ≠ 0) (hz : z ∈ domain B.toData) :
    familyCoeffDeriv (pullbackFamily (metric B.toData) (gaugeField P F n)) z =
      metricPerturbation B (scalarMode n (fun t => -2 * F * nsq n * P t)
        (fun t => -2 * F * nsq n * P t + 6 * F * (deriv B.a t / B.a t))) z := by
  rw [familyCoeffDeriv_pullbackFamily (contDiffOn_gaugeField hPs) hz,
    coordinateLieMetric_gaugeField hP hn hz]

theorem scalarMode_congr {lam mu lam' mu' : ℝ → ℝ} (hl : lam (z 0) = lam' (z 0))
    (hm : mu (z 0) = mu' (z 0)) : scalarMode n lam mu z = scalarMode n lam' mu' z := by
  funext α β
  simp only [scalarMode, mode, scalarAmp, hl, hm]

/-- **The fictitious mode** (Landau–Lifshitz, §115). On the flat dust universe, the synchronous
change of the time `t ↦ t + F cos(n · x)`, generated by `ξ = gaugeField P F n` with
`P = −3t^{−1/3}` (`P' = a⁻²`), gives the scalar mode `λ = 6F n² t^{−1/3}`,
`μ = 6F n² t^{−1/3} + 4F t⁻¹`: the metric perturbation is the derivative of the pulled-back
background, the density contrast `δ = −2F t⁻¹ cos(n · x)` is `ξ(ρ)/ρ` and the velocity
`v_α = F n_α sin(n · x)` is `−∂_α ξ⁰` (the changes of `ρ` and of `u = −dt` along `ξ`). It solves
the linearized Einstein equations, although it is not a physical perturbation: its density
contrast decays like the physical decaying mode, `t⁻¹`, but the dust is not at rest in it. -/
theorem gaugeMode {κ : ℝ} (hκ : κ ≠ 0) (hn : n ≠ 0) (F : ℝ) :
    (∀ z ∈ domain dustBackground.toData,
      familyCoeffDeriv (pullbackFamily (metric dustBackground.toData)
          (gaugeField (fun t => -3 * t ^ (-1 / 3 : ℝ)) F n)) z =
        metricPerturbation dustBackground (scalarMode n
          (fun t => 6 * F * nsq n * t ^ (-1 / 3 : ℝ))
          (fun t => 6 * F * nsq n * t ^ (-1 / 3 : ℝ) + 4 * F * t ^ (-1 : ℝ))) z ∧
      dustDensity κ (z 0) * (-2 * F * z 0 ^ (-1 : ℝ) * Real.cos (phase n z)) =
        fderiv ℝ (fun w => dustDensity κ (w 0)) z
          (gaugeField (fun t => -3 * t ^ (-1 / 3 : ℝ)) F n z) ∧
      fderiv ℝ (fun w => gaugeField (fun t => -3 * t ^ (-1 / 3 : ℝ)) F n w 0) z
          (Pi.single 0 1) = 0 ∧
      ∀ α : Fin 3, F * n α * Real.sin (phase n z) =
        -fderiv ℝ (fun w => gaugeField (fun t => -3 * t ^ (-1 / 3 : ℝ)) F n w 0) z
          (Pi.single α.succ 1)) ∧
    LinearizedEinsteinDust dustBackground κ (dustDensity κ)
      (scalarMode n (fun t => 6 * F * nsq n * t ^ (-1 / 3 : ℝ))
        (fun t => 6 * F * nsq n * t ^ (-1 / 3 : ℝ) + 4 * F * t ^ (-1 : ℝ)))
      (fun z => -2 * F * z 0 ^ (-1 : ℝ) * Real.cos (phase n z))
      fun z α => F * n α * Real.sin (phase n z) := by
  have hn' := nsq_ne_zero hn
  have eP : (fun t : ℝ => -3 * t ^ (-1 / 3 : ℝ)) =
      fun s => (-3) * s ^ (((-1 : ℤ) : ℝ) / 3) + 0 := by
    funext s; push_cast; ring_nf
  have elam : (fun t : ℝ => 6 * F * nsq n * t ^ (-1 / 3 : ℝ)) =
      fun s => (6 * F * nsq n) * s ^ (((-1 : ℤ) : ℝ) / 3) + 0 := by
    funext s; push_cast; ring_nf
  have emu : (fun t : ℝ => 6 * F * nsq n * t ^ (-1 / 3 : ℝ) + 4 * F * t ^ (-1 : ℝ)) =
      fun s => (6 * F * nsq n) * s ^ (((-1 : ℤ) : ℝ) / 3) + (4 * F) * s ^ (((-3 : ℤ) : ℝ) / 3) := by
    funext s; push_cast; ring_nf
  refine ⟨fun z hz => ⟨?_, ?_, ?_, fun α => ?_⟩, ?_⟩
  · -- the metric perturbation
    have ht : (0 : ℝ) < z 0 := time_mem_I hz
    have hP : ∀ t ∈ dustBackground.I, HasDerivAt (fun t : ℝ => -3 * t ^ (-1 / 3 : ℝ))
        (dustBackground.a t ^ 2)⁻¹ t := by
      intro t ht'
      have ht'' : (0 : ℝ) < t := ht'
      rw [eP]
      convert hasDerivAt_powThird (-3) 0 (-1) ht'' using 1
      rw [dustBackground_a ht'', rpow_div_three ht'']
      have hr := cbrt_pos ht''
      norm_num [zpow_neg]
      field_simp
    have hPs : ContDiffOn ℝ ∞ (fun t : ℝ => -3 * t ^ (-1 / 3 : ℝ)) dustBackground.I := by
      rw [eP]; exact contDiffOn_powThird _ _ _
    rw [familyCoeffDeriv_pullback_gaugeField hP hPs hn' hz]
    unfold metricPerturbation
    rw [scalarMode_congr (lam' := fun t => 6 * F * nsq n * t ^ (-1 / 3 : ℝ))
      (mu' := fun t => 6 * F * nsq n * t ^ (-1 / 3 : ℝ) + 4 * F * t ^ (-1 : ℝ))
      (by ring) ?_]
    rw [dustBackground_a ht, deriv_dustBackground_a ht,
      show (-1 : ℝ) = ((-3 : ℤ) : ℝ) / 3 by norm_num, rpow_div_three ht]
    have hr := cbrt_pos ht
    norm_num [zpow_neg]
    field_simp
    ring
  · -- the density
    have ht : (0 : ℝ) < z 0 := time_mem_I hz
    have hρ : HasDerivAt (dustDensity κ) (-(8 / (3 * κ * z 0 ^ 3))) (z 0) := by
      have hne : 3 * κ * z 0 ^ 2 ≠ 0 := by positivity
      have h := (hasDerivAt_const (z 0) (4 : ℝ)).div
        ((hasDerivAt_pow 2 (z 0)).const_mul (3 * κ)) hne
      have e : dustDensity κ = fun t => 4 / (3 * κ * t ^ 2) := rfl
      rw [e]
      convert h using 1
      field_simp
      ring
    rw [fderiv_time hρ]
    simp only [gaugeField, Fin.cons_zero, dustDensity]
    rw [show (-1 : ℝ) = ((-3 : ℤ) : ℝ) / 3 by norm_num, rpow_div_three ht]
    have hr := cbrt_pos ht
    have hc := cbrt_cube ht
    set r := z 0 ^ (1 / 3 : ℝ)
    clear_value r
    rw [← hc]
    norm_num [zpow_neg]
    field_simp
    ring
  · rw [fderiv_gaugeField_zero]
    simp
  · rw [fderiv_gaugeField_zero]
    simp only [phaseCLM_single_succ]
    ring
  · -- the linearized equations
    rw [elam, emu]
    have hv : (fun (z : E) (α : Fin 3) => F * n α * Real.sin (phase n z)) =
        fun z α => (fun _ : ℝ => F) (z 0) * n α * Real.sin (phase n z) := rfl
    rw [hv]
    refine (scalarMode_iff (isEinstein_dustBackground hκ) hn
      (contDiffOn_powThird _ _ _) (contDiffOn_powPair _ _ _ _) (fun t => -2 * F * t ^ (-1 : ℝ))
      fun _ => F).mpr fun t ht => ?_
    have ht' : 0 < t := ht
    simp only [deriv_powThird _ _ _ ht', deriv_deriv_powThird _ _ _ ht', deriv_powPair _ _ _ _ ht',
      deriv_deriv_powPair _ _ _ _ ht']
    simp only [dustBackground_a ht', deriv_dustBackground_a ht', dustDensity, rpow_div_three ht',
      add_zero]
    rw [show (-1 : ℝ) = ((-3 : ℤ) : ℝ) / 3 by norm_num, rpow_div_three ht']
    have hr := cbrt_pos ht'
    have hc := cbrt_cube ht'
    set r := t ^ (1 / 3 : ℝ)
    clear_value r
    subst hc
    push_cast
    norm_num [zpow_neg]
    refine ⟨?_, ?_, ?_, ?_⟩
    · field_simp
      ring
    · field_simp
      ring
    · field_simp
      ring
    · field_simp

/-- **The generator of a change of the spatial co-ordinates**
`x^α ↦ x^α + (c/(2n²)) n_α sin(n · x)`, which keeps the system synchronous. -/
def spatialGaugeField (c : ℝ) (n : Fin 3 → ℝ) (z : E) : E :=
  Fin.cons 0 fun γ => c / (2 * nsq n) * n γ * Real.sin (phase n z)

theorem fderiv_spatialGaugeField_zero (c : ℝ) (z v : E) :
    fderiv ℝ (fun w => spatialGaugeField c n w 0) z v = 0 := by
  simp [spatialGaugeField]

theorem fderiv_spatialGaugeField_succ (c : ℝ) (γ : Fin 3) (z v : E) :
    fderiv ℝ (fun w => spatialGaugeField c n w γ.succ) z v =
      c / (2 * nsq n) * n γ * Real.cos (phase n z) * phaseCLM n v := by
  have e : (fun w => spatialGaugeField c n w γ.succ) =
      fun w => (fun _ : ℝ => c / (2 * nsq n) * n γ) (w 0) * Real.sin (phase n w) := by
    funext w
    simp [spatialGaugeField]
  rw [e, fderiv_wave (hasDerivAt_const _ _) (Real.hasDerivAt_sin _)]
  ring

/-- **The second fictitious mode** (Landau–Lifshitz, §115): the Lie derivative of the background
along `spatialGaugeField c n` is the metric perturbation of the scalar mode `λ = μ = c`, that is
`h_{αβ} = c n_α n_β cos(n · x)/n²`. -/
theorem coordinateLieMetric_spatialGaugeField (hn : nsq n ≠ 0) (hz : z ∈ domain B.toData)
    (c : ℝ) :
    coordinateLieMetric (spatialGaugeField c n) (metric B.toData) z =
      metricPerturbation B (scalarMode n (fun _ => c) fun _ => c) z := by
  ext i j
  simp only [coordinateLieMetric, Matrix.of_apply, lieOf, Fin.sum_univ_succ (n := 3)]
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨α, rfl⟩ <;>
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨β, rfl⟩ <;>
  simp only [fderiv_coefficient_zero_left, fderiv_coefficient_zero_right,
    fderiv_coefficient_succ_succ hz, fderiv_spatialGaugeField_zero,
    fderiv_spatialGaugeField_succ] <;>
  simp only [coefficient_zero_zero, coefficient_zero_succ, coefficient_succ_zero,
    coefficient_succ_succ, phaseCLM_single_zero, phaseCLM_single_succ,
    metricPerturbation_zero_left, metricPerturbation_zero_right, metricPerturbation_succ_succ,
    ite_mul, zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Finset.sum_const_zero, add_zero, zero_add]
  simp only [spatialGaugeField, Fin.cons_zero, scalarMode, mode, scalarAmp, longitudinal, kron]
  split_ifs
  · field_simp
    ring
  · field_simp
    ring

/-- The second fictitious mode solves the linearized equations with `δ = 0` and `v = 0` on every
dust background. -/
theorem spatialGaugeMode {κ : ℝ} {ρ : ℝ → ℝ} (hB : (metric B.toData).IsEinstein κ 0
      (perfectFluidStress B.toData ρ fun _ => 0)) (hn : n ≠ 0) (c : ℝ) :
    LinearizedEinsteinDust B κ ρ (scalarMode n (fun _ => c) fun _ => c) (fun _ => 0)
      (fun _ _ => 0) := by
  have hd0 : (fun _ : E => (0 : ℝ)) =
      fun z => (fun _ : ℝ => (0 : ℝ)) (z 0) * Real.cos (phase n z) := by
    funext z; simp
  have hv0 : (fun (_ : E) (_ : Fin 3) => (0 : ℝ)) =
      fun z α => (fun _ : ℝ => (0 : ℝ)) (z 0) * n α * Real.sin (phase n z) := by
    funext z α; simp
  rw [hd0, hv0]
  refine (scalarMode_iff (lam := fun _ => c) (mu := fun _ => c) hB hn contDiffOn_const
    contDiffOn_const (fun _ => 0) fun _ => 0).mpr fun t _ => ?_
  simp

end Gauge

/-! ### Tensor and vector perturbations -/

section TensorVector

variable {κ : ℝ} {ρ : ℝ → ℝ} {n : Fin 3 → ℝ} {τ : ℝ → ℝ}

/-- The amplitude `τ(t) e_{αβ}` of a plane wave with a constant polarization `e`. -/
def prodAmp (τ : ℝ → ℝ) (e : Fin 3 → Fin 3 → ℝ) (t : ℝ) (α β : Fin 3) : ℝ := τ t * e α β

theorem isAmplitude_prodAmp (hτ : ContDiffOn ℝ ∞ τ B.I) {e : Fin 3 → Fin 3 → ℝ}
    (he : ∀ α β, e α β = e β α) : IsAmplitude B (prodAmp τ e) where
  smooth _ _ := hτ.mul contDiffOn_const
  symm t α β := by simp only [prodAmp, he α β]

theorem Fd_prodAmp (hτ : ContDiffOn ℝ ∞ τ B.I) (e : Fin 3 → Fin 3 → ℝ) {t : ℝ} (ht : t ∈ B.I)
    (α β : Fin 3) : Fd (prodAmp τ e) t α β = deriv τ t * e α β :=
  ((hasDerivAt_of_contDiffOn B.isOpen_I hτ ht).mul_const _).deriv

theorem Fdd_prodAmp (hτ : ContDiffOn ℝ ∞ τ B.I) (e : Fin 3 → Fin 3 → ℝ) {t : ℝ} (ht : t ∈ B.I)
    (α β : Fin 3) : Fdd (prodAmp τ e) t α β = deriv (deriv τ) t * e α β := by
  have hev : (deriv fun s => prodAmp τ e s α β) =ᶠ[𝓝 t] fun s => deriv τ s * e α β :=
    eventually_of_mem (B.isOpen_I.mem_nhds ht) fun s hs => Fd_prodAmp hτ e hs α β
  unfold Fdd
  rw [hev.deriv_eq]
  exact ((hasDerivAt_of_contDiffOn B.isOpen_I
    (contDiffOn_deriv_of_contDiffOn B.isOpen_I hτ) ht).mul_const _).deriv

/-- For a nonzero tensor `e`, `X e_{αβ} = 0` for all `α, β` if and only if `X = 0`. -/
theorem forall_mul_eq_zero_iff {e : Fin 3 → Fin 3 → ℝ} (he : e ≠ 0) (X : ℝ) :
    (∀ α β, X * e α β = 0) ↔ X = 0 := by
  refine ⟨fun h => ?_, fun h α β => by rw [h, zero_mul]⟩
  obtain ⟨α, hα⟩ := Function.ne_iff.mp he
  obtain ⟨β, hβ⟩ := Function.ne_iff.mp hα
  exact (mul_eq_zero.mp (h α β)).resolve_right (by simpa using hβ)

/-- **A polarization of a tensor mode**: symmetric, traceless and transverse to `n`. -/
structure IsTensorPolarization (n : Fin 3 → ℝ) (e : Fin 3 → Fin 3 → ℝ) : Prop where
  /-- The polarization is symmetric. -/
  symm : ∀ α β, e α β = e β α
  /-- The polarization is traceless. -/
  traceless : ∑ γ, e γ γ = 0
  /-- The polarization is transverse. -/
  transverse : ∀ β, ∑ γ, n γ * e γ β = 0

/-- The `+` polarization `diag(1, −1, 0)` of a wave along the third axis. -/
def plusPolarization : Fin 3 → Fin 3 → ℝ := !![1, 0, 0; 0, -1, 0; 0, 0, 0]

theorem isTensorPolarization_plus : IsTensorPolarization ![0, 0, 1] plusPolarization where
  symm α β := by fin_cases α <;> fin_cases β <;> rfl
  traceless := by simp [plusPolarization, Fin.sum_univ_three]
  transverse β := by fin_cases β <;> simp [plusPolarization, Fin.sum_univ_three]

theorem plusPolarization_ne_zero : plusPolarization ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [plusPolarization] at this

/-- **The tensor mode** `h_{αβ} = τ(t) e_{αβ} cos(n · x)`, a gravitational wave. -/
def tensorMode (n : Fin 3 → ℝ) (e : Fin 3 → Fin 3 → ℝ) (τ : ℝ → ℝ) :
    E → Fin 3 → Fin 3 → ℝ :=
  mode (prodAmp τ e) Real.cos n

/-- **The tensor perturbations are gravitational waves** (Landau–Lifshitz, §115). On a flat
background that solves the Einstein equations with dust, for `n ≠ 0` and a nonzero symmetric,
traceless and transverse polarization `e`, the tensor mode `h_{αβ} = τ(t) e_{αβ} cos(n · x)`
without density contrast and velocity solves the linearized Einstein equations if and only if
`τ̈ + 3(ȧ/a) τ̇ + (n²/a²) τ = 0` on `I`. -/
theorem tensorMode_iff (hB : (metric B.toData).IsEinstein κ 0
      (perfectFluidStress B.toData ρ fun _ => 0)) (hn : n ≠ 0) {e : Fin 3 → Fin 3 → ℝ}
    (he : IsTensorPolarization n e) (he0 : e ≠ 0) (hτ : ContDiffOn ℝ ∞ τ B.I) :
    LinearizedEinsteinDust B κ ρ (tensorMode n e τ) (fun _ => 0) (fun _ _ => 0) ↔
      ∀ t ∈ B.I, deriv (deriv τ) t + 3 * (deriv B.a t / B.a t) * deriv τ t +
        nsq n / B.a t ^ 2 * τ t = 0 := by
  have hn' := nsq_ne_zero hn
  have hd0 : (fun _ : E => (0 : ℝ)) =
      fun z => (fun _ : ℝ => (0 : ℝ)) (z 0) * Real.cos (phase n z) := by
    funext z; simp
  have hv0 : (fun (_ : E) (_ : Fin 3) => (0 : ℝ)) =
      fun z α =>
        (fun (_ : ℝ) (_ : Fin 3) => (0 : ℝ)) (z 0) α * (fun s => -Real.sin s) (phase n z) := by
    funext z α; simp
  rw [hd0, hv0, tensorMode]
  refine (mode_iff (isAmplitude_prodAmp hτ he.symm) isProfile_cos hn' ⟨0, by simp⟩
    ⟨Real.pi / 2, by simp⟩ (fun _ => 0) fun _ _ => 0).trans (forall₂_congr fun t ht => ?_)
  have ha := (B.a_pos t ht).ne'
  obtain ⟨e1, e2⟩ := dust_background hB ht
  have hbg : 2 * deriv B.a t ^ 2 + B.a t * deriv (deriv B.a) t = κ * ρ t * B.a t ^ 2 / 2 := by
    rw [e1, e2]; ring
  have hdiag (f : ℝ) : ∑ γ, f * e γ γ = 0 := by rw [← Finset.mul_sum, he.traceless, mul_zero]
  have htr (f : ℝ) (β : Fin 3) : ∑ γ, n γ * (f * e γ β) = 0 := by
    calc ∑ γ, n γ * (f * e γ β) = f * ∑ γ, n γ * e γ β := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun γ _ => by ring
      _ = 0 := by rw [he.transverse β, mul_zero]
  unfold modeTime modeMixed modeSpace
  simp only [Fd_prodAmp hτ e ht, Fdd_prodAmp hτ e ht, prodAmp, hdiag, htr, mul_zero, zero_div,
    neg_zero, sub_zero, add_zero, ite_self, zero_add, sub_self, true_and, forall_const]
  have hS : ∀ α β, (nsq n * (τ t * e α β)) / 2 +
      (2 * deriv B.a t ^ 2 + B.a t * deriv (deriv B.a) t) * (τ t * e α β) +
      3 / 2 * (B.a t * deriv B.a t) * (deriv τ t * e α β) +
      B.a t ^ 2 / 2 * (deriv (deriv τ) t * e α β) - κ * (ρ t * B.a t ^ 2 * (τ t * e α β) / 2) =
      B.a t ^ 2 / 2 * (deriv (deriv τ) t + 3 * (deriv B.a t / B.a t) * deriv τ t +
        nsq n / B.a t ^ 2 * τ t) * e α β := fun α β => by
    rw [hbg]; field_simp; ring
  have ha2 : B.a t ^ 2 / 2 ≠ 0 := by positivity
  constructor
  · intro h
    have h' : ∀ α β, B.a t ^ 2 / 2 * (deriv (deriv τ) t + 3 * (deriv B.a t / B.a t) * deriv τ t +
        nsq n / B.a t ^ 2 * τ t) * e α β = 0 := fun α β => by rw [← hS α β, h α β, sub_self]
    exact (mul_eq_zero.mp ((forall_mul_eq_zero_iff he0 _).mp h')).resolve_left ha2
  · intro hE α β
    have := hS α β
    rw [hE, mul_zero, zero_mul] at this
    exact sub_eq_zero.mp this

/-- The amplitude `n_α e_β + n_β e_α` of a vector mode. -/
def vectorAmp (n e : Fin 3 → ℝ) (α β : Fin 3) : ℝ := n α * e β + n β * e α

theorem vectorAmp_ne_zero {e : Fin 3 → ℝ} (hn : nsq n ≠ 0) (he0 : e ≠ 0)
    (he : ∑ γ, n γ * e γ = 0) : vectorAmp n e ≠ 0 := by
  intro h
  have hs : ∑ α, ∑ β, vectorAmp n e α β * (n α * e β) = 0 := by simp [h]
  have e1 : ∑ α, ∑ β, vectorAmp n e α β * (n α * e β) =
      (∑ α, n α ^ 2) * (∑ β, e β ^ 2) + (∑ α, n α * e α) * (∑ β, n β * e β) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun α _ => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun β _ => by unfold vectorAmp; ring
  rw [e1, he, mul_zero, add_zero] at hs
  exact mul_ne_zero hn (nsq_ne_zero (n := e) he0) hs

/-- **The vector mode** `h_{αβ} = σ(t) (n_α e_β + n_β e_α) sin(n · x)` with `e · n = 0`. -/
def vectorMode (n e : Fin 3 → ℝ) (σ : ℝ → ℝ) : E → Fin 3 → Fin 3 → ℝ :=
  mode (prodAmp σ (vectorAmp n e)) Real.sin n

/-- **The vector perturbations** (Landau–Lifshitz, §115). On a flat background that solves the
Einstein equations with dust, for `n ≠ 0` and `e ≠ 0` with `e · n = 0`, the vector mode
`h_{αβ} = σ(t) (n_α e_β + n_β e_α) sin(n · x)` without density contrast and with the velocity
`v_α = w(t) e_α cos(n · x)` solves the linearized Einstein equations if and only if on `I`
`σ̈ + 3(ȧ/a) σ̇ = 0` and `n² σ̇ = −2κρw`. -/
theorem vectorMode_iff (hB : (metric B.toData).IsEinstein κ 0
      (perfectFluidStress B.toData ρ fun _ => 0)) (hn : n ≠ 0) {e : Fin 3 → ℝ}
    (he : ∑ γ, n γ * e γ = 0) (he0 : e ≠ 0) {σ : ℝ → ℝ} (hσ : ContDiffOn ℝ ∞ σ B.I)
    (w : ℝ → ℝ) :
    LinearizedEinsteinDust B κ ρ (vectorMode n e σ) (fun _ => 0)
        (fun z α => w (z 0) * e α * Real.cos (phase n z)) ↔
      ∀ t ∈ B.I, deriv (deriv σ) t + 3 * (deriv B.a t / B.a t) * deriv σ t = 0 ∧
        nsq n * deriv σ t = -(2 * κ * ρ t * w t) := by
  have hn' := nsq_ne_zero hn
  have hd0 : (fun _ : E => (0 : ℝ)) =
      fun z => (fun _ : ℝ => (0 : ℝ)) (z 0) * Real.sin (phase n z) := by
    funext z; simp
  have hv : (fun (z : E) (α : Fin 3) => w (z 0) * e α * Real.cos (phase n z)) =
      fun z α => (fun t α => w t * e α) (z 0) α * Real.cos (phase n z) := rfl
  have hsym : ∀ α β, vectorAmp n e α β = vectorAmp n e β α := fun α β => by
    unfold vectorAmp; ring
  rw [hd0, hv, vectorMode]
  refine (mode_iff (isAmplitude_prodAmp hσ hsym) isProfile_sin hn' ⟨Real.pi / 2, by simp⟩
    ⟨0, by simp⟩ (fun _ => 0) fun t α => w t * e α).trans (forall₂_congr fun t ht => ?_)
  have ha := (B.a_pos t ht).ne'
  obtain ⟨e1, e2⟩ := dust_background hB ht
  have hbg : 2 * deriv B.a t ^ 2 + B.a t * deriv (deriv B.a) t = κ * ρ t * B.a t ^ 2 / 2 := by
    rw [e1, e2]; ring
  have hdiag (f : ℝ) : ∑ γ, f * vectorAmp n e γ γ = 0 := by
    calc ∑ γ, f * vectorAmp n e γ γ = 2 * f * ∑ γ, n γ * e γ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun γ _ => by unfold vectorAmp; ring
      _ = 0 := by rw [he, mul_zero]
  have htr (f : ℝ) (β : Fin 3) : ∑ γ, n γ * (f * vectorAmp n e γ β) = f * nsq n * e β := by
    calc ∑ γ, n γ * (f * vectorAmp n e γ β) =
        f * (nsq n * e β) + f * n β * ∑ γ, n γ * e γ := by
          rw [Finset.mul_sum, nsq, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun γ _ => by unfold vectorAmp; ring
      _ = f * nsq n * e β := by rw [he]; ring
  unfold modeTime modeMixed modeSpace
  simp only [Fd_prodAmp hσ _ ht, Fdd_prodAmp hσ _ ht, prodAmp, hdiag, htr, mul_zero, zero_div,
    neg_zero, sub_zero, add_zero, ite_self, zero_add, sub_self, true_and]
  have hS : ∀ α β, (nsq n * (σ t * vectorAmp n e α β) - n α * (σ t * nsq n * e β) -
        n β * (σ t * nsq n * e α)) / 2 +
      (2 * deriv B.a t ^ 2 + B.a t * deriv (deriv B.a) t) * (σ t * vectorAmp n e α β) +
      3 / 2 * (B.a t * deriv B.a t) * (deriv σ t * vectorAmp n e α β) +
      B.a t ^ 2 / 2 * (deriv (deriv σ) t * vectorAmp n e α β) -
        κ * (ρ t * B.a t ^ 2 * (σ t * vectorAmp n e α β) / 2) =
      B.a t ^ 2 / 2 * (deriv (deriv σ) t + 3 * (deriv B.a t / B.a t) * deriv σ t) *
        vectorAmp n e α β := fun α β => by
    rw [hbg]; unfold vectorAmp; field_simp; ring
  have ha2 : B.a t ^ 2 / 2 ≠ 0 := by positivity
  obtain ⟨α₀, hα₀⟩ := Function.ne_iff.mp he0
  replace hα₀ : e α₀ ≠ 0 := by simpa using hα₀
  have hM : (∀ α, deriv σ t * nsq n * e α / 2 = κ * -(ρ t * (w t * e α))) ↔
      nsq n * deriv σ t = -(2 * κ * ρ t * w t) := by
    constructor
    · intro h
      have h1 := mul_right_cancel₀ hα₀
        (show deriv σ t * nsq n / 2 * e α₀ = -(κ * ρ t * w t) * e α₀ by
          linear_combination h α₀)
      linear_combination 2 * h1
    · intro h α
      linear_combination e α / 2 * h
  have hSp : (∀ α β,
      (nsq n * (σ t * vectorAmp n e α β) - n α * (σ t * nsq n * e β) -
          n β * (σ t * nsq n * e α)) / 2 +
        (2 * deriv B.a t ^ 2 + B.a t * deriv (deriv B.a) t) * (σ t * vectorAmp n e α β) +
        3 / 2 * (B.a t * deriv B.a t) * (deriv σ t * vectorAmp n e α β) +
        B.a t ^ 2 / 2 * (deriv (deriv σ) t * vectorAmp n e α β) =
      κ * (ρ t * B.a t ^ 2 * (σ t * vectorAmp n e α β) / 2)) ↔
      deriv (deriv σ) t + 3 * (deriv B.a t / B.a t) * deriv σ t = 0 := by
    constructor
    · intro h
      have h' : ∀ α β, B.a t ^ 2 / 2 * (deriv (deriv σ) t + 3 * (deriv B.a t / B.a t) *
          deriv σ t) * vectorAmp n e α β = 0 := fun α β => by rw [← hS α β, h α β, sub_self]
      exact (mul_eq_zero.mp ((forall_mul_eq_zero_iff (vectorAmp_ne_zero hn' he0 he) _).mp
        h')).resolve_left ha2
    · intro hE α β
      have := hS α β
      rw [hE, mul_zero, zero_mul] at this
      exact sub_eq_zero.mp this
  rw [hM, hSp, and_comm]

/-- **The vector perturbations decay** (Landau–Lifshitz, §115). Under the hypotheses of
`vectorMode_iff`, on a preconnected set of times, `a³ σ̇` is a constant `C`: `σ̇ = C/a³`, and the
covariant velocity of the dust is `κρ w = −n² C/(2a³)`. For dust `ρa³` is constant, so `w` is
constant and the velocity `w/a` measured by the comoving observers decays like `1/a`; the constant
part of `σ` is a change of the spatial co-ordinates. -/
theorem vectorMode_decay (hB : (metric B.toData).IsEinstein κ 0
      (perfectFluidStress B.toData ρ fun _ => 0)) (hI : IsPreconnected B.I) (hn : n ≠ 0)
    {e : Fin 3 → ℝ} (he : ∑ γ, n γ * e γ = 0) (he0 : e ≠ 0) {σ : ℝ → ℝ}
    (hσ : ContDiffOn ℝ ∞ σ B.I) (w : ℝ → ℝ)
    (hL : LinearizedEinsteinDust B κ ρ (vectorMode n e σ) (fun _ => 0)
      (fun z α => w (z 0) * e α * Real.cos (phase n z))) :
    ∃ C, ∀ t ∈ B.I, deriv σ t = C / B.a t ^ 3 ∧
      κ * ρ t * w t = -(nsq n * C) / (2 * B.a t ^ 3) := by
  have hODE := (vectorMode_iff hB hn he he0 hσ w).mp hL
  have hdσ : ContDiffOn ℝ ∞ (deriv σ) B.I := contDiffOn_deriv_of_contDiffOn B.isOpen_I hσ
  have hf : ∀ t ∈ B.I, HasDerivAt (fun s => B.a s ^ 3 * deriv σ s)
      (3 * B.a t ^ 2 * deriv B.a t * deriv σ t + B.a t ^ 3 * deriv (deriv σ) t) t := by
    intro t ht
    have h1 := ((hasDerivAt_a' ht).pow 3).fun_mul (hasDerivAt_of_contDiffOn B.isOpen_I hdσ ht)
    convert h1 using 1
  obtain ⟨C, hC⟩ := B.isOpen_I.exists_is_const_of_deriv_eq_zero hI
    (fun t ht => (hf t ht).differentiableAt.differentiableWithinAt) fun t ht => by
      have ha := (B.a_pos t ht).ne'
      rw [(hf t ht).deriv, Pi.zero_apply]
      have h0 := (hODE t ht).1
      field_simp at h0
      linear_combination B.a t ^ 2 * h0
  refine ⟨C, fun t ht => ?_⟩
  have ha := (B.a_pos t ht).ne'
  have hσ' : deriv σ t = C / B.a t ^ 3 := by
    rw [← hC t ht]
    field_simp
  refine ⟨hσ', ?_⟩
  have h2 := (hODE t ht).2
  rw [hσ'] at h2
  calc κ * ρ t * w t = -(nsq n * (C / B.a t ^ 3)) / 2 := by linarith
    _ = -(nsq n * C) / (2 * B.a t ^ 3) := by field_simp

/-- **A decaying vector mode on the flat dust universe**: `σ = −c/t` and the constant velocity
amplitude `w = −3n²c/8` solve the linearized Einstein equations, with `σ̇ = c/t² = c/a³`. -/
theorem vectorMode_dust (hκ : κ ≠ 0) (hn : n ≠ 0) {e : Fin 3 → ℝ} (he : ∑ γ, n γ * e γ = 0)
    (he0 : e ≠ 0) (c : ℝ) :
    LinearizedEinsteinDust dustBackground κ (dustDensity κ)
      (vectorMode n e fun t => -c * t ^ (-1 : ℝ)) (fun _ => 0)
      (fun z α => -(3 * nsq n * c / 8) * e α * Real.cos (phase n z)) := by
  have eσ : (fun t : ℝ => -c * t ^ (-1 : ℝ)) = fun s => (-c) * s ^ (((-3 : ℤ) : ℝ) / 3) + 0 := by
    funext s; push_cast; norm_num
  rw [eσ]
  refine (vectorMode_iff (isEinstein_dustBackground hκ) hn he he0 (contDiffOn_powThird _ _ _)
    fun _ => -(3 * nsq n * c / 8)).mpr fun t ht => ?_
  have ht' : 0 < t := ht
  simp only [deriv_powThird _ _ _ ht', deriv_deriv_powThird _ _ _ ht']
  simp only [dustBackground_a ht', deriv_dustBackground_a ht', dustDensity]
  have hr := cbrt_pos ht'
  have hc := cbrt_cube ht'
  set r := t ^ (1 / 3 : ℝ)
  clear_value r
  subst hc
  push_cast
  norm_num [zpow_neg]
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- The axis `n = (0, 0, 1)` and `e = (1, 0, 0)` satisfy the hypotheses of the vector modes. -/
theorem vectorMode_axis :
    (![0, 0, 1] : Fin 3 → ℝ) ≠ 0 ∧ (![1, 0, 0] : Fin 3 → ℝ) ≠ 0 ∧
      ∑ γ, (![0, 0, 1] : Fin 3 → ℝ) γ * (![1, 0, 0] : Fin 3 → ℝ) γ = 0 := by
  refine ⟨fun h => ?_, fun h => ?_, by simp [Fin.sum_univ_three]⟩
  · simpa using congrFun h 2
  · simpa using congrFun h 0

end TensorVector

end ProjectAinos.GeneralRelativity.CosmologicalPerturbation
