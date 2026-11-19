/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.FLRW
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The flat anisotropic model

Landau–Lifshitz, §117, in the co-ordinates `(t, x¹, x², x³) = (x 0, x 1, x 2, x 3)`, the
signature `(−+++)` and `c = 1`. The data (`Data`) are an open set `I` of times and three scale
factors `a_α` smooth and positive on `I`; the metric is
`ds² = −dt² + a₁(t)² (dx¹)² + a₂(t)² (dx²)² + a₃(t)² (dx³)²` on `t ∈ I` (`metric`). It is
synchronous (`isSynchronous`). Write `H_α = ȧ_α/a_α` (`hubble`), `θ = Σ_α H_α` (`expansion`)
and `ä_α/a_α` (`accel`).

* `christoffelOf_eq`, `christoffelOf_zero_succ_succ`, `christoffelOf_succ_zero_succ`, …: the
  Christoffel symbols are `Γ⁰_{αα} = a_α ȧ_α`, `Γ^α_{0α} = Γ^α_{α0} = ȧ_α/a_α`, all others zero.
* `ricciOf_eq`, `ricci_zero_zero`, `ricci_zero_succ`, `ricci_succ_zero`, `ricci_succ_succ`:
  `R₀₀ = −Σ_α ä_α/a_α`, `R₀α = 0` and `R_{αβ} = (a_α ä_α + a_α ȧ_α (θ − H_α)) δ_{αβ}`;
  `scalarOf_eq`: `R = 2 Σ_α ä_α/a_α + 2(H₁H₂ + H₁H₃ + H₂H₃)`.
* `einsteinOf_eq`, `einstein_zero_zero`, …, `einstein_succ_succ`: `G₀₀ = H₁H₂ + H₁H₃ + H₂H₃`
  (`hubblePairs`), `G₀α = 0` and `G_{αα} = −a_α² (ä_β/a_β + ä_γ/a_γ + H_β H_γ)` for `{β, γ}`
  the other two indices (`spatialFactor`), the off-diagonal components zero.
* `isEinstein_iff`: with the comoving perfect fluid `T = diag(ρ, p a₁², p a₂², p a₃²)`
  (`perfectFluidStress`, `perfectFluidStress_eq`), the Einstein equations
  `G_{ik} + Λ g_{ik} = κ T_{ik}` hold on the domain if and only if on `I` the constraint
  `H₁H₂ + H₁H₃ + H₂H₃ = κρ + Λ` (`Constraint`) and the three evolution equations
  `ä_β/a_β + ä_γ/a_γ + H_β H_γ = −κp + Λ` (`Evolution`) hold.
* `kasner`, `ricciOf_kasner_eq_zero_iff`: the Kasner metric `a_α = t^{p_α}` on `t > 0` has
  `R₀₀ = −(Σp² − Σp)/t²` and `R_{αα} = p_α t^{2p_α−2}(Σp − 1)`, so it is Ricci flat if and only
  if `Σp = Σp² = 1` (Landau–Lifshitz, (117.3)) or `p = 0`; `isEinstein_kasner` (the vacuum
  equations) and `volume_kasner` (`a₁a₂a₃ = t` under `Σp = 1`).
* `kasner_exponent_ne`, `chartCurvature_kasner_ne_zero`: unless `p` is a permutation of
  `(1, 0, 0)`, no exponent of a solution is `0` or `1`, and the curvature component
  `R^α_{0α0} = p_α(p_α − 1)/t²` (`chartCurvature_kasner`) vanishes nowhere: the space is curved.
* The Lifshitz–Khalatnikov parametrisation (117.5)–(117.6): `kasnerExponents u` solves the
  conditions for every real `u` (`sum_kasnerExponents`, `sum_sq_kasnerExponents`), is ordered for
  `u ≥ 1` (`kasnerExponents_mono`), and `u ↦ 1/u` swaps the last two exponents
  (`kasnerExponents_inv`); every ordered solution satisfies
  `−1/3 ≤ p₁ ≤ 0 ≤ p₂ ≤ 2/3 ≤ p₃ ≤ 1` (`kasner_ranges`) and is `(0, 0, 1)` or
  `kasnerExponents u` with `u = p₃/p₂ ≥ 1` (`eq_kasnerExponents`).
* The declared matter model, dust: for `Σp = Σp² = 1`, `t₀ ≥ 0` and `κ ≠ 0`, the scale factors
  `a_α = t^{p_α} (t + t₀)^{2/3 − p_α}` (`dustKasner`) solve the equations with `p = 0` and
  `ρ = 4/(3κ t (t + t₀))` (`isEinstein_dustKasner`, `dustDensity`), positive for `κ > 0`
  (`dustDensity_pos`); for `t₀ > 0`, `a_α/t^{p_α} → t₀^{2/3 − p_α}` as `t → 0⁺`
  (`tendsto_dustKasner_nhdsGT`: Kasner near the singularity), and `a_α/t^{2/3} → 1` as `t → ∞`
  (`tendsto_dustKasner_atTop`: isotropization).
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap Set TopologicalSpace Filter
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.Kasner

open SmoothGeometry CoordinateMetric

local notation "E" => MinkowskiModel 3

/-! ### The data -/

/-- **The data of the flat anisotropic model** (Landau–Lifshitz, §117): an open set `I` of
times and three scale factors `a_α`, smooth and positive on `I`. -/
structure Data where
  /-- The open set of times. -/
  I : Set ℝ
  /-- The scale factors `a_α(t)`, with `g_{αα} = a_α²`. -/
  a : Fin 3 → ℝ → ℝ
  /-- The set of times is open. -/
  isOpen_I : IsOpen I
  /-- The scale factors are smooth on `I`. -/
  contDiffOn_a : ∀ α, ContDiffOn ℝ ∞ (a α) I
  /-- The scale factors are positive on `I`. -/
  a_pos : ∀ α, ∀ t ∈ I, 0 < a α t

variable {D : Data} {x : E}

/-- `t ↦ a_α(t)` has the derivative `ȧ_α` on `I`. -/
theorem hasDerivAt_a (α : Fin 3) {t : ℝ} (ht : t ∈ D.I) :
    HasDerivAt (D.a α) (deriv (D.a α) t) t :=
  FLRW.hasDerivAt_of_contDiffOn D.isOpen_I (D.contDiffOn_a α) ht

/-- `t ↦ ȧ_α(t)` has the derivative `ä_α` on `I`. -/
theorem hasDerivAt_deriv_a (α : Fin 3) {t : ℝ} (ht : t ∈ D.I) :
    HasDerivAt (deriv (D.a α)) (deriv (deriv (D.a α)) t) t :=
  FLRW.hasDerivAt_of_contDiffOn D.isOpen_I
    (FLRW.contDiffOn_deriv_of_contDiffOn D.isOpen_I (D.contDiffOn_a α)) ht

variable (D) in
/-- The domain `t ∈ I` of the co-ordinates `(t, x¹, x², x³)`. -/
def domain : Opens E :=
  ⟨{x | x 0 ∈ D.I}, D.isOpen_I.preimage (continuous_apply 0)⟩

/-- The time of a point of the domain lies in `I`. -/
theorem time_mem (hx : x ∈ domain D) : x 0 ∈ D.I := hx

/-- The scale factors are positive on the domain. -/
theorem a_pos_of_mem (hx : x ∈ domain D) (α : Fin 3) : 0 < D.a α (x 0) := D.a_pos α _ hx

/-- The point `(t, 0, 0, 0)` lies in the domain for every `t ∈ I`. -/
theorem timeAxis_mem {t : ℝ} (ht : t ∈ D.I) : FLRW.timeAxis t ∈ domain D := by
  simpa [domain] using ht

/-! ### The metric -/

variable (D) in
/-- The diagonal coefficients `(−1, a₁², a₂², a₃²)`. -/
def coefficients (x : E) : Fin 4 → ℝ :=
  ![-1, D.a 0 (x 0) ^ 2, D.a 1 (x 0) ^ 2, D.a 2 (x 0) ^ 2]

/-- The spatial coefficient `g_{α+1, α+1} = a_α²`. -/
theorem coefficients_succ (y : E) (α : Fin 3) : coefficients D y α.succ = D.a α (y 0) ^ 2 := by
  fin_cases α <;> rfl

/-- A smooth function of the time is smooth on the domain. -/
theorem contDiffOn_time {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f D.I) :
    ContDiffOn ℝ ∞ (fun z : E => f (z 0)) (domain D) :=
  hf.comp (contDiff_apply ℝ (fun _ => ℝ) 0).contDiffOn fun _ hz => time_mem hz

/-- The coefficients are smooth on the domain. -/
theorem contDiffOn_coefficients (i : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => coefficients D x i) (domain D) := by
  fin_cases i
  · exact contDiffOn_const
  · exact (contDiffOn_time (D.contDiffOn_a 0)).pow 2
  · exact (contDiffOn_time (D.contDiffOn_a 1)).pow 2
  · exact (contDiffOn_time (D.contDiffOn_a 2)).pow 2

variable (D) in
/-- **The flat anisotropic metric** `ds² = −dt² + a₁(t)² (dx¹)² + a₂(t)² (dx²)² + a₃(t)² (dx³)²`
on the domain (Landau–Lifshitz, (117.1) with general scale factors). -/
def metric : CoordinateMetric .timeNegative 3 (domain D) :=
  ofDiagonal (coefficients D) contDiffOn_coefficients
    (fun x _ => by
      simp only [coefficients, LorentzConvention.timeSign_timeNegative, Matrix.cons_val_zero]
      norm_num)
    (fun x hx α => by
      rw [coefficients_succ, LorentzConvention.timeSign_timeNegative]
      have := pow_pos (a_pos_of_mem hx α) 2
      linarith)

/-- The matrix of coefficients of the metric is `diag(−1, a₁², a₂², a₃²)`. -/
theorem coefficient_metric (y : E) :
    (metric D).coefficient y = Matrix.diagonal (coefficients D y) :=
  coefficient_ofDiagonal _ _ _ _ y

/-- No coefficient vanishes on the domain. -/
theorem coefficients_ne_zero (hx : x ∈ domain D) (i : Fin 4) : coefficients D x i ≠ 0 := by
  have h0 := (a_pos_of_mem hx 0).ne'
  have h1 := (a_pos_of_mem hx 1).ne'
  have h2 := (a_pos_of_mem hx 2).ne'
  fin_cases i <;> simp [coefficients, h0, h1, h2]

/-- **The metric is synchronous** (Landau–Lifshitz, §97): `g₀₀ = −1` and `g₀α = 0`. -/
theorem isSynchronous : (metric D).IsSynchronous := by
  intro z _
  refine ⟨?_, fun α => ?_⟩
  · simp [coefficient_metric, coefficients]
  · simp [coefficient_metric, Matrix.diagonal_apply_ne _ (Fin.succ_ne_zero α).symm]

/-! ### Derivatives of the coefficients -/

/-- The derivative of `g_{αα} = a_α²` along `v` is `2 a_α ȧ_α v⁰`. -/
theorem fderiv_scale_sq (hx : x ∈ domain D) (α : Fin 3) (v : E) :
    fderiv ℝ (fun z : E => D.a α (z 0) ^ 2) x v =
      2 * D.a α (x 0) * deriv (D.a α) (x 0) * v 0 := by
  rw [((FLRW.hasFDerivAt_time (hasDerivAt_a α (time_mem hx))).pow 2).fderiv]
  simp only [smul_apply, proj_apply, smul_eq_mul]
  push_cast
  ring

/-- The derivatives of the four coefficients along a vector `v`. -/
theorem fderiv_coefficients (hx : x ∈ domain D) (i : Fin 4) (v : E) :
    fderiv ℝ (fun z => coefficients D z i) x v =
      ![0, 2 * D.a 0 (x 0) * deriv (D.a 0) (x 0) * v 0,
        2 * D.a 1 (x 0) * deriv (D.a 1) (x 0) * v 0,
        2 * D.a 2 (x 0) * deriv (D.a 2) (x 0) * v 0] i := by
  fin_cases i
  · simp [coefficients]
  · exact fderiv_scale_sq hx 0 v
  · exact fderiv_scale_sq hx 1 v
  · exact fderiv_scale_sq hx 2 v

/-! ### The Christoffel symbols -/

variable (D) in
/-- `Γ⁰_{αα} = a_α ȧ_α`. -/
def gammaSpatial (α : Fin 3) (x : E) : ℝ := D.a α (x 0) * deriv (D.a α) (x 0)

variable (D) in
/-- `Γ^α_{0α} = Γ^α_{α0} = ȧ_α/a_α`, the Hubble rate of the axis `α`. -/
def gammaExpansion (α : Fin 3) (x : E) : ℝ := deriv (D.a α) (x 0) / D.a α (x 0)

variable (D) in
/-- **The Christoffel symbols of the anisotropic metric**: the table `Γ^k_{ij}`, indexed
`christoffel D x k i j`, with `Γ⁰_{αα} = a_α ȧ_α`, `Γ^α_{0α} = Γ^α_{α0} = ȧ_α/a_α` and all
other symbols zero. -/
def christoffel (x : E) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![![![0, 0, 0, 0], ![0, gammaSpatial D 0 x, 0, 0], ![0, 0, gammaSpatial D 1 x, 0],
      ![0, 0, 0, gammaSpatial D 2 x]],
    ![![0, gammaExpansion D 0 x, 0, 0], ![gammaExpansion D 0 x, 0, 0, 0], ![0, 0, 0, 0],
      ![0, 0, 0, 0]],
    ![![0, 0, gammaExpansion D 1 x, 0], ![0, 0, 0, 0], ![gammaExpansion D 1 x, 0, 0, 0],
      ![0, 0, 0, 0]],
    ![![0, 0, 0, gammaExpansion D 2 x], ![0, 0, 0, 0], ![0, 0, 0, 0],
      ![gammaExpansion D 2 x, 0, 0, 0]]]

/-- The table is symmetric in the lower indices. -/
theorem christoffel_symm (y : E) (k i j : Fin 4) :
    christoffel D y k i j = christoffel D y k j i := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;> rfl

/-- **The table is the table of Christoffel symbols** of the metric on its domain. -/
theorem christoffelOf_eq (hx : x ∈ domain D) (k i j : Fin 4) :
    christoffelOf (metric D).coefficient x k i j = christoffel D x k i j := by
  have h0 := (a_pos_of_mem hx 0).ne'
  have h1 := (a_pos_of_mem hx 1).ne'
  have h2 := (a_pos_of_mem hx 2).ne'
  rw [metric, christoffelOf_ofDiagonal _ _ _ _ x (coefficients_ne_zero hx)]
  simp only [fderiv_coefficients hx]
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [christoffel, gammaSpatial, gammaExpansion, coefficients] <;>
    field_simp

/-- `Γ⁰_{αβ} = a_α ȧ_α δ_{αβ}`. -/
theorem christoffelOf_zero_succ_succ (hx : x ∈ domain D) (α β : Fin 3) :
    christoffelOf (metric D).coefficient x 0 α.succ β.succ =
      if α = β then D.a α (x 0) * deriv (D.a α) (x 0) else 0 := by
  rw [christoffelOf_eq hx]
  fin_cases α <;> fin_cases β <;> rfl

/-- `Γ^α_{0β} = (ȧ_α/a_α) δ_{αβ}`. -/
theorem christoffelOf_succ_zero_succ (hx : x ∈ domain D) (α β : Fin 3) :
    christoffelOf (metric D).coefficient x α.succ 0 β.succ =
      if α = β then deriv (D.a α) (x 0) / D.a α (x 0) else 0 := by
  rw [christoffelOf_eq hx]
  fin_cases α <;> fin_cases β <;> rfl

/-- `Γ^α_{β0} = (ȧ_α/a_α) δ_{αβ}`. -/
theorem christoffelOf_succ_succ_zero (hx : x ∈ domain D) (α β : Fin 3) :
    christoffelOf (metric D).coefficient x α.succ β.succ 0 =
      if α = β then deriv (D.a α) (x 0) / D.a α (x 0) else 0 := by
  rw [christoffelOf_eq hx]
  fin_cases α <;> fin_cases β <;> rfl

/-- `Γ⁰₀₀ = 0`. -/
theorem christoffelOf_zero_zero_zero (hx : x ∈ domain D) :
    christoffelOf (metric D).coefficient x 0 0 0 = 0 := by
  rw [christoffelOf_eq hx]
  rfl

/-- `Γ⁰_{0α} = Γ⁰_{α0} = 0`. -/
theorem christoffelOf_zero_zero_succ (hx : x ∈ domain D) (α : Fin 3) :
    christoffelOf (metric D).coefficient x 0 0 α.succ = 0 ∧
      christoffelOf (metric D).coefficient x 0 α.succ 0 = 0 := by
  rw [christoffelOf_eq hx, christoffelOf_eq hx]
  fin_cases α <;> exact ⟨rfl, rfl⟩

/-- `Γ^α_{00} = 0`. -/
theorem christoffelOf_succ_zero_zero (hx : x ∈ domain D) (α : Fin 3) :
    christoffelOf (metric D).coefficient x α.succ 0 0 = 0 := by
  rw [christoffelOf_eq hx]
  fin_cases α <;> rfl

/-- `Γ^α_{βγ} = 0`: the spatial sections are flat. -/
theorem christoffelOf_succ_succ_succ (hx : x ∈ domain D) (α β γ : Fin 3) :
    christoffelOf (metric D).coefficient x α.succ β.succ γ.succ = 0 := by
  rw [christoffelOf_eq hx]
  fin_cases α <;> fin_cases β <;> fin_cases γ <;> rfl

/-- The table agrees with the Christoffel symbols near every point of the domain. -/
theorem eventually_christoffelOf_eq (hx : x ∈ domain D) :
    ∀ᶠ z in 𝓝 x, ∀ k i j, christoffelOf (metric D).coefficient z k i j = christoffel D z k i j := by
  filter_upwards [(domain D).isOpen.mem_nhds hx] with z hz using christoffelOf_eq hz

/-! ### Derivatives of the Christoffel symbols -/

/-- The derivative of `Γ⁰_{αα} = a_α ȧ_α` along `v` is `(ȧ_α² + a_α ä_α) v⁰`. -/
theorem fderiv_gammaSpatial (hx : x ∈ domain D) (α : Fin 3) (v : E) :
    fderiv ℝ (gammaSpatial D α) x v =
      (deriv (D.a α) (x 0) ^ 2 + D.a α (x 0) * deriv (deriv (D.a α)) (x 0)) * v 0 := by
  have h := FLRW.hasFDerivAt_time ((hasDerivAt_a α (time_mem hx)).mul
    (hasDerivAt_deriv_a α (time_mem hx)))
  rw [show gammaSpatial D α = fun z : E => (D.a α * deriv (D.a α)) (z 0) from rfl, h.fderiv]
  simp only [smul_apply, proj_apply, smul_eq_mul]
  ring

/-- The derivative of `Γ^α_{0α} = ȧ_α/a_α` along `v` is `(ä_α a_α − ȧ_α²)/a_α² v⁰`. -/
theorem fderiv_gammaExpansion (hx : x ∈ domain D) (α : Fin 3) (v : E) :
    fderiv ℝ (gammaExpansion D α) x v =
      (deriv (deriv (D.a α)) (x 0) * D.a α (x 0) - deriv (D.a α) (x 0) ^ 2) /
        D.a α (x 0) ^ 2 * v 0 := by
  have ha := (a_pos_of_mem hx α).ne'
  have h := FLRW.hasFDerivAt_time ((hasDerivAt_deriv_a α (time_mem hx)).div
    (hasDerivAt_a α (time_mem hx)) ha)
  rw [show gammaExpansion D α = fun z : E => (deriv (D.a α) / D.a α) (z 0) from rfl, h.fderiv]
  simp only [smul_apply, proj_apply, smul_eq_mul]
  ring

/-! ### The Ricci tensor -/

variable (D) in
/-- The Hubble rate `H_α = ȧ_α/a_α` of the axis `α` at the time `t`. -/
def hubble (α : Fin 3) (t : ℝ) : ℝ := deriv (D.a α) t / D.a α t

variable (D) in
/-- The relative acceleration `ä_α/a_α` of the axis `α` at the time `t`. -/
def accel (α : Fin 3) (t : ℝ) : ℝ := deriv (deriv (D.a α)) t / D.a α t

variable (D) in
/-- The expansion rate `θ = H₁ + H₂ + H₃` of the volume. -/
def expansion (t : ℝ) : ℝ := ∑ α, hubble D α t

variable (D) in
/-- `R₀₀ = −Σ_α ä_α/a_α`. -/
def ricciTime (x : E) : ℝ := -∑ α, accel D α (x 0)

variable (D) in
/-- `R_{αα} = a_α ä_α + a_α ȧ_α (θ − ȧ_α/a_α)`. -/
def ricciSpace (α : Fin 3) (x : E) : ℝ :=
  D.a α (x 0) * deriv (deriv (D.a α)) (x 0) +
    D.a α (x 0) * deriv (D.a α) (x 0) * (expansion D (x 0) - hubble D α (x 0))

variable (D) in
/-- The table of the Ricci tensor: `R₀₀ = ricciTime`, `R_{αβ} = ricciSpace α δ_{αβ}`,
`R₀α = 0`. -/
def ricci (x : E) : Fin 4 → Fin 4 → ℝ :=
  ![![ricciTime D x, 0, 0, 0], ![0, ricciSpace D 0 x, 0, 0], ![0, 0, ricciSpace D 1 x, 0],
    ![0, 0, 0, ricciSpace D 2 x]]

/-- **The Ricci tensor of the anisotropic metric** at every point of the domain is the table
`ricci`. -/
theorem ricciOf_eq (hx : x ∈ domain D) (j k : Fin 4) :
    ricciOf (metric D).coefficient x j k = ricci D x j k := by
  have h0 := (a_pos_of_mem hx 0).ne'
  have h1 := (a_pos_of_mem hx 1).ne'
  have h2 := (a_pos_of_mem hx 2).ne'
  rw [ricciOf_eq_ricciOfChristoffel (eventually_christoffelOf_eq hx)]
  fin_cases j <;> fin_cases k <;>
  · simp only [ricciOfChristoffel, SphericalAnsatz.sum_four, christoffel, ricci, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    simp only [fderiv_gammaSpatial hx, fderiv_gammaExpansion hx, fderiv_const_apply, zero_apply]
    simp [gammaSpatial, gammaExpansion, ricciTime, ricciSpace, expansion, hubble, accel,
      Fin.sum_univ_three]
    try field_simp
    try ring

/-- `R₀₀ = −Σ_α ä_α/a_α`. -/
theorem ricci_zero_zero (hx : x ∈ domain D) :
    ricciOf (metric D).coefficient x 0 0 = -∑ α, deriv (deriv (D.a α)) (x 0) / D.a α (x 0) :=
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

/-- `R_{αβ} = (a_α ä_α + a_α ȧ_α (θ − ȧ_α/a_α)) δ_{αβ}`, with `θ = Σ_β ȧ_β/a_β`. -/
theorem ricci_succ_succ (hx : x ∈ domain D) (α β : Fin 3) :
    ricciOf (metric D).coefficient x α.succ β.succ =
      if α = β then
        D.a α (x 0) * deriv (deriv (D.a α)) (x 0) + D.a α (x 0) * deriv (D.a α) (x 0) *
          (∑ γ, deriv (D.a γ) (x 0) / D.a γ (x 0) - deriv (D.a α) (x 0) / D.a α (x 0))
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

variable (D) in
/-- `H₁H₂ + H₁H₃ + H₂H₃`, the second symmetric function of the Hubble rates. -/
def hubblePairs (t : ℝ) : ℝ :=
  hubble D 0 t * hubble D 1 t + hubble D 0 t * hubble D 2 t + hubble D 1 t * hubble D 2 t

/-- **The scalar curvature** `R = 2 Σ_α ä_α/a_α + 2 (H₁H₂ + H₁H₃ + H₂H₃)`. -/
theorem scalarOf_eq (hx : x ∈ domain D) :
    scalarOf (metric D).coefficient x = 2 * ∑ α, accel D α (x 0) + 2 * hubblePairs D (x 0) := by
  have h0 := (a_pos_of_mem hx 0).ne'
  have h1 := (a_pos_of_mem hx 1).ne'
  have h2 := (a_pos_of_mem hx 2).ne'
  rw [scalarOf_eq_sum hx, SphericalAnsatz.sum_four]
  simp only [ricci, coefficients, ricciTime, ricciSpace, expansion, hubblePairs, hubble, accel,
    Fin.sum_univ_three, Fin.isValue, Matrix.cons_val]
  field_simp
  ring

variable (D) in
/-- `ä_β/a_β + ä_γ/a_γ + H_β H_γ` for `{β, γ}` the two indices other than `α`, at the time
`t`: `G_{αα} = −a_α²` times it. -/
def spatialFactor (t : ℝ) : Fin 3 → ℝ :=
  ![accel D 1 t + accel D 2 t + hubble D 1 t * hubble D 2 t,
    accel D 0 t + accel D 2 t + hubble D 0 t * hubble D 2 t,
    accel D 0 t + accel D 1 t + hubble D 0 t * hubble D 1 t]

variable (D) in
/-- The table of the Einstein tensor: `G₀₀ = H₁H₂ + H₁H₃ + H₂H₃`,
`G_{αβ} = −a_α² (ä_β/a_β + ä_γ/a_γ + H_β H_γ) δ_{αβ}` and `G₀α = 0`. -/
def einstein (x : E) : Fin 4 → Fin 4 → ℝ :=
  ![![hubblePairs D (x 0), 0, 0, 0],
    ![0, -(D.a 0 (x 0) ^ 2 * spatialFactor D (x 0) 0), 0, 0],
    ![0, 0, -(D.a 1 (x 0) ^ 2 * spatialFactor D (x 0) 1), 0],
    ![0, 0, 0, -(D.a 2 (x 0) ^ 2 * spatialFactor D (x 0) 2)]]

/-- **The Einstein tensor of the anisotropic metric** at every point of the domain is the table
`einstein`. -/
theorem einsteinOf_eq (hx : x ∈ domain D) (i k : Fin 4) :
    einsteinOf (metric D).coefficient x i k = einstein D x i k := by
  have h0 := (a_pos_of_mem hx 0).ne'
  have h1 := (a_pos_of_mem hx 1).ne'
  have h2 := (a_pos_of_mem hx 2).ne'
  rw [einsteinOf, ricciOf_eq hx, scalarOf_eq hx, coefficient_metric]
  fin_cases i <;> fin_cases k <;>
  · simp [ricci, einstein, coefficients, ricciTime, ricciSpace, expansion, hubblePairs,
      spatialFactor, hubble, accel, Fin.sum_univ_three]
    try field_simp
    try ring

/-- `G₀₀ = H₁H₂ + H₁H₃ + H₂H₃`. -/
theorem einstein_zero_zero (hx : x ∈ domain D) :
    einsteinOf (metric D).coefficient x 0 0 = hubblePairs D (x 0) :=
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

/-- `G_{αβ} = −a_α² (ä_β/a_β + ä_γ/a_γ + H_β H_γ) δ_{αβ}`, `{β, γ}` the other two indices. -/
theorem einstein_succ_succ (hx : x ∈ domain D) (α β : Fin 3) :
    einsteinOf (metric D).coefficient x α.succ β.succ =
      if α = β then -(D.a α (x 0) ^ 2 * spatialFactor D (x 0) α) else 0 := by
  rw [einsteinOf_eq hx]
  fin_cases α <;> fin_cases β <;> rfl

/-! ### The comoving perfect fluid -/

/-- The covector `u_μ = (−1, 0, 0, 0)` of the comoving four-velocity `u^μ = (1, 0, 0, 0)`. -/
def fluidCovector : Fin 4 → ℝ := ![-1, 0, 0, 0]

variable (D) in
/-- **The stress of the comoving perfect fluid** `T_{μν} = (ρ + p) u_μ u_ν + p g_{μν}` with the
energy density `ρ(t)` and the pressure `p(t)` (Landau–Lifshitz, (94.9)). -/
def perfectFluidStress (ρ p : ℝ → ℝ) (x : E) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => (ρ (x 0) + p (x 0)) * fluidCovector i * fluidCovector j +
    p (x 0) * (metric D).coefficient x i j

variable (D) in
/-- The diagonal entries `(ρ, p a₁², p a₂², p a₃²)` of the stress of the fluid. -/
def fluidDiagonal (ρ p : ℝ → ℝ) (x : E) : Fin 4 → ℝ :=
  ![ρ (x 0), p (x 0) * D.a 0 (x 0) ^ 2, p (x 0) * D.a 1 (x 0) ^ 2, p (x 0) * D.a 2 (x 0) ^ 2]

/-- The stress of the comoving fluid is `diag(ρ, p a₁², p a₂², p a₃²)` at every point. -/
theorem perfectFluidStress_eq (ρ p : ℝ → ℝ) (y : E) :
    perfectFluidStress D ρ p y = Matrix.diagonal (fluidDiagonal D ρ p y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [perfectFluidStress, fluidDiagonal, fluidCovector, coefficient_metric, coefficients]

/-- The empty fluid has no stress. -/
@[simp] theorem perfectFluidStress_zero : perfectFluidStress D 0 0 = 0 := by
  funext y
  ext i j
  simp [perfectFluidStress]

/-! ### The Einstein equations -/

variable (D) in
/-- **The constraint equation** at the time `t`: `H₁H₂ + H₁H₃ + H₂H₃ = κρ + Λ`, the time
component `G₀₀ + Λ g₀₀ = κ T₀₀`. -/
def Constraint (κ Λ : ℝ) (ρ : ℝ → ℝ) (t : ℝ) : Prop :=
  hubblePairs D t = κ * ρ t + Λ

variable (D) in
/-- **The evolution equation of the axis `α`** at the time `t`:
`ä_β/a_β + ä_γ/a_γ + H_β H_γ = −κp + Λ` for `{β, γ}` the other two indices, the component
`G_{αα} + Λ g_{αα} = κ T_{αα}` divided by `−a_α²`. -/
def Evolution (κ Λ : ℝ) (p : ℝ → ℝ) (α : Fin 3) (t : ℝ) : Prop :=
  spatialFactor D t α = -κ * p t + Λ

/-- The time component of the Einstein equations is the constraint:
`G₀₀ + Λ g₀₀ − κ T₀₀ = H₁H₂ + H₁H₃ + H₂H₃ − (κρ + Λ)`. -/
theorem einsteinEquation_zero_zero (hx : x ∈ domain D) (κ Λ : ℝ) (ρ p : ℝ → ℝ) :
    einsteinOf (metric D).coefficient x 0 0 + Λ * (metric D).coefficient x 0 0 -
        κ * perfectFluidStress D ρ p x 0 0 =
      hubblePairs D (x 0) - (κ * ρ (x 0) + Λ) := by
  rw [einstein_zero_zero hx, perfectFluidStress_eq, coefficient_metric]
  simp only [Matrix.diagonal_apply_eq, coefficients, fluidDiagonal, Matrix.cons_val_zero]
  ring

/-- The diagonal spatial components of the Einstein equations are `−a_α²` times the evolution
equations. -/
theorem einsteinEquation_succ_succ (hx : x ∈ domain D) (κ Λ : ℝ) (ρ p : ℝ → ℝ) (α : Fin 3) :
    einsteinOf (metric D).coefficient x α.succ α.succ + Λ * (metric D).coefficient x α.succ α.succ -
        κ * perfectFluidStress D ρ p x α.succ α.succ =
      -(D.a α (x 0) ^ 2) * (spatialFactor D (x 0) α - (-κ * p (x 0) + Λ)) := by
  have hc : (metric D).coefficient x α.succ α.succ = D.a α (x 0) ^ 2 := by
    rw [coefficient_metric, Matrix.diagonal_apply_eq, coefficients_succ]
  have hT : perfectFluidStress D ρ p x α.succ α.succ = p (x 0) * D.a α (x 0) ^ 2 := by
    rw [perfectFluidStress_eq, Matrix.diagonal_apply_eq]
    fin_cases α <;> rfl
  rw [einstein_succ_succ hx, hc, hT]
  simp only [↓reduceIte]
  ring

/-- **The Einstein equations at a point** are the constraint and the three evolution equations
at its time. -/
theorem isEinstein_at_iff (hx : x ∈ domain D) (κ Λ : ℝ) (ρ p : ℝ → ℝ) :
    (∀ i k, einsteinOf (metric D).coefficient x i k + Λ * (metric D).coefficient x i k =
      κ * perfectFluidStress D ρ p x i k) ↔
      Constraint D κ Λ ρ (x 0) ∧ ∀ α, Evolution D κ Λ p α (x 0) := by
  constructor
  · intro h
    refine ⟨?_, fun α => ?_⟩
    · have h0 := einsteinEquation_zero_zero hx κ Λ ρ p
      rw [h 0 0, sub_self] at h0
      exact sub_eq_zero.mp h0.symm
    · have h1 := einsteinEquation_succ_succ hx κ Λ ρ p α
      rw [h α.succ α.succ, sub_self] at h1
      have ha := pow_ne_zero 2 (a_pos_of_mem hx α).ne'
      exact sub_eq_zero.mp ((mul_eq_zero.mp h1.symm).resolve_left (neg_ne_zero.mpr ha))
  · rintro ⟨h0, h1⟩ i k
    by_cases hik : i = k
    · subst hik
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨α, rfl⟩
      · have e0 := einsteinEquation_zero_zero hx κ Λ ρ p
        rw [sub_eq_zero.mpr h0] at e0
        exact sub_eq_zero.mp e0
      · have es := einsteinEquation_succ_succ hx κ Λ ρ p α
        rw [sub_eq_zero.mpr (h1 α), mul_zero] at es
        exact sub_eq_zero.mp es
    · rw [einsteinOf_eq hx, coefficient_metric, perfectFluidStress_eq,
        Matrix.diagonal_apply_ne _ hik, Matrix.diagonal_apply_ne _ hik]
      fin_cases i <;> fin_cases k <;> simp_all [einstein]

/-- **The Einstein equations of the anisotropic model**: the metric with the comoving perfect
fluid satisfies `G_{ik} + Λ g_{ik} = κ T_{ik}` on the domain if and only if the constraint and
the three evolution equations hold at every time of `I`. -/
theorem isEinstein_iff (κ Λ : ℝ) (ρ p : ℝ → ℝ) :
    (metric D).IsEinstein κ Λ (perfectFluidStress D ρ p) ↔
      ∀ t ∈ D.I, Constraint D κ Λ ρ t ∧ ∀ α, Evolution D κ Λ p α t := by
  constructor
  · intro h t ht
    simpa using (isEinstein_at_iff (timeAxis_mem ht) κ Λ ρ p).mp (h _ (timeAxis_mem ht))
  · intro h x hx
    exact (isEinstein_at_iff hx κ Λ ρ p).mpr (h _ (time_mem hx))

/-- **A Ricci-flat model solves the vacuum equations**: if the Ricci tensor vanishes on the
domain, so do the scalar curvature and the Einstein tensor, and `IsEinstein κ 0 0` holds for every
`κ`. -/
theorem isEinstein_of_ricciOf_eq_zero
    (h : ∀ z ∈ domain D, ∀ j k, ricciOf (metric D).coefficient z j k = 0) (κ : ℝ) :
    (metric D).IsEinstein κ 0 0 := by
  intro z hz i k
  simp [einsteinOf, scalarOf, h z hz]

/-! ### Scale factors with a known logarithmic derivative -/

/-- If `ȧ_α = a_α h` at `t ∈ I`, the Hubble rate of the axis `α` is `h(t)`. -/
theorem hubble_eq_of_hasDerivAt {α : Fin 3} {h : ℝ → ℝ} {t : ℝ} (ht : t ∈ D.I)
    (hd : HasDerivAt (D.a α) (D.a α t * h t) t) : hubble D α t = h t := by
  have ha := (D.a_pos α t ht).ne'
  rw [hubble, hd.deriv]
  field_simp

/-- If `ȧ_α = a_α h` on `I` and `h` has the derivative `h'` at `t ∈ I`, then
`ä_α/a_α = h(t)² + h'`. -/
theorem accel_eq_of_hasDerivAt {α : Fin 3} {h : ℝ → ℝ} {t h' : ℝ} (ht : t ∈ D.I)
    (hd : ∀ s ∈ D.I, HasDerivAt (D.a α) (D.a α s * h s) s) (hh : HasDerivAt h h' t) :
    accel D α t = h t ^ 2 + h' := by
  have ha := (D.a_pos α t ht).ne'
  have he : deriv (D.a α) =ᶠ[𝓝 t] fun s => D.a α s * h s := by
    filter_upwards [D.isOpen_I.mem_nhds ht] with s hs using (hd s hs).deriv
  rw [accel, he.deriv_eq, ((hd t ht).fun_mul hh).deriv]
  field_simp

/-- `d/dt t^q = t^q (q/t)` for `t > 0`. -/
theorem hasDerivAt_rpow (q : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => s ^ q) (t ^ q * (q / t)) t := by
  refine (Real.hasDerivAt_rpow_const (Or.inl ht.ne')).congr_deriv ?_
  rw [Real.rpow_sub_one ht.ne']
  field_simp

/-! ### The vacuum Kasner metrics -/

/-- **The Kasner metric** `ds² = −dt² + t^{2p₁} (dx¹)² + t^{2p₂} (dx²)² + t^{2p₃} (dx³)²` on
`t > 0` (Landau–Lifshitz, (117.1)), for any exponents `p`: `a_α(t) = t^{p_α}`. -/
def kasner (p : Fin 3 → ℝ) : Data where
  I := Ioi 0
  a α t := t ^ p α
  isOpen_I := isOpen_Ioi
  contDiffOn_a _ := fun _ ht =>
    (Real.contDiffAt_rpow_const_of_ne (mem_Ioi.mp ht).ne').contDiffWithinAt
  a_pos _ _ ht := Real.rpow_pos_of_pos ht _

/-- The scale factors of the Kasner metric are `a_α(t) = t^{p_α}`. -/
@[simp] theorem kasner_a (p : Fin 3 → ℝ) (α : Fin 3) (t : ℝ) : (kasner p).a α t = t ^ p α := rfl

/-- The times of the Kasner metric are `t > 0`. -/
@[simp] theorem kasner_I (p : Fin 3 → ℝ) : (kasner p).I = Ioi 0 := rfl

/-- `ȧ_α = a_α (p_α t⁻¹)` for the Kasner metric. -/
theorem hasDerivAt_kasner (p : Fin 3 → ℝ) (α : Fin 3) {t : ℝ} (ht : 0 < t) :
    HasDerivAt ((kasner p).a α) ((kasner p).a α t * (p α * t⁻¹)) t := by
  have h := hasDerivAt_rpow (p α) ht
  rw [div_eq_mul_inv] at h
  exact h

/-- The Hubble rates of the Kasner metric are `H_α = p_α/t`. -/
theorem hubble_kasner (p : Fin 3 → ℝ) (α : Fin 3) {t : ℝ} (ht : 0 < t) :
    hubble (kasner p) α t = p α / t := by
  rw [hubble_eq_of_hasDerivAt (h := fun s => p α * s⁻¹) ht (hasDerivAt_kasner p α ht)]
  ring

/-- The relative accelerations of the Kasner metric are `ä_α/a_α = p_α (p_α − 1)/t²`. -/
theorem accel_kasner (p : Fin 3 → ℝ) (α : Fin 3) {t : ℝ} (ht : 0 < t) :
    accel (kasner p) α t = p α * (p α - 1) / t ^ 2 := by
  rw [accel_eq_of_hasDerivAt (h := fun s => p α * s⁻¹) ht
    (fun s hs => hasDerivAt_kasner p α (mem_Ioi.mp hs))
    ((hasDerivAt_inv ht.ne').const_mul (p α))]
  field_simp
  ring

/-- The point of the domain has a positive time. -/
theorem time_pos_kasner {p : Fin 3 → ℝ} {z : E} (hz : z ∈ domain (kasner p)) : 0 < z 0 := hz

/-- `R₀₀ = −(Σ_α p_α² − Σ_α p_α)/t²` for the Kasner metric. -/
theorem ricci_zero_zero_kasner {p : Fin 3 → ℝ} {z : E} (hz : z ∈ domain (kasner p)) :
    ricciOf (metric (kasner p)).coefficient z 0 0 = -(∑ α, p α ^ 2 - ∑ α, p α) / z 0 ^ 2 := by
  have ht := time_pos_kasner hz
  rw [ricciOf_eq hz]
  simp only [ricci, ricciTime, Matrix.cons_val_zero, accel_kasner p _ ht, Fin.sum_univ_three]
  field_simp
  ring

/-- `(t^q)² = t^{2q}` for `t > 0`. -/
theorem rpow_sq {t : ℝ} (ht : 0 < t) (q : ℝ) : (t ^ q) ^ 2 = t ^ (2 * q) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  ring_nf

/-- `R_{αβ} = p_α t^{2p_α − 2} (Σ_β p_β − 1) δ_{αβ}` for the Kasner metric. -/
theorem ricci_succ_succ_kasner {p : Fin 3 → ℝ} {z : E} (hz : z ∈ domain (kasner p))
    (α β : Fin 3) :
    ricciOf (metric (kasner p)).coefficient z α.succ β.succ =
      if α = β then p α * z 0 ^ (2 * p α - 2) * (∑ γ, p γ - 1) else 0 := by
  have ht := time_pos_kasner hz
  have hpow : z 0 ^ (2 * p α - 2) = (z 0 ^ p α) ^ 2 / z 0 ^ 2 := by
    rw [Real.rpow_sub ht, rpow_sq ht, Real.rpow_two]
  have hr : ricciSpace (kasner p) α z = p α * z 0 ^ (2 * p α - 2) * (∑ γ, p γ - 1) := by
    have ha := (Real.rpow_pos_of_pos ht (p α)).ne'
    have hs : ricciSpace (kasner p) α z = (kasner p).a α (z 0) ^ 2 *
        (accel (kasner p) α (z 0) + hubble (kasner p) α (z 0) *
          (expansion (kasner p) (z 0) - hubble (kasner p) α (z 0))) := by
      simp only [ricciSpace, accel, hubble, kasner_a]
      field_simp
    rw [hs, accel_kasner p α ht, expansion, Finset.sum_congr rfl fun γ _ => hubble_kasner p γ ht,
      hubble_kasner p α ht, kasner_a, hpow, ← Finset.sum_div]
    field_simp
    ring
  rw [ricciOf_eq hz, ← hr]
  fin_cases α <;> fin_cases β <;> rfl

/-- The Ricci tensor of the Kasner metric vanishes where `Σp² = Σp` and `p_α (Σp − 1) = 0` for
every `α`. -/
theorem ricciOf_kasner_eq_zero_of {p : Fin 3 → ℝ} (h0 : ∑ α, p α ^ 2 = ∑ α, p α)
    (hs : ∀ α, p α * (∑ β, p β - 1) = 0) {z : E} (hz : z ∈ domain (kasner p)) (j k : Fin 4) :
    ricciOf (metric (kasner p)).coefficient z j k = 0 := by
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨α, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨β, rfl⟩
  · rw [ricci_zero_zero_kasner hz, h0, sub_self, neg_zero, zero_div]
  · exact ricci_zero_succ hz β
  · exact ricci_succ_zero hz α
  · rw [ricci_succ_succ_kasner hz]
    split_ifs
    · rw [mul_right_comm, hs α, zero_mul]
    · rfl

/-- **The vacuum Kasner metrics** (Landau–Lifshitz, (117.2)–(117.3)): the Kasner metric with
exponents `p` is Ricci flat on `t > 0` if and only if `Σ_α p_α = 1` and `Σ_α p_α² = 1`, or all
the exponents vanish (Minkowski space). With `R₀₀ = −(Σp² − Σp)/t²` and
`R_{αα} = p_α t^{2p_α−2} (Σp − 1)`, the exponents with `Σp ≠ 1` all vanish. -/
theorem ricciOf_kasner_eq_zero_iff (p : Fin 3 → ℝ) :
    (∀ z ∈ domain (kasner p), ∀ j k, ricciOf (metric (kasner p)).coefficient z j k = 0) ↔
      (∑ α, p α = 1 ∧ ∑ α, p α ^ 2 = 1) ∨ p = 0 := by
  constructor
  · intro h
    have hz : FLRW.timeAxis 1 ∈ domain (kasner p) := timeAxis_mem (by simp)
    have h0 := h _ hz 0 0
    rw [ricci_zero_zero_kasner hz] at h0
    simp only [FLRW.timeAxis_zero, one_pow, div_one, neg_eq_zero, sub_eq_zero] at h0
    have hs (α : Fin 3) : p α * (∑ β, p β - 1) = 0 := by
      have h1 := h _ hz α.succ α.succ
      rw [ricci_succ_succ_kasner hz] at h1
      simpa using h1
    by_cases h1 : ∑ β, p β = 1
    · exact Or.inl ⟨h1, h0.trans h1⟩
    · exact Or.inr (funext fun α => (mul_eq_zero.mp (hs α)).resolve_right (sub_ne_zero.mpr h1))
  · rintro (⟨h1, h2⟩ | rfl)
    · exact fun z hz => ricciOf_kasner_eq_zero_of (h2.trans h1.symm) (fun α => by simp [h1]) hz
    · exact fun z hz => ricciOf_kasner_eq_zero_of (by simp) (fun α => by simp) hz

/-- **The Kasner metrics solve the vacuum Einstein equations** `G_{ik} = 0` for every coupling
constant when `Σp = Σp² = 1` or `p = 0`. -/
theorem isEinstein_kasner {p : Fin 3 → ℝ} (h : (∑ α, p α = 1 ∧ ∑ α, p α ^ 2 = 1) ∨ p = 0)
    (κ : ℝ) : (metric (kasner p)).IsEinstein κ 0 0 :=
  isEinstein_of_ricciOf_eq_zero ((ricciOf_kasner_eq_zero_iff p).mpr h) κ

/-- **The volume of a Kasner metric grows linearly** (Landau–Lifshitz, §117): under `Σp = 1`,
`a₁a₂a₃ = t`, so `√(−g) = t`. -/
theorem volume_kasner {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) {t : ℝ} (ht : 0 < t) :
    (kasner p).a 0 t * (kasner p).a 1 t * (kasner p).a 2 t = t := by
  rw [Fin.sum_univ_three] at h1
  simp only [kasner_a]
  rw [← Real.rpow_add ht, ← Real.rpow_add ht, h1, Real.rpow_one]

/-! ### The curvature does not vanish -/

/-- `R^α_{0α0} = ä_α/a_α` from the table of Christoffel symbols. -/
theorem curvatureOf_christoffel (hx : x ∈ domain D) (α : Fin 3) :
    curvatureOf (christoffel D) x α.succ 0 α.succ 0 = accel D α (x 0) := by
  have h0 := (a_pos_of_mem hx 0).ne'
  have h1 := (a_pos_of_mem hx 1).ne'
  have h2 := (a_pos_of_mem hx 2).ne'
  fin_cases α <;>
  · simp only [curvatureOf, SphericalAnsatz.sum_four, christoffel, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Fin.isValue, Matrix.cons_val, Fin.reduceSucc]
    simp only [fderiv_gammaExpansion hx, fderiv_const_apply, zero_apply]
    simp [gammaExpansion, accel]
    field_simp
    ring

/-- **The curvature component** `R^α_{0α0} = ä_α/a_α` of the Lorentz metric in the inclusion
chart. -/
theorem chartCurvature_succ_zero_succ_zero (x y : domain D) (α : Fin 3) :
    (metric D).toLorentzMetric.chartCurvature (physicalChart x) y α.succ 0 α.succ 0 =
      accel D α (y.1 0) := by
  rw [toLorentzMetric_chartCurvature_eq_curvatureOf (metric D) x y
    (eventually_christoffelOf_eq y.2), curvatureOf_christoffel y.2]

/-- Two Kasner exponents of a solution are determined by a vanishing third one. -/
theorem kasner_of_eq_zero {a b c : ℝ} (h1 : a + b + c = 1) (h2 : a ^ 2 + b ^ 2 + c ^ 2 = 1)
    (ha : a = 0) : (b = 0 ∧ c = 1) ∨ (b = 1 ∧ c = 0) := by
  subst ha
  have hbc : b * c = 0 := by nlinarith
  rcases mul_eq_zero.mp hbc with hb | hc
  · exact Or.inl ⟨hb, by linarith⟩
  · exact Or.inr ⟨by linarith, hc⟩

/-- The other two Kasner exponents of a solution vanish when the third one is `1`. -/
theorem kasner_of_eq_one {a b c : ℝ} (h1 : a + b + c = 1) (h2 : a ^ 2 + b ^ 2 + c ^ 2 = 1)
    (ha : a = 1) : b = 0 ∧ c = 0 := by
  subst ha
  have hb : b ^ 2 + c ^ 2 = 0 := by linarith
  exact ⟨by nlinarith [sq_nonneg b, sq_nonneg c], by nlinarith [sq_nonneg b, sq_nonneg c]⟩

/-- **No exponent of a curved Kasner solution is `0` or `1`**: if `Σp = Σp² = 1` and `p` is not a
permutation of `(1, 0, 0)`, then every `p_α` differs from `0` and from `1`. -/
theorem kasner_exponent_ne {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1)
    (hp : p ≠ ![1, 0, 0] ∧ p ≠ ![0, 1, 0] ∧ p ≠ ![0, 0, 1]) (α : Fin 3) :
    p α ≠ 0 ∧ p α ≠ 1 := by
  rw [Fin.sum_univ_three] at h1 h2
  obtain ⟨hp1, hp2, hp3⟩ := hp
  have hv (a b c : ℝ) (ha : p 0 = a) (hb : p 1 = b) (hc : p 2 = c) : p = ![a, b, c] := by
    funext i
    fin_cases i <;> simpa
  have h1' : p 1 + p 0 + p 2 = 1 := by linarith
  have h2' : p 1 ^ 2 + p 0 ^ 2 + p 2 ^ 2 = 1 := by linarith
  have h1'' : p 2 + p 0 + p 1 = 1 := by linarith
  have h2'' : p 2 ^ 2 + p 0 ^ 2 + p 1 ^ 2 = 1 := by linarith
  fin_cases α
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases kasner_of_eq_zero h1 h2 h with ⟨hb, hc⟩ | ⟨hb, hc⟩
      · exact hp3 (hv 0 0 1 h hb hc)
      · exact hp2 (hv 0 1 0 h hb hc)
    · obtain ⟨hb, hc⟩ := kasner_of_eq_one h1 h2 h
      exact hp1 (hv 1 0 0 h hb hc)
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases kasner_of_eq_zero h1' h2' h with ⟨hb, hc⟩ | ⟨hb, hc⟩
      · exact hp3 (hv 0 0 1 hb h hc)
      · exact hp1 (hv 1 0 0 hb h hc)
    · obtain ⟨hb, hc⟩ := kasner_of_eq_one h1' h2' h
      exact hp2 (hv 0 1 0 hb h hc)
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases kasner_of_eq_zero h1'' h2'' h with ⟨hb, hc⟩ | ⟨hb, hc⟩
      · exact hp2 (hv 0 1 0 hb hc h)
      · exact hp1 (hv 1 0 0 hb hc h)
    · obtain ⟨hb, hc⟩ := kasner_of_eq_one h1'' h2'' h
      exact hp3 (hv 0 0 1 hb hc h)

/-- `R^α_{0α0} = p_α (p_α − 1)/t²` for the Kasner metric. -/
theorem chartCurvature_kasner {p : Fin 3 → ℝ} (x y : domain (kasner p)) (α : Fin 3) :
    (metric (kasner p)).toLorentzMetric.chartCurvature (physicalChart x) y α.succ 0 α.succ 0 =
      p α * (p α - 1) / y.1 0 ^ 2 := by
  rw [chartCurvature_succ_zero_succ_zero, accel_kasner p α (time_pos_kasner y.2)]

/-- **A Kasner solution other than flat space is curved everywhere** (Landau–Lifshitz, §117):
if `Σp = Σp² = 1` and `p` is not a permutation of `(1, 0, 0)`, then at every point of `t > 0`
every component `R^α_{0α0} = p_α (p_α − 1)/t²` of the curvature tensor is nonzero. -/
theorem chartCurvature_kasner_ne_zero {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1)
    (h2 : ∑ α, p α ^ 2 = 1) (hp : p ≠ ![1, 0, 0] ∧ p ≠ ![0, 1, 0] ∧ p ≠ ![0, 0, 1])
    (x y : domain (kasner p)) (α : Fin 3) :
    (metric (kasner p)).toLorentzMetric.chartCurvature (physicalChart x) y α.succ 0 α.succ 0 ≠
      0 := by
  obtain ⟨h0, h1'⟩ := kasner_exponent_ne h1 h2 hp α
  rw [chartCurvature_kasner]
  exact div_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1'))
    (pow_ne_zero 2 (time_pos_kasner y.2).ne')

/-! ### The Lifshitz–Khalatnikov parametrisation -/

/-- `1 + u + u² > 0`. -/
theorem kasnerDenom_pos (u : ℝ) : 0 < 1 + u + u ^ 2 := by nlinarith [sq_nonneg (u + 1 / 2)]

/-- **The Lifshitz–Khalatnikov parametrisation** of the Kasner exponents (Landau–Lifshitz,
(117.5)): `p₁ = −u/(1 + u + u²)`, `p₂ = (1 + u)/(1 + u + u²)`, `p₃ = u(1 + u)/(1 + u + u²)`. -/
def kasnerExponents (u : ℝ) : Fin 3 → ℝ :=
  ![-u / (1 + u + u ^ 2), (1 + u) / (1 + u + u ^ 2), u * (1 + u) / (1 + u + u ^ 2)]

/-- The parametrised exponents satisfy `Σ_α p_α = 1` for every real `u`. -/
theorem sum_kasnerExponents (u : ℝ) : ∑ α, kasnerExponents u α = 1 := by
  have h := (kasnerDenom_pos u).ne'
  simp only [Fin.sum_univ_three, kasnerExponents, Fin.isValue, Matrix.cons_val]
  field_simp
  ring

/-- The parametrised exponents satisfy `Σ_α p_α² = 1` for every real `u`. -/
theorem sum_sq_kasnerExponents (u : ℝ) : ∑ α, kasnerExponents u α ^ 2 = 1 := by
  have h := (kasnerDenom_pos u).ne'
  simp only [Fin.sum_univ_three, kasnerExponents, Fin.isValue, Matrix.cons_val]
  field_simp
  ring

/-- For `u ≥ 1` the parametrised exponents are ordered: `p₁ ≤ p₂ ≤ p₃`. -/
theorem kasnerExponents_mono {u : ℝ} (hu : 1 ≤ u) :
    kasnerExponents u 0 ≤ kasnerExponents u 1 ∧ kasnerExponents u 1 ≤ kasnerExponents u 2 := by
  have h := kasnerDenom_pos u
  simp only [kasnerExponents, Fin.isValue, Matrix.cons_val]
  constructor
  · exact div_le_div_of_nonneg_right (by linarith) h.le
  · exact div_le_div_of_nonneg_right (by nlinarith) h.le

/-- **The symmetry `u ↦ 1/u`** (Landau–Lifshitz, (117.6)) swaps the last two exponents. -/
theorem kasnerExponents_inv {u : ℝ} (hu : u ≠ 0) :
    kasnerExponents u⁻¹ = ![kasnerExponents u 0, kasnerExponents u 2, kasnerExponents u 1] := by
  have h := (kasnerDenom_pos u).ne'
  have hd : 1 + u⁻¹ + u⁻¹ ^ 2 = (1 + u + u ^ 2) / u ^ 2 := by
    field_simp
    ring
  funext i
  fin_cases i <;> simp only [kasnerExponents, Fin.isValue, Matrix.cons_val, Fin.zero_eta,
    Fin.mk_one, Fin.reduceFinMk, hd] <;> field_simp <;> ring

/-- For a solution of the Kasner conditions, `p₁p₂ + p₁p₃ + p₂p₃ = 0`. -/
theorem kasner_pairs {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1) :
    p 0 * p 1 + p 0 * p 2 + p 1 * p 2 = 0 := by
  rw [Fin.sum_univ_three] at h1 h2
  have h : (p 0 + p 1 + p 2) ^ 2 = 1 := by rw [h1]; norm_num
  nlinarith

/-- **The ranges of the Kasner exponents** (Landau–Lifshitz, §117): a solution of
`Σp = Σp² = 1` ordered `p₁ ≤ p₂ ≤ p₃` has `−1/3 ≤ p₁ ≤ 0 ≤ p₂ ≤ 2/3 ≤ p₃ ≤ 1`. -/
theorem kasner_ranges {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1)
    (h01 : p 0 ≤ p 1) (h12 : p 1 ≤ p 2) :
    -1 / 3 ≤ p 0 ∧ p 0 ≤ 0 ∧ 0 ≤ p 1 ∧ p 1 ≤ 2 / 3 ∧ 2 / 3 ≤ p 2 ∧ p 2 ≤ 1 := by
  have he := kasner_pairs h1 h2
  rw [Fin.sum_univ_three] at h1
  have hp0 : p 0 ≤ 0 := by
    by_contra! h
    nlinarith [mul_pos h (h.trans_le h01), mul_pos h (h.trans_le (h01.trans h12)),
      mul_pos (h.trans_le h01) (h.trans_le (h01.trans h12))]
  have hp2 : 1 / 3 ≤ p 2 := by linarith
  -- `(p₁ − p₂)² = (1 − p₃)(1 + 3p₃)` and `(p₂ − p₃)² = (1 − p₁)(1 + 3p₁)`
  have hq2 : (p 0 - p 1) ^ 2 = (1 - p 2) * (1 + 3 * p 2) := by
    have : p 0 + p 1 = 1 - p 2 := by linarith
    nlinarith
  have hq0 : (p 1 - p 2) ^ 2 = (1 - p 0) * (1 + 3 * p 0) := by
    have : p 1 + p 2 = 1 - p 0 := by linarith
    nlinarith
  have hp2' : p 2 ≤ 1 := by
    by_contra! h
    nlinarith [sq_nonneg (p 0 - p 1)]
  have hp0' : -1 / 3 ≤ p 0 := by
    by_contra! h
    nlinarith [sq_nonneg (p 1 - p 2)]
  have hp1 : 0 ≤ p 1 := by
    by_contra! h
    linarith
  -- `(p₃ − p₂)(p₃ − p₁) = p₃ (3p₃ − 2)`
  have hr : (p 2 - p 1) * (p 2 - p 0) = p 2 * (3 * p 2 - 2) := by
    have : p 0 + p 1 = 1 - p 2 := by linarith
    nlinarith
  have hp2'' : 2 / 3 ≤ p 2 := by
    by_contra! h
    have hneg : p 2 * (3 * p 2 - 2) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    nlinarith [mul_nonneg (sub_nonneg.mpr h12) (sub_nonneg.mpr (h01.trans h12))]
  exact ⟨hp0', hp0, hp1, by linarith, hp2'', hp2'⟩

/-- **Every ordered Kasner solution is parametrised** (Landau–Lifshitz, (117.5)): a solution of
`Σp = Σp² = 1` with `p₁ ≤ p₂ ≤ p₃` is `(0, 0, 1)` or `kasnerExponents u` for some `u ≥ 1`, with
`u = p₃/p₂`. -/
theorem eq_kasnerExponents {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1)
    (h01 : p 0 ≤ p 1) (h12 : p 1 ≤ p 2) :
    p = ![0, 0, 1] ∨ ∃ u, 1 ≤ u ∧ p = kasnerExponents u := by
  obtain ⟨-, -, hp1, -, hp2, -⟩ := kasner_ranges h1 h2 h01 h12
  have he := kasner_pairs h1 h2
  rw [Fin.sum_univ_three] at h1 h2
  rcases hp1.eq_or_lt with h | h
  · left
    have hp0 : p 0 = 0 := by
      have : p 0 * p 2 = 0 := by rw [← h] at he; linarith
      exact (mul_eq_zero.mp this).resolve_right (by linarith)
    funext i
    fin_cases i
    · simpa using hp0
    · simpa using h.symm
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      linarith
  · right
    refine ⟨p 2 / p 1, (one_le_div h).mpr h12, ?_⟩
    have hs : p 1 ^ 2 + p 1 * p 2 + p 2 ^ 2 = p 1 + p 2 := by
      have : p 0 = 1 - p 1 - p 2 := by linarith
      rw [this] at h2
      nlinarith
    have hpos : 0 < p 1 + p 2 := by linarith
    have hden : 1 + p 2 / p 1 + (p 2 / p 1) ^ 2 = (p 1 + p 2) / p 1 ^ 2 := by
      field_simp
      linear_combination hs
    have h1' := h.ne'
    have hpos' := hpos.ne'
    funext i
    fin_cases i <;>
      simp only [kasnerExponents, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
        Matrix.cons_val, hden] <;>
      field_simp
    linear_combination he

/-! ### The declared matter model: dust -/

/-- **The dust-filled Kasner model** (Landau–Lifshitz, §117, problem): for exponents `p` and
`t₀ ≥ 0`, the scale factors `a_α(t) = t^{p_α} (t + t₀)^{2/3 − p_α}` on `t > 0`. Near `t = 0` they
are Kasner (`tendsto_dustKasner_nhdsGT`), for large `t` they approach the isotropic `t^{2/3}`
(`tendsto_dustKasner_atTop`); with `Σp = Σp² = 1` they solve the Einstein equations with dust
(`isEinstein_dustKasner`). -/
def dustKasner (p : Fin 3 → ℝ) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) : Data where
  I := Ioi 0
  a α t := t ^ p α * (t + t₀) ^ (2 / 3 - p α)
  isOpen_I := isOpen_Ioi
  contDiffOn_a _ := fun _ ht =>
    ((Real.contDiffAt_rpow_const_of_ne (mem_Ioi.mp ht).ne').mul
      ((contDiffAt_id.add contDiffAt_const).rpow_const_of_ne
        (add_pos_of_pos_of_nonneg (mem_Ioi.mp ht) ht₀).ne')).contDiffWithinAt
  a_pos _ _ ht := mul_pos (Real.rpow_pos_of_pos ht _)
    (Real.rpow_pos_of_pos (add_pos_of_pos_of_nonneg ht ht₀) _)

/-- The density `ρ(t) = 4/(3κ t (t + t₀))` of the dust. -/
def dustDensity (κ t₀ t : ℝ) : ℝ := 4 / (3 * κ * t * (t + t₀))

/-- **The density of the dust is positive** for `κ > 0`. -/
theorem dustDensity_pos {κ t₀ t : ℝ} (hκ : 0 < κ) (ht₀ : 0 ≤ t₀) (ht : 0 < t) :
    0 < dustDensity κ t₀ t := by
  have hs := add_pos_of_pos_of_nonneg ht ht₀
  unfold dustDensity
  positivity

section Dust

variable {p : Fin 3 → ℝ} {t₀ : ℝ} (ht₀ : 0 ≤ t₀)

include ht₀

/-- The scale factors of the dust model are `a_α(t) = t^{p_α} (t + t₀)^{2/3 − p_α}`. -/
@[simp] theorem dustKasner_a (α : Fin 3) (t : ℝ) :
    (dustKasner p t₀ ht₀).a α t = t ^ p α * (t + t₀) ^ (2 / 3 - p α) := rfl

/-- `ȧ_α = a_α (p_α t⁻¹ + (2/3 − p_α)(t + t₀)⁻¹)` for the dust model. -/
theorem hasDerivAt_dustKasner (α : Fin 3) {t : ℝ} (ht : 0 < t) :
    HasDerivAt ((dustKasner p t₀ ht₀).a α)
      ((dustKasner p t₀ ht₀).a α t * (p α * t⁻¹ + (2 / 3 - p α) * (t + t₀)⁻¹)) t := by
  have hs := add_pos_of_pos_of_nonneg ht ht₀
  have h1 := hasDerivAt_rpow (p α) ht
  have h2 := (hasDerivAt_rpow (2 / 3 - p α) hs).comp t ((hasDerivAt_id' t).add_const t₀)
  refine (h1.fun_mul h2).congr_deriv ?_
  simp only [dustKasner_a, Function.comp_apply, mul_one]
  ring

/-- The Hubble rates of the dust model are `H_α = p_α/t + (2/3 − p_α)/(t + t₀)`. -/
theorem hubble_dustKasner (α : Fin 3) {t : ℝ} (ht : 0 < t) :
    hubble (dustKasner p t₀ ht₀) α t = p α / t + (2 / 3 - p α) / (t + t₀) := by
  rw [hubble_eq_of_hasDerivAt (h := fun s => p α * s⁻¹ + (2 / 3 - p α) * (s + t₀)⁻¹) ht
    (hasDerivAt_dustKasner ht₀ α ht)]
  ring

/-- The relative accelerations of the dust model are
`ä_α/a_α = H_α² − p_α/t² − (2/3 − p_α)/(t + t₀)²`. -/
theorem accel_dustKasner (α : Fin 3) {t : ℝ} (ht : 0 < t) :
    accel (dustKasner p t₀ ht₀) α t = (p α / t + (2 / 3 - p α) / (t + t₀)) ^ 2 -
      p α / t ^ 2 - (2 / 3 - p α) / (t + t₀) ^ 2 := by
  have hs := add_pos_of_pos_of_nonneg ht ht₀
  rw [accel_eq_of_hasDerivAt (h := fun s => p α * s⁻¹ + (2 / 3 - p α) * (s + t₀)⁻¹) ht
    (fun s hs => hasDerivAt_dustKasner ht₀ α (mem_Ioi.mp hs))
    (((hasDerivAt_inv ht.ne').const_mul (p α)).add
      ((((hasDerivAt_id' t).add_const t₀).inv hs.ne').const_mul (2 / 3 - p α)))]
  ring

/-- The constraint of the dust model: `H₁H₂ + H₁H₃ + H₂H₃ = 4/(3t(t + t₀)) = κρ`. -/
theorem constraint_dustKasner (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1) {κ : ℝ}
    (hκ : κ ≠ 0) {t : ℝ} (ht : 0 < t) :
    Constraint (dustKasner p t₀ ht₀) κ 0 (dustDensity κ t₀) t := by
  have hs := (add_pos_of_pos_of_nonneg ht ht₀).ne'
  have hρ : κ * dustDensity κ t₀ t = 4 / 3 * t⁻¹ * (t + t₀)⁻¹ := by
    unfold dustDensity
    field_simp
  rw [Fin.sum_univ_three] at h1 h2
  unfold Constraint hubblePairs
  rw [hubble_dustKasner ht₀ 0 ht, hubble_dustKasner ht₀ 1 ht, hubble_dustKasner ht₀ 2 ht, hρ,
    add_zero]
  linear_combination
    (t⁻¹ ^ 2 * (p 0 + p 1 + p 2 + 1) / 2 + (t + t₀)⁻¹ ^ 2 * (p 0 + p 1 + p 2 - 5 / 3) / 2 -
      t⁻¹ * (t + t₀)⁻¹ * (p 0 + p 1 + p 2 - 1 / 3)) * h1 +
    (-(t⁻¹ ^ 2) / 2 - (t + t₀)⁻¹ ^ 2 / 2 + t⁻¹ * (t + t₀)⁻¹) * h2

/-- The evolution equations of the dust model hold with zero pressure: for `{β, γ}` the other two
indices, `ä_β/a_β + ä_γ/a_γ + H_β H_γ = (p_β² + p_γ² + p_β p_γ − p_β − p_γ)(1/t − 1/(t + t₀))²`,
and the Kasner conditions make the first factor vanish. -/
theorem evolution_dustKasner (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1) (κ : ℝ) {t : ℝ}
    (ht : 0 < t) (α : Fin 3) : Evolution (dustKasner p t₀ ht₀) κ 0 0 α t := by
  have ha (β : Fin 3) := accel_dustKasner (p := p) ht₀ β ht
  have hb (β : Fin 3) := hubble_dustKasner (p := p) ht₀ β ht
  rw [Fin.sum_univ_three] at h1 h2
  simp only [Evolution, Pi.zero_apply, mul_zero, add_zero]
  fin_cases α <;>
    simp only [spatialFactor, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val, ha, hb] <;>
    generalize t + t₀ = s
  · linear_combination (t⁻¹ - s⁻¹) ^ 2 / 2 * h2 +
      (t⁻¹ - s⁻¹) ^ 2 * (p 0 + p 1 + p 2 - 1 - 2 * p 0) / 2 * h1
  · linear_combination (t⁻¹ - s⁻¹) ^ 2 / 2 * h2 +
      (t⁻¹ - s⁻¹) ^ 2 * (p 0 + p 1 + p 2 - 1 - 2 * p 1) / 2 * h1
  · linear_combination (t⁻¹ - s⁻¹) ^ 2 / 2 * h2 +
      (t⁻¹ - s⁻¹) ^ 2 * (p 0 + p 1 + p 2 - 1 - 2 * p 2) / 2 * h1

/-- **The Kasner model filled with dust** (Landau–Lifshitz, §117, problem): for `Σp = Σp² = 1`,
`t₀ ≥ 0` and `κ ≠ 0`, the scale factors `a_α = t^{p_α} (t + t₀)^{2/3 − p_α}` solve the Einstein
equations `G_{ik} = κ T_{ik}` with the comoving dust `p = 0`, `ρ = 4/(3κ t (t + t₀))`. -/
theorem isEinstein_dustKasner (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1) {κ : ℝ}
    (hκ : κ ≠ 0) :
    (metric (dustKasner p t₀ ht₀)).IsEinstein κ 0
      (perfectFluidStress (dustKasner p t₀ ht₀) (dustDensity κ t₀) 0) := by
  rw [isEinstein_iff]
  exact fun t ht => ⟨constraint_dustKasner ht₀ h1 h2 hκ ht, evolution_dustKasner ht₀ h1 h2 κ ht⟩

/-- **Near the singularity the dust model is Kasner**: for `t₀ > 0`,
`a_α(t)/t^{p_α} → t₀^{2/3 − p_α}` as `t → 0⁺`. -/
theorem tendsto_dustKasner_nhdsGT (ht₀' : 0 < t₀) (α : Fin 3) :
    Tendsto (fun t => (dustKasner p t₀ ht₀).a α t / t ^ p α) (𝓝[>] 0)
      (𝓝 (t₀ ^ (2 / 3 - p α))) := by
  have hc : ContinuousAt (fun t : ℝ => (t + t₀) ^ (2 / 3 - p α)) 0 :=
    (continuousAt_id.add continuousAt_const).rpow_const (Or.inl (by simpa using ht₀'.ne'))
  have hlim : Tendsto (fun t : ℝ => (t + t₀) ^ (2 / 3 - p α)) (𝓝[>] 0)
      (𝓝 (t₀ ^ (2 / 3 - p α))) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have := (Real.rpow_pos_of_pos (mem_Ioi.mp ht) (p α)).ne'
  rw [dustKasner_a]
  field_simp

/-- **For large times the dust model isotropizes**: `a_α(t)/t^{2/3} → 1` as `t → ∞`. -/
theorem tendsto_dustKasner_atTop (α : Fin 3) :
    Tendsto (fun t => (dustKasner p t₀ ht₀).a α t / t ^ (2 / 3 : ℝ)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun t : ℝ => 1 + t₀ / t) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add ((tendsto_const_nhds (x := t₀)).div_atTop
      (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop))
  have h2 := h1.rpow_const (p := 2 / 3 - p α) (Or.inl one_ne_zero)
  rw [Real.one_rpow] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hs := add_pos_of_pos_of_nonneg ht ht₀
  have e1 : 1 + t₀ / t = (t + t₀) / t := by
    field_simp
  have e2 : t ^ (2 / 3 : ℝ) = t ^ p α * t ^ (2 / 3 - p α) := by
    rw [← Real.rpow_add ht]
    ring_nf
  have h3 := (Real.rpow_pos_of_pos ht (p α)).ne'
  have h4 := (Real.rpow_pos_of_pos ht (2 / 3 - p α)).ne'
  rw [e1, Real.div_rpow hs.le ht.le, dustKasner_a, e2]
  field_simp

end Dust

end ProjectAinos.GeneralRelativity.Kasner
