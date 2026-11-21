/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.WeakWaves
public import ProjectAinos.Electrodynamics.Radiation.Multipole
public import ProjectAinos.Electrodynamics.Radiation.FarZone
public import ProjectAinos.SmoothGeometry.Wave.SlowSource
public import ProjectAinos.SmoothGeometry.Wave.TransverseTraceless
import Mathlib.Tactic

/-!
# The radiation of gravitational waves

Landau–Lifshitz, *The Classical Theory of Fields*, §110, in the linearized theory about the
Minkowski coefficients `η = diag(−1, 1, 1, 1)` (`LorentzConvention.timeNegative`), with `c = 1`
and the Einstein constant `κ = 8πG` of `G_{ik} = κ T_{ik}`. A source is a field `T_{ab}` of
symmetric matrices with lower indices; a `LocalizedStress T a` is smooth, symmetric, conserved in
the flat sense `Σ_c η^{cc} ∂_c T_{cb} = 0` (that is `∂_c T^{cb} = 0`) and vanishes for `‖x‖ > a`
at all times. The retarded integral is the flat one, `Wave.retardedIntegral`, carried to
space-time by `retardedScalar`; no Green operator is assumed.

* **The field.** `retardedPerturbation κ T`: `h̄_{ik} = 2κ R(T_{ik})`, and `metricPerturbation`:
  its trace reverse `h = h̄ − ½ η tr h̄`. The sign: `□ = Σ_a η^{aa} ∂_a² = −∂ₜ² + Δ` is the `box` of
  the electrodynamics (`flatBox_eq_box`) and `(∂ₜ² − Δ)(Rf) = f`, so `□h̄ = −2κT`
  (`flatBox_retardedPerturbation`). The derivatives commute with the retarded integral, so the
  conservation gives the harmonic gauge `Σ_c η^{cc} ∂_c h̄_{cb} = 0`
  (`harmonic_retardedPerturbation`, `isHarmonicGauge_metricPerturbation`), and with
  `δG = −½ □h̄` of `CoordinateMetric.linearizedEinstein_of_isHarmonicGauge`,
  `linearizedEinstein_retardedPerturbation`: **`δG_{jk}(h) = κ T_{jk}`**.
* **The moments.** The columns `T^{μb}` are conserved currents (`stressColumn`,
  `divergence4_stressColumn`); with the second moment `I_{αβ}(s) = ∫ T₀₀ y_α y_β dy`
  (`secondMoment`), `hasDerivAt_secondMoment_stress` and `hasDerivAt_momentumMoment` give
  `integral_stress_eq_moment`: **`∫ T_{αβ} dV = ½ Ï_{αβ}`**, and
  `deriv_deriv_deriv_secondMoment`: `I⃛_{αβ} = 2 ∫ ∂ₜT_{αβ} dV`.
* **The far zone.** `tendstoUniformlyOn_mul_retardedPerturbation`: `R h̄_{ik}(u + R, Rn) → 2κ (1/4π)
  ∫ T_{ik}(u + ⟨n, y⟩, y) dy`. The slow family `slowStress ε T`, `T^ε_{ab}(t, x) = s_a s_b
  T_{ab}(εt, x)` with `s₀ = 1`, `s_α = ε`, is again localized (`LocalizedStress.slow`), and
  `farZone_quadrupole`: **the limit is `(κ/4π) ε² Ï_{αβ}(εu)` up to `(2|κ|/3) M a⁴ ε³`** for
  `|∂ₜT_{αβ}| ≤ M`; that is `h̄_{αβ} ≈ 2G Ï_{αβ}/R`.
* **The flux of energy.** `quadraticPseudotensor h = ½ {…}(η, δΓ(h))`, the part of the
  pseudotensor (96.9) of `η + h` quadratic in `h`, and the energy flux density `t^{0α}_{(2)}/κ`.
  `tendstoUniformlyOn_mul_fderiv_retardedPerturbation`: `R ∂_c h̄_{ab} → k_c Ā_{ab}` with
  `k = (1, −n)` and the amplitude `Ā_{ab} = 2κ (1/4π) ∫ ∂ₜT_{ab}(u + ⟨n, y⟩, y) dy`
  (`gravitationalAmplitude`), which is in harmonic gauge (`gravitationalAmplitude_gauge`). Since the
  braces are quadratic, `R² t_{(2)}` tends to the plane-wave flux, which is
  `¼ Σ (ΛĀ)²` (`Wave.planeFlux_traceReverse`). `tendsto_pseudotensorFlux`: **the flux through the
  sphere of radius `R` at the time `u + R` tends to `gravitationalPower κ T u = (1/κ) ∫ ¼ Σ (ΛĀ)²
  dσ`**, by dominated convergence.
* **The quadrupole formula.** `gravitationalPower_slow` (110.16): for the slow family with
  `|∂ₜT_{αβ}| ≤ M₁`, `|∂ₜ²T_{αβ}| ≤ M₂`, **`P = κ ε⁶/(360π) Σ D⃛_{αβ}²(εu)` up to
  `120π |κ| M₁ M₂ a⁷ ε⁷`**, with `D = 3I − δ tr I`, from `∫ Σ (ΛQ)² dσ = (8π/45) Σ D(Q)²`
  (`Wave.integral_ttSquare`). In the units of Landau and Lifshitz `κ/360π = k/45c⁵`.
  `tendsto_pseudotensorFlux_slow` combines the two statements.
* **A circular binary** (§110, problem 1). `binaryMoment`: `I_{αβ} = μ x_α x_β` for
  `x = a (cos ωt, sin ωt, 0)`; `sum_sq_quadrupoleOf_binary`: `Σ D⃛² = 288 μ² a⁴ ω⁶`, and
  `binary_power`: `(κ/360π) Σ D⃛² = (32/5) G μ² a⁴ ω⁶` with `G = κ/8π`. A smooth model:
  `quadrupoleSource Q χ`, the source of the superpotential `Ψ^{0α0β} = Q_{αβ}(t) χ(x)`
  (`T₀₀ = Σ Q_{γδ} ∂_γ∂_δχ`, `T₀ᵧ = Σ_α Q̇_{αγ} ∂_αχ`, `T_{γδ} = Q̈_{γδ} χ`), is a localized stress
  tensor (`localizedStress_quadrupoleSource`) with the second moment `2 Q ∫ χ`
  (`secondMoment_quadrupoleSource`); `binarySource μ a` has the second moment of the binary
  (`secondMoment_binarySource`), its slow family `slowStress ω` is the binary of angular frequency
  `ω` (`secondMoment_slowStress_binarySource`), and `binary_power_smooth`: the flux of the
  pseudotensor tends to `(32/5) G μ² a⁴ ω⁶ + O(ω⁷)`. `localizedStress_zero` is the trivial
  instance.

The source is not required to be the matter of a solution of the full equations: in the
linearized theory `∂_c T^{cb} = 0` with the flat derivative is the consistency condition of
`δG = κT`, and the binary source contains the stresses that hold the bodies on their orbits.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real
open scoped Topology ContDiff

namespace ProjectAinos.GeneralRelativity.LinearizedRadiation

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Sphere CoordinateMetric
open Electrodynamics Electrodynamics.Radiation SpecialRelativity WeakWaves

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The flat wave operator -/

/-- The second partial derivative is the iterated derivative along the axes. -/
theorem secondPartial_eq_partialAt (f : Spacetime → ℝ) (x : Spacetime) (a b : Fin 4) :
    secondPartial f x a b = partialAt (partialAt f b) a x := rfl

/-- The space signs: `η_{i+1, i+1} = 1`. -/
@[simp] theorem lorentzSign_succ (i : Fin 3) : lorentzSign (d := 3) .timeNegative i.succ = 1 := by
  simp [lorentzSign, LorentzConvention.timeSign, Fin.succ_ne_zero]

/-- **The flat wave operator** `□ = Σ_a η^{aa} ∂_a ∂_a` of the linearized Einstein operator is the
operator `box = −∂₀² + Δ` of the electrodynamics. -/
theorem flatBox_eq_box (f : Spacetime → ℝ) (x : Spacetime) :
    flatBox .timeNegative f x = box f x := by
  simp only [flatBox, box, Fin.sum_univ_succ (n := 3), secondPartial_eq_partialAt, lorentzSign_succ,
    one_mul, lorentzSign_zero]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.sum_univ_succ]
  ring

/-! ### Localized stress tensors -/

/-- The component `T_{ab}(t, x)` of a field of matrices, written as a function of time and space. -/
def splitStress (T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (a b : Fin 4) : ℝ × E3 → ℝ :=
  fun p => T (Wave.timeSpaceEquiv.symm p) a b

/-- A **localized stress tensor** `T_{ab}` (lower indices): smooth, symmetric, conserved in the
flat sense, `Σ_c η^{cc} ∂_c T_{cb} = 0` (that is `∂_c T^{cb} = 0`), and vanishing for `‖x‖ > a`
at all times. -/
structure LocalizedStress (T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (a : ℝ) : Prop where
  radius_nonneg : 0 ≤ a
  contDiff : ∀ i k, ContDiff ℝ ∞ fun z => T z i k
  symm : ∀ z i k, T z i k = T z k i
  conserved : ∀ z b, ∑ c : Fin 4, lorentzSign (d := 3) .timeNegative c *
    fderiv ℝ (fun w => T w c b) z (Pi.single c 1) = 0
  support : ∀ (t : ℝ) (x : E3), a < ‖x‖ → T (vector t x) = 0

namespace LocalizedStress

variable {T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ}

/-- The components of a localized stress tensor are localized in time and space. -/
theorem localizedSupport (hT : LocalizedStress T a) (i k : Fin 4) :
    Wave.LocalizedSupport a (splitStress T i k) := fun t y hy => by
  simp only [splitStress, Wave.timeSpaceEquiv_symm_apply]
  rw [hT.support t y hy]
  rfl

/-- The components have subluminal support. -/
theorem subluminalSupport (hT : LocalizedStress T a) (i k : Fin 4) :
    Wave.SubluminalSupport a 0 fun p => T (Wave.timeSpaceEquiv.symm p) i k :=
  (hT.localizedSupport i k).subluminalSupport

/-- The components in time and space are smooth. -/
theorem contDiff_split (hT : LocalizedStress T a) (i k : Fin 4) :
    ContDiff ℝ ∞ (splitStress T i k) :=
  (hT.contDiff i k).comp Wave.timeSpaceEquiv.symm.contDiff

/-- A component vanishes outside the ball. -/
theorem apply_eq_zero (hT : LocalizedStress T a) {t : ℝ} {x : E3} (hx : a < ‖x‖) (i k : Fin 4) :
    T (vector t x) i k = 0 := by
  rw [hT.support t x hx]
  rfl

end LocalizedStress

/-! ### The retarded perturbation -/

/-- **The retarded perturbation** `h̄_{ik} = 2κ R(T_{ik})`, with the retarded integral
`R f(t, x) = ∫ f(t − ‖y‖, x − y)/(4π‖y‖) dy` (Landau–Lifshitz, §110, with `κ = 8πk/c⁴`). -/
def retardedPerturbation (κ : ℝ) (T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (z : Spacetime) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i k => 2 * κ * retardedScalar (fun w => T w i k) z

/-- The metric perturbation `h = h̄ − ½ η tr h̄`, the trace reverse of the retarded perturbation. -/
def metricPerturbation (κ : ℝ) (T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (z : Spacetime) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  traceReverse .timeNegative (retardedPerturbation κ T z)

variable {T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ} {a κ : ℝ}

theorem retardedPerturbation_apply (z : Spacetime) (i k : Fin 4) :
    retardedPerturbation κ T z i k = 2 * κ * retardedScalar (fun w => T w i k) z := rfl

/-- The trace reverse of the metric perturbation is the retarded perturbation. -/
theorem traceReverse_metricPerturbation (z : Spacetime) :
    traceReverse .timeNegative (metricPerturbation κ T z) = retardedPerturbation κ T z :=
  traceReverse_traceReverse _

/-- The retarded perturbation of a localized stress tensor is smooth. -/
theorem contDiff_retardedPerturbation (hT : LocalizedStress T a) (i k : Fin 4) :
    ContDiff ℝ ∞ fun z => retardedPerturbation κ T z i k :=
  contDiff_const.mul (contDiff_retardedScalar (hT.contDiff i k) (hT.subluminalSupport i k))

/-- The metric perturbation of a localized stress tensor is smooth. -/
theorem contDiff_metricPerturbation (hT : LocalizedStress T a) (i k : Fin 4) :
    ContDiff ℝ ∞ fun z => metricPerturbation κ T z i k := by
  simp only [metricPerturbation, traceReverse_apply, flatTrace]
  exact (contDiff_retardedPerturbation hT i k).sub ((ContDiff.sum fun c _ =>
    contDiff_const.mul (contDiff_retardedPerturbation hT c c)).div_const _ |>.mul contDiff_const)

/-- The retarded perturbation of a symmetric source is symmetric. -/
theorem retardedPerturbation_symm (hT : LocalizedStress T a) (z : Spacetime) (i k : Fin 4) :
    retardedPerturbation κ T z i k = retardedPerturbation κ T z k i := by
  simp only [retardedPerturbation_apply]
  congr 2
  funext w
  exact hT.symm w i k

/-- **The wave equation** `□h̄_{ik} = −2κ T_{ik}`, that is `(∂ₜ² − Δ) h̄_{ik} = 2κ T_{ik}`. -/
theorem flatBox_retardedPerturbation (hT : LocalizedStress T a) (x : Spacetime) (i k : Fin 4) :
    flatBox .timeNegative (fun z => retardedPerturbation κ T z i k) x = -(2 * κ * T x i k) := by
  have hc : ContDiff ℝ ∞ (retardedScalar fun w => T w i k) :=
    contDiff_retardedScalar (hT.contDiff i k) (hT.subluminalSupport i k)
  simp only [retardedPerturbation_apply]
  rw [flatBox, Finset.sum_congr rfl fun c _ => by
    rw [secondPartial_const_mul hc.contDiffAt (2 * κ)]]
  have h := box_retardedScalar ((hT.contDiff i k).of_le (by simp)) (hT.subluminalSupport i k) x
  rw [← flatBox_eq_box, flatBox] at h
  have e : ∑ c : Fin (3 + 1), lorentzSign (d := 3) .timeNegative c *
      (2 * κ * secondPartial (retardedScalar fun w => T w i k) x c c) =
        2 * κ * ∑ c : Fin (3 + 1), lorentzSign (d := 3) .timeNegative c *
          secondPartial (retardedScalar fun w => T w i k) x c c := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [e, h]
  ring

/-- The derivatives commute with the retarded perturbation:
`∂_c h̄_{ik} = 2κ R(∂_c T_{ik})`. -/
theorem fderiv_retardedPerturbation (hT : LocalizedStress T a) (x : Spacetime) (i k c : Fin 4) :
    fderiv ℝ (fun z => retardedPerturbation κ T z i k) x (Pi.single c 1) =
      2 * κ * retardedScalar (partialAt (fun w => T w i k) c) x := by
  have hc : ContDiff ℝ ∞ (retardedScalar fun w => T w i k) :=
    contDiff_retardedScalar (hT.contDiff i k) (hT.subluminalSupport i k)
  simp only [retardedPerturbation_apply]
  rw [fderiv_const_mul ((hc.differentiable (by simp)) x), _root_.smul_apply, smul_eq_mul]
  have h := congrFun (partialAt_retardedScalar ((hT.contDiff i k).of_le (by simp))
    (hT.subluminalSupport i k) c) x
  rw [partialAt] at h
  rw [h]

/-- **The harmonic gauge** of the retarded perturbation: `Σ_c η^{cc} ∂_c h̄_{cb} = 0`, from the
conservation `Σ_c η^{cc} ∂_c T_{cb} = 0`, because the derivatives commute with the retarded
integral. -/
theorem harmonic_retardedPerturbation (hT : LocalizedStress T a) (x : Spacetime) (b : Fin 4) :
    ∑ c : Fin 4, lorentzSign (d := 3) .timeNegative c *
      fderiv ℝ (fun z => retardedPerturbation κ T z c b) x (Pi.single c 1) = 0 := by
  simp only [fderiv_retardedPerturbation hT]
  have hcont : ∀ c : Fin 4, Continuous (partialAt (fun w => T w c b) c) := fun c =>
    (contDiff_partialAt_of_le (m := 0) (hT.contDiff c b) (by simp) c).continuous
  have hsupp : ∀ c : Fin 4, Wave.SubluminalSupport a 0
      fun p => partialAt (fun w => T w c b) c (Wave.timeSpaceEquiv.symm p) := fun c =>
    subluminalSupport_partialAt ((hT.contDiff c b).differentiable (by simp))
      (hT.subluminalSupport c b) c
  have hsum := retardedScalar_finsetSum Finset.univ
    (F := fun c : Fin 4 => fun w => lorentzSign (d := 3) .timeNegative c *
      partialAt (fun w => T w c b) c w)
    (fun c _ => continuous_const.mul (hcont c))
    (fun c _ => (hsupp c).mono (tsupport_mul_subset_right)) x
  have hzero : (fun w => ∑ c : Fin 4, lorentzSign (d := 3) .timeNegative c *
      partialAt (fun w => T w c b) c w) = fun _ => 0 := funext fun w => hT.conserved w b
  rw [hzero, show retardedScalar (fun _ => (0 : ℝ)) x = 0 from Wave.retardedIntegral_zero _]
    at hsum
  have hmul : ∀ c : Fin 4, retardedScalar (fun w => lorentzSign (d := 3) .timeNegative c *
      partialAt (fun w => T w c b) c w) x =
        lorentzSign (d := 3) .timeNegative c * retardedScalar (partialAt (fun w => T w c b) c) x :=
    fun c => Wave.retardedIntegral_const_mul _ _ _
  simp only [hmul] at hsum
  calc ∑ c : Fin 4, lorentzSign (d := 3) .timeNegative c *
        (2 * κ * retardedScalar (partialAt (fun w => T w c b) c) x)
      = 2 * κ * ∑ c : Fin 4, lorentzSign (d := 3) .timeNegative c *
          retardedScalar (partialAt (fun w => T w c b) c) x := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring
    _ = 0 := by rw [← hsum, mul_zero]

/-- The metric perturbation is in harmonic gauge on all of space-time. -/
theorem isHarmonicGauge_metricPerturbation (hT : LocalizedStress T a) :
    IsHarmonicGauge .timeNegative (metricPerturbation κ T) ⊤ := fun x _ b => by
  simp only [traceReverse_metricPerturbation]
  exact harmonic_retardedPerturbation hT x b

/-- **The linearized Einstein equations** (Landau–Lifshitz, §§105, 110): the linearized
Einstein tensor of the metric perturbation is `δG_{jk} = −½ □h̄_{jk} = κ T_{jk}`. -/
theorem linearizedEinstein_retardedPerturbation (hT : LocalizedStress T a) (x : Spacetime)
    (j k : Fin 4) :
    linearizedEinstein .timeNegative (metricPerturbation κ T) x j k = κ * T x j k := by
  rw [linearizedEinstein_of_isHarmonicGauge (U := ⊤)
    (fun i j => (contDiff_metricPerturbation hT i j).contDiffOn)
    (isHarmonicGauge_metricPerturbation hT) (by simp)]
  simp only [traceReverse_metricPerturbation]
  rw [flatBox_retardedPerturbation hT]
  ring

/-! ### The moments of the source -/

/-- The column `T^{μb} = η^{μμ} η^{bb} T_{μb}` of a stress tensor with raised indices, a current
on space-time. -/
def stressColumn (T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (b : Fin 4) : Spacetime → Spacetime :=
  fun v μ => lorentzSign (d := 3) .timeNegative μ * lorentzSign (d := 3) .timeNegative b * T v μ b

theorem stressColumn_apply (b : Fin 4) (v : Spacetime) (μ : Fin 4) :
    stressColumn T b v μ =
      lorentzSign (d := 3) .timeNegative μ * lorentzSign (d := 3) .timeNegative b * T v μ b := rfl

/-- The columns of a smooth stress tensor are smooth. -/
theorem contDiff_stressColumn (hT : LocalizedStress T a) (b : Fin 4) :
    ContDiff ℝ ∞ (stressColumn T b) :=
  contDiff_pi.2 fun μ => contDiff_const.mul (hT.contDiff μ b)

/-- **The columns are conserved currents**: `∂_μ T^{μb} = η^{bb} Σ_μ η^{μμ} ∂_μ T_{μb} = 0`. -/
theorem divergence4_stressColumn (hT : LocalizedStress T a) (b : Fin 4) (v : Spacetime) :
    divergence4 (stressColumn T b) v = 0 := by
  rw [divergence4_eq_sum_partialAt ((contDiff_stressColumn hT b).differentiable (by simp) v)]
  have h : ∀ μ : Fin 4, partialAt (fun w => stressColumn T b w μ) μ v =
      lorentzSign (d := 3) .timeNegative b * (lorentzSign (d := 3) .timeNegative μ *
        fderiv ℝ (fun w => T w μ b) v (Pi.single μ 1)) := fun μ => by
    simp only [partialAt, stressColumn_apply]
    rw [fderiv_const_mul (((hT.contDiff μ b).differentiable (by simp)) v), _root_.smul_apply,
      smul_eq_mul]
    ring
  simp only [h, ← Finset.mul_sum, hT.conserved v b, mul_zero]

/-- The columns vanish outside the ball. -/
theorem stressColumn_eq_zero (hT : LocalizedStress T a) (b : Fin 4) (t : ℝ) (x : E3)
    (hx : a < ‖x‖) : stressColumn T b (vector t x) = 0 := by
  funext μ
  simp [stressColumn_apply, hT.apply_eq_zero hx]

/-- **The conservation law for the first moments** of a conserved current with spatial support in
a ball: `d/ds ∫ k⁰(s, y) y_δ dy = ∫ k^δ(s, y) dy`. -/
theorem hasDerivAt_integral_mul_coord {k : Spacetime → Spacetime} (hk : ContDiff ℝ ∞ k)
    (hdiv : ∀ v, divergence4 k v = 0) (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0)
    (δ : Fin 3) (s : ℝ) :
    HasDerivAt (fun s => ∫ y, k (vector s y) 0 * y δ) (∫ y, k (vector s y) δ.succ) s := by
  have h := hasDerivAt_integral_smul hk hs (w := fun y : E3 => y δ) (by fun_prop) 0 s
  simp only [smul_eq_mul] at h
  have hW : ContDiff ℝ 1 fun y : E3 => y δ := (EuclideanSpace.proj (𝕜 := ℝ) δ).contDiff
  have h2 := integral_mul_currentRate_zero hk hdiv hs hW s
  have hd : ∀ y : E3, fderiv ℝ (fun y : E3 => y δ) y = EuclideanSpace.proj δ := fun y =>
    (EuclideanSpace.proj (𝕜 := ℝ) δ).fderiv
  simp only [hd] at h2
  convert h using 1
  rw [show (fun y => currentRate k (vector s y) 0 * y δ) =
    fun y => y δ * currentRate k (vector s y) 0 from funext fun y => mul_comm _ _, h2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [PiLp.proj_apply, space_apply]

/-- The second moment `I_{αβ}(s) = ∫ T₀₀(s, y) y_α y_β dy` of the energy density
(Landau–Lifshitz, §§41, 110). -/
def secondMoment (T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (s : ℝ) (α β : Fin 3) : ℝ :=
  ∫ y : E3, T (vector s y) 0 0 * (y α * y β)

/-- The moments `∫ T₀ᵧ(s, y) y_δ dy` of the momentum density. -/
def momentumMoment (T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (s : ℝ) (γ δ : Fin 3) : ℝ :=
  ∫ y : E3, T (vector s y) 0 γ.succ * y δ

/-- The integrals `∫ T_{ab}(s, y) dy` of the components over space. -/
def stressIntegral (T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (s : ℝ) (i k : Fin 4) : ℝ :=
  ∫ y : E3, T (vector s y) i k

/-- **The energy conservation for the second moment**:
`İ_{αβ} = −∫ (T₀ᵦ y_α + T₀α y_β) dy` (with `T₀ᵧ = −T^{0γ}`). -/
theorem hasDerivAt_secondMoment_stress (hT : LocalizedStress T a) (α β : Fin 3) (s : ℝ) :
    HasDerivAt (fun s => secondMoment T s α β)
      (-(momentumMoment T s β α + momentumMoment T s α β)) s := by
  have h := Radiation.hasDerivAt_secondMoment (contDiff_stressColumn hT 0)
    (divergence4_stressColumn hT 0) (stressColumn_eq_zero hT 0) α β s
  simp only [stressColumn_apply, lorentzSign_zero, lorentzSign_succ] at h
  have h' : HasDerivAt (fun s => secondMoment T s α β)
      (∫ y, (y α * (1 * -1 * T (vector s y) β.succ 0) +
        y β * (1 * -1 * T (vector s y) α.succ 0))) s := by
    convert h using 1
    funext s
    simp only [secondMoment]
    congr 1
    funext y
    ring
  refine h'.congr_deriv ?_
  have hc : ∀ γ : Fin 3, Continuous fun v : Spacetime => T v 0 γ.succ := fun γ =>
    (hT.contDiff 0 γ.succ).continuous
  have hi : ∀ γ δ : Fin 3, Integrable fun y : E3 => T (vector s y) 0 γ.succ * y δ := fun γ δ =>
    integrable_of_ballSupport (a := a) (((hc γ).comp
      (continuous_vector_of_continuous continuous_const continuous_id)).mul (by fun_prop))
      fun y hy => by simp [hT.apply_eq_zero hy]
  simp only [momentumMoment]
  rw [← integral_add (hi β α) (hi α β), ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [hT.symm (vector s y) β.succ 0, hT.symm (vector s y) α.succ 0]
  ring

/-- **The momentum conservation for the moments of the momentum density**:
`d/ds ∫ T₀ᵧ y_δ dy = −∫ T_{δγ} dy`. -/
theorem hasDerivAt_momentumMoment (hT : LocalizedStress T a) (γ δ : Fin 3) (s : ℝ) :
    HasDerivAt (fun s => momentumMoment T s γ δ) (-stressIntegral T s δ.succ γ.succ) s := by
  have h := hasDerivAt_integral_mul_coord (contDiff_stressColumn hT γ.succ)
    (divergence4_stressColumn hT γ.succ) (stressColumn_eq_zero hT γ.succ) δ s
  simp only [stressColumn_apply, lorentzSign_zero, lorentzSign_succ] at h
  have h' := h.fun_neg
  convert h' using 1
  · funext s
    simp only [momentumMoment]
    rw [← integral_neg]
    congr 1
    funext y
    ring
  · simp only [stressIntegral, one_mul]

/-- **The stresses as the second derivative of the second moment** (Landau–Lifshitz, §110):
for a conserved localized source, `∫ T_{αβ} dV = ½ d²/dt² ∫ T₀₀ x_α x_β dV`.
-/
theorem integral_stress_eq_moment (hT : LocalizedStress T a) (s : ℝ) (α β : Fin 3) :
    ∫ y : E3, T (vector s y) α.succ β.succ =
      deriv (deriv fun s => secondMoment T s α β) s / 2 := by
  have h1 : deriv (fun s => secondMoment T s α β) =
      fun s => -(momentumMoment T s β α + momentumMoment T s α β) :=
    funext fun s => (hasDerivAt_secondMoment_stress hT α β s).deriv
  have h2 := ((hasDerivAt_momentumMoment hT β α s).fun_add
    (hasDerivAt_momentumMoment hT α β s)).fun_neg
  rw [h1, h2.deriv]
  have hs : stressIntegral T s β.succ α.succ = stressIntegral T s α.succ β.succ := by
    simp only [stressIntegral]
    congr 1
    funext y
    exact hT.symm _ _ _
  rw [hs, stressIntegral]
  ring

/-! ### The far zone -/

/-- A constant multiple of a uniformly convergent family of real functions converges uniformly. -/
theorem tendstoUniformlyOn_const_mul {ι X : Type*} {F : ι → X → ℝ} {f : X → ℝ} {l : Filter ι}
    {s : Set X} (h : TendstoUniformlyOn F f l s) (c : ℝ) :
    TendstoUniformlyOn (fun i x => c * F i x) (fun x => c * f x) l s := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h (ε / (|c| + 1)) (by positivity)] with i hi x hx
  have h1 := hi x hx
  rw [Real.dist_eq, ← mul_sub, abs_mul]
  rw [Real.dist_eq] at h1
  calc |c| * |f x - F i x| ≤ |c| * (ε / (|c| + 1)) :=
        mul_le_mul_of_nonneg_left h1.le (abs_nonneg c)
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg c]

/-- The retarded perturbation at the point `(t, x)` is `2κ` times the retarded integral of the
component written in time and space. -/
theorem retardedPerturbation_vector (t : ℝ) (x : E3) (i k : Fin 4) :
    retardedPerturbation κ T (vector t x) i k =
      2 * κ * Wave.retardedIntegral (splitStress T i k) (t, x) := by
  simp only [retardedPerturbation_apply, retardedScalar, Wave.timeSpaceEquiv_apply, vector_zero,
    space_vector]
  rfl

/-- **The far zone** (Landau–Lifshitz, §110): at the distance `R` in the direction `n` and the
retarded time `u`, `R h̄_{ik}(u + R, Rn) → 2κ (1/4π) ∫ T_{ik}(u + ⟨n, y⟩, y) dy`, uniformly for `u`
in a compact set and `n` on the unit sphere. -/
theorem tendstoUniformlyOn_mul_retardedPerturbation (hT : LocalizedStress T a) {K : Set ℝ}
    (hK : IsCompact K) (i k : Fin 4) :
    TendstoUniformlyOn
      (fun R (p : ℝ × E3) => R * retardedPerturbation κ T (vector (p.1 + R) (R • p.2)) i k)
      (fun p => 2 * κ * Wave.farAmplitude (splitStress T i k) p.1 p.2) atTop
      (K ×ˢ sphere (0 : E3) 1) := by
  have h := tendstoUniformlyOn_const_mul (Wave.tendstoUniformlyOn_mul_retardedIntegral
    (hT.contDiff_split i k).continuous (hT.localizedSupport i k) hK) (2 * κ)
  refine h.congr (Eventually.of_forall fun R p _ => ?_)
  simp only [retardedPerturbation_vector]
  ring

/-! ### Slow sources -/

/-- The scale `1` of the time index and `ε` of the spatial indices. -/
def indexScale (ε : ℝ) (a : Fin 4) : ℝ := if a = 0 then 1 else ε

/-- **The slow family** `T^ε_{ab}(t, x) = s_a s_b T_{ab}(εt, x)` with `s₀ = 1` and `s_α = ε`: the
same motion `ε` times more slowly, with the velocities `ε` times smaller, so that the size of the
system is small compared with the wavelengths `~ 1/ε` (Landau–Lifshitz, §110: `v ≪ c`). -/
def slowStress (ε : ℝ) (T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (v : Spacetime) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun a b => indexScale ε a * indexScale ε b * T (timeDilation ε v) a b

theorem slowStress_apply (ε : ℝ) (v : Spacetime) (a b : Fin 4) :
    slowStress ε T v a b = indexScale ε a * indexScale ε b * T (timeDilation ε v) a b := rfl

/-- The derivatives of the slow family:
`∂_c T^ε_{ab} = s_a s_b (ε if c = 0, else 1) (∂_c T_{ab})(εt, x)`. -/
theorem fderiv_slowStress (hT : LocalizedStress T a) (ε : ℝ) (z : Spacetime) (i k c : Fin 4) :
    fderiv ℝ (fun w => slowStress ε T w i k) z (Pi.single c 1) =
      indexScale ε i * indexScale ε k * (if c = 0 then ε else 1) *
        fderiv ℝ (fun w => T w i k) (timeDilation ε z) (Pi.single c 1) := by
  have hd : DifferentiableAt ℝ (fun w => T w i k) (timeDilation ε z) :=
    (hT.contDiff i k).differentiable (by simp) _
  have h : HasFDerivAt (fun w => slowStress ε T w i k)
      ((indexScale ε i * indexScale ε k) •
        (fderiv ℝ (fun w => T w i k) (timeDilation ε z)).comp (timeDilation ε)) z :=
    (hd.hasFDerivAt.comp z (timeDilation ε).hasFDerivAt).const_mul _
  rw [h.fderiv]
  simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  refine Fin.cases ?_ (fun γ => ?_) c
  · rw [timeDilation_single_zero, map_smul, smul_eq_mul]
    simp only [ite_true]
    ring
  · rw [timeDilation_single_succ]
    simp only [Fin.succ_ne_zero, ite_false]
    ring

/-- **The slow family of a localized stress tensor is a localized stress tensor**: the
conservation `Σ_c η^{cc} ∂_c T^ε_{cb} = ε s_b (Σ_c η^{cc} ∂_c T_{cb})(εt, x) = 0`. -/
theorem LocalizedStress.slow (hT : LocalizedStress T a) (ε : ℝ) :
    LocalizedStress (slowStress ε T) a where
  radius_nonneg := hT.radius_nonneg
  contDiff i k := contDiff_const.mul ((hT.contDiff i k).comp (timeDilation ε).contDiff)
  symm z i k := by
    simp only [slowStress_apply, hT.symm _ i k]
    ring
  conserved z b := by
    simp only [fderiv_slowStress hT]
    have h := hT.conserved (timeDilation ε z) b
    calc ∑ c : Fin 4, lorentzSign (d := 3) .timeNegative c * (indexScale ε c * indexScale ε b *
          (if c = 0 then ε else 1) * fderiv ℝ (fun w => T w c b) (timeDilation ε z)
            (Pi.single c 1))
        = ε * indexScale ε b * ∑ c : Fin 4, lorentzSign (d := 3) .timeNegative c *
            fderiv ℝ (fun w => T w c b) (timeDilation ε z) (Pi.single c 1) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          by_cases hc : c = 0
          · subst hc
            simp only [indexScale, ite_true]
            ring
          · simp only [indexScale, hc, ite_false]
            ring
      _ = 0 := by rw [h, mul_zero]
  support t x hx := by
    funext i k
    simp only [slowStress_apply, timeDilation_vector, hT.apply_eq_zero hx, mul_zero]
    rfl

/-- **The mean value theorem along time**: a function with time derivative bounded by `M` changes
by at most `M |s₁ − s₂|` along a line of time. -/
theorem abs_sub_le_of_timeDeriv_le {F : Spacetime → ℝ} (hF : Differentiable ℝ F) {M : ℝ}
    (hM : ∀ v, |fderiv ℝ F v (Pi.single 0 1)| ≤ M) (y : E3) (s₁ s₂ : ℝ) :
    |F (vector s₁ y) - F (vector s₂ y)| ≤ M * |s₁ - s₂| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun s => F (vector s y))
    (f' := fun s => fderiv ℝ F (vector s y) (Pi.single 0 1)) (s := univ)
    (fun s _ => (hasDerivAt_comp_vector_time (hF _)).hasDerivWithinAt)
    (fun s _ => by rw [Real.norm_eq_abs]; exact hM _) convex_univ (mem_univ s₂) (mem_univ s₁)
  simpa [Real.norm_eq_abs] using h

/-- The delay estimate for a localized component: if `|∂ₜF| ≤ M`, then
`|∫ F(s + δ(y), y) dy − ∫ F(s, y) dy| ≤ M d (4π/3) a³` when `|δ(y)| ≤ d` on the ball. -/
theorem abs_integral_delay_sub_le {F : Spacetime → ℝ} (hF : ContDiff ℝ 1 F) {M d : ℝ}
    (ha : 0 ≤ a) (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → F (vector t x) = 0)
    (hM : ∀ v, |fderiv ℝ F v (Pi.single 0 1)| ≤ M) {τ : E3 → ℝ} (hτ : Continuous τ)
    (hτd : ∀ y : E3, ‖y‖ ≤ a → |τ y| ≤ d) (s : ℝ) :
    |(∫ y : E3, F (vector (s + τ y) y)) - ∫ y : E3, F (vector s y)| ≤
      M * d * (4 * π / 3 * a ^ 3) := by
  have hc : Continuous F := hF.continuous
  have i1 : Integrable fun y : E3 => F (vector (s + τ y) y) :=
    integrable_of_ballSupport (a := a) (hc.comp (continuous_vector_of_continuous
      (continuous_const.add hτ) continuous_id)) fun y hy => hs _ y hy
  have i2 : Integrable fun y : E3 => F (vector s y) :=
    integrable_of_ballSupport (a := a) (hc.comp (continuous_vector_of_continuous
      continuous_const continuous_id)) fun y hy => hs _ y hy
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have key : ∫ y : E3, (F (vector (s + τ y) y) - F (vector s y)) =
      (∫ y : E3, F (vector (s + τ y) y)) - ∫ y : E3, F (vector s y) := integral_sub i1 i2
  rw [← key, ← Real.norm_eq_abs]
  refine norm_integral_le_of_ballSupport ha (fun y hy => by simp [hs _ y hy]) fun y hy => ?_
  rw [Real.norm_eq_abs]
  have h := abs_sub_le_of_timeDeriv_le (hF.differentiable (by norm_num)) hM y (s + τ y) s
  rw [add_sub_cancel_left] at h
  exact h.trans (mul_le_mul_of_nonneg_left (hτd y hy) hM0)

/-- The amplitude of the far field of a component of the slow family:
`(1/4π) ∫ T^ε_{ab}(u + ⟨n, y⟩, y) dy = (1/4π) s_a s_b ∫ T_{ab}(εu + ε⟨n, y⟩, y) dy`. -/
theorem farAmplitude_slowStress (ε u : ℝ) (n : E3) (i k : Fin 4) :
    Wave.farAmplitude (splitStress (slowStress ε T) i k) u n =
      (4 * π)⁻¹ * (indexScale ε i * indexScale ε k) *
        ∫ y, T (vector (ε * u + ε * inner ℝ n y) y) i k := by
  simp only [Wave.farAmplitude, splitStress, Wave.timeSpaceEquiv_symm_apply, slowStress_apply,
    timeDilation_vector, integral_const_mul, mul_add]
  ring

/-- **The quadrupole far zone** (Landau–Lifshitz, §110): for the slow family of a
localized stress tensor whose time derivative `|∂ₜT_{αβ}| ≤ M`, the spatial components of the
perturbation have the far-zone limit `R h̄_{αβ}(u + R, Rn) → 2κ (1/4π) ∫ T^ε_{αβ}(u + ⟨n, y⟩, y)
dy`, and this limit is `(κ/4π) ε² Ï_{αβ}(εu)` up to `(2|κ|/3) M a⁴ ε³`, with the second moment
`I_{αβ} = ∫ T₀₀ y_α y_β dy`. -/
theorem farZone_quadrupole (hT : LocalizedStress T a) {α β : Fin 3} {M : ℝ}
    (hM : ∀ v, |fderiv ℝ (fun w => T w α.succ β.succ) v (Pi.single 0 1)| ≤ M) {ε : ℝ}
    (hε : 0 ≤ ε) (u : ℝ) {n : E3} (hn : ‖n‖ = 1) :
    Tendsto (fun R => R * retardedPerturbation κ (slowStress ε T) (vector (u + R) (R • n))
        α.succ β.succ) atTop
      (𝓝 (2 * κ * Wave.farAmplitude (splitStress (slowStress ε T) α.succ β.succ) u n)) ∧
    |2 * κ * Wave.farAmplitude (splitStress (slowStress ε T) α.succ β.succ) u n -
        κ / (4 * π) * ε ^ 2 * deriv (deriv fun s => secondMoment T s α β) (ε * u)| ≤
      2 * |κ| / 3 * M * a ^ 4 * ε ^ 3 := by
  refine ⟨(tendstoUniformlyOn_mul_retardedPerturbation (hT.slow ε) (isCompact_singleton (x := u))
    α.succ β.succ).tendsto_at (x := (u, n)) ⟨rfl, by simpa using hn⟩, ?_⟩
  rw [farAmplitude_slowStress]
  have hsc : indexScale ε α.succ * indexScale ε β.succ = ε ^ 2 := by
    simp [indexScale, Fin.succ_ne_zero, sq]
  rw [hsc]
  have hd := abs_integral_delay_sub_le ((hT.contDiff α.succ β.succ).of_le (by simp))
    hT.radius_nonneg (fun t x hx => hT.apply_eq_zero hx α.succ β.succ) hM
    (τ := fun y => ε * inner ℝ n y) (d := ε * a) (by fun_prop) (fun y hy => by
      rw [abs_mul, abs_of_nonneg hε]
      refine mul_le_mul_of_nonneg_left ?_ hε
      exact (abs_real_inner_le_norm n y).trans (by rw [hn, one_mul]; exact hy)) (ε * u)
  have e : 2 * κ * ((4 * π)⁻¹ * ε ^ 2 * ∫ y : E3, T (vector (ε * u + ε * inner ℝ n y) y)
      α.succ β.succ) - κ / (4 * π) * ε ^ 2 * (2 * ∫ y : E3, T (vector (ε * u) y) α.succ β.succ) =
      2 * κ * (4 * π)⁻¹ * ε ^ 2 * ((∫ y : E3, T (vector (ε * u + ε * inner ℝ n y) y)
        α.succ β.succ) - ∫ y : E3, T (vector (ε * u) y) α.succ β.succ) := by
    ring
  rw [show deriv (deriv fun s => secondMoment T s α β) (ε * u) =
    2 * ∫ y : E3, T (vector (ε * u) y) α.succ β.succ by
      rw [integral_stress_eq_moment hT]; ring, e, abs_mul]
  have hpos : |2 * κ * (4 * π)⁻¹ * ε ^ 2| = 2 * |κ| * (4 * π)⁻¹ * ε ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (4 * π)⁻¹),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2), abs_two]
  rw [hpos]
  calc 2 * |κ| * (4 * π)⁻¹ * ε ^ 2 * |(∫ y : E3, T (vector (ε * u + ε * inner ℝ n y) y)
        α.succ β.succ) - ∫ y : E3, T (vector (ε * u) y) α.succ β.succ|
      ≤ 2 * |κ| * (4 * π)⁻¹ * ε ^ 2 * (M * (ε * a) * (4 * π / 3 * a ^ 3)) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
    _ = 2 * |κ| / 3 * M * a ^ 4 * ε ^ 3 := by
        field_simp

/-! ### The quadratic pseudotensor -/

/-- **The quadratic pseudotensor**: `t^{ik}_{(2)} = ½ {…}`, the braces (96.9) of the inverse
metric `η⁻¹ = η` and of the linearized Christoffel symbols of `h`. By `pseudotensor_eq` the
pseudotensor of a metric is `½ {…}` with its own inverse and Christoffel symbols; the braces are
quadratic in the Christoffel symbols, which are of the first order in `h`, so this is the part of
the pseudotensor of `η + h` of the second order in `h`. The energy flux density is
`t^{0α}_{(2)}/κ` (Landau–Lifshitz, §96: the factor `c⁴/16πk` is `1/2κ`). -/
def quadraticPseudotensor (h : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (x : Spacetime)
    (i k : Fin 4) : ℝ :=
  pseudoBraces (fun a b : Fin 4 => Minkowski.metricMatrix .timeNegative 3 a b)
    (linearizedChristoffel .timeNegative h x) i k / 2

/-- The Christoffel symbols `½ η^{kk}(d_{ijk} + d_{jki} − d_{kij})` of an array of derivatives
`d_{cab} = ∂_c h_{ab}`. -/
def christoffelOfDerivs (d : Fin 4 → Fin 4 → Fin 4 → ℝ) (k i j : Fin 4) : ℝ :=
  lorentzSign (d := 3) .timeNegative k * (d i j k + d j k i - d k i j) / 2

/-- The derivatives `∂_c h_{ab} = ∂_c h̄_{ab} − ½ η_{ab} η^{ee} ∂_c h̄_{ee}` of the trace
reverse. -/
def traceReverseDerivs (d : Fin 4 → Fin 4 → Fin 4 → ℝ) (c a b : Fin 4) : ℝ :=
  traceReverse .timeNegative (Matrix.of fun e f => d c e f) a b

/-- The linearized Christoffel symbols are the Christoffel symbols of the derivatives. -/
theorem linearizedChristoffel_eq (h : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (x : Spacetime)
    (k i j : Fin 4) :
    linearizedChristoffel .timeNegative h x k i j =
      christoffelOfDerivs (fun c a b => fderiv ℝ (fun z => h z a b) x (Pi.single c 1)) k i j :=
  rfl

/-- The derivatives of the metric perturbation are those of the trace reverse. -/
theorem fderiv_metricPerturbation (hT : LocalizedStress T a) (x : Spacetime) (i k c : Fin 4) :
    fderiv ℝ (fun z => metricPerturbation κ T z i k) x (Pi.single c 1) =
      traceReverseDerivs (fun c a b => fderiv ℝ (fun z => retardedPerturbation κ T z a b) x
        (Pi.single c 1)) c i k := by
  have hd : ∀ i k, DifferentiableAt ℝ (fun z => retardedPerturbation κ T z i k) x := fun i k =>
    (contDiff_retardedPerturbation hT i k).differentiable (by simp) x
  have e : (fun z => metricPerturbation κ T z i k) = fun z => retardedPerturbation κ T z i k -
      Minkowski.metricMatrix .timeNegative 3 i k / 2 *
        ∑ e : Fin (3 + 1), lorentzSign (d := 3) .timeNegative e *
          retardedPerturbation κ T z e e := by
    funext z
    rw [metricPerturbation, traceReverse_apply, flatTrace]
    ring
  have hs : DifferentiableAt ℝ (fun z => ∑ e : Fin (3 + 1), lorentzSign (d := 3) .timeNegative e *
      retardedPerturbation κ T z e e) x :=
    DifferentiableAt.fun_sum fun e _ => (hd e e).const_mul _
  rw [e, fderiv_fun_sub (hd i k) (hs.const_mul _), _root_.sub_apply, fderiv_const_mul hs,
    _root_.smul_apply, smul_eq_mul, fderiv_sum_mul_apply Finset.univ (fun e _ => hd e e)]
  simp only [traceReverseDerivs, traceReverse_apply, flatTrace, Matrix.of_apply]
  ring

/-- The Christoffel symbols of the derivatives are linear. -/
theorem christoffelOfDerivs_mul (r : ℝ) (d : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    christoffelOfDerivs (fun c a b => r * d c a b) = fun k i j => r * christoffelOfDerivs d k i j :=
  funext fun k => funext fun i => funext fun j => by
    simp only [christoffelOfDerivs]
    ring

/-- The derivatives of the trace reverse are linear. -/
theorem traceReverseDerivs_mul (r : ℝ) (d : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    traceReverseDerivs (fun c a b => r * d c a b) = fun c a b => r * traceReverseDerivs d c a b :=
  funext fun c => funext fun a => funext fun b => by
    simp only [traceReverseDerivs, traceReverse_apply, flatTrace, Matrix.of_apply]
    rw [show (∑ e : Fin (3 + 1), lorentzSign (d := 3) .timeNegative e * (r * d c e e)) =
      r * ∑ e : Fin (3 + 1), lorentzSign (d := 3) .timeNegative e * d c e e by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => by ring]
    ring

/-- **The Christoffel symbols of a plane wave**: for `∂_c h̄_{ab} = k_c Ā_{ab}`, the Christoffel
symbols of the trace reverse are `planeChristoffel k (Ā − ½ η tr Ā)`. -/
theorem christoffelOfDerivs_plane (k : Fin 4 → ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) :
    christoffelOfDerivs (traceReverseDerivs fun c a b => k c * A a b) =
      Wave.planeChristoffel k (traceReverse .timeNegative A) := by
  have h : ∀ c, (Matrix.of fun e f => k c * A e f) = k c • A := fun c => by
    ext e f
    simp
  funext c i j
  simp only [christoffelOfDerivs, traceReverseDerivs, h, traceReverse_smul, Matrix.smul_apply,
    smul_eq_mul, Wave.planeChristoffel]

/-! ### The far zone of the derivatives -/

/-- The derivatives of the retarded perturbation are those of the retarded integrals. -/
theorem fderiv_retardedPerturbation_eq (hT : LocalizedStress T a) (x : Spacetime) (i k c : Fin 4) :
    fderiv ℝ (fun z => retardedPerturbation κ T z i k) x (Pi.single c 1) =
      2 * κ * partialAt (retardedScalar fun w => T w i k) c x := by
  have hc : ContDiff ℝ ∞ (retardedScalar fun w => T w i k) :=
    contDiff_retardedScalar (hT.contDiff i k) (hT.subluminalSupport i k)
  simp only [retardedPerturbation_apply]
  rw [fderiv_const_mul ((hc.differentiable (by simp)) x), _root_.smul_apply, smul_eq_mul]
  rfl

/-- **The amplitude of the far field** of `∂ₜh̄_{ab}`:
`Ā_{ab}(u, n) = 2κ (1/4π) ∫ ∂ₜT_{ab}(u + ⟨n, y⟩, y) dy`. -/
def gravitationalAmplitude (κ : ℝ) (T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (u : ℝ) (n : E3) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i k => 2 * κ * Wave.farAmplitude (Wave.timeDeriv (splitStress T i k)) u n

theorem waveCovector_zero (n : E3) : Wave.waveCovector n 0 = 1 := rfl

theorem waveCovector_succ (n : E3) (γ : Fin 3) : Wave.waveCovector n γ.succ = -n γ := by
  fin_cases γ <;> rfl

/-- **The far zone of the derivatives**: `R ∂_c h̄_{ab}(u + R, Rn) → k_c Ā_{ab}(u, n)` with the
null covector `k = (1, −n)`, uniformly for `u` in a compact set and `n` on the unit sphere. -/
theorem tendstoUniformlyOn_mul_fderiv_retardedPerturbation (hT : LocalizedStress T a)
    {K : Set ℝ} (hK : IsCompact K) (i k c : Fin 4) :
    TendstoUniformlyOn
      (fun R (p : ℝ × E3) => R * fderiv ℝ (fun z => retardedPerturbation κ T z i k)
        (vector (p.1 + R) (R • p.2)) (Pi.single c 1))
      (fun p => Wave.waveCovector p.2 c * gravitationalAmplitude κ T p.1 p.2 i k) atTop
      (K ×ˢ sphere (0 : E3) 1) := by
  have hc1 : ContDiff ℝ 1 (splitStress T i k) := (hT.contDiff_split i k).of_le (by simp)
  have hg1 : ContDiff ℝ 1 fun w => T w i k := (hT.contDiff i k).of_le (by simp)
  simp only [fderiv_retardedPerturbation_eq hT]
  refine Fin.cases ?_ (fun γ => ?_) c
  · have h := tendstoUniformlyOn_const_mul (Wave.tendstoUniformlyOn_mul_timeDeriv_retardedIntegral
      hc1 (hT.localizedSupport i k) hK) (2 * κ)
    refine (h.congr (Eventually.of_forall fun R p _ => ?_)).congr_right fun p _ => ?_
    · simp only [partialAt_retardedScalar_zero hg1 (hT.subluminalSupport i k),
        Wave.timeSpaceEquiv_apply, vector_zero, space_vector]
      rw [show (fun p : ℝ × E3 => T (Wave.timeSpaceEquiv.symm p) i k) = splitStress T i k from rfl]
      ring
    · simp only [waveCovector_zero, gravitationalAmplitude, Matrix.of_apply, one_mul]
  · have h := tendstoUniformlyOn_const_mul (Wave.tendstoUniformlyOn_mul_spaceDeriv_retardedIntegral
      hc1 (hT.localizedSupport i k) hK γ) (2 * κ)
    refine (h.congr (Eventually.of_forall fun R p _ => ?_)).congr_right fun p _ => ?_
    · simp only [partialAt_retardedScalar_succ hg1 (hT.subluminalSupport i k),
        Wave.timeSpaceEquiv_apply, vector_zero, space_vector]
      rw [show (fun p : ℝ × E3 => T (Wave.timeSpaceEquiv.symm p) i k) = splitStress T i k from rfl]
      ring
    · simp only [waveCovector_succ, gravitationalAmplitude, Matrix.of_apply]
      ring

/-- The far amplitude is linear in finite sums. -/
theorem farAmplitude_finsetSum {ι : Type*} (s : Finset ι) {f : ι → ℝ × E3 → ℝ}
    (hc : ∀ i ∈ s, Continuous (f i)) (hl : ∀ i ∈ s, Wave.LocalizedSupport a (f i)) (u : ℝ)
    (n : E3) :
    Wave.farAmplitude (fun p => ∑ i ∈ s, f i p) u n = ∑ i ∈ s, Wave.farAmplitude (f i) u n := by
  simp only [Wave.farAmplitude]
  rw [integral_finsetSum s fun i hi => Wave.integrable_farIntegrand (hc i hi) (hl i hi) u n,
    Finset.mul_sum]

/-- **The harmonic gauge of the far field**: by the conservation of the source,
`Ā_{0b} = −Σ_α n_α Ā_{αb}` (the gauge `k^a Ā_{ab} = 0` with `k = (1, −n)`). -/
theorem gravitationalAmplitude_gauge (hT : LocalizedStress T a) (u : ℝ) (n : E3) (b : Fin 4) :
    gravitationalAmplitude κ T u n 0 b =
      -∑ α : Fin 3, n α * gravitationalAmplitude κ T u n α.succ b := by
  have hd : ∀ i k, Differentiable ℝ fun w => T w i k := fun i k =>
    (hT.contDiff i k).differentiable (by simp)
  have hcons : Wave.timeDeriv (splitStress T 0 b) =
      fun p => ∑ γ : Fin 3, Wave.spaceDeriv γ (splitStress T γ.succ b) p := by
    funext p
    have h := hT.conserved (Wave.timeSpaceEquiv.symm p) b
    rw [Fin.sum_univ_succ] at h
    simp only [lorentzSign_zero, lorentzSign_succ, one_mul] at h
    have e1 : Wave.timeDeriv (splitStress T 0 b) p =
        partialAt (fun w => T w 0 b) 0 (Wave.timeSpaceEquiv.symm p) :=
      timeDeriv_comp_symm (hd 0 b) p
    have e2 : ∀ γ : Fin 3, Wave.spaceDeriv γ (splitStress T γ.succ b) p =
        partialAt (fun w => T w γ.succ b) γ.succ (Wave.timeSpaceEquiv.symm p) := fun γ =>
      spaceDeriv_comp_symm (hd γ.succ b) γ p
    rw [e1]
    simp only [e2, partialAt]
    linarith
  have hc1 : ∀ γ : Fin 3, ContDiff ℝ 1 (splitStress T γ.succ b) := fun γ =>
    (hT.contDiff_split γ.succ b).of_le (by simp)
  simp only [gravitationalAmplitude, Matrix.of_apply]
  rw [hcons, farAmplitude_finsetSum Finset.univ
    (fun γ _ => (Wave.contDiff_spaceDeriv (n := 0) (by simpa using hc1 γ) γ).continuous)
    (fun γ _ => (hT.localizedSupport γ.succ b).spaceDeriv γ)]
  simp only [Wave.farAmplitude_spaceDeriv (hc1 _) (hT.localizedSupport _ b), Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun γ _ => ?_
  ring

/-- The amplitude of the far field of a symmetric source is symmetric. -/
theorem gravitationalAmplitude_symm (hT : LocalizedStress T a) (u : ℝ) (n : E3) (i k : Fin 4) :
    gravitationalAmplitude κ T u n i k = gravitationalAmplitude κ T u n k i := by
  simp only [gravitationalAmplitude, Matrix.of_apply]
  congr 3
  funext p
  exact hT.symm _ _ _

/-! ### The flux of energy -/

/-- **The power radiated in gravitational waves** at the retarded time `u`:
`(1/κ) ∫ ¼ Σ (ΛĀ)² dσ`, with the transverse-traceless square `ttSquare n Ā = Σ (ΛĀ)²` of the
spatial components of the amplitude `Ā` of `∂ₜh̄` (Landau–Lifshitz, §§107, 110). -/
def gravitationalPower (κ : ℝ) (T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ) (u : ℝ) : ℝ :=
  ∫ n : sphere (0 : E3) 1, Wave.ttSquare (n : E3)
    (fun α β => gravitationalAmplitude κ T u n α.succ β.succ) / (4 * κ) ∂sphereMeasure

/-- The radial flux `(1/κ) t^{0α}_{(2)} n_α` as a function of the array `d_{cab} = ∂_c h̄_{ab}` of
derivatives and of the direction `n`. -/
def fluxIntegrand (κ : ℝ) (q : (Fin 4 → Fin 4 → Fin 4 → ℝ) × E3) : ℝ :=
  (∑ α : Fin 3, pseudoBraces (fun a b : Fin 4 => Minkowski.metricMatrix .timeNegative 3 a b)
    (christoffelOfDerivs (traceReverseDerivs q.1)) 0 α.succ * q.2 α) / 2 / κ

theorem continuous_fluxIntegrand (κ : ℝ) : Continuous (fluxIntegrand κ) := by
  have hΓ : Continuous fun q : (Fin 4 → Fin 4 → Fin 4 → ℝ) × E3 =>
      christoffelOfDerivs (traceReverseDerivs q.1) :=
    continuous_pi fun k => continuous_pi fun i => continuous_pi fun j => by
      simp only [christoffelOfDerivs, traceReverseDerivs, traceReverse_apply, flatTrace,
        Matrix.of_apply]
      fun_prop
  unfold fluxIntegrand
  refine (continuous_finsetSum _ fun α _ =>
    ((Wave.continuous_pseudoBraces _ 0 α.succ).comp hΓ).mul ?_).div_const _ |>.div_const _
  exact (EuclideanSpace.proj (𝕜 := ℝ) α).continuous.comp continuous_snd

/-- The flux of a plane wave: for `d_{cab} = k_c Ā_{ab}`, the integrand is the flux
`planeFlux n (Ā − ½ η tr Ā)` divided by `κ`. -/
theorem fluxIntegrand_plane (κ : ℝ) (n : E3) (A : Matrix (Fin 4) (Fin 4) ℝ) :
    fluxIntegrand κ (fun c i k => Wave.waveCovector n c * A i k, n) =
      Wave.planeFlux n (traceReverse .timeNegative A) / κ := by
  simp only [fluxIntegrand, christoffelOfDerivs_plane, Wave.planeFlux]

/-- **The scaling of the flux**: `R² (1/κ) t^{0α}_{(2)} n_α` at a point is the integrand of the
array `R ∂_c h̄_{ab}`, since the braces are quadratic. -/
theorem fluxIntegrand_mul (hT : LocalizedStress T a) (R : ℝ) (x : Spacetime) (n : E3) :
    R ^ 2 * ∑ α : Fin 3, quadraticPseudotensor (metricPerturbation κ T) x 0 α.succ / κ * n α =
      fluxIntegrand κ (fun c i k => R * fderiv ℝ (fun z => retardedPerturbation κ T z i k) x
        (Pi.single c 1), n) := by
  have hΓ : christoffelOfDerivs (traceReverseDerivs fun c i k =>
      fderiv ℝ (fun z => retardedPerturbation κ T z i k) x (Pi.single c 1)) =
        linearizedChristoffel .timeNegative (metricPerturbation κ T) x := by
    funext k i j
    rw [linearizedChristoffel_eq]
    simp only [fderiv_metricPerturbation hT]
  simp only [fluxIntegrand, traceReverseDerivs_mul, christoffelOfDerivs_mul, Wave.pseudoBraces_mul,
    hΓ, quadraticPseudotensor]
  rw [Finset.mul_sum, Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

/-- The direction cosines of a unit vector are at most `1`. -/
theorem abs_waveCovector_le {n : E3} (hn : n ∈ sphere (0 : E3) 1) (c : Fin 4) :
    |Wave.waveCovector n c| ≤ 1 := by
  refine Fin.cases ?_ (fun γ => ?_) c
  · simp [waveCovector_zero]
  · rw [waveCovector_succ, abs_neg]
    exact abs_apply_le_one hn γ

/-- **The flux of energy through large spheres** (Landau–Lifshitz, §110): for a localized stress
tensor, the flux `R² ∫ (1/κ) t^{0α}_{(2)} n_α dσ` of the quadratic pseudotensor of the metric
perturbation through the sphere of radius `R` at the time `u + R` tends to the radiated power
`gravitationalPower κ T u = (1/κ) ∫ ¼ Σ (ΛĀ)² dσ`. -/
theorem tendsto_pseudotensorFlux (hT : LocalizedStress T a) (u : ℝ) :
    Tendsto (fun R => sphereFlux
        (fun α v => quadraticPseudotensor (metricPerturbation κ T) v 0 α.succ / κ) (u + R) R)
      atTop (𝓝 (gravitationalPower κ T u)) := by
  set D : ℝ → E3 → Fin 4 → Fin 4 → Fin 4 → ℝ := fun R n c i k =>
    R * fderiv ℝ (fun z => retardedPerturbation κ T z i k) (vector (u + R) (R • n))
      (Pi.single c 1) with hD
  set L : E3 → Fin 4 → Fin 4 → Fin 4 → ℝ := fun n c i k =>
    Wave.waveCovector n c * gravitationalAmplitude κ T u n i k with hL
  have hU := fun c i k => tendstoUniformlyOn_mul_fderiv_retardedPerturbation (κ := κ) hT
    (isCompact_singleton (x := u)) i k c
  -- pointwise limits
  have hP : ∀ n ∈ sphere (0 : E3) 1, Tendsto (fun R => D R n) atTop (𝓝 (L n)) := fun n hn =>
    tendsto_pi_nhds.2 fun c => tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun k =>
      (hU c i k).tendsto_at (x := (u, n)) ⟨rfl, hn⟩
  -- a uniform bound
  have hB1 : ∀ c i k, ∃ M, ∀ᶠ R in atTop, ∀ n ∈ sphere (0 : E3) 1, |D R n c i k| ≤ M := by
    intro c i k
    have hc0 : Continuous (Wave.timeDeriv (splitStress T i k)) :=
      (Wave.contDiff_timeDeriv (n := 0) (by
        simpa using (hT.contDiff_split i k).of_le (by simp : (1 : ℕ∞ω) ≤ ∞))).continuous
    obtain ⟨B, hB⟩ := Wave.exists_bound_farAmplitude hc0 (hT.localizedSupport i k).timeDeriv
      (isCompact_singleton (x := u))
    refine ⟨2 * |κ| * |B| + 1, ?_⟩
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hU c i k) 1 one_pos] with R hR n hn
    have h1 := hR (u, n) ⟨rfl, hn⟩
    rw [Real.dist_eq] at h1
    have h2 : |L n c i k| ≤ 2 * |κ| * |B| := by
      simp only [hL, gravitationalAmplitude, Matrix.of_apply, abs_mul, abs_two]
      have := hB u rfl n hn
      have h3 := abs_waveCovector_le hn c
      have h4 : |Wave.farAmplitude (Wave.timeDeriv (splitStress T i k)) u n| ≤ |B| :=
        this.trans (le_abs_self B)
      calc |Wave.waveCovector n c| * (2 * |κ| *
            |Wave.farAmplitude (Wave.timeDeriv (splitStress T i k)) u n|)
          ≤ 1 * (2 * |κ| * |B|) := mul_le_mul h3 (by gcongr) (by positivity) zero_le_one
        _ = 2 * |κ| * |B| := one_mul _
    have h5 := abs_sub_abs_le_abs_sub (D R n c i k) (L n c i k)
    rw [abs_sub_comm] at h5
    simp only [hD, hL] at h1 h2 h5 ⊢
    linarith
  choose M hM using hB1
  set M₀ : ℝ := ∑ c, ∑ i, ∑ k, |M c i k| with hM₀
  have hM₀0 : 0 ≤ M₀ := by positivity
  have hle : ∀ c i k, M c i k ≤ M₀ := fun c i k =>
    calc M c i k ≤ |M c i k| := le_abs_self _
      _ ≤ ∑ k, |M c i k| := Finset.single_le_sum (f := fun k => |M c i k|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
      _ ≤ ∑ i, ∑ k, |M c i k| := Finset.single_le_sum (f := fun i => ∑ k, |M c i k|)
          (fun _ _ => by positivity) (Finset.mem_univ i)
      _ ≤ M₀ := Finset.single_le_sum (f := fun c => ∑ i, ∑ k, |M c i k|)
          (fun _ _ => by positivity) (Finset.mem_univ c)
  have hball : ∀ᶠ R in atTop, ∀ n ∈ sphere (0 : E3) 1,
      D R n ∈ closedBall (0 : Fin 4 → Fin 4 → Fin 4 → ℝ) M₀ := by
    filter_upwards [eventually_all.2 fun c => eventually_all.2 fun i => eventually_all.2 fun k =>
      hM c i k] with R hR n hn
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg hM₀0).2 fun c => (pi_norm_le_iff_of_nonneg hM₀0).2 fun i =>
      (pi_norm_le_iff_of_nonneg hM₀0).2 fun k => ?_
    rw [Real.norm_eq_abs]
    exact (hR c i k n hn).trans (hle c i k)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : Fin 4 → Fin 4 → Fin 4 → ℝ) M₀).prod
    (isCompact_sphere (0 : E3) 1)).exists_bound_of_continuousOn
      (continuous_fluxIntegrand κ).continuousOn
  -- the flux as an integral of the integrand
  have hflux : (fun R => sphereFlux
      (fun α v => quadraticPseudotensor (metricPerturbation κ T) v 0 α.succ / κ) (u + R) R) =
      fun R => ∫ n : sphere (0 : E3) 1, fluxIntegrand κ (D R n, n) ∂sphereMeasure := by
    funext R
    rw [sphereFlux, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun n => ?_)
    exact fluxIntegrand_mul hT R _ _
  -- the limit
  have hlim : gravitationalPower κ T u =
      ∫ n : sphere (0 : E3) 1, fluxIntegrand κ (L n, n) ∂sphereMeasure := by
    unfold gravitationalPower
    refine integral_congr_ae (Eventually.of_forall fun n => ?_)
    simp only [hL]
    rw [fluxIntegrand_plane, Wave.planeFlux_traceReverse (mem_sphere_zero_iff_norm.mp n.2)
      (gravitationalAmplitude_symm hT u n) (gravitationalAmplitude_gauge hT u n)]
    ring
  rw [hflux, hlim]
  have hDc : ∀ R, Continuous fun n : sphere (0 : E3) 1 => D R n := fun R =>
    continuous_pi fun c => continuous_pi fun i => continuous_pi fun k => by
      have hf : Continuous fun x : Spacetime =>
          fderiv ℝ (fun z => retardedPerturbation κ T z i k) x (Pi.single c 1) :=
        ((contDiff_retardedPerturbation hT i k).continuous_fderiv (by simp)).clm_apply
          continuous_const
      have hv : Continuous fun n : sphere (0 : E3) 1 => vector (u + R) (R • (n : E3)) :=
        Wave.timeSpaceEquiv.symm.continuous.comp
          (continuous_const.prodMk (continuous_subtype_val.const_smul R))
      exact continuous_const.mul (hf.comp hv)
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    (Eventually.of_forall fun R => ((continuous_fluxIntegrand κ).comp
      ((hDc R).prodMk continuous_subtype_val)).aestronglyMeasurable) ?_ (integrable_const C) ?_
  · filter_upwards [hball] with R hR
    exact Eventually.of_forall fun n => hC _ ⟨hR n n.2, n.2⟩
  · refine Eventually.of_forall fun n => ?_
    exact ((continuous_fluxIntegrand κ).tendsto _).comp
      ((hP n n.2).prodMk_nhds tendsto_const_nhds)

/-! ### The quadrupole formula -/

/-- **The third derivative of the second moment**: `I⃛_{αβ}(s) = 2 ∫ ∂ₜT_{αβ}(s, y) dy`. -/
theorem deriv_deriv_deriv_secondMoment (hT : LocalizedStress T a) (α β : Fin 3) (s : ℝ) :
    deriv (deriv (deriv fun s => secondMoment T s α β)) s =
      2 * ∫ y : E3, fderiv ℝ (fun w => T w α.succ β.succ) (vector s y) (Pi.single 0 1) := by
  have h1 : deriv (deriv fun s => secondMoment T s α β) =
      fun s => 2 * ∫ y : E3, T (vector s y) α.succ β.succ :=
    funext fun s => by rw [integral_stress_eq_moment hT]; ring
  rw [h1]
  have hF : Continuous (Function.uncurry fun s (y : E3) => T (vector s y) α.succ β.succ) :=
    continuous_comp_vector_slice (hT.contDiff α.succ β.succ).continuous
  have hF' : Continuous (Function.uncurry fun s (y : E3) =>
      fderiv ℝ (fun w => T w α.succ β.succ) (vector s y) (Pi.single 0 1)) :=
    continuous_comp_vector_slice
      (((hT.contDiff α.succ β.succ).continuous_fderiv (by simp)).clm_apply continuous_const)
  have h := hasDerivAt_integral_of_ballSupport (a := a) hF hF'
    (fun s y hy => hT.apply_eq_zero hy _ _)
    (fun s y hy => by
      rw [fderiv_eq_zero_of_ballSupport (F := fun w => T w α.succ β.succ)
        (fun t x hx => hT.apply_eq_zero hx _ _) hy]
      rfl)
    (fun s y => hasDerivAt_comp_vector_time
      ((hT.contDiff α.succ β.succ).differentiable (by simp) _)) s
  exact (h.const_mul 2).deriv

/-- The time derivative of a spatial component of the slow family:
`∂ₜT^ε_{αβ}(t, x) = ε³ (∂ₜT_{αβ})(εt, x)`. -/
theorem timeDeriv_splitStress_slow (hT : LocalizedStress T a) (ε : ℝ) (α β : Fin 3)
    (p : ℝ × E3) :
    Wave.timeDeriv (splitStress (slowStress ε T) α.succ β.succ) p =
      ε ^ 3 * fderiv ℝ (fun w => T w α.succ β.succ) (vector (ε * p.1) p.2) (Pi.single 0 1) := by
  have hd : Differentiable ℝ fun w => slowStress ε T w α.succ β.succ :=
    ((hT.slow ε).contDiff α.succ β.succ).differentiable (by simp)
  have e : Wave.timeDeriv (splitStress (slowStress ε T) α.succ β.succ) p =
      partialAt (fun w => slowStress ε T w α.succ β.succ) 0 (Wave.timeSpaceEquiv.symm p) :=
    timeDeriv_comp_symm hd p
  rw [e, partialAt, fderiv_slowStress hT, Wave.timeSpaceEquiv_symm_apply, timeDilation_vector]
  simp only [indexScale, Fin.succ_ne_zero, ite_false, ite_true]
  ring

/-- The amplitude of the far field of the slow family: `Ā^ε_{αβ}(u, n) = 2κ (1/4π) ε³ Φ_{αβ}(n)`
with `Φ_{αβ}(n) = ∫ ∂ₜT_{αβ}(εu + ε⟨n, y⟩, y) dy`. -/
theorem gravitationalAmplitude_slow (hT : LocalizedStress T a) (ε u : ℝ) (n : E3)
    (α β : Fin 3) :
    gravitationalAmplitude κ (slowStress ε T) u n α.succ β.succ =
      2 * κ * (4 * π)⁻¹ * ε ^ 3 * ∫ y : E3,
        fderiv ℝ (fun w => T w α.succ β.succ) (vector (ε * u + ε * inner ℝ n y) y)
          (Pi.single 0 1) := by
  simp only [gravitationalAmplitude, Matrix.of_apply, Wave.farAmplitude,
    timeDeriv_splitStress_slow hT, mul_add, integral_const_mul]
  ring

/-- `c²/4κ = κ ε⁶/16π²` for `c = 2κ (1/4π) ε³`, also for `κ = 0`. -/
theorem slow_coefficient (κ ε : ℝ) :
    (2 * κ * (4 * π)⁻¹ * ε ^ 3) ^ 2 / (4 * κ) = κ * ε ^ 6 / (16 * π ^ 2) := by
  by_cases hκ : κ = 0
  · simp [hκ]
  · field_simp
    ring

/-- **The quadrupole formula** (Landau–Lifshitz, (110.16)): for the slow family of a localized
stress tensor with `|∂ₜT_{αβ}| ≤ M₁` and `|∂ₜ²T_{αβ}| ≤ M₂`, the radiated power is
`−dE/dt = (κ/8π)(1/45) ε⁶ Σ D⃛_{αβ}²(εu) = κ ε⁶/(360π) Σ D⃛²` up to `120π |κ| M₁ M₂ a⁷ ε⁷`, with
the quadrupole moment `D = 3I − δ tr I` of the second moment `I_{αβ} = ∫ T₀₀ y_α y_β dy`. With
`κ = 8πk/c⁴` this is `(k/45c⁵) D⃛²`. -/
theorem gravitationalPower_slow (hT : LocalizedStress T a) {M₁ M₂ : ℝ}
    (hM₁ : ∀ (α β : Fin 3) (v : Spacetime),
      |fderiv ℝ (fun w => T w α.succ β.succ) v (Pi.single 0 1)| ≤ M₁)
    (hM₂ : ∀ (α β : Fin 3) (v : Spacetime), |fderiv ℝ (fun w =>
      fderiv ℝ (fun w => T w α.succ β.succ) w (Pi.single 0 1)) v (Pi.single 0 1)| ≤ M₂)
    {ε : ℝ} (hε : 0 ≤ ε) (u : ℝ) :
    |gravitationalPower κ (slowStress ε T) u - κ * ε ^ 6 / (360 * π) *
        ∑ α, ∑ β, Wave.quadrupoleOf
          (fun α β => deriv (deriv (deriv fun s => secondMoment T s α β)) (ε * u)) α β ^ 2| ≤
      120 * π * |κ| * M₁ * M₂ * a ^ 7 * ε ^ 7 := by
  set G : Fin 3 → Fin 3 → Spacetime → ℝ := fun α β v =>
    fderiv ℝ (fun w => T w α.succ β.succ) v (Pi.single 0 1) with hG
  set Φ : E3 → Fin 3 → Fin 3 → ℝ := fun n α β =>
    ∫ y : E3, G α β (vector (ε * u + ε * inner ℝ n y) y) with hΦ
  set Φ₀ : Fin 3 → Fin 3 → ℝ := fun α β => ∫ y : E3, G α β (vector (ε * u) y) with hΦ₀
  set c : ℝ := 2 * κ * (4 * π)⁻¹ * ε ^ 3 with hc
  set V : ℝ := 4 * π / 3 * a ^ 3 with hV
  have ha := hT.radius_nonneg
  have hM₁0 : 0 ≤ M₁ := (abs_nonneg _).trans (hM₁ 0 0 0)
  have hM₂0 : 0 ≤ M₂ := (abs_nonneg _).trans (hM₂ 0 0 0)
  have hGc : ∀ α β, ContDiff ℝ 1 (G α β) := fun α β =>
    ((hT.contDiff α.succ β.succ).fderiv_right (m := 1) (by simp)).clm_apply contDiff_const
  have hGs : ∀ α β (t : ℝ) (x : E3), a < ‖x‖ → G α β (vector t x) = 0 := fun α β t x hx => by
    simp only [hG]
    rw [fderiv_eq_zero_of_ballSupport (F := fun w => T w α.succ β.succ)
      (fun t x hx => hT.apply_eq_zero hx _ _) hx]
    rfl
  have hGsymm : ∀ α β v, G α β v = G β α v := fun α β v => by
    simp only [hG]
    congr 2
    funext w
    exact hT.symm w _ _
  -- the amplitude and the power
  have hA : ∀ n : E3, (fun α β => gravitationalAmplitude κ (slowStress ε T) u n α.succ β.succ) =
      fun α β => c * Φ n α β := fun n => funext fun α => funext fun β =>
    gravitationalAmplitude_slow hT ε u n α β
  have hΦc : Continuous fun n : sphere (0 : E3) 1 => Φ n := continuous_pi fun α =>
    continuous_pi fun β => (continuous_integral_of_ballSupport (a := a)
      (F := fun (n : E3) (y : E3) => G α β (vector (ε * u + ε * inner ℝ n y) y))
      ((hGc α β).continuous.comp (continuous_vector_of_continuous (by fun_prop) continuous_snd))
      fun n y hy => hGs α β _ y hy).comp continuous_subtype_val
  have httc : ∀ {S : sphere (0 : E3) 1 → Fin 3 → Fin 3 → ℝ}, Continuous S →
      Continuous fun n : sphere (0 : E3) 1 => Wave.ttSquare (n : E3) (S n) := by
    intro S hS
    have hS' : ∀ i j, Continuous fun n => S n i j := fun i j =>
      (continuous_apply j).comp ((continuous_apply i).comp hS)
    have hn : ∀ i : Fin 3, Continuous fun n : sphere (0 : E3) 1 => (n : E3) i := fun i =>
      (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp continuous_subtype_val
    simp only [Wave.ttSquare]
    fun_prop
  have hP : gravitationalPower κ (slowStress ε T) u =
      κ * ε ^ 6 / (16 * π ^ 2) * ∫ n : sphere (0 : E3) 1, Wave.ttSquare (n : E3) (Φ n)
        ∂sphereMeasure := by
    rw [← slow_coefficient, ← integral_const_mul]
    unfold gravitationalPower
    refine integral_congr_ae (Eventually.of_forall fun n => ?_)
    simp only [hA, Wave.ttSquare_mul]
    ring
  -- the main term
  have hΦ₀s : ∀ α β, Φ₀ α β = Φ₀ β α := fun α β => by
    simp only [hΦ₀, hGsymm α β]
  have hmain : ∑ α, ∑ β, Wave.quadrupoleOf
      (fun α β => deriv (deriv (deriv fun s => secondMoment T s α β)) (ε * u)) α β ^ 2 =
        4 * ∑ α, ∑ β, Wave.quadrupoleOf Φ₀ α β ^ 2 := by
    simp only [deriv_deriv_deriv_secondMoment hT]
    simp only [Wave.quadrupoleOf, Fin.sum_univ_three, hΦ₀, hG, Fin.isValue, Fin.reduceEq,
      ite_true, ite_false]
    ring
  have hI0 := Wave.integral_ttSquare hΦ₀s
  -- the bounds
  have hb1 : ∀ n : E3, ∀ α β, |Φ n α β| ≤ M₁ * V := fun n α β => by
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_of_ballSupport ha (fun y hy => hGs α β _ y hy)
      fun y _ => by rw [Real.norm_eq_abs]; exact hM₁ α β _
  have hb0 : ∀ α β, |Φ₀ α β| ≤ M₁ * V := fun α β => by
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_of_ballSupport ha (fun y hy => hGs α β _ y hy)
      fun y _ => by rw [Real.norm_eq_abs]; exact hM₁ α β _
  have hbd : ∀ n : E3, ‖n‖ = 1 → ∀ α β, |Φ n α β - Φ₀ α β| ≤ M₂ * (ε * a) * V :=
    fun n hn α β => abs_integral_delay_sub_le (hGc α β) ha (hGs α β) (hM₂ α β)
      (τ := fun y => ε * inner ℝ n y) (by fun_prop) (fun y hy => by
        rw [abs_mul, abs_of_nonneg hε]
        refine mul_le_mul_of_nonneg_left ?_ hε
        exact (abs_real_inner_le_norm n y).trans (by rw [hn, one_mul]; exact hy)) (ε * u)
  have hpt : ∀ n : sphere (0 : E3) 1,
      ‖Wave.ttSquare (n : E3) (Φ n) - Wave.ttSquare (n : E3) Φ₀‖ ≤
        270 * (M₁ * V) * (M₂ * (ε * a) * V) := fun n => by
    rw [Real.norm_eq_abs]
    exact Wave.abs_ttSquare_sub_le (abs_apply_le_one n.2) (hb1 n) hb0
      (hbd n (mem_sphere_zero_iff_norm.mp n.2))
  have hint1 : Integrable (fun n : sphere (0 : E3) 1 => Wave.ttSquare (n : E3) (Φ n))
      sphereMeasure := integrable_of_continuous (httc hΦc)
  have hint2 : Integrable (fun n : sphere (0 : E3) 1 => Wave.ttSquare (n : E3) Φ₀)
      sphereMeasure := integrable_of_continuous (httc continuous_const)
  rw [hP, hmain]
  have e : κ * ε ^ 6 / (16 * π ^ 2) * (∫ n : sphere (0 : E3) 1, Wave.ttSquare (n : E3) (Φ n)
      ∂sphereMeasure) - κ * ε ^ 6 / (360 * π) * (4 * (45 / (8 * π) *
        ∫ n : sphere (0 : E3) 1, Wave.ttSquare (n : E3) Φ₀ ∂sphereMeasure)) =
      κ * ε ^ 6 / (16 * π ^ 2) * ∫ n : sphere (0 : E3) 1,
        (Wave.ttSquare (n : E3) (Φ n) - Wave.ttSquare (n : E3) Φ₀) ∂sphereMeasure := by
    rw [integral_sub hint1 hint2]
    field_simp
    ring
  have hI0' : ∑ α, ∑ β, Wave.quadrupoleOf Φ₀ α β ^ 2 = 45 / (8 * π) *
      ∫ n : sphere (0 : E3) 1, Wave.ttSquare (n : E3) Φ₀ ∂sphereMeasure := by
    rw [hI0]
    field_simp
  rw [hI0', e, abs_mul]
  have hk : |κ * ε ^ 6 / (16 * π ^ 2)| = |κ| * ε ^ 6 / (16 * π ^ 2) := by
    rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 6),
      abs_of_pos (by positivity : (0 : ℝ) < 16 * π ^ 2)]
  rw [hk]
  have hint := norm_integral_le_of_norm_le_const (μ := sphereMeasure) (Eventually.of_forall hpt)
  rw [sphereMeasure_real_univ, Real.norm_eq_abs] at hint
  calc |κ| * ε ^ 6 / (16 * π ^ 2) * |∫ n : sphere (0 : E3) 1,
        (Wave.ttSquare (n : E3) (Φ n) - Wave.ttSquare (n : E3) Φ₀) ∂sphereMeasure|
      ≤ |κ| * ε ^ 6 / (16 * π ^ 2) * (270 * (M₁ * V) * (M₂ * (ε * a) * V) * (4 * π)) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = 120 * π * |κ| * M₁ * M₂ * a ^ 7 * ε ^ 7 := by
        simp only [hV]
        field_simp
        ring

/-- **The flux of the slow family tends to the quadrupole formula**: the flux of the quadratic
pseudotensor through the sphere of radius `R` at the time `u + R` tends to a power `P` with
`|P − κ ε⁶/(360π) Σ D⃛²(εu)| ≤ 120π |κ| M₁ M₂ a⁷ ε⁷` (Landau–Lifshitz, (110.16)). -/
theorem tendsto_pseudotensorFlux_slow (hT : LocalizedStress T a) {M₁ M₂ : ℝ}
    (hM₁ : ∀ (α β : Fin 3) (v : Spacetime),
      |fderiv ℝ (fun w => T w α.succ β.succ) v (Pi.single 0 1)| ≤ M₁)
    (hM₂ : ∀ (α β : Fin 3) (v : Spacetime), |fderiv ℝ (fun w =>
      fderiv ℝ (fun w => T w α.succ β.succ) w (Pi.single 0 1)) v (Pi.single 0 1)| ≤ M₂)
    {ε : ℝ} (hε : 0 ≤ ε) (u : ℝ) :
    ∃ P, Tendsto (fun R => sphereFlux (fun α v =>
        quadraticPseudotensor (metricPerturbation κ (slowStress ε T)) v 0 α.succ / κ) (u + R) R)
      atTop (𝓝 P) ∧
      |P - κ * ε ^ 6 / (360 * π) * ∑ α, ∑ β, Wave.quadrupoleOf
          (fun α β => deriv (deriv (deriv fun s => secondMoment T s α β)) (ε * u)) α β ^ 2| ≤
        120 * π * |κ| * M₁ * M₂ * a ^ 7 * ε ^ 7 :=
  ⟨_, tendsto_pseudotensorFlux (hT.slow ε) u, gravitationalPower_slow hT hM₁ hM₂ hε u⟩

/-! ### A circular binary -/

/-- The relative orbit `x(t) = a (cos Ωt, sin Ωt, 0)` of a circular binary. -/
def binaryOrbit (a Ω t : ℝ) : Fin 3 → ℝ := ![a * cos (Ω * t), a * sin (Ω * t), 0]

/-- The second moment `I_{αβ} = μ x_α x_β` of a circular binary of reduced mass `μ` in its
centre-of-mass frame (Landau–Lifshitz, §110, problem 1). -/
def binaryMoment (μ a Ω t : ℝ) (α β : Fin 3) : ℝ :=
  μ * (binaryOrbit a Ω t α * binaryOrbit a Ω t β)

/-- The third derivative of a function given by a chain of derivatives. -/
theorem deriv_deriv_deriv_of_hasDerivAt {f f₁ f₂ f₃ : ℝ → ℝ}
    (h₁ : ∀ t, HasDerivAt f (f₁ t) t) (h₂ : ∀ t, HasDerivAt f₁ (f₂ t) t)
    (h₃ : ∀ t, HasDerivAt f₂ (f₃ t) t) (t : ℝ) : deriv (deriv (deriv f)) t = f₃ t := by
  rw [show deriv f = f₁ from funext fun t => (h₁ t).deriv,
    show deriv f₁ = f₂ from funext fun t => (h₂ t).deriv, (h₃ t).deriv]

private theorem hasDerivAt_cos_mul (k t : ℝ) :
    HasDerivAt (fun t => cos (k * t)) (-(k * sin (k * t))) t := by
  have h := (hasDerivAt_id t).const_mul k |>.cos
  simp only [mul_one, id] at h
  convert h using 1
  ring

private theorem hasDerivAt_sin_mul (k t : ℝ) :
    HasDerivAt (fun t => sin (k * t)) (k * cos (k * t)) t := by
  have h := (hasDerivAt_id t).const_mul k |>.sin
  simp only [mul_one, id] at h
  convert h using 1
  ring

/-- The third derivative of `c cos(kt)` is `c k³ sin(kt)`. -/
private theorem deriv3_cos (c k t : ℝ) :
    deriv (deriv (deriv fun t => c * cos (k * t))) t = c * k ^ 3 * sin (k * t) := by
  refine deriv_deriv_deriv_of_hasDerivAt (f := fun t => c * cos (k * t))
    (f₁ := fun t => -(c * k) * sin (k * t)) (f₂ := fun t => -(c * k ^ 2) * cos (k * t))
    (f₃ := fun t => c * k ^ 3 * sin (k * t)) (fun t => ?_) (fun t => ?_) (fun t => ?_) t
  · convert (hasDerivAt_cos_mul k t).const_mul c using 1
    ring
  · convert (hasDerivAt_sin_mul k t).const_mul (-(c * k)) using 1
    ring
  · convert (hasDerivAt_cos_mul k t).const_mul (-(c * k ^ 2)) using 1
    ring

/-- The third derivative of `c sin(kt)` is `−c k³ cos(kt)`. -/
private theorem deriv3_sin (c k t : ℝ) :
    deriv (deriv (deriv fun t => c * sin (k * t))) t = -(c * k ^ 3 * cos (k * t)) := by
  refine deriv_deriv_deriv_of_hasDerivAt (f := fun t => c * sin (k * t))
    (f₁ := fun t => c * k * cos (k * t)) (f₂ := fun t => -(c * k ^ 2) * sin (k * t))
    (f₃ := fun t => -(c * k ^ 3 * cos (k * t))) (fun t => ?_) (fun t => ?_) (fun t => ?_) t
  · convert (hasDerivAt_sin_mul k t).const_mul c using 1
    ring
  · convert (hasDerivAt_cos_mul k t).const_mul (c * k) using 1
    ring
  · convert (hasDerivAt_sin_mul k t).const_mul (-(c * k ^ 2)) using 1
    ring

/-- The third derivative of a constant plus a function. -/
private theorem deriv3_const_add (b : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    deriv (deriv (deriv fun t => b + f t)) t = deriv (deriv (deriv f)) t := by
  have h : deriv (fun t => b + f t) = deriv f := funext fun t => by
    rw [deriv_const_add]
  rw [h]

/-- **The quadrupole radiation of a circular binary** (Landau–Lifshitz, §110, problem 1): the
third derivatives of the quadrupole moment `D = 3I − δ tr I` of a circular binary satisfy
`Σ D⃛_{αβ}² = 288 μ² a⁴ Ω⁶`. -/
theorem sum_sq_quadrupoleOf_binary (μ a Ω t : ℝ) :
    ∑ α, ∑ β, Wave.quadrupoleOf
      (fun α β => deriv (deriv (deriv fun t => binaryMoment μ a Ω t α β)) t) α β ^ 2 =
        288 * μ ^ 2 * a ^ 4 * Ω ^ 6 := by
  set c : ℝ := μ * a ^ 2 / 2 with hc
  have e00 : (fun t => binaryMoment μ a Ω t 0 0) = fun t => c + c * cos (2 * Ω * t) := by
    funext t
    simp only [binaryMoment, binaryOrbit, Matrix.cons_val_zero, hc]
    rw [show 2 * Ω * t = 2 * (Ω * t) by ring, cos_two_mul]
    ring
  have e11 : (fun t => binaryMoment μ a Ω t 1 1) = fun t => c + -c * cos (2 * Ω * t) := by
    funext t
    simp only [binaryMoment, binaryOrbit, Matrix.cons_val_one, Matrix.cons_val_zero, hc]
    rw [show 2 * Ω * t = 2 * (Ω * t) by ring, cos_two_mul]
    linear_combination μ * a ^ 2 * sin_sq_add_cos_sq (Ω * t)
  have e01 : (fun t => binaryMoment μ a Ω t 0 1) = fun t => c * sin (2 * Ω * t) := by
    funext t
    simp only [binaryMoment, binaryOrbit, Matrix.cons_val_one, Matrix.cons_val_zero, hc]
    rw [show 2 * Ω * t = 2 * (Ω * t) by ring, sin_two_mul]
    ring
  have e10 : (fun t => binaryMoment μ a Ω t 1 0) = fun t => c * sin (2 * Ω * t) := by
    rw [← e01]
    funext t
    simp only [binaryMoment]
    ring
  have ez : ∀ α : Fin 3, (fun t => binaryMoment μ a Ω t α 2) = fun _ => 0 := fun α => by
    funext t
    simp [binaryMoment, binaryOrbit]
  have ez' : ∀ α : Fin 3, (fun t => binaryMoment μ a Ω t 2 α) = fun _ => 0 := fun α => by
    funext t
    simp [binaryMoment, binaryOrbit]
  simp only [Wave.quadrupoleOf, Fin.sum_univ_three, Fin.isValue, Fin.reduceEq, ite_true,
    ite_false, e00, e11, e01, e10, ez, ez', deriv3_const_add,
    deriv3_cos, deriv3_sin, deriv_const']
  have h := sin_sq_add_cos_sq (2 * Ω * t)
  linear_combination 288 * μ ^ 2 * a ^ 4 * Ω ^ 6 * h

/-- **The power radiated by a circular binary** (Landau–Lifshitz, §110, problem 1): the
quadrupole formula `(κ/8π)(1/45) Σ D⃛² = (κ/360π) Σ D⃛²` is `(32/5) G μ² a⁴ ω⁶` with
`G = κ/8π`, for every time `t`. -/
theorem binary_power (κ μ a Ω t : ℝ) :
    κ / (360 * π) * ∑ α, ∑ β, Wave.quadrupoleOf
      (fun α β => deriv (deriv (deriv fun t => binaryMoment μ a Ω t α β)) t) α β ^ 2 =
        32 / 5 * (κ / (8 * π)) * μ ^ 2 * a ^ 4 * Ω ^ 6 := by
  rw [sum_sq_quadrupoleOf_binary]
  field_simp
  ring

/-- The trivial instance: the zero stress tensor is localized in every ball of radius `a ≥ 0`. -/
theorem localizedStress_zero {a : ℝ} (ha : 0 ≤ a) :
    LocalizedStress (fun _ => (0 : Matrix (Fin 4) (Fin 4) ℝ)) a where
  radius_nonneg := ha
  contDiff _ _ := contDiff_const
  symm _ _ _ := rfl
  conserved _ _ := by simp
  support _ _ _ := rfl

/-! ### A smooth source with a prescribed second moment -/

/-- The derivative `∂_γ f` of a function on space along the axis `γ`. -/
def spacePartial (γ : Fin 3) (f : E3 → ℝ) (x : E3) : ℝ := fderiv ℝ f x (EuclideanSpace.single γ 1)

theorem contDiff_spacePartial {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (γ : Fin 3) :
    ContDiff ℝ ∞ (spacePartial γ f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The derivatives of a function that vanishes outside a ball vanish outside the ball. -/
theorem spacePartial_eq_zero {f : E3 → ℝ} {r : ℝ} (hf : ∀ x, r < ‖x‖ → f x = 0) (γ : Fin 3)
    {x : E3} (hx : r < ‖x‖) : spacePartial γ f x = 0 := by
  rw [spacePartial, fderiv_space_eq_zero_of_ballSupport hf hx]
  rfl

/-- **The derivatives on space commute**: `∂_γ ∂_δ f = ∂_δ ∂_γ f` for a `C²` function. -/
theorem spacePartial_comm {f : E3 → ℝ} (hf : ContDiff ℝ 2 f) (γ δ : Fin 3) (x : E3) :
    spacePartial γ (spacePartial δ f) x = spacePartial δ (spacePartial γ f) x := by
  have hsymm := hf.contDiffAt.isSymmSndFDerivAt (x := x) (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have key (v w : E3) : fderiv ℝ (fun z => fderiv ℝ f z w) x v = fderiv ℝ (fderiv ℝ f) x v w := by
    rw [fderiv_clm_apply hd (differentiableAt_const w)]
    simp
  show fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single δ 1)) x (EuclideanSpace.single γ 1) =
    fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single γ 1)) x (EuclideanSpace.single δ 1)
  rw [key, key]
  exact hsymm _ _

/-- The spatial part of the axis `γ + 1` of space-time is `e_γ`. -/
theorem space_single_succ (γ : Fin 3) :
    space (Pi.single γ.succ 1 : Spacetime) = EuclideanSpace.single γ 1 := by
  ext i
  simp only [space_apply, PiLp.single_apply]
  by_cases h : i = γ
  · subst h
    simp
  · simp [h, Fin.succ_inj]

/-- The derivative of `w ↦ q(w⁰) g(𝐰)` along the axis of the time. -/
theorem fderiv_time_mul_space_zero {q : ℝ → ℝ} {g : E3 → ℝ} (hq : Differentiable ℝ q)
    (hg : Differentiable ℝ g) (z : Spacetime) :
    fderiv ℝ (fun w : Spacetime => q (w 0) * g (space w)) z (Pi.single 0 1) =
      deriv q (z 0) * g (space z) := by
  rw [(hasFDerivAt_time_mul_space (hq (z 0)).hasDerivAt (hg (space z))).fderiv]
  simp [space_pi_single_time, mul_comm]

/-- The derivative of `w ↦ q(w⁰) g(𝐰)` along the axis `γ + 1`. -/
theorem fderiv_time_mul_space_succ {q : ℝ → ℝ} {g : E3 → ℝ} (hq : Differentiable ℝ q)
    (hg : Differentiable ℝ g) (z : Spacetime) (γ : Fin 3) :
    fderiv ℝ (fun w : Spacetime => q (w 0) * g (space w)) z (Pi.single γ.succ 1) =
      q (z 0) * spacePartial γ g (space z) := by
  rw [(hasFDerivAt_time_mul_space (hq (z 0)).hasDerivAt (hg (space z))).fderiv]
  simp [space_single_succ, spacePartial, Fin.succ_ne_zero]

/-- The derivative of a finite sum of functions on space-time. -/
theorem fderiv_finsetSum_apply {ι : Type*} (s : Finset ι) {F : ι → Spacetime → ℝ}
    {z : Spacetime} (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) z) (v : Spacetime) :
    fderiv ℝ (fun w => ∑ i ∈ s, F i w) z v = ∑ i ∈ s, fderiv ℝ (F i) z v := by
  rw [fderiv_fun_sum hF, _root_.sum_apply]

/-- **A source with a prescribed second moment**, from a superpotential
`T^{ik} = ∂_l ∂_m Ψ^{ilkm}` with `Ψ^{0α0β} = Q_{αβ}(t) χ(x)` and the symmetries of the Riemann
tensor, which is conserved and symmetric identically. With lower indices
`T₀₀ = Σ Q_{γδ} ∂_γ∂_δχ`, `T₀ᵧ = T_γ₀ = Σ_α Q̇_{αγ} ∂_αχ` and `T_{γδ} = Q̈_{γδ} χ`. -/
def quadrupoleSource (Q : Fin 3 → Fin 3 → ℝ → ℝ) (χ : E3 → ℝ) (v : Spacetime) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i k =>
    Fin.cases (Fin.cases (∑ p : Fin 3 × Fin 3, Q p.1 p.2 (v 0) *
        spacePartial p.1 (spacePartial p.2 χ) (space v))
      (fun δ => ∑ α, deriv (Q α δ) (v 0) * spacePartial α χ (space v)) k)
    (fun γ => Fin.cases (∑ α, deriv (Q α γ) (v 0) * spacePartial α χ (space v))
      (fun δ => deriv (deriv (Q γ δ)) (v 0) * χ (space v)) k) i

section QuadrupoleSource

variable {Q : Fin 3 → Fin 3 → ℝ → ℝ} {χ : E3 → ℝ}

theorem quadrupoleSource_zero_zero (v : Spacetime) :
    quadrupoleSource Q χ v 0 0 = ∑ p : Fin 3 × Fin 3, Q p.1 p.2 (v 0) *
      spacePartial p.1 (spacePartial p.2 χ) (space v) := rfl

theorem quadrupoleSource_zero_succ (v : Spacetime) (δ : Fin 3) :
    quadrupoleSource Q χ v 0 δ.succ = ∑ α, deriv (Q α δ) (v 0) * spacePartial α χ (space v) := rfl

theorem quadrupoleSource_succ_zero (v : Spacetime) (γ : Fin 3) :
    quadrupoleSource Q χ v γ.succ 0 = ∑ α, deriv (Q α γ) (v 0) * spacePartial α χ (space v) := rfl

theorem quadrupoleSource_succ_succ (v : Spacetime) (γ δ : Fin 3) :
    quadrupoleSource Q χ v γ.succ δ.succ = deriv (deriv (Q γ δ)) (v 0) * χ (space v) := rfl

/-- **The source with a prescribed second moment is a localized stress tensor**, for smooth
symmetric `Q` and a smooth `χ` that vanishes outside the ball of radius `r`. -/
theorem localizedStress_quadrupoleSource (hQ : ∀ γ δ, ContDiff ℝ ∞ (Q γ δ))
    (hQs : ∀ γ δ, Q γ δ = Q δ γ) (hχ : ContDiff ℝ ∞ χ) {r : ℝ} (hr : 0 ≤ r)
    (hχs : ∀ x, r < ‖x‖ → χ x = 0) : LocalizedStress (quadrupoleSource Q χ) r := by
  have hQ1 : ∀ γ δ, ContDiff ℝ ∞ (deriv (Q γ δ)) := fun γ δ =>
    (contDiff_infty_iff_deriv.1 (hQ γ δ)).2
  have hQ2 : ∀ γ δ, ContDiff ℝ ∞ (deriv (deriv (Q γ δ))) := fun γ δ =>
    (contDiff_infty_iff_deriv.1 (hQ1 γ δ)).2
  have hχ1 : ∀ γ, ContDiff ℝ ∞ (spacePartial γ χ) := fun γ => contDiff_spacePartial hχ γ
  have hχ2 : ∀ γ δ, ContDiff ℝ ∞ (spacePartial γ (spacePartial δ χ)) := fun γ δ =>
    contDiff_spacePartial (hχ1 δ) γ
  have ht : ∀ {q : ℝ → ℝ}, ContDiff ℝ ∞ q → ContDiff ℝ ∞ fun w : Spacetime => q (w 0) :=
    fun hq => hq.comp (ContinuousLinearMap.proj 0 : Spacetime →L[ℝ] ℝ).contDiff
  have hs : ∀ {g : E3 → ℝ}, ContDiff ℝ ∞ g → ContDiff ℝ ∞ fun w : Spacetime => g (space w) :=
    fun hg => hg.comp space.contDiff
  have hd : ∀ {f : ℝ → ℝ} {g : E3 → ℝ}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      Differentiable ℝ fun w : Spacetime => f (w 0) * g (space w) := fun hf hg =>
    ((ht hf).mul (hs hg)).differentiable (by simp)
  have hdf : ∀ {f : ℝ → ℝ}, ContDiff ℝ ∞ f → Differentiable ℝ f := fun hf =>
    hf.differentiable (by simp)
  have hdg : ∀ {g : E3 → ℝ}, ContDiff ℝ ∞ g → Differentiable ℝ g := fun hg =>
    hg.differentiable (by simp)
  refine ⟨hr, fun i k => ?_, fun z i k => ?_, fun z b => ?_, fun t x hx => ?_⟩
  · refine Fin.cases ?_ (fun γ => ?_) i <;> refine Fin.cases ?_ (fun δ => ?_) k
    · simp only [quadrupoleSource_zero_zero]
      exact ContDiff.sum fun p _ => (ht (hQ p.1 p.2)).mul (hs (hχ2 p.1 p.2))
    · simp only [quadrupoleSource_zero_succ]
      exact ContDiff.sum fun α _ => (ht (hQ1 α δ)).mul (hs (hχ1 α))
    · simp only [quadrupoleSource_succ_zero]
      exact ContDiff.sum fun α _ => (ht (hQ1 α γ)).mul (hs (hχ1 α))
    · simp only [quadrupoleSource_succ_succ]
      exact (ht (hQ2 γ δ)).mul (hs hχ)
  · refine Fin.cases ?_ (fun γ => ?_) i <;> refine Fin.cases ?_ (fun δ => ?_) k
    · rfl
    · rfl
    · rfl
    · simp only [quadrupoleSource_succ_succ, hQs γ δ]
  · rw [Fin.sum_univ_succ]
    simp only [lorentzSign_zero, lorentzSign_succ, one_mul, neg_one_mul]
    refine Fin.cases ?_ (fun δ => ?_) b
    · -- the energy
      simp only [quadrupoleSource_zero_zero, quadrupoleSource_succ_zero]
      rw [fderiv_finsetSum_apply _ fun p _ => (hd (hQ p.1 p.2) (hχ2 p.1 p.2)) z]
      simp only [fderiv_time_mul_space_zero (hdf (hQ _ _)) (hdg (hχ2 _ _))]
      have hγ : ∀ γ : Fin 3, fderiv ℝ (fun w => ∑ α, deriv (Q α γ) (w 0) *
          spacePartial α χ (space w)) z (Pi.single γ.succ 1) =
            ∑ α, deriv (Q α γ) (z 0) * spacePartial γ (spacePartial α χ) (space z) := fun γ => by
        rw [fderiv_finsetSum_apply _ fun α _ => (hd (hQ1 α γ) (hχ1 α)) z]
        simp only [fderiv_time_mul_space_succ (hdf (hQ1 _ _)) (hdg (hχ1 _))]
      simp only [hγ]
      rw [← Fintype.sum_prod_type']
      simp only [Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      rw [neg_add_eq_zero]
      refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
      rw [spacePartial_comm (hχ.of_le (by simp))]
    · -- the momentum
      simp only [quadrupoleSource_zero_succ, quadrupoleSource_succ_succ]
      rw [fderiv_finsetSum_apply _ fun α _ => (hd (hQ1 α δ) (hχ1 α)) z]
      simp only [fderiv_time_mul_space_zero (hdf (hQ1 _ _)) (hdg (hχ1 _)),
        fderiv_time_mul_space_succ (hdf (hQ2 _ _)) (hdg hχ)]
      exact neg_add_cancel _
  · funext i k
    have h0 : ∀ γ, spacePartial γ χ x = 0 := fun γ => spacePartial_eq_zero hχs γ hx
    have h1 : ∀ γ δ, spacePartial γ (spacePartial δ χ) x = 0 := fun γ δ =>
      spacePartial_eq_zero (fun y hy => spacePartial_eq_zero hχs δ hy) γ hx
    refine Fin.cases ?_ (fun γ => ?_) i <;> refine Fin.cases ?_ (fun δ => ?_) k
    · simp [quadrupoleSource_zero_zero, h1]
    · simp [quadrupoleSource_zero_succ, h0]
    · simp [quadrupoleSource_succ_zero, h0]
    · simp [quadrupoleSource_succ_succ, hχs x hx]

/-- **Integration by parts on space**: `∫ ∂_γ f · w dy = −∫ f ∂_γ w dy` for `C¹` functions, `f`
vanishing outside a ball. -/
theorem integral_spacePartial_mul {f w : E3 → ℝ} {r : ℝ} (hf : ContDiff ℝ 1 f)
    (hfs : ∀ x, r < ‖x‖ → f x = 0) (hw : ContDiff ℝ 1 w) (γ : Fin 3) :
    ∫ y, spacePartial γ f y * w y = -∫ y, f y * spacePartial γ w y := by
  have hf' : Continuous (spacePartial γ f) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hw' : Continuous (spacePartial γ w) :=
    (hw.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := w) (g := f)
    (v := EuclideanSpace.single γ 1)
    (integrable_of_ballSupport (a := r) (hw'.mul hf.continuous) fun y hy => by simp [hfs y hy])
    (integrable_of_ballSupport (a := r) (hw.continuous.mul hf') fun y hy => by
      simp [fderiv_space_eq_zero_of_ballSupport hfs hy])
    (integrable_of_ballSupport (a := r) (hw.continuous.mul hf.continuous) fun y hy => by
      simp [hfs y hy])
    (fun y _ => hw.differentiable one_ne_zero y) (fun y _ => hf.differentiable one_ne_zero y)
  simp only [spacePartial]
  rw [show (fun y => fderiv ℝ f y (EuclideanSpace.single γ 1) * w y) =
    fun y => w y * fderiv ℝ f y (EuclideanSpace.single γ 1) from funext fun y => mul_comm _ _, h]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  exact mul_comm _ _

/-- The derivatives of a coordinate: `∂_γ y_δ = δ_{γδ}`. -/
theorem spacePartial_coord (γ δ : Fin 3) (y : E3) :
    spacePartial γ (fun y : E3 => y δ) y = if δ = γ then 1 else 0 := by
  simp only [spacePartial]
  rw [show (fun y : E3 => y δ) = ⇑(EuclideanSpace.proj (𝕜 := ℝ) δ) from rfl,
    ContinuousLinearMap.fderiv]
  simp [PiLp.single_apply]

/-- The derivatives of the products of two coordinates. -/
theorem spacePartial_coord_mul (γ α β : Fin 3) (y : E3) :
    spacePartial γ (fun y : E3 => y α * y β) y =
      (if α = γ then 1 else 0) * y β + y α * (if β = γ then 1 else 0) := by
  have hα : DifferentiableAt ℝ (fun y : E3 => y α) y :=
    (EuclideanSpace.proj (𝕜 := ℝ) α).differentiableAt
  have hβ : DifferentiableAt ℝ (fun y : E3 => y β) y :=
    (EuclideanSpace.proj (𝕜 := ℝ) β).differentiableAt
  rw [spacePartial, fderiv_fun_mul hα hβ]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [← spacePartial, ← spacePartial, spacePartial_coord, spacePartial_coord]
  ring

/-- **The second moment of the source**: `∫ T₀₀ y_α y_β dy = 2 Q_{αβ}(s) ∫ χ`, by two
integrations by parts. -/
theorem secondMoment_quadrupoleSource (hQs : ∀ γ δ, Q γ δ = Q δ γ) (hχ : ContDiff ℝ ∞ χ)
    {r : ℝ} (hχs : ∀ x, r < ‖x‖ → χ x = 0) (s : ℝ) (α β : Fin 3) :
    secondMoment (quadrupoleSource Q χ) s α β = 2 * Q α β s * ∫ y, χ y := by
  have hχ1 : ∀ γ, ContDiff ℝ ∞ (spacePartial γ χ) := fun γ => contDiff_spacePartial hχ γ
  have hχ2 : ∀ γ δ, ContDiff ℝ ∞ (spacePartial γ (spacePartial δ χ)) := fun γ δ =>
    contDiff_spacePartial (hχ1 δ) γ
  have hχs1 : ∀ δ x, r < ‖x‖ → spacePartial δ χ x = 0 := fun δ x hx => spacePartial_eq_zero hχs δ hx
  have hw : ContDiff ℝ ∞ fun y : E3 => y α * y β :=
    (EuclideanSpace.proj (𝕜 := ℝ) α).contDiff.mul (EuclideanSpace.proj (𝕜 := ℝ) β).contDiff
  -- the derivative of the weight is linear
  set w₁ : Fin 3 → E3 → ℝ := fun γ y =>
    (if α = γ then 1 else 0) * y β + y α * (if β = γ then 1 else 0) with hw₁
  have hw₁c : ∀ γ, ContDiff ℝ ∞ (w₁ γ) := fun γ =>
    (contDiff_const.mul (EuclideanSpace.proj (𝕜 := ℝ) β).contDiff).add
      ((EuclideanSpace.proj (𝕜 := ℝ) α).contDiff.mul contDiff_const)
  have hw₁d : ∀ γ δ y, spacePartial δ (w₁ γ) y = (if α = γ then 1 else 0) *
      (if β = δ then 1 else 0) + (if α = δ then 1 else 0) * (if β = γ then 1 else 0) := by
    intro γ δ y
    have hαd : DifferentiableAt ℝ (fun y : E3 => y α) y :=
      (EuclideanSpace.proj (𝕜 := ℝ) α).differentiableAt
    have hβd : DifferentiableAt ℝ (fun y : E3 => y β) y :=
      (EuclideanSpace.proj (𝕜 := ℝ) β).differentiableAt
    have h1 : DifferentiableAt ℝ (fun y : E3 => (if α = γ then (1 : ℝ) else 0) * y β) y :=
      hβd.const_mul _
    have h2 : DifferentiableAt ℝ (fun y : E3 => y α * (if β = γ then (1 : ℝ) else 0)) y :=
      hαd.mul_const _
    simp only [hw₁, spacePartial]
    rw [fderiv_fun_add h1 h2, _root_.add_apply, fderiv_const_mul hβd, fderiv_mul_const hαd]
    simp only [_root_.smul_apply, smul_eq_mul]
    rw [← spacePartial, ← spacePartial, spacePartial_coord, spacePartial_coord]
    ring
  have hibp : ∀ γ δ, ∫ y, spacePartial γ (spacePartial δ χ) y * (y α * y β) =
      ((if α = γ then 1 else 0) * (if β = δ then 1 else 0) +
        (if α = δ then 1 else 0) * (if β = γ then 1 else 0)) * ∫ y, χ y := by
    intro γ δ
    rw [integral_spacePartial_mul ((hχ1 δ).of_le (by simp)) (hχs1 δ) (hw.of_le (by simp)) γ]
    have e1 : (fun y => spacePartial δ χ y * spacePartial γ (fun y : E3 => y α * y β) y) =
        fun y => spacePartial δ χ y * w₁ γ y := funext fun y => by
      rw [spacePartial_coord_mul]
    rw [e1, integral_spacePartial_mul (hχ.of_le (by simp)) hχs ((hw₁c γ).of_le (by simp)) δ]
    simp only [hw₁d, neg_neg]
    rw [integral_mul_const]
    ring
  simp only [secondMoment, quadrupoleSource_zero_zero, vector_zero, space_vector,
    Finset.sum_mul]
  rw [integral_finsetSum _ fun p _ => integrable_of_ballSupport (a := r)
    (((continuous_const.mul (hχ2 p.1 p.2).continuous)).mul (by fun_prop)) fun y hy => by
      simp [spacePartial_eq_zero (hχs1 p.2) p.1 hy]]
  simp only [mul_assoc, integral_const_mul, hibp]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.isValue]
  fin_cases α <;> fin_cases β <;> simp [hQs 1 0, hQs 2 0, hQs 2 1] <;> ring

end QuadrupoleSource

/-! ### A smooth circular binary -/

/-- The modes `A + B cos 2t + C sin 2t`. -/
def trigMode (A B C t : ℝ) : ℝ := A + B * cos (2 * t) + C * sin (2 * t)

theorem hasDerivAt_trigMode (A B C t : ℝ) :
    HasDerivAt (trigMode A B C) (trigMode 0 (2 * C) (-(2 * B)) t) t := by
  have h := (((hasDerivAt_cos_mul 2 t).const_mul B).const_add A).fun_add
    ((hasDerivAt_sin_mul 2 t).const_mul C)
  unfold trigMode
  convert h using 1
  ring

theorem deriv_trigMode (A B C : ℝ) :
    deriv (trigMode A B C) = trigMode 0 (2 * C) (-(2 * B)) :=
  funext fun t => (hasDerivAt_trigMode A B C t).deriv

theorem contDiff_trigMode (A B C : ℝ) : ContDiff ℝ ∞ (trigMode A B C) := by
  unfold trigMode
  fun_prop

theorem abs_trigMode_le (B C t : ℝ) : |trigMode 0 B C t| ≤ |B| + |C| := by
  unfold trigMode
  have h1 : |B * cos (2 * t)| ≤ |B| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)
  have h2 : |C * sin (2 * t)| ≤ |C| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _)
  rw [zero_add]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- The modes of `x_α x_β = (a²/2)(A + B cos 2t + C sin 2t)` for the orbit `a (cos t, sin t, 0)`:
`A = diag(1, 1, 0)`. -/
def binaryA : Fin 3 → Fin 3 → ℝ := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 0]]

/-- `B = diag(1, −1, 0)`. -/
def binaryB : Fin 3 → Fin 3 → ℝ := ![![1, 0, 0], ![0, -1, 0], ![0, 0, 0]]

/-- `C = e₁ ⊗ e₂ + e₂ ⊗ e₁`. -/
def binaryC : Fin 3 → Fin 3 → ℝ := ![![0, 1, 0], ![1, 0, 0], ![0, 0, 0]]

theorem binaryMoment_eq (μ a s : ℝ) (α β : Fin 3) :
    binaryMoment μ a 1 s α β = μ * a ^ 2 / 2 * trigMode (binaryA α β) (binaryB α β)
      (binaryC α β) s := by
  have hc := cos_sq s
  have hs := sin_sq s
  have h2 := sin_two_mul s
  fin_cases α <;> fin_cases β <;>
    simp [binaryMoment, binaryOrbit, binaryA, binaryB, binaryC, trigMode] <;>
    first
    | linear_combination μ * a ^ 2 * hc
    | linear_combination μ * a ^ 2 * hs - μ * a ^ 2 * hc
    | linear_combination (-(μ * a ^ 2 / 2)) * h2

theorem binaryA_symm (γ δ : Fin 3) : binaryA γ δ = binaryA δ γ := by
  fin_cases γ <;> fin_cases δ <;> rfl

theorem binaryB_symm (γ δ : Fin 3) : binaryB γ δ = binaryB δ γ := by
  fin_cases γ <;> fin_cases δ <;> rfl

theorem binaryC_symm (γ δ : Fin 3) : binaryC γ δ = binaryC δ γ := by
  fin_cases γ <;> fin_cases δ <;> rfl

theorem abs_binaryB_le (γ δ : Fin 3) : |binaryB γ δ| ≤ 1 := by
  fin_cases γ <;> fin_cases δ <;> simp [binaryB]

theorem abs_binaryC_le (γ δ : Fin 3) : |binaryC γ δ| ≤ 1 := by
  fin_cases γ <;> fin_cases δ <;> simp [binaryC]

/-- The mass `m = ∫ χ > 0` of the bump `χ = spaceBump`. -/
def bumpMass : ℝ := ∫ y : E3, Wave.spaceBump y

theorem bumpMass_pos : 0 < bumpMass := Wave.spaceBump.integral_pos

/-- The coefficient `c = μ a²/4m` of the binary source. -/
def binaryCoeff (μ a : ℝ) : ℝ := μ * a ^ 2 / (4 * bumpMass)

/-- **A smooth circular binary**: the source with the prescribed second moment
`Q_{αβ}(t) = μ x_α(t) x_β(t)/2m` for the orbit `x(t) = a (cos t, sin t, 0)` and the bump
`χ = spaceBump` of mass `m`, so that its second moment is the second moment `μ x_α x_β` of the
binary (`secondMoment_binarySource`). Its slow family `slowStress Ω` is the binary of angular
frequency `Ω` (`secondMoment_slowStress`). -/
def binarySource (μ a : ℝ) : Spacetime → Matrix (Fin 4) (Fin 4) ℝ :=
  quadrupoleSource (fun γ δ => trigMode (binaryCoeff μ a * binaryA γ δ)
    (binaryCoeff μ a * binaryB γ δ) (binaryCoeff μ a * binaryC γ δ)) fun x => Wave.spaceBump x

theorem spaceBump_eq_zero (x : E3) (hx : 2 < ‖x‖) : Wave.spaceBump x = 0 :=
  Wave.spaceBump.zero_of_le_dist (by rw [dist_zero_right]; exact hx.le)

/-- The binary source is a localized stress tensor in the ball of radius `2`. -/
theorem localizedStress_binarySource (μ a : ℝ) : LocalizedStress (binarySource μ a) 2 :=
  localizedStress_quadrupoleSource (fun _ _ => contDiff_trigMode _ _ _)
    (fun γ δ => by rw [binaryA_symm, binaryB_symm, binaryC_symm]) Wave.spaceBump.contDiff
    (by norm_num) spaceBump_eq_zero

/-- **The second moment of the binary source** is that of the binary: `I_{αβ} = μ x_α x_β`. -/
theorem secondMoment_binarySource (μ a s : ℝ) (α β : Fin 3) :
    secondMoment (binarySource μ a) s α β = binaryMoment μ a 1 s α β := by
  rw [binarySource, secondMoment_quadrupoleSource (fun γ δ => by
      rw [binaryA_symm, binaryB_symm, binaryC_symm]) Wave.spaceBump.contDiff spaceBump_eq_zero,
    binaryMoment_eq]
  have hm := bumpMass_pos.ne'
  rw [show (∫ y : E3, Wave.spaceBump y) = bumpMass from rfl]
  simp only [trigMode, binaryCoeff]
  field_simp
  ring

/-- The second moment of the slow family: `I^ε(s) = I(εs)`. -/
theorem secondMoment_slowStress (ε s : ℝ) (α β : Fin 3) :
    secondMoment (slowStress ε T) s α β = secondMoment T (ε * s) α β := by
  simp only [secondMoment, slowStress_apply, timeDilation_vector, indexScale, ite_true, one_mul]

/-- The slow family of the binary source is the binary of angular frequency `Ω`. -/
theorem secondMoment_slowStress_binarySource (μ a Ω s : ℝ) (α β : Fin 3) :
    secondMoment (slowStress Ω (binarySource μ a)) s α β = binaryMoment μ a Ω s α β := by
  rw [secondMoment_slowStress, secondMoment_binarySource]
  simp only [binaryMoment, binaryOrbit, one_mul]

/-- The time derivatives of the stresses of the binary source are bounded:
`|∂ₜT_{αβ}| ≤ 16 |c|` and `|∂ₜ²T_{αβ}| ≤ 32 |c|`. -/
theorem binarySource_bounds (μ a : ℝ) (α β : Fin 3) (v : Spacetime) :
    |fderiv ℝ (fun w => binarySource μ a w α.succ β.succ) v (Pi.single 0 1)| ≤
        16 * |binaryCoeff μ a| ∧
      |fderiv ℝ (fun w => fderiv ℝ (fun w => binarySource μ a w α.succ β.succ) w
        (Pi.single 0 1)) v (Pi.single 0 1)| ≤ 32 * |binaryCoeff μ a| := by
  set c := binaryCoeff μ a
  have hχc : ContDiff ℝ 1 fun x : E3 => Wave.spaceBump x := Wave.spaceBump.contDiff
  have hχ : Differentiable ℝ fun x : E3 => Wave.spaceBump x := hχc.differentiable one_ne_zero
  have hχ1 : ∀ x : E3, |Wave.spaceBump x| ≤ 1 := fun x => by
    rw [abs_of_nonneg Wave.spaceBump.nonneg]
    exact Wave.spaceBump.le_one
  have e2 : deriv (deriv (trigMode (c * binaryA α β) (c * binaryB α β) (c * binaryC α β))) =
      trigMode 0 (2 * -(2 * (c * binaryB α β))) (-(2 * (2 * (c * binaryC α β)))) := by
    rw [deriv_trigMode, deriv_trigMode]
  have hT : (fun w => binarySource μ a w α.succ β.succ) = fun w =>
      trigMode 0 (2 * -(2 * (c * binaryB α β))) (-(2 * (2 * (c * binaryC α β)))) (w 0) *
        Wave.spaceBump (space w) := funext fun w => by
    rw [binarySource, quadrupoleSource_succ_succ, e2]
  have hd : ∀ B C : ℝ, Differentiable ℝ (trigMode 0 B C) := fun B C =>
    (contDiff_trigMode 0 B C).differentiable (by simp)
  have h1 : (fun w => fderiv ℝ (fun w => binarySource μ a w α.succ β.succ) w (Pi.single 0 1)) =
      fun w => trigMode 0 (2 * -(2 * (2 * (c * binaryC α β))))
        (-(2 * (2 * -(2 * (c * binaryB α β))))) (w 0) * Wave.spaceBump (space w) :=
    funext fun w => by
      rw [hT, fderiv_time_mul_space_zero (hd _ _) hχ, deriv_trigMode]
  have hB := abs_binaryB_le α β
  have hC := abs_binaryC_le α β
  have h1v : fderiv ℝ (fun w => binarySource μ a w α.succ β.succ) v (Pi.single 0 1) =
      trigMode 0 (2 * -(2 * (2 * (c * binaryC α β))))
        (-(2 * (2 * -(2 * (c * binaryB α β))))) (v 0) * Wave.spaceBump (space v) :=
    congrFun h1 v
  constructor
  · rw [h1v, ← mul_one (16 * |c|), abs_mul]
    refine mul_le_mul ((abs_trigMode_le _ _ _).trans ?_) (hχ1 _) (abs_nonneg _) (by positivity)
    simp only [abs_neg, abs_mul, abs_two]
    nlinarith [abs_nonneg c]
  · rw [h1, fderiv_time_mul_space_zero (hd _ _) hχ, deriv_trigMode, ← mul_one (32 * |c|),
      abs_mul]
    refine mul_le_mul ((abs_trigMode_le _ _ _).trans ?_) (hχ1 _) (abs_nonneg _) (by positivity)
    simp only [abs_neg, abs_mul, abs_two]
    nlinarith [abs_nonneg c]

/-- **The gravitational radiation of a smooth circular binary** (Landau–Lifshitz, §110,
problem 1): for the binary source of angular frequency `Ω` (the slow family of
`binarySource μ a`), the flux of the quadratic pseudotensor through large spheres at the retarded
time `u` tends to a power `P` with `P = (32/5) G μ² a⁴ Ω⁶ + O(Ω⁷)`, `G = κ/8π`. -/
theorem binary_power_smooth (κ μ a u : ℝ) : ∃ C, ∀ Ω : ℝ, 0 ≤ Ω →
    ∃ P, Tendsto (fun R => sphereFlux (fun α v => quadraticPseudotensor
        (metricPerturbation κ (slowStress Ω (binarySource μ a))) v 0 α.succ / κ) (u + R) R)
      atTop (𝓝 P) ∧
      |P - 32 / 5 * (κ / (8 * π)) * μ ^ 2 * a ^ 4 * Ω ^ 6| ≤ C * Ω ^ 7 := by
  refine ⟨120 * π * |κ| * (16 * |binaryCoeff μ a|) * (32 * |binaryCoeff μ a|) * 2 ^ 7,
    fun Ω hΩ => ?_⟩
  obtain ⟨P, hP, hb⟩ := tendsto_pseudotensorFlux_slow (κ := κ) (localizedStress_binarySource μ a)
    (fun α β v => (binarySource_bounds μ a α β v).1)
    (fun α β v => (binarySource_bounds μ a α β v).2) hΩ u
  refine ⟨P, hP, ?_⟩
  have hs : ∀ α β : Fin 3, (fun s => secondMoment (binarySource μ a) s α β) =
      fun s => binaryMoment μ a 1 s α β := fun α β => funext fun s =>
    secondMoment_binarySource μ a s α β
  simp only [hs, sum_sq_quadrupoleOf_binary] at hb
  have e : κ * Ω ^ 6 / (360 * π) * (288 * μ ^ 2 * a ^ 4 * 1 ^ 6) =
      32 / 5 * (κ / (8 * π)) * μ ^ 2 * a ^ 4 * Ω ^ 6 := by
    field_simp
    ring
  rw [e] at hb
  calc _ ≤ 120 * π * |κ| * (16 * |binaryCoeff μ a|) * (32 * |binaryCoeff μ a|) * 2 ^ 7 * Ω ^ 7 :=
        hb
    _ = _ := rfl

end ProjectAinos.GeneralRelativity.LinearizedRadiation
