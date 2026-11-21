/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.ODE.RiccatiComparison
import ProjectAinos.SmoothGeometry.Lorentzian.Focusing
import ProjectAinos.GeneralRelativity.EnergyCondition

/-! Public consumers of the focusing of time lines (Landau–Lifshitz §§97, 119): the trace
inequality, the equation of Raychaudhuri for a synchronous system, the scalar Riccati comparison,
the strong energy condition with the timelike convergence of the Ricci tensor, and the breakdown of
a synchronous system within `3/|θ|`. Default elaborator options are intentional: these checks must
not rely on the implementation's transparency settings. Every statement is pinned with its type.
-/

noncomputable section


section RiccatiComparison

open Set Filter

open scoped Topology

namespace ProjectAinos.SmoothGeometry.RiccatiComparison

variable {θ θ' : ℝ → ℝ} {n t₀ T : ℝ}

example (hn : 0 < n) (hc : ContinuousOn θ (Icc t₀ (t₀ + T)))
    (hd : ∀ t ∈ Ioo t₀ (t₀ + T), HasDerivAt θ (θ' t) t)
    (hle : ∀ t ∈ Ioo t₀ (t₀ + T), θ' t ≤ -θ t ^ 2 / n) :
    AntitoneOn θ (Icc t₀ (t₀ + T)) :=
  antitoneOn hn hc hd hle

example (hn : 0 < n) (hc : ContinuousOn θ (Icc t₀ (t₀ + T)))
    (hd : ∀ t ∈ Ioo t₀ (t₀ + T), HasDerivAt θ (θ' t) t)
    (hle : ∀ t ∈ Ioo t₀ (t₀ + T), θ' t ≤ -θ t ^ 2 / n) (h0 : θ t₀ < 0) {t : ℝ}
    (ht : t ∈ Icc t₀ (t₀ + T)) :
    θ t < 0 ∧ (θ t₀)⁻¹ + (t - t₀) / n ≤ (θ t)⁻¹ :=
  inv_add_le hn hc hd hle h0 ht

example (hn : 0 < n) (hc : ContinuousOn θ (Icc t₀ (t₀ + T)))
    (hd : ∀ t ∈ Ioo t₀ (t₀ + T), HasDerivAt θ (θ' t) t)
    (hle : ∀ t ∈ Ioo t₀ (t₀ + T), θ' t ≤ -θ t ^ 2 / n) (h0 : θ t₀ < 0) {t : ℝ}
    (ht : t ∈ Icc t₀ (t₀ + T)) :
    0 < n + θ t₀ * (t - t₀) ∧ θ t ≤ n * θ t₀ / (n + θ t₀ * (t - t₀)) :=
  le_div hn hc hd hle h0 ht

example (hn : 0 < n) (hc : ContinuousOn θ (Icc t₀ (t₀ + T)))
    (hd : ∀ t ∈ Ioo t₀ (t₀ + T), HasDerivAt θ (θ' t) t)
    (hle : ∀ t ∈ Ioo t₀ (t₀ + T), θ' t ≤ -θ t ^ 2 / n) (h0 : θ t₀ < 0) :
    T < n / |θ t₀| :=
  lt_div_abs hn hc hd hle h0

example (hn : 0 < n) (h0 : θ t₀ < 0) (hc : ContinuousOn θ (Ico t₀ (t₀ + n / |θ t₀|)))
    (hd : ∀ t ∈ Ioo t₀ (t₀ + n / |θ t₀|), HasDerivAt θ (θ' t) t)
    (hle : ∀ t ∈ Ioo t₀ (t₀ + n / |θ t₀|), θ' t ≤ -θ t ^ 2 / n) :
    Tendsto θ (𝓝[<] (t₀ + n / |θ t₀|)) atBot :=
  tendsto_atBot hn h0 hc hd hle

example (hn : n ≠ 0) {t₁ t : ℝ} (ht : t ≠ t₁) :
    HasDerivAt (fun s => n / (s - t₁)) (-(n / (t - t₁)) ^ 2 / n) t :=
  hasDerivAt_div_sub hn ht

example (hn : 0 < n) {t₁ : ℝ} (h : t₀ < t₁) :
    n / (t₀ - t₁) < 0 ∧ n / |n / (t₀ - t₁)| = t₁ - t₀ :=
  div_abs_div_sub hn h

end ProjectAinos.SmoothGeometry.RiccatiComparison

end RiccatiComparison

section Focusing

open Set Filter TopologicalSpace

open scoped Manifold ContDiff Topology MatrixOrder

namespace ProjectAinos.SmoothGeometry

namespace Focusing

open Matrix

example {n : Type} [Fintype n] [DecidableEq n] {P B : Matrix n n ℝ} (hP : P.PosSemidef)
    (hB : B.IsSymm) :
    0 ≤ (P * B * (P * B)).trace :=
  trace_mul_mul_nonneg hP hB

example {d : ℕ} {γ S : Matrix (Fin d) (Fin d) ℝ} (hγ : γ.PosDef) (hS : S.IsSymm) :
    (γ⁻¹ * S).trace ^ 2 / d ≤ (γ⁻¹ * S * (γ⁻¹ * S)).trace :=
  trace_sq_ge hγ hS

end Focusing

namespace CoordinateMetric

open LorentzMetric

variable {d : ℕ} {U : Opens (MinkowskiModel d)}

example (g : CoordinateMetric .timeNegative d U) (z : MinkowskiModel d) :
    Matrix (Fin d) (Fin d) ℝ :=
  spatialCoefficient g z

example (g : CoordinateMetric .timeNegative d U) (z : MinkowskiModel d) :
    ℝ :=
  expansion g z

example (g : CoordinateMetric .timeNegative d U) (z : MinkowskiModel d) :
    ℝ :=
  shearSq g z

example (g : CoordinateMetric .timeNegative d U) {z : MinkowskiModel d} (hz : z ∈ U) (α β : Fin d) :
    g.metricRate z α β = g.metricRate z β α :=
  metricRate_symm g hz α β

namespace IsSynchronous

variable {g : CoordinateMetric .timeNegative d U} (hs : g.IsSynchronous) {z : MinkowskiModel d}

include hs

example (hz : z ∈ U) :
    (g.spatialCoefficient z).PosDef :=
  spatialCoefficient_posDef hs hz

example (hz : z ∈ U) :
    (g.spatialCoefficient z)⁻¹ = Matrix.of fun α β => (g.coefficient z)⁻¹ α.succ β.succ :=
  inv_spatialCoefficient hs hz

example (hz : z ∈ U) (α β : Fin d) :
    g.extrinsicRate z α β = ((g.spatialCoefficient z)⁻¹ * Matrix.of (g.metricRate z)) α β :=
  extrinsicRate_eq_mul hs hz α β

example (hz : z ∈ U) :
    (∑ α, g.extrinsicRate z α α) ^ 2 / d ≤
      ∑ α, ∑ β, g.extrinsicRate z α β * g.extrinsicRate z β α :=
  sq_sum_extrinsicRate_le hs hz

example (hz : z ∈ U) :
    g.expansion z =
      fderiv ℝ (fun w => Real.log (densityOf g.coefficient w)) z (Pi.single 0 1) :=
  expansion_eq_fderiv_log hs hz

example (hz : z ∈ U) :
    0 ≤ g.shearSq z :=
  shearSq_nonneg hs hz

example (hz : z ∈ U) (α β : Fin d) :
    DifferentiableAt ℝ (fun w => g.extrinsicRate w α β) z :=
  differentiableAt_extrinsicRate hs hz α β

example (hz : z ∈ U) :
    DifferentiableAt ℝ g.expansion z :=
  differentiableAt_expansion hs hz

example (hz : z ∈ U) :
    fderiv ℝ g.expansion z (Pi.single 0 1) =
      -g.expansion z ^ 2 / d - g.shearSq z - ricciOf g.coefficient z 0 0 :=
  raychaudhuri hs hz

example (hz : z ∈ U) :
    fderiv ℝ g.expansion z (Pi.single 0 1) ≤
      -g.expansion z ^ 2 / d - ricciOf g.coefficient z 0 0 :=
  raychaudhuri_le hs hz

example (hs : g.IsSynchronous) {z₀ v : MinkowskiModel d} {s : ℝ} (hz : z₀ + s • v ∈ U) :
    HasDerivAt (fun s : ℝ => g.expansion (z₀ + s • v)) (fderiv ℝ g.expansion (z₀ + s • v) v) s :=
  hasDerivAt_expansion_line hs hz

example {z₀ : MinkowskiModel d} (hθ : g.expansion z₀ ≠ 0) :
    (0 : ℝ) < d :=
  dimension_pos_of_expansion_ne_zero hθ

example (hR : ∀ z ∈ U, 0 ≤ ricciOf g.coefficient z 0 0) {z₀ : MinkowskiModel d} (hz₀ : z₀ ∈ U)
    (hθ : g.expansion z₀ < 0) :
    ∃ s ∈ Ioc 0 (d / |g.expansion z₀|), z₀ + s • (Pi.single 0 1 : MinkowskiModel d) ∉ U :=
  exists_notMem_of_ricci_nonneg hs hR hz₀ hθ

example (hR : ∀ z ∈ U, 0 ≤ ricciOf g.coefficient z 0 0) {z₀ : MinkowskiModel d} (hz₀ : z₀ ∈ U)
    (hθ : 0 < g.expansion z₀) :
    ∃ s ∈ Ioc 0 (d / |g.expansion z₀|), z₀ - s • (Pi.single 0 1 : MinkowskiModel d) ∉ U :=
  exists_notMem_of_ricci_nonneg_past hs hR hz₀ hθ

example (hR : ∀ z ∈ U, 0 ≤ ricciOf g.coefficient z 0 0) {z₀ : MinkowskiModel d}
    (hθ : g.expansion z₀ < 0)
    (hline : ∀ s ∈ Ico 0 (d / |g.expansion z₀|), z₀ + s • (Pi.single 0 1 : MinkowskiModel d) ∈ U) :
    Tendsto (fun s : ℝ => g.expansion (z₀ + s • (Pi.single 0 1 : MinkowskiModel d)))
      (𝓝[<] (d / |g.expansion z₀|)) atBot :=
  tendsto_expansion_atBot hs hR hθ hline

end IsSynchronous

end CoordinateMetric

end ProjectAinos.SmoothGeometry

end Focusing

section EnergyCondition

open Set Filter TopologicalSpace ContinuousLinearMap

open scoped Manifold ContDiff Topology

namespace ProjectAinos.GeneralRelativity

open SmoothGeometry LorentzMetric CoordinateMetric

local notation "E" => MinkowskiModel 3

local notation "I" => 𝓘(ℝ, MinkowskiModel 3)

variable {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold I ∞ M]

example (g : LorentzMetric .timeNegative 3 M) (T : Tensor.SmoothBilinear («I» := I) (M := M)) :
    Prop :=
  StrongEnergyCondition g T

namespace StrongEnergyCondition

variable {g : LorentzMetric .timeNegative 3 M} {T : Tensor.SmoothBilinear («I» := I) (M := M)}

example (hT : ∀ x, T x = 0) :
    StrongEnergyCondition g T :=
  of_eq_zero hT

example (u : ∀ x : M, TangentSpace I x) (ρ p : M → ℝ)
    (hT : ∀ x, T x = (ρ x + p x) • (g.form x (u x)).smulRight (g.form x (u x)) + p x • g.form x)
    (hu : ∀ x, g.form x (u x) (u x) = -1) (h1 : ∀ x, 0 ≤ ρ x + p x) (h3 : ∀ x, 0 ≤ ρ x + 3 * p x) :
    StrongEnergyCondition g T :=
  perfectFluid u ρ p hT hu h1 h3

example (u : ∀ x : M, TangentSpace I x) (ρ : M → ℝ)
    (hT : ∀ x, T x = ρ x • (g.form x (u x)).smulRight (g.form x (u x)))
    (hu : ∀ x, g.form x (u x) (u x) = -1) (hρ : ∀ x, 0 ≤ ρ x) :
    StrongEnergyCondition g T :=
  dust u ρ hT hu hρ

end StrongEnergyCondition

example (g : LorentzMetric .timeNegative 3 M) :
    StrongEnergyCondition g 0 :=
  strongEnergyCondition_zero g

example {g : LorentzMetric .timeNegative 3 M} {κ Λ : ℝ}
    {T : Tensor.SmoothBilinear («I» := I) (M := M)} (hE : g.SatisfiesEinstein κ Λ T)
    (hT : StrongEnergyCondition g T) (hκ : 0 ≤ κ) (hΛ : Λ ≤ 0) (x : M) {v : TangentSpace I x}
    (hv : g.form x v v < 0) :
    0 ≤ g.ricci x v v :=
  SatisfiesEinstein.ricci_timelike_nonneg hE hT hκ hΛ x hv

namespace IsSynchronous

variable {U : Opens E} {g : CoordinateMetric .timeNegative 3 U} (hs : g.IsSynchronous)
  {κ Λ : ℝ} {T : Tensor.SmoothBilinear («I» := I) (M := U)}

include hs

example (hE : g.toLorentzMetric.SatisfiesEinstein κ Λ T)
    (hT : StrongEnergyCondition g.toLorentzMetric T) (hκ : 0 ≤ κ) (hΛ : Λ ≤ 0) {z : E}
    (hz : z ∈ U) :
    0 ≤ ricciOf g.coefficient z 0 0 :=
  ricci_zero_zero_nonneg hs hE hT hκ hΛ hz

example (hE : g.toLorentzMetric.SatisfiesEinstein κ Λ T)
    (hT : StrongEnergyCondition g.toLorentzMetric T) (hκ : 0 ≤ κ) (hΛ : Λ ≤ 0) {z : E}
    (hz : z ∈ U) :
    fderiv ℝ g.expansion z (Pi.single 0 1) ≤ -g.expansion z ^ 2 / 3 :=
  raychaudhuri_le_of_einstein hs hE hT hκ hΛ hz

example (hE : g.toLorentzMetric.SatisfiesEinstein κ Λ T)
    (hT : StrongEnergyCondition g.toLorentzMetric T) (hκ : 0 ≤ κ) (hΛ : Λ ≤ 0) {z₀ : E}
    (hz₀ : z₀ ∈ U) (hθ : g.expansion z₀ < 0) :
    ∃ s ∈ Ioc 0 (3 / |g.expansion z₀|), z₀ + s • (Pi.single 0 1 : E) ∉ U :=
  exists_notMem_of_focusing hs hE hT hκ hΛ hz₀ hθ

example (hE : g.toLorentzMetric.SatisfiesEinstein κ Λ T)
    (hT : StrongEnergyCondition g.toLorentzMetric T) (hκ : 0 ≤ κ) (hΛ : Λ ≤ 0) {z₀ : E}
    (hz₀ : z₀ ∈ U) (hθ : 0 < g.expansion z₀) :
    ∃ s ∈ Ioc 0 (3 / |g.expansion z₀|), z₀ - s • (Pi.single 0 1 : E) ∉ U :=
  exists_notMem_of_focusing_past hs hE hT hκ hΛ hz₀ hθ

end IsSynchronous

namespace Kasner

variable {D : Kasner.Data}

example {z : E} (hz : z ∈ Kasner.domain D) :
    (Kasner.metric D).expansion z = Kasner.expansion D (z 0) :=
  expansion_metric hz

example (x v : E) :
    (Kasner.metric D).form x (Pi.single 0 1) v = -v 0 :=
  form_timeAxis x v

example (ρ p : ℝ → ℝ)
    (hT : ∀ i k, ContDiffOn ℝ ∞ (fun x => Kasner.perfectFluidStress D ρ p x i k)
      (Kasner.domain D))
    (h1 : ∀ t ∈ D.I, 0 ≤ ρ t + p t) (h3 : ∀ t ∈ D.I, 0 ≤ ρ t + 3 * p t) :
    StrongEnergyCondition (Kasner.metric D).toLorentzMetric
      (bilinearOf (Kasner.perfectFluidStress D ρ p) hT) :=
  strongEnergyCondition_perfectFluidStress ρ p hT h1 h3

example {ρ p : ℝ → ℝ} (hρ : ContDiffOn ℝ ∞ ρ D.I) (hp : ContDiffOn ℝ ∞ p D.I) (i k : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => Kasner.perfectFluidStress D ρ p x i k) (Kasner.domain D) :=
  contDiffOn_perfectFluidStress hρ hp i k

example {κ t₀ : ℝ} (hκ : κ ≠ 0) (ht₀ : 0 ≤ t₀) :
    ContDiffOn ℝ ∞ (Kasner.dustDensity κ t₀) (Ioi 0) :=
  contDiffOn_dustDensity hκ ht₀

example {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {t : ℝ} (ht : 0 < t) :
    Kasner.expansion (Kasner.dustKasner p t₀ ht₀) t = 1 / t + 1 / (t + t₀) :=
  expansion_dustKasner h1 ht₀ ht

example {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    {z₀ : E} (hz₀ : z₀ ∈ Kasner.domain (Kasner.dustKasner p t₀ ht₀)) :
    (Kasner.metric (Kasner.dustKasner p t₀ ht₀)).expansion z₀ = 1 / z₀ 0 + 1 / (z₀ 0 + t₀) ∧
      ∃ s ∈ Ioc 0 (3 / |(Kasner.metric (Kasner.dustKasner p t₀ ht₀)).expansion z₀|),
        z₀ - s • (Pi.single 0 1 : E) ∉ Kasner.domain (Kasner.dustKasner p t₀ ht₀) :=
  dustKasner_exists_notMem_past h1 h2 ht₀ hz₀

example (D : Kasner.Data) :
    Kasner.Data :=
  Data.reverse D

example (α : Fin 3) (t : ℝ) :
    Kasner.hubble D.reverse α t = -Kasner.hubble D α (-t) :=
  hubble_reverse α t

example (α : Fin 3) (t : ℝ) :
    Kasner.accel D.reverse α t = Kasner.accel D α (-t) :=
  accel_reverse α t

example {κ Λ : ℝ} {ρ p : ℝ → ℝ}
    (h : (Kasner.metric D).IsEinstein κ Λ (Kasner.perfectFluidStress D ρ p)) :
    (Kasner.metric D.reverse).IsEinstein κ Λ
      (Kasner.perfectFluidStress D.reverse (fun t => ρ (-t)) (fun t => p (-t))) :=
  isEinstein_reverse h

example {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    {z₀ : E} (hz₀ : z₀ ∈ Kasner.domain (Kasner.dustKasner p t₀ ht₀).reverse) :
    (Kasner.metric (Kasner.dustKasner p t₀ ht₀).reverse).expansion z₀ =
        -(1 / -z₀ 0 + 1 / (-z₀ 0 + t₀)) ∧
      ∃ s ∈ Ioc 0 (3 / |(Kasner.metric (Kasner.dustKasner p t₀ ht₀).reverse).expansion z₀|),
        z₀ + s • (Pi.single 0 1 : E) ∉ Kasner.domain (Kasner.dustKasner p t₀ ht₀).reverse :=
  reverse_dustKasner_exists_notMem h1 h2 ht₀ hz₀

end Kasner

example (κ : ℝ) :
    DeSitterSlicing.metric.IsSynchronous ∧
      DeSitterSlicing.metric.toLorentzMetric.SatisfiesEinstein κ 3 0 ∧
      StrongEnergyCondition DeSitterSlicing.metric.toLorentzMetric 0 ∧
      (∀ z, DeSitterSlicing.metric.expansion z = 3) ∧
      (∀ z, ricciOf DeSitterSlicing.metric.coefficient z 0 0 = -3) ∧
      ¬ ∃ z₀ : E, ∃ s : ℝ, z₀ - s • (Pi.single 0 1 : E) ∉ (⊤ : Opens E) :=
  deSitter_not_focusing κ

end ProjectAinos.GeneralRelativity

end EnergyCondition
