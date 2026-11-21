/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.Focusing
public import ProjectAinos.GeneralRelativity.Kasner
public import ProjectAinos.GeneralRelativity.DeSitterSlicing

/-!
# The strong energy condition and the focusing of the synchronous time lines

Landau–Lifshitz, §97, (97.14)–(97.15), and §119, with `c = 1` and the signature `(−+++)`. The
**strong energy condition** on an energy–momentum tensor `T` is
`(T_{ab} − ½ T^c{}_c g_{ab}) v^a v^b ≥ 0` for every timelike `v` (`StrongEnergyCondition`).
With the Einstein equations `G + Λ g = κ T` in the trace-reversed form
`Ric = κ (T − ½ T^c{}_c g) + Λ g`, `κ ≥ 0` and `Λ ≤ 0`, it gives `Ric(v, v) ≥ 0` for every
timelike `v` (`SatisfiesEinstein.ricci_timelike_nonneg`). In the signature `(−+++)` with the
Ricci tensor `R_{jk} = ∂_i Γ^i_{jk} − …` of the library, a homogeneous isotropic dust has
`R_{00} = −3ä/a = κ ρ/2 − Λ`.

* `StrongEnergyCondition.of_eq_zero`, `strongEnergyCondition_zero`: the vacuum;
  `StrongEnergyCondition.perfectFluid`: the perfect fluid
  `T = (ρ + p) u♭ ⊗ u♭ + p g` with `g(u, u) = −1`, `ρ + p ≥ 0` and `ρ + 3p ≥ 0`;
  `StrongEnergyCondition.dust`: dust with `ρ ≥ 0`.
* `Kasner.strongEnergyCondition_perfectFluidStress`: the comoving perfect fluid of the flat
  anisotropic model, a co-ordinate instance.
* `IsSynchronous.ricci_zero_zero_nonneg`, `IsSynchronous.raychaudhuri_le_of_einstein`: in a
  synchronous system with the Einstein equations, the strong energy condition, `κ ≥ 0` and
  `Λ ≤ 0`, `R_{00} ≥ 0` and `∂_t θ ≤ −θ²/3` for the expansion `θ = ½ κ^α_α` (Landau–Lifshitz,
  (97.14) in terms of `κ^α_α = 2θ`).
* `IsSynchronous.exists_notMem_of_focusing`: **the synchronous co-ordinates break down within
  the proper time `3/|θ(z₀)|`** of a point with `θ(z₀) < 0` (Landau–Lifshitz, (97.15)); the time
  line leaves the domain. `IsSynchronous.exists_notMem_of_focusing_past`: towards the past for
  `θ(z₀) > 0`.
* `Kasner.expansion_metric`: the expansion of the flat anisotropic model is `Σ_α ȧ_α/a_α`;
  `Kasner.dustKasner_exists_notMem_past`: the dust model of `Kasner.dustKasner` is an instance
  of the focusing theorem towards the past, with `θ = 1/t + 1/(t + t₀) > 0`
  (`Kasner.expansion_dustKasner`).
* `Kasner.Data.reverse`, `Kasner.hubble_reverse`, `Kasner.accel_reverse`,
  `Kasner.isEinstein_reverse`: the time reversal `t ↦ −t` of the model, which keeps the Einstein
  equations with the comoving fluid; `Kasner.reverse_dustKasner_exists_notMem`: **the
  contracting dust model is an instance of the focusing theorem**, with
  `θ = −(1/|t| + 1/(|t| + t₀)) < 0`.
* `deSitter_not_focusing`: **the role of `Λ ≤ 0`**: de Sitter space in the flat slicing is
  synchronous, solves the vacuum equations with `Λ = 3` and has `θ = 3 > 0`, but its time lines
  are complete towards the past; its `R_{00} = −3` is negative.

What the focusing theorem does not give is a singularity of the space-time: the breakdown of the
co-ordinates is a caustic of the normal geodesics, which may be a fictitious singularity of the
reference system (Landau–Lifshitz, §97). Geodesic incompleteness (the singularity theorems of
Penrose and Hawking) needs the global causal theory of a time-oriented space-time, and the
structure of the general solution near a physical singularity is the oscillatory regime of
§119.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAinos.GeneralRelativity

open SmoothGeometry LorentzMetric CoordinateMetric

local notation "E" => MinkowskiModel 3
local notation "I" => 𝓘(ℝ, MinkowskiModel 3)

variable {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold I ∞ M]

/-! ### The strong energy condition -/

/-- **The strong energy condition** on an energy–momentum tensor `T`:
`(T_{ab} − ½ T^c{}_c g_{ab}) v^a v^b ≥ 0` for every timelike vector `v`, `g(v, v) < 0`. -/
def StrongEnergyCondition (g : LorentzMetric .timeNegative 3 M)
    (T : Tensor.SmoothBilinear («I» := I) (M := M)) : Prop :=
  ∀ x (v : TangentSpace I x), g.form x v v < 0 →
    0 ≤ T x v v - g.contract x (T x) / 2 * g.form x v v

namespace StrongEnergyCondition

variable {g : LorentzMetric .timeNegative 3 M} {T : Tensor.SmoothBilinear («I» := I) (M := M)}

/-- **The vacuum** satisfies the strong energy condition. -/
theorem of_eq_zero (hT : ∀ x, T x = 0) : StrongEnergyCondition g T := by
  intro x v _
  have h0 : g.contract x (T x) = 0 := by
    rw [hT x]
    simp [contract]
  rw [h0, hT x]
  simp

/-- **The perfect fluid** `T = (ρ + p) u♭ ⊗ u♭ + p g` with a unit timelike velocity `u`,
`ρ + p ≥ 0` and `ρ + 3p ≥ 0` satisfies the strong energy condition: its trace is `3p − ρ`, and
`(T − ½ T^c{}_c g)(v, v) = (ρ + p) g(u, v)² + ½ (ρ − p) g(v, v) ≥ ½ (ρ + 3p) |g(v, v)|` by the
reversed Cauchy–Schwarz inequality `g(u, v)² ≥ −g(v, v)`. -/
theorem perfectFluid (u : ∀ x : M, TangentSpace I x) (ρ p : M → ℝ)
    (hT : ∀ x, T x = (ρ x + p x) • (g.form x (u x)).smulRight (g.form x (u x)) + p x • g.form x)
    (hu : ∀ x, g.form x (u x) (u x) = -1) (h1 : ∀ x, 0 ≤ ρ x + p x)
    (h3 : ∀ x, 0 ≤ ρ x + 3 * p x) : StrongEnergyCondition g T := by
  intro x v hv
  have hflat : g.form x (u x) = g.flat x (u x) := rfl
  have hc : g.contract x (T x) = 3 * p x - ρ x := by
    rw [hT x, g.contract_add, g.contract_smul, g.contract_smul, contract_smulRight, hflat,
      g.sharp_flat, ← hflat, hu x, contract_metric]
    norm_num
    ring
  have hTv : T x v v = (ρ x + p x) * (g.form x (u x) v * g.form x (u x) v) +
      p x * g.form x v v := by
    rw [hT x]
    simp only [add_apply, smul_apply, smulRight_apply, smul_eq_mul]
  have hcs : 0 ≤ g.form x v v - g.form x (u x) v * g.form x (u x) v / g.form x (u x) (u x) :=
    (g.spatialForm_nonneg x (u := u x) (by rw [hu x]; norm_num) v).trans_eq
      (Minkowski.spatialForm_apply _ _ _ _)
  rw [hu x] at hcs
  have hcs' : 0 ≤ g.form x v v + g.form x (u x) v * g.form x (u x) v := by
    norm_num at hcs
    linarith
  rw [hTv, hc]
  nlinarith [mul_nonneg (h1 x) hcs', mul_nonneg (h3 x) (neg_nonneg.mpr hv.le)]

/-- **Dust** `T = ρ u♭ ⊗ u♭` with a unit timelike velocity `u` and `ρ ≥ 0` satisfies the strong
energy condition. -/
theorem dust (u : ∀ x : M, TangentSpace I x) (ρ : M → ℝ)
    (hT : ∀ x, T x = ρ x • (g.form x (u x)).smulRight (g.form x (u x)))
    (hu : ∀ x, g.form x (u x) (u x) = -1) (hρ : ∀ x, 0 ≤ ρ x) : StrongEnergyCondition g T :=
  perfectFluid u ρ 0 (fun x => by ext v w; simp [hT x]) hu (fun x => by simpa using hρ x)
    (fun x => by simpa using hρ x)

end StrongEnergyCondition

/-- The vacuum `T = 0` satisfies the strong energy condition. -/
theorem strongEnergyCondition_zero (g : LorentzMetric .timeNegative 3 M) :
    StrongEnergyCondition g 0 :=
  StrongEnergyCondition.of_eq_zero fun _ => rfl

/-! ### The convergence of timelike geodesics -/

/-- **The timelike convergence condition** (Landau–Lifshitz, §97): with the Einstein equations
`G + Λ g = κ T`, the strong energy condition, `κ ≥ 0` and `Λ ≤ 0`, `Ric(v, v) ≥ 0` for every
timelike `v`, since `Ric(v, v) = κ (T − ½ T^c{}_c g)(v, v) + Λ g(v, v)`. -/
theorem SatisfiesEinstein.ricci_timelike_nonneg {g : LorentzMetric .timeNegative 3 M}
    {κ Λ : ℝ} {T : Tensor.SmoothBilinear («I» := I) (M := M)} (hE : g.SatisfiesEinstein κ Λ T)
    (hT : StrongEnergyCondition g T) (hκ : 0 ≤ κ) (hΛ : Λ ≤ 0) (x : M) {v : TangentSpace I x}
    (hv : g.form x v v < 0) : 0 ≤ g.ricci x v v := by
  have h := congrArg (fun B : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ => B v v)
    (hE.ricci_eq_four rfl x)
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul] at h
  rw [h]
  have h1 := hT x v hv
  have h2 : 0 ≤ Λ * g.form x v v := mul_nonneg_of_nonpos_of_nonpos hΛ hv.le
  nlinarith [mul_nonneg hκ h1]

/-! ### Focusing in a synchronous reference system -/

namespace IsSynchronous

variable {U : Opens E} {g : CoordinateMetric .timeNegative 3 U} (hs : g.IsSynchronous)
  {κ Λ : ℝ} {T : Tensor.SmoothBilinear («I» := I) (M := U)}
include hs

/-- **`R_{00} ≥ 0`** in a synchronous system with the Einstein equations, the strong energy
condition, `κ ≥ 0` and `Λ ≤ 0`: the time direction is timelike. -/
theorem ricci_zero_zero_nonneg (hE : g.toLorentzMetric.SatisfiesEinstein κ Λ T)
    (hT : StrongEnergyCondition g.toLorentzMetric T) (hκ : 0 ≤ κ) (hΛ : Λ ≤ 0)
    {z : E} (hz : z ∈ U) : 0 ≤ ricciOf g.coefficient z 0 0 := by
  have hv : g.toLorentzMetric.form ⟨z, hz⟩
      (chartField (physicalChart ⟨z, hz⟩) (Pi.single 0 1) ⟨z, hz⟩)
      (chartField (physicalChart ⟨z, hz⟩) (Pi.single 0 1) ⟨z, hz⟩) < 0 := by
    have h := g.toLorentzMetric_chartComponent ⟨z, hz⟩ ⟨z, hz⟩ 0 0
    rw [chartComponent] at h
    rw [h]
    change g.coefficient z 0 0 < 0
    rw [(hs z hz).1]
    norm_num
  have h := SatisfiesEinstein.ricci_timelike_nonneg hE hT hκ hΛ ⟨z, hz⟩ hv
  rwa [toLorentzMetric_ricci_chartField] at h

/-- **The focusing inequality** (Landau–Lifshitz, (97.14)): `∂_t θ ≤ −θ²/3`. -/
theorem raychaudhuri_le_of_einstein (hE : g.toLorentzMetric.SatisfiesEinstein κ Λ T)
    (hT : StrongEnergyCondition g.toLorentzMetric T) (hκ : 0 ≤ κ) (hΛ : Λ ≤ 0)
    {z : E} (hz : z ∈ U) :
    fderiv ℝ g.expansion z (Pi.single 0 1) ≤ -g.expansion z ^ 2 / 3 := by
  have h := hs.raychaudhuri_le hz
  have h0 := ricci_zero_zero_nonneg hs hE hT hκ hΛ hz
  norm_num at h
  linarith

/-- **The synchronous co-ordinates break down** (Landau–Lifshitz, (97.15)): with the Einstein
equations, the strong energy condition, `κ ≥ 0` and `Λ ≤ 0`, the time line from a point `z₀`
with `θ(z₀) < 0` leaves the domain at a proper time `s ≤ 3/|θ(z₀)|`. -/
theorem exists_notMem_of_focusing (hE : g.toLorentzMetric.SatisfiesEinstein κ Λ T)
    (hT : StrongEnergyCondition g.toLorentzMetric T) (hκ : 0 ≤ κ) (hΛ : Λ ≤ 0)
    {z₀ : E} (hz₀ : z₀ ∈ U) (hθ : g.expansion z₀ < 0) :
    ∃ s ∈ Ioc 0 (3 / |g.expansion z₀|), z₀ + s • (Pi.single 0 1 : E) ∉ U := by
  have h := hs.exists_notMem_of_ricci_nonneg
    (fun z hz => ricci_zero_zero_nonneg hs hE hT hκ hΛ hz) hz₀ hθ
  norm_num at h
  simpa using h

/-- **The synchronous co-ordinates break down towards the past**: with the same hypotheses, the
time line from a point `z₀` with `θ(z₀) > 0` leaves the domain towards the past at a proper time
`s ≤ 3/|θ(z₀)|`. -/
theorem exists_notMem_of_focusing_past (hE : g.toLorentzMetric.SatisfiesEinstein κ Λ T)
    (hT : StrongEnergyCondition g.toLorentzMetric T) (hκ : 0 ≤ κ) (hΛ : Λ ≤ 0)
    {z₀ : E} (hz₀ : z₀ ∈ U) (hθ : 0 < g.expansion z₀) :
    ∃ s ∈ Ioc 0 (3 / |g.expansion z₀|), z₀ - s • (Pi.single 0 1 : E) ∉ U := by
  have h := hs.exists_notMem_of_ricci_nonneg_past
    (fun z hz => ricci_zero_zero_nonneg hs hE hT hκ hΛ hz) hz₀ hθ
  norm_num at h
  simpa using h

end IsSynchronous

/-! ### Instances: the flat anisotropic model -/

namespace Kasner

variable {D : Kasner.Data}

/-- **The expansion of the flat anisotropic model** is `θ = Σ_α ȧ_α/a_α`. -/
theorem expansion_metric {z : E} (hz : z ∈ Kasner.domain D) :
    (Kasner.metric D).expansion z = Kasner.expansion D (z 0) := by
  have h (α : Fin 3) : (Kasner.metric D).extrinsicRate z α α = 2 * Kasner.hubble D α (z 0) := by
    have h1 := Kasner.isSynchronous.christoffel_succ_zero_succ hz α α
    rw [Kasner.christoffelOf_succ_zero_succ hz] at h1
    simp only [↓reduceIte] at h1
    rw [Kasner.hubble]
    linarith
  rw [CoordinateMetric.expansion, Kasner.expansion]
  simp only [h, ← Finset.mul_sum]
  ring

/-- The time axis `e₀` lowered by the flat anisotropic metric is `−dt`. -/
theorem form_timeAxis (x v : E) : (Kasner.metric D).form x (Pi.single 0 1) v = -v 0 := by
  rw [form_apply, Kasner.coefficient_metric]
  simp [Fin.sum_univ_four, Matrix.diagonal_apply, Kasner.coefficients]

/-- **The comoving perfect fluid of the flat anisotropic model satisfies the strong energy
condition** when `ρ + p ≥ 0` and `ρ + 3p ≥ 0` on the times of the model. -/
theorem strongEnergyCondition_perfectFluidStress (ρ p : ℝ → ℝ)
    (hT : ∀ i k, ContDiffOn ℝ ∞ (fun x => Kasner.perfectFluidStress D ρ p x i k)
      (Kasner.domain D))
    (h1 : ∀ t ∈ D.I, 0 ≤ ρ t + p t) (h3 : ∀ t ∈ D.I, 0 ≤ ρ t + 3 * p t) :
    StrongEnergyCondition (Kasner.metric D).toLorentzMetric
      (bilinearOf (Kasner.perfectFluidStress D ρ p) hT) := by
  refine StrongEnergyCondition.perfectFluid (fun _ => Pi.single 0 1)
    (fun x => ρ ((x : E) 0)) (fun x => p ((x : E) 0)) (fun x => ?_) (fun x => ?_)
    (fun x => h1 _ (Kasner.time_mem x.property)) (fun x => h3 _ (Kasner.time_mem x.property))
  · ext v w
    have hvw : ∀ v w : E, coefficientForm (Kasner.perfectFluidStress D ρ p) (x : E) v w =
        (ρ ((x : E) 0) + p ((x : E) 0)) * ((Kasner.metric D).form x (Pi.single 0 1) v *
          (Kasner.metric D).form x (Pi.single 0 1) w) +
        p ((x : E) 0) * (Kasner.metric D).form x v w := by
      intro v w
      rw [coefficientForm_apply, form_timeAxis, form_timeAxis, form_apply]
      simp only [Kasner.perfectFluidStress, Matrix.of_apply, Kasner.fluidCovector]
      simp [Fin.sum_univ_four]
      ring
    exact hvw v w
  · change (Kasner.metric D).form x (Pi.single 0 1) (Pi.single 0 1) = -1
    rw [form_timeAxis]
    simp

/-- The stress of the comoving fluid is smooth on the domain for smooth `ρ` and `p`. -/
theorem contDiffOn_perfectFluidStress {ρ p : ℝ → ℝ} (hρ : ContDiffOn ℝ ∞ ρ D.I)
    (hp : ContDiffOn ℝ ∞ p D.I) (i k : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => Kasner.perfectFluidStress D ρ p x i k) (Kasner.domain D) := by
  simp only [Kasner.perfectFluidStress, Matrix.of_apply]
  exact ((Kasner.contDiffOn_time hρ).add (Kasner.contDiffOn_time hp)).mul contDiffOn_const
    |>.mul contDiffOn_const |>.add
      ((Kasner.contDiffOn_time hp).mul ((Kasner.metric D).coefficient_contDiffOn i k))

/-- The density `4/(3κ t (t + t₀))` of the dust model is smooth for `t > 0`. -/
theorem contDiffOn_dustDensity {κ t₀ : ℝ} (hκ : κ ≠ 0) (ht₀ : 0 ≤ t₀) :
    ContDiffOn ℝ ∞ (Kasner.dustDensity κ t₀) (Ioi 0) := by
  have h : Kasner.dustDensity κ t₀ = fun t => 4 / (3 * κ * t * (t + t₀)) := rfl
  rw [h]
  refine contDiffOn_const.div (by fun_prop) fun t ht => ?_
  have ht' : 0 < t := ht
  have : 0 < t + t₀ := by linarith
  positivity

/-- The expansion of the dust model is `θ = 1/t + 1/(t + t₀)`. -/
theorem expansion_dustKasner {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    {t : ℝ} (ht : 0 < t) :
    Kasner.expansion (Kasner.dustKasner p t₀ ht₀) t = 1 / t + 1 / (t + t₀) := by
  rw [Kasner.expansion]
  simp only [Kasner.hubble_dustKasner ht₀ _ ht]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, h1, Finset.sum_sub_distrib, h1]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- **The dust model is an instance of focusing towards the past**: for Kasner exponents
(`Σp = Σp² = 1`) and `t₀ ≥ 0`, the dust metric of `Kasner.dustKasner` with `κ = 1` satisfies the
Einstein equations with `Λ = 0` and the strong energy condition, its expansion is
`θ = 1/t + 1/(t + t₀) > 0`, and the time line from every point leaves the domain towards the
past within the proper time `3/θ`. -/
theorem dustKasner_exists_notMem_past {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1)
    (h2 : ∑ α, p α ^ 2 = 1) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {z₀ : E}
    (hz₀ : z₀ ∈ Kasner.domain (Kasner.dustKasner p t₀ ht₀)) :
    (Kasner.metric (Kasner.dustKasner p t₀ ht₀)).expansion z₀ = 1 / z₀ 0 + 1 / (z₀ 0 + t₀) ∧
      ∃ s ∈ Ioc 0 (3 / |(Kasner.metric (Kasner.dustKasner p t₀ ht₀)).expansion z₀|),
        z₀ - s • (Pi.single 0 1 : E) ∉ Kasner.domain (Kasner.dustKasner p t₀ ht₀) := by
  have ht : 0 < z₀ 0 := hz₀
  have hθ : (Kasner.metric (Kasner.dustKasner p t₀ ht₀)).expansion z₀ =
      1 / z₀ 0 + 1 / (z₀ 0 + t₀) := by
    rw [expansion_metric hz₀, expansion_dustKasner h1 ht₀ ht]
  have hpos : 0 < (Kasner.metric (Kasner.dustKasner p t₀ ht₀)).expansion z₀ := by
    rw [hθ]
    have : 0 < z₀ 0 + t₀ := by linarith
    positivity
  have hT := contDiffOn_perfectFluidStress (D := Kasner.dustKasner p t₀ ht₀) (p := 0)
    (contDiffOn_dustDensity one_ne_zero ht₀) contDiffOn_const
  have hE := (satisfiesEinstein_bilinearOf_iff hT 1 0).mpr
    (Kasner.isEinstein_dustKasner ht₀ h1 h2 one_ne_zero)
  have hS := strongEnergyCondition_perfectFluidStress (D := Kasner.dustKasner p t₀ ht₀) _ _ hT
    (fun t ht' => by simpa using (Kasner.dustDensity_pos one_pos ht₀ ht').le)
    (fun t ht' => by simpa using (Kasner.dustDensity_pos one_pos ht₀ ht').le)
  exact ⟨hθ, IsSynchronous.exists_notMem_of_focusing_past Kasner.isSynchronous hE hS
    zero_le_one le_rfl hz₀ hpos⟩

/-! ### The time reversal and the contracting dust model -/

/-- **The time reversal** of the data: the times `−I` and the scale factors `t ↦ a_α(−t)`. -/
def Data.reverse (D : Kasner.Data) : Kasner.Data :=
  ⟨Neg.neg ⁻¹' D.I, fun α t => D.a α (-t), D.isOpen_I.preimage continuous_neg,
    fun α => (D.contDiffOn_a α).comp contDiff_neg.contDiffOn fun _ ht => ht,
    fun α t ht => D.a_pos α (-t) ht⟩

/-- The Hubble rates change sign under the time reversal. -/
theorem hubble_reverse (α : Fin 3) (t : ℝ) :
    Kasner.hubble D.reverse α t = -Kasner.hubble D α (-t) := by
  simp only [Kasner.hubble, Data.reverse]
  rw [deriv_comp_neg]
  ring

/-- The relative accelerations are invariant under the time reversal. -/
theorem accel_reverse (α : Fin 3) (t : ℝ) :
    Kasner.accel D.reverse α t = Kasner.accel D α (-t) := by
  simp only [Kasner.accel, Data.reverse]
  have h : deriv (fun s => D.a α (-s)) = fun s => -deriv (D.a α) (-s) :=
    funext fun s => deriv_comp_neg (D.a α) s
  rw [h, deriv.fun_neg, deriv_comp_neg, neg_neg]

/-- **The time-reversed comoving fluid solves the Einstein equations** when the fluid does:
the constraint and the evolution equations are even in the Hubble rates. -/
theorem isEinstein_reverse {κ Λ : ℝ} {ρ p : ℝ → ℝ}
    (h : (Kasner.metric D).IsEinstein κ Λ (Kasner.perfectFluidStress D ρ p)) :
    (Kasner.metric D.reverse).IsEinstein κ Λ
      (Kasner.perfectFluidStress D.reverse (fun t => ρ (-t)) (fun t => p (-t))) := by
  rw [Kasner.isEinstein_iff] at h ⊢
  intro t ht
  obtain ⟨hc, he⟩ := h (-t) ht
  refine ⟨?_, fun α => ?_⟩
  · have hp : Kasner.hubblePairs D.reverse t = Kasner.hubblePairs D (-t) := by
      simp only [Kasner.hubblePairs, hubble_reverse]
      ring
    unfold Kasner.Constraint at hc ⊢
    rw [hp]
    exact hc
  · have hf : Kasner.spatialFactor D.reverse t = Kasner.spatialFactor D (-t) := by
      simp only [Kasner.spatialFactor, hubble_reverse, accel_reverse, neg_mul_neg]
    unfold Kasner.Evolution at he ⊢
    rw [hf]
    exact he α

/-- **The contracting dust model is an instance of focusing**: the time reversal of the dust
model of `Kasner.dustKasner`, on `t < 0` with `κ = 1`, satisfies the Einstein equations with
`Λ = 0` and the strong energy condition, its expansion is `θ = −(1/|t| + 1/(|t| + t₀)) < 0`, and
the time line from every point leaves the domain within the proper time `3/|θ|`. -/
theorem reverse_dustKasner_exists_notMem {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1)
    (h2 : ∑ α, p α ^ 2 = 1) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {z₀ : E}
    (hz₀ : z₀ ∈ Kasner.domain (Kasner.dustKasner p t₀ ht₀).reverse) :
    (Kasner.metric (Kasner.dustKasner p t₀ ht₀).reverse).expansion z₀ =
        -(1 / -z₀ 0 + 1 / (-z₀ 0 + t₀)) ∧
      ∃ s ∈ Ioc 0 (3 / |(Kasner.metric (Kasner.dustKasner p t₀ ht₀).reverse).expansion z₀|),
        z₀ + s • (Pi.single 0 1 : E) ∉ Kasner.domain (Kasner.dustKasner p t₀ ht₀).reverse := by
  have ht : 0 < -z₀ 0 := hz₀
  have hθ : (Kasner.metric (Kasner.dustKasner p t₀ ht₀).reverse).expansion z₀ =
      -(1 / -z₀ 0 + 1 / (-z₀ 0 + t₀)) := by
    rw [expansion_metric hz₀, Kasner.expansion]
    simp only [hubble_reverse, Finset.sum_neg_distrib]
    rw [← Kasner.expansion, expansion_dustKasner h1 ht₀ ht]
  have hneg : (Kasner.metric (Kasner.dustKasner p t₀ ht₀).reverse).expansion z₀ < 0 := by
    rw [hθ, neg_neg_iff_pos]
    have : 0 < -z₀ 0 + t₀ := by linarith
    positivity
  set ρ : ℝ → ℝ := fun t => Kasner.dustDensity 1 t₀ (-t) with hρ
  set q : ℝ → ℝ := fun t => (0 : ℝ → ℝ) (-t) with hq
  have hρs : ContDiffOn ℝ ∞ ρ (Kasner.dustKasner p t₀ ht₀).reverse.I :=
    (contDiffOn_dustDensity one_ne_zero ht₀).comp contDiff_neg.contDiffOn fun _ ht' => ht'
  have hT := contDiffOn_perfectFluidStress (D := (Kasner.dustKasner p t₀ ht₀).reverse) hρs
    (contDiffOn_const (c := (0 : ℝ)))
  have hE := (satisfiesEinstein_bilinearOf_iff hT 1 0).mpr
    (isEinstein_reverse (Kasner.isEinstein_dustKasner ht₀ h1 h2 one_ne_zero))
  have hS := strongEnergyCondition_perfectFluidStress (D := (Kasner.dustKasner p t₀ ht₀).reverse)
    ρ q hT
    (fun t ht' => by simpa [hρ, hq] using (Kasner.dustDensity_pos one_pos ht₀ ht').le)
    (fun t ht' => by simpa [hρ, hq] using (Kasner.dustDensity_pos one_pos ht₀ ht').le)
  exact ⟨hθ, IsSynchronous.exists_notMem_of_focusing Kasner.isSynchronous hE hS
    zero_le_one le_rfl hz₀ hneg⟩

end Kasner

/-! ### A non-instance: de Sitter space -/

/-- **The role of `Λ ≤ 0`**: de Sitter space `−dt² + e^{2t}(dx² + dy² + dz²)` is synchronous,
solves the vacuum Einstein equations with `Λ = 3 > 0` for every `κ`, satisfies the strong energy
condition (it has no matter) and has the expansion `θ = 3 > 0` everywhere; yet its time lines
never leave the domain `ℝ⁴` towards the past, so the conclusion of
`IsSynchronous.exists_notMem_of_focusing_past` fails. The time component of its Ricci tensor is
`R_{00} = −3 < 0`. -/
theorem deSitter_not_focusing (κ : ℝ) :
    DeSitterSlicing.metric.IsSynchronous ∧
      DeSitterSlicing.metric.toLorentzMetric.SatisfiesEinstein κ 3 0 ∧
      StrongEnergyCondition DeSitterSlicing.metric.toLorentzMetric 0 ∧
      (∀ z, DeSitterSlicing.metric.expansion z = 3) ∧
      (∀ z, ricciOf DeSitterSlicing.metric.coefficient z 0 0 = -3) ∧
      ¬ ∃ z₀ : E, ∃ s : ℝ, z₀ - s • (Pi.single 0 1 : E) ∉ (⊤ : Opens E) := by
  have hric (y : (⊤ : Opens E)) : DeSitterSlicing.metric.toLorentzMetric.ricci y =
      (3 : ℝ) • DeSitterSlicing.metric.toLorentzMetric.form y := by
    refine ext_chartField (physicalChart_mem y) (by simp) fun i => ?_
    refine ext_chartField (physicalChart_mem y) (by simp) fun k => ?_
    rw [toLorentzMetric_ricci_chartField, smul_apply, smul_apply, smul_eq_mul,
      ← chartComponent, toLorentzMetric_chartComponent, DeSitterSlicing.ricci_eq]
    rfl
  refine ⟨DeSitterSlicing.isSynchronous, fun y => ?_, strongEnergyCondition_zero _,
    fun z => ?_, fun z => ?_, fun ⟨z₀, s, h⟩ => h trivial⟩
  · have hS : DeSitterSlicing.metric.toLorentzMetric.scalarCurvature y = 12 := by
      rw [scalarCurvature_apply, hric, contract_smul, contract_metric]
      norm_num
    ext v w
    have h0 : ((0 : Tensor.SmoothBilinear («I» := I) (M := (⊤ : Opens E))) y) v w = 0 := rfl
    simp only [add_apply, smul_apply, einstein_apply, hric, hS, smul_eq_mul, h0]
    ring
  · rw [CoordinateMetric.expansion]
    simp only [DeSitterSlicing.extrinsicRate_eq, ↓reduceIte, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    norm_num
  · rw [DeSitterSlicing.ricci_eq, (DeSitterSlicing.isSynchronous z trivial).1]
    norm_num

end ProjectAinos.GeneralRelativity
