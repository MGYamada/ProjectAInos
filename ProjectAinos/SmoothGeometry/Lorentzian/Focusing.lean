/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.Synchronous
public import ProjectAinos.SmoothGeometry.ODE.RiccatiComparison
public import Mathlib.Analysis.Matrix.Order

/-!
# The focusing of the time lines of a synchronous reference system

Landau–Lifshitz, §97, (97.14)–(97.15), and §119. In a synchronous reference system
`ds² = −dt² + γ_{αβ} dx^α dx^β` (`CoordinateMetric.IsSynchronous`), the time lines are geodesics
normal to the slices `t = const`; their **expansion** is `θ = ½ κ^α_α = ∂_t log √|g|`
(`CoordinateMetric.expansion`) with `κ^α_β = γ^{αδ} ∂_t γ_{βδ}`, and their **shear** is
`σ_{αβ}σ^{αβ} = ¼ κ^α_β κ^β_α − θ²/d` (`CoordinateMetric.shearSq`) in `d` space dimensions. The
lowered rate `κ_{αβ} = ∂_t γ_{αβ}` is symmetric (`CoordinateMetric.metricRate_symm`): the
congruence is normal to the slices and has no vorticity.

* `Focusing.trace_mul_mul_nonneg`: `tr((PB)²) ≥ 0` for `P` positive semidefinite and `B`
  symmetric.
* `Focusing.trace_sq_ge`: **for `γ` positive definite and `S` symmetric,
  `tr(κ²) ≥ (tr κ)²/d` with `κ = γ⁻¹S`**.
* `IsSynchronous.spatialCoefficient_posDef`, `IsSynchronous.inv_spatialCoefficient`,
  `IsSynchronous.extrinsicRate_eq_mul`: the spatial metric is positive definite, the spatial
  block of the inverse is its inverse, and `κ = γ⁻¹ ∂_tγ`.
* `IsSynchronous.expansion_eq_fderiv_log`: `θ = ∂_t log √|g|`, the rate of the volume
  density.
* `IsSynchronous.shearSq_nonneg`: `σ_{αβ}σ^{αβ} ≥ 0`.
* `IsSynchronous.raychaudhuri`: **the equation of Raychaudhuri for the normal congruence**,
  `∂_t θ = −θ²/d − σ_{αβ}σ^{αβ} − R_{00}`, the equation (97.11) of Landau–Lifshitz written for
  the expansion; `IsSynchronous.raychaudhuri_le`: `∂_t θ ≤ −θ²/d − R_{00}`.
* `IsSynchronous.exists_notMem_of_ricci_nonneg`: **focusing**: if `R_{00} ≥ 0` on the domain and
  `θ < 0` at a point `z₀`, the time line from `z₀` leaves the domain at a proper time
  `s ≤ d/|θ(z₀)|` (Landau–Lifshitz, (97.15)): the synchronous co-ordinates cannot be continued
  along it beyond that time. `IsSynchronous.exists_notMem_of_ricci_nonneg_past`: the same
  towards the past for `θ(z₀) > 0`. `IsSynchronous.tendsto_expansion_atBot`: if the time line
  stays in the domain up to that time, `θ → −∞` there.

The scalar comparison is `RiccatiComparison.lt_div_abs`. The condition `R_{00} ≥ 0` is a
consequence of the Einstein equations with the strong energy condition and `Λ ≤ 0`; the
physical statement is in `GeneralRelativity/EnergyCondition.lean`.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology MatrixOrder

namespace ProjectAinos.SmoothGeometry

/-! ### The trace inequality -/

namespace Focusing

open Matrix

/-- `tr((PB)²) ≥ 0` for `P` positive semidefinite and `B` symmetric: with `P = AᵀA`,
`tr(PBPB) = tr(MᵀM)` for `M = ABAᵀ`. -/
theorem trace_mul_mul_nonneg {n : Type} [Fintype n] [DecidableEq n] {P B : Matrix n n ℝ}
    (hP : P.PosSemidef) (hB : B.IsSymm) : 0 ≤ (P * B * (P * B)).trace := by
  obtain ⟨A, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hP.nonneg
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hM : (Aᵀ * A * B * (Aᵀ * A * B)).trace = ((A * B * Aᵀ)ᵀ * (A * B * Aᵀ)).trace := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hB.eq]
    rw [show Aᵀ * A * B * (Aᵀ * A * B) = Aᵀ * (A * B * Aᵀ * A * B) by
      simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [hM]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _

/-- **The trace inequality** (Landau–Lifshitz, §97): for `γ` positive definite and `S`
symmetric, `κ = γ⁻¹S` satisfies `tr(κ²) ≥ (tr κ)²/d`. The difference is `tr((κ − c)²)` with
`c = tr κ/d` and `κ − c = γ⁻¹(S − cγ)`. -/
theorem trace_sq_ge {d : ℕ} {γ S : Matrix (Fin d) (Fin d) ℝ} (hγ : γ.PosDef) (hS : S.IsSymm) :
    (γ⁻¹ * S).trace ^ 2 / d ≤ (γ⁻¹ * S * (γ⁻¹ * S)).trace := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [Matrix.trace]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  set κ := γ⁻¹ * S with hκ
  set c := κ.trace / d with hc
  have hγs : γ.IsSymm := by
    have h := hγ.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hB : (S - c • γ).IsSymm := hS.sub (hγs.smul c)
  have hinv : γ⁻¹ * γ = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det γ).mp hγ.isUnit)
  have hshift : γ⁻¹ * (S - c • γ) = κ - c • 1 := by
    rw [Matrix.mul_sub, Matrix.mul_smul, hinv]
  have h := trace_mul_mul_nonneg hγ.inv.posSemidef hB
  rw [hshift] at h
  have hexp : ((κ - c • 1) * (κ - c • 1)).trace = (κ * κ).trace - 2 * c * κ.trace + c ^ 2 * d := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
      smul_eq_mul]
    ring
  rw [hexp] at h
  have hc2 : 2 * c * κ.trace - c ^ 2 * d = κ.trace ^ 2 / d := by
    rw [hc]
    field_simp
    ring
  linarith

end Focusing

namespace CoordinateMetric

open LorentzMetric

variable {d : ℕ} {U : Opens (MinkowskiModel d)}

/-! ### The expansion and the shear -/

/-- The matrix `γ_{αβ} = g_{α+1, β+1}` of the spatial metric. -/
def spatialCoefficient (g : CoordinateMetric .timeNegative d U) (z : MinkowskiModel d) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun α β => g.coefficient z α.succ β.succ

/-- **The expansion** `θ = ½ κ^α_α` of the time lines, the rate `∂_t log √|g|` of the volume of
the slices. -/
def expansion (g : CoordinateMetric .timeNegative d U) (z : MinkowskiModel d) : ℝ :=
  (∑ α, g.extrinsicRate z α α) / 2

/-- **The shear** `σ_{αβ}σ^{αβ} = ¼ κ^α_β κ^β_α − θ²/d` of the time lines, with the trace-free
part `σ^α_β = ½ κ^α_β − (θ/d) δ^α_β` of the rate. -/
def shearSq (g : CoordinateMetric .timeNegative d U) (z : MinkowskiModel d) : ℝ :=
  (∑ α, ∑ β, g.extrinsicRate z α β * g.extrinsicRate z β α) / 4 - g.expansion z ^ 2 / d

/-- **The lowered rate `∂_t γ_{αβ}` is symmetric**: the congruence of the time lines has no
vorticity. -/
theorem metricRate_symm (g : CoordinateMetric .timeNegative d U) {z : MinkowskiModel d}
    (hz : z ∈ U) (α β : Fin d) : g.metricRate z α β = g.metricRate z β α := by
  have h : (fun w => g.coefficient w α.succ β.succ) =ᶠ[𝓝 z]
      fun w => g.coefficient w β.succ α.succ :=
    eventually_of_mem (U.isOpen.mem_nhds hz) fun w hw => g.coefficient_symmetric hw _ _
  unfold metricRate
  rw [h.fderiv_eq]

namespace IsSynchronous

variable {g : CoordinateMetric .timeNegative d U} (hs : g.IsSynchronous) {z : MinkowskiModel d}
include hs

/-- **The spatial metric is positive definite**: the signature `(−+++)` and `g_{00} = −1`. -/
theorem spatialCoefficient_posDef (hz : z ∈ U) : (g.spatialCoefficient z).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun ξ hξ => ?_
  · ext α β
    simp [spatialCoefficient, Matrix.conjTranspose_apply, g.coefficient_symmetric hz]
  · have h00 : g.form z (Pi.single 0 1) (Pi.single 0 1) < 0 := by
      have h := (hs z hz).1
      change g.form z (Pi.single 0 1) (Pi.single 0 1) = -1 at h
      rw [h]
      norm_num
    have h := g.spatialMetric_pos hz h00 hξ
    have h0 (α : Fin d) : g.form z (Pi.single 0 1) (Pi.single α.succ 1) = 0 := (hs z hz).2 α
    convert h using 1
    simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum, spatialCoefficient,
      Matrix.of_apply, Minkowski.spatialMetric, h0, zero_mul, zero_div, sub_zero]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    rw [coefficient, Matrix.of_apply]
    ring

/-- **The spatial block of the inverse is the inverse of the spatial metric**:
`γ^{αβ} = g^{α+1, β+1}`. -/
theorem inv_spatialCoefficient (hz : z ∈ U) :
    (g.spatialCoefficient z)⁻¹ = Matrix.of fun α β => (g.coefficient z)⁻¹ α.succ β.succ := by
  refine Matrix.inv_eq_left_inv ?_
  have h : (g.coefficient z)⁻¹ * g.coefficient z = 1 :=
    mul_eq_one_comm.mp (g.coefficient_mul_inv ⟨z, hz⟩)
  ext α β
  have h1 := congrFun (congrFun h α.succ) β.succ
  rw [Matrix.mul_apply, Fin.sum_univ_succ, hs.inv_zero_right hz] at h1
  simp only [Fin.succ_ne_zero, ite_false, zero_mul, zero_add, Matrix.one_apply,
    Fin.succ_inj] at h1
  simp only [Matrix.mul_apply, Matrix.of_apply, spatialCoefficient, Matrix.one_apply, h1]

/-- **The rate is `κ = γ⁻¹ ∂_tγ`**: `κ^α_β = γ^{αδ} ∂_t γ_{δβ}`. -/
theorem extrinsicRate_eq_mul (hz : z ∈ U) (α β : Fin d) :
    g.extrinsicRate z α β = ((g.spatialCoefficient z)⁻¹ * Matrix.of (g.metricRate z)) α β := by
  rw [hs.inv_spatialCoefficient hz, Matrix.mul_apply, extrinsicRate]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [Matrix.of_apply, Matrix.of_apply, g.metricRate_symm hz δ β]
  rfl

/-- **The trace inequality for the rate**: `(κ^α_α)²/d ≤ κ^α_β κ^β_α`. -/
theorem sq_sum_extrinsicRate_le (hz : z ∈ U) :
    (∑ α, g.extrinsicRate z α α) ^ 2 / d ≤
      ∑ α, ∑ β, g.extrinsicRate z α β * g.extrinsicRate z β α := by
  have hS : (Matrix.of (g.metricRate z)).IsSymm :=
    Matrix.IsSymm.ext fun α β => by simp only [Matrix.of_apply, g.metricRate_symm hz]
  have h := Focusing.trace_sq_ge (hs.spatialCoefficient_posDef hz) hS
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply] at h
  simp only [hs.extrinsicRate_eq_mul hz, Matrix.mul_apply]
  exact h

/-- **The expansion is the rate of the volume**: `θ = ∂_t log √|g|`, the derivative of the
logarithm of the volume density along the time lines. -/
theorem expansion_eq_fderiv_log (hz : z ∈ U) :
    g.expansion z =
      fderiv ℝ (fun w => Real.log (densityOf g.coefficient w)) z (Pi.single 0 1) := by
  rw [g.fderiv_log_densityOf hz, Fin.sum_univ_succ, hs.christoffel_zero_zero hz, zero_add,
    expansion, Finset.sum_div]
  exact Finset.sum_congr rfl fun α _ => (hs.christoffel_succ_succ_zero hz α α).symm

/-- **The shear is nonnegative**: `σ_{αβ}σ^{αβ} ≥ 0`. -/
theorem shearSq_nonneg (hz : z ∈ U) : 0 ≤ g.shearSq z := by
  have h := hs.sq_sum_extrinsicRate_le hz
  rw [shearSq, expansion]
  have : (∑ α, g.extrinsicRate z α α) ^ 2 / d / 4 = ((∑ α, g.extrinsicRate z α α) / 2) ^ 2 / d := by
    ring
  linarith

/-- The components of the rate are differentiable: `κ^α_β = 2 Γ^α_{0β}` near `z`. -/
theorem differentiableAt_extrinsicRate (hz : z ∈ U) (α β : Fin d) :
    DifferentiableAt ℝ (fun w => g.extrinsicRate w α β) z := by
  have hU := U.isOpen.mem_nhds hz
  have hΓ := ((g.contDiffOn_christoffelOf α.succ 0 β.succ).contDiffAt hU).differentiableAt
    (by simp)
  have hsucc : (fun w => christoffelOf g.coefficient w α.succ 0 β.succ) =ᶠ[𝓝 z]
      fun w => (1 / 2 : ℝ) * g.extrinsicRate w α β :=
    eventually_of_mem hU fun w hw => by
      simp only
      rw [hs.christoffel_succ_zero_succ hw]
      ring
  have h2 := (hΓ.congr_of_eventuallyEq hsucc.symm).const_mul 2
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards with w
  ring

/-- The expansion is differentiable. -/
theorem differentiableAt_expansion (hz : z ∈ U) : DifferentiableAt ℝ g.expansion z := by
  have h : g.expansion = fun w => (1 / 2 : ℝ) * ∑ α, g.extrinsicRate w α α := by
    funext w
    rw [expansion]
    ring
  rw [h]
  exact (DifferentiableAt.fun_sum fun α _ => hs.differentiableAt_extrinsicRate hz α α).const_mul _

/-- **The equation of Raychaudhuri for the time lines** (Landau–Lifshitz, (97.11)):
`∂_t θ = −θ²/d − σ_{αβ}σ^{αβ} − R_{00}`. -/
theorem raychaudhuri (hz : z ∈ U) :
    fderiv ℝ g.expansion z (Pi.single 0 1) =
      -g.expansion z ^ 2 / d - g.shearSq z - ricciOf g.coefficient z 0 0 := by
  have hκ (α : Fin d) := hs.differentiableAt_extrinsicRate hz α α
  have h : g.expansion = fun w => (1 / 2 : ℝ) * ∑ α, g.extrinsicRate w α α := by
    funext w
    rw [expansion]
    ring
  have hD : fderiv ℝ g.expansion z (Pi.single 0 1) =
      (∑ α, fderiv ℝ (fun w => g.extrinsicRate w α α) z (Pi.single 0 1)) / 2 := by
    rw [h, fderiv_const_mul (DifferentiableAt.fun_sum fun α _ => hκ α),
      fderiv_fun_sum fun α _ => hκ α]
    simp only [smul_apply, FunLike.coe_sum, Finset.sum_apply, smul_eq_mul]
    ring
  rw [hD, hs.ricci_zero_zero hz, shearSq]
  ring

/-- **The focusing inequality**: `∂_t θ ≤ −θ²/d − R_{00}`, since the shear is nonnegative. -/
theorem raychaudhuri_le (hz : z ∈ U) :
    fderiv ℝ g.expansion z (Pi.single 0 1) ≤
      -g.expansion z ^ 2 / d - ricciOf g.coefficient z 0 0 := by
  rw [hs.raychaudhuri hz]
  linarith [hs.shearSq_nonneg hz]

omit hs in
/-- The expansion along a line `s ↦ z₀ + s v` of the domain has the derivative `∂_v θ`. -/
theorem hasDerivAt_expansion_line (hs : g.IsSynchronous) {z₀ v : MinkowskiModel d} {s : ℝ}
    (hz : z₀ + s • v ∈ U) :
    HasDerivAt (fun s : ℝ => g.expansion (z₀ + s • v)) (fderiv ℝ g.expansion (z₀ + s • v) v) s := by
  have hline : HasDerivAt (fun s : ℝ => z₀ + s • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add z₀
  exact (hs.differentiableAt_expansion hz).hasFDerivAt.comp_hasDerivAt s hline

omit hs in
/-- A negative or positive expansion needs a space dimension. -/
theorem dimension_pos_of_expansion_ne_zero {z₀ : MinkowskiModel d} (hθ : g.expansion z₀ ≠ 0) :
    (0 : ℝ) < d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h
    simp [expansion] at hθ
  · exact_mod_cast h

/-- **Focusing of the time lines** (Landau–Lifshitz, (97.15)): if `R_{00} ≥ 0` on the domain and
the expansion is negative at `z₀`, the time line `s ↦ z₀ + s e₀` leaves the domain at a proper
time `s ≤ d/|θ(z₀)|`. -/
theorem exists_notMem_of_ricci_nonneg (hR : ∀ z ∈ U, 0 ≤ ricciOf g.coefficient z 0 0)
    {z₀ : MinkowskiModel d} (hz₀ : z₀ ∈ U) (hθ : g.expansion z₀ < 0) :
    ∃ s ∈ Ioc 0 (d / |g.expansion z₀|), z₀ + s • (Pi.single 0 1 : MinkowskiModel d) ∉ U := by
  have hd := dimension_pos_of_expansion_ne_zero (g := g) hθ.ne
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  set T := (d : ℝ) / |g.expansion z₀| with hT
  have hmem : ∀ s ∈ Icc (0 : ℝ) (0 + T), z₀ + s • (Pi.single 0 1 : MinkowskiModel d) ∈ U := by
    intro s hs'
    rcases eq_or_lt_of_le hs'.1 with h | h
    · subst h
      simpa using hz₀
    · exact hcon s ⟨h, by simpa using hs'.2⟩
  have hderiv (s : ℝ) (hs' : s ∈ Icc (0 : ℝ) (0 + T)) :=
    hasDerivAt_expansion_line hs (v := Pi.single 0 1) (hmem s hs')
  have hlt := RiccatiComparison.lt_div_abs (θ := fun s : ℝ =>
      g.expansion (z₀ + s • (Pi.single 0 1 : MinkowskiModel d))) (t₀ := 0) (T := T) hd
    (fun s hs' => (hderiv s hs').continuousAt.continuousWithinAt)
    (fun s hs' => hderiv s (Ioo_subset_Icc_self hs'))
    (fun s hs' => by
      have hz := hmem s (Ioo_subset_Icc_self hs')
      have h1 := hs.raychaudhuri_le hz
      have h2 := hR _ hz
      linarith)
    (by simpa using hθ)
  simp only [zero_smul, add_zero] at hlt
  exact lt_irrefl _ hlt

/-- **Focusing towards the past**: if `R_{00} ≥ 0` on the domain and the expansion is positive at
`z₀`, the time line `s ↦ z₀ − s e₀` leaves the domain at a proper time `s ≤ d/|θ(z₀)|`. -/
theorem exists_notMem_of_ricci_nonneg_past (hR : ∀ z ∈ U, 0 ≤ ricciOf g.coefficient z 0 0)
    {z₀ : MinkowskiModel d} (hz₀ : z₀ ∈ U) (hθ : 0 < g.expansion z₀) :
    ∃ s ∈ Ioc 0 (d / |g.expansion z₀|), z₀ - s • (Pi.single 0 1 : MinkowskiModel d) ∉ U := by
  have hd := dimension_pos_of_expansion_ne_zero (g := g) hθ.ne'
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  set e : MinkowskiModel d := -Pi.single 0 1 with he
  have hsub (s : ℝ) : z₀ - s • (Pi.single 0 1 : MinkowskiModel d) = z₀ + s • e := by
    rw [he, smul_neg, sub_eq_add_neg]
  set T := (d : ℝ) / |g.expansion z₀| with hT
  have hmem : ∀ s ∈ Icc (0 : ℝ) (0 + T), z₀ + s • e ∈ U := by
    intro s hs'
    rw [← hsub]
    rcases eq_or_lt_of_le hs'.1 with h | h
    · subst h
      simpa using hz₀
    · exact hcon s ⟨h, by simpa using hs'.2⟩
  have hderiv (s : ℝ) (hs' : s ∈ Icc (0 : ℝ) (0 + T)) :
      HasDerivAt (fun s : ℝ => -g.expansion (z₀ + s • e))
        (fderiv ℝ g.expansion (z₀ + s • e) (Pi.single 0 1)) s := by
    have h := (hasDerivAt_expansion_line hs (v := e) (hmem s hs')).neg
    rw [he, map_neg, neg_neg] at h
    exact h
  have hlt := RiccatiComparison.lt_div_abs (θ := fun s : ℝ => -g.expansion (z₀ + s • e))
    (t₀ := 0) (T := T) hd
    (fun s hs' => (hderiv s hs').continuousAt.continuousWithinAt)
    (fun s hs' => hderiv s (Ioo_subset_Icc_self hs'))
    (fun s hs' => by
      have hz := hmem s (Ioo_subset_Icc_self hs')
      have h1 := hs.raychaudhuri_le hz
      have h2 := hR _ hz
      simp only [neg_sq]
      linarith)
    (by simpa using hθ)
  simp only [zero_smul, add_zero, abs_neg] at hlt
  exact lt_irrefl _ hlt

/-- **The expansion diverges** (Landau–Lifshitz, §97): if `R_{00} ≥ 0` on the domain, the
expansion is negative at `z₀` and the time line from `z₀` stays in the domain for the proper
times `s ∈ [0, d/|θ(z₀)|)`, then `θ(z₀ + s e₀) → −∞` as `s → d/|θ(z₀)|`: the logarithmic rate
of the volume density diverges there. -/
theorem tendsto_expansion_atBot (hR : ∀ z ∈ U, 0 ≤ ricciOf g.coefficient z 0 0)
    {z₀ : MinkowskiModel d} (hθ : g.expansion z₀ < 0)
    (hline : ∀ s ∈ Ico 0 (d / |g.expansion z₀|),
      z₀ + s • (Pi.single 0 1 : MinkowskiModel d) ∈ U) :
    Tendsto (fun s : ℝ => g.expansion (z₀ + s • (Pi.single 0 1 : MinkowskiModel d)))
      (𝓝[<] (d / |g.expansion z₀|)) atBot := by
  have hd := dimension_pos_of_expansion_ne_zero (g := g) hθ.ne
  set f := fun s : ℝ => g.expansion (z₀ + s • (Pi.single 0 1 : MinkowskiModel d)) with hf
  have hf0 : f 0 = g.expansion z₀ := by simp [hf]
  have hline' : ∀ s ∈ Ico (0 : ℝ) (0 + d / |f 0|),
      z₀ + s • (Pi.single 0 1 : MinkowskiModel d) ∈ U := by
    rw [hf0, zero_add]
    exact hline
  have hderiv (s : ℝ) (hs' : s ∈ Ico (0 : ℝ) (0 + d / |f 0|)) :=
    hasDerivAt_expansion_line hs (v := Pi.single 0 1) (hline' s hs')
  have h := RiccatiComparison.tendsto_atBot (θ := f) (t₀ := 0) hd (by rw [hf0]; exact hθ)
    (fun s hs' => (hderiv s hs').continuousAt.continuousWithinAt)
    (fun s hs' => hderiv s (Ioo_subset_Ico_self hs'))
    (fun s hs' => by
      have hz := hline' s (Ioo_subset_Ico_self hs')
      have h1 := hs.raychaudhuri_le hz
      have h2 := hR _ hz
      simp only [hf]
      linarith)
  rwa [hf0, zero_add] at h

end IsSynchronous

end CoordinateMetric

end ProjectAinos.SmoothGeometry
