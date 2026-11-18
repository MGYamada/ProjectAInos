/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateFirstVariation
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateScalarField
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateTangent
public import ProjectAinos.SmoothGeometry.Lorentzian.Geodesic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The synchronous reference system

Landau–Lifshitz, §97. A coordinate metric in the convention `(−+++)` is synchronous when
`g_{00} = −1` and `g_{0α} = 0`, that is `ds² = −dt² + γ_{αβ} dx^α dx^β`
(`CoordinateMetric.IsSynchronous`). With `κ^α_β = γ^{αδ} ∂_t γ_{βδ}` (`extrinsicRate`):

* `IsSynchronous.inv_zero`: the inverse has the same time row, `g^{0l} = −δ_{0l}`;
* `IsSynchronous.christoffel_zero_zero`, `christoffel_zero_zero_succ`,
  `christoffel_succ_zero_succ`: `Γ^k_{00} = 0`, `Γ^0_{0β} = 0` and `Γ^α_{0β} = ½ κ^α_β`;
* `IsSynchronous.ricci_zero_zero`, `ricci_zero_succ`, `ricci_succ_succ`: **the Ricci tensor in
  the synchronous system**, `R_{00} = −½ ∂_t κ^α_α − ¼ κ^α_β κ^β_α`,
  `R_{0α} = ½ (κ^β_{α;β} − κ^β_{β;α})` and
  `R_{αβ} = P_{αβ} + ½ ∂_t κ_{αβ} + ¼ (κ^γ_γ κ_{αβ} − κ_{αγ} κ^γ_β − κ^γ_α κ_{γβ})`, the equations
  (97.11)–(97.13) of Landau–Lifshitz with `κ_{αβ} = ∂_t γ_{αβ}` (`metricRate`), the covariant
  derivative and the Ricci tensor `P_{αβ}` (`sliceRicci`) of the slices; they are read natively
  by `toLorentzMetric_ricci_chartField`;
* `IsSynchronous.isGeodesicOn_timeLine`: the time lines `x^α = const` are geodesics, their
  parameter is the proper time and they are orthogonal to the slices `t = const`.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

open LorentzMetric

variable {d : ℕ} {U : Opens (MinkowskiModel d)}

/-- A synchronous coordinate metric: `g_{00} = −1` and `g_{0α} = 0` on `U`. -/
def IsSynchronous (g : CoordinateMetric .timeNegative d U) : Prop :=
  ∀ z ∈ U, g.coefficient z 0 0 = -1 ∧ ∀ α : Fin d, g.coefficient z 0 α.succ = 0

/-- The rate `κ^α_β = γ^{αδ} ∂_t γ_{βδ}` of the spatial metric of a synchronous metric. -/
def extrinsicRate (g : CoordinateMetric .timeNegative d U) (z : MinkowskiModel d)
    (α β : Fin d) : ℝ :=
  ∑ δ : Fin d, (g.coefficient z)⁻¹ α.succ δ.succ *
    fderiv ℝ (fun w => g.coefficient w β.succ δ.succ) z (Pi.single 0 1)

/-- The rate `∂_t γ_{αβ}` of the spatial metric. -/
def metricRate (g : CoordinateMetric .timeNegative d U) (z : MinkowskiModel d) (α β : Fin d) : ℝ :=
  fderiv ℝ (fun w => g.coefficient w α.succ β.succ) z (Pi.single 0 1)

/-- The Ricci tensor `P_{αβ}` of the slices `t = const`, from the spatial Christoffel symbols
`Γ^γ_{αβ}` and the spatial derivatives. -/
def sliceRicci (g : CoordinateMetric .timeNegative d U) (z : MinkowskiModel d) (α β : Fin d) :
    ℝ :=
  ∑ γ : Fin d, (fderiv ℝ (fun w => christoffelOf g.coefficient w γ.succ α.succ β.succ) z
      (Pi.single γ.succ 1) -
    fderiv ℝ (fun w => christoffelOf g.coefficient w γ.succ γ.succ β.succ) z
      (Pi.single α.succ 1) +
    ∑ δ : Fin d, (christoffelOf g.coefficient z γ.succ γ.succ δ.succ *
        christoffelOf g.coefficient z δ.succ α.succ β.succ -
      christoffelOf g.coefficient z γ.succ α.succ δ.succ *
        christoffelOf g.coefficient z δ.succ γ.succ β.succ))

/-- The contracted Christoffel symbols are the derivatives of `log √|g|`. -/
theorem fderiv_log_densityOf (g : CoordinateMetric .timeNegative d U) {z : MinkowskiModel d}
    (hz : z ∈ U) (k : Fin (d + 1)) :
    fderiv ℝ (fun w => Real.log (densityOf g.coefficient w)) z (Pi.single k 1) =
      ∑ c, christoffelOf g.coefficient z c c k := by
  have hD := ((g.contDiffOn_densityOf).contDiffAt (U.isOpen.mem_nhds hz)).differentiableAt
    (by simp)
  have hpos := g.densityOf_pos hz
  rw [(hD.hasFDerivAt.log hpos.ne').fderiv, smul_apply, smul_eq_mul, g.fderiv_densityOf hz]
  field_simp

namespace IsSynchronous

variable {g : CoordinateMetric .timeNegative d U} (hs : g.IsSynchronous) {z : MinkowskiModel d}
include hs

/-- The time row of the coefficients: `g_{0l} = −δ_{0l}`. -/
theorem coefficient_zero (hz : z ∈ U) (l : Fin (d + 1)) :
    g.coefficient z 0 l = if l = 0 then -1 else 0 := by
  rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨α, rfl⟩
  · simp [(hs z hz).1]
  · simp [(hs z hz).2 α, Fin.succ_ne_zero]

/-- The time column of the coefficients: `g_{l0} = −δ_{l0}`. -/
theorem coefficient_zero_right (hz : z ∈ U) (l : Fin (d + 1)) :
    g.coefficient z l 0 = if l = 0 then -1 else 0 := by
  rw [g.coefficient_symmetric hz, hs.coefficient_zero hz]

/-- The inverse has the same time row: `g^{0l} = −δ_{0l}`. -/
theorem inv_zero (hz : z ∈ U) (j : Fin (d + 1)) :
    (g.coefficient z)⁻¹ 0 j = if j = 0 then -1 else 0 := by
  have h := congrFun (congrFun (g.coefficient_mul_inv ⟨z, hz⟩) 0) j
  rw [Matrix.mul_apply] at h
  simp only [hs.coefficient_zero hz, ite_mul, neg_one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Matrix.one_apply] at h
  by_cases hj : j = 0
  · subst hj
    simp only [ite_true] at h ⊢
    linarith
  · simp only [hj, ite_false, Ne.symm hj] at h ⊢
    linarith

/-- The inverse has the same time column: `g^{l0} = −δ_{l0}`. -/
theorem inv_zero_right (hz : z ∈ U) (j : Fin (d + 1)) :
    (g.coefficient z)⁻¹ j 0 = if j = 0 then -1 else 0 := by
  rw [g.coefficient_inv_symmetric hz, hs.inv_zero hz]

/-- The derivatives of the time row vanish. -/
theorem fderiv_coefficient_zero (hz : z ∈ U) (l : Fin (d + 1)) (v : MinkowskiModel d) :
    fderiv ℝ (fun w => g.coefficient w 0 l) z v = 0 := by
  have h : (fun w => g.coefficient w 0 l) =ᶠ[𝓝 z] fun _ => if l = 0 then -1 else 0 :=
    eventually_of_mem (U.isOpen.mem_nhds hz) fun w hw => hs.coefficient_zero hw l
  rw [h.fderiv_eq, fderiv_const_apply, zero_apply]

/-- The derivatives of the time column vanish. -/
theorem fderiv_coefficient_zero_right (hz : z ∈ U) (l : Fin (d + 1)) (v : MinkowskiModel d) :
    fderiv ℝ (fun w => g.coefficient w l 0) z v = 0 := by
  have h : (fun w => g.coefficient w l 0) =ᶠ[𝓝 z] fun _ => if l = 0 then -1 else 0 :=
    eventually_of_mem (U.isOpen.mem_nhds hz) fun w hw => hs.coefficient_zero_right hw l
  rw [h.fderiv_eq, fderiv_const_apply, zero_apply]

/-- `Γ^k_{00} = 0`. -/
theorem christoffel_zero_zero (hz : z ∈ U) (k : Fin (d + 1)) :
    christoffelOf g.coefficient z k 0 0 = 0 := by
  unfold christoffelOf
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [hs.fderiv_coefficient_zero hz, hs.fderiv_coefficient_zero_right hz,
    hs.fderiv_coefficient_zero hz]
  ring

/-- `Γ^0_{0j} = 0`. -/
theorem christoffel_zero_zero_succ (hz : z ∈ U) (j : Fin (d + 1)) :
    christoffelOf g.coefficient z 0 0 j = 0 := by
  unfold christoffelOf
  rw [Fin.sum_univ_succ, hs.inv_zero hz, hs.fderiv_coefficient_zero_right hz,
    hs.fderiv_coefficient_zero hz, hs.fderiv_coefficient_zero hz]
  simp only [ite_true, sub_self, add_zero, mul_zero, zero_div, zero_add]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [hs.inv_zero hz]
  simp [Fin.succ_ne_zero]

/-- `Γ^0_{j0} = 0`. -/
theorem christoffel_zero_succ_zero (hz : z ∈ U) (j : Fin (d + 1)) :
    christoffelOf g.coefficient z 0 j 0 = 0 := by
  rw [christoffelOf_coefficient_symm hz, hs.christoffel_zero_zero_succ hz]

/-- `Γ^α_{0β} = ½ κ^α_β`. -/
theorem christoffel_succ_zero_succ (hz : z ∈ U) (α β : Fin d) :
    christoffelOf g.coefficient z α.succ 0 β.succ = g.extrinsicRate z α β / 2 := by
  unfold christoffelOf extrinsicRate
  rw [Fin.sum_univ_succ, hs.inv_zero_right hz]
  simp only [Fin.succ_ne_zero, ite_false, zero_mul, zero_div, zero_add]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [hs.fderiv_coefficient_zero_right hz, hs.fderiv_coefficient_zero hz]
  ring

/-- `Γ^α_{β0} = ½ κ^α_β`. -/
theorem christoffel_succ_succ_zero (hz : z ∈ U) (α β : Fin d) :
    christoffelOf g.coefficient z α.succ β.succ 0 = g.extrinsicRate z α β / 2 := by
  rw [christoffelOf_coefficient_symm hz, hs.christoffel_succ_zero_succ hz]

/-- **The time component of the Ricci tensor**: `R_{00} = −½ ∂_t κ^α_α − ¼ κ^α_β κ^β_α`. -/
theorem ricci_zero_zero (hz : z ∈ U) :
    ricciOf g.coefficient z 0 0 =
      -(∑ α, fderiv ℝ (fun w => g.extrinsicRate w α α) z (Pi.single 0 1)) / 2 -
        (∑ α, ∑ β, g.extrinsicRate z α β * g.extrinsicRate z β α) / 4 := by
  have hev (k : Fin (d + 1)) :
      (fun w => christoffelOf g.coefficient w k 0 0) =ᶠ[𝓝 z] fun _ => 0 :=
    eventually_of_mem (U.isOpen.mem_nhds hz) fun w hw => hs.christoffel_zero_zero hw k
  have hdiag (α : Fin d) : (fun w => christoffelOf g.coefficient w α.succ α.succ 0) =ᶠ[𝓝 z]
      fun w => (1 / 2 : ℝ) * g.extrinsicRate w α α :=
    eventually_of_mem (U.isOpen.mem_nhds hz) fun w hw => by
      simp only
      rw [hs.christoffel_succ_succ_zero hw α α]
      ring
  have hκ (α : Fin d) : DifferentiableAt ℝ (fun w => g.extrinsicRate w α α) z := by
    have h := ((g.contDiffOn_christoffelOf α.succ α.succ 0).contDiffAt
      (U.isOpen.mem_nhds hz)).differentiableAt (by simp)
    have h2 := (h.congr_of_eventuallyEq (hdiag α).symm).const_mul 2
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards with w
    ring
  have hB (α : Fin d) :
      fderiv ℝ (fun w => christoffelOf g.coefficient w α.succ α.succ 0) z (Pi.single 0 1) =
        fderiv ℝ (fun w => g.extrinsicRate w α α) z (Pi.single 0 1) / 2 := by
    rw [(hdiag α).fderiv_eq, fderiv_const_mul (hκ α), smul_apply, smul_eq_mul]
    ring
  have hterm (i : Fin (d + 1)) :
      fderiv ℝ (fun w => christoffelOf g.coefficient w i 0 0) z (Pi.single i 1) -
          fderiv ℝ (fun w => christoffelOf g.coefficient w i i 0) z (Pi.single 0 1) +
          ∑ a, (christoffelOf g.coefficient z i i a * christoffelOf g.coefficient z a 0 0 -
            christoffelOf g.coefficient z i 0 a * christoffelOf g.coefficient z a i 0) =
        -fderiv ℝ (fun w => christoffelOf g.coefficient w i i 0) z (Pi.single 0 1) -
          ∑ a, christoffelOf g.coefficient z i 0 a * christoffelOf g.coefficient z a i 0 := by
    rw [(hev i).fderiv_eq, fderiv_const_apply, zero_apply]
    simp only [hs.christoffel_zero_zero hz, mul_zero, zero_sub, Finset.sum_neg_distrib]
    ring
  unfold ricciOf
  rw [Finset.sum_congr rfl fun i _ => hterm i, Fin.sum_univ_succ,
    (hev 0).fderiv_eq, fderiv_const_apply, zero_apply]
  simp only [hs.christoffel_zero_zero hz, mul_zero, Finset.sum_const_zero, neg_zero,
    sub_zero, zero_add, Fin.sum_univ_succ (n := d), hB, hs.christoffel_succ_zero_succ hz,
    hs.christoffel_succ_succ_zero hz, zero_mul]
  rw [neg_div, Finset.sum_div, Finset.sum_div, ← Finset.sum_neg_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_div]
  have hsum : ∑ β, g.extrinsicRate z α β / 2 * (g.extrinsicRate z β α / 2) =
      ∑ β, g.extrinsicRate z α β * g.extrinsicRate z β α / 4 :=
    Finset.sum_congr rfl fun β _ => by ring
  rw [hsum]

/-- `Γ^0_{αβ} = ½ ∂_t γ_{αβ}`. -/
theorem christoffel_zero_succ_succ (hz : z ∈ U) (α β : Fin d) :
    christoffelOf g.coefficient z 0 α.succ β.succ = g.metricRate z α β / 2 := by
  unfold christoffelOf metricRate
  rw [Fin.sum_univ_succ]
  simp only [hs.inv_zero hz, hs.fderiv_coefficient_zero_right hz, hs.fderiv_coefficient_zero hz,
    Fin.succ_ne_zero, ite_true, ite_false, zero_mul, zero_div, Finset.sum_const_zero, add_zero]
  ring

/-- **The mixed component of the Ricci tensor** (the momentum constraint):
`R_{0α} = ½ (κ^β_{α;β} − κ^β_{β;α})` with the covariant derivative of the slices,
`κ^β_{α;β} = ∂_β κ^β_α + Γ^β_{βγ} κ^γ_α − Γ^γ_{βα} κ^β_γ`. -/
theorem ricci_zero_succ (hz : z ∈ U) (α : Fin d) :
    ricciOf g.coefficient z 0 α.succ =
      (∑ β, (fderiv ℝ (fun w => g.extrinsicRate w β α) z (Pi.single β.succ 1) +
          ∑ γ : Fin d, (christoffelOf g.coefficient z β.succ β.succ γ.succ *
              g.extrinsicRate z γ α -
            christoffelOf g.coefficient z γ.succ β.succ α.succ * g.extrinsicRate z β γ)) -
        ∑ β, fderiv ℝ (fun w => g.extrinsicRate w β β) z (Pi.single α.succ 1)) / 2 := by
  have hU := U.isOpen.mem_nhds hz
  have hΓ (k i j : Fin (d + 1)) :
      DifferentiableAt ℝ (fun w => christoffelOf g.coefficient w k i j) z :=
    ((g.contDiffOn_christoffelOf k i j).contDiffAt hU).differentiableAt (by simp)
  have hsucc (β γ : Fin d) : (fun w => christoffelOf g.coefficient w β.succ 0 γ.succ) =ᶠ[𝓝 z]
      fun w => (1 / 2 : ℝ) * g.extrinsicRate w β γ :=
    eventually_of_mem hU fun w hw => by
      simp only
      rw [hs.christoffel_succ_zero_succ hw]
      ring
  have hκ (β γ : Fin d) : DifferentiableAt ℝ (fun w => g.extrinsicRate w β γ) z := by
    have h2 := ((hΓ β.succ 0 γ.succ).congr_of_eventuallyEq (hsucc β γ).symm).const_mul 2
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards with w
    ring
  have hL : ContDiffOn ℝ ∞ (fun w => Real.log (densityOf g.coefficient w)) U :=
    ContDiffOn.log g.contDiffOn_densityOf fun w hw => (g.densityOf_pos hw).ne'
  have htrace : (fun w => fderiv ℝ (fun v => Real.log (densityOf g.coefficient v)) w
      (Pi.single 0 1)) =ᶠ[𝓝 z] fun w => (1 / 2 : ℝ) * ∑ β, g.extrinsicRate w β β :=
    eventually_of_mem hU fun w hw => by
      simp only
      rw [g.fderiv_log_densityOf hw, Fin.sum_univ_succ, hs.christoffel_zero_zero hw,
        zero_add, Finset.mul_sum]
      exact Finset.sum_congr rfl fun β _ => by rw [hs.christoffel_succ_succ_zero hw]; ring
  have hcontr : (fun w => ∑ c, christoffelOf g.coefficient w c c α.succ) =ᶠ[𝓝 z]
      fun w => fderiv ℝ (fun v => Real.log (densityOf g.coefficient v)) w
        (Pi.single α.succ 1) :=
    eventually_of_mem hU fun w hw => (g.fderiv_log_densityOf hw α.succ).symm
  have hzero : (fun w => christoffelOf g.coefficient w 0 0 α.succ) =ᶠ[𝓝 z] fun _ => 0 :=
    eventually_of_mem hU fun w hw => hs.christoffel_zero_zero_succ hw α.succ
  have hS1 : ∑ i, fderiv ℝ (fun w => christoffelOf g.coefficient w i 0 α.succ) z
      (Pi.single i 1) =
      (∑ β, fderiv ℝ (fun w => g.extrinsicRate w β α) z (Pi.single β.succ 1)) / 2 := by
    rw [Fin.sum_univ_succ, hzero.fderiv_eq, fderiv_const_apply, zero_apply, zero_add,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [(hsucc β α).fderiv_eq, fderiv_const_mul (hκ β α), smul_apply, smul_eq_mul]
    ring
  have hS2 : ∑ c, fderiv ℝ (fun w => christoffelOf g.coefficient w c c α.succ) z
      (Pi.single 0 1) =
      (∑ β, fderiv ℝ (fun w => g.extrinsicRate w β β) z (Pi.single α.succ 1)) / 2 := by
    rw [← _root_.sum_apply, ← fderiv_fun_sum fun c _ => hΓ c c α.succ, hcontr.fderiv_eq,
      fderiv_fderiv_comm hL hz 0 α.succ, htrace.fderiv_eq,
      fderiv_const_mul (DifferentiableAt.fun_sum fun β _ => hκ β β), smul_apply, smul_eq_mul,
      fderiv_fun_sum fun β _ => hκ β β, _root_.sum_apply]
    ring
  have hS3 : ∑ i, ∑ a, christoffelOf g.coefficient z i i a *
      christoffelOf g.coefficient z a 0 α.succ =
      (∑ β : Fin d, ∑ γ : Fin d, christoffelOf g.coefficient z β.succ β.succ γ.succ *
        g.extrinsicRate z γ α) / 2 := by
    simp only [Fin.sum_univ_succ (n := d), hs.christoffel_zero_zero_succ hz,
      hs.christoffel_succ_zero_succ hz, mul_zero, zero_mul, zero_add, Finset.sum_const_zero,
      Finset.sum_div]
    exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun γ _ => by ring
  have hS4 : ∑ i, ∑ a, christoffelOf g.coefficient z i 0 a *
      christoffelOf g.coefficient z a i α.succ =
      (∑ β : Fin d, ∑ γ : Fin d, christoffelOf g.coefficient z γ.succ β.succ α.succ *
        g.extrinsicRate z β γ) / 2 := by
    simp only [Fin.sum_univ_succ (n := d), hs.christoffel_zero_zero_succ hz,
      hs.christoffel_zero_zero hz, hs.christoffel_succ_zero_succ hz, zero_mul,
      zero_add, Finset.sum_const_zero, Finset.sum_div]
    exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun γ _ => by ring
  have hR : ricciOf g.coefficient z 0 α.succ =
      ∑ i, fderiv ℝ (fun w => christoffelOf g.coefficient w i 0 α.succ) z (Pi.single i 1) -
        ∑ c, fderiv ℝ (fun w => christoffelOf g.coefficient w c c α.succ) z (Pi.single 0 1) +
        ∑ i, ∑ a, christoffelOf g.coefficient z i i a *
          christoffelOf g.coefficient z a 0 α.succ -
        ∑ i, ∑ a, christoffelOf g.coefficient z i 0 a *
          christoffelOf g.coefficient z a i α.succ := by
    unfold ricciOf
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [hR, hS1, hS2, hS3, hS4]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- **The spatial components of the Ricci tensor**:
`R_{αβ} = P_{αβ} + ½ ∂_t² γ_{αβ} + ¼ (κ^γ_γ ∂_tγ_{αβ} − ∂_tγ_{αγ} κ^γ_β − κ^γ_α ∂_tγ_{γβ})`,
the equation (97.13) of Landau–Lifshitz with `κ_{αβ} = ∂_t γ_{αβ}`. -/
theorem ricci_succ_succ (hz : z ∈ U) (α β : Fin d) :
    ricciOf g.coefficient z α.succ β.succ =
      g.sliceRicci z α β + fderiv ℝ (fun w => g.metricRate w α β) z (Pi.single 0 1) / 2 +
        (∑ γ, (g.extrinsicRate z γ γ * g.metricRate z α β -
          g.metricRate z α γ * g.extrinsicRate z γ β -
          g.extrinsicRate z γ α * g.metricRate z γ β)) / 4 := by
  have hU := U.isOpen.mem_nhds hz
  have hΓ (k i j : Fin (d + 1)) :
      DifferentiableAt ℝ (fun w => christoffelOf g.coefficient w k i j) z :=
    ((g.contDiffOn_christoffelOf k i j).contDiffAt hU).differentiableAt (by simp)
  have h0 : (fun w => christoffelOf g.coefficient w 0 α.succ β.succ) =ᶠ[𝓝 z]
      fun w => (1 / 2 : ℝ) * g.metricRate w α β :=
    eventually_of_mem hU fun w hw => by
      simp only
      rw [hs.christoffel_zero_succ_succ hw]
      ring
  have hk : DifferentiableAt ℝ (fun w => g.metricRate w α β) z := by
    have h2 := ((hΓ 0 α.succ β.succ).congr_of_eventuallyEq h0.symm).const_mul 2
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards with w
    ring
  have hzero : (fun w => christoffelOf g.coefficient w 0 0 β.succ) =ᶠ[𝓝 z] fun _ => 0 :=
    eventually_of_mem hU fun w hw => hs.christoffel_zero_zero_succ hw β.succ
  have hT1 : ∑ i, fderiv ℝ (fun w => christoffelOf g.coefficient w i α.succ β.succ) z
      (Pi.single i 1) =
      fderiv ℝ (fun w => g.metricRate w α β) z (Pi.single 0 1) / 2 +
        ∑ γ : Fin d, fderiv ℝ (fun w => christoffelOf g.coefficient w γ.succ α.succ β.succ) z
          (Pi.single γ.succ 1) := by
    rw [Fin.sum_univ_succ, h0.fderiv_eq, fderiv_const_mul hk, smul_apply, smul_eq_mul]
    ring
  have hT2 : ∑ i, fderiv ℝ (fun w => christoffelOf g.coefficient w i i β.succ) z
      (Pi.single α.succ 1) =
      ∑ γ : Fin d, fderiv ℝ (fun w => christoffelOf g.coefficient w γ.succ γ.succ β.succ) z
        (Pi.single α.succ 1) := by
    rw [Fin.sum_univ_succ, hzero.fderiv_eq, fderiv_const_apply, zero_apply, zero_add]
  have hT3 : ∑ i, ∑ a, christoffelOf g.coefficient z i i a *
      christoffelOf g.coefficient z a α.succ β.succ =
      ∑ γ : Fin d, (g.extrinsicRate z γ γ * g.metricRate z α β / 4 +
        ∑ δ : Fin d, christoffelOf g.coefficient z γ.succ γ.succ δ.succ *
          christoffelOf g.coefficient z δ.succ α.succ β.succ) := by
    simp only [Fin.sum_univ_succ (n := d), hs.christoffel_zero_zero hz,
      hs.christoffel_zero_zero_succ hz, hs.christoffel_succ_succ_zero hz,
      hs.christoffel_zero_succ_succ hz, zero_mul, zero_add, Finset.sum_const_zero]
    exact Finset.sum_congr rfl fun γ _ => by ring
  have hT4 : ∑ i, ∑ a, christoffelOf g.coefficient z i α.succ a *
      christoffelOf g.coefficient z a i β.succ =
      ∑ δ : Fin d, g.metricRate z α δ * g.extrinsicRate z δ β / 4 +
        ∑ γ : Fin d, (g.extrinsicRate z γ α * g.metricRate z γ β / 4 +
          ∑ δ : Fin d, christoffelOf g.coefficient z γ.succ α.succ δ.succ *
            christoffelOf g.coefficient z δ.succ γ.succ β.succ) := by
    simp only [Fin.sum_univ_succ (n := d), hs.christoffel_zero_succ_zero hz,
      hs.christoffel_zero_zero_succ hz, hs.christoffel_zero_succ_succ hz,
      hs.christoffel_succ_zero_succ hz, hs.christoffel_succ_succ_zero hz, zero_mul, zero_add]
    rw [Finset.sum_congr rfl fun δ _ => (by ring : g.metricRate z α δ / 2 *
      (g.extrinsicRate z δ β / 2) = g.metricRate z α δ * g.extrinsicRate z δ β / 4)]
    exact congrArg _ (Finset.sum_congr rfl fun γ _ => by ring)
  have hR : ricciOf g.coefficient z α.succ β.succ =
      ∑ i, fderiv ℝ (fun w => christoffelOf g.coefficient w i α.succ β.succ) z (Pi.single i 1) -
        ∑ i, fderiv ℝ (fun w => christoffelOf g.coefficient w i i β.succ) z
          (Pi.single α.succ 1) +
        ∑ i, ∑ a, christoffelOf g.coefficient z i i a *
          christoffelOf g.coefficient z a α.succ β.succ -
        ∑ i, ∑ a, christoffelOf g.coefficient z i α.succ a *
          christoffelOf g.coefficient z a i β.succ := by
    unfold ricciOf
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [hR, hT1, hT2, hT3, hT4, sliceRicci]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_div, sub_div]
  ring

/-- **The time lines are geodesics in the proper time, orthogonal to the slices**: a curve
`t ↦ z₀ + t e₀` in `U` on an open set of times is a geodesic of the synchronous metric, its
velocity has norm `−1` and it is orthogonal to the spatial co-ordinate directions. -/
theorem isGeodesicOn_timeLine {γ : ℝ → U} {s : Set ℝ} (hso : IsOpen s) {z₀ : MinkowskiModel d}
    (hγ : ∀ t ∈ s, (γ t : MinkowskiModel d) = z₀ + t • Pi.single 0 1) :
    g.toLorentzMetric.IsGeodesicOn s γ ∧ ∀ t ∈ s,
      g.toLorentzMetric.form (γ t) (curveVelocity γ t) (curveVelocity γ t) = -1 ∧
        ∀ α : Fin d, g.toLorentzMetric.form (γ t) (curveVelocity γ t) (Pi.single α.succ 1) = 0 := by
  have hev (t : ℝ) (ht : t ∈ s) : (fun t' => (γ t' : MinkowskiModel d)) =ᶠ[𝓝 t]
      fun t' => z₀ + t' • Pi.single 0 1 :=
    eventually_of_mem (hso.mem_nhds ht) hγ
  have hline (t : ℝ) : HasDerivAt (fun t' => z₀ + t' • (Pi.single 0 1 : MinkowskiModel d))
      (Pi.single 0 1) t := by
    simpa using ((hasDerivAt_id t).smul_const (Pi.single 0 1 : MinkowskiModel d)).const_add z₀
  have hsmooth (t : ℝ) (ht : t ∈ s) : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, MinkowskiModel d) 2 γ t :=
    contMDiffAt_iff_contDiffAt_val.mpr
      ((contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffAt.congr_of_eventuallyEq
        (hev t ht))
  have hderiv (t : ℝ) (ht : t ∈ s) : deriv (fun t' => (γ t' : MinkowskiModel d)) t =
      Pi.single 0 1 := by
    rw [(hev t ht).deriv_eq]
    exact (hline t).deriv
  have hvel (t : ℝ) (ht : t ∈ s) : curveVelocity γ t = (Pi.single 0 1 : MinkowskiModel d) := by
    rw [curveVelocity_val ((hsmooth t ht).mdifferentiableAt (by norm_num)), hderiv t ht]
  refine ⟨fun t ht => ⟨hsmooth t ht, ?_⟩, fun t ht => ⟨?_, fun α => ?_⟩⟩
  · have he := physicalChart_mem (γ t)
    have hx : γ t ∈ (physicalChart (γ t)).source := by simp
    have hcomp : (physicalChart (γ t) ∘ γ) = fun t' => (γ t' : MinkowskiModel d) :=
      funext fun t' => physicalChart_apply (γ t) (γ t')
    rw [g.toLorentzMetric.geodesic_equation_iff_coordinates he hx (hsmooth t ht), hcomp]
    intro k
    have hdd : deriv (deriv (fun t' => (γ t' : MinkowskiModel d))) t = 0 := by
      have h : deriv (fun t' => (γ t' : MinkowskiModel d)) =ᶠ[𝓝 t] fun _ => Pi.single 0 1 :=
        eventually_of_mem (hso.mem_nhds ht) hderiv
      rw [h.deriv_eq, deriv_const]
    rw [hdd, hderiv t ht]
    simp only [Pi.zero_apply, zero_add, toLorentzMetric_chartChristoffel, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact hs.christoffel_zero_zero (γ t).property k
  · rw [hvel t ht]
    exact (hs (γ t) (γ t).property).1
  · rw [hvel t ht]
    exact (hs (γ t) (γ t).property).2 α

end IsSynchronous

end ProjectAinos.SmoothGeometry.CoordinateMetric
