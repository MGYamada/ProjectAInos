/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.ScalarCurvatureVariation
public import ProjectAinos.SmoothGeometry.Lorentzian.Einstein
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The first variation of the relative scalar-curvature action

For a coordinate metric `g` on an open set `U` of the model space and a smooth symmetric
variation `h` with compact support in `U`, the relative action

`ε ↦ ∫ ((R_ε − 2Λ) √|g_ε| − (R − 2Λ) √|g|) dx`

of `g_ε = g + ε h` has at `ε = 0` the derivative
`−∫ (Ric^{mn} − (R/2 − Λ) g^{mn}) h_{mn} √|g| dx` (`hasDerivAt_integral_scalarDensity`).

* The integrand vanishes outside the support of `h`: every quantity is a function of the germ of
  the coefficients (`scalarOf_congr`, `densityOf_congr`).
* The derivative is taken under the integral on a compact set, where the derivative in `ε` is
  bounded by the smoothness of the family in `(ε, z)`.
* The divergence term `∂_a(√|g| V^a)` integrates to zero: it has compact support.
* For every admissible `ε` the integrand is the native density of the Lorentz metric `g + εh`
  (`scalarDensity_eq_toLorentzMetric`), and the derivative is
  `∫ (G_{ik} + Λ g_{ik}) δg^{ik} √|g| dx` with the native Einstein tensor
  (`toLorentzMetric_einstein_chartField`, `eulerLagrangeDensity_eq`).
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

namespace CoordinateMetric

/-! ### Locality -/

section Locality

variable {C C' : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}

theorem christoffelOf_congr (hC : C =ᶠ[𝓝 x] C') (k i j : Fin (d + 1)) :
    christoffelOf C x k i j = christoffelOf C' x k i j := by
  have hd (a b : Fin (d + 1)) : fderiv ℝ (fun z => C z a b) x = fderiv ℝ (fun z => C' z a b) x :=
    Filter.EventuallyEq.fderiv_eq (hC.mono fun z hz => congrArg (fun M => M a b) hz)
  unfold christoffelOf
  rw [hC.eq_of_nhds]
  simp only [hd]

theorem christoffelOf_eventuallyEq (hC : C =ᶠ[𝓝 x] C') (k i j : Fin (d + 1)) :
    (fun z => christoffelOf C z k i j) =ᶠ[𝓝 x] fun z => christoffelOf C' z k i j :=
  hC.eventuallyEq_nhds.mono fun _ hz => christoffelOf_congr hz k i j

theorem ricciOf_congr (hC : C =ᶠ[𝓝 x] C') (j k : Fin (d + 1)) :
    ricciOf C x j k = ricciOf C' x j k := by
  have hd (a b c : Fin (d + 1)) := (christoffelOf_eventuallyEq hC a b c).fderiv_eq (𝕜 := ℝ)
  unfold ricciOf
  simp only [hd, christoffelOf_congr hC]

theorem scalarOf_congr (hC : C =ᶠ[𝓝 x] C') : scalarOf C x = scalarOf C' x := by
  unfold scalarOf
  simp only [ricciOf_congr hC, hC.eq_of_nhds]

theorem densityOf_congr (hC : C =ᶠ[𝓝 x] C') : densityOf C x = densityOf C' x := by
  unfold densityOf
  rw [hC.eq_of_nhds]

end Locality

/-! ### Constant coefficients -/

section Constant

variable (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (y : MinkowskiModel d)

@[simp] theorem christoffelOf_const (k i j : Fin (d + 1)) :
    christoffelOf (fun _ => M) y k i j = 0 := by
  simp [christoffelOf]

@[simp] theorem ricciOf_const (j k : Fin (d + 1)) : ricciOf (fun _ => M) y j k = 0 := by
  simp [ricciOf]

@[simp] theorem scalarOf_const : scalarOf (fun _ => M) y = 0 := by
  simp [scalarOf]

end Constant

theorem minkowski_coefficient {U : Opens (MinkowskiModel d)} (y : MinkowskiModel d) :
    (minkowski σ d U).coefficient y = Matrix.diagonal (lorentzSign σ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [coefficient, minkowski, minkowskiForm_apply, Pi.single_apply]
  · simp [coefficient, minkowski, minkowskiForm_apply, Pi.single_apply, hij, Ne.symm hij]

variable {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U)
  (h : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)

/-- The density `(R − 2Λ) √|g|` of `g + ε h`, as a function of `(ε, z)`. -/
def scalarDensity (Λ : ℝ) (p : ℝ × MinkowskiModel d) : ℝ :=
  (familyScalar (g.variationFamily h) p - 2 * Λ) * familyDensity (g.variationFamily h) p

variable {g h}

theorem variationFamily_eventuallyEq_of_notMem {x : MinkowskiModel d} (hx : x ∉ tsupport h)
    (ε : ℝ) :
    (fun z => g.variationFamily h (ε, z)) =ᶠ[𝓝 x] fun z => g.variationFamily h (0, z) := by
  filter_upwards [(isClosed_tsupport h).isOpen_compl.mem_nhds hx] with z hz
  have hz0 : h z = 0 := image_eq_zero_of_notMem_tsupport hz
  have hf : formCoeff h z = 0 := by
    ext i j
    simp [formCoeff, hz0]
  simp [variationFamily, hf]

/-- Outside the support of the variation, the density does not change. -/
theorem scalarDensity_of_notMem (Λ : ℝ) {x : MinkowskiModel d} (hx : x ∉ tsupport h) (ε : ℝ) :
    g.scalarDensity h Λ (ε, x) = g.scalarDensity h Λ (0, x) := by
  have hC := variationFamily_eventuallyEq_of_notMem (g := g) hx ε
  unfold scalarDensity familyScalar familyDensity
  rw [scalarOf_congr hC, densityOf_congr hC]

theorem contDiffAt_scalarDensity (hh : ContDiff ℝ ∞ h) (Λ : ℝ) {p : ℝ × MinkowskiModel d}
    (hp : p.2 ∈ U) (hdet : (g.variationFamily h p).det ≠ 0) :
    ContDiffAt ℝ ∞ (g.scalarDensity h Λ) p := by
  have hC := fun i j => contDiffAt_variationFamily (g := g) hh hp i j
  exact ((contDiffAt_familyScalar hC hdet).sub contDiffAt_const).mul
    (contDiffAt_familyDensity hC hdet)

theorem variationFamily_det_ne_zero (hh : ContDiff ℝ ∞ h) {ε : ℝ} (hε : g.IsAdmissible h ε)
    {z : MinkowskiModel d} (hz : z ∈ U) : (g.variationFamily h (ε, z)).det ≠ 0 := by
  have h1 := (g.addVariation h hh.contDiffOn ε hε).coefficient_det_ne_zero ⟨z, hz⟩
  rwa [addVariation_coefficient] at h1

/-- A function of `(t, z)` that does not depend on `t` near `(0, x)` has zero derivative in `t`. -/
theorem fderiv_fst_eq_zero_of_eventually {Φ : ℝ × MinkowskiModel d → ℝ} {x : MinkowskiModel d}
    (hΦ : Φ =ᶠ[𝓝 ((0 : ℝ), x)] fun q => Φ (0, q.2)) :
    fderiv ℝ Φ ((0 : ℝ), x) (1, 0) = 0 := by
  rw [hΦ.fderiv_eq]
  by_cases hd : DifferentiableAt ℝ (fun z => Φ (0, z)) x
  · have hc : HasFDerivAt (fun q : ℝ × MinkowskiModel d => Φ (0, q.2))
        ((fderiv ℝ (fun z => Φ (0, z)) x).comp
          (ContinuousLinearMap.snd ℝ ℝ (MinkowskiModel d))) ((0 : ℝ), x) :=
      HasFDerivAt.comp (g := fun z => Φ (0, z)) ((0 : ℝ), x) hd.hasFDerivAt
        (hasFDerivAt_snd (𝕜 := ℝ) (p := ((0 : ℝ), x)))
    rw [hc.fderiv]
    simp
  · have hnd : ¬ DifferentiableAt ℝ (fun q : ℝ × MinkowskiModel d => Φ (0, q.2))
        ((0 : ℝ), x) := fun hq => hd (by
      have hin : DifferentiableAt ℝ (fun z : MinkowskiModel d => ((0 : ℝ), z)) x :=
        (differentiableAt_const _).prodMk differentiableAt_id
      exact hq.comp x hin)
    rw [fderiv_zero_of_not_differentiableAt hnd]
    rfl

/-- The variation of the Christoffel symbols vanishes outside the support of `h`. -/
theorem christoffelVariation_of_notMem {x : MinkowskiModel d} (hx : x ∉ tsupport h)
    (k i j : Fin (d + 1)) : g.christoffelVariation h x k i j = 0 := by
  refine fderiv_fst_eq_zero_of_eventually ?_
  have hopen := (isClosed_tsupport h).isOpen_compl
  have hev : ∀ᶠ q : ℝ × MinkowskiModel d in 𝓝 ((0 : ℝ), x), q.2 ∈ (tsupport h)ᶜ :=
    continuousAt_snd.eventually (hopen.mem_nhds hx)
  filter_upwards [hev] with q hq
  unfold familyChristoffel
  exact christoffelOf_congr (variationFamily_eventuallyEq_of_notMem (g := g) hq q.1) k i j

theorem variationVector_of_notMem {x : MinkowskiModel d} (hx : x ∉ tsupport h)
    (a : Fin (d + 1)) : g.variationVector h x a = 0 := by
  simp [variationVector, christoffelVariation_of_notMem (g := g) hx]

/-- The divergence term vanishes near every point outside the support of `h`. -/
theorem density_mul_variationVector_eventuallyEq {x : MinkowskiModel d} (hx : x ∉ tsupport h)
    (a : Fin (d + 1)) :
    (fun z => densityOf g.coefficient z * g.variationVector h z a) =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [(isClosed_tsupport h).isOpen_compl.mem_nhds hx] with z hz
  simp [variationVector_of_notMem (g := g) hz a]

theorem contDiffAt_christoffelVariation' (hh : ContDiff ℝ ∞ h) {x : MinkowskiModel d}
    (hx : x ∈ U) (k i j : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (fun z => g.christoffelVariation h z k i j) x := by
  have hD := ((g.contDiffAt_variationChristoffel hh hx k i j).fderiv_right (m := ∞)
    (by simp)).clm_apply (contDiffAt_const (c := ((1 : ℝ), (0 : MinkowskiModel d))))
  have hin : ContDiffAt ℝ ∞ (fun z : MinkowskiModel d => ((0 : ℝ), z)) x :=
    contDiffAt_const.prodMk contDiffAt_id
  exact hD.comp x hin

theorem contDiff_density_mul_variationVector (hh : ContDiff ℝ ∞ h)
    (hKU : tsupport h ⊆ U) (a : Fin (d + 1)) :
    ContDiff ℝ ∞ (fun z => densityOf g.coefficient z * g.variationVector h z a) := by
  refine contDiff_iff_contDiffAt.mpr fun x => ?_
  by_cases hx : x ∈ U
  · have hG (b c : Fin (d + 1)) : ContDiffAt ℝ ∞ (fun z => (g.coefficient z)⁻¹ b c) x :=
      (g.contDiffOn_coefficient_inv b c).contDiffAt (U.isOpen.mem_nhds hx)
    have hP := contDiffAt_christoffelVariation' (g := g) hh hx
    refine (g.contDiffAt_densityOf hx).mul ?_
    unfold variationVector
    exact (ContDiffAt.sum fun b _ => ContDiffAt.sum fun c _ => (hG b c).mul (hP a b c)).sub
      (ContDiffAt.sum fun b _ => (hG a b).mul (ContDiffAt.sum fun c _ => hP c c b))
  · have hxK : x ∉ tsupport h := fun h' => hx (hKU h')
    exact contDiffAt_const.congr_of_eventuallyEq
      (density_mul_variationVector_eventuallyEq (g := g) hxK a)

theorem hasCompactSupport_density_mul_variationVector (hK : HasCompactSupport h)
    (a : Fin (d + 1)) :
    HasCompactSupport (fun z => densityOf g.coefficient z * g.variationVector h z a) := by
  refine HasCompactSupport.intro hK fun z hz => ?_
  simp [variationVector_of_notMem (g := g) hz a]

/-- The divergence term integrates to zero. -/
theorem integral_fderiv_density_mul_variationVector (hh : ContDiff ℝ ∞ h)
    (hK : HasCompactSupport h) (hKU : tsupport h ⊆ U) (a : Fin (d + 1)) :
    (∫ x, fderiv ℝ (fun z => densityOf g.coefficient z * g.variationVector h z a) x
      (Pi.single a 1)) = 0 := by
  set f := fun z => densityOf g.coefficient z * g.variationVector h z a
  have hf : ContDiff ℝ 1 f := (contDiff_density_mul_variationVector (g := g) hh hKU a).of_le
    (by simp)
  have hk : HasCompactSupport f := hasCompactSupport_density_mul_variationVector (g := g) hK a
  have hzero : Integrable (fun x : MinkowskiModel d =>
      fderiv ℝ (fun _ : MinkowskiModel d => (1 : ℝ)) x (Pi.single a 1) * f x) volume := by
    simp
  have hleft : Integrable (fun x => (1 : ℝ) * fderiv ℝ f x (Pi.single a 1)) volume := by
    simpa only [one_mul] using Continuous.integrable_of_hasCompactSupport
      ((hf.fderiv_right (m := 0) (by norm_num)).continuous.clm_apply continuous_const)
      (hk.fderiv_apply ℝ (Pi.single a 1))
  have hprod : Integrable (fun x => (1 : ℝ) * f x) volume := by
    simpa only [one_mul] using hf.continuous.integrable_of_hasCompactSupport hk
  simpa using integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hzero hleft hprod
    (fun _ _ => differentiableAt_const _) (fun x _ => hf.differentiable one_ne_zero x)

variable (g h) in
/-- The Euler–Lagrange density `−(Ric^{mn} − (R/2 − Λ) g^{mn}) h_{mn} √|g|`. -/
def eulerLagrangeDensity (Λ : ℝ) (x : MinkowskiModel d) : ℝ :=
  -(densityOf g.coefficient x * ∑ m, ∑ n, (g.ricciUp x m n -
    (scalarOf g.coefficient x / 2 - Λ) * (g.coefficient x)⁻¹ m n) * formCoeff h x m n)

theorem eulerLagrangeDensity_of_notMem (Λ : ℝ) {x : MinkowskiModel d} (hx : x ∉ tsupport h) :
    g.eulerLagrangeDensity h Λ x = 0 := by
  have hf : formCoeff h x = 0 := by
    ext i j
    simp [formCoeff, image_eq_zero_of_notMem_tsupport hx]
  simp [eulerLagrangeDensity, hf]

/-- The derivative in `ε` at `0` of the density at every point of the model. -/
theorem deriv_scalarDensity_zero (hh : ContDiff ℝ ∞ h) (hs : ∀ z v w, h z v w = h z w v)
    (hKU : tsupport h ⊆ U) (Λ : ℝ) (x : MinkowskiModel d) :
    deriv (fun t => g.scalarDensity h Λ (t, x)) 0 = g.eulerLagrangeDensity h Λ x +
      ∑ a, fderiv ℝ (fun z => densityOf g.coefficient z * g.variationVector h z a) x
        (Pi.single a 1) := by
  by_cases hx : x ∈ U
  · exact (hasDerivAt_scalarDensity hh hs Λ hx).deriv
  · have hxK : x ∉ tsupport h := fun h' => hx (hKU h')
    rw [show (fun t => g.scalarDensity h Λ (t, x)) = fun _ => g.scalarDensity h Λ (0, x) from
      funext fun t => scalarDensity_of_notMem Λ hxK t, deriv_const,
      eulerLagrangeDensity_of_notMem Λ hxK]
    have hz (a : Fin (d + 1)) : fderiv ℝ (fun z => densityOf g.coefficient z *
        g.variationVector h z a) x = 0 := by
      rw [(density_mul_variationVector_eventuallyEq (g := g) hxK a).fderiv_eq]
      exact fderiv_const_apply _
    simp [hz]

/-- **The first variation of the relative scalar-curvature action.** For a smooth symmetric
variation `h` with compact support in `U`,
`d/dε ∫ ((R_ε − 2Λ) √|g_ε| − (R − 2Λ) √|g|) dx = −∫ (Ric^{mn} − (R/2 − Λ) g^{mn}) h_{mn} √|g| dx`
at `ε = 0`. -/
theorem hasDerivAt_integral_scalarDensity (hh : ContDiff ℝ ∞ h) (hK : HasCompactSupport h)
    (hKU : tsupport h ⊆ U) (hs : ∀ z v w, h z v w = h z w v) (Λ : ℝ) :
    HasDerivAt (fun ε => ∫ x, (g.scalarDensity h Λ (ε, x) - g.scalarDensity h Λ (0, x)))
      (∫ x, g.eulerLagrangeDensity h Λ x) 0 := by
  set K := tsupport h
  have hKc : IsCompact K := hK
  obtain ⟨δ, hδ, hadm⟩ :=
    Metric.eventually_nhds_iff.mp (g.eventually_isAdmissible hh.continuous hK hKU hs)
  set s := Metric.closedBall (0 : ℝ) (δ / 2)
  have hs0 : s ∈ 𝓝 (0 : ℝ) := Metric.closedBall_mem_nhds _ (half_pos hδ)
  have h0s : (0 : ℝ) ∈ s := Metric.mem_closedBall_self (half_pos hδ).le
  have hsadm : ∀ ε ∈ s, g.IsAdmissible h ε := fun ε hε => hadm (by
    rw [Metric.mem_closedBall] at hε
    linarith [half_lt_self hδ])
  set L := g.scalarDensity h Λ
  have hL : ∀ ε ∈ s, ∀ z ∈ U, ContDiffAt ℝ ∞ L (ε, z) := fun ε hε z hz =>
    contDiffAt_scalarDensity hh Λ hz (variationFamily_det_ne_zero hh (hsadm ε hε) hz)
  have hconst : ∀ x ∉ K, (fun t => L (t, x)) = fun _ => L (0, x) := fun x hx =>
    funext fun t => scalarDensity_of_notMem Λ hx t
  -- the bound on the derivative in `ε`
  set D : ℝ × MinkowskiModel d → ℝ := fun q => fderiv ℝ L q (1, 0)
  have hDat : ∀ ε ∈ s, ∀ z ∈ U, ContinuousAt D (ε, z) := fun ε hε z hz =>
    ((hL ε hε z hz).fderiv_right (m := 0) (by simp)).continuousAt.clm_apply continuousAt_const
  have hDcont : ContinuousOn D (s ×ˢ K) := fun q hq =>
    (hDat q.1 hq.1 q.2 (hKU hq.2)).continuousWithinAt
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall (0 : ℝ) (δ / 2)).prod hKc).exists_bound_of_continuousOn hDcont
  have hslice : ∀ ε ∈ s, ∀ z ∈ U, deriv (fun t => L (t, z)) ε = D (ε, z) := fun ε hε z hz =>
    (hasDerivAt_slice ((hL ε hε z hz).differentiableAt (by simp))).deriv
  have hderiv : ∀ x, ∀ ε ∈ s, HasDerivAt (fun t => L (t, x) - L (0, x))
      (deriv (fun t => L (t, x)) ε) ε := by
    intro x ε hε
    by_cases hxK : x ∈ K
    · have hd := hasDerivAt_slice ((hL ε hε x (hKU hxK)).differentiableAt (by simp))
      rw [hd.deriv]
      exact hd.sub_const _
    · have h1 : (fun t => L (t, x) - L (0, x)) = fun _ => 0 := funext fun t => by
        rw [show L (t, x) = L (0, x) from congrFun (hconst x hxK) t, sub_self]
      rw [h1, hconst x hxK, deriv_const]
      exact hasDerivAt_const _ _
  have hbound : ∀ x, ∀ ε ∈ s, ‖deriv (fun t => L (t, x)) ε‖ ≤ K.indicator (fun _ => C) x := by
    intro x ε hε
    by_cases hxK : x ∈ K
    · rw [Set.indicator_of_mem hxK, hslice ε hε x (hKU hxK)]
      exact hC (ε, x) ⟨hε, hxK⟩
    · rw [Set.indicator_of_notMem hxK, hconst x hxK, deriv_const, norm_zero]
  have hbint : Integrable (K.indicator fun _ => C) volume :=
    (continuousOn_const.integrableOn_compact hKc).integrable_indicator
      hKc.isClosed.measurableSet
  -- continuity in the point
  have hin (t : ℝ) (x : MinkowskiModel d) : ContinuousAt (fun z : MinkowskiModel d => (t, z)) x :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hFcont : ∀ ε ∈ s, Continuous (fun x => L (ε, x) - L (0, x)) := by
    intro ε hε
    refine continuous_iff_continuousAt.mpr fun x => ?_
    by_cases hx : x ∈ U
    · exact ((hL ε hε x hx).continuousAt.comp_of_eq (hin ε x) rfl).sub
        ((hL 0 h0s x hx).continuousAt.comp_of_eq (hin 0 x) rfl)
    · have hxK : x ∉ K := fun h' => hx (hKU h')
      refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [(isClosed_tsupport h).isOpen_compl.mem_nhds hxK] with z hz
      rw [show L (ε, z) = L (0, z) from congrFun (hconst z hz) ε, sub_self]
  have hF'cont : Continuous (fun x => deriv (fun t => L (t, x)) 0) := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    by_cases hx : x ∈ U
    · have hDc : ContinuousAt (fun z => D (0, z)) x := (hDat 0 h0s x hx).comp_of_eq (hin 0 x) rfl
      refine hDc.congr ?_
      filter_upwards [U.isOpen.mem_nhds hx] with z hz
      exact (hslice 0 h0s z hz).symm
    · have hxK : x ∉ K := fun h' => hx (hKU h')
      refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [(isClosed_tsupport h).isOpen_compl.mem_nhds hxK] with z hz
      rw [hconst z hz, deriv_const]
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun ε x => L (ε, x) - L (0, x)) (F' := fun ε x => deriv (fun t => L (t, x)) ε)
    (bound := K.indicator fun _ => C) hs0
    (Filter.eventually_of_mem hs0 fun ε hε => (hFcont ε hε).aestronglyMeasurable)
    (by simp) hF'cont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ε hε => hbound x ε hε) hbint
    (Filter.Eventually.of_forall fun x ε hε => hderiv x ε hε)
  -- the divergence terms integrate to zero
  have hdivint (a : Fin (d + 1)) : Integrable (fun x => fderiv ℝ
      (fun z => densityOf g.coefficient z * g.variationVector h z a) x (Pi.single a 1)) volume :=
    Continuous.integrable_of_hasCompactSupport
      (((contDiff_density_mul_variationVector (g := g) hh hKU a).fderiv_right (m := 0)
        (by simp)).continuous.clm_apply continuous_const)
      ((hasCompactSupport_density_mul_variationVector (g := g) hK a).fderiv_apply ℝ _)
  have hsumint : Integrable (fun x => ∑ a, fderiv ℝ
      (fun z => densityOf g.coefficient z * g.variationVector h z a) x (Pi.single a 1)) volume :=
    integrable_finsetSum _ fun a _ => hdivint a
  have hpt (x : MinkowskiModel d) : deriv (fun t => L (t, x)) 0 = g.eulerLagrangeDensity h Λ x +
      ∑ a, fderiv ℝ (fun z => densityOf g.coefficient z * g.variationVector h z a) x
        (Pi.single a 1) :=
    deriv_scalarDensity_zero (g := g) hh hs hKU Λ x
  have heint : Integrable (g.eulerLagrangeDensity h Λ) volume := by
    refine (hmain.1.sub hsumint).congr (Filter.Eventually.of_forall fun x => ?_)
    change deriv (fun t => L (t, x)) 0 - _ = _
    rw [hpt x]
    ring
  have hval : (∫ x, deriv (fun t => L (t, x)) 0) = ∫ x, g.eulerLagrangeDensity h Λ x := by
    rw [show (fun x => deriv (fun t => L (t, x)) 0) = fun x => g.eulerLagrangeDensity h Λ x +
      ∑ a, fderiv ℝ (fun z => densityOf g.coefficient z * g.variationVector h z a) x
        (Pi.single a 1) from funext hpt]
    rw [integral_add heint hsumint, integral_finsetSum _ fun a _ => hdivint a]
    simp [integral_fderiv_density_mul_variationVector (g := g) hh hK hKU]
  rw [← hval]
  exact hmain.2

/-! ### The native reading -/

section Native

/-- The integrand is the native density `(R − 2Λ) √|g|` of the Lorentz metric `g + εh`. -/
theorem scalarDensity_eq_toLorentzMetric (hh : ContDiffOn ℝ ∞ h U) {ε : ℝ}
    (hε : g.IsAdmissible h ε) (Λ : ℝ) (y : U) :
    g.scalarDensity h Λ (ε, y) =
      ((g.addVariation h hh ε hε).toLorentzMetric.scalarCurvature y - 2 * Λ) *
        (g.addVariation h hh ε hε).toLorentzMetric.chartDensity (physicalChart y) y := by
  rw [toLorentzMetric_scalarCurvature, toLorentzMetric_chartDensity, addVariation_coefficient]
  rfl

/-- At `ε = 0` the integrand is the native density of `g`. -/
theorem scalarDensity_zero_eq_toLorentzMetric (Λ : ℝ) (y : U) :
    g.scalarDensity h Λ (0, y) = (g.toLorentzMetric.scalarCurvature y - 2 * Λ) *
      g.toLorentzMetric.chartDensity (physicalChart y) y := by
  rw [toLorentzMetric_scalarCurvature, toLorentzMetric_chartDensity, scalarDensity,
    familyScalar, familyDensity, variationFamily_zero]

/-- The Einstein tensor `R_{ik} − (R/2) g_{ik}` of the coefficients. -/
def einsteinOf (C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (y : MinkowskiModel d) (i k : Fin (d + 1)) : ℝ :=
  ricciOf C y i k - scalarOf C y / 2 * C y i k

@[simp] theorem einsteinOf_const (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (y : MinkowskiModel d) (i k : Fin (d + 1)) : einsteinOf (fun _ => M) y i k = 0 := by
  simp [einsteinOf]

/-- The native Einstein tensor on the co-ordinate fields. -/
theorem toLorentzMetric_einstein_chartField (x y : U) (i k : Fin (d + 1)) :
    g.toLorentzMetric.einstein y (chartField (physicalChart x) (Pi.single i 1) y)
      (chartField (physicalChart x) (Pi.single k 1) y) = einsteinOf g.coefficient y i k := by
  have hf : g.toLorentzMetric.form y (chartField (physicalChart x) (Pi.single i 1) y)
      (chartField (physicalChart x) (Pi.single k 1) y) = g.coefficient y i k :=
    g.toLorentzMetric_chartComponent x y i k
  rw [einstein_apply, hf, g.toLorentzMetric_ricci_chartField x y,
    g.toLorentzMetric_scalarCurvature, einsteinOf]

variable (g h) in
/-- The variation `δg^{ik} = −g^{im} h_{mn} g^{nk}` of the inverse coefficients. -/
def inverseVariation (x : MinkowskiModel d) (i k : Fin (d + 1)) : ℝ :=
  -((g.coefficient x)⁻¹ * formCoeff h x * (g.coefficient x)⁻¹) i k

/-- `δg^{ik}` is the derivative of the inverse coefficients of `g + εh`. -/
theorem hasDerivAt_inverseVariation (hh : ContDiff ℝ ∞ h) {x : MinkowskiModel d} (hx : x ∈ U)
    (i k : Fin (d + 1)) :
    HasDerivAt (fun ε => (g.variationFamily h (ε, x))⁻¹ i k) (g.inverseVariation h x i k) 0 :=
  hasDerivAt_variationFamily_inv hh hx i k

/-- Raising both indices of the coefficients gives the inverse. -/
theorem sum_inv_mul_inv_mul_coefficient {x : MinkowskiModel d} (hx : x ∈ U)
    (m n : Fin (d + 1)) :
    ∑ a, ∑ c, (g.coefficient x)⁻¹ m a * (g.coefficient x)⁻¹ n c * g.coefficient x a c =
      (g.coefficient x)⁻¹ m n := by
  have h1 : (g.coefficient x)⁻¹ * g.coefficient x = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (g.coefficient_det_ne_zero ⟨x, hx⟩))
  have h2 (c : Fin (d + 1)) : ∑ a, (g.coefficient x)⁻¹ m a * g.coefficient x a c =
      (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) m c := by
    rw [← h1, Matrix.mul_apply]
  calc ∑ a, ∑ c, (g.coefficient x)⁻¹ m a * (g.coefficient x)⁻¹ n c * g.coefficient x a c
      = ∑ c, (g.coefficient x)⁻¹ n c * ∑ a, (g.coefficient x)⁻¹ m a * g.coefficient x a c := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => by ring
    _ = (g.coefficient x)⁻¹ n m := by
        simp only [h2, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
          Finset.mem_univ, ite_true]
    _ = (g.coefficient x)⁻¹ m n := g.coefficient_inv_symmetric hx n m

/-- The Euler–Lagrange density is `(G_{ik} + Λ g_{ik}) δg^{ik} √|g|`. -/
theorem eulerLagrangeDensity_eq (hKU : tsupport h ⊆ U) (Λ : ℝ) (x : MinkowskiModel d) :
    g.eulerLagrangeDensity h Λ x = (∑ i, ∑ k, (einsteinOf g.coefficient x i k +
      Λ * g.coefficient x i k) * g.inverseVariation h x i k) * densityOf g.coefficient x := by
  by_cases hx : x ∈ U
  · have hR := sum_mul_neg_sandwich (Matrix.of fun i k => einsteinOf g.coefficient x i k +
      Λ * g.coefficient x i k) _ (formCoeff h x) (g.coefficient_inv_symmetric hx)
    simp only [Matrix.of_apply] at hR
    rw [eulerLagrangeDensity]
    unfold inverseVariation
    rw [hR]
    have hT (m n : Fin (d + 1)) : ∑ a, ∑ c, (g.coefficient x)⁻¹ m a * (g.coefficient x)⁻¹ n c *
        (einsteinOf g.coefficient x a c + Λ * g.coefficient x a c) =
        g.ricciUp x m n - (scalarOf g.coefficient x / 2 - Λ) * (g.coefficient x)⁻¹ m n := by
      have h3 := g.sum_inv_mul_inv_mul_coefficient hx m n
      simp only [einsteinOf, ricciUp]
      rw [← h3, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    simp only [hT]
    ring
  · have hxK : x ∉ tsupport h := fun h' => hx (hKU h')
    have hf : formCoeff h x = 0 := by
      ext i j
      simp [formCoeff, image_eq_zero_of_notMem_tsupport hxK]
    rw [eulerLagrangeDensity_of_notMem Λ hxK]
    simp [inverseVariation, hf]

end Native

end CoordinateMetric

end ProjectAinos.SmoothGeometry
