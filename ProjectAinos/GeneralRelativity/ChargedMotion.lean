/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.ManifoldStationary
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateTangent

/-!
# A charge on a curved background

Landau–Lifshitz, §§17 and 90: the action of a charge `e` of mass `m` in the field of a potential
`A` on a curved background is `S = −m ∫ dτ + e ∫ A(γ̇) dt`. The background is a Lorentz metric
on an open set `U` of the model space and `A` a field of covectors that is `C¹` on `U`; the
variations are the actual fixed-endpoint families of curves in the manifold `U`.

* `lineIntegral_family_hasDerivAt`: the first variation of the line integral is
  `∫ F(J, γ̇) dt` with the variation field `J` and `F(u, w) = ∂_u A(w) − ∂_w A(u)`, that is
  `F_{ab} = ∂_a A_b − ∂_b A_a`; the term `d/dt A(J)` integrates to zero at the fixed end
  points.
* `chargedStationary_iff`: **the action is stationary if and only if
  `m ∇_t U = e F(·, γ̇)^♯`** along the curve, with the four-velocity `U = γ̇/s` and the proper
  speed `s = √(−g(γ̇, γ̇))`. In proper time this is `m ∇_τ U = e F(·, U)^♯ = −e (ι_U F)^♯`, and
  for `e = 0` it is the free motion of `freeStationary_iff_acceleration`.
* `fieldCovector_gauge`, `lineIntegral_gauge`, `chargedStationary_gauge_iff`: a gauge change
  `A ↦ A + dχ` leaves `F` unchanged and changes the action by the end-point term
  `e (χ(γ(b)) − χ(γ(a)))`, so the equation of motion does not change.
-/

@[expose] public section

noncomputable section

open Bundle Set Filter MeasureTheory TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.GeneralRelativity

open SmoothGeometry LorentzMetric CoordinateMetric Variational

variable {d : ℕ} {U : Opens (MinkowskiModel d)}

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "J" => 𝓘(ℝ, ℝ × ℝ)

/-- The line integral `∫ A(γ̇) dt` of a field of covectors along a curve in `U`. -/
def lineIntegral (A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ) (γ : ℝ → U) (a b : ℝ) : ℝ :=
  ∫ t in a..b, A (γ t) (curveVelocity γ t)

/-- The covector `w ↦ F(w, v)` of the field `F(u, w) = ∂_u A(w) − ∂_w A(u)` at `z`. -/
def fieldCovector (A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ) (z v : MinkowskiModel d) :
    MinkowskiModel d →L[ℝ] ℝ :=
  (fderiv ℝ A z).flip v - fderiv ℝ A z v

theorem fieldCovector_apply (A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ)
    (z v w : MinkowskiModel d) :
    fieldCovector A z v w = fderiv ℝ A z w v - fderiv ℝ A z v w := by
  simp [fieldCovector]

/-- The field is antisymmetric: `F(v, v) = 0`. -/
theorem fieldCovector_self (A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ)
    (z v : MinkowskiModel d) : fieldCovector A z v v = 0 := by
  rw [fieldCovector_apply, sub_self]

/-- The action `−m ∫ dτ + e ∫ A(γ̇) dt` of a charge in the field of the potential `A`. -/
def chargedAction (g : LorentzMetric .timeNegative d U) (m e : ℝ)
    (A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ) (γ : ℝ → U) (a b : ℝ) : ℝ :=
  freeAction g m γ a b + e * lineIntegral A γ a b

/-- Stationarity of the action of a charge under every actual fixed-endpoint family. -/
def ChargedStationary (g : LorentzMetric .timeNegative d U) (m e : ℝ)
    (A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ) (γ : ℝ → U) (a b : ℝ) : Prop :=
  ∀ V : ManifoldCurveVariation («E» := E) γ a b,
    HasDerivAt (fun ε => chargedAction g m e A (fun t => V.family (ε, t)) a b) 0 0

/-- The residual of the action of a charge: `−(m/s)(∇_t γ̇ − (ṡ/s) γ̇) + e F(·, γ̇)^♯`. -/
def chargedResidual (g : LorentzMetric .timeNegative d U) (m e : ℝ)
    (A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ) (γ : ℝ → U) (t : ℝ) :
    TangentSpace 𝓘(ℝ, MinkowskiModel d) (γ t) :=
  -(m / speedAlong g γ t) • (g.covariantAlong (curveVelocity γ) t -
      (deriv (speedAlong g γ) t / speedAlong g γ t) • curveVelocity γ t) +
    e • g.sharp (γ t) (fieldCovector A (γ t) (curveVelocity γ t))

/-- The metric pairing with a raised covector of the model. -/
theorem form_sharp_model (g : LorentzMetric .timeNegative d U) (x : U)
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) (α : MinkowskiModel d →L[ℝ] ℝ) :
    g.form x v (g.sharp x α) = α v :=
  g.form_sharp_right x v α

variable {A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ}

/-! ### The first variation of the line integral -/

/-- Near a point of `C²` regularity the density of the line integral of a family is written with
the derivative of the coordinates. -/
theorem lineDensity_eventuallyEq {Γ : ℝ × ℝ → U} {z : ℝ × ℝ} (hΓ : ContMDiffAt J I 2 Γ z) :
    (fun p : ℝ × ℝ => A (Γ p) (curveVelocity (fun s => Γ (p.1, s)) p.2)) =ᶠ[𝓝 z]
      fun p => A (Γ p) (fderiv ℝ (fun q => (Γ q : E)) p (0, 1)) := by
  have hn := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by norm_num)).mp
    (hΓ.of_le (by norm_num))
  filter_upwards [hn] with p hp
  have hd := hp.mdifferentiableAt (by norm_num)
  rw [curveVelocity_family_snd hd, familyVelocity_val (0, 1) hd]

/-- The coordinate density `A(Γ)(∂_v Γ)` is `C¹`. -/
theorem coordinateDensity_contDiffAt (hA : ContDiffOn ℝ 1 A U) {Γ : ℝ × ℝ → U} {z : ℝ × ℝ}
    (hΓ : ContMDiffAt J I 2 Γ z) (v : ℝ × ℝ) :
    ContDiffAt ℝ 1 (fun p => A (Γ p) (fderiv ℝ (fun q => (Γ q : E)) p v)) z := by
  have hΦ := contDiffAt_val hΓ
  have hAx : ContDiffAt ℝ 1 A (Γ z) := hA.contDiffAt (U.isOpen.mem_nhds (Γ z).2)
  exact (hAx.comp z (hΦ.of_le (by norm_num))).clm_apply
    ((hΦ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const)

/-- The derivative of the coordinate density along a path of parameters. -/
theorem coordinateDensity_hasDerivAt (hA : ContDiffOn ℝ 1 A U) {Γ : ℝ × ℝ → U}
    {ρ : ℝ → ℝ × ℝ} {s : ℝ} {w : ℝ × ℝ} (hρ : HasDerivAt ρ w s)
    (hΓ : ContMDiffAt J I 2 Γ (ρ s)) (v : ℝ × ℝ) :
    HasDerivAt (fun r => A (Γ (ρ r)) (fderiv ℝ (fun q => (Γ q : E)) (ρ r) v))
      (fderiv ℝ A (Γ (ρ s)) (fderiv ℝ (fun q => (Γ q : E)) (ρ s) w)
          (fderiv ℝ (fun q => (Γ q : E)) (ρ s) v) +
        A (Γ (ρ s)) (fderiv ℝ (fderiv ℝ (fun q => (Γ q : E))) (ρ s) w v)) s := by
  have hΦ := contDiffAt_val hΓ
  have hAx : ContDiffAt ℝ 1 A (Γ (ρ s)) := hA.contDiffAt (U.isOpen.mem_nhds (Γ (ρ s)).2)
  have h₁ : HasFDerivAt (fun q => A (Γ q))
      ((fderiv ℝ A (Γ (ρ s))).comp (fderiv ℝ (fun q => (Γ q : E)) (ρ s))) (ρ s) :=
    (hAx.differentiableAt (by norm_num)).hasFDerivAt.comp (ρ s)
      (hΦ.differentiableAt (by norm_num)).hasFDerivAt
  have h₂ : HasFDerivAt (fderiv ℝ (fun q => (Γ q : E)))
      (fderiv ℝ (fderiv ℝ (fun q => (Γ q : E))) (ρ s)) (ρ s) :=
    ((hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have h₃ := (h₁.comp_hasDerivAt s hρ).clm_apply
    ((h₂.comp_hasDerivAt s hρ).clm_apply (hasDerivAt_const s v))
  refine h₃.congr_deriv ?_
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, map_zero, add_zero]

/-- **The first variation of the line integral** on a family with fixed end points:
`∫ F(J, γ̇) dt` with the variation field `J`. -/
theorem lineIntegral_family_hasDerivAt (hA : ContDiffOn ℝ 1 A U) {Γ : ℝ × ℝ → U}
    {ε₀ a b : ℝ} (hΓ : ∀ t ∈ uIcc a b, ContMDiffAt J I 2 Γ (ε₀, t))
    (ha : ∀ᶠ ε in 𝓝 ε₀, Γ (ε, a) = Γ (ε₀, a))
    (hb : ∀ᶠ ε in 𝓝 ε₀, Γ (ε, b) = Γ (ε₀, b)) :
    HasDerivAt (fun ε => lineIntegral A (fun t => Γ (ε, t)) a b)
      (∫ t in a..b, fieldCovector A (Γ (ε₀, t)) (curveVelocity (fun s => Γ (ε₀, s)) t)
        (familyVelocity Γ (1, 0) (ε₀, t))) ε₀ := by
  have hp₁ (t : ℝ) : HasDerivAt (fun ε : ℝ => (ε, t)) ((1 : ℝ), (0 : ℝ)) ε₀ :=
    (hasDerivAt_id ε₀).prodMk (hasDerivAt_const ε₀ t)
  have hp₂ (t : ℝ) : HasDerivAt (fun s : ℝ => (ε₀, s)) ((0 : ℝ), (1 : ℝ)) t :=
    (hasDerivAt_const t ε₀).prodMk (hasDerivAt_id t)
  have hF : ∀ t ∈ uIcc a b, ContDiffAt ℝ 1
      (fun p : ℝ × ℝ => A (Γ p) (curveVelocity (fun s => Γ (p.1, s)) p.2)) (ε₀, t) :=
    fun t ht => (coordinateDensity_contDiffAt hA (hΓ t ht) (0, 1)).congr_of_eventuallyEq
      (lineDensity_eventuallyEq (hΓ t ht))
  have hD : ∀ t ∈ uIcc a b, HasDerivAt
      (fun ε => A (Γ (ε, t)) (curveVelocity (fun s => Γ (ε, s)) t))
      (fderiv ℝ A (Γ (ε₀, t)) (fderiv ℝ (fun q => (Γ q : E)) (ε₀, t) (1, 0))
          (fderiv ℝ (fun q => (Γ q : E)) (ε₀, t) (0, 1)) +
        A (Γ (ε₀, t)) (fderiv ℝ (fderiv ℝ (fun q => (Γ q : E))) (ε₀, t) (1, 0) (0, 1))) ε₀ :=
    fun t ht => (coordinateDensity_hasDerivAt hA (hp₁ t) (hΓ t ht) (0, 1)).congr_of_eventuallyEq
      ((lineDensity_eventuallyEq (hΓ t ht)).comp_tendsto (hp₁ t).continuousAt)
  have hP : ∀ t ∈ uIcc a b, ContDiffAt ℝ 1
      (fun s => A (Γ (ε₀, s)) (fderiv ℝ (fun q => (Γ q : E)) (ε₀, s) (1, 0))) t :=
    fun t ht => (coordinateDensity_contDiffAt hA (hΓ t ht) (1, 0)).comp t
      (contDiffAt_const.prodMk contDiffAt_id)
  have hd : ∀ t ∈ uIcc a b, HasDerivAt
      (fun s => A (Γ (ε₀, s)) (fderiv ℝ (fun q => (Γ q : E)) (ε₀, s) (1, 0)))
      ((fderiv ℝ A (Γ (ε₀, t)) (fderiv ℝ (fun q => (Γ q : E)) (ε₀, t) (1, 0))
          (fderiv ℝ (fun q => (Γ q : E)) (ε₀, t) (0, 1)) +
        A (Γ (ε₀, t)) (fderiv ℝ (fderiv ℝ (fun q => (Γ q : E))) (ε₀, t) (1, 0) (0, 1))) -
        fieldCovector A (Γ (ε₀, t)) (fderiv ℝ (fun q => (Γ q : E)) (ε₀, t) (0, 1))
          (fderiv ℝ (fun q => (Γ q : E)) (ε₀, t) (1, 0))) t := by
    intro t ht
    have h := coordinateDensity_hasDerivAt hA (hp₂ t) (hΓ t ht) (1, 0)
    have hsym := ((contDiffAt_val (hΓ t ht)).isSymmSndFDerivAt (by norm_num)).eq (0, 1) (1, 0)
    refine h.congr_deriv ?_
    rw [fieldCovector_apply, hsym]
    ring
  have hzero {c : ℝ} (hc : c ∈ uIcc a b) (hfix : ∀ᶠ ε in 𝓝 ε₀, Γ (ε, c) = Γ (ε₀, c)) :
      fderiv ℝ (fun q => (Γ q : E)) (ε₀, c) (1, 0) = 0 := by
    have hdc := (hΓ c hc).mdifferentiableAt (by norm_num)
    rw [← familyVelocity_val (1, 0) hdc]
    exact familyVelocity_fst_eq_zero_of_eventually_const hdc hfix
  refine (hasDerivAt_intervalIntegral_of_contDiffAt hF hD).congr_deriv ?_
  refine (integral_eq_boundary_add_residual hP (continuousOn_parameter_derivative hF hD)
    hd).trans ?_
  rw [hzero left_mem_uIcc ha, hzero right_mem_uIcc hb, map_zero, map_zero, sub_self, zero_add]
  apply intervalIntegral.integral_congr
  intro t ht
  have hdt := (hΓ t ht).mdifferentiableAt (by norm_num)
  have hc : curveVelocity (fun s => Γ (ε₀, s)) t = familyVelocity Γ (0, 1) (ε₀, t) :=
    curveVelocity_family_snd hdt
  dsimp only
  rw [hc, familyVelocity_val (0, 1) hdt, familyVelocity_val (1, 0) hdt]

/-! ### Stationarity -/

/-- The tangent vector of a cast is the same point of the tangent bundle. -/
theorem mk_tangentSpaceCast {x y : U} (h : x = y) (v : TangentSpace I x) :
    TotalSpace.mk' E y (tangentSpaceCast I x y v) = TotalSpace.mk' E x v := by
  subst h
  rfl

/-- The variation field of an admissible family is `C¹` along the reference curve. -/
theorem variationField_contMDiffAt {γ : ℝ → U} {a b t : ℝ}
    (V : ManifoldCurveVariation («E» := E) γ a b) (ht : t ∈ uIcc a b) :
    ContMDiffAt 𝓘(ℝ) ((I).prod I) 1
      (fun s => TotalSpace.mk' E (γ s) (variationField V s)) t := by
  have h : (fun s => TotalSpace.mk' E (γ s) (variationField V s)) =
      fun s => TotalSpace.mk' E (V.family (0, s)) (familyVelocity V.family (1, 0) (0, s)) :=
    funext fun s => mk_tangentSpaceCast (V.reference s) _
  rw [h]
  exact familyVariation_contMDiffAt (V.regular t ht)

/-- The pairing of a continuous field with the free residual is continuous. -/
theorem freeResidual_continuousAt (g : LorentzMetric .timeNegative d U) (m : ℝ)
    {γ : ℝ → U} {t : ℝ} {X : AlongField (d := d) γ} (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : Timelike g (curveVelocity γ t))
    (hX : ContMDiffAt 𝓘(ℝ) ((I).prod I) 0 (fun s => TotalSpace.mk' E (γ s) (X s)) t) :
    ContinuousAt (fun s => -(m / speedAlong g γ s) * g.form (γ s) (X s)
      (g.covariantAlong (curveVelocity γ) s -
        (deriv (speedAlong g γ) s / speedAlong g γ s) • curveVelocity γ s)) t := by
  have hcurve : ContMDiffAt 𝓘(ℝ) I 0 γ t := hγ.of_le (by norm_num)
  have hspeed : 0 < speedAlong g γ t := (properSpeed_pos_iff g _).mpr hv
  have hacc := (g.contDiffAt_pairing_along hcurve hX
    (g.covariantAcceleration_contMDiffAt hγ)).continuousAt
  have hvel := (g.contDiffAt_pairing_along hcurve hX
    ((curveVelocity_contMDiffAt (n := 1) hγ).of_le (by norm_num))).continuousAt
  have hc := contDiffAt_speedAlong g hγ hv
  have hd : ContinuousAt (deriv (speedAlong g γ)) t :=
    (hc.derivWithin (show (0 : ℕ∞ω) + 1 ≤ 1 by norm_num)).continuousAt
  have hcont : ContinuousAt (fun s => -(m / speedAlong g γ s) *
      (g.form (γ s) (X s) (g.covariantAlong (curveVelocity γ) s) -
        deriv (speedAlong g γ) s / speedAlong g γ s * g.form (γ s) (X s) (curveVelocity γ s)))
      t :=
    ((continuousAt_const (y := m)).div hc.continuousAt hspeed.ne').neg.mul
      (hacc.sub ((hd.div hc.continuousAt hspeed.ne').mul hvel))
  simpa only [map_sub, map_smul, smul_eq_mul] using hcont

/-- The field covector on a continuous field along a `C²` curve is continuous. -/
theorem fieldCovector_continuousAt (hA : ContDiffOn ℝ 1 A U) {γ : ℝ → U} {t : ℝ}
    {X : AlongField (d := d) γ} (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hX : ContMDiffAt 𝓘(ℝ) ((I).prod I) 0 (fun s => TotalSpace.mk' E (γ s) (X s)) t) :
    ContinuousAt (fun s => fieldCovector A (γ s) (curveVelocity γ s) (X s)) t := by
  have hx : ContinuousAt (fun s => (γ s : E)) t := (contDiffAt_val hγ).continuousAt
  have hAx : ContDiffAt ℝ 1 A (γ t) := hA.contDiffAt (U.isOpen.mem_nhds (γ t).2)
  have hdA : ContinuousAt (fun s => fderiv ℝ A (γ s)) t :=
    ContinuousAt.comp (g := fderiv ℝ A) (f := fun s => (γ s : E))
      (hAx.continuousAt_fderiv one_ne_zero) hx
  have hvel : ContinuousAt (fun s => (curveVelocity γ s : E)) t :=
    (contMDiffAt_tangent_iff.mp
      (curveVelocity_contMDiffAt (n := 0) (hγ.of_le (by norm_num)))).2.continuousAt
  have hXc : ContinuousAt (fun s => (X s : E)) t := (contMDiffAt_tangent_iff.mp hX).2.continuousAt
  exact (((hdA.clm_apply hXc).clm_apply hvel).sub ((hdA.clm_apply hvel).clm_apply hXc)).congr
    (Eventually.of_forall fun s => (fieldCovector_apply A _ _ _).symm)

/-- The pairing of a continuous field with the residual of a charge is continuous. -/
theorem chargedResidual_continuousAt (g : LorentzMetric .timeNegative d U) (m e : ℝ)
    (hA : ContDiffOn ℝ 1 A U) {γ : ℝ → U} {t : ℝ} {X : AlongField (d := d) γ}
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t) (hv : Timelike g (curveVelocity γ t))
    (hX : ContMDiffAt 𝓘(ℝ) ((I).prod I) 0 (fun s => TotalSpace.mk' E (γ s) (X s)) t) :
    ContinuousAt (fun s => g.form (γ s) (X s) (chargedResidual g m e A γ s)) t := by
  have h : ContinuousAt (fun s => -(m / speedAlong g γ s) * g.form (γ s) (X s)
      (g.covariantAlong (curveVelocity γ) s -
        (deriv (speedAlong g γ) s / speedAlong g γ s) • curveVelocity γ s) +
      e * fieldCovector A (γ s) (curveVelocity γ s) (X s)) t :=
    (freeResidual_continuousAt g m hγ hv hX).add
      ((continuousAt_const (y := e)).mul (fieldCovector_continuousAt hA hγ hX))
  simpa only [chargedResidual, map_add, map_smul, smul_eq_mul, form_sharp_model] using h

/-- The first variation of the line integral under an admissible family. -/
theorem lineIntegral_variation_hasDerivAt (hA : ContDiffOn ℝ 1 A U) {γ : ℝ → U} {a b : ℝ}
    (V : ManifoldCurveVariation («E» := E) γ a b) :
    HasDerivAt (fun ε => lineIntegral A (fun t => V.family (ε, t)) a b)
      (∫ t in a..b, fieldCovector A (γ t) (curveVelocity γ t) (variationField V t)) 0 := by
  have href : (fun t => V.family (0, t)) = γ := funext V.reference
  have h := lineIntegral_family_hasDerivAt hA V.regular
    (V.left_fixed.mono fun ε hε => hε.trans (V.reference a).symm)
    (V.right_fixed.mono fun ε hε => hε.trans (V.reference b).symm)
  apply h.congr_deriv
  apply intervalIntegral.integral_congr
  intro t _ht
  dsimp only
  unfold variationField
  rw [href, V.reference t]
  rfl

/-- **The first variation of the action of a charge** is the pairing of the variation field
with the residual `−(m/s)(∇_t γ̇ − (ṡ/s) γ̇) + e F(·, γ̇)^♯`. -/
theorem chargedAction_variation_hasDerivAt (g : LorentzMetric .timeNegative d U) (m e : ℝ)
    (hA : ContDiffOn ℝ 1 A U) {γ : ℝ → U} {a b : ℝ}
    (V : ManifoldCurveVariation («E» := E) γ a b)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : ∀ t ∈ uIcc a b, Timelike g (curveVelocity γ t)) :
    HasDerivAt (fun ε => chargedAction g m e A (fun t => V.family (ε, t)) a b)
      (∫ t in a..b, g.form (γ t) (variationField V t) (chargedResidual g m e A γ t)) 0 := by
  have hJ (t : ℝ) (ht : t ∈ uIcc a b) : ContMDiffAt 𝓘(ℝ) ((I).prod I) 0
      (fun s => TotalSpace.mk' E (γ s) (variationField V s)) t :=
    (variationField_contMDiffAt V ht).of_le (by norm_num)
  have hi₁ : IntervalIntegrable (fun t => -(m / speedAlong g γ t) *
      g.form (γ t) (variationField V t) (g.covariantAlong (curveVelocity γ) t -
        (deriv (speedAlong g γ) t / speedAlong g γ t) • curveVelocity γ t)) volume a b :=
    ContinuousOn.intervalIntegrable fun t ht =>
      (freeResidual_continuousAt g m (hγ t ht) (hv t ht) (hJ t ht)).continuousWithinAt
  have hi₂ : IntervalIntegrable
      (fun t => fieldCovector A (γ t) (curveVelocity γ t) (variationField V t)) volume a b :=
    ContinuousOn.intervalIntegrable fun t ht =>
      (fieldCovector_continuousAt hA (hγ t ht) (hJ t ht)).continuousWithinAt
  refine ((freeAction_variation_hasDerivAt g m V hv).add
    ((lineIntegral_variation_hasDerivAt hA V).const_mul e)).congr_deriv ?_
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hi₁ (hi₂.const_mul e)]
  apply intervalIntegral.integral_congr
  intro t _ht
  simp only [chargedResidual, map_add, map_smul, smul_eq_mul, form_sharp_model]

/-- **The equation of motion of a charge on a curved background**: for a timelike `C²`
curve, the action is stationary under every fixed-endpoint family if and only if
`m ∇_t U = e F(·, γ̇)^♯` with `U = γ̇/s`, written as `(m/s)(∇_t γ̇ − (ṡ/s) γ̇)`. -/
theorem chargedStationary_iff (g : LorentzMetric .timeNegative d U) (m e : ℝ)
    (hA : ContDiffOn ℝ 1 A U) {γ : ℝ → U} {a b : ℝ} (hab : a < b)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : ∀ t ∈ uIcc a b, Timelike g (curveVelocity γ t)) :
    ChargedStationary g m e A γ a b ↔ ∀ t ∈ Ioo a b,
      (m / speedAlong g γ t) • (g.covariantAlong (curveVelocity γ) t -
          (deriv (speedAlong g γ) t / speedAlong g γ t) • curveVelocity γ t) =
        e • g.sharp (γ t) (fieldCovector A (γ t) (curveVelocity γ t)) := by
  have hinc : Ioo a b ⊆ uIcc a b := by
    rw [uIcc_of_le hab.le]
    exact Ioo_subset_Icc_self
  have hres (t : ℝ) : chargedResidual g m e A γ t = 0 ↔
      (m / speedAlong g γ t) • (g.covariantAlong (curveVelocity γ) t -
          (deriv (speedAlong g γ) t / speedAlong g γ t) • curveVelocity γ t) =
        e • g.sharp (γ t) (fieldCovector A (γ t) (curveVelocity γ t)) := by
    rw [chargedResidual, neg_smul, neg_add_eq_zero]
  constructor
  · intro hs t ht
    have hz := g.eq_zero_of_variation_pairing hab hγ (chargedResidual g m e A γ)
      (fun c hc w s hs hx => ?_) (fun V => ?_)
    · exact (hres t).mp (hz t ht)
    · exact chargedResidual_continuousAt g m e hA (hγ s (hinc hs)) (hv s (hinc hs))
        (((chartField_contMDiffAt hc hx w).of_le (by simp)).comp s
          ((hγ s (hinc hs)).of_le (by norm_num)))
    · exact (chargedAction_variation_hasDerivAt g m e hA V hγ hv).unique (hs V)
  · intro h V
    apply (chargedAction_variation_hasDerivAt g m e hA V hγ hv).congr_deriv
    calc
      _ = ∫ _t in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hab.le
        intro t ht
        simp only [(hres t).mpr (h t ht), map_zero]
      _ = 0 := by simp

/-! ### Gauge invariance -/

/-- A gauge change `A ↦ A + dχ` does not change the field. -/
theorem fieldCovector_gauge {χ : MinkowskiModel d → ℝ} {z : MinkowskiModel d}
    (hA : DifferentiableAt ℝ A z) (hχ : ContDiffAt ℝ 2 χ z) (v : MinkowskiModel d) :
    fieldCovector (fun y => A y + fderiv ℝ χ y) z v = fieldCovector A z v := by
  have hd : fderiv ℝ (fun y => A y + fderiv ℝ χ y) z = fderiv ℝ A z + fderiv ℝ (fderiv ℝ χ) z :=
    fderiv_add hA ((hχ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have hsym := hχ.isSymmSndFDerivAt (by norm_num)
  ext w
  rw [fieldCovector_apply, fieldCovector_apply, hd, add_apply, add_apply, add_apply, add_apply,
    hsym.eq w v]
  ring

/-- **The end-point term of a gauge change**: `∫ (A + dχ)(γ̇) dt = ∫ A(γ̇) dt + χ(γ(b)) − χ(γ(a))`
along a `C¹` curve in `U`. -/
theorem lineIntegral_gauge {χ : MinkowskiModel d → ℝ} (hA : ContinuousOn A U)
    (hχ : ContDiffOn ℝ 1 χ U) {γ : ℝ → U} {a b : ℝ}
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 1 γ t) :
    lineIntegral (fun y => A y + fderiv ℝ χ y) γ a b =
      lineIntegral A γ a b + (χ (γ b) - χ (γ a)) := by
  have hx (t : ℝ) (ht : t ∈ uIcc a b) : ContinuousAt (fun s => (γ s : E)) t :=
    (contDiffAt_val (hγ t ht)).continuousAt
  have hvel (t : ℝ) (ht : t ∈ uIcc a b) : ContinuousAt (fun s => (curveVelocity γ s : E)) t :=
    (contMDiffAt_tangent_iff.mp (curveVelocity_contMDiffAt (n := 0) (hγ t ht))).2.continuousAt
  have hAc (t : ℝ) (ht : t ∈ uIcc a b) : ContinuousAt (fun s => A (γ s)) t :=
    ContinuousAt.comp (g := A) (f := fun s => (γ s : E))
      (hA.continuousAt (U.isOpen.mem_nhds (γ t).2)) (hx t ht)
  have hdχ (t : ℝ) (ht : t ∈ uIcc a b) : ContinuousAt (fun s => fderiv ℝ χ (γ s)) t :=
    ContinuousAt.comp (g := fderiv ℝ χ) (f := fun s => (γ s : E))
      ((hχ.contDiffAt (U.isOpen.mem_nhds (γ t).2)).continuousAt_fderiv one_ne_zero) (hx t ht)
  have hi₁ : IntervalIntegrable (fun t => A (γ t) (curveVelocity γ t)) volume a b :=
    ContinuousOn.intervalIntegrable fun t ht =>
      ((hAc t ht).clm_apply (hvel t ht)).continuousWithinAt
  have hi₂ : IntervalIntegrable (fun t => fderiv ℝ χ (γ t) (curveVelocity γ t)) volume a b :=
    ContinuousOn.intervalIntegrable fun t ht =>
      ((hdχ t ht).clm_apply (hvel t ht)).continuousWithinAt
  have hderiv : ∀ t ∈ uIcc a b, HasDerivAt (fun s => χ (γ s))
      (fderiv ℝ χ (γ t) (curveVelocity γ t)) t := by
    intro t ht
    have hγd : HasDerivAt (fun s => (γ s : E)) (curveVelocity γ t) t := by
      rw [curveVelocity_val ((hγ t ht).mdifferentiableAt one_ne_zero)]
      exact ((contDiffAt_val (hγ t ht)).differentiableAt one_ne_zero).hasDerivAt
    exact ((hχ.contDiffAt (U.isOpen.mem_nhds (γ t).2)).differentiableAt
      one_ne_zero).hasFDerivAt.comp_hasDerivAt t hγd
  unfold lineIntegral
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hi₂,
    ← intervalIntegral.integral_add hi₁ hi₂]
  rfl

/-- **Gauge invariance of the equation of motion**: for a `C²` gauge function the potentials
`A` and `A + dχ` have the same stationary curves. -/
theorem chargedStationary_gauge_iff (g : LorentzMetric .timeNegative d U) (m e : ℝ)
    (hA : ContDiffOn ℝ 1 A U) {χ : MinkowskiModel d → ℝ} (hχ : ContDiffOn ℝ 2 χ U)
    {γ : ℝ → U} {a b : ℝ} (hab : a < b)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : ∀ t ∈ uIcc a b, Timelike g (curveVelocity γ t)) :
    ChargedStationary g m e (fun y => A y + fderiv ℝ χ y) γ a b ↔
      ChargedStationary g m e A γ a b := by
  have hA' : ContDiffOn ℝ 1 (fun y => A y + fderiv ℝ χ y) U :=
    hA.add (hχ.fderiv_of_isOpen U.isOpen (by norm_num))
  rw [chargedStationary_iff g m e hA' hab hγ hv, chargedStationary_iff g m e hA hab hγ hv]
  refine forall₂_congr fun t _ => ?_
  have hn : (U : Set E) ∈ 𝓝 (γ t : E) := U.isOpen.mem_nhds (γ t).2
  rw [fieldCovector_gauge ((hA.contDiffAt hn).differentiableAt one_ne_zero)
    (hχ.contDiffAt hn) (curveVelocity γ t)]

end ProjectAinos.GeneralRelativity
