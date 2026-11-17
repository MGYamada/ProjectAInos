/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialRelativity.FreeMotion
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The action with an auxiliary field, and the massless particle

The action `−m ∫ ds` has no meaning for `m = 0`. With an auxiliary positive function `e` of the
parameter, the action is

`S[x, e] = ½ ∫ (−Q(ẋ)/e − e m²) ds`,

where `Q(ẋ) = −g(ẋ, ẋ)` for `(−+++)`. Its Lagrangian `Einbein.lagrangian d m` is a function on
the configurations `(x, e)` in `MinkowskiModel d × ℝ`, smooth where `e > 0`, in `d` space
dimensions.

* `stationary_iff`: for `C²` functions `x` and `e` with `e > 0` on `[a, b]`, the action is
  stationary if and only if, on `(a, b)`, `Q(ẋ) = e² m²` and the derivative of `ẋ/e` is zero.
* **Positive mass.** `lagrangian_eliminate`: with `e = √Q(ẋ)/m` the Lagrangian is
  `−m √Q(ẋ)`, the Lagrangian of the action `−m ∫ ds`. `timelike_of_stationary` shows that the
  velocity of a stationary curve is timelike, and `fourVelocity_eq_of_stationary` that its unit
  four-velocity is constant; in three space dimensions the curve is then stationary for the
  action `−m ∫ ds` (`free_stationary_of_stationary`).
* **Mass zero.** `stationary_massless_iff`: the action is stationary if and only if the velocity
  is null and `ẋ/e` has zero derivative; then `ẋ = e k` on `[a, b]` with a constant null vector
  `k` (`deriv_eq_smul_of_stationary_massless`). No null vector is divided by its proper length.
* **The parameter.** `lagrangian_reparametrize` and `action_reparametrize`: under an increasing
  change `f` of the parameter, with `e` replaced by `(e ∘ f) f′`, the action is unchanged.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Topology
open scoped ContDiff

namespace ProjectAinos.SpecialRelativity.Einbein

open SmoothGeometry SmoothGeometry.Minkowski Mechanics

variable {d : ℕ} {m : ℝ}

/-- The Lagrangian `½ (−Q(ẋ)/e − e m²)` of the configurations `(x, e)`. -/
def lagrangian (d : ℕ) (m : ℝ) : Lagrangian (MinkowskiModel d × ℝ) :=
  fun _ z => 1 / 2 * (-(z.1.2)⁻¹ * intervalQuadratic z.2.1 - z.1.2 * m ^ 2)

/-- The jets with a positive auxiliary field. -/
def positiveJets (d : ℕ) :
    Set (ℝ × ((MinkowskiModel d × ℝ) × (MinkowskiModel d × ℝ))) :=
  {z | 0 < z.2.1.2}

theorem isOpen_positiveJets : IsOpen (positiveJets d) :=
  isOpen_lt continuous_const (continuous_snd.comp (continuous_fst.comp continuous_snd))

theorem contDiff_intervalQuadratic {n : ℕ∞ω} :
    ContDiff ℝ n (intervalQuadratic : MinkowskiModel d → ℝ) :=
  pair.contDiff.clm_apply contDiff_id

theorem hasFDerivAt_intervalQuadratic (v : MinkowskiModel d) :
    HasFDerivAt (intervalQuadratic : MinkowskiModel d → ℝ) ((2 : ℝ) • pair v) v := by
  have h := (pair.hasFDerivAt (x := v)).clm_apply (hasFDerivAt_id v)
  have he : (pair v).comp (ContinuousLinearMap.id ℝ (MinkowskiModel d)) + pair.flip v =
      (2 : ℝ) • pair v := by
    ext w
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.flip_apply, smul_apply, smul_eq_mul]
    rw [Minkowski.pair_comm w v]
    ring
  simp only [id_eq] at h
  rw [he] at h
  exact h

theorem lagrangian_contDiffOn (m : ℝ) :
    ContDiffOn ℝ 2 (Function.uncurry (lagrangian d m)) (positiveJets d) := by
  intro z hz
  have he : ContDiffAt ℝ 2
      (fun z : ℝ × ((MinkowskiModel d × ℝ) × (MinkowskiModel d × ℝ)) => z.2.1.2) z :=
    (contDiff_snd.comp (contDiff_fst.comp contDiff_snd)).contDiffAt
  have hv : ContDiffAt ℝ 2
      (fun z : ℝ × ((MinkowskiModel d × ℝ) × (MinkowskiModel d × ℝ)) =>
        intervalQuadratic z.2.2.1) z :=
    (contDiff_intervalQuadratic.comp
      (contDiff_fst.comp (contDiff_snd.comp contDiff_snd))).contDiffAt
  have hne : z.2.1.2 ≠ 0 := ne_of_gt hz
  exact (contDiffAt_const.mul (((he.inv hne).neg.mul hv).sub
    (he.mul contDiffAt_const))).contDiffWithinAt

/-- The linear map that takes the variation of `e` out of a variation of the jet. -/
def eComponent (d : ℕ) :
    ((MinkowskiModel d × ℝ) × (MinkowskiModel d × ℝ)) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ (MinkowskiModel d) ℝ).comp
    (ContinuousLinearMap.fst ℝ (MinkowskiModel d × ℝ) (MinkowskiModel d × ℝ))

/-- The linear map that takes the variation of the velocity out of a variation of the jet. -/
def vComponent (d : ℕ) :
    ((MinkowskiModel d × ℝ) × (MinkowskiModel d × ℝ)) →L[ℝ] MinkowskiModel d :=
  (ContinuousLinearMap.fst ℝ (MinkowskiModel d) ℝ).comp
    (ContinuousLinearMap.snd ℝ (MinkowskiModel d × ℝ) (MinkowskiModel d × ℝ))

/-- The derivative of the Lagrangian:
`½ (Q(v)/e² − m²) δe − (1/e) ⟨v, δv⟩`. -/
theorem hasFDerivAt_lagrangian (m : ℝ)
    {z : (MinkowskiModel d × ℝ) × (MinkowskiModel d × ℝ)} (hz : z.1.2 ≠ 0) (t : ℝ) :
    HasFDerivAt (lagrangian d m t)
      ((1 / 2 * ((z.1.2 ^ 2)⁻¹ * intervalQuadratic z.2.1 - m ^ 2)) • eComponent d -
        (z.1.2)⁻¹ • (pair z.2.1).comp (vComponent d)) z := by
  have he : HasFDerivAt (fun z : (MinkowskiModel d × ℝ) × (MinkowskiModel d × ℝ) => z.1.2)
      (eComponent d) z := (eComponent d).hasFDerivAt
  have hv : HasFDerivAt (fun z : (MinkowskiModel d × ℝ) × (MinkowskiModel d × ℝ) => z.2.1)
      (vComponent d) z := (vComponent d).hasFDerivAt
  have hQ := (hasFDerivAt_intervalQuadratic z.2.1).comp z hv
  have hinv := (hasDerivAt_inv hz).comp_hasFDerivAt z he
  have h := ((hinv.neg.mul hQ).sub (he.mul_const (m ^ 2))).const_mul (1 / 2 : ℝ)
  refine h.congr_fderiv (ContinuousLinearMap.ext fun δ => ?_)
  simp only [smul_apply, sub_apply, add_apply, neg_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul, Function.comp_apply, Pi.neg_apply]
  ring

variable {x : ℝ → MinkowskiModel d} {e : ℝ → ℝ} {a b : ℝ}

theorem hasDerivAt_path (hx : ContDiff ℝ 2 x) (he : ContDiff ℝ 2 e) (t : ℝ) :
    HasDerivAt (fun s => (x s, e s)) (deriv x t, deriv e t) t :=
  ((hx.differentiable (by norm_num) t).hasDerivAt).prodMk
    ((he.differentiable (by norm_num) t).hasDerivAt)

theorem deriv_path (hx : ContDiff ℝ 2 x) (he : ContDiff ℝ 2 e) (t : ℝ) :
    deriv (fun s => (x s, e s)) t = (deriv x t, deriv e t) :=
  (hasDerivAt_path hx he t).deriv

/-- The covector `δ ↦ ⟨w, δx⟩` of a configuration, as a linear function of `w`. -/
def positionCovector (d : ℕ) :
    MinkowskiModel d →L[ℝ] ((MinkowskiModel d × ℝ) →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ (MinkowskiModel d × ℝ) (MinkowskiModel d) ℝ).flip
    (ContinuousLinearMap.fst ℝ (MinkowskiModel d) ℝ)).comp pair

theorem positionCovector_apply (w δx : MinkowskiModel d) (δe : ℝ) :
    positionCovector d w (δx, δe) = pair w δx := rfl

theorem positionCovector_eq_zero_iff (w : MinkowskiModel d) :
    positionCovector d w = 0 ↔ w = 0 := by
  constructor
  · intro h
    refine minkowskiForm_nondegenerate .timePositive w fun z => ?_
    have hz := congrArg (fun L : (MinkowskiModel d × ℝ) →L[ℝ] ℝ => L (z, 0)) h
    exact hz
  · rintro rfl
    exact map_zero _

/-- The force of the Lagrangian along a path: the derivative in `e`. -/
theorem force_lagrangian (m : ℝ) (hx : ContDiff ℝ 2 x) (he : ContDiff ℝ 2 e) {t : ℝ}
    (ht : e t ≠ 0) :
    force (lagrangian d m) (fun s => (x s, e s)) t =
      (1 / 2 * ((e t ^ 2)⁻¹ * intervalQuadratic (deriv x t) - m ^ 2)) •
        ContinuousLinearMap.snd ℝ (MinkowskiModel d) ℝ := by
  rw [force, deriv_path hx he,
    (hasFDerivAt_lagrangian m (z := ((x t, e t), (deriv x t, deriv e t))) ht t).fderiv]
  ext δ
  · simp [eComponent, vComponent]
  · simp [eComponent, vComponent]

/-- The momentum of the Lagrangian along a path: `−ẋ♭/e`. -/
theorem momentum_lagrangian (m : ℝ) (hx : ContDiff ℝ 2 x) (he : ContDiff ℝ 2 e) {t : ℝ}
    (ht : e t ≠ 0) :
    momentum (lagrangian d m) (fun s => (x s, e s)) t =
      -positionCovector d ((e t)⁻¹ • deriv x t) := by
  rw [momentum, deriv_path hx he,
    (hasFDerivAt_lagrangian m (z := ((x t, e t), (deriv x t, deriv e t))) ht t).fderiv]
  ext δ
  · simp [eComponent, vComponent, positionCovector_apply]
  · simp [eComponent, vComponent, positionCovector_apply]

theorem differentiableAt_inv_smul_deriv (hx : ContDiff ℝ 2 x) (he : ContDiff ℝ 2 e) {t : ℝ}
    (ht : e t ≠ 0) : DifferentiableAt ℝ (fun s => (e s)⁻¹ • deriv x s) t :=
  ((he.differentiable (by norm_num) t).inv ht).smul (hx.differentiable_deriv_two t)

/-- The Euler–Lagrange covector along a path with `e ≠ 0`. -/
theorem eulerLagrange_lagrangian (m : ℝ) (hx : ContDiff ℝ 2 x) (he : ContDiff ℝ 2 e) {t : ℝ}
    (ht : e t ≠ 0) :
    eulerLagrange (lagrangian d m) (fun s => (x s, e s)) t =
      (1 / 2 * ((e t ^ 2)⁻¹ * intervalQuadratic (deriv x t) - m ^ 2)) •
          ContinuousLinearMap.snd ℝ (MinkowskiModel d) ℝ +
        positionCovector d (deriv (fun s => (e s)⁻¹ • deriv x s) t) := by
  have hnear : ∀ᶠ s in 𝓝 t, e s ≠ 0 :=
    (he.continuous.continuousAt).eventually (isOpen_ne.mem_nhds ht)
  have hmom : momentum (lagrangian d m) (fun s => (x s, e s)) =ᶠ[𝓝 t]
      fun s => -positionCovector d ((e s)⁻¹ • deriv x s) :=
    hnear.mono fun s hs => momentum_lagrangian m hx he hs
  have hd : HasDerivAt (fun s => -positionCovector d ((e s)⁻¹ • deriv x s))
      (-positionCovector d (deriv (fun s => (e s)⁻¹ • deriv x s) t)) t :=
    ((positionCovector d).hasFDerivAt.comp_hasDerivAt t
      (differentiableAt_inv_smul_deriv hx he ht).hasDerivAt).neg
  rw [eulerLagrange, force_lagrangian m hx he ht, hmom.deriv_eq, hd.deriv, sub_neg_eq_add]

/-- The equations of the action with an auxiliary field: the action is stationary if and only
if `Q(ẋ) = e² m²` and `ẋ/e` has zero derivative on `(a, b)`. -/
theorem stationary_iff (m : ℝ) (hab : a < b) (hx : ContDiff ℝ 2 x) (he : ContDiff ℝ 2 e)
    (hpos : ∀ t ∈ Icc a b, 0 < e t) :
    Stationary a b (lagrangian d m) (fun s => (x s, e s)) ↔
      ∀ t ∈ Ioo a b, intervalQuadratic (deriv x t) = e t ^ 2 * m ^ 2 ∧
        deriv (fun s => (e s)⁻¹ • deriv x s) t = 0 := by
  rw [stationary_iff_eulerLagrange_on hab (hx.prodMk he) isOpen_positiveJets
    (lagrangian_contDiffOn m) fun t ht => hpos t ht]
  refine forall₂_congr fun t ht => ?_
  have hpt : 0 < e t := hpos t (Ioo_subset_Icc_self ht)
  rw [eulerLagrange_lagrangian m hx he hpt.ne']
  constructor
  · intro h
    have h1 := congrArg (fun L : (MinkowskiModel d × ℝ) →L[ℝ] ℝ => L (0, 1)) h
    simp only [add_apply, smul_apply, ContinuousLinearMap.coe_snd', smul_eq_mul, mul_one,
      positionCovector_apply, map_zero, add_zero, zero_apply] at h1
    have hQ : intervalQuadratic (deriv x t) = e t ^ 2 * m ^ 2 := by
      have h2 : (e t ^ 2)⁻¹ * intervalQuadratic (deriv x t) = m ^ 2 := by linarith
      have hne : e t ^ 2 ≠ 0 := pow_ne_zero 2 hpt.ne'
      field_simp at h2
      linarith
    refine ⟨hQ, ?_⟩
    have hcoef : 1 / 2 * ((e t ^ 2)⁻¹ * intervalQuadratic (deriv x t) - m ^ 2) = 0 := by
      linarith
    rw [hcoef, zero_smul, zero_add] at h
    exact (positionCovector_eq_zero_iff _).mp h
  · rintro ⟨hQ, hd⟩
    have hne : e t ^ 2 ≠ 0 := pow_ne_zero 2 hpt.ne'
    have hcoef : 1 / 2 * ((e t ^ 2)⁻¹ * intervalQuadratic (deriv x t) - m ^ 2) = 0 := by
      rw [hQ]
      field_simp
      ring
    rw [hcoef, hd, zero_smul, map_zero, add_zero]

/-! ### The equations on the closed interval -/

/-- On a stationary pair the relation `Q(ẋ) = e² m²` holds on the closed interval. -/
theorem intervalQuadratic_deriv_eq_of_stationary (hab : a < b) (hx : ContDiff ℝ 2 x)
    (he : ContDiff ℝ 2 e) (hpos : ∀ t ∈ Icc a b, 0 < e t)
    (h : Stationary a b (lagrangian d m) (fun s => (x s, e s))) {t : ℝ} (ht : t ∈ Icc a b) :
    intervalQuadratic (deriv x t) = e t ^ 2 * m ^ 2 := by
  have hIoo : EqOn (fun s => intervalQuadratic (deriv x s)) (fun s => e s ^ 2 * m ^ 2)
      (Ioo a b) := fun s hs => (((stationary_iff m hab hx he hpos).mp h) s hs).1
  have hc1 : Continuous fun s => intervalQuadratic (deriv x s) :=
    (contDiff_intervalQuadratic (n := 0)).continuous.comp (hx.continuous_deriv (by norm_num))
  have hc2 : Continuous fun s => e s ^ 2 * m ^ 2 := (he.continuous.pow 2).mul continuous_const
  exact hIoo.of_subset_closure hc1.continuousOn hc2.continuousOn Ioo_subset_Icc_self
    (closure_Ioo hab.ne).ge ht

/-- On a stationary pair `ẋ/e` is constant on the closed interval. -/
theorem inv_smul_deriv_eq_of_stationary (hab : a < b) (hx : ContDiff ℝ 2 x)
    (he : ContDiff ℝ 2 e) (hpos : ∀ t ∈ Icc a b, 0 < e t)
    (h : Stationary a b (lagrangian d m) (fun s => (x s, e s))) {t : ℝ} (ht : t ∈ Icc a b) :
    (e t)⁻¹ • deriv x t = (e a)⁻¹ • deriv x a := by
  refine eq_of_hasDerivAt_zero_Ioo (f := fun s => (e s)⁻¹ • deriv x s)
    (fun s hs => (differentiableAt_inv_smul_deriv hx he (hpos s hs).ne').continuousAt
      |>.continuousWithinAt) (fun s hs => ?_) ht
  have hd := (differentiableAt_inv_smul_deriv hx he
    (hpos s (Ioo_subset_Icc_self hs)).ne').hasDerivAt
  rwa [(((stationary_iff m hab hx he hpos).mp h) s hs).2] at hd

/-! ### Positive mass -/

/-- With `e = √Q(v)/m` the Lagrangian is `−m √Q(v)`, the Lagrangian of the action `−m ∫ ds`. -/
theorem lagrangian_eliminate (hm : 0 < m) {v : MinkowskiModel d} (hv : Timelike v) (t : ℝ)
    (y : MinkowskiModel d) (w : ℝ) :
    lagrangian d m t ((y, properSpeed v / m), (v, w)) = -m * properSpeed v := by
  have hpos : 0 < properSpeed v := Real.sqrt_pos.mpr hv
  have hQ : intervalQuadratic v = properSpeed v ^ 2 := (Real.sq_sqrt hv.le).symm
  simp only [lagrangian]
  rw [hQ]
  field_simp
  ring

/-- For a nonzero mass the velocity of a stationary curve is timelike. -/
theorem timelike_of_stationary (hm : m ≠ 0) (hab : a < b) (hx : ContDiff ℝ 2 x)
    (he : ContDiff ℝ 2 e) (hpos : ∀ t ∈ Icc a b, 0 < e t)
    (h : Stationary a b (lagrangian d m) (fun s => (x s, e s))) {t : ℝ} (ht : t ∈ Icc a b) :
    Timelike (deriv x t) := by
  change 0 < intervalQuadratic (deriv x t)
  rw [intervalQuadratic_deriv_eq_of_stationary hab hx he hpos h ht]
  exact mul_pos (pow_pos (hpos t ht) 2) (by positivity)

/-- For a positive mass the auxiliary field of a stationary pair is `√Q(ẋ)/m`. -/
theorem properSpeed_deriv_eq_of_stationary (hm : 0 < m) (hab : a < b) (hx : ContDiff ℝ 2 x)
    (he : ContDiff ℝ 2 e) (hpos : ∀ t ∈ Icc a b, 0 < e t)
    (h : Stationary a b (lagrangian d m) (fun s => (x s, e s))) {t : ℝ} (ht : t ∈ Icc a b) :
    properSpeed (deriv x t) = e t * m := by
  rw [properSpeed, intervalQuadratic_deriv_eq_of_stationary hab hx he hpos h ht, ← mul_pow,
    Real.sqrt_sq (mul_pos (hpos t ht) hm).le]

/-- For a positive mass the unit four-velocity of a stationary curve is constant. -/
theorem fourVelocity_eq_of_stationary (hm : 0 < m) (hab : a < b) (hx : ContDiff ℝ 2 x)
    (he : ContDiff ℝ 2 e) (hpos : ∀ t ∈ Icc a b, 0 < e t)
    (h : Stationary a b (lagrangian d m) (fun s => (x s, e s))) {t : ℝ} (ht : t ∈ Icc a b) :
    fourVelocity (deriv x t) = fourVelocity (deriv x a) := by
  have h1 := properSpeed_deriv_eq_of_stationary hm hab hx he hpos h ht
  have h2 := properSpeed_deriv_eq_of_stationary hm hab hx he hpos h (left_mem_Icc.mpr hab.le)
  have h3 := inv_smul_deriv_eq_of_stationary hab hx he hpos h ht
  have hsplit (s : ℝ) : (e s * m)⁻¹ • deriv x s = m⁻¹ • ((e s)⁻¹ • deriv x s) := by
    rw [smul_smul, mul_inv, mul_comm]
  rw [fourVelocity, fourVelocity, h1, h2, hsplit t, hsplit a, h3]

/-- In three space dimensions a stationary curve of the action with an auxiliary field and a
positive mass is stationary for the action `−m ∫ ds`. -/
theorem free_stationary_of_stationary (hm : 0 < m) (hab : a < b) {x : ℝ → Spacetime}
    (hx : ContDiff ℝ 2 x) (he : ContDiff ℝ 2 e) (hpos : ∀ t ∈ Icc a b, 0 < e t)
    (h : Stationary a b (lagrangian 3 m) (fun s => (x s, e s))) :
    Stationary a b (freeLagrangian m) x :=
  (free_stationary_iff_fourVelocity_const hm.ne' hab hx fun _ ht =>
    timelike_of_stationary hm.ne' hab hx he hpos h ht).mpr fun _ ht =>
      fourVelocity_eq_of_stationary hm hab hx he hpos h ht

/-- Conversely, a stationary curve of the action `−m ∫ ds` with the auxiliary field
`e = √Q(ẋ)/m` is stationary for the action with an auxiliary field. -/
theorem stationary_of_free_stationary (hm : 0 < m) (hab : a < b) {x : ℝ → Spacetime}
    (hx : ContDiff ℝ 2 x) (he : ContDiff ℝ 2 e) (hv : ∀ t ∈ Icc a b, Timelike (deriv x t))
    (hrel : ∀ t ∈ Icc a b, e t = properSpeed (deriv x t) / m)
    (h : Stationary a b (freeLagrangian m) x) :
    Stationary a b (lagrangian 3 m) (fun s => (x s, e s)) := by
  have hpos : ∀ t ∈ Icc a b, 0 < e t := fun t ht => by
    rw [hrel t ht]
    exact div_pos (Real.sqrt_pos.mpr (hv t ht)) hm
  have hU := (free_stationary_iff_fourVelocity_const hm.ne' hab hx hv).mp h
  rw [stationary_iff m hab hx he hpos]
  intro t ht
  have ht' := Ioo_subset_Icc_self ht
  refine ⟨?_, ?_⟩
  · rw [hrel t ht', div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hm.ne')]
    exact (Real.sq_sqrt (hv t ht').le).symm
  · have hconst : ∀ s ∈ Icc a b, (e s)⁻¹ • deriv x s = m • fourVelocity (deriv x a) := by
      intro s hs
      rw [← hU s hs, fourVelocity, smul_smul, hrel s hs, inv_div, div_eq_mul_inv]
    have heq : (fun s => (e s)⁻¹ • deriv x s) =ᶠ[𝓝 t] fun _ => m • fourVelocity (deriv x a) :=
      Filter.eventuallyEq_of_mem (Icc_mem_nhds ht.1 ht.2) hconst
    rw [heq.deriv_eq, deriv_const]

/-! ### Mass zero -/

/-- For the mass zero the action is stationary if and only if the velocity is null and `ẋ/e`
has zero derivative. -/
theorem stationary_massless_iff (hab : a < b) (hx : ContDiff ℝ 2 x) (he : ContDiff ℝ 2 e)
    (hpos : ∀ t ∈ Icc a b, 0 < e t) :
    Stationary a b (lagrangian d 0) (fun s => (x s, e s)) ↔
      ∀ t ∈ Ioo a b, intervalQuadratic (deriv x t) = 0 ∧
        deriv (fun s => (e s)⁻¹ • deriv x s) t = 0 := by
  rw [stationary_iff 0 hab hx he hpos]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]

/-- A stationary curve of mass zero moves along a constant null vector: `ẋ = e k` on `[a, b]`
with `Q(k) = 0`. -/
theorem deriv_eq_smul_of_stationary_massless (hab : a < b) (hx : ContDiff ℝ 2 x)
    (he : ContDiff ℝ 2 e) (hpos : ∀ t ∈ Icc a b, 0 < e t)
    (h : Stationary a b (lagrangian d 0) (fun s => (x s, e s))) :
    intervalQuadratic ((e a)⁻¹ • deriv x a) = 0 ∧
      ∀ t ∈ Icc a b, deriv x t = e t • ((e a)⁻¹ • deriv x a) := by
  refine ⟨?_, fun t ht => ?_⟩
  · have hQ := intervalQuadratic_deriv_eq_of_stationary hab hx he hpos h
      (left_mem_Icc.mpr hab.le)
    rw [QuadraticMap.map_smul, hQ]
    simp
  · rw [← inv_smul_deriv_eq_of_stationary hab hx he hpos h ht, smul_smul,
      mul_inv_cancel₀ (hpos t ht).ne', one_smul]

/-! ### The parameter -/

/-- The Lagrangian under a change of the parameter: with the velocity multiplied by `c` and the
auxiliary field multiplied by `c`, the Lagrangian is multiplied by `c`. -/
theorem lagrangian_reparametrize (m : ℝ) {c ε : ℝ} (hc : c ≠ 0) (hε : ε ≠ 0) (s t : ℝ)
    (y y' v : MinkowskiModel d) (w w' : ℝ) :
    lagrangian d m s ((y, ε * c), (c • v, w)) = c * lagrangian d m t ((y', ε), (v, w')) := by
  simp only [lagrangian, QuadraticMap.map_smul, smul_eq_mul]
  field_simp

/-- The action does not depend on the parameter: for a change `f` of the parameter with a
nonzero derivative, the pair `(x ∘ f, (e ∘ f) f′)` has the action of `(x, e)` between the
corresponding ends. -/
theorem action_reparametrize (m : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hx : ContDiff ℝ 2 x)
    (he : ContDiff ℝ 2 e) (hfne : ∀ s ∈ uIcc a b, deriv f s ≠ 0)
    (hene : ∀ s ∈ uIcc a b, e (f s) ≠ 0) :
    action a b (lagrangian d m) (fun s => (x (f s), e (f s) * deriv f s)) =
      action (f a) (f b) (lagrangian d m) (fun t => (x t, e t)) := by
  have hRHS : action (f a) (f b) (lagrangian d m) (fun t => (x t, e t)) =
      ∫ t in f a..f b, lagrangian d m t ((x t, e t), (deriv x t, deriv e t)) := by
    unfold action
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [deriv_path hx he]
  have hLHS : action a b (lagrangian d m) (fun s => (x (f s), e (f s) * deriv f s)) =
      ∫ s in a..b, ((fun t => lagrangian d m t ((x t, e t), (deriv x t, deriv e t))) ∘ f) s *
        deriv f s := by
    unfold action
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hdx : HasDerivAt (fun s => x (f s)) (deriv f s • deriv x (f s)) s :=
      ((hx.differentiable (by norm_num) (f s)).hasDerivAt).scomp s
        ((hf.differentiable (by norm_num) s).hasDerivAt)
    have hde : DifferentiableAt ℝ (fun s => e (f s) * deriv f s) s :=
      ((he.differentiable (by norm_num) (f s)).comp s (hf.differentiable (by norm_num) s)).mul
        (hf.differentiable_deriv_two s)
    have hpair : HasDerivAt (fun s => (x (f s), e (f s) * deriv f s))
        (deriv f s • deriv x (f s), deriv (fun s => e (f s) * deriv f s) s) s :=
      hdx.prodMk hde.hasDerivAt
    have hpath := hpair.deriv
    change lagrangian d m s ((x (f s), e (f s) * deriv f s),
      deriv (fun s => (x (f s), e (f s) * deriv f s)) s) =
      lagrangian d m (f s) ((x (f s), e (f s)), (deriv x (f s), deriv e (f s))) * deriv f s
    rw [hpath]
    exact (lagrangian_reparametrize m (hfne s hs) (hene s hs) s (f s) (x (f s)) (x (f s))
      (deriv x (f s)) _ (deriv e (f s))).trans (mul_comm _ _)
  rw [hLHS, hRHS]
  refine intervalIntegral.integral_comp_mul_deriv'
    (fun s _ => (hf.differentiable (by norm_num) s).hasDerivAt)
    (hf.continuous_deriv (by norm_num)).continuousOn ?_
  rintro _ ⟨s, hs, rfl⟩
  have h1 : ContinuousAt (fun t => (e t)⁻¹) (f s) :=
    he.continuous.continuousAt.inv₀ (hene s hs)
  have h2 : Continuous fun t => intervalQuadratic (deriv x t) :=
    (contDiff_intervalQuadratic (n := 0)).continuous.comp (hx.continuous_deriv (by norm_num))
  exact (continuousAt_const.mul ((h1.neg.mul h2.continuousAt).sub
    (he.continuous.continuousAt.mul continuousAt_const))).continuousWithinAt

end ProjectAinos.SpecialRelativity.Einbein
