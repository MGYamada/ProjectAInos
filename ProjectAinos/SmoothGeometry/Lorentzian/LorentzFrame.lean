/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Minkowski.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Real
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# A criterion for the signature of a symmetric bilinear form

On the model space `MinkowskiModel d = Fin (d + 1) → ℝ`, a symmetric bilinear form `B` that is
negative on the time axis `e₀` and positive definite on the space `{(0, v)}` has a frame in which
it is the Minkowski form of the convention `.timeNegative` (`exists_lorentzFrame`). The proof
completes the square along `e₀`.

`exists_lorentzFrame_convention` is the statement for either convention: for `.timePositive`
the hypotheses are on `−B`.
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap

namespace ProjectAinos.SmoothGeometry.Minkowski

variable {d : ℕ}

/-- A positive definite quadratic form on `ℝᵈ` is a sum of squares of linear co-ordinates. -/
theorem exists_linearEquiv_sum_sq (Q : QuadraticForm ℝ (Fin d → ℝ))
    (hQ : ∀ v ≠ 0, 0 < Q v) :
    ∃ e : (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ), ∀ v, Q v = ∑ i, (e v i) ^ 2 := by
  obtain ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares
  have hdim : Module.finrank ℝ (Fin d → ℝ) = d := Module.finrank_fin_fun ℝ
  revert w e
  rw [hdim]
  intro w e
  have hw (i : Fin d) : 0 < w i := by
    let v : Fin d → ℝ := Pi.single i 1
    have hv : v ≠ 0 := by
      intro h
      have h' := congrFun h i
      simp [v] at h'
    have hp := hQ (e.symm v) (by
      intro hz
      exact hv (by simpa using congrArg e hz))
    rw [← e.map_app, e.apply_symm_apply, QuadraticMap.weightedSumSquares_apply] at hp
    simpa [v, Pi.single_apply, ite_pow, Finset.sum_ite_eq', mul_comm] using hp
  let r := QuadraticForm.isometryEquivSignWeightedSumSquares w
  refine ⟨(e.trans r).toLinearEquiv, fun v => ?_⟩
  rw [← (e.trans r).map_app, QuadraticMap.weightedSumSquares_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [sign_pos (hw i), smul_eq_mul, pow_two]

/-- A symmetric bilinear form that is negative on the time axis and positive definite on the
space has a Lorentz frame for the convention `.timeNegative`. -/
theorem exists_lorentzFrame (B : MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)
    (hs : ∀ v w, B v w = B w v)
    (ht : B (Fin.cons 1 (0 : Fin d → ℝ)) (Fin.cons 1 (0 : Fin d → ℝ)) < 0)
    (hx : ∀ v : Fin d → ℝ, v ≠ 0 → 0 < B (Fin.cons 0 v) (Fin.cons 0 v)) :
    ∃ e : MinkowskiModel d ≃L[ℝ] MinkowskiModel d,
      ∀ v w, B v w = minkowskiForm .timeNegative d (e v) (e w) := by
  let z : MinkowskiModel d := Fin.cons 1 (0 : Fin d → ℝ)
  let a := B z z
  have ha : a < 0 := ht
  let J : (Fin d → ℝ) →L[ℝ] MinkowskiModel d :=
    (0 : (Fin d → ℝ) →L[ℝ] ℝ).finCons (ContinuousLinearMap.id ℝ (Fin d → ℝ))
  have hJ (v : Fin d → ℝ) : J v = Fin.cons 0 v := rfl
  let b : (Fin d → ℝ) →L[ℝ] ℝ := ((B.flip) z).comp J
  let P : (Fin d → ℝ) →L[ℝ] MinkowskiModel d := J - (a⁻¹ • b).smulRight z
  have hP (v : Fin d → ℝ) : P v = J v - (b v / a) • z := by
    simp [P, div_eq_mul_inv, mul_comm]
  have hb (v : Fin d → ℝ) : b v = B (J v) z := rfl
  let Q : QuadraticForm ℝ (Fin d → ℝ) :=
    LinearMap.BilinMap.toQuadraticMap (LinearMap.mk₂ ℝ (fun u v => B (P u) (P v))
      (by intros; simp [add_apply])
      (by intros; simp [smul_apply])
      (by intros; simp)
      (by intros; simp))
  have hQ (v : Fin d → ℝ) : Q v = B (P v) (P v) := rfl
  have horth (v : Fin d → ℝ) : B (P v) z = 0 := by
    rw [hP, map_sub, map_smul]
    simp only [sub_apply, smul_apply, smul_eq_mul, ← hb]
    change b v - (b v / a) * a = 0
    field_simp [ha.ne]
    ring
  have hsplit (v : Fin d → ℝ) : B (P v) (P v) = B (J v) (J v) - (b v) ^ 2 / a := by
    calc
      B (P v) (P v) = B (P v) (J v) := by
        conv_lhs => arg 2; rw [hP v]
        simp [horth]
      _ = _ := by
        rw [hP, map_sub, map_smul]
        simp only [sub_apply, smul_apply, smul_eq_mul, hs z (J v), ← hb]
        ring
  obtain ⟨e, he⟩ := exists_linearEquiv_sum_sq Q (fun v hv => by
    rw [hQ, hsplit]
    have hp := hx v hv
    rw [← hJ v] at hp
    exact sub_pos.mpr ((div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) ha.le).trans_lt hp))
  let tailMap : MinkowskiModel d →L[ℝ] (Fin d → ℝ) := ContinuousLinearMap.pi fun i => proj i.succ
  let timeMap : MinkowskiModel d →L[ℝ] ℝ := proj 0 + a⁻¹ • (b.comp tailMap)
  let r := Real.sqrt (-a)
  have hr : r ≠ 0 := (Real.sqrt_pos.2 (neg_pos.mpr ha)).ne'
  let L : MinkowskiModel d →L[ℝ] MinkowskiModel d :=
    (r • timeMap).finCons (e.toContinuousLinearEquiv.toContinuousLinearMap.comp tailMap)
  have htL (v : MinkowskiModel d) : L v 0 = r * (v 0 + b (Fin.tail v) / a) := by
    change r * (v 0 + a⁻¹ * b (Fin.tail v)) = _
    rw [div_eq_mul_inv, mul_comm a⁻¹]
  have hxL (v : MinkowskiModel d) : Fin.tail (L v) = e (Fin.tail v) := rfl
  have hinj : Function.Injective L := by
    intro v w h
    have hs' := e.injective ((hxL v).symm.trans ((congrArg Fin.tail h).trans (hxL w)))
    have ht' := congrFun h 0
    rw [htL, htL, hs'] at ht'
    have h0 := add_right_cancel (mul_left_cancel₀ hr ht')
    rw [← Fin.cons_self_tail v, ← Fin.cons_self_tail w, h0, hs']
  let iso := (LinearEquiv.ofBijective L.toLinearMap
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj⟩
    ).toContinuousLinearEquiv
  have hdiag (v : MinkowskiModel d) :
      B v v = minkowskiForm .timeNegative d (iso v) (iso v) := by
    let u := Fin.tail v
    let t := v 0 + b u / a
    have hv : v = t • z + P u := by
      rw [hP, hJ]
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · change v 0 = t * 1 + (0 - b u / a * 1)
        dsimp [t]
        ring
      · change v j.succ = t * 0 + (u j - b u / a * 0)
        simp only [mul_zero, sub_zero, zero_add]
        rfl
    calc
      B v v = a * t ^ 2 + Q u := by
        nth_rw 1 2 [hv]
        simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, horth,
          hs z (P u), mul_zero, zero_add, add_zero, ← hQ]
        change t * (t * a) + Q u = _
        ring
      _ = _ := by
        have hsqrt : r ^ 2 = -a := Real.sq_sqrt (neg_nonneg.mpr ha.le)
        rw [he, minkowskiForm_apply, Fin.sum_univ_succ]
        change a * t ^ 2 + ∑ i, (e u i) ^ 2 =
          lorentzSign .timeNegative (0 : Fin (d + 1)) * (L v 0 * L v 0) +
            ∑ i : Fin d, lorentzSign .timeNegative i.succ * (L v i.succ * L v i.succ)
        have htail (i : Fin d) : L v i.succ = e u i := congrFun (hxL v) i
        have ht0 : L v 0 = r * t := htL v
        simp only [ht0, htail, lorentzSign, LorentzConvention.timeSign, Fin.succ_ne_zero,
          ite_false, ite_true, neg_mul, one_mul, mul_neg, mul_one, neg_neg]
        simp_rw [← pow_two]
        rw [mul_pow, hsqrt]
        ring
  refine ⟨iso, fun v w => ?_⟩
  have h := hdiag (v + w)
  simp only [map_add, add_apply] at h
  rw [hs w v, hdiag v, hdiag w, minkowskiForm_symmetric .timeNegative (iso w) (iso v)] at h
  linarith

/-- The criterion for either convention: for `σ` the hypotheses are on `−σ.timeSign • B`,
which is `B` for `.timeNegative` and `−B` for `.timePositive`. -/
theorem exists_lorentzFrame_convention (σ : LorentzConvention)
    (B : MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)
    (hs : ∀ v w, B v w = B w v)
    (ht : -σ.timeSign * B (Fin.cons 1 (0 : Fin d → ℝ)) (Fin.cons 1 (0 : Fin d → ℝ)) < 0)
    (hx : ∀ v : Fin d → ℝ, v ≠ 0 → 0 < -σ.timeSign * B (Fin.cons 0 v) (Fin.cons 0 v)) :
    ∃ e : MinkowskiModel d ≃L[ℝ] MinkowskiModel d,
      ∀ v w, B v w = minkowskiForm σ d (e v) (e w) := by
  obtain ⟨e, he⟩ := exists_lorentzFrame ((-σ.timeSign) • B)
    (fun v w => by simp only [smul_apply, smul_eq_mul, hs v w])
    (by simpa only [smul_apply, smul_eq_mul] using ht)
    (fun v hv => by simpa only [smul_apply, smul_eq_mul] using hx v hv)
  refine ⟨e, fun v w => ?_⟩
  have h := he v w
  simp only [smul_apply, smul_eq_mul] at h
  have hconv (a b : MinkowskiModel d) :
      minkowskiForm σ d a b = -σ.timeSign * minkowskiForm .timeNegative d a b := by
    cases σ <;> simp [minkowskiForm_apply, lorentzSign, LorentzConvention.timeSign,
      Finset.mul_sum]
  rw [hconv]
  have hsq := LorentzConvention.timeSign_mul_self σ
  linear_combination (-σ.timeSign) * h - B v w * hsq

end ProjectAinos.SmoothGeometry.Minkowski
