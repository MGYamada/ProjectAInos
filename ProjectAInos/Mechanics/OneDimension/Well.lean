/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.DividedDifference
public import ProjectAInos.SmoothAlgebra.ImplicitFunction
public import ProjectAInos.Variational.MovingLimits
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A potential well with simple turning points

`IsWell U E a b` states that `a < b` are simple turning points of the energy
`E` for the potential `U`: `U(a) = U(b) = E`, `U′(a) < 0 < U′(b)`, and `U < E`
between them (Landau–Lifshitz §11).

* `IsWell.sub_eq`: `E − U(x) = (x − a)(b − x) W(x)` with the smooth factor
  `W = wellFactor U a b`, the second divided difference of `U`, which is
  positive on `[a, b]` (`IsWell.wellFactor_pos`).
* `IsWell.exists_family`: the turning points are smooth functions `α(E)`,
  `β(E)` of the energy on an open set of energies around `E`, and every energy
  of that set has a well between them. The proof is the implicit function
  theorem at each turning point and the positivity of the factor.
* `isWell_oscillator`: the oscillator `U = k x²/2` with `k > 0` has a well at
  every energy `E > 0`.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace ProjectAInos.Mechanics.OneDim

open SmoothAlgebra

variable {U : ℝ → ℝ} {E a b : ℝ}

/-- `a < b` are simple turning points of the energy `E`, with `U < E` between
them. -/
structure IsWell (U : ℝ → ℝ) (E a b : ℝ) : Prop where
  /-- The left turning point is to the left of the right one. -/
  lt : a < b
  /-- The left point is on the level. -/
  left : U a = E
  /-- The right point is on the level. -/
  right : U b = E
  /-- The potential decreases at the left point. -/
  deriv_left : deriv U a < 0
  /-- The potential increases at the right point. -/
  deriv_right : 0 < deriv U b
  /-- The potential is below the level between the points. -/
  lt_energy : ∀ x ∈ Ioo a b, U x < E

/-- The factor `W` of `E − U(x) = (x − a)(b − x) W(x)`. -/
def wellFactor (U : ℝ → ℝ) (a b x : ℝ) : ℝ := dividedDifference₂ U (a, b, x)

theorem contDiff_wellFactor (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ fun q : ℝ × ℝ × ℝ => wellFactor U q.1 q.2.1 q.2.2 :=
  contDiff_dividedDifference₂ hU

theorem contDiff_wellFactor_right (hU : ContDiff ℝ ∞ U) (a b : ℝ) :
    ContDiff ℝ ∞ (wellFactor U a b) :=
  (contDiff_wellFactor hU).comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))

namespace IsWell

/-- The factorization of `E − U` between the turning points. -/
theorem sub_eq (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (x : ℝ) :
    E - U x = (x - a) * (b - x) * wellFactor U a b x :=
  sub_eq_mul_mul_dividedDifference₂ hU h.lt.ne h.left h.right x

/-- The factor at the left turning point. -/
theorem wellFactor_left (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) :
    wellFactor U a b a = -deriv U a / (b - a) := by
  have hW : DifferentiableAt ℝ (wellFactor U a b) a :=
    (contDiff_wellFactor_right hU a b).differentiable (by simp) a
  have hg : HasDerivAt (fun x => (b - x) * wellFactor U a b x)
      (-1 * wellFactor U a b a + (b - a) * deriv (wellFactor U a b) a) a :=
    ((hasDerivAt_id a).const_sub b).mul hW.hasDerivAt
  have h1 : HasDerivAt (fun x => (x - a) * ((b - x) * wellFactor U a b x))
      (1 * ((b - a) * wellFactor U a b a) +
        (a - a) * (-1 * wellFactor U a b a + (b - a) * deriv (wellFactor U a b) a)) a :=
    ((hasDerivAt_id a).sub_const a).mul hg
  have h2 : HasDerivAt (fun x => E - U x) (-deriv U a) a :=
    ((hU.differentiable (by simp) a).hasDerivAt).const_sub E
  have hfun : (fun x => E - U x) = fun x => (x - a) * ((b - x) * wellFactor U a b x) := by
    funext x
    rw [h.sub_eq hU x]
    ring
  rw [hfun] at h2
  have hval := h2.unique h1
  have hne : b - a ≠ 0 := sub_ne_zero.mpr h.lt.ne'
  rw [eq_div_iff hne]
  linarith

/-- The factor at the right turning point. -/
theorem wellFactor_right (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) :
    wellFactor U a b b = deriv U b / (b - a) := by
  have hW : DifferentiableAt ℝ (wellFactor U a b) b :=
    (contDiff_wellFactor_right hU a b).differentiable (by simp) b
  have hg : HasDerivAt (fun x => (x - a) * wellFactor U a b x)
      (1 * wellFactor U a b b + (b - a) * deriv (wellFactor U a b) b) b :=
    ((hasDerivAt_id b).sub_const a).mul hW.hasDerivAt
  have h1 : HasDerivAt (fun x => (b - x) * ((x - a) * wellFactor U a b x))
      (-1 * ((b - a) * wellFactor U a b b) +
        (b - b) * (1 * wellFactor U a b b + (b - a) * deriv (wellFactor U a b) b)) b :=
    ((hasDerivAt_id b).const_sub b).mul hg
  have h2 : HasDerivAt (fun x => E - U x) (-deriv U b) b :=
    ((hU.differentiable (by simp) b).hasDerivAt).const_sub E
  have hfun : (fun x => E - U x) = fun x => (b - x) * ((x - a) * wellFactor U a b x) := by
    funext x
    rw [h.sub_eq hU x]
    ring
  rw [hfun] at h2
  have hval := h2.unique h1
  have hne : b - a ≠ 0 := sub_ne_zero.mpr h.lt.ne'
  rw [eq_div_iff hne]
  linarith

/-- The factor is positive on the closed interval between the turning points. -/
theorem wellFactor_pos (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) {x : ℝ}
    (hx : x ∈ Icc a b) : 0 < wellFactor U a b x := by
  have hba : 0 < b - a := sub_pos.mpr h.lt
  rcases eq_or_lt_of_le hx.1 with rfl | hax
  · rw [h.wellFactor_left hU]
    exact div_pos (neg_pos.mpr h.deriv_left) hba
  rcases eq_or_lt_of_le hx.2 with rfl | hxb
  · rw [h.wellFactor_right hU]
    exact div_pos h.deriv_right hba
  have hpos : 0 < E - U x := sub_pos.mpr (h.lt_energy x ⟨hax, hxb⟩)
  rw [h.sub_eq hU x] at hpos
  have hprod : 0 < (x - a) * (b - x) := mul_pos (sub_pos.mpr hax) (sub_pos.mpr hxb)
  exact (pos_iff_pos_of_mul_pos hpos).mp hprod

end IsWell

/-- If the level is reached at two points and the factor is positive between
them, with the right signs of the derivative at the points, there is a well. -/
theorem isWell_of_wellFactor_pos (hU : ContDiff ℝ ∞ U) (hab : a < b) (ha : U a = E)
    (hb : U b = E) (hda : deriv U a < 0) (hdb : 0 < deriv U b)
    (hW : ∀ x ∈ Icc a b, 0 < wellFactor U a b x) : IsWell U E a b where
  lt := hab
  left := ha
  right := hb
  deriv_left := hda
  deriv_right := hdb
  lt_energy x hx := by
    have h := sub_eq_mul_mul_dividedDifference₂ hU hab.ne ha hb x
    have hpos : 0 < (x - a) * (b - x) * wellFactor U a b x :=
      mul_pos (mul_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)) (hW x ⟨hx.1.le, hx.2.le⟩)
    rw [← sub_pos, h]
    exact hpos

/-- A simple point of a level is a smooth function of the level, on an open set
of levels. -/
theorem exists_level_point (hU : ContDiff ℝ ∞ U) {E₀ x₀ : ℝ} (hx₀ : U x₀ = E₀)
    (hd : deriv U x₀ ≠ 0) :
    ∃ (J : Set ℝ) (ξ : ℝ → ℝ), IsOpen J ∧ E₀ ∈ J ∧ ξ E₀ = x₀ ∧ ContDiffOn ℝ ∞ ξ J ∧
      ∀ E ∈ J, U (ξ E) = E := by
  let f : ℝ × ℝ → ℝ := fun v => U v.2 - v.1
  have hf : ContDiff ℝ ∞ f := (hU.comp contDiff_snd).sub contDiff_fst
  have hfd : ∀ v : ℝ × ℝ, fderiv ℝ f v ∘L ContinuousLinearMap.inr ℝ ℝ ℝ =
      deriv U v.2 • ContinuousLinearMap.id ℝ ℝ := by
    intro v
    have h1 : HasFDerivAt (fun y : ℝ => f (v.1, y)) (fderiv ℝ f v ∘L
        ContinuousLinearMap.inr ℝ ℝ ℝ) v.2 :=
      HasFDerivAt.comp (g := f) (f := fun y : ℝ => (v.1, y)) v.2
        (hf.differentiable (by simp) v).hasFDerivAt (hasFDerivAt_prodMk_right v.1 v.2)
    have h2 : HasDerivAt (fun y : ℝ => f (v.1, y)) (deriv U v.2) v.2 :=
      ((hU.differentiable (by simp) v.2).hasDerivAt).sub_const v.1
    have h3 := h1.unique h2.hasFDerivAt
    rw [h3]
    ext
    simp
  have hopen : IsOpen {v : ℝ × ℝ | deriv U v.2 ≠ 0} :=
    isOpen_ne_fun ((hU.continuous_deriv (by simp)).comp continuous_snd) continuous_const
  have hinv : ∀ v ∈ {v : ℝ × ℝ | deriv U v.2 ≠ 0},
      (fderiv ℝ f v ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    intro v hv
    rw [hfd v]
    refine ContinuousLinearMap.IsInvertible.of_inverse
      (g := (deriv U v.2)⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_
    · ext
      simp
      exact inv_mul_cancel₀ hv
    · ext
      simp
      exact mul_inv_cancel₀ hv
  obtain ⟨J, ξ, hJ, hE₀, hξ₀, hξ, hsol⟩ := exists_contDiffOn_implicitFunction (f := f)
    hopen hf.contDiffOn hinv (u := (E₀, x₀)) hd
  refine ⟨J, ξ, hJ, hE₀, hξ₀, hξ, fun E hE => ?_⟩
  have h := (hsol E hE).2
  change U (ξ E) - E = U x₀ - E₀ at h
  rw [hx₀, sub_self, sub_eq_zero] at h
  exact h

/-- The turning points of a well are smooth functions of the energy, and the
nearby energies have wells between them. -/
theorem IsWell.exists_family (hU : ContDiff ℝ ∞ U) {E₀ a₀ b₀ : ℝ} (h : IsWell U E₀ a₀ b₀) :
    ∃ (J : Set ℝ) (α β : ℝ → ℝ), IsOpen J ∧ E₀ ∈ J ∧ α E₀ = a₀ ∧ β E₀ = b₀ ∧
      ContDiffOn ℝ ∞ α J ∧ ContDiffOn ℝ ∞ β J ∧ ∀ E ∈ J, IsWell U E (α E) (β E) := by
  obtain ⟨Ja, α, hJa, hEa, hα₀, hα, hαU⟩ := exists_level_point hU h.left h.deriv_left.ne
  obtain ⟨Jb, β, hJb, hEb, hβ₀, hβ, hβU⟩ := exists_level_point hU h.right h.deriv_right.ne'
  have hJ₀ : IsOpen (Ja ∩ Jb) := hJa.inter hJb
  have hE₀ : E₀ ∈ Ja ∩ Jb := ⟨hEa, hEb⟩
  have hαc : ContinuousOn α (Ja ∩ Jb) := hα.continuousOn.mono inter_subset_left
  have hβc : ContinuousOn β (Ja ∩ Jb) := hβ.continuousOn.mono inter_subset_right
  have hαat : ContinuousAt α E₀ := hαc.continuousAt (hJ₀.mem_nhds hE₀)
  have hβat : ContinuousAt β E₀ := hβc.continuousAt (hJ₀.mem_nhds hE₀)
  -- the open set of energies and points at which the factor is positive
  have hWc : ContinuousOn (fun v : ℝ × ℝ => wellFactor U (α v.1) (β v.1) v.2)
      (Prod.fst ⁻¹' (Ja ∩ Jb)) := by
    have hmap : ContinuousOn (fun v : ℝ × ℝ => (α v.1, β v.1, v.2))
        (Prod.fst ⁻¹' (Ja ∩ Jb)) :=
      (hαc.comp continuousOn_fst fun v hv => hv).prodMk
        ((hβc.comp continuousOn_fst fun v hv => hv).prodMk continuousOn_snd)
    exact Continuous.comp_continuousOn
      (g := fun q : ℝ × ℝ × ℝ => wellFactor U q.1 q.2.1 q.2.2)
      (f := fun v : ℝ × ℝ => (α v.1, β v.1, v.2)) (contDiff_wellFactor hU).continuous hmap
  have hV : IsOpen ((Prod.fst ⁻¹' (Ja ∩ Jb) : Set (ℝ × ℝ)) ∩
      (fun v : ℝ × ℝ => wellFactor U (α v.1) (β v.1) v.2) ⁻¹' Ioi 0) :=
    hWc.isOpen_inter_preimage (hJ₀.preimage continuous_fst) isOpen_Ioi
  have hbase : ∀ x ∈ uIcc (α E₀) (β E₀), (E₀, x) ∈
      (Prod.fst ⁻¹' (Ja ∩ Jb) : Set (ℝ × ℝ)) ∩
        (fun v : ℝ × ℝ => wellFactor U (α v.1) (β v.1) v.2) ⁻¹' Ioi 0 := by
    intro x hx
    rw [hα₀, hβ₀, uIcc_of_le h.lt.le] at hx
    refine ⟨hE₀, ?_⟩
    change 0 < wellFactor U (α E₀) (β E₀) x
    rw [hα₀, hβ₀]
    exact h.wellFactor_pos hU hx
  have hev := Variational.eventually_uIcc_mem_open hαat hβat hV hbase
  have hlt : ∀ᶠ E in 𝓝 E₀, α E < β E := by
    have h1 : ContinuousAt (fun E => β E - α E) E₀ := hβat.sub hαat
    have h2 : 0 < β E₀ - α E₀ := by rw [hα₀, hβ₀]; exact sub_pos.mpr h.lt
    exact (h1.eventually (lt_mem_nhds h2)).mono fun E hE => sub_pos.mp hE
  have hdc : Continuous (deriv U) := hU.continuous_deriv (by simp)
  have hda : ∀ᶠ E in 𝓝 E₀, deriv U (α E) < 0 := by
    have h1 : ContinuousAt (fun E => deriv U (α E)) E₀ := hdc.continuousAt.comp hαat
    have h2 : (fun E => deriv U (α E)) E₀ < 0 := by
      change deriv U (α E₀) < 0
      rw [hα₀]
      exact h.deriv_left
    exact h1.eventually (gt_mem_nhds h2)
  have hdb : ∀ᶠ E in 𝓝 E₀, 0 < deriv U (β E) := by
    have h1 : ContinuousAt (fun E => deriv U (β E)) E₀ := hdc.continuousAt.comp hβat
    have h2 : 0 < (fun E => deriv U (β E)) E₀ := by
      change 0 < deriv U (β E₀)
      rw [hβ₀]
      exact h.deriv_right
    exact h1.eventually (lt_mem_nhds h2)
  have hmemJ : ∀ᶠ E in 𝓝 E₀, E ∈ Ja ∩ Jb := hJ₀.mem_nhds hE₀
  obtain ⟨J, hJsub, hJ, hEJ⟩ := eventually_nhds_iff.mp
    (hmemJ.and (hev.and (hlt.and (hda.and hdb))))
  refine ⟨J, α, β, hJ, hEJ, hα₀, hβ₀, hα.mono fun E hE => (hJsub E hE).1.1,
    hβ.mono fun E hE => (hJsub E hE).1.2, fun E hE => ?_⟩
  obtain ⟨hEJ₀, hpos, hEl, hEa', hEb'⟩ := hJsub E hE
  refine isWell_of_wellFactor_pos hU hEl (hαU E hEJ₀.1) (hβU E hEJ₀.2) hEa' hEb' fun x hx => ?_
  have hx' : x ∈ uIcc (α E) (β E) := by rwa [uIcc_of_le hEl.le]
  exact (hpos x hx').2

/-! ### The oscillator -/

/-- The oscillator `U = k x²/2` has a well at every positive energy. -/
theorem isWell_oscillator {k E : ℝ} (hk : 0 < k) (hE : 0 < E) :
    IsWell (fun x => k / 2 * x ^ 2) E (-√(2 * E / k)) √(2 * E / k) := by
  have hpos : 0 < 2 * E / k := by positivity
  have hs : 0 < √(2 * E / k) := Real.sqrt_pos.mpr hpos
  have hsq : √(2 * E / k) ^ 2 = 2 * E / k := Real.sq_sqrt hpos.le
  have hd : ∀ x : ℝ, deriv (fun x : ℝ => k / 2 * x ^ 2) x = k * x := by
    intro x
    have h : HasDerivAt (fun x : ℝ => k / 2 * x ^ 2) (k * x) x := by
      refine (((hasDerivAt_id x).pow 2).const_mul (k / 2)).congr_deriv ?_
      simp
      ring
    exact h.deriv
  refine ⟨by linarith, ?_, ?_, ?_, ?_, fun x hx => ?_⟩
  · rw [neg_sq, hsq]
    field_simp
  · rw [hsq]
    field_simp
  · rw [hd]
    nlinarith
  · rw [hd]
    positivity
  · have hx2 : x ^ 2 < √(2 * E / k) ^ 2 := by
      rw [sq_lt_sq, abs_of_pos hs]
      exact abs_lt.mpr ⟨hx.1, hx.2⟩
    rw [hsq] at hx2
    have h1 : k / 2 * x ^ 2 < k / 2 * (2 * E / k) := by gcongr
    have h2 : k / 2 * (2 * E / k) = E := by field_simp
    linarith

end ProjectAInos.Mechanics.OneDim
