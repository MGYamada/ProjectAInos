/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.SphericalAnsatz
public import ProjectAinos.GeneralRelativity.SchwarzschildExterior
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Birkhoff's theorem in the centrally symmetric ansatz

Landau–Lifshitz, §100: the field of a centrally symmetric distribution of matter is static
outside the matter, and it is the Schwarzschild field. In the ansatz
`ds² = −A(t, r) dt² + B(t, r) dr² + r² (dθ² + sin²θ dφ²)` of `SphericalAnsatz` on a product
`I × J` of open intervals, the vacuum equations `R_{ik} = 0` force the form (100.14) of the field
up to a function of the time alone, which a change of the time co-ordinate removes.

* `birkhoff`: **Birkhoff's theorem.** If `I` and `J` are preconnected and the Ricci tensor
  vanishes on the domain, there are a real `M` with `r > 2M` on `J` and a smooth positive `f` on
  `I` with `B = r/(r − 2M)` and `A = f(t) (r − 2M)/r`. The proof reads `G₀₁ = B_t/(rB) = 0`, so
  that `B` does not depend on `t`; `G₀₀ = 0` as `∂_r(r/B) = 1`, so that `r/B = r − 2M`; and
  `G₀₀/A + G₁₁/B = ∂_r(AB)/(rAB²) = 0`, so that `AB = f(t)`. The constant `M` may be negative.
* `schwarzschildData`, `ricciOf_schwarzschildData`: conversely, for every real `M` with
  `r > 2M` on `J` and every smooth positive `f`, the data `A = f(t)(r − 2M)/r`, `B = r/(r − 2M)`
  are Ricci flat.
* `timeChange`, `hasFDerivAt_timeChange`, `form_schwarzschildData`,
  `timeChange_schwarzschildData`: with a new time `T` with `T' = √f`, the map
  `(t, r, θ, φ) ↦ (T(t), r, θ, φ)` pulls the Schwarzschild form
  `SchwarzschildExterior.form M` back to the metric of these data: the vacuum field is the
  Schwarzschild field (100.14) in the time `T`. `exists_hasDerivAt_sqrt` gives such a `T` on an
  open interval, and `birkhoff_timeChange` states the theorem in this form.
* `eq_of_B_eq`, `mass_schwarzschildData`: the constant `M` is determined by `B` when `I` and
  `J` are nonempty, so `birkhoff` returns the constant of the Schwarzschild data.
* `exteriorData`, `form_exteriorData`, `exists_birkhoff_exteriorData`: the exterior
  Schwarzschild data of a mass `M ≥ 0` (`f = 1`) have the form `SchwarzschildExterior.form M`,
  satisfy the hypotheses of `birkhoff`, and `birkhoff` returns the mass `M`; `expTimeData`,
  `form_expTimeData`, `exists_birkhoff_expTimeData` are the same with the nonconstant `f = eᵗ`
  and the new time `T = 2 e^{t/2}`.
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap Set Filter
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.SphericalAnsatz

open SmoothGeometry CoordinateMetric

/-! ### The vacuum equations in the ansatz -/

variable {D : Data}

/-- Where the Ricci tensor vanishes, so does the Einstein tensor. -/
theorem einsteinOf_eq_zero_of_ricciOf {x : MinkowskiModel 3}
    (h : ∀ j k, ricciOf (metric D).coefficient x j k = 0) (i k : Fin 4) :
    einsteinOf (metric D).coefficient x i k = 0 := by
  simp [einsteinOf, scalarOf, h]

/-- The point `(t, r, π/2, 0)` of the equatorial plane. -/
def equatorialPoint (t r : ℝ) : MinkowskiModel 3 := ![t, r, Real.pi / 2, 0]

/-- The equatorial point of a time of `I` and a radius of `J` lies in the domain. -/
theorem equatorialPoint_mem {t r : ℝ} (ht : t ∈ D.I) (hr : r ∈ D.J) :
    equatorialPoint t r ∈ domain D :=
  ⟨ht, hr, by simp [equatorialPoint, Real.pi_pos], by
    simp only [equatorialPoint, Matrix.cons_val]
    linarith [Real.pi_pos]⟩

/-- In vacuum `G_{ik} = 0` at the equatorial points. -/
private theorem einstein_equatorial
    (hvac : ∀ x ∈ domain D, ∀ j k, ricciOf (metric D).coefficient x j k = 0) {t r : ℝ}
    (ht : t ∈ D.I) (hr : r ∈ D.J) (i k : Fin 4) :
    einsteinOf (metric D).coefficient (equatorialPoint t r) i k = 0 :=
  einsteinOf_eq_zero_of_ricciOf (hvac _ (equatorialPoint_mem ht hr)) i k

/-- In vacuum `∂_t B = 0`, from `G₀₁ = B_t/(rB)`. -/
theorem partialT_B_eq_zero_of_vacuum
    (hvac : ∀ x ∈ domain D, ∀ j k, ricciOf (metric D).coefficient x j k = 0) {t r : ℝ}
    (ht : t ∈ D.I) (hr : r ∈ D.J) :
    partialT D.B t r = 0 := by
  have h : partialT D.B t r / (r * D.B t r) = 0 :=
    (einstein_zero_one (equatorialPoint_mem ht hr)).symm.trans (einstein_equatorial hvac ht hr 0 1)
  have hd : r * D.B t r ≠ 0 := mul_ne_zero (D.J_pos hr).ne' (D.B_pos t ht r hr).ne'
  exact (div_eq_zero_iff.mp h).resolve_right hd

/-- In vacuum `1 − 1/B + r B_r/B² = 0`, from `G₀₀ = A/r² (1 − 1/B + r B_r/B²)`. -/
theorem one_sub_inv_add_eq_zero_of_vacuum
    (hvac : ∀ x ∈ domain D, ∀ j k, ricciOf (metric D).coefficient x j k = 0) {t r : ℝ}
    (ht : t ∈ D.I) (hr : r ∈ D.J) :
    1 - 1 / D.B t r + r * partialR D.B t r / D.B t r ^ 2 = 0 := by
  have h : D.A t r / r ^ 2 * (1 - 1 / D.B t r + r * partialR D.B t r / D.B t r ^ 2) = 0 :=
    (einstein_zero_zero (equatorialPoint_mem ht hr)).symm.trans
      (einstein_equatorial hvac ht hr 0 0)
  have hd : D.A t r / r ^ 2 ≠ 0 :=
    div_ne_zero (D.A_pos t ht r hr).ne' (pow_pos (D.J_pos hr) 2).ne'
  exact (mul_eq_zero.mp h).resolve_left hd

/-- In vacuum `∂_r(AB) = 0`, from `G₀₀/A + G₁₁/B = ∂_r(AB)/(rAB²)`. -/
theorem partialR_mul_eq_zero_of_vacuum
    (hvac : ∀ x ∈ domain D, ∀ j k, ricciOf (metric D).coefficient x j k = 0) {t r : ℝ}
    (ht : t ∈ D.I) (hr : r ∈ D.J) :
    partialR D.A t r * D.B t r + D.A t r * partialR D.B t r = 0 := by
  have hx := equatorialPoint_mem ht hr
  have h : partialR (fun t r => D.A t r * D.B t r) t r / (r * D.A t r * D.B t r ^ 2) = 0 := by
    have e := einstein_zero_zero_div_add_one_one_div hx
    rw [einstein_equatorial hvac ht hr 0 0, einstein_equatorial hvac ht hr 1 1] at e
    simp only [zero_div, add_zero] at e
    exact e.symm
  have hd : r * D.A t r * D.B t r ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (D.J_pos hr).ne' (D.A_pos t ht r hr).ne')
      (pow_pos (D.B_pos t ht r hr) 2).ne'
  have e : partialR (fun t r => D.A t r * D.B t r) t r =
      partialR D.A t r * D.B t r + D.A t r * partialR D.B t r := partialR_mul hx
  rw [← e]
  exact (div_eq_zero_iff.mp h).resolve_right hd

/-- A function with derivative `0` on a preconnected open set takes equal values there. -/
private theorem eq_of_hasDerivAt_zero {s : Set ℝ} {g : ℝ → ℝ} (hs : IsOpen s)
    (hs' : IsPreconnected s) (hg : ∀ y ∈ s, HasDerivAt g 0 y) {a b : ℝ} (ha : a ∈ s)
    (hb : b ∈ s) : g a = g b :=
  hs.is_const_of_deriv_eq_zero hs' (fun y hy => (hg y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hg y hy).deriv) ha hb

/-- A smooth function of `(t, r)` is smooth in `t` at a fixed radius of `J`. -/
private theorem contDiffOn_slice {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (D.I ×ˢ D.J)) {r₀ : ℝ} (hr₀ : r₀ ∈ D.J) :
    ContDiffOn ℝ ∞ (fun t => g t r₀) D.I :=
  hg.comp (contDiffOn_id.prodMk contDiffOn_const) fun _ ht => ⟨ht, hr₀⟩

/-- **Birkhoff's theorem** (Landau–Lifshitz, §100). On a product `I × J` of open intervals, a
centrally symmetric vacuum field `ds² = −A dt² + B dr² + r² dΩ²` is the Schwarzschild field
`B = r/(r − 2M)`, `A = f(t)(r − 2M)/r` for a real `M` with `r > 2M` on `J`, up to the smooth
positive function `f` of the time, which a change of the time removes (`form_eq_timeChange`).
The constant `M` may be negative: the vacuum equations do not fix its sign. -/
theorem birkhoff (D : Data) (hI : IsPreconnected D.I) (hJ : IsPreconnected D.J)
    (hvac : ∀ x ∈ domain D, ∀ j k, ricciOf (metric D).coefficient x j k = 0) :
    ∃ M : ℝ, (∀ r ∈ D.J, 2 * M < r) ∧ ∃ f : ℝ → ℝ, ContDiffOn ℝ ∞ f D.I ∧
      (∀ t ∈ D.I, 0 < f t) ∧
      ∀ t ∈ D.I, ∀ r ∈ D.J, D.B t r = r / (r - 2 * M) ∧ D.A t r = f t * ((r - 2 * M) / r) := by
  rcases (D.I ×ˢ D.J).eq_empty_or_nonempty with hIJ | ⟨⟨t₀, r₀⟩, ht₀, hr₀⟩
  · refine ⟨0, fun r hr => by simpa using D.J_pos hr, fun _ => 1, contDiffOn_const,
      fun _ _ => one_pos, fun t ht r hr => ?_⟩
    have h : (t, r) ∈ D.I ×ˢ D.J := ⟨ht, hr⟩
    rw [hIJ] at h
    exact absurd h (notMem_empty _)
  have ht₀ : t₀ ∈ D.I := ht₀
  have hr₀ : r₀ ∈ D.J := hr₀
  have hS := isOpen_timeRadius D
  -- `B` does not depend on the time.
  have hBt : ∀ t ∈ D.I, ∀ r ∈ D.J, D.B t r = D.B t₀ r := fun t ht r hr =>
    eq_of_hasDerivAt_zero (g := fun s => D.B s r) D.isOpen_I hI (fun s hs => by
      have h := hasDerivAt_partialT hS D.contDiffOn_B (show (s, r) ∈ D.I ×ˢ D.J from ⟨hs, hr⟩)
      rwa [partialT_B_eq_zero_of_vacuum hvac hs hr] at h) ht ht₀
  -- `r/B − r` is a constant `−2M`.
  set M : ℝ := (r₀ - r₀ / D.B t₀ r₀) / 2 with hMdef
  have hrad : ∀ r ∈ D.J, r / D.B t₀ r = r - 2 * M := fun r hr => by
    have h := eq_of_hasDerivAt_zero (g := fun s => s / D.B t₀ s - s) D.isOpen_J hJ
      (fun s hs => by
        have hB := D.B_pos t₀ ht₀ s hs
        have h2 : HasDerivAt (fun s => s / D.B t₀ s - s)
            ((1 * D.B t₀ s - s * partialR D.B t₀ s) / D.B t₀ s ^ 2 - 1) s :=
          ((hasDerivAt_id' s).div (hasDerivAt_partialR hS D.contDiffOn_B
            (show (t₀, s) ∈ D.I ×ˢ D.J from ⟨ht₀, hs⟩)) hB.ne').sub (hasDerivAt_id' s)
        refine h2.congr_deriv ?_
        have e : (1 * D.B t₀ s - s * partialR D.B t₀ s) / D.B t₀ s ^ 2 - 1 =
            -(1 - 1 / D.B t₀ s + s * partialR D.B t₀ s / D.B t₀ s ^ 2) := by
          field_simp
          ring
        rw [e, one_sub_inv_add_eq_zero_of_vacuum hvac ht₀ hs, neg_zero]) hr hr₀
    rw [hMdef]
    linarith
  have hpos : ∀ r ∈ D.J, 2 * M < r := fun r hr => by
    have h := div_pos (D.J_pos hr) (D.B_pos t₀ ht₀ r hr)
    rw [hrad r hr] at h
    linarith
  have hB : ∀ t ∈ D.I, ∀ r ∈ D.J, D.B t r = r / (r - 2 * M) := fun t ht r hr => by
    have hb := D.B_pos t₀ ht₀ r hr
    rw [hBt t ht r hr, ← hrad r hr]
    field_simp [(D.J_pos hr).ne']
  refine ⟨M, hpos, fun t => D.A t r₀ * D.B t r₀,
    (contDiffOn_slice D.contDiffOn_A hr₀).mul (contDiffOn_slice D.contDiffOn_B hr₀),
    fun t ht => mul_pos (D.A_pos t ht r₀ hr₀) (D.B_pos t ht r₀ hr₀),
    fun t ht r hr => ⟨hB t ht r hr, ?_⟩⟩
  -- `AB` does not depend on the radius.
  have hAB : D.A t r * D.B t r = D.A t r₀ * D.B t r₀ :=
    eq_of_hasDerivAt_zero (g := fun s => D.A t s * D.B t s) D.isOpen_J hJ (fun s hs => by
      have h := (hasDerivAt_partialR hS D.contDiffOn_A
        (show (t, s) ∈ D.I ×ˢ D.J from ⟨ht, hs⟩)).mul
        (hasDerivAt_partialR hS D.contDiffOn_B (show (t, s) ∈ D.I ×ˢ D.J from ⟨ht, hs⟩))
      rwa [partialR_mul_eq_zero_of_vacuum hvac ht hs] at h) hr hr₀
  have hb := D.B_pos t ht r hr
  have hr2 : r - 2 * M ≠ 0 := (sub_pos.mpr (hpos r hr)).ne'
  have hr0 := (D.J_pos hr).ne'
  show D.A t r = D.A t r₀ * D.B t r₀ * ((r - 2 * M) / r)
  rw [← hAB, hB t ht r hr]
  field_simp

/-! ### The Schwarzschild data -/

/-- The coefficient `A(t, r) = f(t)(r − 2M)/r` of the Schwarzschild data. -/
def schwarzschildA (M : ℝ) (f : ℝ → ℝ) (t r : ℝ) : ℝ := f t * ((r - 2 * M) / r)

/-- The coefficient `B(t, r) = r/(r − 2M)` of the Schwarzschild data. -/
def schwarzschildB (M : ℝ) (_t r : ℝ) : ℝ := r / (r - 2 * M)

/-- **The Schwarzschild data** (Landau–Lifshitz, (100.14)) of a real `M` on a product `I × J` of
open sets with `0 < r` and `2M < r` on `J`, with a smooth positive function `f` of the time:
`A = f(t)(r − 2M)/r`, `B = r/(r − 2M)`. -/
def schwarzschildData (M : ℝ) (I J : Set ℝ) (hI : IsOpen I) (hJ : IsOpen J)
    (hJM : ∀ r ∈ J, 0 < r ∧ 2 * M < r) (f : ℝ → ℝ) (hf : ContDiffOn ℝ ∞ f I)
    (hfpos : ∀ t ∈ I, 0 < f t) : Data where
  I := I
  J := J
  A := schwarzschildA M f
  B := schwarzschildB M
  isOpen_I := hI
  isOpen_J := hJ
  J_pos := fun r hr => (hJM r hr).1
  contDiffOn_A := (hf.comp contDiffOn_fst fun _ hp => hp.1).mul
    ((contDiffOn_snd.sub contDiffOn_const).div contDiffOn_snd fun p hp => (hJM p.2 hp.2).1.ne')
  contDiffOn_B := contDiffOn_snd.div (contDiffOn_snd.sub contDiffOn_const)
    fun p hp => (sub_pos.mpr (hJM p.2 hp.2).2).ne'
  A_pos := fun t ht r hr =>
    mul_pos (hfpos t ht) (div_pos (sub_pos.mpr (hJM r hr).2) (hJM r hr).1)
  B_pos := fun _ _ r hr => div_pos (hJM r hr).1 (sub_pos.mpr (hJM r hr).2)

variable {M : ℝ} {f : ℝ → ℝ}

/-- `B = r/(r − 2M)` does not depend on the time. -/
@[simp] theorem partialT_schwarzschildB : partialT (schwarzschildB M) = fun _ _ => 0 := by
  funext t r
  simp [partialT, schwarzschildB]

/-- `∂_r B = −2M/(r − 2M)²`. -/
theorem partialR_schwarzschildB {t r : ℝ} (hr : r - 2 * M ≠ 0) :
    partialR (schwarzschildB M) t r = -(2 * M) / (r - 2 * M) ^ 2 := by
  have h : HasDerivAt (fun s => s / (s - 2 * M)) ((1 * (r - 2 * M) - r * 1) / (r - 2 * M) ^ 2)
      r := (hasDerivAt_id' r).div ((hasDerivAt_id' r).sub_const (2 * M)) hr
  rw [partialR, show (fun s => schwarzschildB M t s) = fun s => s / (s - 2 * M) from rfl, h.deriv]
  field_simp
  ring

/-- The derivative of `(r − 2M)/r` is `2M/r²`. -/
private theorem hasDerivAt_lapse {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun s => (s - 2 * M) / s) (2 * M / r ^ 2) r := by
  refine (((hasDerivAt_id' r).sub_const (2 * M)).div (hasDerivAt_id' r) hr).congr_deriv ?_
  field_simp
  ring

/-- `∂_r A = f(t) 2M/r²`. -/
theorem partialR_schwarzschildA {t r : ℝ} (hr : r ≠ 0) :
    partialR (schwarzschildA M f) t r = f t * (2 * M / r ^ 2) :=
  ((hasDerivAt_lapse hr).const_mul (f t)).deriv

/-- `∂_r² A = −f(t) 4M/r³`. -/
theorem partialR_partialR_schwarzschildA {t r : ℝ} (hr : r ≠ 0) :
    partialR (partialR (schwarzschildA M f)) t r = f t * (-(4 * M) / r ^ 3) := by
  have e : (fun s => partialR (schwarzschildA M f) t s) =ᶠ[𝓝 r]
      fun s => f t * (2 * M / s ^ 2) := by
    filter_upwards [isOpen_ne.mem_nhds hr] with s hs
    exact partialR_schwarzschildA hs
  have h : HasDerivAt (fun s => f t * (2 * M / s ^ 2)) (f t * (-(4 * M) / r ^ 3)) r := by
    refine (((hasDerivAt_const r (2 * M)).div (hasDerivAt_pow 2 r)
      (pow_ne_zero 2 hr)).const_mul (f t)).congr_deriv ?_
    field_simp
    ring
  rw [partialR, e.deriv_eq, h.deriv]

section SchwarzschildData

variable {I J : Set ℝ} {hI : IsOpen I} {hJ : IsOpen J} {hJM : ∀ r ∈ J, 0 < r ∧ 2 * M < r}
  {hf : ContDiffOn ℝ ∞ f I} {hfpos : ∀ t ∈ I, 0 < f t}

/-- **The Schwarzschild data are Ricci flat** on their domain (Landau–Lifshitz, (100.14)), for
every real `M` and every smooth positive function `f` of the time. -/
theorem ricciOf_schwarzschildData {x : MinkowskiModel 3}
    (hx : x ∈ domain (schwarzschildData M I J hI hJ hJM f hf hfpos)) (j k : Fin 4) :
    ricciOf (metric (schwarzschildData M I J hI hJ hJM f hf hfpos)).coefficient x j k = 0 := by
  have hr : x 1 ≠ 0 := (radius_pos hx).ne'
  have hrM : x 1 - 2 * M ≠ 0 := (sub_pos.mpr (hJM _ hx.2.1).2).ne'
  have hf0 : f (x 0) ≠ 0 := (hfpos _ hx.1).ne'
  rw [ricciOf_eq hx]
  have eA : (schwarzschildData M I J hI hJ hJM f hf hfpos).A = schwarzschildA M f := rfl
  have eB : (schwarzschildData M I J hI hJ hJM f hf hfpos).B = schwarzschildB M := rfl
  fin_cases j <;> fin_cases k <;>
  · simp only [ricci, eA, eB, partialT_schwarzschildB, partialT_const,
      partialR_schwarzschildB hrM, partialR_schwarzschildA hr,
      partialR_partialR_schwarzschildA hr, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Fin.isValue, Matrix.cons_val]
    try simp only [schwarzschildA, schwarzschildB]
    try field_simp
    try ring

/-! ### The change of the time -/

/-- The change `(t, r, θ, φ) ↦ (T(t), r, θ, φ)` of the time co-ordinate. -/
def timeChange (T : ℝ → ℝ) (x : MinkowskiModel 3) : MinkowskiModel 3 := ![T (x 0), x 1, x 2, x 3]

/-- The differential `v ↦ (√(f(t)) v⁰, v¹, v², v³)` of the change of the time with
`T' = √f`. -/
def timeChangeDeriv (f : ℝ → ℝ) (x : MinkowskiModel 3) :
    MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 :=
  ContinuousLinearMap.pi (R := ℝ) (φ := fun _ : Fin (3 + 1) => ℝ)
    ![Real.sqrt (f (x 0)) • (proj 0 : MinkowskiModel 3 →L[ℝ] ℝ),
      (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ), (proj 2 : MinkowskiModel 3 →L[ℝ] ℝ),
      (proj 3 : MinkowskiModel 3 →L[ℝ] ℝ)]

/-- The differential of the change of the time on a vector. -/
theorem timeChangeDeriv_apply (f : ℝ → ℝ) (x v : MinkowskiModel 3) :
    timeChangeDeriv f x v = ![Real.sqrt (f (x 0)) * v 0, v 1, v 2, v 3] := by
  ext i
  fin_cases i <;> simp [timeChangeDeriv]

/-- **The change of the time is differentiable**: where `T' = √f`, the derivative of
`(t, r, θ, φ) ↦ (T(t), r, θ, φ)` is `timeChangeDeriv f`. -/
theorem hasFDerivAt_timeChange {T : ℝ → ℝ} {x : MinkowskiModel 3}
    (hT : HasDerivAt T (Real.sqrt (f (x 0))) (x 0)) :
    HasFDerivAt (timeChange T) (timeChangeDeriv f x) x := by
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  · refine (hT.comp_hasFDerivAt x (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin (3 + 1)) x)).congr_fderiv
      ?_
    ext v
    simp [timeChangeDeriv_apply]
  · refine (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin (3 + 1)) x).congr_fderiv ?_
    ext v
    simp [timeChangeDeriv_apply]
  · refine (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin (3 + 1)) x).congr_fderiv ?_
    ext v
    simp [timeChangeDeriv_apply]
  · refine (hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin (3 + 1)) x).congr_fderiv ?_
    ext v
    simp [timeChangeDeriv_apply]

/-- The form of the ansatz is `g(v, w) = −A v⁰w⁰ + B v¹w¹ + r² v²w² + r² sin²θ v³w³`. -/
private theorem form_metric_apply (D : Data) (x v w : MinkowskiModel 3) :
    (metric D).form x v w = -D.A (x 0) (x 1) * v 0 * w 0 + D.B (x 0) (x 1) * v 1 * w 1 +
      x 1 ^ 2 * v 2 * w 2 + x 1 ^ 2 * Real.sin (x 2) ^ 2 * v 3 * w 3 := by
  change diagonalForm (coefficients D) x v w = _
  rw [diagonalForm_apply, Fin.sum_univ_four]
  simp [coefficients]

/-- **The Schwarzschild field after a change of the time.** At a point where
`A = f(t)(r − 2M)/r` and `B = r/(r − 2M)` with `f(t) ≥ 0`, the form of the ansatz is the
pull-back of the Schwarzschild form `SchwarzschildExterior.form M` by
`(t, r, θ, φ) ↦ (T(t), r, θ, φ)` with the differential `timeChangeDeriv f`; the identity is
algebraic and holds for every real `M`. -/
theorem form_eq_timeChange (D : Data) {T : ℝ → ℝ} {x : MinkowskiModel 3}
    (hA : D.A (x 0) (x 1) = f (x 0) * ((x 1 - 2 * M) / x 1))
    (hB : D.B (x 0) (x 1) = x 1 / (x 1 - 2 * M)) (hf : 0 ≤ f (x 0)) (v w : MinkowskiModel 3) :
    (metric D).form x v w = SchwarzschildExterior.form M (timeChange T x)
      (timeChangeDeriv f x v) (timeChangeDeriv f x w) := by
  rw [form_metric_apply, SchwarzschildExterior.form_apply, timeChangeDeriv_apply,
    timeChangeDeriv_apply, hA, hB]
  have hs := Real.mul_self_sqrt hf
  simp only [timeChange, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  linear_combination ((x 1 - 2 * M) / x 1 * v 0 * w 0) * hs

/-- The change of the time maps the domain of the data with `r > 2M` into the exterior
Schwarzschild domain. -/
theorem timeChange_mem {D : Data} (hJM : ∀ r ∈ D.J, 2 * M < r) (T : ℝ → ℝ)
    {x : MinkowskiModel 3} (hx : x ∈ domain D) :
    timeChange T x ∈ SchwarzschildExterior.domain M := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [timeChange, Matrix.cons_val]
  · exact hJM _ hx.2.1
  · exact hx.2.2.1
  · exact hx.2.2.2

/-- **A new time with `T' = √f` exists** on a preconnected open set of times where `f` is
continuous: `T(t) = ∫_{t₀}^t √(f(s)) ds`. -/
theorem exists_hasDerivAt_sqrt {I : Set ℝ} (hI : IsOpen I) (hI' : IsPreconnected I)
    (hf : ContinuousOn f I) : ∃ T : ℝ → ℝ, ∀ t ∈ I, HasDerivAt T (Real.sqrt (f t)) t := by
  rcases I.eq_empty_or_nonempty with rfl | ⟨t₀, ht₀⟩
  · exact ⟨fun _ => 0, fun t ht => absurd ht (notMem_empty t)⟩
  have hc : ContinuousOn (fun s => Real.sqrt (f s)) I := Real.continuous_sqrt.comp_continuousOn hf
  refine ⟨fun t => ∫ s in t₀..t, Real.sqrt (f s), fun t ht => ?_⟩
  exact intervalIntegral.integral_hasDerivAt_right
    ((hc.mono (hI'.ordConnected.uIcc_subset ht₀ ht)).intervalIntegrable)
    (hc.stronglyMeasurableAtFilter hI t ht) (hc.continuousAt (hI.mem_nhds ht))

/-- **Birkhoff's theorem with the change of the time** (Landau–Lifshitz, §100). On a product
`I × J` of open intervals, a centrally symmetric vacuum field is the exterior Schwarzschild field
`−(1 − 2M/r) dT² + dr²/(1 − 2M/r) + r² dΩ²` in a new time `T(t)` with `T' = √f > 0`: the map
`(t, r, θ, φ) ↦ (T(t), r, θ, φ)` sends the domain into the region `r > 2M` and pulls the
Schwarzschild form back to the metric. -/
theorem birkhoff_timeChange (D : Data) (hI : IsPreconnected D.I) (hJ : IsPreconnected D.J)
    (hvac : ∀ x ∈ domain D, ∀ j k, ricciOf (metric D).coefficient x j k = 0) :
    ∃ M : ℝ, (∀ r ∈ D.J, 2 * M < r) ∧ ∃ f T : ℝ → ℝ,
      (∀ t ∈ D.I, 0 < f t ∧ HasDerivAt T (Real.sqrt (f t)) t) ∧
      ∀ x ∈ domain D, HasFDerivAt (timeChange T) (timeChangeDeriv f x) x ∧
        timeChange T x ∈ SchwarzschildExterior.domain M ∧
        ∀ v w, (metric D).form x v w = SchwarzschildExterior.form M (timeChange T x)
          (timeChangeDeriv f x v) (timeChangeDeriv f x w) := by
  obtain ⟨M, hM, f, hf, hfpos, hAB⟩ := birkhoff D hI hJ hvac
  obtain ⟨T, hT⟩ := exists_hasDerivAt_sqrt D.isOpen_I hI hf.continuousOn
  refine ⟨M, hM, f, T, fun t ht => ⟨hfpos t ht, hT t ht⟩, fun x hx => ⟨hasFDerivAt_timeChange
    (hT _ hx.1), timeChange_mem hM T hx, fun v w => ?_⟩⟩
  exact form_eq_timeChange D (hAB _ hx.1 _ hx.2.1).2 (hAB _ hx.1 _ hx.2.1).1 (hfpos _ hx.1).le v w

/-- **The Schwarzschild data are the exterior Schwarzschild field in a new time**: at a time of
`I`, the form of `schwarzschildData` is `SchwarzschildExterior.form M` at
`(T(t), r, θ, φ)` on the vectors `timeChangeDeriv f x v`. The identity is algebraic and holds for
every `T`, since the Schwarzschild form does not depend on the time; `timeChangeDeriv f x` is the
differential of the change of the time when `T' = √f` (`timeChange_schwarzschildData`). -/
theorem form_schwarzschildData {T : ℝ → ℝ} {x : MinkowskiModel 3} (hx : x 0 ∈ I)
    (v w : MinkowskiModel 3) :
    (metric (schwarzschildData M I J hI hJ hJM f hf hfpos)).form x v w =
      SchwarzschildExterior.form M (timeChange T x) (timeChangeDeriv f x v)
        (timeChangeDeriv f x w) :=
  form_eq_timeChange _ rfl rfl (hfpos _ hx).le v w

/-- **The pull-back of the exterior Schwarzschild field** (Landau–Lifshitz, §100): for a new time
with `T' = √f` on `I`, the change `(t, r, θ, φ) ↦ (T(t), r, θ, φ)` has the differential
`timeChangeDeriv f x` at every point of the domain of `schwarzschildData`, maps the domain into
the region `r > 2M`, and pulls `SchwarzschildExterior.form M` back to the metric of the data. -/
theorem timeChange_schwarzschildData {T : ℝ → ℝ}
    (hT : ∀ t ∈ I, HasDerivAt T (Real.sqrt (f t)) t) {x : MinkowskiModel 3}
    (hx : x ∈ domain (schwarzschildData M I J hI hJ hJM f hf hfpos)) :
    HasFDerivAt (timeChange T) (timeChangeDeriv f x) x ∧
      timeChange T x ∈ SchwarzschildExterior.domain M ∧
      ∀ v w, (metric (schwarzschildData M I J hI hJ hJM f hf hfpos)).form x v w =
        SchwarzschildExterior.form M (timeChange T x) (timeChangeDeriv f x v)
          (timeChangeDeriv f x w) :=
  ⟨hasFDerivAt_timeChange (hT _ hx.1),
    timeChange_mem (D := schwarzschildData M I J hI hJ hJM f hf hfpos)
      (fun r hr => (hJM r hr).2) T hx,
    fun v w => form_schwarzschildData hx.1 v w⟩

/-- **The constant `M` is determined by `B`**: if `B = r/(r − 2M₁) = r/(r − 2M₂)` on a nonempty
`I × J`, then `M₁ = M₂`. -/
theorem eq_of_B_eq (D : Data) (hI : D.I.Nonempty) (hJ : D.J.Nonempty) {M₁ M₂ : ℝ}
    (h₁ : ∀ t ∈ D.I, ∀ r ∈ D.J, D.B t r = r / (r - 2 * M₁))
    (h₂ : ∀ t ∈ D.I, ∀ r ∈ D.J, D.B t r = r / (r - 2 * M₂)) : M₁ = M₂ := by
  obtain ⟨t, ht⟩ := hI
  obtain ⟨r, hr⟩ := hJ
  have hb := D.B_pos t ht r hr
  have hr0 : r ≠ 0 := (D.J_pos hr).ne'
  have hd₁ : r - 2 * M₁ ≠ 0 := fun h => by
    rw [h₁ t ht r hr, h, div_zero] at hb
    exact lt_irrefl 0 hb
  have hd₂ : r - 2 * M₂ ≠ 0 := fun h => by
    rw [h₂ t ht r hr, h, div_zero] at hb
    exact lt_irrefl 0 hb
  have h := (h₁ t ht r hr).symm.trans (h₂ t ht r hr)
  rw [div_eq_div_iff hd₁ hd₂] at h
  have := mul_left_cancel₀ hr0 h
  linarith

/-- **Birkhoff's theorem returns the mass of the Schwarzschild data**: on a nonempty `I × J`,
every constant `M'` with `B = r/(r − 2M')` is the constant `M` of the data. -/
theorem mass_schwarzschildData (hIne : I.Nonempty) (hJne : J.Nonempty) {M' : ℝ}
    (h : ∀ t ∈ I, ∀ r ∈ J,
      (schwarzschildData M I J hI hJ hJM f hf hfpos).B t r = r / (r - 2 * M')) :
    M' = M :=
  eq_of_B_eq (schwarzschildData M I J hI hJ hJM f hf hfpos) hIne hJne h fun _ _ _ _ => rfl

end SchwarzschildData

/-! ### Regression instances -/

/-- The exterior Schwarzschild data of a mass `M ≥ 0`: all times, the radii `r > 2M` and
`f = 1`. -/
def exteriorData (hM : 0 ≤ M) : Data :=
  schwarzschildData M univ (Ioi (2 * M)) isOpen_univ isOpen_Ioi
    (fun r hr => ⟨by have : 2 * M < r := hr; linarith, hr⟩) (fun _ => 1) contDiffOn_const
    fun _ _ => one_pos

/-- The exterior Schwarzschild data are Ricci flat. -/
theorem ricciOf_exteriorData (hM : 0 ≤ M) {x : MinkowskiModel 3}
    (hx : x ∈ domain (exteriorData hM)) (j k : Fin 4) :
    ricciOf (metric (exteriorData hM)).coefficient x j k = 0 :=
  ricciOf_schwarzschildData hx j k

/-- The metric of the exterior data is the exterior Schwarzschild form. -/
theorem form_exteriorData (hM : 0 ≤ M) (x : MinkowskiModel 3) :
    (metric (exteriorData hM)).form x = SchwarzschildExterior.form M x := by
  ext v w
  refine (form_schwarzschildData (T := id) (mem_univ (x 0)) v w).trans ?_
  have hx : timeChange id x = x := by
    ext i
    fin_cases i <;> rfl
  have hv (u : MinkowskiModel 3) : timeChangeDeriv (fun _ => 1) x u = u := by
    ext i
    fin_cases i <;> simp [timeChangeDeriv_apply]
  rw [hx, hv, hv]

/-- **Regression: Birkhoff's theorem on the exterior Schwarzschild field.** The exterior data of
a mass `M ≥ 0` satisfy the hypotheses of `birkhoff`, and the constant it returns is `M`. -/
theorem exists_birkhoff_exteriorData (hM : 0 ≤ M) :
    ∃ M' : ℝ, M' = M ∧ (∀ r ∈ Ioi (2 * M), 2 * M' < r) ∧ ∃ f : ℝ → ℝ,
      ContDiffOn ℝ ∞ f univ ∧ (∀ t ∈ univ, 0 < f t) ∧
      ∀ t ∈ univ, ∀ r ∈ Ioi (2 * M), (exteriorData hM).B t r = r / (r - 2 * M') ∧
        (exteriorData hM).A t r = f t * ((r - 2 * M') / r) := by
  obtain ⟨M', hM', f, hf, hfpos, hAB⟩ := birkhoff (exteriorData hM) isPreconnected_univ
    isPreconnected_Ioi fun x hx => ricciOf_exteriorData hM hx
  refine ⟨M', mass_schwarzschildData ⟨0, mem_univ 0⟩ nonempty_Ioi
    fun t ht r hr => (hAB t ht r hr).1, hM', f, hf, hfpos, hAB⟩

/-- The data of a mass `M ≥ 0` with the nonconstant `f = eᵗ`: `ds² = −eᵗ(1 − 2M/r) dt² + ⋯`. -/
def expTimeData (hM : 0 ≤ M) : Data :=
  schwarzschildData M univ (Ioi (2 * M)) isOpen_univ isOpen_Ioi
    (fun r hr => ⟨by have : 2 * M < r := hr; linarith, hr⟩) Real.exp
    Real.contDiff_exp.contDiffOn fun t _ => Real.exp_pos t

/-- The data with `f = eᵗ` are Ricci flat. -/
theorem ricciOf_expTimeData (hM : 0 ≤ M) {x : MinkowskiModel 3}
    (hx : x ∈ domain (expTimeData hM)) (j k : Fin 4) :
    ricciOf (metric (expTimeData hM)).coefficient x j k = 0 :=
  ricciOf_schwarzschildData hx j k

/-- The new time `T = 2 e^{t/2}` has `T' = √(eᵗ)`. -/
theorem hasDerivAt_expTime (t : ℝ) :
    HasDerivAt (fun s => 2 * Real.exp (s / 2)) (Real.sqrt (Real.exp t)) t := by
  rw [← Real.exp_half]
  refine (((hasDerivAt_id' t).div_const 2).exp.const_mul 2).congr_deriv ?_
  ring

/-- **Regression: a nonconstant `f`.** The data with `f = eᵗ` are the exterior Schwarzschild
field in the time `T = 2 e^{t/2}`. -/
theorem form_expTimeData (hM : 0 ≤ M) (x v w : MinkowskiModel 3) :
    (metric (expTimeData hM)).form x v w =
      SchwarzschildExterior.form M (timeChange (fun s => 2 * Real.exp (s / 2)) x)
        (timeChangeDeriv Real.exp x v) (timeChangeDeriv Real.exp x w) :=
  form_schwarzschildData (mem_univ (x 0)) v w

/-- Birkhoff's theorem applies to the data with `f = eᵗ` and returns the mass `M`. -/
theorem exists_birkhoff_expTimeData (hM : 0 ≤ M) :
    ∃ M' : ℝ, M' = M ∧ (∀ r ∈ Ioi (2 * M), 2 * M' < r) ∧ ∃ f : ℝ → ℝ,
      ContDiffOn ℝ ∞ f univ ∧ (∀ t ∈ univ, 0 < f t) ∧
      ∀ t ∈ univ, ∀ r ∈ Ioi (2 * M), (expTimeData hM).B t r = r / (r - 2 * M') ∧
        (expTimeData hM).A t r = f t * ((r - 2 * M') / r) := by
  obtain ⟨M', hM', f, hf, hfpos, hAB⟩ := birkhoff (expTimeData hM) isPreconnected_univ
    isPreconnected_Ioi fun x hx => ricciOf_expTimeData hM hx
  refine ⟨M', mass_schwarzschildData ⟨0, mem_univ 0⟩ nonempty_Ioi
    fun t ht r hr => (hAB t ht r hr).1, hM', f, hf, hfpos, hAB⟩

end ProjectAinos.GeneralRelativity.SphericalAnsatz
