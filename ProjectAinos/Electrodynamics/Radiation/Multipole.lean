/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Radiation.Dipole
public import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic

/-!
# Quadrupole and magnetic-dipole radiation

Landau–Lifshitz, *The Classical Theory of Fields*, §71, for the slow family `slowCurrent κ k` of a
localized source (`Radiation.Dipole`). The moments of the current are
`Nᵢₗ(s) = ∫ yᵢ jₗ(s, 𝐲) d𝐲` (`currentMoment`).

* `quadrupoleMoment`: `D_ij = ∫ ρ (3yᵢyⱼ − |𝐲|²δᵢⱼ) d𝐲`. By the conservation of charge
  (`hasDerivAt_quadrupoleMoment`) `Ḋ_ij = 3(N_ji + N_ij) − 2δᵢⱼ Σₗ Nₗₗ` (`quadrupoleRate`), and
  `deriv_deriv_deriv_quadrupoleMoment`: `D'''_ij` is the same combination of the moments
  `Mᵢₗ = ∫ yᵢ ∂ₛ²jₗ d𝐲` of the second time derivative.
* `magneticMoment`: `𝐦 = ½ ∫ 𝐲 × 𝐣 d𝐲`, with the cross product `cross3` of `ℝ³`;
  `deriv_deriv_magneticMoment`: `𝐦̈ = ½ ∫ 𝐲 × ∂ₛ²𝐣 d𝐲`, whose components are
  `½(M₁₂ − M₂₁)`, … (`norm_sq_integral_cross3`).
* The first correction to the amplitude is `𝐜(n) = Σₖ nₖ 𝐰ₖ` with `(𝐰ₖ)ᵢ = Mₖᵢ`
  (`firstCorrection_eq_sum`, `integral_coord_smul_apply`), and the second and fourth moments of
  the sphere give `integral_transverse_sq_sum`:
  `∫ (|𝐜|² − ⟨n, 𝐜⟩²) dσ = (4π/3) Σ M² − (4π/15)(Σ M² + (tr M)² + tr M²)`, which is
  `4π[(1/180) Σ (D''')² + (2/3)|𝐦̈|²]` by `quadrupole_magnetic_identity`: the symmetric part of
  `M` is `Q'''/2` with `Q = ∫ ρ yᵢyₖ`, the antisymmetric part is `εᵢₖₗ m̈ₗ`, and the cross term of
  the two parts vanishes.
* `power_sub_le` (71.5): **if `𝐝̈(κu) = 0`, the slow family radiates
  `κ⁶ (1/4π)[(1/180) Σᵢⱼ (D'''ᵢⱼ)² + (2/3)|𝐦̈|²]` up to `(4π/9) M² a⁹ (4 + a) κ⁷`**, the units
  turning `1/(180c⁵)` and `2/(3c³)` into `1/(4π·180)` and `2/(3·4π)`.
* `power_general`: without the hypothesis on `𝐝̈`, the radiated power has in addition the dipole
  term `κ⁴|𝐝̈|²/(6π)` and the cross term `(κ⁶/16π²) ∫ (⟨𝐝̈, 𝐪⟩ − ⟨n, 𝐝̈⟩⟨n, 𝐪⟩) dσ` of the dipole
  amplitude with the second correction `𝐪(n) = ∫ ⟨n, 𝐲⟩² ∂ₛ³𝐣 d𝐲` (`secondCorrection`), up to
  `O(κ⁷)`, by Taylor's formula to the third order (`norm_taylor_three_le`).
* An instance: `oscillatingQuadrupole`, `ρ = cos s ∂₁²χ` and `𝐣 = sin s ∂₁χ e₁` for the bump `χ`.
  It has no dipole moment (`dipoleMoment_oscillatingQuadrupole`), `D'''₁₁(s) = 4 sin s ∫ χ`
  (`deriv_deriv_deriv_quadrupoleMoment_oscillatingQuadrupole`, nonzero at `s = π/2`), `𝐦̈ = 0`,
  and by `power_oscillatingQuadrupole` its slow family radiates
  `κ⁶ sin²(κu)(∫ χ)²/(30π) + O(κ⁷)`.

The indices are those of `Fin 3`: the axis `1` of the text is the index `0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Real Filter
open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics.Radiation

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Sphere SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The moments of the current -/

/-- The moments `Nᵢₗ(s) = ∫ yᵢ Kˡ(s, 𝐲) d𝐲` of the spatial components of a current. -/
def currentMoment (K : Spacetime → Spacetime) (s : ℝ) (i l : Fin 3) : ℝ :=
  ∫ y, K (vector s y) l.succ * y i

/-- The products `Kᵘ(s, 𝐲) yᵢ` are integrable for a current supported in a ball. -/
theorem integrable_component_mul_coord {K : Spacetime → Spacetime} {a : ℝ} (hK : Continuous K)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → K (vector t x) = 0) (s : ℝ) (μ : Fin 4) (i : Fin 3) :
    Integrable fun y : E3 => K (vector s y) μ * y i :=
  integrable_of_ballSupport (a := a) (((continuous_apply μ).comp (hK.comp
    (continuous_vector_of_continuous continuous_const continuous_id))).mul (by fun_prop))
    fun y hy => by simp [hs s y hy]

/-- The time derivative of the moments: `Ṅᵢₗ = ∫ yᵢ ∂ₛjₗ d𝐲`. -/
theorem hasDerivAt_currentMoment {K : Spacetime → Spacetime} {a : ℝ} (hK : ContDiff ℝ ∞ K)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → K (vector t x) = 0) (i l : Fin 3) (s : ℝ) :
    HasDerivAt (fun s => currentMoment K s i l) (currentMoment (currentRate K) s i l) s := by
  have h := hasDerivAt_integral_smul hK hs (w := fun y : E3 => y i) (by fun_prop) l.succ s
  simp only [smul_eq_mul] at h
  exact h

/-- The quadrupole moment `D_ij(s) = ∫ ρ(s, 𝐲)(3yᵢyⱼ − |𝐲|²δᵢⱼ) d𝐲` (Landau–Lifshitz, §41). -/
def quadrupoleMoment (k : Spacetime → Spacetime) (s : ℝ) (i j : Fin 3) : ℝ :=
  ∫ y, k (vector s y) 0 * (3 * (y i * y j) - ‖y‖ ^ 2 * if i = j then 1 else 0)

/-- The combination `3(N_ji + N_ij) − 2δᵢⱼ Σₗ Nₗₗ` of current moments: the time derivative of the
quadrupole moment. -/
def quadrupoleRate (N : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  3 * (N j i + N i j) - if i = j then 2 * ∑ l, N l l else 0

/-- **The conservation of charge for the quadrupole moment**:
`Ḋ_ij = ∫ (3(jᵢyⱼ + yᵢjⱼ) − 2δᵢⱼ ⟨𝐲, 𝐣⟩) d𝐲 = 3(N_ji + N_ij) − 2δᵢⱼ Σₗ Nₗₗ`. -/
theorem hasDerivAt_quadrupoleMoment {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hdiv : ∀ v, divergence4 k v = 0)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0) (i j : Fin 3) (s : ℝ) :
    HasDerivAt (fun s => quadrupoleMoment k s i j) (quadrupoleRate (currentMoment k s) i j) s := by
  set δ : ℝ := if i = j then 1 else 0 with hδ
  have hw : Continuous fun y : E3 => 3 * (y i * y j) - ‖y‖ ^ 2 * δ := by fun_prop
  have h := hasDerivAt_integral_smul hk hs hw 0 s
  simp only [smul_eq_mul] at h
  convert h using 1
  · rfl
  have hp : ∀ y : E3, HasFDerivAt (fun y : E3 => y i * y j)
      (y i • EuclideanSpace.proj j + y j • EuclideanSpace.proj i) y := fun y => by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.fun_mul
      (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt (x := y)
  have hW : ∀ y : E3, HasFDerivAt (fun y : E3 => 3 * (y i * y j) - ‖y‖ ^ 2 * δ)
      ((3 : ℝ) • (y i • EuclideanSpace.proj j + y j • EuclideanSpace.proj i) -
        δ • (2 • (innerSL ℝ y).comp (ContinuousLinearMap.id ℝ E3))) y := fun y =>
    ((hp y).const_mul 3).fun_sub ((hasFDerivAt_id y).norm_sq.mul_const δ)
  have hpc : ContDiff ℝ 1 fun y : E3 => y i * y j := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.mul
      (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff (n := 1)
  have hc : ContDiff ℝ 1 fun y : E3 => 3 * (y i * y j) - ‖y‖ ^ 2 * δ :=
    (contDiff_const.mul hpc).sub ((contDiff_norm_sq ℝ).mul contDiff_const)
  have h2 := integral_mul_currentRate_zero hk hdiv hs hc s
  have hpt : ∀ y : E3, fderiv ℝ (fun y : E3 => 3 * (y i * y j) - ‖y‖ ^ 2 * δ) y
        (space (k (vector s y))) =
      3 * (k (vector s y) i.succ * y j + k (vector s y) j.succ * y i) -
        δ * (2 * ∑ l, k (vector s y) l.succ * y l) := fun y => by
    rw [(hW y).fderiv]
    simp [inner_eq_sum_mul_fin_three, space_apply, Fin.sum_univ_three]
    ring
  simp_rw [hpt] at h2
  rw [show (fun y => currentRate k (vector s y) 0 * (3 * (y i * y j) - ‖y‖ ^ 2 * δ)) =
    fun y => (3 * (y i * y j) - ‖y‖ ^ 2 * δ) * currentRate k (vector s y) 0 from
      funext fun y => mul_comm _ _, h2]
  have hI := integrable_component_mul_coord hk.continuous hs s
  have i1 : Integrable fun y : E3 =>
      3 * (k (vector s y) i.succ * y j + k (vector s y) j.succ * y i) :=
    ((hI _ _).add (hI _ _)).const_mul 3
  have i2 : Integrable fun y : E3 => δ * (2 * ∑ l, k (vector s y) l.succ * y l) :=
    ((integrable_finsetSum _ fun l _ => hI l.succ l).const_mul 2).const_mul δ
  rw [integral_sub i1 i2, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_add (hI _ _) (hI _ _), integral_finsetSum _ fun l _ => hI l.succ l]
  simp only [quadrupoleRate, currentMoment, hδ]
  split_ifs <;> ring

/-- The time derivative of `quadrupoleRate (currentMoment K s) i j`. -/
theorem hasDerivAt_quadrupoleRate {K : Spacetime → Spacetime} {a : ℝ} (hK : ContDiff ℝ ∞ K)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → K (vector t x) = 0) (i j : Fin 3) (s : ℝ) :
    HasDerivAt (fun s => quadrupoleRate (currentMoment K s) i j)
      (quadrupoleRate (currentMoment (currentRate K) s) i j) s := by
  have h := fun i l => hasDerivAt_currentMoment hK hs i l s
  unfold quadrupoleRate
  split_ifs
  · exact (((h j i).fun_add (h i j)).const_mul 3).fun_sub
      ((HasDerivAt.fun_sum fun l _ => h l l).const_mul 2)
  · simpa using ((h j i).fun_add (h i j)).const_mul 3

/-- **The third derivative of the quadrupole moment**:
`D'''_ij = 3(Mⱼᵢ + Mᵢⱼ) − 2δᵢⱼ Σₗ Mₗₗ` with the moments `Mᵢₗ = ∫ yᵢ ∂ₛ²jₗ d𝐲`. -/
theorem deriv_deriv_deriv_quadrupoleMoment {k : Spacetime → Spacetime} {a : ℝ}
    (hk : ContDiff ℝ ∞ k) (hdiv : ∀ v, divergence4 k v = 0)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0) (i j : Fin 3) (s : ℝ) :
    deriv (deriv (deriv fun s => quadrupoleMoment k s i j)) s =
      quadrupoleRate (currentMoment (currentRate (currentRate k)) s) i j := by
  have hs1 := currentRate_eq_zero_of_ballSupport hs
  have h1 : deriv (fun s => quadrupoleMoment k s i j) =
      fun s => quadrupoleRate (currentMoment k s) i j :=
    funext fun s => (hasDerivAt_quadrupoleMoment hk hdiv hs i j s).deriv
  have h2 : deriv (fun s => quadrupoleRate (currentMoment k s) i j) =
      fun s => quadrupoleRate (currentMoment (currentRate k) s) i j :=
    funext fun s => (hasDerivAt_quadrupoleRate hk hs i j s).deriv
  rw [h1, h2]
  exact (hasDerivAt_quadrupoleRate (contDiff_currentRate hk) hs1 i j s).deriv

/-! ### The magnetic moment -/

/-- The cross product `x × z` of `ℝ³`. -/
def cross3 (x z : E3) : E3 := WithLp.toLp 2 (crossProduct (WithLp.ofLp x) (WithLp.ofLp z))

/-- The first component of the cross product. -/
theorem cross3_apply_zero (x z : E3) : cross3 x z 0 = x 1 * z 2 - x 2 * z 1 := by
  simp [cross3, cross_apply]

/-- The second component of the cross product. -/
theorem cross3_apply_one (x z : E3) : cross3 x z 1 = x 2 * z 0 - x 0 * z 2 := by
  simp [cross3, cross_apply]

/-- The third component of the cross product. -/
theorem cross3_apply_two (x z : E3) : cross3 x z 2 = x 0 * z 1 - x 1 * z 0 := by
  simp [cross3, cross_apply]

/-- The cross product with `0` vanishes. -/
theorem cross3_zero_right (x : E3) : cross3 x 0 = 0 := by
  simp [cross3]

/-- The cross product is continuous. -/
theorem continuous_cross3 : Continuous fun p : E3 × E3 => cross3 p.1 p.2 := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fin_cases i <;> simp [cross_apply] <;> fun_prop

/-- The linear map `z ↦ x × z`. -/
def crossLeft (x : E3) : E3 →L[ℝ] E3 := LinearMap.toContinuousLinearMap
  { toFun := cross3 x
    map_add' := fun z w => by simp [cross3]
    map_smul' := fun c z => by simp [cross3] }

/-- The linear map `z ↦ x × z` applied to `z`. -/
theorem crossLeft_apply (x z : E3) : crossLeft x z = cross3 x z := rfl

/-- The magnetic moment `𝐦(s) = ½ ∫ 𝐲 × 𝐣(s, 𝐲) d𝐲` (Landau–Lifshitz, §44). -/
def magneticMoment (k : Spacetime → Spacetime) (s : ℝ) : E3 :=
  (2 : ℝ)⁻¹ • ∫ y, cross3 y (space (k (vector s y)))

/-- The time derivative of `∫ 𝐲 × 𝐊(s, 𝐲) d𝐲` is `∫ 𝐲 × ∂ₛ𝐊(s, 𝐲) d𝐲`. -/
theorem hasDerivAt_integral_cross3 {K : Spacetime → Spacetime} {a : ℝ} (hK : ContDiff ℝ ∞ K)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → K (vector t x) = 0) (s : ℝ) :
    HasDerivAt (fun s => ∫ y, cross3 y (space (K (vector s y))))
      (∫ y, cross3 y (space (currentRate K (vector s y)))) s := by
  have hK1 : Differentiable ℝ K := hK.differentiable (by simp)
  have hc : ∀ {L : Spacetime → Spacetime}, ContDiff ℝ ∞ L →
      Continuous (Function.uncurry fun s y => cross3 y (space (L (vector s y)))) := fun hL =>
    continuous_cross3.comp (continuous_snd.prodMk
      (space.continuous.comp (continuous_comp_vector_slice hL.continuous)))
  refine hasDerivAt_integral_of_ballSupport (a := a) (hc hK) (hc (contDiff_currentRate hK))
    (fun s y hy => by simp [hs s y hy, cross3_zero_right])
    (fun s y hy => by simp [currentRate_eq_zero_of_ballSupport hs s y hy, cross3_zero_right])
    (fun s y => ?_) s
  have h := (crossLeft y).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_space_current_vector hK1 s y)
  simpa only [Function.comp_def, crossLeft_apply] using h

/-- The second derivative of the magnetic moment: `𝐦̈(s) = ½ ∫ 𝐲 × ∂ₛ²𝐣(s, 𝐲) d𝐲`. -/
theorem deriv_deriv_magneticMoment {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0) (s : ℝ) :
    deriv (deriv (magneticMoment k)) s =
      (2 : ℝ)⁻¹ • ∫ y, cross3 y (space (currentRate (currentRate k) (vector s y))) := by
  have h1 : deriv (magneticMoment k) =
      fun s => (2 : ℝ)⁻¹ • ∫ y, cross3 y (space (currentRate k (vector s y))) :=
    funext fun s => ((hasDerivAt_integral_cross3 hk hs s).const_smul (2 : ℝ)⁻¹).deriv
  rw [h1]
  exact ((hasDerivAt_integral_cross3 (contDiff_currentRate hk)
    (currentRate_eq_zero_of_ballSupport hs) s).const_smul (2 : ℝ)⁻¹).deriv

/-- The components of `∫ 𝐲 × 𝐊 d𝐲` are the antisymmetric parts `Nᵢₗ − Nₗᵢ` of the moments. -/
theorem norm_sq_integral_cross3 {K : Spacetime → Spacetime} {a : ℝ} (hK : Continuous K)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → K (vector t x) = 0) (s : ℝ) :
    ‖∫ y, cross3 y (space (K (vector s y)))‖ ^ 2 =
      (currentMoment K s 1 2 - currentMoment K s 2 1) ^ 2 +
        (currentMoment K s 2 0 - currentMoment K s 0 2) ^ 2 +
        (currentMoment K s 0 1 - currentMoment K s 1 0) ^ 2 := by
  have hint : Integrable fun y => cross3 y (space (K (vector s y))) :=
    integrable_of_ballSupport (a := a) (continuous_cross3.comp (continuous_id.prodMk
      (space.continuous.comp (hK.comp (continuous_vector_of_continuous continuous_const
        continuous_id))))) fun y hy => by simp [hs s y hy, cross3_zero_right]
  have hI := integrable_component_mul_coord hK hs s
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three,
    eval_integral_piLp (fun i => hint.eval_piLp i), eval_integral_piLp (fun i => hint.eval_piLp i),
    eval_integral_piLp (fun i => hint.eval_piLp i)]
  have e0 : ∀ y : E3, cross3 y (space (K (vector s y))) 0 =
      K (vector s y) (2 : Fin 3).succ * y 1 - K (vector s y) (1 : Fin 3).succ * y 2 := fun y => by
    rw [cross3_apply_zero, space_apply, space_apply]; ring
  have e1 : ∀ y : E3, cross3 y (space (K (vector s y))) 1 =
      K (vector s y) (0 : Fin 3).succ * y 2 - K (vector s y) (2 : Fin 3).succ * y 0 := fun y => by
    rw [cross3_apply_one, space_apply, space_apply]; ring
  have e2 : ∀ y : E3, cross3 y (space (K (vector s y))) 2 =
      K (vector s y) (1 : Fin 3).succ * y 0 - K (vector s y) (0 : Fin 3).succ * y 1 := fun y => by
    rw [cross3_apply_two, space_apply, space_apply]; ring
  simp_rw [e0, e1, e2]
  rw [integral_sub (hI _ 1) (hI _ 2), integral_sub (hI _ 2) (hI _ 0),
    integral_sub (hI _ 0) (hI _ 1)]
  rfl

/-! ### The angular integral -/

/-- The expansion `|v|² − ⟨n, v⟩²` at `v = κc + e`. -/
theorem transverse_sq_expand_smul_add (n c e : E3) (κ : ℝ) :
    ‖κ • c + e‖ ^ 2 - inner ℝ n (κ • c + e) ^ 2 =
      κ ^ 2 * (‖c‖ ^ 2 - inner ℝ n c ^ 2) +
        (2 * κ * (inner ℝ c e - inner ℝ n c * inner ℝ n e) + (‖e‖ ^ 2 - inner ℝ n e ^ 2)) := by
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm e c]
  ring

/-- The first correction as a combination `𝐜(n) = Σₗ nₗ 𝐰ₗ` of the vectors
`𝐰ₗ = ∫ yₗ ∂ₛ²𝐣(s, 𝐲) d𝐲`. -/
theorem firstCorrection_eq_sum {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0) (s : ℝ) (n : E3) :
    firstCorrection k s n = ∑ l : Fin 3, inner ℝ n (EuclideanSpace.single l 1) •
      ∫ y, y l • space (currentRate (currentRate k) (vector s y)) := by
  have hs2 := currentRate_eq_zero_of_ballSupport (currentRate_eq_zero_of_ballSupport hs)
  have hint : ∀ l : Fin 3, Integrable fun y : E3 =>
      y l • space (currentRate (currentRate k) (vector s y)) := fun l =>
    integrable_of_ballSupport (a := a) ((by fun_prop : Continuous fun y : E3 => y l).fun_smul
      (space.continuous.comp ((contDiff_currentRate (contDiff_currentRate hk)).continuous.comp
        (continuous_vector_of_continuous continuous_const continuous_id))))
      fun y hy => by simp [hs2 s y hy]
  simp_rw [← integral_smul]
  rw [← integral_finsetSum (f := fun l y => inner ℝ n (EuclideanSpace.single l 1) •
    (y l • space (currentRate (currentRate k) (vector s y)))) _ fun l _ => by
      exact (hint l).smul (inner ℝ n (EuclideanSpace.single l 1)), firstCorrection]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [inner_eq_sum_mul_fin_three n y, Finset.sum_smul, smul_smul,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul]

/-- The components of `𝐰ₗ = ∫ yₗ 𝐊 d𝐲` are the moments `Nₗᵢ`. -/
theorem integral_coord_smul_apply {K : Spacetime → Spacetime} {a : ℝ} (hK : Continuous K)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → K (vector t x) = 0) (s : ℝ) (l i : Fin 3) :
    (∫ y, y l • space (K (vector s y))) i = currentMoment K s l i := by
  have hint : Integrable fun y : E3 => y l • space (K (vector s y)) :=
    integrable_of_ballSupport (a := a) ((by fun_prop : Continuous fun y : E3 => y l).fun_smul
      (space.continuous.comp (hK.comp
        (continuous_vector_of_continuous continuous_const continuous_id))))
      fun y hy => by simp [hs s y hy]
  rw [eval_integral_piLp (fun j => hint.eval_piLp j)]
  simp [currentMoment, space_apply, mul_comm]

/-- **The angular integral of the first correction**: for `𝐜(n) = Σₗ nₗ 𝐰ₗ` with
`𝐰ₗ = (Aₗᵢ)ᵢ`, `∫ (|𝐜|² − ⟨n, 𝐜⟩²) dσ = (4π/3) Σ Aₗᵢ² − (4π/15)(Σ Aₗᵢ² + (Σ Aₗₗ)² + Σ AₘₗAₗₘ)`,
from the second and fourth moments of the sphere. -/
theorem integral_transverse_sq_sum (w : Fin 3 → E3) :
    ∫ n : sphere (0 : E3) 1,
      (‖∑ l : Fin 3, inner ℝ (n : E3) (EuclideanSpace.single l 1) • w l‖ ^ 2 -
        inner ℝ (n : E3) (∑ l : Fin 3, inner ℝ (n : E3) (EuclideanSpace.single l 1) • w l) ^ 2)
      ∂sphereMeasure =
      4 * π / 3 * ∑ l : Fin 3, ∑ i : Fin 3, w l i ^ 2 -
        4 * π / 15 * (∑ l : Fin 3, ∑ i : Fin 3, w l i ^ 2 + (∑ l : Fin 3, w l l) ^ 2 +
          ∑ l : Fin 3, ∑ m : Fin 3, w m l * w l m) := by
  have h1 : ∀ n : E3, ‖∑ l : Fin 3, inner ℝ n (EuclideanSpace.single l 1) • w l‖ ^ 2 =
      ∑ l : Fin 3, ∑ m : Fin 3, inner ℝ n (EuclideanSpace.single l 1) *
        inner ℝ n (EuclideanSpace.single m 1) * inner ℝ (w l) (w m) := fun n => by
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact Finset.sum_congr rfl fun m _ => by rw [real_inner_comm (w l) (w m)]; ring
  have h2 : ∀ n : E3, inner ℝ n (∑ l : Fin 3, inner ℝ n (EuclideanSpace.single l 1) • w l) ^ 2 =
      ∑ l : Fin 3, ∑ m : Fin 3, inner ℝ n (EuclideanSpace.single l 1) * inner ℝ n (w l) *
        inner ℝ n (EuclideanSpace.single m 1) * inner ℝ n (w m) := fun n => by
    rw [inner_sum, sq, Finset.sum_mul_sum]
    simp only [real_inner_smul_right]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by ring
  simp_rw [h1, h2]
  rw [integral_sub (integrable_of_continuous (by fun_prop)) (integrable_of_continuous
      (by fun_prop)), integral_finsetSum _ fun l _ => integrable_of_continuous (by fun_prop),
    integral_finsetSum _ fun l _ => integrable_of_continuous (by fun_prop)]
  have hA : ∀ l : Fin 3, ∫ n : sphere (0 : E3) 1, ∑ m : Fin 3,
      inner ℝ (n : E3) (EuclideanSpace.single l 1) * inner ℝ (n : E3) (EuclideanSpace.single m 1) *
        inner ℝ (w l) (w m) ∂sphereMeasure =
      ∑ m : Fin 3, 4 * π / 3 * inner ℝ (EuclideanSpace.single l (1 : ℝ))
        (EuclideanSpace.single m 1) * inner ℝ (w l) (w m) := fun l => by
    rw [integral_finsetSum _ fun m _ => integrable_of_continuous (by fun_prop)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_mul_const, integral_inner_mul_inner]
  have hB : ∀ l : Fin 3, ∫ n : sphere (0 : E3) 1, ∑ m : Fin 3,
      inner ℝ (n : E3) (EuclideanSpace.single l 1) * inner ℝ (n : E3) (w l) *
        inner ℝ (n : E3) (EuclideanSpace.single m 1) * inner ℝ (n : E3) (w m) ∂sphereMeasure =
      ∑ m : Fin 3, 4 * π / 15 *
        (inner ℝ (EuclideanSpace.single l (1 : ℝ)) (w l) *
            inner ℝ (EuclideanSpace.single m (1 : ℝ)) (w m) +
          inner ℝ (EuclideanSpace.single l (1 : ℝ)) (EuclideanSpace.single m 1) *
            inner ℝ (w l) (w m) +
          inner ℝ (EuclideanSpace.single l (1 : ℝ)) (w m) *
            inner ℝ (w l) (EuclideanSpace.single m 1)) := fun l => by
    rw [integral_finsetSum _ fun m _ => integrable_of_continuous (by fun_prop)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_inner_mul_inner_mul_inner_mul_inner]
  rw [Finset.sum_congr rfl fun l _ => hA l, Finset.sum_congr rfl fun l _ => hB l]
  simp only [Fin.sum_univ_three, inner_eq_sum_mul_fin_three]
  simp
  ring

/-- The identity of the angular algebra (also checked with SymPy): with
`D_ij = 3(Aⱼᵢ + Aᵢⱼ) − 2δᵢⱼ Σ Aₗₗ` and `𝐦 = ½(A₁₂ − A₂₁, A₂₀ − A₀₂, A₀₁ − A₁₀)`,
`(1/3) Σ A² − (1/15)(Σ A² + (tr A)² + tr A²) = (1/180) Σ D² + (2/3)|𝐦|²`. -/
theorem quadrupole_magnetic_identity (A : Fin 3 → Fin 3 → ℝ) :
    (∑ l : Fin 3, ∑ i : Fin 3, A l i ^ 2) / 3 -
        (∑ l : Fin 3, ∑ i : Fin 3, A l i ^ 2 + (∑ l : Fin 3, A l l) ^ 2 +
          ∑ l : Fin 3, ∑ m : Fin 3, A m l * A l m) / 15 =
      1 / 180 * ∑ i : Fin 3, ∑ j : Fin 3, quadrupoleRate A i j ^ 2 +
        2 / 3 * ((2 : ℝ)⁻¹ ^ 2 *
          ((A 1 2 - A 2 1) ^ 2 + (A 2 0 - A 0 2) ^ 2 + (A 0 1 - A 1 0) ^ 2)) := by
  simp only [Fin.sum_univ_three, quadrupoleRate]
  simp
  ring

/-! ### Quadrupole and magnetic-dipole radiation -/

/-- The angular density of the slow family when `𝐝̈(κu) = 0`: it is
`(κ²/4π)² κ² (|𝐜|² − ⟨n, 𝐜⟩²)` with the first correction `𝐜(n)`, up to
`(κ²/4π)² κ³ M² V² a³ (4 + a)`, where `V = (4π/3)a³`. -/
theorem abs_angularIntensity_slowCurrent_sub_le_of_dipole {k : Spacetime → Spacetime} {a M : ℝ}
    {N : ℕ} (hk : LocalizedSource k a M N) (hN : 3 ≤ N) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (u : ℝ) (hd : ∫ y, space (currentRate k (vector (κ * u) y)) = 0) {n : E3} (hn : ‖n‖ = 1) :
    |angularIntensity (slowCurrent κ k) u n - (κ ^ 2 / (4 * π)) ^ 2 *
        (κ ^ 2 * (‖firstCorrection k (κ * u) n‖ ^ 2 -
          inner ℝ n (firstCorrection k (κ * u) n) ^ 2))| ≤
      (κ ^ 2 / (4 * π)) ^ 2 * (κ ^ 3 * (M ^ 2 * (4 * π / 3 * a ^ 3) ^ 2 * a ^ 3 * (4 + a))) := by
  set c := firstCorrection k (κ * u) n
  set V := 4 * π / 3 * a ^ 3 with hV
  set e := slowAmplitude k κ (κ * u) n - κ • c
  have hM := hk.bound_nonneg
  have ha := hk.radius_nonneg
  have hV0 : 0 ≤ V := by positivity
  have hcγ : ‖c‖ ≤ a * M * V := norm_firstCorrection_le hk (by omega) _ hn
  have heε : ‖e‖ ≤ M * κ ^ 2 * a ^ 2 * V := by
    have h := norm_slowAmplitude_sub_le hk hN κ (κ * u) hn
    rwa [hd, sub_zero] at h
  have hΦ : slowAmplitude k κ (κ * u) n = κ • c + e := by
    simp only [e]
    abel
  rw [angularIntensity_slowCurrent hk.contDiff hk.support, hΦ, transverse_sq_expand_smul_add,
    show ∀ X R : ℝ, (κ ^ 2 / (4 * π)) ^ 2 * (X + R) - (κ ^ 2 / (4 * π)) ^ 2 * X =
      (κ ^ 2 / (4 * π)) ^ 2 * R from fun X R => by ring,
    abs_mul, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 := abs_transverse_inner_le (v := c) (w := e) hn
  have h2 := abs_transverse_sq_le (v := e) hn
  have hce : ‖c‖ * ‖e‖ ≤ a * M * V * (M * κ ^ 2 * a ^ 2 * V) :=
    mul_le_mul hcγ heε (norm_nonneg _) (by positivity)
  have he2 : ‖e‖ ^ 2 ≤ (M * κ ^ 2 * a ^ 2 * V) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) heε 2
  have hk4 : κ ^ 4 ≤ κ ^ 3 := pow_le_pow_of_le_one hκ0.le hκ1 (by norm_num)
  calc _ ≤ |2 * κ * (inner ℝ c e - inner ℝ n c * inner ℝ n e)| + |‖e‖ ^ 2 - inner ℝ n e ^ 2| :=
        abs_add_le _ _
    _ ≤ 2 * κ * (2 * (a * M * V * (M * κ ^ 2 * a ^ 2 * V))) + (M * κ ^ 2 * a ^ 2 * V) ^ 2 := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * κ)]
        gcongr
        · exact h1.trans (by linarith)
        · exact h2.trans he2
    _ = M ^ 2 * V ^ 2 * (4 * κ ^ 3 * a ^ 3 + κ ^ 4 * a ^ 4) := by ring
    _ ≤ M ^ 2 * V ^ 2 * (4 * κ ^ 3 * a ^ 3 + κ ^ 3 * a ^ 4) := by gcongr
    _ = _ := by ring

/-- **The quadrupole and magnetic-dipole radiation** (Landau–Lifshitz, §71, (71.5)): if the
second derivative of the dipole moment vanishes at the slow time `κu` (for instance for charges
with one ratio `e/m`), the slow family radiates
`I = κ⁶ (1/4π) [(1/180) Σᵢⱼ (D'''ᵢⱼ)² + (2/3)|𝐦̈|²]` at `s = κu`, up to
`(4π/9) M² a⁹ (4 + a) κ⁷`. The amplitude to the order `κ³` is `(κ³/4π) Σₖ nₖ 𝐰ₖ` with
`(𝐰ₖ)ᵢ = Mₖᵢ = ∫ yₖ ∂ₛ²jᵢ d𝐲`, whose symmetric part is `Q'''/2` and antisymmetric part
`εₖᵢₗ m̈ₗ`. -/
theorem power_sub_le {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ}
    (hk : LocalizedSource k a M N) (hN : 3 ≤ N) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (u : ℝ)
    (hd : deriv (deriv (dipoleMoment k)) (κ * u) = 0) :
    |radiatedPower (slowCurrent κ k) u - κ ^ 6 * (1 / (4 * π)) *
        (1 / 180 * ∑ i : Fin 3, ∑ j : Fin 3,
            deriv (deriv (deriv fun s => quadrupoleMoment k s i j)) (κ * u) ^ 2 +
          2 / 3 * ‖deriv (deriv (magneticMoment k)) (κ * u)‖ ^ 2)| ≤
      4 * π / 9 * M ^ 2 * a ^ 9 * (4 + a) * κ ^ 7 := by
  have hc2 : ContDiff ℝ ∞ (currentRate (currentRate k)) :=
    contDiff_currentRate (contDiff_currentRate hk.contDiff)
  have hs2 := currentRate_eq_zero_of_ballSupport (currentRate_eq_zero_of_ballSupport hk.support)
  have hd' : ∫ y, space (currentRate k (vector (κ * u) y)) = 0 := by
    rwa [deriv_deriv_dipoleMoment hk.contDiff hk.conserved hk.support] at hd
  simp only [deriv_deriv_deriv_quadrupoleMoment hk.contDiff hk.conserved hk.support,
    deriv_deriv_magneticMoment hk.contDiff hk.support]
  rw [norm_smul, mul_pow, norm_sq_integral_cross3 hc2.continuous hs2, Real.norm_eq_abs, sq_abs,
    ← quadrupole_magnetic_identity, radiatedPower_eq_integral]
  set A := currentMoment (currentRate (currentRate k)) (κ * u) with hA
  set c := firstCorrection k (κ * u)
  set Φ := slowAmplitude k κ (κ * u)
  set C₀ := (κ ^ 2 / (4 * π)) ^ 2 with hC₀
  set main : E3 → ℝ := fun n => C₀ * (κ ^ 2 * (‖c n‖ ^ 2 - inner ℝ n (c n) ^ 2)) with hmain
  have hcΦ : Continuous Φ := continuous_slowAmplitude hk.contDiff hk.support κ _
  have hcc : Continuous c := continuous_firstCorrection hk.contDiff hk.support _
  have hAP : (fun n : sphere (0 : E3) 1 => angularIntensity (slowCurrent κ k) u n) =
      fun n : sphere (0 : E3) 1 => C₀ * (‖Φ (n : E3)‖ ^ 2 - inner ℝ (n : E3) (Φ n) ^ 2) :=
    funext fun n => angularIntensity_slowCurrent hk.contDiff hk.support κ u n
  have hint1 : Integrable (fun n : sphere (0 : E3) 1 => angularIntensity (slowCurrent κ k) u n)
      sphereMeasure := by
    rw [hAP]
    exact integrable_of_continuous (by fun_prop)
  have hint2 : Integrable (fun n : sphere (0 : E3) 1 => main n) sphereMeasure :=
    integrable_of_continuous (by fun_prop)
  have hmain_int : ∫ n : sphere (0 : E3) 1, main n ∂sphereMeasure =
      κ ^ 6 * (1 / (4 * π)) * ((∑ l : Fin 3, ∑ i : Fin 3, A l i ^ 2) / 3 -
        (∑ l : Fin 3, ∑ i : Fin 3, A l i ^ 2 + (∑ l : Fin 3, A l l) ^ 2 +
          ∑ l : Fin 3, ∑ m : Fin 3, A m l * A l m) / 15) := by
    simp only [hmain]
    rw [integral_const_mul, integral_const_mul]
    have hcs : ∀ n : sphere (0 : E3) 1, c n = ∑ l : Fin 3,
        inner ℝ (n : E3) (EuclideanSpace.single l 1) •
          ∫ y, y l • space (currentRate (currentRate k) (vector (κ * u) y)) := fun n =>
      firstCorrection_eq_sum hk.contDiff hk.support _ _
    simp_rw [hcs]
    rw [integral_transverse_sq_sum]
    simp_rw [integral_coord_smul_apply hc2.continuous hs2]
    rw [hC₀]
    field_simp
    ring
  have hpt : ∀ n : sphere (0 : E3) 1, ‖angularIntensity (slowCurrent κ k) u n - main n‖ ≤
      C₀ * (κ ^ 3 * (M ^ 2 * (4 * π / 3 * a ^ 3) ^ 2 * a ^ 3 * (4 + a))) :=
    fun n => abs_angularIntensity_slowCurrent_sub_le_of_dipole hk hN hκ0 hκ1 u hd' (by simp)
  calc _ = |∫ n : sphere (0 : E3) 1, (angularIntensity (slowCurrent κ k) u n - main n)
        ∂sphereMeasure| := by rw [integral_sub hint1 hint2, hmain_int]
    _ ≤ C₀ * (κ ^ 3 * (M ^ 2 * (4 * π / 3 * a ^ 3) ^ 2 * a ^ 3 * (4 + a))) *
          sphereMeasure.real univ := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le_const (Eventually.of_forall hpt)
    _ = _ := by
        rw [sphereMeasure_real_univ, hC₀]
        field_simp
        ring

/-! ### The general expansion to the order `κ⁶` -/

/-- **Taylor's formula** with a bounded third derivative:
`‖f(h) − f(0) − h f'(0) − (h²/2) f''(0)‖ ≤ M |h|³`. -/
theorem norm_taylor_three_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f f' f'' f''' : ℝ → G} {M : ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) (hf'' : ∀ t, HasDerivAt f'' (f''' t) t)
    (hM : ∀ t, ‖f''' t‖ ≤ M) (h : ℝ) :
    ‖f h - f 0 - h • f' 0 - (h ^ 2 / 2) • f'' 0‖ ≤ M * |h| ^ 3 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have h1 : ∀ t, ‖f' t - f' 0 - t • f'' 0‖ ≤ M * t ^ 2 := fun t =>
    norm_sub_sub_smul_le_of_deriv_two hf' hf'' hM t
  have hd : ∀ x, HasDerivAt (fun t => f t - t • f' 0 - (t ^ 2 / 2) • f'' 0)
      (f' x - f' 0 - x • f'' 0) x := fun x => by
    have hq : HasDerivAt (fun t : ℝ => (t ^ 2 / 2) • f'' 0) (x • f'' 0) x := by
      simpa using ((hasDerivAt_pow 2 x).div_const 2).smul_const (f'' 0)
    simpa using ((hf x).fun_sub ((hasDerivAt_id x).smul_const (f' 0))).fun_sub hq
  have h2 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => f t - t • f' 0 - (t ^ 2 / 2) • f'' 0)
    (f' := fun t => f' t - f' 0 - t • f'' 0) (s := uIcc 0 h) (C := M * h ^ 2)
    (fun x _ => (hd x).hasDerivWithinAt)
    (fun x hx => (h1 x).trans (mul_le_mul_of_nonneg_left (by
      have := abs_sub_left_of_mem_uIcc hx
      rw [sub_zero, sub_zero] at this
      rw [← sq_abs x, ← sq_abs h]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2) hM0)) (convex_uIcc 0 h) left_mem_uIcc
    right_mem_uIcc
  have he : f h - f 0 - h • f' 0 - (h ^ 2 / 2) • f'' 0 =
      (f h - h • f' 0 - (h ^ 2 / 2) • f'' 0) -
        (f 0 - (0 : ℝ) • f' 0 - ((0 : ℝ) ^ 2 / 2) • f'' 0) := by
    simp only [zero_smul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_div]
    abel
  rw [he]
  calc _ ≤ M * h ^ 2 * ‖h - 0‖ := h2
    _ = M * |h| ^ 3 := by rw [sub_zero, Real.norm_eq_abs, ← sq_abs h]; ring

/-- The second correction `𝐪(n) = ∫ ⟨n, y⟩² ∂ₛ³𝐣(s, y) dy` to the amplitude of the slow family;
the amplitude has the term `(κ²/2) 𝐪(n)` of the second order. -/
def secondCorrection (k : Spacetime → Spacetime) (s : ℝ) (n : E3) : E3 :=
  ∫ y, inner ℝ n y ^ 2 • space (currentRate (currentRate (currentRate k)) (vector s y))

/-- The second correction `𝐪(n)` is continuous in the direction. -/
theorem continuous_secondCorrection {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0) (s : ℝ) :
    Continuous (secondCorrection k s) := by
  have hc : Continuous fun p : E3 × E3 =>
      inner ℝ p.1 p.2 ^ 2 • space (currentRate (currentRate (currentRate k)) (vector s p.2)) :=
    ((continuous_fst.inner continuous_snd).pow 2).fun_smul
      (space.continuous.comp ((contDiff_currentRate (contDiff_currentRate
        (contDiff_currentRate hk))).continuous.comp
          (continuous_vector_of_continuous continuous_const continuous_snd)))
  exact continuous_integral_of_ballSupport (a := a) hc fun n y hy => by
    simp [currentRate_eq_zero_of_ballSupport (currentRate_eq_zero_of_ballSupport
      (currentRate_eq_zero_of_ballSupport hs)) _ y hy]

/-- The bound `‖𝐪(n)‖ ≤ a² M (4π/3)a³` of the second correction. -/
theorem norm_secondCorrection_le {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ}
    (hk : LocalizedSource k a M N) (hN : 3 ≤ N) (s : ℝ) {n : E3} (hn : ‖n‖ = 1) :
    ‖secondCorrection k s n‖ ≤ a ^ 2 * M * (4 * π / 3 * a ^ 3) := by
  refine norm_integral_le_of_ballSupport hk.radius_nonneg (fun y hy => by
    simp [currentRate_eq_zero_of_ballSupport (currentRate_eq_zero_of_ballSupport
      (currentRate_eq_zero_of_ballSupport hk.support)) _ y hy]) fun y hy => ?_
  rw [norm_smul, Real.norm_eq_abs]
  have hny : |inner ℝ n y| ≤ a := by
    calc |inner ℝ n y| ≤ ‖n‖ * ‖y‖ := abs_real_inner_le_norm n y
      _ ≤ a := by rw [hn, one_mul]; exact hy
  refine mul_le_mul ?_ (hk.bound 3 hN _) (norm_nonneg _) (sq_nonneg a)
  rw [abs_pow, ← sq_abs a]
  exact pow_le_pow_left₀ (abs_nonneg _) (hny.trans (le_abs_self a)) 2

/-- **The expansion of the amplitude to the second order**:
`Φ(n) = 𝐝̈(s) + κ 𝐜(n) + (κ²/2) 𝐪(n) + 𝐞(n)` with `‖𝐞(n)‖ ≤ M κ³ a³ (4π/3)a³`. -/
theorem norm_slowAmplitude_sub_le_three {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ}
    (hk : LocalizedSource k a M N) (hN : 4 ≤ N) {κ : ℝ} (hκ0 : 0 ≤ κ) (s : ℝ) {n : E3}
    (hn : ‖n‖ = 1) :
    ‖slowAmplitude k κ s n - (∫ y, space (currentRate k (vector s y))) -
        κ • firstCorrection k s n - (κ ^ 2 / 2) • secondCorrection k s n‖ ≤
      M * κ ^ 3 * a ^ 3 * (4 * π / 3 * a ^ 3) := by
  have hc1 : ContDiff ℝ ∞ (currentRate k) := contDiff_currentRate hk.contDiff
  have hc2 : ContDiff ℝ ∞ (currentRate (currentRate k)) := contDiff_currentRate hc1
  have hc3 : ContDiff ℝ ∞ (currentRate (currentRate (currentRate k))) := contDiff_currentRate hc2
  have hs1 : ∀ (t : ℝ) (x : E3), a < ‖x‖ → currentRate k (vector t x) = 0 :=
    currentRate_eq_zero_of_ballSupport hk.support
  have hs2 : ∀ (t : ℝ) (x : E3), a < ‖x‖ → currentRate (currentRate k) (vector t x) = 0 :=
    currentRate_eq_zero_of_ballSupport hs1
  have hs3 : ∀ (t : ℝ) (x : E3), a < ‖x‖ →
      currentRate (currentRate (currentRate k)) (vector t x) = 0 :=
    currentRate_eq_zero_of_ballSupport hs2
  have i1 : Integrable fun y => space (currentRate k (vector (s + κ * inner ℝ n y) y)) :=
    integrable_of_ballSupport (a := a) (space.continuous.comp (hc1.continuous.comp
      (continuous_vector_of_continuous (by fun_prop) continuous_id))) fun y hy => by
        simp [hs1 _ y hy]
  have i2 : Integrable fun y => space (currentRate k (vector s y)) :=
    integrable_of_ballSupport (a := a) (space.continuous.comp (hc1.continuous.comp
      (continuous_vector_of_continuous continuous_const continuous_id))) fun y hy => by
        simp [hs1 _ y hy]
  have hc3' : Continuous fun y => inner ℝ n y • space (currentRate (currentRate k) (vector s y)) :=
    (continuous_const.inner continuous_id).fun_smul (space.continuous.comp (hc2.continuous.comp
      (continuous_vector_of_continuous continuous_const continuous_id)))
  have i3 : Integrable fun y =>
      κ • (inner ℝ n y • space (currentRate (currentRate k) (vector s y))) :=
    (integrable_of_ballSupport (a := a) hc3' fun y hy => by simp [hs2 _ y hy]).smul κ
  have hc4 : Continuous fun y => inner ℝ n y ^ 2 •
      space (currentRate (currentRate (currentRate k)) (vector s y)) :=
    ((continuous_const.inner continuous_id).pow 2).fun_smul (space.continuous.comp
      (hc3.continuous.comp (continuous_vector_of_continuous continuous_const continuous_id)))
  have i4 : Integrable fun y => (κ ^ 2 / 2) • (inner ℝ n y ^ 2 •
      space (currentRate (currentRate (currentRate k)) (vector s y))) :=
    (integrable_of_ballSupport (a := a) hc4 fun y hy => by simp [hs3 _ y hy]).smul (κ ^ 2 / 2)
  have i12 : Integrable fun y => space (currentRate k (vector (s + κ * inner ℝ n y) y)) -
      space (currentRate k (vector s y)) := i1.sub i2
  have i123 : Integrable fun y => space (currentRate k (vector (s + κ * inner ℝ n y) y)) -
      space (currentRate k (vector s y)) -
        κ • (inner ℝ n y • space (currentRate (currentRate k) (vector s y))) := i12.sub i3
  rw [slowAmplitude, firstCorrection, secondCorrection, ← integral_smul, ← integral_smul,
    ← integral_sub i1 i2, ← integral_sub i12 i3, ← integral_sub i123 i4]
  refine norm_integral_le_of_ballSupport hk.radius_nonneg
    (fun y hy => by simp [hs1 _ y hy, hs2 _ y hy, hs3 _ y hy]) fun y hy => ?_
  have hd1 : ∀ t, HasDerivAt (fun t => space (currentRate k (vector (s + t) y)))
      (space (currentRate (currentRate k) (vector (s + t) y))) t := fun t =>
    (hasDerivAt_space_current_vector (hc1.differentiable (by simp)) (s + t) y).comp_const_add s t
  have hd2 : ∀ t, HasDerivAt (fun t => space (currentRate (currentRate k) (vector (s + t) y)))
      (space (currentRate (currentRate (currentRate k)) (vector (s + t) y))) t := fun t =>
    (hasDerivAt_space_current_vector (hc2.differentiable (by simp)) (s + t) y).comp_const_add s t
  have hd3 : ∀ t, HasDerivAt
      (fun t => space (currentRate (currentRate (currentRate k)) (vector (s + t) y)))
      (space (currentRate (currentRate (currentRate (currentRate k))) (vector (s + t) y))) t :=
    fun t => (hasDerivAt_space_current_vector (hc3.differentiable (by simp)) (s + t)
      y).comp_const_add s t
  have hT := norm_taylor_three_le hd1 hd2 hd3 (fun t => hk.bound 4 hN _) (κ * inner ℝ n y)
  simp only [add_zero] at hT
  rw [smul_smul, smul_smul, show κ ^ 2 / 2 * inner ℝ n y ^ 2 =
    (κ * inner ℝ n y) ^ 2 / 2 by ring]
  have hny : |inner ℝ n y| ≤ a := by
    calc |inner ℝ n y| ≤ ‖n‖ * ‖y‖ := abs_real_inner_le_norm n y
      _ ≤ a := by rw [hn, one_mul]; exact hy
  calc _ ≤ M * |κ * inner ℝ n y| ^ 3 := hT
    _ ≤ M * κ ^ 3 * a ^ 3 := by
        rw [abs_mul, abs_of_nonneg hκ0, mul_pow, mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg _) hny 3) (by positivity)) hk.bound_nonneg

/-- The expansion of `|v|² − ⟨n, v⟩²` at `v = b + κc + (κ²/2)q + e`. -/
theorem transverse_sq_expand_three (n b c q e : E3) (κ : ℝ) :
    ‖b + κ • c + (κ ^ 2 / 2) • q + e‖ ^ 2 - inner ℝ n (b + κ • c + (κ ^ 2 / 2) • q + e) ^ 2 =
      (‖b‖ ^ 2 - inner ℝ n b ^ 2) + 2 * κ * (inner ℝ b c - inner ℝ n b * inner ℝ n c) +
        κ ^ 2 * ((‖c‖ ^ 2 - inner ℝ n c ^ 2) + (inner ℝ b q - inner ℝ n b * inner ℝ n q)) +
        (2 * (inner ℝ b e - inner ℝ n b * inner ℝ n e) +
          (‖(κ ^ 2 / 2) • q + e‖ ^ 2 - inner ℝ n ((κ ^ 2 / 2) • q + e) ^ 2) +
          2 * κ * (inner ℝ c ((κ ^ 2 / 2) • q + e) -
            inner ℝ n c * inner ℝ n ((κ ^ 2 / 2) • q + e))) := by
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm c b, real_inner_comm q b, real_inner_comm e b, real_inner_comm q c,
    real_inner_comm e c, real_inner_comm e q]
  ring

/-- **The radiated power to the order `κ⁶` in general** (Landau–Lifshitz, §71): without the
assumption `𝐝̈ = 0`, the slow family radiates
`κ⁴ |𝐝̈|²/(6π) + κ⁶ (1/4π)[(1/180) Σ (D''')² + (2/3)|𝐦̈|²] + (κ⁶/16π²) X` at `s = κu`, up to
`(4π/9) M² a⁹ (6 + 4a + a(1/2 + a)²) κ⁷`, where `X = ∫ (⟨𝐝̈, 𝐪⟩ − ⟨n, 𝐝̈⟩⟨n, 𝐪⟩) dσ` is the
cross term of the dipole amplitude with the second correction
`𝐪(n) = ∫ ⟨n, y⟩² ∂ₛ³𝐣 dy` (the amplitude has `(κ²/2)𝐪`). -/
theorem power_general {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ}
    (hk : LocalizedSource k a M N) (hN : 4 ≤ N) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (u : ℝ) :
    |radiatedPower (slowCurrent κ k) u -
        κ ^ 4 * (1 / (6 * π)) * ‖deriv (deriv (dipoleMoment k)) (κ * u)‖ ^ 2 -
        κ ^ 6 * (1 / (4 * π)) * (1 / 180 * ∑ i : Fin 3, ∑ j : Fin 3,
            deriv (deriv (deriv fun s => quadrupoleMoment k s i j)) (κ * u) ^ 2 +
          2 / 3 * ‖deriv (deriv (magneticMoment k)) (κ * u)‖ ^ 2) -
        κ ^ 6 / (16 * π ^ 2) * ∫ n : sphere (0 : E3) 1,
          (inner ℝ (deriv (deriv (dipoleMoment k)) (κ * u)) (secondCorrection k (κ * u) n) -
            inner ℝ (n : E3) (deriv (deriv (dipoleMoment k)) (κ * u)) *
              inner ℝ (n : E3) (secondCorrection k (κ * u) n)) ∂sphereMeasure| ≤
      4 * π / 9 * M ^ 2 * a ^ 9 * (6 + 4 * a + a * (1 / 2 + a) ^ 2) * κ ^ 7 := by
  have hc2 : ContDiff ℝ ∞ (currentRate (currentRate k)) :=
    contDiff_currentRate (contDiff_currentRate hk.contDiff)
  have hs2 := currentRate_eq_zero_of_ballSupport (currentRate_eq_zero_of_ballSupport hk.support)
  simp only [deriv_deriv_deriv_quadrupoleMoment hk.contDiff hk.conserved hk.support,
    deriv_deriv_magneticMoment hk.contDiff hk.support,
    deriv_deriv_dipoleMoment hk.contDiff hk.conserved hk.support]
  rw [norm_smul (2 : ℝ)⁻¹, mul_pow, norm_sq_integral_cross3 hc2.continuous hs2, Real.norm_eq_abs,
    sq_abs, ← quadrupole_magnetic_identity, radiatedPower_eq_integral]
  set A := currentMoment (currentRate (currentRate k)) (κ * u) with hA
  set b := ∫ y, space (currentRate k (vector (κ * u) y))
  set c := firstCorrection k (κ * u)
  set q := secondCorrection k (κ * u)
  set Φ := slowAmplitude k κ (κ * u)
  set V := 4 * π / 3 * a ^ 3 with hV
  set C₀ := (κ ^ 2 / (4 * π)) ^ 2 with hC₀
  set main : E3 → ℝ := fun n => C₀ * ((‖b‖ ^ 2 - inner ℝ n b ^ 2) +
    2 * κ * (inner ℝ b (c n) - inner ℝ n b * inner ℝ n (c n)) +
    κ ^ 2 * ((‖c n‖ ^ 2 - inner ℝ n (c n) ^ 2) +
      (inner ℝ b (q n) - inner ℝ n b * inner ℝ n (q n)))) with hmain
  have hM := hk.bound_nonneg
  have ha := hk.radius_nonneg
  have hV0 : 0 ≤ V := by positivity
  have hcΦ : Continuous Φ := continuous_slowAmplitude hk.contDiff hk.support κ _
  have hcc : Continuous c := continuous_firstCorrection hk.contDiff hk.support _
  have hcq : Continuous q := continuous_secondCorrection hk.contDiff hk.support _
  have hAP : (fun n : sphere (0 : E3) 1 => angularIntensity (slowCurrent κ k) u n) =
      fun n : sphere (0 : E3) 1 => C₀ * (‖Φ (n : E3)‖ ^ 2 - inner ℝ (n : E3) (Φ n) ^ 2) :=
    funext fun n => angularIntensity_slowCurrent hk.contDiff hk.support κ u n
  have hint1 : Integrable (fun n : sphere (0 : E3) 1 => angularIntensity (slowCurrent κ k) u n)
      sphereMeasure := by
    rw [hAP]
    exact integrable_of_continuous (by fun_prop)
  have hint2 : Integrable (fun n : sphere (0 : E3) 1 => main n) sphereMeasure :=
    integrable_of_continuous (by fun_prop)
  have hQc : ∫ n : sphere (0 : E3) 1, (‖c n‖ ^ 2 - inner ℝ (n : E3) (c n) ^ 2) ∂sphereMeasure =
      4 * π * ((∑ l : Fin 3, ∑ i : Fin 3, A l i ^ 2) / 3 -
        (∑ l : Fin 3, ∑ i : Fin 3, A l i ^ 2 + (∑ l : Fin 3, A l l) ^ 2 +
          ∑ l : Fin 3, ∑ m : Fin 3, A m l * A l m) / 15) := by
    have hcs : ∀ n : sphere (0 : E3) 1, c n = ∑ l : Fin 3,
        inner ℝ (n : E3) (EuclideanSpace.single l 1) •
          ∫ y, y l • space (currentRate (currentRate k) (vector (κ * u) y)) := fun n =>
      firstCorrection_eq_sum hk.contDiff hk.support _ _
    simp_rw [hcs]
    rw [integral_transverse_sq_sum]
    simp_rw [integral_coord_smul_apply hc2.continuous hs2]
    ring
  have hmain_int : ∫ n : sphere (0 : E3) 1, main n ∂sphereMeasure =
      κ ^ 4 * (1 / (6 * π)) * ‖b‖ ^ 2 +
        κ ^ 6 * (1 / (4 * π)) * ((∑ l : Fin 3, ∑ i : Fin 3, A l i ^ 2) / 3 -
          (∑ l : Fin 3, ∑ i : Fin 3, A l i ^ 2 + (∑ l : Fin 3, A l l) ^ 2 +
            ∑ l : Fin 3, ∑ m : Fin 3, A m l * A l m) / 15) +
        κ ^ 6 / (16 * π ^ 2) * ∫ n : sphere (0 : E3) 1,
          (inner ℝ b (q n) - inner ℝ (n : E3) b * inner ℝ (n : E3) (q n)) ∂sphereMeasure := by
    simp only [hmain]
    rw [integral_const_mul, integral_add (integrable_of_continuous (by fun_prop))
      (integrable_of_continuous (by fun_prop)), integral_add (integrable_of_continuous
        (by fun_prop)) (integrable_of_continuous (by fun_prop)), integral_norm_sq_sub_inner_sq,
      integral_const_mul, integral_inner_firstCorrection, integral_const_mul,
      integral_add (integrable_of_continuous (by fun_prop))
        (integrable_of_continuous (by fun_prop)), hQc, hC₀]
    field_simp
    ring
  have hpt : ∀ n : sphere (0 : E3) 1, ‖angularIntensity (slowCurrent κ k) u n - main n‖ ≤
      C₀ * (κ ^ 3 * (M ^ 2 * V ^ 2 * a ^ 3 * (6 + 4 * a + a * (1 / 2 + a) ^ 2))) := by
    intro n
    have hn : ‖(n : E3)‖ = 1 := by simp
    set e := Φ n - b - κ • c n - (κ ^ 2 / 2) • q n
    have hbβ : ‖b‖ ≤ M * V := norm_integral_currentRate_le hk (by omega) _
    have hcγ : ‖c n‖ ≤ a * M * V := norm_firstCorrection_le hk (by omega) _ hn
    have hqρ : ‖q n‖ ≤ a ^ 2 * M * V := norm_secondCorrection_le hk (by omega) _ hn
    have heε : ‖e‖ ≤ M * κ ^ 3 * a ^ 3 * V := norm_slowAmplitude_sub_le_three hk hN hκ0.le _ hn
    have hΦ : Φ n = b + κ • c n + (κ ^ 2 / 2) • q n + e := by
      simp only [e]
      abel
    have hf : ‖(κ ^ 2 / 2) • q n + e‖ ≤ κ ^ 2 * (M * V * a ^ 2 * (1 / 2 + a)) := by
      have hk3 : κ ^ 3 ≤ κ ^ 2 := pow_le_pow_of_le_one hκ0.le hκ1 (by norm_num)
      calc _ ≤ ‖(κ ^ 2 / 2) • q n‖ + ‖e‖ := norm_add_le _ _
        _ ≤ κ ^ 2 / 2 * (a ^ 2 * M * V) + M * κ ^ 3 * a ^ 3 * V := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            gcongr
        _ ≤ κ ^ 2 / 2 * (a ^ 2 * M * V) + M * κ ^ 2 * a ^ 3 * V := by gcongr
        _ = _ := by ring
    rw [show angularIntensity (slowCurrent κ k) u n = C₀ * (‖Φ (n : E3)‖ ^ 2 -
      inner ℝ (n : E3) (Φ n) ^ 2) from congrFun hAP n, hΦ, transverse_sq_expand_three]
    simp only [hmain]
    rw [show ∀ X Y Z R : ℝ, C₀ * (X + Y + Z + R) - C₀ * (X + Y + Z) = C₀ * R from
      fun X Y Z R => by ring, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 := abs_transverse_inner_le (v := b) (w := e) hn
    have h2 := abs_transverse_sq_le (v := (κ ^ 2 / 2) • q n + e) hn
    have h3 := abs_transverse_inner_le (v := c n) (w := (κ ^ 2 / 2) • q n + e) hn
    have hbe : ‖b‖ * ‖e‖ ≤ M * V * (M * κ ^ 3 * a ^ 3 * V) :=
      mul_le_mul hbβ heε (norm_nonneg _) (by positivity)
    have hcf : ‖c n‖ * ‖(κ ^ 2 / 2) • q n + e‖ ≤
        a * M * V * (κ ^ 2 * (M * V * a ^ 2 * (1 / 2 + a))) :=
      mul_le_mul hcγ hf (norm_nonneg _) (by positivity)
    have hf2 : ‖(κ ^ 2 / 2) • q n + e‖ ^ 2 ≤ (κ ^ 2 * (M * V * a ^ 2 * (1 / 2 + a))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hf 2
    have hk4 : κ ^ 4 ≤ κ ^ 3 := pow_le_pow_of_le_one hκ0.le hκ1 (by norm_num)
    calc _ ≤ |2 * (inner ℝ b e - inner ℝ (n : E3) b * inner ℝ (n : E3) e)| +
          |‖(κ ^ 2 / 2) • q n + e‖ ^ 2 - inner ℝ (n : E3) ((κ ^ 2 / 2) • q n + e) ^ 2| +
          |2 * κ * (inner ℝ (c n) ((κ ^ 2 / 2) • q n + e) -
            inner ℝ (n : E3) (c n) * inner ℝ (n : E3) ((κ ^ 2 / 2) • q n + e))| :=
          (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ ≤ 2 * (2 * (M * V * (M * κ ^ 3 * a ^ 3 * V))) +
          (κ ^ 2 * (M * V * a ^ 2 * (1 / 2 + a))) ^ 2 +
          2 * κ * (2 * (a * M * V * (κ ^ 2 * (M * V * a ^ 2 * (1 / 2 + a))))) := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2),
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * κ)]
          gcongr
          · exact h1.trans (by linarith)
          · exact h2.trans hf2
          · exact h3.trans (by linarith)
      _ = M ^ 2 * V ^ 2 * a ^ 3 * (4 * κ ^ 3 + κ ^ 4 * a * (1 / 2 + a) ^ 2 +
          4 * κ ^ 3 * (1 / 2 + a)) := by ring
      _ ≤ M ^ 2 * V ^ 2 * a ^ 3 * (4 * κ ^ 3 + κ ^ 3 * a * (1 / 2 + a) ^ 2 +
          4 * κ ^ 3 * (1 / 2 + a)) := by gcongr
      _ = _ := by ring
  calc _ = |∫ n : sphere (0 : E3) 1, (angularIntensity (slowCurrent κ k) u n - main n)
        ∂sphereMeasure| := by
        rw [integral_sub hint1 hint2, hmain_int]
        congr 1
        ring
    _ ≤ C₀ * (κ ^ 3 * (M ^ 2 * V ^ 2 * a ^ 3 * (6 + 4 * a + a * (1 / 2 + a) ^ 2))) *
          sphereMeasure.real univ := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le_const (Eventually.of_forall hpt)
    _ = _ := by
        rw [sphereMeasure_real_univ, hC₀, hV]
        field_simp
        ring

/-! ### An instance: the oscillating quadrupole -/

/-- The integral of a derivative vanishes: `∫ ∂₁f d𝐲 = 0` for a smooth `f` supported in a ball. -/
theorem integral_partialOne_eq_zero {f : E3 → ℝ} {r : ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : ∀ x, r < ‖x‖ → f x = 0) : ∫ y, partialOne f y = 0 := by
  have hp : Integrable fun y : E3 => fderiv ℝ f y (EuclideanSpace.single 0 1) :=
    integrable_of_ballSupport (a := r) (contDiff_partialOne hf).continuous
      fun y hy => partialOne_eq_zero hs hy
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : E3 => (1 : ℝ)) (g := f) (v := EuclideanSpace.single 0 1) (by simp)
    (by simpa using hp) (by simpa using integrable_of_ballSupport (a := r) hf.continuous hs)
    (fun _ _ => differentiableAt_const _) (fun y _ => hf.differentiable (by simp) y)
  simpa [partialOne] using h

/-- The oscillating quadrupole `ρ = cos s ∂₁²χ`, `𝐣 = sin s ∂₁χ e₁` of the bump `χ = dipoleBump`:
the oscillating current of the profile `∂₁χ`. -/
def oscillatingQuadrupole : Spacetime → Spacetime := oscillatingCurrent (partialOne dipoleBump) 0

/-- The derivative `∂₁χ` of the bump vanishes outside the ball of radius `2`. -/
theorem partialOne_dipoleBump_eq_zero (x : E3) (hx : 2 < ‖x‖) : partialOne dipoleBump x = 0 :=
  partialOne_eq_zero dipoleBump_eq_zero hx

/-- The derivative `∂₁χ` of the bump is bounded. -/
theorem exists_bound_partialOne_dipoleBump : ∃ B, ∀ x, |partialOne dipoleBump x| ≤ B := by
  obtain ⟨B, hB⟩ :=
    (contDiff_partialOne dipoleBump.contDiff).continuous.bounded_above_of_compact_support
    (HasCompactSupport.intro (isCompact_closedBall 0 2) fun x hx =>
      partialOne_dipoleBump_eq_zero x (by simpa using hx))
  exact ⟨B, fun x => by simpa [Real.norm_eq_abs] using hB x⟩

/-- The oscillating quadrupole is a localized source with `a = 2`. -/
theorem exists_localizedSource_oscillatingQuadrupole :
    ∃ M, ∀ N, LocalizedSource oscillatingQuadrupole 2 M N := by
  obtain ⟨B, hB⟩ := exists_bound_partialOne_dipoleBump
  exact ⟨B, fun N => localizedSource_oscillatingCurrent (contDiff_partialOne dipoleBump.contDiff)
    (by norm_num) partialOne_dipoleBump_eq_zero hB 0 N⟩

/-- The oscillating quadrupole has no dipole moment: `𝐝(s) = −cos s (∫ ∂₁χ) e₁ = 0`. -/
theorem dipoleMoment_oscillatingQuadrupole (s : ℝ) :
    dipoleMoment oscillatingQuadrupole s = 0 := by
  rw [oscillatingQuadrupole, dipoleMoment_oscillatingCurrent
    (contDiff_partialOne dipoleBump.contDiff) partialOne_dipoleBump_eq_zero,
    integral_partialOne_eq_zero dipoleBump.contDiff dipoleBump_eq_zero]
  simp

/-- The moments `Mₖᵢ = ∫ yₖ ∂ₛ²jᵢ d𝐲` of the oscillating quadrupole:
`Mₖᵢ = sin s (∫ χ) δᵢ₀ δₖ₀`. -/
theorem currentMoment_oscillatingQuadrupole (s : ℝ) (l i : Fin 3) :
    currentMoment (currentRate (currentRate oscillatingQuadrupole)) s l i =
      sin s * (∫ y, dipoleBump y) *
        ((EuclideanSpace.single 0 (1 : ℝ) : E3) i * (EuclideanSpace.single 0 (1 : ℝ) : E3) l) := by
  have hf := contDiff_partialOne dipoleBump.contDiff
  rw [oscillatingQuadrupole, currentRate_oscillatingCurrent hf, currentRate_oscillatingCurrent hf,
    currentMoment]
  have hpt : ∀ y : E3,
      oscillatingCurrent (partialOne dipoleBump) (0 + π / 2 + π / 2) (vector s y) i.succ * y l =
        (-sin s * (EuclideanSpace.single 0 (1 : ℝ) : E3) i) * (partialOne dipoleBump y * y l) :=
    fun y => by
      rw [← space_apply
        (oscillatingCurrent (partialOne dipoleBump) (0 + π / 2 + π / 2) (vector s y)),
        space_oscillatingCurrent]
      simp only [vector_zero, space_vector, PiLp.smul_apply, smul_eq_mul]
      rw [zero_add, add_halves, sin_add_pi]
      ring
  simp_rw [hpt]
  rw [integral_const_mul]
  have hint : Integrable fun y : E3 => partialOne dipoleBump y • y :=
    integrable_of_ballSupport (a := 2) (hf.continuous.smul continuous_id)
      fun y hy => by simp [partialOne_dipoleBump_eq_zero y hy]
  have hl : ∫ y, partialOne dipoleBump y * y l =
      -(∫ y, dipoleBump y) * (EuclideanSpace.single 0 (1 : ℝ) : E3) l := by
    have h := congrArg (fun v : E3 => v l)
      (integral_partialOne_smul dipoleBump.contDiff dipoleBump_eq_zero)
    simp only at h
    rw [eval_integral_piLp (fun j => hint.eval_piLp j)] at h
    simpa only [PiLp.smul_apply, smul_eq_mul] using h
  rw [hl]
  ring

/-- **The third derivative of the quadrupole moment** of the oscillating quadrupole:
`D'''₁₁(s) = 4 sin s ∫ χ`, which does not vanish at `s = π/2`. -/
theorem deriv_deriv_deriv_quadrupoleMoment_oscillatingQuadrupole (s : ℝ) :
    deriv (deriv (deriv fun s => quadrupoleMoment oscillatingQuadrupole s 0 0)) s =
      4 * sin s * ∫ y, dipoleBump y := by
  obtain ⟨M, hM⟩ := exists_localizedSource_oscillatingQuadrupole
  have hk := hM 0
  rw [deriv_deriv_deriv_quadrupoleMoment hk.contDiff hk.conserved hk.support]
  simp only [quadrupoleRate, currentMoment_oscillatingQuadrupole, Fin.sum_univ_three]
  simp
  ring

/-- The leading term of the oscillating quadrupole does not vanish: `D'''₁₁(π/2) = 4 ∫ χ ≠ 0`. -/
theorem deriv_deriv_deriv_quadrupoleMoment_oscillatingQuadrupole_ne_zero :
    deriv (deriv (deriv fun s => quadrupoleMoment oscillatingQuadrupole s 0 0)) (π / 2) ≠ 0 := by
  rw [deriv_deriv_deriv_quadrupoleMoment_oscillatingQuadrupole, sin_pi_div_two]
  have := integral_dipoleBump_pos
  positivity

/-- The sum of squares `Σᵢⱼ (D'''ᵢⱼ)² = 24 sin² s (∫ χ)²` of the oscillating quadrupole. -/
theorem sum_sq_quadrupole_oscillatingQuadrupole (s : ℝ) :
    ∑ i : Fin 3, ∑ j : Fin 3,
        deriv (deriv (deriv fun s => quadrupoleMoment oscillatingQuadrupole s i j)) s ^ 2 =
      24 * sin s ^ 2 * (∫ y, dipoleBump y) ^ 2 := by
  obtain ⟨M, hM⟩ := exists_localizedSource_oscillatingQuadrupole
  have hk := hM 0
  simp only [deriv_deriv_deriv_quadrupoleMoment hk.contDiff hk.conserved hk.support,
    quadrupoleRate, currentMoment_oscillatingQuadrupole, Fin.sum_univ_three]
  simp
  ring

/-- The oscillating quadrupole has no magnetic radiation: `𝐦̈ = 0`. -/
theorem norm_magneticMoment_oscillatingQuadrupole (s : ℝ) :
    ‖deriv (deriv (magneticMoment oscillatingQuadrupole)) s‖ ^ 2 = 0 := by
  obtain ⟨M, hM⟩ := exists_localizedSource_oscillatingQuadrupole
  have hk := hM 0
  rw [deriv_deriv_magneticMoment hk.contDiff hk.support, norm_smul, mul_pow,
    norm_sq_integral_cross3 (contDiff_currentRate (contDiff_currentRate hk.contDiff)).continuous
      (currentRate_eq_zero_of_ballSupport (currentRate_eq_zero_of_ballSupport hk.support))]
  simp [currentMoment_oscillatingQuadrupole]

/-- **An instance of the quadrupole formula**: the slow family of the oscillating quadrupole has
no dipole radiation, and radiates `κ⁶ sin²(κu) (∫ χ)²/(30π)` up to `C κ⁷`; the leading term is
`κ⁶ (1/4π)(1/180) Σ (D''')²` with `Σ (D''')² = 24 sin² (∫ χ)²` and `𝐦̈ = 0`. -/
theorem power_oscillatingQuadrupole : ∃ C, ∀ κ : ℝ, 0 < κ → κ ≤ 1 → ∀ u : ℝ,
    |radiatedPower (slowCurrent κ oscillatingQuadrupole) u -
        κ ^ 6 * (1 / (30 * π)) * (sin (κ * u) ^ 2 * (∫ y, dipoleBump y) ^ 2)| ≤ C * κ ^ 7 := by
  obtain ⟨M, hM⟩ := exists_localizedSource_oscillatingQuadrupole
  refine ⟨4 * π / 9 * M ^ 2 * 2 ^ 9 * (4 + 2), fun κ hκ0 hκ1 u => ?_⟩
  have hd : deriv (deriv (dipoleMoment oscillatingQuadrupole)) (κ * u) = 0 := by
    have h0 : dipoleMoment oscillatingQuadrupole = fun _ => 0 :=
      funext dipoleMoment_oscillatingQuadrupole
    simp [h0]
  have h := power_sub_le (hM 3) le_rfl hκ0 hκ1 u hd
  rw [sum_sq_quadrupole_oscillatingQuadrupole, norm_magneticMoment_oscillatingQuadrupole] at h
  convert h using 3
  field_simp
  ring

end ProjectAinos.Electrodynamics.Radiation
