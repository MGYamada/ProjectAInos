/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.Synchronous
public import ProjectAinos.SmoothGeometry.Lorentzian.DiagonalMetric

/-!
# Orthogonal slicings by co-ordinate hypersurfaces

Let `g` be a coordinate metric on an open set `U` of the model space and `k` an index. The
co-ordinate hypersurfaces `x^k = c` form an **orthogonal slicing** when `g_{kμ} = 0` for every
`μ ≠ k` on `U` (`CoordinateMetric.IsOrthogonalSlicing`): the co-ordinate field `∂_k` is normal to
them. The `d` indices of a hypersurface are the indices `a' = k.succAbove a` different from `k`.

* `inducedMetric`: the first fundamental form `h_{ab} = g_{a'b'}` of the hypersurface through `z`.
* `unitNormal`, `IsOrthogonalSlicing.form_unitNormal_self`,
  `IsOrthogonalSlicing.form_unitNormal_tangent`: the normal `n = ε |g_{kk}|^{-1/2} ∂_k` has
  `g(n, n) = ε² g_{kk}/|g_{kk}|`, which is `±1` for `ε = ±1`, and `g(n, ∂_{a'}) = 0`; the sign `ε`
  chooses its orientation, `ε = 1` towards increasing `x^k`.
* `secondFundamental`: the second fundamental form `K_{ab} = ½ ε |g_{kk}|^{-1/2} ∂_k g_{a'b'}`.
  `IsOrthogonalSlicing.secondFundamental_eq`: `K_{ab} = −g(n, Γ_{a'b'})`, with the vector
  `Γ_{a'b'} = Γ^μ_{a'b'} ∂_μ` of the Christoffel symbols, that is
  `K(∂_a, ∂_b) = −g(n, ∇_{∂_a} ∂_b) = g(∇_{∂_a} n, ∂_b)`; the normal component is
  `Γ^k_{a'b'} = −∂_k g_{a'b'}/(2 g_{kk})` (`IsOrthogonalSlicing.christoffel_normal`).
* `IsOrthogonalSlicing.coefficient_self_ne_zero`, `IsOrthogonalSlicing.inv_row`: `g_{kk} ≠ 0`,
  and the row `k` of the inverse is `g^{kμ} = δ^{kμ}/g_{kk}`.
* Instances. A diagonal metric is an orthogonal slicing in every co-ordinate
  (`isOrthogonalSlicing_ofDiagonal`), with the diagonal forms `inducedMetric_ofDiagonal` and
  `secondFundamental_ofDiagonal`; so is the Minkowski metric (`isOrthogonalSlicing_minkowski`). A
  synchronous metric (Landau–Lifshitz, §97) is an orthogonal slicing by the times `t = const`
  (`IsSynchronous.isOrthogonalSlicing`); its induced metric is the spatial metric `γ_{αβ}`
  (`IsSynchronous.inducedMetric_eq`) and its second fundamental form is `K_{αβ} = ½ ε ∂_t γ_{αβ}`
  (`IsSynchronous.secondFundamental_eq`), so that `g^{αδ} K_{βδ} = ½ ε κ^α_β` with the rate `κ` of
  §97 (`IsSynchronous.sum_inv_mul_secondFundamental`).
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology ContDiff

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

/-- The co-ordinate hypersurfaces `x^k = c` are an orthogonal slicing of `g`: `g_{kμ} = 0` on `U`
for every `μ ≠ k`. -/
def IsOrthogonalSlicing (g : CoordinateMetric σ d U) (k : Fin (d + 1)) : Prop :=
  ∀ z ∈ U, ∀ μ, μ ≠ k → g.coefficient z k μ = 0

/-- The induced metric `h_{ab} = g_{a'b'}` of the hypersurface `x^k = z^k` at `z`, with
`a' = k.succAbove a`. -/
def inducedMetric (g : CoordinateMetric σ d U) (k : Fin (d + 1)) (z : MinkowskiModel d) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun a b => g.coefficient z (k.succAbove a) (k.succAbove b)

/-- The normal `n = ε |g_{kk}|^{-1/2} ∂_k` of the hypersurface `x^k = z^k` at `z`. -/
def unitNormal (g : CoordinateMetric σ d U) (k : Fin (d + 1)) (ε : ℝ) (z : MinkowskiModel d) :
    MinkowskiModel d :=
  (ε / Real.sqrt |g.coefficient z k k|) • Pi.single k 1

/-- The second fundamental form `K_{ab} = ½ ε |g_{kk}|^{-1/2} ∂_k g_{a'b'}` of the hypersurface
`x^k = z^k` at `z`, for the normal `unitNormal g k ε`. -/
def secondFundamental (g : CoordinateMetric σ d U) (k : Fin (d + 1)) (ε : ℝ)
    (z : MinkowskiModel d) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun a b => ε / (2 * Real.sqrt |g.coefficient z k k|) *
    fderiv ℝ (fun w => g.coefficient w (k.succAbove a) (k.succAbove b)) z (Pi.single k 1)

theorem inducedMetric_apply (g : CoordinateMetric σ d U) (k : Fin (d + 1)) (z : MinkowskiModel d)
    (a b : Fin d) :
    g.inducedMetric k z a b = g.coefficient z (k.succAbove a) (k.succAbove b) := rfl

theorem secondFundamental_apply (g : CoordinateMetric σ d U) (k : Fin (d + 1)) (ε : ℝ)
    (z : MinkowskiModel d) (a b : Fin d) :
    g.secondFundamental k ε z a b = ε / (2 * Real.sqrt |g.coefficient z k k|) *
      fderiv ℝ (fun w => g.coefficient w (k.succAbove a) (k.succAbove b)) z (Pi.single k 1) :=
  rfl

namespace IsOrthogonalSlicing

variable {g : CoordinateMetric σ d U} {k : Fin (d + 1)} (hg : g.IsOrthogonalSlicing k)
  {z : MinkowskiModel d}
include hg

/-- The column `k` vanishes off the diagonal: `g_{μk} = 0` for `μ ≠ k`. -/
theorem coefficient_right (hz : z ∈ U) {μ : Fin (d + 1)} (hμ : μ ≠ k) :
    g.coefficient z μ k = 0 := by
  rw [g.coefficient_symmetric hz]
  exact hg z hz μ hμ

/-- `g_{kk} g^{kj} = δ_{kj}`. -/
theorem mul_inv_row (hz : z ∈ U) (j : Fin (d + 1)) :
    g.coefficient z k k * (g.coefficient z)⁻¹ k j = if k = j then 1 else 0 := by
  have h := congrFun (congrFun (g.coefficient_mul_inv ⟨z, hz⟩) k) j
  rw [Matrix.mul_apply, Finset.sum_eq_single k] at h
  · simpa [Matrix.one_apply] using h
  · intro l _ hl
    change g.coefficient z k l * _ = 0
    rw [hg z hz l hl, zero_mul]
  · simp

/-- The normal coefficient does not vanish: `g_{kk} ≠ 0`. -/
theorem coefficient_self_ne_zero (hz : z ∈ U) : g.coefficient z k k ≠ 0 := by
  have h := hg.mul_inv_row hz k
  simp only [↓reduceIte] at h
  exact left_ne_zero_of_mul_eq_one h

/-- The row `k` of the inverse: `g^{kj} = δ_{kj}/g_{kk}`. -/
theorem inv_row (hz : z ∈ U) (j : Fin (d + 1)) :
    (g.coefficient z)⁻¹ k j = if j = k then (g.coefficient z k k)⁻¹ else 0 := by
  have h := hg.mul_inv_row hz j
  have h0 := hg.coefficient_self_ne_zero hz
  by_cases hj : j = k
  · subst hj
    simp only [↓reduceIte] at h ⊢
    exact eq_inv_of_mul_eq_one_right h
  · simp only [Ne.symm hj, hj, ↓reduceIte] at h ⊢
    exact (mul_eq_zero.mp h).resolve_left h0

/-- The derivatives of a vanishing coefficient `g_{μk}`, `μ ≠ k`, vanish. -/
theorem fderiv_coefficient_right (hz : z ∈ U) {μ : Fin (d + 1)} (hμ : μ ≠ k)
    (v : MinkowskiModel d) : fderiv ℝ (fun w => g.coefficient w μ k) z v = 0 := by
  have h : (fun w => g.coefficient w μ k) =ᶠ[𝓝 z] fun _ => 0 :=
    eventually_of_mem (U.isOpen.mem_nhds hz) fun w hw => hg.coefficient_right hw hμ
  rw [h.fderiv_eq]
  simp

/-- The derivatives of a vanishing coefficient `g_{kμ}`, `μ ≠ k`, vanish. -/
theorem fderiv_coefficient_left (hz : z ∈ U) {μ : Fin (d + 1)} (hμ : μ ≠ k)
    (v : MinkowskiModel d) : fderiv ℝ (fun w => g.coefficient w k μ) z v = 0 := by
  have h : (fun w => g.coefficient w k μ) =ᶠ[𝓝 z] fun _ => 0 :=
    eventually_of_mem (U.isOpen.mem_nhds hz) fun w hw => hg w hw μ hμ
  rw [h.fderiv_eq]
  simp

/-- **The normal Christoffel symbols**: `Γ^k_{a'b'} = −∂_k g_{a'b'}/(2 g_{kk})`. -/
theorem christoffel_normal (hz : z ∈ U) (a b : Fin d) :
    christoffelOf g.coefficient z k (k.succAbove a) (k.succAbove b) =
      -(fderiv ℝ (fun w => g.coefficient w (k.succAbove a) (k.succAbove b)) z
        (Pi.single k 1)) / (2 * g.coefficient z k k) := by
  have h0 := hg.coefficient_self_ne_zero hz
  unfold christoffelOf
  rw [Finset.sum_eq_single k]
  · rw [hg.inv_row hz k, hg.fderiv_coefficient_right hz (Fin.succAbove_ne k b),
      hg.fderiv_coefficient_left hz (Fin.succAbove_ne k a)]
    simp only [↓reduceIte]
    field_simp
    ring
  · intro l _ hl
    rw [hg.inv_row hz l]
    simp [hl]
  · simp

/-- The form on the normal and a vector: `g(n, w) = ε |g_{kk}|^{-1/2} g_{kk} w^k`. -/
theorem form_unitNormal (hz : z ∈ U) (ε : ℝ) (w : MinkowskiModel d) :
    g.form z (unitNormal g k ε z) w =
      ε / Real.sqrt |g.coefficient z k k| * g.coefficient z k k * w k := by
  have hn (i : Fin (d + 1)) : unitNormal g k ε z i =
      if i = k then ε / Real.sqrt |g.coefficient z k k| else 0 := by
    by_cases hi : i = k
    · subst hi
      simp [unitNormal]
    · simp [unitNormal, hi]
  rw [g.form_apply, Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single k]
    · simp only [hn k, ↓reduceIte]
      ring
    · intro j _ hj
      rw [hg z hz j hj]
      ring
    · simp
  · intro i _ hi
    simp [hn i, hi]
  · simp

/-- The normal has the norm `g(n, n) = ε² g_{kk}/|g_{kk}|`, which is `±1` for `ε = ±1`. -/
theorem form_unitNormal_self (hz : z ∈ U) (ε : ℝ) :
    g.form z (unitNormal g k ε z) (unitNormal g k ε z) =
      ε ^ 2 * g.coefficient z k k / |g.coefficient z k k| := by
  have h0 := hg.coefficient_self_ne_zero hz
  have hpos : 0 < |g.coefficient z k k| := abs_pos.mpr h0
  have hs : Real.sqrt |g.coefficient z k k| ^ 2 = |g.coefficient z k k| :=
    Real.sq_sqrt hpos.le
  have hs0 : Real.sqrt |g.coefficient z k k| ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  rw [hg.form_unitNormal hz]
  simp only [unitNormal, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  rw [show ε / Real.sqrt |g.coefficient z k k| * g.coefficient z k k *
      (ε / Real.sqrt |g.coefficient z k k|) =
      ε ^ 2 * g.coefficient z k k / Real.sqrt |g.coefficient z k k| ^ 2 by field_simp, hs]

/-- The normal is orthogonal to the hypersurface: `g(n, ∂_{a'}) = 0`. -/
theorem form_unitNormal_tangent (hz : z ∈ U) (ε : ℝ) (a : Fin d) :
    g.form z (unitNormal g k ε z) (Pi.single (k.succAbove a) 1) = 0 := by
  rw [hg.form_unitNormal hz, Pi.single_eq_of_ne (Fin.succAbove_ne k a).symm, mul_zero]

/-- **The second fundamental form is the normal part of the connection**:
`K_{ab} = −g(n, Γ_{a'b'})` with the vector `Γ_{a'b'} = Γ^μ_{a'b'} ∂_μ`, that is
`K(∂_a, ∂_b) = −g(n, ∇_{∂_a} ∂_b)`. -/
theorem secondFundamental_eq (hz : z ∈ U) (ε : ℝ) (a b : Fin d) :
    g.secondFundamental k ε z a b =
      -g.form z (unitNormal g k ε z)
        (fun μ => christoffelOf g.coefficient z μ (k.succAbove a) (k.succAbove b)) := by
  have h0 := hg.coefficient_self_ne_zero hz
  have hpos : 0 < |g.coefficient z k k| := abs_pos.mpr h0
  have hs0 : Real.sqrt |g.coefficient z k k| ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  rw [hg.form_unitNormal hz, hg.christoffel_normal hz, secondFundamental_apply]
  field_simp

end IsOrthogonalSlicing

/-! ### Instances -/

section Diagonal

variable (c : MinkowskiModel d → Fin (d + 1) → ℝ)
    (hc : ∀ i, ContDiffOn ℝ ∞ (fun x => c x i) U)
    (h0 : ∀ x ∈ U, -σ.timeSign * c x 0 < 0)
    (hs : ∀ x ∈ U, ∀ α : Fin d, 0 < -σ.timeSign * c x α.succ)

/-- **A diagonal metric is an orthogonal slicing in every co-ordinate.** -/
theorem isOrthogonalSlicing_ofDiagonal (k : Fin (d + 1)) :
    (ofDiagonal c hc h0 hs).IsOrthogonalSlicing k := by
  intro z _ μ hμ
  rw [coefficient_ofDiagonal, Matrix.diagonal_apply_ne _ (Ne.symm hμ)]

/-- The induced metric of a diagonal metric is the diagonal of the tangential coefficients. -/
theorem inducedMetric_ofDiagonal (k : Fin (d + 1)) (z : MinkowskiModel d) :
    (ofDiagonal c hc h0 hs).inducedMetric k z = Matrix.diagonal fun a => c z (k.succAbove a) := by
  ext a b
  rw [inducedMetric_apply, coefficient_ofDiagonal]
  by_cases h : a = b
  · subst h
    simp
  · rw [Matrix.diagonal_apply_ne _ h,
      Matrix.diagonal_apply_ne _ ((Fin.succAbove_right_inj).not.mpr h)]

/-- The second fundamental form of a diagonal metric is
`K_{ab} = δ_{ab} ½ ε |c_k|^{-1/2} ∂_k c_{a'}`. -/
theorem secondFundamental_ofDiagonal (k : Fin (d + 1)) (ε : ℝ) (z : MinkowskiModel d) :
    (ofDiagonal c hc h0 hs).secondFundamental k ε z = Matrix.diagonal fun a =>
      ε / (2 * Real.sqrt |c z k|) *
        fderiv ℝ (fun w => c w (k.succAbove a)) z (Pi.single k 1) := by
  ext a b
  rw [secondFundamental_apply]
  simp_rw [coefficient_ofDiagonal]
  rw [fderiv_diagonal_apply, Matrix.diagonal_apply_eq]
  by_cases h : a = b
  · subst h
    simp
  · rw [Matrix.diagonal_apply_ne _ h]
    simp [(Fin.succAbove_right_inj).not.mpr h]

end Diagonal

/-- **The Minkowski metric is an orthogonal slicing in every co-ordinate.** -/
theorem isOrthogonalSlicing_minkowski (k : Fin (d + 1)) :
    (minkowski σ d U).IsOrthogonalSlicing k := by
  rw [minkowski_eq_ofDiagonal]
  exact isOrthogonalSlicing_ofDiagonal _ _ _ _ k

namespace IsSynchronous

variable {g : CoordinateMetric .timeNegative d U} (hs : g.IsSynchronous)
include hs

/-- **A synchronous metric is an orthogonal slicing by the times** `t = const`. -/
theorem isOrthogonalSlicing : g.IsOrthogonalSlicing 0 := by
  intro z hz μ hμ
  obtain ⟨α, rfl⟩ := Fin.exists_succ_eq.mpr hμ
  exact (hs z hz).2 α

omit hs in
/-- The induced metric of the slices `t = const` is the spatial metric `γ_{αβ}`. -/
theorem inducedMetric_eq (z : MinkowskiModel d) (α β : Fin d) :
    g.inducedMetric 0 z α β = g.coefficient z α.succ β.succ := by
  rw [inducedMetric_apply, Fin.succAbove_zero]

/-- The second fundamental form of the slices `t = const` is `K_{αβ} = ½ ε ∂_t γ_{αβ}`. -/
theorem secondFundamental_eq {z : MinkowskiModel d} (hz : z ∈ U) (ε : ℝ) (α β : Fin d) :
    g.secondFundamental 0 ε z α β = ε / 2 * g.metricRate z α β := by
  rw [secondFundamental_apply, (hs z hz).1, Fin.succAbove_zero, metricRate]
  simp

/-- With the rate `κ^α_β = γ^{αδ} ∂_t γ_{βδ}` of §97, `g^{αδ} K_{βδ} = ½ ε κ^α_β`. -/
theorem sum_inv_mul_secondFundamental {z : MinkowskiModel d} (hz : z ∈ U) (ε : ℝ)
    (α β : Fin d) :
    ∑ δ : Fin d, (g.coefficient z)⁻¹ α.succ δ.succ * g.secondFundamental 0 ε z β δ =
      ε / 2 * g.extrinsicRate z α β := by
  simp only [hs.secondFundamental_eq hz, extrinsicRate, metricRate, Finset.mul_sum]
  exact Finset.sum_congr rfl fun δ _ => by ring

end IsSynchronous

end ProjectAinos.SmoothGeometry.CoordinateMetric
