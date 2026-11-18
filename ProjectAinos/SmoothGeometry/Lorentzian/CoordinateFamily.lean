/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateCurvature

/-!
# Families of coefficients and their derivatives in the parameter

A family of coefficient matrices `Cp : ℝ × E → Matrix` has, for each parameter `ε`, the slice
`z ↦ Cp (ε, z)`. Its Christoffel symbols, Ricci tensor, scalar curvature and density are the
formulas of `CoordinateCurvature.lean` applied to the slices, as functions of `(ε, z)`.

* `contDiffAt_familyChristoffel`, `contDiffAt_familyRicci`, `contDiffAt_familyScalar`,
  `contDiffAt_familyDensity`: these are smooth in `(ε, z)` where the family is smooth and its
  determinant does not vanish.
* `hasDerivAt_slice` and `hasDerivAt_fderiv_slice`: the derivative in `ε` of a slice, and of
  the derivative of a slice in `z`, the latter by the symmetry of second derivatives.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff Topology

namespace ProjectAinos.SmoothGeometry

/-! ### Derivatives in the parameter -/

section Slice

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative of a slice in the parameter. -/
theorem hasDerivAt_slice {Φ : ℝ × F → ℝ} {ε : ℝ} {x : F} (hΦ : DifferentiableAt ℝ Φ (ε, x)) :
    HasDerivAt (fun t => Φ (t, x)) (fderiv ℝ Φ (ε, x) (1, 0)) ε := by
  have hγ : HasDerivAt (fun t : ℝ => (t, x)) ((1 : ℝ), (0 : F)) ε :=
    (hasDerivAt_id ε).prodMk (hasDerivAt_const ε x)
  exact hΦ.hasFDerivAt.comp_hasDerivAt ε hγ

/-- The derivative of a slice in the second variable, through the derivative of the family. -/
theorem fderiv_slice_apply {Φ : ℝ × F → ℝ} {ε : ℝ} {x : F} (hΦ : DifferentiableAt ℝ Φ (ε, x))
    (v : F) : fderiv ℝ (fun z => Φ (ε, z)) x v = fderiv ℝ Φ (ε, x) (0, v) := by
  have hγ : HasFDerivAt (fun z : F => (ε, z)) (ContinuousLinearMap.inr ℝ ℝ F) x :=
    (hasFDerivAt_const ε x).prodMk (hasFDerivAt_id x)
  have h : HasFDerivAt (fun z => Φ (ε, z))
      ((fderiv ℝ Φ (ε, x)).comp (ContinuousLinearMap.inr ℝ ℝ F)) x :=
    hΦ.hasFDerivAt.comp x hγ
  rw [h.fderiv]
  rfl

/-- **The derivatives in the parameter and in the point commute.** For a family that is smooth
near `(0, x)`, the derivative in `ε` at `0` of `∂_v Φ(ε, x)` is `∂_v` of the derivative in
`ε`. -/
theorem hasDerivAt_fderiv_slice {Φ : ℝ × F → ℝ} {x : F} (hΦ : ContDiffAt ℝ ∞ Φ (0, x))
    (v : F) :
    HasDerivAt (fun ε => fderiv ℝ (fun z => Φ (ε, z)) x v)
      (fderiv ℝ (fun z => fderiv ℝ Φ (0, z) (1, 0)) x v) 0 := by
  set D := fderiv ℝ Φ
  have h2 : ∀ᶠ p in 𝓝 ((0 : ℝ), x), ContDiffAt ℝ 2 Φ p :=
    (hΦ.of_le (by simp)).eventually (by simp)
  have hγ : Filter.Tendsto (fun t : ℝ => (t, x)) (𝓝 0) (𝓝 ((0 : ℝ), x)) :=
    (continuous_id.prodMk continuous_const).tendsto' _ _ (by simp)
  have heq : ∀ᶠ t in 𝓝 (0 : ℝ),
      fderiv ℝ (fun z => Φ (t, z)) x v = D (t, x) (0, v) := by
    filter_upwards [hγ.eventually h2] with t ht
    exact fderiv_slice_apply (ht.differentiableAt (by simp)) v
  have hD : DifferentiableAt ℝ D ((0 : ℝ), x) :=
    (hΦ.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hpath : HasDerivAt (fun t : ℝ => (t, x)) ((1 : ℝ), (0 : F)) 0 :=
    (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) x)
  have hcomp : HasDerivAt (fun t : ℝ => D (t, x) ((0 : ℝ), v))
      (fderiv ℝ D ((0 : ℝ), x) ((1 : ℝ), (0 : F)) ((0 : ℝ), v)) 0 := by
    let ev : (ℝ × F →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), v)
    exact (ev.hasFDerivAt.comp _ hD.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hpath
  have hval : fderiv ℝ (fun z => D (0, z) (1, 0)) x v = fderiv ℝ D (0, x) (0, v) (1, 0) := by
    have hγ' : HasFDerivAt (fun z : F => ((0 : ℝ), z)) (ContinuousLinearMap.inr ℝ ℝ F) x :=
      (hasFDerivAt_const (0 : ℝ) x).prodMk (hasFDerivAt_id x)
    let ev : (ℝ × F →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : F))
    have h' : HasFDerivAt (fun z => D (0, z) ((1 : ℝ), (0 : F)))
        (ev.comp ((fderiv ℝ D ((0 : ℝ), x)).comp (ContinuousLinearMap.inr ℝ ℝ F))) x :=
      ev.hasFDerivAt.comp x (hD.hasFDerivAt.comp x hγ')
    rw [h'.fderiv]
    rfl
  have hsymm := (hΦ.isSymmSndFDerivAt (by simp)) ((1 : ℝ), (0 : F)) ((0 : ℝ), v)
  rw [hval, ← hsymm]
  exact hcomp.congr_of_eventuallyEq heq

end Slice

namespace CoordinateMetric

variable {d : ℕ}

/-! ### Families of coefficients -/

section Family

variable (Cp : ℝ × MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)

/-- The Christoffel symbols of the slices, as a function of `(ε, z)`. -/
def familyChristoffel (p : ℝ × MinkowskiModel d) (k i j : Fin (d + 1)) : ℝ :=
  christoffelOf (fun z => Cp (p.1, z)) p.2 k i j

/-- The Ricci tensor of the slices. -/
def familyRicci (p : ℝ × MinkowskiModel d) (j k : Fin (d + 1)) : ℝ :=
  ricciOf (fun z => Cp (p.1, z)) p.2 j k

/-- The scalar curvature of the slices. -/
def familyScalar (p : ℝ × MinkowskiModel d) : ℝ := scalarOf (fun z => Cp (p.1, z)) p.2

/-- The volume density of the slices. -/
def familyDensity (p : ℝ × MinkowskiModel d) : ℝ := densityOf (fun z => Cp (p.1, z)) p.2

variable {Cp} {p : ℝ × MinkowskiModel d}

/-- A partial derivative of a smooth function of `(ε, z)` in `z` is smooth in `(ε, z)`. -/
theorem contDiffAt_fderiv_snd {Φ : ℝ × MinkowskiModel d → ℝ} (hΦ : ContDiffAt ℝ ∞ Φ p)
    (v : MinkowskiModel d) :
    ContDiffAt ℝ ∞ (fun q : ℝ × MinkowskiModel d => fderiv ℝ (fun z => Φ (q.1, z)) q.2 v) p := by
  have hf : ContDiffAt ℝ ∞
      (Function.uncurry fun (q : ℝ × MinkowskiModel d) (z : MinkowskiModel d) => Φ (q.1, z))
      (p, p.2) := by
    have hm : ContDiffAt ℝ ∞
        (fun r : (ℝ × MinkowskiModel d) × MinkowskiModel d => (r.1.1, r.2)) (p, p.2) :=
      (contDiffAt_fst.comp _ contDiffAt_fst).prodMk contDiffAt_snd
    exact hΦ.comp (p, p.2) hm
  exact (hf.fderiv contDiffAt_snd (by simp)).clm_apply contDiffAt_const

theorem contDiffAt_familyInv (hC : ∀ i j, ContDiffAt ℝ ∞ (fun q => Cp q i j) p)
    (hdet : (Cp p).det ≠ 0) (k l : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (fun q => (Cp q)⁻¹ k l) p :=
  (contDiffAt_matrix_inv_apply hdet k l).comp p
    (contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => hC i j)

theorem contDiffAt_familyChristoffel (hC : ∀ i j, ContDiffAt ℝ ∞ (fun q => Cp q i j) p)
    (hdet : (Cp p).det ≠ 0) (k i j : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (fun q => familyChristoffel Cp q k i j) p := by
  unfold familyChristoffel christoffelOf
  refine ContDiffAt.sum fun l _ => ?_
  exact ((contDiffAt_familyInv hC hdet k l).mul
    (((contDiffAt_fderiv_snd (hC j l) _).add (contDiffAt_fderiv_snd (hC l i) _)).sub
      (contDiffAt_fderiv_snd (hC i j) _))).div_const 2

theorem contDiffAt_familyRicci (hC : ∀ i j, ContDiffAt ℝ ∞ (fun q => Cp q i j) p)
    (hdet : (Cp p).det ≠ 0) (j k : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (fun q => familyRicci Cp q j k) p := by
  have hΓ := contDiffAt_familyChristoffel hC hdet
  unfold familyRicci ricciOf
  refine ContDiffAt.sum fun i _ => ?_
  refine ((contDiffAt_fderiv_snd (hΓ i j k) _).sub (contDiffAt_fderiv_snd (hΓ i i k) _)).add
    (ContDiffAt.sum fun a _ => ?_)
  exact ((hΓ i i a).mul (hΓ a j k)).sub ((hΓ i j a).mul (hΓ a i k))

theorem contDiffAt_familyScalar (hC : ∀ i j, ContDiffAt ℝ ∞ (fun q => Cp q i j) p)
    (hdet : (Cp p).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => familyScalar Cp q) p := by
  unfold familyScalar scalarOf
  exact ContDiffAt.sum fun a _ => ContDiffAt.sum fun c _ =>
    (contDiffAt_familyRicci hC hdet a c).mul (contDiffAt_familyInv hC hdet a c)

theorem contDiffAt_familyDensity (hC : ∀ i j, ContDiffAt ℝ ∞ (fun q => Cp q i j) p)
    (hdet : (Cp p).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => familyDensity Cp q) p := by
  have hdetC : ContDiffAt ℝ ∞ (fun q => (Cp q).det) p :=
    MetricDensity.contDiff_matrix_det.contDiffAt.comp p
      (contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => hC i j)
  have habs : ContDiffAt ℝ ∞ (fun q => |(Cp q).det|) p := by
    rcases lt_or_gt_of_ne hdet with hneg | hpos
    · have hev : (fun q => |(Cp q).det|) =ᶠ[𝓝 p] fun q => -(Cp q).det := by
        filter_upwards [hdetC.continuousAt.eventually (gt_mem_nhds hneg)] with q hq
        exact abs_of_neg hq
      exact hdetC.neg.congr_of_eventuallyEq hev
    · have hev : (fun q => |(Cp q).det|) =ᶠ[𝓝 p] fun q => (Cp q).det := by
        filter_upwards [hdetC.continuousAt.eventually (lt_mem_nhds hpos)] with q hq
        exact abs_of_pos hq
      exact hdetC.congr_of_eventuallyEq hev
  unfold familyDensity densityOf
  exact habs.sqrt (abs_pos.mpr hdet).ne'

/-! ### Derivatives in the parameter at `ε = 0` -/

variable (Cp) in
/-- The derivative in `ε` at `0` of the Christoffel symbols, `δΓ^k_{ij}(z)`. -/
def familyChristoffelDeriv (z : MinkowskiModel d) (k i j : Fin (d + 1)) : ℝ :=
  fderiv ℝ (fun q => familyChristoffel Cp q k i j) ((0 : ℝ), z) (1, 0)

variable {x : MinkowskiModel d}

theorem hasDerivAt_familyChristoffel {k i j : Fin (d + 1)}
    (hΓ : ContDiffAt ℝ ∞ (fun q => familyChristoffel Cp q k i j) ((0 : ℝ), x)) :
    HasDerivAt (fun ε => familyChristoffel Cp (ε, x) k i j)
      (familyChristoffelDeriv Cp x k i j) 0 :=
  hasDerivAt_slice (hΓ.differentiableAt (by simp))

variable (Cp) in
/-- The first variation of the Ricci tensor in co-ordinates:
`δRic_{jk} = ∂_i δΓ^i_{jk} − ∂_j δΓ^i_{ik} + δΓ^i_{ia} Γ^a_{jk} + Γ^i_{ia} δΓ^a_{jk}
− δΓ^i_{ja} Γ^a_{ik} − Γ^i_{ja} δΓ^a_{ik}`. -/
def familyRicciDeriv (x : MinkowskiModel d) (j k : Fin (d + 1)) : ℝ :=
  ∑ i, (fderiv ℝ (fun z => familyChristoffelDeriv Cp z i j k) x (Pi.single i 1) -
    fderiv ℝ (fun z => familyChristoffelDeriv Cp z i i k) x (Pi.single j 1) +
    ∑ a, ((familyChristoffelDeriv Cp x i i a * familyChristoffel Cp (0, x) a j k +
        familyChristoffel Cp (0, x) i i a * familyChristoffelDeriv Cp x a j k) -
      (familyChristoffelDeriv Cp x i j a * familyChristoffel Cp (0, x) a i k +
        familyChristoffel Cp (0, x) i j a * familyChristoffelDeriv Cp x a i k)))

/-- **The first variation of the Ricci tensor.** -/
theorem hasDerivAt_familyRicci
    (hΓ : ∀ k i j, ContDiffAt ℝ ∞ (fun q => familyChristoffel Cp q k i j) ((0 : ℝ), x))
    (j k : Fin (d + 1)) :
    HasDerivAt (fun ε => familyRicci Cp (ε, x) j k) (familyRicciDeriv Cp x j k) 0 := by
  have hs (a b c : Fin (d + 1)) := hasDerivAt_familyChristoffel (Cp := Cp) (x := x) (hΓ a b c)
  have hf (a b c : Fin (d + 1)) (v : MinkowskiModel d) :=
    hasDerivAt_fderiv_slice (Φ := fun q => familyChristoffel Cp q a b c) (hΓ a b c) v
  unfold familyRicci ricciOf familyRicciDeriv
  refine HasDerivAt.fun_sum fun i _ => ?_
  refine ((hf i j k _).sub (hf i i k _)).add (HasDerivAt.fun_sum fun a _ => ?_)
  exact ((hs i i a).mul (hs a j k)).sub ((hs i j a).mul (hs a i k))

/-- The first variation of the scalar curvature, given the variation `Q` of the inverse. -/
theorem hasDerivAt_familyScalar
    (hΓ : ∀ k i j, ContDiffAt ℝ ∞ (fun q => familyChristoffel Cp q k i j) ((0 : ℝ), x))
    {Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hQ : ∀ a c, HasDerivAt (fun ε => (Cp (ε, x))⁻¹ a c) (Q a c) 0) :
    HasDerivAt (fun ε => familyScalar Cp (ε, x))
      (∑ a, ∑ c, (familyRicciDeriv Cp x a c * (Cp (0, x))⁻¹ a c +
        familyRicci Cp (0, x) a c * Q a c)) 0 := by
  unfold familyScalar scalarOf
  refine HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun c _ => ?_
  exact (hasDerivAt_familyRicci hΓ a c).mul (hQ a c)

end Family

end CoordinateMetric

end ProjectAinos.SmoothGeometry
