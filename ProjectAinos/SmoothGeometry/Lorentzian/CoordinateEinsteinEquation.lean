/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateMatter
public import ProjectAinos.SmoothGeometry.Lorentzian.EinsteinEquation
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Tensors that pair to zero with every metric variation

For a coordinate metric `g` on an open set `U` and a continuous symmetric field `E_{ik}` on `U`,
`∫ E_{ik} δg^{ik} √|g| dx = 0` for every smooth symmetric variation `h` with compact support in
`U` if and only if `E = 0` on `U` (`integral_inverseVariation_eq_zero_iff`). The variations
`φ (dx^p ⊗ dx^q + dx^q ⊗ dx^p)` with a bump function `φ` test each component of the raised
tensor `E^{pq}`; the fundamental lemma of the calculus of variations and the positivity of
`√|g|` give `E^{pq} = 0`, and lowering the indices gives `E = 0`.

The curvature formulas of the coefficients are smooth on `U` (`contDiffAt_ricciOf`,
`contDiffAt_scalarOf`, `contDiffAt_einsteinOf`), so the Einstein tensor is such a field.

A field of coefficients `T_{ik}` that is smooth on `U` is a smooth covariant two-tensor
`bilinearOf T hT` on the manifold `U`, and the equations `G_{ik} + Λ g_{ik} = κ T_{ik}` on `U` are
the native Einstein equations of `g.toLorentzMetric` (`satisfiesEinstein_bilinearOf_iff`).
-/

@[expose] public section

noncomputable section

open Bundle Set TopologicalSpace MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

/-- Raising both indices of a matrix with a symmetric matrix `A` is the product `A R A`. -/
theorem sum_mul_mul_eq_mul_mul {n : ℕ} (A R : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ a b, A a b = A b a) (m k : Fin n) :
    ∑ a, ∑ c, A m a * A k c * R a c = (A * R * A) m k := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by
    rw [hA k c]
    ring

namespace CoordinateMetric

variable {U : Opens (MinkowskiModel d)} {g : CoordinateMetric σ d U}

/-! ### Smoothness of the curvature formulas -/

theorem contDiffAt_ricciOf {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (fun z => ricciOf g.coefficient z j k) x := by
  have hC (i l : Fin (d + 1)) : ContDiffAt ℝ ∞
      (fun q : ℝ × MinkowskiModel d => g.coefficient q.2 i l) ((0 : ℝ), x) :=
    ((g.coefficient_contDiffOn i l).contDiffAt (U.isOpen.mem_nhds hx)).comp ((0 : ℝ), x)
      contDiffAt_snd
  have h0 := contDiffAt_familyRicci (Cp := fun q => g.coefficient q.2) hC
    (g.coefficient_det_ne_zero ⟨x, hx⟩) j k
  have hin : ContDiffAt ℝ ∞ (fun z : MinkowskiModel d => ((0 : ℝ), z)) x :=
    contDiffAt_const.prodMk contDiffAt_id
  exact h0.comp x hin

theorem contDiffAt_scalarOf {x : MinkowskiModel d} (hx : x ∈ U) :
    ContDiffAt ℝ ∞ (fun z => scalarOf g.coefficient z) x := by
  unfold scalarOf
  exact ContDiffAt.sum fun a _ => ContDiffAt.sum fun c _ => (contDiffAt_ricciOf hx a c).mul
    ((g.contDiffOn_coefficient_inv a c).contDiffAt (U.isOpen.mem_nhds hx))

theorem contDiffAt_einsteinOf {x : MinkowskiModel d} (hx : x ∈ U) (i k : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (fun z => einsteinOf g.coefficient z i k) x := by
  unfold einsteinOf
  exact (contDiffAt_ricciOf hx i k).sub (((contDiffAt_scalarOf hx).div_const 2).mul
    ((g.coefficient_contDiffOn i k).contDiffAt (U.isOpen.mem_nhds hx)))

theorem einsteinOf_symm {x : MinkowskiModel d} (hx : x ∈ U) (i k : Fin (d + 1)) :
    einsteinOf g.coefficient x i k = einsteinOf g.coefficient x k i := by
  rw [← toLorentzMetric_einstein_chartField ⟨x, hx⟩ ⟨x, hx⟩,
    ← toLorentzMetric_einstein_chartField ⟨x, hx⟩ ⟨x, hx⟩, einstein_symmetric]

theorem contDiffOn_scalarStress {φ : MinkowskiModel d → ℝ} (hφ : ContDiffOn ℝ ∞ φ U) (m : ℝ)
    (i k : Fin (d + 1)) : ContDiffOn ℝ ∞ (fun x => g.scalarStress m φ x i k) U := by
  have hd (a : Fin (d + 1)) : ContDiffOn ℝ ∞ (fun x => fderiv ℝ φ x (Pi.single a 1)) U :=
    (hφ.fderiv_of_isOpen U.isOpen (by simp)).clm_apply contDiffOn_const
  unfold scalarStress
  exact ((hd i).mul (hd k)).sub (((g.coefficient_contDiffOn i k).div_const 2).mul
    ((ContDiffOn.sum fun a _ => ContDiffOn.sum fun b _ =>
      (g.contDiffOn_coefficient_inv a b).mul ((hd a).mul (hd b))).add
        (contDiffOn_const.mul (hφ.pow 2))))

theorem contDiffOn_maxwellStress {F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hF : ∀ a b, ContDiffOn ℝ ∞ (fun x => F x a b) U) (i k : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun x => g.maxwellStress F x i k) U := by
  unfold maxwellStress maxwellProduct maxwellInvariant
  exact (ContDiffOn.sum fun b _ => ContDiffOn.sum fun e _ =>
    (g.contDiffOn_coefficient_inv b e).mul ((hF i b).mul (hF k e))).sub
      (((g.coefficient_contDiffOn i k).div_const 4).mul
        (ContDiffOn.sum fun a _ => ContDiffOn.sum fun b _ => ContDiffOn.sum fun c _ =>
          ContDiffOn.sum fun e _ => ((g.contDiffOn_coefficient_inv a c).mul
            (g.contDiffOn_coefficient_inv b e)).mul ((hF a b).mul (hF c e))))

theorem continuousOn_inverseVariation
    {h : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ}
    (hh : Continuous h) (i k : Fin (d + 1)) :
    ContinuousOn (fun x => g.inverseVariation h x i k) U := by
  have hinv (a b : Fin (d + 1)) : ContinuousOn (fun x => (g.coefficient x)⁻¹ a b) U :=
    (g.contDiffOn_coefficient_inv a b).continuousOn
  have hf (a b : Fin (d + 1)) : Continuous (fun x => formCoeff h x a b) :=
    (hh.clm_apply continuous_const).clm_apply continuous_const
  unfold inverseVariation
  simp only [Matrix.mul_apply]
  exact (continuousOn_finsetSum _ fun c _ => (continuousOn_finsetSum _ fun a _ =>
    (hinv i a).mul (hf a c).continuousOn).mul (hinv c k)).neg

theorem densityOf_pos {x : MinkowskiModel d} (hx : x ∈ U) : 0 < densityOf g.coefficient x :=
  Real.sqrt_pos.mpr (abs_pos.mpr (g.coefficient_det_ne_zero ⟨x, hx⟩))

/-- A function that is continuous on `U` and vanishes off a compact subset of `U` is
integrable. -/
theorem integrable_of_continuousOn {f : MinkowskiModel d → ℝ} {K : Set (MinkowskiModel d)}
    (hK : IsCompact K) (hKU : K ⊆ U) (hf : ContinuousOn f U) (h0 : ∀ x ∉ K, f x = 0) :
    Integrable f := by
  have hc : Continuous f := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    by_cases hx : x ∈ U
    · exact hf.continuousAt (U.isOpen.mem_nhds hx)
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds fun h' => hx (hKU h')] with z hz
      exact (h0 z hz).symm
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.intro hK h0)

/-! ### Symmetric test variations -/

/-- The symmetric form `v_p w_q + v_q w_p`. -/
def symmetricTest (p q : Fin (d + 1)) : MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj p : MinkowskiModel d →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj q : MinkowskiModel d →L[ℝ] ℝ) +
    (ContinuousLinearMap.proj q : MinkowskiModel d →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj p : MinkowskiModel d →L[ℝ] ℝ)

theorem symmetricTest_apply (p q : Fin (d + 1)) (v w : MinkowskiModel d) :
    symmetricTest p q v w = v p * w q + v q * w p := by
  simp [symmetricTest]

/-- The variation `φ (dx^p ⊗ dx^q + dx^q ⊗ dx^p)`. -/
def testVariation (φ : MinkowskiModel d → ℝ) (p q : Fin (d + 1)) (x : MinkowskiModel d) :
    MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ :=
  φ x • symmetricTest p q

theorem testVariation_apply (φ : MinkowskiModel d → ℝ) (p q : Fin (d + 1))
    (x v w : MinkowskiModel d) : testVariation φ p q x v w = φ x * (v p * w q + v q * w p) := by
  simp only [testVariation, smul_apply, smul_eq_mul, symmetricTest_apply]

theorem testVariation_symm (φ : MinkowskiModel d → ℝ) (p q : Fin (d + 1))
    (x v w : MinkowskiModel d) : testVariation φ p q x v w = testVariation φ p q x w v := by
  rw [testVariation_apply, testVariation_apply]
  ring

theorem contDiff_testVariation {φ : MinkowskiModel d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (p q : Fin (d + 1)) : ContDiff ℝ ∞ (testVariation φ p q) := by
  refine contDiff_clm_apply_iff.mpr fun v => contDiff_clm_apply_iff.mpr fun w => ?_
  simp only [testVariation_apply]
  exact hφ.mul contDiff_const

theorem support_testVariation (φ : MinkowskiModel d → ℝ) (p q : Fin (d + 1)) :
    Function.support (testVariation φ p q) ⊆ Function.support φ := by
  intro x hx hφx
  apply hx
  ext v w
  simp [testVariation_apply, hφx]

theorem tsupport_testVariation (φ : MinkowskiModel d → ℝ) (p q : Fin (d + 1)) :
    tsupport (testVariation φ p q) ⊆ tsupport φ :=
  closure_mono (support_testVariation φ p q)

theorem hasCompactSupport_testVariation {φ : MinkowskiModel d → ℝ} (hφ : HasCompactSupport φ)
    (p q : Fin (d + 1)) : HasCompactSupport (testVariation φ p q) :=
  hφ.mono' ((support_testVariation φ p q).trans (subset_tsupport φ))

theorem formCoeff_testVariation (φ : MinkowskiModel d → ℝ) (p q : Fin (d + 1))
    (x : MinkowskiModel d) (a b : Fin (d + 1)) :
    formCoeff (testVariation φ p q) x a b =
      φ x * ((if p = a then 1 else 0) * (if q = b then 1 else 0) +
        (if q = a then 1 else 0) * (if p = b then 1 else 0)) := by
  simp only [formCoeff, Matrix.of_apply, testVariation_apply, Pi.single_apply]

variable (g) in
/-- The tensor `E^{mn} = g^{ma} g^{nc} E_{ac}` with both indices raised. -/
def raised (E : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (m n : Fin (d + 1)) : ℝ :=
  ∑ a, ∑ c, (g.coefficient x)⁻¹ m a * (g.coefficient x)⁻¹ n c * E x a c

/-- The pairing with a test variation reads off `E^{pq} + E^{qp}`. -/
theorem sum_mul_inverseVariation_test {x : MinkowskiModel d} (hx : x ∈ U)
    (E : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (φ : MinkowskiModel d → ℝ)
    (p q : Fin (d + 1)) :
    ∑ i, ∑ k, E x i k * g.inverseVariation (testVariation φ p q) x i k =
      -(φ x * (g.raised E x p q + g.raised E x q p)) := by
  unfold inverseVariation
  rw [sum_mul_neg_sandwich _ _ _ (g.coefficient_inv_symmetric hx)]
  simp only [formCoeff_testVariation, mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [raised, raised]
  ring

/-- If the raised tensor vanishes at a point of `U`, so does the tensor. -/
theorem eq_zero_of_raised_eq_zero {x : MinkowskiModel d} (hx : x ∈ U)
    {E : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hE : ∀ m n, g.raised E x m n = 0) (i k : Fin (d + 1)) : E x i k = 0 := by
  have hdet := isUnit_iff_ne_zero.mpr (g.coefficient_det_ne_zero ⟨x, hx⟩)
  have h0 : (g.coefficient x)⁻¹ * E x * (g.coefficient x)⁻¹ = 0 := by
    ext m n
    rw [← sum_mul_mul_eq_mul_mul _ _ (g.coefficient_inv_symmetric hx)]
    exact hE m n
  have h1 : E x = g.coefficient x * ((g.coefficient x)⁻¹ * E x * (g.coefficient x)⁻¹) *
      g.coefficient x := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
  rw [h1, h0, Matrix.mul_zero, Matrix.zero_mul]
  rfl

theorem raised_symm {x : MinkowskiModel d}
    {E : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hsym : ∀ i k, E x i k = E x k i) (m n : Fin (d + 1)) :
    g.raised E x m n = g.raised E x n m := by
  rw [raised, raised, Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by
    rw [hsym a c]
    ring

theorem continuousOn_raised {E : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hE : ∀ i k, ContinuousOn (fun x => E x i k) U) (m n : Fin (d + 1)) :
    ContinuousOn (fun x => g.raised E x m n) U := by
  unfold raised
  exact continuousOn_finsetSum _ fun a _ => continuousOn_finsetSum _ fun c _ =>
    (((g.contDiffOn_coefficient_inv m a).continuousOn).mul
      (g.contDiffOn_coefficient_inv n c).continuousOn).mul (hE a c)

/-- **Tensors that pair to zero with every metric variation vanish.** For a continuous symmetric
field `E` on `U`, `∫ E_{ik} δg^{ik} √|g| dx = 0` for every smooth symmetric variation with
compact support in `U` if and only if `E = 0` on `U`. -/
theorem integral_inverseVariation_eq_zero_iff
    {E : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hE : ∀ i k, ContinuousOn (fun x => E x i k) U) (hsym : ∀ x ∈ U, ∀ i k, E x i k = E x k i) :
    (∀ h : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ,
      ContDiff ℝ ∞ h → HasCompactSupport h → tsupport h ⊆ U → (∀ z v w, h z v w = h z w v) →
        ∫ x, (∑ i, ∑ k, E x i k * g.inverseVariation h x i k) * densityOf g.coefficient x = 0) ↔
      ∀ x ∈ U, ∀ i k, E x i k = 0 := by
  constructor
  · intro hint x hx i k
    refine eq_zero_of_raised_eq_zero (g := g) hx (fun p q => ?_) i k
    set f : MinkowskiModel d → ℝ := fun z =>
      (g.raised E z p q + g.raised E z q p) * densityOf g.coefficient z
    have hfc : ContinuousOn f U :=
      ((continuousOn_raised hE p q).add (continuousOn_raised hE q p)).mul
        fun z hz => (contDiffAt_densityOf hz).continuousAt.continuousWithinAt
    have htest : ∀ φ : MinkowskiModel d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ U → ∫ z, φ z • f z = 0 := by
      intro φ hφ hφK hφU
      have h0 := hint (testVariation φ p q) (contDiff_testVariation hφ p q)
        (hasCompactSupport_testVariation hφK p q) ((tsupport_testVariation φ p q).trans hφU)
        (testVariation_symm φ p q)
      have hpt : ∀ z, (∑ i, ∑ k, E z i k * g.inverseVariation (testVariation φ p q) z i k) *
          densityOf g.coefficient z = -(φ z • f z) := by
        intro z
        by_cases hz : z ∈ U
        · rw [sum_mul_inverseVariation_test hz]
          simp only [f, smul_eq_mul]
          ring
        · have hzφ : z ∉ tsupport φ := fun h' => hz (hφU h')
          have hzh : z ∉ tsupport (testVariation φ p q) :=
            fun h' => hzφ (tsupport_testVariation φ p q h')
          simp [inverseVariation_of_notMem hzh, image_eq_zero_of_notMem_tsupport hzφ]
      simp_rw [hpt, integral_neg] at h0
      exact neg_eq_zero.mp h0
    have hae := U.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hfc.locallyIntegrableOn U.isOpen.measurableSet) htest
    have heq := Measure.eqOn_open_of_ae_eq (μ := volume)
      ((ae_restrict_iff' U.isOpen.measurableSet).mpr hae) U.isOpen hfc continuousOn_const hx
    have hsum : g.raised E x p q + g.raised E x q p = 0 :=
      (mul_eq_zero.mp heq).resolve_right (densityOf_pos hx).ne'
    rw [raised_symm (hsym x hx) q p] at hsum
    linarith
  · intro h0 h _ _ hKU _
    have hpt : ∀ x, (∑ i, ∑ k, E x i k * g.inverseVariation h x i k) *
        densityOf g.coefficient x = 0 := by
      intro x
      by_cases hx : x ∈ U
      · simp [h0 x hx]
      · simp [inverseVariation_of_notMem fun h' => hx (hKU h')]
    simp [hpt]

/-! ### Native tensors from coefficients -/

/-- The bilinear form `v, w ↦ T_{ik} v^i w^k`. -/
def coefficientForm (T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) : MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ :=
  ∑ i, ∑ k, T x i k • (ContinuousLinearMap.proj i : MinkowskiModel d →L[ℝ] ℝ).smulRight
    (ContinuousLinearMap.proj k : MinkowskiModel d →L[ℝ] ℝ)

theorem coefficientForm_apply (T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x v w : MinkowskiModel d) :
    coefficientForm T x v w = ∑ i, ∑ k, T x i k * (v i * w k) := by
  simp [coefficientForm, smul_eq_mul]

theorem coefficientForm_single (T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (i k : Fin (d + 1)) :
    coefficientForm T x (Pi.single i 1) (Pi.single k 1) = T x i k := by
  rw [coefficientForm_apply]
  simp [Pi.single_apply]

theorem contDiffOn_coefficientForm
    {T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hT : ∀ i k, ContDiffOn ℝ ∞ (fun x => T x i k) U) :
    ContDiffOn ℝ ∞ (coefficientForm T) U := by
  refine contDiffOn_clm_apply.mpr fun v => contDiffOn_clm_apply.mpr fun w => ?_
  simp only [coefficientForm_apply]
  exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun k _ => (hT i k).mul contDiffOn_const

/-- The smooth covariant two-tensor on `U` with the coefficients `T_{ik}`. -/
def bilinearOf (T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hT : ∀ i k, ContDiffOn ℝ ∞ (fun x => T x i k) U) :
    Tensor.SmoothBilinear («I» := 𝓘(ℝ, MinkowskiModel d)) (M := U) :=
  ⟨fun x => coefficientForm T x, by
    have hs := (contDiffOn_coefficientForm hT).contMDiffOn.comp_contMDiff
      (contMDiff_subtype_val (U := U)) (fun x : U => x.property)
    intro x
    refine (contMDiffAt_section x).mpr ?_
    convert hs x using 1
    funext y
    ext v w
    have hy : y ∈ (trivializationAt (MinkowskiModel d)
        (TangentSpace 𝓘(ℝ, MinkowskiModel d)) x).baseSet := by
      change y ∈ (physicalChart x).source
      simp
    rw [hom_trivializationAt_apply, inCoordinates_apply_eq₂ hy hy (by simp),
      ← Trivialization.symmL_apply (R := ℝ) _ hy, ← Trivialization.symmL_apply (R := ℝ) _ hy,
      physicalChart_symmL]
    simp
    rfl⟩

theorem bilinearOf_apply (T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hT : ∀ i k, ContDiffOn ℝ ∞ (fun x => T x i k) U) (y : U)
    (v w : TangentSpace 𝓘(ℝ, MinkowskiModel d) y) :
    bilinearOf T hT y v w = coefficientForm T y v w := rfl

/-- The coefficients of `bilinearOf T hT` on the co-ordinate fields are `T_{ik}`. -/
theorem bilinearOf_chartField (T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hT : ∀ i k, ContDiffOn ℝ ∞ (fun x => T x i k) U) (x y : U) (i k : Fin (d + 1)) :
    bilinearOf T hT y (chartField (physicalChart x) (Pi.single i 1) y)
      (chartField (physicalChart x) (Pi.single k 1) y) = T y i k := by
  rw [bilinearOf_apply, physicalChart_chartField, physicalChart_chartField,
    coefficientForm_single]

variable (g) in
/-- The Einstein equations `G_{ik} + Λ g_{ik} = κ T_{ik}` on `U`, in the co-ordinates. -/
def IsEinstein (κ Λ : ℝ) (T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) : Prop :=
  ∀ x ∈ U, ∀ i k, einsteinOf g.coefficient x i k + Λ * g.coefficient x i k = κ * T x i k

/-- **The co-ordinate equations are the native Einstein equations.** -/
theorem satisfiesEinstein_bilinearOf_iff
    {T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hT : ∀ i k, ContDiffOn ℝ ∞ (fun x => T x i k) U) (κ Λ : ℝ) :
    g.toLorentzMetric.SatisfiesEinstein κ Λ (bilinearOf T hT) ↔ g.IsEinstein κ Λ T := by
  have hform (x y : U) (i k : Fin (d + 1)) :
      g.toLorentzMetric.form y (chartField (physicalChart x) (Pi.single i 1) y)
        (chartField (physicalChart x) (Pi.single k 1) y) = g.coefficient y i k :=
    g.toLorentzMetric_chartComponent x y i k
  constructor
  · intro h x hx i k
    have h1 := congrArg (fun B => B (chartField (physicalChart ⟨x, hx⟩) (Pi.single i 1) ⟨x, hx⟩)
      (chartField (physicalChart ⟨x, hx⟩) (Pi.single k 1) ⟨x, hx⟩)) (h ⟨x, hx⟩)
    simp only [add_apply, smul_apply, smul_eq_mul] at h1
    rwa [toLorentzMetric_einstein_chartField, hform, bilinearOf_chartField] at h1
  · intro h y
    refine ext_chartField (physicalChart_mem y) (by simp) fun i => ?_
    refine ext_chartField (physicalChart_mem y) (by simp) fun k => ?_
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [toLorentzMetric_einstein_chartField, hform, bilinearOf_chartField]
    exact h y y.property i k

end CoordinateMetric

end ProjectAinos.SmoothGeometry
