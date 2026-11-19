/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Virial
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Instances of the virial theorem

The improvement tensor `T^{μν} = (∂^μ ∂^ν − g^{μν} □) χ` of a `C³` function `χ` is `C¹`,
symmetric and conserved, `∂_μ T^{μν} = 0`, for every `χ` (`contDiff_improvementStress`,
`improvementStress_symm`, `improvementStress_conserved`). Its spatial trace is
`3 ∂₀∂₀χ − 2 Δχ` (`spatialTrace_improvementStress`), and it vanishes outside the closed support
of `χ`.

For `χ(t, x) = cos t · b(x)` with a bump function `b` that is supported in the cube `|xⁱ| < 2`
(`improvementPotential`, `improvement`):

* `tendsto_average_spatialTrace_improvement`: the tensor satisfies every hypothesis of
  `tendsto_average_spatialTrace` on the box `|xⁱ| ≤ 3`;
* `sliceIntegral_spatialTrace_improvement`: `∫ Σ_α T^{αα} d³x = −3 cos t ∫ b d³x`, with
  `integral_laplacianBump`: `∫ Δb d³x = 0` by the divergence theorem, and
  `integral_cubeBump_pos`: `∫ b d³x > 0`; so the integrand of the average is not zero
  (`sliceIntegral_spatialTrace_improvement_zero_ne`), and the average `−3 (sin τ / τ) ∫ b d³x`
  tends to `0` only because the time average of `cos t` does;
* `virialMoment_improvement`: the moment is `sin t ∫ Σ_α x^α ∂_α b d³x`.

`tendsto_average_energy_sub_restMass_cubeBump`: neutral dust at rest with the density `b(x)` and
without a field satisfies every hypothesis of `ChargedDust.tendsto_average_energy_sub_restMass`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace ProjectAinos.Electrodynamics.Virial.Examples

open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity

/-! ### Second derivatives -/

/-- The derivative of a `Cⁿ` function along a co-ordinate is `Cᵐ` for `m + 1 ≤ n`. -/
theorem contDiff_partialAt {m n : ℕ∞ω} {f : Spacetime → ℝ} (hf : ContDiff ℝ n f)
    (hmn : m + 1 ≤ n) (μ : Fin 4) : ContDiff ℝ m (partialAt f μ) :=
  (hf.fderiv_right hmn).clm_apply contDiff_const

/-- The second derivatives of a `C²` function commute. -/
theorem partialAt_comm {f : Spacetime → ℝ} (hf : ContDiff ℝ 2 f) (μ ν : Fin 4) :
    partialAt (partialAt f ν) μ = partialAt (partialAt f μ) ν := by
  funext x
  have hsymm : IsSymmSndFDerivAt ℝ f x := hf.contDiffAt.isSymmSndFDerivAt (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x
  have key (a b : Spacetime) :
      fderiv ℝ (fun y => fderiv ℝ f y b) x a = fderiv ℝ (fderiv ℝ f) x a b := by
    rw [fderiv_clm_apply hd (differentiableAt_const b)]
    simp
  change fderiv ℝ (fun y => fderiv ℝ f y (Pi.single ν 1)) x (Pi.single μ 1) =
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single μ 1)) x (Pi.single ν 1)
  rw [key, key]
  exact hsymm _ _

/-- The derivative vanishes outside the closed support. -/
theorem partialAt_eq_zero_of_notMem_tsupport {f : Spacetime → ℝ} {y : Spacetime}
    (hy : y ∉ tsupport f) (μ : Fin 4) : partialAt f μ y = 0 := by
  have h : fderiv ℝ f y = 0 :=
    Function.notMem_support.mp fun h => hy (support_fderiv_subset ℝ h)
  rw [partialAt, h]
  rfl

/-- The closed support of a derivative lies in that of the function. -/
theorem tsupport_partialAt_subset (f : Spacetime → ℝ) (μ : Fin 4) :
    tsupport (partialAt f μ) ⊆ tsupport f :=
  closure_minimal (fun _ hy => by_contra fun h => hy (partialAt_eq_zero_of_notMem_tsupport h μ))
    (isClosed_tsupport f)

/-! ### The improvement tensor -/

/-- The d'Alembertian `□χ = g^{λλ} ∂_λ ∂_λ χ`. -/
def dAlembertian (χ : Spacetime → ℝ) (y : Spacetime) : ℝ :=
  ∑ l : Fin 4, lorentzSign .timeNegative l * partialAt (partialAt χ l) l y

/-- The improvement tensor `T^{μν} = (∂^μ ∂^ν − g^{μν} □) χ` of a function `χ`. -/
def improvementStress (χ : Spacetime → ℝ) (μ ν : Fin 4) (y : Spacetime) : ℝ :=
  lorentzSign .timeNegative μ * lorentzSign .timeNegative ν * partialAt (partialAt χ ν) μ y -
    (if μ = ν then lorentzSign .timeNegative μ else 0) * dAlembertian χ y

/-- The improvement tensor of a `C³` function is `C¹`. -/
theorem contDiff_improvementStress {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 3 χ) (μ ν : Fin 4) :
    ContDiff ℝ 1 (improvementStress χ μ ν) := by
  have h2 : ∀ μ ν, ContDiff ℝ 1 (partialAt (partialAt χ ν) μ) := fun μ ν =>
    contDiff_partialAt (contDiff_partialAt hχ (m := 2) (by norm_num) ν) (by norm_num) μ
  have hbox : ContDiff ℝ 1 (dAlembertian χ) :=
    ContDiff.sum fun l _ => contDiff_const.mul (h2 l l)
  exact (contDiff_const.mul (h2 μ ν)).sub (contDiff_const.mul hbox)

/-- The improvement tensor of a `C²` function is symmetric. -/
theorem improvementStress_symm {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 2 χ) (μ ν : Fin 4)
    (y : Spacetime) : improvementStress χ μ ν y = improvementStress χ ν μ y := by
  rw [improvementStress, improvementStress, partialAt_comm hχ μ ν]
  by_cases h : μ = ν
  · subst h
    ring
  · simp only [h, Ne.symm h, ↓reduceIte, zero_mul, sub_zero]
    ring

/-- The improvement tensor of a `C³` function is conserved: `∂_μ T^{μν} = 0`. -/
theorem improvementStress_conserved {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 3 χ) (y : Spacetime)
    (ν : Fin 4) : ∑ μ : Fin 4, partialAt (improvementStress χ μ ν) μ y = 0 := by
  have h1 : ∀ μ, ContDiff ℝ 2 (partialAt χ μ) := fun μ =>
    contDiff_partialAt hχ (by norm_num) μ
  have hd2 : ∀ μ ν, DifferentiableAt ℝ (partialAt (partialAt χ ν) μ) y := fun μ ν =>
    (contDiff_partialAt (h1 ν) (m := 1) (by norm_num) μ).differentiable one_ne_zero y
  have hbox : DifferentiableAt ℝ (dAlembertian χ) y :=
    DifferentiableAt.fun_sum fun l _ => (hd2 l l).const_mul _
  have hthird : ∀ μ, partialAt (partialAt (partialAt χ ν) μ) μ y =
      partialAt (partialAt (partialAt χ μ) μ) ν y := by
    intro μ
    rw [partialAt_comm (hχ.of_le (by norm_num)) μ ν, partialAt_comm (h1 μ) μ ν]
  have hterm : ∀ μ, partialAt (improvementStress χ μ ν) μ y =
      lorentzSign .timeNegative μ * lorentzSign .timeNegative ν *
          partialAt (partialAt (partialAt χ μ) μ) ν y -
        (if μ = ν then lorentzSign .timeNegative μ else 0) * partialAt (dAlembertian χ) μ y := by
    intro μ
    rw [show improvementStress χ μ ν = fun y =>
        lorentzSign .timeNegative μ * lorentzSign .timeNegative ν *
            partialAt (partialAt χ ν) μ y -
          (if μ = ν then lorentzSign .timeNegative μ else 0) * dAlembertian χ y from rfl,
      partialAt_sub ((hd2 μ ν).const_mul _) (hbox.const_mul _),
      partialAt_const_mul _ (hd2 μ ν), partialAt_const_mul _ hbox, hthird]
  have hboxd : partialAt (dAlembertian χ) ν y = ∑ l : Fin 4,
      lorentzSign .timeNegative l * partialAt (partialAt (partialAt χ l) l) ν y := by
    rw [show dAlembertian χ = fun y => ∑ l : Fin 4,
        lorentzSign .timeNegative l * partialAt (partialAt χ l) l y from rfl,
      partialAt_sum _ fun l _ => (hd2 l l).const_mul _]
    exact Finset.sum_congr rfl fun l _ => partialAt_const_mul _ (hd2 l l) _
  rw [Finset.sum_congr rfl fun μ _ => hterm μ, Finset.sum_sub_distrib]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hboxd,
    Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_eq_zero fun μ _ => by ring

/-- The spatial trace of the improvement tensor is `3 ∂₀∂₀χ − 2 Δχ`. -/
theorem spatialTrace_improvementStress (χ : Spacetime → ℝ) (y : Spacetime) :
    spatialTrace (improvementStress χ) y = 3 * partialAt (partialAt χ 0) 0 y -
      2 * ∑ α : Fin 3, partialAt (partialAt χ α.succ) α.succ y := by
  simp only [spatialTrace, improvementStress, dAlembertian, Fin.sum_univ_succ (n := 3),
    lorentzSign_zero, lorentzSign_succ, ite_true]
  simp only [Fin.sum_univ_three]
  ring

/-- The components `T^{0α} = −∂₀∂_α χ` of the improvement tensor. -/
theorem improvementStress_zero_succ (χ : Spacetime → ℝ) (α : Fin 3) (y : Spacetime) :
    improvementStress χ 0 α.succ y = -partialAt (partialAt χ α.succ) 0 y := by
  simp only [improvementStress, (Fin.succ_ne_zero α).symm, ↓reduceIte, lorentzSign_zero,
    lorentzSign_succ, zero_mul, sub_zero]
  ring

/-- The improvement tensor vanishes outside the closed support of `χ`. -/
theorem improvementStress_eq_zero_of_notMem {χ : Spacetime → ℝ} {y : Spacetime}
    (hy : y ∉ tsupport χ) (μ ν : Fin 4) : improvementStress χ μ ν y = 0 := by
  have h : ∀ μ ν, partialAt (partialAt χ ν) μ y = 0 := fun μ ν =>
    partialAt_eq_zero_of_notMem_tsupport (fun h => hy (tsupport_partialAt_subset χ ν h)) μ
  simp [improvementStress, dAlembertian, h]

/-! ### Products of a function of the time and a function of space -/

/-- The spatial co-ordinates `(x¹, x², x³)` of a point of space-time. -/
def spatialPart : Spacetime →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ

/-- The components of `spatialPart y` are `y¹, y², y³`. -/
theorem spatialPart_apply (y : Spacetime) (i : Fin 3) : spatialPart y i = y i.succ := rfl

/-- The time axis has no spatial part. -/
theorem spatialPart_single_zero : spatialPart (Pi.single 0 1) = 0 := by
  funext i
  rw [spatialPart_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero i)]
  rfl

/-- The spatial part of the axis `i + 1` of space-time is the axis `i` of space. -/
theorem spatialPart_single_succ (i : Fin 3) :
    spatialPart (Pi.single i.succ 1) = Pi.single i 1 := by
  funext j
  rw [spatialPart_apply]
  by_cases h : j = i
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne fun h' => h (Fin.succ_injective _ h')]

/-- The spatial co-ordinates of the point `(t, z)` are `z`. -/
theorem insertNth_zero_succ (t : ℝ) (z : Fin 3 → ℝ) (α : Fin 3) :
    (Fin.insertNth 0 t z : Spacetime) α.succ = z α := by
  rw [Fin.insertNth_zero', Fin.cons_succ]

/-- The spatial part of the point `(t, z)` is `z`. -/
theorem spatialPart_insertNth (t : ℝ) (z : Fin 3 → ℝ) :
    spatialPart (Fin.insertNth 0 t z) = z :=
  funext fun α => insertNth_zero_succ t z α

/-- The derivative `∂ᵢ g` of a function on space. -/
def spatialPartial (g : (Fin 3 → ℝ) → ℝ) (i : Fin 3) (z : Fin 3 → ℝ) : ℝ :=
  fderiv ℝ g z (Pi.single i 1)

/-- The derivative of a `Cⁿ` function on space is `Cᵐ` for `m + 1 ≤ n`. -/
theorem contDiff_spatialPartial {m n : ℕ∞ω} {g : (Fin 3 → ℝ) → ℝ} (hg : ContDiff ℝ n g)
    (hmn : m + 1 ≤ n) (i : Fin 3) : ContDiff ℝ m (spatialPartial g i) :=
  (hg.fderiv_right hmn).clm_apply contDiff_const

/-- The derivative of a function on space vanishes outside its closed support. -/
theorem spatialPartial_eq_zero_of_notMem {g : (Fin 3 → ℝ) → ℝ} {z : Fin 3 → ℝ}
    (hz : z ∉ tsupport g) (i : Fin 3) : spatialPartial g i z = 0 := by
  have h : fderiv ℝ g z = 0 :=
    Function.notMem_support.mp fun h => hz (support_fderiv_subset ℝ h)
  rw [spatialPartial, h]
  rfl

/-- The product `f(t) g(x)` of a function of the time and a function of space. -/
def separated (f : ℝ → ℝ) (g : (Fin 3 → ℝ) → ℝ) : Spacetime → ℝ :=
  fun y => f (y 0) * g (spatialPart y)

/-- The value of `f(t) g(x)` at the point `(t, z)`. -/
theorem separated_insertNth (f : ℝ → ℝ) (g : (Fin 3 → ℝ) → ℝ) (t : ℝ) (z : Fin 3 → ℝ) :
    separated f g (Fin.insertNth 0 t z) = f t * g z := by
  rw [separated, Fin.insertNth_apply_same, spatialPart_insertNth]

/-- The product of a `Cⁿ` function of the time and a `Cⁿ` function of space is `Cⁿ`. -/
theorem contDiff_separated {n : ℕ∞ω} {f : ℝ → ℝ} {g : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ n f)
    (hg : ContDiff ℝ n g) : ContDiff ℝ n (separated f g) :=
  (hf.comp (contDiff_apply ℝ (fun _ => ℝ) 0)).mul (hg.comp spatialPart.contDiff)

/-- The derivative of `f(t) g(x)` along the co-ordinate `x^μ`, by the rule of Leibniz. -/
theorem partialAt_separated {f : ℝ → ℝ} {g : (Fin 3 → ℝ) → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (μ : Fin 4) (y : Spacetime) :
    partialAt (separated f g) μ y =
      f (y 0) * fderiv ℝ g (spatialPart y) (spatialPart (Pi.single μ 1)) +
        g (spatialPart y) * (deriv f (y 0) * (Pi.single μ 1 : Spacetime) 0) := by
  have h0 : HasFDerivAt (fun y : Spacetime => f (y 0))
      (deriv f (y 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0) y :=
    (hf (y 0)).hasDerivAt.comp_hasFDerivAt y
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).hasFDerivAt
  have h1 : HasFDerivAt (fun y => g (spatialPart y))
      ((fderiv ℝ g (spatialPart y)).comp spatialPart) y :=
    (hg (spatialPart y)).hasFDerivAt.comp y spatialPart.hasFDerivAt
  have h : HasFDerivAt (separated f g) (f (y 0) • (fderiv ℝ g (spatialPart y)).comp spatialPart +
      g (spatialPart y) •
        (deriv f (y 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0)) y :=
    h0.mul h1
  rw [partialAt, h.fderiv]
  rfl

/-- `∂₀ (f(t) g(x)) = f'(t) g(x)`. -/
theorem partialAt_separated_zero {f : ℝ → ℝ} {g : (Fin 3 → ℝ) → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) : partialAt (separated f g) 0 = separated (deriv f) g := by
  funext y
  rw [partialAt_separated hf hg, spatialPart_single_zero, map_zero, Pi.single_eq_same,
    separated]
  ring

/-- `∂ᵢ (f(t) g(x)) = f(t) ∂ᵢ g(x)`. -/
theorem partialAt_separated_succ {f : ℝ → ℝ} {g : (Fin 3 → ℝ) → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (i : Fin 3) :
    partialAt (separated f g) i.succ = separated f (spatialPartial g i) := by
  funext y
  rw [partialAt_separated hf hg, spatialPart_single_succ,
    Pi.single_eq_of_ne (Fin.succ_ne_zero i).symm, separated, spatialPartial]
  ring

/-- The closed support of `f(t) g(x)` lies over the closed support of `g`. -/
theorem tsupport_separated_subset (f : ℝ → ℝ) (g : (Fin 3 → ℝ) → ℝ) :
    tsupport (separated f g) ⊆ spatialPart ⁻¹' tsupport g :=
  tsupport_mul_subset_right.trans (tsupport_comp_subset_preimage g spatialPart.continuous)

/-! ### The bump function -/

/-- A bump function on space, equal to `1` on the cube `|xⁱ| ≤ 1` and supported in the cube
`|xⁱ| < 2` (the norm of `Fin 3 → ℝ` is the maximum norm). -/
def cubeBump : ContDiffBump (0 : Fin 3 → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The bump function is `C³`. -/
theorem contDiff_cubeBump : ContDiff ℝ 3 cubeBump := cubeBump.contDiff

/-- The closed support of the bump function is the cube `|xⁱ| ≤ 2`. -/
theorem tsupport_cubeBump : tsupport cubeBump = Metric.closedBall 0 2 := cubeBump.tsupport_eq

/-- A point with a co-ordinate of modulus at least `3` lies outside the closed support. -/
theorem notMem_closedBall_of_le_abs {z : Fin 3 → ℝ} {i : Fin 3} (hz : 3 ≤ |z i|) :
    z ∉ Metric.closedBall (0 : Fin 3 → ℝ) 2 := by
  intro h
  rw [mem_closedBall_zero_iff] at h
  have hi := norm_le_pi_norm z i
  rw [Real.norm_eq_abs] at hi
  linarith

/-- The cube `|xⁱ| ≤ 3` of space. -/
def cube : Set (Fin 3 → ℝ) := Icc (fun _ => -3) fun _ => 3

/-- The Laplacian `Δb = Σᵢ ∂ᵢ∂ᵢ b` of the bump function. -/
def laplacianBump (z : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, spatialPartial (spatialPartial cubeBump i) i z

/-- The Laplacian of the bump function is continuous. -/
theorem continuous_laplacianBump : Continuous laplacianBump :=
  continuous_finsetSum _ fun i _ => (contDiff_spatialPartial
    (contDiff_spatialPartial contDiff_cubeBump (m := 2) (by norm_num) i) (m := 0)
      (by norm_num) i).continuous

/-- The integral of the Laplacian of the bump function over the cube is zero, by the divergence
theorem: `∇b` vanishes on the faces. -/
theorem integral_laplacianBump : ∫ z in cube, laplacianBump z = 0 := by
  have hb1 : ∀ i, ContDiff ℝ 1 (spatialPartial cubeBump i) := fun i =>
    contDiff_spatialPartial contDiff_cubeBump (by norm_num) i
  let G : (Fin 3 → ℝ) → Fin 3 → ℝ := fun z i => spatialPartial cubeBump i z
  have hG : ∀ z, HasFDerivAt G
      (ContinuousLinearMap.pi fun i => fderiv ℝ (spatialPartial cubeBump i) z) z := fun z =>
    hasFDerivAt_pi.mpr fun i => ((hb1 i).differentiable one_ne_zero z).hasFDerivAt
  have hcont : Continuous G := continuous_pi fun i => (hb1 i).continuous
  have hface : ∀ (c : ℝ), 3 ≤ |c| → ∀ (i : Fin 3) (w : Fin 2 → ℝ),
      G (Fin.insertNth i c w) i = 0 := by
    intro c hc i w
    refine spatialPartial_eq_zero_of_notMem ?_ i
    rw [tsupport_cubeBump]
    refine notMem_closedBall_of_le_abs (i := i) ?_
    rwa [Fin.insertNth_apply_same]
  have h3 : ∀ (i : Fin 3) (w : Fin 2 → ℝ), G (Fin.insertNth i 3 w) i = 0 :=
    hface 3 (by norm_num)
  have hm3 : ∀ (i : Fin 3) (w : Fin 2 → ℝ), G (Fin.insertNth i (-3) w) i = 0 :=
    hface (-3) (by norm_num)
  have h := integral_divergence_of_hasFDerivAt_off_countable (fun _ : Fin 3 => (-3 : ℝ))
    (fun _ => 3) (fun _ => by norm_num) G
    (fun z => ContinuousLinearMap.pi fun i => fderiv ℝ (spatialPartial cubeBump i) z) ∅
    countable_empty hcont.continuousOn (fun z _ => hG z)
    (continuous_laplacianBump.continuousOn.integrableOn_compact isCompact_Icc)
  simp only [h3, hm3, integral_zero, sub_self, Finset.sum_const_zero] at h
  exact h

/-- The integral of the bump function over the cube is positive. -/
theorem integral_cubeBump_pos : 0 < ∫ z in cube, cubeBump z := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact cubeBump.integral_pos
  · intro z hz
    refine Function.notMem_support.mp fun hs => ?_
    have hzc : z ∉ Icc (fun _ : Fin 3 => (-3 : ℝ)) fun _ => 3 := hz
    rw [mem_Icc, not_and_or] at hzc
    have hball : z ∈ Metric.closedBall (0 : Fin 3 → ℝ) 2 := by
      rw [← tsupport_cubeBump]
      exact subset_tsupport _ hs
    rw [Pi.le_def, Pi.le_def, not_forall, not_forall] at hzc
    rcases hzc with ⟨i, hi⟩ | ⟨i, hi⟩
    · rw [not_le] at hi
      exact notMem_closedBall_of_le_abs (i := i) (by rw [abs_of_neg (by linarith)]; linarith)
        hball
    · rw [not_le] at hi
      exact notMem_closedBall_of_le_abs (i := i) (by rw [abs_of_pos (by linarith)]; linarith)
        hball

/-! ### The improvement tensor of `cos t · b(x)` -/

/-- The function `χ(t, x) = cos t · b(x)`. -/
def improvementPotential : Spacetime → ℝ := separated Real.cos cubeBump

/-- The improvement tensor `(∂^μ ∂^ν − g^{μν} □)(cos t · b(x))`. -/
def improvement : Fin 4 → Fin 4 → Spacetime → ℝ := improvementStress improvementPotential

/-- The lower corner of the box `|xⁱ| ≤ 3`. -/
def cubeLo : Spacetime := fun _ => -3

/-- The upper corner of the box `|xⁱ| ≤ 3`. -/
def cubeHi : Spacetime := fun _ => 3

/-- The function `cos t · b(x)` is `C³`. -/
theorem contDiff_improvementPotential : ContDiff ℝ 3 improvementPotential :=
  contDiff_separated Real.contDiff_cos contDiff_cubeBump

/-- The bump function is differentiable. -/
theorem differentiable_cubeBump : Differentiable ℝ cubeBump :=
  contDiff_cubeBump.differentiable (by norm_num)

/-- The derivatives of the bump function are differentiable. -/
theorem differentiable_spatialPartial_cubeBump (i : Fin 3) :
    Differentiable ℝ (spatialPartial cubeBump i) :=
  (contDiff_spatialPartial contDiff_cubeBump (m := 1) (by norm_num) i).differentiable one_ne_zero

/-- The derivative of `−sin` is `−cos`. -/
theorem deriv_neg_sin : deriv (fun x => -Real.sin x) = fun x => -Real.cos x :=
  funext fun x => (Real.hasDerivAt_sin x).neg.deriv

/-- `∂₀∂₀χ = −cos t · b(x)`. -/
theorem partialAt_improvementPotential_zero_zero :
    partialAt (partialAt improvementPotential 0) 0 =
      separated (fun x => -Real.cos x) cubeBump := by
  rw [improvementPotential,
    partialAt_separated_zero Real.differentiable_cos differentiable_cubeBump, Real.deriv_cos',
    partialAt_separated_zero (f := fun x => -Real.sin x) Real.differentiable_sin.neg
      differentiable_cubeBump, deriv_neg_sin]

/-- `∂_α∂_α χ = cos t · ∂_α∂_α b(x)`. -/
theorem partialAt_improvementPotential_succ_succ (α : Fin 3) :
    partialAt (partialAt improvementPotential α.succ) α.succ =
      separated Real.cos (spatialPartial (spatialPartial cubeBump α) α) := by
  rw [improvementPotential,
    partialAt_separated_succ Real.differentiable_cos differentiable_cubeBump,
    partialAt_separated_succ Real.differentiable_cos (differentiable_spatialPartial_cubeBump α)]

/-- `∂₀∂_α χ = −sin t · ∂_α b(x)`. -/
theorem partialAt_improvementPotential_succ_zero (α : Fin 3) :
    partialAt (partialAt improvementPotential α.succ) 0 =
      separated (fun x => -Real.sin x) (spatialPartial cubeBump α) := by
  rw [improvementPotential,
    partialAt_separated_succ Real.differentiable_cos differentiable_cubeBump,
    partialAt_separated_zero Real.differentiable_cos (differentiable_spatialPartial_cubeBump α),
    Real.deriv_cos']

/-- The improvement tensor is symmetric. -/
theorem improvement_symm (μ ν : Fin 4) (y : Spacetime) :
    improvement μ ν y = improvement ν μ y :=
  improvementStress_symm (contDiff_improvementPotential.of_le (by norm_num)) μ ν y

/-- The spatial trace on the time slice: `Σ_α T^{αα} = cos t · (−3 b − 2 Δb)`. -/
theorem spatialTrace_improvement (t : ℝ) (z : Fin 3 → ℝ) :
    spatialTrace improvement (Fin.insertNth 0 t z) =
      Real.cos t * (-3 * cubeBump z - 2 * laplacianBump z) := by
  rw [improvement, spatialTrace_improvementStress, partialAt_improvementPotential_zero_zero]
  simp only [partialAt_improvementPotential_succ_succ, separated_insertNth, laplacianBump,
    ← Finset.mul_sum]
  ring

/-- `∫ Σ_α T^{αα} d³x = −3 cos t ∫ b d³x` over the box `|xⁱ| ≤ 3`. -/
theorem sliceIntegral_spatialTrace_improvement (t : ℝ) :
    sliceIntegral (spatialTrace improvement) cubeLo cubeHi t =
      -3 * Real.cos t * ∫ z in cube, cubeBump z := by
  have hc : Icc (cubeLo ∘ Fin.succAbove 0) (cubeHi ∘ Fin.succAbove 0) = cube := rfl
  have hb : IntegrableOn (fun z => cubeBump z) cube :=
    contDiff_cubeBump.continuous.continuousOn.integrableOn_compact isCompact_Icc
  have hl : IntegrableOn laplacianBump cube :=
    continuous_laplacianBump.continuousOn.integrableOn_compact isCompact_Icc
  rw [sliceIntegral, hc]
  simp only [spatialTrace_improvement]
  rw [integral_const_mul, integral_sub (hb.const_mul _) (hl.const_mul _), integral_const_mul,
    integral_const_mul, integral_laplacianBump]
  ring

/-- The integrand of the average is not zero: at `t = 0`, `∫ Σ_α T^{αα} d³x = −3 ∫ b d³x`. -/
theorem sliceIntegral_spatialTrace_improvement_zero_ne :
    sliceIntegral (spatialTrace improvement) cubeLo cubeHi 0 ≠ 0 := by
  rw [sliceIntegral_spatialTrace_improvement, Real.cos_zero]
  exact mul_ne_zero (by norm_num) integral_cubeBump_pos.ne'

/-- The moment `∫ Σ_α x^α T^{0α} d³x = sin t ∫ Σ_α x^α ∂_α b d³x`. -/
theorem virialMoment_improvement (t : ℝ) :
    virialMoment improvement cubeLo cubeHi t =
      Real.sin t * ∫ z in cube, ∑ α : Fin 3, z α * spatialPartial cubeBump α z := by
  have hc : Icc (cubeLo ∘ Fin.succAbove 0) (cubeHi ∘ Fin.succAbove 0) = cube := rfl
  rw [virialMoment, charge, hc, ← integral_const_mul]
  congr 1
  funext z
  simp only [momentCurrent, improvement, improvementStress_zero_succ,
    partialAt_improvementPotential_succ_zero, separated_insertNth, insertNth_zero_succ,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun α _ => by ring

/-- The improvement tensor of `cos t · b(x)` satisfies every hypothesis of
`tendsto_average_spatialTrace` on the box `|xⁱ| ≤ 3`: it is `C¹` and conserved, vanishes
outside the cube `|xⁱ| < 2`, and its moment is bounded. By
`sliceIntegral_spatialTrace_improvement` the average is `−3 (sin τ / τ) ∫ b d³x`. -/
theorem tendsto_average_spatialTrace_improvement :
    Tendsto (fun τ : ℝ => (1 / τ) * ∫ t in (0 : ℝ)..τ,
      sliceIntegral (spatialTrace improvement) cubeLo cubeHi t) atTop (𝓝 0) := by
  refine tendsto_average_spatialTrace (T := improvement)
    (B := |∫ z in cube, ∑ α : Fin 3, z α * spatialPartial cubeBump α z|)
    (contDiff_improvementStress contDiff_improvementPotential)
    (fun i => by norm_num [cubeLo, cubeHi])
    (fun y _ ν => improvementStress_conserved contDiff_improvementPotential y ν) ?_ ?_
  · intro y _ hout μ ν
    refine improvementStress_eq_zero_of_notMem (fun hy => ?_) μ ν
    have h := tsupport_separated_subset Real.cos cubeBump hy
    rw [Set.mem_preimage, tsupport_cubeBump] at h
    obtain ⟨i, hi⟩ := hout
    refine notMem_closedBall_of_le_abs (i := i) ?_ h
    rw [spatialPart_apply]
    simp only [cubeLo, cubeHi] at hi
    rcases hi with hi | hi
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      linarith
  · intro t _
    rw [virialMoment_improvement, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one t)

/-! ### Static neutral dust -/

/-- The density `b(x)` of the rest mass, constant in time. -/
def staticDensity : Spacetime → ℝ := separated (fun _ => 1) cubeBump

/-- Neutral dust at rest with the density `b(x)` and without a field satisfies every hypothesis
of `ChargedDust.tendsto_average_energy_sub_restMass` on the box `|xⁱ| ≤ 3`. -/
theorem tendsto_average_energy_sub_restMass_cubeBump :
    Tendsto (fun τ : ℝ => (1 / τ) * ∫ t in (0 : ℝ)..τ,
      (sliceIntegral ((ChargedDust.staticNeutral staticDensity).totalStress (fun _ => 0) 0 0)
          cubeLo cubeHi t -
        sliceIntegral (ChargedDust.staticNeutral staticDensity).massDensity cubeLo cubeHi t))
      atTop (𝓝 0) := by
  refine ChargedDust.tendsto_average_energy_sub_restMass_static (μ₀ := staticDensity)
    ((contDiff_separated contDiff_const contDiff_cubeBump).of_le (by norm_num)) (fun y => ?_)
    (fun i => by norm_num [cubeLo, cubeHi]) (fun y _ hout => ?_)
  · rw [staticDensity, partialAt_separated_zero (differentiable_const _) differentiable_cubeBump]
    simp [separated]
  · obtain ⟨i, hi⟩ := hout
    have hz : spatialPart y ∉ tsupport cubeBump := by
      rw [tsupport_cubeBump]
      refine notMem_closedBall_of_le_abs (i := i) ?_
      rw [spatialPart_apply]
      simp only [cubeLo, cubeHi] at hi
      rcases hi with hi | hi
      · rw [abs_of_neg (by linarith)]
        linarith
      · rw [abs_of_pos (by linarith)]
        linarith
    rw [staticDensity, separated, image_eq_zero_of_notMem_tsupport hz, mul_zero]

end ProjectAinos.Electrodynamics.Virial.Examples
