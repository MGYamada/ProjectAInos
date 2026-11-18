/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.InertialDerivatives

/-! # The contracted Bianchi identity and the Einstein tensor

For a smooth Lorentz metric of either sign convention and in every dimension:

* `bilinearDivergenceCovector g B x b = ∇^a B_{ab}`, the divergence of a smooth covariant
  two-tensor on its first index.
* `ricci_contracted_bianchi`: `∇^a Ric_{ab} = ½ ∂_b R` (Landau–Lifshitz, §92).
* `einstein x = Ric − (R/2) g`, symmetric and smooth, with trace `(1 − n/2) R` in dimension
  `n = d + 1`, and `einstein_divergence_eq_zero`: `∇^a G_{ab} = 0`.

The contracted identity is proved at the centre of an inertial chart. There the Christoffel
symbols and the derivatives of `g^{ij}` vanish, so the covariant derivatives of the Ricci and
Riemann components are their partial derivatives, and the second Bianchi identity contracted
twice is an identity between real arrays (`contracted_bianchi_algebra`).
-/

@[expose] public section
noncomputable section

open Bundle FiberBundle VectorField ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)

local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "E" => MinkowskiModel d
local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

local instance (x : M) : T2Space (TM x) := FiberBundle.t2Space E TM x
local instance (x : M) : FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x

/-- The divergence `∇^a B_{ab}` of a smooth covariant two-tensor, contracting its first slot with
the direction of differentiation. -/
def bilinearDivergenceCovector (B : Tensor.SmoothBilinear («I» := I) (M := M)) (x : M) :
    TM x →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun v := g.contract x ((Tensor.bilinearCovariantDerivative g.leviCivita B x).flip v)
    map_add' v w := by rw [map_add, g.contract_add]
    map_smul' r v := by rw [map_smul, g.contract_smul]; rfl }

@[simp] theorem bilinearDivergenceCovector_apply
    (B : Tensor.SmoothBilinear («I» := I) (M := M)) (x : M) (v : TM x) :
    g.bilinearDivergenceCovector B x v =
      g.contract x ((Tensor.bilinearCovariantDerivative g.leviCivita B x).flip v) := rfl

/-- The Ricci tensor as a smooth bilinear section. -/
def ricciBilinear : Tensor.SmoothBilinear («I» := I) (M := M) := ⟨g.ricci, g.ricci_smooth⟩

@[simp] theorem ricciBilinear_apply (x : M) : g.ricciBilinear x = g.ricci x := rfl

/-- The second Bianchi identity contracted twice, as an identity between real arrays:
`DR m l i j k = ∂_m R^l_{ijk}`, `DRic c a b = ∂_c Ric_{ab}` and `G a c = g^{ac}` at a point
where the derivatives of `g^{ac}` vanish. -/
private theorem contracted_bianchi_algebra {n : ℕ} (G : Fin n → Fin n → ℝ)
    (DR : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ)
    (DRic : Fin n → Fin n → Fin n → ℝ) (hG : ∀ a c, G a c = G c a)
    (hRic : ∀ c a b, DRic c a b = ∑ i, DR c i i a b)
    (hsymm : ∀ c a b, DRic c a b = DRic c b a)
    (hswap : ∀ m l i j k, DR m l i j k = -DR m l j i k)
    (hbianchi : ∀ m l i j k, DR m l i j k + DR i l j m k + DR j l m i k = 0)
    (hcontr : ∀ i j, ∑ m, ∑ k, DR i i j m k * G m k = ∑ l, DRic i l j * G l i) (j : Fin n) :
    ∑ a, ∑ c, DRic c a j * G a c = (∑ a, ∑ c, DRic j a c * G a c) / 2 := by
  have h1 (m k : Fin n) : DRic m j k + ∑ i, DR i i j m k - DRic j m k = 0 := by
    have h := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hbianchi m i i j k
    rw [Finset.sum_const_zero] at h
    simp only [Finset.sum_add_distrib] at h
    have hl : ∑ i, DR j i m i k = -DRic j m k := by
      rw [hRic, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => hswap j i m i k
    rw [← hRic, hl] at h
    linarith
  have h2 : ∑ m, ∑ k, (DRic m j k + ∑ i, DR i i j m k - DRic j m k) * G m k = 0 := by
    simp only [h1, zero_mul, Finset.sum_const_zero]
  simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_mul] at h2
  have hmid : ∑ m, ∑ k, ∑ i, DR i i j m k * G m k = ∑ a, ∑ c, DRic c a j * G a c := by
    calc ∑ m, ∑ k, ∑ i, DR i i j m k * G m k
        = ∑ m, ∑ i, ∑ k, DR i i j m k * G m k :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ i, ∑ m, ∑ k, DR i i j m k * G m k := Finset.sum_comm
      _ = ∑ i, ∑ l, DRic i l j * G l i := Finset.sum_congr rfl fun i _ => hcontr i j
      _ = ∑ a, ∑ c, DRic c a j * G a c := Finset.sum_comm
  have hfirst : ∑ m, ∑ k, DRic m j k * G m k = ∑ a, ∑ c, DRic c a j * G a c := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [hsymm c j a, hG c a]
  rw [hmid, hfirst] at h2
  linarith

/-- **The contracted Bianchi identity** `∇^a Ric_{ab} = ½ ∂_b R`. -/
theorem ricci_contracted_bianchi (x : M) (v : TM x) :
    g.bilinearDivergenceCovector g.ricciBilinear x v =
      mvfderiv I (fun y => g.scalarCurvature y) x v / 2 := by
  obtain ⟨e, h⟩ := g.exists_inertialChart x
  have he := h.smooth
  have hx := h.mem_source
  have hsrc : ∀ᶠ y in 𝓝 x, y ∈ e.source := e.open_source.mem_nhds hx
  have hRm (a b : Fin (d + 1)) : MDifferentiableAt I 𝓘(ℝ)
      (fun y => g.ricci y (chartField e (Pi.single a 1) y) (chartField e (Pi.single b 1) y)) x :=
    g.ricciBilinear.mdifferentiableAt_apply (chartField_mdifferentiableAt he hx _)
      (chartField_mdifferentiableAt he hx _)
  have hRc (l i j k : Fin (d + 1)) :
      MDifferentiableAt I 𝓘(ℝ) (fun y => g.chartCurvature e y l i j k) x :=
    (g.chartCurvature_contMDiffAt he hx l i j k).mdifferentiableAt (by simp)
  have hGm (a c : Fin (d + 1)) :
      MDifferentiableAt I 𝓘(ℝ) (fun y => g.chartInverse e y a c) x :=
    (g.chartInverse_contMDiffAt he hx a c).mdifferentiableAt (by simp)
  let G : Fin (d + 1) → Fin (d + 1) → ℝ := fun a c => g.chartInverse e x a c
  let DR : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ :=
    fun m l i j k => mvfderiv I (fun y => g.chartCurvature e y l i j k) x
      (chartField e (Pi.single m 1) x)
  let DRic : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ := fun c a b =>
    mvfderiv I (fun y => g.ricci y (chartField e (Pi.single a 1) y)
      (chartField e (Pi.single b 1) y)) x (chartField e (Pi.single c 1) x)
  have hG (a c : Fin (d + 1)) : G a c = G c a := g.chartInverse_symmetric e x a c
  have hRic (c a b : Fin (d + 1)) : DRic c a b = ∑ i, DR c i i a b := by
    have heq : (fun y => g.ricci y (chartField e (Pi.single a 1) y)
        (chartField e (Pi.single b 1) y)) =ᶠ[𝓝 x]
          fun y => ∑ i, g.chartCurvature e y i i a b := by
      filter_upwards [hsrc] with y hy
      exact g.ricci_chartField he hy a b
    simp only [DRic, DR]
    rw [mvfderiv_congr_of_eventuallyEq (d := d) heq,
      mvfderiv_finset_sum Finset.univ fun i _ => hRc i i a b, sum_apply]
  have hsymm (c a b : Fin (d + 1)) : DRic c a b = DRic c b a := by
    simp only [DRic]
    rw [show (fun y => g.ricci y (chartField e (Pi.single a 1) y)
        (chartField e (Pi.single b 1) y)) = fun y => g.ricci y
          (chartField e (Pi.single b 1) y) (chartField e (Pi.single a 1) y) from
      funext fun y => g.ricci_symmetric y _ _]
  have hswap (m l i j k : Fin (d + 1)) : DR m l i j k = -DR m l j i k := by
    simp only [DR]
    rw [show (fun y => g.chartCurvature e y l i j k) =
        fun y => -g.chartCurvature e y l j i k from funext fun y => by
      simp only [chartCurvature]
      rw [g.curvature_swap y (chartField e (Pi.single i 1) y)]
      simp only [map_neg, Pi.neg_apply],
      mvfderiv_fun_neg, neg_apply]
  have hbianchi (m l i j k : Fin (d + 1)) : DR m l i j k + DR i l j m k + DR j l m i k = 0 := by
    have hb := g.chartCurvatureDerivative_bianchi e x l i j k m
    rw [h.chartCurvatureDerivative_eq, h.chartCurvatureDerivative_eq,
      h.chartCurvatureDerivative_eq] at hb
    exact hb
  have hcontr (i j : Fin (d + 1)) :
      ∑ m, ∑ k, DR i i j m k * G m k = ∑ l, DRic i l j * G l i := by
    have heq : (fun y => ∑ m, ∑ k, g.chartCurvature e y i j m k * g.chartInverse e y m k)
        =ᶠ[𝓝 x] fun y => ∑ l, g.ricci y (chartField e (Pi.single l 1) y)
          (chartField e (Pi.single j 1) y) * g.chartInverse e y l i := by
      filter_upwards [hsrc] with y hy
      exact g.chartCurvature_contract he hy i j
    have hd : mvfderiv I (fun y => ∑ m, ∑ k, g.chartCurvature e y i j m k *
          g.chartInverse e y m k) x (chartField e (Pi.single i 1) x) =
        mvfderiv I (fun y => ∑ l, g.ricci y (chartField e (Pi.single l 1) y)
          (chartField e (Pi.single j 1) y) * g.chartInverse e y l i) x
          (chartField e (Pi.single i 1) x) := by
      rw [mvfderiv_congr_of_eventuallyEq (d := d) heq]
    rw [mvfderiv_sum_sum_mul_of_mvfderiv_eq_zero (fun m k => hRc i j m k) (fun m k => hGm m k)
        (fun m k => h.mvfderiv_chartInverse m k),
      mvfderiv_sum_mul_of_mvfderiv_eq_zero Finset.univ (fun l _ => hRm l j) (fun l _ => hGm l i)
        (fun l _ => h.mvfderiv_chartInverse l i)] at hd
    simp only [sum_apply, smul_apply, smul_eq_mul] at hd
    simp only [DR, DRic, G]
    simpa only [mul_comm] using hd
  have hj (j : Fin (d + 1)) :
      g.bilinearDivergenceCovector g.ricciBilinear x (chartField e (Pi.single j 1) x) =
        ((2⁻¹ : ℝ) • mvfderiv I (fun y => g.scalarCurvature y) x)
          (chartField e (Pi.single j 1) x) := by
    have hL : g.bilinearDivergenceCovector g.ricciBilinear x (chartField e (Pi.single j 1) x) =
        ∑ a, ∑ c, DRic c a j * G a c := by
      rw [bilinearDivergenceCovector_apply, g.contract_chart he hx]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
      rw [flip_apply, h.bilinearCovariantDerivative_chartField]
      rfl
    have hS : (fun y => g.scalarCurvature y) =ᶠ[𝓝 x] fun y => ∑ a, ∑ c,
        g.ricci y (chartField e (Pi.single a 1) y) (chartField e (Pi.single c 1) y) *
          g.chartInverse e y a c := by
      filter_upwards [hsrc] with y hy
      exact g.scalarCurvature_chart he hy
    have hR : mvfderiv I (fun y => g.scalarCurvature y) x (chartField e (Pi.single j 1) x) =
        ∑ a, ∑ c, DRic j a c * G a c := by
      rw [mvfderiv_congr_of_eventuallyEq (d := d) hS,
        mvfderiv_sum_sum_mul_of_mvfderiv_eq_zero (fun a c => hRm a c) (fun a c => hGm a c)
          (fun a c => h.mvfderiv_chartInverse a c)]
      simp only [sum_apply, smul_apply, smul_eq_mul, DRic, G]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => mul_comm _ _
    rw [smul_apply, smul_eq_mul, hL, hR,
      contracted_bianchi_algebra G DR DRic hG hRic hsymm hswap hbianchi hcontr j]
    ring
  rw [ext_chartField he hx (L := g.bilinearDivergenceCovector g.ricciBilinear x)
    (L' := (2⁻¹ : ℝ) • mvfderiv I (fun y => g.scalarCurvature y) x) hj, smul_apply,
    smul_eq_mul]
  ring

/-- The Einstein tensor `G = Ric − (R/2) g`. -/
def einstein (x : M) : TM x →L[ℝ] TM x →L[ℝ] ℝ :=
  g.ricci x - (g.scalarCurvature x / 2) • g.form x

@[simp] theorem einstein_apply (x : M) (u v : TM x) :
    g.einstein x u v = g.ricci x u v - g.scalarCurvature x / 2 * g.form x u v := by
  simp only [einstein, sub_apply, smul_apply, smul_eq_mul]

theorem einstein_symmetric (x : M) (u v : TM x) : g.einstein x u v = g.einstein x v u := by
  rw [einstein_apply, einstein_apply, g.ricci_symmetric, g.symmetric]

theorem einstein_smooth :
    ContMDiff I ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (g.einstein x)) := by
  have hS : ContMDiff I 𝓘(ℝ) ∞ (fun x => g.scalarCurvature x / 2) := by
    simpa only [div_eq_mul_inv, Pi.mul_def] using
      g.scalarCurvature.contMDiff.mul (contMDiff_const (c := (2⁻¹ : ℝ)))
  exact g.ricci_smooth.sub_section (hS.smul_section g.smooth)

/-- The Einstein tensor as a smooth bilinear section. -/
def einsteinBilinear : Tensor.SmoothBilinear («I» := I) (M := M) :=
  ⟨g.einstein, g.einstein_smooth⟩

@[simp] theorem einsteinBilinear_apply (x : M) : g.einsteinBilinear x = g.einstein x := rfl

/-- The Einstein tensor as a smooth covariant two-tensor. -/
def einsteinTensor : CovariantTwoTensor d M := ⟨g.einstein, g.einstein_smooth⟩

/-- The Einstein tensor does not depend on the overall sign of the metric. -/
@[simp] theorem einstein_opposite (x : M) : g.opposite.einstein x = g.einstein x := by
  ext u v
  simp only [einstein_apply, ricci_opposite, scalarCurvature_opposite, opposite_form,
    neg_apply]
  ring

/-- The trace of the Einstein tensor is `(1 − n/2) R` in dimension `n = d + 1`. -/
theorem contract_einstein (x : M) :
    g.contract x (g.einstein x) = (1 - ((d : ℝ) + 1) / 2) * g.scalarCurvature x := by
  rw [einstein, g.contract_sub, g.contract_smul, contract_metric, ← scalarCurvature_apply]
  ring

/-- Away from dimension two, the Einstein tensor vanishes only where the Ricci tensor does. -/
theorem ricci_eq_zero_of_einstein_eq_zero (hd : d ≠ 1) {x : M} (h : g.einstein x = 0) :
    g.ricci x = 0 := by
  have hc := g.contract_einstein x
  have h0 : g.contract x 0 = 0 := by simp [contract]
  rw [h, h0] at hc
  have hcoef : (1 - ((d : ℝ) + 1) / 2) ≠ 0 := by
    intro h'
    apply hd
    have hd1 : (d : ℝ) = 1 := by linarith
    exact_mod_cast hd1
  have hS : g.scalarCurvature x = 0 :=
    (mul_eq_zero.mp hc.symm).resolve_left hcoef
  have he : g.einstein x = g.ricci x := by
    ext u v
    simp [hS]
  rw [← he, h]

/-- The covariant derivative of the Einstein tensor:
`∇_u G(v, w) = ∇_u Ric(v, w) − ½ ∂_u R g(v, w)`. -/
theorem bilinearCovariantDerivative_einstein (x : M) (v w u : TM x) :
    Tensor.bilinearCovariantDerivative g.leviCivita g.einsteinBilinear x v w u =
      Tensor.bilinearCovariantDerivative g.leviCivita g.ricciBilinear x v w u -
        mvfderiv I (fun y => g.scalarCurvature y) x u / 2 * g.form x v w := by
  have hV : MDifferentiableAt I ((I).prod I) (T% (extend E v)) x :=
    mdifferentiableAt_extend I E v
  have hW : MDifferentiableAt I ((I).prod I) (T% (extend E w)) x :=
    mdifferentiableAt_extend I E w
  have hSd : MDifferentiableAt I 𝓘(ℝ) (fun y => g.scalarCurvature y) x :=
    (g.scalarCurvature.contMDiff x).mdifferentiableAt (by simp)
  have hS2 : MDifferentiableAt I 𝓘(ℝ) (fun y => g.scalarCurvature y / 2) x := by
    simpa only [div_eq_mul_inv, Pi.mul_def] using
      hSd.mul (mdifferentiableAt_const (c := (2⁻¹ : ℝ)))
  have hhalf : mvfderiv I (fun y => g.scalarCurvature y / 2) x =
      (2⁻¹ : ℝ) • mvfderiv I (fun y => g.scalarCurvature y) x := by
    simp only [div_eq_mul_inv]
    rw [mvfderiv_fun_mul hSd mdifferentiableAt_const, mvfderiv_const, smul_zero, zero_add]
  have hg := g.mdifferentiableAt_pairing hV hW
  have hRic := g.ricciBilinear.mdifferentiableAt_apply hV hW
  have hprod : MDifferentiableAt I 𝓘(ℝ) (fun y => g.scalarCurvature y / 2 *
      g.form y (extend E v y) (extend E w y)) x := hS2.mul hg
  have hfun : (fun y => g.einsteinBilinear y (extend E v y) (extend E w y)) =
      fun y => g.ricciBilinear y (extend E v y) (extend E w y) -
        g.scalarCurvature y / 2 * g.form y (extend E v y) (extend E w y) := by
    funext y
    exact g.einstein_apply y _ _
  simp only [Tensor.bilinearCovariantDerivative, TensorialAt.mkHom₂_apply_eq_extend,
    Tensor.bilinearDerivativeAux_apply]
  rw [hfun, mvfderiv_fun_sub hRic hprod, mvfderiv_fun_mul hS2 hg, hhalf]
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
  rw [g.leviCivita_metricCompatible u hV hW]
  simp only [einsteinBilinear_apply, ricciBilinear_apply, einstein_apply, extend_apply_self]
  ring

/-- **The Einstein tensor is divergence-free**: `∇^a G_{ab} = 0`. -/
theorem einstein_divergence_eq_zero (x : M) :
    g.bilinearDivergenceCovector g.einsteinBilinear x = 0 := by
  ext b
  have hflip : (Tensor.bilinearCovariantDerivative g.leviCivita g.einsteinBilinear x).flip b =
      (Tensor.bilinearCovariantDerivative g.leviCivita g.ricciBilinear x).flip b -
        (2⁻¹ : ℝ) • ((g.form x).flip b).smulRight
          (mvfderiv I (fun y => g.scalarCurvature y) x) := by
    ext a c
    simp only [flip_apply, sub_apply, smul_apply, smulRight_apply, smul_eq_mul,
      g.bilinearCovariantDerivative_einstein]
    ring
  rw [bilinearDivergenceCovector_apply, hflip, g.contract_sub, g.contract_smul,
    g.contract_smulRight, ← bilinearDivergenceCovector_apply, ricci_contracted_bianchi,
    flip_apply, g.form_sharp_left, zero_apply]
  ring

end ProjectAinos.SmoothGeometry.LorentzMetric
