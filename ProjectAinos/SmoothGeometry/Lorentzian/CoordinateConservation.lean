/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateEinsteinEquation
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateConnection

/-!
# The conservation of the stress of a scalar field

For a coordinate metric `g` on an open set `U` and a scalar field `φ` that is smooth on `U`, the
divergence of the Hilbert tensor `T_{ab} = ∂_aφ ∂_bφ − ½ g_{ab} (g^{cd} ∂_cφ ∂_dφ + m² φ²)` is
`∇^a T_{ab} = (□φ − m² φ) ∂_bφ` (`divergenceOf_scalarStress`), with the wave operator
`□φ = g^{ab} ∇_a ∇_b φ`. A field that satisfies the Klein–Gordon equation `□φ = m² φ` therefore
has a conserved stress on a fixed background, without the Einstein equations (Landau–Lifshitz,
§94).

* `fderiv_coefficient`: metric compatibility `∂_c g_{ab} = Γ^l_{ca} g_{lb} + Γ^l_{cb} g_{al}`.
* `hessianOf`, `boxOf`: the covariant Hessian `∇_a ∇_b φ = ∂_a ∂_b φ − Γ^c_{ab} ∂_cφ`, symmetric
  (`hessianOf_symm`), and its trace.
* `divergenceOf`: the divergence `∇^a T_{ab}` of a field of coefficients, which is the native
  divergence of `bilinearOf T` on the co-ordinate fields (`bilinearDivergence_bilinearOf`).
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

namespace CoordinateMetric

variable {U : Opens (MinkowskiModel d)} {g : CoordinateMetric σ d U}

/-- **Metric compatibility of the coefficients**:
`∂_c g_{ab} = Γ^l_{ca} g_{lb} + Γ^l_{cb} g_{al}`. -/
theorem fderiv_coefficient {x : MinkowskiModel d} (hx : x ∈ U) (a b c : Fin (d + 1)) :
    fderiv ℝ (fun z => g.coefficient z a b) x (Pi.single c 1) =
      ∑ l, (christoffelOf g.coefficient x l c a * g.coefficient x l b +
        christoffelOf g.coefficient x l c b * g.coefficient x a l) := by
  let y : U := ⟨x, hx⟩
  have he := physicalChart_mem y
  have hy : y ∈ (physicalChart y).source := by simp
  have hm := g.toLorentzMetric.leviCivita_metricCompatible
    (chartField (physicalChart y) (Pi.single c 1) y)
    (Y := chartField (physicalChart y) (Pi.single a 1))
    (Z := chartField (physicalChart y) (Pi.single b 1))
    (chartField_mdifferentiableAt he hy _) (chartField_mdifferentiableAt he hy _)
  rw [g.toLorentzMetric_pairing_derivative y y,
    g.toLorentzMetric.leviCivita_chartField_eq_sum he hy c a,
    g.toLorentzMetric.leviCivita_chartField_eq_sum he hy c b] at hm
  have hform (i k : Fin (d + 1)) : g.toLorentzMetric.form y
      (chartField (physicalChart y) (Pi.single i 1) y)
      (chartField (physicalChart y) (Pi.single k 1) y) = g.coefficient x i k :=
    g.toLorentzMetric_chartComponent y y i k
  change fderiv ℝ (fun q => g.form q (Pi.single a 1) (Pi.single b 1)) x (Pi.single c 1) = _
  rw [hm]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, hform,
    g.toLorentzMetric_chartChristoffel, ← Finset.sum_add_distrib]
  rfl

/-- Second partial derivatives of a field that is smooth on `U` commute. -/
theorem fderiv_fderiv_comm {φ : MinkowskiModel d → ℝ} (hφ : ContDiffOn ℝ ∞ φ U)
    {x : MinkowskiModel d} (hx : x ∈ U) (a b : Fin (d + 1)) :
    fderiv ℝ (fun z => fderiv ℝ φ z (Pi.single b 1)) x (Pi.single a 1) =
      fderiv ℝ (fun z => fderiv ℝ φ z (Pi.single a 1)) x (Pi.single b 1) := by
  have hc := hφ.contDiffAt (U.isOpen.mem_nhds hx)
  have hsymm := hc.isSymmSndFDerivAt (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    ((hφ.fderiv_of_isOpen U.isOpen (m := 1) (by simp)).contDiffAt
      (U.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have key (v w : MinkowskiModel d) :
      fderiv ℝ (fun z => fderiv ℝ φ z w) x v = fderiv ℝ (fderiv ℝ φ) x v w := by
    rw [fderiv_clm_apply hd (differentiableAt_const w)]
    simp
  rw [key, key]
  exact hsymm _ _

variable (g) in
/-- The covariant Hessian `∇_a ∇_b φ = ∂_a ∂_b φ − Γ^c_{ab} ∂_cφ`. -/
def hessianOf (φ : MinkowskiModel d → ℝ) (x : MinkowskiModel d) (a b : Fin (d + 1)) : ℝ :=
  fderiv ℝ (fun z => fderiv ℝ φ z (Pi.single b 1)) x (Pi.single a 1) -
    ∑ c, christoffelOf g.coefficient x c a b * fderiv ℝ φ x (Pi.single c 1)

variable (g) in
/-- The wave operator `□φ = g^{ab} ∇_a ∇_b φ`. -/
def boxOf (φ : MinkowskiModel d → ℝ) (x : MinkowskiModel d) : ℝ :=
  ∑ a, ∑ b, (g.coefficient x)⁻¹ a b * g.hessianOf φ x a b

variable (g) in
/-- The divergence `∇^a T_{ab} = g^{ac} (∂_c T_{ab} − Γ^l_{ca} T_{lb} − Γ^l_{cb} T_{al})`. -/
def divergenceOf (T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (b : Fin (d + 1)) : ℝ :=
  ∑ a, ∑ c, (g.coefficient x)⁻¹ a c * (fderiv ℝ (fun z => T z a b) x (Pi.single c 1) -
    ∑ l, christoffelOf g.coefficient x l c a * T x l b -
    ∑ l, christoffelOf g.coefficient x l c b * T x a l)

theorem hessianOf_symm {φ : MinkowskiModel d → ℝ} (hφ : ContDiffOn ℝ ∞ φ U)
    {x : MinkowskiModel d} (hx : x ∈ U) (a b : Fin (d + 1)) :
    g.hessianOf φ x a b = g.hessianOf φ x b a := by
  rw [hessianOf, hessianOf, fderiv_fderiv_comm hφ hx a b]
  congr 1
  exact Finset.sum_congr rfl fun c _ => by rw [christoffelOf_coefficient_symm hx c a b]

/-- The divergence of `bilinearOf T` on a co-ordinate field is `divergenceOf T`. -/
theorem bilinearDivergence_bilinearOf
    {T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hT : ∀ i k, ContDiffOn ℝ ∞ (fun x => T x i k) U) (x : U) (b : Fin (d + 1)) :
    g.toLorentzMetric.bilinearDivergenceCovector (bilinearOf T hT) x
        (chartField (physicalChart x) (Pi.single b 1) x) = g.divergenceOf T x b := by
  have he := physicalChart_mem x
  have hx : x ∈ (physicalChart x).source := by simp
  rw [bilinearDivergenceCovector_apply, g.toLorentzMetric.contract_chart he hx, divergenceOf]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [ContinuousLinearMap.flip_apply, g.toLorentzMetric.bilinearCovariantDerivative_chart
    (bilinearOf T hT) he hx a b c, chartInverse_physicalChart]
  have hfun : (fun y : U => bilinearOf T hT y (chartField (physicalChart x) (Pi.single a 1) y)
      (chartField (physicalChart x) (Pi.single b 1) y)) = fun y : U => T y a b :=
    funext fun y => bilinearOf_chartField T hT x y a b
  rw [hfun, mvfderiv_val x x (((hT a b).contDiffAt (U.isOpen.mem_nhds x.property)).differentiableAt
    (by simp))]
  simp only [bilinearOf_chartField, g.toLorentzMetric_chartChristoffel]
  ring

/-- Reversing the order of three finite sums. -/
theorem sum_sum_sum_rotate {n : ℕ} (f : Fin n → Fin n → Fin n → ℝ) :
    ∑ x, ∑ y, ∑ z, f z y x = ∑ x, ∑ y, ∑ z, f x y z := by
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun y _ => Finset.sum_comm).trans ?_
  exact Finset.sum_comm

/-! ### The divergence of the stress of a scalar field -/

section Scalar

variable {φ : MinkowskiModel d → ℝ}

variable (g) in
/-- The invariant `g^{de} ∂_dφ ∂_eφ + m² φ²` of a scalar field. -/
def scalarInvariant (m : ℝ) (φ : MinkowskiModel d → ℝ) (z : MinkowskiModel d) : ℝ :=
  ∑ e₁, ∑ e₂, (g.coefficient z)⁻¹ e₁ e₂ * (fderiv ℝ φ z (Pi.single e₁ 1) *
    fderiv ℝ φ z (Pi.single e₂ 1)) + m ^ 2 * φ z ^ 2

theorem scalarStress_eq (m : ℝ) (φ : MinkowskiModel d → ℝ) (z : MinkowskiModel d)
    (a b : Fin (d + 1)) :
    g.scalarStress m φ z a b = fderiv ℝ φ z (Pi.single a 1) * fderiv ℝ φ z (Pi.single b 1) -
      1 / 2 * (g.coefficient z a b * g.scalarInvariant m φ z) := by
  rw [scalarStress, scalarInvariant]
  ring

theorem differentiableAt_fderiv_apply (hφ : ContDiffOn ℝ ∞ φ U) {x : MinkowskiModel d}
    (hx : x ∈ U) (v : MinkowskiModel d) :
    DifferentiableAt ℝ (fun z => fderiv ℝ φ z v) x :=
  (((hφ.fderiv_of_isOpen U.isOpen (m := ∞) (by simp)).clm_apply contDiffOn_const).contDiffAt
    (U.isOpen.mem_nhds hx)).differentiableAt (by simp)

/-- `∂_c (g^{de} ∂_dφ ∂_eφ + m² φ²) = 2 g^{de} ∇_c ∇_d φ ∂_eφ + 2 m² φ ∂_cφ`. -/
theorem fderiv_scalarInvariant (hφ : ContDiffOn ℝ ∞ φ U) (m : ℝ) {x : MinkowskiModel d}
    (hx : x ∈ U) (c : Fin (d + 1)) :
    fderiv ℝ (g.scalarInvariant m φ) x (Pi.single c 1) =
      2 * ∑ e₁, ∑ e₂, (g.coefficient x)⁻¹ e₁ e₂ * g.hessianOf φ x c e₁ *
        fderiv ℝ φ x (Pi.single e₂ 1) + 2 * m ^ 2 * φ x * fderiv ℝ φ x (Pi.single c 1) := by
  have hAd (e₁ e₂ : Fin (d + 1)) : HasFDerivAt (fun z => (g.coefficient z)⁻¹ e₁ e₂)
      (fderiv ℝ (fun z => (g.coefficient z)⁻¹ e₁ e₂) x) x :=
    (((g.contDiffOn_coefficient_inv e₁ e₂).contDiffAt (U.isOpen.mem_nhds hx)).differentiableAt
      (by simp)).hasFDerivAt
  have hpd (e : Fin (d + 1)) := (differentiableAt_fderiv_apply hφ hx (Pi.single e 1)).hasFDerivAt
  have hφd : HasFDerivAt φ (fderiv ℝ φ x) x :=
    ((hφ.contDiffAt (U.isOpen.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have htot := (HasFDerivAt.fun_sum (u := Finset.univ) fun e₁ _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) fun e₂ _ =>
      (hAd e₁ e₂).mul ((hpd e₁).mul (hpd e₂))).add ((hφd.pow 2).const_mul (m ^ 2))
  have hfd : fderiv ℝ (g.scalarInvariant m φ) x = _ := htot.fderiv
  rw [hfd]
  simp only [add_apply, FunLike.coe_sum, Finset.sum_apply,
    smul_apply, smul_eq_mul, fderiv_coefficient_inv hx]
  -- name the pieces
  obtain ⟨P, hP⟩ : ∃ P : Fin (d + 1) → ℝ, ∀ a, P a = fderiv ℝ φ x (Pi.single a 1) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Fin (d + 1) → ℝ, ∀ a,
      Q a = fderiv ℝ (fun z => fderiv ℝ φ z (Pi.single a 1)) x (Pi.single c 1) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : Fin (d + 1) → ℝ, ∀ l,
      r l = ∑ e, christoffelOf g.coefficient x e c l * P e := ⟨_, fun _ => rfl⟩
  have hH (e₁ : Fin (d + 1)) : g.hessianOf φ x c e₁ = Q e₁ - r e₁ := by
    rw [hessianOf, hQ, hr]
    simp only [hP]
  simp only [hH, ← hP, ← hQ, Pi.mul_apply, nsmul_eq_mul, Nat.cast_ofNat]
  have hAs (e₁ e₂ : Fin (d + 1)) : (g.coefficient x)⁻¹ e₁ e₂ = (g.coefficient x)⁻¹ e₂ e₁ :=
    g.coefficient_inv_symmetric hx e₁ e₂
  have hsplit : ∑ e₁, ∑ e₂, ((g.coefficient x)⁻¹ e₁ e₂ * (P e₁ * Q e₂ + P e₂ * Q e₁) +
      P e₁ * P e₂ * -∑ e, (christoffelOf g.coefficient x e₁ c e * (g.coefficient x)⁻¹ e e₂ +
        christoffelOf g.coefficient x e₂ c e * (g.coefficient x)⁻¹ e₁ e)) =
      ∑ e₁, ∑ e₂, (g.coefficient x)⁻¹ e₁ e₂ * (P e₁ * Q e₂ + P e₂ * Q e₁) -
        ∑ e₁, ∑ e₂, P e₁ * P e₂ * ∑ e, christoffelOf g.coefficient x e₁ c e *
          (g.coefficient x)⁻¹ e e₂ -
        ∑ e₁, ∑ e₂, P e₁ * P e₂ * ∑ e, christoffelOf g.coefficient x e₂ c e *
          (g.coefficient x)⁻¹ e₁ e := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e₁ _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e₂ _ => ?_
    rw [Finset.sum_add_distrib]
    ring
  have hα : ∑ e₁, ∑ e₂, (g.coefficient x)⁻¹ e₁ e₂ * (P e₁ * Q e₂ + P e₂ * Q e₁) =
      2 * ∑ e₁, ∑ e₂, (g.coefficient x)⁻¹ e₁ e₂ * Q e₁ * P e₂ := by
    have hsw : ∑ e₁, ∑ e₂, (g.coefficient x)⁻¹ e₁ e₂ * (P e₁ * Q e₂) =
        ∑ e₁, ∑ e₂, (g.coefficient x)⁻¹ e₁ e₂ * Q e₁ * P e₂ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun e₁ _ => Finset.sum_congr rfl fun e₂ _ => by
        rw [hAs e₂ e₁]
        ring
    simp only [mul_add, Finset.sum_add_distrib, hsw]
    rw [two_mul]
    congr 1
    exact Finset.sum_congr rfl fun e₁ _ => Finset.sum_congr rfl fun e₂ _ => by ring
  have hβ₁ : ∑ e₁, ∑ e₂, P e₁ * P e₂ * ∑ e, christoffelOf g.coefficient x e₁ c e *
      (g.coefficient x)⁻¹ e e₂ = ∑ e₁, ∑ e₂, (g.coefficient x)⁻¹ e₁ e₂ * r e₁ * P e₂ := by
    have h1 : ∑ e₁, ∑ e₂, P e₁ * P e₂ * ∑ e, christoffelOf g.coefficient x e₁ c e *
        (g.coefficient x)⁻¹ e e₂ = ∑ e₁, ∑ e₂, ∑ e,
          (fun a b i => (g.coefficient x)⁻¹ a b * (christoffelOf g.coefficient x i c a * P i) *
            P b) e e₂ e₁ := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ring
    have h2 : ∑ e₁, ∑ e₂, (g.coefficient x)⁻¹ e₁ e₂ * r e₁ * P e₂ = ∑ e₁, ∑ e₂, ∑ e,
        (fun a b i => (g.coefficient x)⁻¹ a b * (christoffelOf g.coefficient x i c a * P i) *
          P b) e₁ e₂ e := by
      simp only [hr, Finset.mul_sum, Finset.sum_mul]
    rw [h1, h2, sum_sum_sum_rotate]
  have hβ₂ : ∑ e₁, ∑ e₂, P e₁ * P e₂ * ∑ e, christoffelOf g.coefficient x e₂ c e *
      (g.coefficient x)⁻¹ e₁ e = ∑ e₁, ∑ e₂, (g.coefficient x)⁻¹ e₁ e₂ * r e₁ * P e₂ := by
    rw [← hβ₁, Finset.sum_comm]
    exact Finset.sum_congr rfl fun e₂ _ => Finset.sum_congr rfl fun e₁ _ => by
      rw [mul_comm (P e₂) (P e₁)]
      exact congrArg _ (Finset.sum_congr rfl fun e _ => by rw [hAs e₁ e])
  have hrhs : ∑ e₁, ∑ e₂, (g.coefficient x)⁻¹ e₁ e₂ * (Q e₁ - r e₁) * P e₂ =
      ∑ e₁, ∑ e₂, (g.coefficient x)⁻¹ e₁ e₂ * Q e₁ * P e₂ -
        ∑ e₁, ∑ e₂, (g.coefficient x)⁻¹ e₁ e₂ * r e₁ * P e₂ := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e₁ _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun e₂ _ => by ring
  rw [hsplit, hα, hβ₁, hβ₂, hrhs]
  norm_num
  ring

theorem differentiableAt_scalarInvariant (hφ : ContDiffOn ℝ ∞ φ U) (m : ℝ)
    {x : MinkowskiModel d} (hx : x ∈ U) : DifferentiableAt ℝ (g.scalarInvariant m φ) x := by
  have hAd (e₁ e₂ : Fin (d + 1)) : DifferentiableAt ℝ (fun z => (g.coefficient z)⁻¹ e₁ e₂) x :=
    ((g.contDiffOn_coefficient_inv e₁ e₂).contDiffAt (U.isOpen.mem_nhds hx)).differentiableAt
      (by simp)
  have hpd (e : Fin (d + 1)) := (differentiableAt_fderiv_apply hφ hx (Pi.single e 1)).hasFDerivAt
  have hφd : HasFDerivAt φ (fderiv ℝ φ x) x :=
    ((hφ.contDiffAt (U.isOpen.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  exact ((HasFDerivAt.fun_sum (u := Finset.univ) fun e₁ _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) fun e₂ _ =>
      (hAd e₁ e₂).hasFDerivAt.mul ((hpd e₁).mul (hpd e₂))).add
        ((hφd.pow 2).const_mul (m ^ 2))).differentiableAt

/-- The covariant derivative of the stress:
`∇_c T_{ab} = ∇_c∇_aφ ∂_bφ + ∂_aφ ∇_c∇_bφ − ½ g_{ab} ∂_c(g^{de} ∂_dφ ∂_eφ + m² φ²)`. -/
theorem covariantDerivative_scalarStress (hφ : ContDiffOn ℝ ∞ φ U) (m : ℝ)
    {x : MinkowskiModel d} (hx : x ∈ U) (a b c : Fin (d + 1)) :
    fderiv ℝ (fun z => g.scalarStress m φ z a b) x (Pi.single c 1) -
        ∑ l, christoffelOf g.coefficient x l c a * g.scalarStress m φ x l b -
        ∑ l, christoffelOf g.coefficient x l c b * g.scalarStress m φ x a l =
      g.hessianOf φ x c a * fderiv ℝ φ x (Pi.single b 1) +
        fderiv ℝ φ x (Pi.single a 1) * g.hessianOf φ x c b -
        1 / 2 * (g.coefficient x a b * fderiv ℝ (g.scalarInvariant m φ) x (Pi.single c 1)) := by
  have hpa := differentiableAt_fderiv_apply hφ hx (Pi.single a 1)
  have hpb := differentiableAt_fderiv_apply hφ hx (Pi.single b 1)
  have hG : DifferentiableAt ℝ (fun z => g.coefficient z a b) x :=
    ((g.coefficient_contDiffOn a b).contDiffAt (U.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hI := differentiableAt_scalarInvariant (g := g) hφ m hx
  have hfun : (fun z => g.scalarStress m φ z a b) = fun z =>
      fderiv ℝ φ z (Pi.single a 1) * fderiv ℝ φ z (Pi.single b 1) -
        1 / 2 * (g.coefficient z a b * g.scalarInvariant m φ z) :=
    funext fun z => scalarStress_eq m φ z a b
  have hd := (hpa.hasFDerivAt.mul hpb.hasFDerivAt).sub
    ((hG.hasFDerivAt.mul hI.hasFDerivAt).const_mul (1 / 2 : ℝ))
  have hfd : fderiv ℝ (fun z => fderiv ℝ φ z (Pi.single a 1) * fderiv ℝ φ z (Pi.single b 1) -
      1 / 2 * (g.coefficient z a b * g.scalarInvariant m φ z)) x = _ := hd.fderiv
  rw [hfun, hfd]
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_coefficient hx a b c]
  simp only [scalarStress_eq, hessianOf]
  have h1 : ∑ l, christoffelOf g.coefficient x l c a *
      (fderiv ℝ φ x (Pi.single l 1) * fderiv ℝ φ x (Pi.single b 1) -
        1 / 2 * (g.coefficient x l b * g.scalarInvariant m φ x)) =
      (∑ l, christoffelOf g.coefficient x l c a * fderiv ℝ φ x (Pi.single l 1)) *
          fderiv ℝ φ x (Pi.single b 1) -
        1 / 2 * g.scalarInvariant m φ x *
          ∑ l, christoffelOf g.coefficient x l c a * g.coefficient x l b := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  have h2 : ∑ l, christoffelOf g.coefficient x l c b *
      (fderiv ℝ φ x (Pi.single a 1) * fderiv ℝ φ x (Pi.single l 1) -
        1 / 2 * (g.coefficient x a l * g.scalarInvariant m φ x)) =
      fderiv ℝ φ x (Pi.single a 1) *
          (∑ l, christoffelOf g.coefficient x l c b * fderiv ℝ φ x (Pi.single l 1)) -
        1 / 2 * g.scalarInvariant m φ x *
          ∑ l, christoffelOf g.coefficient x l c b * g.coefficient x a l := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [h1, h2, Finset.sum_add_distrib]
  ring

/-- **The divergence of the stress of a scalar field**: `∇^a T_{ab} = (□φ − m² φ) ∂_bφ`. -/
theorem divergenceOf_scalarStress (hφ : ContDiffOn ℝ ∞ φ U) (m : ℝ) {x : MinkowskiModel d}
    (hx : x ∈ U) (b : Fin (d + 1)) :
    g.divergenceOf (g.scalarStress m φ) x b =
      (g.boxOf φ x - m ^ 2 * φ x) * fderiv ℝ φ x (Pi.single b 1) := by
  have hdet := isUnit_iff_ne_zero.mpr (g.coefficient_det_ne_zero ⟨x, hx⟩)
  have hAs (e₁ e₂ : Fin (d + 1)) : (g.coefficient x)⁻¹ e₁ e₂ = (g.coefficient x)⁻¹ e₂ e₁ :=
    g.coefficient_inv_symmetric hx e₁ e₂
  have hδ (c : Fin (d + 1)) : ∑ a, (g.coefficient x)⁻¹ a c * g.coefficient x a b =
      if c = b then 1 else 0 := by
    have h1 := congrFun (congrFun (Matrix.nonsing_inv_mul _ hdet) c) b
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    rw [← h1]
    exact Finset.sum_congr rfl fun a _ => by rw [hAs a c]
  unfold divergenceOf
  simp only [covariantDerivative_scalarStress hφ m hx]
  -- split the three terms
  have hsplit : ∑ a, ∑ c, (g.coefficient x)⁻¹ a c *
      (g.hessianOf φ x c a * fderiv ℝ φ x (Pi.single b 1) +
        fderiv ℝ φ x (Pi.single a 1) * g.hessianOf φ x c b -
        1 / 2 * (g.coefficient x a b * fderiv ℝ (g.scalarInvariant m φ) x (Pi.single c 1))) =
      g.boxOf φ x * fderiv ℝ φ x (Pi.single b 1) +
        ∑ a, ∑ c, (g.coefficient x)⁻¹ a c * g.hessianOf φ x b c * fderiv ℝ φ x (Pi.single a 1) -
        1 / 2 * fderiv ℝ (g.scalarInvariant m φ) x (Pi.single b 1) := by
    have hbox : g.boxOf φ x * fderiv ℝ φ x (Pi.single b 1) = ∑ a, ∑ c,
        (g.coefficient x)⁻¹ a c * g.hessianOf φ x c a * fderiv ℝ φ x (Pi.single b 1) := by
      rw [boxOf, Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ => by rw [hessianOf_symm hφ hx c a]
    have hthird : 1 / 2 * fderiv ℝ (g.scalarInvariant m φ) x (Pi.single b 1) = ∑ a, ∑ c,
        (g.coefficient x)⁻¹ a c * (1 / 2 * (g.coefficient x a b *
          fderiv ℝ (g.scalarInvariant m φ) x (Pi.single c 1))) := by
      rw [Finset.sum_comm]
      have : ∀ c, ∑ a, (g.coefficient x)⁻¹ a c * (1 / 2 * (g.coefficient x a b *
          fderiv ℝ (g.scalarInvariant m φ) x (Pi.single c 1))) =
          (∑ a, (g.coefficient x)⁻¹ a c * g.coefficient x a b) *
            (1 / 2 * fderiv ℝ (g.scalarInvariant m φ) x (Pi.single c 1)) := fun c => by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by ring
      simp only [this, hδ, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
    rw [hbox, hthird, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hessianOf_symm hφ hx c b]
    ring
  rw [hsplit, fderiv_scalarInvariant hφ m hx b]
  have hswap : ∑ a, ∑ c, (g.coefficient x)⁻¹ a c * g.hessianOf φ x b c *
      fderiv ℝ φ x (Pi.single a 1) = ∑ e₁, ∑ e₂, (g.coefficient x)⁻¹ e₁ e₂ *
        g.hessianOf φ x b e₁ * fderiv ℝ φ x (Pi.single e₂ 1) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by rw [hAs a c]
  rw [hswap]
  ring

end Scalar

end CoordinateMetric

end ProjectAinos.SmoothGeometry
