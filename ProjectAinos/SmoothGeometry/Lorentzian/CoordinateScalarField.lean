/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateConservation

/-!
# The field equation of a scalar field on a fixed background

For a coordinate metric `g` on an open set `U` and a scalar field `φ` smooth on `U`, the relative
action `ψ, ε ↦ ∫ (ℒ(φ + εψ) − ℒ(φ)) dx` of the density
`ℒ(φ) = −½ (g^{ab} ∂_aφ ∂_bφ + m² φ²) √|g|` has, for a smooth `ψ` with compact support in `U`,
the derivative `∫ ψ (□φ − m² φ) √|g| dx` at `ε = 0` (`hasDerivAt_fieldAction`). It is
stationary under every such `ψ` if and only if `φ` satisfies the Klein–Gordon equation
`□φ = m² φ` on `U` (`isFieldStationary_iff`). With `divergenceOf_scalarStress`, a solution has a
conserved stress (`bilinearDivergence_scalarStress_eq_zero`).

* `sum_fderiv_density_inv_mul`: `∂_b(√|g| g^{ab} ∂_aφ) = √|g| □φ`.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

namespace CoordinateMetric

variable {U : Opens (MinkowskiModel d)} {g : CoordinateMetric σ d U}
  {φ ψ : MinkowskiModel d → ℝ}

variable (g) in
/-- The density `−½ (g^{ab} ∂_aφ ∂_bφ + m² φ²) √|g|` of a scalar field on the fixed metric. -/
def fieldDensity (m : ℝ) (φ : MinkowskiModel d → ℝ) (x : MinkowskiModel d) : ℝ :=
  -(g.scalarInvariant m φ x / 2) * densityOf g.coefficient x

variable (g) in
/-- The relative action `S[φ + εψ] − S[φ]` of the scalar field. -/
def fieldAction (m : ℝ) (φ ψ : MinkowskiModel d → ℝ) (ε : ℝ) : ℝ :=
  ∫ x, (g.fieldDensity m (fun z => φ z + ε * ψ z) x - g.fieldDensity m φ x)

variable (g) in
/-- The density of `φ + εψ`, with the derivatives of `φ` and `ψ` written apart. -/
def fieldVariationDensity (m : ℝ) (φ ψ : MinkowskiModel d → ℝ) (p : ℝ × MinkowskiModel d) :
    ℝ :=
  -((∑ a, ∑ b, (g.coefficient p.2)⁻¹ a b *
      ((fderiv ℝ φ p.2 (Pi.single a 1) + p.1 * fderiv ℝ ψ p.2 (Pi.single a 1)) *
        (fderiv ℝ φ p.2 (Pi.single b 1) + p.1 * fderiv ℝ ψ p.2 (Pi.single b 1))) +
      m ^ 2 * (φ p.2 + p.1 * ψ p.2) ^ 2) / 2) * densityOf g.coefficient p.2

theorem fderiv_eq_zero_of_notMem {x : MinkowskiModel d} (hx : x ∉ tsupport ψ) :
    fderiv ℝ ψ x = 0 := by
  have h : ψ =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hx] with z hz
    exact image_eq_zero_of_notMem_tsupport hz
  rw [h.fderiv_eq]
  exact fderiv_const_apply 0

/-- The integrand of the relative action is that of the density of `φ + εψ`. -/
theorem fieldDensity_sub_eq (hφ : ContDiffOn ℝ ∞ φ U) (hψ : ContDiff ℝ ∞ ψ)
    (hKU : tsupport ψ ⊆ U) (m ε : ℝ) (x : MinkowskiModel d) :
    g.fieldDensity m (fun z => φ z + ε * ψ z) x - g.fieldDensity m φ x =
      g.fieldVariationDensity m φ ψ (ε, x) - g.fieldVariationDensity m φ ψ (0, x) := by
  by_cases hx : x ∈ U
  · have hφd : DifferentiableAt ℝ φ x :=
      (hφ.contDiffAt (U.isOpen.mem_nhds hx)).differentiableAt (by simp)
    have hψd : DifferentiableAt ℝ ψ x := (hψ.differentiable (by simp)) x
    have hfd : fderiv ℝ (fun z => φ z + ε * ψ z) x = fderiv ℝ φ x + ε • fderiv ℝ ψ x := by
      rw [fderiv_fun_add hφd (hψd.const_mul ε), fderiv_const_mul hψd]
    simp only [fieldDensity, fieldVariationDensity, scalarInvariant, hfd, add_apply, smul_apply,
      smul_eq_mul, zero_mul, add_zero]
  · have hxK : x ∉ tsupport ψ := fun h' => hx (hKU h')
    have hψx : ψ x = 0 := image_eq_zero_of_notMem_tsupport hxK
    have hfd : fderiv ℝ (fun z => φ z + ε * ψ z) x = fderiv ℝ φ x := by
      have h : (fun z => φ z + ε * ψ z) =ᶠ[𝓝 x] φ := by
        filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hxK] with z hz
        rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, add_zero]
      exact h.fderiv_eq
    simp only [fieldDensity, fieldVariationDensity, scalarInvariant, hfd, hψx,
      fderiv_eq_zero_of_notMem hxK, zero_apply, mul_zero, add_zero, sub_self]

theorem fieldVariationDensity_of_notMem (m : ℝ) {x : MinkowskiModel d} (hx : x ∉ tsupport ψ)
    (t : ℝ) : g.fieldVariationDensity m φ ψ (t, x) = g.fieldVariationDensity m φ ψ (0, x) := by
  simp only [fieldVariationDensity, image_eq_zero_of_notMem_tsupport hx,
    fderiv_eq_zero_of_notMem hx, zero_apply, mul_zero]

theorem contDiffAt_fieldVariationDensity (hφ : ContDiffOn ℝ ∞ φ U) (hψ : ContDiff ℝ ∞ ψ) (m : ℝ)
    {p : ℝ × MinkowskiModel d} (hp : p.2 ∈ U) :
    ContDiffAt ℝ ∞ (g.fieldVariationDensity m φ ψ) p := by
  have hn := U.isOpen.mem_nhds hp
  have hφp : ContDiffAt ℝ ∞ (fun q : ℝ × MinkowskiModel d => φ q.2) p :=
    (hφ.contDiffAt hn).comp p contDiffAt_snd
  have hψp : ContDiffAt ℝ ∞ (fun q : ℝ × MinkowskiModel d => ψ q.2) p :=
    hψ.contDiffAt.comp p contDiffAt_snd
  have hdφ (a : Fin (d + 1)) : ContDiffAt ℝ ∞
      (fun q : ℝ × MinkowskiModel d => fderiv ℝ φ q.2 (Pi.single a 1)) p :=
    contDiffAt_fderiv_snd hφp (Pi.single a 1)
  have hdψ (a : Fin (d + 1)) : ContDiffAt ℝ ∞
      (fun q : ℝ × MinkowskiModel d => fderiv ℝ ψ q.2 (Pi.single a 1)) p :=
    contDiffAt_fderiv_snd hψp (Pi.single a 1)
  have hA (a b : Fin (d + 1)) : ContDiffAt ℝ ∞
      (fun q : ℝ × MinkowskiModel d => (g.coefficient q.2)⁻¹ a b) p :=
    ((g.contDiffOn_coefficient_inv a b).contDiffAt hn).comp p contDiffAt_snd
  have hD : ContDiffAt ℝ ∞ (fun q : ℝ × MinkowskiModel d => densityOf g.coefficient q.2) p :=
    (contDiffAt_densityOf hp).comp p contDiffAt_snd
  have hsum : ContDiffAt ℝ ∞ (fun q : ℝ × MinkowskiModel d => ∑ a, ∑ b,
      (g.coefficient q.2)⁻¹ a b *
        ((fderiv ℝ φ q.2 (Pi.single a 1) + q.1 * fderiv ℝ ψ q.2 (Pi.single a 1)) *
          (fderiv ℝ φ q.2 (Pi.single b 1) + q.1 * fderiv ℝ ψ q.2 (Pi.single b 1)))) p :=
    ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ => (hA a b).mul
      (((hdφ a).add (contDiffAt_fst.mul (hdψ a))).mul ((hdφ b).add (contDiffAt_fst.mul (hdψ b))))
  exact (((hsum.add (contDiffAt_const.mul ((hφp.add (contDiffAt_fst.mul hψp)).pow 2))).div_const
    2).neg).mul hD

variable (g) in
/-- The first variation `−(½ g^{ab} (∂_aψ ∂_bφ + ∂_aφ ∂_bψ) + m² φ ψ) √|g|` of the density. -/
def fieldVariationDeriv (m : ℝ) (φ ψ : MinkowskiModel d → ℝ) (x : MinkowskiModel d) : ℝ :=
  -((∑ a, ∑ b, (g.coefficient x)⁻¹ a b *
      (fderiv ℝ ψ x (Pi.single a 1) * fderiv ℝ φ x (Pi.single b 1) +
        fderiv ℝ φ x (Pi.single a 1) * fderiv ℝ ψ x (Pi.single b 1))) / 2 +
      m ^ 2 * φ x * ψ x) * densityOf g.coefficient x

theorem hasDerivAt_fieldVariationDensity (m : ℝ) (φ ψ : MinkowskiModel d → ℝ)
    (x : MinkowskiModel d) :
    HasDerivAt (fun t => g.fieldVariationDensity m φ ψ (t, x)) (g.fieldVariationDeriv m φ ψ x)
      0 := by
  have hl (a : Fin (d + 1)) : HasDerivAt (fun t : ℝ => fderiv ℝ φ x (Pi.single a 1) +
      t * fderiv ℝ ψ x (Pi.single a 1)) (fderiv ℝ ψ x (Pi.single a 1)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (fderiv ℝ ψ x (Pi.single a 1))).const_add
      (fderiv ℝ φ x (Pi.single a 1))
  have hv : HasDerivAt (fun t : ℝ => φ x + t * ψ x) (ψ x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (ψ x)).const_add (φ x)
  have hsum := (HasDerivAt.fun_sum (u := Finset.univ) fun a _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun b _ =>
      ((hl a).mul (hl b)).const_mul ((g.coefficient x)⁻¹ a b)).add
        ((hv.pow 2).const_mul (m ^ 2))
  have h := ((hsum.div_const 2).neg).mul_const (densityOf g.coefficient x)
  convert h using 1
  · funext t
    rfl
  · simp only [fieldVariationDeriv, zero_mul, add_zero, Nat.cast_ofNat]
    norm_num
    ring

theorem split_aux {n : ℕ} (D : ℝ) (X Y : Fin n → Fin n → ℝ) (P W Z A : Fin n → ℝ) :
    D * ∑ a, ((-∑ e, (X a e + Y a e)) * P a + W a) + (∑ a, A a * P a) * (D * ∑ c, Z c) =
      D * (∑ a, W a - ∑ a, ∑ e, X a e * P a - ∑ a, ∑ e, Y a e * P a +
        ∑ c, ∑ a, Z c * A a * P a) := by
  have h1 : ∑ a, ((-∑ e, (X a e + Y a e)) * P a + W a) =
      ∑ a, W a - ∑ a, ∑ e, X a e * P a - ∑ a, ∑ e, Y a e * P a := by
    have hx (a : Fin n) : (-∑ e, (X a e + Y a e)) * P a =
        -(∑ e, X a e * P a + ∑ e, Y a e * P a) := by
      rw [neg_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact congrArg _ (Finset.sum_congr rfl fun e _ => by ring)
    rw [Finset.sum_add_distrib, Finset.sum_congr rfl fun a _ => hx a, Finset.sum_neg_distrib,
      Finset.sum_add_distrib]
    ring
  have h2 : (∑ a, A a * P a) * (D * ∑ c, Z c) = D * ∑ c, ∑ a, Z c * A a * P a := by
    have h3 : ∑ c, ∑ a, Z c * A a * P a = (∑ c, Z c) * ∑ a, A a * P a := by
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [h3]
    ring
  rw [h1, h2]
  ring

/-- **The wave operator in divergence form**: `∂_b(√|g| g^{ab} ∂_aφ) = √|g| □φ`. -/
theorem sum_fderiv_density_inv_mul (hφ : ContDiffOn ℝ ∞ φ U) {x : MinkowskiModel d}
    (hx : x ∈ U) :
    ∑ b, fderiv ℝ (fun z => densityOf g.coefficient z *
      ∑ a, (g.coefficient z)⁻¹ a b * fderiv ℝ φ z (Pi.single a 1)) x (Pi.single b 1) =
      densityOf g.coefficient x * g.boxOf φ x := by
  have hn := U.isOpen.mem_nhds hx
  have hD : HasFDerivAt (fun z => densityOf g.coefficient z)
      (fderiv ℝ (fun z => densityOf g.coefficient z) x) x :=
    ((contDiffAt_densityOf hx).differentiableAt (by simp)).hasFDerivAt
  have hA (a b : Fin (d + 1)) : HasFDerivAt (fun z => (g.coefficient z)⁻¹ a b)
      (fderiv ℝ (fun z => (g.coefficient z)⁻¹ a b) x) x :=
    (((g.contDiffOn_coefficient_inv a b).contDiffAt hn).differentiableAt (by simp)).hasFDerivAt
  have hp (a : Fin (d + 1)) := (differentiableAt_fderiv_apply hφ hx (Pi.single a 1)).hasFDerivAt
  have hterm (b : Fin (d + 1)) : fderiv ℝ (fun z => densityOf g.coefficient z *
      ∑ a, (g.coefficient z)⁻¹ a b * fderiv ℝ φ z (Pi.single a 1)) x (Pi.single b 1) =
      densityOf g.coefficient x * ∑ a,
        (fderiv ℝ (fun z => (g.coefficient z)⁻¹ a b) x (Pi.single b 1) *
            fderiv ℝ φ x (Pi.single a 1) + (g.coefficient x)⁻¹ a b *
          fderiv ℝ (fun z => fderiv ℝ φ z (Pi.single a 1)) x (Pi.single b 1)) +
      (∑ a, (g.coefficient x)⁻¹ a b * fderiv ℝ φ x (Pi.single a 1)) *
        fderiv ℝ (fun z => densityOf g.coefficient z) x (Pi.single b 1) := by
    have h := hD.mul (HasFDerivAt.fun_sum (u := Finset.univ) fun a _ => (hA a b).mul (hp a))
    have hfd : fderiv ℝ (fun z => densityOf g.coefficient z *
        ∑ a, (g.coefficient z)⁻¹ a b * fderiv ℝ φ z (Pi.single a 1)) x = _ := h.fderiv
    rw [hfd]
    simp only [add_apply, smul_apply, smul_eq_mul, FunLike.coe_sum, Finset.sum_apply]
    congr 1
    congr 1
    exact Finset.sum_congr rfl fun a _ => by ring
  simp only [hterm, fderiv_densityOf hx, fderiv_coefficient_inv hx]
  -- name the pieces
  obtain ⟨P, hP⟩ : ∃ P : Fin (d + 1) → ℝ, ∀ a, P a = fderiv ℝ φ x (Pi.single a 1) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Fin (d + 1) → Fin (d + 1) → ℝ, ∀ a b,
      Q a b = fderiv ℝ (fun z => fderiv ℝ φ z (Pi.single b 1)) x (Pi.single a 1) :=
    ⟨_, fun _ _ => rfl⟩
  have hbox : g.boxOf φ x = ∑ a, ∑ b, (g.coefficient x)⁻¹ a b * Q a b -
      ∑ a, ∑ b, (g.coefficient x)⁻¹ a b * ∑ c, christoffelOf g.coefficient x c a b * P c := by
    rw [boxOf, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hessianOf, hQ]
    simp only [hP]
    ring
  rw [hbox]
  simp only [← hP, ← hQ]
  have hAs (e₁ e₂ : Fin (d + 1)) : (g.coefficient x)⁻¹ e₁ e₂ = (g.coefficient x)⁻¹ e₂ e₁ :=
    g.coefficient_inv_symmetric hx e₁ e₂
  have hΓ (c a b : Fin (d + 1)) : christoffelOf g.coefficient x c a b =
      christoffelOf g.coefficient x c b a := christoffelOf_coefficient_symm hx c a b
  -- split the sum over `b` into its four parts
  have hsplit : ∑ b, (densityOf g.coefficient x * ∑ a,
      ((-∑ e, (christoffelOf g.coefficient x a b e * (g.coefficient x)⁻¹ e b +
          christoffelOf g.coefficient x b b e * (g.coefficient x)⁻¹ a e)) * P a +
        (g.coefficient x)⁻¹ a b * Q b a) +
      (∑ a, (g.coefficient x)⁻¹ a b * P a) *
        (densityOf g.coefficient x * ∑ c, christoffelOf g.coefficient x c c b)) =
      densityOf g.coefficient x * (∑ b, ∑ a, (g.coefficient x)⁻¹ a b * Q b a -
        ∑ b, ∑ a, ∑ e, christoffelOf g.coefficient x a b e * (g.coefficient x)⁻¹ e b * P a -
        ∑ b, ∑ a, ∑ e, christoffelOf g.coefficient x b b e * (g.coefficient x)⁻¹ a e * P a +
        ∑ b, ∑ c, ∑ a, christoffelOf g.coefficient x c c b * (g.coefficient x)⁻¹ a b * P a) := by
    have hb : ∀ b, densityOf g.coefficient x * ∑ a,
        ((-∑ e, (christoffelOf g.coefficient x a b e * (g.coefficient x)⁻¹ e b +
            christoffelOf g.coefficient x b b e * (g.coefficient x)⁻¹ a e)) * P a +
          (g.coefficient x)⁻¹ a b * Q b a) +
        (∑ a, (g.coefficient x)⁻¹ a b * P a) *
          (densityOf g.coefficient x * ∑ c, christoffelOf g.coefficient x c c b) =
        densityOf g.coefficient x * (∑ a, (g.coefficient x)⁻¹ a b * Q b a -
          ∑ a, ∑ e, christoffelOf g.coefficient x a b e * (g.coefficient x)⁻¹ e b * P a -
          ∑ a, ∑ e, christoffelOf g.coefficient x b b e * (g.coefficient x)⁻¹ a e * P a +
          ∑ c, ∑ a, christoffelOf g.coefficient x c c b * (g.coefficient x)⁻¹ a b * P a) :=
      fun b => split_aux (densityOf g.coefficient x)
        (fun a e => christoffelOf g.coefficient x a b e * (g.coefficient x)⁻¹ e b)
        (fun a e => christoffelOf g.coefficient x b b e * (g.coefficient x)⁻¹ a e) P
        (fun a => (g.coefficient x)⁻¹ a b * Q b a) (fun c => christoffelOf g.coefficient x c c b)
        (fun a => (g.coefficient x)⁻¹ a b)
    refine (Finset.sum_congr rfl fun b _ => hb b).trans ?_
    rw [← Finset.mul_sum]
    congr 1
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hS1 : ∑ b, ∑ a, (g.coefficient x)⁻¹ a b * Q b a =
      ∑ a, ∑ b, (g.coefficient x)⁻¹ a b * Q a b := by
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hAs j i]
  have hS2 : ∑ b, ∑ a, ∑ e, christoffelOf g.coefficient x a b e * (g.coefficient x)⁻¹ e b *
      P a = ∑ a, ∑ b, (g.coefficient x)⁻¹ a b * ∑ c, christoffelOf g.coefficient x c a b * P c := by
    simp only [Finset.mul_sum]
    rw [show (∑ b, ∑ a, ∑ e, christoffelOf g.coefficient x a b e * (g.coefficient x)⁻¹ e b *
        P a) = ∑ b, ∑ c, ∑ a, (g.coefficient x)⁻¹ a b *
          (christoffelOf g.coefficient x c a b * P c) from
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
        Finset.sum_congr rfl fun a _ => by rw [hΓ c b a]; ring]
    refine (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans ?_
    exact Finset.sum_comm
  have hS34 : ∑ b, ∑ a, ∑ e, christoffelOf g.coefficient x b b e * (g.coefficient x)⁻¹ a e *
      P a = ∑ b, ∑ c, ∑ a, christoffelOf g.coefficient x c c b * (g.coefficient x)⁻¹ a b * P a := by
    symm
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
  refine hsplit.trans ?_
  rw [hS1, hS2, hS34]
  ring

theorem contDiffOn_fderiv_apply (hφ : ContDiffOn ℝ ∞ φ U) (v : MinkowskiModel d) :
    ContDiffOn ℝ ∞ (fun z => fderiv ℝ φ z v) U :=
  (hφ.fderiv_of_isOpen U.isOpen (m := ∞) (by simp)).clm_apply contDiffOn_const

theorem contDiffOn_densityOf : ContDiffOn ℝ ∞ (fun z => densityOf g.coefficient z) U :=
  fun _ hz => (contDiffAt_densityOf hz).contDiffWithinAt

/-- The current `√|g| g^{ab} ∂_aφ`. -/
theorem contDiffOn_density_inv_mul (hφ : ContDiffOn ℝ ∞ φ U) (b : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => densityOf g.coefficient z *
      ∑ a, (g.coefficient z)⁻¹ a b * fderiv ℝ φ z (Pi.single a 1)) U :=
  contDiffOn_densityOf.mul (ContDiffOn.sum fun a _ =>
    (g.contDiffOn_coefficient_inv a b).mul (contDiffOn_fderiv_apply hφ _))

theorem continuousOn_boxOf (hφ : ContDiffOn ℝ ∞ φ U) :
    ContinuousOn (fun z => g.boxOf φ z) U := by
  unfold boxOf hessianOf
  exact continuousOn_finsetSum _ fun a _ => continuousOn_finsetSum _ fun b _ =>
    (g.contDiffOn_coefficient_inv a b).continuousOn.mul
      ((((contDiffOn_fderiv_apply hφ (Pi.single b 1)).fderiv_of_isOpen U.isOpen (m := ∞)
        (by simp)).clm_apply contDiffOn_const).continuousOn.sub
        (continuousOn_finsetSum _ fun c _ => (g.contDiffOn_christoffelOf c a b).continuousOn.mul
          (contDiffOn_fderiv_apply hφ _).continuousOn))

/-- **The field equation from the action.** For a smooth `ψ` with compact support in `U`,
`d/dε (S[φ + εψ] − S[φ]) = ∫ ψ (□φ − m² φ) √|g| dx` at `ε = 0`. -/
theorem hasDerivAt_fieldAction (hφ : ContDiffOn ℝ ∞ φ U) (hψ : ContDiff ℝ ∞ ψ)
    (hK : HasCompactSupport ψ) (hKU : tsupport ψ ⊆ U) (m : ℝ) :
    HasDerivAt (g.fieldAction m φ ψ)
      (∫ x, ψ x * ((g.boxOf φ x - m ^ 2 * φ x) * densityOf g.coefficient x)) 0 := by
  have hact : g.fieldAction m φ ψ = fun ε => ∫ x, (g.fieldVariationDensity m φ ψ (ε, x) -
      g.fieldVariationDensity m φ ψ (0, x)) :=
    funext fun ε => integral_congr_ae (Filter.Eventually.of_forall fun x =>
      fieldDensity_sub_eq hφ hψ hKU m ε x)
  have hd := Variational.hasDerivAt_integral_sub (μ := volume) U.isOpen hK hKU one_pos
    (fun _ _ z hz => contDiffAt_fieldVariationDensity (g := g) hφ hψ m hz)
    fun x hx t => fieldVariationDensity_of_notMem m hx t
  rw [hact]
  refine hd.congr_deriv ?_
  rw [show (fun x => deriv (fun t => g.fieldVariationDensity m φ ψ (t, x)) 0) =
    g.fieldVariationDeriv m φ ψ from
      funext fun x => (hasDerivAt_fieldVariationDensity m φ ψ x).deriv]
  -- integration by parts
  set f : Fin (d + 1) → MinkowskiModel d → ℝ := fun b z => densityOf g.coefficient z *
    ∑ a, (g.coefficient z)⁻¹ a b * fderiv ℝ φ z (Pi.single a 1) with hf
  have hfc (b : Fin (d + 1)) : ContDiffOn ℝ ∞ (f b) U := contDiffOn_density_inv_mul hφ b
  have hψs (b : Fin (d + 1)) : ContDiff ℝ ∞ (fun z => fderiv ℝ ψ z (Pi.single b 1)) :=
    (hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hzero (x : MinkowskiModel d) (hx : x ∉ U) : x ∉ tsupport ψ := fun h' => hx (hKU h')
  have hpt (x : MinkowskiModel d) : g.fieldVariationDeriv m φ ψ x =
      -∑ b, f b x * fderiv ℝ ψ x (Pi.single b 1) -
        m ^ 2 * φ x * ψ x * densityOf g.coefficient x := by
    by_cases hx : x ∈ U
    · have hAs (e₁ e₂ : Fin (d + 1)) : (g.coefficient x)⁻¹ e₁ e₂ = (g.coefficient x)⁻¹ e₂ e₁ :=
        g.coefficient_inv_symmetric hx e₁ e₂
      have hsym : ∑ a, ∑ b, (g.coefficient x)⁻¹ a b *
          (fderiv ℝ ψ x (Pi.single a 1) * fderiv ℝ φ x (Pi.single b 1) +
            fderiv ℝ φ x (Pi.single a 1) * fderiv ℝ ψ x (Pi.single b 1)) =
          2 * ∑ b, (∑ a, (g.coefficient x)⁻¹ a b * fderiv ℝ φ x (Pi.single a 1)) *
            fderiv ℝ ψ x (Pi.single b 1) := by
        have h1 : ∑ a, ∑ b, (g.coefficient x)⁻¹ a b *
            (fderiv ℝ ψ x (Pi.single a 1) * fderiv ℝ φ x (Pi.single b 1)) =
            ∑ b, ∑ a, (g.coefficient x)⁻¹ a b *
              (fderiv ℝ φ x (Pi.single a 1) * fderiv ℝ ψ x (Pi.single b 1)) := by
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
            rw [hAs i j]
            ring
        simp only [mul_add, Finset.sum_add_distrib, h1]
        rw [Finset.sum_comm (f := fun a b => (g.coefficient x)⁻¹ a b *
          (fderiv ℝ φ x (Pi.single a 1) * fderiv ℝ ψ x (Pi.single b 1))), ← two_mul]
        congr 1
        exact Finset.sum_congr rfl fun b _ => by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun a _ => by ring
      have hfs : ∑ b, f b x * fderiv ℝ ψ x (Pi.single b 1) = densityOf g.coefficient x *
          ∑ b, (∑ a, (g.coefficient x)⁻¹ a b * fderiv ℝ φ x (Pi.single a 1)) *
            fderiv ℝ ψ x (Pi.single b 1) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by simp only [hf]; ring
      rw [fieldVariationDeriv, hsym, hfs]
      ring
    · have hxK := hzero x hx
      simp [fieldVariationDeriv, fderiv_eq_zero_of_notMem hxK,
        image_eq_zero_of_notMem_tsupport hxK]
  have hint (F : MinkowskiModel d → ℝ) (hF : ContinuousOn F U)
      (h0 : ∀ x ∉ tsupport ψ, F x = 0) : Integrable F :=
    integrable_of_continuousOn hK hKU hF h0
  have hcont_f (b : Fin (d + 1)) := (hfc b).continuousOn
  have hcont_df (b : Fin (d + 1)) : ContinuousOn (fun x => fderiv ℝ (f b) x (Pi.single b 1)) U :=
    (((hfc b).fderiv_of_isOpen U.isOpen (m := ∞) (by simp)).clm_apply contDiffOn_const).continuousOn
  have hibp (b : Fin (d + 1)) : ∫ x, f b x * fderiv ℝ ψ x (Pi.single b 1) =
      -∫ x, fderiv ℝ (f b) x (Pi.single b 1) * ψ x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (hint _ ((hcont_df b).mul hψ.continuous.continuousOn) fun x hx => by
        simp [image_eq_zero_of_notMem_tsupport hx])
      (hint _ ((hcont_f b).mul (hψs b).continuous.continuousOn) fun x hx => by
        simp [fderiv_eq_zero_of_notMem hx])
      (hint _ ((hcont_f b).mul hψ.continuous.continuousOn) fun x hx => by
        simp [image_eq_zero_of_notMem_tsupport hx])
      (fun x hx => ((hfc b).contDiffAt (U.isOpen.mem_nhds (hKU hx))).differentiableAt (by simp))
      (fun x _ => (hψ.differentiable (by simp)) x)
  have hI1 (b : Fin (d + 1)) : Integrable fun x => f b x * fderiv ℝ ψ x (Pi.single b 1) :=
    hint _ ((hcont_f b).mul (hψs b).continuous.continuousOn) fun x hx => by
      simp [fderiv_eq_zero_of_notMem hx]
  have hI2 : Integrable fun x => m ^ 2 * φ x * ψ x * densityOf g.coefficient x :=
    hint _ (((continuousOn_const.mul hφ.continuousOn).mul hψ.continuous.continuousOn).mul
      contDiffOn_densityOf.continuousOn) fun x hx => by
        simp [image_eq_zero_of_notMem_tsupport hx]
  have hI3 (b : Fin (d + 1)) : Integrable fun x => fderiv ℝ (f b) x (Pi.single b 1) * ψ x :=
    hint _ ((hcont_df b).mul hψ.continuous.continuousOn) fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport hx]
  have hS : Integrable fun x => ∑ b, f b x * fderiv ℝ ψ x (Pi.single b 1) :=
    integrable_finsetSum _ fun b _ => hI1 b
  have hneg : Integrable fun x => -∑ b, f b x * fderiv ℝ ψ x (Pi.single b 1) := hS.neg
  have hS3 : Integrable fun x => ∑ b, fderiv ℝ (f b) x (Pi.single b 1) * ψ x :=
    integrable_finsetSum _ fun b _ => hI3 b
  rw [show g.fieldVariationDeriv m φ ψ = _ from funext hpt, integral_sub hneg hI2, integral_neg,
    integral_finsetSum _ fun b _ => hI1 b]
  simp only [hibp, Finset.sum_neg_distrib, neg_neg]
  rw [← integral_finsetSum _ fun b _ => hI3 b, ← integral_sub hS3 hI2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ U
  · have h := sum_fderiv_density_inv_mul (g := g) hφ hx
    simp only [hf] at h ⊢
    rw [← Finset.sum_mul, h]
    ring
  · have hxK := hzero x hx
    simp [image_eq_zero_of_notMem_tsupport hxK]

/-- **The Klein–Gordon equation.** The action of the scalar field is stationary under every
smooth variation with compact support in `U` if and only if `□φ = m² φ` on `U`. -/
theorem isFieldStationary_iff (hφ : ContDiffOn ℝ ∞ φ U) (m : ℝ) :
    (∀ ψ : MinkowskiModel d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      HasDerivAt (g.fieldAction m φ ψ) 0 0) ↔ ∀ x ∈ U, g.boxOf φ x = m ^ 2 * φ x := by
  set F : MinkowskiModel d → ℝ := fun x => (g.boxOf φ x - m ^ 2 * φ x) * densityOf g.coefficient x
  have hFc : ContinuousOn F U :=
    ((continuousOn_boxOf hφ).sub (continuousOn_const.mul hφ.continuousOn)).mul
      contDiffOn_densityOf.continuousOn
  constructor
  · intro hst x hx
    have htest : ∀ ψ : MinkowskiModel d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ U → ∫ z, ψ z • F z = 0 := fun ψ hψ hK hKU =>
      (hasDerivAt_fieldAction hφ hψ hK hKU m).unique (hst ψ hψ hK hKU)
    have hae := U.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hFc.locallyIntegrableOn U.isOpen.measurableSet) htest
    have heq := Measure.eqOn_open_of_ae_eq (μ := volume)
      ((ae_restrict_iff' U.isOpen.measurableSet).mpr hae) U.isOpen hFc continuousOn_const hx
    have h0 : g.boxOf φ x - m ^ 2 * φ x = 0 :=
      (mul_eq_zero.mp heq).resolve_right (densityOf_pos hx).ne'
    linarith
  · intro hKG ψ hψ hK hKU
    have hd := hasDerivAt_fieldAction (g := g) hφ hψ hK hKU m
    have h0 : (fun x => ψ x * ((g.boxOf φ x - m ^ 2 * φ x) * densityOf g.coefficient x)) =
        fun _ => 0 := by
      funext x
      by_cases hx : x ∈ U
      · rw [hKG x hx, sub_self, zero_mul, mul_zero]
      · rw [image_eq_zero_of_notMem_tsupport fun h' => hx (hKU h'), zero_mul]
    rwa [h0, integral_zero] at hd

/-- The native divergence of the stress of a scalar field: `∇^a T_{ab} = (□φ − m² φ) ∂_bφ`. -/
theorem bilinearDivergence_scalarStress (hφ : ContDiffOn ℝ ∞ φ U) (m : ℝ) (y : U)
    (b : Fin (d + 1)) :
    g.toLorentzMetric.bilinearDivergenceCovector
        (bilinearOf (g.scalarStress m φ) (contDiffOn_scalarStress hφ m)) y
        (chartField (physicalChart y) (Pi.single b 1) y) =
      (g.boxOf φ y - m ^ 2 * φ y) * fderiv ℝ φ y (Pi.single b 1) := by
  exact (bilinearDivergence_bilinearOf (T := g.scalarStress m φ) _ y b).trans
    (divergenceOf_scalarStress hφ m y.property b)

/-- **A solution of the Klein–Gordon equation has a conserved stress** on the fixed metric. -/
theorem bilinearDivergence_scalarStress_eq_zero (hφ : ContDiffOn ℝ ∞ φ U) (m : ℝ)
    (hKG : ∀ x ∈ U, g.boxOf φ x = m ^ 2 * φ x) (y : U) :
    g.toLorentzMetric.bilinearDivergenceCovector
      (bilinearOf (g.scalarStress m φ) (contDiffOn_scalarStress hφ m)) y = 0 := by
  refine ext_chartField (physicalChart_mem y) (by simp) fun b => ?_
  rw [bilinearDivergence_scalarStress hφ m y b, hKG y y.property, sub_self, zero_mul,
    zero_apply]

end CoordinateMetric

end ProjectAinos.SmoothGeometry
