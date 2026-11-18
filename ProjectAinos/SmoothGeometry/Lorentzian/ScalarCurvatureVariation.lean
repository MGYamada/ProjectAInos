/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateFirstVariation

/-!
# The first variation of the scalar curvature density

For a coordinate metric `g` on an open set `U` and a smooth symmetric variation `h`, at every
point of `U`

`δ((R − 2Λ) √|g|) = −(Ric^{mn} − (R/2 − Λ) g^{mn}) h_{mn} √|g| + ∂_a(√|g| V^a)`,

with `V^a = g^{bc} δΓ^a_{bc} − g^{ab} δΓ^c_{cb}` (`hasDerivAt_scalarDensity`). The derivative is
the derivative in `ε` at `0` of the coefficients of `g + ε h`; the divergence term comes from the
variation of the Ricci tensor through `palatini_algebra`.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

/-- Contracting a matrix `R` against `−A H A` for a symmetric `A` raises both indices of `R`. -/
theorem sum_mul_neg_sandwich {n : ℕ} (R A H : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ a b, A a b = A b a) :
    ∑ a, ∑ c, R a c * -((A * H * A) a c) =
      -∑ m, ∑ k, (∑ a, ∑ c, A m a * A k c * R a c) * H m k := by
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_neg,
    Finset.sum_neg_distrib, neg_inj]
  calc ∑ a, ∑ c, ∑ k, ∑ m, R a c * (A a m * H m k * A k c) =
        ∑ a, ∑ k, ∑ c, ∑ m, R a c * (A a m * H m k * A k c) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ k, ∑ m, ∑ c, R a c * (A a m * H m k * A k c) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ a, ∑ m, ∑ k, ∑ c, R a c * (A a m * H m k * A k c) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ m, ∑ a, ∑ k, ∑ c, R a c * (A a m * H m k * A k c) := Finset.sum_comm
    _ = ∑ m, ∑ k, ∑ a, ∑ c, R a c * (A a m * H m k * A k c) :=
        Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ =>
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by
          rw [hA a m]
          ring

namespace CoordinateMetric

variable {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U)
  (h : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)

/-- The variation `δΓ^k_{ij}` of the Christoffel symbols of `g + ε h`. -/
abbrev christoffelVariation (z : MinkowskiModel d) (k i j : Fin (d + 1)) : ℝ :=
  familyChristoffelDeriv (g.variationFamily h) z k i j

/-- The vector field `V^a = g^{bc} δΓ^a_{bc} − g^{ab} δΓ^c_{cb}` whose divergence the variation
of the Ricci tensor contributes. -/
def variationVector (z : MinkowskiModel d) (a : Fin (d + 1)) : ℝ :=
  ∑ b, ∑ c, (g.coefficient z)⁻¹ b c * g.christoffelVariation h z a b c -
    ∑ b, (g.coefficient z)⁻¹ a b * ∑ c, g.christoffelVariation h z c c b

/-- The Ricci tensor with both indices raised. -/
def ricciUp (z : MinkowskiModel d) (m n : Fin (d + 1)) : ℝ :=
  ∑ a, ∑ c, (g.coefficient z)⁻¹ m a * (g.coefficient z)⁻¹ n c * ricciOf g.coefficient z a c

variable {g h}

theorem familyChristoffel_variationFamily_zero (z : MinkowskiModel d) (k i j : Fin (d + 1)) :
    familyChristoffel (g.variationFamily h) (0, z) k i j = christoffelOf g.coefficient z k i j := by
  unfold familyChristoffel
  rw [g.variationFamily_zero h]

theorem familyRicci_variationFamily_zero (z : MinkowskiModel d) (j k : Fin (d + 1)) :
    familyRicci (g.variationFamily h) (0, z) j k = ricciOf g.coefficient z j k := by
  unfold familyRicci
  rw [g.variationFamily_zero h]

theorem contDiffAt_christoffelVariation (hh : ContDiff ℝ ∞ h) {x : MinkowskiModel d}
    (hx : x ∈ U) (k i j : Fin (d + 1)) :
    DifferentiableAt ℝ (fun z => g.christoffelVariation h z k i j) x := by
  have hD := ((g.contDiffAt_variationChristoffel hh hx k i j).fderiv_right (m := 1)
    (by simp)).clm_apply (contDiffAt_const (c := ((1 : ℝ), (0 : MinkowskiModel d))))
  have hin : ContDiffAt ℝ 1 (fun z : MinkowskiModel d => ((0 : ℝ), z)) x :=
    contDiffAt_const.prodMk contDiffAt_id
  exact (hD.comp x hin).differentiableAt (by simp)

/-- The divergence term, expanded by the product rule. -/
theorem fderiv_density_mul_variationVector (hh : ContDiff ℝ ∞ h) {x : MinkowskiModel d}
    (hx : x ∈ U) (a : Fin (d + 1)) :
    fderiv ℝ (fun z => densityOf g.coefficient z * g.variationVector h z a) x (Pi.single a 1) =
      densityOf g.coefficient x *
          (∑ b, ∑ c, ((g.coefficient x)⁻¹ b c *
              fderiv ℝ (fun z => g.christoffelVariation h z a b c) x (Pi.single a 1) +
            g.christoffelVariation h x a b c *
              fderiv ℝ (fun z => (g.coefficient z)⁻¹ b c) x (Pi.single a 1)) -
          ∑ b, ((g.coefficient x)⁻¹ a b *
              ∑ c, fderiv ℝ (fun z => g.christoffelVariation h z c c b) x (Pi.single a 1) +
            (∑ c, g.christoffelVariation h x c c b) *
              fderiv ℝ (fun z => (g.coefficient z)⁻¹ a b) x (Pi.single a 1))) +
        g.variationVector h x a * fderiv ℝ (fun z => densityOf g.coefficient z) x (Pi.single a 1)
      := by
  have hG (b c : Fin (d + 1)) : HasFDerivAt (fun z => (g.coefficient z)⁻¹ b c)
      (fderiv ℝ (fun z => (g.coefficient z)⁻¹ b c) x) x :=
    (((g.contDiffOn_coefficient_inv b c).contDiffAt (U.isOpen.mem_nhds hx)).differentiableAt
      (by simp)).hasFDerivAt
  have hP (k i j : Fin (d + 1)) : HasFDerivAt (fun z => g.christoffelVariation h z k i j)
      (fderiv ℝ (fun z => g.christoffelVariation h z k i j) x) x :=
    (contDiffAt_christoffelVariation hh hx k i j).hasFDerivAt
  have hρ : HasFDerivAt (fun z => densityOf g.coefficient z)
      (fderiv ℝ (fun z => densityOf g.coefficient z) x) x :=
    ((g.contDiffAt_densityOf hx).differentiableAt (by simp)).hasFDerivAt
  have hV := (HasFDerivAt.fun_sum (u := Finset.univ) fun b _ =>
      HasFDerivAt.fun_sum (u := Finset.univ) fun c _ => (hG b c).mul (hP a b c)).sub
    (HasFDerivAt.fun_sum (u := Finset.univ) fun b _ =>
      (hG a b).mul (HasFDerivAt.fun_sum (u := Finset.univ) fun c _ => hP c c b))
  have hfd : fderiv ℝ (fun z => densityOf g.coefficient z * g.variationVector h z a) x = _ :=
    (hρ.mul hV).fderiv
  rw [hfd]
  simp only [add_apply, smul_apply, smul_eq_mul, sub_apply, sum_apply]
  rfl

/-- **The first variation of the Einstein–Hilbert density** at a point of `U`:
`δ((R − 2Λ) √|g|) = −(Ric^{mn} − (R/2 − Λ) g^{mn}) h_{mn} √|g| + ∂_a(√|g| V^a)`. -/
theorem hasDerivAt_scalarDensity (hh : ContDiff ℝ ∞ h) (hs : ∀ z v w, h z v w = h z w v)
    (Λ : ℝ) {x : MinkowskiModel d} (hx : x ∈ U) :
    HasDerivAt (fun ε => (familyScalar (g.variationFamily h) (ε, x) - 2 * Λ) *
        familyDensity (g.variationFamily h) (ε, x))
      (-(densityOf g.coefficient x * ∑ m, ∑ n, (g.ricciUp x m n -
          (scalarOf g.coefficient x / 2 - Λ) * (g.coefficient x)⁻¹ m n) * formCoeff h x m n) +
        ∑ a, fderiv ℝ (fun z => densityOf g.coefficient z * g.variationVector h z a) x
          (Pi.single a 1)) 0 := by
  set ρ := densityOf g.coefficient x with hρdef
  set S := scalarOf g.coefficient x with hSdef
  have hΓ := g.contDiffAt_variationChristoffel hh hx
  have hS := hasDerivAt_familyScalar (Cp := g.variationFamily h) hΓ
    (g.hasDerivAt_variationFamily_inv hh hx)
  have hρ := g.hasDerivAt_variationFamily_density hs hx
  have hprod := (hS.sub_const (2 * Λ)).mul hρ
  have hS0 : familyScalar (g.variationFamily h) (0, x) = S := by
    unfold familyScalar
    rw [g.variationFamily_zero h]
  have hρ0 : familyDensity (g.variationFamily h) (0, x) = ρ := by
    unfold familyDensity
    rw [g.variationFamily_zero h]
  have hinv0 : (g.variationFamily h (0, x))⁻¹ = (g.coefficient x)⁻¹ := by
    simp [variationFamily]
  -- the arrays of the Palatini identity
  let G : Fin (d + 1) → Fin (d + 1) → ℝ := fun b c => (g.coefficient x)⁻¹ b c
  let Γ : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ :=
    fun a b c => christoffelOf g.coefficient x a b c
  let P : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ :=
    fun a b c => g.christoffelVariation h x a b c
  let DP : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ := fun e a b c =>
    fderiv ℝ (fun z => g.christoffelVariation h z a b c) x (Pi.single e 1)
  let DG : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ := fun e b c =>
    fderiv ℝ (fun z => (g.coefficient z)⁻¹ b c) x (Pi.single e 1)
  have hpal := palatini_algebra G Γ P DP DG (g.coefficient_inv_symmetric hx)
    (g.christoffelOf_coefficient_symm hx) (g.christoffelVariation_symm hs hx)
    (fun e b c => g.fderiv_coefficient_inv hx b c e)
  have hX : (∑ a, ∑ c, familyRicciDeriv (g.variationFamily h) x a c * (g.coefficient x)⁻¹ a c) =
      ∑ b, ∑ c, G b c * (∑ a, (DP a a b c - DP b a a c +
        ∑ d, ((P a a d * Γ d b c + Γ a a d * P d b c) -
          (P a b d * Γ d a c + Γ a b d * P d a c)))) := by
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm]
    unfold familyRicciDeriv
    simp only [familyChristoffel_variationFamily_zero]
    rfl
  have hdiv : (∑ a, fderiv ℝ (fun z => densityOf g.coefficient z * g.variationVector h z a) x
      (Pi.single a 1)) = ρ * ∑ b, ∑ c, G b c * (∑ a, (DP a a b c - DP b a a c +
        ∑ d, ((P a a d * Γ d b c + Γ a a d * P d b c) -
          (P a b d * Γ d a c + Γ a b d * P d a c)))) := by
    rw [hpal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [fderiv_density_mul_variationVector hh hx a, g.fderiv_densityOf hx a]
    have h1 : (∑ b, ∑ c, ((g.coefficient x)⁻¹ b c *
          fderiv ℝ (fun z => g.christoffelVariation h z a b c) x (Pi.single a 1) +
        g.christoffelVariation h x a b c *
          fderiv ℝ (fun z => (g.coefficient z)⁻¹ b c) x (Pi.single a 1))) =
        ∑ b, ∑ c, (DG a b c * P a b c + G b c * DP a a b c) :=
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by
        simp only [DG, P, G, DP]
        ring
    have h2 : (∑ b, ((g.coefficient x)⁻¹ a b *
          ∑ c, fderiv ℝ (fun z => g.christoffelVariation h z c c b) x (Pi.single a 1) +
        (∑ c, g.christoffelVariation h x c c b) *
          fderiv ℝ (fun z => (g.coefficient z)⁻¹ a b) x (Pi.single a 1))) =
        ∑ b, (DG a a b * ∑ c, P c c b + G a b * ∑ c, DP a c c b) :=
      Finset.sum_congr rfl fun b _ => by
        simp only [DG, P, G, DP]
        ring
    rw [h1, h2]
    simp only [variationVector, G, P, Γ]
    ring
  have hRQ : (∑ a, ∑ c, ricciOf g.coefficient x a c *
      -(((g.coefficient x)⁻¹ * formCoeff h x * (g.coefficient x)⁻¹) a c)) =
      -∑ m, ∑ n, g.ricciUp x m n * formCoeff h x m n :=
    sum_mul_neg_sandwich (fun a c => ricciOf g.coefficient x a c) _ _
      (g.coefficient_inv_symmetric hx)
  have hsplit : (∑ m, ∑ n, (g.ricciUp x m n - (S / 2 - Λ) * (g.coefficient x)⁻¹ m n) *
        formCoeff h x m n) = (∑ m, ∑ n, g.ricciUp x m n * formCoeff h x m n) -
      (S / 2 - Λ) * ∑ m, ∑ n, (g.coefficient x)⁻¹ m n * formCoeff h x m n := by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  convert hprod using 1
  rw [hinv0, hS0, hρ0]
  simp only [familyRicci_variationFamily_zero, Finset.sum_add_distrib]
  rw [hX, hRQ, hdiv, hsplit]
  ring

end CoordinateMetric

end ProjectAinos.SmoothGeometry
