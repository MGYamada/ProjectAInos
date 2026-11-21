/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.Linearized
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateGeodesic
public import ProjectAinos.SmoothGeometry.Lorentzian.ChristoffelCertificate
public import ProjectAinos.SmoothGeometry.Lorentzian.CurvatureNaturality

/-!
# The linearization about a curved background

For a coordinate metric `g` on an open set `U` of the model space and a field `h` of coefficient
matrices, smooth and symmetric on `U`, the family `g + ε h` (`perturbationFamily`) has the first
variations `familyChristoffelDeriv` and `familyRicciDeriv` of `CoordinateFamily.lean`. This file
writes them covariantly, with the Levi-Civita connection of `g` (Landau–Lifshitz, §108).

* `covDerivTwo`, `covDerivThree`: the covariant derivatives `∇_a h_{ij}` and `∇_a P^k_{ij}` of
  coefficient arrays, with `Γ = christoffelOf g.coefficient`.
* `familyChristoffelDeriv_eq`: `δΓ^k_{ij} = ½ g^{kl} (∇_i h_{jl} + ∇_j h_{li} − ∇_l h_{ij})`
  (`curvedChristoffel`). `familyChristoffelDeriv_eq_of_family` is the same for any family that is
  smooth near `ε = 0` and equals `g` there, with `h` its derivative `familyCoeffDeriv`; it uses
  `hasDerivAt_matrix_inv`, `δ(M⁻¹) = −M⁻¹ Ṁ M⁻¹`.
* `familyRicciDeriv_eq`, `familyRicciDeriv_eq_palatini`: the Palatini identity
  `δRic_{jk} = ∇_i δΓ^i_{jk} − ∇_j δΓ^i_{ik}` (`palatini`). `hasDerivAt_ricciOf_perturbation`:
  this is the derivative at `ε = 0` of `ricciOf (g + ε h)`.
* **Gauge invariance.** `coordinateLieMetric X g` is `L_X g` (`lieOf`). On a Ricci-flat
  background, `familyRicciDeriv_lie_eq_zero`: `δRic[L_X g] = 0`, and `familyRicciDeriv_add_lie`:
  `δRic[h + L_X g] = δRic[h]`. The proof compares `g + ε L_X g` with the pullback of `g` by
  `z ↦ z + ε X(z)` (`pullbackFamily`, the coordinate metric `pullbackMetric` on `pullbackDomain`,
  the map `pullbackMap`). Both families have the derivative `L_X g` at `ε = 0`
  (`familyCoeffDeriv_pullbackFamily`), and the pullback is Ricci flat by the naturality of the
  native curvature (`ricciOf_pullbackFamily`, `familyRicciDeriv_pullbackFamily`).
* **Leibniz rules.** `curvedChristoffel_smul`: `δΓ[f a] = f δΓ[a] + Q(df, a)`, with the algebraic
  part `symbolChristoffel`; `palatini_smul_add`, `palatini_smul`; the linearity
  (`curvedChristoffel_add`, `palatini_add`) and the smoothness (`contDiffOn_curvedChristoffel`).
* **Flat background.** `perturbationFamily_minkowski`, `curvedChristoffel_minkowski` and
  `palatini_curvedChristoffel_minkowski` recover `linearizedChristoffel` and `linearizedRicci` of
  `Linearized.lean`; `familyRicciDeriv_lie_minkowski` is the flat gauge invariance.
* **Rays.** For a phase `ψ`, `gradientField` is `k = (dψ)^♯` and `gradientNorm` is `g(dψ, dψ)`.
  `gradientField_covariant`: `k^i ∂_i k^k + Γ^k_{ij} k^i k^j = ½ g^{km} ∂_m g(dψ, dψ)`, that is
  `∇_k k = ½ ∇ g(k, k)`. `isGeodesicOn_ray`: if `g(dψ, dψ) = 0` on `U`, the integral curves of `k`
  are affinely parametrized geodesics (in the sense of `isGeodesicOn_iff`), with null velocity
  (`form_curveVelocity_ray`).
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

/-! ### The derivative of an inverse matrix -/

/-- The derivative of the inverse of a family of matrices: `δ(M⁻¹) = −M⁻¹ Ṁ M⁻¹`. -/
theorem hasDerivAt_matrix_inv {n : ℕ} {M : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {M' : Matrix (Fin n) (Fin n) ℝ} (hM : ∀ i j, HasDerivAt (fun ε => M ε i j) (M' i j) 0)
    (hdet : (M 0).det ≠ 0) (k l : Fin n) :
    HasDerivAt (fun ε => (M ε)⁻¹ k l) (-((M 0)⁻¹ * M' * (M 0)⁻¹) k l) 0 := by
  set A := M 0
  have hMd : HasDerivAt (fun ε => (fun i j => M ε i j : Fin n → Fin n → ℝ))
      (fun i j => M' i j) 0 := hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hM i j
  have hinvd (a c : Fin n) : DifferentiableAt ℝ (fun ε => (M ε)⁻¹ a c) 0 := by
    have h1 := (contDiffAt_matrix_inv_apply (A := fun i j => A i j) hdet a c).differentiableAt
      (by simp)
    exact h1.comp (0 : ℝ) hMd.differentiableAt
  set N : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a c => deriv (fun ε => (M ε)⁻¹ a c) 0
  have hN (a c : Fin n) : HasDerivAt (fun ε => (M ε)⁻¹ a c) (N a c) 0 := (hinvd a c).hasDerivAt
  have hcont : ContinuousAt (fun ε => (M ε).det) 0 :=
    (MetricDensity.contDiff_matrix_det (r := 0)).continuous.continuousAt.comp
      (f := fun ε => (fun i j => M ε i j : Fin n → Fin n → ℝ)) hMd.continuousAt
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), (M ε).det ≠ 0 := hcont.eventually_ne hdet
  have hprod (a b : Fin n) : HasDerivAt (fun ε => ∑ m, (M ε)⁻¹ a m * M ε m b)
      (∑ m, (N a m * A m b + A⁻¹ a m * M' m b)) 0 :=
    HasDerivAt.fun_sum fun m _ => (hN a m).fun_mul (hM m b)
  have hzero (a b : Fin n) : ∑ m, (N a m * A m b + A⁻¹ a m * M' m b) = 0 := by
    have hconst : (fun ε => ∑ m, (M ε)⁻¹ a m * M ε m b) =ᶠ[𝓝 0]
        fun _ => (1 : Matrix (Fin n) (Fin n) ℝ) a b := by
      filter_upwards [hev] with ε hε
      have hi := Matrix.nonsing_inv_mul (M ε) (isUnit_iff_ne_zero.mpr hε)
      have h' := congrFun (congrFun hi a) b
      rwa [Matrix.mul_apply] at h'
    exact (hprod a b).unique ((hasDerivAt_const _ _).congr_of_eventuallyEq hconst)
  have hmat : N * A = -(A⁻¹ * M') := by
    ext a b
    have := hzero a b
    simp only [Matrix.mul_apply, Matrix.neg_apply, Finset.sum_add_distrib] at this ⊢
    linarith
  have hsol : N = -(A⁻¹ * M' * A⁻¹) := by
    have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hdet)
    calc N = N * (A * A⁻¹) := by rw [hAA, Matrix.mul_one]
      _ = (N * A) * A⁻¹ := by rw [Matrix.mul_assoc]
      _ = _ := by rw [hmat, Matrix.neg_mul]
  have := hN k l
  rwa [show N k l = (-(A⁻¹ * M' * A⁻¹)) k l by rw [hsol]] at this

/-! ### Covariant derivatives of coefficient arrays -/

section Covariant

variable (g : CoordinateMetric σ d U)

/-- The covariant derivative `∇_a h_{ij} = ∂_a h_{ij} − Γ^b_{ai} h_{bj} − Γ^b_{aj} h_{ib}` of a
field of coefficient matrices, with the Christoffel symbols `Γ = christoffelOf g.coefficient`. -/
def covDerivTwo (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (a i j : Fin (d + 1)) : ℝ :=
  fderiv ℝ (fun z => h z i j) x (Pi.single a 1) -
    ∑ b, (christoffelOf g.coefficient x b a i * h x b j +
      christoffelOf g.coefficient x b a j * h x i b)

/-- The covariant derivative `∇_a P^k_{ij} = ∂_a P^k_{ij} + Γ^k_{ab} P^b_{ij} − Γ^b_{ai} P^k_{bj}
− Γ^b_{aj} P^k_{ib}` of an array with one upper and two lower indices. -/
def covDerivThree (P : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ)
    (x : MinkowskiModel d) (a k i j : Fin (d + 1)) : ℝ :=
  fderiv ℝ (fun z => P z k i j) x (Pi.single a 1) +
    ∑ b, (christoffelOf g.coefficient x k a b * P x b i j -
      christoffelOf g.coefficient x b a i * P x k b j -
      christoffelOf g.coefficient x b a j * P x k i b)

/-- **The linearized Christoffel symbols on the background `g`**,
`δΓ^k_{ij} = ½ g^{kl} (∇_i h_{jl} + ∇_j h_{li} − ∇_l h_{ij})`. -/
def curvedChristoffel (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (k i j : Fin (d + 1)) : ℝ :=
  ∑ l, (g.coefficient x)⁻¹ k l *
    (g.covDerivTwo h x i j l + g.covDerivTwo h x j l i - g.covDerivTwo h x l i j) / 2

/-- **The Palatini form** `∇_i P^i_{jk} − ∇_j P^i_{ik}` of an array `P^i_{jk}`. -/
def palatini (P : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ)
    (x : MinkowskiModel d) (j k : Fin (d + 1)) : ℝ :=
  ∑ i, (g.covDerivThree P x i i j k - g.covDerivThree P x j i i k)

/-- The family `g + ε h` of coefficients, as a function of `(ε, z)`. -/
def perturbationFamily (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (p : ℝ × MinkowskiModel d) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  g.coefficient p.2 + p.1 • h p.2

theorem perturbationFamily_apply (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (p : ℝ × MinkowskiModel d) (i j : Fin (d + 1)) :
    g.perturbationFamily h p i j = g.coefficient p.2 i j + p.1 * h p.2 i j := by
  simp [perturbationFamily]

theorem perturbationFamily_zero
    (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    (fun z => g.perturbationFamily h (0, z)) = g.coefficient := by
  funext z
  simp [perturbationFamily]

variable {g}

theorem covDerivTwo_congr {h h' : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {x : MinkowskiModel d} (hh : h =ᶠ[𝓝 x] h') (a i j : Fin (d + 1)) :
    g.covDerivTwo h x a i j = g.covDerivTwo h' x a i j := by
  have hd (p q : Fin (d + 1)) : fderiv ℝ (fun z => h z p q) x = fderiv ℝ (fun z => h' z p q) x :=
    Filter.EventuallyEq.fderiv_eq (hh.mono fun z hz => congrArg (fun M => M p q) hz)
  unfold covDerivTwo
  rw [hh.eq_of_nhds, hd]

theorem curvedChristoffel_congr {h h' : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {x : MinkowskiModel d} (hh : h =ᶠ[𝓝 x] h') (k i j : Fin (d + 1)) :
    g.curvedChristoffel h x k i j = g.curvedChristoffel h' x k i j := by
  unfold curvedChristoffel
  simp only [covDerivTwo_congr hh]

theorem covDerivThree_congr
    {P P' : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ}
    {x : MinkowskiModel d} (hP : P =ᶠ[𝓝 x] P') (a k i j : Fin (d + 1)) :
    g.covDerivThree P x a k i j = g.covDerivThree P' x a k i j := by
  have hd (p q r : Fin (d + 1)) :
      fderiv ℝ (fun z => P z p q r) x = fderiv ℝ (fun z => P' z p q r) x :=
    Filter.EventuallyEq.fderiv_eq (hP.mono fun z hz => by simp only [hz])
  unfold covDerivThree
  rw [hP.eq_of_nhds, hd]

theorem palatini_congr {P P' : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ}
    {x : MinkowskiModel d} (hP : P =ᶠ[𝓝 x] P') (j k : Fin (d + 1)) :
    g.palatini P x j k = g.palatini P' x j k := by
  unfold palatini
  simp only [covDerivThree_congr hP]

end Covariant

/-! ### The first variation of the Christoffel symbols -/

/-- The derivative in the parameter at `ε = 0` of a family of coefficients, `Ċ_{ij}(z)`. -/
def familyCoeffDeriv (Cp : ℝ × MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (z : MinkowskiModel d) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.of fun i j => fderiv ℝ (fun q => Cp q i j) ((0 : ℝ), z) (1, 0)

section Variation

variable {g : CoordinateMetric σ d U}

/-- **The variation of the Christoffel symbols of a family.** If a family of coefficients is
smooth near `(0, x)`, equals `g` at `ε = 0` near `x`, and has a symmetric derivative `Ċ` at `x`,
then `δΓ^k_{ij} = ½ g^{kl} (∇_i Ċ_{jl} + ∇_j Ċ_{li} − ∇_l Ċ_{ij})`. -/
theorem familyChristoffelDeriv_eq_of_family
    {Cp : ℝ × MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {x : MinkowskiModel d} (hx : x ∈ U)
    (hC : ∀ i j, ContDiffAt ℝ ∞ (fun q => Cp q i j) ((0 : ℝ), x))
    (h0 : (fun z => Cp (0, z)) =ᶠ[𝓝 x] g.coefficient)
    (hs : ∀ i j, familyCoeffDeriv Cp x i j = familyCoeffDeriv Cp x j i) (k i j : Fin (d + 1)) :
    familyChristoffelDeriv Cp x k i j = g.curvedChristoffel (familyCoeffDeriv Cp) x k i j := by
  set A := g.coefficient x
  set V := familyCoeffDeriv Cp
  have hA0 : Cp (0, x) = A := h0.eq_of_nhds
  have hdet : (Cp (0, x)).det ≠ 0 := by rw [hA0]; exact g.coefficient_det_ne_zero ⟨x, hx⟩
  have hΓ := contDiffAt_familyChristoffel hC hdet k i j
  have hent (a b : Fin (d + 1)) : HasDerivAt (fun ε => Cp (ε, x) a b) (V x a b) 0 :=
    hasDerivAt_slice ((hC a b).differentiableAt (by simp))
  have hinv (l : Fin (d + 1)) : HasDerivAt (fun ε => (Cp (ε, x))⁻¹ k l)
      (-(A⁻¹ * V x * A⁻¹) k l) 0 := by
    have := hasDerivAt_matrix_inv (M := fun ε => Cp (ε, x)) hent hdet k l
    simpa only [hA0] using this
  have hpar (a b c : Fin (d + 1)) : HasDerivAt
      (fun ε => fderiv ℝ (fun z => Cp (ε, z) a b) x (Pi.single c 1))
      (fderiv ℝ (fun z => V z a b) x (Pi.single c 1)) 0 :=
    hasDerivAt_fderiv_slice (hC a b) _
  have hg0 (a b c : Fin (d + 1)) :
      fderiv ℝ (fun z => Cp (0, z) a b) x (Pi.single c 1) =
        fderiv ℝ (fun z => g.coefficient z a b) x (Pi.single c 1) := by
    rw [Filter.EventuallyEq.fderiv_eq (h0.mono fun z hz => congrArg (fun M => M a b) hz)]
  set D₀ : Fin (d + 1) → ℝ := fun l =>
    fderiv ℝ (fun z => g.coefficient z j l) x (Pi.single i 1) +
      fderiv ℝ (fun z => g.coefficient z l i) x (Pi.single j 1) -
      fderiv ℝ (fun z => g.coefficient z i j) x (Pi.single l 1)
  set D₁ : Fin (d + 1) → ℝ := fun l =>
    fderiv ℝ (fun z => V z j l) x (Pi.single i 1) +
      fderiv ℝ (fun z => V z l i) x (Pi.single j 1) -
      fderiv ℝ (fun z => V z i j) x (Pi.single l 1)
  have hsum : HasDerivAt (fun ε => familyChristoffel Cp (ε, x) k i j)
      (∑ l, (-(A⁻¹ * V x * A⁻¹) k l * D₀ l + A⁻¹ k l * D₁ l) / 2) 0 := by
    have h := HasDerivAt.fun_sum (u := Finset.univ) fun l _ =>
      ((hinv l).fun_mul (((hpar j l i).fun_add (hpar l i j)).fun_sub (hpar i j l))).div_const 2
    convert h using 1
    · funext ε
      rfl
    · refine Finset.sum_congr rfl fun l _ => ?_
      simp only [hg0, hA0, D₀, D₁]
  rw [(hasDerivAt_familyChristoffel hΓ).unique hsum]
  -- the algebra
  have hΓdef (m : Fin (d + 1)) : christoffelOf g.coefficient x m i j = ∑ l, A⁻¹ m l * D₀ l / 2 :=
    rfl
  have hsymΓ (a b c : Fin (d + 1)) : christoffelOf g.coefficient x a b c =
      christoffelOf g.coefficient x a c b := g.christoffelOf_coefficient_symm hx a b c
  have hcov : ∀ l, g.covDerivTwo V x i j l + g.covDerivTwo V x j l i - g.covDerivTwo V x l i j =
      D₁ l - 2 * ∑ b, christoffelOf g.coefficient x b i j * V x b l := by
    intro l
    have this : ∀ b, christoffelOf g.coefficient x b i j * V x b l +
          christoffelOf g.coefficient x b i l * V x j b +
        (christoffelOf g.coefficient x b j l * V x b i +
          christoffelOf g.coefficient x b j i * V x l b) -
        (christoffelOf g.coefficient x b l i * V x b j +
          christoffelOf g.coefficient x b l j * V x i b) =
        2 * (christoffelOf g.coefficient x b i j * V x b l) := by
      intro b
      rw [hsymΓ b l i, hsymΓ b l j, hsymΓ b j i, hs j b, hs b i, hs l b]
      ring
    have hX : ∑ b, (christoffelOf g.coefficient x b i j * V x b l +
          christoffelOf g.coefficient x b i l * V x j b) +
        ∑ b, (christoffelOf g.coefficient x b j l * V x b i +
          christoffelOf g.coefficient x b j i * V x l b) -
        ∑ b, (christoffelOf g.coefficient x b l i * V x b j +
          christoffelOf g.coefficient x b l j * V x i b) =
        2 * ∑ b, christoffelOf g.coefficient x b i j * V x b l := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => this b
    simp only [covDerivTwo, D₁]
    linarith [hX]
  unfold curvedChristoffel
  simp only [hcov]
  have hT : ∑ l, (A⁻¹ * V x * A⁻¹) k l * D₀ l / 2 =
      ∑ l, A⁻¹ k l * ∑ b, christoffelOf g.coefficient x b i j * V x b l := by
    have e1 : ∑ l, (A⁻¹ * V x * A⁻¹) k l * D₀ l / 2 =
        ∑ l, ∑ m, ∑ n, A⁻¹ k n * V x n m * A⁻¹ m l * D₀ l / 2 := by
      simp only [Matrix.mul_apply, Finset.sum_mul, Finset.sum_div]
    have e2 : ∑ l, A⁻¹ k l * ∑ b, christoffelOf g.coefficient x b i j * V x b l =
        ∑ n, ∑ m, ∑ l, A⁻¹ k n * V x n m * A⁻¹ m l * D₀ l / 2 := by
      simp only [hΓdef, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ =>
        Finset.sum_congr rfl fun l _ => ?_
      rw [hs m n]
      ring
    calc ∑ l, (A⁻¹ * V x * A⁻¹) k l * D₀ l / 2
        = ∑ l, ∑ m, ∑ n, A⁻¹ k n * V x n m * A⁻¹ m l * D₀ l / 2 := e1
      _ = ∑ m, ∑ l, ∑ n, A⁻¹ k n * V x n m * A⁻¹ m l * D₀ l / 2 := Finset.sum_comm
      _ = ∑ m, ∑ n, ∑ l, A⁻¹ k n * V x n m * A⁻¹ m l * D₀ l / 2 :=
          Finset.sum_congr rfl fun m _ => Finset.sum_comm
      _ = ∑ n, ∑ m, ∑ l, A⁻¹ k n * V x n m * A⁻¹ m l * D₀ l / 2 := Finset.sum_comm
      _ = _ := e2.symm
  rw [← sub_eq_zero]
  have e1 : ∑ l, (-(A⁻¹ * V x * A⁻¹) k l * D₀ l + A⁻¹ k l * D₁ l) / 2 =
      ∑ l, A⁻¹ k l * D₁ l / 2 - ∑ l, (A⁻¹ * V x * A⁻¹) k l * D₀ l / 2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have e2 : ∑ l, A⁻¹ k l * (D₁ l - 2 * ∑ b, christoffelOf g.coefficient x b i j * V x b l) / 2 =
      ∑ l, A⁻¹ k l * D₁ l / 2 -
        ∑ l, A⁻¹ k l * ∑ b, christoffelOf g.coefficient x b i j * V x b l := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [e1, e2, hT]
  ring

/-- **The Palatini identity.** For a family that equals `g` at `ε = 0` near `x`, the first
variation of the Ricci tensor is `δRic_{jk} = ∇_i δΓ^i_{jk} − ∇_j δΓ^i_{ik}`. -/
theorem familyRicciDeriv_eq_palatini
    {Cp : ℝ × MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {x : MinkowskiModel d} (hx : x ∈ U) (h0 : (fun z => Cp (0, z)) =ᶠ[𝓝 x] g.coefficient)
    (j k : Fin (d + 1)) :
    familyRicciDeriv Cp x j k = g.palatini (familyChristoffelDeriv Cp) x j k := by
  have hΓ0 (a b c : Fin (d + 1)) :
      familyChristoffel Cp (0, x) a b c = christoffelOf g.coefficient x a b c :=
    christoffelOf_congr h0 a b c
  have hsymΓ (a b c : Fin (d + 1)) : christoffelOf g.coefficient x a b c =
      christoffelOf g.coefficient x a c b := g.christoffelOf_coefficient_symm hx a b c
  set P := familyChristoffelDeriv Cp
  unfold familyRicciDeriv palatini covDerivThree
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hΓ0]
  have hb : ∑ a, ((P x i i a * christoffelOf g.coefficient x a j k +
        christoffelOf g.coefficient x i i a * P x a j k) -
      (P x i j a * christoffelOf g.coefficient x a i k +
        christoffelOf g.coefficient x i j a * P x a i k)) =
      ∑ b, (christoffelOf g.coefficient x i i b * P x b j k -
          christoffelOf g.coefficient x b i j * P x i b k -
          christoffelOf g.coefficient x b i k * P x i j b) -
        ∑ b, (christoffelOf g.coefficient x i j b * P x b i k -
          christoffelOf g.coefficient x b j i * P x i b k -
          christoffelOf g.coefficient x b j k * P x i i b) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hsymΓ b j i]
    ring
  rw [hb]
  ring

end Variation

/-! ### The family `g + ε h` -/

section Perturbation

variable {g : CoordinateMetric σ d U} {h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}

/-- The family `g + ε h` is smooth in `(ε, z)` where `h` is smooth. -/
theorem contDiffAt_perturbationFamily (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    {p : ℝ × MinkowskiModel d} (hp : p.2 ∈ U) (i j : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (fun q => g.perturbationFamily h q i j) p := by
  have e : (fun q => g.perturbationFamily h q i j) =
      fun q => g.coefficient q.2 i j + q.1 * h q.2 i j :=
    funext fun q => g.perturbationFamily_apply h q i j
  rw [e]
  have h1 : ContDiffAt ℝ ∞ (fun q : ℝ × MinkowskiModel d => g.coefficient q.2 i j) p :=
    ((g.coefficient_contDiffOn i j).contDiffAt (U.isOpen.mem_nhds hp)).comp p contDiffAt_snd
  have h2 : ContDiffAt ℝ ∞ (fun q : ℝ × MinkowskiModel d => h q.2 i j) p :=
    ((hh i j).contDiffAt (U.isOpen.mem_nhds hp)).comp p contDiffAt_snd
  exact h1.add (contDiffAt_fst.mul h2)

/-- The derivative of `g + ε h` in `ε` is `h`. -/
theorem familyCoeffDeriv_perturbationFamily (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    {z : MinkowskiModel d} (hz : z ∈ U) : familyCoeffDeriv (g.perturbationFamily h) z = h z := by
  ext i j
  have h1 := hasDerivAt_slice ((contDiffAt_perturbationFamily (g := g) hh
    (p := ((0 : ℝ), z)) hz i j).differentiableAt (by simp))
  have h2 : HasDerivAt (fun t => g.perturbationFamily h (t, z) i j) (h z i j) 0 := by
    have e : (fun t => g.perturbationFamily h (t, z) i j) =
        fun t => g.coefficient z i j + t * h z i j :=
      funext fun t => g.perturbationFamily_apply h (t, z) i j
    rw [e]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (h z i j)).const_add (g.coefficient z i j)
  exact h1.unique h2

/-- **The variation of the Christoffel symbols on a curved background** (target of §108): for
the family `g + ε h`, `d/dε Γ^k_{ij}|₀ = ½ g^{kl} (∇_i h_{jl} + ∇_j h_{li} − ∇_l h_{ij})`. -/
theorem familyChristoffelDeriv_eq (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) {z : MinkowskiModel d} (hz : z ∈ U)
    (k i j : Fin (d + 1)) :
    familyChristoffelDeriv (g.perturbationFamily h) z k i j = g.curvedChristoffel h z k i j := by
  have hev : familyCoeffDeriv (g.perturbationFamily h) =ᶠ[𝓝 z] h :=
    Filter.eventually_of_mem (U.isOpen.mem_nhds hz) fun y hy =>
      familyCoeffDeriv_perturbationFamily hh hy
  rw [familyChristoffelDeriv_eq_of_family hz (fun a b => contDiffAt_perturbationFamily hh hz a b)
    (.of_eq (perturbationFamily_zero g h)) (fun a b => by
      rw [familyCoeffDeriv_perturbationFamily hh hz]; exact hs z hz a b),
    curvedChristoffel_congr hev]

/-- **The Palatini form of the variation of the Ricci tensor** (target of §108): for the family
`g + ε h`, `d/dε Ric_{jk}|₀ = ∇_i δΓ^i_{jk} − ∇_j δΓ^i_{ik}`. -/
theorem familyRicciDeriv_eq (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) {x : MinkowskiModel d} (hx : x ∈ U)
    (j k : Fin (d + 1)) :
    familyRicciDeriv (g.perturbationFamily h) x j k = g.palatini (g.curvedChristoffel h) x j k := by
  rw [familyRicciDeriv_eq_palatini hx (.of_eq (perturbationFamily_zero g h))]
  exact palatini_congr (Filter.eventually_of_mem (U.isOpen.mem_nhds hx) fun z hz =>
    funext fun k => funext fun i => funext fun j => familyChristoffelDeriv_eq hh hs hz k i j) j k

/-- **The derivative theorem on a curved background.** The derivative in `ε` at `0` of the Ricci
tensor of `g + ε h` is the Palatini form of `δΓ`. -/
theorem hasDerivAt_ricciOf_perturbation (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) {x : MinkowskiModel d} (hx : x ∈ U)
    (j k : Fin (d + 1)) :
    HasDerivAt (fun ε : ℝ => ricciOf (fun z => g.coefficient z + ε • h z) x j k)
      (g.palatini (g.curvedChristoffel h) x j k) 0 := by
  have hdet : (g.perturbationFamily h (0, x)).det ≠ 0 := by
    simpa [perturbationFamily] using g.coefficient_det_ne_zero ⟨x, hx⟩
  have hΓ (a b c : Fin (d + 1)) : ContDiffAt ℝ ∞
      (fun q => familyChristoffel (g.perturbationFamily h) q a b c) ((0 : ℝ), x) :=
    contDiffAt_familyChristoffel (fun a b => contDiffAt_perturbationFamily hh hx a b) hdet a b c
  rw [← familyRicciDeriv_eq hh hs hx]
  exact hasDerivAt_familyRicci hΓ j k

/-! ### Smoothness and the Leibniz rules -/

theorem contDiffOn_partial {f : MinkowskiModel d → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (v : MinkowskiModel d) : ContDiffOn ℝ ∞ (fun z => fderiv ℝ f z v) U :=
  (hf.fderiv_of_isOpen U.isOpen (by simp)).clm_apply contDiffOn_const

theorem contDiffOn_covDerivTwo (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (a i j : Fin (d + 1)) : ContDiffOn ℝ ∞ (fun z => g.covDerivTwo h z a i j) U := by
  unfold covDerivTwo
  refine (contDiffOn_partial (hh i j) _).sub (ContDiffOn.sum fun b _ => ?_)
  exact ((g.contDiffOn_christoffelOf b a i).mul (hh b j)).add
    ((g.contDiffOn_christoffelOf b a j).mul (hh i b))

/-- The linearized Christoffel symbols of a smooth `h` are smooth. -/
theorem contDiffOn_curvedChristoffel (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (k i j : Fin (d + 1)) : ContDiffOn ℝ ∞ (fun z => g.curvedChristoffel h z k i j) U := by
  unfold curvedChristoffel
  refine ContDiffOn.sum fun l _ => ?_
  exact ((g.contDiffOn_coefficient_inv k l).mul (((contDiffOn_covDerivTwo hh i j l).add
    (contDiffOn_covDerivTwo hh j l i)).sub (contDiffOn_covDerivTwo hh l i j))).div_const 2

end Perturbation

section Leibniz

variable {g : CoordinateMetric σ d U}

variable (g) in
/-- The algebraic part `Q(w, A)^k_{ij} = ½ g^{kl} (w_i A_{jl} + w_j A_{li} − w_l A_{ij})` of the
linearized Christoffel symbols, for a covector `w` and a matrix `A` at the point `x`. -/
def symbolChristoffel (w : Fin (d + 1) → ℝ) (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (k i j : Fin (d + 1)) : ℝ :=
  ∑ l, (g.coefficient x)⁻¹ k l * (w i * A j l + w j * A l i - w l * A i j) / 2

/-- The gradient covector `w_i = ∂_i f` of a function. -/
def gradientCovector (f : MinkowskiModel d → ℝ) (x : MinkowskiModel d) (i : Fin (d + 1)) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

theorem covDerivTwo_smul {f : MinkowskiModel d → ℝ}
    {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}
    (hf : DifferentiableAt ℝ f x) (ha : ∀ p q, DifferentiableAt ℝ (fun z => a z p q) x)
    (m p q : Fin (d + 1)) :
    g.covDerivTwo (fun z => f z • a z) x m p q =
      gradientCovector f x m * a x p q + f x * g.covDerivTwo a x m p q := by
  have hd : fderiv ℝ (fun z => f z * a z p q) x (Pi.single m 1) =
      f x * fderiv ℝ (fun z => a z p q) x (Pi.single m 1) +
        a x p q * fderiv ℝ f x (Pi.single m 1) := by
    rw [fderiv_fun_mul hf (ha p q)]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  unfold covDerivTwo gradientCovector
  simp only [Matrix.smul_apply, smul_eq_mul, hd]
  have hS : ∑ b, (christoffelOf g.coefficient x b m p * (f x * a x b q) +
        christoffelOf g.coefficient x b m q * (f x * a x p b)) =
      f x * ∑ b, (christoffelOf g.coefficient x b m p * a x b q +
        christoffelOf g.coefficient x b m q * a x p b) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hS]
  ring

/-- **The Leibniz rule for `δΓ`**: `δΓ[f a] = f δΓ[a] + Q(df, a)`. -/
theorem curvedChristoffel_smul {f : MinkowskiModel d → ℝ}
    {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}
    (hf : DifferentiableAt ℝ f x) (ha : ∀ p q, DifferentiableAt ℝ (fun z => a z p q) x)
    (k i j : Fin (d + 1)) :
    g.curvedChristoffel (fun z => f z • a z) x k i j =
      f x * g.curvedChristoffel a x k i j +
        g.symbolChristoffel (gradientCovector f x) (a x) x k i j := by
  unfold curvedChristoffel symbolChristoffel
  simp only [covDerivTwo_smul hf ha, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **The Leibniz rule for the Palatini form**:
`∇_i (f P + P')^i_{jk} − ∇_j (f P + P')^i_{ik} = f (∇·P)_{jk} + ∂_i f P^i_{jk} − ∂_j f P^i_{ik}
+ (∇·P')_{jk}`. -/
theorem covDerivThree_smul_add {f : MinkowskiModel d → ℝ}
    {P P' : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ}
    {x : MinkowskiModel d} (hf : DifferentiableAt ℝ f x)
    (hP : ∀ a b c, DifferentiableAt ℝ (fun z => P z a b c) x)
    (hP' : ∀ a b c, DifferentiableAt ℝ (fun z => P' z a b c) x) (a k i j : Fin (d + 1)) :
    g.covDerivThree (fun z => f z • P z + P' z) x a k i j =
      gradientCovector f x a * P x k i j + f x * g.covDerivThree P x a k i j +
        g.covDerivThree P' x a k i j := by
  have hd : fderiv ℝ (fun z => f z * P z k i j + P' z k i j) x (Pi.single a 1) =
      f x * fderiv ℝ (fun z => P z k i j) x (Pi.single a 1) +
        P x k i j * fderiv ℝ f x (Pi.single a 1) +
        fderiv ℝ (fun z => P' z k i j) x (Pi.single a 1) := by
    rw [fderiv_fun_add (hf.fun_mul (hP k i j)) (hP' k i j), fderiv_fun_mul hf (hP k i j)]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  unfold covDerivThree gradientCovector
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hd]
  have hS : ∑ b, (christoffelOf g.coefficient x k a b * (f x * P x b i j + P' x b i j) -
        christoffelOf g.coefficient x b a i * (f x * P x k b j + P' x k b j) -
        christoffelOf g.coefficient x b a j * (f x * P x k i b + P' x k i b)) =
      f x * ∑ b, (christoffelOf g.coefficient x k a b * P x b i j -
        christoffelOf g.coefficient x b a i * P x k b j -
        christoffelOf g.coefficient x b a j * P x k i b) +
      ∑ b, (christoffelOf g.coefficient x k a b * P' x b i j -
        christoffelOf g.coefficient x b a i * P' x k b j -
        christoffelOf g.coefficient x b a j * P' x k i b) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hS]
  ring

/-- **The Leibniz rule for the Palatini form**:
`∇_i (f P + P')^i_{jk} − ∇_j (f P + P')^i_{ik} = f (∇·P)_{jk} + ∂_i f P^i_{jk} − ∂_j f P^i_{ik}
+ (∇·P')_{jk}`. -/
theorem palatini_smul_add {f : MinkowskiModel d → ℝ}
    {P P' : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ}
    {x : MinkowskiModel d} (hf : DifferentiableAt ℝ f x)
    (hP : ∀ a b c, DifferentiableAt ℝ (fun z => P z a b c) x)
    (hP' : ∀ a b c, DifferentiableAt ℝ (fun z => P' z a b c) x) (j k : Fin (d + 1)) :
    g.palatini (fun z => f z • P z + P' z) x j k =
      f x * g.palatini P x j k +
        ∑ i, (gradientCovector f x i * P x i j k - gradientCovector f x j * P x i i k) +
        g.palatini P' x j k := by
  unfold palatini
  simp only [covDerivThree_smul_add hf hP hP']
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem palatini_zero (x : MinkowskiModel d) (j k : Fin (d + 1)) :
    g.palatini (fun _ => 0) x j k = 0 := by
  simp [palatini, covDerivThree]

/-- The Leibniz rule for the Palatini form of `f P`. -/
theorem palatini_smul {f : MinkowskiModel d → ℝ}
    {P : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ}
    {x : MinkowskiModel d} (hf : DifferentiableAt ℝ f x)
    (hP : ∀ a b c, DifferentiableAt ℝ (fun z => P z a b c) x) (j k : Fin (d + 1)) :
    g.palatini (fun z => f z • P z) x j k =
      f x * g.palatini P x j k +
        ∑ i, (gradientCovector f x i * P x i j k - gradientCovector f x j * P x i i k) := by
  have h := palatini_smul_add (g := g) (P' := fun _ => 0) hf hP
    (fun _ _ _ => differentiableAt_const _) j k
  simp only [add_zero] at h
  rw [h, palatini_zero, add_zero]

/-- `Q(w, A)` is linear in the covector. -/
theorem symbolChristoffel_smul (c : ℝ) (w : Fin (d + 1) → ℝ)
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d) (k i j : Fin (d + 1)) :
    g.symbolChristoffel (c • w) A x k i j = c * g.symbolChristoffel w A x k i j := by
  unfold symbolChristoffel
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- The chain rule for the gradient: `∂_i F(ψ) = F'(ψ) ∂_i ψ`. -/
theorem gradientCovector_comp {F : ℝ → ℝ} {ψ : MinkowskiModel d → ℝ} {x : MinkowskiModel d}
    (hF : DifferentiableAt ℝ F (ψ x)) (hψ : DifferentiableAt ℝ ψ x) (i : Fin (d + 1)) :
    gradientCovector (fun z => F (ψ z)) x i = deriv F (ψ x) * gradientCovector ψ x i := by
  unfold gradientCovector
  have h : HasFDerivAt (fun z => F (ψ z)) (deriv F (ψ x) • fderiv ℝ ψ x) x :=
    hF.hasDerivAt.comp_hasFDerivAt x hψ.hasFDerivAt
  rw [h.fderiv]
  rfl

end Leibniz

/-! ### The flat background -/

section Flat

variable {h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}

/-- On the Minkowski background, `g + ε h` is the family `η + ε h` of the flat linearization. -/
theorem perturbationFamily_minkowski :
    (minkowski σ d U).perturbationFamily h = linearFamily σ h := by
  funext p
  simp [perturbationFamily, linearFamily, minkowski_coefficient, Minkowski.metricMatrix]

theorem covDerivTwo_minkowski {z : MinkowskiModel d} (hz : z ∈ U) (a i j : Fin (d + 1)) :
    (minkowski σ d U).covDerivTwo h z a i j = fderiv ℝ (fun y => h y i j) z (Pi.single a 1) := by
  simp [covDerivTwo, minkowski_christoffelOf hz]

/-- On the Minkowski background, `δΓ` is the flat `linearizedChristoffel`. -/
theorem curvedChristoffel_minkowski {z : MinkowskiModel d} (hz : z ∈ U) (k i j : Fin (d + 1)) :
    (minkowski σ d U).curvedChristoffel h z k i j = linearizedChristoffel σ h z k i j := by
  have hc : (minkowski σ d U).coefficient z = Minkowski.metricMatrix σ d := by
    rw [minkowski_coefficient]; rfl
  simp only [curvedChristoffel, linearizedChristoffel, covDerivTwo_minkowski hz, hc,
    metricMatrix_inv]
  rw [← Finset.sum_div]
  simp only [metricMatrix_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem palatini_minkowski {x : MinkowskiModel d} (hx : x ∈ U)
    (P : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ) (j k : Fin (d + 1)) :
    (minkowski σ d U).palatini P x j k = ∑ i,
      (fderiv ℝ (fun z => P z i j k) x (Pi.single i 1) -
        fderiv ℝ (fun z => P z i i k) x (Pi.single j 1)) := by
  simp [palatini, covDerivThree, minkowski_christoffelOf hx]

/-- On the Minkowski background, the Palatini form of `δΓ` is the flat `linearizedRicci` of
`SmoothGeometry/Lorentzian/Linearized.lean`. -/
theorem palatini_curvedChristoffel_minkowski (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) {x : MinkowskiModel d} (hx : x ∈ U)
    (j k : Fin (d + 1)) :
    (minkowski σ d U).palatini ((minkowski σ d U).curvedChristoffel h) x j k =
      linearizedRicci σ h x j k := by
  rw [← familyRicciDeriv_eq hh hs hx, perturbationFamily_minkowski,
    familyRicciDeriv_linearFamily hh hs hx]

end Flat

/-! ### Gauge invariance on a Ricci-flat background -/

section Gauge

variable {g : CoordinateMetric σ d U} {X : MinkowskiModel d → MinkowskiModel d}

/-- **The coordinate Lie derivative of the metric**,
`(L_X g)_{ij} = X^k ∂_k g_{ij} + g_{kj} ∂_i X^k + g_{ik} ∂_j X^k` (`lieOf`), as a field of
coefficient matrices. -/
def coordinateLieMetric (X : MinkowskiModel d → MinkowskiModel d) (g : CoordinateMetric σ d U)
    (z : MinkowskiModel d) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.of fun i j => lieOf g.coefficient X z i j

/-- The derivative `v ↦ v + ε ∂_v X` of the map `z ↦ z + ε X(z)`. -/
def shiftDeriv (X : MinkowskiModel d → MinkowskiModel d) (ε : ℝ) (z : MinkowskiModel d) :
    MinkowskiModel d →L[ℝ] MinkowskiModel d :=
  ContinuousLinearMap.id ℝ (MinkowskiModel d) + ε • fderiv ℝ X z

theorem shiftDeriv_apply (ε : ℝ) (z v : MinkowskiModel d) :
    shiftDeriv X ε z v = v + ε • fderiv ℝ X z v := rfl

variable (g X) in
/-- The pullback of the forms of `g` by `z ↦ z + ε X(z)`:
`(v, w) ↦ g_{z + ε X(z)}(v + ε ∂_v X, w + ε ∂_w X)`. -/
def pullbackForm (ε : ℝ) (z : MinkowskiModel d) :
    MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ (MinkowskiModel d) (MinkowskiModel d) ℝ).flip
    (shiftDeriv X ε z)).comp ((g.form (z + ε • X z)).comp (shiftDeriv X ε z))

theorem pullbackForm_apply (ε : ℝ) (z v w : MinkowskiModel d) :
    pullbackForm g X ε z v w =
      g.form (z + ε • X z) (shiftDeriv X ε z v) (shiftDeriv X ε z w) := rfl

variable (g X) in
/-- The coefficients `g_{ab}(z + ε X) (δ^a_i + ε ∂_i X^a)(δ^b_j + ε ∂_j X^b)` of the pullback of
`g` by `z ↦ z + ε X(z)`, as a function of `(ε, z)`. -/
def pullbackFamily (p : ℝ × MinkowskiModel d) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.of fun i j => pullbackForm g X p.1 p.2 (Pi.single i 1) (Pi.single j 1)

theorem pullbackFamily_zero : (fun z => pullbackFamily g X (0, z)) = g.coefficient := by
  funext z
  ext i j
  simp [pullbackFamily, pullbackForm_apply, shiftDeriv_apply, coefficient]

theorem contDiffOn_shiftDeriv (hX : ContDiffOn ℝ ∞ X U) (ε : ℝ) :
    ContDiffOn ℝ ∞ (shiftDeriv X ε) U :=
  contDiffOn_const.add ((hX.fderiv_of_isOpen (m := ∞) U.isOpen (by simp)).const_smul ε)

theorem contDiffAt_pullbackFamily (hX : ContDiffOn ℝ ∞ X U) {z : MinkowskiModel d} (hz : z ∈ U)
    (i j : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (fun q => pullbackFamily g X q i j) ((0 : ℝ), z) := by
  have hXz : ContDiffAt ℝ ∞ X z := hX.contDiffAt (U.isOpen.mem_nhds hz)
  have hDX : ContDiffAt ℝ ∞ (fderiv ℝ X) z :=
    (hX.fderiv_of_isOpen U.isOpen (by simp)).contDiffAt (U.isOpen.mem_nhds hz)
  have hΨ : ContDiffAt ℝ ∞ (fun q : ℝ × MinkowskiModel d => q.2 + q.1 • X q.2) ((0 : ℝ), z) :=
    contDiffAt_snd.add (contDiffAt_fst.smul (hXz.comp _ contDiffAt_snd))
  have hB : ContDiffAt ℝ ∞ (fun q : ℝ × MinkowskiModel d => g.form (q.2 + q.1 • X q.2))
      ((0 : ℝ), z) := by
    have hg : ContDiffAt ℝ ∞ g.form
        ((((0 : ℝ), z) : ℝ × MinkowskiModel d).2 +
          (((0 : ℝ), z) : ℝ × MinkowskiModel d).1 • X (((0 : ℝ), z) : ℝ × MinkowskiModel d).2) := by
      simpa using g.smooth.contDiffAt (U.isOpen.mem_nhds hz)
    exact ContDiffAt.comp (f := fun q : ℝ × MinkowskiModel d => q.2 + q.1 • X q.2) _ hg hΨ
  have hL (v : MinkowskiModel d) : ContDiffAt ℝ ∞
      (fun q : ℝ × MinkowskiModel d => shiftDeriv X q.1 q.2 v) ((0 : ℝ), z) := by
    simp only [shiftDeriv_apply]
    exact contDiffAt_const.add (contDiffAt_fst.smul
      ((hDX.comp _ contDiffAt_snd).clm_apply contDiffAt_const))
  exact (hB.clm_apply (hL _)).clm_apply (hL _)

/-- A component of the derivative of a map is the derivative of the component. -/
theorem fderiv_component {Y : MinkowskiModel d → MinkowskiModel d} {z : MinkowskiModel d}
    (hY : DifferentiableAt ℝ Y z) (k : Fin (d + 1)) (v : MinkowskiModel d) :
    fderiv ℝ (fun y => Y y k) z v = fderiv ℝ Y z v k := by
  have hk : fderiv ℝ (fun y => Y y k) z =
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) k).comp
        (fderiv ℝ Y z) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) k).hasFDerivAt.comp
      z hY.hasFDerivAt).fderiv
  rw [hk]
  rfl

/-- The coefficients of the pullback family as a double sum. -/
theorem pullbackFamily_apply (p : ℝ × MinkowskiModel d) (i j : Fin (d + 1)) :
    pullbackFamily g X p i j = ∑ a, ∑ b, g.coefficient (p.2 + p.1 • X p.2) a b *
      ((Pi.single i 1 : MinkowskiModel d) a + p.1 * fderiv ℝ X p.2 (Pi.single i 1) a) *
      ((Pi.single j 1 : MinkowskiModel d) b + p.1 * fderiv ℝ X p.2 (Pi.single j 1) b) := by
  change g.form _ _ _ = _
  rw [g.form_apply]
  rfl

/-- **The derivative of the pullback is the Lie derivative**: `d/dε (φ_ε^* g)|₀ = L_X g` for
`φ_ε(z) = z + ε X(z)`. -/
theorem familyCoeffDeriv_pullbackFamily (hX : ContDiffOn ℝ ∞ X U) {z : MinkowskiModel d}
    (hz : z ∈ U) : familyCoeffDeriv (pullbackFamily g X) z = coordinateLieMetric X g z := by
  ext i j
  have h1 := hasDerivAt_slice ((contDiffAt_pullbackFamily (g := g) hX hz i j).differentiableAt
    (by simp))
  have hXd : DifferentiableAt ℝ X z :=
    (hX.contDiffAt (U.isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hpath : HasDerivAt (fun t : ℝ => z + t • X z) (X z) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (X z)).const_add z
  have hC (a b : Fin (d + 1)) : HasDerivAt (fun t : ℝ => g.coefficient (z + t • X z) a b)
      (fderiv ℝ (fun y => g.coefficient y a b) z (X z)) 0 := by
    have hd : HasFDerivAt (fun y => g.coefficient y a b)
        (fderiv ℝ (fun y => g.coefficient y a b) z) z :=
      (((g.coefficient_contDiffOn a b).contDiffAt (U.isOpen.mem_nhds hz)).differentiableAt
        (by simp)).hasFDerivAt
    have h := hd.comp_hasDerivAt_of_eq (0 : ℝ) hpath (by simp)
    exact h
  have hL (c : Fin (d + 1)) (a : Fin (d + 1)) : HasDerivAt
      (fun t : ℝ => (Pi.single c 1 : MinkowskiModel d) a + t * fderiv ℝ X z (Pi.single c 1) a)
      (fderiv ℝ X z (Pi.single c 1) a) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (fderiv ℝ X z (Pi.single c 1) a)).const_add
      ((Pi.single c 1 : MinkowskiModel d) a)
  have h2 := HasDerivAt.fun_sum (u := Finset.univ) fun a _ => HasDerivAt.fun_sum
    (u := Finset.univ) fun b _ => ((hC a b).fun_mul (hL i a)).fun_mul (hL j b)
  have hfun : (fun t => pullbackFamily g X (t, z) i j) = fun t =>
      ∑ a, ∑ b, g.coefficient (z + t • X z) a b *
        ((Pi.single i 1 : MinkowskiModel d) a + t * fderiv ℝ X z (Pi.single i 1) a) *
        ((Pi.single j 1 : MinkowskiModel d) b + t * fderiv ℝ X z (Pi.single j 1) b) :=
    funext fun t => pullbackFamily_apply (t, z) i j
  rw [← hfun] at h2
  change fderiv ℝ (fun q => pullbackFamily g X q i j) ((0 : ℝ), z) (1, 0) =
    lieOf g.coefficient X z i j
  rw [h1.unique h2, lieOf]
  simp only [zero_smul, add_zero, zero_mul, Finset.sum_add_distrib, Pi.single_apply, mul_ite,
    ite_mul, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    fderiv_component hXd]
  congr 1
  rw [Finset.sum_comm]
  simp

theorem coordinateLieMetric_symm {z : MinkowskiModel d} (hz : z ∈ U) (i j : Fin (d + 1)) :
    coordinateLieMetric X g z i j = coordinateLieMetric X g z j i := by
  simp only [coordinateLieMetric, Matrix.of_apply, lieOf]
  have hd : fderiv ℝ (fun y => g.coefficient y i j) z = fderiv ℝ (fun y => g.coefficient y j i) z :=
    Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (U.isOpen.mem_nhds hz)
      fun y hy => g.coefficient_symmetric hy i j)
  have h1 : ∑ k, g.coefficient z k j * fderiv ℝ (fun y => X y k) z (Pi.single i 1) =
      ∑ k, g.coefficient z j k * fderiv ℝ (fun y => X y k) z (Pi.single i 1) :=
    Finset.sum_congr rfl fun k _ => by rw [g.coefficient_symmetric hz k j]
  have h2 : ∑ k, g.coefficient z i k * fderiv ℝ (fun y => X y k) z (Pi.single j 1) =
      ∑ k, g.coefficient z k i * fderiv ℝ (fun y => X y k) z (Pi.single j 1) :=
    Finset.sum_congr rfl fun k _ => by rw [g.coefficient_symmetric hz i k]
  rw [hd, h1, h2]
  ring

theorem contDiffOn_coordinateLieMetric (hX : ContDiffOn ℝ ∞ X U) (i j : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => coordinateLieMetric X g z i j) U := by
  simp only [coordinateLieMetric, Matrix.of_apply, lieOf]
  have hD (a b : Fin (d + 1)) : ContDiffOn ℝ ∞ (fderiv ℝ (fun y => g.coefficient y a b)) U :=
    (g.coefficient_contDiffOn a b).fderiv_of_isOpen U.isOpen (by simp)
  have hXk (k : Fin (d + 1)) : ContDiffOn ℝ ∞ (fun y => X y k) U := contDiffOn_pi.1 hX k
  exact (((hD i j).clm_apply hX).add (ContDiffOn.sum fun k _ =>
    (g.coefficient_contDiffOn k j).mul (contDiffOn_partial (hXk k) _))).add
    (ContDiffOn.sum fun k _ => (g.coefficient_contDiffOn i k).mul (contDiffOn_partial (hXk k) _))

/-! #### The pullback metric -/

variable (X) in
/-- The open set where `z ↦ z + ε X(z)` stays in `U` and has an invertible derivative. -/
def pullbackDomain (hX : ContDiffOn ℝ ∞ X U) (ε : ℝ) : Opens (MinkowskiModel d) where
  carrier := ((U : Set (MinkowskiModel d)) ∩ (fun z => z + ε • X z) ⁻¹' U) ∩
    shiftDeriv X ε ⁻¹' range ContinuousLinearEquiv.toContinuousLinearMap
  is_open' := by
    have hφ : ContinuousOn (fun z => z + ε • X z) U :=
      (contDiffOn_id.add (ContDiffOn.const_smul ε hX)).continuousOn
    have h1 : IsOpen ((U : Set (MinkowskiModel d)) ∩ (fun z => z + ε • X z) ⁻¹' U) :=
      hφ.isOpen_inter_preimage U.isOpen U.isOpen
    exact ((contDiffOn_shiftDeriv hX ε).continuousOn.mono inter_subset_left).isOpen_inter_preimage
      h1 ContinuousLinearEquiv.isOpen

theorem mem_pullbackDomain {hX : ContDiffOn ℝ ∞ X U} {ε : ℝ} {z : MinkowskiModel d} :
    z ∈ pullbackDomain X hX ε ↔ (z ∈ U ∧ z + ε • X z ∈ U) ∧ (shiftDeriv X ε z).IsInvertible :=
  Iff.rfl

variable (g) in
/-- The pullback of `g` by `z ↦ z + ε X(z)`, a coordinate metric on `pullbackDomain`. -/
def pullbackMetric (hX : ContDiffOn ℝ ∞ X U) (ε : ℝ) :
    CoordinateMetric σ d (pullbackDomain X hX ε) where
  form := pullbackForm g X ε
  smooth := by
    refine contDiffOn_clm_apply.2 fun v => contDiffOn_clm_apply.2 fun w => ?_
    intro z hz
    obtain ⟨⟨hzU, hφ⟩, -⟩ := mem_pullbackDomain.mp hz
    refine ContDiffAt.contDiffWithinAt ?_
    have hXz := hX.contDiffAt (U.isOpen.mem_nhds hzU)
    have hDX : ContDiffAt ℝ ∞ (fderiv ℝ X) z :=
      (hX.fderiv_of_isOpen (m := ∞) U.isOpen (by simp)).contDiffAt (U.isOpen.mem_nhds hzU)
    have hB : ContDiffAt ℝ ∞ (fun y => g.form (y + ε • X y)) z :=
      ContDiffAt.comp (f := fun y => y + ε • X y) z (g.smooth.contDiffAt (U.isOpen.mem_nhds hφ))
        (contDiffAt_id.add (hXz.const_smul ε))
    have hL (u : MinkowskiModel d) : ContDiffAt ℝ ∞ (fun y => shiftDeriv X ε y u) z := by
      simp only [shiftDeriv_apply]
      exact contDiffAt_const.add ((hDX.clm_apply contDiffAt_const).const_smul ε)
    exact (hB.clm_apply (hL v)).clm_apply (hL w)
  signature := by
    intro z hz
    obtain ⟨⟨-, hφ⟩, e, he⟩ := mem_pullbackDomain.mp hz
    obtain ⟨j, hj⟩ := g.signature _ hφ
    refine ⟨e.trans j, fun v w => ?_⟩
    have hv (u : MinkowskiModel d) : shiftDeriv X ε z u = e u := by rw [← he]; rfl
    rw [pullbackForm_apply, hj, hv, hv]
    rfl

theorem pullbackMetric_coefficient (hX : ContDiffOn ℝ ∞ X U) (ε : ℝ) :
    (pullbackMetric g hX ε).coefficient = fun z => pullbackFamily g X (ε, z) := rfl

variable (X) in
/-- The map `z ↦ z + ε X(z)` from `pullbackDomain` into `U`. -/
def pullbackMap (hX : ContDiffOn ℝ ∞ X U) (ε : ℝ) (z : pullbackDomain X hX ε) : U :=
  ⟨(z : MinkowskiModel d) + ε • X z, (mem_pullbackDomain.mp z.2).1.2⟩

theorem contMDiff_pullbackMap (hX : ContDiffOn ℝ ∞ X U) (ε : ℝ) :
    ContMDiff 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) ∞ (pullbackMap X hX ε) := by
  apply (ContMDiff.subtypeVal_comp_iff U _).mp
  have hφ : ContDiffOn ℝ ∞ (fun z => z + ε • X z) U := contDiffOn_id.add (hX.const_smul ε)
  exact (hφ.mono fun z hz => (mem_pullbackDomain.mp hz).1.1).contMDiffOn.comp_contMDiff
    (contMDiff_subtype_val (U := pullbackDomain X hX ε)) (fun z => z.property)

theorem mfderiv_pullbackMap (hX : ContDiffOn ℝ ∞ X U) (ε : ℝ) (z : pullbackDomain X hX ε)
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) z) :
    (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) (pullbackMap X hX ε) z v :
      MinkowskiModel d) = shiftDeriv X ε z v := by
  have hzU : (z : MinkowskiModel d) ∈ U := (mem_pullbackDomain.mp z.2).1.1
  have hF := contMDiff_pullbackMap hX ε
  have h₁ := congrArg (fun L => L v) (mfderiv_comp z
    ((contMDiff_subtype_val (U := U) (n := ∞)).mdifferentiableAt (by simp))
    ((hF z).mdifferentiableAt (by simp)))
  change mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d)
      (Subtype.val ∘ pullbackMap X hX ε) z v =
    mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) Subtype.val (pullbackMap X hX ε z)
      (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) (pullbackMap X hX ε) z v) at h₁
  rw [Manifold.mfderiv_subtype_val_apply] at h₁
  rw [← h₁]
  have hXd : DifferentiableAt ℝ X z :=
    (hX.contDiffAt (U.isOpen.mem_nhds hzU)).differentiableAt (by simp)
  have hφ : HasFDerivAt (fun y : MinkowskiModel d => y + ε • X y) (shiftDeriv X ε z) z :=
    (hasFDerivAt_id (z : MinkowskiModel d)).add (hXd.hasFDerivAt.const_smul ε)
  have hcomp : (Subtype.val ∘ pullbackMap X hX ε) =
      (fun y : MinkowskiModel d => y + ε • X y) ∘ (Subtype.val : pullbackDomain X hX ε → _) :=
    rfl
  rw [hcomp, mfderiv_comp z hφ.differentiableAt.mdifferentiableAt
    ((contMDiff_subtype_val (U := pullbackDomain X hX ε) (n := ∞)).mdifferentiableAt (by simp))]
  rw [ContinuousLinearMap.comp_apply, Manifold.mfderiv_subtype_val_apply, mfderiv_eq_fderiv,
    hφ.fderiv]
  rfl

/-- The native Ricci tensor vanishes at a point where the Ricci tensor of the coefficients
vanishes. -/
theorem ricci_eq_zero_of_ricciOf {y : U} (hRic : ∀ i j, ricciOf g.coefficient y i j = 0)
    (u v : MinkowskiModel d) : g.toLorentzMetric.ricci y u v = 0 := by
  have hb (j k : Fin (d + 1)) :
      g.toLorentzMetric.ricci y (Pi.single j 1) (Pi.single k 1) = 0 := by
    have h := g.toLorentzMetric_ricci_chartField y y j k
    rw [physicalChart_chartField, physicalChart_chartField] at h
    rw [h, hRic]
  let R : MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ := g.toLorentzMetric.ricci y
  have hR (j k : Fin (d + 1)) : R (Pi.single j 1) (Pi.single k 1) = 0 := hb j k
  change R u v = 0
  rw [pi_eq_sum_univ' u, pi_eq_sum_univ' v]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, hR, smul_zero,
    Finset.sum_const_zero]

/-- **The pullback of a Ricci-flat metric is Ricci flat**, from the naturality of the native
curvature under the map `z ↦ z + ε X(z)`. -/
theorem ricciOf_pullbackFamily (hRic : ∀ z ∈ U, ∀ i j, ricciOf g.coefficient z i j = 0)
    (hX : ContDiffOn ℝ ∞ X U) {ε : ℝ} {x : MinkowskiModel d} (hx : x ∈ pullbackDomain X hX ε)
    (j k : Fin (d + 1)) : ricciOf (fun z => pullbackFamily g X (ε, z)) x j k = 0 := by
  set M := pullbackMetric g hX ε
  let x' : pullbackDomain X hX ε := ⟨x, hx⟩
  rw [← pullbackMetric_coefficient hX ε]
  change ricciOf M.coefficient x' j k = 0
  rw [← M.toLorentzMetric_ricci_chartField x' x' j k]
  have hF := contMDiff_pullbackMap hX ε
  have hinv : ∀ y, (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d)
      (pullbackMap X hX ε) y).IsInvertible := by
    intro y
    obtain ⟨-, e, he⟩ := mem_pullbackDomain.mp y.2
    refine ⟨e, ?_⟩
    ext1 v
    have := mfderiv_pullbackMap hX ε y v
    rw [← he] at this
    exact this.symm
  have hmetric : ∀ y v w, M.toLorentzMetric.form y v w =
      g.toLorentzMetric.form (pullbackMap X hX ε y)
        (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) (pullbackMap X hX ε) y v)
        (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) (pullbackMap X hX ε) y w) := by
    intro y v w
    have h1 := mfderiv_pullbackMap hX ε y v
    have h2 := mfderiv_pullbackMap hX ε y w
    change g.form _ (shiftDeriv X ε y v) (shiftDeriv X ε y w) = g.form _ _ _
    rw [← h1, ← h2]
    rfl
  obtain ⟨e, he⟩ := hinv x'
  have hR : ∀ u v w, e (M.toLorentzMetric.curvature x' u v w) =
      g.toLorentzMetric.curvature (pullbackMap X hX ε x') (e u) (e v) (e w) := by
    intro u v w
    have h := M.toLorentzMetric.curvature_naturality g.toLorentzMetric hF hinv hmetric x' u v w
    rw [← he] at h
    exact h
  rw [M.toLorentzMetric.ricci_naturality g.toLorentzMetric x' _ e hR]
  exact ricci_eq_zero_of_ricciOf (hRic _ (pullbackMap X hX ε x').2) _ _

/-- On a Ricci-flat background the first variation of the Ricci tensor along the pullback family
vanishes. -/
theorem familyRicciDeriv_pullbackFamily (hRic : ∀ z ∈ U, ∀ i j, ricciOf g.coefficient z i j = 0)
    (hX : ContDiffOn ℝ ∞ X U) {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    familyRicciDeriv (pullbackFamily g X) x j k = 0 := by
  have hdet : (pullbackFamily g X (0, x)).det ≠ 0 := by
    rw [show pullbackFamily g X (0, x) = g.coefficient x from congrFun pullbackFamily_zero x]
    exact g.coefficient_det_ne_zero ⟨x, hx⟩
  have hΓ (a b c : Fin (d + 1)) := contDiffAt_familyChristoffel
    (fun a b => contDiffAt_pullbackFamily (g := g) hX hx a b) hdet a b c
  have hderiv := hasDerivAt_familyRicci hΓ j k
  have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), x + ε • X x ∈ U := by
    have hc : Continuous (fun ε : ℝ => x + ε • X x) :=
      continuous_const.add (continuous_id.smul continuous_const)
    exact hc.continuousAt.eventually_mem (by simpa using U.isOpen.mem_nhds hx)
  have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ),
      shiftDeriv X ε x ∈ range ContinuousLinearEquiv.toContinuousLinearMap := by
    have hc : Continuous (fun ε : ℝ => shiftDeriv X ε x) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have h0 : shiftDeriv X 0 x ∈ range ContinuousLinearEquiv.toContinuousLinearMap :=
      ⟨ContinuousLinearEquiv.refl ℝ (MinkowskiModel d), by
        ext1 v
        simp [shiftDeriv_apply]⟩
    exact hc.continuousAt.eventually_mem (ContinuousLinearEquiv.isOpen.mem_nhds h0)
  have hev : (fun ε => familyRicci (pullbackFamily g X) (ε, x) j k) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [h1, h2] with ε h1 h2
    exact ricciOf_pullbackFamily hRic hX (x := x) (mem_pullbackDomain.mpr ⟨⟨hx, h1⟩, h2⟩) j k
  exact hderiv.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev)

/-- **Gauge invariance on a Ricci-flat background** (target of §108): if `Ric(g) = 0` on `U`,
the variation `h = L_X g` changes the Ricci tensor only at second order, `δRic[L_X g] = 0`. The
proof compares `g + ε L_X g` with the pullback of `g` by `z ↦ z + ε X(z)`: the two families
have the same derivative at `ε = 0`, and the pullback is Ricci flat by naturality. -/
theorem familyRicciDeriv_lie_eq_zero (hRic : ∀ z ∈ U, ∀ i j, ricciOf g.coefficient z i j = 0)
    (hX : ContDiffOn ℝ ∞ X U) {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    familyRicciDeriv (g.perturbationFamily (coordinateLieMetric X g)) x j k = 0 := by
  have hh := contDiffOn_coordinateLieMetric (g := g) hX
  have hs : ∀ z ∈ U, ∀ i j, coordinateLieMetric X g z i j = coordinateLieMetric X g z j i :=
    fun z hz i j => coordinateLieMetric_symm hz i j
  have hpb (z : MinkowskiModel d) (hz : z ∈ U) (a b c : Fin (d + 1)) :
      familyChristoffelDeriv (pullbackFamily g X) z a b c =
        g.curvedChristoffel (coordinateLieMetric X g) z a b c := by
    have hev : familyCoeffDeriv (pullbackFamily g X) =ᶠ[𝓝 z] coordinateLieMetric X g :=
      Filter.eventually_of_mem (U.isOpen.mem_nhds hz) fun y hy =>
        familyCoeffDeriv_pullbackFamily hX hy
    rw [familyChristoffelDeriv_eq_of_family hz (fun a b => contDiffAt_pullbackFamily hX hz a b)
      (.of_eq pullbackFamily_zero) (fun a b => by
        rw [familyCoeffDeriv_pullbackFamily hX hz]; exact hs z hz a b),
      curvedChristoffel_congr hev]
  rw [familyRicciDeriv_eq hh hs hx, ← familyRicciDeriv_pullbackFamily hRic hX hx j k,
    familyRicciDeriv_eq_palatini hx (.of_eq pullbackFamily_zero)]
  exact palatini_congr (Filter.eventually_of_mem (U.isOpen.mem_nhds hx) fun z hz =>
    funext fun a => funext fun b => funext fun c => (hpb z hz a b c).symm) j k

/-- The same statement in Palatini form: `∇_i δΓ^i_{jk}[L_X g] − ∇_j δΓ^i_{ik}[L_X g] = 0`. -/
theorem palatini_curvedChristoffel_lie_eq_zero
    (hRic : ∀ z ∈ U, ∀ i j, ricciOf g.coefficient z i j = 0)
    (hX : ContDiffOn ℝ ∞ X U) {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    g.palatini (g.curvedChristoffel (coordinateLieMetric X g)) x j k = 0 := by
  rw [← familyRicciDeriv_eq (contDiffOn_coordinateLieMetric hX)
    (fun z hz i j => coordinateLieMetric_symm hz i j) hx]
  exact familyRicciDeriv_lie_eq_zero hRic hX hx j k

end Gauge

/-! ### Linearity and the gauge freedom -/

section Linear

variable {g : CoordinateMetric σ d U}

theorem covDerivTwo_add {h h' : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {x : MinkowskiModel d} (hh : ∀ p q, DifferentiableAt ℝ (fun z => h z p q) x)
    (hh' : ∀ p q, DifferentiableAt ℝ (fun z => h' z p q) x) (a i j : Fin (d + 1)) :
    g.covDerivTwo (fun z => h z + h' z) x a i j =
      g.covDerivTwo h x a i j + g.covDerivTwo h' x a i j := by
  have hd : fderiv ℝ (fun z => h z i j + h' z i j) x (Pi.single a 1) =
      fderiv ℝ (fun z => h z i j) x (Pi.single a 1) +
        fderiv ℝ (fun z => h' z i j) x (Pi.single a 1) := by
    rw [fderiv_fun_add (hh i j) (hh' i j), _root_.add_apply]
  unfold covDerivTwo
  simp only [Matrix.add_apply, hd, mul_add, Finset.sum_add_distrib]
  ring

theorem curvedChristoffel_add {h h' : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {x : MinkowskiModel d} (hh : ∀ p q, DifferentiableAt ℝ (fun z => h z p q) x)
    (hh' : ∀ p q, DifferentiableAt ℝ (fun z => h' z p q) x) (k i j : Fin (d + 1)) :
    g.curvedChristoffel (fun z => h z + h' z) x k i j =
      g.curvedChristoffel h x k i j + g.curvedChristoffel h' x k i j := by
  unfold curvedChristoffel
  simp only [covDerivTwo_add hh hh']
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem covDerivThree_add
    {P P' : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ}
    {x : MinkowskiModel d} (hP : ∀ a b c, DifferentiableAt ℝ (fun z => P z a b c) x)
    (hP' : ∀ a b c, DifferentiableAt ℝ (fun z => P' z a b c) x) (a k i j : Fin (d + 1)) :
    g.covDerivThree (fun z => P z + P' z) x a k i j =
      g.covDerivThree P x a k i j + g.covDerivThree P' x a k i j := by
  have hd : fderiv ℝ (fun z => P z k i j + P' z k i j) x (Pi.single a 1) =
      fderiv ℝ (fun z => P z k i j) x (Pi.single a 1) +
        fderiv ℝ (fun z => P' z k i j) x (Pi.single a 1) := by
    rw [fderiv_fun_add (hP k i j) (hP' k i j), _root_.add_apply]
  unfold covDerivThree
  simp only [Pi.add_apply, hd, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

theorem palatini_add {P P' : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ}
    {x : MinkowskiModel d} (hP : ∀ a b c, DifferentiableAt ℝ (fun z => P z a b c) x)
    (hP' : ∀ a b c, DifferentiableAt ℝ (fun z => P' z a b c) x) (j k : Fin (d + 1)) :
    g.palatini (fun z => P z + P' z) x j k = g.palatini P x j k + g.palatini P' x j k := by
  unfold palatini
  simp only [covDerivThree_add hP hP']
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Gauge invariance of the linearized Ricci tensor on a Ricci-flat background**:
`δRic[h + L_X g] = δRic[h]`. -/
theorem familyRicciDeriv_add_lie {X : MinkowskiModel d → MinkowskiModel d}
    {h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hRic : ∀ z ∈ U, ∀ i j, ricciOf g.coefficient z i j = 0) (hX : ContDiffOn ℝ ∞ X U)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    familyRicciDeriv (g.perturbationFamily (fun z => h z + coordinateLieMetric X g z)) x j k =
      familyRicciDeriv (g.perturbationFamily h) x j k := by
  have hL := contDiffOn_coordinateLieMetric (g := g) hX
  have hLs : ∀ z ∈ U, ∀ i j, coordinateLieMetric X g z i j = coordinateLieMetric X g z j i :=
    fun z hz i j => coordinateLieMetric_symm hz i j
  have hS : ∀ i j, ContDiffOn ℝ ∞ (fun z => (h z + coordinateLieMetric X g z) i j) U :=
    fun i j => (hh i j).add (hL i j)
  have hSs : ∀ z ∈ U, ∀ i j, (h z + coordinateLieMetric X g z) i j =
      (h z + coordinateLieMetric X g z) j i := fun z hz i j => by
    simp only [Matrix.add_apply, hs z hz i j, hLs z hz i j]
  have hdiff {F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
      (hF : ∀ i j, ContDiffOn ℝ ∞ (fun z => F z i j) U) {z : MinkowskiModel d} (hz : z ∈ U)
      (p q : Fin (d + 1)) : DifferentiableAt ℝ (fun y => F y p q) z :=
    ((hF p q).contDiffAt (U.isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hdΓ {F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
      (hF : ∀ i j, ContDiffOn ℝ ∞ (fun z => F z i j) U) (a b c : Fin (d + 1)) :
      DifferentiableAt ℝ (fun y => g.curvedChristoffel F y a b c) x :=
    ((contDiffOn_curvedChristoffel hF a b c).contDiffAt (U.isOpen.mem_nhds hx)).differentiableAt
      (by simp)
  have hP : g.curvedChristoffel (fun z => h z + coordinateLieMetric X g z) =ᶠ[𝓝 x]
      fun z => g.curvedChristoffel h z + g.curvedChristoffel (coordinateLieMetric X g) z :=
    Filter.eventually_of_mem (U.isOpen.mem_nhds hx) fun z hz => funext fun a => funext fun b =>
      funext fun c => curvedChristoffel_add (hdiff hh hz) (hdiff hL hz) a b c
  rw [familyRicciDeriv_eq hS hSs hx, familyRicciDeriv_eq hh hs hx, palatini_congr hP,
    palatini_add (hdΓ hh) (hdΓ hL), palatini_curvedChristoffel_lie_eq_zero hRic hX hx, add_zero]

/-- The flat instance of gauge invariance: the Minkowski coefficients are Ricci flat, so
`δRic[L_X η] = 0` for every field `X` smooth on `U`. -/
theorem familyRicciDeriv_lie_minkowski {X : MinkowskiModel d → MinkowskiModel d}
    (hX : ContDiffOn ℝ ∞ X U) {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    familyRicciDeriv ((minkowski σ d U).perturbationFamily
      (coordinateLieMetric X (minkowski σ d U))) x j k = 0 :=
  familyRicciDeriv_lie_eq_zero (fun _ hz i j => minkowski_ricciOf hz i j) hX hx j k

end Linear

/-! ### The rays of a null phase -/

section Rays

variable {g : CoordinateMetric σ d U} {ψ : MinkowskiModel d → ℝ}

variable (g) in
/-- The raised gradient `k^i = g^{ij} ∂_j ψ` of a phase `ψ`. -/
def gradientField (ψ : MinkowskiModel d → ℝ) (z : MinkowskiModel d) : MinkowskiModel d :=
  fun i => ∑ j, (g.coefficient z)⁻¹ i j * gradientCovector ψ z j

variable (g) in
/-- The squared norm `g(dψ, dψ) = g^{ij} ∂_i ψ ∂_j ψ` of the gradient of a phase. -/
def gradientNorm (ψ : MinkowskiModel d → ℝ) (z : MinkowskiModel d) : ℝ :=
  ∑ i, ∑ j, (g.coefficient z)⁻¹ i j * gradientCovector ψ z i * gradientCovector ψ z j

theorem contDiffOn_gradientCovector (hψ : ContDiffOn ℝ ∞ ψ U) (i : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => gradientCovector ψ z i) U :=
  contDiffOn_partial hψ _

theorem contDiffOn_gradientField (hψ : ContDiffOn ℝ ∞ ψ U) :
    ContDiffOn ℝ ∞ (g.gradientField ψ) U :=
  contDiffOn_pi.2 fun i => ContDiffOn.sum fun j _ =>
    (g.contDiffOn_coefficient_inv i j).mul (contDiffOn_gradientCovector hψ j)

theorem contDiffOn_gradientNorm (hψ : ContDiffOn ℝ ∞ ψ U) :
    ContDiffOn ℝ ∞ (g.gradientNorm ψ) U :=
  ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
    ((g.contDiffOn_coefficient_inv i j).mul (contDiffOn_gradientCovector hψ i)).mul
      (contDiffOn_gradientCovector hψ j)

/-- The derivative of a finite sum of products. -/
theorem fderiv_sum_mul {ι : Type} (s : Finset ι) {F P : ι → MinkowskiModel d → ℝ}
    {x : MinkowskiModel d} (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) x)
    (hP : ∀ i ∈ s, DifferentiableAt ℝ (P i) x) (v : MinkowskiModel d) :
    fderiv ℝ (fun z => ∑ i ∈ s, F i z * P i z) x v =
      ∑ i ∈ s, (fderiv ℝ (F i) x v * P i x + F i x * fderiv ℝ (P i) x v) := by
  rw [fderiv_fun_sum fun i hi => (hF i hi).fun_mul (hP i hi), _root_.sum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [fderiv_fun_mul (hF i hi) (hP i hi)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

/-- A derivative along `v` is the combination `v^i ∂_i` of the partial derivatives. -/
theorem fderiv_apply_eq_sum (F : MinkowskiModel d → ℝ) (x v : MinkowskiModel d) :
    fderiv ℝ F x v = ∑ i, v i * fderiv ℝ F x (Pi.single i 1) := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- **The gradient of a phase is geodesic up to the gradient of its norm**:
`k^i ∂_i k^k + Γ^k_{ij} k^i k^j = ½ g^{km} ∂_m g(k, k)` for `k = (dψ)^♯`, that is
`∇_k k = ½ ∇ g(k, k)`. -/
theorem gradientField_covariant (hψ : ContDiffOn ℝ ∞ ψ U) {z : MinkowskiModel d} (hz : z ∈ U)
    (k : Fin (d + 1)) :
    fderiv ℝ (fun y => g.gradientField ψ y k) z (g.gradientField ψ z) +
        ∑ i, ∑ j, christoffelOf g.coefficient z k i j * g.gradientField ψ z i *
          g.gradientField ψ z j =
      (∑ m, (g.coefficient z)⁻¹ k m * gradientCovector (g.gradientNorm ψ) z m) / 2 := by
  set G := (g.coefficient z)⁻¹
  set Γ := christoffelOf g.coefficient z
  set p := gradientCovector ψ z
  set K := g.gradientField ψ z
  set H : Fin (d + 1) → Fin (d + 1) → ℝ := fun i l => secondPartial ψ z i l
  have hU := U.isOpen.mem_nhds hz
  have hGd (a b : Fin (d + 1)) : DifferentiableAt ℝ (fun y => (g.coefficient y)⁻¹ a b) z :=
    ((g.contDiffOn_coefficient_inv a b).contDiffAt hU).differentiableAt (by simp)
  have hpd (a : Fin (d + 1)) : DifferentiableAt ℝ (fun y => gradientCovector ψ y a) z :=
    ((contDiffOn_gradientCovector hψ a).contDiffAt hU).differentiableAt (by simp)
  have hGs (a b : Fin (d + 1)) : G a b = G b a := g.coefficient_inv_symmetric hz a b
  have hΓs (a b c : Fin (d + 1)) : Γ a b c = Γ a c b := g.christoffelOf_coefficient_symm hz a b c
  have hHs (a b : Fin (d + 1)) : H a b = H b a :=
    secondPartial_comm ((hψ.contDiffAt hU).of_le (by simp)) a b
  have hdp (m a : Fin (d + 1)) :
      fderiv ℝ (fun y => gradientCovector ψ y a) z (Pi.single m 1) = H m a := rfl
  have hdG (m a b : Fin (d + 1)) :
      fderiv ℝ (fun y => (g.coefficient y)⁻¹ a b) z (Pi.single m 1) =
        -∑ e, (Γ a m e * G e b + Γ b m e * G a e) := g.fderiv_coefficient_inv hz a b m
  have hKe (e : Fin (d + 1)) : ∑ l, G e l * p l = K e := rfl
  -- the derivative of `k^k` along `e_i`
  have hdK (i : Fin (d + 1)) : fderiv ℝ (fun y => g.gradientField ψ y k) z (Pi.single i 1) =
      -∑ e, Γ k i e * K e - ∑ e, G k e * ∑ l, Γ l i e * p l + ∑ l, G k l * H i l := by
    change fderiv ℝ (fun y => ∑ l, (g.coefficient y)⁻¹ k l * gradientCovector ψ y l) z _ = _
    rw [fderiv_sum_mul _ (fun l _ => hGd k l) (fun l _ => hpd l)]
    simp only [hdG, hdp]
    have h2 : ∀ e, ∑ l, (Γ k i e * G e l + Γ l i e * G k e) * gradientCovector ψ z l =
        Γ k i e * K e + G k e * ∑ l, Γ l i e * p l := by
      intro e
      rw [← hKe, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    have h1 : ∑ l, (-∑ e, (Γ k i e * G e l + Γ l i e * G k e)) * gradientCovector ψ z l =
        -∑ e, ∑ l, (Γ k i e * G e l + Γ l i e * G k e) * gradientCovector ψ z l := by
      simp only [neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [Finset.sum_add_distrib, h1]
    simp only [h2, Finset.sum_add_distrib]
    ring
  -- the derivative of the norm along `e_m`
  have hdN (m : Fin (d + 1)) : gradientCovector (g.gradientNorm ψ) z m =
      2 * (∑ a, H m a * K a - ∑ a, ∑ e, Γ a m e * p a * K e) := by
    unfold gradientCovector gradientNorm
    have hin (a : Fin (d + 1)) : fderiv ℝ (fun y => ∑ b, (g.coefficient y)⁻¹ a b *
        gradientCovector ψ y a * gradientCovector ψ y b) z (Pi.single m 1) =
        ∑ b, ((-∑ e, (Γ a m e * G e b + Γ b m e * G a e)) * p a * p b + G a b * H m a * p b +
          G a b * p a * H m b) := by
      rw [fderiv_sum_mul _ (fun b _ => (hGd a b).fun_mul (hpd a)) (fun b _ => hpd b)]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [fderiv_fun_mul (hGd a b) (hpd a)]
      simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, hdG, hdp]
      ring
    rw [fderiv_fun_sum fun a _ => DifferentiableAt.fun_sum fun b _ =>
      ((hGd a b).fun_mul (hpd a)).fun_mul (hpd b), _root_.sum_apply]
    simp only [hin]
    -- rearrange
    have t1 : ∑ a, ∑ b, (-∑ e, Γ a m e * G e b) * p a * p b =
        -∑ a, ∑ e, Γ a m e * p a * K e := by
      simp only [← hKe, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun b _ => by ring
    have t2 : ∑ a, ∑ b, (-∑ e, Γ b m e * G a e) * p a * p b =
        -∑ a, ∑ e, Γ a m e * p a * K e := by
      simp only [← hKe, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun a _ => by
        rw [hGs a e]; ring
    have t3 : ∑ a, ∑ b, G a b * H m a * p b = ∑ a, H m a * K a := by
      simp only [← hKe, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    have t4 : ∑ a, ∑ b, G a b * p a * H m b = ∑ a, H m a * K a := by
      simp only [← hKe, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by
        rw [hGs b a]; ring
    have hsplit : ∑ a, ∑ b, ((-∑ e, (Γ a m e * G e b + Γ b m e * G a e)) * p a * p b +
        G a b * H m a * p b + G a b * p a * H m b) =
        ∑ a, ∑ b, (-∑ e, Γ a m e * G e b) * p a * p b +
          ∑ a, ∑ b, (-∑ e, Γ b m e * G a e) * p a * p b +
          ∑ a, ∑ b, G a b * H m a * p b + ∑ a, ∑ b, G a b * p a * H m b := by
      simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        rw [Finset.sum_add_distrib]; ring
    rw [hsplit, t1, t2, t3, t4]
    ring
  -- assemble
  rw [fderiv_apply_eq_sum]
  simp only [hdK, hdN]
  have e2 : ∑ i, K i * ∑ l, G k l * H i l = ∑ m, G k m * ∑ a, H m a * K a := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by rw [hHs i l]; ring
  have e3 : ∑ i, K i * ∑ e, G k e * ∑ l, Γ l i e * p l =
      ∑ m, G k m * ∑ a, ∑ e, Γ a m e * p a * K e := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by
      rw [hΓs l i e]; ring
  have e4 : ∑ i, K i * ∑ e, Γ k i e * K e = ∑ i, ∑ j, Γ k i j * K i * K j := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hlhs : ∑ i, K i * (-∑ e, Γ k i e * K e - ∑ e, G k e * ∑ l, Γ l i e * p l +
      ∑ l, G k l * H i l) = -∑ i, K i * ∑ e, Γ k i e * K e -
        ∑ i, K i * ∑ e, G k e * ∑ l, Γ l i e * p l + ∑ i, K i * ∑ l, G k l * H i l := by
    simp only [mul_add, mul_sub, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib]
  have hrhs : ∑ m, G k m * (2 * (∑ a, H m a * K a - ∑ a, ∑ e, Γ a m e * p a * K e)) =
      2 * (∑ m, G k m * ∑ a, H m a * K a - ∑ m, G k m * ∑ a, ∑ e, Γ a m e * p a * K e) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hlhs, hrhs, e2, e3, e4]
  ring

/-- The velocity `k = (dψ)^♯` has the squared norm `g_{ij} k^i k^j = g(dψ, dψ)`. -/
theorem sum_coefficient_gradientField {z : MinkowskiModel d} (hz : z ∈ U) :
    ∑ i, ∑ j, g.coefficient z i j * g.gradientField ψ z i * g.gradientField ψ z j =
      g.gradientNorm ψ z := by
  have hCG : g.coefficient z * (g.coefficient z)⁻¹ = 1 := g.coefficient_mul_inv ⟨z, hz⟩
  have hrow (i : Fin (d + 1)) :
      ∑ j, g.coefficient z i j * g.gradientField ψ z j = gradientCovector ψ z i := by
    have h := congrFun (Matrix.mulVec_mulVec (gradientCovector ψ z) (g.coefficient z)
      (g.coefficient z)⁻¹) i
    rw [hCG, Matrix.one_mulVec] at h
    exact h
  have hl : ∑ i, ∑ j, g.coefficient z i j * g.gradientField ψ z i * g.gradientField ψ z j =
      ∑ i, g.gradientField ψ z i * ∑ j, g.coefficient z i j * g.gradientField ψ z j := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hl]
  simp only [hrow]
  simp only [gradientField, gradientNorm, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **Rays are null geodesics** (target of §108): if the phase `ψ` is smooth on `U` and its
gradient is null there, `g(dψ, dψ) = 0`, then every integral curve of `k = (dψ)^♯` on an open
set of parameters is an affinely parametrized geodesic of `g`. -/
theorem isGeodesicOn_ray (hψ : ContDiffOn ℝ ∞ ψ U) (hnull : ∀ z ∈ U, g.gradientNorm ψ z = 0)
    {γ : ℝ → U} {s : Set ℝ} (hs : IsOpen s)
    (hγ : ∀ t ∈ s, HasDerivAt (fun t => (γ t : MinkowskiModel d)) (g.gradientField ψ (γ t)) t) :
    g.toLorentzMetric.IsGeodesicOn s γ := by
  set x : ℝ → MinkowskiModel d := fun t => (γ t : MinkowskiModel d)
  have hK := contDiffOn_gradientField (g := g) hψ
  have hxc : ContinuousOn x s := fun t ht => (hγ t ht).continuousAt.continuousWithinAt
  have hmaps : MapsTo x s U := fun t _ => (γ t).2
  have hdx : EqOn (deriv x) (fun t => g.gradientField ψ (x t)) s := fun t ht => (hγ t ht).deriv
  have hdiff : DifferentiableOn ℝ x s := fun t ht =>
    (hγ t ht).differentiableAt.differentiableWithinAt
  have hx1 : ContDiffOn ℝ 1 x s := by
    rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hs]
    refine ⟨hdiff, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact ((hK.continuousOn.comp hxc hmaps).congr hdx)
  have hx2 : ContDiffOn ℝ 2 x s := by
    rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hs]
    refine ⟨hdiff, by simp, ?_⟩
    exact ((hK.of_le (by simp)).comp hx1 hmaps).congr hdx
  rw [g.isGeodesicOn_iff hs hx2]
  intro t ht k
  have hy : x t ∈ U := (γ t).2
  have hKd : DifferentiableAt ℝ (g.gradientField ψ) (x t) :=
    (hK.contDiffAt (U.isOpen.mem_nhds hy)).differentiableAt (by simp)
  have hev : deriv x =ᶠ[𝓝 t] fun t => g.gradientField ψ (x t) :=
    Filter.eventually_of_mem (hs.mem_nhds ht) hdx
  have hd2 : deriv (deriv x) t = fderiv ℝ (g.gradientField ψ) (x t) (g.gradientField ψ (x t)) := by
    rw [hev.deriv_eq]
    exact (hKd.hasFDerivAt.comp_hasDerivAt t (hγ t ht)).deriv
  have hN0 (m : Fin (d + 1)) : gradientCovector (g.gradientNorm ψ) (x t) m = 0 := by
    have hzero : g.gradientNorm ψ =ᶠ[𝓝 (x t)] fun _ => 0 :=
      Filter.eventually_of_mem (U.isOpen.mem_nhds hy) hnull
    simp [gradientCovector, hzero.fderiv_eq]
  change deriv (deriv x) t k + ∑ i, ∑ j, christoffelOf g.coefficient (x t) k i j *
    deriv x t i * deriv x t j = 0
  rw [hd2, hdx ht, ← fderiv_component hKd, gradientField_covariant hψ hy k]
  simp [hN0]

/-- Along such a ray the velocity is null: `g(γ̇, γ̇) = 0`. -/
theorem form_curveVelocity_ray (hnull : ∀ z ∈ U, g.gradientNorm ψ z = 0) {γ : ℝ → U} {t : ℝ}
    (hγ : HasDerivAt (fun t => (γ t : MinkowskiModel d)) (g.gradientField ψ (γ t)) t) :
    g.toLorentzMetric.form (γ t) (curveVelocity γ t) (curveVelocity γ t) = 0 := by
  rw [g.form_curveVelocity hγ.differentiableAt, hγ.deriv,
    sum_coefficient_gradientField (γ t).2, hnull _ (γ t).2]

end Rays

end ProjectAinos.SmoothGeometry.CoordinateMetric
