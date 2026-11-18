/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateEinsteinHilbert
public import ProjectAinos.Variational.RelativeIntegral

/-!
# The metric variation of matter actions

For a coordinate metric `g` on an open set `U` and a smooth symmetric variation `h` with compact
support in `U`, a matter density `ℒ(g)` that depends on the metric only through `g^{ab}` and
`√|g|` at the point has the first variation `δℒ = −½ T_{ik} δg^{ik} √|g|`, which defines the
Hilbert stress tensor `T_{ik}`.

* `hasDerivAt_integral_of_pointwise`: a relative integral `∫ (L(ε, x) − L(0, x)) dx` of a density
  that is smooth where `g + εh` is admissible and does not change off the support of `h` has the
  derivative `∫ ∂_ε L(0, x) dx`.
* `scalarFieldDensity`, `scalarStress`, `hasDerivAt_integral_scalarFieldDensity`: the scalar field
  `−½ (g^{ab} ∂_aφ ∂_bφ + m² φ²) √|g|` has
  `T_{ik} = ∂_iφ ∂_kφ − ½ g_{ik} (g^{ab} ∂_aφ ∂_bφ + m² φ²)`.
* `maxwellDensity`, `maxwellStress`, `hasDerivAt_integral_maxwellDensity`: for a fixed
  antisymmetric field `F_{ab}`, the density `−¼ F_{ab} F^{ab} √|g|` has
  `T_{ik} = F_{ib} F_k{}^b − ¼ g_{ik} F_{ab} F^{ab}`; it is symmetric and, in four dimensions,
  trace-free (`maxwellStress_symm`, `sum_inv_mul_maxwellStress`).
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

namespace CoordinateMetric

variable {U : Opens (MinkowskiModel d)} {g : CoordinateMetric σ d U}
  {h : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ}

/-! ### Relative integrals of admissible variations -/

theorem formCoeff_of_notMem {x : MinkowskiModel d} (hx : x ∉ tsupport h) : formCoeff h x = 0 := by
  ext i j
  simp [formCoeff, image_eq_zero_of_notMem_tsupport hx]

theorem inverseVariation_of_notMem {x : MinkowskiModel d} (hx : x ∉ tsupport h)
    (i k : Fin (d + 1)) : g.inverseVariation h x i k = 0 := by
  simp [inverseVariation, formCoeff_of_notMem hx]

theorem variationFamily_of_notMem {x : MinkowskiModel d} (hx : x ∉ tsupport h) (ε : ℝ) :
    g.variationFamily h (ε, x) = g.variationFamily h (0, x) :=
  (variationFamily_eventuallyEq_of_notMem hx ε).eq_of_nhds

theorem familyDensity_of_notMem {x : MinkowskiModel d} (hx : x ∉ tsupport h) (ε : ℝ) :
    familyDensity (g.variationFamily h) (ε, x) = familyDensity (g.variationFamily h) (0, x) :=
  densityOf_congr (variationFamily_eventuallyEq_of_notMem hx ε)

theorem variationFamily_zero_apply (x : MinkowskiModel d) :
    g.variationFamily h (0, x) = g.coefficient x := by
  simp [variationFamily]

theorem familyDensity_zero (x : MinkowskiModel d) :
    familyDensity (g.variationFamily h) (0, x) = densityOf g.coefficient x := by
  rw [familyDensity, variationFamily_zero]

/-- `g_{ik} δg^{ik} = −g^{ab} h_{ab}`. -/
theorem sum_coefficient_mul_inverseVariation {x : MinkowskiModel d} (hx : x ∈ U) :
    ∑ i, ∑ k, g.coefficient x i k * g.inverseVariation h x i k =
      -∑ a, ∑ b, (g.coefficient x)⁻¹ a b * formCoeff h x a b := by
  unfold inverseVariation
  rw [sum_mul_neg_sandwich _ _ _ (g.coefficient_inv_symmetric hx)]
  simp only [g.sum_inv_mul_inv_mul_coefficient hx]

/-- **A relative integral of an admissible variation.** Let `L(ε, x)` be smooth at `(ε, z)` for
every admissible `ε` and `z ∈ U`, unchanged off the support of `h`, and with the derivative
`L' x` in `ε` at `0` on `U`. Then `d/dε ∫ (L(ε, x) − L(0, x)) dx = ∫ L' x dx` at `ε = 0`. -/
theorem hasDerivAt_integral_of_pointwise (hh : ContDiff ℝ ∞ h) (hK : HasCompactSupport h)
    (hKU : tsupport h ⊆ U) (hs : ∀ z v w, h z v w = h z w v) {L : ℝ × MinkowskiModel d → ℝ}
    (hL : ∀ ε, g.IsAdmissible h ε → ∀ z ∈ U, ContDiffAt ℝ ∞ L (ε, z))
    (hconst : ∀ x ∉ tsupport h, ∀ t, L (t, x) = L (0, x)) {L' : MinkowskiModel d → ℝ}
    (hL' : ∀ x ∈ U, HasDerivAt (fun ε => L (ε, x)) (L' x) 0)
    (hL'0 : ∀ x ∉ tsupport h, L' x = 0) :
    HasDerivAt (fun ε => ∫ x, (L (ε, x) - L (0, x))) (∫ x, L' x) 0 := by
  obtain ⟨δ, hδ, hadm⟩ :=
    Metric.eventually_nhds_iff.mp (g.eventually_isAdmissible hh.continuous hK hKU hs)
  have hball : ∀ ε ∈ Metric.closedBall (0 : ℝ) (δ / 2), ∀ z ∈ U, ContDiffAt ℝ ∞ L (ε, z) :=
    fun ε hε => hL ε (hadm (by
      rw [Metric.mem_closedBall] at hε
      linarith [half_lt_self hδ]))
  have hd := Variational.hasDerivAt_integral_sub (μ := volume) U.isOpen hK hKU (half_pos hδ)
    hball hconst
  have hL'eq : (fun x => deriv (fun t => L (t, x)) 0) = L' := by
    funext x
    by_cases hx : x ∈ U
    · exact (hL' x hx).deriv
    · have hxK : x ∉ tsupport h := fun h' => hx (hKU h')
      rw [show (fun t => L (t, x)) = fun _ => L (0, x) from funext fun t => hconst x hxK t,
        deriv_const, hL'0 x hxK]
  rw [hL'eq] at hd
  exact hd

/-! ### A scalar field -/

section Scalar

variable (g h) in
/-- The density `−½ (g^{ab} ∂_aφ ∂_bφ + m² φ²) √|g|` of a scalar field for `g + εh`. -/
def scalarFieldDensity (m : ℝ) (φ : MinkowskiModel d → ℝ) (p : ℝ × MinkowskiModel d) : ℝ :=
  -((∑ a, ∑ b, (g.variationFamily h p)⁻¹ a b * (fderiv ℝ φ p.2 (Pi.single a 1) *
    fderiv ℝ φ p.2 (Pi.single b 1)) + m ^ 2 * φ p.2 ^ 2) / 2) *
    familyDensity (g.variationFamily h) p

variable (g) in
/-- The Hilbert tensor `T_{ik} = ∂_iφ ∂_kφ − ½ g_{ik} (g^{ab} ∂_aφ ∂_bφ + m² φ²)` of a scalar
field. -/
def scalarStress (m : ℝ) (φ : MinkowskiModel d → ℝ) (x : MinkowskiModel d) (i k : Fin (d + 1)) :
    ℝ :=
  fderiv ℝ φ x (Pi.single i 1) * fderiv ℝ φ x (Pi.single k 1) - g.coefficient x i k / 2 *
    (∑ a, ∑ b, (g.coefficient x)⁻¹ a b * (fderiv ℝ φ x (Pi.single a 1) *
      fderiv ℝ φ x (Pi.single b 1)) + m ^ 2 * φ x ^ 2)

theorem scalarStress_symm {x : MinkowskiModel d} (hx : x ∈ U) (m : ℝ) (φ : MinkowskiModel d → ℝ)
    (i k : Fin (d + 1)) : g.scalarStress m φ x i k = g.scalarStress m φ x k i := by
  rw [scalarStress, scalarStress, g.coefficient_symmetric hx i k, mul_comm (fderiv ℝ φ x _)]

theorem scalarFieldDensity_of_notMem (m : ℝ) (φ : MinkowskiModel d → ℝ) {x : MinkowskiModel d}
    (hx : x ∉ tsupport h) (t : ℝ) :
    g.scalarFieldDensity h m φ (t, x) = g.scalarFieldDensity h m φ (0, x) := by
  simp only [scalarFieldDensity]
  rw [variationFamily_of_notMem hx t, familyDensity_of_notMem hx t]

theorem contDiffAt_scalarFieldDensity (hh : ContDiff ℝ ∞ h) (m : ℝ) {φ : MinkowskiModel d → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ U) {p : ℝ × MinkowskiModel d} (hp : p.2 ∈ U)
    (hdet : (g.variationFamily h p).det ≠ 0) :
    ContDiffAt ℝ ∞ (g.scalarFieldDensity h m φ) p := by
  have hC := fun i j => contDiffAt_variationFamily (g := g) hh hp i j
  have hφp : ContDiffAt ℝ ∞ (fun q : ℝ × MinkowskiModel d => φ q.2) p :=
    (hφ.contDiffAt (U.isOpen.mem_nhds hp)).comp p contDiffAt_snd
  have hdφ (a : Fin (d + 1)) : ContDiffAt ℝ ∞
      (fun q : ℝ × MinkowskiModel d => fderiv ℝ φ q.2 (Pi.single a 1)) p :=
    contDiffAt_fderiv_snd hφp (Pi.single a 1)
  have hsum : ContDiffAt ℝ ∞ (fun q : ℝ × MinkowskiModel d => ∑ a, ∑ b,
      (g.variationFamily h q)⁻¹ a b * (fderiv ℝ φ q.2 (Pi.single a 1) *
        fderiv ℝ φ q.2 (Pi.single b 1))) p :=
    ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ =>
      (contDiffAt_familyInv hC hdet a b).mul ((hdφ a).mul (hdφ b))
  exact ((((hsum.add (contDiffAt_const.mul (hφp.pow 2))).div_const 2).neg).mul
    (contDiffAt_familyDensity hC hdet))

/-- **The Hilbert tensor of a scalar field**, pointwise:
`δ(−½ (g^{ab} ∂_aφ ∂_bφ + m² φ²) √|g|) = −½ T_{ik} δg^{ik} √|g|`. -/
theorem hasDerivAt_scalarFieldDensity (hh : ContDiff ℝ ∞ h) (hs : ∀ z v w, h z v w = h z w v)
    (m : ℝ) (φ : MinkowskiModel d → ℝ) {x : MinkowskiModel d} (hx : x ∈ U) :
    HasDerivAt (fun ε => g.scalarFieldDensity h m φ (ε, x))
      (-(∑ i, ∑ k, g.scalarStress m φ x i k * g.inverseVariation h x i k) / 2 *
        densityOf g.coefficient x) 0 := by
  set p : Fin (d + 1) → ℝ := fun a => fderiv ℝ φ x (Pi.single a 1) with hp
  have hP : HasDerivAt (fun ε => ∑ a, ∑ b, (g.variationFamily h (ε, x))⁻¹ a b * (p a * p b) +
      m ^ 2 * φ x ^ 2) (∑ a, ∑ b, g.inverseVariation h x a b * (p a * p b)) 0 :=
    (HasDerivAt.fun_sum (u := Finset.univ) fun a _ => HasDerivAt.fun_sum (u := Finset.univ)
      fun b _ => (hasDerivAt_inverseVariation hh hx a b).mul_const (p a * p b)).add_const _
  have hD := g.hasDerivAt_variationFamily_density hs hx
  have hprod := (hP.div_const 2).neg.mul hD
  simp only [scalarFieldDensity]
  convert hprod using 1
  simp only [Pi.neg_apply, variationFamily_zero_apply, familyDensity_zero]
  have htr := g.sum_coefficient_mul_inverseVariation (h := h) hx
  have hsplit : ∑ i, ∑ k, g.scalarStress m φ x i k * g.inverseVariation h x i k =
      ∑ a, ∑ b, g.inverseVariation h x a b * (p a * p b) -
        (∑ a, ∑ b, (g.coefficient x)⁻¹ a b * (p a * p b) + m ^ 2 * φ x ^ 2) / 2 *
          ∑ i, ∑ k, g.coefficient x i k * g.inverseVariation h x i k := by
    simp only [scalarStress, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hsplit, htr]
  ring

/-- **The Hilbert tensor of a scalar field.** For a smooth symmetric variation `h` with compact
support in `U`,
`d/dε ∫ (ℒ(g_ε) − ℒ(g)) dx = −½ ∫ T_{ik} δg^{ik} √|g| dx` at `ε = 0`. -/
theorem hasDerivAt_integral_scalarFieldDensity (hh : ContDiff ℝ ∞ h) (hK : HasCompactSupport h)
    (hKU : tsupport h ⊆ U) (hs : ∀ z v w, h z v w = h z w v) (m : ℝ)
    {φ : MinkowskiModel d → ℝ} (hφ : ContDiffOn ℝ ∞ φ U) :
    HasDerivAt (fun ε => ∫ x, (g.scalarFieldDensity h m φ (ε, x) -
        g.scalarFieldDensity h m φ (0, x)))
      (∫ x, -(∑ i, ∑ k, g.scalarStress m φ x i k * g.inverseVariation h x i k) / 2 *
        densityOf g.coefficient x) 0 :=
  hasDerivAt_integral_of_pointwise hh hK hKU hs
    (fun _ hε z hz => contDiffAt_scalarFieldDensity hh m hφ hz
      (variationFamily_det_ne_zero hh hε hz))
    (fun x hx t => scalarFieldDensity_of_notMem m φ hx t)
    (fun x hx => hasDerivAt_scalarFieldDensity hh hs m φ hx)
    (fun x hx => by simp [inverseVariation_of_notMem hx])

end Scalar

/-! ### A fixed electromagnetic field -/

section Maxwell

variable (g h) in
/-- The density `−¼ F_{ab} F_{ce} g^{ac} g^{be} √|g|` of a fixed field `F` for `g + εh`. -/
def maxwellDensity (F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (p : ℝ × MinkowskiModel d) : ℝ :=
  -((∑ a, ∑ b, ∑ c, ∑ e, (g.variationFamily h p)⁻¹ a c * (g.variationFamily h p)⁻¹ b e *
    (F p.2 a b * F p.2 c e)) / 4) * familyDensity (g.variationFamily h) p

variable (g) in
/-- The invariant `F_{ab} F^{ab}`. -/
def maxwellInvariant (F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ e, (g.coefficient x)⁻¹ a c * (g.coefficient x)⁻¹ b e * (F x a b * F x c e)

variable (g) in
/-- The contraction `F_{ib} F_k{}^b = F_{ib} F_{ke} g^{be}`. -/
def maxwellProduct (F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (i k : Fin (d + 1)) : ℝ :=
  ∑ b, ∑ e, (g.coefficient x)⁻¹ b e * (F x i b * F x k e)

variable (g) in
/-- The Hilbert tensor `T_{ik} = F_{ib} F_k{}^b − ¼ g_{ik} F_{ab} F^{ab}` of a fixed field. -/
def maxwellStress (F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (i k : Fin (d + 1)) : ℝ :=
  g.maxwellProduct F x i k - g.coefficient x i k / 4 * g.maxwellInvariant F x

theorem maxwellStress_symm {x : MinkowskiModel d} (hx : x ∈ U)
    (F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (i k : Fin (d + 1)) :
    g.maxwellStress F x i k = g.maxwellStress F x k i := by
  rw [maxwellStress, maxwellStress, g.coefficient_symmetric hx i k, maxwellProduct,
    maxwellProduct, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => by
    rw [g.coefficient_inv_symmetric hx b e]
    ring

/-- In dimension four the Hilbert tensor of the field is trace-free: `g^{ik} T_{ik} = 0`. -/
theorem sum_inv_mul_maxwellStress (hd : d = 3) {x : MinkowskiModel d} (hx : x ∈ U)
    (F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    ∑ i, ∑ k, (g.coefficient x)⁻¹ i k * g.maxwellStress F x i k = 0 := by
  subst hd
  have h1 : (g.coefficient x)⁻¹ * g.coefficient x = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (g.coefficient_det_ne_zero ⟨x, hx⟩))
  have htr : ∑ i, ∑ k, (g.coefficient x)⁻¹ i k * g.coefficient x i k = ((3 : ℕ) : ℝ) + 1 := by
    have h2 : ∑ i, ∑ k, (g.coefficient x)⁻¹ i k * g.coefficient x i k =
        Matrix.trace ((g.coefficient x)⁻¹ * (g.coefficient x).transpose) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    rw [h2, g.coefficient_transpose hx, h1, Matrix.trace_one, Fintype.card_fin]
    push_cast
    ring
  have hfirst : ∑ i, ∑ k, (g.coefficient x)⁻¹ i k * g.maxwellProduct F x i k =
      g.maxwellInvariant F x := by
    simp only [maxwellInvariant, maxwellProduct, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => by ring
  have hsecond : ∑ i, ∑ k, (g.coefficient x)⁻¹ i k * (g.coefficient x i k / 4 *
      g.maxwellInvariant F x) = (((3 : ℕ) : ℝ) + 1) / 4 * g.maxwellInvariant F x := by
    rw [← htr, Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hterm (i k : Fin (3 + 1)) : (g.coefficient x)⁻¹ i k * g.maxwellStress F x i k =
      (g.coefficient x)⁻¹ i k * g.maxwellProduct F x i k -
        (g.coefficient x)⁻¹ i k * (g.coefficient x i k / 4 * g.maxwellInvariant F x) := by
    rw [maxwellStress, mul_sub]
  simp only [hterm, Finset.sum_sub_distrib, hfirst, hsecond]
  push_cast
  ring

theorem maxwellDensity_of_notMem (F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    {x : MinkowskiModel d} (hx : x ∉ tsupport h) (t : ℝ) :
    g.maxwellDensity h F (t, x) = g.maxwellDensity h F (0, x) := by
  simp only [maxwellDensity]
  rw [variationFamily_of_notMem hx t, familyDensity_of_notMem hx t]

theorem contDiffAt_maxwellDensity (hh : ContDiff ℝ ∞ h)
    {F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hF : ∀ a b, ContDiffOn ℝ ∞ (fun x => F x a b) U) {p : ℝ × MinkowskiModel d} (hp : p.2 ∈ U)
    (hdet : (g.variationFamily h p).det ≠ 0) :
    ContDiffAt ℝ ∞ (g.maxwellDensity h F) p := by
  have hC := fun i j => contDiffAt_variationFamily (g := g) hh hp i j
  have hFp (a b : Fin (d + 1)) : ContDiffAt ℝ ∞ (fun q : ℝ × MinkowskiModel d => F q.2 a b) p :=
    ((hF a b).contDiffAt (U.isOpen.mem_nhds hp)).comp p contDiffAt_snd
  have hsum : ContDiffAt ℝ ∞ (fun q : ℝ × MinkowskiModel d => ∑ a, ∑ b, ∑ c, ∑ e,
      (g.variationFamily h q)⁻¹ a c * (g.variationFamily h q)⁻¹ b e *
        (F q.2 a b * F q.2 c e)) p :=
    ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ => ContDiffAt.sum fun c _ =>
      ContDiffAt.sum fun e _ => ((contDiffAt_familyInv hC hdet a c).mul
        (contDiffAt_familyInv hC hdet b e)).mul ((hFp a b).mul (hFp c e))
  exact (hsum.div_const 4).neg.mul (contDiffAt_familyDensity hC hdet)

/-- **The Hilbert tensor of a fixed field**, pointwise:
`δ(−¼ F_{ab} F^{ab} √|g|) = −½ T_{ik} δg^{ik} √|g|`. -/
theorem hasDerivAt_maxwellDensity (hh : ContDiff ℝ ∞ h) (hs : ∀ z v w, h z v w = h z w v)
    {F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}
    (hx : x ∈ U) (hFa : ∀ a b, F x a b = -F x b a) :
    HasDerivAt (fun ε => g.maxwellDensity h F (ε, x))
      (-(∑ i, ∑ k, g.maxwellStress F x i k * g.inverseVariation h x i k) / 2 *
        densityOf g.coefficient x) 0 := by
  have hinv := fun a b => hasDerivAt_inverseVariation (g := g) hh hx a b
  have hQ : HasDerivAt (fun ε => ∑ a, ∑ b, ∑ c, ∑ e, (g.variationFamily h (ε, x))⁻¹ a c *
      (g.variationFamily h (ε, x))⁻¹ b e * (F x a b * F x c e))
      (∑ a, ∑ b, ∑ c, ∑ e, (g.inverseVariation h x a c * (g.coefficient x)⁻¹ b e +
        (g.coefficient x)⁻¹ a c * g.inverseVariation h x b e) * (F x a b * F x c e)) 0 := by
    refine HasDerivAt.fun_sum (u := Finset.univ) fun a _ => HasDerivAt.fun_sum
      (u := Finset.univ) fun b _ => HasDerivAt.fun_sum (u := Finset.univ) fun c _ =>
        HasDerivAt.fun_sum (u := Finset.univ) fun e _ => ?_
    have h1 := ((hinv a c).mul (hinv b e)).mul_const (F x a b * F x c e)
    rw [variationFamily_zero_apply] at h1
    exact h1
  have hD := g.hasDerivAt_variationFamily_density hs hx
  have hprod := (hQ.div_const 4).neg.mul hD
  simp only [maxwellDensity]
  convert hprod using 1
  simp only [Pi.neg_apply, variationFamily_zero_apply, familyDensity_zero]
  have htr := g.sum_coefficient_mul_inverseVariation (h := h) hx
  -- the two terms of `δQ` are equal
  have hswap : ∑ a, ∑ b, ∑ c, ∑ e, (g.coefficient x)⁻¹ a c * g.inverseVariation h x b e *
      (F x a b * F x c e) = ∑ a, ∑ b, ∑ c, ∑ e, g.inverseVariation h x a c *
        (g.coefficient x)⁻¹ b e * (F x a b * F x c e) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun c _ => by
      rw [hFa b a, hFa e c]
      ring
  have hdQ : ∑ a, ∑ b, ∑ c, ∑ e, (g.inverseVariation h x a c * (g.coefficient x)⁻¹ b e +
      (g.coefficient x)⁻¹ a c * g.inverseVariation h x b e) * (F x a b * F x c e) =
      2 * ∑ a, ∑ c, g.inverseVariation h x a c * g.maxwellProduct F x a c := by
    simp only [maxwellProduct, add_mul, Finset.sum_add_distrib]
    rw [hswap, ← two_mul]
    congr 1
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun e _ => by ring
  have hsplit : ∑ i, ∑ k, g.maxwellStress F x i k * g.inverseVariation h x i k =
      ∑ a, ∑ c, g.inverseVariation h x a c * g.maxwellProduct F x a c -
      g.maxwellInvariant F x / 4 * ∑ i, ∑ k, g.coefficient x i k * g.inverseVariation h x i k := by
    simp only [maxwellStress, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hdQ, hsplit, htr]
  simp only [maxwellInvariant]
  ring

/-- **The Hilbert tensor of a fixed field.** For a smooth symmetric variation `h` with compact
support in `U` and an antisymmetric field `F` that is smooth on `U`,
`d/dε ∫ (ℒ(g_ε) − ℒ(g)) dx = −½ ∫ T_{ik} δg^{ik} √|g| dx` at `ε = 0`. -/
theorem hasDerivAt_integral_maxwellDensity (hh : ContDiff ℝ ∞ h) (hK : HasCompactSupport h)
    (hKU : tsupport h ⊆ U) (hs : ∀ z v w, h z v w = h z w v)
    {F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hF : ∀ a b, ContDiffOn ℝ ∞ (fun x => F x a b) U)
    (hFa : ∀ x ∈ U, ∀ a b, F x a b = -F x b a) :
    HasDerivAt (fun ε => ∫ x, (g.maxwellDensity h F (ε, x) - g.maxwellDensity h F (0, x)))
      (∫ x, -(∑ i, ∑ k, g.maxwellStress F x i k * g.inverseVariation h x i k) / 2 *
        densityOf g.coefficient x) 0 :=
  hasDerivAt_integral_of_pointwise hh hK hKU hs
    (fun _ hε z hz => contDiffAt_maxwellDensity hh hF hz (variationFamily_det_ne_zero hh hε hz))
    (fun x hx t => maxwellDensity_of_notMem F hx t)
    (fun x hx => hasDerivAt_maxwellDensity hh hs hx (hFa x hx))
    (fun x hx => by simp [inverseVariation_of_notMem hx])

end Maxwell

end CoordinateMetric

end ProjectAinos.SmoothGeometry
