/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.Pseudotensor
public import ProjectAinos.SmoothGeometry.Lorentzian.PseudotensorQuadratic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The pseudotensor in the Christoffel symbols

Landau–Lifshitz, (96.9). For a metric given by coefficients on an open set `U`:

* `superpotential_eq`: `h^{ikl} = (−g) H^{ikl}` with `H` (`pseudoH`) in the Christoffel symbols;
* `fderiv_christoffelOf`: at every point of `U`, `∂_m Γ^k_{ij} = ½ g^{kl}(Ŝ_{jl,mi} + Ŝ_{li,mj}
  − Ŝ_{ij,ml}) − Γ^k_{me} Γ^e_{ij}` for the array `Ŝ = reducedSecondDerivative`, which is
  symmetric in each pair, and `ricciOf_eq`: the Ricci tensor is the part of the Ricci formula
  linear in these `Ŝ`-terms;
* `pseudotensor_eq`: **the expression (96.9)**, `t^{ik} = ½ {…}` with the braces `pseudoBraces`
  of Landau and Lifshitz (the factor `c⁴/16πk` is outside `t` here).
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

/-! ### The derivative of `pseudoH` along functions -/

section Derivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {z : E}

theorem fderiv_mul_mul_apply {a b c : E → ℝ} (ha : DifferentiableAt ℝ a z)
    (hb : DifferentiableAt ℝ b z) (hc : DifferentiableAt ℝ c z) (v : E) :
    fderiv ℝ (fun w => a w * b w * c w) z v =
      (fderiv ℝ a z v * b z + a z * fderiv ℝ b z v) * c z + a z * b z * fderiv ℝ c z v := by
  rw [fderiv_fun_mul (ha.fun_mul hb) hc, fderiv_fun_mul ha hb]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

variable {Gf : E → Fin n → Fin n → ℝ} {Γf : E → Fin n → Fin n → Fin n → ℝ}

theorem differentiableAt_pseudoH (hG : ∀ a b, DifferentiableAt ℝ (fun w => Gf w a b) z)
    (hΓ : ∀ a b c, DifferentiableAt ℝ (fun w => Γf w a b c) z) (i k l : Fin n) :
    DifferentiableAt ℝ (fun w => pseudoH (Gf w) (Γf w) i k l) z := by
  have h3 (a b c e p q r : Fin n) :
      DifferentiableAt ℝ (fun w => Gf w a b * Gf w c e * Γf w p q r) z :=
    ((hG a b).fun_mul (hG c e)).fun_mul (hΓ p q r)
  unfold pseudoH
  exact DifferentiableAt.fun_sum fun m _ => DifferentiableAt.fun_sum fun e _ =>
    (((((h3 i k l m e e m).fun_sub (h3 i k m e l m e)).fun_sub (h3 i l k m e e m)).fun_add
      (h3 i l m e k m e)).fun_sub (h3 i e l m k m e)).fun_add (h3 i e k m l m e)

/-- The derivative of `w ↦ H(G(w), Γ(w))` is `pseudoHDeriv` of the derivatives. -/
theorem fderiv_pseudoH (hG : ∀ a b, DifferentiableAt ℝ (fun w => Gf w a b) z)
    (hΓ : ∀ a b c, DifferentiableAt ℝ (fun w => Γf w a b c) z) (v : E) (i k l : Fin n) :
    fderiv ℝ (fun w => pseudoH (Gf w) (Γf w) i k l) z v =
      pseudoHDeriv (Gf z) (fun a b => fderiv ℝ (fun w => Gf w a b) z v) (Γf z)
        (fun a b c => fderiv ℝ (fun w => Γf w a b c) z v) i k l := by
  have h3 (a b c e p q r : Fin n) :
      DifferentiableAt ℝ (fun w => Gf w a b * Gf w c e * Γf w p q r) z :=
    ((hG a b).fun_mul (hG c e)).fun_mul (hΓ p q r)
  have hb (m e : Fin n) := (((((h3 i k l m e e m).hasFDerivAt.fun_sub
    (h3 i k m e l m e).hasFDerivAt).fun_sub (h3 i l k m e e m).hasFDerivAt).fun_add
    (h3 i l m e k m e).hasFDerivAt).fun_sub (h3 i e l m k m e).hasFDerivAt).fun_add
    (h3 i e k m l m e).hasFDerivAt
  unfold pseudoH pseudoHDeriv
  rw [fderiv_fun_sum fun m _ => DifferentiableAt.fun_sum fun e _ => (hb m e).differentiableAt,
    _root_.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [fderiv_fun_sum fun e _ => (hb m e).differentiableAt, _root_.sum_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [(hb m e).fderiv]
  simp only [add_apply, sub_apply, fderiv_mul_mul_apply (hG _ _) (hG _ _) (hΓ _ _ _)]

end Derivative

namespace CoordinateMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}
  (g : CoordinateMetric σ d U)

/-- The array `Ŝ_{ab,ce} = ∂_c ∂_e g_{ab} − g_{pq}(Γ^p_{cb} Γ^q_{ea} + Γ^p_{ca} Γ^q_{eb})`. -/
def reducedSecondDerivative (x : MinkowskiModel d) (a b c e : Fin (d + 1)) : ℝ :=
  reducedSecond (fun p q => g.coefficient x p q) (christoffelOf g.coefficient x)
    (g.secondDerivative x) a b c e

variable {g} {z : MinkowskiModel d}

theorem reducedSecondDerivative_symm_left (hz : z ∈ U) (a b c e : Fin (d + 1)) :
    g.reducedSecondDerivative z a b c e = g.reducedSecondDerivative z b a c e :=
  reducedSecond_symm_left (secondDerivative_symm_left hz) a b c e

theorem reducedSecondDerivative_symm_right (hz : z ∈ U) (a b c e : Fin (d + 1)) :
    g.reducedSecondDerivative z a b c e = g.reducedSecondDerivative z a b e c :=
  reducedSecond_symm_right (g.coefficient_symmetric hz) (secondDerivative_symm_right hz) a b c e

/-- Lowering the Christoffel symbols:
`g_{lq} Γ^q_{ij} = ½(∂_i g_{jl} + ∂_j g_{li} − ∂_l g_{ij})`. -/
theorem sum_coefficient_mul_christoffelOf (hz : z ∈ U) (l i j : Fin (d + 1)) :
    ∑ q, g.coefficient z l q * christoffelOf g.coefficient z q i j =
      (fderiv ℝ (fun w => g.coefficient w j l) z (Pi.single i 1) +
        fderiv ℝ (fun w => g.coefficient w l i) z (Pi.single j 1) -
        fderiv ℝ (fun w => g.coefficient w i j) z (Pi.single l 1)) / 2 := by
  set Y : Fin (d + 1) → ℝ := fun r => (fderiv ℝ (fun w => g.coefficient w j r) z (Pi.single i 1) +
    fderiv ℝ (fun w => g.coefficient w r i) z (Pi.single j 1) -
    fderiv ℝ (fun w => g.coefficient w i j) z (Pi.single r 1)) / 2 with hY
  have hΓ (q : Fin (d + 1)) :
      christoffelOf g.coefficient z q i j = ∑ r, (g.coefficient z)⁻¹ q r * Y r := by
    unfold christoffelOf
    exact Finset.sum_congr rfl fun r _ => by simp only [hY]; ring
  have hinv := g.coefficient_mul_inv ⟨z, hz⟩
  calc ∑ q, g.coefficient z l q * christoffelOf g.coefficient z q i j =
        ∑ r, (∑ q, g.coefficient z l q * (g.coefficient z)⁻¹ q r) * Y r := by
        simp only [hΓ, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun q _ => by ring
    _ = ∑ r, (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) l r * Y r :=
        Finset.sum_congr rfl fun r _ => by rw [← Matrix.mul_apply, hinv]
    _ = Y l := by simp [Matrix.one_apply]

/-- **The derivative of the Christoffel symbols at every point**:
`∂_m Γ^k_{ij} = ½ g^{kl}(Ŝ_{jl,mi} + Ŝ_{li,mj} − Ŝ_{ij,ml}) − Γ^k_{me} Γ^e_{ij}`. -/
theorem fderiv_christoffelOf (hz : z ∈ U) (k i j m : Fin (d + 1)) :
    fderiv ℝ (fun w => christoffelOf g.coefficient w k i j) z (Pi.single m 1) =
      christoffelDerivative (fun a b => (g.coefficient z)⁻¹ a b) (g.reducedSecondDerivative z)
          m k i j -
        ∑ e, christoffelOf g.coefficient z k m e * christoffelOf g.coefficient z e i j := by
  have hU := U.isOpen.mem_nhds hz
  have hD (a b e : Fin (d + 1)) :
      DifferentiableAt ℝ (fun w => fderiv ℝ (fun v => g.coefficient v a b) w (Pi.single e 1)) z :=
    ((((g.coefficient_contDiffOn a b).fderiv_of_isOpen U.isOpen (m := ∞) (by simp)).clm_apply
      contDiffOn_const).contDiffAt hU).differentiableAt (by simp)
  have hI (a b : Fin (d + 1)) : DifferentiableAt ℝ (fun w => (g.coefficient w)⁻¹ a b) z :=
    ((g.contDiffOn_coefficient_inv a b).contDiffAt hU).differentiableAt (by simp)
  set Y : Fin (d + 1) → ℝ := fun r => (fderiv ℝ (fun w => g.coefficient w j r) z (Pi.single i 1) +
    fderiv ℝ (fun w => g.coefficient w r i) z (Pi.single j 1) -
    fderiv ℝ (fun w => g.coefficient w i j) z (Pi.single r 1)) / 2 with hY
  have hterm (l : Fin (d + 1)) : HasFDerivAt (fun w => (g.coefficient w)⁻¹ k l *
      (fderiv ℝ (fun v => g.coefficient v j l) w (Pi.single i 1) +
        fderiv ℝ (fun v => g.coefficient v l i) w (Pi.single j 1) -
        fderiv ℝ (fun v => g.coefficient v i j) w (Pi.single l 1)) / 2)
      ((1 / 2 : ℝ) • ((g.coefficient z)⁻¹ k l •
        (fderiv ℝ (fun w => fderiv ℝ (fun v => g.coefficient v j l) w (Pi.single i 1)) z +
          fderiv ℝ (fun w => fderiv ℝ (fun v => g.coefficient v l i) w (Pi.single j 1)) z -
          fderiv ℝ (fun w => fderiv ℝ (fun v => g.coefficient v i j) w (Pi.single l 1)) z) +
        (fderiv ℝ (fun v => g.coefficient v j l) z (Pi.single i 1) +
          fderiv ℝ (fun v => g.coefficient v l i) z (Pi.single j 1) -
          fderiv ℝ (fun v => g.coefficient v i j) z (Pi.single l 1)) •
          fderiv ℝ (fun w => (g.coefficient w)⁻¹ k l) z)) z := by
    have h := (((hI k l).hasFDerivAt.mul
      (((hD j l i).hasFDerivAt.add (hD l i j).hasFDerivAt).sub (hD i j l).hasFDerivAt)).const_mul
      (1 / 2 : ℝ))
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
    ring
  have hfirst : ∑ l, Y l * -∑ e, (christoffelOf g.coefficient z k m e *
      (g.coefficient z)⁻¹ e l + christoffelOf g.coefficient z l m e * (g.coefficient z)⁻¹ k e) =
      -∑ e, christoffelOf g.coefficient z k m e * christoffelOf g.coefficient z e i j -
        ∑ l, (g.coefficient z)⁻¹ k l * ∑ p, ∑ q, g.coefficient z p q *
          christoffelOf g.coefficient z p m l * christoffelOf g.coefficient z q i j := by
    have hΓ (e : Fin (d + 1)) :
        christoffelOf g.coefficient z e i j = ∑ l, (g.coefficient z)⁻¹ e l * Y l := by
      unfold christoffelOf
      exact Finset.sum_congr rfl fun r _ => by simp only [hY]; ring
    have hlow (l : Fin (d + 1)) : Y l = ∑ q, g.coefficient z l q *
        christoffelOf g.coefficient z q i j := (g.sum_coefficient_mul_christoffelOf hz l i j).symm
    have h1 : ∑ l, Y l * ∑ e, christoffelOf g.coefficient z k m e * (g.coefficient z)⁻¹ e l =
        ∑ e, christoffelOf g.coefficient z k m e * christoffelOf g.coefficient z e i j := by
      simp only [hΓ, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun l _ => by ring
    have h2 : ∑ l, Y l * ∑ e, christoffelOf g.coefficient z l m e * (g.coefficient z)⁻¹ k e =
        ∑ l, (g.coefficient z)⁻¹ k l * ∑ p, ∑ q, g.coefficient z p q *
          christoffelOf g.coefficient z p m l * christoffelOf g.coefficient z q i j := by
      conv_lhs => rw [Finset.sum_congr rfl fun l _ => by rw [hlow l]]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun l _ =>
        Finset.sum_congr rfl fun q _ => by ring
    simp only [mul_neg, Finset.sum_neg_distrib, mul_add, Finset.sum_add_distrib, neg_add]
    rw [h1, h2]
    ring
  have hrhs : christoffelDerivative (fun a b => (g.coefficient z)⁻¹ a b)
      (g.reducedSecondDerivative z) m k i j =
      christoffelDerivative (fun a b => (g.coefficient z)⁻¹ a b) (g.secondDerivative z) m k i j -
        ∑ l, (g.coefficient z)⁻¹ k l * ∑ p, ∑ q, g.coefficient z p q *
          christoffelOf g.coefficient z p m l * christoffelOf g.coefficient z q i j :=
    christoffelDerivative_reducedSecond _ (g.christoffelOf_coefficient_symm hz) m k i j
  have hlhs : fderiv ℝ (fun w => christoffelOf g.coefficient w k i j) z (Pi.single m 1) =
      ∑ l, fderiv ℝ (fun w => (g.coefficient w)⁻¹ k l *
        (fderiv ℝ (fun v => g.coefficient v j l) w (Pi.single i 1) +
          fderiv ℝ (fun v => g.coefficient v l i) w (Pi.single j 1) -
          fderiv ℝ (fun v => g.coefficient v i j) w (Pi.single l 1)) / 2) z (Pi.single m 1) := by
    unfold christoffelOf
    rw [fderiv_fun_sum fun l _ => (hterm l).differentiableAt, _root_.sum_apply]
  rw [hrhs, hlhs]
  have hsum : ∑ l, fderiv ℝ (fun w => (g.coefficient w)⁻¹ k l *
      (fderiv ℝ (fun v => g.coefficient v j l) w (Pi.single i 1) +
        fderiv ℝ (fun v => g.coefficient v l i) w (Pi.single j 1) -
        fderiv ℝ (fun v => g.coefficient v i j) w (Pi.single l 1)) / 2) z (Pi.single m 1) =
      christoffelDerivative (fun a b => (g.coefficient z)⁻¹ a b) (g.secondDerivative z) m k i j +
        ∑ l, Y l * -∑ e, (christoffelOf g.coefficient z k m e *
          (g.coefficient z)⁻¹ e l + christoffelOf g.coefficient z l m e *
            (g.coefficient z)⁻¹ k e) := by
    unfold christoffelDerivative
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [(hterm l).fderiv]
    simp only [smul_apply, add_apply, sub_apply, smul_eq_mul]
    rw [g.fderiv_coefficient_inv hz]
    simp only [secondDerivative, hY]
    ring
  rw [hsum, hfirst]
  ring

/-- **The Ricci tensor at every point** is `ricciDerivative` of the array `Ŝ`. -/
theorem ricciOf_eq (hz : z ∈ U) (a b : Fin (d + 1)) :
    ricciOf g.coefficient z a b =
      ricciDerivative (fun p q => (g.coefficient z)⁻¹ p q) (g.reducedSecondDerivative z) a b := by
  unfold ricciOf ricciDerivative
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [fderiv_christoffelOf hz, fderiv_christoffelOf hz, Finset.sum_sub_distrib]
  ring

/-- **The superpotential in the Christoffel symbols**: `h^{ikl} = (−g) H^{ikl}` on `U`. -/
theorem superpotential_eq (hz : z ∈ U) (i k l : Fin (d + 1)) :
    g.superpotential z i k l = densityOf g.coefficient z ^ 2 *
      pseudoH (fun a b => (g.coefficient z)⁻¹ a b) (christoffelOf g.coefficient z) i k l := by
  have hU := U.isOpen.mem_nhds hz
  have hD : DifferentiableAt ℝ (fun w => densityOf g.coefficient w) z :=
    (g.contDiffAt_densityOf hz).differentiableAt (by simp)
  have hI (a b : Fin (d + 1)) : DifferentiableAt ℝ (fun w => (g.coefficient w)⁻¹ a b) z :=
    ((g.contDiffOn_coefficient_inv a b).contDiffAt hU).differentiableAt (by simp)
  rw [← superpotential_algebra _ _ (g.coefficient_inv_symmetric hz)
    (g.christoffelOf_coefficient_symm hz), Finset.mul_sum]
  unfold superpotential
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold superpotentialDensity
  simp only [sq]
  have hQ := (hI i k).fun_mul (hI l m)
  have hR := (hI i l).fun_mul (hI k m)
  rw [fderiv_fun_mul (hD.fun_mul hD) (hQ.fun_sub hR), fderiv_fun_mul hD hD,
    fderiv_fun_sub hQ hR, fderiv_fun_mul (hI i k) (hI l m), fderiv_fun_mul (hI i l) (hI k m)]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul, g.fderiv_densityOf hz,
    g.fderiv_coefficient_inv hz]
  ring

/-- **The divergence of the superpotential at every point**:
`∂_l h^{ikl} = (−g)(2 Γ^c_{cl} H^{ikl} + ∂_l H^{ikl})`. -/
theorem divergence_superpotential_christoffel (hz : z ∈ U) (i k : Fin (d + 1)) :
    ∑ l, fderiv ℝ (fun w => g.superpotential w i k l) z (Pi.single l 1) =
      densityOf g.coefficient z ^ 2 *
        (2 * ∑ l, ∑ c, christoffelOf g.coefficient z c c l *
            pseudoH (fun a b => (g.coefficient z)⁻¹ a b) (christoffelOf g.coefficient z) i k l +
          ∑ l, pseudoHDeriv (fun a b => (g.coefficient z)⁻¹ a b)
            (fun a b => -∑ e, (christoffelOf g.coefficient z a l e * (g.coefficient z)⁻¹ e b +
              christoffelOf g.coefficient z b l e * (g.coefficient z)⁻¹ a e))
            (christoffelOf g.coefficient z)
            (fun p q r => fderiv ℝ (fun w => christoffelOf g.coefficient w p q r) z
              (Pi.single l 1)) i k l) := by
  have hU := U.isOpen.mem_nhds hz
  have hD : DifferentiableAt ℝ (fun w => densityOf g.coefficient w) z :=
    (g.contDiffAt_densityOf hz).differentiableAt (by simp)
  have hI (a b : Fin (d + 1)) : DifferentiableAt ℝ (fun w => (g.coefficient w)⁻¹ a b) z :=
    ((g.contDiffOn_coefficient_inv a b).contDiffAt hU).differentiableAt (by simp)
  have hΓ (a b c : Fin (d + 1)) :
      DifferentiableAt ℝ (fun w => christoffelOf g.coefficient w a b c) z :=
    ((g.contDiffOn_christoffelOf a b c).contDiffAt hU).differentiableAt (by simp)
  have hH := differentiableAt_pseudoH (Gf := fun w a b => (g.coefficient w)⁻¹ a b)
    (Γf := fun w => christoffelOf g.coefficient w) hI hΓ i k
  have hl (l : Fin (d + 1)) : fderiv ℝ (fun w => g.superpotential w i k l) z (Pi.single l 1) =
      densityOf g.coefficient z ^ 2 *
        (2 * ((∑ c, christoffelOf g.coefficient z c c l) *
            pseudoH (fun a b => (g.coefficient z)⁻¹ a b) (christoffelOf g.coefficient z) i k l) +
          pseudoHDeriv (fun a b => (g.coefficient z)⁻¹ a b)
            (fun a b => -∑ e, (christoffelOf g.coefficient z a l e * (g.coefficient z)⁻¹ e b +
              christoffelOf g.coefficient z b l e * (g.coefficient z)⁻¹ a e))
            (christoffelOf g.coefficient z)
            (fun p q r => fderiv ℝ (fun w => christoffelOf g.coefficient w p q r) z
              (Pi.single l 1)) i k l) := by
    have hev : (fun w => g.superpotential w i k l) =ᶠ[𝓝 z] fun w =>
        densityOf g.coefficient w * densityOf g.coefficient w *
          pseudoH (fun a b => (g.coefficient w)⁻¹ a b) (christoffelOf g.coefficient w) i k l :=
      eventually_of_mem hU fun w hw => by simp only [superpotential_eq hw, sq]
    have hdG : (fun a b => fderiv ℝ (fun w => (g.coefficient w)⁻¹ a b) z (Pi.single l 1)) =
        fun a b => -∑ e, (christoffelOf g.coefficient z a l e * (g.coefficient z)⁻¹ e b +
          christoffelOf g.coefficient z b l e * (g.coefficient z)⁻¹ a e) :=
      funext fun a => funext fun b => g.fderiv_coefficient_inv hz a b l
    rw [hev.fderiv_eq, fderiv_fun_mul (hD.fun_mul hD) (hH l), fderiv_fun_mul hD hD]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [g.fderiv_densityOf hz, fderiv_pseudoH (Gf := fun w a b => (g.coefficient w)⁻¹ a b)
      (Γf := fun w => christoffelOf g.coefficient w) hI hΓ, hdG]
    ring
  rw [Finset.sum_congr rfl fun l _ => hl l, ← Finset.mul_sum, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  simp only [Finset.sum_mul]

/-- The raised Einstein tensor is `g^{ia} g^{kb} R_{ab} − ½ g^{ik} R`. -/
theorem raisedEinstein_eq (hz : z ∈ U) (i k : Fin (d + 1)) :
    g.raisedEinstein z i k = ∑ a, ∑ b, (g.coefficient z)⁻¹ i a * (g.coefficient z)⁻¹ k b *
      ricciOf g.coefficient z a b - (g.coefficient z)⁻¹ i k *
        (∑ a, ∑ b, (g.coefficient z)⁻¹ a b * ricciOf g.coefficient z a b) / 2 := by
  have hscal : scalarOf g.coefficient z = ∑ a, ∑ b, (g.coefficient z)⁻¹ a b *
      ricciOf g.coefficient z a b := by
    unfold scalarOf
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  unfold raisedEinstein
  rw [← hscal, ← sum_inv_mul_coefficient hz i k, Finset.sum_mul, Finset.sum_div,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul, Finset.sum_div, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- **The energy-momentum pseudotensor in the Christoffel symbols**, Landau–Lifshitz (96.9):
`t^{ik} = ½ {…}` at every point of `U`, with the braces `pseudoBraces` of (96.9). -/
theorem pseudotensor_eq (hz : z ∈ U) (i k : Fin (d + 1)) :
    g.pseudotensor z i k = pseudoBraces (fun a b => (g.coefficient z)⁻¹ a b)
      (christoffelOf g.coefficient z) i k / 2 := by
  have hpos := g.densityOf_pos hz
  have hD2 : densityOf g.coefficient z ^ 2 ≠ 0 := by positivity
  have hsplit (l : Fin (d + 1)) :
      pseudoHDeriv (fun a b => (g.coefficient z)⁻¹ a b)
        (fun a b => -∑ e, (christoffelOf g.coefficient z a l e * (g.coefficient z)⁻¹ e b +
          christoffelOf g.coefficient z b l e * (g.coefficient z)⁻¹ a e))
        (christoffelOf g.coefficient z)
        (fun p q r => fderiv ℝ (fun w => christoffelOf g.coefficient w p q r) z
          (Pi.single l 1)) i k l =
      pseudoHDeriv (fun a b => (g.coefficient z)⁻¹ a b)
          (fun a b => -∑ e, (christoffelOf g.coefficient z a l e * (g.coefficient z)⁻¹ e b +
            christoffelOf g.coefficient z b l e * (g.coefficient z)⁻¹ a e))
          (christoffelOf g.coefficient z)
          (fun p q r => -∑ e, christoffelOf g.coefficient z p l e *
            christoffelOf g.coefficient z e q r) i k l +
        pseudoHDeriv (fun a b => (g.coefficient z)⁻¹ a b) (fun _ _ => 0)
          (christoffelOf g.coefficient z)
          (christoffelDerivative (fun a b => (g.coefficient z)⁻¹ a b)
            (g.reducedSecondDerivative z) l) i k l := by
    have hdΓ : (fun p q r => fderiv ℝ (fun w => christoffelOf g.coefficient w p q r) z
        (Pi.single l 1)) = fun p q r => -∑ e, christoffelOf g.coefficient z p l e *
          christoffelOf g.coefficient z e q r + christoffelDerivative
            (fun a b => (g.coefficient z)⁻¹ a b) (g.reducedSecondDerivative z) l p q r :=
      funext fun p => funext fun q => funext fun r => by
        rw [fderiv_christoffelOf hz]
        ring
    rw [hdΓ, pseudoHDeriv_add]
  have hquad := pseudotensor_quadratic (fun a b => (g.coefficient z)⁻¹ a b)
    (christoffelOf g.coefficient z) (g.coefficient_inv_symmetric hz)
    (g.christoffelOf_coefficient_symm hz) i k
  have hsec := pseudotensor_second_algebra (fun a b => (g.coefficient z)⁻¹ a b)
    (christoffelOf g.coefficient z) (g.reducedSecondDerivative z)
    (g.coefficient_inv_symmetric hz) (reducedSecondDerivative_symm_left hz)
    (reducedSecondDerivative_symm_right hz) i k
  unfold pseudotensor
  have hdiv (X : ℝ) : densityOf g.coefficient z ^ 2 * X / (2 * densityOf g.coefficient z ^ 2) =
      X / 2 := by
    field_simp
  rw [divergence_superpotential_christoffel hz, raisedEinstein_eq hz, hdiv]
  simp only [ricciOf_eq hz]
  simp only [hsplit]
  rw [Finset.sum_add_distrib]
  linear_combination hquad + hsec

end CoordinateMetric

end ProjectAinos.SmoothGeometry
