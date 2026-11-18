/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The algebra of the pseudotensor in the Christoffel symbols

Landau–Lifshitz, (96.9). For arrays `G^{ab}` (an inverse metric) and `Γ^k_{ij}` (Christoffel
symbols), symmetric in `a, b` and in `i, j`:

* `pseudoH`: `H^{ikl} = g^{ik}(g^{lm} Γ^e_{em} − g^{me} Γ^l_{me}) − g^{il}(g^{km} Γ^e_{em} −
  g^{me} Γ^k_{me}) − g^{ie} g^{lm} Γ^k_{me} + g^{ie} g^{km} Γ^l_{me}`, the superpotential
  `h^{ikl}` divided by `−g` (`superpotential_algebra` is the step from `∂_m λ^{iklm}`), and
  `pseudoHDeriv`, its derivative along a variation `(δG, δΓ)`;
* `christoffelDerivative`: `½ G^{kl}(S_{jl,mi} + S_{li,mj} − S_{ij,ml})`, and `ricciDerivative`,
  the part `∂_c Γ^c_{ab} − ∂_a Γ^c_{cb}` of the Ricci tensor, for an array `S_{ab,ce}`
  symmetric in `a, b` and in `c, e`; `reducedSecond` is the array `Ŝ` for which `∂_m Γ^k_{ij}` is
  `christoffelDerivative G Ŝ − Γ^k_{me} Γ^e_{ij}` at every point;
* `pseudoBraces`: the braces of (96.9).

`pseudotensor_second_algebra` shows that the part of `t^{ik}` linear in `Ŝ` vanishes, and
`pseudotensor_quadratic` that the part quadratic in `Γ` is half the braces. Each of these
identities is a sum of contractions with four (or two) summed indices; after the sums are
expanded, the proofs reindex every sum to a representative of its contraction class.
-/

@[expose] public section

noncomputable section

open Finset

namespace ProjectAinos.SmoothGeometry

variable {n : ℕ}

/-! ### Definitions -/

/-- `H^{ikl} = h^{ikl}/(−g)` in the Christoffel symbols. -/
def pseudoH (G : Fin n → Fin n → ℝ) (Γ : Fin n → Fin n → Fin n → ℝ) (i k l : Fin n) : ℝ :=
  ∑ m, ∑ e, (G i k * G l m * Γ e e m - G i k * G m e * Γ l m e - G i l * G k m * Γ e e m +
    G i l * G m e * Γ k m e - G i e * G l m * Γ k m e + G i e * G k m * Γ l m e)

/-- The derivative of `pseudoH` along a variation `(dG, dΓ)` of its arguments. -/
def pseudoHDeriv (G dG : Fin n → Fin n → ℝ) (Γ dΓ : Fin n → Fin n → Fin n → ℝ)
    (i k l : Fin n) : ℝ :=
  ∑ m, ∑ e, ((dG i k * G l m + G i k * dG l m) * Γ e e m + G i k * G l m * dΓ e e m -
    ((dG i k * G m e + G i k * dG m e) * Γ l m e + G i k * G m e * dΓ l m e) -
    ((dG i l * G k m + G i l * dG k m) * Γ e e m + G i l * G k m * dΓ e e m) +
    ((dG i l * G m e + G i l * dG m e) * Γ k m e + G i l * G m e * dΓ k m e) -
    ((dG i e * G l m + G i e * dG l m) * Γ k m e + G i e * G l m * dΓ k m e) +
    ((dG i e * G k m + G i e * dG k m) * Γ l m e + G i e * G k m * dΓ l m e))

/-- **The braces of (96.9)**, with `n ↦ a` and `p ↦ b`:
`(2Γ^a_{lm}Γ^b_{ab} − Γ^a_{lb}Γ^b_{ma} − Γ^a_{la}Γ^b_{mb})(g^{il}g^{km} − g^{ik}g^{lm})
+ g^{il}g^{ma}(Γ^k_{lb}Γ^b_{ma} + Γ^k_{ma}Γ^b_{lb} − Γ^k_{ab}Γ^b_{lm} − Γ^k_{lm}Γ^b_{ab})
+ g^{kl}g^{ma}(Γ^i_{lb}Γ^b_{ma} + Γ^i_{ma}Γ^b_{lb} − Γ^i_{ab}Γ^b_{lm} − Γ^i_{lm}Γ^b_{ab})
+ g^{lm}g^{ab}(Γ^i_{al}Γ^k_{bm} − Γ^i_{lm}Γ^k_{ab})`. -/
def pseudoBraces (G : Fin n → Fin n → ℝ) (Γ : Fin n → Fin n → Fin n → ℝ) (i k : Fin n) : ℝ :=
  ∑ l, ∑ m, (∑ a, ∑ b, (2 * Γ a l m * Γ b a b - Γ a l b * Γ b m a - Γ a l a * Γ b m b)) *
      (G i l * G k m - G i k * G l m) +
    ∑ l, ∑ m, ∑ a, G i l * G m a * ∑ b, (Γ k l b * Γ b m a + Γ k m a * Γ b l b -
      Γ k a b * Γ b l m - Γ k l m * Γ b a b) +
    ∑ l, ∑ m, ∑ a, G k l * G m a * ∑ b, (Γ i l b * Γ b m a + Γ i m a * Γ b l b -
      Γ i a b * Γ b l m - Γ i l m * Γ b a b) +
    ∑ l, ∑ m, ∑ a, ∑ b, G l m * G a b * (Γ i a l * Γ k b m - Γ i l m * Γ k a b)

/-- `½ G^{kl}(S_{jl,mi} + S_{li,mj} − S_{ij,ml})`, the derivative `∂_m Γ^k_{ij}` at a point
where the first derivatives of the metric vanish, for `S_{ab,ce} = ∂_c ∂_e g_{ab}`. -/
def christoffelDerivative (G : Fin n → Fin n → ℝ) (S : Fin n → Fin n → Fin n → Fin n → ℝ)
    (m k i j : Fin n) : ℝ :=
  ∑ l, G k l * (S j l m i + S l i m j - S i j m l) / 2

/-- `Σ_c (∂_c Γ^c_{ab} − ∂_a Γ^c_{cb})` with `∂_m Γ^k_{ij} = christoffelDerivative G S m k i j`. -/
def ricciDerivative (G : Fin n → Fin n → ℝ) (S : Fin n → Fin n → Fin n → Fin n → ℝ)
    (a b : Fin n) : ℝ :=
  ∑ c, (christoffelDerivative G S c c a b - christoffelDerivative G S a c c b)

/-- `Ŝ_{ab,ce} = S_{ab,ce} − C_{pq}(Γ^p_{cb} Γ^q_{ea} + Γ^p_{ca} Γ^q_{eb})`. -/
def reducedSecond (C : Fin n → Fin n → ℝ) (Γ : Fin n → Fin n → Fin n → ℝ)
    (S : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c e : Fin n) : ℝ :=
  S a b c e - ∑ p, ∑ q, C p q * (Γ p c b * Γ q e a + Γ p c a * Γ q e b)

/-! ### Reindexing a sum -/

theorem sum2_reindex (f g : Fin n → Fin n → ℝ) (c : ℝ) (σ : Fin n × Fin n ≃ Fin n × Fin n)
    (h : ∀ p : Fin n × Fin n, f p.1 p.2 = c * g (σ p).1 (σ p).2) :
    ∑ a, ∑ b, f a b = c * ∑ a, ∑ b, g a b := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type', Finset.mul_sum]
  exact Fintype.sum_equiv σ _ _ h

theorem sum4_eq_sum_prod (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d =
      ∑ p : Fin n × Fin n × Fin n × Fin n, f p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  simp only [Fintype.sum_prod_type]

theorem sum4_reindex (f g : Fin n → Fin n → Fin n → Fin n → ℝ) (c : ℝ)
    (σ : Fin n × Fin n × Fin n × Fin n ≃ Fin n × Fin n × Fin n × Fin n)
    (h : ∀ p : Fin n × Fin n × Fin n × Fin n, f p.1 p.2.1 p.2.2.1 p.2.2.2 =
      c * g (σ p).1 (σ p).2.1 (σ p).2.2.1 (σ p).2.2.2) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = c * ∑ a, ∑ b, ∑ c, ∑ d, g a b c d := by
  rw [sum4_eq_sum_prod, sum4_eq_sum_prod, Finset.mul_sum]
  exact Fintype.sum_equiv σ _ _ h

/-! ### Linear relations -/

/-- The derivative of `pseudoH` is additive in the variation of the Christoffel symbols. -/
theorem pseudoHDeriv_add (G dG : Fin n → Fin n → ℝ) (Γ dΓ₁ dΓ₂ : Fin n → Fin n → Fin n → ℝ)
    (i k l : Fin n) :
    pseudoHDeriv G dG Γ (fun p q r => dΓ₁ p q r + dΓ₂ p q r) i k l =
      pseudoHDeriv G dG Γ dΓ₁ i k l + pseudoHDeriv G (fun _ _ => 0) Γ dΓ₂ i k l := by
  unfold pseudoHDeriv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

section Reduced

variable {C : Fin n → Fin n → ℝ} {Γ : Fin n → Fin n → Fin n → ℝ}
  {S : Fin n → Fin n → Fin n → Fin n → ℝ}

theorem reducedSecond_symm_left (hS : ∀ a b c e, S a b c e = S b a c e) (a b c e : Fin n) :
    reducedSecond C Γ S a b c e = reducedSecond C Γ S b a c e := by
  unfold reducedSecond
  rw [hS a b c e]
  congr 1
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

theorem reducedSecond_symm_right (hC : ∀ a b, C a b = C b a)
    (hS : ∀ a b c e, S a b c e = S a b e c) (a b c e : Fin n) :
    reducedSecond C Γ S a b c e = reducedSecond C Γ S a b e c := by
  unfold reducedSecond
  rw [hS a b c e]
  congr 1
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
    rw [hC q p]
    ring

/-- `christoffelDerivative` of `Ŝ` differs from that of `S` by `G^{kl} C_{pq} Γ^p_{ml} Γ^q_{ij}`. -/
theorem christoffelDerivative_reducedSecond (G : Fin n → Fin n → ℝ)
    (hΓ : ∀ a b c, Γ a b c = Γ a c b) (m k i j : Fin n) :
    christoffelDerivative G (reducedSecond C Γ S) m k i j =
      christoffelDerivative G S m k i j - ∑ l, G k l * ∑ p, ∑ q, C p q * Γ p m l * Γ q i j := by
  unfold christoffelDerivative reducedSecond
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h : (∑ p, ∑ q, C p q * (Γ p m l * Γ q i j + Γ p m j * Γ q i l)) +
      (∑ p, ∑ q, C p q * (Γ p m i * Γ q j l + Γ p m l * Γ q j i)) -
      (∑ p, ∑ q, C p q * (Γ p m j * Γ q l i + Γ p m i * Γ q l j)) =
      2 * ∑ p, ∑ q, C p q * Γ p m l * Γ q i j := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hΓ q i l, hΓ q j l, hΓ q j i]
    ring
  linear_combination (-(G k l) / 2) * h

end Reduced

/-! ### The identities -/

/-- **The superpotential in the Christoffel symbols**: with `∂_m (−g) = 2(−g) Γ^c_{cm}` and
`∂_m G^{bc} = −Γ^b_{me} G^{ec} − Γ^c_{me} G^{be}`, `∂_m λ^{iklm} = (−g) H^{ikl}`. -/
theorem superpotential_algebra (G : Fin n → Fin n → ℝ) (Γ : Fin n → Fin n → Fin n → ℝ)
    (hG : ∀ a b, G a b = G b a) (hΓ : ∀ a b c, Γ a b c = Γ a c b) (i k l : Fin n) :
    ∑ m, (2 * (∑ c, Γ c c m) * (G i k * G l m - G i l * G k m) +
      ((-∑ e, (Γ i m e * G e k + Γ k m e * G i e)) * G l m +
        G i k * (-∑ e, (Γ l m e * G e m + Γ m m e * G l e)) -
        ((-∑ e, (Γ i m e * G e l + Γ l m e * G i e)) * G k m +
          G i l * (-∑ e, (Γ k m e * G e m + Γ m m e * G k e))))) = pseudoH G Γ i k l := by
  unfold pseudoH
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, mul_add, add_mul, mul_sub, neg_mul, mul_neg]
  have h1 : (∑ x, ∑ i_1, 2 * Γ i_1 i_1 x * (G i k * G l x)) =
      (2 : ℝ) * (∑ x, ∑ i_1, G i k * (Γ x x i_1 * G l i_1)) :=
    sum2_reindex _ _ _
      ⟨fun p => (p.2, p.1), fun p => (p.2, p.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        ring
  have h2 : (∑ x, ∑ x_1, G i k * G l x * Γ x_1 x_1 x) =
      (1 : ℝ) * (∑ x, ∑ i_1, G i k * (Γ x x i_1 * G l i_1)) :=
    sum2_reindex _ _ _
      ⟨fun p => (p.2, p.1), fun p => (p.2, p.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        ring
  have h3 : (∑ x, ∑ i_1, 2 * Γ i_1 i_1 x * (G i l * G k x)) =
      (2 : ℝ) * (∑ x, ∑ i_1, G i l * (Γ x x i_1 * G k i_1)) :=
    sum2_reindex _ _ _
      ⟨fun p => (p.2, p.1), fun p => (p.2, p.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        ring
  have h4 : (∑ x, ∑ x_1, G i l * G k x * Γ x_1 x_1 x) =
      (1 : ℝ) * (∑ x, ∑ i_1, G i l * (Γ x x i_1 * G k i_1)) :=
    sum2_reindex _ _ _
      ⟨fun p => (p.2, p.1), fun p => (p.2, p.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        ring
  have h5 : (∑ x, ∑ i_1, Γ i x i_1 * G i_1 l * G k x) =
      (1 : ℝ) * (∑ x, ∑ i_1, Γ i x i_1 * G i_1 k * G l x) :=
    sum2_reindex _ _ _
      ⟨fun p => (p.2, p.1), fun p => (p.2, p.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hΓ i p.1 p.2, hG p.2 l, hG k p.1]
        ring
  have h6 : (∑ x, ∑ x_1, G i x_1 * G l x * Γ k x x_1) =
      (1 : ℝ) * (∑ x, ∑ i_1, Γ k x i_1 * G i i_1 * G l x) :=
    sum2_reindex _ _ _
      ⟨fun p => (p.1, p.2), fun p => (p.1, p.2), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        ring
  have h7 : (∑ x, ∑ x_1, G i k * G x x_1 * Γ l x x_1) =
      (1 : ℝ) * (∑ x, ∑ i_1, G i k * (Γ l x i_1 * G i_1 x)) :=
    sum2_reindex _ _ _
      ⟨fun p => (p.1, p.2), fun p => (p.1, p.2), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hG p.1 p.2]
        ring
  have h8 : (∑ x, ∑ x_1, G i x_1 * G k x * Γ l x x_1) =
      (1 : ℝ) * (∑ x, ∑ i_1, Γ l x i_1 * G i i_1 * G k x) :=
    sum2_reindex _ _ _
      ⟨fun p => (p.1, p.2), fun p => (p.1, p.2), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        ring
  have h9 : (∑ x, ∑ x_1, G i l * G x x_1 * Γ k x x_1) =
      (1 : ℝ) * (∑ x, ∑ i_1, G i l * (Γ k x i_1 * G i_1 x)) :=
    sum2_reindex _ _ _
      ⟨fun p => (p.1, p.2), fun p => (p.1, p.2), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hG p.1 p.2]
        ring
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9]
  ring

/-- **The part of the pseudotensor linear in the second derivatives vanishes**: for `S`
symmetric in each pair, half the divergence of `H` along `δΓ = christoffelDerivative G S` is
the raised Einstein tensor of `ricciDerivative G S`. -/
theorem pseudotensor_second_algebra (G : Fin n → Fin n → ℝ) (Γ : Fin n → Fin n → Fin n → ℝ)
    (S : Fin n → Fin n → Fin n → Fin n → ℝ) (hG : ∀ a b, G a b = G b a)
    (hS₁ : ∀ a b c e, S a b c e = S b a c e) (hS₂ : ∀ a b c e, S a b c e = S a b e c)
    (i k : Fin n) :
    (∑ l, pseudoHDeriv G (fun _ _ => 0) Γ (christoffelDerivative G S l) i k l) / 2 =
      ∑ a, ∑ b, G i a * G k b * ricciDerivative G S a b -
        G i k * (∑ a, ∑ b, G a b * ricciDerivative G S a b) / 2 := by
  unfold pseudoHDeriv ricciDerivative christoffelDerivative
  simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_div,
    mul_add, mul_sub, zero_mul, mul_zero, add_zero, zero_add, add_div, sub_div, mul_div_assoc']
  have h1 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * G x x_1 * (G x_2 i_1 * S x_2 x_1 x i_1) / 2 / 2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * G x x_1 * (G x_2 i_1 * S x_1 i_1 x x_2) / 2 / 2)
          :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.1, p.2.2.2, p.2.2.1),
        fun p => (p.1, p.2.1, p.2.2.2, p.2.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hG p.2.2.1 p.2.2.2, hS₁ p.2.2.1 p.2.1 p.1 p.2.2.2]
        ring
  have h2 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * G x_1 x_2 * (G x i_1 * S x_2 i_1 x x_1) / 2 / 2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * G x x_1 * (G x_2 i_1 * S x_1 i_1 x x_2) / 2 / 2)
          :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.2.2, p.2.1, p.2.2.1),
        fun p => (p.1, p.2.2.1, p.2.2.2, p.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hS₁ p.2.2.1 p.2.2.2 p.1 p.2.1]
        ring
  have h3 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * G x_1 x_2 * (G x i_1 * S i_1 x_1 x x_2) / 2 / 2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * G x x_1 * (G x_2 i_1 * S x_1 i_1 x x_2) / 2 / 2)
          :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.2.2, p.2.2.1, p.2.1),
        fun p => (p.1, p.2.2.2, p.2.2.1, p.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hG p.2.1 p.2.2.1]
        ring
  have h4 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * (G x x_1 * (G x_2 i_1 * S x_1 i_1 x_2 x)) / 2 / 2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * G x x_1 * (G x_2 i_1 * S x_1 i_1 x x_2) / 2 / 2)
          :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2),
        fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hS₂ p.2.1 p.2.2.2 p.2.2.1 p.1]
        ring
  have h5 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * (G x x_1 * (G x_2 i_1 * S i_1 x x_2 x_1)) / 2 / 2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * G x x_1 * (G x_2 i_1 * S x_1 i_1 x x_2) / 2 / 2)
          :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.1, p.1, p.2.2.1, p.2.2.2),
        fun p => (p.2.1, p.1, p.2.2.1, p.2.2.2), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hG p.1 p.2.1, hS₁ p.2.2.2 p.1 p.2.2.1 p.2.1, hS₂ p.1 p.2.2.2 p.2.2.1 p.2.1]
        ring
  have h6 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * (G x x_1 * (G x_2 i_1 * S x_1 i_1 x x_2)) / 2 / 2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * G x x_1 * (G x_2 i_1 * S x_1 i_1 x x_2) / 2 / 2)
          :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2),
        fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        ring
  have h7 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * (G x x_1 * (G x_2 i_1 * S x_2 x_1 x i_1)) / 2 / 2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * G x x_1 * (G x_2 i_1 * S x_1 i_1 x x_2) / 2 / 2)
          :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.1, p.2.2.2, p.2.2.1),
        fun p => (p.1, p.2.1, p.2.2.2, p.2.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hG p.2.2.1 p.2.2.2, hS₁ p.2.2.1 p.2.1 p.1 p.2.2.2]
        ring
  have h8 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * G x_1 x_2 * (G x i_1 * S x_1 x_2 x i_1) / 2 / 2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * G x x_1 * (G x_2 i_1 * S i_1 x_2 x x_1) / 2 / 2)
          :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.2.2, p.2.1, p.2.2.1),
        fun p => (p.1, p.2.2.1, p.2.2.2, p.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hS₁ p.2.1 p.2.2.1 p.1 p.2.2.2]
        ring
  have h9 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * (G x x_1 * (G x_2 i_1 * S x x_1 x_2 i_1)) / 2 / 2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * G x x_1 * (G x_2 i_1 * S i_1 x_2 x x_1) / 2 / 2)
          :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1),
        fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hS₁ p.1 p.2.1 p.2.2.1 p.2.2.2]
        ring
  have h10 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * (G x x_1 * (G x_2 i_1 * S i_1 x_2 x x_1)) / 2 / 2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * G x x_1 * (G x_2 i_1 * S i_1 x_2 x x_1) / 2 / 2)
          :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2),
        fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        ring
  have h11 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * G k x_1 * (G x_2 i_1 * S x_2 x_1 x i_1) / 2 / 2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * G k x_1 * (G x_2 i_1 * S x_1 i_1 x x_2) / 2 / 2)
          :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.1, p.2.2.2, p.2.2.1),
        fun p => (p.1, p.2.1, p.2.2.2, p.2.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hG p.2.2.1 p.2.2.2, hS₁ p.2.2.1 p.2.1 p.1 p.2.2.2]
        ring
  have h12 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * G x_1 x_2 * (G k i_1 * S x_2 i_1 x x_1) / 2 / 2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * G k x_1 * (G x_2 i_1 * S x_1 i_1 x x_2) / 2 / 2)
          :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.2.2, p.2.1, p.2.2.1),
        fun p => (p.1, p.2.2.1, p.2.2.2, p.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hS₁ p.2.2.1 p.2.2.2 p.1 p.2.1]
        ring
  have h13 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * G x_1 x_2 * (G k i_1 * S i_1 x_1 x x_2) / 2 / 2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * G k x_1 * (G x_2 i_1 * S x_1 i_1 x x_2) / 2 / 2)
          :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.2.2, p.2.2.1, p.2.1),
        fun p => (p.1, p.2.2.2, p.2.2.1, p.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hG p.2.1 p.2.2.1]
        ring
  have h14 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x_2 * G x x_1 * (G k i_1 * S i_1 x_1 x x_2) / 2 / 2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * G k x_1 * (G x_2 i_1 * S x_1 i_1 x x_2) / 2 / 2)
          :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1),
        fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hS₂ p.2.2.2 p.2.1 p.1 p.2.2.1]
        ring
  have h15 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x_2 * G k x_1 * (G x i_1 * S i_1 x_1 x x_2) / 2 / 2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * G k x_1 * (G x_2 i_1 * S x_1 i_1 x x_2) / 2 / 2)
          :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.2.1, p.2.1, p.1, p.2.2.2),
        fun p => (p.2.2.1, p.2.1, p.1, p.2.2.2), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hS₁ p.2.2.2 p.2.1 p.1 p.2.2.1, hS₂ p.2.1 p.2.2.2 p.1 p.2.2.1]
        ring
  have h16 : (∑ x, ∑ x_1, ∑ x_2, ∑ x_3, G i x * G k x_1 * (G x_2 x_3 * S x_1 x_3 x_2 x) / 2) =
      (2 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * G k x_1 * (G x_2 i_1 * S x_1 i_1 x x_2) / 2 / 2)
          :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2),
        fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hS₂ p.2.1 p.2.2.2 p.2.2.1 p.1]
        ring
  have h17 : (∑ x, ∑ x_1, ∑ x_2, ∑ x_3, G i x * G k x_1 * (G x_2 x_3 * S x_1 x_3 x x_2) / 2) =
      (2 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * G k x_1 * (G x_2 i_1 * S x_1 i_1 x x_2) / 2 / 2)
          :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2),
        fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        ring
  have h18 : (∑ x, ∑ x_1, ∑ x_2, ∑ x_3, G i x * G k x_1 * (G x_2 x_3 * S x_2 x_1 x x_3) / 2) =
      (2 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * G k x_1 * (G x_2 i_1 * S x_1 i_1 x x_2) / 2 / 2)
          :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.1, p.2.2.2, p.2.2.1),
        fun p => (p.1, p.2.1, p.2.2.2, p.2.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hG p.2.2.1 p.2.2.2, hS₁ p.2.2.1 p.2.1 p.1 p.2.2.2]
        ring
  have h19 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * G x_1 x_2 * (G k i_1 * S x_1 x_2 x i_1) / 2 / 2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * G k x_1 * (G x_2 i_1 * S i_1 x_2 x x_1) / 2 / 2)
          :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.2.2, p.2.1, p.2.2.1),
        fun p => (p.1, p.2.2.1, p.2.2.2, p.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hS₁ p.2.1 p.2.2.1 p.1 p.2.2.2]
        ring
  have h20 : (∑ x, ∑ x_1, ∑ x_2, ∑ x_3, G i x * G k x_1 * (G x_2 x_3 * S x_3 x_2 x x_1) / 2) =
      (2 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * G k x_1 * (G x_2 i_1 * S i_1 x_2 x x_1) / 2 / 2)
          :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2),
        fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        ring
  have h21 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x_2 * G k x_1 * (G x i_1 * S x_1 x_2 x i_1) / 2 / 2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x_2 * G x x_1 * (G k i_1 * S x_2 i_1 x x_1) / 2 / 2)
          :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.2.2, p.2.2.1, p.2.1),
        fun p => (p.1, p.2.2.2, p.2.2.1, p.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hS₁ p.2.1 p.2.2.1 p.1 p.2.2.2]
        ring
  have h22 : (∑ x, ∑ x_1, ∑ x_2, ∑ x_3, G i x * G k x_1 * (G x_2 x_3 * S x x_1 x_2 x_3) / 2) =
      (2 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x_2 * G x x_1 * (G k i_1 * S x_2 i_1 x x_1) / 2 / 2)
          :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1),
        fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        ring
  have h23 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x_2 * G k x_1 * (G x i_1 * S x_2 i_1 x x_1) / 2 / 2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x_2 * G x x_1 * (G k i_1 * S x_1 x_2 x i_1) / 2 / 2)
          :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.2.2, p.2.2.1, p.2.1),
        fun p => (p.1, p.2.2.2, p.2.2.1, p.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hS₁ p.2.2.1 p.2.2.2 p.1 p.2.1]
        ring
  have h24 : (∑ x, ∑ x_1, ∑ x_2, ∑ x_3, G i x * G k x_1 * (G x_2 x_3 * S x_3 x x_2 x_1) / 2) =
      (2 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x_2 * G x x_1 * (G k i_1 * S x_1 x_2 x i_1) / 2 / 2)
          :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1),
        fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        ring
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
      h21, h22, h23, h24]
  ring

/-- **The part of the pseudotensor quadratic in the Christoffel symbols** is half the braces of
(96.9): `Γ^c_{cl} H^{ikl} + ½ ∂_l H^{ikl}` with `δG^{ab} = −Γ^a_{le} G^{eb} − Γ^b_{le} G^{ae}` and
`δΓ^p_{qr} = −Γ^p_{le} Γ^e_{qr}`. -/
theorem pseudotensor_quadratic (G : Fin n → Fin n → ℝ) (Γ : Fin n → Fin n → Fin n → ℝ)
    (hG : ∀ a b, G a b = G b a) (hΓ : ∀ a b c, Γ a b c = Γ a c b) (i k : Fin n) :
    ∑ l, ∑ c, Γ c c l * pseudoH G Γ i k l +
      (∑ l, pseudoHDeriv G (fun a b => -∑ e, (Γ a l e * G e b + Γ b l e * G a e)) Γ
        (fun p q r => -∑ e, Γ p l e * Γ e q r) i k l) / 2 = pseudoBraces G Γ i k / 2 := by
  unfold pseudoH pseudoHDeriv pseudoBraces
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, neg_add]
  have h1 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * (Γ x x i_1 * G i_1 x_1) * Γ x_2 x_2 x_1) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ x_1 x_1 x * (G i k * G x x_2 * Γ i_1 i_1 x_2)) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.2.2, p.1, p.2.1, p.2.2.1),
        fun p => (p.2.1, p.2.2.1, p.2.2.2, p.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        ring
  have h2 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ x_2 x x_2 * Γ i_1 x_1 i_1 * (G i k * G x x_1)) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ x_1 x_1 x * (G i k * G x x_2 * Γ i_1 i_1 x_2)) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.2.1, p.2.1, p.2.2.2),
        fun p => (p.1, p.2.2.1, p.2.1, p.2.2.2), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hΓ p.2.2.1 p.1 p.2.2.1, hΓ p.2.2.2 p.2.1 p.2.2.2]
        ring
  have h3 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * (Γ x_1 x i_1 * G x i_1) * Γ x_2 x_2 x_1) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ x_1 x_1 x * (G i k * G x_2 i_1 * Γ x x_2 i_1)) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.1, p.2.2.1, p.1, p.2.2.2),
        fun p => (p.2.2.1, p.1, p.2.1, p.2.2.2), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        ring
  have h4 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * G x_1 x_2 * (Γ x x i_1 * Γ i_1 x_1 x_2)) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ x_1 x_1 x * (G i k * G x_2 i_1 * Γ x x_2 i_1)) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.2.2, p.1, p.2.1, p.2.2.1),
        fun p => (p.2.1, p.2.2.1, p.2.2.2, p.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        ring
  have h5 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, 2 * Γ x_2 x x_1 * Γ i_1 x_2 i_1 * (G i k * G x x_1)) =
      (2 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ x_1 x_1 x * (G i k * G x_2 i_1 * Γ x x_2 i_1)) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1),
        fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hΓ p.2.2.2 p.2.2.1 p.2.2.2]
        ring
  have h6 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ x x i_1 * G i i_1 * G k x_1 * Γ x_2 x_2 x_1) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ x_1 x_1 x * (G i x * G k x_2 * Γ i_1 i_1 x_2)) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.2.2, p.1, p.2.1, p.2.2.1),
        fun p => (p.2.1, p.2.2.1, p.2.2.2, p.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        ring
  have h7 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ x_2 x x_2 * Γ i_1 x_1 i_1 * (G i x * G k x_1)) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ x_1 x_1 x * (G i x * G k x_2 * Γ i_1 i_1 x_2)) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.2.1, p.2.1, p.2.2.2),
        fun p => (p.1, p.2.2.1, p.2.1, p.2.2.2), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hΓ p.2.2.1 p.1 p.2.2.1, hΓ p.2.2.2 p.2.1 p.2.2.2]
        ring
  have h8 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ x x i_1 * G i i_1 * G x_1 x_2 * Γ k x_1 x_2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ x_1 x_1 x * (G i x * G x_2 i_1 * Γ k x_2 i_1)) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.2.2, p.1, p.2.1, p.2.2.1),
        fun p => (p.2.1, p.2.2.1, p.2.2.2, p.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        ring
  have h9 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * G x_1 x_2 * (Γ k x_1 x_2 * Γ i_1 x i_1)) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ x_1 x_1 x * (G i x * G x_2 i_1 * Γ k x_2 i_1)) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.2.2, p.2.1, p.2.2.1),
        fun p => (p.1, p.2.2.1, p.2.2.2, p.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hΓ p.2.2.2 p.1 p.2.2.2]
        ring
  have h10 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ k x i_1 * G i i_1 * G x x_1 * Γ x_2 x_2 x_1) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ x_1 x_1 x * (G i i_1 * G x x_2 * Γ k x_2 i_1)) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.1, p.2.2.1, p.1, p.2.2.2),
        fun p => (p.2.2.1, p.1, p.2.1, p.2.2.2), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hG p.1 p.2.1]
        ring
  have h11 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * (Γ k x i_1 * G i_1 x_1) * Γ x_2 x_2 x_1) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ x_1 x_1 x * (G i i_1 * G x x_2 * Γ k x_2 i_1)) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.1, p.2.2.1, p.2.2.2, p.1),
        fun p => (p.2.2.2, p.1, p.2.1, p.2.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hΓ k p.1 p.2.2.2, hG p.2.2.2 p.2.1]
        ring
  have h12 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x_2 * (Γ x x i_1 * G i_1 x_1) * Γ k x_1 x_2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ x_1 x_1 x * (G i i_1 * G x x_2 * Γ k x_2 i_1)) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.2.2, p.1, p.2.1, p.2.2.1),
        fun p => (p.2.1, p.2.2.1, p.2.2.2, p.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        ring
  have h13 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * G x_1 x_2 * (Γ k x x_1 * Γ i_1 x_2 i_1)) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ x_1 x_1 x * (G i i_1 * G x x_2 * Γ k x_2 i_1)) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.2.1, p.2.2.2, p.2.1, p.1),
        fun p => (p.2.2.2, p.2.2.1, p.1, p.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hG p.2.1 p.2.2.1, hΓ k p.1 p.2.1, hΓ p.2.2.2 p.2.2.1 p.2.2.2]
        ring
  have h14 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * (Γ x_1 x i_1 * G k i_1) * Γ x_2 x_2 x_1) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ x_1 x_1 x * (G i i_1 * G k x_2 * Γ x x_2 i_1)) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.1, p.2.2.1, p.2.2.2, p.1),
        fun p => (p.2.2.2, p.1, p.2.1, p.2.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hΓ p.2.1 p.1 p.2.2.2]
        ring
  have h15 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x_2 * G k x_1 * (Γ x x i_1 * Γ i_1 x_1 x_2)) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ x_1 x_1 x * (G i i_1 * G k x_2 * Γ x x_2 i_1)) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.2.2, p.1, p.2.1, p.2.2.1),
        fun p => (p.2.1, p.2.2.1, p.2.2.2, p.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        ring
  have h16 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, 2 * Γ x_2 x x_1 * Γ i_1 x_2 i_1 * (G i x * G k x_1)) =
      (2 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ x_1 x_1 x * (G i i_1 * G k x_2 * Γ x x_2 i_1)) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.2.1, p.2.2.2, p.2.1, p.1),
        fun p => (p.2.2.2, p.2.2.1, p.1, p.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hΓ p.2.2.1 p.1 p.2.1, hΓ p.2.2.2 p.2.2.1 p.2.2.2]
        ring
  have h17 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G k x * G x_1 x_2 * (Γ i x x_1 * Γ i_1 x_2 i_1)) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ i x i_1 * G i_1 k * G x x_1 * Γ x_2 x_2 x_1) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.1, p.2.2.1, p.2.2.2, p.1),
        fun p => (p.2.2.2, p.1, p.2.1, p.2.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hG k p.1, hΓ i p.1 p.2.1, hΓ p.2.2.2 p.2.2.1 p.2.2.2]
        ring
  have h18 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * (Γ x_1 x i_1 * G i_1 x_2) * Γ x x_1 x_2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * G x x_1 * (Γ x_2 x i_1 * Γ i_1 x_2 x_1)) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1),
        fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hG p.2.2.2 p.2.2.1, hΓ p.1 p.2.1 p.2.2.1]
        ring
  have h19 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * (Γ x_2 x i_1 * G x_1 i_1) * Γ x x_1 x_2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * G x x_1 * (Γ x_2 x i_1 * Γ i_1 x_2 x_1)) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.1, p.2.2.2, p.1, p.2.2.1),
        fun p => (p.2.2.1, p.1, p.2.2.2, p.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        ring
  have h20 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ x_2 x i_1 * Γ i_1 x_1 x_2 * (G i k * G x x_1)) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i k * G x x_1 * (Γ x_2 x i_1 * Γ i_1 x_2 x_1)) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2),
        fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hΓ p.2.2.2 p.2.1 p.2.2.1]
        ring
  have h21 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G k x * G x_1 x_2 * (Γ i x i_1 * Γ i_1 x_1 x_2)) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ i x i_1 * G i_1 k * G x_1 x_2 * Γ x x_1 x_2) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.2.2, p.2.1, p.2.2.1, p.1),
        fun p => (p.2.2.2, p.2.1, p.2.2.1, p.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hG k p.1, hΓ i p.1 p.2.2.2]
        ring
  have h22 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * G x_1 x_2 * (Γ k x i_1 * Γ i_1 x_1 x_2)) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ k x i_1 * G i i_1 * G x_1 x_2 * Γ x x_1 x_2) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.2.2, p.2.1, p.2.2.1, p.1),
        fun p => (p.2.2.2, p.2.1, p.2.2.1, p.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hΓ k p.1 p.2.2.2]
        ring
  have h23 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x_2 * (Γ x_1 x i_1 * G x i_1) * Γ k x_1 x_2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ k x i_1 * G i i_1 * G x_1 x_2 * Γ x x_1 x_2) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.1, p.1, p.2.2.2, p.2.2.1),
        fun p => (p.2.1, p.1, p.2.2.2, p.2.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        ring
  have h24 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G k x * G x_1 x_2 * (Γ i x_1 x_2 * Γ i_1 x i_1)) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ i x i_1 * G i_1 x * G k x_1 * Γ x_2 x_2 x_1) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.1, p.1, p.2.2.2, p.2.2.1),
        fun p => (p.2.1, p.1, p.2.2.2, p.2.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hG p.2.1 p.2.2.1, hΓ p.2.2.2 p.1 p.2.2.2]
        ring
  have h25 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ x_2 x i_1 * G i i_1 * G k x_1 * Γ x x_1 x_2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * G k x_1 * (Γ x_2 x i_1 * Γ i_1 x_2 x_1)) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.2.2, p.2.1, p.2.2.1, p.1),
        fun p => (p.2.2.2, p.2.1, p.2.2.1, p.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hΓ p.2.2.1 p.1 p.2.2.2, hΓ p.1 p.2.1 p.2.2.1]
        ring
  have h26 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x_2 * (Γ x_1 x i_1 * G k i_1) * Γ x x_1 x_2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * G k x_1 * (Γ x_2 x i_1 * Γ i_1 x_2 x_1)) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1),
        fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hΓ p.1 p.2.1 p.2.2.1]
        ring
  have h27 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ x_2 x i_1 * Γ i_1 x_1 x_2 * (G i x * G k x_1)) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * G k x_1 * (Γ x_2 x i_1 * Γ i_1 x_2 x_1)) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2),
        fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hΓ p.2.2.2 p.2.1 p.2.2.1]
        ring
  have h28 : (∑ x, ∑ x_1, ∑ x_2, ∑ x_3, G x x_1 * G x_2 x_3 * (Γ i x x_1 * Γ k x_2 x_3)) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ i x i_1 * G i_1 x * G x_1 x_2 * Γ k x_1 x_2) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.2.1, p.2.2.2, p.2.1),
        fun p => (p.1, p.2.2.2, p.2.1, p.2.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hG p.1 p.2.1]
        ring
  have h29 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * (Γ x_2 x i_1 * G x_1 i_1) * Γ k x_1 x_2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * (Γ x_1 x i_1 * G i_1 x_2) * Γ k x_1 x_2) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.2.1, p.2.1, p.2.2.2),
        fun p => (p.1, p.2.2.1, p.2.1, p.2.2.2), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hG p.2.1 p.2.2.2, hΓ k p.2.1 p.2.2.1]
        ring
  have h30 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ x_2 x i_1 * G i i_1 * G x x_1 * Γ k x_1 x_2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * (Γ x_1 x i_1 * G i_1 x_2) * Γ k x_1 x_2) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.2.2, p.2.2.1, p.2.1, p.1),
        fun p => (p.2.2.2, p.2.2.1, p.2.1, p.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hΓ p.2.2.1 p.1 p.2.2.2, hΓ k p.2.1 p.2.2.1]
        ring
  have h31 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x_2 * G x x_1 * (Γ k x i_1 * Γ i_1 x_1 x_2)) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * (Γ x_1 x i_1 * G i_1 x_2) * Γ k x_1 x_2) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1),
        fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hG p.1 p.2.1, hΓ k p.1 p.2.2.2, hΓ p.2.2.2 p.2.1 p.2.2.1]
        ring
  have h32 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x_2 * (Γ k x i_1 * G i_1 x_1) * Γ x x_1 x_2) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * (Γ x_1 x i_1 * G i_1 x_2) * Γ k x_1 x_2) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.2.1, p.1, p.2.2.2, p.2.1),
        fun p => (p.2.1, p.2.2.2, p.1, p.2.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hG p.2.2.2 p.2.1, hΓ p.1 p.2.1 p.2.2.1]
        ring
  have h33 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * G x_1 x_2 * (Γ k x_2 i_1 * Γ i_1 x x_1)) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G i x * (Γ x_1 x i_1 * G i_1 x_2) * Γ k x_1 x_2) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.2.2, p.2.2.1, p.2.1),
        fun p => (p.1, p.2.2.2, p.2.2.1, p.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hΓ k p.2.2.1 p.2.2.2]
        ring
  have h34 : (∑ x, ∑ x_1, ∑ x_2, ∑ x_3, G x x_1 * G x_2 x_3 * (Γ i x_2 x * Γ k x_3 x_1)) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ i x i_1 * G i_1 x_2 * G x x_1 * Γ k x_1 x_2) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.1, p.2.1, p.2.2.2, p.2.2.1),
        fun p => (p.1, p.2.1, p.2.2.2, p.2.2.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hΓ i p.2.2.1 p.1, hΓ k p.2.2.2 p.2.1]
        ring
  have h35 : (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, G k x * G x_1 x_2 * (Γ i x_2 i_1 * Γ i_1 x x_1)) =
      (1 : ℝ) * (∑ x, ∑ x_1, ∑ x_2, ∑ i_1, Γ i x i_1 * G i_1 x_2 * G k x_1 * Γ x x_1 x_2) :=
    sum4_reindex _ _ _
      ⟨fun p => (p.2.2.2, p.1, p.2.1, p.2.2.1),
        fun p => (p.2.1, p.2.2.1, p.2.2.2, p.1), fun _ => rfl, fun _ => rfl⟩ fun p => by
        dsimp only [Equiv.coe_fn_mk]
        rw [hG p.2.1 p.2.2.1, hΓ i p.2.2.1 p.2.2.2]
        ring
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
      h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
  ring

end ProjectAinos.SmoothGeometry
