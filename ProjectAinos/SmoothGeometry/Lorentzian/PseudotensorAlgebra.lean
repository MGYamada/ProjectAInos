/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The algebra of the Landau–Lifshitz superpotential

At a point where the first derivatives of a metric vanish, the second derivatives of
`λ^{iklm} = (−g)(g^{ik} g^{lm} − g^{il} g^{km})` and of the Einstein tensor are linear in the
array `S_{ab,cd} = ∂_c ∂_d g_{ab}`, symmetric in `a, b` and in `c, d`. With an inverse metric
`G`, `∂_l ∂_m (−g) = (−g) G^{cd} S_{cd,lm}` and `∂_l ∂_m G^{pq} = −G^{pa} G^{qe} S_{ae,lm}`, and
`∂_m Γ^c_{ab} = ½ G^{cd}(S_{bd,ma} + S_{da,mb} − S_{ab,md})`. `pseudotensor_algebra` is the
identity `Σ_{lm} ∂_l ∂_m λ^{iklm} = 2 (−g) G^{ik}` in these terms (Landau–Lifshitz, (96.5)).
-/

@[expose] public section

open Finset

namespace ProjectAinos.SmoothGeometry

/-- **The identity of the superpotential for arrays.** -/
theorem pseudotensor_algebra {n : ℕ} (G : Fin n → Fin n → ℝ)
    (S : Fin n → Fin n → Fin n → Fin n → ℝ) (hG : ∀ a b, G a b = G b a)
    (hS₁ : ∀ a b c e, S a b c e = S b a c e) (hS₂ : ∀ a b c e, S a b c e = S a b e c)
    (i k : Fin n) :
    ∑ l, ∑ m, ((∑ c, ∑ d, G c d * S c d l m) * (G i k * G l m - G i l * G k m) +
        (-∑ a, ∑ e, G i a * G k e * S a e l m) * G l m +
        G i k * (-∑ a, ∑ e, G l a * G m e * S a e l m) -
        (-∑ a, ∑ e, G i a * G l e * S a e l m) * G k m -
        G i l * (-∑ a, ∑ e, G k a * G m e * S a e l m)) =
      2 * ∑ a, ∑ b, G i a * G k b *
          (∑ c, ∑ d, G c d * (S b d c a + S d a c b - S a b c d - S c d a b) / 2) -
        G i k * ∑ a, ∑ b, G a b *
          (∑ c, ∑ d, G c d * (S b d c a + S d a c b - S a b c d - S c d a b) / 2) := by
  -- the four-fold sums in the normal form `Σ_{lmae} f · S_{ae,lm}`
  set T1 := ∑ l, ∑ m, ∑ a, ∑ e, G a e * G l m * S a e l m with hT1
  set T2 := ∑ l, ∑ m, ∑ a, ∑ e, G l a * G m e * S a e l m with hT2
  set X1 := ∑ l, ∑ m, ∑ a, ∑ e, G a e * G i l * G k m * S a e l m with hX1
  set X2 := ∑ l, ∑ m, ∑ a, ∑ e, G i a * G k e * G l m * S a e l m with hX2
  set X3 := ∑ l, ∑ m, ∑ a, ∑ e, G i a * G l e * G k m * S a e l m with hX3
  set X4 := ∑ l, ∑ m, ∑ a, ∑ e, G i l * G k a * G m e * S a e l m with hX4
  -- the left side
  have hL : ∑ l, ∑ m, ((∑ c, ∑ d, G c d * S c d l m) * (G i k * G l m - G i l * G k m) +
        (-∑ a, ∑ e, G i a * G k e * S a e l m) * G l m +
        G i k * (-∑ a, ∑ e, G l a * G m e * S a e l m) -
        (-∑ a, ∑ e, G i a * G l e * S a e l m) * G k m -
        G i l * (-∑ a, ∑ e, G k a * G m e * S a e l m)) =
      G i k * T1 - X1 - X2 - G i k * T2 + X3 + X4 := by
    simp only [hT1, hT2, hX1, hX2, hX3, hX4, Finset.mul_sum, Finset.sum_mul, mul_sub,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, neg_mul, mul_neg]
    have e1 : ∑ l, ∑ m, ∑ c, ∑ d, G c d * S c d l m * (G i k * G l m) =
        ∑ l, ∑ m, ∑ a, ∑ e, G i k * (G a e * G l m * S a e l m) :=
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
    have e2 : ∑ l, ∑ m, ∑ c, ∑ d, G c d * S c d l m * (G i l * G k m) = X1 :=
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
    have e3 : ∑ l, ∑ m, ∑ a, ∑ e, G i a * G k e * S a e l m * G l m = X2 :=
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
    have e4 : ∑ l, ∑ m, ∑ a, ∑ e, G i k * (G l a * G m e * S a e l m) =
        ∑ l, ∑ m, ∑ a, ∑ e, G i k * (G l a * G m e * S a e l m) := rfl
    have e5 : ∑ l, ∑ m, ∑ a, ∑ e, G i a * G l e * S a e l m * G k m = X3 :=
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
    have e6 : ∑ l, ∑ m, ∑ a, ∑ e, G i l * (G k a * G m e * S a e l m) = X4 :=
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
    rw [e1, e2, e3, e5, e6]
    simp only [← Finset.mul_sum]
    ring
  -- the right side, term by term
  have y1 : ∑ a, ∑ b, ∑ c, ∑ d, G i a * G k b * G c d * S b d c a = X4 := by
    rw [hX4]
    calc ∑ a, ∑ b, ∑ c, ∑ d, G i a * G k b * G c d * S b d c a =
          ∑ a, ∑ c, ∑ b, ∑ d, G i a * G k b * G c d * S b d c a :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by
            rw [hS₂ a e m l]
  have y2 : ∑ a, ∑ b, ∑ c, ∑ d, G i a * G k b * G c d * S d a c b = X3 := by
    rw [hX3]
    calc ∑ a, ∑ b, ∑ c, ∑ d, G i a * G k b * G c d * S d a c b =
          ∑ b, ∑ a, ∑ c, ∑ d, G i a * G k b * G c d * S d a c b := Finset.sum_comm
      _ = ∑ b, ∑ c, ∑ a, ∑ d, G i a * G k b * G c d * S d a c b :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ c, ∑ b, ∑ a, ∑ d, G i a * G k b * G c d * S d a c b := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by
            rw [hS₁ e a l m]; ring
  have y3 : ∑ a, ∑ b, ∑ c, ∑ d, G i a * G k b * G c d * S a b c d = X2 := by
    rw [hX2]
    calc ∑ a, ∑ b, ∑ c, ∑ d, G i a * G k b * G c d * S a b c d =
          ∑ a, ∑ c, ∑ b, ∑ d, G i a * G k b * G c d * S a b c d :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ c, ∑ a, ∑ b, ∑ d, G i a * G k b * G c d * S a b c d := Finset.sum_comm
      _ = ∑ c, ∑ a, ∑ d, ∑ b, G i a * G k b * G c d * S a b c d :=
          Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ c, ∑ d, ∑ a, ∑ b, G i a * G k b * G c d * S a b c d :=
          Finset.sum_congr rfl fun c _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by ring
  have y4 : ∑ a, ∑ b, ∑ c, ∑ d, G i a * G k b * G c d * S c d a b = X1 := by
    rw [hX1]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by ring
  have z1 : ∑ a, ∑ b, ∑ c, ∑ d, G a b * G c d * S b d c a = T2 := by
    rw [hT2]
    calc ∑ a, ∑ b, ∑ c, ∑ d, G a b * G c d * S b d c a =
          ∑ a, ∑ c, ∑ b, ∑ d, G a b * G c d * S b d c a :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by
            rw [hS₂ a e m l]
  have z2 : ∑ a, ∑ b, ∑ c, ∑ d, G a b * G c d * S d a c b = T2 := by
    rw [hT2]
    calc ∑ a, ∑ b, ∑ c, ∑ d, G a b * G c d * S d a c b =
          ∑ b, ∑ a, ∑ c, ∑ d, G a b * G c d * S d a c b := Finset.sum_comm
      _ = ∑ b, ∑ c, ∑ a, ∑ d, G a b * G c d * S d a c b :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ c, ∑ b, ∑ a, ∑ d, G a b * G c d * S d a c b := Finset.sum_comm
      _ = ∑ c, ∑ b, ∑ d, ∑ a, G a b * G c d * S d a c b :=
          Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by
            rw [hG e m]; ring
  have z3 : ∑ a, ∑ b, ∑ c, ∑ d, G a b * G c d * S a b c d = T1 := by
    rw [hT1]
    calc ∑ a, ∑ b, ∑ c, ∑ d, G a b * G c d * S a b c d =
          ∑ a, ∑ c, ∑ b, ∑ d, G a b * G c d * S a b c d :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ c, ∑ a, ∑ b, ∑ d, G a b * G c d * S a b c d := Finset.sum_comm
      _ = ∑ c, ∑ a, ∑ d, ∑ b, G a b * G c d * S a b c d :=
          Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ c, ∑ d, ∑ a, ∑ b, G a b * G c d * S a b c d :=
          Finset.sum_congr rfl fun c _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by ring
  have z4 : ∑ a, ∑ b, ∑ c, ∑ d, G a b * G c d * S c d a b = T1 := by
    rw [hT1]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by ring
  have hR : 2 * ∑ a, ∑ b, G i a * G k b *
          (∑ c, ∑ d, G c d * (S b d c a + S d a c b - S a b c d - S c d a b) / 2) -
        G i k * ∑ a, ∑ b, G a b *
          (∑ c, ∑ d, G c d * (S b d c a + S d a c b - S a b c d - S c d a b) / 2) =
      G i k * T1 - X1 - X2 - G i k * T2 + X3 + X4 := by
    have hexp : 2 * ∑ a, ∑ b, G i a * G k b *
          (∑ c, ∑ d, G c d * (S b d c a + S d a c b - S a b c d - S c d a b) / 2) -
        G i k * ∑ a, ∑ b, G a b *
          (∑ c, ∑ d, G c d * (S b d c a + S d a c b - S a b c d - S c d a b) / 2) =
        (∑ a, ∑ b, ∑ c, ∑ d, G i a * G k b * G c d * S b d c a +
          ∑ a, ∑ b, ∑ c, ∑ d, G i a * G k b * G c d * S d a c b -
          ∑ a, ∑ b, ∑ c, ∑ d, G i a * G k b * G c d * S a b c d -
          ∑ a, ∑ b, ∑ c, ∑ d, G i a * G k b * G c d * S c d a b) -
        G i k * ((∑ a, ∑ b, ∑ c, ∑ d, G a b * G c d * S b d c a +
          ∑ a, ∑ b, ∑ c, ∑ d, G a b * G c d * S d a c b -
          ∑ a, ∑ b, ∑ c, ∑ d, G a b * G c d * S a b c d -
          ∑ a, ∑ b, ∑ c, ∑ d, G a b * G c d * S c d a b) / 2) := by
      simp only [Finset.mul_sum, Finset.sum_div, mul_add, mul_sub, add_div, sub_div,
        Finset.sum_add_distrib, Finset.sum_sub_distrib]
      congr 1
      · simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
        ring
      · simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
        ring
    rw [hexp, y1, y2, y3, y4, z1, z2, z3, z4]
    ring
  rw [hL, hR]

/-- The second derivative of the inverse at a critical point:
`−(∂_lΓ^b_{me} G^{ec} + ∂_lΓ^c_{me} G^{be}) = −G^{ba} G^{ce} S_{ae,lm}`. -/
theorem inverse_second_algebra {n : ℕ} (G : Fin n → Fin n → ℝ)
    (S : Fin n → Fin n → Fin n → Fin n → ℝ) (hG : ∀ a b, G a b = G b a)
    (hS₁ : ∀ a b c e, S a b c e = S b a c e) (b c l m : Fin n) :
    -∑ e, ((∑ a, G b a * (S e a l m + S a m l e - S m e l a) / 2) * G e c +
        (∑ a, G c a * (S e a l m + S a m l e - S m e l a) / 2) * G b e) =
      -∑ a, ∑ e, G b a * G c e * S a e l m := by
  have h1 : ∑ e, (∑ a, G b a * (S e a l m + S a m l e - S m e l a) / 2) * G e c =
      ∑ a, ∑ e, G b a * G c e * ((S e a l m + S a m l e - S m e l a) / 2) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by rw [hG e c]; ring
  have h2 : ∑ e, (∑ a, G c a * (S e a l m + S a m l e - S m e l a) / 2) * G b e =
      ∑ a, ∑ e, G b a * G c e * ((S a e l m + S e m l a - S m a l e) / 2) := by
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by ring
  rw [Finset.sum_add_distrib, h1, h2, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hS₁ e a l m, hS₁ a m l e, hS₁ m e l a]
  ring

/-- The second derivative of the density at a critical point: the contracted derivative of the
Christoffel symbols is `½ G^{cd} S_{cd,lm}`. -/
theorem density_second_algebra {n : ℕ} (G : Fin n → Fin n → ℝ)
    (S : Fin n → Fin n → Fin n → Fin n → ℝ) (hG : ∀ a b, G a b = G b a)
    (hS₁ : ∀ a b c e, S a b c e = S b a c e) (l m : Fin n) :
    ∑ c, ∑ d, G c d * (S m d l c + S d c l m - S c m l d) / 2 =
      (∑ c, ∑ d, G c d * S c d l m) / 2 := by
  have hc : ∑ c, ∑ d, G c d * S c m l d = ∑ c, ∑ d, G c d * S m d l c := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by
      rw [hG d c, hS₁ d m l c]
  have hsplit : ∑ c, ∑ d, G c d * (S m d l c + S d c l m - S c m l d) / 2 =
      (∑ c, ∑ d, G c d * S m d l c + ∑ c, ∑ d, G c d * S d c l m -
        ∑ c, ∑ d, G c d * S c m l d) / 2 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hsplit, hc]
  congr 1
  rw [add_sub_cancel_left]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by rw [hS₁ d c l m]

/-- The Ricci tensor at a critical point in the second derivatives of the coefficients. -/
theorem ricci_algebra {n : ℕ} (G : Fin n → Fin n → ℝ)
    (S : Fin n → Fin n → Fin n → Fin n → ℝ) (hG : ∀ a b, G a b = G b a)
    (hS₁ : ∀ a b c e, S a b c e = S b a c e) (hS₂ : ∀ a b c e, S a b c e = S a b e c)
    (a b : Fin n) :
    ∑ c, (∑ d, G c d * (S b d c a + S d a c b - S a b c d) / 2 -
        ∑ d, G c d * (S b d a c + S d c a b - S c b a d) / 2) =
      ∑ c, ∑ d, G c d * (S b d c a + S d a c b - S a b c d - S c d a b) / 2 := by
  have hc : ∑ c, ∑ d, G c d * S c b a d = ∑ c, ∑ d, G c d * S b d a c := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by
      rw [hG d c, hS₁ d b a c]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  have hpt : ∀ c, (∑ d, G c d * (S b d c a + S d a c b - S a b c d) / 2 -
        ∑ d, G c d * (S b d a c + S d c a b - S c b a d) / 2) -
      ∑ d, G c d * (S b d c a + S d a c b - S a b c d - S c d a b) / 2 =
      ∑ d, (G c d * S c b a d / 2 - G c d * S b d a c / 2) := by
    intro c
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hS₂ b d c a, hS₁ d c a b]
    ring
  rw [Finset.sum_congr rfl fun c _ => hpt c]
  simp only [Finset.sum_sub_distrib, ← Finset.sum_div, hc, sub_self]

end ProjectAinos.SmoothGeometry
