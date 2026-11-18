/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # The Palatini identity as an identity between arrays

At a point, write `G^{bc}` for the inverse metric, `Γ^a_{bc}` for the Christoffel symbols, and
`P^a_{bc}` for their first variation, with `∂_e P^a_{bc}` and `∂_e G^{bc}` their derivatives.
If `∂_e G^{bc} = −Γ^b_{ed} G^{dc} − Γ^c_{ed} G^{bd}` (metric compatibility), the contraction of the
first variation of the Ricci tensor,

`G^{bc} δRic_{bc}`, with `δRic_{bc} = ∂_a P^a_{bc} − ∂_b P^a_{ac} + P^a_{ad} Γ^d_{bc}
+ Γ^a_{ad} P^d_{bc} − P^a_{bd} Γ^d_{ac} − Γ^a_{bd} P^d_{ac}`,

is `Γ^e_{ea} V^a + ∂_a V^a` for `V^a = G^{bc} P^a_{bc} − G^{ab} P^c_{cb}`
(`palatini_algebra`). With `∂_a ρ = ρ Γ^e_{ea}` for the density, this says
`ρ G^{bc} δRic_{bc} = ∂_a (ρ V^a)`: the variation of the Ricci tensor contributes a divergence.
-/

@[expose] public section

open Finset

namespace ProjectAinos.SmoothGeometry

/-- **The Palatini identity for arrays.** -/
theorem palatini_algebra {n : ℕ} (G : Fin n → Fin n → ℝ)
    (Γ P : Fin n → Fin n → Fin n → ℝ) (DP : Fin n → Fin n → Fin n → Fin n → ℝ)
    (DG : Fin n → Fin n → Fin n → ℝ)
    (hG : ∀ a b, G a b = G b a) (hΓ : ∀ a b c, Γ a b c = Γ a c b)
    (hP : ∀ a b c, P a b c = P a c b)
    (hDG : ∀ e b c, DG e b c = -∑ d, (Γ b e d * G d c + Γ c e d * G b d)) :
    ∑ b, ∑ c, G b c * (∑ a, (DP a a b c - DP b a a c +
        ∑ d, ((P a a d * Γ d b c + Γ a a d * P d b c) -
          (P a b d * Γ d a c + Γ a b d * P d a c)))) =
      ∑ a, ((∑ e, Γ e e a) * (∑ b, ∑ c, G b c * P a b c - ∑ b, G a b * ∑ c, P c c b) +
        (∑ b, ∑ c, (DG a b c * P a b c + G b c * DP a a b c) -
          ∑ b, (DG a a b * ∑ c, P c c b + G a b * ∑ c, DP a c c b))) := by
  -- expansion of the left side
  have hL : ∑ b, ∑ c, G b c * (∑ a, (DP a a b c - DP b a a c +
        ∑ d, ((P a a d * Γ d b c + Γ a a d * P d b c) -
          (P a b d * Γ d a c + Γ a b d * P d a c)))) =
      (∑ b, ∑ c, G b c * ∑ a, DP a a b c) - (∑ b, ∑ c, G b c * ∑ a, DP b a a c) +
        ((∑ b, ∑ c, G b c * ∑ a, ∑ d, P a a d * Γ d b c) +
          (∑ b, ∑ c, G b c * ∑ a, ∑ d, Γ a a d * P d b c)) -
        ((∑ b, ∑ c, G b c * ∑ a, ∑ d, P a b d * Γ d a c) +
          (∑ b, ∑ c, G b c * ∑ a, ∑ d, Γ a b d * P d a c)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, mul_sub]
    ring
  -- expansion of the right side
  have hR : ∑ a, ((∑ e, Γ e e a) * (∑ b, ∑ c, G b c * P a b c - ∑ b, G a b * ∑ c, P c c b) +
        (∑ b, ∑ c, (DG a b c * P a b c + G b c * DP a a b c) -
          ∑ b, (DG a a b * ∑ c, P c c b + G a b * ∑ c, DP a c c b))) =
      (∑ a, (∑ e, Γ e e a) * ∑ b, ∑ c, G b c * P a b c) -
        (∑ a, (∑ e, Γ e e a) * ∑ b, G a b * ∑ c, P c c b) -
        (∑ a, ∑ b, ∑ c, (∑ d, (Γ b a d * G d c + Γ c a d * G b d)) * P a b c) +
        (∑ a, ∑ b, ∑ c, G b c * DP a a b c) +
        (∑ a, ∑ b, (∑ d, (Γ a a d * G d b + Γ b a d * G a d)) * ∑ c, P c c b) -
        (∑ a, ∑ b, G a b * ∑ c, DP a c c b) := by
    simp only [hDG, neg_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_sub,
      Finset.sum_neg_distrib]
    ring
  -- the terms with derivatives of δΓ
  have hD1 : ∑ b, ∑ c, G b c * ∑ a, DP a a b c = ∑ a, ∑ b, ∑ c, G b c * DP a a b c := by
    simp only [Finset.mul_sum]
    calc ∑ b, ∑ c, ∑ a, G b c * DP a a b c = ∑ b, ∑ a, ∑ c, G b c * DP a a b c :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  have hD2 : ∑ b, ∑ c, G b c * ∑ a, DP b a a c = ∑ a, ∑ b, G a b * ∑ c, DP a c c b := rfl
  -- the trace term
  have hT2 : ∑ b, ∑ c, G b c * ∑ a, ∑ d, Γ a a d * P d b c =
      ∑ a, (∑ e, Γ e e a) * ∑ b, ∑ c, G b c * P a b c := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    calc ∑ b, ∑ c, ∑ a, ∑ d, G b c * (Γ a a d * P d b c) =
          ∑ b, ∑ c, ∑ d, ∑ a, G b c * (Γ a a d * P d b c) :=
          Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
      _ = ∑ b, ∑ d, ∑ c, ∑ a, G b c * (Γ a a d * P d b c) :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ d, ∑ b, ∑ c, ∑ a, G b c * (Γ a a d * P d b c) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by ring
  -- the term that pairs with the trace of `δΓ`
  have hT1 : ∑ b, ∑ c, G b c * ∑ a, ∑ d, P a a d * Γ d b c =
      ∑ a, ∑ b, (∑ d, Γ b a d * G a d) * ∑ c, P c c b := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    calc ∑ b, ∑ c, ∑ a, ∑ d, G b c * (P a a d * Γ d b c) =
          ∑ b, ∑ c, ∑ d, ∑ a, G b c * (P a a d * Γ d b c) :=
          Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
      _ = ∑ b, ∑ d, ∑ c, ∑ a, G b c * (P a a d * Γ d b c) :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ b, ∑ d, ∑ a, ∑ c, G b c * (P a a d * Γ d b c) :=
          Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
  -- the two terms with the bracket structure
  set R3a := ∑ a, ∑ b, ∑ c, ∑ d, Γ b a d * G d c * P a b c
  have hT3 : ∑ b, ∑ c, G b c * ∑ a, ∑ d, P a b d * Γ d a c = R3a := by
    simp only [R3a, Finset.mul_sum]
    calc ∑ b, ∑ c, ∑ a, ∑ d, G b c * (P a b d * Γ d a c) =
          ∑ b, ∑ a, ∑ c, ∑ d, G b c * (P a b d * Γ d a c) :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ c, ∑ d, G b c * (P a b d * Γ d a c) := Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ d, ∑ c, G b c * (P a b d * Γ d a c) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ a, ∑ d, ∑ b, ∑ c, G b c * (P a b d * Γ d a c) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ =>
          Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by
            rw [hG b c, hP a b d]; ring
  have hT4 : ∑ b, ∑ c, G b c * ∑ a, ∑ d, Γ a b d * P d a c = R3a := by
    simp only [R3a, Finset.mul_sum]
    calc ∑ b, ∑ c, ∑ a, ∑ d, G b c * (Γ a b d * P d a c) =
          ∑ b, ∑ c, ∑ d, ∑ a, G b c * (Γ a b d * P d a c) :=
          Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
      _ = ∑ b, ∑ d, ∑ c, ∑ a, G b c * (Γ a b d * P d a c) :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ d, ∑ b, ∑ c, ∑ a, G b c * (Γ a b d * P d a c) := Finset.sum_comm
      _ = ∑ d, ∑ b, ∑ a, ∑ c, G b c * (Γ a b d * P d a c) :=
          Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ d, ∑ a, ∑ b, ∑ c, G b c * (Γ a b d * P d a c) :=
          Finset.sum_congr rfl fun d _ => Finset.sum_comm
      _ = ∑ d, ∑ a, ∑ c, ∑ b, G b c * (Γ a b d * P d a c) :=
          Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by
            rw [hΓ a b d]; ring
  have hR3 : ∑ a, ∑ b, ∑ c, (∑ d, (Γ b a d * G d c + Γ c a d * G b d)) * P a b c =
      2 * R3a := by
    have hswap : ∑ a, ∑ b, ∑ c, ∑ d, Γ c a d * G b d * P a b c = R3a := by
      simp only [R3a]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
        Finset.sum_congr rfl fun e _ => by rw [hG c e, hP a c b]
    simp only [Finset.sum_mul, add_mul, Finset.sum_add_distrib, hswap, R3a]
    ring
  -- the trace of `δΓ` against the inverse metric
  have hR2 : ∑ a, (∑ e, Γ e e a) * ∑ b, G a b * ∑ c, P c c b =
      ∑ a, ∑ b, (∑ d, Γ a a d * G d b) * ∑ c, P c c b := by
    set X : Fin n → ℝ := fun b => ∑ c, P c c b with hX
    have hl : ∑ a, (∑ e, Γ e e a) * ∑ b, G a b * X b =
        ∑ a, ∑ e, ∑ b, Γ e e a * (G a b * X b) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    have hr : ∑ a, ∑ b, (∑ d, Γ a a d * G d b) * X b = ∑ a, ∑ b, ∑ d, Γ a a d * G d b * X b := by
      simp only [Finset.sum_mul]
    change ∑ a, (∑ e, Γ e e a) * ∑ b, G a b * X b = ∑ a, ∑ b, (∑ d, Γ a a d * G d b) * X b
    rw [hl, hr]
    calc ∑ a, ∑ e, ∑ b, Γ e e a * (G a b * X b) = ∑ e, ∑ a, ∑ b, Γ e e a * (G a b * X b) :=
          Finset.sum_comm
      _ = ∑ e, ∑ b, ∑ a, Γ e e a * (G a b * X b) :=
          Finset.sum_congr rfl fun e _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun a _ => by ring
  have hR4 : ∑ a, ∑ b, (∑ d, (Γ a a d * G d b + Γ b a d * G a d)) * ∑ c, P c c b =
      ∑ a, ∑ b, (∑ d, Γ a a d * G d b) * ∑ c, P c c b +
        ∑ a, ∑ b, (∑ d, Γ b a d * G a d) * ∑ c, P c c b := by
    simp only [Finset.sum_add_distrib, add_mul]
  rw [hL, hR, hD1, hD2, hT2, hT1, hT3, hT4, hR3, hR2, hR4]
  ring

end ProjectAinos.SmoothGeometry
