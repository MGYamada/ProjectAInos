/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.GeneralRelativity.BKL

/-! Public consumers of the oscillating regime (Landau–Lifshitz §118): the bounce of the Kasner
exponents with the maps `u ↦ u − 1` and `u ↦ 1/(u − 1)`, the vacuum Bianchi II metric with the
lapse `abc` and its reduction to the one-wall system, the exact one-bounce solution, and the
transition of its rates between two Kasner epochs with explicit exponential rates. Default
elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/

noncomputable section

section BKL

open ContinuousLinearMap Set TopologicalSpace Filter

open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.BKL

open Kasner (kasnerExponents kasnerDenom_pos)

example (p : Fin 3 → ℝ) :
    Fin 3 → ℝ :=
  bounce p

example {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) (hp : 1 + 2 * p 0 ≠ 0) :
    ∑ α, bounce p α = 1 :=
  sum_bounce h1 hp

example {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1) (hp : 1 + 2 * p 0 ≠ 0) :
    ∑ α, bounce p α ^ 2 = 1 :=
  sum_sq_bounce h1 h2 hp

example (u : ℝ) :
    1 + 2 * kasnerExponents u 0 = (1 + (u - 1) + (u - 1) ^ 2) / (1 + u + u ^ 2) :=
  one_add_two_mul_kasnerExponents u

example (u : ℝ) :
    bounce (kasnerExponents u) =
      ![kasnerExponents (u - 1) 1, kasnerExponents (u - 1) 0, kasnerExponents (u - 1) 2] :=
  bounce_kasnerExponents u

example {u : ℝ} (hu : u ≠ 1) :
    bounce (kasnerExponents u) =
      ![kasnerExponents (u - 1)⁻¹ 2, kasnerExponents (u - 1)⁻¹ 0, kasnerExponents (u - 1)⁻¹ 1] :=
  bounce_kasnerExponents_era hu

example (u : ℝ) :
    ℝ :=
  bklMap u

example {u : ℝ} (hu : 2 ≤ u) :
    bklMap u = u - 1 :=
  bklMap_of_two_le hu

example {u : ℝ} (hu : u < 2) :
    bklMap u = (u - 1)⁻¹ :=
  bklMap_of_lt_two hu

example {u : ℝ} (hu : 1 < u) :
    1 ≤ bklMap u :=
  one_le_bklMap hu

example {u : ℝ} (hu : u ≠ 1) :
    ∃ σ : Equiv.Perm (Fin 3), bounce (kasnerExponents u) = kasnerExponents (bklMap u) ∘ σ :=
  exists_bounce_eq_comp hu

example {u : ℝ} (hu : 0 < u) :
    kasnerExponents u 0 < 0 ∧ 0 < kasnerExponents (u - 1) 1 :=
  kasnerExponents_zero_neg_and_pos hu

example {u : ℝ} (hu : 1 ≤ u) :
    kasnerExponents (u - 1) 0 ≤ 0 :=
  kasnerExponents_sub_one_zero_nonpos hu

namespace TypeII

open SmoothGeometry CoordinateMetric LorentzMetric

local notation "E" => MinkowskiModel 3

namespace Data

variable (D : Data)

example :
    Fin 3 → ℝ → ℝ :=
  w D

example :
    D.w 0 = D.α :=
  w_zero D

example :
    D.w 1 = D.β :=
  w_one D

example :
    D.w 2 = D.γ :=
  w_two D

example (k : Fin 3) :
    ContDiffOn ℝ ∞ (D.w k) D.I :=
  contDiffOn_w D k

example (τ : ℝ) :
    ℝ :=
  a D τ

example (τ : ℝ) :
    ℝ :=
  b D τ

example (τ : ℝ) :
    ℝ :=
  c D τ

example (τ : ℝ) :
    ℝ :=
  lapse D τ

example (τ : ℝ) :
    ℝ :=
  expansion D τ

example (τ : ℝ) :
    0 < D.a τ :=
  a_pos D τ

example (τ : ℝ) :
    0 < D.b τ :=
  b_pos D τ

example (τ : ℝ) :
    0 < D.c τ :=
  c_pos D τ

example (τ : ℝ) :
    0 < D.lapse τ :=
  lapse_pos D τ

variable {D}

example (k : Fin 3) {τ : ℝ} (hτ : τ ∈ D.I) :
    HasDerivAt (D.w k) (deriv (D.w k) τ) τ :=
  hasDerivAt_w k hτ

example (k : Fin 3) {τ : ℝ} (hτ : τ ∈ D.I) :
    HasDerivAt (deriv (D.w k)) (deriv (deriv (D.w k)) τ) τ :=
  hasDerivAt_deriv_w k hτ

example {τ : ℝ} (hτ : τ ∈ D.I) :
    HasDerivAt D.a (D.a τ * deriv D.α τ) τ :=
  hasDerivAt_a hτ

example {τ : ℝ} (hτ : τ ∈ D.I) :
    HasDerivAt D.b (D.b τ * deriv D.β τ) τ :=
  hasDerivAt_b hτ

example {τ : ℝ} (hτ : τ ∈ D.I) :
    HasDerivAt D.c (D.c τ * deriv D.γ τ) τ :=
  hasDerivAt_c hτ

example {τ : ℝ} (hτ : τ ∈ D.I) :
    HasDerivAt D.lapse (D.lapse τ * D.expansion τ) τ :=
  hasDerivAt_lapse hτ

variable (D)

example :
    ContDiffOn ℝ ∞ D.a D.I :=
  contDiffOn_a D

example :
    ContDiffOn ℝ ∞ D.b D.I :=
  contDiffOn_b D

example :
    ContDiffOn ℝ ∞ D.c D.I :=
  contDiffOn_c D

example :
    ContDiffOn ℝ ∞ D.lapse D.I :=
  contDiffOn_lapse D

example :
    Opens E :=
  domain D

variable {D}

example {x : E} (hx : x ∈ D.domain) :
    x 0 ∈ D.I :=
  time_mem hx

example {τ : ℝ} (hτ : τ ∈ D.I) :
    FLRW.timeAxis τ ∈ D.domain :=
  timeAxis_mem hτ

example {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f D.I) :
    ContDiffOn ℝ ∞ (fun z : E => f (z 0)) D.domain :=
  contDiffOn_time hf

variable (D)

example (x : E) :
    E →L[ℝ] ℝ :=
  omega x

example (x : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  form D x

example (x v u : E) :
    D.form x v u = -(D.lapse (x 0) ^ 2) * (v 0 * u 0) +
      D.a (x 0) ^ 2 * ((v 1 - x 3 * v 2) * (u 1 - x 3 * u 2)) + D.b (x 0) ^ 2 * (v 2 * u 2) +
      D.c (x 0) ^ 2 * (v 3 * u 3) :=
  form_apply D x v u

example (x v u : E) :
    D.form x v u = D.form x u v :=
  form_symm D x v u

example :
    ContDiffOn ℝ ∞ D.form D.domain :=
  contDiffOn_form D

example :
    CoordinateMetric .timeNegative 3 D.domain :=
  metric D

example :
    (metric D).form = D.form :=
  metric_form D

example (k : Fin 4) :
    E :=
  unit k

example (k j : Fin 4) :
    unit k j = if j = k then 1 else 0 :=
  unit_apply k j

example (p : Fin 4) (x : E) :
    E :=
  frameField D p x

example (p : Fin 4) (x : E) :
    D.frameField p x 0 = if p = 0 then (D.lapse (x 0))⁻¹ else 0 :=
  frameField_apply_zero D p x

example (x : E) (p q : Fin 4) :
    D.form x (D.frameField p x) (D.frameField q x) =
      if p = q then lorentzSign .timeNegative p else 0 :=
  form_frameField D x p q

example (p : Fin 4) :
    ContDiffOn ℝ ∞ (D.frameField p) D.domain :=
  contDiffOn_frameField D p

variable {D}

example (p : Fin 4) (y v : E) :
    E :=
  frameDeriv D p y v

example {y : E} (hy : y ∈ D.domain) (v : E) :
    fderiv ℝ (D.frameField 0) y v = D.frameDeriv 0 y v :=
  fderiv_frameField_zero hy v

example {y : E} (hy : y ∈ D.domain) (v : E) :
    fderiv ℝ (D.frameField 1) y v = D.frameDeriv 1 y v :=
  fderiv_frameField_one hy v

example {y : E} (hy : y ∈ D.domain) (v : E) :
    fderiv ℝ (D.frameField 2) y v = D.frameDeriv 2 y v :=
  fderiv_frameField_two hy v

example {y : E} (hy : y ∈ D.domain) (v : E) :
    fderiv ℝ (D.frameField 3) y v = D.frameDeriv 3 y v :=
  fderiv_frameField_three hy v

example {y : E} (hy : y ∈ D.domain) (p : Fin 4) (v : E) :
    fderiv ℝ (D.frameField p) y v = D.frameDeriv p y v :=
  fderiv_frameField hy p v

variable (D)

example (k : Fin 3) (τ : ℝ) :
    ℝ :=
  rate D k τ

example (k : Fin 3) (τ : ℝ) :
    ℝ :=
  rateDeriv D k τ

example (τ : ℝ) :
    ℝ :=
  wall D τ

example (τ : ℝ) :
    ℝ :=
  wallDeriv D τ

example (k i j : Fin 3) :
    ℝ :=
  wallSign k i j

example (τ : ℝ) (p q r : Fin 4) :
    ℝ :=
  lam D τ p q r

example (τ : ℝ) (p q r : Fin 4) :
    ℝ :=
  lamDeriv D τ p q r

variable {D}

example {y : E} (hy : y ∈ D.domain) (p q r : Fin 4) :
    D.form y (D.frameField p y) (lieBracketOf (D.frameField q) (D.frameField r) y) =
      D.lam (y 0) p q r :=
  commutator_frame hy p q r

example (k : Fin 3) {τ : ℝ} (hτ : τ ∈ D.I) :
    HasDerivAt (D.rate k) (D.rateDeriv k τ) τ :=
  hasDerivAt_rate k hτ

example {τ : ℝ} (hτ : τ ∈ D.I) :
    HasDerivAt D.wall (D.wallDeriv τ) τ :=
  hasDerivAt_wall hτ

example {τ : ℝ} (hτ : τ ∈ D.I) (p q r : Fin 4) :
    HasDerivAt (fun s => D.lam s p q r) (D.lamDeriv τ p q r) τ :=
  hasDerivAt_lam hτ p q r

variable (D)

example (k : Fin 3) :
    ContDiffOn ℝ ∞ (D.rate k) D.I :=
  contDiffOn_rate D k

example :
    ContDiffOn ℝ ∞ D.wall D.I :=
  contDiffOn_wall D

example (p q r : Fin 4) :
    ContDiffOn ℝ ∞ (fun τ => D.lam τ p q r) D.I :=
  contDiffOn_lam D p q r

example (τ : ℝ) (p q r : Fin 4) :
    ℝ :=
  rot D τ p q r

example (τ : ℝ) (p q r : Fin 4) :
    ℝ :=
  rotDeriv D τ p q r

example (τ : ℝ) (b k : Fin 4) :
    ℝ :=
  frameRicci D τ b k

example (y : D.domain) :
    (metric D).toLorentzMetric.OrthonormalFrame (univ : Set D.domain) :=
  frame D y

variable {D}

example {τ : ℝ} (hτ : τ ∈ D.I) (p q r : Fin 4) :
    HasDerivAt (fun s => D.rot s p q r) (D.rotDeriv τ p q r) τ :=
  hasDerivAt_rot hτ p q r

example {z : E} (hz : z ∈ D.domain) (p q r : Fin 4) (v : E) :
    fderiv ℝ (rotationOf (fun p q r (y : E) => D.lam (y 0) p q r) p q r) z v =
      D.rotDeriv (z 0) p q r * v 0 :=
  fderiv_rotationOf hz p q r v

example (y : D.domain) (b k : Fin 4) :
    (metric D).toLorentzMetric.ricci y ((frame D y).field b y) ((frame D y).field k y) =
      D.frameRicci ((y : E) 0) b k :=
  ricci_frame y b k

example :
    (∀ y : D.domain, (metric D).toLorentzMetric.ricci y = 0) ↔
      ∀ τ ∈ D.I, ∀ b k, D.frameRicci τ b k = 0 :=
  ricci_eq_zero_iff

example (τ : ℝ) :
    Fin 4 → ℝ :=
  ricciDiag D τ

example (τ : ℝ) :
    D.frameRicci τ 0 0 = D.ricciDiag τ 0 :=
  frameRicci_zero_zero τ

example (τ : ℝ) :
    D.frameRicci τ 1 1 = D.ricciDiag τ 1 :=
  frameRicci_one_one τ

example (τ : ℝ) :
    D.frameRicci τ 2 2 = D.ricciDiag τ 2 :=
  frameRicci_two_two τ

example (τ : ℝ) :
    D.frameRicci τ 3 3 = D.ricciDiag τ 3 :=
  frameRicci_three_three τ

example (τ : ℝ) :
    D.frameRicci τ 0 1 = 0 :=
  frameRicci_zero_one τ

example (τ : ℝ) :
    D.frameRicci τ 0 2 = 0 :=
  frameRicci_zero_two τ

example (τ : ℝ) :
    D.frameRicci τ 0 3 = 0 :=
  frameRicci_zero_three τ

example (τ : ℝ) :
    D.frameRicci τ 1 0 = 0 :=
  frameRicci_one_zero τ

example (τ : ℝ) :
    D.frameRicci τ 1 2 = 0 :=
  frameRicci_one_two τ

example (τ : ℝ) :
    D.frameRicci τ 1 3 = 0 :=
  frameRicci_one_three τ

example (τ : ℝ) :
    D.frameRicci τ 2 0 = 0 :=
  frameRicci_two_zero τ

example (τ : ℝ) :
    D.frameRicci τ 2 1 = 0 :=
  frameRicci_two_one τ

example (τ : ℝ) :
    D.frameRicci τ 2 3 = 0 :=
  frameRicci_two_three τ

example (τ : ℝ) :
    D.frameRicci τ 3 0 = 0 :=
  frameRicci_three_zero τ

example (τ : ℝ) :
    D.frameRicci τ 3 1 = 0 :=
  frameRicci_three_one τ

example (τ : ℝ) :
    D.frameRicci τ 3 2 = 0 :=
  frameRicci_three_two τ

example (τ : ℝ) (b k : Fin 4) :
    D.frameRicci τ b k = if b = k then D.ricciDiag τ b else 0 :=
  frameRicci_eq τ b k

example :
    Prop :=
  IsVacuum D

example (τ : ℝ) :
    Prop :=
  OneWall D τ

example (τ : ℝ) :
    (∀ b k, D.frameRicci τ b k = 0) ↔ D.OneWall τ :=
  frameRicci_eq_zero_iff τ

example :
    D.IsVacuum ↔ ∀ τ ∈ D.I, D.OneWall τ :=
  isVacuum_iff

example (h : D.IsVacuum) {x : E} (hx : x ∈ D.domain) (j k : Fin 4) :
    ricciOf (metric D).coefficient x j k = 0 :=
  ricciOf_eq_zero_of_isVacuum h hx j k

example (h : D.IsVacuum) (κ : ℝ) :
    (metric D).IsEinstein κ 0 0 :=
  isEinstein_of_isVacuum h κ

example (τ : ℝ) (k : Fin 3) :
    ℝ :=
  exponents D τ k

example {τ : ℝ} (h : D.expansion τ ≠ 0) :
    ∑ k, D.exponents τ k = 1 :=
  sum_exponents h

end Data

example (u τ : ℝ) :
    ℝ :=
  logCosh u τ

example (u : ℝ) :
    ContDiff ℝ ∞ (logCosh u) :=
  contDiff_logCosh u

example (u τ : ℝ) :
    HasDerivAt (logCosh u) (2 * u * Real.tanh (2 * u * τ)) τ :=
  hasDerivAt_logCosh u τ

example (u τ : ℝ) :
    HasDerivAt (fun s => Real.tanh (2 * u * s)) (2 * u / Real.cosh (2 * u * τ) ^ 2) τ :=
  hasDerivAt_tanh u τ

example (x : ℝ) :
    1 - Real.tanh x ^ 2 = 1 / Real.cosh x ^ 2 :=
  one_sub_tanh_sq x

example (u : ℝ) :
    Data :=
  solution u

variable {u : ℝ}

example (u : ℝ) :
    (solution u).I = univ :=
  solution_I u

example (u τ : ℝ) :
    HasDerivAt (solution u).α (-(u * Real.tanh (2 * u * τ))) τ :=
  hasDerivAt_solution_α u τ

example (u τ : ℝ) :
    HasDerivAt (solution u).β (u * Real.tanh (2 * u * τ) + 1) τ :=
  hasDerivAt_solution_β u τ

example (u τ : ℝ) :
    HasDerivAt (solution u).γ (u * Real.tanh (2 * u * τ) + u ^ 2) τ :=
  hasDerivAt_solution_γ u τ

example (u : ℝ) :
    deriv (solution u).α = fun τ => -(u * Real.tanh (2 * u * τ)) :=
  deriv_solution_α u

example (u : ℝ) :
    deriv (solution u).β = fun τ => u * Real.tanh (2 * u * τ) + 1 :=
  deriv_solution_β u

example (u : ℝ) :
    deriv (solution u).γ = fun τ => u * Real.tanh (2 * u * τ) + u ^ 2 :=
  deriv_solution_γ u

example (u τ : ℝ) :
    deriv (deriv (solution u).α) τ = -(2 * u ^ 2 / Real.cosh (2 * u * τ) ^ 2) :=
  deriv_deriv_solution_α u τ

example (u τ : ℝ) :
    deriv (deriv (solution u).β) τ = 2 * u ^ 2 / Real.cosh (2 * u * τ) ^ 2 :=
  deriv_deriv_solution_β u τ

example (u τ : ℝ) :
    deriv (deriv (solution u).γ) τ = 2 * u ^ 2 / Real.cosh (2 * u * τ) ^ 2 :=
  deriv_deriv_solution_γ u τ

example (hu : 0 < u) (τ : ℝ) :
    (solution u).a τ ^ 4 = 4 * u ^ 2 / Real.cosh (2 * u * τ) ^ 2 :=
  a_solution_pow_four hu τ

example (hu : 0 < u) :
    (solution u).IsVacuum :=
  isVacuum_solution hu

example (hu : 0 < u) (κ : ℝ) :
    (solution u).metric.IsEinstein κ 0 0 :=
  isEinstein_solution hu κ

example (u τ : ℝ) :
    (solution u).expansion τ = u * Real.tanh (2 * u * τ) + (1 + u ^ 2) :=
  expansion_solution u τ

example (u τ : ℝ) (k : Fin 3) :
    (solution u).exponents τ k =
      ![-(u * Real.tanh (2 * u * τ)), u * Real.tanh (2 * u * τ) + 1,
        u * Real.tanh (2 * u * τ) + u ^ 2] k / (u * Real.tanh (2 * u * τ) + (1 + u ^ 2)) :=
  exponents_solution u τ k

example (x : ℝ) :
    1 - Real.tanh x ≤ 2 * Real.exp (-(2 * x)) :=
  one_sub_tanh_le x

example (x : ℝ) :
    1 + Real.tanh x ≤ 2 * Real.exp (2 * x) :=
  one_add_tanh_le x

example (u : ℝ) (k : Fin 3) :
    kasnerExponents (u - 1) k = ![-(u - 1), u, u * (u - 1)] k / (1 - u + u ^ 2) :=
  kasnerExponents_sub_one u k

example (hu : 0 < u) (τ : ℝ) (k : Fin 3) :
    |(solution u).exponents τ k - kasnerExponents u k| ≤
      8 * u / (1 + u ^ 2) * Real.exp (-(4 * u * τ)) :=
  abs_exponents_sub_le_atTop hu τ k

example (hu : 0 < u) (τ : ℝ) (k : Fin 3) :
    |(solution u).exponents τ k -
        ![kasnerExponents (u - 1) 1, kasnerExponents (u - 1) 0, kasnerExponents (u - 1) 2] k| ≤
      8 * u / (1 + u ^ 2) * Real.exp (4 * u * τ) :=
  abs_exponents_sub_le_atBot hu τ k

example (hu : 0 < u) {τ₀ τ : ℝ} (k : Fin 3) :
    (τ₀ ≤ τ → |(solution u).exponents τ k - kasnerExponents u k| ≤
        8 * u / (1 + u ^ 2) * Real.exp (-(4 * u * τ₀))) ∧
      (τ ≤ -τ₀ → |(solution u).exponents τ k -
          ![kasnerExponents (u - 1) 1, kasnerExponents (u - 1) 0, kasnerExponents (u - 1) 2] k| ≤
        8 * u / (1 + u ^ 2) * Real.exp (-(4 * u * τ₀))) :=
  abs_exponents_sub_le hu k

example (hu : 0 < u) :
    Tendsto (solution u).exponents atTop (𝓝 (kasnerExponents u)) :=
  tendsto_exponents_atTop hu

example (hu : 0 < u) :
    Tendsto (solution u).exponents atBot
      (𝓝 ![kasnerExponents (u - 1) 1, kasnerExponents (u - 1) 0, kasnerExponents (u - 1) 2]) :=
  tendsto_exponents_atBot hu

example (hu : 0 < u) :
    Tendsto (solution u).exponents atTop (𝓝 (kasnerExponents u)) ∧
      Tendsto (solution u).exponents atBot
        (𝓝 ![kasnerExponents (u - 1) 1, kasnerExponents (u - 1) 0, kasnerExponents (u - 1) 2]) :=
  tendsto_exponents hu

example (hu : 0 < u) :
    Tendsto (solution u).exponents atBot (𝓝 (bounce (kasnerExponents u))) :=
  tendsto_exponents_atBot_bounce hu

example (hu : 0 < u) (hu1 : u ≠ 1) :
    Tendsto (solution u).exponents atBot
      (𝓝 ![kasnerExponents (u - 1)⁻¹ 2, kasnerExponents (u - 1)⁻¹ 0,
        kasnerExponents (u - 1)⁻¹ 1]) :=
  tendsto_exponents_atBot_era hu hu1

end TypeII

end ProjectAinos.GeneralRelativity.BKL

end BKL
