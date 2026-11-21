/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Potential.Multipole
import ProjectAinos.Electrodynamics.ExtendedChargeInteraction

/-! Public consumers of multipoles (Landau–Lifshitz §§40–42): the Taylor bounds of the Newton
kernel with explicit constants through order two and existential ones at every order, the
symmetry and trace of its derivatives; the charge, dipole and quadrupole moments with the uniform
remainders of the potential outside the source, the translation laws, the dipole field; and the
energy, force and torque of a localized source in an external field, with instances.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/

noncomputable section

section PotentialMultipole

open MeasureTheory Filter Set Metric Real Nat

open scoped Topology ContDiff RealInnerProductSpace

namespace ProjectAinos.SmoothGeometry.Potential

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (n : ℕ) :
    ∫ t in (0 : ℝ)..1, (1 - t) ^ n = 1 / (n + 1) :=
  integral_one_sub_pow n

example {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {f : E → F} {x y : E} {n : ℕ} {M : ℝ}
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (n + 1) f (x + t • y))
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖ ≤ M) :
    ‖f (x + y) - ∑ k ∈ Finset.range (n + 1), (k ! : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ => y)‖
      ≤ M / (n + 1)! :=
  norm_sub_sum_iteratedFDeriv_le hf hM

example (x b : E3) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖x‖ - ‖b‖ ≤ ‖x + t • b‖ :=
  sub_le_norm_add_smul x b ht

example (x y : E3) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖x‖ - ‖y‖ ≤ ‖x + t • -y‖ :=
  sub_le_norm_add_smul_neg x y ht

example {x y : E3} (hy : ‖y‖ < ‖x‖) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    x + t • -y ≠ 0 :=
  add_smul_neg_ne_zero hy ht

example {x y : E3} (hy : ‖y‖ < ‖x‖) :
    |newtonKernel (x - y) - newtonKernel x| ≤ ‖y‖ / (4 * π * ‖x‖ * (‖x‖ - ‖y‖)) :=
  abs_newtonKernel_sub_le hy

example {g g' : ℝ → ℝ} {g'' : ℝ} {x : E3} (hg : ∀ᶠ s in 𝓝 (‖x‖ ^ 2), HasDerivAt g (g' s) s)
    (hg' : HasDerivAt g' g'' (‖x‖ ^ 2)) (v w : E3) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => g (‖z‖ ^ 2)) y w) x v =
      2 * g' (‖x‖ ^ 2) * ⟪v, w⟫ + 4 * g'' * ⟪x, v⟫ * ⟪x, w⟫ :=
  fderiv_fderiv_comp_normSq_apply hg hg' v w

example (x : E3) (k : ℕ) :
    (‖x‖ ^ 2 + 0) ^ (-((k : ℝ) / 2)) = (‖x‖ ^ k)⁻¹ :=
  normSq_rpow_neg_half x k

example :
    newtonKernel = fun y => kernelProfile 0 (‖y‖ ^ 2) :=
  newtonKernel_eq_kernelProfile

example {z : E3} (hz : z ≠ 0) (m : Fin 2 → E3) :
    iteratedFDeriv ℝ 2 newtonKernel z m =
      (3 * ⟪z, m 0⟫ * ⟪z, m 1⟫ - ‖z‖ ^ 2 * ⟪m 0, m 1⟫) / (4 * π * ‖z‖ ^ 5) :=
  iteratedFDeriv_two_newtonKernel hz m

example {z : E3} (hz : z ≠ 0) (v : E3) :
    |iteratedFDeriv ℝ 2 newtonKernel z (fun _ => v)| ≤ ‖v‖ ^ 2 / (2 * π * ‖z‖ ^ 3) :=
  abs_iteratedFDeriv_two_newtonKernel_le hz v

example {x : E3} (hx : x ≠ 0) (y : E3) :
    fderiv ℝ newtonKernel x (-y) = ⟪x, y⟫ / (4 * π * ‖x‖ ^ 3) :=
  fderiv_newtonKernel_neg_apply hx y

example {x y : E3} (hy : ‖y‖ < ‖x‖) :
    |newtonKernel (x - y) - newtonKernel x - ⟪x, y⟫ / (4 * π * ‖x‖ ^ 3)| ≤
      ‖y‖ ^ 2 / (4 * π * (‖x‖ - ‖y‖) ^ 3) :=
  abs_newtonKernel_sub_dipole_le hy

example {c : ℝ} (hc : 0 < c) (z : E3) :
    newtonKernel (c • z) = c⁻¹ * newtonKernel z :=
  newtonKernel_smul hc z

example {c : ℝ} (hc : 0 < c) {z : E3} (hz : z ≠ 0) (n : ℕ) :
    iteratedFDeriv ℝ n newtonKernel (c • z) =
      (c ^ (n + 1))⁻¹ • iteratedFDeriv ℝ n newtonKernel z :=
  iteratedFDeriv_newtonKernel_smul hc hz n

example {z : E3} (hz : z ≠ 0) (n : ℕ) :
    ContinuousAt (iteratedFDeriv ℝ n newtonKernel) z :=
  continuousAt_iteratedFDeriv_newtonKernel hz n

example (n : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ z : E3, z ≠ 0 → ‖iteratedFDeriv ℝ n newtonKernel z‖ ≤ C / ‖z‖ ^ (n + 1) :=
  norm_iteratedFDeriv_newtonKernel_le n

example (n : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x y : E3, ‖y‖ < ‖x‖ →
      |newtonKernel (x - y) - ∑ k ∈ Finset.range (n + 1),
          (k ! : ℝ)⁻¹ * iteratedFDeriv ℝ k newtonKernel x (fun _ => -y)| ≤
        C * ‖y‖ ^ (n + 1) / (‖x‖ - ‖y‖) ^ (n + 2) :=
  newtonKernel_taylor_le n

example {z : E3} (hz : z ≠ 0) {n : ℕ} (v : Fin n → E3) (σ : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℝ n newtonKernel z (v ∘ σ) = iteratedFDeriv ℝ n newtonKernel z v :=
  iteratedFDeriv_newtonKernel_comp_perm hz v σ

example :
    (E3 →L[ℝ] E3 →L[ℝ] ℝ) →L[ℝ] ℝ :=
  traceForm

example (B : E3 →L[ℝ] E3 →L[ℝ] ℝ) :
    traceForm B = ∑ i : Fin 3, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) :=
  traceForm_apply B

example {z : E3} (hz : z ≠ 0) {k : ℕ} (v : Fin k → E3) :
    ∑ i : Fin 3, iteratedFDeriv ℝ (k + 2) newtonKernel z
      (Fin.snoc (Fin.snoc v (EuclideanSpace.single i 1)) (EuclideanSpace.single i 1)) = 0 :=
  sum_iteratedFDeriv_newtonKernel_snoc_snoc hz v

example (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x b : E3, ‖b‖ < ‖x‖ →
      ‖iteratedFDeriv ℝ k newtonKernel (x + b) - iteratedFDeriv ℝ k newtonKernel x‖ ≤
        C * ‖b‖ / (‖x‖ - ‖b‖) ^ (k + 2) :=
  norm_iteratedFDeriv_newtonKernel_add_sub_le k

example {z : E3} (hz : z ≠ 0) (v : E3) :
    iteratedFDeriv ℝ 3 newtonKernel z (fun _ => v) =
      (9 * ⟪z, v⟫ * ‖v‖ ^ 2 * ‖z‖ ^ 2 - 15 * ⟪z, v⟫ ^ 3) / (4 * π * ‖z‖ ^ 7) :=
  iteratedFDeriv_three_newtonKernel_diag hz v

example {z : E3} (hz : z ≠ 0) (v : E3) :
    |iteratedFDeriv ℝ 3 newtonKernel z (fun _ => v)| ≤ 3 * ‖v‖ ^ 3 / (2 * π * ‖z‖ ^ 4) :=
  abs_iteratedFDeriv_three_newtonKernel_le hz v

example {x y : E3} (hy : ‖y‖ < ‖x‖) :
    |newtonKernel (x - y) - ∑ k ∈ Finset.range 3,
        (k ! : ℝ)⁻¹ * iteratedFDeriv ℝ k newtonKernel x (fun _ => -y)| ≤
      ‖y‖ ^ 3 / (4 * π * (‖x‖ - ‖y‖) ^ 4) :=
  abs_newtonKernel_sub_taylor_two_le hy

example {x y : E3} (hy : ‖y‖ < ‖x‖) :
    |newtonKernel (x - y) - newtonKernel x - ⟪x, y⟫ / (4 * π * ‖x‖ ^ 3) -
        (3 * ⟪x, y⟫ ^ 2 - ‖x‖ ^ 2 * ‖y‖ ^ 2) / (8 * π * ‖x‖ ^ 5)| ≤
      ‖y‖ ^ 3 / (4 * π * (‖x‖ - ‖y‖) ^ 4) :=
  abs_newtonKernel_sub_quadrupole_le hy

example {k : ℕ} {c : ℕ → ℝ} {M t₀ : ℝ} (ht₀ : 0 < t₀)
    (h : ∀ t, 0 < t → t ≤ t₀ → |∑ j ∈ Finset.range (k + 1), c j * t ^ j| ≤ M * t ^ (k + 1)) :
    ∀ j ≤ k, c j = 0 :=
  eq_zero_of_abs_sum_mul_pow_le ht₀ h

end ProjectAinos.SmoothGeometry.Potential

end PotentialMultipole

section Multipole

open MeasureTheory Filter Set Metric Real Nat

open scoped Topology ContDiff RealInnerProductSpace Laplacian

namespace ProjectAinos.Electrodynamics.Multipole

open SmoothGeometry.Potential

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example {ρ : E3 → ℝ} {a : ℝ} (ha : tsupport ρ ⊆ closedBall 0 a) :
    HasCompactSupport ρ :=
  hasCompactSupport_of_tsupport_subset ha

example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ρ : E3 → ℝ} {g : E3 → F}
    {s : Set E3} (hρ : Continuous ρ) (hs : tsupport ρ ⊆ s) (hg : ∀ w ∈ s, ContinuousAt g w) :
    Continuous fun y => ρ y • g y :=
  continuous_smul_of_tsupport_subset hρ hs hg

example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ρ : E3 → ℝ} (hρ : Continuous ρ)
    (hcρ : HasCompactSupport ρ) {g : E3 → F} (hg : Continuous g) :
    Integrable fun y => ρ y • g y :=
  integrable_density_smul hρ hcρ hg

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) {g : E3 → ℝ}
    (hg : Continuous g) :
    Integrable fun y => ρ y * g y :=
  integrable_density_mul hρ hcρ hg

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (x : E3) :
    Integrable fun y => ρ y * newtonKernel (x - y) :=
  integrable_density_mul_newtonKernel_sub hρ hcρ x

example (ρ : E3 → ℝ) :
    ℝ :=
  totalCharge ρ

example (ρ : E3 → ℝ) :
    E3 :=
  dipoleMoment ρ

example (ρ : E3 → ℝ) (i j : Fin 3) :
    ℝ :=
  quadrupoleMoment ρ i j

example (ρ : E3 → ℝ) (k : ℕ) (x : E3) :
    ℝ :=
  multipoleTerm ρ k x

example {k : ℕ} (L : ContinuousMultilinearMap ℝ (fun _ : Fin k => E3) ℝ) :
    Continuous fun y : E3 => L (fun _ => -y) :=
  continuous_apply_neg L

example {k : ℕ} (L : ContinuousMultilinearMap ℝ (fun _ : Fin k => E3) ℝ) (y : E3) :
    |L (fun _ => -y)| ≤ ‖L‖ * ‖y‖ ^ k :=
  abs_apply_neg_le L y

example (ρ : E3 → ℝ) (x : E3) :
    multipoleTerm ρ 0 x = totalCharge ρ * newtonKernel x :=
  multipoleTerm_zero ρ x

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) {x : E3} (hx : x ≠ 0) :
    multipoleTerm ρ 1 x = ⟪dipoleMoment ρ, x⟫ / (4 * π * ‖x‖ ^ 3) :=
  multipoleTerm_one hρ hcρ hx

example {ρ : E3 → ℝ} {a : ℝ} (ha : tsupport ρ ⊆ closedBall 0 a) {y : E3} (hy : ρ y ≠ 0) :
    ‖y‖ ≤ a :=
  norm_le_of_ne_zero ha hy

example {ρ R : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) {m : ℕ} {c : ℝ}
    (hR : ∀ y, ρ y ≠ 0 → |R y| ≤ c * ‖y‖ ^ m) :
    |∫ y, ρ y * R y| ≤ (∫ y, |ρ y| * ‖y‖ ^ m) * c :=
  abs_integral_mul_le hρ hcρ hR

example (ρ : E3 → ℝ) (c : ℝ) :
    totalCharge ρ * c = ∫ y, ρ y * c :=
  totalCharge_mul ρ c

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (x : E3) :
    ⟪dipoleMoment ρ, x⟫ = ∫ y, ρ y * ⟪x, y⟫ :=
  inner_dipoleMoment hρ hcρ x

example {ρ : E3 → ℝ} (hρ : Continuous ρ) {a : ℝ} (ha : tsupport ρ ⊆ closedBall 0 a) {x : E3}
    (hx : a < ‖x‖) :
    |newtonPotential ρ x - totalCharge ρ / (4 * π * ‖x‖) -
        ⟪dipoleMoment ρ, x⟫ / (4 * π * ‖x‖ ^ 3)| ≤
      (∫ y, |ρ y| * ‖y‖ ^ 2) / (4 * π * (‖x‖ - a) ^ 3) :=
  abs_newtonPotential_sub_dipole_le hρ ha hx

example (ρ : E3 → ℝ) (b : E3) :
    totalCharge (fun y => ρ (y + b)) = totalCharge ρ :=
  totalCharge_translate ρ b

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (b : E3) :
    dipoleMoment (fun y => ρ (y + b)) = dipoleMoment ρ - totalCharge ρ • b :=
  dipoleMoment_translate hρ hcρ b

example (ρ : E3 → ℝ) (b x : E3) :
    newtonPotential (fun y => ρ (y + b)) x = newtonPotential ρ (x + b) :=
  newtonPotential_translate ρ b x

example {ρ : E3 → ℝ} {a : ℝ} (ha : tsupport ρ ⊆ closedBall 0 a) (b : E3) :
    tsupport (fun y => ρ (y + b)) ⊆ closedBall 0 (a + ‖b‖) :=
  tsupport_translate_subset ha b

example (d x : E3) :
    ℝ :=
  dipolePotential d x

example (d x : E3) :
    E3 :=
  dipoleField d x

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) {x : E3} (hx : x ≠ 0) :
    multipoleTerm ρ 1 x = dipolePotential (dipoleMoment ρ) x :=
  multipoleTerm_one_eq_dipolePotential hρ hcρ hx

example {d x : E3} (hx : x ≠ 0) :
    dipolePotential d x = fderiv ℝ newtonKernel x (-d) :=
  dipolePotential_eq hx

example (d : E3) {x : E3} (hx : x ≠ 0) :
    HasGradientAt (dipolePotential d) (-dipoleField d x) x :=
  hasGradientAt_dipolePotential d hx

example (d : E3) {x : E3} (hx : x ≠ 0) :
    -gradient (dipolePotential d) x = dipoleField d x :=
  neg_gradient_dipolePotential d hx

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (n : ℕ) (x : E3) :
    ∑ k ∈ Finset.range (n + 1), multipoleTerm ρ k x = ∫ y, ρ y * ∑ k ∈ Finset.range (n + 1),
      (k ! : ℝ)⁻¹ * iteratedFDeriv ℝ k newtonKernel x (fun _ => -y) :=
  sum_multipoleTerm_eq hρ hcρ n x

example (n : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ {ρ : E3 → ℝ}, Continuous ρ → ∀ {a : ℝ}, tsupport ρ ⊆ closedBall 0 a →
      ∀ {x : E3}, a < ‖x‖ →
        |newtonPotential ρ x - ∑ k ∈ Finset.range (n + 1), multipoleTerm ρ k x| ≤
          C * (∫ y, |ρ y| * ‖y‖ ^ (n + 1)) / (‖x‖ - a) ^ (n + 2) :=
  abs_newtonPotential_sub_multipole_le n

example {ρ : E3 → ℝ} (hρ : Continuous ρ) {a : ℝ} (ha : tsupport ρ ⊆ closedBall 0 a) {x : E3}
    (hx : a < ‖x‖) :
    |newtonPotential ρ x - ∑ k ∈ Finset.range 3, multipoleTerm ρ k x| ≤
      (∫ y, |ρ y| * ‖y‖ ^ 3) / (4 * π * (‖x‖ - a) ^ 4) :=
  abs_newtonPotential_sub_quadrupole_le hρ ha hx

example (ρ : E3 → ℝ) (k : ℕ) {c : ℝ} (hc : 0 < c) {x : E3} (hx : x ≠ 0) :
    multipoleTerm ρ k (c • x) = (c ^ (k + 1))⁻¹ * multipoleTerm ρ k x :=
  multipoleTerm_smul ρ k hc hx

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (k : ℕ) (x x' : E3) :
    |multipoleTerm ρ k x' - multipoleTerm ρ k x| ≤ (k ! : ℝ)⁻¹ * ((∫ y, |ρ y| * ‖y‖ ^ k) *
      ‖iteratedFDeriv ℝ k newtonKernel x' - iteratedFDeriv ℝ k newtonKernel x‖) :=
  abs_multipoleTerm_sub_le hρ hcρ k x x'

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) {k : ℕ}
    (hlow : ∀ j < k, ∀ x : E3, x ≠ 0 → multipoleTerm ρ j x = 0) (b : E3) {x : E3} (hx : x ≠ 0) :
    ∃ M t₀, 0 < t₀ ∧ ∀ t, 0 < t → t ≤ t₀ →
      |∑ j ∈ Finset.range (k + 1), (multipoleTerm (fun y => ρ (y + b)) j x -
        if j = k then multipoleTerm ρ k x else 0) * t ^ j| ≤ M * t ^ (k + 1) :=
  exists_abs_sum_multipoleTerm_translate_le hρ hcρ hlow b hx

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) {k : ℕ}
    (hlow : ∀ j < k, ∀ x : E3, x ≠ 0 → multipoleTerm ρ j x = 0) (b : E3) {x : E3} (hx : x ≠ 0) :
    multipoleTerm (fun y => ρ (y + b)) k x = multipoleTerm ρ k x :=
  multipoleTerm_translate hρ hcρ hlow b hx

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) {k : ℕ}
    (hlow : ∀ j < k, ∀ x : E3, x ≠ 0 → multipoleTerm ρ j x = 0) (b : E3) {j : ℕ} (hj : j < k)
    {x : E3} (hx : x ≠ 0) :
    multipoleTerm (fun y => ρ (y + b)) j x = 0 :=
  multipoleTerm_translate_of_lt hρ hcρ hlow b hj hx

example (ρ : E3 → ℝ) (i j : Fin 3) :
    quadrupoleMoment ρ i j = quadrupoleMoment ρ j i :=
  quadrupoleMoment_symm ρ i j

example (y : E3) :
    ∑ i : Fin 3, y i • EuclideanSpace.single i (1 : ℝ) = y :=
  sum_smul_single y

example (B : E3 →L[ℝ] E3 →L[ℝ] ℝ) (y : E3) :
    B y y = ∑ i : Fin 3, ∑ j : Fin 3, y i * y j *
      B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) :=
  bilinear_apply_eq_sum B y

example (y : E3) :
    ‖y‖ ^ 2 = ∑ i : Fin 3, y i ^ 2 :=
  norm_sq_eq_sum y

example (i : Fin 3) :
    Continuous fun y : E3 => y i :=
  continuous_coord i

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) :
    ∑ i : Fin 3, quadrupoleMoment ρ i i = 0 :=
  quadrupoleMoment_trace hρ hcρ

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (B : E3 →L[ℝ] E3 →L[ℝ] ℝ) :
    ∑ i : Fin 3, ∑ j : Fin 3, quadrupoleMoment ρ i j *
        B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      3 * (∫ y, ρ y * B y y) - (∫ y, ρ y * ‖y‖ ^ 2) *
        ∑ i : Fin 3, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) :=
  sum_quadrupoleMoment_mul hρ hcρ B

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) {x : E3} (hx : x ≠ 0) :
    multipoleTerm ρ 2 x =
      (∑ i : Fin 3, ∑ j : Fin 3, quadrupoleMoment ρ i j * x i * x j) / (8 * π * ‖x‖ ^ 5) :=
  multipoleTerm_two_eq hρ hcρ hx

example {ρ : E3 → ℝ} (hρ : Continuous ρ) {a : ℝ} (ha0 : 0 ≤ a) (ha : tsupport ρ ⊆ closedBall 0 a)
    {x : E3} (hx : a < ‖x‖) :
    |newtonPotential ρ x - totalCharge ρ / (4 * π * ‖x‖) -
        ⟪dipoleMoment ρ, x⟫ / (4 * π * ‖x‖ ^ 3) -
        (∑ i : Fin 3, ∑ j : Fin 3, quadrupoleMoment ρ i j * x i * x j) / (8 * π * ‖x‖ ^ 5)| ≤
      (∫ y, |ρ y| * ‖y‖ ^ 3) / (4 * π * (‖x‖ - a) ^ 4) :=
  abs_newtonPotential_sub_moments_le hρ ha0 ha hx

example {a : ℝ} {y : E3} (hy : ‖y‖ ≤ a) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (0 : E3) + t • y ∈ closedBall (0 : E3) a :=
  zero_add_smul_mem_closedBall hy ht

example {ψ : E3 → ℝ} {a B : ℝ} (hψ : ∀ w ∈ closedBall (0 : E3) a, ContDiffAt ℝ 3 ψ w)
    (hB : ∀ w ∈ closedBall (0 : E3) a, ‖iteratedFDeriv ℝ 3 ψ w‖ ≤ B) {y : E3} (hy : ‖y‖ ≤ a) :
    |ψ y - ψ 0 - fderiv ℝ ψ 0 y - fderiv ℝ (fderiv ℝ ψ) 0 y y / 2| ≤ B / 6 * ‖y‖ ^ 3 :=
  abs_sub_taylor_two_le hψ hB hy

example {ψ : E3 → ℝ} {a B : ℝ} (hψ : ∀ w ∈ closedBall (0 : E3) a, ContDiffAt ℝ 3 ψ w)
    (hB : ∀ w ∈ closedBall (0 : E3) a, ‖iteratedFDeriv ℝ 3 ψ w‖ ≤ B) {y : E3} (hy : ‖y‖ ≤ a)
    (v : E3) :
    |fderiv ℝ ψ y v - fderiv ℝ ψ 0 v - fderiv ℝ (fderiv ℝ ψ) 0 y v| ≤ B / 2 * ‖y‖ ^ 2 * ‖v‖ :=
  abs_fderiv_sub_taylor_one_le hψ hB hy v

example (ρ ψ : E3 → ℝ) :
    ℝ :=
  externalEnergy ρ ψ

example (ρ ψ : E3 → ℝ) :
    E3 :=
  externalForce ρ ψ

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (L : E3 →L[ℝ] ℝ) :
    L (dipoleMoment ρ) = ∫ y, ρ y * L y :=
  clm_dipoleMoment hρ hcρ L

example {ψ : E3 → ℝ} {x : E3} (hψ : ContDiffAt ℝ 2 ψ x) :
    ∑ i : Fin 3, fderiv ℝ (fderiv ℝ ψ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single i 1) = Δ ψ x :=
  sum_fderiv_fderiv_single_eq_laplacian hψ

example {ρ ψ : E3 → ℝ} (hρ : Continuous ρ) {a B : ℝ} (ha0 : 0 ≤ a)
    (ha : tsupport ρ ⊆ closedBall 0 a) (hψ : ∀ w ∈ closedBall (0 : E3) a, ContDiffAt ℝ 3 ψ w)
    (hB : ∀ w ∈ closedBall (0 : E3) a, ‖iteratedFDeriv ℝ 3 ψ w‖ ≤ B) (hΔ : Δ ψ 0 = 0) :
    |externalEnergy ρ ψ - (totalCharge ρ * ψ 0 + fderiv ℝ ψ 0 (dipoleMoment ρ) +
        1 / 6 * ∑ i : Fin 3, ∑ j : Fin 3, quadrupoleMoment ρ i j *
          fderiv ℝ (fderiv ℝ ψ) 0 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))| ≤
      (∫ y, |ρ y| * ‖y‖ ^ 3) / 6 * B :=
  abs_externalEnergy_sub_le hρ ha0 ha hψ hB hΔ

example {w : E3} {C : ℝ} (hC : 0 ≤ C) (h : ∀ v : E3, |⟪w, v⟫| ≤ C * ‖v‖) :
    ‖w‖ ≤ C :=
  norm_le_of_forall_abs_inner_le hC h

example {ψ : E3 → ℝ} {w : E3} (hψ : ContDiffAt ℝ 1 ψ w) :
    ContinuousAt (gradient ψ) w :=
  continuousAt_gradient hψ

example {ρ ψ : E3 → ℝ} (hρ : Continuous ρ) {a B : ℝ} (ha0 : 0 ≤ a)
    (ha : tsupport ρ ⊆ closedBall 0 a) (hψ : ∀ w ∈ closedBall (0 : E3) a, ContDiffAt ℝ 3 ψ w)
    (hB : ∀ w ∈ closedBall (0 : E3) a, ‖iteratedFDeriv ℝ 3 ψ w‖ ≤ B) :
    ‖externalForce ρ ψ - (totalCharge ρ • -gradient ψ 0 -
        gradient (fun y => fderiv ℝ ψ y (dipoleMoment ρ)) 0)‖ ≤
      (∫ y, |ρ y| * ‖y‖ ^ 2) / 2 * B :=
  norm_externalForce_sub_le hρ ha0 ha hψ hB

example :
    Continuous Electrostatics.bumpCharge :=
  continuous_bumpCharge

example :
    tsupport Electrostatics.bumpCharge ⊆ closedBall 0 2 :=
  tsupport_bumpCharge

example :
    0 < totalCharge Electrostatics.bumpCharge :=
  totalCharge_bumpCharge_pos

example :
    0 < totalCharge Electrostatics.bumpCharge ∧ ∀ x : E3, 2 < ‖x‖ →
      |newtonPotential Electrostatics.bumpCharge x -
          totalCharge Electrostatics.bumpCharge / (4 * π * ‖x‖) -
          ⟪dipoleMoment Electrostatics.bumpCharge, x⟫ / (4 * π * ‖x‖ ^ 3)| ≤
        (∫ y, |Electrostatics.bumpCharge y| * ‖y‖ ^ 2) / (4 * π * (‖x‖ - 2) ^ 3) :=
  bumpCharge_dipole_instance

example (n : ℕ) :
    ∃ C, ∀ x : E3, 2 < ‖x‖ →
      |newtonPotential Electrostatics.bumpCharge x -
          ∑ k ∈ Finset.range (n + 1), multipoleTerm Electrostatics.bumpCharge k x| ≤
        C * (∫ y, |Electrostatics.bumpCharge y| * ‖y‖ ^ (n + 1)) / (‖x‖ - 2) ^ (n + 2) :=
  bumpCharge_multipole_instance n

example (c y : E3) :
    ℝ :=
  neutralPair c y

example (c : E3) :
    Continuous (neutralPair c) :=
  continuous_neutralPair c

example (c : E3) :
    HasCompactSupport (neutralPair c) :=
  hasCompactSupport_neutralPair c

example (c : E3) :
    totalCharge (neutralPair c) = 0 :=
  totalCharge_neutralPair c

example (c : E3) :
    dipoleMoment (neutralPair c) = -(totalCharge Electrostatics.bumpCharge • c) :=
  dipoleMoment_neutralPair c

example (c b : E3) {x : E3} (hx : x ≠ 0) :
    multipoleTerm (fun y => neutralPair c (y + b)) 1 x = multipoleTerm (neutralPair c) 1 x :=
  neutralPair_translate_instance c b hx

example (e y : E3) :
    ℝ :=
  uniformFieldPotential e y

example (e : E3) {n : WithTop ℕ∞} :
    ContDiff ℝ n (uniformFieldPotential e) :=
  contDiff_uniformFieldPotential e

example (e : E3) :
    fderiv ℝ (uniformFieldPotential e) = fun _ => innerSL ℝ e :=
  fderiv_uniformFieldPotential e

example (e w : E3) :
    ‖iteratedFDeriv ℝ 3 (uniformFieldPotential e) w‖ = 0 :=
  norm_iteratedFDeriv_three_uniformFieldPotential e w

example (e : E3) :
    Δ (uniformFieldPotential e) 0 = 0 :=
  laplacian_uniformFieldPotential e

example (e : E3) :
    |externalEnergy Electrostatics.bumpCharge (uniformFieldPotential e) -
        (totalCharge Electrostatics.bumpCharge * uniformFieldPotential e 0 +
          fderiv ℝ (uniformFieldPotential e) 0 (dipoleMoment Electrostatics.bumpCharge) +
          1 / 6 * ∑ i : Fin 3, ∑ j : Fin 3, quadrupoleMoment Electrostatics.bumpCharge i j *
            fderiv ℝ (fderiv ℝ (uniformFieldPotential e)) 0 (EuclideanSpace.single i 1)
              (EuclideanSpace.single j 1))| ≤
        (∫ y, |Electrostatics.bumpCharge y| * ‖y‖ ^ 3) / 6 * 0 ∧
    ‖externalForce Electrostatics.bumpCharge (uniformFieldPotential e) -
        (totalCharge Electrostatics.bumpCharge • -gradient (uniformFieldPotential e) 0 -
          gradient (fun y => fderiv ℝ (uniformFieldPotential e) y
            (dipoleMoment Electrostatics.bumpCharge)) 0)‖ ≤
        (∫ y, |Electrostatics.bumpCharge y| * ‖y‖ ^ 2) / 2 * 0 :=
  bumpCharge_external_instance e

example (u v : E3) :
    E3 :=
  cross3 u v

example (u u' v : E3) :
    cross3 (u + u') v = cross3 u v + cross3 u' v :=
  cross3_add_left u u' v

example (c : ℝ) (u v : E3) :
    cross3 (c • u) v = c • cross3 u v :=
  cross3_smul_left c u v

example (u v v' : E3) :
    cross3 u v - cross3 u v' = cross3 u (v - v') :=
  cross3_sub_right u v v'

example (u v : E3) :
    ‖cross3 u v‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 :=
  norm_cross3_sq u v

example (u v : E3) :
    ‖cross3 u v‖ ≤ ‖u‖ * ‖v‖ :=
  norm_cross3_le u v

example :
    Continuous fun p : E3 × E3 => cross3 p.1 p.2 :=
  continuous_cross3

example (w : E3) :
    E3 →L[ℝ] E3 :=
  cross3Right w

example (w u : E3) :
    cross3Right w u = cross3 u w :=
  cross3Right_apply w u

example (ρ ψ : E3 → ℝ) :
    E3 :=
  externalTorque ρ ψ

example {ψ : E3 → ℝ} {a B : ℝ} (hψ : ∀ w ∈ closedBall (0 : E3) a, ContDiffAt ℝ 2 ψ w)
    (hB : ∀ w ∈ closedBall (0 : E3) a, ‖iteratedFDeriv ℝ 2 ψ w‖ ≤ B) {y : E3} (hy : ‖y‖ ≤ a) :
    ‖gradient ψ y - gradient ψ 0‖ ≤ B * ‖y‖ :=
  norm_gradient_sub_le hψ hB hy

example {ρ ψ : E3 → ℝ} (hρ : Continuous ρ) {a B : ℝ} (ha : tsupport ρ ⊆ closedBall 0 a)
    (hψ : ∀ w ∈ closedBall (0 : E3) a, ContDiffAt ℝ 2 ψ w)
    (hB : ∀ w ∈ closedBall (0 : E3) a, ‖iteratedFDeriv ℝ 2 ψ w‖ ≤ B) :
    ‖externalTorque ρ ψ - cross3 (dipoleMoment ρ) (-gradient ψ 0)‖ ≤
      (∫ y, |ρ y| * ‖y‖ ^ 2) * B :=
  norm_externalTorque_sub_le hρ ha hψ hB

example (e w : E3) :
    ‖iteratedFDeriv ℝ 2 (uniformFieldPotential e) w‖ = 0 :=
  norm_iteratedFDeriv_two_uniformFieldPotential e w

example (e : E3) :
    ‖externalTorque Electrostatics.bumpCharge (uniformFieldPotential e) -
        cross3 (dipoleMoment Electrostatics.bumpCharge) (-gradient (uniformFieldPotential e) 0)‖ ≤
      (∫ y, |Electrostatics.bumpCharge y| * ‖y‖ ^ 2) * 0 :=
  bumpCharge_torque_instance e

example (v : E3) :
    ‖ContinuousLinearMap.apply ℝ ℝ v‖ ≤ ‖v‖ :=
  norm_apply_le v

example {d w : E3} (hw : w ≠ 0) :
    dipolePotential d =ᶠ[𝓝 w] fun x => fderiv ℝ newtonKernel x (-d) :=
  dipolePotential_eventuallyEq hw

example (d : E3) {w : E3} (hw : w ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (dipolePotential d) w :=
  contDiffAt_dipolePotential d hw

example :
    ∃ C, 0 ≤ C ∧ ∀ d w : E3, w ≠ 0 →
      ‖iteratedFDeriv ℝ 2 (dipolePotential d) w‖ ≤ C * ‖d‖ / ‖w‖ ^ 4 :=
  norm_iteratedFDeriv_two_dipolePotential_le

example {ψ : E3 → ℝ} {a B : ℝ} (hψ : ∀ w ∈ closedBall (0 : E3) a, ContDiffAt ℝ 2 ψ w)
    (hB : ∀ w ∈ closedBall (0 : E3) a, ‖iteratedFDeriv ℝ 2 ψ w‖ ≤ B) {y : E3} (hy : ‖y‖ ≤ a) :
    |ψ y - ψ 0 - fderiv ℝ ψ 0 y| ≤ B / 2 * ‖y‖ ^ 2 :=
  abs_sub_taylor_one_le hψ hB hy

example (d₁ d₂ R : E3) :
    ℝ :=
  dipoleInteraction d₁ d₂ R

example (d₁ d₂ : E3) {R : E3} (hR : R ≠ 0) :
    fderiv ℝ (dipolePotential d₁) R d₂ = dipoleInteraction d₁ d₂ R :=
  fderiv_dipolePotential_apply d₁ d₂ hR

example :
    ∃ C, 0 ≤ C ∧ ∀ {ρ : E3 → ℝ}, Continuous ρ → ∀ {a : ℝ}, 0 ≤ a →
      tsupport ρ ⊆ closedBall 0 a → totalCharge ρ = 0 → ∀ d₁ R : E3, a < ‖R‖ →
        |externalEnergy ρ (fun y => dipolePotential d₁ (y + R)) -
            dipoleInteraction d₁ (dipoleMoment ρ) R| ≤
          C * ‖d₁‖ * (∫ y, |ρ y| * ‖y‖ ^ 2) / (‖R‖ - a) ^ 4 :=
  abs_externalEnergy_dipolePotential_sub_le

example (c : E3) :
    tsupport (neutralPair c) ⊆ closedBall 0 (2 + ‖c‖) :=
  tsupport_neutralPair c

example (c : E3) :
    ∃ C, ∀ d₁ R : E3, 2 + ‖c‖ < ‖R‖ →
      |externalEnergy (neutralPair c) (fun y => dipolePotential d₁ (y + R)) -
          dipoleInteraction d₁ (dipoleMoment (neutralPair c)) R| ≤
        C * ‖d₁‖ * (∫ y, |neutralPair c y| * ‖y‖ ^ 2) / (‖R‖ - (2 + ‖c‖)) ^ 4 :=
  neutralPair_dipole_dipole_instance c

end ProjectAinos.Electrodynamics.Multipole

end Multipole

open ProjectAinos.Electrodynamics.Multipole ProjectAinos.SpecialFunctions.SphericalHarmonics

example (ρ : EuclideanSpace ℝ (Fin 3) → ℝ) (n : ℕ) (i : Fin (2 * n + 1)) :
    sphericalMoment ρ n i = ∫ y, ρ y * MvPolynomial.eval y
      (solidRepresentative n (realBasis n i)).val.val := rfl

example {ρ : EuclideanSpace ℝ (Fin 3) → ℝ} (hρ : Continuous ρ) (hcomp : HasCompactSupport ρ)
    (n : ℕ) (u : UnitSphere 3) {r : ℝ} (hr : 0 < r) :
    multipoleTerm ρ n (r • u.val) = ((2 * (n : ℝ) + 1) * r ^ (n + 1))⁻¹ *
      ∑ i, representative 3 n (realBasis n i) u * sphericalMoment ρ n i :=
  multipoleTerm_eq_sphericalMoments hρ hcomp n u hr

open Metric MeasureTheory ProjectAinos.SmoothGeometry.Potential
local notation "Space3" => EuclideanSpace ℝ (Fin 3)

example (ρ σ : Space3 → ℝ) (n : ℕ) (i : Fin (2 * n + 1)) : interactionMoment ρ σ n i =
    ∫ p : Space3 × Space3, σ p.1 * ρ p.2 * MvPolynomial.eval (p.2 - p.1)
      (solidRepresentative n (realBasis n i)).val.val ∂(volume.prod volume) := rfl

example {ρ σ : Space3 → ℝ} (hρ : Continuous ρ) (hσ : Continuous σ)
    {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hsa : tsupport ρ ⊆ closedBall 0 a)
    (hsb : tsupport σ ⊆ closedBall 0 b) (hr : a + b < r) (u : UnitSphere 3) :
    HasSum (fun n : ℕ => ((2 * (n : ℝ) + 1) * r ^ (n + 1))⁻¹ *
      ∑ i, representative 3 n (realBasis n i) u * interactionMoment ρ σ n i)
      (externalEnergy σ (fun z => newtonPotential ρ (r • u.val + z))) :=
  hasSum_interactionEnergy hρ hσ ha hb hsa hsb hr u

example {r : ℝ} (hr : 4 < r) (u : UnitSphere 3) :
    HasSum (fun n : ℕ => ((2 * (n : ℝ) + 1) * r ^ (n + 1))⁻¹ *
      ∑ i, representative 3 n (realBasis n i) u *
        interactionMoment ProjectAinos.Electrodynamics.Electrostatics.bumpCharge
          ProjectAinos.Electrodynamics.Electrostatics.bumpCharge n i)
      (externalEnergy ProjectAinos.Electrodynamics.Electrostatics.bumpCharge
        (fun z => newtonPotential ProjectAinos.Electrodynamics.Electrostatics.bumpCharge
          (r • u.val + z))) :=
  hasSum_interactionEnergy continuous_bumpCharge continuous_bumpCharge (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num : (0 : ℝ) ≤ 2) tsupport_bumpCharge tsupport_bumpCharge (by linarith) u
