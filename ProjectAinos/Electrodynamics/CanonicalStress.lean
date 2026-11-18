/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Variational.FieldJet.Belinfante
public import ProjectAinos.Variational.FieldJet.Standard
public import ProjectAinos.Electrodynamics.HilbertStress

/-!
# The Hilbert tensor of the field and the canonical tensor

Landau–Lifshitz, §§32–33: the canonical energy-momentum tensor of the translations is not
symmetric; adding a divergence makes it the symmetric tensor. For a smooth potential `A` on
Minkowski space, with the jet ring of `Variational.StandardFieldJet` and its prolongation:

* `prolongation_symmetricStress`: the symmetric tensor `Θ^μ_ν` of `FieldJetRing.symmetricStress`
  on the jet of `A` is the Hilbert tensor `η^{μα} T_{αν}` of `CoordinateMetric.maxwellStress`,
  which the variation of the metric gives (`CoordinateMetric.hasDerivAt_integral_maxwellDensity`),
  for the field `F_{ab} = ∂_a A_b − ∂_b A_a`;
* `hilbertStress_eq_neg_canonical`: on a solution of the field equations,
  `η^{μα} T_{αν} = −T^μ_ν − Σₐ ∂ₐ(F^{μa} A_ν)` with the canonical tensor `T^μ_ν` of
  `FieldJetRing.stress`; the added term is divergence-free identically
  (`FieldJetRing.divergence_belinfante`).
-/

@[expose] public section

noncomputable section

open TopologicalSpace

namespace ProjectAinos.Electrodynamics

open SmoothAlgebra Variational SmoothGeometry

local notation "R₄" => StandardFieldJet.jetRing (Fin 4) (Fin 4)

/-- The Minkowski matrix `η^{μν} = η_{μν}` in the signature `(−+++)`. -/
def etaMatrix (μ ν : Fin 4) : ℝ := if μ = ν then lorentzSign .timeNegative μ else 0

theorem etaMatrix_symm (μ ν : Fin 4) : etaMatrix μ ν = etaMatrix ν μ := by
  by_cases h : μ = ν
  · subst h; rfl
  · simp [etaMatrix, h, Ne.symm h]

/-- The field strength `F_{ab} = ∂_a A_b − ∂_b A_a` of a smooth potential. -/
def potentialField (A : Fin 4 → SmoothOperation 4) (x : MinkowskiModel 3) :
    Matrix (Fin (3 + 1)) (Fin (3 + 1)) ℝ :=
  Matrix.of fun a b => fderiv ℝ (A b) x (Pi.single a 1) - fderiv ℝ (A a) x (Pi.single b 1)

theorem prolongation_u_single (A : Fin 4 → SmoothOperation 4) (a μ : Fin 4) (x : Fin 4 → ℝ) :
    StandardFieldJet.prolongation A ((R₄).u a {μ}) x = fderiv ℝ (A a) x (Pi.single μ 1) := by
  rw [StandardFieldJet.prolongation_u, ← Multiset.cons_zero,
    SmoothOperation.iterPartialDeriv_cons, SmoothOperation.iterPartialDeriv_zero,
    SmoothOperation.partialDeriv_apply]

theorem prolongation_fieldStrength (A : Fin 4 → SmoothOperation 4) (a b : Fin 4)
    (x : Fin 4 → ℝ) :
    StandardFieldJet.prolongation A ((R₄).fieldStrength a b) x = potentialField A x a b := by
  rw [FieldJetRing.fieldStrength, SmoothRingHom.map_sub]
  change StandardFieldJet.prolongation A ((R₄).u b {a}) x -
    StandardFieldJet.prolongation A ((R₄).u a {b}) x = _
  rw [prolongation_u_single, prolongation_u_single]
  rfl

theorem prolongation_algebraMap (A : Fin 4 → SmoothOperation 4) (r : ℝ) (x : Fin 4 → ℝ) :
    StandardFieldJet.prolongation A (algebraMap ℝ (StandardFieldJet (Fin 4) (Fin 4)) r) x = r := by
  rw [SmoothRingHom.map_algebraMap]
  rfl

theorem eval_sum {ι : Type*} (s : Finset ι) (f : ι → SmoothOperation 4) (x : Fin 4 → ℝ) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x :=
  map_sum (ContMDiffMap.evalRingHom x : SmoothOperation 4 →+* ℝ) f s

theorem eval_mul (f g : SmoothOperation 4) (x : Fin 4 → ℝ) : (f * g) x = f x * g x := rfl

theorem eval_add (f g : SmoothOperation 4) (x : Fin 4 → ℝ) : (f + g) x = f x + g x := rfl

theorem eval_sub (f g : SmoothOperation 4) (x : Fin 4 → ℝ) : (f - g) x = f x - g x := rfl

theorem eval_neg (f : SmoothOperation 4) (x : Fin 4 → ℝ) : (-f) x = -f x := rfl

theorem prolongation_raisedFieldStrength (A : Fin 4 → SmoothOperation 4) (μ a : Fin 4)
    (x : Fin 4 → ℝ) :
    StandardFieldJet.prolongation A ((R₄).raisedFieldStrength etaMatrix μ a) x =
      ∑ ν, ∑ b, etaMatrix μ ν * etaMatrix a b * potentialField A x ν b := by
  rw [FieldJetRing.raisedFieldStrength]
  simp only [SmoothRingHom.map_sum, SmoothRingHom.map_mul, eval_sum, eval_mul,
    prolongation_algebraMap, prolongation_fieldStrength]

/-- On a diagonal matrix the raised field strength is `F^{μa} = η_{μμ} η_{aa} F_{μa}`. -/
theorem prolongation_raisedFieldStrength_eq (A : Fin 4 → SmoothOperation 4) (μ a : Fin 4)
    (x : Fin 4 → ℝ) :
    StandardFieldJet.prolongation A ((R₄).raisedFieldStrength etaMatrix μ a) x =
      lorentzSign .timeNegative μ * lorentzSign .timeNegative a * potentialField A x μ a := by
  rw [prolongation_raisedFieldStrength]
  simp [etaMatrix, ite_mul, Finset.sum_ite_eq]

theorem minkowski_inv_coefficient {U : Opens (MinkowskiModel 3)} (x : MinkowskiModel 3) :
    ((CoordinateMetric.minkowski .timeNegative 3 U).coefficient x)⁻¹ =
      Matrix.diagonal (lorentzSign .timeNegative) := by
  rw [CoordinateMetric.minkowski_coefficient]
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.diagonal_mul_diagonal]
  simp only [SmoothGeometry.lorentzSign_sq, Matrix.diagonal_one]

/-- `½ C^{aμ,bν} w_{aμ} w_{bν} = −¼ F_{ab} F^{ab}` with `F_{ab} = w_{ba} − w_{ab}`, for the
constants of `gaugeConstants` and any symmetric matrix. -/
theorem gauge_quadratic_identity {n : ℕ} (η : Fin n → Fin n → ℝ) (hη : ∀ μ ν, η μ ν = η ν μ)
    (w : Fin n → Fin n → ℝ) :
    1 / 2 * ∑ a, ∑ μ, ∑ b, ∑ ν, (η μ b * η ν a - η μ ν * η a b) * (w a μ * w b ν) =
      -(∑ a, ∑ b, ∑ c, ∑ e, η a c * η b e * ((w b a - w a b) * (w e c - w c e))) / 4 := by
  set S1 := ∑ a, ∑ μ, ∑ b, ∑ ν, η μ ν * η a b * (w a μ * w b ν) with hS1
  set S2 := ∑ a, ∑ μ, ∑ b, ∑ ν, η μ b * η ν a * (w a μ * w b ν) with hS2
  have hL : ∑ a, ∑ μ, ∑ b, ∑ ν, (η μ b * η ν a - η μ ν * η a b) * (w a μ * w b ν) = S2 - S1 := by
    simp only [hS1, hS2, sub_mul, Finset.sum_sub_distrib]
  have hexp (a b c e : Fin n) : η a c * η b e * ((w b a - w a b) * (w e c - w c e)) =
      η a c * η b e * (w b a * w e c) - η a c * η b e * (w b a * w c e) -
        η a c * η b e * (w a b * w e c) + η a c * η b e * (w a b * w c e) := by ring
  have hT1 : ∑ a, ∑ b, ∑ c, ∑ e, η a c * η b e * (w b a * w e c) = S1 := by
    rw [hS1, Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have hT2 : ∑ a, ∑ b, ∑ c, ∑ e, η a c * η b e * (w b a * w c e) = S2 := by
    rw [hS2, Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => by rw [hη e b]
  have hT3 : ∑ a, ∑ b, ∑ c, ∑ e, η a c * η b e * (w a b * w e c) = S2 := by
    rw [hS2]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun c _ => by
        rw [hη c a]
        ring
  have hT4 : ∑ a, ∑ b, ∑ c, ∑ e, η a c * η b e * (w a b * w c e) = S1 := by
    rw [hS1]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => by ring
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, hT1, hT2, hT3, hT4]
  rw [hL]
  ring

/-- The Lagrangian `−¼ F_{ab} F^{ab}` on the jet of a potential. -/
theorem prolongation_gaugeLagrangian (A : Fin 4 → SmoothOperation 4) (x : Fin 4 → ℝ) :
    StandardFieldJet.prolongation A
        ((R₄).quadraticLagrangian (FieldJetRing.gaugeConstants etaMatrix)) x =
      -(CoordinateMetric.minkowski .timeNegative 3 ⊤).maxwellInvariant (potentialField A) x /
        4 := by
  have hD (i j : Fin 4) : Matrix.diagonal (lorentzSign (d := 3) .timeNegative) i j =
      etaMatrix i j := by
    simp [Matrix.diagonal_apply, etaMatrix]
  simp only [FieldJetRing.quadraticLagrangian, SmoothRingHom.map_mul, SmoothRingHom.map_sum,
    eval_mul, eval_sum, prolongation_algebraMap, prolongation_u_single,
    CoordinateMetric.maxwellInvariant, minkowski_inv_coefficient, hD, potentialField,
    Matrix.of_apply, FieldJetRing.gaugeConstants, neg_sub]
  exact gauge_quadratic_identity etaMatrix etaMatrix_symm
    (fun a μ => fderiv ℝ (A a) x (Pi.single μ 1))

/-- **The symmetric tensor on the jet of a potential is the Hilbert tensor**:
`Θ^μ_ν = η^{μα} T_{αν}` with `T` of `CoordinateMetric.maxwellStress` for `F = dA`. -/
theorem prolongation_symmetricStress (A : Fin 4 → SmoothOperation 4) (μ ν : Fin 4)
    (x : Fin 4 → ℝ) :
    StandardFieldJet.prolongation A ((R₄).symmetricStress etaMatrix μ ν) x =
      ∑ α, etaMatrix μ α *
        (CoordinateMetric.minkowski .timeNegative 3 ⊤).maxwellStress (potentialField A) x α ν := by
  have hite : StandardFieldJet.prolongation A
      (if μ = ν then (R₄).quadraticLagrangian (FieldJetRing.gaugeConstants etaMatrix) else 0) x =
      if μ = ν then -(CoordinateMetric.minkowski .timeNegative 3 ⊤).maxwellInvariant
        (potentialField A) x / 4 else 0 := by
    split_ifs
    · exact prolongation_gaugeLagrangian A x
    · rw [SmoothRingHom.map_zero]
      rfl
  rw [FieldJetRing.symmetricStress, SmoothRingHom.map_add, eval_add, SmoothRingHom.map_sum,
    eval_sum, hite]
  simp only [SmoothRingHom.map_mul, eval_mul, prolongation_raisedFieldStrength_eq,
    prolongation_fieldStrength, CoordinateMetric.maxwellStress, CoordinateMetric.maxwellProduct,
    minkowski_inv_coefficient, sum_diagonal_mul]
  rw [CoordinateMetric.minkowski_coefficient]
  simp only [etaMatrix, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Matrix.diagonal_apply]
  set Q := (CoordinateMetric.minkowski .timeNegative 3 ⊤).maxwellInvariant (potentialField A) x
  have hs := SmoothGeometry.lorentzSign_sq (d := 3) LorentzConvention.timeNegative μ
  have hsum : ∑ b, lorentzSign .timeNegative μ * lorentzSign .timeNegative b *
      potentialField A x μ b * potentialField A x ν b = lorentzSign .timeNegative μ *
        ∑ b, lorentzSign .timeNegative b * (potentialField A x μ b * potentialField A x ν b) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hsum]
  by_cases h : μ = ν
  · subst h
    simp only [ite_true]
    linear_combination (Q / 4) * hs
  · simp only [h, ite_false, add_zero, zero_div, zero_mul, sub_zero]

/-- **The Hilbert tensor and the canonical tensor** (Landau–Lifshitz, §§32–33): on a solution
of the field equations, `η^{μα} T_{αν} = −T^μ_ν − Σₐ ∂ₐ(F^{μa} A_ν)`, with the canonical tensor
`T^μ_ν` of the translations. -/
theorem hilbertStress_eq_neg_canonical (A : Fin 4 → SmoothOperation 4)
    (hA : StandardFieldJet.IsSolution
      ((R₄).quadraticLagrangian (FieldJetRing.gaugeConstants etaMatrix)) A)
    (μ ν : Fin 4) (x : Fin 4 → ℝ) :
    ∑ α, etaMatrix μ α *
        (CoordinateMetric.minkowski .timeNegative 3 ⊤).maxwellStress (potentialField A) x α ν =
      -StandardFieldJet.prolongation A
          ((R₄).stress ((R₄).quadraticLagrangian (FieldJetRing.gaugeConstants etaMatrix)) μ ν) x -
        StandardFieldJet.prolongation A ((R₄).divergence
          (fun a => (R₄).raisedFieldStrength etaMatrix μ a * (R₄).u ν 0)) x := by
  have h := congrArg (fun F => StandardFieldJet.prolongation A F x)
    (FieldJetRing.symmetricStress_add_stress (R := R₄) etaMatrix_symm μ ν)
  simp only [SmoothRingHom.map_add, SmoothRingHom.map_neg, SmoothRingHom.map_mul, eval_add,
    eval_neg, eval_mul, hA μ] at h
  rw [← prolongation_symmetricStress]
  have h0 : (0 : SmoothOperation 4) x = 0 := rfl
  rw [h0, mul_zero, neg_zero] at h
  linarith

end ProjectAinos.Electrodynamics
