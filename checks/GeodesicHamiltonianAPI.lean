/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.GeneralRelativity.SchwarzschildEquatorial

/-! Public consumers of the geodesic Hamiltonian: Hamilton's equations of `½ g^{μν} p_μ p_ν`,
the bracket of a momentum with the Hamiltonian, the Killing equation of the metric and of its
inverse, the integrals of the motion, the equivalence of the trajectories with the geodesics of
the chart, the rest trajectory, the conserved Killing pairing and the red shift, and the
equatorial plane of the exterior Schwarzschild field as an instance.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section

namespace ProjectAinos.GeneralRelativity.GeodesicHamiltonian

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace Mechanics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

example (ξ : ι → FreeSmoothRing ι) (b : ι) :
    (canonical ι).bracket (q b) (vectorMomentum ξ) = ofPosition ι (ξ b) :=
  canonical_q_vectorMomentum ξ b

example (F : ι → ι → FreeSmoothRing ι) (a : ι) :
    (canonical ι).bracket (q a) (quadratic F) =
      vectorMomentum (fun μ => F μ a) + vectorMomentum (F a) :=
  canonical_q_quadratic F a

example (F : ι → ι → FreeSmoothRing ι) (l : ι) :
    (canonical ι).bracket (p l) (quadratic F) =
      -quadratic (fun μ ν => partialDerivation l (F μ ν)) :=
  canonical_p_quadratic F l

example (ξ : ι → FreeSmoothRing ι) (f : FreeSmoothRing ι)
    (α β : ι) :
    (canonical ι).bracket (vectorMomentum ξ) (ofPosition ι f * (p α * p β)) =
      -∑ l, ofPosition ι (ξ l * partialDerivation l f) * (p α * p β) +
        (∑ μ, ofPosition ι (f * partialDerivation α (ξ μ)) * (p μ * p β) +
          ∑ μ, ofPosition ι (f * partialDerivation β (ξ μ)) * (p α * p μ)) :=
  canonical_vectorMomentum_term ξ f α β

example (ξ : ι → FreeSmoothRing ι)
    (F : ι → ι → FreeSmoothRing ι) :
    (canonical ι).bracket (vectorMomentum ξ) (quadratic F) = -quadratic (lieInverse ξ F) :=
  canonical_vectorMomentum_quadratic ξ F

variable {gi gm : ι → ι → FreeSmoothRing ι}

example (hs : ∀ μ ν, gi μ ν = gi ν μ) (a : ι) :
    (canonical ι).bracket (q a) (hamiltonian gi) = velocity gi a :=
  canonical_q_hamiltonian hs a

example (l : ι) :
    (canonical ι).bracket (p l) (hamiltonian gi) =
      -(algebraMap ℝ (PhaseSpace ι) (1 / 2) *
        quadratic (fun μ ν => partialDerivation l (gi μ ν))) :=
  canonical_p_hamiltonian l

example (ξ : ι → FreeSmoothRing ι) :
    (canonical ι).bracket (vectorMomentum ξ) (hamiltonian gi) =
      -(algebraMap ℝ (PhaseSpace ι) (1 / 2) * quadratic (lieInverse ξ gi)) :=
  canonical_vectorMomentum_hamiltonian ξ

example (F : ι → ι → FreeSmoothRing ι) (a b : ι) :
    (canonical ι).bracket (q b) ((canonical ι).bracket (q a) (quadratic F)) =
      ofPosition ι (F b a + F a b) :=
  canonical_q_q_quadratic F a b

example (hs : ∀ μ ν, gi μ ν = gi ν μ) (ξ : ι → FreeSmoothRing ι) (μ ν : ι) :
    lieInverse ξ gi μ ν = lieInverse ξ gi ν μ :=
  lieInverse_symm hs ξ μ ν

example {ξ : ι → FreeSmoothRing ι}
    (hξ : ∀ μ ν, lieInverse ξ gi μ ν = 0) :
    (canonical ι).IsIntegral (hamiltonian gi) (vectorMomentum ξ) :=
  isIntegral_vectorMomentum_of_lieInverse hξ

example (hs : ∀ μ ν, gi μ ν = gi ν μ) (ξ : ι → FreeSmoothRing ι) :
    (canonical ι).IsIntegral (hamiltonian gi) (vectorMomentum ξ) ↔
      ∀ μ ν, lieInverse ξ gi μ ν = 0 :=
  isIntegral_vectorMomentum_iff hs ξ

example {k : ι} (h : ∀ μ ν, partialDerivation k (gi μ ν) = 0) :
    (canonical ι).IsIntegral (hamiltonian gi) (p k) :=
  isIntegral_p_of_independent h

example (k : ι) : vectorMomentum (coordinateField k) = p k :=
  vectorMomentum_coordinateField k

example (k : ι) (gi : ι → ι → FreeSmoothRing ι) (μ ν : ι) :
    lieInverse (coordinateField k) gi μ ν = partialDerivation k (gi μ ν) :=
  lieInverse_coordinateField k gi μ ν

example (l : ι) (M N : Matrix ι ι (FreeSmoothRing ι)) :
    matrixDeriv l (M * N) = matrixDeriv l M * N + M * matrixDeriv l N :=
  matrixDeriv_mul l M N

omit [Fintype ι] in
example (l : ι) : matrixDeriv l (1 : Matrix ι ι (FreeSmoothRing ι)) = 0 :=
  matrixDeriv_one l

example (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0)
    (ξ : ι → FreeSmoothRing ι) :
    Matrix.of (lieInverse ξ gi) = -(Matrix.of gi * Matrix.of (lieMetric ξ gm) * Matrix.of gi) :=
  of_lieInverse hinv ξ

example (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0)
    (ξ : ι → FreeSmoothRing ι) :
    Matrix.of (lieMetric ξ gm) = -(Matrix.of gm * Matrix.of (lieInverse ξ gi) * Matrix.of gm) :=
  of_lieMetric hinv ξ

example (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0)
    (ξ : ι → FreeSmoothRing ι) :
    (∀ μ ν, lieInverse ξ gi μ ν = 0) ↔ ∀ μ ν, lieMetric ξ gm μ ν = 0 :=
  lieInverse_eq_zero_iff hinv ξ

example (k : ι) (gm : ι → ι → FreeSmoothRing ι) (μ ν : ι) :
    lieMetric (coordinateField k) gm μ ν = partialDerivation k (gm μ ν) :=
  lieMetric_coordinateField k gm μ ν

example (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0) (μ ν : ι) :
    ∑ l, gi μ l * gm l ν = if μ = ν then 1 else 0 :=
  inverse_mul hinv μ ν

example (hm : ∀ μ ν, gm μ ν = gm ν μ)
    (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0) (μ ν : ι) :
    gi μ ν = gi ν μ :=
  inverse_symm hm hinv μ ν

example
    (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0) {ξ : ι → FreeSmoothRing ι}
    (hξ : ∀ μ ν, lieMetric ξ gm μ ν = 0) :
    (canonical ι).IsIntegral (hamiltonian gi) (vectorMomentum ξ) :=
  isIntegral_vectorMomentum_of_killing hinv hξ

example (hm : ∀ μ ν, gm μ ν = gm ν μ)
    (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0) (ξ : ι → FreeSmoothRing ι) :
    (canonical ι).IsIntegral (hamiltonian gi) (vectorMomentum ξ) ↔
      ∀ μ ν, lieMetric ξ gm μ ν = 0 :=
  isIntegral_vectorMomentum_iff_killing hm hinv ξ

example
    (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0) {k : ι}
    (h : ∀ μ ν, partialDerivation k (gm μ ν) = 0) :
    (canonical ι).IsIntegral (hamiltonian gi) (p k) :=
  isIntegral_p_of_metric_independent hinv h

example (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0)
    (μ : ι) : p μ = ∑ ν, ofPosition ι (gm μ ν) * velocity gi ν :=
  p_eq_sum_velocity hinv μ

omit [DecidableEq ι] in
example :
    hamiltonian gi = algebraMap ℝ (PhaseSpace ι) (1 / 2) * ∑ μ, p μ * velocity gi μ :=
  hamiltonian_eq_sum

example (hm : ∀ μ ν, gm μ ν = gm ν μ)
    (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0) (l : ι) :
    (canonical ι).bracket (p l) (hamiltonian gi) =
      algebraMap ℝ (PhaseSpace ι) (1 / 2) *
        ∑ α, ∑ β, ofPosition ι (partialDerivation l (gm α β)) *
          (velocity gi α * velocity gi β) :=
  canonical_p_hamiltonian_eq hm hinv l

example {B : Type*} [CommRing B] [Algebra ℝ B] [SmoothRing B]
    (φ : SmoothRingHom (FreeSmoothRing ι) B) (v : ι → B) (l : ι) :
    ∑ α, ∑ β, φ (partialDerivation α (gm l β) - christoffelLower gm l α β) * (v α * v β) =
      algebraMap ℝ B (1 / 2) *
        ∑ α, ∑ β, φ (partialDerivation l (gm α β)) * (v α * v β) :=
  sum_sub_christoffelLower φ v l

example (hm : ∀ μ ν, gm μ ν = gm ν μ)
    (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0) (l : ι) :
    (canonical ι).bracket (p l) (hamiltonian gi) =
      ∑ α, ∑ β, ofPosition ι (partialDerivation α (gm l β) - christoffelLower gm l α β) *
        (velocity gi α * velocity gi β) :=
  canonical_p_hamiltonian_christoffel hm hinv l

example (x : ι → TimeFunction) (f : ι → FreeSmoothRing ι)
    (w : ι → TimeFunction) :
    timeDerivative (∑ ν, lift x (f ν) * w ν) =
      ∑ ν, lift x (f ν) * timeDerivative (w ν) +
        ∑ α, ∑ β, lift x (partialDerivation α (f β)) * (timeDerivative (x α) * w β) :=
  timeDerivative_sum x f w

omit [DecidableEq ι] in
example (c : ι ⊕ ι → TimeFunction) (μ : ι) :
    lift c (velocity gi μ) = ∑ ν, lift (position c) (gi μ ν) * c (Sum.inr ν) :=
  lift_velocity c μ

example (hm : ∀ μ ν, gm μ ν = gm ν μ)
    (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0) (c : ι ⊕ ι → TimeFunction) :
    IsTrajectory (canonical ι) (hamiltonian gi) c ↔
      (∀ μ, timeDerivative (position c μ) = lift c (velocity gi μ)) ∧
        ∀ l, timeDerivative (c (Sum.inr l)) =
          ∑ α, ∑ β, lift (position c) (partialDerivation α (gm l β) -
            christoffelLower gm l α β) * (lift c (velocity gi α) * lift c (velocity gi β)) :=
  isTrajectory_iff_velocity hm hinv c

example (hm : ∀ μ ν, gm μ ν = gm ν μ)
    (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0) (c : ι ⊕ ι → TimeFunction) :
    IsTrajectory (canonical ι) (hamiltonian gi) c ↔
      (∀ μ, c (Sum.inr μ) =
        ∑ ν, lift (position c) (gm μ ν) * timeDerivative (position c ν)) ∧
        IsCoordinateGeodesic gm (position c) :=
  isTrajectory_iff hm hinv c

example (gi : ι → ι → FreeSmoothRing ι) (x₀ : ι → ℝ) :
    IsTrajectory (canonical ι) (hamiltonian gi)
      (Sum.elim (fun μ => algebraMap ℝ TimeFunction (x₀ μ)) fun _ => 0) :=
  isTrajectory_rest gi x₀

example (G : ι → ι → ℝ) (hG : ∀ μ ν, G μ ν = G ν μ) (x₀ p₀ : ι → ℝ) :
    IsTrajectory (canonical ι) (hamiltonian fun μ ν => algebraMap ℝ (FreeSmoothRing ι) (G μ ν))
      (Sum.elim
        (fun μ => algebraMap ℝ TimeFunction (x₀ μ) +
          algebraMap ℝ TimeFunction (∑ ν, G μ ν * p₀ ν) * SmoothOperation.proj 0)
        fun μ => algebraMap ℝ TimeFunction (p₀ μ)) :=
  isTrajectory_line G hG x₀ p₀

example (hm : ∀ μ ν, gm μ ν = gm ν μ)
    (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0) {c : ι ⊕ ι → TimeFunction}
    (h : IsTrajectory (canonical ι) (hamiltonian gi) c) (ξ : ι → FreeSmoothRing ι) :
    pairing gm ξ (position c) = lift c (vectorMomentum ξ) :=
  pairing_eq_lift hm hinv h ξ

example (hm : ∀ μ ν, gm μ ν = gm ν μ)
    (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0) {c : ι ⊕ ι → TimeFunction}
    (h : IsTrajectory (canonical ι) (hamiltonian gi) c) {ξ : ι → FreeSmoothRing ι}
    (hξ : ∀ μ ν, lieMetric ξ gm μ ν = 0) (s t : Fin 1 → ℝ) :
    pairing gm ξ (position c) s = pairing gm ξ (position c) t :=
  pairing_eq_of_killing hm hinv h hξ s t

example (k : ι) (x : ι → TimeFunction) :
    norm2 gm (coordinateField k) x = lift x (gm k k) :=
  norm2_coordinateField k x

example (k : ι) (x : ι → TimeFunction) :
    pairing gm (coordinateField k) x = ∑ ν, lift x (gm k ν) * timeDerivative (x ν) :=
  pairing_coordinateField k x

omit [DecidableEq ι] in
example {x : ι → TimeFunction} {ξ : ι → FreeSmoothRing ι} {t : Fin 1 → ℝ}
    (ht : norm2 gm ξ x t < 0) :
    killingNorm gm ξ x t * frequency gm ξ x t = -pairing gm ξ x t :=
  killingNorm_mul_frequency ht

example (hm : ∀ μ ν, gm μ ν = gm ν μ)
    (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0) {c : ι ⊕ ι → TimeFunction}
    (h : IsTrajectory (canonical ι) (hamiltonian gi) c) {ξ : ι → FreeSmoothRing ι}
    (hξ : ∀ μ ν, lieMetric ξ gm μ ν = 0) {s t : Fin 1 → ℝ}
    (hs : norm2 gm ξ (position c) s < 0) (ht : norm2 gm ξ (position c) t < 0) :
    killingNorm gm ξ (position c) s * frequency gm ξ (position c) s =
      killingNorm gm ξ (position c) t * frequency gm ξ (position c) t :=
  killingNorm_mul_frequency_eq hm hinv h hξ hs ht

end ProjectAinos.GeneralRelativity.GeodesicHamiltonian

namespace ProjectAinos.GeneralRelativity.GeodesicHamiltonian.SchwarzschildEquatorial

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace Mechanics SmoothOperation

open scoped ContDiff

variable {M : ℝ}

example (hM : 0 ≤ M) (s : ℝ) : 0 < radius M s :=
  radius_pos hM s

example (M s : ℝ) (hM : 0 ≤ M) :
    Real.exp s / radius M s = 1 - 2 * M / radius M s :=
  exp_div_radius M s hM

example : ContDiff ℝ ∞ (fun x : Fin 1 → ℝ => Real.exp (x 0)) :=
  contDiff_exp_coord

example (M : ℝ) : ContDiff ℝ ∞ (fun x : Fin 1 → ℝ => radius M (x 0)) :=
  contDiff_radius M

example (hM : 0 ≤ M) (μ : Fin 3) : lowerOp hM μ * upperOp hM μ = 1 :=
  lowerOp_mul_upperOp hM μ

example (hM : 0 ≤ M) (μ ν : Fin 3) : metric hM μ ν = metric hM ν μ :=
  metric_symm hM μ ν

example (hM : 0 ≤ M) (μ ν : Fin 3) : inverse hM μ ν = inverse hM ν μ :=
  inverse_symm hM μ ν

example (hM : 0 ≤ M) (μ ν : Fin 3) :
    ∑ l, metric hM μ l * inverse hM l ν = if μ = ν then 1 else 0 :=
  metric_mul_inverse hM μ ν

example {k : Fin 3} (hk : k ≠ 1) (a : Fin 3 → SmoothOperation 1)
    (μ ν : Fin 3) : partialDerivation k (Matrix.diagonal (fun μ => ofRadial (a μ)) μ ν) = 0 :=
  partialDerivation_diagonal hk a μ ν

example {k : Fin 3} (hk : k ≠ 1) (hM : 0 ≤ M) (μ ν : Fin 3) :
    partialDerivation k (metric hM μ ν) = 0 :=
  partialDerivation_metric hk hM μ ν

example {k : Fin 3} (hk : k ≠ 1) (hM : 0 ≤ M) (μ ν : Fin 3) :
    partialDerivation k (inverse hM μ ν) = 0 :=
  partialDerivation_inverse hk hM μ ν

example (hM : 0 ≤ M) (c : Fin 3 ⊕ Fin 3 → TimeFunction) :
    IsTrajectory (canonical (Fin 3)) (hamiltonian (inverse hM)) c ↔
      (∀ μ, c (Sum.inr μ) =
        ∑ ν, lift (position c) (metric hM μ ν) * timeDerivative (position c ν)) ∧
        IsCoordinateGeodesic (metric hM) (position c) :=
  isTrajectory_iff hM c

example (hM : 0 ≤ M) :
    (canonical (Fin 3)).IsIntegral (hamiltonian (inverse hM)) (p 0) :=
  isIntegral_p_time hM

example (hM : 0 ≤ M) :
    (canonical (Fin 3)).IsIntegral (hamiltonian (inverse hM)) (p 2) :=
  isIntegral_p_angle hM

example (hM : 0 ≤ M) (μ ν : Fin 3) :
    lieMetric (coordinateField 0) (metric hM) μ ν = 0 :=
  lieMetric_time hM μ ν

example (hM : 0 ≤ M) (μ ν : Fin 3) :
    lieInverse (coordinateField 0) (inverse hM) μ ν = 0 :=
  lieInverse_time hM μ ν

example (hM : 0 ≤ M) :
    (canonical (Fin 3)).IsIntegral (hamiltonian (inverse hM))
      (vectorMomentum (coordinateField 0)) :=
  isIntegral_vectorMomentum_time hM

example (f : SmoothOperation 1) (x : Fin 3 → TimeFunction)
    (τ : Fin 1 → ℝ) : lift x (ofRadial f) τ = f fun _ => x 1 τ :=
  lift_ofRadial_apply f x τ

example (hM : 0 ≤ M) (x : Fin 3 → TimeFunction) (τ : Fin 1 → ℝ) :
    norm2 (metric hM) (coordinateField 0) x τ = -(1 - 2 * M / radius M (x 1 τ)) :=
  norm2_time hM x τ

example (hM : 0 ≤ M) (x : Fin 3 → TimeFunction) (τ : Fin 1 → ℝ) :
    norm2 (metric hM) (coordinateField 0) x τ < 0 :=
  norm2_time_neg hM x τ

example (hM : 0 ≤ M) (x : Fin 3 → TimeFunction) (τ : Fin 1 → ℝ) :
    killingNorm (metric hM) (coordinateField 0) x τ =
      Real.sqrt (1 - 2 * M / radius M (x 1 τ)) :=
  killingNorm_eq hM x τ

example (hM : 0 ≤ M) {c : Fin 3 ⊕ Fin 3 → TimeFunction}
    (h : IsTrajectory (canonical (Fin 3)) (hamiltonian (inverse hM)) c) (s t : Fin 1 → ℝ) :
    Real.sqrt (1 - 2 * M / radius M (position c 1 s)) *
        frequency (metric hM) (coordinateField 0) (position c) s =
      Real.sqrt (1 - 2 * M / radius M (position c 1 t)) *
        frequency (metric hM) (coordinateField 0) (position c) t :=
  killingNorm_mul_frequency_eq hM h s t

end ProjectAinos.GeneralRelativity.GeodesicHamiltonian.SchwarzschildEquatorial
