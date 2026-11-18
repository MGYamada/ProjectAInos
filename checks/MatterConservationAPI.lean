/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.GeneralRelativity.ScalarFieldEquation
import ProjectAinos.Electrodynamics.CanonicalStress

/-! Public consumers of the conservation of matter and the comparison of stress tensors: metric
compatibility of the coefficients, the covariant Hessian, the wave operator and the divergence
of a field of coefficients with its native reading, the divergence of the stress of a scalar
field, the field equation of the scalar field from its action with the wave operator in
divergence form, the Klein–Gordon equation with the conservation of the stress and a solution in
Minkowski space, the symmetric and the canonical stress tensor of a one-form in the jet ring with
the term of Belinfante, and their evaluation on the jet of a potential, where the symmetric
tensor is the Hilbert tensor of the field. Default elaborator options are intentional: these
checks must not rely on the implementation's transparency settings. Every statement is pinned
with its type. -/

noncomputable section

open Set TopologicalSpace

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

namespace CoordinateMetric

variable {U : Opens (MinkowskiModel d)} {g : CoordinateMetric σ d U}

example {x : MinkowskiModel d} (hx : x ∈ U) (a b c : Fin (d + 1)) :
    fderiv ℝ (fun z => g.coefficient z a b) x (Pi.single c 1) =
      ∑ l, (christoffelOf g.coefficient x l c a * g.coefficient x l b +
        christoffelOf g.coefficient x l c b * g.coefficient x a l) :=
  fderiv_coefficient hx a b c

example {φ : MinkowskiModel d → ℝ} (hφ : ContDiffOn ℝ ∞ φ U) {x : MinkowskiModel d} (hx : x ∈ U)
    (a b : Fin (d + 1)) :
    fderiv ℝ (fun z => fderiv ℝ φ z (Pi.single b 1)) x (Pi.single a 1) =
      fderiv ℝ (fun z => fderiv ℝ φ z (Pi.single a 1)) x (Pi.single b 1) :=
  fderiv_fderiv_comm hφ hx a b

example (φ : MinkowskiModel d → ℝ) (x : MinkowskiModel d) (a b : Fin (d + 1)) :
    ℝ :=
  hessianOf g φ x a b

example (φ : MinkowskiModel d → ℝ) (x : MinkowskiModel d) :
    ℝ :=
  boxOf g φ x

example (T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (b : Fin (d + 1)) :
    ℝ :=
  divergenceOf g T x b

example {φ : MinkowskiModel d → ℝ} (hφ : ContDiffOn ℝ ∞ φ U) {x : MinkowskiModel d} (hx : x ∈ U)
    (a b : Fin (d + 1)) :
    g.hessianOf φ x a b = g.hessianOf φ x b a :=
  hessianOf_symm hφ hx a b

example {T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hT : ∀ i k, ContDiffOn ℝ ∞ (fun x => T x i k) U) (x : U) (b : Fin (d + 1)) :
    g.toLorentzMetric.bilinearDivergenceCovector (bilinearOf T hT) x
        (chartField (physicalChart x) (Pi.single b 1) x) = g.divergenceOf T x b :=
  bilinearDivergence_bilinearOf hT x b

example {n : ℕ} (f : Fin n → Fin n → Fin n → ℝ) :
    ∑ x, ∑ y, ∑ z, f z y x = ∑ x, ∑ y, ∑ z, f x y z :=
  sum_sum_sum_rotate f

section Scalar

variable {φ : MinkowskiModel d → ℝ}

example (m : ℝ) (φ : MinkowskiModel d → ℝ) (z : MinkowskiModel d) :
    ℝ :=
  scalarInvariant g m φ z

example (m : ℝ) (φ : MinkowskiModel d → ℝ) (z : MinkowskiModel d) (a b : Fin (d + 1)) :
    g.scalarStress m φ z a b = fderiv ℝ φ z (Pi.single a 1) * fderiv ℝ φ z (Pi.single b 1) -
      1 / 2 * (g.coefficient z a b * g.scalarInvariant m φ z) :=
  scalarStress_eq m φ z a b

example (hφ : ContDiffOn ℝ ∞ φ U) {x : MinkowskiModel d} (hx : x ∈ U) (v : MinkowskiModel d) :
    DifferentiableAt ℝ (fun z => fderiv ℝ φ z v) x :=
  differentiableAt_fderiv_apply hφ hx v

example (hφ : ContDiffOn ℝ ∞ φ U) (m : ℝ) {x : MinkowskiModel d} (hx : x ∈ U) (c : Fin (d + 1)) :
    fderiv ℝ (g.scalarInvariant m φ) x (Pi.single c 1) =
      2 * ∑ e₁, ∑ e₂, (g.coefficient x)⁻¹ e₁ e₂ * g.hessianOf φ x c e₁ *
        fderiv ℝ φ x (Pi.single e₂ 1) + 2 * m ^ 2 * φ x * fderiv ℝ φ x (Pi.single c 1) :=
  fderiv_scalarInvariant hφ m hx c

example (hφ : ContDiffOn ℝ ∞ φ U) (m : ℝ) {x : MinkowskiModel d} (hx : x ∈ U) :
    DifferentiableAt ℝ (g.scalarInvariant m φ) x :=
  differentiableAt_scalarInvariant hφ m hx

example (hφ : ContDiffOn ℝ ∞ φ U) (m : ℝ) {x : MinkowskiModel d} (hx : x ∈ U)
    (a b c : Fin (d + 1)) :
    fderiv ℝ (fun z => g.scalarStress m φ z a b) x (Pi.single c 1) -
        ∑ l, christoffelOf g.coefficient x l c a * g.scalarStress m φ x l b -
        ∑ l, christoffelOf g.coefficient x l c b * g.scalarStress m φ x a l =
      g.hessianOf φ x c a * fderiv ℝ φ x (Pi.single b 1) +
        fderiv ℝ φ x (Pi.single a 1) * g.hessianOf φ x c b -
        1 / 2 * (g.coefficient x a b * fderiv ℝ (g.scalarInvariant m φ) x (Pi.single c 1)) :=
  covariantDerivative_scalarStress hφ m hx a b c

example (hφ : ContDiffOn ℝ ∞ φ U) (m : ℝ) {x : MinkowskiModel d} (hx : x ∈ U) (b : Fin (d + 1)) :
    g.divergenceOf (g.scalarStress m φ) x b =
      (g.boxOf φ x - m ^ 2 * φ x) * fderiv ℝ φ x (Pi.single b 1) :=
  divergenceOf_scalarStress hφ m hx b

end Scalar

end CoordinateMetric

end ProjectAinos.SmoothGeometry

end

noncomputable section

open Set TopologicalSpace MeasureTheory Filter

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

namespace CoordinateMetric

variable {U : Opens (MinkowskiModel d)} {g : CoordinateMetric σ d U}
  {φ ψ : MinkowskiModel d → ℝ}

example (m : ℝ) (φ : MinkowskiModel d → ℝ) (x : MinkowskiModel d) :
    ℝ :=
  fieldDensity g m φ x

example (m : ℝ) (φ ψ : MinkowskiModel d → ℝ) (ε : ℝ) :
    ℝ :=
  fieldAction g m φ ψ ε

example (m : ℝ) (φ ψ : MinkowskiModel d → ℝ) (p : ℝ × MinkowskiModel d) :
    ℝ :=
  fieldVariationDensity g m φ ψ p

example {x : MinkowskiModel d} (hx : x ∉ tsupport ψ) :
    fderiv ℝ ψ x = 0 :=
  fderiv_eq_zero_of_notMem hx

example (hφ : ContDiffOn ℝ ∞ φ U) (hψ : ContDiff ℝ ∞ ψ) (hKU : tsupport ψ ⊆ U) (m ε : ℝ)
    (x : MinkowskiModel d) :
    g.fieldDensity m (fun z => φ z + ε * ψ z) x - g.fieldDensity m φ x =
      g.fieldVariationDensity m φ ψ (ε, x) - g.fieldVariationDensity m φ ψ (0, x) :=
  fieldDensity_sub_eq hφ hψ hKU m ε x

example (m : ℝ) {x : MinkowskiModel d} (hx : x ∉ tsupport ψ) (t : ℝ) :
    g.fieldVariationDensity m φ ψ (t, x) = g.fieldVariationDensity m φ ψ (0, x) :=
  fieldVariationDensity_of_notMem m hx t

example (hφ : ContDiffOn ℝ ∞ φ U) (hψ : ContDiff ℝ ∞ ψ) (m : ℝ) {p : ℝ × MinkowskiModel d}
    (hp : p.2 ∈ U) :
    ContDiffAt ℝ ∞ (g.fieldVariationDensity m φ ψ) p :=
  contDiffAt_fieldVariationDensity hφ hψ m hp

example (m : ℝ) (φ ψ : MinkowskiModel d → ℝ) (x : MinkowskiModel d) :
    ℝ :=
  fieldVariationDeriv g m φ ψ x

example (m : ℝ) (φ ψ : MinkowskiModel d → ℝ) (x : MinkowskiModel d) :
    HasDerivAt (fun t => g.fieldVariationDensity m φ ψ (t, x)) (g.fieldVariationDeriv m φ ψ x)
      0 :=
  hasDerivAt_fieldVariationDensity m φ ψ x

example {n : ℕ} (D : ℝ) (X Y : Fin n → Fin n → ℝ) (P W Z A : Fin n → ℝ) :
    D * ∑ a, ((-∑ e, (X a e + Y a e)) * P a + W a) + (∑ a, A a * P a) * (D * ∑ c, Z c) =
      D * (∑ a, W a - ∑ a, ∑ e, X a e * P a - ∑ a, ∑ e, Y a e * P a +
        ∑ c, ∑ a, Z c * A a * P a) :=
  split_aux D X Y P W Z A

example (hφ : ContDiffOn ℝ ∞ φ U) {x : MinkowskiModel d} (hx : x ∈ U) :
    ∑ b, fderiv ℝ (fun z => densityOf g.coefficient z *
      ∑ a, (g.coefficient z)⁻¹ a b * fderiv ℝ φ z (Pi.single a 1)) x (Pi.single b 1) =
      densityOf g.coefficient x * g.boxOf φ x :=
  sum_fderiv_density_inv_mul hφ hx

example (hφ : ContDiffOn ℝ ∞ φ U) (v : MinkowskiModel d) :
    ContDiffOn ℝ ∞ (fun z => fderiv ℝ φ z v) U :=
  contDiffOn_fderiv_apply hφ v

example :
    ContDiffOn ℝ ∞ (fun z => densityOf g.coefficient z) U :=
  contDiffOn_densityOf

example (hφ : ContDiffOn ℝ ∞ φ U) (b : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => densityOf g.coefficient z *
      ∑ a, (g.coefficient z)⁻¹ a b * fderiv ℝ φ z (Pi.single a 1)) U :=
  contDiffOn_density_inv_mul hφ b

example (hφ : ContDiffOn ℝ ∞ φ U) :
    ContinuousOn (fun z => g.boxOf φ z) U :=
  continuousOn_boxOf hφ

example (hφ : ContDiffOn ℝ ∞ φ U) (hψ : ContDiff ℝ ∞ ψ) (hK : HasCompactSupport ψ)
    (hKU : tsupport ψ ⊆ U) (m : ℝ) :
    HasDerivAt (g.fieldAction m φ ψ)
      (∫ x, ψ x * ((g.boxOf φ x - m ^ 2 * φ x) * densityOf g.coefficient x)) 0 :=
  hasDerivAt_fieldAction hφ hψ hK hKU m

example (hφ : ContDiffOn ℝ ∞ φ U) (m : ℝ) :
    (∀ ψ : MinkowskiModel d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      HasDerivAt (g.fieldAction m φ ψ) 0 0) ↔ ∀ x ∈ U, g.boxOf φ x = m ^ 2 * φ x :=
  isFieldStationary_iff hφ m

example (hφ : ContDiffOn ℝ ∞ φ U) (m : ℝ) (y : U) (b : Fin (d + 1)) :
    g.toLorentzMetric.bilinearDivergenceCovector
        (bilinearOf (g.scalarStress m φ) (contDiffOn_scalarStress hφ m)) y
        (chartField (physicalChart y) (Pi.single b 1) y) =
      (g.boxOf φ y - m ^ 2 * φ y) * fderiv ℝ φ y (Pi.single b 1) :=
  bilinearDivergence_scalarStress hφ m y b

example (hφ : ContDiffOn ℝ ∞ φ U) (m : ℝ) (hKG : ∀ x ∈ U, g.boxOf φ x = m ^ 2 * φ x) (y : U) :
    g.toLorentzMetric.bilinearDivergenceCovector
      (bilinearOf (g.scalarStress m φ) (contDiffOn_scalarStress hφ m)) y = 0 :=
  bilinearDivergence_scalarStress_eq_zero hφ m hKG y

end CoordinateMetric

end ProjectAinos.SmoothGeometry

end

noncomputable section

namespace ProjectAinos.Variational.FieldJetRing

open SmoothAlgebra

variable {ι J : Type*} [CommRing J] [Algebra ℝ J] [SmoothRing J] [Fintype ι] [DecidableEq ι]
  {R : FieldJetRing ι ι J}

example (η : ι → ι → ℝ) (μ a : ι) :
    R.raisedFieldStrength η μ a = -R.raisedFieldStrength η a μ :=
  raisedFieldStrength_antisymm η μ a

example {η : ι → ι → ℝ} (hη : ∀ μ ν, η μ ν = η ν μ) (b : ι) :
    R.euler b (R.quadraticLagrangian (gaugeConstants η)) =
      ∑ μ, R.totalDeriv μ (R.raisedFieldStrength η μ b) :=
  euler_gauge hη b

example (η : ι → ι → ℝ) (μ ν : ι) :
    J :=
  symmetricStress R η μ ν

example {η : ι → ι → ℝ} (hη : ∀ μ ν, η μ ν = η ν μ) (μ ν : ι) :
    R.symmetricStress η μ ν + R.stress (R.quadraticLagrangian (gaugeConstants η)) μ ν +
        R.divergence (fun a => R.raisedFieldStrength η μ a * R.u ν 0) =
      -(R.u ν 0 * R.euler μ (R.quadraticLagrangian (gaugeConstants η))) :=
  symmetricStress_add_stress hη μ ν

example {η : ι → ι → ℝ} (hη : ∀ μ ν, η μ ν = η ν μ) (μ ν : ι) :
    R.symmetricStress η μ ν + R.stress (R.quadraticLagrangian (gaugeConstants η)) μ ν +
        R.divergence (fun a => R.raisedFieldStrength η μ a * R.u ν 0) ∈
      R.eulerLagrangeIdeal (R.quadraticLagrangian (gaugeConstants η)) :=
  symmetricStress_add_stress_mem hη μ ν

example (η : ι → ι → ℝ) (ν : ι) :
    R.divergence (fun μ => R.divergence (fun a => R.raisedFieldStrength η μ a * R.u ν 0)) =
      0 :=
  divergence_belinfante η ν

example {η : ι → ι → ℝ} (hη : ∀ μ ν, η μ ν = η ν μ) (ν : ι) :
    R.Conserved (R.quadraticLagrangian (gaugeConstants η))
      fun μ => R.symmetricStress η μ ν :=
  conserved_symmetricStress hη ν

end ProjectAinos.Variational.FieldJetRing

end

noncomputable section

open Set TopologicalSpace MeasureTheory Filter

open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.EinsteinEquations

open SmoothGeometry CoordinateMetric

open LorentzMetric (chartField)

variable {U : Opens (MinkowskiModel 3)} (g : CoordinateMetric .timeNegative 3 U)

example (m : ℝ) (φ : MinkowskiModel 3 → ℝ) :
    Prop :=
  KleinGordon g m φ

variable {g} {φ : MinkowskiModel 3 → ℝ}

example (hφ : ContDiffOn ℝ ∞ φ U) (m : ℝ) :
    (∀ ψ : MinkowskiModel 3 → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      HasDerivAt (g.fieldAction m φ ψ) 0 0) ↔ KleinGordon g m φ :=
  isFieldStationary_iff_kleinGordon hφ m

example (hφ : ContDiffOn ℝ ∞ φ U) (m : ℝ) (y : U) (b : Fin (3 + 1)) :
    g.toLorentzMetric.bilinearDivergenceCovector
        (bilinearOf (MatterAction.scalarField g m φ hφ).stress
          (MatterAction.scalarField g m φ hφ).stress_smooth) y
        (chartField (physicalChart y) (Pi.single b 1) y) =
      (g.boxOf φ y - m ^ 2 * φ y) * fderiv ℝ φ y (Pi.single b 1) :=
  divergence_scalarStress hφ m y b

example (hφ : ContDiffOn ℝ ∞ φ U) (m : ℝ) (hKG : KleinGordon g m φ) (y : U) :
    g.toLorentzMetric.bilinearDivergenceCovector
      (bilinearOf (MatterAction.scalarField g m φ hφ).stress
        (MatterAction.scalarField g m φ hφ).stress_smooth) y = 0 :=
  divergence_scalarStress_eq_zero hφ m hKG y

local notation "η₄" => CoordinateMetric.minkowski LorentzConvention.timeNegative 3 ⊤

example (m : ℝ) (z : MinkowskiModel 3) :
    HasFDerivAt (fun x : MinkowskiModel 3 => Real.exp (m * x 1))
      ((Real.exp (m * z 1) * m) • (ContinuousLinearMap.proj 1 : MinkowskiModel 3 →L[ℝ] ℝ)) z :=
  hasFDerivAt_exp_coord m z

example (m : ℝ) :
    KleinGordon (η₄) m (fun x => Real.exp (m * x 1)) :=
  kleinGordon_exp m

end ProjectAinos.GeneralRelativity.EinsteinEquations

end

noncomputable section

open TopologicalSpace

namespace ProjectAinos.Electrodynamics

open SmoothAlgebra Variational SmoothGeometry

local notation "R₄" => StandardFieldJet.jetRing (Fin 4) (Fin 4)

example (μ ν : Fin 4) :
    ℝ :=
  etaMatrix μ ν

example (μ ν : Fin 4) :
    etaMatrix μ ν = etaMatrix ν μ :=
  etaMatrix_symm μ ν

example (A : Fin 4 → SmoothOperation 4) (x : MinkowskiModel 3) :
    Matrix (Fin (3 + 1)) (Fin (3 + 1)) ℝ :=
  potentialField A x

example (A : Fin 4 → SmoothOperation 4) (a μ : Fin 4) (x : Fin 4 → ℝ) :
    StandardFieldJet.prolongation A ((R₄).u a {μ}) x = fderiv ℝ (A a) x (Pi.single μ 1) :=
  prolongation_u_single A a μ x

example (A : Fin 4 → SmoothOperation 4) (a b : Fin 4) (x : Fin 4 → ℝ) :
    StandardFieldJet.prolongation A ((R₄).fieldStrength a b) x = potentialField A x a b :=
  prolongation_fieldStrength A a b x

example (A : Fin 4 → SmoothOperation 4) (r : ℝ) (x : Fin 4 → ℝ) :
    StandardFieldJet.prolongation A (algebraMap ℝ (StandardFieldJet (Fin 4) (Fin 4)) r) x = r :=
  prolongation_algebraMap A r x

example {ι : Type*} (s : Finset ι) (f : ι → SmoothOperation 4) (x : Fin 4 → ℝ) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x :=
  eval_sum s f x

example (f g : SmoothOperation 4) (x : Fin 4 → ℝ) :
    (f * g) x = f x * g x :=
  eval_mul f g x

example (f g : SmoothOperation 4) (x : Fin 4 → ℝ) :
    (f + g) x = f x + g x :=
  eval_add f g x

example (f g : SmoothOperation 4) (x : Fin 4 → ℝ) :
    (f - g) x = f x - g x :=
  eval_sub f g x

example (f : SmoothOperation 4) (x : Fin 4 → ℝ) :
    (-f) x = -f x :=
  eval_neg f x

example (A : Fin 4 → SmoothOperation 4) (μ a : Fin 4) (x : Fin 4 → ℝ) :
    StandardFieldJet.prolongation A ((R₄).raisedFieldStrength etaMatrix μ a) x =
      ∑ ν, ∑ b, etaMatrix μ ν * etaMatrix a b * potentialField A x ν b :=
  prolongation_raisedFieldStrength A μ a x

example (A : Fin 4 → SmoothOperation 4) (μ a : Fin 4) (x : Fin 4 → ℝ) :
    StandardFieldJet.prolongation A ((R₄).raisedFieldStrength etaMatrix μ a) x =
      lorentzSign .timeNegative μ * lorentzSign .timeNegative a * potentialField A x μ a :=
  prolongation_raisedFieldStrength_eq A μ a x

example {U : Opens (MinkowskiModel 3)} (x : MinkowskiModel 3) :
    ((CoordinateMetric.minkowski .timeNegative 3 U).coefficient x)⁻¹ =
      Matrix.diagonal (lorentzSign .timeNegative) :=
  minkowski_inv_coefficient x

example {n : ℕ} (η : Fin n → Fin n → ℝ) (hη : ∀ μ ν, η μ ν = η ν μ) (w : Fin n → Fin n → ℝ) :
    1 / 2 * ∑ a, ∑ μ, ∑ b, ∑ ν, (η μ b * η ν a - η μ ν * η a b) * (w a μ * w b ν) =
      -(∑ a, ∑ b, ∑ c, ∑ e, η a c * η b e * ((w b a - w a b) * (w e c - w c e))) / 4 :=
  gauge_quadratic_identity η hη w

example (A : Fin 4 → SmoothOperation 4) (x : Fin 4 → ℝ) :
    StandardFieldJet.prolongation A
        ((R₄).quadraticLagrangian (FieldJetRing.gaugeConstants etaMatrix)) x =
      -(CoordinateMetric.minkowski .timeNegative 3 ⊤).maxwellInvariant (potentialField A) x /
        4 :=
  prolongation_gaugeLagrangian A x

example (A : Fin 4 → SmoothOperation 4) (μ ν : Fin 4) (x : Fin 4 → ℝ) :
    StandardFieldJet.prolongation A ((R₄).symmetricStress etaMatrix μ ν) x =
      ∑ α, etaMatrix μ α *
        (CoordinateMetric.minkowski .timeNegative 3 ⊤).maxwellStress (potentialField A) x α ν :=
  prolongation_symmetricStress A μ ν x

example (A : Fin 4 → SmoothOperation 4)
    (hA : StandardFieldJet.IsSolution
      ((R₄).quadraticLagrangian (FieldJetRing.gaugeConstants etaMatrix)) A)
    (μ ν : Fin 4) (x : Fin 4 → ℝ) :
    ∑ α, etaMatrix μ α *
        (CoordinateMetric.minkowski .timeNegative 3 ⊤).maxwellStress (potentialField A) x α ν =
      -StandardFieldJet.prolongation A
          ((R₄).stress ((R₄).quadraticLagrangian (FieldJetRing.gaugeConstants etaMatrix)) μ ν) x -
        StandardFieldJet.prolongation A ((R₄).divergence
          (fun a => (R₄).raisedFieldStrength etaMatrix μ a * (R₄).u ν 0)) x :=
  hilbertStress_eq_neg_canonical A hA μ ν x

end ProjectAinos.Electrodynamics

end
