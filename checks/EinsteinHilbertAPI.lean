/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.GeneralRelativity.EinsteinHilbertAction

/-! Public consumers of the first variation of the Einstein–Hilbert action: the stability of the
Lorentz signature under small perturbations, admissible variations `g + εh` of a coordinate
metric, the coefficient formulas for the Christoffel symbols, Ricci and scalar curvature and the
density with their native readings, families of coefficients with their parameter derivatives,
the Palatini identity, the derivative of the inverse metric in a chart, the pointwise first
variation of `(R − 2Λ) √|g|`, the integrated first variation with the vanishing divergence
term, and the physical action `(1/2κ) ∫ (R − 2Λ) √|g|` with its flat and curved regressions.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/

noncomputable section

open scoped Manifold ContDiff

namespace ProjectAinos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "I" => 𝓘(ℝ, MinkowskiModel d)

local notation "E" => MinkowskiModel d

variable (g : LorentzMetric σ d M)

example {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M}
    (hx : x ∈ e.source) (i j k : Fin (d + 1)) :
    mvfderiv I (fun y => g.chartInverse e y i j) x (chartField e (Pi.single k 1) x) =
      -∑ b, (g.chartChristoffel e x i k b * g.chartInverse e x j b +
        g.chartChristoffel e x j k b * g.chartInverse e x i b) :=
  mvfderiv_chartInverse_chartField g he hx i j k

end ProjectAinos.SmoothGeometry.LorentzMetric

end

noncomputable section

open ContinuousLinearMap

namespace ProjectAinos.SmoothGeometry.Minkowski

variable {d : ℕ}

example (σ : LorentzConvention) :
    minkowskiForm σ d (Fin.cons 1 (0 : Fin d → ℝ)) (Fin.cons 1 (0 : Fin d → ℝ)) =
      σ.timeSign :=
  minkowskiForm_cons_one σ

example (σ : LorentzConvention) (v : Fin d → ℝ) :
    minkowskiForm σ d (Fin.cons 0 v) (Fin.cons 0 v) = -σ.timeSign * ∑ i, v i ^ 2 :=
  minkowskiForm_cons_zero σ v

example :
    ‖(Fin.cons 1 (0 : Fin d → ℝ) : MinkowskiModel d)‖ ≤ 1 :=
  norm_cons_one_le

example (v : Fin d → ℝ) :
    ‖(Fin.cons 0 v : MinkowskiModel d)‖ ≤ ‖v‖ :=
  norm_cons_zero_le v

example (v : Fin d → ℝ) :
    ‖v‖ ^ 2 ≤ ∑ i, v i ^ 2 :=
  sq_norm_le_sum_sq v

example (B : MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ) (u : MinkowskiModel d) :
    |B u u| ≤ (∑ i, ∑ j, |B (Pi.single i 1) (Pi.single j 1)|) * ‖u‖ ^ 2 :=
  abs_apply_self_le B u

example (σ : LorentzConvention) {B₀ B : MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ}
    (e₀ : MinkowskiModel d ≃L[ℝ] MinkowskiModel d)
    (h₀ : ∀ v w, B₀ v w = minkowskiForm σ d (e₀ v) (e₀ w)) (hs : ∀ v w, B v w = B w v) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hB : ∀ u, |B u u - B₀ u u| ≤ δ * ‖u‖ ^ 2)
    (hδ : δ * ‖(e₀.symm : MinkowskiModel d →L[ℝ] MinkowskiModel d)‖ ^ 2 < 1) :
    ∃ e : MinkowskiModel d ≃L[ℝ] MinkowskiModel d,
      ∀ v w, B v w = minkowskiForm σ d (e v) (e w) :=
  exists_lorentzFrame_of_near σ e₀ h₀ hs hδ0 hB hδ

end ProjectAinos.SmoothGeometry.Minkowski

end

noncomputable section

open Bundle ContinuousLinearMap Set TopologicalSpace

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

variable {σ : LorentzConvention} {d : ℕ}

namespace CoordinateMetric

variable {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U)

example (h : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ) (ε : ℝ) :
    Prop :=
  IsAdmissible g h ε

example (h : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ) :
    g.IsAdmissible h 0 :=
  isAdmissible_zero g h

example {x : MinkowskiModel d} (hx : x ∈ U) (v w : MinkowskiModel d) :
    g.form x v w = g.form x w v :=
  form_symmetric g hx v w

example {h : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ}
    (hc : Continuous h) (hK : HasCompactSupport h) (hKU : tsupport h ⊆ U)
    (hs : ∀ x v w, h x v w = h x w v) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), g.IsAdmissible h ε :=
  eventually_isAdmissible g hc hK hKU hs

example (h : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)
    (hh : ContDiffOn ℝ ∞ h U) (ε : ℝ) (hε : g.IsAdmissible h ε) :
    CoordinateMetric σ d U :=
  addVariation g h hh ε hε

example (h : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)
    (hh : ContDiffOn ℝ ∞ h U) (ε : ℝ) (hε : g.IsAdmissible h ε) (x : MinkowskiModel d) :
    (g.addVariation h hh ε hε).form x = g.form x + ε • h x :=
  addVariation_form g h hh ε hε x

end CoordinateMetric

end ProjectAinos.SmoothGeometry

end

noncomputable section

open Bundle ContinuousLinearMap Set TopologicalSpace

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

example {n : ℕ} {A : Fin n → Fin n → ℝ} (hA : (Matrix.of A).det ≠ 0) (k l : Fin n) :
    ContDiffAt ℝ ∞ (fun B : Fin n → Fin n → ℝ => (Matrix.of B)⁻¹ k l) A :=
  contDiffAt_matrix_inv_apply hA k l

namespace CoordinateMetric

example (C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (y : MinkowskiModel d)
    (k i j : Fin (d + 1)) :
    ℝ :=
  christoffelOf C y k i j

example (C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (y : MinkowskiModel d)
    (j k : Fin (d + 1)) :
    ℝ :=
  ricciOf C y j k

example (C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (y : MinkowskiModel d) :
    ℝ :=
  scalarOf C y

example (C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (y : MinkowskiModel d) :
    ℝ :=
  densityOf C y

variable {U : Opens (MinkowskiModel d)}

example (x y : U) {F : MinkowskiModel d → ℝ} (hF : DifferentiableAt ℝ F y) (v : MinkowskiModel d) :
    mvfderiv 𝓘(ℝ, MinkowskiModel d) (fun z : U => F z) y (chartField (physicalChart x) v y) =
      fderiv ℝ F y v :=
  mvfderiv_val x y hF v

variable (g : CoordinateMetric σ d U)

example (y : U) :
    (g.coefficient y).det ≠ 0 :=
  coefficient_det_ne_zero g y

example (k l : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => (g.coefficient z)⁻¹ k l) U :=
  contDiffOn_coefficient_inv g k l

example (i j : Fin (d + 1)) (v : MinkowskiModel d) :
    ContDiffOn ℝ ∞ (fun z => fderiv ℝ (fun y => g.coefficient y i j) z v) U :=
  contDiffOn_fderiv_coefficient g i j v

example (k i j : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => christoffelOf g.coefficient z k i j) U :=
  contDiffOn_christoffelOf g k i j

example (x y : U) (k i j : Fin (d + 1)) :
    g.toLorentzMetric.chartChristoffel (physicalChart x) y k i j =
      christoffelOf g.coefficient y k i j :=
  toLorentzMetric_chartChristoffel g x y k i j

example (x y : U) (l i j k : Fin (d + 1)) :
    g.toLorentzMetric.chartCurvature (physicalChart x) y l i j k =
      fderiv ℝ (fun z => christoffelOf g.coefficient z l j k) y (Pi.single i 1) -
      fderiv ℝ (fun z => christoffelOf g.coefficient z l i k) y (Pi.single j 1) +
      ∑ a, (christoffelOf g.coefficient y l i a * christoffelOf g.coefficient y a j k -
        christoffelOf g.coefficient y l j a * christoffelOf g.coefficient y a i k) :=
  toLorentzMetric_chartCurvature g x y l i j k

example (x y : U) (j k : Fin (d + 1)) :
    g.toLorentzMetric.ricci y (chartField (physicalChart x) (Pi.single j 1) y)
      (chartField (physicalChart x) (Pi.single k 1) y) = ricciOf g.coefficient y j k :=
  toLorentzMetric_ricci_chartField g x y j k

example (y : U) :
    g.toLorentzMetric.scalarCurvature y = scalarOf g.coefficient y :=
  toLorentzMetric_scalarCurvature g y

example (x y : U) :
    g.toLorentzMetric.chartDensity (physicalChart x) y = densityOf g.coefficient y :=
  toLorentzMetric_chartDensity g x y

end CoordinateMetric

end ProjectAinos.SmoothGeometry

end

noncomputable section

open Set

open scoped ContDiff Topology

namespace ProjectAinos.SmoothGeometry

section Slice

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

example {Φ : ℝ × F → ℝ} {ε : ℝ} {x : F} (hΦ : DifferentiableAt ℝ Φ (ε, x)) :
    HasDerivAt (fun t => Φ (t, x)) (fderiv ℝ Φ (ε, x) (1, 0)) ε :=
  hasDerivAt_slice hΦ

example {Φ : ℝ × F → ℝ} {ε : ℝ} {x : F} (hΦ : DifferentiableAt ℝ Φ (ε, x)) (v : F) :
    fderiv ℝ (fun z => Φ (ε, z)) x v = fderiv ℝ Φ (ε, x) (0, v) :=
  fderiv_slice_apply hΦ v

example {Φ : ℝ × F → ℝ} {x : F} (hΦ : ContDiffAt ℝ ∞ Φ (0, x)) (v : F) :
    HasDerivAt (fun ε => fderiv ℝ (fun z => Φ (ε, z)) x v)
      (fderiv ℝ (fun z => fderiv ℝ Φ (0, z) (1, 0)) x v) 0 :=
  hasDerivAt_fderiv_slice hΦ v

end Slice

namespace CoordinateMetric

variable {d : ℕ}

section Family

variable (Cp : ℝ × MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)

example (p : ℝ × MinkowskiModel d) (k i j : Fin (d + 1)) :
    ℝ :=
  familyChristoffel Cp p k i j

example (p : ℝ × MinkowskiModel d) (j k : Fin (d + 1)) :
    ℝ :=
  familyRicci Cp p j k

example (p : ℝ × MinkowskiModel d) :
    ℝ :=
  familyScalar Cp p

example (p : ℝ × MinkowskiModel d) :
    ℝ :=
  familyDensity Cp p

variable {Cp} {p : ℝ × MinkowskiModel d}

example {Φ : ℝ × MinkowskiModel d → ℝ} (hΦ : ContDiffAt ℝ ∞ Φ p) (v : MinkowskiModel d) :
    ContDiffAt ℝ ∞ (fun q : ℝ × MinkowskiModel d => fderiv ℝ (fun z => Φ (q.1, z)) q.2 v) p :=
  contDiffAt_fderiv_snd hΦ v

example (hC : ∀ i j, ContDiffAt ℝ ∞ (fun q => Cp q i j) p) (hdet : (Cp p).det ≠ 0)
    (k l : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (fun q => (Cp q)⁻¹ k l) p :=
  contDiffAt_familyInv hC hdet k l

example (hC : ∀ i j, ContDiffAt ℝ ∞ (fun q => Cp q i j) p) (hdet : (Cp p).det ≠ 0)
    (k i j : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (fun q => familyChristoffel Cp q k i j) p :=
  contDiffAt_familyChristoffel hC hdet k i j

example (hC : ∀ i j, ContDiffAt ℝ ∞ (fun q => Cp q i j) p) (hdet : (Cp p).det ≠ 0)
    (j k : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (fun q => familyRicci Cp q j k) p :=
  contDiffAt_familyRicci hC hdet j k

example (hC : ∀ i j, ContDiffAt ℝ ∞ (fun q => Cp q i j) p) (hdet : (Cp p).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => familyScalar Cp q) p :=
  contDiffAt_familyScalar hC hdet

example (hC : ∀ i j, ContDiffAt ℝ ∞ (fun q => Cp q i j) p) (hdet : (Cp p).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => familyDensity Cp q) p :=
  contDiffAt_familyDensity hC hdet

example (z : MinkowskiModel d) (k i j : Fin (d + 1)) :
    ℝ :=
  familyChristoffelDeriv Cp z k i j

variable {x : MinkowskiModel d}

example {k i j : Fin (d + 1)}
    (hΓ : ContDiffAt ℝ ∞ (fun q => familyChristoffel Cp q k i j) ((0 : ℝ), x)) :
    HasDerivAt (fun ε => familyChristoffel Cp (ε, x) k i j)
      (familyChristoffelDeriv Cp x k i j) 0 :=
  hasDerivAt_familyChristoffel hΓ

example (x : MinkowskiModel d) (j k : Fin (d + 1)) :
    ℝ :=
  familyRicciDeriv Cp x j k

example (hΓ : ∀ k i j, ContDiffAt ℝ ∞ (fun q => familyChristoffel Cp q k i j) ((0 : ℝ), x))
    (j k : Fin (d + 1)) :
    HasDerivAt (fun ε => familyRicci Cp (ε, x) j k) (familyRicciDeriv Cp x j k) 0 :=
  hasDerivAt_familyRicci hΓ j k

example (hΓ : ∀ k i j, ContDiffAt ℝ ∞ (fun q => familyChristoffel Cp q k i j) ((0 : ℝ), x))
    {Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hQ : ∀ a c, HasDerivAt (fun ε => (Cp (ε, x))⁻¹ a c) (Q a c) 0) :
    HasDerivAt (fun ε => familyScalar Cp (ε, x))
      (∑ a, ∑ c, (familyRicciDeriv Cp x a c * (Cp (0, x))⁻¹ a c +
        familyRicci Cp (0, x) a c * Q a c)) 0 :=
  hasDerivAt_familyScalar hΓ hQ

end Family

end CoordinateMetric

end ProjectAinos.SmoothGeometry

end

open Finset

namespace ProjectAinos.SmoothGeometry

example {n : ℕ} (G : Fin n → Fin n → ℝ) (Γ P : Fin n → Fin n → Fin n → ℝ)
    (DP : Fin n → Fin n → Fin n → Fin n → ℝ) (DG : Fin n → Fin n → Fin n → ℝ)
    (hG : ∀ a b, G a b = G b a) (hΓ : ∀ a b c, Γ a b c = Γ a c b)
    (hP : ∀ a b c, P a b c = P a c b)
    (hDG : ∀ e b c, DG e b c = -∑ d, (Γ b e d * G d c + Γ c e d * G b d)) :
    ∑ b, ∑ c, G b c * (∑ a, (DP a a b c - DP b a a c +
        ∑ d, ((P a a d * Γ d b c + Γ a a d * P d b c) -
          (P a b d * Γ d a c + Γ a b d * P d a c)))) =
      ∑ a, ((∑ e, Γ e e a) * (∑ b, ∑ c, G b c * P a b c - ∑ b, G a b * ∑ c, P c c b) +
        (∑ b, ∑ c, (DG a b c * P a b c + G b c * DP a a b c) -
          ∑ b, (DG a a b * ∑ c, P c c b + G a b * ∑ c, DP a c c b))) :=
  palatini_algebra G Γ P DP DG hG hΓ hP hDG

end ProjectAinos.SmoothGeometry

noncomputable section

open Set TopologicalSpace

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

namespace CoordinateMetric

example (h : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)
    (z : MinkowskiModel d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  formCoeff h z

variable {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U)
  (h : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)

example (p : ℝ × MinkowskiModel d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  variationFamily g h p

example (p : ℝ × MinkowskiModel d) (i j : Fin (d + 1)) :
    g.variationFamily h p i j = g.coefficient p.2 i j + p.1 * formCoeff h p.2 i j :=
  variationFamily_apply g h p i j

example :
    (fun z => g.variationFamily h (0, z)) = g.coefficient :=
  variationFamily_zero g h

example (hh : ContDiffOn ℝ ∞ h U) (ε : ℝ) (hε : g.IsAdmissible h ε) :
    (g.addVariation h hh ε hε).coefficient = fun z => g.variationFamily h (ε, z) :=
  addVariation_coefficient g h hh ε hε

variable {g h}

example (hh : ContDiff ℝ ∞ h) {p : ℝ × MinkowskiModel d} (hp : p.2 ∈ U) (i j : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (fun q => g.variationFamily h q i j) p :=
  contDiffAt_variationFamily hh hp i j

example {x : MinkowskiModel d} (hx : x ∈ U) :
    (g.variationFamily h (0, x)).det ≠ 0 :=
  variationFamily_det_zero hx

example (hh : ContDiff ℝ ∞ h) {x : MinkowskiModel d} (hx : x ∈ U) (k i j : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (fun q => familyChristoffel (g.variationFamily h) q k i j) ((0 : ℝ), x) :=
  contDiffAt_variationChristoffel hh hx k i j

example (hh : ContDiff ℝ ∞ h) {x : MinkowskiModel d} (hx : x ∈ U) (a c : Fin (d + 1)) :
    HasDerivAt (fun ε => (g.variationFamily h (ε, x))⁻¹ a c)
      (-((g.coefficient x)⁻¹ * formCoeff h x * (g.coefficient x)⁻¹) a c) 0 :=
  hasDerivAt_variationFamily_inv hh hx a c

example {x : MinkowskiModel d} (hx : x ∈ U) :
    (g.coefficient x).transpose = g.coefficient x :=
  coefficient_transpose hx

example {x : MinkowskiModel d} (hx : x ∈ U) (a b : Fin (d + 1)) :
    (g.coefficient x)⁻¹ a b = (g.coefficient x)⁻¹ b a :=
  coefficient_inv_symmetric hx a b

example (hs : ∀ z v w, h z v w = h z w v) {x : MinkowskiModel d} (hx : x ∈ U) :
    HasDerivAt (fun ε => familyDensity (g.variationFamily h) (ε, x))
      ((∑ a, ∑ b, (g.coefficient x)⁻¹ a b * formCoeff h x a b) / 2 *
        densityOf g.coefficient x) 0 :=
  hasDerivAt_variationFamily_density hs hx

example {C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {y : MinkowskiModel d}
    (hC : ∀ᶠ z in 𝓝 y, ∀ i j, C z i j = C z j i) (k i j : Fin (d + 1)) :
    christoffelOf C y k i j = christoffelOf C y k j i :=
  christoffelOf_symm hC k i j

example (hs : ∀ z v w, h z v w = h z w v) {p : ℝ × MinkowskiModel d} (hp : p.2 ∈ U)
    (i j : Fin (d + 1)) :
    g.variationFamily h p i j = g.variationFamily h p j i :=
  variationFamily_symm hs hp i j

example (hs : ∀ z v w, h z v w = h z w v) {x : MinkowskiModel d} (hx : x ∈ U)
    (k i j : Fin (d + 1)) :
    familyChristoffelDeriv (g.variationFamily h) x k i j =
      familyChristoffelDeriv (g.variationFamily h) x k j i :=
  christoffelVariation_symm hs hx k i j

example {x : MinkowskiModel d} (hx : x ∈ U) (k i j : Fin (d + 1)) :
    christoffelOf g.coefficient x k i j = christoffelOf g.coefficient x k j i :=
  christoffelOf_coefficient_symm hx k i j

example (x y : U) (i j : Fin (d + 1)) :
    g.toLorentzMetric.chartInverse (physicalChart x) y i j = (g.coefficient y)⁻¹ i j :=
  chartInverse_physicalChart x y i j

example {x : MinkowskiModel d} (hx : x ∈ U) :
    ContDiffAt ℝ ∞ (fun z => densityOf g.coefficient z) x :=
  contDiffAt_densityOf hx

example {x : MinkowskiModel d} (hx : x ∈ U) (b c k : Fin (d + 1)) :
    fderiv ℝ (fun z => (g.coefficient z)⁻¹ b c) x (Pi.single k 1) =
      -∑ e, (christoffelOf g.coefficient x b k e * (g.coefficient x)⁻¹ e c +
        christoffelOf g.coefficient x c k e * (g.coefficient x)⁻¹ b e) :=
  fderiv_coefficient_inv hx b c k

example {x : MinkowskiModel d} (hx : x ∈ U) (k : Fin (d + 1)) :
    fderiv ℝ (fun z => densityOf g.coefficient z) x (Pi.single k 1) =
      densityOf g.coefficient x * ∑ c, christoffelOf g.coefficient x c c k :=
  fderiv_densityOf hx k

end CoordinateMetric

end ProjectAinos.SmoothGeometry

end

noncomputable section

open Set TopologicalSpace ContinuousLinearMap

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

example {n : ℕ} (R A H : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ a b, A a b = A b a) :
    ∑ a, ∑ c, R a c * -((A * H * A) a c) =
      -∑ m, ∑ k, (∑ a, ∑ c, A m a * A k c * R a c) * H m k :=
  sum_mul_neg_sandwich R A H hA

namespace CoordinateMetric

variable {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U)
  (h : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)

example (z : MinkowskiModel d) (k i j : Fin (d + 1)) :
    ℝ :=
  christoffelVariation g h z k i j

example (z : MinkowskiModel d) (a : Fin (d + 1)) :
    ℝ :=
  variationVector g h z a

example (z : MinkowskiModel d) (m n : Fin (d + 1)) :
    ℝ :=
  ricciUp g z m n

variable {g h}

example (z : MinkowskiModel d) (k i j : Fin (d + 1)) :
    familyChristoffel (g.variationFamily h) (0, z) k i j = christoffelOf g.coefficient z k i j :=
  familyChristoffel_variationFamily_zero z k i j

example (z : MinkowskiModel d) (j k : Fin (d + 1)) :
    familyRicci (g.variationFamily h) (0, z) j k = ricciOf g.coefficient z j k :=
  familyRicci_variationFamily_zero z j k

example (hh : ContDiff ℝ ∞ h) {x : MinkowskiModel d} (hx : x ∈ U) (k i j : Fin (d + 1)) :
    DifferentiableAt ℝ (fun z => g.christoffelVariation h z k i j) x :=
  contDiffAt_christoffelVariation hh hx k i j

example (hh : ContDiff ℝ ∞ h) {x : MinkowskiModel d} (hx : x ∈ U) (a : Fin (d + 1)) :
    fderiv ℝ (fun z => densityOf g.coefficient z * g.variationVector h z a) x (Pi.single a 1) =
      densityOf g.coefficient x *
          (∑ b, ∑ c, ((g.coefficient x)⁻¹ b c *
              fderiv ℝ (fun z => g.christoffelVariation h z a b c) x (Pi.single a 1) +
            g.christoffelVariation h x a b c *
              fderiv ℝ (fun z => (g.coefficient z)⁻¹ b c) x (Pi.single a 1)) -
          ∑ b, ((g.coefficient x)⁻¹ a b *
              ∑ c, fderiv ℝ (fun z => g.christoffelVariation h z c c b) x (Pi.single a 1) +
            (∑ c, g.christoffelVariation h x c c b) *
              fderiv ℝ (fun z => (g.coefficient z)⁻¹ a b) x (Pi.single a 1))) +
        g.variationVector h x a * fderiv ℝ (fun z => densityOf g.coefficient z) x (Pi.single a 1) :=
  fderiv_density_mul_variationVector hh hx a

example (hh : ContDiff ℝ ∞ h) (hs : ∀ z v w, h z v w = h z w v) (Λ : ℝ) {x : MinkowskiModel d}
    (hx : x ∈ U) :
    HasDerivAt (fun ε => (familyScalar (g.variationFamily h) (ε, x) - 2 * Λ) *
        familyDensity (g.variationFamily h) (ε, x))
      (-(densityOf g.coefficient x * ∑ m, ∑ n, (g.ricciUp x m n -
          (scalarOf g.coefficient x / 2 - Λ) * (g.coefficient x)⁻¹ m n) * formCoeff h x m n) +
        ∑ a, fderiv ℝ (fun z => densityOf g.coefficient z * g.variationVector h z a) x
          (Pi.single a 1)) 0 :=
  hasDerivAt_scalarDensity hh hs Λ hx

end CoordinateMetric

end ProjectAinos.SmoothGeometry

end

noncomputable section

open Set TopologicalSpace MeasureTheory

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

namespace CoordinateMetric

section Locality

variable {C C' : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}

example (hC : C =ᶠ[𝓝 x] C') (k i j : Fin (d + 1)) :
    christoffelOf C x k i j = christoffelOf C' x k i j :=
  christoffelOf_congr hC k i j

example (hC : C =ᶠ[𝓝 x] C') (k i j : Fin (d + 1)) :
    (fun z => christoffelOf C z k i j) =ᶠ[𝓝 x] fun z => christoffelOf C' z k i j :=
  christoffelOf_eventuallyEq hC k i j

example (hC : C =ᶠ[𝓝 x] C') (j k : Fin (d + 1)) :
    ricciOf C x j k = ricciOf C' x j k :=
  ricciOf_congr hC j k

example (hC : C =ᶠ[𝓝 x] C') :
    scalarOf C x = scalarOf C' x :=
  scalarOf_congr hC

example (hC : C =ᶠ[𝓝 x] C') :
    densityOf C x = densityOf C' x :=
  densityOf_congr hC

end Locality

section Constant

variable (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (y : MinkowskiModel d)

example (k i j : Fin (d + 1)) :
    christoffelOf (fun _ => M) y k i j = 0 :=
  christoffelOf_const M y k i j

example (j k : Fin (d + 1)) :
    ricciOf (fun _ => M) y j k = 0 :=
  ricciOf_const M y j k

example :
    scalarOf (fun _ => M) y = 0 :=
  scalarOf_const M y

end Constant

example {U : Opens (MinkowskiModel d)} (y : MinkowskiModel d) :
    (minkowski σ d U).coefficient y = Matrix.diagonal (lorentzSign σ) :=
  minkowski_coefficient y

variable {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U)
  (h : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)

example (Λ : ℝ) (p : ℝ × MinkowskiModel d) :
    ℝ :=
  scalarDensity g h Λ p

variable {g h}

example {x : MinkowskiModel d} (hx : x ∉ tsupport h) (ε : ℝ) :
    (fun z => g.variationFamily h (ε, z)) =ᶠ[𝓝 x] fun z => g.variationFamily h (0, z) :=
  variationFamily_eventuallyEq_of_notMem hx ε

example (Λ : ℝ) {x : MinkowskiModel d} (hx : x ∉ tsupport h) (ε : ℝ) :
    g.scalarDensity h Λ (ε, x) = g.scalarDensity h Λ (0, x) :=
  scalarDensity_of_notMem Λ hx ε

example (hh : ContDiff ℝ ∞ h) (Λ : ℝ) {p : ℝ × MinkowskiModel d} (hp : p.2 ∈ U)
    (hdet : (g.variationFamily h p).det ≠ 0) :
    ContDiffAt ℝ ∞ (g.scalarDensity h Λ) p :=
  contDiffAt_scalarDensity hh Λ hp hdet

example (hh : ContDiff ℝ ∞ h) {ε : ℝ} (hε : g.IsAdmissible h ε) {z : MinkowskiModel d}
    (hz : z ∈ U) :
    (g.variationFamily h (ε, z)).det ≠ 0 :=
  variationFamily_det_ne_zero hh hε hz

example {Φ : ℝ × MinkowskiModel d → ℝ} {x : MinkowskiModel d}
    (hΦ : Φ =ᶠ[𝓝 ((0 : ℝ), x)] fun q => Φ (0, q.2)) :
    fderiv ℝ Φ ((0 : ℝ), x) (1, 0) = 0 :=
  fderiv_fst_eq_zero_of_eventually hΦ

example {x : MinkowskiModel d} (hx : x ∉ tsupport h) (k i j : Fin (d + 1)) :
    g.christoffelVariation h x k i j = 0 :=
  christoffelVariation_of_notMem hx k i j

example {x : MinkowskiModel d} (hx : x ∉ tsupport h) (a : Fin (d + 1)) :
    g.variationVector h x a = 0 :=
  variationVector_of_notMem hx a

example {x : MinkowskiModel d} (hx : x ∉ tsupport h) (a : Fin (d + 1)) :
    (fun z => densityOf g.coefficient z * g.variationVector h z a) =ᶠ[𝓝 x] fun _ => 0 :=
  density_mul_variationVector_eventuallyEq hx a

example (hh : ContDiff ℝ ∞ h) {x : MinkowskiModel d} (hx : x ∈ U) (k i j : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (fun z => g.christoffelVariation h z k i j) x :=
  contDiffAt_christoffelVariation' hh hx k i j

example (hh : ContDiff ℝ ∞ h) (hKU : tsupport h ⊆ U) (a : Fin (d + 1)) :
    ContDiff ℝ ∞ (fun z => densityOf g.coefficient z * g.variationVector h z a) :=
  contDiff_density_mul_variationVector hh hKU a

example (hK : HasCompactSupport h) (a : Fin (d + 1)) :
    HasCompactSupport (fun z => densityOf g.coefficient z * g.variationVector h z a) :=
  hasCompactSupport_density_mul_variationVector hK a

example (hh : ContDiff ℝ ∞ h) (hK : HasCompactSupport h) (hKU : tsupport h ⊆ U) (a : Fin (d + 1)) :
    (∫ x, fderiv ℝ (fun z => densityOf g.coefficient z * g.variationVector h z a) x
      (Pi.single a 1)) = 0 :=
  integral_fderiv_density_mul_variationVector hh hK hKU a

example (Λ : ℝ) (x : MinkowskiModel d) :
    ℝ :=
  eulerLagrangeDensity g h Λ x

example (Λ : ℝ) {x : MinkowskiModel d} (hx : x ∉ tsupport h) :
    g.eulerLagrangeDensity h Λ x = 0 :=
  eulerLagrangeDensity_of_notMem Λ hx

example (hh : ContDiff ℝ ∞ h) (hs : ∀ z v w, h z v w = h z w v) (hKU : tsupport h ⊆ U) (Λ : ℝ)
    (x : MinkowskiModel d) :
    deriv (fun t => g.scalarDensity h Λ (t, x)) 0 = g.eulerLagrangeDensity h Λ x +
      ∑ a, fderiv ℝ (fun z => densityOf g.coefficient z * g.variationVector h z a) x
        (Pi.single a 1) :=
  deriv_scalarDensity_zero hh hs hKU Λ x

example (hh : ContDiff ℝ ∞ h) (hK : HasCompactSupport h) (hKU : tsupport h ⊆ U)
    (hs : ∀ z v w, h z v w = h z w v) (Λ : ℝ) :
    HasDerivAt (fun ε => ∫ x, (g.scalarDensity h Λ (ε, x) - g.scalarDensity h Λ (0, x)))
      (∫ x, g.eulerLagrangeDensity h Λ x) 0 :=
  hasDerivAt_integral_scalarDensity hh hK hKU hs Λ

section Native

example (hh : ContDiffOn ℝ ∞ h U) {ε : ℝ} (hε : g.IsAdmissible h ε) (Λ : ℝ) (y : U) :
    g.scalarDensity h Λ (ε, y) =
      ((g.addVariation h hh ε hε).toLorentzMetric.scalarCurvature y - 2 * Λ) *
        (g.addVariation h hh ε hε).toLorentzMetric.chartDensity (physicalChart y) y :=
  scalarDensity_eq_toLorentzMetric hh hε Λ y

example (Λ : ℝ) (y : U) :
    g.scalarDensity h Λ (0, y) = (g.toLorentzMetric.scalarCurvature y - 2 * Λ) *
      g.toLorentzMetric.chartDensity (physicalChart y) y :=
  scalarDensity_zero_eq_toLorentzMetric Λ y

example (C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (y : MinkowskiModel d)
    (i k : Fin (d + 1)) :
    ℝ :=
  einsteinOf C y i k

example (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (y : MinkowskiModel d) (i k : Fin (d + 1)) :
    einsteinOf (fun _ => M) y i k = 0 :=
  einsteinOf_const M y i k

example (x y : U) (i k : Fin (d + 1)) :
    g.toLorentzMetric.einstein y (chartField (physicalChart x) (Pi.single i 1) y)
      (chartField (physicalChart x) (Pi.single k 1) y) = einsteinOf g.coefficient y i k :=
  toLorentzMetric_einstein_chartField x y i k

example (x : MinkowskiModel d) (i k : Fin (d + 1)) :
    ℝ :=
  inverseVariation g h x i k

example (hh : ContDiff ℝ ∞ h) {x : MinkowskiModel d} (hx : x ∈ U) (i k : Fin (d + 1)) :
    HasDerivAt (fun ε => (g.variationFamily h (ε, x))⁻¹ i k) (g.inverseVariation h x i k) 0 :=
  hasDerivAt_inverseVariation hh hx i k

example {x : MinkowskiModel d} (hx : x ∈ U) (m n : Fin (d + 1)) :
    ∑ a, ∑ c, (g.coefficient x)⁻¹ m a * (g.coefficient x)⁻¹ n c * g.coefficient x a c =
      (g.coefficient x)⁻¹ m n :=
  sum_inv_mul_inv_mul_coefficient hx m n

example (hKU : tsupport h ⊆ U) (Λ : ℝ) (x : MinkowskiModel d) :
    g.eulerLagrangeDensity h Λ x = (∑ i, ∑ k, (einsteinOf g.coefficient x i k +
      Λ * g.coefficient x i k) * g.inverseVariation h x i k) * densityOf g.coefficient x :=
  eulerLagrangeDensity_eq hKU Λ x

end Native

end CoordinateMetric

end ProjectAinos.SmoothGeometry

end

noncomputable section

open Set TopologicalSpace MeasureTheory Filter

open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.EinsteinHilbert

open SmoothGeometry CoordinateMetric

open LorentzMetric (chartField)

variable {U : Opens (MinkowskiModel 3)}

example (g : CoordinateMetric .timeNegative 3 U) (κ Λ : ℝ) (y : U) :
    ℝ :=
  lagrangian g κ Λ y

variable (g : CoordinateMetric .timeNegative 3 U)
  (h : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 →L[ℝ] ℝ)

example (κ Λ ε : ℝ) :
    ℝ :=
  relativeAction g h κ Λ ε

example (κ Λ : ℝ) :
    relativeAction g h κ Λ 0 = 0 :=
  relativeAction_zero g h κ Λ

variable {g h}

example (hh : ContDiffOn ℝ ∞ h U) {ε : ℝ} (hε : g.IsAdmissible h ε) (κ Λ : ℝ) (y : U) :
    (2 * κ)⁻¹ * (g.scalarDensity h Λ (ε, y) - g.scalarDensity h Λ (0, y)) =
      lagrangian (g.addVariation h hh ε hε) κ Λ y - lagrangian g κ Λ y :=
  relativeAction_integrand hh hε κ Λ y

example {x : MinkowskiModel 3} (hx : x ∉ tsupport h) (Λ ε : ℝ) :
    g.scalarDensity h Λ (ε, x) - g.scalarDensity h Λ (0, x) = 0 :=
  relativeAction_integrand_of_notMem hx Λ ε

example (hh : ContDiff ℝ ∞ h) (hK : HasCompactSupport h) (hKU : tsupport h ⊆ U)
    (hs : ∀ z v w, h z v w = h z w v) (κ Λ : ℝ) :
    ∀ᶠ ε in 𝓝 0, ∃ hε : g.IsAdmissible h ε, ∀ y : U,
      (2 * κ)⁻¹ * (g.scalarDensity h Λ (ε, y) - g.scalarDensity h Λ (0, y)) =
        lagrangian (g.addVariation h hh.contDiffOn ε hε) κ Λ y - lagrangian g κ Λ y :=
  eventually_relativeAction_integrand hh hK hKU hs κ Λ

example (hh : ContDiff ℝ ∞ h) (hK : HasCompactSupport h) (hKU : tsupport h ⊆ U)
    (hs : ∀ z v w, h z v w = h z w v) (κ Λ : ℝ) :
    HasDerivAt (relativeAction g h κ Λ)
      ((2 * κ)⁻¹ * ∫ x, (∑ i, ∑ k, (einsteinOf g.coefficient x i k +
        Λ * g.coefficient x i k) * g.inverseVariation h x i k) * densityOf g.coefficient x) 0 :=
  hasDerivAt_relativeAction hh hK hKU hs κ Λ

example (Λ : ℝ) (y : U) :
    (∑ i, ∑ k, (einsteinOf g.coefficient y i k + Λ * g.coefficient y i k) *
      g.inverseVariation h y i k) * densityOf g.coefficient y =
    (∑ i, ∑ k, (g.toLorentzMetric.einstein y (chartField (physicalChart y) (Pi.single i 1) y)
      (chartField (physicalChart y) (Pi.single k 1) y) +
      Λ * g.toLorentzMetric.chartComponent (physicalChart y) y i k) *
      g.inverseVariation h y i k) * g.toLorentzMetric.chartDensity (physicalChart y) y :=
  integrand_eq_native Λ y

section Flat

local notation "η₄" => CoordinateMetric.minkowski LorentzConvention.timeNegative 3 ⊤

example (f : MinkowskiModel 3 → ℝ) (x : MinkowskiModel 3) :
    MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 →L[ℝ] ℝ :=
  flatVariation f x

variable {f : MinkowskiModel 3 → ℝ}

example (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (flatVariation f) :=
  contDiff_flatVariation hf

example (hfK : HasCompactSupport f) :
    HasCompactSupport (flatVariation f) :=
  hasCompactSupport_flatVariation hfK

example (z v w : MinkowskiModel 3) :
    flatVariation f z v w = flatVariation f z w v :=
  flatVariation_symm z v w

example (x : MinkowskiModel 3) :
    formCoeff (flatVariation f) x = f x • Matrix.diagonal (lorentzSign .timeNegative) :=
  formCoeff_flatVariation x

example (Λ : ℝ) (x : MinkowskiModel 3) :
    (∑ i, ∑ k, (einsteinOf (η₄).coefficient x i k + Λ * (η₄).coefficient x i k) *
      (η₄).inverseVariation (flatVariation f) x i k) * densityOf (η₄).coefficient x =
      -(4 * Λ * f x) :=
  flat_integrand Λ x

example (hf : ContDiff ℝ ∞ f) (hfK : HasCompactSupport f) (κ Λ : ℝ) :
    HasDerivAt (relativeAction (η₄) (flatVariation f) κ Λ)
      (-(2 * Λ / κ) * ∫ x, f x) 0 :=
  hasDerivAt_relativeAction_flat hf hfK κ Λ

example {κ Λ : ℝ} (hκ : κ ≠ 0) (hΛ : Λ ≠ 0) :
    ∃ f : MinkowskiModel 3 → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      deriv (relativeAction (η₄) (flatVariation f) κ Λ) 0 ≠ 0 :=
  exists_deriv_relativeAction_flat_ne_zero hκ hΛ

end Flat

section Conformal

local notation "D" => Matrix.diagonal (lorentzSign (d := 3) LorentzConvention.timeNegative)

local notation "gc" => ExponentialConformalExample.metric

variable {f : MinkowskiModel 3 → ℝ}

example (y : MinkowskiModel 3) :
    (gc).coefficient y = Real.exp (2 * y 3) • D :=
  conformal_coefficient y

example (y : MinkowskiModel 3) (i k : Fin 4) :
    einsteinOf (gc).coefficient y i k =
      2 * ((Pi.single i 1 : MinkowskiModel 3) 3 * (Pi.single k 1 : MinkowskiModel 3) 3) +
        D i k :=
  conformal_einsteinOf y i k

example (Λ : ℝ) (x : MinkowskiModel 3) :
    (∑ i, ∑ k, (einsteinOf (gc).coefficient x i k + Λ * (gc).coefficient x i k) *
      (gc).inverseVariation (flatVariation f) x i k) * densityOf (gc).coefficient x =
      -(f x * (6 + 4 * Λ * Real.exp (2 * x 3))) :=
  conformal_integrand Λ x

example (hf : ContDiff ℝ ∞ f) (hfK : HasCompactSupport f) (κ Λ : ℝ) :
    HasDerivAt (relativeAction (gc) (flatVariation f) κ Λ)
      (-(2 * κ)⁻¹ * ∫ x, f x * (6 + 4 * Λ * Real.exp (2 * x 3))) 0 :=
  hasDerivAt_relativeAction_conformal hf hfK κ Λ

example {κ : ℝ} (hκ : κ ≠ 0) :
    ∃ f : MinkowskiModel 3 → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      deriv (relativeAction (gc) (flatVariation f) κ 0) 0 ≠ 0 :=
  exists_deriv_relativeAction_conformal_ne_zero hκ

end Conformal

end ProjectAinos.GeneralRelativity.EinsteinHilbert

end
