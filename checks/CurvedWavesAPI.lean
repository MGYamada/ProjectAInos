/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Lorentzian.CurvedLinearization
import ProjectAinos.GeneralRelativity.ShortWave

/-! Public consumers of gravitational waves on a curved background (Landau–Lifshitz §108): the
covariant first variation of the Christoffel symbols and the Palatini form of the first variation
of the Ricci tensor along `g + εh`, gauge invariance on Ricci-flat backgrounds, the exact
short-wave expansion with the eikonal equation in the gauge, and the rays as null geodesics, with
flat and plane-wave instances. Default elaborator options are intentional: these checks must not
rely on the implementation's transparency settings. Every statement is pinned with its type. -/

noncomputable section


section CurvedLinearization

open Set Filter TopologicalSpace

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

example {n : ℕ} {M : ℝ → Matrix (Fin n) (Fin n) ℝ} {M' : Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ i j, HasDerivAt (fun ε => M ε i j) (M' i j) 0) (hdet : (M 0).det ≠ 0) (k l : Fin n) :
    HasDerivAt (fun ε => (M ε)⁻¹ k l) (-((M 0)⁻¹ * M' * (M 0)⁻¹) k l) 0 :=
  hasDerivAt_matrix_inv hM hdet k l

section Covariant

variable (g : CoordinateMetric σ d U)

example (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (a i j : Fin (d + 1)) :
    ℝ :=
  covDerivTwo g h x a i j

example (P : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ)
    (x : MinkowskiModel d) (a k i j : Fin (d + 1)) :
    ℝ :=
  covDerivThree g P x a k i j

example (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (k i j : Fin (d + 1)) :
    ℝ :=
  curvedChristoffel g h x k i j

example (P : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ)
    (x : MinkowskiModel d) (j k : Fin (d + 1)) :
    ℝ :=
  palatini g P x j k

example (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (p : ℝ × MinkowskiModel d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  perturbationFamily g h p

example (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (p : ℝ × MinkowskiModel d)
    (i j : Fin (d + 1)) :
    g.perturbationFamily h p i j = g.coefficient p.2 i j + p.1 * h p.2 i j :=
  perturbationFamily_apply g h p i j

example (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    (fun z => g.perturbationFamily h (0, z)) = g.coefficient :=
  perturbationFamily_zero g h

variable {g}

example {h h' : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}
    (hh : h =ᶠ[𝓝 x] h') (a i j : Fin (d + 1)) :
    g.covDerivTwo h x a i j = g.covDerivTwo h' x a i j :=
  covDerivTwo_congr hh a i j

example {h h' : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}
    (hh : h =ᶠ[𝓝 x] h') (k i j : Fin (d + 1)) :
    g.curvedChristoffel h x k i j = g.curvedChristoffel h' x k i j :=
  curvedChristoffel_congr hh k i j

example {P P' : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ}
    {x : MinkowskiModel d} (hP : P =ᶠ[𝓝 x] P') (a k i j : Fin (d + 1)) :
    g.covDerivThree P x a k i j = g.covDerivThree P' x a k i j :=
  covDerivThree_congr hP a k i j

example {P P' : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ}
    {x : MinkowskiModel d} (hP : P =ᶠ[𝓝 x] P') (j k : Fin (d + 1)) :
    g.palatini P x j k = g.palatini P' x j k :=
  palatini_congr hP j k

end Covariant

example (Cp : ℝ × MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (z : MinkowskiModel d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  familyCoeffDeriv Cp z

section Variation

variable {g : CoordinateMetric σ d U}

example {Cp : ℝ × MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}
    (hx : x ∈ U) (hC : ∀ i j, ContDiffAt ℝ ∞ (fun q => Cp q i j) ((0 : ℝ), x))
    (h0 : (fun z => Cp (0, z)) =ᶠ[𝓝 x] g.coefficient)
    (hs : ∀ i j, familyCoeffDeriv Cp x i j = familyCoeffDeriv Cp x j i) (k i j : Fin (d + 1)) :
    familyChristoffelDeriv Cp x k i j = g.curvedChristoffel (familyCoeffDeriv Cp) x k i j :=
  familyChristoffelDeriv_eq_of_family hx hC h0 hs k i j

example {Cp : ℝ × MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}
    (hx : x ∈ U) (h0 : (fun z => Cp (0, z)) =ᶠ[𝓝 x] g.coefficient) (j k : Fin (d + 1)) :
    familyRicciDeriv Cp x j k = g.palatini (familyChristoffelDeriv Cp) x j k :=
  familyRicciDeriv_eq_palatini hx h0 j k

end Variation

section Perturbation

variable {g : CoordinateMetric σ d U} {h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}

example (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) {p : ℝ × MinkowskiModel d}
    (hp : p.2 ∈ U) (i j : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (fun q => g.perturbationFamily h q i j) p :=
  contDiffAt_perturbationFamily hh hp i j

example (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) {z : MinkowskiModel d} (hz : z ∈ U) :
    familyCoeffDeriv (g.perturbationFamily h) z = h z :=
  familyCoeffDeriv_perturbationFamily hh hz

example (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i)
    {z : MinkowskiModel d} (hz : z ∈ U) (k i j : Fin (d + 1)) :
    familyChristoffelDeriv (g.perturbationFamily h) z k i j = g.curvedChristoffel h z k i j :=
  familyChristoffelDeriv_eq hh hs hz k i j

example (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    familyRicciDeriv (g.perturbationFamily h) x j k = g.palatini (g.curvedChristoffel h) x j k :=
  familyRicciDeriv_eq hh hs hx j k

example (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    HasDerivAt (fun ε : ℝ => ricciOf (fun z => g.coefficient z + ε • h z) x j k)
      (g.palatini (g.curvedChristoffel h) x j k) 0 :=
  hasDerivAt_ricciOf_perturbation hh hs hx j k

example {f : MinkowskiModel d → ℝ} (hf : ContDiffOn ℝ ∞ f U) (v : MinkowskiModel d) :
    ContDiffOn ℝ ∞ (fun z => fderiv ℝ f z v) U :=
  contDiffOn_partial hf v

example (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) (a i j : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => g.covDerivTwo h z a i j) U :=
  contDiffOn_covDerivTwo hh a i j

example (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) (k i j : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => g.curvedChristoffel h z k i j) U :=
  contDiffOn_curvedChristoffel hh k i j

end Perturbation

section Leibniz

variable {g : CoordinateMetric σ d U}

example (w : Fin (d + 1) → ℝ) (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (k i j : Fin (d + 1)) :
    ℝ :=
  symbolChristoffel g w A x k i j

example (f : MinkowskiModel d → ℝ) (x : MinkowskiModel d) (i : Fin (d + 1)) :
    ℝ :=
  gradientCovector f x i

example {f : MinkowskiModel d → ℝ} {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {x : MinkowskiModel d} (hf : DifferentiableAt ℝ f x)
    (ha : ∀ p q, DifferentiableAt ℝ (fun z => a z p q) x) (m p q : Fin (d + 1)) :
    g.covDerivTwo (fun z => f z • a z) x m p q =
      gradientCovector f x m * a x p q + f x * g.covDerivTwo a x m p q :=
  covDerivTwo_smul hf ha m p q

example {f : MinkowskiModel d → ℝ} {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {x : MinkowskiModel d} (hf : DifferentiableAt ℝ f x)
    (ha : ∀ p q, DifferentiableAt ℝ (fun z => a z p q) x) (k i j : Fin (d + 1)) :
    g.curvedChristoffel (fun z => f z • a z) x k i j =
      f x * g.curvedChristoffel a x k i j +
        g.symbolChristoffel (gradientCovector f x) (a x) x k i j :=
  curvedChristoffel_smul hf ha k i j

example {f : MinkowskiModel d → ℝ}
    {P P' : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ} {x : MinkowskiModel d}
    (hf : DifferentiableAt ℝ f x) (hP : ∀ a b c, DifferentiableAt ℝ (fun z => P z a b c) x)
    (hP' : ∀ a b c, DifferentiableAt ℝ (fun z => P' z a b c) x) (a k i j : Fin (d + 1)) :
    g.covDerivThree (fun z => f z • P z + P' z) x a k i j =
      gradientCovector f x a * P x k i j + f x * g.covDerivThree P x a k i j +
        g.covDerivThree P' x a k i j :=
  covDerivThree_smul_add hf hP hP' a k i j

example {f : MinkowskiModel d → ℝ}
    {P P' : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ} {x : MinkowskiModel d}
    (hf : DifferentiableAt ℝ f x) (hP : ∀ a b c, DifferentiableAt ℝ (fun z => P z a b c) x)
    (hP' : ∀ a b c, DifferentiableAt ℝ (fun z => P' z a b c) x) (j k : Fin (d + 1)) :
    g.palatini (fun z => f z • P z + P' z) x j k =
      f x * g.palatini P x j k +
        ∑ i, (gradientCovector f x i * P x i j k - gradientCovector f x j * P x i i k) +
        g.palatini P' x j k :=
  palatini_smul_add hf hP hP' j k

example (x : MinkowskiModel d) (j k : Fin (d + 1)) :
    g.palatini (fun _ => 0) x j k = 0 :=
  palatini_zero x j k

example {f : MinkowskiModel d → ℝ}
    {P : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ} {x : MinkowskiModel d}
    (hf : DifferentiableAt ℝ f x) (hP : ∀ a b c, DifferentiableAt ℝ (fun z => P z a b c) x)
    (j k : Fin (d + 1)) :
    g.palatini (fun z => f z • P z) x j k =
      f x * g.palatini P x j k +
        ∑ i, (gradientCovector f x i * P x i j k - gradientCovector f x j * P x i i k) :=
  palatini_smul hf hP j k

example (c : ℝ) (w : Fin (d + 1) → ℝ) (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (k i j : Fin (d + 1)) :
    g.symbolChristoffel (c • w) A x k i j = c * g.symbolChristoffel w A x k i j :=
  symbolChristoffel_smul c w A x k i j

example {F : ℝ → ℝ} {ψ : MinkowskiModel d → ℝ} {x : MinkowskiModel d}
    (hF : DifferentiableAt ℝ F (ψ x)) (hψ : DifferentiableAt ℝ ψ x) (i : Fin (d + 1)) :
    gradientCovector (fun z => F (ψ z)) x i = deriv F (ψ x) * gradientCovector ψ x i :=
  gradientCovector_comp hF hψ i

end Leibniz

section Flat

variable {h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}

example :
    (minkowski σ d U).perturbationFamily h = linearFamily σ h :=
  perturbationFamily_minkowski

example {z : MinkowskiModel d} (hz : z ∈ U) (a i j : Fin (d + 1)) :
    (minkowski σ d U).covDerivTwo h z a i j = fderiv ℝ (fun y => h y i j) z (Pi.single a 1) :=
  covDerivTwo_minkowski hz a i j

example {z : MinkowskiModel d} (hz : z ∈ U) (k i j : Fin (d + 1)) :
    (minkowski σ d U).curvedChristoffel h z k i j = linearizedChristoffel σ h z k i j :=
  curvedChristoffel_minkowski hz k i j

example {x : MinkowskiModel d} (hx : x ∈ U)
    (P : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ) (j k : Fin (d + 1)) :
    (minkowski σ d U).palatini P x j k = ∑ i,
      (fderiv ℝ (fun z => P z i j k) x (Pi.single i 1) -
        fderiv ℝ (fun z => P z i i k) x (Pi.single j 1)) :=
  palatini_minkowski hx P j k

example (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    (minkowski σ d U).palatini ((minkowski σ d U).curvedChristoffel h) x j k =
      linearizedRicci σ h x j k :=
  palatini_curvedChristoffel_minkowski hh hs hx j k

end Flat

section Gauge

variable {g : CoordinateMetric σ d U} {X : MinkowskiModel d → MinkowskiModel d}

example (X : MinkowskiModel d → MinkowskiModel d) (g : CoordinateMetric σ d U)
    (z : MinkowskiModel d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  coordinateLieMetric X g z

example (X : MinkowskiModel d → MinkowskiModel d) (ε : ℝ) (z : MinkowskiModel d) :
    MinkowskiModel d →L[ℝ] MinkowskiModel d :=
  shiftDeriv X ε z

example (ε : ℝ) (z v : MinkowskiModel d) :
    shiftDeriv X ε z v = v + ε • fderiv ℝ X z v :=
  shiftDeriv_apply ε z v

example (ε : ℝ) (z : MinkowskiModel d) :
    MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ :=
  pullbackForm g X ε z

example (ε : ℝ) (z v w : MinkowskiModel d) :
    pullbackForm g X ε z v w =
      g.form (z + ε • X z) (shiftDeriv X ε z v) (shiftDeriv X ε z w) :=
  pullbackForm_apply ε z v w

example (p : ℝ × MinkowskiModel d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  pullbackFamily g X p

example :
    (fun z => pullbackFamily g X (0, z)) = g.coefficient :=
  pullbackFamily_zero

example (hX : ContDiffOn ℝ ∞ X U) (ε : ℝ) :
    ContDiffOn ℝ ∞ (shiftDeriv X ε) U :=
  contDiffOn_shiftDeriv hX ε

example (hX : ContDiffOn ℝ ∞ X U) {z : MinkowskiModel d} (hz : z ∈ U) (i j : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (fun q => pullbackFamily g X q i j) ((0 : ℝ), z) :=
  contDiffAt_pullbackFamily hX hz i j

example {Y : MinkowskiModel d → MinkowskiModel d} {z : MinkowskiModel d}
    (hY : DifferentiableAt ℝ Y z) (k : Fin (d + 1)) (v : MinkowskiModel d) :
    fderiv ℝ (fun y => Y y k) z v = fderiv ℝ Y z v k :=
  fderiv_component hY k v

example (p : ℝ × MinkowskiModel d) (i j : Fin (d + 1)) :
    pullbackFamily g X p i j = ∑ a, ∑ b, g.coefficient (p.2 + p.1 • X p.2) a b *
      ((Pi.single i 1 : MinkowskiModel d) a + p.1 * fderiv ℝ X p.2 (Pi.single i 1) a) *
      ((Pi.single j 1 : MinkowskiModel d) b + p.1 * fderiv ℝ X p.2 (Pi.single j 1) b) :=
  pullbackFamily_apply p i j

example (hX : ContDiffOn ℝ ∞ X U) {z : MinkowskiModel d} (hz : z ∈ U) :
    familyCoeffDeriv (pullbackFamily g X) z = coordinateLieMetric X g z :=
  familyCoeffDeriv_pullbackFamily hX hz

example {z : MinkowskiModel d} (hz : z ∈ U) (i j : Fin (d + 1)) :
    coordinateLieMetric X g z i j = coordinateLieMetric X g z j i :=
  coordinateLieMetric_symm hz i j

example (hX : ContDiffOn ℝ ∞ X U) (i j : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => coordinateLieMetric X g z i j) U :=
  contDiffOn_coordinateLieMetric hX i j

example (hX : ContDiffOn ℝ ∞ X U) (ε : ℝ) :
    Opens (MinkowskiModel d) :=
  pullbackDomain X hX ε

example {hX : ContDiffOn ℝ ∞ X U} {ε : ℝ} {z : MinkowskiModel d} :
    z ∈ pullbackDomain X hX ε ↔ (z ∈ U ∧ z + ε • X z ∈ U) ∧ (shiftDeriv X ε z).IsInvertible :=
  mem_pullbackDomain

example (hX : ContDiffOn ℝ ∞ X U) (ε : ℝ) :
    CoordinateMetric σ d (pullbackDomain X hX ε) :=
  pullbackMetric g hX ε

example (hX : ContDiffOn ℝ ∞ X U) (ε : ℝ) :
    (pullbackMetric g hX ε).coefficient = fun z => pullbackFamily g X (ε, z) :=
  pullbackMetric_coefficient hX ε

example (hX : ContDiffOn ℝ ∞ X U) (ε : ℝ) (z : pullbackDomain X hX ε) :
    U :=
  pullbackMap X hX ε z

example (hX : ContDiffOn ℝ ∞ X U) (ε : ℝ) :
    ContMDiff 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) ∞ (pullbackMap X hX ε) :=
  contMDiff_pullbackMap hX ε

example (hX : ContDiffOn ℝ ∞ X U) (ε : ℝ) (z : pullbackDomain X hX ε)
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) z) :
    (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) (pullbackMap X hX ε) z v :
      MinkowskiModel d) = shiftDeriv X ε z v :=
  mfderiv_pullbackMap hX ε z v

example {y : U} (hRic : ∀ i j, ricciOf g.coefficient y i j = 0) (u v : MinkowskiModel d) :
    g.toLorentzMetric.ricci y u v = 0 :=
  ricci_eq_zero_of_ricciOf hRic u v

example (hRic : ∀ z ∈ U, ∀ i j, ricciOf g.coefficient z i j = 0) (hX : ContDiffOn ℝ ∞ X U) {ε : ℝ}
    {x : MinkowskiModel d} (hx : x ∈ pullbackDomain X hX ε) (j k : Fin (d + 1)) :
    ricciOf (fun z => pullbackFamily g X (ε, z)) x j k = 0 :=
  ricciOf_pullbackFamily hRic hX hx j k

example (hRic : ∀ z ∈ U, ∀ i j, ricciOf g.coefficient z i j = 0) (hX : ContDiffOn ℝ ∞ X U)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    familyRicciDeriv (pullbackFamily g X) x j k = 0 :=
  familyRicciDeriv_pullbackFamily hRic hX hx j k

example (hRic : ∀ z ∈ U, ∀ i j, ricciOf g.coefficient z i j = 0) (hX : ContDiffOn ℝ ∞ X U)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    familyRicciDeriv (g.perturbationFamily (coordinateLieMetric X g)) x j k = 0 :=
  familyRicciDeriv_lie_eq_zero hRic hX hx j k

example (hRic : ∀ z ∈ U, ∀ i j, ricciOf g.coefficient z i j = 0) (hX : ContDiffOn ℝ ∞ X U)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    g.palatini (g.curvedChristoffel (coordinateLieMetric X g)) x j k = 0 :=
  palatini_curvedChristoffel_lie_eq_zero hRic hX hx j k

end Gauge

section Linear

variable {g : CoordinateMetric σ d U}

example {h h' : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}
    (hh : ∀ p q, DifferentiableAt ℝ (fun z => h z p q) x)
    (hh' : ∀ p q, DifferentiableAt ℝ (fun z => h' z p q) x) (a i j : Fin (d + 1)) :
    g.covDerivTwo (fun z => h z + h' z) x a i j =
      g.covDerivTwo h x a i j + g.covDerivTwo h' x a i j :=
  covDerivTwo_add hh hh' a i j

example {h h' : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}
    (hh : ∀ p q, DifferentiableAt ℝ (fun z => h z p q) x)
    (hh' : ∀ p q, DifferentiableAt ℝ (fun z => h' z p q) x) (k i j : Fin (d + 1)) :
    g.curvedChristoffel (fun z => h z + h' z) x k i j =
      g.curvedChristoffel h x k i j + g.curvedChristoffel h' x k i j :=
  curvedChristoffel_add hh hh' k i j

example {P P' : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ}
    {x : MinkowskiModel d} (hP : ∀ a b c, DifferentiableAt ℝ (fun z => P z a b c) x)
    (hP' : ∀ a b c, DifferentiableAt ℝ (fun z => P' z a b c) x) (a k i j : Fin (d + 1)) :
    g.covDerivThree (fun z => P z + P' z) x a k i j =
      g.covDerivThree P x a k i j + g.covDerivThree P' x a k i j :=
  covDerivThree_add hP hP' a k i j

example {P P' : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ}
    {x : MinkowskiModel d} (hP : ∀ a b c, DifferentiableAt ℝ (fun z => P z a b c) x)
    (hP' : ∀ a b c, DifferentiableAt ℝ (fun z => P' z a b c) x) (j k : Fin (d + 1)) :
    g.palatini (fun z => P z + P' z) x j k = g.palatini P x j k + g.palatini P' x j k :=
  palatini_add hP hP' j k

example {X : MinkowskiModel d → MinkowskiModel d}
    {h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hRic : ∀ z ∈ U, ∀ i j, ricciOf g.coefficient z i j = 0) (hX : ContDiffOn ℝ ∞ X U)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    familyRicciDeriv (g.perturbationFamily (fun z => h z + coordinateLieMetric X g z)) x j k =
      familyRicciDeriv (g.perturbationFamily h) x j k :=
  familyRicciDeriv_add_lie hRic hX hh hs hx j k

example {X : MinkowskiModel d → MinkowskiModel d} (hX : ContDiffOn ℝ ∞ X U) {x : MinkowskiModel d}
    (hx : x ∈ U) (j k : Fin (d + 1)) :
    familyRicciDeriv ((minkowski σ d U).perturbationFamily
      (coordinateLieMetric X (minkowski σ d U))) x j k = 0 :=
  familyRicciDeriv_lie_minkowski hX hx j k

end Linear

section Rays

variable {g : CoordinateMetric σ d U} {ψ : MinkowskiModel d → ℝ}

example (ψ : MinkowskiModel d → ℝ) (z : MinkowskiModel d) :
    MinkowskiModel d :=
  gradientField g ψ z

example (ψ : MinkowskiModel d → ℝ) (z : MinkowskiModel d) :
    ℝ :=
  gradientNorm g ψ z

example (hψ : ContDiffOn ℝ ∞ ψ U) (i : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => gradientCovector ψ z i) U :=
  contDiffOn_gradientCovector hψ i

example (hψ : ContDiffOn ℝ ∞ ψ U) :
    ContDiffOn ℝ ∞ (g.gradientField ψ) U :=
  contDiffOn_gradientField hψ

example (hψ : ContDiffOn ℝ ∞ ψ U) :
    ContDiffOn ℝ ∞ (g.gradientNorm ψ) U :=
  contDiffOn_gradientNorm hψ

example {ι : Type} (s : Finset ι) {F P : ι → MinkowskiModel d → ℝ} {x : MinkowskiModel d}
    (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) x) (hP : ∀ i ∈ s, DifferentiableAt ℝ (P i) x)
    (v : MinkowskiModel d) :
    fderiv ℝ (fun z => ∑ i ∈ s, F i z * P i z) x v =
      ∑ i ∈ s, (fderiv ℝ (F i) x v * P i x + F i x * fderiv ℝ (P i) x v) :=
  fderiv_sum_mul s hF hP v

example (F : MinkowskiModel d → ℝ) (x v : MinkowskiModel d) :
    fderiv ℝ F x v = ∑ i, v i * fderiv ℝ F x (Pi.single i 1) :=
  fderiv_apply_eq_sum F x v

example (hψ : ContDiffOn ℝ ∞ ψ U) {z : MinkowskiModel d} (hz : z ∈ U) (k : Fin (d + 1)) :
    fderiv ℝ (fun y => g.gradientField ψ y k) z (g.gradientField ψ z) +
        ∑ i, ∑ j, christoffelOf g.coefficient z k i j * g.gradientField ψ z i *
          g.gradientField ψ z j =
      (∑ m, (g.coefficient z)⁻¹ k m * gradientCovector (g.gradientNorm ψ) z m) / 2 :=
  gradientField_covariant hψ hz k

example {z : MinkowskiModel d} (hz : z ∈ U) :
    ∑ i, ∑ j, g.coefficient z i j * g.gradientField ψ z i * g.gradientField ψ z j =
      g.gradientNorm ψ z :=
  sum_coefficient_gradientField hz

example (hψ : ContDiffOn ℝ ∞ ψ U) (hnull : ∀ z ∈ U, g.gradientNorm ψ z = 0) {γ : ℝ → U}
    {s : Set ℝ} (hs : IsOpen s)
    (hγ : ∀ t ∈ s, HasDerivAt (fun t => (γ t : MinkowskiModel d)) (g.gradientField ψ (γ t)) t) :
    g.toLorentzMetric.IsGeodesicOn s γ :=
  isGeodesicOn_ray hψ hnull hs hγ

example (hnull : ∀ z ∈ U, g.gradientNorm ψ z = 0) {γ : ℝ → U} {t : ℝ}
    (hγ : HasDerivAt (fun t => (γ t : MinkowskiModel d)) (g.gradientField ψ (γ t)) t) :
    g.toLorentzMetric.form (γ t) (curveVelocity γ t) (curveVelocity γ t) = 0 :=
  form_curveVelocity_ray hnull hγ

end Rays

end ProjectAinos.SmoothGeometry.CoordinateMetric

end CurvedLinearization

section ShortWave

open Set Filter TopologicalSpace

open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.ShortWave

open SmoothGeometry CoordinateMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

section Algebra

variable (g : CoordinateMetric σ d U)

example (k : Fin (d + 1) → ℝ) (x : MinkowskiModel d) (l : Fin (d + 1)) :
    ℝ :=
  raiseCovector g k x l

example (k : Fin (d + 1) → ℝ) (x : MinkowskiModel d) :
    ℝ :=
  covectorNorm g k x

example (a : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d) :
    ℝ :=
  amplitudeTrace g a x

example (k : Fin (d + 1) → ℝ) (a : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (j : Fin (d + 1)) :
    ℝ :=
  contractAmplitude g k a x j

example (k : Fin (d + 1) → ℝ) (a : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (j l : Fin (d + 1)) :
    ℝ :=
  shortWaveSymbol g k a x j l

example (k : Fin (d + 1) → ℝ) (a : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d) :
    Prop :=
  IsShortWaveGauge g k a x

end Algebra

example (w : Fin (d + 1) → ℝ) (P : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ)
    (j k : Fin (d + 1)) :
    ℝ :=
  gradientContraction w P j k

section AlgebraLemmas

variable {g : CoordinateMetric σ d U} {x : MinkowskiModel d}

example (hx : x ∈ U) (k : Fin (d + 1) → ℝ) (b : Fin (d + 1)) :
    ∑ m, raiseCovector g k x m * g.coefficient x m b = k b :=
  sum_raiseCovector_mul_coefficient hx k b

example (hx : x ∈ U) (k : Fin (d + 1) → ℝ) (a : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    IsShortWaveGauge g k a x ↔
      ∀ b, contractAmplitude g k a x b = k b * amplitudeTrace g a x / 2 :=
  isShortWaveGauge_iff hx k a

example (hx : x ∈ U) (k : Fin (d + 1) → ℝ) {a : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (ha : ∀ i j, a i j = a j i) (j l : Fin (d + 1)) :
    gradientContraction k (g.symbolChristoffel k a x) j l = -shortWaveSymbol g k a x j l :=
  gradientContraction_symbolChristoffel hx k ha j l

example (hx : x ∈ U) {k : Fin (d + 1) → ℝ} {a : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hg : IsShortWaveGauge g k a x) (j l : Fin (d + 1)) :
    shortWaveSymbol g k a x j l = covectorNorm g k x / 2 * a j l :=
  shortWaveSymbol_of_gauge hx hg j l

example (hx : x ∈ U) {k : Fin (d + 1) → ℝ} {a : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hg : IsShortWaveGauge g k a x) (ha : a ≠ 0) :
    (∀ j l, shortWaveSymbol g k a x j l = 0) ↔ covectorNorm g k x = 0 :=
  shortWaveSymbol_eq_zero_iff hx hg ha

end AlgebraLemmas

section Expansion

variable (g : CoordinateMetric σ d U)

example (ψ : MinkowskiModel d → ℝ) (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (j k : Fin (d + 1)) :
    ℝ :=
  transportTerm g ψ a x j k

variable {g}

example {ψ : MinkowskiModel d → ℝ} (hψ : ContDiffOn ℝ ∞ ψ U)
    {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) (b c e : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => g.symbolChristoffel (gradientCovector ψ z) (a z) z b c e) U :=
  contDiffOn_symbolChristoffel hψ ha b c e

example {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {ψ : MinkowskiModel d → ℝ} (hψ : ContDiffOn ℝ ∞ ψ U)
    {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) (has : ∀ z ∈ U, ∀ i j, a z i j = a z j i)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    familyRicciDeriv (g.perturbationFamily (fun z => F (ψ z) • a z)) x j k =
      F (ψ x) * familyRicciDeriv (g.perturbationFamily a) x j k +
        deriv F (ψ x) * transportTerm g ψ a x j k -
        deriv (deriv F) (ψ x) * shortWaveSymbol g (gradientCovector ψ x) (a x) x j k :=
  familyRicciDeriv_phase hF hψ ha has hx j k

example {ψ : MinkowskiModel d → ℝ} (hψ : ContDiffOn ℝ ∞ ψ U)
    {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) (has : ∀ z ∈ U, ∀ i j, a z i j = a z j i)
    {x : MinkowskiModel d} (hx : x ∈ U) (ε : ℝ) (j k : Fin (d + 1)) :
    familyRicciDeriv (g.perturbationFamily (fun z => Real.cos (ψ z / ε) • a z)) x j k =
      ε⁻¹ ^ 2 * Real.cos (ψ x / ε) * shortWaveSymbol g (gradientCovector ψ x) (a x) x j k -
        ε⁻¹ * Real.sin (ψ x / ε) * transportTerm g ψ a x j k +
        Real.cos (ψ x / ε) * familyRicciDeriv (g.perturbationFamily a) x j k :=
  familyRicciDeriv_shortWave hψ ha has hx ε j k

end Expansion

section Leading

variable {g : CoordinateMetric σ d U}

example {ψ : MinkowskiModel d → ℝ} (hψ : ContDiffOn ℝ ∞ ψ U)
    {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) (has : ∀ z ∈ U, ∀ i j, a z i j = a z j i)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    Tendsto (fun ε : ℝ => ε ^ 2 *
        familyRicciDeriv (g.perturbationFamily (fun z => Real.cos (ψ z / ε) • a z)) x j k -
      Real.cos (ψ x / ε) * shortWaveSymbol g (gradientCovector ψ x) (a x) x j k)
      (𝓝[≠] 0) (𝓝 0) :=
  tendsto_shortWave hψ ha has hx j k

end Leading

section Flat

example (k : Fin (d + 1) → ℝ) (z : MinkowskiModel d) :
    covectorNorm (minkowski σ d U) k z = ∑ a, lorentzSign σ a * k a ^ 2 :=
  covectorNorm_minkowski k z

example (κ : Fin (d + 1) → ℝ) (z : MinkowskiModel d) (j : Fin (d + 1)) :
    gradientCovector (fun y : MinkowskiModel d => ∑ i, κ i * y i) z j = κ j :=
  gradientCovector_linear κ z j

example (κ : Fin (d + 1) → ℝ) (z : MinkowskiModel d) :
    (minkowski σ d U).gradientField (fun y => ∑ i, κ i * y i) z =
      fun i => lorentzSign σ i * κ i :=
  gradientField_minkowski_linear κ z

example (κ : Fin (d + 1) → ℝ) (z : MinkowskiModel d) :
    (minkowski σ d U).gradientNorm (fun y => ∑ i, κ i * y i) z =
      ∑ a, lorentzSign σ a * κ a ^ 2 :=
  gradientNorm_minkowski_linear κ z

example (κ : Fin (d + 1) → ℝ) (hκ : ∑ a, lorentzSign σ a * κ a ^ 2 = 0) (x₀ : MinkowskiModel d) :
    (minkowski σ d ⊤).toLorentzMetric.IsGeodesicOn univ
      (fun t => (⟨x₀ + t • fun i => lorentzSign σ i * κ i, trivial⟩ :
        (⊤ : Opens (MinkowskiModel d)))) :=
  isGeodesicOn_minkowski_ray κ hκ x₀

end Flat

namespace PlaneWave

open ExactPlaneWave

open LorentzMetric (curveVelocity)

variable {D : Data}

example (z : MinkowskiModel 3) (i : Fin 4) :
    gradientCovector retarded z i = nullCovector i :=
  gradientCovector_retarded z i

example {z : MinkowskiModel 3} (hz : z ∈ domain D) :
    ((metric D).coefficient z)⁻¹ = Matrix.diagonal fun l => (coefficients D z l)⁻¹ :=
  coefficient_inv_metric hz

example :
    MinkowskiModel 3 :=
  rayDirection

example {z : MinkowskiModel 3} (hz : z ∈ domain D) :
    raiseCovector (metric D) nullCovector z = rayDirection :=
  raiseCovector_nullCovector hz

example {z : MinkowskiModel 3} (hz : z ∈ domain D) :
    (metric D).gradientField retarded z = rayDirection :=
  gradientField_retarded hz

example {z : MinkowskiModel 3} (hz : z ∈ domain D) :
    covectorNorm (metric D) nullCovector z = 0 :=
  covectorNorm_nullCovector hz

example {z : MinkowskiModel 3} (hz : z ∈ domain D) :
    (metric D).gradientNorm retarded z = 0 :=
  gradientNorm_retarded hz

example (x₀ : MinkowskiModel 3) (τ : ℝ) :
    retarded (x₀ + τ • rayDirection) = retarded x₀ :=
  retarded_add_ray x₀ τ

example (x₀ : domain D) (τ : ℝ) :
    domain D :=
  ray x₀ τ

example (x₀ : domain D) (t : ℝ) :
    HasDerivAt (fun t => (ray x₀ t : MinkowskiModel 3)) ((metric D).gradientField retarded
      (ray x₀ t)) t :=
  hasDerivAt_ray x₀ t

example (x₀ : domain D) :
    (metric D).toLorentzMetric.IsGeodesicOn univ (ray x₀) :=
  isGeodesicOn_planeWave_ray x₀

example (x₀ : domain D) (t : ℝ) :
    (metric D).toLorentzMetric.form (ray x₀ t) (curveVelocity (ray x₀) t)
      (curveVelocity (ray x₀) t) = 0 :=
  form_curveVelocity_planeWave_ray x₀ t

example {X : MinkowskiModel 3 → MinkowskiModel 3} (hX : ContDiffOn ℝ ∞ X (domain strong.toData))
    {x : MinkowskiModel 3} (hx : x ∈ domain strong.toData) (j k : Fin 4) :
    familyRicciDeriv ((metric strong.toData).perturbationFamily
      (coordinateLieMetric X (metric strong.toData))) x j k = 0 :=
  familyRicciDeriv_lie_strong hX hx j k

example :
    Matrix (Fin 4) (Fin 4) ℝ :=
  crossAmplitude

example :
    crossAmplitude ≠ 0 :=
  crossAmplitude_ne_zero

example {z : MinkowskiModel 3} (hz : z ∈ domain D) :
    IsShortWaveGauge (metric D) nullCovector crossAmplitude z :=
  isShortWaveGauge_cross hz

example {z : MinkowskiModel 3} (hz : z ∈ domain D) (j l : Fin 4) :
    shortWaveSymbol (metric D) nullCovector crossAmplitude z j l = 0 :=
  shortWaveSymbol_cross hz j l

end PlaneWave

end ProjectAinos.GeneralRelativity.ShortWave

end ShortWave
