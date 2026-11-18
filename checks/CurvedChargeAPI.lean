/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateTangent
import ProjectAinos.SmoothGeometry.Lorentzian.CoordinatePotential
import ProjectAinos.GeneralRelativity.ChargedMotion
import ProjectAinos.GeneralRelativity.FlatChargedMotion
import ProjectAinos.Electrodynamics.CurvedAction

/-! Public consumers of the field and the charge on a curved background: tangent fields on an
open set of the model space in coordinates, the action of a potential on a coordinate metric with
its first variation, its stationarity and the native equation `∇_a F^{ab} = j^b`, the line
integral of a potential with its first variation, the equation of motion of a charge on a curved
background with its gauge invariance, the flat case of the motion of a charge, and the Maxwell
equations from the action on a curved background with the flat density and functional. Default
elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/

noncomputable section

open Bundle Set Filter TopologicalSpace

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

example (x y : U) (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) y) :
    (trivializationAt (MinkowskiModel d) (TangentSpace 𝓘(ℝ, MinkowskiModel d)) x ⟨y, v⟩).2 =
      v :=
  trivializationAt_snd x y v

example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω} {f : F → U}
    {X : F → MinkowskiModel d} {p₀ : F} :
    ContMDiffAt 𝓘(ℝ, F) (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) n
        (fun p => TotalSpace.mk' (MinkowskiModel d)
          (E := TangentSpace 𝓘(ℝ, MinkowskiModel d)) (f p) (X p)) p₀ ↔
      ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, MinkowskiModel d) n f p₀ ∧ ContDiffAt ℝ n X p₀ :=
  contMDiffAt_tangent_iff

example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω} {f : F → U} {p₀ : F}
    (hf : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, MinkowskiModel d) n f p₀) :
    ContDiffAt ℝ n (fun p => (f p : MinkowskiModel d)) p₀ :=
  contDiffAt_val hf

example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω} {f : F → U} {p₀ : F} :
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, MinkowskiModel d) n f p₀ ↔
      ContDiffAt ℝ n (fun p => (f p : MinkowskiModel d)) p₀ :=
  contMDiffAt_iff_contDiffAt_val

example {γ : ℝ → U} {t : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, MinkowskiModel d) γ t) :
    (curveVelocity γ t : MinkowskiModel d) = deriv (fun s => (γ s : MinkowskiModel d)) t :=
  curveVelocity_val hγ

example {Γ : ℝ × ℝ → U} {z : ℝ × ℝ} (v : ℝ × ℝ)
    (hΓ : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, MinkowskiModel d) Γ z) :
    (familyVelocity Γ v z : MinkowskiModel d) =
      fderiv ℝ (fun q => (Γ q : MinkowskiModel d)) z v :=
  familyVelocity_val v hΓ

example (x : U) (α : MinkowskiModel d →L[ℝ] ℝ) :
    ((minkowski (σ := σ) (U := U)).toLorentzMetric.sharp x α : MinkowskiModel d) =
      Minkowski.sharp σ α :=
  minkowski_sharp x α

end ProjectAinos.SmoothGeometry.CoordinateMetric

open Set TopologicalSpace MeasureTheory Filter

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

namespace CoordinateMetric

variable {U : Opens (MinkowskiModel d)} {g : CoordinateMetric σ d U}

example (A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ) (z : MinkowskiModel d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  potentialField A z

example (A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ) (z : MinkowskiModel d)
    (a b : Fin (d + 1)) :
    potentialField A z a b = -potentialField A z b a :=
  potentialField_antisymm A z a b

example (F G : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (z : MinkowskiModel d) :
    ℝ :=
  fieldPairing g F G z

example (F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (z : MinkowskiModel d)
    (a b : Fin (d + 1)) :
    ℝ :=
  raisedField g F z a b

example (j : MinkowskiModel d → Fin (d + 1) → ℝ) (A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ)
    (z : MinkowskiModel d) :
    ℝ :=
  potentialDensity g j A z

example (j : MinkowskiModel d → Fin (d + 1) → ℝ)
    (A η : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ) (ε : ℝ) :
    ℝ :=
  potentialAction g j A η ε

example (j : MinkowskiModel d → Fin (d + 1) → ℝ) (A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ)
    (z : MinkowskiModel d) (b : Fin (d + 1)) :
    ℝ :=
  potentialEuler g j A z b

variable {A η : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ}

example (hA : ContDiffOn ℝ ∞ A U) {z : MinkowskiModel d} (hz : z ∈ U) (v : MinkowskiModel d) :
    DifferentiableAt ℝ (fun w => A w v) z :=
  differentiableAt_component hA hz v

example {z : MinkowskiModel d} (hz : z ∉ tsupport η) (v : MinkowskiModel d) :
    (fun w => η w v) =ᶠ[𝓝 z] fun _ => 0 :=
  component_eventually_zero hz v

example {z : MinkowskiModel d} (hz : z ∉ tsupport η) :
    potentialField η z = 0 :=
  potentialField_of_notMem hz

example (hA : ContDiffOn ℝ ∞ A U) (hη : ContDiff ℝ ∞ η) (hKU : tsupport η ⊆ U) (ε : ℝ)
    (z : MinkowskiModel d) :
    potentialField (fun w => A w + ε • η w) z = potentialField A z + ε • potentialField η z :=
  potentialField_add hA hη hKU ε z

example (F G : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (ε : ℝ)
    (z : MinkowskiModel d) :
    g.fieldPairing (fun w => F w + ε • G w) (fun w => F w + ε • G w) z =
      g.fieldPairing F F z + ε * (g.fieldPairing F G z + g.fieldPairing G F z) +
        ε ^ 2 * g.fieldPairing G G z :=
  fieldPairing_add_smul F G ε z

example {n : ℕ} (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, f a b c e = ∑ c, ∑ e, ∑ a, ∑ b, f a b c e :=
  sum4_swap_pairs f

example {z : MinkowskiModel d} (hz : z ∈ U)
    (F G : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    g.fieldPairing G F z = g.fieldPairing F G z :=
  fieldPairing_comm hz F G

example (hA : ContDiffOn ℝ ∞ A U) (hη : ContDiff ℝ ∞ η) (hKU : tsupport η ⊆ U)
    (j : MinkowskiModel d → Fin (d + 1) → ℝ) (ε : ℝ) (z : MinkowskiModel d) :
    g.potentialDensity j (fun w => A w + ε • η w) z - g.potentialDensity j A z =
      (ε * (-(g.fieldPairing (potentialField A) (potentialField η) z / 2) -
          ∑ b, η z (Pi.single b 1) * j z b) -
        ε ^ 2 * (g.fieldPairing (potentialField η) (potentialField η) z / 4)) *
        densityOf g.coefficient z :=
  potentialDensity_sub hA hη hKU j ε z

example (hA : ContDiffOn ℝ ∞ A U) (a b : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => potentialField A z a b) U :=
  contDiffOn_potentialField hA a b

example {F G : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hF : ∀ a b, ContDiffOn ℝ ∞ (fun z => F z a b) U)
    (hG : ∀ a b, ContDiffOn ℝ ∞ (fun z => G z a b) U) :
    ContDiffOn ℝ ∞ (g.fieldPairing F G) U :=
  contDiffOn_fieldPairing hF hG

example {F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hF : ∀ a b, ContDiffOn ℝ ∞ (fun z => F z a b) U) (a b : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => g.raisedField F z a b) U :=
  contDiffOn_raisedField hF a b

example {z : MinkowskiModel d} (hz : z ∈ U) :
    g.fieldPairing (potentialField A) (potentialField η) z =
      2 * ∑ c, ∑ e, g.raisedField (potentialField A) z c e *
        fderiv ℝ (fun w => η w (Pi.single e 1)) z (Pi.single c 1) :=
  fieldPairing_potentialField hz

example (hA : ContDiffOn ℝ ∞ A U) (a b : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun w => densityOf g.coefficient w * g.raisedField (potentialField A) w a b)
      U :=
  contDiffOn_density_raisedField hA a b

example (hA : ContDiffOn ℝ ∞ A U) {j : MinkowskiModel d → Fin (d + 1) → ℝ}
    (hj : ∀ b, ContinuousOn (fun z => j z b) U) (b : Fin (d + 1)) :
    ContinuousOn (fun z => g.potentialEuler j A z b) U :=
  continuousOn_potentialEuler hA hj b

example (hA : ContDiffOn ℝ ∞ A U) (hη : ContDiff ℝ ∞ η) (hK : HasCompactSupport η)
    (hKU : tsupport η ⊆ U) {j : MinkowskiModel d → Fin (d + 1) → ℝ}
    (hj : ∀ b, ContinuousOn (fun z => j z b) U) :
    HasDerivAt (g.potentialAction j A η)
      (∑ b, ∫ x, η x (Pi.single b 1) * g.potentialEuler j A x b) 0 :=
  hasDerivAt_potentialAction hA hη hK hKU hj

example (hA : ContDiffOn ℝ ∞ A U) {j : MinkowskiModel d → Fin (d + 1) → ℝ}
    (hj : ∀ b, ContinuousOn (fun z => j z b) U) :
    (∀ η : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ U → HasDerivAt (g.potentialAction j A η) 0 0) ↔
      ∀ z ∈ U, ∀ b, g.potentialEuler j A z b = 0 :=
  isPotentialStationary_iff hA hj

end CoordinateMetric

section TwoForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

example (f : V [⋀^Fin 2]→L[ℝ] ℝ) (v w : V) :
    f ![v, w] = -f ![w, v] :=
  alternatingTwo_swap f v w

example (f : V [⋀^Fin 2]→L[ℝ] ℝ) {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → V) (y : V) :
    f ![∑ a ∈ s, c a • u a, y] = ∑ a ∈ s, c a * f ![u a, y] :=
  alternatingTwo_sum_left f s c u y

example (f : V [⋀^Fin 2]→L[ℝ] ℝ) {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → V) (x : V) :
    f ![x, ∑ b ∈ s, c b • u b] = ∑ b ∈ s, c b * f ![x, u b] :=
  alternatingTwo_sum_right f s c u x

end TwoForm

namespace CoordinateMetric

variable {U : Opens (MinkowskiModel d)} {g : CoordinateMetric σ d U}
  {A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ}

example (F : DifferentialForm.SmoothForm 𝓘(ℝ, MinkowskiModel d) U 2) (x y : U) (i k : Fin (d + 1)) :
    g.toLorentzMetric.raisedTwoFormComponent F (physicalChart x) y i k =
      ∑ a, ∑ b, (g.coefficient y)⁻¹ a i * (g.coefficient y)⁻¹ b k *
        F y ![Pi.single a 1, Pi.single b 1] :=
  raisedTwoFormComponent_eq F x y i k

example (hA : ContDiffOn ℝ ∞ A U) (F : DifferentialForm.SmoothForm 𝓘(ℝ, MinkowskiModel d) U 2)
    (hF : ∀ (y : U) (a b : Fin (d + 1)), F y ![Pi.single a 1, Pi.single b 1] =
      potentialField A y a b)
    (x : U) (b : Fin (d + 1)) :
    (g.toLorentzMetric.twoFormDivergence F x : MinkowskiModel d) b =
      (densityOf g.coefficient x)⁻¹ * ∑ a, fderiv ℝ (fun w => densityOf g.coefficient w *
        g.raisedField (potentialField A) w a b) x (Pi.single a 1) :=
  twoFormDivergence_component hA F hF x b

example (hA : ContDiffOn ℝ ∞ A U) (F : DifferentialForm.SmoothForm 𝓘(ℝ, MinkowskiModel d) U 2)
    (hF : ∀ (y : U) (a b : Fin (d + 1)), F y ![Pi.single a 1, Pi.single b 1] =
      potentialField A y a b)
    (J : ∀ y : U, TangentSpace 𝓘(ℝ, MinkowskiModel d) y) {j : MinkowskiModel d → Fin (d + 1) → ℝ}
    (hJ : ∀ (y : U) b, (J y : MinkowskiModel d) b = j y b) :
    g.toLorentzMetric.twoFormDivergence F = J ↔ ∀ z ∈ U, ∀ b, g.potentialEuler j A z b = 0 :=
  twoFormDivergence_eq_iff hA F hF J hJ

end CoordinateMetric

end ProjectAinos.SmoothGeometry

open Bundle Set Filter MeasureTheory TopologicalSpace

open scoped Manifold ContDiff Topology

namespace ProjectAinos.GeneralRelativity

open SmoothGeometry LorentzMetric CoordinateMetric Variational

variable {d : ℕ} {U : Opens (MinkowskiModel d)}

local notation "E" => MinkowskiModel d

local notation "I" => 𝓘(ℝ, MinkowskiModel d)

local notation "J" => 𝓘(ℝ, ℝ × ℝ)

example (A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ) (γ : ℝ → U) (a b : ℝ) :
    ℝ :=
  lineIntegral A γ a b

example (A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ) (z v : MinkowskiModel d) :
    MinkowskiModel d →L[ℝ] ℝ :=
  fieldCovector A z v

example (A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ) (z v w : MinkowskiModel d) :
    fieldCovector A z v w = fderiv ℝ A z w v - fderiv ℝ A z v w :=
  fieldCovector_apply A z v w

example (A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ) (z v : MinkowskiModel d) :
    fieldCovector A z v v = 0 :=
  fieldCovector_self A z v

example (g : LorentzMetric .timeNegative d U) (m e : ℝ)
    (A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ) (γ : ℝ → U) (a b : ℝ) :
    ℝ :=
  chargedAction g m e A γ a b

example (g : LorentzMetric .timeNegative d U) (m e : ℝ)
    (A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ) (γ : ℝ → U) (a b : ℝ) :
    Prop :=
  ChargedStationary g m e A γ a b

example (g : LorentzMetric .timeNegative d U) (m e : ℝ)
    (A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ) (γ : ℝ → U) (t : ℝ) :
    TangentSpace 𝓘(ℝ, MinkowskiModel d) (γ t) :=
  chargedResidual g m e A γ t

example (g : LorentzMetric .timeNegative d U) (x : U) (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x)
    (α : MinkowskiModel d →L[ℝ] ℝ) :
    g.form x v (g.sharp x α) = α v :=
  form_sharp_model g x v α

variable {A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ}

example {Γ : ℝ × ℝ → U} {z : ℝ × ℝ} (hΓ : ContMDiffAt J I 2 Γ z) :
    (fun p : ℝ × ℝ => A (Γ p) (curveVelocity (fun s => Γ (p.1, s)) p.2)) =ᶠ[𝓝 z]
      fun p => A (Γ p) (fderiv ℝ (fun q => (Γ q : E)) p (0, 1)) :=
  lineDensity_eventuallyEq hΓ

example (hA : ContDiffOn ℝ 1 A U) {Γ : ℝ × ℝ → U} {z : ℝ × ℝ} (hΓ : ContMDiffAt J I 2 Γ z)
    (v : ℝ × ℝ) :
    ContDiffAt ℝ 1 (fun p => A (Γ p) (fderiv ℝ (fun q => (Γ q : E)) p v)) z :=
  coordinateDensity_contDiffAt hA hΓ v

example (hA : ContDiffOn ℝ 1 A U) {Γ : ℝ × ℝ → U} {ρ : ℝ → ℝ × ℝ} {s : ℝ} {w : ℝ × ℝ}
    (hρ : HasDerivAt ρ w s) (hΓ : ContMDiffAt J I 2 Γ (ρ s)) (v : ℝ × ℝ) :
    HasDerivAt (fun r => A (Γ (ρ r)) (fderiv ℝ (fun q => (Γ q : E)) (ρ r) v))
      (fderiv ℝ A (Γ (ρ s)) (fderiv ℝ (fun q => (Γ q : E)) (ρ s) w)
          (fderiv ℝ (fun q => (Γ q : E)) (ρ s) v) +
        A (Γ (ρ s)) (fderiv ℝ (fderiv ℝ (fun q => (Γ q : E))) (ρ s) w v)) s :=
  coordinateDensity_hasDerivAt hA hρ hΓ v

example (hA : ContDiffOn ℝ 1 A U) {Γ : ℝ × ℝ → U} {ε₀ a b : ℝ}
    (hΓ : ∀ t ∈ uIcc a b, ContMDiffAt J I 2 Γ (ε₀, t)) (ha : ∀ᶠ ε in 𝓝 ε₀, Γ (ε, a) = Γ (ε₀, a))
    (hb : ∀ᶠ ε in 𝓝 ε₀, Γ (ε, b) = Γ (ε₀, b)) :
    HasDerivAt (fun ε => lineIntegral A (fun t => Γ (ε, t)) a b)
      (∫ t in a..b, fieldCovector A (Γ (ε₀, t)) (curveVelocity (fun s => Γ (ε₀, s)) t)
        (familyVelocity Γ (1, 0) (ε₀, t))) ε₀ :=
  lineIntegral_family_hasDerivAt hA hΓ ha hb

example {x y : U} (h : x = y) (v : TangentSpace I x) :
    TotalSpace.mk' E y (tangentSpaceCast I x y v) = TotalSpace.mk' E x v :=
  mk_tangentSpaceCast h v

example {γ : ℝ → U} {a b t : ℝ} (V : ManifoldCurveVariation («E» := E) γ a b) (ht : t ∈ uIcc a b) :
    ContMDiffAt 𝓘(ℝ) ((I).prod I) 1
      (fun s => TotalSpace.mk' E (γ s) (variationField V s)) t :=
  variationField_contMDiffAt V ht

example (g : LorentzMetric .timeNegative d U) (m : ℝ) {γ : ℝ → U} {t : ℝ}
    {X : AlongField (d := d) γ} (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : Timelike g (curveVelocity γ t))
    (hX : ContMDiffAt 𝓘(ℝ) ((I).prod I) 0 (fun s => TotalSpace.mk' E (γ s) (X s)) t) :
    ContinuousAt (fun s => -(m / speedAlong g γ s) * g.form (γ s) (X s)
      (g.covariantAlong (curveVelocity γ) s -
        (deriv (speedAlong g γ) s / speedAlong g γ s) • curveVelocity γ s)) t :=
  freeResidual_continuousAt g m hγ hv hX

example (hA : ContDiffOn ℝ 1 A U) {γ : ℝ → U} {t : ℝ} {X : AlongField (d := d) γ}
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hX : ContMDiffAt 𝓘(ℝ) ((I).prod I) 0 (fun s => TotalSpace.mk' E (γ s) (X s)) t) :
    ContinuousAt (fun s => fieldCovector A (γ s) (curveVelocity γ s) (X s)) t :=
  fieldCovector_continuousAt hA hγ hX

example (g : LorentzMetric .timeNegative d U) (m e : ℝ) (hA : ContDiffOn ℝ 1 A U) {γ : ℝ → U}
    {t : ℝ} {X : AlongField (d := d) γ} (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : Timelike g (curveVelocity γ t))
    (hX : ContMDiffAt 𝓘(ℝ) ((I).prod I) 0 (fun s => TotalSpace.mk' E (γ s) (X s)) t) :
    ContinuousAt (fun s => g.form (γ s) (X s) (chargedResidual g m e A γ s)) t :=
  chargedResidual_continuousAt g m e hA hγ hv hX

example (hA : ContDiffOn ℝ 1 A U) {γ : ℝ → U} {a b : ℝ}
    (V : ManifoldCurveVariation («E» := E) γ a b) :
    HasDerivAt (fun ε => lineIntegral A (fun t => V.family (ε, t)) a b)
      (∫ t in a..b, fieldCovector A (γ t) (curveVelocity γ t) (variationField V t)) 0 :=
  lineIntegral_variation_hasDerivAt hA V

example (g : LorentzMetric .timeNegative d U) (m e : ℝ) (hA : ContDiffOn ℝ 1 A U) {γ : ℝ → U}
    {a b : ℝ} (V : ManifoldCurveVariation («E» := E) γ a b)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : ∀ t ∈ uIcc a b, Timelike g (curveVelocity γ t)) :
    HasDerivAt (fun ε => chargedAction g m e A (fun t => V.family (ε, t)) a b)
      (∫ t in a..b, g.form (γ t) (variationField V t) (chargedResidual g m e A γ t)) 0 :=
  chargedAction_variation_hasDerivAt g m e hA V hγ hv

example (g : LorentzMetric .timeNegative d U) (m e : ℝ) (hA : ContDiffOn ℝ 1 A U) {γ : ℝ → U}
    {a b : ℝ} (hab : a < b) (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : ∀ t ∈ uIcc a b, Timelike g (curveVelocity γ t)) :
    ChargedStationary g m e A γ a b ↔ ∀ t ∈ Ioo a b,
      (m / speedAlong g γ t) • (g.covariantAlong (curveVelocity γ) t -
          (deriv (speedAlong g γ) t / speedAlong g γ t) • curveVelocity γ t) =
        e • g.sharp (γ t) (fieldCovector A (γ t) (curveVelocity γ t)) :=
  chargedStationary_iff g m e hA hab hγ hv

example {χ : MinkowskiModel d → ℝ} {z : MinkowskiModel d} (hA : DifferentiableAt ℝ A z)
    (hχ : ContDiffAt ℝ 2 χ z) (v : MinkowskiModel d) :
    fieldCovector (fun y => A y + fderiv ℝ χ y) z v = fieldCovector A z v :=
  fieldCovector_gauge hA hχ v

example {χ : MinkowskiModel d → ℝ} (hA : ContinuousOn A U) (hχ : ContDiffOn ℝ 1 χ U) {γ : ℝ → U}
    {a b : ℝ} (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 1 γ t) :
    lineIntegral (fun y => A y + fderiv ℝ χ y) γ a b =
      lineIntegral A γ a b + (χ (γ b) - χ (γ a)) :=
  lineIntegral_gauge hA hχ hγ

example (g : LorentzMetric .timeNegative d U) (m e : ℝ) (hA : ContDiffOn ℝ 1 A U)
    {χ : MinkowskiModel d → ℝ} (hχ : ContDiffOn ℝ 2 χ U) {γ : ℝ → U} {a b : ℝ} (hab : a < b)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : ∀ t ∈ uIcc a b, Timelike g (curveVelocity γ t)) :
    ChargedStationary g m e (fun y => A y + fderiv ℝ χ y) γ a b ↔
      ChargedStationary g m e A γ a b :=
  chargedStationary_gauge_iff g m e hA hχ hab hγ hv

end ProjectAinos.GeneralRelativity

open Set Filter TopologicalSpace

open scoped Manifold ContDiff Topology

namespace ProjectAinos.GeneralRelativity

open SmoothGeometry LorentzMetric CoordinateMetric SpecialRelativity Electrodynamics

local notation "I" => 𝓘(ℝ, MinkowskiModel 3)

example {A : Electrodynamics.Potential} {z : Spacetime} (hA : DifferentiableAt ℝ A z)
    (v : Spacetime) :
    fieldCovector (potentialCovector A) z v = -oneCovector ((fieldTensor A z).curryLeft v) :=
  fieldCovector_potentialCovector hA v

example (m e : ℝ) {A : Electrodynamics.Potential} {U : Opens Spacetime} (hA : ContDiffOn ℝ 2 A U)
    {γ : ℝ → U} {a b : ℝ} (hab : a < b) (hγ : ContDiff ℝ 2 (fun t => (γ t : Spacetime)))
    (hv : ∀ t ∈ Icc a b, Minkowski.Timelike (deriv (fun s => (γ s : Spacetime)) t)) :
    ChargedStationary (minkowski (σ := .timeNegative) (U := U)).toLorentzMetric m e
        (potentialCovector A) γ a b ↔
      Mechanics.Stationary a b (chargedLagrangian m e A) (fun t => (γ t : Spacetime)) :=
  chargedStationary_minkowski_iff m e hA hab hγ hv

end ProjectAinos.GeneralRelativity

open Set TopologicalSpace MeasureTheory

open scoped Manifold ContDiff

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.DifferentialForm

namespace Curved

variable {U : Opens (MinkowskiModel 3)}

example (g : CoordinateMetric .timeNegative 3 U) (o : OrientedAtlas 4 U)
    {A : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] ℝ} (hA : ContDiffOn ℝ ∞ A U)
    (F : Field (M := U))
    (hF : ∀ (y : U) (a b : Fin 4), F y ![Pi.single a 1, Pi.single b 1] =
      CoordinateMetric.potentialField A y a b)
    (j : CurrentVector (M := U)) {jc : MinkowskiModel 3 → Fin 4 → ℝ}
    (hj : ∀ (y : U) (b : Fin 4), (j y : MinkowskiModel 3) b = jc y b)
    (hjc : ∀ b, ContinuousOn (fun z => jc z b) U) :
    (∀ η : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ U → HasDerivAt (g.potentialAction jc A η) 0 0) ↔
      smoothExteriorDerivative (excitation g.toLorentzMetric o F) =
        currentForm g.toLorentzMetric o j :=
  potentialStationary_iff_sourced g o hA F hF j hj hjc

example (g : CoordinateMetric .timeNegative 3 U) (o : OrientedAtlas 4 U)
    {A : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] ℝ} (hA : ContDiffOn ℝ ∞ A U)
    (F : Field (M := U))
    (hF : ∀ (y : U) (a b : Fin 4), F y ![Pi.single a 1, Pi.single b 1] =
      CoordinateMetric.potentialField A y a b)
    (hdF : smoothExteriorDerivative F = 0) (j : CurrentVector (M := U))
    {jc : MinkowskiModel 3 → Fin 4 → ℝ}
    (hj : ∀ (y : U) (b : Fin 4), (j y : MinkowskiModel 3) b = jc y b)
    (hjc : ∀ b, ContinuousOn (fun z => jc z b) U) :
    Maxwell g.toLorentzMetric o F j ↔
      ∀ η : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
        tsupport η ⊆ U → HasDerivAt (g.potentialAction jc A η) 0 0 :=
  maxwell_iff_potentialStationary g o hA F hF hdF j hj hjc

example (g : CoordinateMetric .timeNegative 3 U) (k : MinkowskiModel 3 → Fin 4 → ℝ)
    (A : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] ℝ) (z : MinkowskiModel 3) :
    g.potentialDensity (fun y b => -k y b) A z =
      (-(g.fieldPairing (CoordinateMetric.potentialField A)
          (CoordinateMetric.potentialField A) z / 4) +
        ∑ b, A z (Pi.single b 1) * k z b) * CoordinateMetric.densityOf g.coefficient z :=
  potentialDensity_matter g k A z

example (g : CoordinateMetric .timeNegative 3 U) (o : OrientedAtlas 4 U)
    {A : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] ℝ} (hA : ContDiffOn ℝ ∞ A U)
    (F : Field (M := U))
    (hF : ∀ (y : U) (a b : Fin 4), F y ![Pi.single a 1, Pi.single b 1] =
      CoordinateMetric.potentialField A y a b)
    (k : CurrentVector (M := U)) {kc : MinkowskiModel 3 → Fin 4 → ℝ}
    (hk : ∀ (y : U) (b : Fin 4), (k y : MinkowskiModel 3) b = kc y b)
    (hkc : ∀ b, ContinuousOn (fun z => kc z b) U) :
    (∀ η : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ U → HasDerivAt (g.potentialAction (fun y b => -kc y b) A η) 0 0) ↔
      smoothExteriorDerivative (excitation g.toLorentzMetric o F) =
        currentForm g.toLorentzMetric o (-k) :=
  potentialStationary_matter_iff g o hA F hF k hk hkc

end Curved

open Module exteriorPower

open SmoothGeometry.Minkowski SpecialRelativity VacuumAction

example (F G : TwoForm) :
    coefficient (wedgeFiber F (star G)) = exteriorPairing F G :=
  coefficient_wedge_star F G

example (A : Potential) (x : Spacetime) :
    Variational.density VacuumAction.lagrangian A x =
      -(tensorContraction (fieldTensor A x) (fieldTensor A x) / 4) :=
  vacuumDensity_eq A x

example {A : Potential} {z : Spacetime} (hA : DifferentiableAt ℝ A z) (a b : Fin 4) :
    CoordinateMetric.potentialField (potentialCovector A) z a b =
      component (fieldTensor A z) a b :=
  potentialField_potentialCovector hA a b

example {U : Opens Spacetime} {A : Potential} {x : Spacetime} (hA : DifferentiableAt ℝ A x)
    (j : Spacetime → Spacetime) :
    (CoordinateMetric.minkowski .timeNegative 3 U).potentialDensity j (potentialCovector A) x =
      Variational.density (SourcedAction.lagrangian fun z => interior (j z) (coordinateForm id))
        A x :=
  potentialDensity_minkowski hA j

example {U : Opens Spacetime} {A η : Potential} (hA : Differentiable ℝ A)
    (hη : Differentiable ℝ η) (j : Spacetime → Spacetime) (ε : ℝ) :
    (CoordinateMetric.minkowski .timeNegative 3 U).potentialAction j (potentialCovector A)
        (potentialCovector η) ε =
      ∫ x, (Variational.density
          (SourcedAction.lagrangian fun z => interior (j z) (coordinateForm id))
          (Variational.perturb A η ε) x -
        Variational.density
          (SourcedAction.lagrangian fun z => interior (j z) (coordinateForm id)) A x) :=
  potentialAction_minkowski hA hη j ε

end ProjectAinos.Electrodynamics
