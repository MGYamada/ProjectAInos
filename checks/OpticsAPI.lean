/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Euclidean.Similarity
import ProjectAinos.Electrodynamics.Optics.Basic
import ProjectAinos.Electrodynamics.Optics.Imaging
import ProjectAinos.SmoothGeometry.ODE.Riccati
import ProjectAinos.Electrodynamics.Optics.NarrowBundle
import ProjectAinos.Electrodynamics.Optics.AngularEikonal
import ProjectAinos.SmoothGeometry.Wave.HighFrequency
import ProjectAinos.Electrodynamics.Optics.Eikonal
import ProjectAinos.Electrodynamics.Optics.RayOptics
import ProjectAinos.SmoothGeometry.Wave.Energy
import ProjectAinos.Electrodynamics.Optics.Error

/-! Public consumers of geometrical optics (Landau–Lifshitz §§53–58): the exact expansion of the
wave operator on a high-frequency phase, the eikonal and transport equations of a high-frequency
potential with its null rays and conserved intensity, rays in a medium by a complete integral and
Fermat's principle, the angular eikonal and the canonical ray map, the Riccati law of the
curvature of a wave front with its focal points and the blow-up of the amplitude, the first
variation of the optical length with the sine condition and Maxwell's theorem on absolute
instruments, and the energy estimate for the error of geometrical optics. Default elaborator
options are intentional: these checks must not rely on the implementation's transparency
settings. Every statement is pinned with its type. -/

noncomputable section


section Similarity

open Set Filter

open scoped Topology RealInnerProductSpace

namespace ProjectAinos.SmoothGeometry.Similarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

example {A : E →L[ℝ] E} {k : ℝ} (hA : ∀ v, ‖A v‖ = k * ‖v‖) (u v : E) :
    ⟪A u, A v⟫ = k ^ 2 * ⟪u, v⟫ :=
  inner_map_map_of_norm hA u v

example {F : Type*} (T : F → F → F → ℝ) (hs : ∀ a b c, T a b c = T b a c)
    (ha : ∀ a b c, T a b c = -T a c b) (a b c : F) :
    T a b c = 0 :=
  eq_zero_of_symm_of_antisymm T hs ha a b c

example (K : Submodule ℝ E) [K.HasOrthogonalProjection] (n : ℝ) (x v : E) :
    n * ‖fderiv ℝ K.reflection x v‖ = n * ‖v‖ :=
  norm_fderiv_reflection K n x v

example (K : Submodule ℝ E) [K.HasOrthogonalProjection] :
    ContDiff ℝ 2 K.reflection :=
  contDiff_reflection K

variable [FiniteDimensional ℝ E]

example {φ : E → E} {x : E} {k : ℝ} (hk : 0 < k) (hφ : ContDiffAt ℝ 2 φ x)
    (hA : ∀ᶠ y in 𝓝 x, ∀ v, ‖fderiv ℝ φ y v‖ = k * ‖v‖) :
    fderiv ℝ (fderiv ℝ φ) x = 0 :=
  fderiv_fderiv_eq_zero_of_norm hk hφ hA

example {n n' : ℝ} (hn : 0 < n) (hn' : 0 < n') {φ : E → E} {Ω : Set E} (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hφ : ContDiffOn ℝ 2 φ Ω)
    (hiso : ∀ x ∈ Ω, ∀ v, n' * ‖fderiv ℝ φ x v‖ = n * ‖v‖) :
    ∃ (L : E ≃ₗᵢ[ℝ] E) (c : E), ∀ x ∈ Ω, φ x = (n / n') • L x + c :=
  exists_linearIsometryEquiv_of_norm_fderiv hn hn' hΩ hΩc hφ hiso

end ProjectAinos.SmoothGeometry.Similarity

end Similarity

section Basic

namespace ProjectAinos.Electrodynamics.Optics

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (n : E3 → ℝ) (γ : ℝ → E3) (a b : ℝ) :
    ℝ :=
  opticalLength n γ a b

end ProjectAinos.Electrodynamics.Optics

end Basic

section Imaging

open Set Filter MeasureTheory

open scoped Topology ContDiff RealInnerProductSpace

namespace ProjectAinos.Electrodynamics.Optics.Imaging

section Similarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

example {n n' : ℝ} (hn : 0 < n) (hn' : 0 < n') {φ : E → E} {Ω : Set E} (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hφ : ContDiffOn ℝ 2 φ Ω)
    (hiso : ∀ x ∈ Ω, ∀ v, n' * ‖fderiv ℝ φ x v‖ = n * ‖v‖) :
    ∃ (L : E ≃ₗᵢ[ℝ] E) (c : E), ∀ x ∈ Ω, φ x = (n / n') • L x + c :=
  isSimilarity_of_absolute hn hn' hΩ hΩc hφ hiso

example (K : Submodule ℝ E) [K.HasOrthogonalProjection] {n : ℝ} (hn : 0 < n) :
    ∃ (L : E ≃ₗᵢ[ℝ] E) (c : E), ∀ x, K.reflection x = (n / n) • L x + c :=
  isSimilarity_reflection K hn

end Similarity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Rays

example (n : E3 → ℝ) :
    Mechanics.Lagrangian E3 :=
  opticalLagrangian n

example (n : E3 → ℝ) (γ : ℝ → E3) (a b : ℝ) :
    Mechanics.action a b (opticalLagrangian n) γ = opticalLength n γ a b :=
  action_opticalLagrangian n γ a b

example (γ : ℝ → E3) (t : ℝ) :
    E3 :=
  unitTangent γ t

example {v : E3} (hv : v ≠ 0) :
    HasFDerivAt (fun z : E3 => ‖z‖) (‖v‖⁻¹ • innerSL ℝ v) v :=
  hasFDerivAt_norm hv

example {n : E3 → ℝ} {q v : E3} (hn : DifferentiableAt ℝ n q) (hv : v ≠ 0) (t : ℝ) :
    HasFDerivAt (opticalLagrangian n t)
      (n q • (‖v‖⁻¹ • innerSL ℝ v).comp (ContinuousLinearMap.snd ℝ E3 E3) +
        ‖v‖ • (fderiv ℝ n q).comp (ContinuousLinearMap.fst ℝ E3 E3)) (q, v) :=
  hasFDerivAt_opticalLagrangian hn hv t

example {n : E3 → ℝ} {γ : ℝ → E3} {t : ℝ} (hn : DifferentiableAt ℝ n (γ t)) (hγ : deriv γ t ≠ 0) :
    Mechanics.momentum (opticalLagrangian n) γ t = n (γ t) • innerSL ℝ (unitTangent γ t) :=
  momentum_opticalLagrangian hn hγ

example {n : E3 → ℝ} {γ : ℝ → E3} {t : ℝ} (hn : DifferentiableAt ℝ n (γ t)) (hγ : deriv γ t ≠ 0) :
    Mechanics.force (opticalLagrangian n) γ t = ‖deriv γ t‖ • fderiv ℝ n (γ t) :=
  force_opticalLagrangian hn hγ

example {V : Set E3} (hV : IsOpen V) :
    IsOpen {p : ℝ × (E3 × E3) | p.2.1 ∈ V ∧ p.2.2 ≠ 0} :=
  isOpen_rayJets hV

example {n : E3 → ℝ} {V : Set E3} (hV : IsOpen V) (hn : ContDiffOn ℝ ∞ n V) :
    ContDiffOn ℝ ∞ (Function.uncurry (opticalLagrangian n))
      {p : ℝ × (E3 × E3) | p.2.1 ∈ V ∧ p.2.2 ≠ 0} :=
  contDiffOn_opticalLagrangian hV hn

example {n : E3 → ℝ} {V : Set E3} (hV : IsOpen V) (hn : ContDiffOn ℝ ∞ n V) {γ : ℝ × ℝ → E3}
    {a b s₀ : ℝ} (hγ : IsRayFamily n V γ a b s₀) :
    HasDerivAt (fun s => opticalLength n (fun t => γ (s, t)) a b)
      (n (γ (s₀, b)) * ⟪unitTangent (fun t => γ (s₀, t)) b, deriv (fun s => γ (s, b)) s₀⟫ -
        n (γ (s₀, a)) * ⟪unitTangent (fun t => γ (s₀, t)) a, deriv (fun s => γ (s, a)) s₀⟫)
      s₀ :=
  hasDerivAt_opticalLength hV hn hγ

example {n : E3 → ℝ} {V : Set E3} (hV : IsOpen V) (hn : ContDiffOn ℝ ∞ n V) {γ : ℝ × ℝ → E3}
    {I : Set ℝ} (hIo : IsOpen I) (hIc : IsPreconnected I) {a b : ℝ}
    (hγ : ∀ ε ∈ I, IsRayFamily n V γ a b ε) {P P' : E3} (hP : ∀ ε ∈ I, γ (ε, a) = P)
    (hP' : ∀ ε ∈ I, γ (ε, b) = P') {ε₁ ε₂ : ℝ} (h₁ : ε₁ ∈ I) (h₂ : ε₂ ∈ I) :
    opticalLength n (fun t => γ (ε₁, t)) a b = opticalLength n (fun t => γ (ε₂, t)) a b :=
  opticalLength_eq hV hn hIo hIc hγ hP hP' h₁ h₂

example {N : E3 → ℝ} {V : Set E3} (hV : IsOpen V) (hN : ContDiffOn ℝ ∞ N V) {γ₁ γ₂ : ℝ × ℝ → E3}
    {a b s₀ : ℝ} (hγ₁ : IsRayFamily N V γ₁ a b s₀) (hγ₂ : IsRayFamily N V γ₂ a b s₀)
    {r r' : ℝ → E3} (hr₁ : (fun s => γ₁ (s, a)) =ᶠ[𝓝 s₀] r)
    (hr₁' : (fun s => γ₁ (s, b)) =ᶠ[𝓝 s₀] r') (hr₂ : (fun s => γ₂ (s, a)) =ᶠ[𝓝 s₀] r)
    (hr₂' : (fun s => γ₂ (s, b)) =ᶠ[𝓝 s₀] r')
    (hstig : ∀ᶠ s in 𝓝 s₀, opticalLength N (fun t => γ₁ (s, t)) a b =
      opticalLength N (fun t => γ₂ (s, t)) a b) :
    N (r' s₀) * ⟪unitTangent (fun t => γ₁ (s₀, t)) b, deriv r' s₀⟫ -
        N (r s₀) * ⟪unitTangent (fun t => γ₁ (s₀, t)) a, deriv r s₀⟫ =
      N (r' s₀) * ⟪unitTangent (fun t => γ₂ (s₀, t)) b, deriv r' s₀⟫ -
        N (r s₀) * ⟪unitTangent (fun t => γ₂ (s₀, t)) a, deriv r s₀⟫ :=
  eikonal_variation_eq hV hN hγ₁ hγ₂ hr₁ hr₁' hr₂ hr₂' hstig

example {N : E3 → ℝ} {V : Set E3} (hV : IsOpen V) (hN : ContDiffOn ℝ ∞ N V) {γ₁ γ₂ : ℝ × ℝ → E3}
    {a b s₀ : ℝ} (hγ₁ : IsRayFamily N V γ₁ a b s₀) (hγ₂ : IsRayFamily N V γ₂ a b s₀)
    {r r' : ℝ → E3} (hr₁ : (fun s => γ₁ (s, a)) =ᶠ[𝓝 s₀] r)
    (hr₁' : (fun s => γ₁ (s, b)) =ᶠ[𝓝 s₀] r') (hr₂ : (fun s => γ₂ (s, a)) =ᶠ[𝓝 s₀] r)
    (hr₂' : (fun s => γ₂ (s, b)) =ᶠ[𝓝 s₀] r')
    (hstig : ∀ᶠ s in 𝓝 s₀, opticalLength N (fun t => γ₁ (s, t)) a b =
      opticalLength N (fun t => γ₂ (s, t)) a b)
    (haxis : ⟪unitTangent (fun t => γ₂ (s₀, t)) a, deriv r s₀⟫ = 0)
    (haxis' : ⟪unitTangent (fun t => γ₂ (s₀, t)) b, deriv r' s₀⟫ = 0) {n n' : ℝ}
    (hn : N (r s₀) = n) (hn' : N (r' s₀) = n') :
    n * ⟪unitTangent (fun t => γ₁ (s₀, t)) a, deriv r s₀⟫ =
      n' * ⟪unitTangent (fun t => γ₁ (s₀, t)) b, deriv r' s₀⟫ :=
  sine_condition hV hN hγ₁ hγ₂ hr₁ hr₁' hr₂ hr₂' hstig haxis haxis' hn hn'

example {n₀ : ℝ} {P w : E3} (hw : w ≠ 0) {h h' : ℝ → ℝ} (hh : ∀ t, HasDerivAt h (h' t) t)
    (hh' : Continuous h') {a b : ℝ} (hpos : ∀ t ∈ uIcc a b, 0 < h' t) :
    IsRay (fun _ => n₀) (fun t => P + h t • w) a b :=
  isRay_const hw hh hh' hpos

example (P P' : E3) (p : ℝ × ℝ) :
    E3 :=
  segmentFamily P P' p

example (ε t : ℝ) :
    HasDerivAt (fun t => t + ε * (t * (1 - t))) (1 + ε * (1 - 2 * t)) t :=
  hasDerivAt_segmentParam ε t

example {ε t : ℝ} (hε : ε ∈ Ioo (-1 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < 1 + ε * (1 - 2 * t) :=
  segmentParam_speed_pos hε ht

example (P P' : E3) {ε t : ℝ} (hε : ε ∈ Ioo (-1 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    unitTangent (fun t => segmentFamily P P' (ε, t)) t = ‖P' - P‖⁻¹ • (P' - P) :=
  unitTangent_segmentFamily P P' hε ht

example (n₀ : ℝ) {P P' : E3} (hPP' : P ≠ P') {ε : ℝ} (hε : ε ∈ Ioo (-1 : ℝ) 1) :
    IsRayFamily (fun _ => n₀) univ (segmentFamily P P') 0 1 ε :=
  isRayFamily_segmentFamily n₀ hPP' hε

example (P P' : E3) (ε : ℝ) :
    segmentFamily P P' (ε, 0) = P :=
  segmentFamily_zero P P' ε

example (P P' : E3) (ε : ℝ) :
    segmentFamily P P' (ε, 1) = P' :=
  segmentFamily_one P P' ε

example (n₀ : ℝ) {P P' : E3} (hPP' : P ≠ P') {ε₁ ε₂ : ℝ} (h₁ : ε₁ ∈ Ioo (-1 : ℝ) 1)
    (h₂ : ε₂ ∈ Ioo (-1 : ℝ) 1) :
    opticalLength (fun _ => n₀) (fun t => segmentFamily P P' (ε₁, t)) 0 1 =
      opticalLength (fun _ => n₀) (fun t => segmentFamily P P' (ε₂, t)) 0 1 :=
  opticalLength_segmentFamily n₀ hPP' h₁ h₂

example (d e : E3) (ε : ℝ) (p : ℝ × ℝ) :
    E3 :=
  shiftedSegmentFamily d e ε p

example (n₀ : ℝ) {d : E3} (hd : d ≠ 0) (e : E3) {ε : ℝ} (hε : ε ∈ Ioo (-1 : ℝ) 1) (s₀ : ℝ) :
    IsRayFamily (fun _ => n₀) univ (shiftedSegmentFamily d e ε) 0 1 s₀ :=
  isRayFamily_shiftedSegmentFamily n₀ hd e hε s₀

example (n₀ : ℝ) {d e : E3} (hd : d ≠ 0) (hde : ⟪d, e⟫ = 0) (s₀ : ℝ) :
    n₀ * ⟪unitTangent (fun t => shiftedSegmentFamily d e (1 / 2) (s₀, t)) 0,
        deriv (fun s : ℝ => s • e) s₀⟫ =
      n₀ * ⟪unitTangent (fun t => shiftedSegmentFamily d e (1 / 2) (s₀, t)) 1,
        deriv (fun s : ℝ => s • e + d) s₀⟫ :=
  sine_condition_shiftedSegment n₀ hd hde s₀

end Rays

section Absolute

example {N : E3 → ℝ} (hN : Continuous N) {φ : E3 → E3} {ψ : E3 → ℝ} {σ : ℝ → E3} {τ : ℝ → ℝ}
    {x v : E3} (hσ : ContDiff ℝ 1 σ) (h0 : σ 0 = x) (hv : deriv σ 0 = v)
    (hτ : DifferentiableAt ℝ τ 0) (him : ∀ᶠ s in 𝓝 0, σ (τ s) = φ (σ s))
    (heik : ∀ᶠ s in 𝓝 0, opticalLength N σ s (τ s) = ψ (σ s)) (hφ : DifferentiableAt ℝ φ x)
    (hψ : DifferentiableAt ℝ ψ x) :
    fderiv ℝ ψ x v = N (φ x) * (‖deriv σ (τ 0)‖ * deriv τ 0) - N x * ‖v‖ ∧
      ‖fderiv ℝ φ x v‖ = |‖deriv σ (τ 0)‖ * deriv τ 0| :=
  fderiv_eikonal_of_carries hN hσ h0 hv hτ him heik hφ hψ

example {N : E3 → ℝ} {n n' : ℝ} {Ω : Set E3} {φ : E3 → E3} {ψ : E3 → ℝ}
    (hI : IsAbsoluteInstrument N n n' Ω φ ψ) (hN : Continuous N) (hn : 0 < n) (hn' : 0 < n')
    {x : E3} (hx : x ∈ Ω) (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ x) (v : E3) :
    n' * ‖fderiv ℝ φ x v‖ = n * ‖v‖ ∧ fderiv ℝ ψ x v = 0 :=
  IsAbsoluteInstrument.norm_fderiv_eq_and_fderiv_eikonal hI hN hn hn' hx hφ hψ v

example {N : E3 → ℝ} {n n' : ℝ} {Ω : Set E3} {φ : E3 → E3} {ψ : E3 → ℝ}
    (hI : IsAbsoluteInstrument N n n' Ω φ ψ) (hN : Continuous N) (hn : 0 < n) (hn' : 0 < n')
    {x : E3} (hx : x ∈ Ω) (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ x) (v : E3) :
    n' * ‖fderiv ℝ φ x v‖ = n * ‖v‖ :=
  IsAbsoluteInstrument.norm_fderiv_eq hI hN hn hn' hx hφ hψ v

example {N : E3 → ℝ} {n n' : ℝ} {Ω : Set E3} {φ : E3 → E3} {ψ : E3 → ℝ}
    (hI : IsAbsoluteInstrument N n n' Ω φ ψ) (hN : Continuous N) (hn : 0 < n) (hn' : 0 < n')
    {x : E3} (hx : x ∈ Ω) (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ x) :
    fderiv ℝ ψ x = 0 :=
  IsAbsoluteInstrument.fderiv_eikonal_eq_zero hI hN hn hn' hx hφ hψ

example {N : E3 → ℝ} {n n' : ℝ} {Ω : Set E3} {φ : E3 → E3} {ψ : E3 → ℝ}
    (hI : IsAbsoluteInstrument N n n' Ω φ ψ) (hN : Continuous N) (hn : 0 < n) (hn' : 0 < n')
    (hφ : ∀ x ∈ Ω, DifferentiableAt ℝ φ x) (hψ : ∀ x ∈ Ω, DifferentiableAt ℝ ψ x) {c : ℝ → E3}
    {a b : ℝ} (hcΩ : ∀ t ∈ uIcc a b, c t ∈ Ω) (hc : ∀ t ∈ uIcc a b, DifferentiableAt ℝ c t) :
    opticalLength N (φ ∘ c) a b = opticalLength N c a b :=
  IsAbsoluteInstrument.opticalLength_curve_eq hI hN hn hn' hφ hψ hcΩ hc

example {N : E3 → ℝ} {n n' : ℝ} {Ω : Set E3} {φ : E3 → E3} {ψ : E3 → ℝ}
    (hI : IsAbsoluteInstrument N n n' Ω φ ψ) (hN : Continuous N) (hn : 0 < n) (hn' : 0 < n')
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hφ : ContDiffOn ℝ 2 φ Ω)
    (hψ : ∀ x ∈ Ω, DifferentiableAt ℝ ψ x) :
    ∃ (L : E3 ≃ₗᵢ[ℝ] E3) (c : E3), ∀ x ∈ Ω, φ x = (n / n') • L x + c :=
  IsAbsoluteInstrument.isSimilarity hI hN hn hn' hΩ hΩc hφ hψ

example (n₀ : ℝ) (Ω : Set E3) :
    IsAbsoluteInstrument (fun _ => n₀) n₀ n₀ Ω id fun _ => 0 :=
  isAbsoluteInstrument_id n₀ Ω

end Absolute

end ProjectAinos.Electrodynamics.Optics.Imaging

end Imaging

section Riccati

open Set Filter ContinuousLinearMap

open scoped Topology NNReal

namespace ProjectAinos.SmoothGeometry.Riccati

open LinearODE

section Linear

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

example {A : ℝ → F →L[ℝ] F} {a b C : ℝ} (hA : ∀ t ∈ uIcc a b, ‖A t‖ ≤ C) {w : ℝ → F}
    (hw : ∀ t ∈ uIcc a b, HasDerivAt w (A t (w t)) t) (ha : w a = 0) :
    EqOn w 0 (uIcc a b) :=
  eqOn_zero_of_hasDerivAt hA hw ha

end Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

example (H₀ : E →L[ℝ] E) (s : ℝ) :
    E →L[ℝ] E :=
  solution H₀ s

example (H₀ : E →L[ℝ] E) :
    solution H₀ 0 = H₀ :=
  solution_zero H₀

example {H : ℝ → E →L[ℝ] E} {H₀ : E →L[ℝ] E} {l : ℝ}
    (hH : ∀ s ∈ uIcc 0 l, HasDerivAt H (-(H s * H s)) s) (h0 : H 0 = H₀) :
    (1 + l • H₀) * H l = H₀ ∧ H l * (1 + l • H₀) = H₀ :=
  one_add_smul_mul_eq hH h0

example {H : ℝ → E →L[ℝ] E} {H₀ : E →L[ℝ] E} {l : ℝ}
    (hH : ∀ s ∈ uIcc 0 l, HasDerivAt H (-(H s * H s)) s) (h0 : H 0 = H₀) :
    IsUnit (1 + l • H₀) ∧ Ring.inverse (1 + l • H₀) = 1 - l • H l :=
  isUnit_one_add_smul hH h0

example {H : ℝ → E →L[ℝ] E} {H₀ : E →L[ℝ] E} {l : ℝ}
    (hH : ∀ s ∈ uIcc 0 l, HasDerivAt H (-(H s * H s)) s) (h0 : H 0 = H₀) :
    H l = H₀ * Ring.inverse (1 + l • H₀) :=
  matrix_eq_of_hasDerivAt hH h0

example [CompleteSpace E] (H₀ : E →L[ℝ] E) {s : ℝ} (hs : IsUnit (1 + s • H₀)) :
    HasDerivAt (solution H₀) (-(solution H₀ s * solution H₀ s)) s :=
  hasDerivAt_solution H₀ hs

section FiniteDimensional

variable [FiniteDimensional ℝ E]

example (C : E →L[ℝ] E) :
    HasDerivAt (fun r : ℝ => LinearMap.det ((1 + r • C : E →L[ℝ] E) : E →ₗ[ℝ] E))
      (traceCLM C) 0 :=
  hasDerivAt_det_one_add_smul_zero C

example {A : E →L[ℝ] E} (hA : IsUnit A) :
    LinearMap.det (A : E →ₗ[ℝ] E) ≠ 0 :=
  det_ne_zero_of_isUnit hA

example (H₀ : E →L[ℝ] E) {s : ℝ} (hs : IsUnit (1 + s • H₀)) :
    HasDerivAt (fun r : ℝ => LinearMap.det ((1 + r • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E))
      (LinearMap.det ((1 + s • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E) * traceCLM (solution H₀ s)) s :=
  hasDerivAt_det_one_add_smul H₀ hs

example (H₀ : E →L[ℝ] E) {s : ℝ} (hs : IsUnit (1 + s • H₀)) :
    HasDerivAt (fun r : ℝ => Real.log (LinearMap.det ((1 + r • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E)))
      (traceCLM (solution H₀ s)) s :=
  hasDerivAt_log_det_solution H₀ hs

example {H : ℝ → E →L[ℝ] E} {H₀ : E →L[ℝ] E} {l : ℝ}
    (hH : ∀ s ∈ uIcc 0 l, HasDerivAt H (-(H s * H s)) s) (h0 : H 0 = H₀) :
    HasDerivAt (fun r : ℝ => Real.log (LinearMap.det ((1 + r • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E)))
      (traceCLM (H l)) l :=
  hasDerivAt_log_det hH h0

example (H₀ : E →L[ℝ] E) :
    Continuous fun r : ℝ => LinearMap.det ((1 + r • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E) :=
  continuous_det_one_add_smul H₀

example {H : ℝ → E →L[ℝ] E} {H₀ : E →L[ℝ] E} {l : ℝ}
    (hH : ∀ s ∈ uIcc 0 l, HasDerivAt H (-(H s * H s)) s) (h0 : H 0 = H₀) :
    ∀ s ∈ uIcc 0 l, 0 < LinearMap.det ((1 + s • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E) :=
  det_pos hH h0

example {H : ℝ → E →L[ℝ] E} {H₀ : E →L[ℝ] E} {l : ℝ}
    (hH : ∀ s ∈ uIcc 0 l, HasDerivAt H (-(H s * H s)) s) (h0 : H 0 = H₀) {α : ℝ → ℝ}
    (hα : ∀ s ∈ uIcc 0 l, HasDerivAt α (-(α s * traceCLM (H s)) / 2) s) :
    α l = α 0 / Real.sqrt (LinearMap.det ((1 + l • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E)) :=
  eq_div_sqrt_det hH h0 hα

example {H₀ : E →L[ℝ] E} {l₀ : ℝ} (hl₀ : 0 < l₀) {α : ℝ → ℝ}
    (hα : ∀ s ∈ Ico 0 l₀,
      α s = α 0 / Real.sqrt (LinearMap.det ((1 + s • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E)))
    (hpos : ∀ s ∈ Ico 0 l₀, 0 < LinearMap.det ((1 + s • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E))
    (hdet : LinearMap.det ((1 + l₀ • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E) = 0) (h0 : α 0 ≠ 0) :
    Tendsto (fun s => |α s|) (𝓝[<] l₀) atTop :=
  tendsto_abs_div_sqrt_det hl₀ hα hpos hdet h0

end FiniteDimensional

end ProjectAinos.SmoothGeometry.Riccati

namespace ProjectAinos.SmoothGeometry.NonlinearODE

example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {Φ : ℝ × F → F} {Ω : Set (ℝ × F)} (hΩ : IsOpen Ω) (hΦ : ∀ p ∈ Ω, ContDiffAt ℝ 2 Φ p)
    {K : Set ℝ} (hK : IsCompact K) {z₀ : F} (hKz : ∀ t ∈ K, (t, z₀) ∈ Ω) :
    ∃ δ > 0, ∃ C : ℝ, ∀ t ∈ K, ∀ w : F, ‖w‖ ≤ δ →
      ‖Φ (t, z₀ + w) - Φ (t, z₀) - fderiv ℝ (fun y => Φ (t, y)) z₀ w‖ ≤ C * ‖w‖ ^ 2 :=
  exists_norm_sub_sub_fderiv_le hΩ hΦ hK hKz

end ProjectAinos.SmoothGeometry.NonlinearODE

end Riccati

section NarrowBundle

open Set Filter ContinuousLinearMap InnerProductSpace

open scoped Topology Gradient RealInnerProductSpace ContDiff Laplacian

namespace ProjectAinos.Electrodynamics.Optics.NarrowBundle

open SmoothGeometry LinearODE NonlinearODE

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (ψ : E3 → ℝ) (x : E3) :
    E3 →L[ℝ] E3 :=
  hessian ψ x

example (ψ : E3 → ℝ) (x₀ : E3) (l : ℝ) :
    E3 :=
  ray ψ x₀ l

variable {ψ : E3 → ℝ} {U : Set E3}

example (ψ : E3 → ℝ) (x₀ : E3) :
    ray ψ x₀ 0 = x₀ :=
  ray_zero ψ x₀

example (ψ : E3 → ℝ) (x₀ : E3) (l : ℝ) :
    HasDerivAt (ray ψ x₀) (∇ ψ x₀) l :=
  hasDerivAt_ray ψ x₀ l

example (ψ : E3 → ℝ) (x₀ : E3) :
    Continuous (ray ψ x₀) :=
  continuous_ray ψ x₀

example (ψ : E3 → ℝ) :
    fderiv ℝ ψ = fun x => innerSL ℝ (∇ ψ x) :=
  fderiv_eq_innerSL_gradient ψ

example {m n : WithTop ℕ∞} {x : E3} (hψ : ContDiffAt ℝ n ψ x) (hmn : m + 1 ≤ n) :
    ContDiffAt ℝ m (∇ ψ) x :=
  contDiffAt_gradient hψ hmn

example {m n : WithTop ℕ∞} (hψ : ContDiff ℝ n ψ) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (∇ ψ) :=
  contDiff_gradient hψ hmn

example {m n : WithTop ℕ∞} (hU : IsOpen U) (hψ : ContDiffOn ℝ n ψ U) (hmn : m + 1 ≤ n) :
    ContDiffOn ℝ m (∇ ψ) U :=
  contDiffOn_gradient hU hψ hmn

example {x : E3} (hψ : ContDiffAt ℝ 2 ψ x) :
    DifferentiableAt ℝ (∇ ψ) x :=
  differentiableAt_gradient hψ

example {x : E3} (hx : DifferentiableAt ℝ (∇ ψ) x) (u v : E3) :
    fderiv ℝ (fderiv ℝ ψ) x u v = ⟪hessian ψ x u, v⟫ :=
  fderiv_fderiv_apply hx u v

example {x : E3} (hψ : ContDiffAt ℝ 2 ψ x) (u v : E3) :
    ⟪hessian ψ x u, v⟫ = ⟪u, hessian ψ x v⟫ :=
  inner_hessian_comm hψ u v

example {x : E3} (hψ : ContDiffAt ℝ 2 ψ x) :
    Δ ψ x = traceCLM (hessian ψ x) :=
  laplacian_eq_traceCLM_hessian hψ

example (hU : IsOpen U) (hψ : ContDiffOn ℝ 2 ψ U) (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x : E3}
    (hx : x ∈ U) (v : E3) :
    ⟪∇ ψ x, hessian ψ x v⟫ = 0 :=
  inner_gradient_hessian_eq_zero hU hψ heik hx v

example (hU : IsOpen U) (hψ : ContDiffOn ℝ 2 ψ U) (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x : E3}
    (hx : x ∈ U) :
    hessian ψ x (∇ ψ x) = 0 :=
  hessian_apply_gradient hU hψ heik hx

example (hU : IsOpen U) (hψ : ContDiffOn ℝ 3 ψ U) (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x : E3}
    (hx : x ∈ U) :
    fderiv ℝ (hessian ψ) x (∇ ψ x) = -(hessian ψ x * hessian ψ x) :=
  fderiv_hessian_apply_gradient hU hψ heik hx

example (hU : IsOpen U) (hψ : ContDiffOn ℝ 2 ψ U) (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x₀ : E3}
    {l : ℝ} (hseg : ∀ s ∈ uIcc 0 l, ray ψ x₀ s ∈ U) :
    ∇ ψ (ray ψ x₀ l) = ∇ ψ x₀ :=
  gradient_ray hU hψ heik hseg

example (hU : IsOpen U) (hψ : ContDiffOn ℝ 3 ψ U) (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x₀ : E3}
    {l : ℝ} (hseg : ∀ s ∈ uIcc 0 l, ray ψ x₀ s ∈ U) :
    HasDerivAt (fun s => hessian ψ (ray ψ x₀ s))
      (-(hessian ψ (ray ψ x₀ l) * hessian ψ (ray ψ x₀ l))) l :=
  hessian_hasDerivAt hU hψ heik hseg

example (hU : IsOpen U) (hψ : ContDiffOn ℝ 3 ψ U) (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x₀ : E3}
    {l : ℝ} (hseg : ∀ s ∈ uIcc 0 l, ray ψ x₀ s ∈ U) :
    ∀ s ∈ uIcc 0 l, HasDerivAt (fun r => hessian ψ (ray ψ x₀ r))
      (-(hessian ψ (ray ψ x₀ s) * hessian ψ (ray ψ x₀ s))) s :=
  hessian_hasDerivAt_of_mem hU hψ heik hseg

example (hU : IsOpen U) (hψ : ContDiffOn ℝ 3 ψ U) (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x₀ : E3}
    {l : ℝ} (hseg : ∀ s ∈ uIcc 0 l, ray ψ x₀ s ∈ U) :
    hessian ψ (ray ψ x₀ l) = hessian ψ x₀ * Ring.inverse (1 + l • hessian ψ x₀) :=
  hessian_ray hU hψ heik hseg

example (hU : IsOpen U) (hψ : ContDiffOn ℝ 3 ψ U) (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x₀ : E3}
    {l : ℝ} (hseg : ∀ s ∈ uIcc 0 l, ray ψ x₀ s ∈ U) :
    IsUnit (1 + l • hessian ψ x₀) :=
  isUnit_one_add_smul_hessian hU hψ heik hseg

example (hU : IsOpen U) (hψ : ContDiffOn ℝ 3 ψ U) (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x₀ : E3}
    {l : ℝ} (hseg : ∀ s ∈ uIcc 0 l, ray ψ x₀ s ∈ U) {R : ℝ} (hR : R ≠ 0) {v : E3}
    (hv : hessian ψ x₀ v = R⁻¹ • v) :
    hessian ψ (ray ψ x₀ l) v = (R + l)⁻¹ • v :=
  principalRadius_add hU hψ heik hseg hR hv

example (hU : IsOpen U) (hψ : ContDiffOn ℝ 2 ψ U) (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x₀ : E3}
    (hx₀ : x₀ ∈ U) (l : ℝ) :
    LinearMap.det ((1 + l • hessian ψ x₀ : E3 →L[ℝ] E3) : E3 →ₗ[ℝ] E3) = 0 ↔
      ∃ R : ℝ, R ≠ 0 ∧ l = -R ∧
        ∃ v : E3, v ≠ 0 ∧ ⟪v, ∇ ψ x₀⟫ = 0 ∧ hessian ψ x₀ v = R⁻¹ • v :=
  focal_iff hU hψ heik hx₀ l

example (hU : IsOpen U) (hψ : ContDiffOn ℝ 3 ψ U) (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x₀ : E3}
    {l : ℝ} (hdet : LinearMap.det ((1 + l • hessian ψ x₀ : E3 →L[ℝ] E3) : E3 →ₗ[ℝ] E3) = 0) :
    ∃ s ∈ uIcc 0 l, ray ψ x₀ s ∉ U :=
  exists_not_mem_of_det_eq_zero hU hψ heik hdet

example (hU : IsOpen U) (hψ : ContDiffOn ℝ 3 ψ U) (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x₀ : E3}
    {l : ℝ} (hseg : ∀ s ∈ uIcc 0 l, ray ψ x₀ s ∈ U) {α : ℝ → ℝ}
    (hα : ∀ s ∈ uIcc 0 l, HasDerivAt α (-(α s * Δ ψ (ray ψ x₀ s)) / 2) s) :
    α l = α 0 /
      Real.sqrt (LinearMap.det ((1 + l • hessian ψ x₀ : E3 →L[ℝ] E3) : E3 →ₗ[ℝ] E3)) :=
  amplitude_eq hU hψ heik hseg hα

example (hU : IsOpen U) (hψ : ContDiffOn ℝ 2 ψ U) (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x₀ : E3}
    {l : ℝ} (hseg : ∀ s ∈ uIcc 0 l, ray ψ x₀ s ∈ U) {a : E3 → ℝ}
    (ha : DifferentiableAt ℝ a (ray ψ x₀ l)) :
    HasDerivAt (fun s => a (ray ψ x₀ s)) ⟪∇ a (ray ψ x₀ l), ∇ ψ (ray ψ x₀ l)⟫ l :=
  hasDerivAt_comp_ray hU hψ heik hseg ha

example (hU : IsOpen U) (hψ : ContDiffOn ℝ 3 ψ U) (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x₀ : E3}
    {l : ℝ} (hseg : ∀ s ∈ uIcc 0 l, ray ψ x₀ s ∈ U) {a : E3 → ℝ}
    (ha : ∀ x ∈ U, DifferentiableAt ℝ a x) (htr : ∀ x ∈ U, 2 * ⟪∇ a x, ∇ ψ x⟫ + a x * Δ ψ x = 0) :
    a (ray ψ x₀ l) = a x₀ /
      Real.sqrt (LinearMap.det ((1 + l • hessian ψ x₀ : E3 →L[ℝ] E3) : E3 →ₗ[ℝ] E3)) :=
  amplitude_ray hU hψ heik hseg ha htr

example (hU : IsOpen U) (hψ : ContDiffOn ℝ 3 ψ U) (heik : ∀ x ∈ U, ‖∇ ψ x‖ ^ 2 = 1) {x₀ : E3}
    {l₀ : ℝ} (hl₀ : 0 < l₀) (hseg : ∀ s ∈ Ico 0 l₀, ray ψ x₀ s ∈ U) {a : E3 → ℝ}
    (ha : ∀ x ∈ U, DifferentiableAt ℝ a x) (htr : ∀ x ∈ U, 2 * ⟪∇ a x, ∇ ψ x⟫ + a x * Δ ψ x = 0)
    (hdet : LinearMap.det ((1 + l₀ • hessian ψ x₀ : E3 →L[ℝ] E3) : E3 →ₗ[ℝ] E3) = 0)
    (h0 : a x₀ ≠ 0) :
    Tendsto (fun s => |a (ray ψ x₀ s)|) (𝓝[<] l₀) atTop :=
  amplitude_tendsto_focal hU hψ heik hl₀ hseg ha htr hdet h0

example (n : E3 → ℝ) (z : E3 × E3) :
    E3 × E3 :=
  rayField n z

example {n : E3 → ℝ} (hn : ContDiff ℝ ∞ n) :
    ContDiff ℝ ∞ (rayField n) :=
  contDiff_rayField hn

example (n : E3 → ℝ) (t : ℝ) (z : E3 × E3) :
    E3 × E3 →L[ℝ] E3 × E3 :=
  transverseMap n t z

example {n : E3 → ℝ} (hn : ContDiff ℝ ∞ n) (z : E3 × E3) :
    transverseMap n 0 z = ContinuousLinearMap.id ℝ (E3 × E3) :=
  transverseMap_zero hn z

example {n : E3 → ℝ} (hn : ContDiff ℝ ∞ n) {t : ℝ} {z : E3 × E3}
    (h : (t, z) ∈ flowDomain (rayField n)) :
    HasDerivAt (fun s => transverseMap n s z)
      (fderiv ℝ (rayField n) (flow (rayField n) (t, z)) ∘L transverseMap n t z) t :=
  transverseMap_hasDerivAt hn h

example {n : E3 → ℝ} (hn : ContDiff ℝ ∞ n) (z w : E3 × E3) :
    fderiv ℝ (rayField n) z w = (w.2, fderiv ℝ (∇ fun q => n q ^ 2 / 2) z.1 w.1) :=
  fderiv_rayField_apply hn z w

example {n : E3 → ℝ} (hn : ContDiff ℝ ∞ n) {K : Set ℝ} (hK : IsCompact K) {z₀ : E3 × E3}
    (hKz : ∀ t ∈ K, (t, z₀) ∈ flowDomain (rayField n)) :
    ∃ δ > 0, ∃ C : ℝ, ∀ t ∈ K, ∀ w : E3 × E3, ‖w‖ ≤ δ →
      ‖flow (rayField n) (t, z₀ + w) - flow (rayField n) (t, z₀) - transverseMap n t z₀ w‖ ≤
        C * ‖w‖ ^ 2 :=
  norm_beam_sub_linear_le hn hK hKz

example (n₀ : ℝ) :
    rayField (fun _ : E3 => n₀) = fun z => (z.2, 0) :=
  rayField_const n₀

example (n₀ : ℝ) :
    ContDiff ℝ 1 (rayField fun _ : E3 => n₀) :=
  contDiff_rayField_const n₀

example (n₀ t : ℝ) (z : E3 × E3) :
    flow (rayField fun _ : E3 => n₀) (t, z) = (z.1 + t • z.2, z.2) :=
  flow_rayField_const n₀ t z

example (n₀ : ℝ) :
    flowDomain (rayField fun _ : E3 => n₀) = univ :=
  flowDomain_rayField_const n₀

example (n₀ t : ℝ) (z w : E3 × E3) :
    transverseMap (fun _ : E3 => n₀) t z w = (w.1 + t • w.2, w.2) :=
  transverseMap_const n₀ t z w

example (n₀ t : ℝ) (z₀ w : E3 × E3) :
    flow (rayField fun _ : E3 => n₀) (t, z₀ + w) - flow (rayField fun _ : E3 => n₀) (t, z₀) -
      transverseMap (fun _ : E3 => n₀) t z₀ w = 0 :=
  beam_sub_linear_const n₀ t z₀ w

example (u w : E3) :
    ∃ v : E3, v ≠ 0 ∧ ⟪u, v⟫ = 0 ∧ ⟪w, v⟫ = 0 :=
  exists_ne_zero_inner_eq_zero u w

example (P : E3 →L[ℝ] E3) (c x : E3) :
    ℝ :=
  convergingFront P c x

variable {P : E3 →L[ℝ] E3} {c : E3}

example (P : E3 →L[ℝ] E3) (c : E3) :
    IsOpen {x : E3 | P (x - c) ≠ 0} :=
  isOpen_frontDomain P c

example (P : E3 →L[ℝ] E3) (c : E3) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (convergingFront P c) {x | P (x - c) ≠ 0} :=
  contDiffOn_convergingFront P c

example (P : E3 →L[ℝ] E3) (c x : E3) :
    HasFDerivAt (fun y => P (y - c)) P x :=
  hasFDerivAt_sub_apply P c x

example {x : E3} (hx : P (x - c) ≠ 0) :
    HasFDerivAt (convergingFront P c)
      (-((‖P (x - c)‖⁻¹ • innerSL ℝ (P (x - c))).comp P)) x :=
  hasFDerivAt_convergingFront hx

example (hP : ∀ u v, ⟪P u, v⟫ = ⟪P u, P v⟫) {x : E3} (hx : P (x - c) ≠ 0) :
    ∇ (convergingFront P c) x = -‖P (x - c)‖⁻¹ • P (x - c) :=
  gradient_convergingFront hP hx

example (hP : ∀ u v, ⟪P u, v⟫ = ⟪P u, P v⟫) {x : E3} (hx : P (x - c) ≠ 0) :
    ‖∇ (convergingFront P c) x‖ ^ 2 = 1 :=
  eikonal_convergingFront hP hx

example (hP : ∀ u v, ⟪P u, v⟫ = ⟪P u, P v⟫) {x : E3} (hx : P (x - c) ≠ 0) (v : E3) :
    hessian (convergingFront P c) x v =
      -‖P (x - c)‖⁻¹ • (P v - (‖P (x - c)‖⁻¹ ^ 2 * ⟪P (x - c), v⟫) • P (x - c)) :=
  hessian_convergingFront_apply hP hx v

example (hP : ∀ u v, ⟪P u, v⟫ = ⟪P u, P v⟫) (u : E3) :
    P (P u) = P u :=
  apply_apply_of_inner hP u

example (hP : ∀ u v, ⟪P u, v⟫ = ⟪P u, P v⟫) {x₀ : E3} (hx₀ : P (x₀ - c) ≠ 0)
    (hex : ∃ v : E3, v ≠ 0 ∧ P v = v ∧ ⟪P (x₀ - c), v⟫ = 0) (l : ℝ) :
    LinearMap.det
        ((1 + l • hessian (convergingFront P c) x₀ : E3 →L[ℝ] E3) : E3 →ₗ[ℝ] E3) = 0 ↔
      l = ‖P (x₀ - c)‖ :=
  focal_convergingFront_iff hP hx₀ hex l

example (hP : ∀ u v, ⟪P u, v⟫ = ⟪P u, P v⟫) {x₀ : E3} (hx₀ : P (x₀ - c) ≠ 0) :
    P (ray (convergingFront P c) x₀ ‖P (x₀ - c)‖ - c) = 0 :=
  apply_ray_convergingFront hP hx₀

example (c x : E3) :
    convergingFront (ContinuousLinearMap.id ℝ E3) c x = -‖x - c‖ :=
  convergingFront_id_apply c x

example {x₀ : E3} (hx₀ : x₀ ≠ c) {v : E3} (hv : ⟪x₀ - c, v⟫ = 0) :
    hessian (convergingFront (ContinuousLinearMap.id ℝ E3) c) x₀ v = (-‖x₀ - c‖)⁻¹ • v :=
  hessian_sphericalFront_apply hx₀ hv

example {x₀ : E3} (hx₀ : x₀ ≠ c) (l : ℝ) :
    LinearMap.det ((1 + l • hessian (convergingFront (ContinuousLinearMap.id ℝ E3) c) x₀ :
        E3 →L[ℝ] E3) : E3 →ₗ[ℝ] E3) = 0 ↔ l = ‖x₀ - c‖ :=
  focal_sphericalFront_iff hx₀ l

example {x₀ : E3} (hx₀ : x₀ ≠ c) :
    ray (convergingFront (ContinuousLinearMap.id ℝ E3) c) x₀ ‖x₀ - c‖ = c :=
  ray_sphericalFront hx₀

example {x₀ : E3} (hx₀ : x₀ ≠ c) (s : ℝ) :
    ray (convergingFront (ContinuousLinearMap.id ℝ E3) c) x₀ s - c =
      (1 - s * ‖x₀ - c‖⁻¹) • (x₀ - c) :=
  sub_ray_sphericalFront hx₀ s

example {x₀ : E3} (hx₀ : x₀ ≠ c) {s : ℝ} (hs : s ≠ ‖x₀ - c‖) :
    ray (convergingFront (ContinuousLinearMap.id ℝ E3) c) x₀ s ∈
      {x : E3 | ContinuousLinearMap.id ℝ E3 (x - c) ≠ 0} :=
  ray_mem_sphericalFront hx₀ hs

example {x₀ : E3} (hx₀ : x₀ ≠ c) {l : ℝ} (hl : l < ‖x₀ - c‖) {v : E3} (hv : ⟪x₀ - c, v⟫ = 0) :
    hessian (convergingFront (ContinuousLinearMap.id ℝ E3) c)
        (ray (convergingFront (ContinuousLinearMap.id ℝ E3) c) x₀ l) v =
      (-‖x₀ - c‖ + l)⁻¹ • v :=
  principalRadius_sphericalFront hx₀ hl hv

example (e : E3) :
    E3 →L[ℝ] E3 :=
  axisProj e

example (e v : E3) :
    axisProj e v = v - ⟪e, v⟫ • e :=
  axisProj_apply e v

example {e : E3} (he : ‖e‖ = 1) (u : E3) :
    ⟪axisProj e u, e⟫ = 0 :=
  inner_axisProj_self he u

example {e : E3} (he : ‖e‖ = 1) (u v : E3) :
    ⟪axisProj e u, v⟫ = ⟪axisProj e u, axisProj e v⟫ :=
  inner_axisProj he u v

example {e : E3} (he : ‖e‖ = 1) {x₀ : E3} (hx₀ : axisProj e (x₀ - c) ≠ 0) :
    hessian (convergingFront (axisProj e) c) x₀ e = 0 ∧
      ⟪e, ∇ (convergingFront (axisProj e) c) x₀⟫ = 0 :=
  hessian_cylindricalFront_axis he hx₀

example {e : E3} (he : ‖e‖ = 1) {x₀ : E3} (hx₀ : axisProj e (x₀ - c) ≠ 0) {v : E3}
    (hve : ⟪e, v⟫ = 0) (hv : ⟪axisProj e (x₀ - c), v⟫ = 0) :
    hessian (convergingFront (axisProj e) c) x₀ v = (-‖axisProj e (x₀ - c)‖)⁻¹ • v :=
  hessian_cylindricalFront_apply he hx₀ hve hv

example {e : E3} (he : ‖e‖ = 1) {x₀ : E3} (hx₀ : axisProj e (x₀ - c) ≠ 0) (l : ℝ) :
    LinearMap.det ((1 + l • hessian (convergingFront (axisProj e) c) x₀ :
        E3 →L[ℝ] E3) : E3 →ₗ[ℝ] E3) = 0 ↔ l = ‖axisProj e (x₀ - c)‖ :=
  focal_cylindricalFront_iff he hx₀ l

example (hP : ∀ u v, ⟪P u, v⟫ = ⟪P u, P v⟫) {x : E3} (hx : P (x - c) ≠ 0) :
    traceCLM (hessian (convergingFront P c) x) = -‖P (x - c)‖⁻¹ * (traceCLM P - 1) :=
  traceCLM_hessian_convergingFront hP hx

example :
    traceCLM (ContinuousLinearMap.id ℝ E3) = 3 :=
  traceCLM_id

example {x : E3} (hx : x ≠ c) :
    Δ (convergingFront (ContinuousLinearMap.id ℝ E3) c) x = -2 * ‖x - c‖⁻¹ :=
  laplacian_sphericalFront hx

example {x : E3} (hx : x ≠ c) :
    HasFDerivAt (fun y => ‖y - c‖⁻¹)
      ((-(‖x - c‖ ^ 2)⁻¹) • (‖x - c‖⁻¹ • innerSL ℝ (x - c))) x :=
  hasFDerivAt_inv_norm_sub hx

example {x : E3} (hx : x ≠ c) :
    2 * ⟪∇ (fun y => ‖y - c‖⁻¹) x, ∇ (convergingFront (ContinuousLinearMap.id ℝ E3) c) x⟫ +
      ‖x - c‖⁻¹ * Δ (convergingFront (ContinuousLinearMap.id ℝ E3) c) x = 0 :=
  transport_sphericalFront hx

example {x₀ : E3} (hx₀ : x₀ ≠ c) :
    Tendsto (fun s => |‖ray (convergingFront (ContinuousLinearMap.id ℝ E3) c) x₀ s - c‖⁻¹|)
      (𝓝[<] ‖x₀ - c‖) atTop :=
  amplitude_tendsto_sphericalFront hx₀

end ProjectAinos.Electrodynamics.Optics.NarrowBundle

end NarrowBundle

section AngularEikonal

namespace ProjectAinos.Electrodynamics.Optics.AngularEikonal

open InnerProductSpace ContinuousLinearMap Set Filter

open scoped Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

example :
    ((E × E) →L[ℝ] ℝ) →L[ℝ] E :=
  firstVector

example :
    ((E × E) →L[ℝ] ℝ) →L[ℝ] E :=
  secondVector

example (φ : (E × E) →L[ℝ] ℝ) (a : E) :
    ⟪firstVector φ, a⟫ = φ (a, 0) :=
  inner_firstVector φ a

example (φ : (E × E) →L[ℝ] ℝ) (b : E) :
    ⟪secondVector φ, b⟫ = φ (0, b) :=
  inner_secondVector φ b

example (ψ : E × E → ℝ) (x : E × E) :
    E :=
  entryMomentum ψ x

example (ψ : E × E → ℝ) (x : E × E) :
    E :=
  exitMomentum ψ x

example (ψ : E × E → ℝ) (x : E × E) :
    E × E :=
  momentumMap ψ x

example (ψ : E × E → ℝ) (x : E × E) (a : E) :
    ⟪entryMomentum ψ x, a⟫ = -fderiv ℝ ψ x (a, 0) :=
  inner_entryMomentum ψ x a

example (ψ : E × E → ℝ) (x : E × E) (b : E) :
    ⟪exitMomentum ψ x, b⟫ = fderiv ℝ ψ x (0, b) :=
  inner_exitMomentum ψ x b

example (ψ : E × E → ℝ) (x u : E × E) :
    fderiv ℝ ψ x u = -⟪entryMomentum ψ x, u.1⟫ + ⟪exitMomentum ψ x, u.2⟫ :=
  fderiv_apply_eq_inner ψ x u

example {ψ : E × E → ℝ} {x : E × E} (hψ : DifferentiableAt ℝ ψ x) :
    entryMomentum ψ x = -gradient (fun r => ψ (r, x.2)) x.1 :=
  entryMomentum_eq_neg_gradient hψ

example {ψ : E × E → ℝ} {x : E × E} (hψ : DifferentiableAt ℝ ψ x) :
    exitMomentum ψ x = gradient (fun r' => ψ (x.1, r')) x.2 :=
  exitMomentum_eq_gradient hψ

example {ψ : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U) (hψ : ContDiffOn ℝ 2 ψ U) :
    ContDiffOn ℝ 1 (entryMomentum ψ) U :=
  contDiffOn_entryMomentum hU hψ

example {ψ : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U) (hψ : ContDiffOn ℝ 2 ψ U) :
    ContDiffOn ℝ 1 (exitMomentum ψ) U :=
  contDiffOn_exitMomentum hU hψ

example {ψ : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U) (hψ : ContDiffOn ℝ 2 ψ U) :
    ContDiffOn ℝ 1 (momentumMap ψ) U :=
  contDiffOn_momentumMap hU hψ

example {ψ : E × E → ℝ} {x : E × E} (hψ : ContDiffAt ℝ 2 ψ x) :
    HasFDerivAt (entryMomentum ψ) (-(firstVector.comp (fderiv ℝ (fderiv ℝ ψ) x))) x :=
  hasFDerivAt_entryMomentum hψ

example {ψ : E × E → ℝ} {x : E × E} (hψ : ContDiffAt ℝ 2 ψ x) :
    HasFDerivAt (exitMomentum ψ) (secondVector.comp (fderiv ℝ (fderiv ℝ ψ) x)) x :=
  hasFDerivAt_exitMomentum hψ

example (ψ : E × E → ℝ) (x : E × E) :
    E →L[ℝ] E :=
  mixedHessian ψ x

example {ψ : E × E → ℝ} {x : E × E} (hψ : ContDiffAt ℝ 2 ψ x) (a b : E) :
    ⟪mixedHessian ψ x b, a⟫ = fderiv ℝ (fderiv ℝ ψ) x (0, b) (a, 0) :=
  inner_mixedHessian hψ a b

example (ψ : E × E → ℝ) (g : E × E → E × E) (y : E × E) :
    ℝ :=
  angularEikonal ψ g y

example {ψ : E × E → ℝ} {g : E × E → E × E} {y : E × E} (hψ : DifferentiableAt ℝ ψ (g y))
    (hg : DifferentiableAt ℝ g y) (hy : momentumMap ψ (g y) = y) :
    HasFDerivAt (angularEikonal ψ g)
      ((innerSL ℝ (g y).1).comp (fst ℝ E E) - (innerSL ℝ (g y).2).comp (snd ℝ E E)) y :=
  hasFDerivAt_angularEikonal hψ hg hy

example {ψ : E × E → ℝ} {g : E × E → E × E} {V : Set (E × E)}
    (hψ : ∀ y ∈ V, DifferentiableAt ℝ ψ (g y)) (hg : ∀ y ∈ V, DifferentiableAt ℝ g y)
    (hinv : ∀ y ∈ V, momentumMap ψ (g y) = y) {y : E × E} (hy : y ∈ V) :
    fderiv ℝ (angularEikonal ψ g) y =
      (innerSL ℝ (g y).1).comp (fst ℝ E E) - (innerSL ℝ (g y).2).comp (snd ℝ E E) :=
  fderiv_angularEikonal hψ hg hinv hy

example {ψ : E × E → ℝ} {g : E × E → E × E} {y : E × E} (hψ : DifferentiableAt ℝ ψ (g y))
    (hg : DifferentiableAt ℝ g y) (hy : momentumMap ψ (g y) = y) :
    gradient (fun p => angularEikonal ψ g (p, y.2)) y.1 = (g y).1 :=
  gradient_angularEikonal_fst hψ hg hy

example {ψ : E × E → ℝ} {g : E × E → E × E} {y : E × E} (hψ : DifferentiableAt ℝ ψ (g y))
    (hg : DifferentiableAt ℝ g y) (hy : momentumMap ψ (g y) = y) :
    gradient (fun p' => angularEikonal ψ g (y.1, p')) y.2 = -(g y).2 :=
  gradient_angularEikonal_snd hψ hg hy

example (v w : E × E) :
    ℝ :=
  canonicalForm v w

example (ψ : E × E → ℝ) (Φ : E × E → E × E) (W : Set (E × E)) :
    Prop :=
  IsRayMapOn ψ Φ W

example {ψ : E × E → ℝ} {Φ : E × E → E × E} {W : Set (E × E)} (hW : IsOpen W)
    (hray : IsRayMapOn ψ Φ W) {z : E × E} (hz : z ∈ W) (hΦ : DifferentiableAt ℝ Φ z)
    (hψ : ContDiffAt ℝ 2 ψ (z.1, (Φ z).1)) (v w : E × E) :
    canonicalForm (fderiv ℝ Φ z v) (fderiv ℝ Φ z w) = canonicalForm v w :=
  rayMap_symplectic hW hray hz hΦ hψ v w

example {ψ : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U) (hψ : ContDiffOn ℝ 2 ψ U) {x₀ : E × E}
    (hx₀ : x₀ ∈ U) (hinv : (fderiv ℝ (momentumMap ψ) x₀).IsInvertible) :
    ∃ (V : Set (E × E)) (g : E × E → E × E), IsOpen V ∧ momentumMap ψ x₀ ∈ V ∧
      g (momentumMap ψ x₀) = x₀ ∧ ContDiffOn ℝ 1 g V ∧
      (∀ y ∈ V, g y ∈ U ∧ momentumMap ψ (g y) = y) ∧
      ∀ᶠ x in 𝓝 x₀, g (momentumMap ψ x) = x :=
  exists_localInverse_momentumMap hU hψ hx₀ hinv

example {ψ : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U) (hψ : ContDiffOn ℝ 2 ψ U) {x₀ : E × E}
    (hx₀ : x₀ ∈ U) (hinv : (fderiv ℝ (momentumMap ψ) x₀).IsInvertible) :
    ∃ (V : Set (E × E)) (g : E × E → E × E), IsOpen V ∧ momentumMap ψ x₀ ∈ V ∧
      g (momentumMap ψ x₀) = x₀ ∧ ContDiffOn ℝ 1 g V ∧
      (∀ y ∈ V, g y ∈ U ∧ momentumMap ψ (g y) = y) ∧
      ∀ y ∈ V, fderiv ℝ (angularEikonal ψ g) y =
        (innerSL ℝ (g y).1).comp (fst ℝ E E) - (innerSL ℝ (g y).2).comp (snd ℝ E E) :=
  exists_angularEikonal hU hψ hx₀ hinv

example {ψ : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U) (hψ : ContDiffOn ℝ 2 ψ U) {x₀ : E × E}
    (hx₀ : x₀ ∈ U) (hinv : (mixedHessian ψ x₀).IsInvertible) :
    ∃ (W : Set (E × E)) (Φ : E × E → E × E), IsOpen W ∧ (x₀.1, entryMomentum ψ x₀) ∈ W ∧
      Φ (x₀.1, entryMomentum ψ x₀) = (x₀.2, exitMomentum ψ x₀) ∧ ContDiffOn ℝ 1 Φ W ∧
      (∀ z ∈ W, (z.1, (Φ z).1) ∈ U) ∧ IsRayMapOn ψ Φ W :=
  exists_rayMap hU hψ hx₀ hinv

example {ψ : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U) (hψ : ContDiffOn ℝ 2 ψ U) {x₀ : E × E}
    (hx₀ : x₀ ∈ U) (hinv : (mixedHessian ψ x₀).IsInvertible) :
    ∃ (W : Set (E × E)) (Φ : E × E → E × E), IsOpen W ∧ (x₀.1, entryMomentum ψ x₀) ∈ W ∧
      ContDiffOn ℝ 1 Φ W ∧ IsRayMapOn ψ Φ W ∧ ∀ z ∈ W, ∀ v w : E × E,
        canonicalForm (fderiv ℝ Φ z v) (fderiv ℝ Φ z w) = canonicalForm v w :=
  exists_rayMap_symplectic hU hψ hx₀ hinv

example (ψ₀ a b c : ℝ) (x : E × E) :
    ℝ :=
  paraxialEikonal ψ₀ a b c x

example (ψ₀ a b c : ℝ) (x : E × E) :
    HasFDerivAt (paraxialEikonal ψ₀ a b c)
      ((innerSL ℝ (a • x.1 - b • x.2)).comp (fst ℝ E E) +
        (innerSL ℝ (c • x.2 - b • x.1)).comp (snd ℝ E E)) x :=
  hasFDerivAt_paraxialEikonal ψ₀ a b c x

example (ψ₀ a b c : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (paraxialEikonal (E := E) ψ₀ a b c) :=
  contDiff_paraxialEikonal ψ₀ a b c

example (ψ₀ a b c : ℝ) (x : E × E) :
    momentumMap (paraxialEikonal ψ₀ a b c) x = (b • x.2 - a • x.1, c • x.2 - b • x.1) :=
  momentumMap_paraxialEikonal ψ₀ a b c x

example (a b c : ℝ) :
    (E × E) →L[ℝ] E × E :=
  paraxialMomentum a b c

example (ψ₀ a b c : ℝ) :
    momentumMap (paraxialEikonal ψ₀ a b c) = paraxialMomentum (E := E) a b c :=
  momentumMap_paraxialEikonal_eq ψ₀ a b c

example (a b c : ℝ) :
    (E × E) →L[ℝ] E × E :=
  paraxialInverse a b c

example {a b c : ℝ} (hD : b ^ 2 - a * c ≠ 0) (y : E × E) :
    paraxialMomentum a b c (paraxialInverse a b c y) = y :=
  paraxialMomentum_paraxialInverse hD y

example {a b c : ℝ} (hD : b ^ 2 - a * c ≠ 0) (x : E × E) :
    paraxialInverse a b c (paraxialMomentum a b c x) = x :=
  paraxialInverse_paraxialMomentum hD x

example {ψ₀ a b c : ℝ} (hD : b ^ 2 - a * c ≠ 0) (x : E × E) :
    (fderiv ℝ (momentumMap (paraxialEikonal ψ₀ a b c)) x).IsInvertible :=
  isInvertible_fderiv_momentumMap_paraxialEikonal hD x

example {ψ₀ a b c : ℝ} (hD : b ^ 2 - a * c ≠ 0) (y : E × E) :
    momentumMap (paraxialEikonal ψ₀ a b c) (paraxialInverse a b c y) = y :=
  momentumMap_paraxialInverse hD y

example {ψ₀ a b c : ℝ} (hD : b ^ 2 - a * c ≠ 0) (y : E × E) :
    angularEikonal (paraxialEikonal ψ₀ a b c) (paraxialInverse a b c) y =
      ψ₀ + (c * ‖y.1‖ ^ 2 - 2 * b * ⟪y.1, y.2⟫ + a * ‖y.2‖ ^ 2) / (2 * (b ^ 2 - a * c)) :=
  angularEikonal_paraxialEikonal hD y

example (ψ₀ a b c : ℝ) :
    entryMomentum (paraxialEikonal ψ₀ a b c) = ⇑(b • snd ℝ E E - a • fst ℝ E E) :=
  entryMomentum_paraxialEikonal ψ₀ a b c

example (ψ₀ a b c : ℝ) (x : E × E) :
    mixedHessian (paraxialEikonal ψ₀ a b c) x = -b • ContinuousLinearMap.id ℝ E :=
  mixedHessian_paraxialEikonal ψ₀ a b c x

example {ψ₀ a b c : ℝ} (hb : b ≠ 0) (x : E × E) :
    (mixedHessian (paraxialEikonal ψ₀ a b c) x).IsInvertible :=
  isInvertible_mixedHessian_paraxialEikonal hb x

example (a b c : ℝ) :
    (E × E) →L[ℝ] E × E :=
  paraxialRayMap a b c

example {ψ₀ a b c : ℝ} (hb : b ≠ 0) :
    IsRayMapOn (paraxialEikonal ψ₀ a b c) (paraxialRayMap (E := E) a b c) univ :=
  isRayMapOn_paraxialRayMap hb

example {a b c : ℝ} (hb : b ≠ 0) (v w : E × E) :
    canonicalForm (paraxialRayMap a b c v) (paraxialRayMap a b c w) = canonicalForm v w :=
  paraxialRayMap_symplectic hb v w

example (L : ℝ) (x : E × E) :
    paraxialEikonal L L⁻¹ L⁻¹ L⁻¹ x = L + ‖x.2 - x.1‖ ^ 2 / (2 * L) :=
  paraxialEikonal_freePropagation L x

example {L : ℝ} (hL : L ≠ 0) (z : E × E) :
    paraxialRayMap L⁻¹ L⁻¹ L⁻¹ z = (z.1 + L • z.2, z.2) :=
  paraxialRayMap_freePropagation hL z

example [Nontrivial E] (ψ₀ a : ℝ) (x : E × E) :
    ¬(fderiv ℝ (momentumMap (paraxialEikonal ψ₀ a a a)) x).IsInvertible :=
  not_isInvertible_fderiv_momentumMap_freePropagation ψ₀ a x

example {ψ₀ F L : ℝ} (hF : F ≠ 0) (hL : L ≠ 0) (y : E × E) :
    angularEikonal (paraxialEikonal ψ₀ (L⁻¹ - F⁻¹) L⁻¹ L⁻¹)
        (paraxialInverse (L⁻¹ - F⁻¹) L⁻¹ L⁻¹) y =
      ψ₀ + (F * ‖y.1 - y.2‖ ^ 2 - L * ‖y.2‖ ^ 2) / 2 :=
  angularEikonal_thinLens hF hL y

example {F L : ℝ} (hL : L ≠ 0) (z : E × E) :
    paraxialRayMap (L⁻¹ - F⁻¹) L⁻¹ L⁻¹ z = (z.1 + L • (z.2 - F⁻¹ • z.1), z.2 - F⁻¹ • z.1) :=
  paraxialRayMap_thinLens hL z

example (L : ℝ) (x : E × E) :
    ℝ :=
  freeEikonal L x

example {L : ℝ} (hL : L ≠ 0) (x : E × E) :
    0 < freeEikonal L x :=
  freeEikonal_pos hL x

example {L : ℝ} (hL : L ≠ 0) {n : WithTop ℕ∞} :
    ContDiff ℝ n (freeEikonal (E := E) L) :=
  contDiff_freeEikonal hL

example {L : ℝ} (hL : L ≠ 0) (x : E × E) :
    HasFDerivAt (freeEikonal L)
      ((freeEikonal L x)⁻¹ • (innerSL ℝ (x.2 - x.1)).comp (snd ℝ E E - fst ℝ E E)) x :=
  hasFDerivAt_freeEikonal hL x

example {L : ℝ} (hL : L ≠ 0) (x : E × E) :
    momentumMap (freeEikonal L) x =
      ((freeEikonal L x)⁻¹ • (x.2 - x.1), (freeEikonal L x)⁻¹ • (x.2 - x.1)) :=
  momentumMap_freeEikonal hL x

example (L : ℝ) (z : E × E) :
    E × E :=
  freeRayMap L z

example (L : ℝ) {z : E × E} (hz : ‖z.2‖ < 1) :
    DifferentiableAt ℝ (freeRayMap L) z :=
  differentiableAt_freeRayMap L hz

example {L : ℝ} (hL : 0 < L) :
    IsRayMapOn (freeEikonal L) (freeRayMap L) {z : E × E | ‖z.2‖ < 1} :=
  isRayMapOn_freeRayMap hL

example {L : ℝ} (hL : 0 < L) {z : E × E} (hz : ‖z.2‖ < 1) (v w : E × E) :
    canonicalForm (fderiv ℝ (freeRayMap L) z v) (fderiv ℝ (freeRayMap L) z w) =
      canonicalForm v w :=
  freeRayMap_symplectic hL hz v w

namespace Free

open SmoothAlgebra SmoothRing FreeSmoothRing Mechanics.GeneratingFunction

variable {ι : Type*} [DecidableEq ι]

example (ψ : PositionPair ι) (G : SmoothRingHom (PositionPair ι) (PhaseSpace ι)) :
    SmoothRingHom (PhaseSpace ι) (PhaseSpace ι) :=
  rayMap ψ G

example (ψ : PositionPair ι) (G : SmoothRingHom (PositionPair ι) (PhaseSpace ι)) (i : ι) :
    rayMap ψ G (PhaseSpace.q i) = G (newPosition i) :=
  rayMap_q ψ G i

example (ψ : PositionPair ι) (G : SmoothRingHom (PositionPair ι) (PhaseSpace ι)) (i : ι) :
    rayMap ψ G (PhaseSpace.p i) = G (gradNew ψ i) :=
  rayMap_p ψ G i

example [Fintype ι] {ψ : PositionPair ι} {G : SmoothRingHom (PositionPair ι) (PhaseSpace ι)}
    (h : IsFree (-ψ) G) :
    IsPoissonHom (PhaseSpace.canonical ι).toAlmostPoissonStructure
      (PhaseSpace.canonical ι).toAlmostPoissonStructure (rayMap ψ G) :=
  rayMap_isPoissonHom h

example [Fintype ι] (a b c : ℝ) :
    PositionPair ι :=
  paraxialEikonal ι a b c

example [Fintype ι] (a b c : ℝ) (i : ι) :
    gradOld (paraxialEikonal ι a b c) i =
      algebraMap ℝ (PositionPair ι) a * oldPosition i -
        algebraMap ℝ (PositionPair ι) b * newPosition i :=
  gradOld_paraxialEikonal a b c i

example [Fintype ι] (a b c : ℝ) (i : ι) :
    gradNew (paraxialEikonal ι a b c) i =
      algebraMap ℝ (PositionPair ι) c * newPosition i -
        algebraMap ℝ (PositionPair ι) b * oldPosition i :=
  gradNew_paraxialEikonal a b c i

example (a b : ℝ) :
    SmoothRingHom (PositionPair ι) (PhaseSpace ι) :=
  paraxialInverse ι a b

example (a b : ℝ) (i : ι) :
    paraxialInverse ι a b (oldPosition i) = PhaseSpace.q i :=
  paraxialInverse_oldPosition a b i

example (a b : ℝ) (i : ι) :
    paraxialInverse ι a b (newPosition i) = algebraMap ℝ (PhaseSpace ι) b⁻¹ *
      (PhaseSpace.p i + algebraMap ℝ (PhaseSpace ι) a * PhaseSpace.q i) :=
  paraxialInverse_newPosition a b i

example [Fintype ι] {a b : ℝ} (c : ℝ) (hb : b ≠ 0) :
    IsFree (-paraxialEikonal ι a b c) (paraxialInverse ι a b) :=
  isFree_paraxialEikonal c hb

example [Fintype ι] (a b c : ℝ) (i : ι) :
    rayMap (paraxialEikonal ι a b c) (paraxialInverse ι a b) (PhaseSpace.q i) =
      algebraMap ℝ (PhaseSpace ι) b⁻¹ *
        (PhaseSpace.p i + algebraMap ℝ (PhaseSpace ι) a * PhaseSpace.q i) :=
  rayMap_paraxialEikonal_q a b c i

example [Fintype ι] (a b c : ℝ) (i : ι) :
    rayMap (paraxialEikonal ι a b c) (paraxialInverse ι a b) (PhaseSpace.p i) =
      algebraMap ℝ (PhaseSpace ι) c * (algebraMap ℝ (PhaseSpace ι) b⁻¹ *
        (PhaseSpace.p i + algebraMap ℝ (PhaseSpace ι) a * PhaseSpace.q i)) -
        algebraMap ℝ (PhaseSpace ι) b * PhaseSpace.q i :=
  rayMap_paraxialEikonal_p a b c i

example [Fintype ι] {a b : ℝ} (c : ℝ) (hb : b ≠ 0) :
    IsPoissonHom (PhaseSpace.canonical ι).toAlmostPoissonStructure
      (PhaseSpace.canonical ι).toAlmostPoissonStructure
      (rayMap (paraxialEikonal ι a b c) (paraxialInverse ι a b)) :=
  rayMap_paraxialEikonal_isPoissonHom c hb

example [Fintype ι] (F L : ℝ) :
    PositionPair ι :=
  thinLens ι F L

example [Fintype ι] (F : ℝ) {L : ℝ} (hL : L ≠ 0) :
    IsPoissonHom (PhaseSpace.canonical ι).toAlmostPoissonStructure
      (PhaseSpace.canonical ι).toAlmostPoissonStructure
      (rayMap (thinLens ι F L) (paraxialInverse ι (L⁻¹ - F⁻¹) L⁻¹)) :=
  rayMap_thinLens_isPoissonHom F hL

example [Fintype ι] (F : ℝ) {L : ℝ} (hL : L ≠ 0) (i : ι) :
    rayMap (thinLens ι F L) (paraxialInverse ι (L⁻¹ - F⁻¹) L⁻¹) (PhaseSpace.q i) =
      PhaseSpace.q i + algebraMap ℝ (PhaseSpace ι) L *
        (PhaseSpace.p i - algebraMap ℝ (PhaseSpace ι) F⁻¹ * PhaseSpace.q i) :=
  rayMap_thinLens_q F hL i

example [Fintype ι] (F : ℝ) {L : ℝ} (hL : L ≠ 0) (i : ι) :
    rayMap (thinLens ι F L) (paraxialInverse ι (L⁻¹ - F⁻¹) L⁻¹) (PhaseSpace.p i) =
      PhaseSpace.p i - algebraMap ℝ (PhaseSpace ι) F⁻¹ * PhaseSpace.q i :=
  rayMap_thinLens_p F hL i

end Free

end ProjectAinos.Electrodynamics.Optics.AngularEikonal

end AngularEikonal

section HighFrequency

open Real Filter

open scoped Topology ContDiff

namespace ProjectAinos.SmoothGeometry.Wave

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (f g : ℝ × E3 → ℝ) (p : ℝ × E3) :
    ℝ :=
  wavePairing f g p

example {ψ : ℝ × E3 → ℝ} {q : ℝ × E3} (hψ : DifferentiableAt ℝ ψ q) (ε : ℝ) :
    HasFDerivAt (fun y => ψ y / ε) (ε⁻¹ • fderiv ℝ ψ q) q :=
  hasFDerivAt_div_const hψ ε

example {a ψ : ℝ × E3 → ℝ} {q : ℝ × E3} (ha : DifferentiableAt ℝ a q)
    (hψ : DifferentiableAt ℝ ψ q) (ε : ℝ) (v : ℝ × E3) :
    fderiv ℝ (fun y => a y * cos (ψ y / ε)) q v =
      fderiv ℝ a q v * cos (ψ q / ε) - ε⁻¹ * (a q * fderiv ℝ ψ q v) * sin (ψ q / ε) :=
  fderiv_mul_cos_apply ha hψ ε v

example {b ψ : ℝ × E3 → ℝ} {q : ℝ × E3} (hb : DifferentiableAt ℝ b q)
    (hψ : DifferentiableAt ℝ ψ q) (ε : ℝ) (v : ℝ × E3) :
    fderiv ℝ (fun y => b y * sin (ψ y / ε)) q v =
      fderiv ℝ b q v * sin (ψ q / ε) + ε⁻¹ * (b q * fderiv ℝ ψ q v) * cos (ψ q / ε) :=
  fderiv_mul_sin_apply hb hψ ε v

example {f : ℝ × E3 → ℝ} {p : ℝ × E3} (hf : ContDiffAt ℝ 2 f p) (v : ℝ × E3) :
    DifferentiableAt ℝ (fun q => fderiv ℝ f q v) p :=
  differentiableAt_fderiv_apply hf v

example {a ψ : ℝ × E3 → ℝ} {p : ℝ × E3} (ha : ContDiffAt ℝ 2 a p) (hψ : ContDiffAt ℝ 2 ψ p)
    (ε : ℝ) (v : ℝ × E3) :
    fderiv ℝ (fun q => fderiv ℝ (fun y => a y * cos (ψ y / ε)) q v) p v =
      fderiv ℝ (fun q => fderiv ℝ a q v) p v * cos (ψ p / ε) -
        2 * ε⁻¹ * (fderiv ℝ a p v * fderiv ℝ ψ p v) * sin (ψ p / ε) -
        ε⁻¹ ^ 2 * (a p * fderiv ℝ ψ p v ^ 2) * cos (ψ p / ε) -
        ε⁻¹ * (a p * fderiv ℝ (fun q => fderiv ℝ ψ q v) p v) * sin (ψ p / ε) :=
  fderiv_fderiv_mul_cos_apply ha hψ ε v

example {b ψ : ℝ × E3 → ℝ} {p : ℝ × E3} (hb : ContDiffAt ℝ 2 b p) (hψ : ContDiffAt ℝ 2 ψ p)
    (ε : ℝ) (v : ℝ × E3) :
    fderiv ℝ (fun q => fderiv ℝ (fun y => b y * sin (ψ y / ε)) q v) p v =
      fderiv ℝ (fun q => fderiv ℝ b q v) p v * sin (ψ p / ε) +
        2 * ε⁻¹ * (fderiv ℝ b p v * fderiv ℝ ψ p v) * cos (ψ p / ε) -
        ε⁻¹ ^ 2 * (b p * fderiv ℝ ψ p v ^ 2) * sin (ψ p / ε) +
        ε⁻¹ * (b p * fderiv ℝ (fun q => fderiv ℝ ψ q v) p v) * cos (ψ p / ε) :=
  fderiv_fderiv_mul_sin_apply hb hψ ε v

example {a ψ : ℝ × E3 → ℝ} {p : ℝ × E3} (ha : ContDiffAt ℝ 2 a p) (hψ : ContDiffAt ℝ 2 ψ p)
    (ε : ℝ) :
    timeDeriv (timeDeriv fun q => a q * cos (ψ q / ε)) p =
      timeDeriv (timeDeriv a) p * cos (ψ p / ε) -
        2 * ε⁻¹ * (timeDeriv a p * timeDeriv ψ p) * sin (ψ p / ε) -
        ε⁻¹ ^ 2 * (a p * timeDeriv ψ p ^ 2) * cos (ψ p / ε) -
        ε⁻¹ * (a p * timeDeriv (timeDeriv ψ) p) * sin (ψ p / ε) :=
  timeDeriv_timeDeriv_mul_cos ha hψ ε

example {a ψ : ℝ × E3 → ℝ} {p : ℝ × E3} (ha : ContDiffAt ℝ 2 a p) (hψ : ContDiffAt ℝ 2 ψ p)
    (ε : ℝ) (i : Fin 3) :
    spaceDeriv i (spaceDeriv i fun q => a q * cos (ψ q / ε)) p =
      spaceDeriv i (spaceDeriv i a) p * cos (ψ p / ε) -
        2 * ε⁻¹ * (spaceDeriv i a p * spaceDeriv i ψ p) * sin (ψ p / ε) -
        ε⁻¹ ^ 2 * (a p * spaceDeriv i ψ p ^ 2) * cos (ψ p / ε) -
        ε⁻¹ * (a p * spaceDeriv i (spaceDeriv i ψ) p) * sin (ψ p / ε) :=
  spaceDeriv_spaceDeriv_mul_cos ha hψ ε i

example {b ψ : ℝ × E3 → ℝ} {p : ℝ × E3} (hb : ContDiffAt ℝ 2 b p) (hψ : ContDiffAt ℝ 2 ψ p)
    (ε : ℝ) :
    timeDeriv (timeDeriv fun q => b q * sin (ψ q / ε)) p =
      timeDeriv (timeDeriv b) p * sin (ψ p / ε) +
        2 * ε⁻¹ * (timeDeriv b p * timeDeriv ψ p) * cos (ψ p / ε) -
        ε⁻¹ ^ 2 * (b p * timeDeriv ψ p ^ 2) * sin (ψ p / ε) +
        ε⁻¹ * (b p * timeDeriv (timeDeriv ψ) p) * cos (ψ p / ε) :=
  timeDeriv_timeDeriv_mul_sin hb hψ ε

example {b ψ : ℝ × E3 → ℝ} {p : ℝ × E3} (hb : ContDiffAt ℝ 2 b p) (hψ : ContDiffAt ℝ 2 ψ p)
    (ε : ℝ) (i : Fin 3) :
    spaceDeriv i (spaceDeriv i fun q => b q * sin (ψ q / ε)) p =
      spaceDeriv i (spaceDeriv i b) p * sin (ψ p / ε) +
        2 * ε⁻¹ * (spaceDeriv i b p * spaceDeriv i ψ p) * cos (ψ p / ε) -
        ε⁻¹ ^ 2 * (b p * spaceDeriv i ψ p ^ 2) * sin (ψ p / ε) +
        ε⁻¹ * (b p * spaceDeriv i (spaceDeriv i ψ) p) * cos (ψ p / ε) :=
  spaceDeriv_spaceDeriv_mul_sin hb hψ ε i

example {a ψ : ℝ × E3 → ℝ} {p : ℝ × E3} (ha : ContDiffAt ℝ 2 a p) (hψ : ContDiffAt ℝ 2 ψ p)
    {ε : ℝ} (hε : ε ≠ 0) :
    waveOperator (fun q => a q * cos (ψ q / ε)) p =
      -(ε⁻¹ ^ 2 * wavePairing ψ ψ p * a p * cos (ψ p / ε)) -
        ε⁻¹ * (2 * wavePairing a ψ p + a p * waveOperator ψ p) * sin (ψ p / ε) +
        waveOperator a p * cos (ψ p / ε) :=
  waveOperator_mul_cos ha hψ hε

example {b ψ : ℝ × E3 → ℝ} {p : ℝ × E3} (hb : ContDiffAt ℝ 2 b p) (hψ : ContDiffAt ℝ 2 ψ p)
    {ε : ℝ} (hε : ε ≠ 0) :
    waveOperator (fun q => b q * sin (ψ q / ε)) p =
      -(ε⁻¹ ^ 2 * wavePairing ψ ψ p * b p * sin (ψ p / ε)) +
        ε⁻¹ * (2 * wavePairing b ψ p + b p * waveOperator ψ p) * cos (ψ p / ε) +
        waveOperator b p * sin (ψ p / ε) :=
  waveOperator_mul_sin hb hψ hε

example (f g : ℝ × E3 → ℝ) (p : ℝ × E3) :
    wavePairing f g p = wavePairing g f p :=
  wavePairing_comm f g p

example {f g : ℝ × E3 → ℝ} {p : ℝ × E3} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) (ψ : ℝ × E3 → ℝ) :
    wavePairing (fun q => f q * g q) ψ p = f p * wavePairing g ψ p + g p * wavePairing f ψ p :=
  wavePairing_fun_mul hf hg ψ

example {f g : ℝ × E3 → ℝ} {p : ℝ × E3} (hf : ContDiffAt ℝ 2 f p) (hg : ContDiffAt ℝ 2 g p)
    (v : ℝ × E3) :
    fderiv ℝ (fun q => fderiv ℝ (fun y => f y + g y) q v) p v =
      fderiv ℝ (fun q => fderiv ℝ f q v) p v + fderiv ℝ (fun q => fderiv ℝ g q v) p v :=
  fderiv_fderiv_add_apply hf hg v

example {f g : ℝ × E3 → ℝ} {p : ℝ × E3} (hf : ContDiffAt ℝ 2 f p) (hg : ContDiffAt ℝ 2 g p) :
    waveOperator (fun q => f q + g q) p = waveOperator f p + waveOperator g p :=
  waveOperator_fun_add hf hg

example (a ψ : ℝ × E3 → ℝ) (p : ℝ × E3) :
    ℝ :=
  transport a ψ p

example (a b ψ : ℝ × E3 → ℝ) (ε : ℝ) (p : ℝ × E3) :
    ℝ :=
  highFrequencyWave a b ψ ε p

example {n : ℕ∞ω} {a b ψ : ℝ × E3 → ℝ} {p : ℝ × E3} (ha : ContDiffAt ℝ n a p)
    (hb : ContDiffAt ℝ n b p) (hψ : ContDiffAt ℝ n ψ p) (ε : ℝ) :
    ContDiffAt ℝ n (highFrequencyWave a b ψ ε) p :=
  contDiffAt_highFrequencyWave ha hb hψ ε

example {a b ψ : ℝ × E3 → ℝ} {p : ℝ × E3} (ha : DifferentiableAt ℝ a p)
    (hb : DifferentiableAt ℝ b p) (hψ : DifferentiableAt ℝ ψ p) (ε : ℝ) (v : ℝ × E3) :
    fderiv ℝ (highFrequencyWave a b ψ ε) p v =
      ε⁻¹ * (fderiv ℝ ψ p v * (b p * cos (ψ p / ε) - a p * sin (ψ p / ε))) +
        (fderiv ℝ a p v * cos (ψ p / ε) + fderiv ℝ b p v * sin (ψ p / ε)) :=
  fderiv_highFrequencyWave_apply ha hb hψ ε v

example {a b ψ : ℝ × E3 → ℝ} {p : ℝ × E3} (ha : DifferentiableAt ℝ a p)
    (hb : DifferentiableAt ℝ b p) (hψ : DifferentiableAt ℝ ψ p) (ε : ℝ) :
    timeDeriv (highFrequencyWave a b ψ ε) p =
      ε⁻¹ * (timeDeriv ψ p * (b p * cos (ψ p / ε) - a p * sin (ψ p / ε))) +
        (timeDeriv a p * cos (ψ p / ε) + timeDeriv b p * sin (ψ p / ε)) :=
  timeDeriv_highFrequencyWave ha hb hψ ε

example {a b ψ : ℝ × E3 → ℝ} {p : ℝ × E3} (ha : DifferentiableAt ℝ a p)
    (hb : DifferentiableAt ℝ b p) (hψ : DifferentiableAt ℝ ψ p) (ε : ℝ) (i : Fin 3) :
    spaceDeriv i (highFrequencyWave a b ψ ε) p =
      ε⁻¹ * (spaceDeriv i ψ p * (b p * cos (ψ p / ε) - a p * sin (ψ p / ε))) +
        (spaceDeriv i a p * cos (ψ p / ε) + spaceDeriv i b p * sin (ψ p / ε)) :=
  spaceDeriv_highFrequencyWave ha hb hψ ε i

example {a b ψ : ℝ × E3 → ℝ} {p : ℝ × E3} (ha : ContDiffAt ℝ 2 a p) (hb : ContDiffAt ℝ 2 b p)
    (hψ : ContDiffAt ℝ 2 ψ p) {ε : ℝ} (hε : ε ≠ 0) :
    waveOperator (highFrequencyWave a b ψ ε) p =
      ε⁻¹ ^ 2 * (-wavePairing ψ ψ p * (a p * cos (ψ p / ε) + b p * sin (ψ p / ε))) +
        ε⁻¹ * (transport b ψ p * cos (ψ p / ε) - transport a ψ p * sin (ψ p / ε)) +
        (waveOperator a p * cos (ψ p / ε) + waveOperator b p * sin (ψ p / ε)) :=
  waveOperator_highFrequencyWave ha hb hψ hε

example (L : ℝ × E3 →L[ℝ] ℝ) (c : ℝ) (x : E3) :
    L (c, x) = c * L (1, 0) + ∑ i, x i * L (0, EuclideanSpace.single i 1) :=
  clm_apply_prod L c x

example (ψ : ℝ × E3 → ℝ) (p : ℝ × E3) :
    ℝ × E3 :=
  raisedGradient ψ p

example (f ψ : ℝ × E3 → ℝ) (p : ℝ × E3) :
    fderiv ℝ f p (raisedGradient ψ p) = wavePairing f ψ p :=
  fderiv_raisedGradient f ψ p

end ProjectAinos.SmoothGeometry.Wave

end HighFrequency

section Eikonal

open Real Filter Set MeasureTheory

open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics.Optics.Eikonal

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Wave SpecialRelativity

open SmoothGeometry.LinearODE SmoothGeometry.NonlinearODE

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (a b : Fin 4 → ℝ × E3 → ℝ) (ψ : ℝ × E3 → ℝ) (ε : ℝ) :
    Potential :=
  highFrequencyPotential a b ψ ε

example (a b : Fin 4 → ℝ × E3 → ℝ) (ψ : ℝ × E3 → ℝ) (ε : ℝ) (μ : Fin 4) :
    potentialComponent (highFrequencyPotential a b ψ ε) μ =
      fun v => highFrequencyWave (a μ) (b μ) ψ ε (timeSpaceEquiv v) :=
  potentialComponent_highFrequencyPotential a b ψ ε μ

example {n : ℕ∞ω} {φ : Spacetime → ℝ} {a : Spacetime → Fin 3 → ℝ} {v : Spacetime}
    (hφ : ContDiffAt ℝ n φ v) (ha : ∀ i, ContDiffAt ℝ n (fun y => a y i) v) :
    ContDiffAt ℝ n (potentialOf φ a) v :=
  contDiffAt_potentialOf hφ ha

example {a b : Fin 4 → ℝ × E3 → ℝ} {ψ : ℝ × E3 → ℝ} {v : Spacetime}
    (ha : ∀ μ, ContDiffAt ℝ 2 (a μ) (timeSpaceEquiv v))
    (hb : ∀ μ, ContDiffAt ℝ 2 (b μ) (timeSpaceEquiv v)) (hψ : ContDiffAt ℝ 2 ψ (timeSpaceEquiv v))
    (ε : ℝ) :
    ContDiffAt ℝ 2 (highFrequencyPotential a b ψ ε) v :=
  contDiffAt_highFrequencyPotential ha hb hψ ε

example {u : ℝ × E3 → ℝ} {v : Spacetime} (hu : DifferentiableAt ℝ u (timeSpaceEquiv v)) :
    partialAt (fun w => u (timeSpaceEquiv w)) 0 v = timeDeriv u (timeSpaceEquiv v) :=
  partialAt_comp_timeSpaceEquiv_zero hu

example {u : ℝ × E3 → ℝ} {v : Spacetime} (hu : DifferentiableAt ℝ u (timeSpaceEquiv v))
    (i : Fin 3) :
    partialAt (fun w => u (timeSpaceEquiv w)) i.succ v = spaceDeriv i u (timeSpaceEquiv v) :=
  partialAt_comp_timeSpaceEquiv_succ hu i

example {u : ℝ × E3 → ℝ} {v : Spacetime} (hu : ContDiffAt ℝ 2 u (timeSpaceEquiv v)) :
    box (fun w => u (timeSpaceEquiv w)) v = -waveOperator u (timeSpaceEquiv v) :=
  box_comp_timeSpaceEquiv_of_contDiffAt hu

example (c : ℝ × ℝ) (θ : ℝ) :
    ℝ :=
  trigValue c θ

example (a b : Fin 4 → ℝ × E3 → ℝ) (ψ : ℝ × E3 → ℝ) (μ : Fin 4) (q : ℝ × E3) :
    ℝ × ℝ :=
  leadingCoeff a b ψ μ q

example (a b : Fin 4 → ℝ × E3 → ℝ) (ψ : ℝ × E3 → ℝ) (μ : Fin 4) (q : ℝ × E3) :
    ℝ × ℝ :=
  subleadingCoeff a b ψ μ q

example (a b : Fin 4 → ℝ × E3 → ℝ) (μ : Fin 4) (q : ℝ × E3) :
    ℝ × ℝ :=
  zerothCoeff a b μ q

example {a b : Fin 4 → ℝ × E3 → ℝ} {ψ : ℝ × E3 → ℝ} {v : Spacetime} {μ : Fin 4}
    (ha : ContDiffAt ℝ 2 (a μ) (timeSpaceEquiv v)) (hb : ContDiffAt ℝ 2 (b μ) (timeSpaceEquiv v))
    (hψ : ContDiffAt ℝ 2 ψ (timeSpaceEquiv v)) {ε : ℝ} (hε : ε ≠ 0) :
    box (potentialComponent (highFrequencyPotential a b ψ ε) μ) v =
      ε⁻¹ ^ 2 * trigValue (leadingCoeff a b ψ μ (timeSpaceEquiv v))
          (ψ (timeSpaceEquiv v) / ε) +
        ε⁻¹ * trigValue (subleadingCoeff a b ψ μ (timeSpaceEquiv v))
          (ψ (timeSpaceEquiv v) / ε) +
        trigValue (zerothCoeff a b μ (timeSpaceEquiv v)) (ψ (timeSpaceEquiv v) / ε) :=
  box_highFrequencyPotential ha hb hψ hε

example (a : Fin 4 → ℝ × E3 → ℝ) (ψ : ℝ × E3 → ℝ) (q : ℝ × E3) :
    ℝ :=
  amplitudePairing a ψ q

example (a : Fin 4 → ℝ × E3 → ℝ) (q : ℝ × E3) :
    ℝ :=
  amplitudeDivergence a q

example {a b : Fin 4 → ℝ × E3 → ℝ} {ψ : ℝ × E3 → ℝ} {v : Spacetime}
    (ha : ∀ μ, DifferentiableAt ℝ (a μ) (timeSpaceEquiv v))
    (hb : ∀ μ, DifferentiableAt ℝ (b μ) (timeSpaceEquiv v))
    (hψ : DifferentiableAt ℝ ψ (timeSpaceEquiv v)) (ε : ℝ) :
    lorenzDivergence (highFrequencyPotential a b ψ ε) v =
      ε⁻¹ * trigValue (amplitudePairing b ψ (timeSpaceEquiv v),
          -amplitudePairing a ψ (timeSpaceEquiv v)) (ψ (timeSpaceEquiv v) / ε) +
        trigValue (amplitudeDivergence a (timeSpaceEquiv v),
          amplitudeDivergence b (timeSpaceEquiv v)) (ψ (timeSpaceEquiv v) / ε) :=
  lorenzDivergence_highFrequencyPotential ha hb hψ ε

example (a b : Fin 4 → ℝ × E3 → ℝ) (ψ : ℝ × E3 → ℝ) (q : ℝ × E3) :
    ((amplitudePairing b ψ q, -amplitudePairing a ψ q) : ℝ × ℝ) = 0 ↔
      amplitudePairing a ψ q = 0 ∧ amplitudePairing b ψ q = 0 :=
  lorenz_leading_eq_zero_iff a b ψ q

example {a b : Fin 4 → ℝ × E3 → ℝ} {ψ : ℝ × E3 → ℝ} {q : ℝ × E3}
    (h : ∃ μ, ((a μ q, b μ q) : ℝ × ℝ) ≠ 0) :
    (∀ μ, leadingCoeff a b ψ μ q = 0) ↔ wavePairing ψ ψ q = 0 :=
  leading_eq_zero_iff h

example {a b : Fin 4 → ℝ × E3 → ℝ} {ψ : ℝ × E3 → ℝ} {q : ℝ × E3} :
    (∀ μ, subleadingCoeff a b ψ μ q = 0) ↔
      ∀ μ, transport (a μ) ψ q = 0 ∧ transport (b μ) ψ q = 0 :=
  subleading_eq_zero_iff_transport

example {a b : Fin 4 → ℝ × E3 → ℝ} {ψ : ℝ × E3 → ℝ} {U : Set (ℝ × E3)}
    (hne : ∀ q ∈ U, ∃ μ, ((a μ q, b μ q) : ℝ × ℝ) ≠ 0) :
    (∀ q ∈ U, ∀ μ, leadingCoeff a b ψ μ q = 0 ∧ subleadingCoeff a b ψ μ q = 0) ↔
      (∀ q ∈ U, wavePairing ψ ψ q = 0) ∧
        ∀ q ∈ U, ∀ μ, transport (a μ) ψ q = 0 ∧ transport (b μ) ψ q = 0 :=
  leadingOrders_eq_zero_iff hne

example {V : Set Spacetime} (hV : IsOpen V) {a b : Fin 4 → ℝ × E3 → ℝ} {ψ : ℝ × E3 → ℝ}
    (ha : ∀ v ∈ V, ∀ μ, ContDiffAt ℝ 2 (a μ) (timeSpaceEquiv v))
    (hb : ∀ v ∈ V, ∀ μ, ContDiffAt ℝ 2 (b μ) (timeSpaceEquiv v))
    (hψ : ∀ v ∈ V, ContDiffAt ℝ 2 ψ (timeSpaceEquiv v)) {ε : ℝ} (hε : ε ≠ 0)
    (hL : ∀ v ∈ V, lorenzDivergence (highFrequencyPotential a b ψ ε) v = 0) :
    (∀ y ∈ V, (divergence3 (magneticField (fieldTensor (highFrequencyPotential a b ψ ε))) y = 0 ∧
        ∀ i, partialAt (magneticField (fieldTensor (highFrequencyPotential a b ψ ε)) i) 0 y +
          curl (electricField (fieldTensor (highFrequencyPotential a b ψ ε))) y i = 0) ∧
      (divergence3 (electricField (fieldTensor (highFrequencyPotential a b ψ ε))) y = 0 ∧
        ∀ i, curl (magneticField (fieldTensor (highFrequencyPotential a b ψ ε))) y i -
          partialAt (electricField (fieldTensor (highFrequencyPotential a b ψ ε)) i) 0 y = 0)) ↔
    ∀ v ∈ V, ∀ μ,
      ε⁻¹ ^ 2 * trigValue (leadingCoeff a b ψ μ (timeSpaceEquiv v)) (ψ (timeSpaceEquiv v) / ε) +
        ε⁻¹ * trigValue (subleadingCoeff a b ψ μ (timeSpaceEquiv v))
          (ψ (timeSpaceEquiv v) / ε) +
        trigValue (zerothCoeff a b μ (timeSpaceEquiv v)) (ψ (timeSpaceEquiv v) / ε) = 0 :=
  maxwell_highFrequencyPotential_iff hV ha hb hψ hε hL

example {V : Set Spacetime} (hV : IsOpen V) {a b : Fin 4 → ℝ × E3 → ℝ} {ψ : ℝ × E3 → ℝ}
    (ha : ∀ v ∈ V, ∀ μ, ContDiffAt ℝ 2 (a μ) (timeSpaceEquiv v))
    (hb : ∀ v ∈ V, ∀ μ, ContDiffAt ℝ 2 (b μ) (timeSpaceEquiv v))
    (hψ : ∀ v ∈ V, ContDiffAt ℝ 2 ψ (timeSpaceEquiv v)) {ε : ℝ} (hε : ε ≠ 0)
    (hL : ∀ v ∈ V, lorenzDivergence (highFrequencyPotential a b ψ ε) v = 0)
    (heik : ∀ v ∈ V, wavePairing ψ ψ (timeSpaceEquiv v) = 0)
    (htr : ∀ v ∈ V, ∀ μ, transport (a μ) ψ (timeSpaceEquiv v) = 0 ∧
      transport (b μ) ψ (timeSpaceEquiv v) = 0) :
    (∀ y ∈ V, (divergence3 (magneticField (fieldTensor (highFrequencyPotential a b ψ ε))) y = 0 ∧
        ∀ i, partialAt (magneticField (fieldTensor (highFrequencyPotential a b ψ ε)) i) 0 y +
          curl (electricField (fieldTensor (highFrequencyPotential a b ψ ε))) y i = 0) ∧
      (divergence3 (electricField (fieldTensor (highFrequencyPotential a b ψ ε))) y = 0 ∧
        ∀ i, curl (magneticField (fieldTensor (highFrequencyPotential a b ψ ε))) y i -
          partialAt (electricField (fieldTensor (highFrequencyPotential a b ψ ε)) i) 0 y = 0)) ↔
    ∀ v ∈ V, ∀ μ, waveOperator (a μ) (timeSpaceEquiv v) * cos (ψ (timeSpaceEquiv v) / ε) +
      waveOperator (b μ) (timeSpaceEquiv v) * sin (ψ (timeSpaceEquiv v) / ε) = 0 :=
  maxwell_highFrequencyPotential_iff_of_eikonal hV ha hb hψ hε hL heik htr

example {L S : ℝ × ℝ} {c : ℝ} (hc : c ≠ 0)
    (h : ∀ ε : ℝ, ε ≠ 0 → ε⁻¹ ^ 2 * trigValue L (c / ε) + ε⁻¹ * trigValue S (c / ε) = 0) :
    L = 0 ∧ S = 0 :=
  eq_zero_of_forall_trigValue hc h

example {a b : Fin 4 → ℝ × E3 → ℝ} {ψ : ℝ × E3 → ℝ} {v : Spacetime}
    (ha : ∀ μ, ContDiffAt ℝ 2 (a μ) (timeSpaceEquiv v))
    (hb : ∀ μ, ContDiffAt ℝ 2 (b μ) (timeSpaceEquiv v)) (hψ : ContDiffAt ℝ 2 ψ (timeSpaceEquiv v))
    (hψ0 : ψ (timeSpaceEquiv v) ≠ 0)
    (hne : ∃ μ, ((a μ (timeSpaceEquiv v), b μ (timeSpaceEquiv v)) : ℝ × ℝ) ≠ 0) :
    (∀ ε : ℝ, ε ≠ 0 → ∀ μ, box (potentialComponent (highFrequencyPotential a b ψ ε) μ) v =
        trigValue (zerothCoeff a b μ (timeSpaceEquiv v)) (ψ (timeSpaceEquiv v) / ε)) ↔
      wavePairing ψ ψ (timeSpaceEquiv v) = 0 ∧
        ∀ μ, transport (a μ) ψ (timeSpaceEquiv v) = 0 ∧
          transport (b μ) ψ (timeSpaceEquiv v) = 0 :=
  box_eq_zerothOrder_iff ha hb hψ hψ0 hne

example {ψ : ℝ × E3 → ℝ} {q : ℝ × E3} (hψ : ContDiffAt ℝ 2 ψ q) (w : ℝ × E3) :
    fderiv ℝ (wavePairing ψ ψ) q w =
      2 * (fderiv ℝ (timeDeriv ψ) q w * timeDeriv ψ q -
        ∑ i, fderiv ℝ (spaceDeriv i ψ) q w * spaceDeriv i ψ q) :=
  fderiv_wavePairing_self_apply hψ w

example {ψ : ℝ × E3 → ℝ} {q : ℝ × E3} (hψ : ContDiffAt ℝ 2 ψ q) :
    timeDeriv (wavePairing ψ ψ) q = 2 * wavePairing (timeDeriv ψ) ψ q :=
  timeDeriv_wavePairing_self hψ

example {ψ : ℝ × E3 → ℝ} {q : ℝ × E3} (hψ : ContDiffAt ℝ 2 ψ q) (j : Fin 3) :
    spaceDeriv j (wavePairing ψ ψ) q = 2 * wavePairing (spaceDeriv j ψ) ψ q :=
  spaceDeriv_wavePairing_self hψ j

example {ψ : ℝ × E3 → ℝ} {U : Set (ℝ × E3)} (hU : IsOpen U)
    (heik : ∀ q ∈ U, wavePairing ψ ψ q = 0) {q : ℝ × E3} (hq : q ∈ U) (hψ : ContDiffAt ℝ 2 ψ q) :
    wavePairing (timeDeriv ψ) ψ q = 0 ∧ ∀ j, wavePairing (spaceDeriv j ψ) ψ q = 0 :=
  wavePairing_deriv_eq_zero hU heik hq hψ

example {f ψ : ℝ × E3 → ℝ} {γ : ℝ → ℝ × E3} {s : ℝ} (hf : DifferentiableAt ℝ f (γ s))
    (hγ : HasDerivAt γ (raisedGradient ψ (γ s)) s) :
    HasDerivAt (fun r => f (γ r)) (wavePairing f ψ (γ s)) s :=
  hasDerivAt_comp_ray hf hγ

example {f ψ : ℝ × E3 → ℝ} {γ : ℝ → ℝ × E3} {s₀ s₁ : ℝ}
    (hf : ∀ s ∈ Icc s₀ s₁, DifferentiableAt ℝ f (γ s))
    (hγ : ∀ s ∈ Icc s₀ s₁, HasDerivAt γ (raisedGradient ψ (γ s)) s)
    (h0 : ∀ s ∈ Icc s₀ s₁, wavePairing f ψ (γ s) = 0) :
    ∀ s ∈ Icc s₀ s₁, f (γ s) = f (γ s₀) :=
  eq_of_isRay hf hγ h0

example {ψ : ℝ × E3 → ℝ} {U : Set (ℝ × E3)} (hU : IsOpen U) (hψ : ∀ q ∈ U, ContDiffAt ℝ 2 ψ q)
    (heik : ∀ q ∈ U, wavePairing ψ ψ q = 0) {γ : ℝ → ℝ × E3} {s₀ s₁ : ℝ}
    (hγU : ∀ s ∈ Icc s₀ s₁, γ s ∈ U)
    (hγ : ∀ s ∈ Icc s₀ s₁, HasDerivAt γ (raisedGradient ψ (γ s)) s) :
    ∀ s ∈ Icc s₀ s₁, raisedGradient ψ (γ s) = raisedGradient ψ (γ s₀) :=
  raisedGradient_eq_of_isRay hU hψ heik hγU hγ

example (ψ : ℝ × E3 → ℝ) (q : ℝ × E3) :
    intervalQuadratic (timeSpaceEquiv.symm (raisedGradient ψ q)) = wavePairing ψ ψ q :=
  intervalQuadratic_raisedGradient ψ q

example {ψ : ℝ × E3 → ℝ} {q : ℝ × E3} (heik : wavePairing ψ ψ q = 0)
    (hne : raisedGradient ψ q ≠ 0) :
    Lightlike (timeSpaceEquiv.symm (raisedGradient ψ q)) :=
  lightlike_raisedGradient heik hne

example {ψ : ℝ × E3 → ℝ} {U : Set (ℝ × E3)} (hU : IsOpen U) (hψ : ∀ q ∈ U, ContDiffAt ℝ 2 ψ q)
    (heik : ∀ q ∈ U, wavePairing ψ ψ q = 0) {γ : ℝ → ℝ × E3} {s₀ s₁ : ℝ}
    (hγU : ∀ s ∈ Icc s₀ s₁, γ s ∈ U)
    (hγ : ∀ s ∈ Icc s₀ s₁, HasDerivAt γ (raisedGradient ψ (γ s)) s)
    (hne : raisedGradient ψ (γ s₀) ≠ 0) :
    ∀ s ∈ Icc s₀ s₁, raisedGradient ψ (γ s) = raisedGradient ψ (γ s₀) ∧
      Lightlike (timeSpaceEquiv.symm (raisedGradient ψ (γ s))) :=
  lightlike_of_isRay hU hψ heik hγU hγ hne

example {a ψ : ℝ × E3 → ℝ} {γ : ℝ → ℝ × E3} {s : ℝ} (ha : DifferentiableAt ℝ a (γ s))
    (hγ : HasDerivAt γ (raisedGradient ψ (γ s)) s) (htr : transport a ψ (γ s) = 0) :
    HasDerivAt (fun r => a (γ r)) (-(a (γ s) * waveOperator ψ (γ s)) / 2) s :=
  hasDerivAt_comp_ray_of_transport ha hγ htr

example (ρ : ℝ × E3 → ℝ) (j : Fin 3 → ℝ × E3 → ℝ) (q : ℝ × E3) :
    ℝ :=
  currentDivergence ρ j q

example (a b : ℝ × E3 → ℝ) (q : ℝ × E3) :
    ℝ :=
  intensity a b q

example (a b ψ : ℝ × E3 → ℝ) (q : ℝ × E3) :
    ℝ :=
  intensityDensity a b ψ q

example (a b ψ : ℝ × E3 → ℝ) (i : Fin 3) (q : ℝ × E3) :
    ℝ :=
  intensityFlux a b ψ i q

example {a b : ℝ × E3 → ℝ} {q : ℝ × E3} (ha : DifferentiableAt ℝ a q)
    (hb : DifferentiableAt ℝ b q) :
    HasFDerivAt (intensity a b) (a q • fderiv ℝ a q + b q • fderiv ℝ b q) q :=
  hasFDerivAt_intensity ha hb

example {a b f : ℝ × E3 → ℝ} {q : ℝ × E3} (ha : DifferentiableAt ℝ a q)
    (hb : DifferentiableAt ℝ b q) (hf : DifferentiableAt ℝ f q) (w : ℝ × E3) :
    fderiv ℝ (fun p => intensity a b p * f p) q w =
      intensity a b q * fderiv ℝ f q w +
        f q * (a q * fderiv ℝ a q w + b q * fderiv ℝ b q w) :=
  fderiv_intensity_mul_apply ha hb hf w

example {a b ψ : ℝ × E3 → ℝ} {q : ℝ × E3} (ha : DifferentiableAt ℝ a q)
    (hb : DifferentiableAt ℝ b q) (hψ : ContDiffAt ℝ 2 ψ q) :
    currentDivergence (intensityDensity a b ψ) (intensityFlux a b ψ) q =
      (a q * transport a ψ q + b q * transport b ψ q) / 2 :=
  currentDivergence_intensity ha hb hψ

example {a b ψ : ℝ × E3 → ℝ} {q : ℝ × E3} (ha : DifferentiableAt ℝ a q)
    (hb : DifferentiableAt ℝ b q) (hψ : ContDiffAt ℝ 2 ψ q) (hta : transport a ψ q = 0)
    (htb : transport b ψ q = 0) :
    currentDivergence (intensityDensity a b ψ) (intensityFlux a b ψ) q = 0 :=
  divergence_intensityCurrent_eq_zero ha hb hψ hta htb

example {a b : Fin 4 → ℝ × E3 → ℝ} {ψ : ℝ × E3 → ℝ} {q : ℝ × E3}
    (ha : ∀ μ, DifferentiableAt ℝ (a μ) q) (hb : ∀ μ, DifferentiableAt ℝ (b μ) q)
    (hψ : ContDiffAt ℝ 2 ψ q) (htr : ∀ μ, transport (a μ) ψ q = 0 ∧ transport (b μ) ψ q = 0) :
    currentDivergence (fun p => ∑ μ, intensityDensity (a μ) (b μ) ψ p)
      (fun i p => ∑ μ, intensityFlux (a μ) (b μ) ψ i p) q = 0 :=
  divergence_totalIntensityCurrent_eq_zero ha hb hψ htr

example {I : E3 → ℝ} {X : E3 → E3} {y : E3} (hI : DifferentiableAt ℝ I y)
    (hX : DifferentiableAt ℝ X y) :
    traceCLM (fderiv ℝ (fun z => I z • X z) y) =
      fderiv ℝ I y (X y) + I y * traceCLM (fderiv ℝ X y) :=
  traceCLM_fderiv_smul hI hX

example {X : E3 → E3} {Φ : ℝ × E3 → E3} {Ω : Set (ℝ × E3)} (hflow : IsLocalFlowOn X Φ Ω)
    (hX : ContDiff ℝ 1 X) {U : Set E3} {I : E3 → ℝ} (hI : ∀ y ∈ U, DifferentiableAt ℝ I y)
    (hdiv : ∀ y ∈ U, traceCLM (fderiv ℝ (fun z => I z • X z) y) = 0) {t : ℝ} {x : E3}
    (hp : (t, x) ∈ Ω) (horb : ∀ s ∈ uIcc 0 t, Φ (s, x) ∈ U) :
    I (Φ (t, x)) * LinearMap.det (fderiv ℝ (fun y => Φ (t, y)) x : E3 →ₗ[ℝ] E3) = I x :=
  intensity_mul_det_eq hflow hX hI hdiv hp horb

example (c : ℝ) (q : ℝ × E3) :
    timeDeriv (fun _ => c) q = 0 :=
  timeDeriv_const c q

example (c : ℝ) (i : Fin 3) (q : ℝ × E3) :
    spaceDeriv i (fun _ => c) q = 0 :=
  spaceDeriv_const c i q

example (c : ℝ) (q : ℝ × E3) :
    waveOperator (fun _ => c) q = 0 :=
  waveOperator_const c q

example (c : ℝ) (ψ : ℝ × E3 → ℝ) (q : ℝ × E3) :
    wavePairing (fun _ => c) ψ q = 0 :=
  wavePairing_const c ψ q

example (c : ℝ) (ψ : ℝ × E3 → ℝ) (q : ℝ × E3) :
    transport (fun _ => c) ψ q = c * waveOperator ψ q :=
  transport_const c ψ q

example (L : ℝ × E3 →L[ℝ] ℝ) (q : ℝ × E3) :
    timeDeriv L q = L (1, 0) :=
  timeDeriv_clm L q

example (L : ℝ × E3 →L[ℝ] ℝ) (i : Fin 3) (q : ℝ × E3) :
    spaceDeriv i L q = L (0, EuclideanSpace.single i 1) :=
  spaceDeriv_clm L i q

example (L : ℝ × E3 →L[ℝ] ℝ) (q : ℝ × E3) :
    waveOperator L q = 0 :=
  waveOperator_clm L q

example :
    ℝ × E3 →L[ℝ] ℝ :=
  planePhase

example (q : ℝ × E3) :
    timeDeriv planePhase q = 1 :=
  timeDeriv_planePhase q

example (i : Fin 3) (q : ℝ × E3) :
    spaceDeriv i planePhase q = -if i = 0 then 1 else 0 :=
  spaceDeriv_planePhase i q

example (q : ℝ × E3) :
    wavePairing planePhase planePhase q = 0 :=
  wavePairing_planePhase q

example (q : ℝ × E3) :
    raisedGradient planePhase q = (1, EuclideanSpace.single 0 1) :=
  raisedGradient_planePhase q

example (s : ℝ) :
    ℝ × E3 :=
  planeRay s

example (s : ℝ) :
    HasDerivAt planeRay (raisedGradient planePhase (planeRay s)) s :=
  hasDerivAt_planeRay s

example (q : ℝ × E3) :
    ℝ :=
  sphericalPhase q

example (q : ℝ × E3) :
    ℝ :=
  sphericalAmplitude q

example {q : ℝ × E3} (hq : q.2 ≠ 0) :
    HasFDerivAt (fun p : ℝ × E3 => ‖p.2‖)
      ((‖q.2‖⁻¹ • innerSL ℝ q.2).comp (ContinuousLinearMap.snd ℝ ℝ E3)) q :=
  hasFDerivAt_norm_snd hq

example {q : ℝ × E3} (hq : q.2 ≠ 0) (w : ℝ × E3) :
    fderiv ℝ sphericalPhase q w = w.1 - ‖q.2‖⁻¹ * inner ℝ q.2 w.2 :=
  fderiv_sphericalPhase_apply hq w

example {q : ℝ × E3} (hq : q.2 ≠ 0) (w : ℝ × E3) :
    fderiv ℝ sphericalAmplitude q w = -((‖q.2‖ ^ 3)⁻¹ * inner ℝ q.2 w.2) :=
  fderiv_sphericalAmplitude_apply hq w

example {q : ℝ × E3} (hq : q.2 ≠ 0) :
    timeDeriv sphericalPhase q = 1 :=
  timeDeriv_sphericalPhase hq

example {q : ℝ × E3} (hq : q.2 ≠ 0) (i : Fin 3) :
    spaceDeriv i sphericalPhase q = -(sphericalAmplitude q * q.2 i) :=
  spaceDeriv_sphericalPhase hq i

example {q : ℝ × E3} (hq : q.2 ≠ 0) :
    timeDeriv sphericalAmplitude q = 0 :=
  timeDeriv_sphericalAmplitude hq

example {q : ℝ × E3} (hq : q.2 ≠ 0) (i : Fin 3) :
    spaceDeriv i sphericalAmplitude q = -((‖q.2‖ ^ 3)⁻¹ * q.2 i) :=
  spaceDeriv_sphericalAmplitude hq i

example :
    IsOpen {q : ℝ × E3 | q.2 ≠ 0} :=
  isOpen_ne_zero_snd

example {n : ℕ∞ω} {q : ℝ × E3} (hq : q.2 ≠ 0) :
    ContDiffAt ℝ n sphericalPhase q :=
  contDiffAt_sphericalPhase hq

example {n : ℕ∞ω} {q : ℝ × E3} (hq : q.2 ≠ 0) :
    ContDiffAt ℝ n sphericalAmplitude q :=
  contDiffAt_sphericalAmplitude hq

example (q : ℝ × E3) :
    q.2 0 ^ 2 + q.2 1 ^ 2 + q.2 2 ^ 2 = ‖q.2‖ ^ 2 :=
  sum_sq_snd q

example {q : ℝ × E3} (hq : q.2 ≠ 0) :
    wavePairing sphericalPhase sphericalPhase q = 0 :=
  wavePairing_sphericalPhase hq

example {q : ℝ × E3} (hq : q.2 ≠ 0) :
    waveOperator sphericalPhase q = 2 * sphericalAmplitude q :=
  waveOperator_sphericalPhase hq

example {q : ℝ × E3} (hq : q.2 ≠ 0) :
    transport sphericalAmplitude sphericalPhase q = 0 :=
  transport_sphericalAmplitude hq

example (α β : Fin 4 → ℝ) (ε : ℝ) :
    Potential :=
  planeWavePotential α β ε

example (α : Fin 4 → ℝ) (q : ℝ × E3) :
    amplitudePairing (fun μ _ => α μ) planePhase q = -(α 0 + α 1) :=
  amplitudePairing_planePhase α q

example (α : Fin 4 → ℝ) (q : ℝ × E3) :
    amplitudeDivergence (fun μ _ => α μ) q = 0 :=
  amplitudeDivergence_const α q

example {α β : Fin 4 → ℝ} (hα : α 0 + α 1 = 0) (hβ : β 0 + β 1 = 0) (ε : ℝ) (v : Spacetime) :
    lorenzDivergence (planeWavePotential α β ε) v = 0 :=
  lorenzDivergence_planeWavePotential hα hβ ε v

example (α β : Fin 4 → ℝ) :
    ∀ q ∈ (univ : Set (ℝ × E3)), ∀ μ, leadingCoeff (fun μ _ => α μ) (fun μ _ => β μ)
      planePhase μ q = 0 ∧ subleadingCoeff (fun μ _ => α μ) (fun μ _ => β μ) planePhase μ q = 0 :=
  leadingOrders_planeWave α β

example {α β : Fin 4 → ℝ} (hα : α 0 + α 1 = 0) (hβ : β 0 + β 1 = 0) {ε : ℝ} (hε : ε ≠ 0) :
    ∀ y ∈ (univ : Set Spacetime),
      (divergence3 (magneticField (fieldTensor (planeWavePotential α β ε))) y = 0 ∧
        ∀ i, partialAt (magneticField (fieldTensor (planeWavePotential α β ε)) i) 0 y +
          curl (electricField (fieldTensor (planeWavePotential α β ε))) y i = 0) ∧
      (divergence3 (electricField (fieldTensor (planeWavePotential α β ε))) y = 0 ∧
        ∀ i, curl (magneticField (fieldTensor (planeWavePotential α β ε))) y i -
          partialAt (electricField (fieldTensor (planeWavePotential α β ε)) i) 0 y = 0) :=
  maxwell_planeWavePotential hα hβ hε

example :
    ∀ ε : ℝ, ε ≠ 0 → ∀ μ, box (potentialComponent (highFrequencyPotential
        (fun μ _ => (Pi.single 2 1 : Fin 4 → ℝ) μ) (fun _ _ => 0) planePhase ε) μ)
        (Pi.single 0 1) =
      trigValue (zerothCoeff (fun μ _ => (Pi.single 2 1 : Fin 4 → ℝ) μ) (fun _ _ => 0) μ
        (timeSpaceEquiv (Pi.single 0 1))) (planePhase (timeSpaceEquiv (Pi.single 0 1)) / ε) :=
  box_planeWave_eq_zerothOrder

example {s₀ s₁ : ℝ} :
    ∀ s ∈ Icc s₀ s₁, raisedGradient planePhase (planeRay s) =
        raisedGradient planePhase (planeRay s₀) ∧
      Lightlike (timeSpaceEquiv.symm (raisedGradient planePhase (planeRay s))) :=
  lightlike_planeRay

example {q : ℝ × E3} (hq : q.2 ≠ 0) :
    currentDivergence (intensityDensity sphericalAmplitude (fun _ => 0) sphericalPhase)
      (intensityFlux sphericalAmplitude (fun _ => 0) sphericalPhase) q = 0 :=
  divergence_intensityCurrent_spherical hq

example (n : E3) (s : ℝ) :
    ℝ × E3 :=
  sphericalRay n s

example {n : E3} (hn : ‖n‖ = 1) {s : ℝ} (hs : -1 < s) :
    (sphericalRay n s).2 ≠ 0 :=
  sphericalRay_snd_ne_zero hn hs

example {n : E3} (hn : ‖n‖ = 1) {s : ℝ} (hs : -1 < s) :
    raisedGradient sphericalPhase (sphericalRay n s) = (1, n) :=
  raisedGradient_sphericalRay hn hs

example {n : E3} (hn : ‖n‖ = 1) {s : ℝ} (hs : -1 < s) :
    HasDerivAt (sphericalRay n) (raisedGradient sphericalPhase (sphericalRay n s)) s :=
  hasDerivAt_sphericalRay hn hs

example {n : E3} (hn : ‖n‖ = 1) {s₀ s₁ : ℝ} (hs₀ : -1 < s₀) :
    ∀ s ∈ Icc s₀ s₁, raisedGradient sphericalPhase (sphericalRay n s) =
        raisedGradient sphericalPhase (sphericalRay n s₀) ∧
      Lightlike (timeSpaceEquiv.symm (raisedGradient sphericalPhase (sphericalRay n s))) :=
  lightlike_sphericalRay hn hs₀

example {n : E3} (hn : ‖n‖ = 1) {s : ℝ} (hs : -1 < s) :
    HasDerivAt (fun r => sphericalAmplitude (sphericalRay n r))
      (-(sphericalAmplitude (sphericalRay n s) *
        waveOperator sphericalPhase (sphericalRay n s)) / 2) s :=
  hasDerivAt_sphericalAmplitude_ray hn hs

example :
    IsLocalFlowOn (fun x : E3 => x) (fun p : ℝ × E3 => Real.exp p.1 • p.2) univ :=
  isLocalFlowOn_radial

example {y : E3} (hy : y ≠ 0) :
    traceCLM (fderiv ℝ (fun z : E3 => (‖z‖ ^ 3)⁻¹ • z) y) = 0 :=
  traceCLM_fderiv_radial hy

example (t : ℝ) {x : E3} (hx : x ≠ 0) :
    (‖Real.exp t • x‖ ^ 3)⁻¹ *
        LinearMap.det (fderiv ℝ (fun y : E3 => Real.exp t • y) x : E3 →ₗ[ℝ] E3) =
      (‖x‖ ^ 3)⁻¹ :=
  intensity_mul_det_radial t hx

end ProjectAinos.Electrodynamics.Optics.Eikonal

end Eikonal

section RayOptics

open Set

namespace ProjectAinos.Electrodynamics.Optics.RayOptics

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace Mechanics Mechanics.CompleteIntegral

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (nsq : FreeSmoothRing (Fin 3)) :
    PhaseSpace (Fin 3) :=
  rayHamiltonian nsq

example (nsq : FreeSmoothRing (Fin 3)) (c : Fin 3 ⊕ Fin 3 → TimeFunction) :
    IsTrajectory (canonical (Fin 3)) (rayHamiltonian nsq) c ↔
      (∀ i, timeDerivative (c (Sum.inl i)) = c (Sum.inr i)) ∧
      ∀ i, timeDerivative (c (Sum.inr i)) = algebraMap ℝ TimeFunction (1 / 2) *
        FreeSmoothRing.lift (fun k => c (Sum.inl k)) (partialDerivation i nsq) :=
  isTrajectory_rayHamiltonian_iff nsq c

example {nsq : FreeSmoothRing (Fin 3)} {c : Fin 3 ⊕ Fin 3 → TimeFunction}
    (h : IsTrajectory (canonical (Fin 3)) (rayHamiltonian nsq) c) (i : Fin 3) :
    timeDerivative (timeDerivative (c (Sum.inl i))) = algebraMap ℝ TimeFunction (1 / 2) *
      FreeSmoothRing.lift (fun k => c (Sum.inl k)) (partialDerivation i nsq) :=
  timeDerivative_timeDerivative_of_isTrajectory h i

example {nsq : FreeSmoothRing (Fin 3)} {S : ActionSpace (Fin 3)}
    (hS : IsHamiltonJacobi (rayHamiltonian nsq) S) {Q : Fin 3 → TimeFunction} {α : Fin 3 → ℝ}
    (hβ : ∀ i, timeDerivative (along Q α (partialDerivation (αIndex i) S)) = 0)
    (hnd : ∀ w : Fin 3 → TimeFunction,
      (∀ i, ∑ k, along Q α (partialDerivation (αIndex i) (partialDerivation (qIndex k) S)) *
        w k = 0) → ∀ k, w k = 0) :
    (∀ i, timeDerivative (Q i) = momentum S Q α i) ∧
      ∀ i, timeDerivative (timeDerivative (Q i)) = algebraMap ℝ TimeFunction (1 / 2) *
        FreeSmoothRing.lift Q (partialDerivation i nsq) :=
  isRay_of_isHamiltonJacobi hS hβ hnd

example :
    ActionSpace (Fin 3) :=
  rayTime

example (i : Fin 3) :
    ActionSpace (Fin 3) :=
  rayPosition i

example (k : Fin 3) :
    partialDerivation (qIndex k) rayTime = 0 :=
  partialDerivation_q_rayTime k

example (k : Fin 3) :
    partialDerivation (αIndex k) rayTime = 0 :=
  partialDerivation_α_rayTime k

example :
    partialDerivation (tIndex : Fin 3 ⊕ Fin 3 ⊕ Unit) rayTime = 1 :=
  partialDerivation_t_rayTime

example (k i : Fin 3) :
    partialDerivation (qIndex k) (rayPosition i) = if i = k then 1 else 0 :=
  partialDerivation_q_rayPosition k i

example (k i : Fin 3) :
    partialDerivation (αIndex k) (rayPosition i) = 0 :=
  partialDerivation_α_rayPosition k i

example (i : Fin 3) :
    partialDerivation (tIndex : Fin 3 ⊕ Fin 3 ⊕ Unit) (rayPosition i) = 0 :=
  partialDerivation_t_rayPosition i

example (k i : Fin 3) :
    partialDerivation (qIndex k) (parameter i) = 0 :=
  partialDerivation_q_parameter k i

example (k i : Fin 3) :
    partialDerivation (αIndex k) (parameter i) = if i = k then 1 else 0 :=
  partialDerivation_α_parameter k i

example (i : Fin 3) :
    partialDerivation (tIndex : Fin 3 ⊕ Fin 3 ⊕ Unit) (parameter i) = 0 :=
  partialDerivation_t_parameter i

example (n0sq g : ℝ) :
    FreeSmoothRing (Fin 3) :=
  linearIndexSq n0sq g

example (nsq : ℝ) :
    ActionSpace (Fin 3) :=
  constantIndexAction nsq

example (n0sq g : ℝ) :
    ActionSpace (Fin 3) :=
  linearIndexAction n0sq g

example (n0sq g : ℝ) (k : Fin 3) :
    partialDerivation (qIndex k) (linearIndexAction n0sq g) =
      parameter k + if k = 2 then algebraMap ℝ (ActionSpace (Fin 3)) g * rayTime else 0 :=
  partialDerivation_q_linearIndexAction n0sq g k

example (n0sq g : ℝ) :
    partialDerivation (tIndex : Fin 3 ⊕ Fin 3 ⊕ Unit) (linearIndexAction n0sq g) =
      algebraMap ℝ (ActionSpace (Fin 3)) g * rayPosition 2 -
        algebraMap ℝ (ActionSpace (Fin 3)) (1 / 2) *
          (∑ i, parameter i * parameter i - algebraMap ℝ (ActionSpace (Fin 3)) n0sq) -
        algebraMap ℝ (ActionSpace (Fin 3)) (1 / 2) * algebraMap ℝ (ActionSpace (Fin 3)) g *
          (parameter 2 * (rayTime + rayTime)) -
        algebraMap ℝ (ActionSpace (Fin 3)) (1 / 2) * algebraMap ℝ (ActionSpace (Fin 3)) (1 / 3) *
          (algebraMap ℝ (ActionSpace (Fin 3)) g * algebraMap ℝ (ActionSpace (Fin 3)) g) *
          (3 * (rayTime * rayTime)) :=
  partialDerivation_t_linearIndexAction n0sq g

example (n0sq g : ℝ) (k : Fin 3) :
    partialDerivation (αIndex k) (linearIndexAction n0sq g) =
      rayPosition k -
        algebraMap ℝ (ActionSpace (Fin 3)) (1 / 2) * (parameter k + parameter k) * rayTime -
        if k = 2 then algebraMap ℝ (ActionSpace (Fin 3)) (1 / 2) *
          algebraMap ℝ (ActionSpace (Fin 3)) g * (rayTime * rayTime) else 0 :=
  partialDerivation_α_linearIndexAction n0sq g k

example (n0sq g : ℝ) :
    IsHamiltonJacobi (rayHamiltonian (linearIndexSq n0sq g)) (linearIndexAction n0sq g) :=
  isHamiltonJacobi_linearIndex n0sq g

example (g : ℝ) (α β : Fin 3 → ℝ) (k : Fin 3) :
    TimeFunction :=
  linearIndexRay g α β k

example (Q : Fin 3 → TimeFunction) (α : Fin 3 → ℝ) (k : Fin 3) :
    along Q α (rayPosition k) = Q k :=
  along_rayPosition Q α k

example (Q : Fin 3 → TimeFunction) (α : Fin 3 → ℝ) (k : Fin 3) :
    along Q α (parameter k) = algebraMap ℝ TimeFunction (α k) :=
  along_parameter Q α k

example (Q : Fin 3 → TimeFunction) (α : Fin 3 → ℝ) :
    along Q α rayTime = TimeFunction.time :=
  along_rayTime Q α

example (n0sq g : ℝ) (α β : Fin 3 → ℝ) (k : Fin 3) :
    along (linearIndexRay g α β) α (partialDerivation (αIndex k) (linearIndexAction n0sq g)) =
      algebraMap ℝ TimeFunction (β k) :=
  along_partialDerivation_α_linearIndexAction n0sq g α β k

example (n0sq g : ℝ) (i k : Fin 3) :
    partialDerivation (αIndex i) (partialDerivation (qIndex k) (linearIndexAction n0sq g)) =
      if k = i then 1 else 0 :=
  partialDerivation_α_q_linearIndexAction n0sq g i k

example (n0sq g : ℝ) (α β : Fin 3 → ℝ) :
    IsTrajectory (canonical (Fin 3)) (rayHamiltonian (linearIndexSq n0sq g))
      (Sum.elim (linearIndexRay g α β)
        (momentum (linearIndexAction n0sq g) (linearIndexRay g α β) α)) :=
  isTrajectory_linearIndexRay n0sq g α β

example (n0sq g : ℝ) (i : Fin 3) :
    partialDerivation i (linearIndexSq n0sq g) =
      if i = 2 then algebraMap ℝ (FreeSmoothRing (Fin 3)) (2 * g) else 0 :=
  partialDerivation_linearIndexSq n0sq g i

example (n0sq g : ℝ) (α β : Fin 3 → ℝ) (i : Fin 3) :
    timeDerivative (timeDerivative (linearIndexRay g α β i)) =
      if i = 2 then algebraMap ℝ TimeFunction g else 0 :=
  timeDerivative_timeDerivative_linearIndexRay n0sq g α β i

example (nsq : ℝ) :
    linearIndexSq nsq 0 = algebraMap ℝ (FreeSmoothRing (Fin 3)) nsq :=
  linearIndexSq_zero nsq

example (nsq : ℝ) :
    linearIndexAction nsq 0 = constantIndexAction nsq :=
  linearIndexAction_zero nsq

example (nsq : ℝ) :
    IsHamiltonJacobi (rayHamiltonian (algebraMap ℝ (FreeSmoothRing (Fin 3)) nsq))
      (constantIndexAction nsq) :=
  isHamiltonJacobi_constantIndex nsq

example (α β : Fin 3 → ℝ) (k : Fin 3) :
    TimeFunction :=
  constantIndexRay α β k

example (α β : Fin 3 → ℝ) :
    linearIndexRay 0 α β = constantIndexRay α β :=
  linearIndexRay_zero α β

example (nsq : ℝ) (α β : Fin 3 → ℝ) :
    IsTrajectory (canonical (Fin 3)) (rayHamiltonian (algebraMap ℝ (FreeSmoothRing (Fin 3)) nsq))
      (Sum.elim (constantIndexRay α β)
        (momentum (constantIndexAction nsq) (constantIndexRay α β) α)) :=
  isTrajectory_constantIndexRay nsq α β

example (z : E3 × E3) :
    ℝ :=
  rayKinetic z

example (n : E3 → ℝ) (x : E3) :
    ℝ :=
  rayPotential n x

example (n : E3 → ℝ) :
    Lagrangian E3 :=
  opticalLagrangian n

example (n : E3 → ℝ) (γ : ℝ → E3) (a b : ℝ) :
    action a b (opticalLagrangian n) γ = opticalLength n γ a b :=
  action_opticalLagrangian n γ a b

example (n : E3 → ℝ) (a b : ℝ) (γ : ℝ → E3) :
    Prop :=
  OpticalStationary n a b γ

example (n : E3 → ℝ) (a b : ℝ) (γ : ℝ → E3) :
    OpticalStationary n a b γ ↔ Stationary a b (opticalLagrangian n) γ :=
  opticalStationary_iff n a b γ

example {n : E3 → ℝ} (hn : ∀ x, 0 ≤ n x) :
    Maupertuis.jacobiLength rayKinetic (rayPotential n) 0 = opticalLagrangian n :=
  jacobiLength_eq_opticalLagrangian hn

example :
    ContDiff ℝ 2 rayKinetic :=
  contDiff_rayKinetic

example {n : E3 → ℝ} (hn : ContDiff ℝ 2 n) :
    ContDiff ℝ 2 (rayPotential n) :=
  contDiff_rayPotential hn

example {n : E3 → ℝ} (hn : ContDiff ℝ 2 n) {γ : ℝ → E3} (hγ : ContDiff ℝ 2 γ) (t : ℝ) :
    eulerLagrange (Maupertuis.naturalLagrangian rayKinetic (rayPotential n)) γ t = 0 ↔
      deriv (deriv γ) t = gradient (fun x => n x ^ 2 / 2) (γ t) :=
  eulerLagrange_ray_eq_zero_iff hn hγ t

example {n : E3 → ℝ} (hn : ContDiff ℝ 2 n) (hpos : ∀ x, 0 < n x) {γ : ℝ → E3}
    (hγ : ContDiff ℝ 2 γ) {a b : ℝ} (hab : a < b) (hE : ∀ t ∈ Icc a b, ‖deriv γ t‖ = n (γ t)) :
    OpticalStationary n a b γ ↔
      ∀ t ∈ Ioo a b, deriv (deriv γ) t = gradient (fun x => n x ^ 2 / 2) (γ t) :=
  fermat hn hpos hγ hab hE

example {n₀ : ℝ} (hn₀ : 0 < n₀) (x₀ v : E3) (hv : ‖v‖ = n₀) {a b : ℝ} (hab : a < b) :
    OpticalStationary (fun _ => n₀) a b fun t => x₀ + t • v :=
  opticalStationary_line hn₀ x₀ v hv hab

end ProjectAinos.Electrodynamics.Optics.RayOptics

end RayOptics

section Energy

open MeasureTheory Filter Set Metric Real

open scoped Topology

namespace ProjectAinos.SmoothGeometry.Wave

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (f : ℝ × E3 → ℝ) (p : ℝ × E3) :
    ℝ :=
  gradNormSq f p

example (f g : ℝ × E3 → ℝ) (p : ℝ × E3) :
    ℝ :=
  gradInner f g p

example (f : ℝ × E3 → ℝ) (p : ℝ × E3) :
    gradNormSq f p = gradInner f f p :=
  gradNormSq_eq_gradInner f p

example (w : ℝ × E3 → ℝ) (t : ℝ) :
    ℝ :=
  energy w t

example (f : ℝ × E3 → ℝ) (t : ℝ) :
    ℝ :=
  spatialL2Norm f t

example (f : ℝ × E3 → ℝ) (p : ℝ × E3) :
    0 ≤ gradNormSq f p :=
  gradNormSq_nonneg f p

example (w : ℝ × E3 → ℝ) (t : ℝ) :
    0 ≤ energy w t :=
  energy_nonneg w t

example (f : ℝ × E3 → ℝ) (t : ℝ) :
    0 ≤ spatialL2Norm f t :=
  spatialL2Norm_nonneg f t

example {f : ℝ × E3 → ℝ} {s : ℝ} {x : E3} (hf : DifferentiableAt ℝ f (s, x)) :
    HasFDerivAt (fun y => f (s, y))
      ((fderiv ℝ f (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ E3)) x :=
  hasFDerivAt_spaceSlice hf

example {f : ℝ × E3 → ℝ} {s : ℝ} {x : E3} (hf : DifferentiableAt ℝ f (s, x)) (i : Fin 3) :
    fderiv ℝ (fun y => f (s, y)) x (EuclideanSpace.single i 1) = spaceDeriv i f (s, x) :=
  fderiv_spaceSlice hf i

example (T R : ℝ) (f : ℝ × E3 → ℝ) :
    Prop :=
  BallSupportOn T R f

example {a : ℝ} {f : ℝ × E3 → ℝ} (hf : LocalizedSupport a f) (T : ℝ) :
    BallSupportOn T a f :=
  LocalizedSupport.ballSupportOn hf T

example {T T' R R' : ℝ} {f : ℝ × E3 → ℝ} (hf : BallSupportOn T R f) (hT : T' ≤ T) (hR : R ≤ R') :
    BallSupportOn T' R' f :=
  BallSupportOn.mono hf hT hR

example {T R : ℝ} {g : ℝ × E3 → ℝ} (hg : BallSupportOn T R g) (f : ℝ × E3 → ℝ) :
    BallSupportOn T R fun p => f p * g p :=
  BallSupportOn.mul_left hg f

example {T R : ℝ} {g : ℝ × E3 → ℝ} (hg : BallSupportOn T R g) (f : ℝ × E3 → ℝ) :
    BallSupportOn T R fun p => g p * f p :=
  BallSupportOn.mul_right hg f

example {T R : ℝ} {f g : ℝ × E3 → ℝ} (hf : BallSupportOn T R f) (hg : BallSupportOn T R g) :
    BallSupportOn T R fun p => f p + g p :=
  BallSupportOn.add hf hg

example {T R : ℝ} {f g : ℝ × E3 → ℝ} (hf : BallSupportOn T R f) (hg : BallSupportOn T R g) :
    BallSupportOn T R fun p => f p - g p :=
  BallSupportOn.sub hf hg

example {T R : ℝ} {f : ℝ × E3 → ℝ} (hf : BallSupportOn T R f) {n : ℕ} (hn : n ≠ 0) :
    BallSupportOn T R fun p => f p ^ n :=
  BallSupportOn.pow hf hn

example {T R : ℝ} {f : ℝ × E3 → ℝ} (hf : BallSupportOn T R f) {s : ℝ} (hs : s ∈ Ioo 0 T) {y : E3}
    (hy : R < ‖y‖) :
    fderiv ℝ f (s, y) = 0 :=
  BallSupportOn.fderiv_eq_zero hf hs hy

example {T R : ℝ} {f : ℝ × E3 → ℝ} (hT : 0 < T) (hc : Continuous f)
    (h : ∀ s ∈ Ioo 0 T, ∀ y : E3, R < ‖y‖ → f (s, y) = 0) :
    BallSupportOn T R f :=
  BallSupportOn.of_Ioo hT hc h

example {T R : ℝ} {f : ℝ × E3 → ℝ} (hT : 0 < T) (hf : ContDiff ℝ 1 f) (h : BallSupportOn T R f) :
    BallSupportOn T R (timeDeriv f) :=
  BallSupportOn.timeDeriv hT hf h

example {T R : ℝ} {f : ℝ × E3 → ℝ} (hf : Differentiable ℝ f) (h : BallSupportOn T R f) (i : Fin 3) :
    BallSupportOn T R (spaceDeriv i f) :=
  BallSupportOn.spaceDeriv hf h i

example {T R : ℝ} {f : ℝ × E3 → ℝ} (hT : 0 < T) (hf : ContDiff ℝ 2 f) (h : BallSupportOn T R f) :
    BallSupportOn T R (waveOperator f) :=
  BallSupportOn.waveOperator hT hf h

example {f g : ℝ × E3 → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    Continuous (gradInner f g) :=
  continuous_gradInner hf hg

example {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (gradNormSq f) :=
  continuous_gradNormSq hf

example {T R : ℝ} {f : ℝ × E3 → ℝ} (hT : 0 < T) (hf : ContDiff ℝ 1 f) (h : BallSupportOn T R f)
    (g : ℝ × E3 → ℝ) :
    BallSupportOn T R (gradInner f g) :=
  BallSupportOn.gradInner_left hT hf h g

example {T R : ℝ} {f : ℝ × E3 → ℝ} (hT : 0 < T) (hf : ContDiff ℝ 1 f) (h : BallSupportOn T R f) :
    BallSupportOn T R (gradNormSq f) :=
  BallSupportOn.gradNormSq hT hf h

example {T R : ℝ} {f : ℝ × E3 → ℝ} (hc : Continuous f) (h : BallSupportOn T R f) {s : ℝ}
    (hs : s ∈ Icc 0 T) :
    Integrable fun x : E3 => f (s, x) :=
  BallSupportOn.integrable hc h hs

example {T R : ℝ} {f : ℝ × E3 → ℝ} (hc : Continuous f) (h : BallSupportOn T R f) :
    ContinuousOn (fun s => ∫ x, f (s, x)) (Icc 0 T) :=
  BallSupportOn.continuousOn_integral hc h

example {T R : ℝ} {f f' : ℝ × E3 → ℝ} (hc : Continuous f) (hc' : Continuous f')
    (hd : ∀ (s : ℝ) (x : E3), HasDerivAt (fun r => f (r, x)) (f' (s, x)) s)
    (h : BallSupportOn T R f) (h' : BallSupportOn T R f') {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => ∫ x, f (s, x)) (∫ x, f' (t, x)) t :=
  BallSupportOn.hasDerivAt_integral hc hc' hd h h' ht

example {f g : ℝ × E3 → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) {T R : ℝ}
    (h : BallSupportOn T R f) {s : ℝ} (hs : s ∈ Icc 0 T) (i : Fin 3) :
    ∫ x, f (s, x) * spaceDeriv i g (s, x) = -∫ x, spaceDeriv i f (s, x) * g (s, x) :=
  integral_mul_spaceDeriv_eq_neg hf hg h hs i

example {w : ℝ × E3 → ℝ} (hw : ContDiff ℝ 2 w) {T R : ℝ} (hT : 0 < T) (h : BallSupportOn T R w)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (energy w) (∫ x, timeDeriv w (t, x) * waveOperator w (t, x)) t :=
  hasDerivAt_energy hw hT h ht

example {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : Integrable (fun x => f x ^ 2) μ) (hg : Integrable (fun x => g x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    |∫ x, f x * g x ∂μ| ≤ √(∫ x, f x ^ 2 ∂μ) * √(∫ x, g x ^ 2 ∂μ) :=
  abs_integral_mul_le_sqrt hf hg hfg

example {w : ℝ × E3 → ℝ} (hw : ContDiff ℝ 2 w) {T R : ℝ} (h : BallSupportOn T R w) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    √(2 * energy w t) ≤ √(2 * energy w 0) + ∫ s in 0..t, spatialL2Norm (waveOperator w) s :=
  sqrt_two_mul_energy_le hw h ht

example {w : ℝ × E3 → ℝ} (hw : ContDiff ℝ 2 w) {T R : ℝ} (h : BallSupportOn T R w) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    √(energy w t) ≤ √(energy w 0) + ∫ s in 0..t, spatialL2Norm (waveOperator w) s :=
  sqrt_energy_le hw h ht

example {T t : ℝ} (ht : t ∈ Icc 0 T) :
    √(energy (fun p : ℝ × E3 => cos p.1 * spaceBump p.2) t) ≤
      √(energy (fun p : ℝ × E3 => cos p.1 * spaceBump p.2) 0) +
        ∫ s in 0..t, spatialL2Norm (waveOperator fun p : ℝ × E3 => cos p.1 * spaceBump p.2) s :=
  sqrt_energy_le_bump ht

end ProjectAinos.SmoothGeometry.Wave

end Energy

section Error

open MeasureTheory Filter Set Metric Real

open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics.Optics.Limits

open SmoothGeometry SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example {a : ℝ × E3 → ℝ} (ψ : ℝ × E3 → ℝ) {p : ℝ × E3} (hp : p ∉ tsupport a) :
    Wave.transport a ψ p = 0 :=
  transport_eq_zero_of_notMem ψ hp

example {T : ℝ} {a b ψ : ℝ × E3 → ℝ} (h : IsGeometricalOptics T a b ψ) (ha : ContDiff ℝ 2 a)
    (hb : ContDiff ℝ 2 b) (hψ : ContDiff ℝ 2 ψ) {ε : ℝ} (hε : ε ≠ 0) {p : ℝ × E3}
    (hp : p.1 ∈ Icc 0 T) :
    Wave.waveOperator (Wave.highFrequencyWave a b ψ ε) p =
      Wave.waveOperator a p * cos (ψ p / ε) + Wave.waveOperator b p * sin (ψ p / ε) :=
  IsGeometricalOptics.waveOperator_eq h ha hb hψ hε hp

example (x y θ : ℝ) :
    (x * cos θ + y * sin θ) ^ 2 ≤ x ^ 2 + y ^ 2 :=
  sq_mul_cos_add_mul_sin_le x y θ

example (a b : ℝ × E3 → ℝ) (t : ℝ) :
    ℝ :=
  amplitudeSource a b t

example (a b : ℝ × E3 → ℝ) (t : ℝ) :
    0 ≤ amplitudeSource a b t :=
  amplitudeSource_nonneg a b t

example {a b ψ : ℝ × E3 → ℝ} (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b) (hψ : ContDiff ℝ 2 ψ)
    (ε : ℝ) :
    ContDiff ℝ 2 (Wave.highFrequencyWave a b ψ ε) :=
  contDiff_highFrequencyWave ha hb hψ ε

example {T R : ℝ} {a b : ℝ × E3 → ℝ} (has : Wave.BallSupportOn T R a)
    (hbs : Wave.BallSupportOn T R b) (ψ : ℝ × E3 → ℝ) (ε : ℝ) :
    Wave.BallSupportOn T R (Wave.highFrequencyWave a b ψ ε) :=
  ballSupportOn_highFrequencyWave has hbs ψ ε

example {T R : ℝ} {a b : ℝ × E3 → ℝ} (hT : 0 < T) (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (has : Wave.BallSupportOn T R a) (hbs : Wave.BallSupportOn T R b) :
    ContinuousOn (amplitudeSource a b) (Icc 0 T) :=
  continuousOn_amplitudeSource hT ha hb has hbs

example {T R : ℝ} {a b ψ : ℝ × E3 → ℝ} (h : IsGeometricalOptics T a b ψ) (ha : ContDiff ℝ 2 a)
    (hb : ContDiff ℝ 2 b) (hψ : ContDiff ℝ 2 ψ) (hT : 0 < T) (has : Wave.BallSupportOn T R a)
    (hbs : Wave.BallSupportOn T R b) {ε : ℝ} (hε : ε ≠ 0) {s : ℝ} (hs : s ∈ Icc 0 T) :
    Wave.spatialL2Norm (Wave.waveOperator (Wave.highFrequencyWave a b ψ ε)) s ≤
      amplitudeSource a b s :=
  IsGeometricalOptics.spatialL2Norm_waveOperator_le h ha hb hψ hT has hbs hε hs

example {u w : ℝ × E3 → ℝ} (hu : Differentiable ℝ u) (hw : Differentiable ℝ w)
    (h0 : ∀ x, u (0, x) = w (0, x)) (h1 : ∀ x, Wave.timeDeriv u (0, x) = Wave.timeDeriv w (0, x)) :
    Wave.energy (fun p => u p - w p) 0 = 0 :=
  energy_sub_eq_zero hu hw h0 h1

example {T R : ℝ} {a b ψ u : ℝ × E3 → ℝ} (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hψ : ContDiff ℝ 2 ψ) (h : IsGeometricalOptics T a b ψ) (has : Wave.BallSupportOn T R a)
    (hbs : Wave.BallSupportOn T R b) (hu : ContDiff ℝ 2 u) (hus : Wave.BallSupportOn T R u)
    (hwave : ∀ p : ℝ × E3, p.1 ∈ Icc 0 T → Wave.waveOperator u p = 0) {ε : ℝ} (hε : ε ≠ 0)
    (h0 : ∀ x, u (0, x) = Wave.highFrequencyWave a b ψ ε (0, x))
    (h1 : ∀ x, Wave.timeDeriv u (0, x) = Wave.timeDeriv (Wave.highFrequencyWave a b ψ ε) (0, x))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    √(Wave.energy (fun p => u p - Wave.highFrequencyWave a b ψ ε p) t) ≤
      ∫ s in 0..t, amplitudeSource a b s :=
  sqrt_energy_sub_le ha hb hψ h has hbs hu hus hwave hε h0 h1 ht

example {T R : ℝ} {a b ψ : ℝ × E3 → ℝ} (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hψ : ContDiff ℝ 2 ψ) (h : IsGeometricalOptics T a b ψ) (has : Wave.BallSupportOn T R a)
    (hbs : Wave.BallSupportOn T R b) :
    ∃ C, ∀ ε ≠ 0, ∀ u : ℝ × E3 → ℝ, ContDiff ℝ 2 u → Wave.BallSupportOn T R u →
      (∀ p : ℝ × E3, p.1 ∈ Icc 0 T → Wave.waveOperator u p = 0) →
      (∀ x, u (0, x) = Wave.highFrequencyWave a b ψ ε (0, x)) →
      (∀ x, Wave.timeDeriv u (0, x) = Wave.timeDeriv (Wave.highFrequencyWave a b ψ ε) (0, x)) →
      ∀ t ∈ Icc 0 T,
        √(Wave.energy (fun p => u p - Wave.highFrequencyWave a b ψ ε p) t) ≤ C * t :=
  exists_sqrt_energy_sub_le ha hb hψ h has hbs

example (a b ψ : ℝ × E3 → ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    Wave.highFrequencyWave a b (fun p => ψ p + ε * (π / 2)) ε =
      Wave.highFrequencyWave b (fun p => -a p) ψ ε :=
  highFrequencyWave_add_quarter a b ψ hε

example (a ψ : ℝ × E3 → ℝ) (p : ℝ × E3) :
    Wave.transport (fun q => -a q) ψ p = -Wave.transport a ψ p :=
  transport_fun_neg a ψ p

example {T : ℝ} {a b ψ : ℝ × E3 → ℝ} (h : IsGeometricalOptics T a b ψ) :
    IsGeometricalOptics T b (fun p => -a p) ψ :=
  IsGeometricalOptics.shift h

example (a b : ℝ × E3 → ℝ) (t : ℝ) :
    amplitudeSource b (fun p => -a p) t = amplitudeSource a b t :=
  amplitudeSource_shift a b t

example {a b ψ : ℝ × E3 → ℝ} {p : ℝ × E3} (ha : DifferentiableAt ℝ a p)
    (hb : DifferentiableAt ℝ b p) (hψ : DifferentiableAt ℝ ψ p) (ε : ℝ) :
    Wave.gradNormSq (Wave.highFrequencyWave a b ψ ε) p +
        Wave.gradNormSq (Wave.highFrequencyWave b (fun q => -a q) ψ ε) p =
      ε⁻¹ ^ 2 * ((a p ^ 2 + b p ^ 2) * Wave.gradNormSq ψ p) +
        2 * ε⁻¹ * (b p * Wave.gradInner a ψ p - a p * Wave.gradInner b ψ p) +
        (Wave.gradNormSq a p + Wave.gradNormSq b p) :=
  gradNormSq_highFrequencyWave_add_shift ha hb hψ ε

example (a b ψ : ℝ × E3 → ℝ) (t : ℝ) :
    ℝ :=
  leadingEnergy a b ψ t

example (a b ψ : ℝ × E3 → ℝ) (t : ℝ) :
    ℝ :=
  crossEnergy a b ψ t

example (a b ψ : ℝ × E3 → ℝ) (t : ℝ) :
    0 ≤ leadingEnergy a b ψ t :=
  leadingEnergy_nonneg a b ψ t

example {T R : ℝ} {a b ψ : ℝ × E3 → ℝ} (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hψ : ContDiff ℝ 2 ψ) (hT : 0 < T) (has : Wave.BallSupportOn T R a)
    (hbs : Wave.BallSupportOn T R b) {t : ℝ} (ht : t ∈ Icc 0 T) {ε : ℝ} (hε : ε ≠ 0) :
    ε ^ 2 * (Wave.energy (Wave.highFrequencyWave a b ψ ε) t +
        Wave.energy (Wave.highFrequencyWave b (fun q => -a q) ψ ε) t) =
      leadingEnergy a b ψ t + ε * crossEnergy a b ψ t +
        ε ^ 2 * (Wave.energy a t + Wave.energy b t) :=
  sq_mul_energy_add_shift ha hb hψ hT has hbs ht hε

example {T R : ℝ} {a b ψ : ℝ × E3 → ℝ} (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hψ : ContDiff ℝ 2 ψ) (hT : 0 < T) (has : Wave.BallSupportOn T R a)
    (hbs : Wave.BallSupportOn T R b) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun ε => ε ^ 2 * (Wave.energy (Wave.highFrequencyWave a b ψ ε) t +
        Wave.energy (Wave.highFrequencyWave b (fun q => -a q) ψ ε) t))
      (𝓝[≠] 0) (𝓝 (leadingEnergy a b ψ t)) :=
  tendsto_sq_mul_energy_add_shift ha hb hψ hT has hbs ht

example {T R : ℝ} {a b ψ : ℝ × E3 → ℝ} (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hψ : ContDiff ℝ 2 ψ) (hT : 0 < T) (has : Wave.BallSupportOn T R a)
    (hbs : Wave.BallSupportOn T R b) {t : ℝ} (ht : t ∈ Icc 0 T) {ε : ℝ} (hε : ε ≠ 0)
    (hsmall : |ε| * |crossEnergy a b ψ t| ≤ leadingEnergy a b ψ t / 2) :
    leadingEnergy a b ψ t / 2 ≤ ε ^ 2 * (Wave.energy (Wave.highFrequencyWave a b ψ ε) t +
      Wave.energy (Wave.highFrequencyWave b (fun q => -a q) ψ ε) t) :=
  leadingEnergy_div_two_le ha hb hψ hT has hbs ht hε hsmall

example {T R : ℝ} {a b ψ u u' : ℝ × E3 → ℝ} (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hψ : ContDiff ℝ 2 ψ) (h : IsGeometricalOptics T a b ψ) (hT : 0 < T)
    (has : Wave.BallSupportOn T R a) (hbs : Wave.BallSupportOn T R b) (hu : ContDiff ℝ 2 u)
    (hus : Wave.BallSupportOn T R u)
    (hwave : ∀ p : ℝ × E3, p.1 ∈ Icc 0 T → Wave.waveOperator u p = 0) (hu' : ContDiff ℝ 2 u')
    (hus' : Wave.BallSupportOn T R u')
    (hwave' : ∀ p : ℝ × E3, p.1 ∈ Icc 0 T → Wave.waveOperator u' p = 0) {ε : ℝ} (hε : ε ≠ 0)
    (h0 : ∀ x, u (0, x) = Wave.highFrequencyWave a b ψ ε (0, x))
    (h1 : ∀ x, Wave.timeDeriv u (0, x) = Wave.timeDeriv (Wave.highFrequencyWave a b ψ ε) (0, x))
    (h0' : ∀ x, u' (0, x) = Wave.highFrequencyWave b (fun q => -a q) ψ ε (0, x))
    (h1' : ∀ x, Wave.timeDeriv u' (0, x) =
      Wave.timeDeriv (Wave.highFrequencyWave b (fun q => -a q) ψ ε) (0, x))
    {t : ℝ} (ht : t ∈ Icc 0 T) (hL : 0 < leadingEnergy a b ψ t)
    (hsmall : |ε| * |crossEnergy a b ψ t| ≤ leadingEnergy a b ψ t / 2) :
    Wave.energy (fun p => u p - Wave.highFrequencyWave a b ψ ε p) t +
        Wave.energy (fun p => u' p - Wave.highFrequencyWave b (fun q => -a q) ψ ε p) t ≤
      ε ^ 2 * (4 * (∫ s in 0..t, amplitudeSource a b s) ^ 2 / leadingEnergy a b ψ t) *
        (Wave.energy (Wave.highFrequencyWave a b ψ ε) t +
          Wave.energy (Wave.highFrequencyWave b (fun q => -a q) ψ ε) t) :=
  energy_sub_add_energy_sub_le ha hb hψ h hT has hbs hu hus hwave hu' hus' hwave' hε h0 h1 h0'
    h1' ht hL hsmall

example (p : ℝ × E3) :
    ℝ :=
  planePhase p

example (f : E3 → ℝ) (p : ℝ × E3) :
    ℝ :=
  planeAmplitude f p

example {n : ℕ∞} :
    ContDiff ℝ n planePhase :=
  contDiff_planePhase

example {n : ℕ∞} {f : E3 → ℝ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (planeAmplitude f) :=
  contDiff_planeAmplitude hf

example (p : ℝ × E3) :
    Wave.timeDeriv planePhase p = 1 :=
  timeDeriv_planePhase p

example (i : Fin 3) (p : ℝ × E3) :
    Wave.spaceDeriv i planePhase p = -(EuclideanSpace.single i (1 : ℝ)) 0 :=
  spaceDeriv_planePhase i p

example (p : ℝ × E3) :
    Wave.waveOperator planePhase p = 0 :=
  waveOperator_planePhase p

example (p : ℝ × E3) :
    Wave.wavePairing planePhase planePhase p = 0 :=
  wavePairing_planePhase p

example {f : E3 → ℝ} (hf : Differentiable ℝ f) (p : ℝ × E3) :
    Wave.transport (planeAmplitude f) planePhase p = 0 :=
  transport_planeAmplitude hf p

example {f g : E3 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (T : ℝ) :
    IsGeometricalOptics T (planeAmplitude f) (planeAmplitude g) planePhase :=
  isGeometricalOptics_plane hf hg T

example {f : E3 → ℝ} {r : ℝ} (hf : ∀ y, r < ‖y‖ → f y = 0) (T : ℝ) :
    Wave.BallSupportOn T (r + T) (planeAmplitude f) :=
  ballSupportOn_planeAmplitude hf T

example (p : ℝ × E3) :
    Wave.gradNormSq planePhase p = 2 :=
  gradNormSq_planePhase p

example (f g : E3 → ℝ) (t : ℝ) :
    leadingEnergy (planeAmplitude f) (planeAmplitude g) planePhase t =
      ∫ x, (f x ^ 2 + g x ^ 2) :=
  leadingEnergy_plane f g t

example (t : ℝ) :
    0 < leadingEnergy (planeAmplitude Wave.spaceBump) (planeAmplitude fun _ => 0) planePhase t :=
  leadingEnergy_plane_spaceBump_pos t

example {f g : E3 → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) {ε : ℝ} (hε : ε ≠ 0)
    {p : ℝ × E3} (hp : 0 ≤ p.1) :
    Wave.waveOperator
        (Wave.highFrequencyWave (planeAmplitude f) (planeAmplitude g) planePhase ε) p =
      Wave.waveOperator (planeAmplitude f) p * cos (planePhase p / ε) +
        Wave.waveOperator (planeAmplitude g) p * sin (planePhase p / ε) :=
  waveOperator_plane hf hg hε hp

example (p : ℝ × E3) :
    ℝ :=
  radialPhase p

example (g : ℝ → ℝ) (p : ℝ × E3) :
    ℝ :=
  radialAmplitude g p

example {q : ℝ × E3} (hq : q.2 ≠ 0) :
    Wave.timeDeriv radialPhase q = 1 :=
  timeDeriv_radialPhase hq

example {q : ℝ × E3} (hq : q.2 ≠ 0) (i : Fin 3) :
    Wave.spaceDeriv i radialPhase q = -(q.2 i * ‖q.2‖⁻¹) :=
  spaceDeriv_radialPhase hq i

example {g : ℝ → ℝ} (hg : Differentiable ℝ g) {q : ℝ × E3} (hq : q.2 ≠ 0) :
    Wave.timeDeriv (radialAmplitude g) q = radialAmplitude (deriv g) q :=
  timeDeriv_radialAmplitude hg hq

example {g : ℝ → ℝ} (hg : Differentiable ℝ g) {q : ℝ × E3} (hq : q.2 ≠ 0) (i : Fin 3) :
    Wave.spaceDeriv i (radialAmplitude g) q = -(q.2 i * (deriv g (q.1 - ‖q.2‖) * ‖q.2‖⁻¹ ^ 2 +
      g (q.1 - ‖q.2‖) * ‖q.2‖⁻¹ ^ 3)) :=
  spaceDeriv_radialAmplitude hg hq i

example {g : ℝ → ℝ} (hg : Differentiable ℝ g) (hg' : Differentiable ℝ (deriv g)) {q : ℝ × E3}
    (hq : q.2 ≠ 0) :
    Wave.waveOperator (radialAmplitude g) q = 0 :=
  waveOperator_radialAmplitude hg hg' hq

example {q : ℝ × E3} (hq : q.2 ≠ 0) :
    Wave.waveOperator radialPhase q = 2 * ‖q.2‖⁻¹ :=
  waveOperator_radialPhase hq

example {q : ℝ × E3} (hq : q.2 ≠ 0) :
    Wave.wavePairing radialPhase radialPhase q = 0 :=
  wavePairing_radialPhase hq

example {q : ℝ × E3} (hq : q.2 ≠ 0) :
    Wave.gradNormSq radialPhase q = 2 :=
  gradNormSq_radialPhase hq

example {g : ℝ → ℝ} (hg : Differentiable ℝ g) {q : ℝ × E3} (hq : q.2 ≠ 0) :
    Wave.transport (radialAmplitude g) radialPhase q = 0 :=
  transport_radialAmplitude hg hq

example (x : E3) :
    ℝ :=
  smoothRadius x

example (x : E3) :
    ℝ :=
  smoothInvRadius x

example {n : ℕ∞} :
    ContDiff ℝ n smoothRadius :=
  contDiff_smoothRadius

example {n : ℕ∞} :
    ContDiff ℝ n smoothInvRadius :=
  contDiff_smoothInvRadius

example {x : E3} (hx : 1 ≤ ‖x‖) :
    smoothRadius x = ‖x‖ :=
  smoothRadius_of_one_le hx

example {x : E3} (hx : 1 ≤ ‖x‖) :
    smoothInvRadius x = ‖x‖⁻¹ :=
  smoothInvRadius_of_one_le hx

example :
    ContDiffBump (-5 : ℝ) :=
  shellBump

example (p : ℝ × E3) :
    ℝ :=
  sphericalPhase p

example (p : ℝ × E3) :
    ℝ :=
  sphericalAmplitude p

example {n : ℕ∞} :
    ContDiff ℝ n sphericalPhase :=
  contDiff_sphericalPhase

example {n : ℕ∞} :
    ContDiff ℝ n sphericalAmplitude :=
  contDiff_sphericalAmplitude

example {p : ℝ × E3} (hp : 0 ≤ p.1) :
    Wave.waveOperator sphericalAmplitude p = 0 :=
  waveOperator_sphericalAmplitude hp

example (T : ℝ) :
    IsGeometricalOptics T sphericalAmplitude sphericalAmplitude sphericalPhase :=
  isGeometricalOptics_spherical T

example (T : ℝ) :
    Wave.BallSupportOn T (T + 6) sphericalAmplitude :=
  ballSupportOn_sphericalAmplitude T

example (a ψ : ℝ × E3 → ℝ) (t : ℝ) :
    crossEnergy a a ψ t = 0 :=
  crossEnergy_self a ψ t

example {t : ℝ} (ht : 0 ≤ t) :
    0 < leadingEnergy sphericalAmplitude sphericalAmplitude sphericalPhase t :=
  leadingEnergy_spherical_pos ht

example {ε : ℝ} (hε : ε ≠ 0) {p : ℝ × E3} (hp : 0 ≤ p.1) :
    Wave.waveOperator
      (Wave.highFrequencyWave sphericalAmplitude sphericalAmplitude sphericalPhase ε) p = 0 :=
  waveOperator_spherical hε hp

example {ε : ℝ} (hε : ε ≠ 0) {p : ℝ × E3} (hp : 0 ≤ p.1) :
    Wave.waveOperator (Wave.highFrequencyWave sphericalAmplitude
      (fun q => -sphericalAmplitude q) sphericalPhase ε) p = 0 :=
  waveOperator_spherical_shift hε hp

example (T : ℝ) {ε : ℝ} (hε : ε ≠ 0) {t : ℝ} (ht : t ∈ Icc 0 T) :
    √(Wave.energy (fun p =>
        Wave.highFrequencyWave sphericalAmplitude sphericalAmplitude sphericalPhase ε p -
          Wave.highFrequencyWave sphericalAmplitude sphericalAmplitude sphericalPhase ε p) t) ≤
      ∫ s in 0..t, amplitudeSource sphericalAmplitude sphericalAmplitude s :=
  sqrt_energy_sub_le_spherical T hε ht

example {T : ℝ} (hT : 0 < T) {ε : ℝ} (hε : ε ≠ 0) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Wave.energy (fun p =>
        Wave.highFrequencyWave sphericalAmplitude sphericalAmplitude sphericalPhase ε p -
          Wave.highFrequencyWave sphericalAmplitude sphericalAmplitude sphericalPhase ε p) t +
      Wave.energy (fun p =>
        Wave.highFrequencyWave sphericalAmplitude (fun q => -sphericalAmplitude q)
            sphericalPhase ε p -
          Wave.highFrequencyWave sphericalAmplitude (fun q => -sphericalAmplitude q)
            sphericalPhase ε p) t ≤
      ε ^ 2 * (4 * (∫ s in 0..t, amplitudeSource sphericalAmplitude sphericalAmplitude s) ^ 2 /
          leadingEnergy sphericalAmplitude sphericalAmplitude sphericalPhase t) *
        (Wave.energy (Wave.highFrequencyWave sphericalAmplitude sphericalAmplitude
            sphericalPhase ε) t +
          Wave.energy (Wave.highFrequencyWave sphericalAmplitude
            (fun q => -sphericalAmplitude q) sphericalPhase ε) t) :=
  energy_sub_add_energy_sub_le_spherical hT hε ht

example {U : Set Spacetime} (hU : IsOpen U) {A : Potential} (hA : ContDiff ℝ 2 A)
    (hL : ∀ y ∈ U, lorenzDivergence A y = 0)
    (hM : ∀ y ∈ U, (divergence3 (magneticField (fieldTensor A)) y = 0 ∧
        ∀ i, partialAt (magneticField (fieldTensor A) i) 0 y +
          curl (electricField (fieldTensor A)) y i = 0) ∧
      (divergence3 (electricField (fieldTensor A)) y = 0 ∧
        ∀ i, curl (magneticField (fieldTensor A)) y i -
          partialAt (electricField (fieldTensor A) i) 0 y = 0))
    (μ : Fin 4) {p : ℝ × E3} (hp : Wave.timeSpaceEquiv.symm p ∈ U) :
    Wave.waveOperator (fun q => potentialComponent A μ (Wave.timeSpaceEquiv.symm q)) p = 0 :=
  waveOperator_potentialComponent_eq_zero hU hA hL hM μ hp

example {U : Set Spacetime} (hU : IsOpen U) {A : Potential} (hA : ContDiff ℝ 2 A)
    (hL : ∀ y ∈ U, lorenzDivergence A y = 0)
    (hM : ∀ y ∈ U, (divergence3 (magneticField (fieldTensor A)) y = 0 ∧
        ∀ i, partialAt (magneticField (fieldTensor A) i) 0 y +
          curl (electricField (fieldTensor A)) y i = 0) ∧
      (divergence3 (electricField (fieldTensor A)) y = 0 ∧
        ∀ i, curl (magneticField (fieldTensor A)) y i -
          partialAt (electricField (fieldTensor A) i) 0 y = 0))
    {T R : ℝ} (hTU : ∀ p : ℝ × E3, p.1 ∈ Icc 0 T → Wave.timeSpaceEquiv.symm p ∈ U) (μ : Fin 4)
    (hAs : Wave.BallSupportOn T R fun q => potentialComponent A μ (Wave.timeSpaceEquiv.symm q))
    {a b ψ : ℝ × E3 → ℝ} (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b) (hψ : ContDiff ℝ 2 ψ)
    (h : IsGeometricalOptics T a b ψ) (has : Wave.BallSupportOn T R a)
    (hbs : Wave.BallSupportOn T R b) {ε : ℝ} (hε : ε ≠ 0)
    (h0 : ∀ x, potentialComponent A μ (Wave.timeSpaceEquiv.symm (0, x)) =
      Wave.highFrequencyWave a b ψ ε (0, x))
    (h1 : ∀ x, Wave.timeDeriv (fun q => potentialComponent A μ (Wave.timeSpaceEquiv.symm q))
      (0, x) = Wave.timeDeriv (Wave.highFrequencyWave a b ψ ε) (0, x))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    √(Wave.energy (fun q => potentialComponent A μ (Wave.timeSpaceEquiv.symm q) -
        Wave.highFrequencyWave a b ψ ε q) t) ≤ ∫ s in 0..t, amplitudeSource a b s :=
  sqrt_energy_potentialComponent_sub_le hU hA hL hM hTU μ hAs ha hb hψ h has hbs hε h0 h1 ht

end ProjectAinos.Electrodynamics.Optics.Limits

end Error
