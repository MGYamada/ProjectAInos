/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAInos

/-! Typed contracts for the public GR physics layer. These examples intentionally
use default elaborator options. Native manifold clocks and model-coordinate
variation are checked separately so their hypotheses cannot silently change. -/

noncomputable section
open MeasureTheory Set
open scoped Manifold ContDiff Topology
open ProjectAInos ProjectAInos.SmoothGeometry ProjectAInos.GeneralRelativity
open ProjectAInos.SmoothGeometry.LorentzMetric

section ScalarIntegral

example {F : ℝ × ℝ → ℝ} {D : ℝ → ℝ} {ε₀ a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContDiffAt ℝ 1 F (ε₀, t))
    (hD : ∀ t ∈ uIcc a b, HasDerivAt (fun ε => F (ε, t)) (D t) ε₀) :
    HasDerivAt (fun ε => ∫ t in a..b, F (ε, t)) (∫ t in a..b, D t) ε₀ :=
  Variational.hasDerivAt_intervalIntegral_of_contDiffAt hF hD

end ScalarIntegral

section Native

variable {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric .timeNegative d M)

example {x : M} (a : ℝ) (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    properSpeed g (a • v) = |a| * properSpeed g v := properSpeed_smul g a v

example {x : M} {v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x} (hv : Timelike g v) :
    g.form x (fourVelocity g v) (fourVelocity g v) = -1 := fourVelocity_unit g hv

example (γ : ℝ → M) (a b : ℝ)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, MinkowskiModel d) 1 γ t) :
    IntervalIntegrable (speedAlong g γ) volume a b := properTime_integrable g γ a b hγ

example (γ : ℝ → M) (r : ℝ → ℝ) (a b : ℝ)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, MinkowskiModel d) 1 γ (r t))
    (hr : ∀ t ∈ uIcc a b, ContDiffAt ℝ 1 r t)
    (hpos : ∀ t ∈ uIcc a b, 0 ≤ deriv r t) :
    properTime g (γ ∘ r) a b = properTime g γ (r a) (r b) :=
  properTime_reparametrize g γ r a b hγ hr hpos

example (m : ℝ) (γ : ℝ → M) (r : ℝ → ℝ) (a b : ℝ)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, MinkowskiModel d) 1 γ (r t))
    (hr : ∀ t ∈ uIcc a b, ContDiffAt ℝ 1 r t)
    (hpos : ∀ t ∈ uIcc a b, 0 ≤ deriv r t) :
    freeAction g m (γ ∘ r) a b = freeAction g m γ (r a) (r b) :=
  freeAction_reparametrize g m γ r a b hγ hr hpos

example (γ : ℝ → M) (a b c : ℝ)
    (hab : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, MinkowskiModel d) 1 γ t)
    (hbc : ∀ t ∈ uIcc b c, ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, MinkowskiModel d) 1 γ t) :
    properTime g γ a b + properTime g γ b c = properTime g γ a c :=
  properTime_add g γ a b c hab hbc

example (γ : ℝ → M) (a b c : ℝ)
    (hab : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, MinkowskiModel d) 1 γ t)
    (hbc : ∀ t ∈ uIcc b c, ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, MinkowskiModel d) 1 γ t) :
    quadraticAction g γ a b + quadraticAction g γ b c = quadraticAction g γ a c :=
  quadraticAction_add g γ a b c hab hbc

example {γ : ℝ → M} {a b : ℝ} (hγ : g.IsGeodesicOn (uIcc a b) γ) :
    properTime g γ a b = (b - a) * speedAlong g γ a := properTime_geodesic g hγ

example {γ : ℝ → M} {t : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, MinkowskiModel d) 2 γ t)
    (hv : Timelike g (curveVelocity γ t)) :
    HasDerivAt (speedAlong g γ)
      (-g.form (γ t) (g.covariantAlong (curveVelocity γ) t) (curveVelocity γ t) /
        speedAlong g γ t) t := hasDerivAt_speedAlong g hγ hv

example (γ : ℝ → M) (a b : ℝ)
    (h : ∀ t ∈ uIcc a b, g.form (γ t) (curveVelocity γ t) (curveVelocity γ t) = 0) :
    quadraticAction g γ a b = 0 := quadraticAction_null g γ a b h

example {e : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M)
    (γ : ℝ → M) (a b : ℝ) (hstay : ∀ t ∈ uIcc a b, γ t ∈ e.source)
    (hγ : ∀ t ∈ uIcc a b, MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, MinkowskiModel d) γ t) :
    properTime g γ a b = ∫ t in a..b, Real.sqrt (-g.chartMetric e (γ t)
      (deriv (e ∘ γ) t) (deriv (e ∘ γ) t)) := properTime_chart g he γ a b hstay hγ

example {e : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M)
    (γ : ℝ → M) (a b : ℝ) (hstay : ∀ t ∈ uIcc a b, γ t ∈ e.source)
    (hγ : ∀ t ∈ uIcc a b, MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, MinkowskiModel d) γ t) :
    quadraticAction g γ a b = ∫ t in a..b, (1 / 2 : ℝ) * g.chartMetric e (γ t)
      (deriv (e ∘ γ) t) (deriv (e ∘ γ) t) := quadraticAction_chart g he γ a b hstay hγ

variable {d' : ℕ} {N : Type} [TopologicalSpace N]
  [ChartedSpace (MinkowskiModel d') N] [IsManifold 𝓘(ℝ, MinkowskiModel d') ∞ N]

example (h : LorentzMetric .timeNegative d' N) (f : M → N) (γ : ℝ → M) (a b : ℝ)
    (hf : ∀ t ∈ uIcc a b,
      MDifferentiableAt 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d') f (γ t))
    (hγ : ∀ t ∈ uIcc a b, MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, MinkowskiModel d) γ t)
    (hmetric : ∀ t ∈ uIcc a b,
      g.form (γ t) (curveVelocity γ t) (curveVelocity γ t) =
        h.form (f (γ t))
          (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d') f (γ t) (curveVelocity γ t))
          (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d') f (γ t) (curveVelocity γ t))) :
    properTime h (f ∘ γ) a b = properTime g γ a b := properTime_map g h f γ a b hf hγ hmetric

example {γ : ℝ → M} {a b t₀ : ℝ}
    (hγ : ∀ s ∈ Ioo a b, ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, MinkowskiModel d) 2 γ s)
    (hv : ∀ s ∈ Ioo a b, Timelike g (curveVelocity γ s)) (ht₀ : t₀ ∈ Ioo a b) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      (e : ℝ → ℝ) = properTime g γ t₀ ∧ t₀ ∈ e.source ∧ e.source ⊆ Ioo a b ∧
      e t₀ = 0 ∧ ∀ τ ∈ e.target,
        ContDiffAt ℝ 2 e.symm τ ∧
        HasDerivAt e.symm (speedAlong g γ (e.symm τ))⁻¹ τ ∧
        speedAlong g (γ ∘ e.symm) τ = 1 := exists_properTime_parameter g hγ hv ht₀

example {γ : ℝ → M} {a b t₀ : ℝ}
    (hγ : ∀ s ∈ Ioo a b, ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, MinkowskiModel d) 2 γ s)
    (hv : ∀ s ∈ Ioo a b, Timelike g (curveVelocity γ s))
    (ha : ∀ s ∈ Ioo a b, ∃ k : ℝ,
      g.covariantAlong (curveVelocity γ) s = k • curveVelocity γ s)
    (ht₀ : t₀ ∈ Ioo a b) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      (e : ℝ → ℝ) = properTime g γ t₀ ∧ t₀ ∈ e.source ∧ e.source ⊆ Ioo a b ∧
      e t₀ = 0 ∧
      (∀ τ ∈ e.target, ContDiffAt ℝ 2 e.symm τ ∧
        HasDerivAt e.symm (speedAlong g γ (e.symm τ))⁻¹ τ ∧
        speedAlong g (γ ∘ e.symm) τ = 1) ∧
      g.IsGeodesicOn e.target (γ ∘ e.symm) :=
  exists_properTime_geodesic_parameter g hγ hv ha ht₀

end Native

section NativeFiniteAndFamilies

variable {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "J" => 𝓘(ℝ, ℝ × ℝ)

example (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : ∀ t ∈ Icc a b, Timelike g (curveVelocity γ t)) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      (e : ℝ → ℝ) = properTime g γ a ∧ Icc a b ⊆ e.source ∧ StrictMonoOn e e.source ∧
      e '' Icc a b = Icc 0 (properTime g γ a b) ∧
      e.symm '' Icc 0 (properTime g γ a b) = Icc a b ∧
      e.symm 0 = a ∧ e.symm (properTime g γ a b) = b ∧
      ∀ τ ∈ e.target,
        ContDiffAt ℝ 2 e.symm τ ∧
        HasDerivAt e.symm (speedAlong g γ (e.symm τ))⁻¹ τ ∧
        speedAlong g (γ ∘ e.symm) τ = 1 :=
  exists_finite_properTime_parameter g hab hγ hv

example (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : ∀ t ∈ Icc a b, Timelike g (curveVelocity γ t))
    (ha : ∀ t ∈ Ioo a b, ∃ k : ℝ,
      g.covariantAlong (curveVelocity γ) t = k • curveVelocity γ t) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      (e : ℝ → ℝ) = properTime g γ a ∧ Icc a b ⊆ e.source ∧
      e '' Icc a b = Icc 0 (properTime g γ a b) ∧
      e.symm '' Icc 0 (properTime g γ a b) = Icc a b ∧
      e.symm 0 = a ∧ e.symm (properTime g γ a b) = b ∧
      (∀ τ ∈ e.target, ContDiffAt ℝ 2 e.symm τ ∧
        HasDerivAt e.symm (speedAlong g γ (e.symm τ))⁻¹ τ ∧
        speedAlong g (γ ∘ e.symm) τ = 1) ∧
      g.IsGeodesicOn (Ioo 0 (properTime g γ a b)) (γ ∘ e.symm) :=
  exists_finite_properTime_geodesic g hab hγ hv ha

example (g : LorentzMetric .timeNegative d M)
    {Γ : ℝ × ℝ → M} {a t : ℝ} (hΓ : ContMDiffAt J I 2 Γ (a, t)) :
    HasDerivAt (fun ε => (1 / 2 : ℝ) * g.form (Γ (ε, t))
      (curveVelocity (fun s => Γ (ε, s)) t) (curveVelocity (fun s => Γ (ε, s)) t))
      (g.form (Γ (a, t))
        (g.covariantAlong (γ := fun s => Γ (a, s))
          (fun s => familyVelocity Γ (1, 0) (a, s)) t)
        (curveVelocity (fun s => Γ (a, s)) t)) a :=
  quadraticDensity_hasDerivAt g hΓ

example (g : LorentzMetric .timeNegative d M) (m : ℝ)
    {Γ : ℝ × ℝ → M} {a t : ℝ} (hΓ : ContMDiffAt J I 2 Γ (a, t))
    (hv : Timelike g (curveVelocity (fun s => Γ (a, s)) t)) :
    HasDerivAt (fun ε => -m * speedAlong g (fun s => Γ (ε, s)) t)
      ((m / speedAlong g (fun s => Γ (a, s)) t) * g.form (Γ (a, t))
        (g.covariantAlong (γ := fun s => Γ (a, s))
          (fun s => familyVelocity Γ (1, 0) (a, s)) t)
        (curveVelocity (fun s => Γ (a, s)) t)) a :=
  freeDensity_hasDerivAt g m hΓ hv

example (g : LorentzMetric .timeNegative d M)
    {Γ : ℝ × ℝ → M} {ε₀ a b : ℝ}
    (hΓ : ∀ t ∈ uIcc a b, ContMDiffAt J I 2 Γ (ε₀, t)) :
    HasDerivAt (fun ε => quadraticAction g (fun t => Γ (ε, t)) a b)
      (∫ t in a..b, g.form (Γ (ε₀, t))
        (g.covariantAlong (γ := fun s => Γ (ε₀, s))
          (fun s => familyVelocity Γ (1, 0) (ε₀, s)) t)
        (curveVelocity (fun s => Γ (ε₀, s)) t)) ε₀ :=
  quadraticAction_family_hasDerivAt g hΓ

example (g : LorentzMetric .timeNegative d M) (m : ℝ)
    {Γ : ℝ × ℝ → M} {ε₀ a b : ℝ}
    (hΓ : ∀ t ∈ uIcc a b, ContMDiffAt J I 2 Γ (ε₀, t))
    (hv : ∀ t ∈ uIcc a b, Timelike g (curveVelocity (fun s => Γ (ε₀, s)) t)) :
    HasDerivAt (fun ε => freeAction g m (fun t => Γ (ε, t)) a b)
      (∫ t in a..b, (m / speedAlong g (fun s => Γ (ε₀, s)) t) * g.form (Γ (ε₀, t))
        (g.covariantAlong (γ := fun s => Γ (ε₀, s))
          (fun s => familyVelocity Γ (1, 0) (ε₀, s)) t)
        (curveVelocity (fun s => Γ (ε₀, s)) t)) ε₀ :=
  freeAction_family_hasDerivAt g m hΓ hv

example (g : LorentzMetric .timeNegative d M)
    {Γ : ℝ × ℝ → M} {ε₀ a b : ℝ}
    (hΓ : ∀ t ∈ uIcc a b, ContMDiffAt J I 2 Γ (ε₀, t)) :
    HasDerivAt (fun ε => quadraticAction g (fun t => Γ (ε, t)) a b)
      ((g.form (Γ (ε₀, b)) (familyVelocity Γ (1, 0) (ε₀, b))
          (curveVelocity (fun s => Γ (ε₀, s)) b) -
        g.form (Γ (ε₀, a)) (familyVelocity Γ (1, 0) (ε₀, a))
          (curveVelocity (fun s => Γ (ε₀, s)) a)) +
        ∫ t in a..b, -g.form (Γ (ε₀, t)) (familyVelocity Γ (1, 0) (ε₀, t))
          (g.covariantAlong (curveVelocity (fun s => Γ (ε₀, s))) t)) ε₀ :=
  quadraticAction_family_firstVariation g hΓ

example (g : LorentzMetric .timeNegative d M) (m : ℝ)
    {Γ : ℝ × ℝ → M} {ε₀ a b : ℝ}
    (hΓ : ∀ t ∈ uIcc a b, ContMDiffAt J I 2 Γ (ε₀, t))
    (hv : ∀ t ∈ uIcc a b, Timelike g (curveVelocity (fun s => Γ (ε₀, s)) t)) :
    HasDerivAt (fun ε => freeAction g m (fun t => Γ (ε, t)) a b)
      (((m / speedAlong g (fun s => Γ (ε₀, s)) b) *
          g.form (Γ (ε₀, b)) (familyVelocity Γ (1, 0) (ε₀, b))
            (curveVelocity (fun s => Γ (ε₀, s)) b) -
        (m / speedAlong g (fun s => Γ (ε₀, s)) a) *
          g.form (Γ (ε₀, a)) (familyVelocity Γ (1, 0) (ε₀, a))
            (curveVelocity (fun s => Γ (ε₀, s)) a)) +
        ∫ t in a..b, -(m / speedAlong g (fun s => Γ (ε₀, s)) t) *
          g.form (Γ (ε₀, t)) (familyVelocity Γ (1, 0) (ε₀, t))
            (g.covariantAlong (curveVelocity (fun s => Γ (ε₀, s))) t -
              (deriv (speedAlong g (fun s => Γ (ε₀, s))) t /
                speedAlong g (fun s => Γ (ε₀, s)) t) •
                curveVelocity (fun s => Γ (ε₀, s)) t)) ε₀ :=
  freeAction_family_firstVariation g m hΓ hv

example (g : LorentzMetric .timeNegative d M)
    {Γ : ℝ × ℝ → M} {ε₀ a b : ℝ} (hab : a ≤ b)
    (hΓ : ∀ t ∈ uIcc a b, ContMDiffAt J I 2 Γ (ε₀, t))
    (ha : ∀ᶠ ε in 𝓝 ε₀, Γ (ε, a) = Γ (ε₀, a))
    (hb : ∀ᶠ ε in 𝓝 ε₀, Γ (ε, b) = Γ (ε₀, b))
    (hg : g.IsGeodesicOn (Ioo a b) (fun s => Γ (ε₀, s))) :
    HasDerivAt (fun ε => quadraticAction g (fun t => Γ (ε, t)) a b) 0 ε₀ :=
  quadraticAction_family_stationary_of_geodesic g hab hΓ ha hb hg

example (g : LorentzMetric .timeNegative d M) (m : ℝ)
    {Γ : ℝ × ℝ → M} {ε₀ a b : ℝ} (hab : a ≤ b)
    (hΓ : ∀ t ∈ uIcc a b, ContMDiffAt J I 2 Γ (ε₀, t))
    (hv : ∀ t ∈ uIcc a b, Timelike g (curveVelocity (fun s => Γ (ε₀, s)) t))
    (ha : ∀ᶠ ε in 𝓝 ε₀, Γ (ε, a) = Γ (ε₀, a))
    (hb : ∀ᶠ ε in 𝓝 ε₀, Γ (ε, b) = Γ (ε₀, b))
    (hacc : ∀ t ∈ Ioo a b, ∃ k : ℝ,
      g.covariantAlong (curveVelocity (fun s => Γ (ε₀, s))) t =
        k • curveVelocity (fun s => Γ (ε₀, s)) t) :
    HasDerivAt (fun ε => freeAction g m (fun t => Γ (ε, t)) a b) 0 ε₀ :=
  freeAction_family_stationary_of_tangential g m hab hΓ hv ha hb hacc

example (g : LorentzMetric .timeNegative d M)
    {Γ : ℝ × ℝ → M} {ε₀ a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hΓ : ∀ t ∈ uIcc a c, ContMDiffAt J I 2 Γ (ε₀, t)) :
    deriv (fun ε => quadraticAction g (fun t => Γ (ε, t)) a b) ε₀ +
      deriv (fun ε => quadraticAction g (fun t => Γ (ε, t)) b c) ε₀ =
      deriv (fun ε => quadraticAction g (fun t => Γ (ε, t)) a c) ε₀ :=
  quadraticAction_family_deriv_add g hab hbc hΓ

example (g : LorentzMetric .timeNegative d M) (m : ℝ)
    {Γ : ℝ × ℝ → M} {ε₀ a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hΓ : ∀ t ∈ uIcc a c, ContMDiffAt J I 2 Γ (ε₀, t))
    (hv : ∀ t ∈ uIcc a c, Timelike g (curveVelocity (fun s => Γ (ε₀, s)) t)) :
    deriv (fun ε => freeAction g m (fun t => Γ (ε, t)) a b) ε₀ +
      deriv (fun ε => freeAction g m (fun t => Γ (ε, t)) b c) ε₀ =
      deriv (fun ε => freeAction g m (fun t => Γ (ε, t)) a c) ε₀ :=
  freeAction_family_deriv_add g m hab hbc hΓ hv

end NativeFiniteAndFamilies

section NativeStationarity

open Variational
variable {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

example (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {a b : ℝ} (V : ManifoldCurveVariation («E» := E) γ a b) :
    HasDerivAt (fun ε => quadraticAction g (fun t => V.family (ε, t)) a b)
      (∫ t in a..b, -g.form (γ t) (variationField V t)
        (g.covariantAlong (curveVelocity γ) t)) 0 :=
  quadraticAction_variation_hasDerivAt g V

example (g : LorentzMetric .timeNegative d M) (m : ℝ)
    {γ : ℝ → M} {a b : ℝ} (V : ManifoldCurveVariation («E» := E) γ a b)
    (hv : ∀ t ∈ uIcc a b, Timelike g (curveVelocity γ t)) :
    HasDerivAt (fun ε => freeAction g m (fun t => V.family (ε, t)) a b)
      (∫ t in a..b, -(m / speedAlong g γ t) * g.form (γ t) (variationField V t)
        (g.covariantAlong (curveVelocity γ) t -
          (deriv (speedAlong g γ) t / speedAlong g γ t) • curveVelocity γ t)) 0 :=
  freeAction_variation_hasDerivAt g m V hv

example (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t) :
    QuadraticStationary g γ a b ↔ g.IsGeodesicOn (Ioo a b) γ :=
  quadraticStationary_iff_geodesic g hab hγ

example (g : LorentzMetric .timeNegative d M)
    {m : ℝ} (hm : 0 < m) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : ∀ t ∈ uIcc a b, Timelike g (curveVelocity γ t)) :
    FreeStationary g m γ a b ↔ ∀ t ∈ Ioo a b,
      g.covariantAlong (curveVelocity γ) t =
        (deriv (speedAlong g γ) t / speedAlong g γ t) • curveVelocity γ t :=
  freeStationary_iff_acceleration g hm hab hγ hv

example (g : LorentzMetric .timeNegative d M)
    {m : ℝ} (hm : 0 < m) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : ∀ t ∈ uIcc a b, Timelike g (curveVelocity γ t)) :
    FreeStationary g m γ a b ↔ ∀ t ∈ Ioo a b, ∃ k : ℝ,
      g.covariantAlong (curveVelocity γ) t = k • curveVelocity γ t :=
  freeStationary_iff_tangential g hm hab hγ hv

example (g : LorentzMetric .timeNegative d M)
    {m : ℝ} (hm : 0 < m) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hunit : ∀ t ∈ uIcc a b, speedAlong g γ t = 1) :
    FreeStationary g m γ a b ↔ g.IsGeodesicOn (Ioo a b) γ :=
  freeStationary_iff_geodesic_of_unitSpeed g hm hab hγ hunit

example (g : LorentzMetric .timeNegative d M)
    {m : ℝ} (hm : 0 < m) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : ∀ t ∈ uIcc a b, Timelike g (curveVelocity γ t)) :
    FreeStationary g m γ a b ↔
      ∀ t₀ ∈ Ioo a b, ∃ e : OpenPartialHomeomorph ℝ ℝ,
        t₀ ∈ e.source ∧ e.source ⊆ Ioo a b ∧
        (∀ τ ∈ e.target, ContDiffAt ℝ 2 e.symm τ ∧ 0 < deriv e.symm τ) ∧
        g.IsGeodesicOn e.target (γ ∘ e.symm) :=
  freeStationary_iff_localGeodesic g hm hab hγ hv

example (g : LorentzMetric .timeNegative d M)
    {m : ℝ} (hm : 0 < m) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : ∀ t ∈ uIcc a b, Timelike g (curveVelocity γ t))
    (hs : FreeStationary g m γ a b) :
    ∃ r : ℝ → ℝ,
      r 0 = a ∧ r (properTime g γ a b) = b ∧
      MapsTo r (Icc 0 (properTime g γ a b)) (Icc a b) ∧
      (∀ τ ∈ Icc 0 (properTime g γ a b),
        ContDiffAt ℝ 2 r τ ∧ HasDerivAt r (speedAlong g γ (r τ))⁻¹ τ ∧
        properTime g γ a (r τ) = τ ∧ speedAlong g (γ ∘ r) τ = 1) ∧
      g.IsGeodesicOn (Ioo 0 (properTime g γ a b)) (γ ∘ r) :=
  freeStationary_finite_properTime g hm hab hγ hv hs

example {g : LorentzMetric .timeNegative d M}
    {γ : ℝ → M} {a b : ℝ} (hs : QuadraticStationary g γ a b) (hab : a < b)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hnull : curveVelocity (d := d) γ a ≠ 0 ∧
      g.form (γ a) (curveVelocity γ a) (curveVelocity γ a) = 0) :
    ∀ t ∈ Icc a b, curveVelocity (d := d) γ t ≠ 0 ∧
      g.form (γ t) (curveVelocity γ t) (curveVelocity γ t) = 0 :=
  hs.null_initial hab hγ hnull

example (g : LorentzMetric .timeNegative d M) (γ : ℝ → M) (a b : ℝ) :
    QuadraticStationary g γ a b ↔
      ∀ V : ManifoldCurveVariation («E» := E) γ a b,
        HasDerivAt (fun ε => quadraticAction g (fun t => V.family (ε, t)) a b) 0 0 := Iff.rfl

end NativeStationarity

section CoordinateVariation

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

example (B : E → E →L[ℝ] E →L[ℝ] ℝ) {U : Set E}
    (hU : IsOpen U) (hB : ContDiffOn ℝ 2 B U)
    {q η : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hq : ContDiff ℝ 2 q)
    (hη : ContDiff ℝ 2 η) (hstay : ∀ t ∈ Icc a b, q t ∈ U) :
    HasDerivAt (fun ε => Mechanics.action a b (quadraticLagrangian B)
      (Variational.perturb q η ε)) (Mechanics.firstVariation a b (quadraticLagrangian B) q η) 0 :=
  quadratic_hasDerivAt_action B hU hB hab hq hη hstay

example (B : E → E →L[ℝ] E →L[ℝ] ℝ) {U : Set E}
    (hU : IsOpen U) (hB : ContDiffOn ℝ 2 B U)
    {q : ℝ → E} {a b : ℝ} (hab : a < b) (hq : ContDiff ℝ 2 q)
    (hstay : ∀ t ∈ Icc a b, q t ∈ U) :
    Mechanics.Stationary a b (quadraticLagrangian B) q ↔
      ∀ t ∈ Ioo a b, Mechanics.eulerLagrange (quadraticLagrangian B) q t = 0 :=
  quadratic_stationary_iff B hU hB hab hq hstay

example (B : E → E →L[ℝ] E →L[ℝ] ℝ) (m : ℝ) {U : Set E}
    (hU : IsOpen U) (hB : ContDiffOn ℝ 2 B U)
    {q η : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hq : ContDiff ℝ 2 q)
    (hη : ContDiff ℝ 2 η) (hstay : ∀ t ∈ Icc a b, q t ∈ U)
    (hv : ∀ t ∈ Icc a b, B (q t) (deriv q t) (deriv q t) < 0) :
    HasDerivAt (fun ε => Mechanics.action a b (freeLagrangian B m)
      (Variational.perturb q η ε))
      (Mechanics.firstVariation a b (freeLagrangian B m) q η) 0 :=
  free_hasDerivAt_action B m hU hB hab hq hη hstay hv

variable {d : ℕ} (g : LorentzMetric .timeNegative d (MinkowskiModel d))

example {γ : ℝ → MinkowskiModel d} {t : ℝ} (hγ : ContDiffAt ℝ 2 γ t) (w : MinkowskiModel d) :
    Mechanics.eulerLagrange (quadraticLagrangian (modelMetric g)) γ t w =
      -g.form (γ t) (g.covariantAlong (curveVelocity γ) t) (modelField w (γ t)) :=
  quadratic_eulerLagrange_native g hγ w

example {γ η : ℝ → MinkowskiModel d} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContDiff ℝ 2 γ) (hη : ContDiff ℝ 2 η) :
    HasDerivAt (fun ε => quadraticAction g (Variational.perturb γ η ε) a b)
      ((g.form (γ b) (curveVelocity γ b) (modelField (η b) (γ b)) -
        g.form (γ a) (curveVelocity γ a) (modelField (η a) (γ a))) +
        ∫ t in a..b, -g.form (γ t) (g.covariantAlong (curveVelocity γ) t)
          (modelField (η t) (γ t))) 0 := quadraticAction_hasDerivAt g hab hγ hη

example {γ : ℝ → MinkowskiModel d} {a b : ℝ} (hab : a < b) (hγ : ContDiff ℝ 2 γ) :
    (∀ η : ℝ → MinkowskiModel d, Mechanics.FixedEndpointVariation a b η →
      HasDerivAt (fun ε => quadraticAction g (Variational.perturb γ η ε) a b) 0 0) ↔
      g.IsGeodesicOn (Ioo a b) γ := quadraticAction_stationary_iff_geodesic g hab hγ

example (m : ℝ) {γ : ℝ → MinkowskiModel d} {t : ℝ}
    (hγ : ContDiffAt ℝ 2 γ t) (hv : Timelike g (curveVelocity γ t)) (w : MinkowskiModel d) :
    Mechanics.eulerLagrange (freeLagrangian (modelMetric g) m) γ t w =
      -(m / speedAlong g γ t) * g.form (γ t)
        (g.covariantAlong (curveVelocity γ) t -
          (deriv (speedAlong g γ) t / speedAlong g γ t) • curveVelocity γ t)
        (modelField w (γ t)) := free_eulerLagrange_native g m hγ hv w

example {m : ℝ} (hm : 0 < m) {γ : ℝ → MinkowskiModel d} {a b : ℝ}
    (hab : a < b) (hγ : ContDiff ℝ 2 γ)
    (hv : ∀ t ∈ Icc a b, Timelike g (curveVelocity γ t)) :
    (∀ η : ℝ → MinkowskiModel d, Mechanics.FixedEndpointVariation a b η →
      HasDerivAt (fun ε => freeAction g m (Variational.perturb γ η ε) a b) 0 0) ↔
      ∀ t ∈ Ioo a b, g.covariantAlong (curveVelocity γ) t =
        (deriv (speedAlong g γ) t / speedAlong g γ t) • curveVelocity γ t :=
  freeAction_stationary_iff_acceleration g hm hab hγ hv

example {m : ℝ} (hm : 0 < m) {γ : ℝ → MinkowskiModel d} {a b : ℝ}
    (hab : a < b) (hγ : ContDiff ℝ 2 γ)
    (hv : ∀ t ∈ Icc a b, Timelike g (curveVelocity γ t)) :
    (∀ η : ℝ → MinkowskiModel d, Mechanics.FixedEndpointVariation a b η →
      HasDerivAt (fun ε => freeAction g m (Variational.perturb γ η ε) a b) 0 0) ↔
      ∀ t₀ ∈ Ioo a b, ∃ e : OpenPartialHomeomorph ℝ ℝ,
        t₀ ∈ e.source ∧ e.source ⊆ Ioo a b ∧
        (∀ τ ∈ e.target, ContDiffAt ℝ 2 e.symm τ ∧ 0 < deriv e.symm τ) ∧
        g.IsGeodesicOn e.target (γ ∘ e.symm) :=
  freeAction_stationary_iff_localGeodesic g hm hab hγ hv

example {m : ℝ} (hm : 0 < m) {γ : ℝ → MinkowskiModel d} {a b : ℝ}
    (hab : a < b) (hγ : ContDiff ℝ 2 γ)
    (hunit : ∀ t ∈ Icc a b, speedAlong g γ t = 1) :
    (∀ η : ℝ → MinkowskiModel d, Mechanics.FixedEndpointVariation a b η →
      HasDerivAt (fun ε => freeAction g m (Variational.perturb γ η ε) a b) 0 0) ↔
      g.IsGeodesicOn (Ioo a b) γ :=
  freeAction_stationary_iff_geodesic_of_unitSpeed g hm hab hγ hunit

example (g : LorentzMetric .timeNegative d (MinkowskiModel d))
    {m : ℝ} (hm : 0 < m) {γ : ℝ → (MinkowskiModel d)} {a b : ℝ}
    (hab : a < b) (hγ : ContDiff ℝ 2 γ)
    (hv : ∀ t ∈ Icc a b, Timelike g (curveVelocity γ t))
    (hs : ∀ η : ℝ → (MinkowskiModel d), Mechanics.FixedEndpointVariation a b η →
      HasDerivAt (fun ε => freeAction g m (Variational.perturb γ η ε) a b) 0 0) :
    ∃ r : ℝ → ℝ,
      r 0 = a ∧ r (properTime g γ a b) = b ∧
      MapsTo r (Icc 0 (properTime g γ a b)) (Icc a b) ∧
      (∀ τ ∈ Icc 0 (properTime g γ a b),
        ContDiffAt ℝ 2 r τ ∧ HasDerivAt r (speedAlong g γ (r τ))⁻¹ τ ∧
        properTime g γ a (r τ) = τ ∧ speedAlong g (γ ∘ r) τ = 1) ∧
      g.IsGeodesicOn (Ioo 0 (properTime g γ a b)) (γ ∘ r) :=
  freeAction_stationary_finite_properTime g hm hab hγ hv hs

end CoordinateVariation

section Examples

example {d : ℕ} (γ : ℝ → MinkowskiModel d) (a b : ℝ) :
    properTime (minkowskiMetric .timeNegative d) γ a b = SpecialRelativity.properTime γ a b :=
  properTime_minkowski γ a b

example (m : ℝ) (γ : ℝ → SpecialRelativity.Spacetime) (a b : ℝ) :
    freeAction (minkowskiMetric .timeNegative 3) m γ a b =
      SpecialRelativity.freeAction m γ a b := freeAction_minkowski m γ a b

example (m : ℝ) (γ : ℝ → SpecialRelativity.Spacetime) (a b : ℝ) :
    freeAction (minkowskiMetric .timeNegative 3) m γ a b =
      Mechanics.action a b (SpecialRelativity.freeLagrangian m) γ :=
  freeAction_minkowski_eq_mechanics m γ a b

example (a b : ℝ) :
    properTime LorentzianCharts.metric LorentzianCharts.inertialTimePath a b = b - a :=
  ClockExamples.shear_properTime a b

example (x a b : ℝ) :
    properTime LorentzianConformalExample.metric (ClockExamples.stationaryClock x) a b =
      (b - a) * Real.exp (x ^ 2) := ClockExamples.conformal_clock_properTime x a b

example (x a b : ℝ) :
    quadraticAction LorentzianConformalExample.metric (ClockExamples.stationaryClock x) a b =
      -(b - a) / 2 * Real.exp (2 * x ^ 2) := ClockExamples.conformal_clock_quadraticAction x a b

example {m a b : ℝ} (hm : 0 < m) (hab : a < b) :
    ∀ η : ℝ → LorentzianCharts.Plane, Mechanics.FixedEndpointVariation a b η →
      HasDerivAt (fun ε => freeAction LorentzianCharts.metric m
        (Variational.perturb ParticleExamples.exponentialClock η ε) a b) 0 0 :=
  ParticleExamples.exponentialClock_free_stationary hm hab

example {a b : ℝ} (hab : a < b) :
    ¬(∀ η : ℝ → LorentzianCharts.Plane, Mechanics.FixedEndpointVariation a b η →
      HasDerivAt (fun ε => quadraticAction LorentzianCharts.metric
        (Variational.perturb ParticleExamples.exponentialClock η ε) a b) 0 0) :=
  ParticleExamples.exponentialClock_not_quadratic_stationary hab

example (a b : ℝ) :
    properTime LorentzianCharts.metric ParticleExamples.exponentialClock a b =
      Real.exp b - Real.exp a := ParticleExamples.exponentialClock_properTime a b

example {a b : ℝ} (hab : a < b) :
    ∃ r : ℝ → ℝ, r 0 = a ∧ r (Real.exp b - Real.exp a) = b ∧
      MapsTo r (Icc 0 (Real.exp b - Real.exp a)) (Icc a b) ∧
      (∀ τ ∈ Icc 0 (Real.exp b - Real.exp a),
        ContDiffAt ℝ 2 r τ ∧ r τ = Real.log (τ + Real.exp a) ∧
        speedAlong LorentzianCharts.metric (ParticleExamples.exponentialClock ∘ r) τ = 1) ∧
      LorentzianCharts.metric.IsGeodesicOn (Ioo 0 (Real.exp b - Real.exp a)) (ParticleExamples.exponentialClock ∘ r) :=
  ParticleExamples.exponentialClock_finite_parameter hab

example :
    HasDerivAt (fun ε => quadraticAction LorentzianCharts.metric
      (fun t => VariationExamples.nonlinearFamily (ε, t)) 0 1) 0 0 :=
  VariationExamples.nonlinearFamily_quadratic_stationary

example (m : ℝ) :
    HasDerivAt (fun ε => freeAction LorentzianCharts.metric m
      (fun t => VariationExamples.nonlinearFamily (ε, t)) 0 1) 0 0 :=
  VariationExamples.nonlinearFamily_free_stationary m

example (w : LorentzianCharts.Plane) :
    variationField (VariationExamples.localTest w) (1 / 2) =
      chartField LorentzianCharts.inertialChart w (LorentzianCharts.inertialTimePath (1 / 2)) :=
  VariationExamples.localTest_field_center w

example {m a b : ℝ} (hm : 0 < m) (hab : a < b) :
    FreeStationary LorentzianCharts.metric m ParticleExamples.exponentialClock a b :=
  VariationExamples.exponentialClock_native_free_stationary hm hab

example {a b : ℝ} (hab : a < b) :
    ¬QuadraticStationary LorentzianCharts.metric ParticleExamples.exponentialClock a b :=
  VariationExamples.exponentialClock_not_native_quadratic_stationary hab

end Examples

section NewtonianFamily

open NewtonianMetricFamily
variable {U : TopologicalSpace.Opens NewtonianCoordinates} (f : NewtonianMetricFamily U)

example {c : ℝ} (hc : 1 ≤ c) {q : NewtonianCoordinates} (hq : q ∈ U) :
    ‖fderiv ℝ (fderiv ℝ (f.spatialCorrection c)) q‖ ≤ f.bound :=
  (f.spatial_bound c hc).second q hq

example (c : ℝ) (q : NewtonianCoordinates) (i j : Fin 3) :
    f.coefficient c q i.succ j.succ =
      (if i = j then 1 else 0) + (c ^ 2)⁻¹ * f.spatialCorrection c q i j :=
  f.coefficient_spatial c q i j

example {c : ℝ} (hc : 0 < c) {q : NewtonianCoordinates} (hq : q ∈ U) (i j : Fin 4) :
    f.coefficient c q i j = f.coefficient c q j i := f.coefficient_symmetric hc hq i j

example {c : ℝ} (hc : 0 < c) : ContDiffOn ℝ ∞ (f.form c) U := f.form_contDiffOn hc

example {c : ℝ} (hc : 1 ≤ c) {q : NewtonianCoordinates} (hq : q ∈ U)
    {v : NewtonianSpace} {V : ℝ} (hv : ‖v‖ ≤ V) (hV : 0 ≤ V) :
    f.form c q (timeVelocity v) (timeVelocity v) ≤
      -c ^ 2 + (3 * f.bound + 6 * f.bound * V + (3 + 9 * f.bound) * V ^ 2) :=
  f.form_timeVelocity_le hc hq hv hV

example {V : ℝ} (hV : 0 ≤ V) :
    ∀ᶠ c in Filter.atTop, ∀ q ∈ U, ∀ v : NewtonianSpace, ‖v‖ ≤ V →
      f.form c q (timeVelocity v) (timeVelocity v) < 0 :=
  f.eventually_form_timeVelocity_neg hV

example {c : ℝ} (hc : 1 ≤ c) {q : NewtonianCoordinates} (hq : q ∈ U)
    (hlarge : 9 * f.bound < c ^ 2) {v : NewtonianSpace} (hv : v ≠ 0) :
    0 < f.form c q (Fin.cons 0 v) (Fin.cons 0 v) := f.form_spatial_pos hc hq hlarge hv

example : fderiv ℝ NewtonianExamples.family.potential NewtonianExamples.sample
    (Pi.single 0 1) = 1 / 2 := NewtonianExamples.potential_time_derivative

end NewtonianFamily

section PhysicalTime

variable {M : Type} [TopologicalSpace M] [ChartedSpace (MinkowskiModel 3) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel 3) ∞ M] (g : LorentzMetric .timeNegative 3 M)

example (e : OpenPartialHomeomorph M NewtonianCoordinates) (q : NewtonianCoordinates)
    (v : NewtonianSpace) (k : Fin 3) :
    coordinateTimeAcceleration g e q v k =
      -(∑ i : Fin 4, ∑ j : Fin 4, g.chartChristoffel e (e.symm q) k.succ i j *
        NewtonianMetricFamily.timeVelocity v i * NewtonianMetricFamily.timeVelocity v j) +
      v k * (∑ i : Fin 4, ∑ j : Fin 4, g.chartChristoffel e (e.symm q) 0 i j *
        NewtonianMetricFamily.timeVelocity v i * NewtonianMetricFamily.timeVelocity v j) := rfl

example {e : OpenPartialHomeomorph M NewtonianCoordinates}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel 3) ∞ M)
    {γ : ℝ → M} {t : ℝ} (hx : γ t ∈ e.source)
    (hγ : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, MinkowskiModel 3) 2 γ t)
    (hclock : (fun s => e (γ s) 0) =ᶠ[𝓝 t] id) :
    (∃ a : ℝ, g.covariantAlong (curveVelocity γ) t = a • curveVelocity γ t) ↔
      ∀ k : Fin 3, deriv (deriv (e ∘ γ)) t k.succ =
        coordinateTimeAcceleration g e (e (γ t)) (fun j => deriv (e ∘ γ) t j.succ) k :=
  tangential_iff_coordinateTime g he hx hγ hclock

example {e : OpenPartialHomeomorph M NewtonianCoordinates}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel 3) ∞ M)
    {γ : ℝ → M} {r : ℝ → ℝ} {t : ℝ} (hx : γ (r t) ∈ e.source)
    (hγ : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, MinkowskiModel 3) 2 γ (r t))
    (hr : ContDiffAt ℝ 2 r t) (hn : deriv r t ≠ 0)
    (hgeo : g.covariantAlong (curveVelocity γ) (r t) = 0)
    (hclock : (fun s => e (γ (r s)) 0) =ᶠ[𝓝 t] id) :
    ∀ k : Fin 3, deriv (deriv (e ∘ γ ∘ r)) t k.succ =
      coordinateTimeAcceleration g e (e (γ (r t)))
        (fun j => deriv (e ∘ γ ∘ r) t j.succ) k :=
  coordinateTime_of_affine_reparam g he hx hγ hr hn hgeo hclock

example {e : OpenPartialHomeomorph M NewtonianCoordinates}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel 3) ∞ M)
    {z : NewtonianCoordinates × NewtonianSpace} (hz : z.1 ∈ e.target) :
    ContDiffAt ℝ ∞ (fun y : NewtonianCoordinates × NewtonianSpace =>
      coordinateTimeAcceleration g e y.1 y.2) z := coordinateTimeAcceleration_contDiffAt g he hz

end PhysicalTime

section NewtonianNativeMetric

open NewtonianMetricFamily

variable {U : TopologicalSpace.Opens NewtonianCoordinates} (f : NewtonianMetricFamily U)
  {c : ℝ} (hc : 1 ≤ c) (hlarge : 9 * f.bound < c^2)

example (q : U) :
    ∃ e : NewtonianCoordinates ≃L[ℝ] NewtonianCoordinates,
      ∀ v w, f.form c q v w = minkowskiForm .timeNegative 3 (e v) (e w) :=
  f.form_signature hc hlarge q

example (x q : U) (i j : Fin 4) :
    (f.lorentzMetric c hc hlarge).chartComponent (physicalChart x) q i j =
      f.coefficient c q i j :=
  f.lorentzMetric_component hc hlarge x q i j

example (x q : U) (k i j : Fin 4) :
    (f.lorentzMetric c hc hlarge).chartChristoffel (physicalChart x) q k i j =
      ∑ l, (f.coefficient c q)⁻¹ k l *
        (fderiv ℝ (fun z => f.coefficient c z j l) q (Pi.single i 1) +
         fderiv ℝ (fun z => f.coefficient c z l i) q (Pi.single j 1) -
         fderiv ℝ (fun z => f.coefficient c z i j) q (Pi.single l 1)) / 2 :=
  f.lorentzMetric_christoffel hc hlarge x q k i j

example (x q : U) (v : NewtonianSpace) :
    f.acceleration c q v =
      coordinateTimeAcceleration (f.lorentzMetric c hc hlarge) (physicalChart x) q v :=
  f.acceleration_eq_native hc hlarge x q v

example (q : U) {V : ℝ} (hV : 0 ≤ V) (v : NewtonianSpace) (hv : ‖v‖ ≤ V)
    (hspeed : f.timelikeThreshold V < c^2) :
    Timelike (f.lorentzMetric c hc hlarge) (x := q) (timeVelocity v) :=
  f.timelike_timeVelocity hc hlarge q hV hv hspeed

example (hc : 1 ≤ c) (hlarge : 24 * f.bound < c^2) (q : U) :
    (∀ i : Fin 4, |(f.coefficient c q)⁻¹ i 0| ≤ 2 * epsilon c) ∧
    (∀ j : Fin 4, |(f.coefficient c q)⁻¹ 0 j| ≤ 2 * epsilon c) ∧
    (∀ i j : Fin 3,
      |(f.coefficient c q)⁻¹ i.succ j.succ - (if i = j then 1 else 0)| ≤
        24 * f.bound * epsilon c) :=
  f.inverseComponent_bounds hc hlarge q

example {c : ℝ} (hc : NewtonianExamples.family.lorentzThreshold ≤ c) :
    let q : NewtonianExamples.domain := ⟨NewtonianExamples.sample, NewtonianExamples.sample_mem⟩
    let g := NewtonianExamples.family.lorentzMetric c
      (NewtonianExamples.family.one_le_of_lorentzThreshold_le hc)
      (NewtonianExamples.family.spatialBound_lt_sq_of_lorentzThreshold_le hc)
    g.chartComponent (physicalChart q) q 0 1 = epsilon c / 4 := by
  dsimp
  rw [NewtonianExamples.family.lorentzMetric_component]
  exact (NewtonianExamples.sample_coefficients c).2.1

end NewtonianNativeMetric

section NewtonianError

open NewtonianMetricFamily

variable {U : TopologicalSpace.Opens NewtonianCoordinates} (f : NewtonianMetricFamily U)

example {V : ℝ} (hV : 0 ≤ V) :
    ∀ᶠ c : ℝ in Filter.atTop, ∀ q : U, ∀ v : NewtonianSpace, ‖v‖ ≤ V →
      ‖f.acceleration c q v + f.spatialGradient q‖ ≤ f.accelerationErrorConstant V / c^2 :=
  f.eventually_acceleration_error hV

example {c V : ℝ} (hc : 1 ≤ c) (hlarge : 24 * f.bound < c^2)
    (x q : U) (hV : 0 ≤ V) {v : NewtonianSpace} (hv : ‖v‖ ≤ V) :
    ‖coordinateTimeAcceleration (f.lorentzMetric c hc
        (show 9 * f.bound < c^2 by linarith [f.bound_nonneg])) (physicalChart x) q v +
      (fun k : Fin 3 => fderiv ℝ f.potential q (Pi.single k.succ 1))‖ ≤
      f.accelerationErrorConstant V / c^2 :=
  f.native_acceleration_error hc hlarge x q hV hv

example {c a b V δ : ℝ} (hc : 1 ≤ c) (hlarge : 24 * f.bound < c^2)
    (hV : 0 ≤ V) {z w : ℝ → NewtonianSpace × NewtonianSpace}
    (hz : ContinuousOn z (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hz' : ∀ t ∈ Ico a b, HasDerivWithinAt z (f.relativisticPhaseField c t (z t)) (Ici t) t)
    (hw' : ∀ t ∈ Ico a b, HasDerivWithinAt w (f.newtonianPhaseField t (w t)) (Ici t) t)
    (hseg : ∀ t ∈ Ico a b,
      segment ℝ (Fin.cons t (w t).1 : NewtonianCoordinates) (Fin.cons t (z t).1) ⊆ U)
    (hspeed : ∀ t ∈ Ico a b, ‖(z t).2‖ ≤ V) (hδ : ‖z a - w a‖ ≤ δ) :
    ∀ t ∈ Icc a b,
      ‖z t - w t‖ ≤ gronwallBound δ (max 1 f.bound) (f.accelerationErrorConstant V / c^2) (t - a) :=
  f.phase_error_gronwall hc hlarge hV hz hw hz' hw' hseg hspeed hδ

end NewtonianError
