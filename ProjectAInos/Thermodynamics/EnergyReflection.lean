module

public import ProjectAInos.Thermodynamics.EnergyOrientation

/-!
# Reversal of the energy-coordinate convention

Reflecting the energy coordinate preserves every simple-system premise. The
pressure changes sign so that its defining form remains normalized with energy
coefficient one. Positive and negative orientations are interchanged, while
accessibility and relative-boundary geometry are transported exactly.
-/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace ProjectAInos.Thermodynamics.Physical

/-- Reverse energy and retain all work coordinates. -/
def energyReflection (n : ℕ) : SimpleCoordinates n ≃ₗᵢ[ℝ] SimpleCoordinates n where
  toFun x := (-x.1, x.2)
  invFun x := (-x.1, x.2)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by ext <;> simp [add_comm]
  map_smul' a x := by ext <;> simp
  norm_map' x := by simp [Prod.norm_def]

@[simp] theorem energyReflection_apply {n : ℕ} (x : SimpleCoordinates n) :
    energyReflection n x = (-x.1, x.2) := rfl

@[simp] theorem energyReflection_involutive {n : ℕ} (x : SimpleCoordinates n) :
    energyReflection n (energyReflection n x) = x := by simp

/-- Negating pressure retains the normalized energy coefficient after reflection. -/
theorem pressureForm_energyReflection {n : ℕ} (p : WorkCoordinates n) (x : SimpleCoordinates n) :
    pressureForm (-p) x = -pressureForm p (energyReflection n x) := by
  simp only [pressureForm, LinearMap.coe_mk, AddHom.coe_mk, Pi.neg_apply,
    energyReflection_apply, neg_mul, Finset.sum_neg_distrib]
  ring

/-- A supporting functional pulls back along energy reflection. -/
theorem SupportsAt.reflectEnergy {n : ℕ} {C : Set (SimpleCoordinates n)}
    {x : SimpleCoordinates n} {f : SimpleCoordinates n →ₗ[ℝ] ℝ}
    (hf : SupportsAt C (energyReflection n x) f) :
    SupportsAt ((energyReflection n) ⁻¹' C) x
      (f.comp (energyReflection n).toLinearEquiv.toLinearMap) := by
  refine ⟨?_, fun y hy => hf.2 _ hy⟩
  intro hzero
  apply hf.1
  apply LinearMap.ext
  intro y
  have h := LinearMap.congr_fun hzero (energyReflection n y)
  simpa using h

/-- The inverse support transport uses the same involution. -/
theorem SupportsAt.of_reflectEnergy {n : ℕ} {C : Set (SimpleCoordinates n)}
    {x : SimpleCoordinates n} {f : SimpleCoordinates n →ₗ[ℝ] ℝ}
    (hf : SupportsAt ((energyReflection n) ⁻¹' C) x f) :
    SupportsAt C (energyReflection n x)
      (f.comp (energyReflection n).toLinearEquiv.toLinearMap) := by
  refine ⟨?_, ?_⟩
  · intro hzero
    apply hf.1
    apply LinearMap.ext
    intro y
    have h := LinearMap.congr_fun hzero (energyReflection n y)
    simpa using h
  · intro y hy
    have h := hf.2 (energyReflection n y) (by simpa using hy)
    simpa using h

namespace SimpleSystem

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X} {n : ℕ}

/-- The same physical simple system with the opposite energy convention. All
regularity and boundary premises are transported, rather than postulated. -/
noncomputable def reflected (S : SimpleSystem P n) : SimpleSystem P n where
  domain := (energyReflection n) ⁻¹' S.domain
  isOpen_domain := S.isOpen_domain.preimage (energyReflection n).continuous
  convex_domain := S.convex_domain.linear_preimage (energyReflection n).toLinearEquiv.toLinearMap
  represent x := S.represent (energyReflection n x)
  mixing x hx y hy a b hab := by
    simpa only [map_add, map_smul] using
      S.mixing (energyReflection n x) hx (energyReflection n y) hy a b hab
  irreversible x hx := by
    obtain ⟨y, hy, hxy, hyx⟩ := S.irreversible (energyReflection n x) hx
    exact ⟨energyReflection n y, by simpa using hy, by simpa using hxy, by simpa using hyx⟩
  pressure x := -S.pressure (energyReflection n x)
  pressure_support x hx := by
    have hform : (pressureForm (S.pressure (energyReflection n x))).comp
        (energyReflection n).toLinearEquiv.toLinearMap =
          -pressureForm (-S.pressure (energyReflection n x)) := by
      apply LinearMap.ext
      intro y
      change pressureForm (S.pressure (energyReflection n x)) (energyReflection n y) =
        -pressureForm (-S.pressure (energyReflection n x)) y
      rw [pressureForm_energyReflection, neg_neg]
    rcases S.pressure_support (energyReflection n x) hx with h | h
    · right
      have h' := h.reflectEnergy
      rw [hform] at h'
      exact h'
    · left
      have h' := h.reflectEnergy
      rw [LinearMap.neg_comp, hform, neg_neg] at h'
      exact h'
  unique_support x hx f hf := by
    have hf' := SupportsAt.of_reflectEnergy (C := S.sector (energyReflection n x)) hf
    have hker := S.unique_support (energyReflection n x) hx
      (f.comp (energyReflection n).toLinearEquiv.toLinearMap) hf'
    ext v
    change f v = 0 ↔ pressureForm (-S.pressure (energyReflection n x)) v = 0
    rw [pressureForm_energyReflection, neg_eq_zero]
    have h : (energyReflection n v) ∈ LinearMap.ker
        (f.comp (energyReflection n).toLinearEquiv.toLinearMap) ↔
      (energyReflection n v) ∈ LinearMap.ker (pressureForm (S.pressure (energyReflection n x))) := by
      rw [hker]
    simpa using h
  pressure_locallyLipschitz := by
    intro x hx
    obtain ⟨K, t, ht, hLip⟩ := S.pressure_locallyLipschitz hx
    rw [S.isOpen_domain.nhdsWithin_eq hx] at ht
    refine ⟨K, (energyReflection n) ⁻¹' t,
      mem_nhdsWithin_of_mem_nhds ((energyReflection n).continuous.tendsto x ht), ?_⟩
    intro u hu v hv
    simpa only [edist_neg_neg, (energyReflection n).isometry.edist_eq] using hLip hu hv
  boundary_pathConnected x hx := by
    have hsector : P.forwardSector ((energyReflection n) ⁻¹' S.domain)
        (fun x => S.represent (energyReflection n x)) x =
      (energyReflection n) ⁻¹' S.sector (energyReflection n x) := rfl
    rw [hsector]
    change IsPathConnected ((energyReflection n).toHomeomorph ⁻¹' S.domain ∩
      frontier ((energyReflection n).toHomeomorph ⁻¹' S.sector (energyReflection n x)))
    rw [← (energyReflection n).toHomeomorph.preimage_frontier,
      ← Set.preimage_inter]
    exact (energyReflection n).toHomeomorph.isPathConnected_preimage.mpr
      (S.boundary_pathConnected (energyReflection n x) hx)

@[simp] theorem reflected_domain (S : SimpleSystem P n) :
    S.reflected.domain = (energyReflection n) ⁻¹' S.domain := rfl

@[simp] theorem reflected_represent (S : SimpleSystem P n) (x : SimpleCoordinates n) :
    S.reflected.represent x = S.represent (energyReflection n x) := rfl

@[simp] theorem reflected_pressure (S : SimpleSystem P n) (x : SimpleCoordinates n) :
    S.reflected.pressure x = -S.pressure (energyReflection n x) := rfl

@[simp] theorem reflected_represent_reflection (S : SimpleSystem P n) (x : SimpleCoordinates n) :
    S.reflected.represent (energyReflection n x) = S.represent x := by simp

@[simp] theorem mem_reflected_domain_reflection (S : SimpleSystem P n) (x : SimpleCoordinates n) :
    energyReflection n x ∈ S.reflected.domain ↔ x ∈ S.domain := by simp

/-- Forward sectors are exact preimages under reflection. -/
theorem reflected_sector (S : SimpleSystem P n) (x : SimpleCoordinates n) :
    S.reflected.sector x = (energyReflection n) ⁻¹' S.sector (energyReflection n x) := rfl

theorem reflected_sector_interior (S : SimpleSystem P n) (x : SimpleCoordinates n) :
    interior (S.reflected.sector x) =
      (energyReflection n) ⁻¹' interior (S.sector (energyReflection n x)) := by
  rw [reflected_sector]
  exact ((energyReflection n).toHomeomorph.preimage_interior _).symm

/-- The relative boundary, including its domain restriction, is preserved. -/
theorem reflected_boundary (S : SimpleSystem P n) (x : SimpleCoordinates n) :
    S.reflected.boundary x = (energyReflection n) ⁻¹' S.boundary (energyReflection n x) := by
  change S.reflected.domain ∩ frontier (S.reflected.sector x) = _
  rw [reflected_domain, reflected_sector]
  change (energyReflection n).toHomeomorph ⁻¹' S.domain ∩
    frontier ((energyReflection n).toHomeomorph ⁻¹' S.sector (energyReflection n x)) = _
  rw [← (energyReflection n).toHomeomorph.preimage_frontier, ← Set.preimage_inter]
  rfl

/-- The normalized pressure sign reverses under energy-coordinate reflection. -/
theorem reflected_hasSign_iff (S : SimpleSystem P n) (s : ℝ) (x : SimpleCoordinates n) :
    S.reflected.HasSign s x ↔ S.HasSign (-s) (energyReflection n x) := by
  have hform (y : SimpleCoordinates n) :
      pressureForm (S.reflected.pressure x) (y - x) =
        -pressureForm (S.pressure (energyReflection n x))
          (energyReflection n y - energyReflection n x) := by
    rw [reflected_pressure, pressureForm_energyReflection, map_sub]
  constructor
  · intro h y hy
    have hmem : energyReflection n y ∈ S.reflected.sector x := by
      change energyReflection n (energyReflection n y) ∈ S.sector (energyReflection n x)
      simpa only [energyReflection_involutive] using hy
    have h' := h (energyReflection n y) hmem
    rw [hform] at h'
    simpa only [energyReflection_involutive, mul_neg, neg_mul] using h'
  · intro h y hy
    have h' := h (energyReflection n y) hy
    change 0 ≤ s * pressureForm (S.reflected.pressure x) (y - x)
    rw [hform]
    simpa only [mul_neg, neg_mul] using h'

theorem negative_iff_reflected_positive (S : SimpleSystem P n) (x : SimpleCoordinates n) :
    S.Negative x ↔ S.reflected.Positive (energyReflection n x) := by
  simpa only [energyReflection_involutive] using
    (S.reflected_hasSign_iff 1 (energyReflection n x)).symm

theorem positive_iff_reflected_negative (S : SimpleSystem P n) (x : SimpleCoordinates n) :
    S.Positive x ↔ S.reflected.Negative (energyReflection n x) := by
  simpa only [energyReflection_involutive, neg_neg] using
    (S.reflected_hasSign_iff (-1) (energyReflection n x)).symm

theorem reflected_positive_everywhere_iff (S : SimpleSystem P n) :
    (∀ x ∈ S.reflected.domain, S.reflected.Positive x) ↔
      ∀ x ∈ S.domain, S.Negative x := by
  constructor
  · intro h x hx
    exact (S.negative_iff_reflected_positive x).mpr
      (h (energyReflection n x) ((S.mem_reflected_domain_reflection x).mpr hx))
  · intro h x hx
    exact (S.reflected_hasSign_iff 1 x).mpr (h (energyReflection n x) hx)

/-- Either the original convention or its reflected convention is positive
throughout the equilibrium domain. Empty domains cause no exception. -/
theorem positive_or_reflected_positive (S : SimpleSystem P n) :
    (∀ x ∈ S.domain, S.Positive x) ∨
      (∀ x ∈ S.reflected.domain, S.reflected.Positive x) := by
  by_cases hnonempty : S.domain.Nonempty
  · obtain ⟨x, hx⟩ := hnonempty
    rcases S.positive_or_negative hx with hp | hn
    · exact Or.inl (S.positive_everywhere hx hp)
    · exact Or.inr (S.reflected_positive_everywhere_iff.mpr (S.negative_everywhere hx hn))
  · exact Or.inl (fun x hx => False.elim (hnonempty ⟨x, hx⟩))

/-- Reflection restricts to a homeomorphism of the equilibrium domains. -/
noncomputable def reflectedDomainHomeomorph (S : SimpleSystem P n) :
    S.reflected.domain ≃ₜ S.domain :=
  (energyReflection n).toHomeomorph.subtype (fun _ => Iff.rfl)

@[simp] theorem reflectedDomainHomeomorph_val (S : SimpleSystem P n) (x : S.reflected.domain) :
    (S.reflectedDomainHomeomorph x).val = energyReflection n x.val := rfl

@[simp] theorem reflectedDomainHomeomorph_symm_val (S : SimpleSystem P n) (x : S.domain) :
    (S.reflectedDomainHomeomorph.symm x).val = energyReflection n x.val := rfl

@[simp] theorem represent_reflectedDomainHomeomorph_symm (S : SimpleSystem P n) (x : S.domain) :
    S.reflected.represent (S.reflectedDomainHomeomorph.symm x) = S.represent x := by
  change S.represent (energyReflection n (energyReflection n x.val)) = S.represent x.val
  rw [energyReflection_involutive]

/-- Comparison in reflected coordinates is comparison in the original system. -/
theorem comparison_of_reflected (S : SimpleSystem P n)
    (h : ∀ x y : S.reflected.domain,
      P.relation (S.reflected.represent x) (S.reflected.represent y) ∨
        P.relation (S.reflected.represent y) (S.reflected.represent x)) :
    ∀ x y : S.domain,
      P.relation (S.represent x) (S.represent y) ∨
        P.relation (S.represent y) (S.represent x) := by
  intro x y
  simpa only [represent_reflectedDomainHomeomorph_symm] using
    h (S.reflectedDomainHomeomorph.symm x) (S.reflectedDomainHomeomorph.symm y)

/-- Openness of strict reference strips transfers through the domain
homeomorphism, including the reverse-accessibility exclusions. -/
theorem strict_strips_open_of_reflected (S : SimpleSystem P n)
    (h : ∀ a b : S.reflected.domain, IsOpen {y : S.reflected.domain |
      (P.relation (S.reflected.represent a) (S.reflected.represent y) ∧
        ¬ P.relation (S.reflected.represent y) (S.reflected.represent a)) ∧
      (P.relation (S.reflected.represent y) (S.reflected.represent b) ∧
        ¬ P.relation (S.reflected.represent b) (S.reflected.represent y))}) :
    ∀ a b : S.domain, IsOpen {y : S.domain |
      (P.relation (S.represent a) (S.represent y) ∧
        ¬ P.relation (S.represent y) (S.represent a)) ∧
      (P.relation (S.represent y) (S.represent b) ∧
        ¬ P.relation (S.represent b) (S.represent y))} := by
  intro a b
  have hopen := (h (S.reflectedDomainHomeomorph.symm a) (S.reflectedDomainHomeomorph.symm b)).preimage
    S.reflectedDomainHomeomorph.symm.continuous
  simpa only [Set.preimage_ofPred_eq, represent_reflectedDomainHomeomorph_symm] using hopen

end SimpleSystem

end ProjectAInos.Thermodynamics.Physical
