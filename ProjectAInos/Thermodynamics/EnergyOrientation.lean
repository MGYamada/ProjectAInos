module

public import ProjectAInos.Thermodynamics.SectorGeometry
public import Mathlib.Topology.Connected.Clopen

/-!
# Orientation of energy in a simple system

The direction of a forward sector is encoded without initially choosing the
positive-energy convention. Local vertical interior and the collinear lemma
compare every state with an appropriately oriented higher-energy target.
-/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace ProjectAInos.Thermodynamics.Physical.SimpleSystem

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X} {n : ℕ}

/-- The forward sector lies on the side selected by the nonzero energy sign. -/
def HasSign (S : SimpleSystem P n) (s : ℝ) (x : SimpleCoordinates n) : Prop :=
  ∀ y ∈ S.sector x, 0 ≤ s * pressureForm (S.pressure x) (y - x)

abbrev Positive (S : SimpleSystem P n) (x : SimpleCoordinates n) : Prop := S.HasSign 1 x
abbrev Negative (S : SimpleSystem P n) (x : SimpleCoordinates n) : Prop := S.HasSign (-1) x

/-- States of the specified orientation, restricted to the equilibrium domain. -/
def signedStates (S : SimpleSystem P n) (s : ℝ) : Set (SimpleCoordinates n) :=
  {x | x ∈ S.domain ∧ S.HasSign s x}

theorem positive_or_negative (S : SimpleSystem P n) {x : SimpleCoordinates n}
    (hx : x ∈ S.domain) : S.Positive x ∨ S.Negative x := by
  obtain h | h := S.pressure_support x hx
  · right
    intro y hy
    have hle := h.2 y hy
    simp only [neg_mul, one_mul, map_sub]
    linarith
  · left
    intro y hy
    have hle := h.2 y hy
    simp only [LinearMap.neg_apply] at hle
    simp only [one_mul, map_sub]
    linarith

theorem HasSign.support (S : SimpleSystem P n) {s : ℝ} (hs : s ≠ 0)
    {x : SimpleCoordinates n} (h : S.HasSign s x) :
    SupportsAt (S.sector x) x ((-s) • pressureForm (S.pressure x)) := by
  constructor
  · intro hf
    have he := congrArg (fun f : SimpleCoordinates n →ₗ[ℝ] ℝ => f (1, 0)) hf
    simp at he
    exact hs he
  · intro y hy
    have hle := h y hy
    simp only [map_sub] at hle
    simp only [LinearMap.smul_apply, smul_eq_mul]
    nlinarith

theorem HasSign.strict_of_mem_interior (S : SimpleSystem P n) {s : ℝ} (hs : s ≠ 0)
    {x y : SimpleCoordinates n} (h : S.HasSign s x)
    (hy : y ∈ interior (S.sector x)) :
    0 < s * pressureForm (S.pressure x) (y - x) := by
  have hlt := (HasSign.support S hs h).lt_of_mem_interior hy
  simp only [LinearMap.smul_apply, smul_eq_mul] at hlt
  simp only [map_sub]
  nlinarith

theorem not_hasSign_neg (S : SimpleSystem P n) {s : ℝ} (hs : s ≠ 0)
    {x : SimpleCoordinates n} (hx : x ∈ S.domain) (h : S.HasSign s x) :
    ¬ S.HasSign (-s) x := by
  intro hn
  obtain ⟨y, hy⟩ := S.forwardSector_interior_nonempty x hx
  have hp := HasSign.strict_of_mem_interior S hs h hy
  have hm := hn y (interior_subset hy)
  nlinarith

theorem HasSign.energy_lt_of_interior_same_work (S : SimpleSystem P n)
    {s : ℝ} (hs : s ≠ 0) {x y : SimpleCoordinates n} (h : S.HasSign s x)
    (hy : y ∈ interior (S.sector x)) (hv : y.2 = x.2) :
    s * x.1 < s * y.1 := by
  have hlt := HasSign.strict_of_mem_interior S hs h hy
  have hform : pressureForm (S.pressure x) (y - x) = y.1 - x.1 := by
    simp [pressureForm, hv]
  rw [hform] at hlt
  nlinarith

/-- Every state below a positively oriented target (or above a negatively
oriented target) on its vertical fibre can reach that target. -/
theorem accessible_of_signed_energy_lt (S : SimpleSystem P n)
    {s : ℝ} (hs : s ≠ 0) {x y : SimpleCoordinates n}
    (hx : x ∈ S.domain) (hy : y ∈ S.domain) (hv : x.2 = y.2)
    (hysign : S.HasSign s y) (hlt : s * x.1 < s * y.1) :
    P.relation (S.represent x) (S.represent y) := by
  obtain ⟨z, hz, hzv⟩ := S.exists_interior_same_work hy
  have hyz := HasSign.energy_lt_of_interior_same_work S hs hysign hz hzv
  have hden : 0 < s * z.1 - s * x.1 := by linarith
  let a : ℝ≥0 := ⟨(s * z.1 - s * y.1) / (s * z.1 - s * x.1), by positivity⟩
  let b : ℝ≥0 := ⟨(s * y.1 - s * x.1) / (s * z.1 - s * x.1), by positivity⟩
  have ha : 0 < a := by
    change 0 < (s * z.1 - s * y.1) / (s * z.1 - s * x.1)
    exact div_pos (sub_pos.mpr hyz) hden
  have hab : a + b = 1 := by
    apply Subtype.ext
    change (s * z.1 - s * y.1) / (s * z.1 - s * x.1) +
      (s * y.1 - s * x.1) / (s * z.1 - s * x.1) = 1
    rw [← add_div]
    convert div_self hden.ne' using 1
    ring
  have hzx : z.1 - x.1 ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    simp [he] at hden
  have hcoord : y = (a : ℝ) • x + (b : ℝ) • z := by
    apply Prod.ext
    · change y.1 = (a : ℝ) * x.1 + (b : ℝ) * z.1
      apply mul_left_cancel₀ hs
      change s * y.1 = s *
        (((s * z.1 - s * y.1) / (s * z.1 - s * x.1)) * x.1 +
        ((s * y.1 - s * x.1) / (s * z.1 - s * x.1)) * z.1)
      field_simp [hzx]
      ring
    · change y.2 = (a : ℝ) • x.2 + (b : ℝ) • z.2
      rw [hv, hzv, ← add_smul]
      have hsum : (a : ℝ) + (b : ℝ) = 1 := congrArg (fun q : ℝ≥0 => (q : ℝ)) hab
      rw [hsum, one_smul]
  exact P.collinear_accessibility S.domain S.represent S.mixing hx
    (interior_subset hz).1 ha hab hcoord (interior_subset hz).2

/-- A vertical interior point can be chosen subject to any strict energy bound
already satisfied by the anchor; no orientation is required here. -/
theorem exists_vertical_interior_with_bound (S : SimpleSystem P n)
    {x : SimpleCoordinates n} (hx : x ∈ S.domain) (s B : ℝ)
    (hB : s * x.1 < B) :
    ∃ u : ℝ, (u, x.2) ∈ interior (S.sector x) ∧ s * u < B := by
  obtain ⟨w, hw, hwv⟩ := S.exists_interior_same_work hx
  have hlim : Tendsto (fun t : ℝ => s * ((1 - t) * x.1 + t * w.1))
      (𝓝 0) (𝓝 (s * x.1)) := by
    have hc : Continuous (fun t : ℝ => s * ((1 - t) * x.1 + t * w.1)) :=
      continuous_const.mul (((continuous_const.sub continuous_id).mul continuous_const).add
        (continuous_id.mul continuous_const))
    simpa using hc.tendsto (0 : ℝ)
  have ht1 : ∀ᶠ t : ℝ in 𝓝 0, t < 1 := gt_mem_nhds (by norm_num)
  obtain ⟨t, ht, ht1', htB⟩ := (ht1.and (hlim.eventually (gt_mem_nhds hB))).exists_gt
  have hw' : (w.1, x.2) ∈ interior (S.sector x) := by
    simpa only [← hwv, Prod.eta] using hw
  exact ⟨(1 - t) * x.1 + t * w.1,
    S.vertical_between_mem_interior hx hw' ht ht1', htB⟩

/-- Oppositely oriented states cannot accumulate at an equilibrium state.
The argument uses relative closedness of forward sectors rather than assuming
continuity of the orientation. -/
theorem not_mem_closure_signedStates (S : SimpleSystem P n)
    {s : ℝ} (hs : s ≠ 0) {x : SimpleCoordinates n} (hx : x ∈ S.domain)
    (hxsign : S.HasSign (-s) x) : x ∉ closure (S.signedStates s) := by
  obtain ⟨z, hz, hzv⟩ := S.exists_interior_same_work hx
  have hzdomain := (interior_subset hz).1
  have hxz := (interior_subset hz).2
  have hzx : s * z.1 < s * x.1 := by
    have h := HasSign.energy_lt_of_interior_same_work S (neg_ne_zero.mpr hs) hxsign hz hzv
    nlinarith
  obtain ⟨u, hu, hub⟩ := S.exists_vertical_interior_with_bound hzdomain s (s * x.1) hzx
  have hxnot : x ∉ closure (S.sector z) := by
    intro hxc
    have hxC : x ∈ S.sector z := by
      have hmem : x ∈ closure (S.sector z) ∩ S.domain := ⟨hxc, hx⟩
      rw [P.forwardSector_closure_inter S.domain S.represent S.isOpen_domain
        S.convex_domain S.mixing z hzdomain] at hmem
      exact hmem
    have hsub : S.sector x ⊆ S.sector z := S.sector_subset_of_mem hxC
    exact S.self_not_mem_interior hzdomain (interior_mono hsub hz)
  let U : Set (SimpleCoordinates n) :=
    {y | (u, y.2) ∈ interior (S.sector z)} ∩
      {y | s * u < s * y.1} ∩ (closure (S.sector z))ᶜ
  have hU : IsOpen U := by
    apply IsOpen.inter
    · apply IsOpen.inter
      · exact isOpen_interior.preimage (continuous_const.prodMk continuous_snd)
      · exact isOpen_lt continuous_const (continuous_const.mul continuous_fst)
    · exact isClosed_closure.isOpen_compl
  have hxU : x ∈ U := by
    refine ⟨⟨?_, hub⟩, hxnot⟩
    change (u, x.2) ∈ interior (S.sector z)
    simpa only [hzv] using hu
  intro hclosure
  obtain ⟨y, hyU, hy⟩ := mem_closure_iff.mp hclosure U hU hxU
  have hcy : (u, y.2) ∈ S.sector z := interior_subset hyU.1.1
  have hcmp := S.accessible_of_signed_energy_lt hs hcy.1 hy.1 rfl hy.2 hyU.1.2
  exact hyU.2 (subset_closure ⟨hy.1, P.trans hcy.2 hcmp⟩)

/-- If a system admits only the two opposite signs, each sign class is open. -/
theorem signedStates_isOpen (S : SimpleSystem P n) {s : ℝ} (hs : s ≠ 0)
    (hcover : ∀ x ∈ S.domain, S.HasSign s x ∨ S.HasSign (-s) x) :
    IsOpen (S.signedStates s) := by
  have heq : S.signedStates s = S.domain ∩ (closure (S.signedStates (-s)))ᶜ := by
    ext x
    constructor
    · rintro ⟨hx, hsign⟩
      refine ⟨hx, S.not_mem_closure_signedStates (neg_ne_zero.mpr hs) hx ?_⟩
      simpa only [neg_neg] using hsign
    · rintro ⟨hx, hnot⟩
      refine ⟨hx, ?_⟩
      obtain hp | hn := hcover x hx
      · exact hp
      · exact False.elim (hnot (subset_closure ⟨hx, hn⟩))
  rw [heq]
  exact S.isOpen_domain.inter isClosed_closure.isOpen_compl

/-- Connectedness of the equilibrium domain makes a two-valued orientation
constant. Openness of the sign classes was derived from accessibility. -/
theorem sign_constant (S : SimpleSystem P n) {s : ℝ} (hs : s ≠ 0)
    (hcover : ∀ x ∈ S.domain, S.HasSign s x ∨ S.HasSign (-s) x)
    {x : SimpleCoordinates n} (hx : x ∈ S.domain) (hxsign : S.HasSign s x) :
    ∀ y ∈ S.domain, S.HasSign s y := by
  have hop := S.signedStates_isOpen hs hcover
  have hon : IsOpen (S.signedStates (-s)) := by
    apply S.signedStates_isOpen (neg_ne_zero.mpr hs)
    intro y hy
    simpa only [neg_neg] using (hcover y hy).symm
  have hdisj : Disjoint (S.signedStates s) (S.signedStates (-s)) := by
    apply Set.disjoint_left.mpr
    intro y hy hn
    exact S.not_hasSign_neg hs hy.1 hy.2 hn.2
  have hsubset : S.domain ⊆ S.signedStates s ∪ S.signedStates (-s) := by
    intro y hy
    exact (hcover y hy).imp (fun h => ⟨hy, h⟩) (fun h => ⟨hy, h⟩)
  have hall := S.convex_domain.isPreconnected.subset_left_of_subset_union
    hop hon hdisj hsubset ⟨x, hx, hx, hxsign⟩
  exact fun y hy => (hall hy).2

/-- LY 3.3: one positive forward sector fixes the positive orientation throughout
the simple system. -/
theorem positive_everywhere (S : SimpleSystem P n)
    {x : SimpleCoordinates n} (hx : x ∈ S.domain) (hxsign : S.Positive x) :
    ∀ y ∈ S.domain, S.Positive y :=
  S.sign_constant one_ne_zero (fun _ hy => S.positive_or_negative hy) hx hxsign

/-- The corresponding negative orientation is also globally consistent. -/
theorem negative_everywhere (S : SimpleSystem P n)
    {x : SimpleCoordinates n} (hx : x ∈ S.domain) (hxsign : S.Negative x) :
    ∀ y ∈ S.domain, S.Negative y := by
  apply S.sign_constant (by norm_num : (-1 : ℝ) ≠ 0) _ hx hxsign
  intro y hy
  simpa only [neg_neg] using (S.positive_or_negative hy).symm

/-- Entire vertical half-lines are accessible in the common orientation.
Choosing `s = 1` is Planck's principle (LY 3.4). -/
theorem accessible_iff_signed_energy_le (S : SimpleSystem P n)
    {s : ℝ} (hs : s ≠ 0)
    (hsign : ∀ z ∈ S.domain, S.HasSign s z)
    {x y : SimpleCoordinates n} (hx : x ∈ S.domain) (hy : y ∈ S.domain)
    (hv : x.2 = y.2) :
    P.relation (S.represent x) (S.represent y) ↔ s * x.1 ≤ s * y.1 := by
  constructor
  · intro hxy
    have h := hsign x hx y ⟨hy, hxy⟩
    have hform : pressureForm (S.pressure x) (y - x) = y.1 - x.1 := by
      simp [pressureForm, hv]
    rw [hform] at h
    nlinarith
  · intro hle
    obtain hlt | heq := hle.lt_or_eq
    · exact S.accessible_of_signed_energy_lt hs hx hy hv (hsign y hy) hlt
    · have he : x = y := Prod.ext (mul_left_cancel₀ hs heq) hv
      subst y
      exact P.refl _

/-- Planck's principle once a positive reference state fixes the convention. -/
theorem accessible_iff_energy_le (S : SimpleSystem P n)
    {reference x y : SimpleCoordinates n} (href : reference ∈ S.domain)
    (hrefsign : S.Positive reference) (hx : x ∈ S.domain) (hy : y ∈ S.domain)
    (hv : x.2 = y.2) :
    P.relation (S.represent x) (S.represent y) ↔ x.1 ≤ y.1 := by
  simpa only [one_mul] using S.accessible_iff_signed_energy_le one_ne_zero
    (S.positive_everywhere href hrefsign) hx hy hv

end ProjectAInos.Thermodynamics.Physical.SimpleSystem
