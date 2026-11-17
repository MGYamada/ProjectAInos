/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothAlgebra.FormalSeries.Homological
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# The Birkhoff normal form in one degree of freedom

Let `H = ω · action + (terms of degree at least three)` in `ℝ[[q, p]]` with
`ω ≠ 0`. There is an automorphism `Ψ` of the algebra that preserves the Poisson
bracket and a power series `h` in one variable with `Ψ H = h(action)`,
`h = ω x + ⋯` (`exists_birkhoff_normal_form`).

The automorphism is the Lie transform of a generator `W`, the limit of the
partial generators `generatorSeq`: the step of degree `k` adds a solution of
the homological equation for the component of degree `k`, and leaves the
components of lower degree unchanged. The version
`exists_normal_form_of_resonant` starts at a degree `N` below which the series
is already normal, and does not change the series below that degree.
-/

@[expose] public section
noncomputable section

open MvPowerSeries

namespace ProjectAinos.SmoothAlgebra.FormalSeries

/-- A solution of the homological equation for the component of degree `k`. -/
def homologicalSolution (k : ℕ) (G : PhaseSeries) : PhaseSeries :=
  Classical.choose (exists_homological k (homogeneousComponent_mem k G))

theorem homologicalSolution_mem (k : ℕ) (G : PhaseSeries) :
    homologicalSolution k G ∈ homogeneous k :=
  (Classical.choose_spec (exists_homological k (homogeneousComponent_mem k G))).1

theorem exists_homogeneousComponent_eq (k : ℕ) (G : PhaseSeries) :
    ∃ c : ℝ, homogeneousComponent k G =
      bracket action (homologicalSolution k G) + c • resonant k :=
  (Classical.choose_spec (exists_homological k (homogeneousComponent_mem k G))).2

variable {ω : ℝ} {H : PhaseSeries}

theorem mem_orderGE_two_of_sub_mem (hH : H - ω • action ∈ orderGE (Fin 2) 3) :
    H ∈ orderGE (Fin 2) 2 := by
  have h1 : ω • action ∈ orderGE (Fin 2) 2 :=
    Submodule.smul_mem _ _ (homogeneous_le_orderGE 2 action_mem_homogeneous)
  simpa using add_mem (mem_orderGE_of_le hH (by norm_num : 2 ≤ 3)) h1

/-- One step of the normalization: adding a solution of the homological
equation of degree `k` to the generator makes the component of degree `k`
resonant, and changes the transformed series only from the degree `k` on. -/
theorem normalize_step (hω : ω ≠ 0) (hH : H - ω • action ∈ orderGE (Fin 2) 3)
    {W : PhaseSeries} (hW : W ∈ orderGE (Fin 2) 3) {k : ℕ} (hk : 3 ≤ k) :
    lieExp (ad (W + ω⁻¹ • homologicalSolution k (lieExp (ad W) H))) H - lieExp (ad W) H ∈
        orderGE (Fin 2) k ∧
      ∃ c : ℝ, homogeneousComponent k
        (lieExp (ad (W + ω⁻¹ • homologicalSolution k (lieExp (ad W) H))) H) =
          c • resonant k := by
  obtain ⟨F, hFdef⟩ : ∃ F : PhaseSeries, F = homologicalSolution k (lieExp (ad W) H) :=
    ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := exists_homogeneousComponent_eq k (lieExp (ad W) H)
  rw [← hFdef] at hc ⊢
  have hF : F ∈ homogeneous k := hFdef ▸ homologicalSolution_mem k _
  have hFk : ω⁻¹ • F ∈ orderGE (Fin 2) k :=
    Submodule.smul_mem _ _ (homogeneous_le_orderGE k hF)
  have hV : ω⁻¹ • F ∈ orderGE (Fin 2) (k - 2 + 2) := by
    rwa [Nat.sub_add_cancel (by omega)]
  have hH2 := mem_orderGE_two_of_sub_mem hH
  have hE := lieExp_add_sub_mem (raises_ad (j := 1) hW) (raises_ad hV) (by omega) hH2
  rw [← ad_add] at hE
  have h1 : bracket (ω⁻¹ • F) (ω • action) = -bracket action F := by
    rw [bracket_smul_left, bracket_smul_right, smul_smul, inv_mul_cancel₀ hω, one_smul,
      bracket_swap action F]
  have hbr : ad (ω⁻¹ • F) H + bracket action F ∈ orderGE (Fin 2) (k + 1) := by
    have e : ad (ω⁻¹ • F) H + bracket action F = bracket (ω⁻¹ • F) (H - ω • action) := by
      rw [bracket_sub_right, h1, sub_neg_eq_add, ad_apply]
    rw [e]
    exact mem_orderGE_of_le (bracket_mem_orderGE hFk hH) (by omega)
  have hkey : lieExp (ad (W + ω⁻¹ • F)) H - (lieExp (ad W) H - bracket action F) ∈
      orderGE (Fin 2) (k + 1) := by
    have e : lieExp (ad (W + ω⁻¹ • F)) H - (lieExp (ad W) H - bracket action F) =
        (lieExp (ad (W + ω⁻¹ • F)) H - lieExp (ad W) H - ad (ω⁻¹ • F) H) +
          (ad (ω⁻¹ • F) H + bracket action F) := by
      abel
    rw [e]
    exact add_mem (mem_orderGE_of_le hE (by omega)) hbr
  have hbF : bracket action F ∈ homogeneous k := bracket_action_mem_homogeneous hF
  constructor
  · have e : lieExp (ad (W + ω⁻¹ • F)) H - lieExp (ad W) H =
        (lieExp (ad (W + ω⁻¹ • F)) H - (lieExp (ad W) H - bracket action F)) -
          bracket action F := by
      abel
    rw [e]
    exact sub_mem (mem_orderGE_of_le hkey (Nat.le_succ k)) (homogeneous_le_orderGE k hbF)
  · refine ⟨c, ?_⟩
    rw [homogeneousComponent_congr hkey, map_sub, homogeneousComponent_eq_self hbF, hc]
    abel

/-! ### The generator -/

/-- The partial generators of the normalizing transformation, from the degree
`N` on. -/
def generatorSeq (ω : ℝ) (H : PhaseSeries) (N : ℕ) : ℕ → PhaseSeries
  | 0 => 0
  | i + 1 => generatorSeq ω H N i +
      ω⁻¹ • homologicalSolution (N + i) (lieExp (ad (generatorSeq ω H N i)) H)

theorem generatorSeq_zero (ω : ℝ) (H : PhaseSeries) (N : ℕ) : generatorSeq ω H N 0 = 0 :=
  rfl

theorem generatorSeq_succ (ω : ℝ) (H : PhaseSeries) (N i : ℕ) :
    generatorSeq ω H N (i + 1) = generatorSeq ω H N i +
      ω⁻¹ • homologicalSolution (N + i) (lieExp (ad (generatorSeq ω H N i)) H) :=
  rfl

theorem generatorSeq_succ_sub_mem (ω : ℝ) (H : PhaseSeries) (N i : ℕ) :
    generatorSeq ω H N (i + 1) - generatorSeq ω H N i ∈ orderGE (Fin 2) (i + N) := by
  rw [generatorSeq_succ, add_sub_cancel_left, Nat.add_comm]
  exact Submodule.smul_mem _ _ (homogeneous_le_orderGE _ (homologicalSolution_mem _ _))

theorem generatorSeq_mem (ω : ℝ) (H : PhaseSeries) (N i : ℕ) :
    generatorSeq ω H N i ∈ orderGE (Fin 2) N := by
  induction i with
  | zero => exact zero_mem _
  | succ i ih =>
    simpa using add_mem
      (mem_orderGE_of_le (generatorSeq_succ_sub_mem ω H N i) (Nat.le_add_left N i)) ih

/-- The generator of the normalizing transformation. -/
def generator (ω : ℝ) (H : PhaseSeries) (N : ℕ) : PhaseSeries :=
  seqLimit (generatorSeq ω H N)

theorem generator_sub_mem (ω : ℝ) (H : PhaseSeries) (N i : ℕ) :
    generator ω H N - generatorSeq ω H N i ∈ orderGE (Fin 2) (i + N) :=
  seqLimit_sub_mem (generatorSeq_succ_sub_mem ω H N) i

theorem generator_mem (ω : ℝ) (H : PhaseSeries) (N : ℕ) :
    generator ω H N ∈ orderGE (Fin 2) N := by
  simpa [generatorSeq_zero] using generator_sub_mem ω H N 0

/-- The transformed series has a resonant component in every degree from `N`
on. -/
theorem exists_component_generator (hω : ω ≠ 0) (hH : H - ω • action ∈ orderGE (Fin 2) 3)
    {N : ℕ} (hN : 3 ≤ N) (i : ℕ) :
    ∃ c : ℝ, homogeneousComponent (N + i) (lieExp (ad (generator ω H N)) H) =
      c • resonant (N + i) := by
  have hH2 := mem_orderGE_two_of_sub_mem hH
  have hWi : generatorSeq ω H N i ∈ orderGE (Fin 2) 3 :=
    mem_orderGE_of_le (generatorSeq_mem ω H N i) hN
  obtain ⟨-, c, hc⟩ := normalize_step hω hH hWi (k := N + i) (by omega)
  rw [← generatorSeq_succ] at hc
  refine ⟨c, ?_⟩
  have hW1 : generatorSeq ω H N (i + 1) ∈ orderGE (Fin 2) (1 + 2) :=
    mem_orderGE_of_le (generatorSeq_mem ω H N (i + 1)) hN
  have hV : generator ω H N - generatorSeq ω H N (i + 1) ∈
      orderGE (Fin 2) (N + i - 1 + 2) :=
    mem_orderGE_of_le (generator_sub_mem ω H N (i + 1)) (by omega)
  have hE := lieExp_add_sub_mem' (raises_ad hW1) (raises_ad hV) (by omega) hH2
  rw [← ad_add, add_sub_cancel] at hE
  rw [homogeneousComponent_congr (mem_orderGE_of_le hE (by omega))]
  exact hc

theorem lieExp_generator_sub_mem (hH : H - ω • action ∈ orderGE (Fin 2) 3) {N : ℕ}
    (hN : 3 ≤ N) : lieExp (ad (generator ω H N)) H - H ∈ orderGE (Fin 2) N := by
  have hW : generator ω H N ∈ orderGE (Fin 2) (N - 2 + 2) := by
    rw [Nat.sub_add_cancel (by omega)]
    exact generator_mem ω H N
  exact mem_orderGE_of_le
    (lieExp_sub_self_mem (raises_ad hW) (by omega) (mem_orderGE_two_of_sub_mem hH)) (by omega)

/-! ### Series in the action -/

theorem hasSubst_action : PowerSeries.HasSubst action :=
  PowerSeries.HasSubst.of_constantCoeff_zero (by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact action_mem_homogeneous 0 (by simp))

theorem action_pow_mem_homogeneous (m : ℕ) : action ^ m ∈ homogeneous (2 * m) := by
  rw [Nat.mul_comm]
  exact pow_mem_homogeneous action_mem_homogeneous m

theorem coeff_subst_action_even (h : PowerSeries ℝ) {e : Fin 2 →₀ ℕ} {m : ℕ}
    (he : e.degree = 2 * m) :
    coeff e (PowerSeries.subst action h) = PowerSeries.coeff m h * coeff e (action ^ m) := by
  rw [PowerSeries.coeff_subst hasSubst_action, finsum_eq_single _ m, smul_eq_mul]
  intro d hd
  rw [action_pow_mem_homogeneous d e (by omega), smul_zero]

theorem coeff_subst_action_odd (h : PowerSeries ℝ) {e : Fin 2 →₀ ℕ} {m : ℕ}
    (he : e.degree = 2 * m + 1) : coeff e (PowerSeries.subst action h) = 0 := by
  rw [PowerSeries.coeff_subst hasSubst_action]
  refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
  rw [action_pow_mem_homogeneous d e (by omega), smul_zero]

/-- The component of degree `2m` of a series in the action. -/
theorem homogeneousComponent_subst_action (h : PowerSeries ℝ) (m : ℕ) :
    homogeneousComponent (2 * m) (PowerSeries.subst action h) =
      PowerSeries.coeff m h • action ^ m := by
  ext e
  rw [coeff_homogeneousComponent, map_smul, smul_eq_mul]
  split_ifs with he
  · exact coeff_subst_action_even h he
  · rw [action_pow_mem_homogeneous m e he, mul_zero]

theorem smul_action_pow_injective {m : ℕ} {c c' : ℝ} (h : c • action ^ m = c' • action ^ m) :
    c = c' := by
  have h1 := congrArg (coeff (mono 0 (2 * m))) h
  rw [map_smul, map_smul, coeff_mono_zero_action_pow, smul_eq_mul, smul_eq_mul] at h1
  exact mul_right_cancel₀ (pow_ne_zero m (by norm_num)) h1

/-- The coefficient of a series in the action is read off from the component
of the degree `2m`. -/
theorem coeff_eq_of_homogeneousComponent {h : PowerSeries ℝ} {G : PhaseSeries} {m : ℕ}
    {c : ℝ} (hG : G = PowerSeries.subst action h)
    (hc : homogeneousComponent (2 * m) G = c • action ^ m) : PowerSeries.coeff m h = c := by
  rw [hG, homogeneousComponent_subst_action] at hc
  exact smul_action_pow_injective hc

/-- A series all of whose components are resonant is a series in the action. -/
theorem exists_eq_subst_action {G : PhaseSeries}
    (hG : ∀ k, ∃ c : ℝ, homogeneousComponent k G = c • resonant k) :
    ∃ h : PowerSeries ℝ, G = PowerSeries.subst action h := by
  choose c hc using hG
  refine ⟨PowerSeries.mk fun m => c (2 * m), ?_⟩
  ext e
  have h1 : coeff e G = coeff e (homogeneousComponent e.degree G) := by
    simp [coeff_homogeneousComponent]
  rw [h1, hc, map_smul, smul_eq_mul]
  rcases Nat.even_or_odd' e.degree with ⟨m, hm | hm⟩
  · rw [coeff_subst_action_even _ hm, PowerSeries.coeff_mk, hm, resonant_two_mul]
  · rw [coeff_subst_action_odd _ hm, hm, resonant_two_mul_add_one, map_zero, mul_zero]

/-! ### The normal form -/

/-- The normal form from the degree `N` on: if the components of `H` of degree
less than `N` are resonant, a Poisson automorphism that is the identity below
the degree `N` carries `H` to a series in the action. -/
theorem exists_normal_form_of_resonant (hω : ω ≠ 0)
    (hH : H - ω • action ∈ orderGE (Fin 2) 3) {N : ℕ} (hN : 3 ≤ N)
    (hres : ∀ k < N, ∃ c : ℝ, homogeneousComponent k H = c • resonant k) :
    ∃ (Ψ : PhaseSeries ≃ₐ[ℝ] PhaseSeries) (h : PowerSeries ℝ),
      (∀ f g, Ψ (bracket f g) = bracket (Ψ f) (Ψ g)) ∧
        Ψ H = PowerSeries.subst action h ∧ Ψ H - H ∈ orderGE (Fin 2) N := by
  have hW3 : generator ω H N ∈ orderGE (Fin 2) 3 :=
    mem_orderGE_of_le (generator_mem ω H N) hN
  have hsub := lieExp_generator_sub_mem hH hN
  have hall : ∀ k, ∃ c : ℝ,
      homogeneousComponent k (lieExp (ad (generator ω H N)) H) = c • resonant k := by
    intro k
    rcases lt_or_ge k N with hk | hk
    · rw [homogeneousComponent_congr (mem_orderGE_of_le hsub (by omega))]
      exact hres k hk
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hk
      exact exists_component_generator hω hH hN i
  obtain ⟨h, hh⟩ := exists_eq_subst_action hall
  exact ⟨lieAlgEquiv (generator ω H N) hW3, h,
    fun f g => lieExp_ad_bracket (j := 0) hW3 f g, hh, hsub⟩

theorem homogeneousComponent_action {k : ℕ} :
    homogeneousComponent k action = if k = 2 then action else 0 := by
  split_ifs with h
  · rw [h, homogeneousComponent_eq_self action_mem_homogeneous]
  · exact homogeneousComponent_eq_zero_of_mem action_mem_homogeneous h

/-- **The Birkhoff normal form in one degree of freedom** (Proposition 71). A
formal Hamiltonian `ω (q² + p²)/2 + ⋯` with `ω ≠ 0` is carried by a Poisson
automorphism of `ℝ[[q, p]]` to a series `h` in the action, with
`h = ω x + ⋯`. -/
theorem exists_birkhoff_normal_form (hω : ω ≠ 0) (hH : H - ω • action ∈ orderGE (Fin 2) 3) :
    ∃ (Ψ : PhaseSeries ≃ₐ[ℝ] PhaseSeries) (h : PowerSeries ℝ),
      (∀ f g, Ψ (bracket f g) = bracket (Ψ f) (Ψ g)) ∧
        Ψ H = PowerSeries.subst action h ∧ PowerSeries.coeff 0 h = 0 ∧
          PowerSeries.coeff 1 h = ω := by
  have hcomp : ∀ k < 3, homogeneousComponent k H = ω • homogeneousComponent k action := by
    intro k hk
    rw [homogeneousComponent_congr (mem_orderGE_of_le hH (by omega)), map_smul]
  have hres : ∀ k < 3, ∃ c : ℝ, homogeneousComponent k H = c • resonant k := by
    intro k hk
    rw [hcomp k hk, homogeneousComponent_action]
    interval_cases k
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨ω, by simp [resonant]⟩
  obtain ⟨Ψ, h, hΨ, hh, hsub⟩ := exists_normal_form_of_resonant hω hH le_rfl hres
  refine ⟨Ψ, h, hΨ, hh, ?_, ?_⟩
  · refine coeff_eq_of_homogeneousComponent (m := 0) hh ?_
    rw [homogeneousComponent_congr (mem_orderGE_of_le hsub (by norm_num)), hcomp 0 (by norm_num),
      homogeneousComponent_action]
    simp
  · refine coeff_eq_of_homogeneousComponent (m := 1) hh ?_
    rw [homogeneousComponent_congr (mem_orderGE_of_le hsub (by norm_num)), hcomp 2 (by norm_num),
      homogeneousComponent_action]
    simp

end ProjectAinos.SmoothAlgebra.FormalSeries
