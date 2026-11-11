module
public import ProjectAInos.Mechanics.EulerLagrange
public import ProjectAInos.Variational.LocalExtension

/-! # Variation on an open admissible jet domain

Compactness provides both a smooth extension near the reference jet and a
uniform neighborhood of admissible perturbations. The extension is auxiliary:
all conclusions concern the original action and its original derivatives.
-/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace ProjectAInos.Mechanics
variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

def pathJet (q : ℝ → Q) (t : ℝ) : ℝ × (Q × Q) := (t, q t, deriv q t)

theorem continuous_pathJet {q : ℝ → Q} (hq : ContDiff ℝ 2 q) :
    Continuous (pathJet q) :=
  continuous_id.prodMk (contDiff_positionVelocity hq).continuous

theorem fibre_fderiv_eq {L M : Lagrangian Q} {V : Set (ℝ × (Q × Q))}
    (hV : IsOpen V) (hLM : EqOn (Function.uncurry L) (Function.uncurry M) V)
    {t : ℝ} {z : Q × Q} (hz : (t, z) ∈ V) : fderiv ℝ (L t) z = fderiv ℝ (M t) z := by
  have he : L t =ᶠ[𝓝 z] M t := by
    filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hV.mem_nhds hz)] with y hy
    exact hLM hy
  exact he.fderiv_eq

theorem eulerLagrange_eq_of_local_eq {L M : Lagrangian Q}
    {V : Set (ℝ × (Q × Q))} (hV : IsOpen V)
    (hLM : EqOn (Function.uncurry L) (Function.uncurry M) V)
    {q : ℝ → Q} (hq : ContDiff ℝ 2 q) {t : ℝ} (ht : pathJet q t ∈ V) :
    eulerLagrange L q t = eulerLagrange M q t := by
  have he : momentum L q =ᶠ[𝓝 t] momentum M q := by
    filter_upwards [(continuous_pathJet hq).continuousAt.preimage_mem_nhds (hV.mem_nhds ht)] with s hs
    simp only [momentum, fibre_fderiv_eq hV hLM hs]
  simp only [eulerLagrange, force, fibre_fderiv_eq hV hLM ht, he.deriv_eq]

/-- Small perturbations remain admissible uniformly on the entire interval. -/
theorem eventually_pathJet_perturb_mem {q η : ℝ → Q} (hq : ContDiff ℝ 2 q)
    (hη : ContDiff ℝ 2 η) {a b : ℝ} {V : Set (ℝ × (Q × Q))}
    (hV : IsOpen V) (hqV : ∀ t ∈ Icc a b, pathJet q t ∈ V) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t ∈ Icc a b, pathJet (Variational.perturb q η ε) t ∈ V := by
  let p : ℝ × ℝ → ℝ × (Q × Q) := fun z =>
    (z.2, q z.2 + z.1 • η z.2, deriv q z.2 + z.1 • deriv η z.2)
  have hp : Continuous p := continuous_snd.prodMk
    ((hq.continuous.comp continuous_snd).add
      (continuous_fst.smul (hη.continuous.comp continuous_snd)) |>.prodMk
    (((contDiff_positionVelocity hq).continuous.snd.comp continuous_snd).add
      (continuous_fst.smul ((contDiff_positionVelocity hη).continuous.snd.comp continuous_snd))))
  have h := Variational.eventually_mapsTo_open isCompact_Icc hp hV
    (by simpa [p, pathJet] using hqV)
  apply h.mono
  intro ε hε t ht
  convert hε t ht using 1
  have hj := congrArg positionVelocity (Variational.jet_perturb
    (hq.differentiable (by norm_num) t) (hη.differentiable (by norm_num) t) ε)
  simpa [pathJet, p, positionVelocity, Variational.jet] using congrArg (fun z => (t, z)) hj

theorem action_perturb_eventually_eq {L M : Lagrangian Q}
    {V : Set (ℝ × (Q × Q))} (hV : IsOpen V)
    (hLM : EqOn (Function.uncurry L) (Function.uncurry M) V)
    {q η : ℝ → Q} (hq : ContDiff ℝ 2 q) (hη : ContDiff ℝ 2 η)
    {a b : ℝ} (hab : a ≤ b) (hqV : ∀ t ∈ Icc a b, pathJet q t ∈ V) :
    (fun ε => action a b L (Variational.perturb q η ε)) =ᶠ[𝓝 0]
      (fun ε => action a b M (Variational.perturb q η ε)) := by
  apply (eventually_pathJet_perturb_mem hq hη hV hqV).mono
  intro ε hε
  apply intervalIntegral.integral_congr
  intro t ht
  exact hLM (hε t (by simpa [uIcc_of_le hab] using ht))

variable [FiniteDimensional ℝ Q]

theorem exists_local_lagrangian_extension {L : Lagrangian Q} {q : ℝ → Q}
    (hq : ContDiff ℝ 2 q) {a b : ℝ} {U : Set (ℝ × (Q × Q))}
    (hU : IsOpen U) (hL : ContDiffOn ℝ 2 (Function.uncurry L) U)
    (hqU : ∀ t ∈ Icc a b, pathJet q t ∈ U) :
    ∃ M : Lagrangian Q, ContDiff ℝ 2 (Function.uncurry M) ∧
      ∃ V, IsOpen V ∧ (∀ t ∈ Icc a b, pathJet q t ∈ V) ∧
        EqOn (Function.uncurry L) (Function.uncurry M) V := by
  obtain ⟨g, hg, V, hV, hKV, he⟩ := Variational.exists_contDiff_extension_near_compact
    (isCompact_Icc.image (continuous_pathJet hq)) hU
    (by rintro _ ⟨t, ht, rfl⟩; exact hqU t ht) hL
  exact ⟨Function.curry g, hg, V, hV, fun t ht => hKV ⟨t, ht, rfl⟩, he.symm⟩

/-- The compact-interval first variation requires C² regularity only on an
open neighborhood of the reference jet. Domination follows by localization
from the established global compact-interval theorem. -/
theorem hasDerivAt_action_firstVariation_on {L : Lagrangian Q} {q η : ℝ → Q}
    {a b : ℝ} (hab : a ≤ b) (hq : ContDiff ℝ 2 q) (hη : ContDiff ℝ 2 η)
    {U : Set (ℝ × (Q × Q))} (hU : IsOpen U)
    (hL : ContDiffOn ℝ 2 (Function.uncurry L) U)
    (hqU : ∀ t ∈ Icc a b, pathJet q t ∈ U) :
    HasDerivAt (fun ε => action a b L (Variational.perturb q η ε))
      (firstVariation a b L q η) 0 := by
  obtain ⟨M, hM, V, hV, hqV, he⟩ := exists_local_lagrangian_extension hq hU hL hqU
  have hi : firstVariation a b L q η = firstVariation a b M q η := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htV := hqV t (by simpa [uIcc_of_le hab] using ht)
    simp only [force, momentum, fibre_fderiv_eq hV he htV]
  rw [hi]
  exact (hasDerivAt_action_firstVariation hab hM hq hη).congr_of_eventuallyEq
    (action_perturb_eventually_eq hV he hq hη hab hqV)

/-- Fixed-endpoint stationarity is equivalent to Euler–Lagrange on the actual
open domain; no global extension is part of the statement or a physical premise. -/
theorem stationary_iff_eulerLagrange_on {L : Lagrangian Q} {q : ℝ → Q}
    {a b : ℝ} (hab : a < b) (hq : ContDiff ℝ 2 q)
    {U : Set (ℝ × (Q × Q))} (hU : IsOpen U)
    (hL : ContDiffOn ℝ 2 (Function.uncurry L) U)
    (hqU : ∀ t ∈ Icc a b, pathJet q t ∈ U) :
    Stationary a b L q ↔ ∀ t ∈ Ioo a b, eulerLagrange L q t = 0 := by
  obtain ⟨M, hM, V, hV, hqV, he⟩ := exists_local_lagrangian_extension hq hU hL hqU
  have hs : Stationary a b L q ↔ Stationary a b M q := by
    apply forall_congr'
    intro η
    apply forall_congr'
    intro hη
    have h := action_perturb_eventually_eq hV he hq (hη.smooth.of_le (by norm_num)) hab.le hqV
    exact ⟨fun hd => hd.congr_of_eventuallyEq h.symm, fun hd => hd.congr_of_eventuallyEq h⟩
  rw [hs, stationary_iff_eulerLagrange hab hM hq]
  apply forall_congr'
  intro t
  apply forall_congr'
  intro ht
  rw [eulerLagrange_eq_of_local_eq hV he hq (hqV t ⟨ht.1.le, ht.2.le⟩)]

end ProjectAInos.Mechanics
