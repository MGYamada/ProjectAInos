/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Constants
public import ProjectAInos.Mechanics.Poisson.Trajectory
public import ProjectAInos.SmoothAlgebra.Poisson.Reduction

/-!
# Reduction with respect to cyclic co-ordinates

The phase space has co-ordinates `q_i`, `p_i` for `i : ι` and `q_k`, `p_k` for
`k : κ`. For constants `c_k` the ideal `I = (p_k − c_k)` is coisotropic, and
its normalizer consists of the functions `f` with `∂f/∂q_k ∈ I`. The reduced
ring `N(I)/I` is the phase space of the co-ordinates `q_i`, `p_i`, as a
Poisson C-infinity ring: the class of `f` is `f` at `q_k = 0`, `p_k = c_k`.

The proof has two steps. By Hadamard's lemma `f` agrees modulo `I` with `f` at
`p_k = c_k`. For `f` in the normalizer, the derivatives of that function in
the `q_k` vanish, so it does not depend on the `q_k`.

If the `q_k` are cyclic co-ordinates of a Hamiltonian `H`, then `H` is in the
normalizer, the momenta `p_k` are integrals of the motion, and the other
co-ordinates of a trajectory with `p_k = c_k` form a trajectory of the reduced
Hamiltonian `H` at `p_k = c_k` (Landau–Lifshitz §41).
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.CyclicReduction

open SmoothAlgebra SmoothRing FreeSmoothRing

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

variable (ι) in
/-- The equation `p_k − c_k = 0` for the momentum of a cyclic co-ordinate. -/
def momentumEquation (c : κ → ℝ) (k : κ) : PhaseSpace (ι ⊕ κ) :=
  PhaseSpace.p (Sum.inr k) - algebraMap ℝ (PhaseSpace (ι ⊕ κ)) (c k)

variable (ι) in
/-- The ideal `(p_k − c_k)` of the fixed values of the cyclic momenta. -/
def momentumIdeal (c : κ → ℝ) : Ideal (PhaseSpace (ι ⊕ κ)) :=
  Ideal.span (Set.range (momentumEquation ι c))

variable (ι κ) in
/-- The phase space of the remaining co-ordinates, in the full phase space. -/
def inclusion : SmoothRingHom (PhaseSpace ι) (PhaseSpace (ι ⊕ κ)) :=
  FreeSmoothRing.lift fun a => generator (Sum.map Sum.inl Sum.inl a)

variable (ι) in
/-- A function at `q_k = 0`, `p_k = c_k`, as a function of the remaining
co-ordinates. -/
def restriction (c : κ → ℝ) : SmoothRingHom (PhaseSpace (ι ⊕ κ)) (PhaseSpace ι) :=
  FreeSmoothRing.lift (Sum.elim (Sum.elim PhaseSpace.q fun _ => 0)
    (Sum.elim PhaseSpace.p fun k => algebraMap ℝ (PhaseSpace ι) (c k)))

variable (ι) in
/-- A function at `p_k = c_k`, as a function on the full phase space. -/
def fixMomenta (c : κ → ℝ) : SmoothRingHom (PhaseSpace (ι ⊕ κ)) (PhaseSpace (ι ⊕ κ)) :=
  FreeSmoothRing.lift (Sum.elim (fun a => generator (Sum.inl a))
    (Sum.elim (fun i => generator (Sum.inr (Sum.inl i)))
      fun k => algebraMap ℝ (PhaseSpace (ι ⊕ κ)) (c k)))

variable (ι κ) in
/-- A function at `q_k = 0`, as a function on the full phase space. -/
def dropCyclic : SmoothRingHom (PhaseSpace (ι ⊕ κ)) (PhaseSpace (ι ⊕ κ)) :=
  FreeSmoothRing.lift (Sum.elim (Sum.elim (fun i => generator (Sum.inl (Sum.inl i))) fun _ => 0)
    fun a => generator (Sum.inr a))

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
@[simp] theorem inclusion_generator (a : ι ⊕ ι) :
    inclusion ι κ (generator a) = generator (Sum.map Sum.inl Sum.inl a) :=
  lift_generator _ _

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- The restriction is a retraction of the inclusion. -/
theorem restriction_inclusion (c : κ → ℝ) (g : PhaseSpace ι) :
    restriction ι c (inclusion ι κ g) = g := by
  have h : (restriction ι c).comp (inclusion ι κ) = SmoothRingHom.id (PhaseSpace ι) :=
    FreeSmoothRing.hom_ext fun a => by
      rw [SmoothRingHom.comp_apply, inclusion_generator, SmoothRingHom.id_apply, restriction,
        lift_generator]
      rcases a with i | i <;> rfl
  exact congrArg (fun χ : SmoothRingHom (PhaseSpace ι) (PhaseSpace ι) => χ g) h

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem restriction_momentumEquation (c : κ → ℝ) (k : κ) :
    restriction ι c (momentumEquation ι c k) = 0 := by
  rw [momentumEquation, SmoothRingHom.map_sub, SmoothRingHom.map_algebraMap, PhaseSpace.p,
    restriction, lift_generator]
  exact sub_self _

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- The restriction vanishes on the ideal. -/
theorem restriction_eq_zero_of_mem {c : κ → ℝ} {f : PhaseSpace (ι ⊕ κ)}
    (hf : f ∈ momentumIdeal ι c) : restriction ι c f = 0 :=
  SmoothRingHom.eq_zero_of_mem_span (by
    rintro _ ⟨k, rfl⟩
    exact restriction_momentumEquation c k) hf

/-- `{f, p_k − c_k} = ∂f/∂q_k`. -/
theorem bracket_momentumEquation (c : κ → ℝ) (f : PhaseSpace (ι ⊕ κ)) (k : κ) :
    (PhaseSpace.canonical (ι ⊕ κ)).bracket f (momentumEquation ι c k) =
      partialDerivation (Sum.inl (Sum.inr k)) f := by
  rw [momentumEquation, (PhaseSpace.canonical (ι ⊕ κ)).toAlmostPoissonStructure.bracket_sub_right,
    (PhaseSpace.canonical (ι ⊕ κ)).toAlmostPoissonStructure.bracket_algebraMap_right, sub_zero,
    (PhaseSpace.canonical (ι ⊕ κ)).antisymm, PhaseSpace.canonical_p_bracket, neg_neg]

/-- The normalizer of the ideal: the functions whose derivatives in the cyclic
co-ordinates are in the ideal. -/
theorem mem_normalizer_iff {c : κ → ℝ} {f : PhaseSpace (ι ⊕ κ)} :
    f ∈ (PhaseSpace.canonical (ι ⊕ κ)).normalizer (momentumIdeal ι c) ↔
      ∀ k, partialDerivation (Sum.inl (Sum.inr k)) f ∈ momentumIdeal ι c := by
  constructor
  · intro h k
    rw [← bracket_momentumEquation c f k]
    exact h _ (Ideal.subset_span ⟨k, rfl⟩)
  · intro h
    refine PoissonStructure.mem_normalizer_span ?_
    rintro _ ⟨k, rfl⟩
    rw [bracket_momentumEquation]
    exact h k

/-- The ideal of fixed cyclic momenta is coisotropic. -/
theorem isCoisotropic_momentumIdeal (c : κ → ℝ) :
    (PhaseSpace.canonical (ι ⊕ κ)).IsCoisotropic (momentumIdeal ι c) := by
  refine PoissonStructure.isCoisotropic_span ?_
  rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
  rw [bracket_momentumEquation, momentumEquation, map_sub, SmoothDerivation.map_algebraMap,
    sub_zero, PhaseSpace.p, partialDerivation_generator_of_ne (by simp)]
  exact zero_mem _

omit [Fintype κ] in
/-- A function of the remaining co-ordinates does not depend on the cyclic
co-ordinates. -/
theorem partialDerivation_inclusion (g : PhaseSpace ι) (k : κ) :
    partialDerivation (Sum.inl (Sum.inr k)) (inclusion ι κ g) = 0 := by
  rw [inclusion, derivation_lift_mul]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [partialDerivation_generator_of_ne (by rcases a with i | i <;> simp), mul_zero]

/-- The functions of the remaining co-ordinates are in the normalizer. -/
theorem inclusion_mem_normalizer (c : κ → ℝ) (g : PhaseSpace ι) :
    inclusion ι κ g ∈ (PhaseSpace.canonical (ι ⊕ κ)).normalizer (momentumIdeal ι c) :=
  mem_normalizer_iff.mpr fun k => by
    rw [partialDerivation_inclusion]
    exact zero_mem _

/-- The inclusion of the phase space of the remaining co-ordinates is a Poisson
morphism. -/
theorem isPoissonHom_inclusion :
    IsPoissonHom (PhaseSpace.canonical ι).toAlmostPoissonStructure
      (PhaseSpace.canonical (ι ⊕ κ)).toAlmostPoissonStructure (inclusion ι κ) := by
  refine FreeSmoothRing.isPoissonHom_of_generators fun a b => ?_
  rw [inclusion_generator, inclusion_generator, PhaseSpace.canonical_bracket_generator,
    PhaseSpace.canonical_bracket_generator]
  rcases a with i | i <;> rcases b with j | j
  · exact SmoothRingHom.map_zero _
  · change inclusion ι κ (if i = j then 1 else 0) =
      if (Sum.inl i : ι ⊕ κ) = Sum.inl j then 1 else 0
    by_cases h : i = j
    · subst h
      simp only [↓reduceIte, SmoothRingHom.map_one]
    · have h' : (Sum.inl i : ι ⊕ κ) ≠ Sum.inl j := fun e => h (Sum.inl.inj e)
      simp only [h, h', ↓reduceIte, SmoothRingHom.map_zero]
  · change inclusion ι κ (if i = j then -1 else 0) =
      if (Sum.inl i : ι ⊕ κ) = Sum.inl j then -1 else 0
    by_cases h : i = j
    · subst h
      simp only [↓reduceIte, SmoothRingHom.map_neg, SmoothRingHom.map_one]
    · have h' : (Sum.inl i : ι ⊕ κ) ≠ Sum.inl j := fun e => h (Sum.inl.inj e)
      simp only [h, h', ↓reduceIte, SmoothRingHom.map_zero]
  · exact SmoothRingHom.map_zero _

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- Hadamard's lemma: a function agrees modulo the ideal with the function at
`p_k = c_k`. -/
theorem sub_fixMomenta_mem (c : κ → ℝ) (f : PhaseSpace (ι ⊕ κ)) :
    f - fixMomenta ι c f ∈ momentumIdeal ι c := by
  refine FreeSmoothRing.hom_sub_hom_mem (φ := SmoothRingHom.id _) (ψ := fixMomenta ι c)
    (fun a => ?_) f
  rw [SmoothRingHom.id_apply, fixMomenta, lift_generator]
  rcases a with a | i | k
  · rw [Sum.elim_inl, sub_self]
    exact zero_mem _
  · rw [Sum.elim_inr, Sum.elim_inl, sub_self]
    exact zero_mem _
  · exact Ideal.subset_span ⟨k, rfl⟩

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem fixMomenta_eq_zero_of_mem {c : κ → ℝ} {f : PhaseSpace (ι ⊕ κ)}
    (hf : f ∈ momentumIdeal ι c) : fixMomenta ι c f = 0 :=
  SmoothRingHom.eq_zero_of_mem_span (by
    rintro _ ⟨k, rfl⟩
    rw [momentumEquation, SmoothRingHom.map_sub, SmoothRingHom.map_algebraMap, PhaseSpace.p,
      fixMomenta, lift_generator]
    exact sub_self _) hf

/-- Fixing the cyclic momenta commutes with the derivatives in the cyclic
co-ordinates. -/
theorem partialDerivation_fixMomenta (c : κ → ℝ) (f : PhaseSpace (ι ⊕ κ)) (k : κ) :
    partialDerivation (Sum.inl (Sum.inr k)) (fixMomenta ι c f) =
      fixMomenta ι c (partialDerivation (Sum.inl (Sum.inr k)) f) := by
  rw [fixMomenta, derivation_lift_mul, Finset.sum_eq_single (Sum.inl (Sum.inr k))]
  · rw [Sum.elim_inl, partialDerivation_generator_self, mul_one]
  · intro a _ ha
    rcases a with a | i | l
    · rw [Sum.elim_inl, partialDerivation_generator_of_ne ha, mul_zero]
    · rw [Sum.elim_inr, Sum.elim_inl, partialDerivation_generator_of_ne (by simp), mul_zero]
    · rw [Sum.elim_inr, Sum.elim_inr, SmoothDerivation.map_algebraMap, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem dropCyclic_fixMomenta (c : κ → ℝ) (f : PhaseSpace (ι ⊕ κ)) :
    dropCyclic ι κ (fixMomenta ι c f) = inclusion ι κ (restriction ι c f) := by
  have h : (dropCyclic ι κ).comp (fixMomenta ι c) = (inclusion ι κ).comp (restriction ι c) :=
    FreeSmoothRing.hom_ext fun a => by
      rw [SmoothRingHom.comp_apply, SmoothRingHom.comp_apply, fixMomenta, restriction,
        lift_generator, lift_generator]
      rcases a with (i | k) | (i | k)
      · change dropCyclic ι κ (generator (Sum.inl (Sum.inl i))) =
          inclusion ι κ (generator (Sum.inl i))
        rw [dropCyclic, lift_generator, inclusion_generator]
        rfl
      · change dropCyclic ι κ (generator (Sum.inl (Sum.inr k))) = inclusion ι κ 0
        rw [dropCyclic, lift_generator, SmoothRingHom.map_zero]
        rfl
      · change dropCyclic ι κ (generator (Sum.inr (Sum.inl i))) =
          inclusion ι κ (generator (Sum.inr i))
        rw [dropCyclic, lift_generator, inclusion_generator]
        rfl
      · change dropCyclic ι κ (algebraMap ℝ _ (c k)) = inclusion ι κ (algebraMap ℝ _ (c k))
        rw [SmoothRingHom.map_algebraMap, SmoothRingHom.map_algebraMap]
  exact congrArg
    (fun χ : SmoothRingHom (PhaseSpace (ι ⊕ κ)) (PhaseSpace (ι ⊕ κ)) => χ f) h

/-- An element of the normalizer agrees modulo the ideal with its restriction
to `q_k = 0`, `p_k = c_k`. -/
theorem sub_inclusion_restriction_mem {c : κ → ℝ} {f : PhaseSpace (ι ⊕ κ)}
    (hf : f ∈ (PhaseSpace.canonical (ι ⊕ κ)).normalizer (momentumIdeal ι c)) :
    f - inclusion ι κ (restriction ι c f) ∈ momentumIdeal ι c := by
  have hd : dropCyclic ι κ (fixMomenta ι c f) = fixMomenta ι c f := by
    refine lift_eq_self_of_partialDerivation_eq_zero fun a ha => ?_
    rcases a with (i | k) | a
    · exact absurd rfl ha
    · rw [partialDerivation_fixMomenta, fixMomenta_eq_zero_of_mem (mem_normalizer_iff.mp hf k)]
    · exact absurd rfl ha
  rw [← dropCyclic_fixMomenta, hd]
  exact sub_fixMomenta_mem c f

/-! ### The reduced ring -/

variable (ι) in
/-- The morphism from the phase space of the remaining co-ordinates to the
reduced ring `N(I)/I`. -/
def reductionHom (c : κ → ℝ) : SmoothRingHom (PhaseSpace ι)
    ((PhaseSpace.canonical (ι ⊕ κ)).Reduction (momentumIdeal ι c)) :=
  PoissonStructure.toReduction (inclusion ι κ) (inclusion_mem_normalizer c)

/-- Reduction with respect to cyclic co-ordinates at fixed values of their
momenta (Landau–Lifshitz §41): the reduced ring is the phase space of the
remaining co-ordinates. -/
theorem reductionHom_bijective (c : κ → ℝ) : Function.Bijective (reductionHom ι c) :=
  PoissonStructure.toReduction_bijective (inclusion_mem_normalizer c) (restriction_inclusion c)
    (fun _ hj => restriction_eq_zero_of_mem hj) fun _ hf => sub_inclusion_restriction_mem hf

/-- The identification of the reduced ring with the phase space of the
remaining co-ordinates preserves the bracket. -/
theorem isPoissonHom_reductionHom (c : κ → ℝ) :
    IsPoissonHom (PhaseSpace.canonical ι).toAlmostPoissonStructure
      ((PhaseSpace.canonical (ι ⊕ κ)).reduction (momentumIdeal ι c)).toAlmostPoissonStructure
      (reductionHom ι c) :=
  PoissonStructure.isPoissonHom_toReduction (inclusion_mem_normalizer c) isPoissonHom_inclusion

/-- The class of an element of the normalizer is its restriction to `q_k = 0`,
`p_k = c_k`. -/
theorem reductionHom_restriction {c : κ → ℝ} {f : PhaseSpace (ι ⊕ κ)}
    (hf : f ∈ (PhaseSpace.canonical (ι ⊕ κ)).normalizer (momentumIdeal ι c)) :
    reductionHom ι c (restriction ι c f) =
      (PhaseSpace.canonical (ι ⊕ κ)).reductionMap (momentumIdeal ι c) ⟨f, hf⟩ :=
  PoissonStructure.toReduction_apply_eq (inclusion_mem_normalizer c) (restriction ι c) hf
    (sub_inclusion_restriction_mem hf)

/-! ### Cyclic co-ordinates of a Hamiltonian -/

/-- A Hamiltonian that does not depend on the co-ordinates `q_k` is in the
normalizer, for all values of the momenta. -/
theorem mem_normalizer_of_cyclic {H : PhaseSpace (ι ⊕ κ)}
    (hH : ∀ k, partialDerivation (Sum.inl (Sum.inr k)) H = 0) (c : κ → ℝ) :
    H ∈ (PhaseSpace.canonical (ι ⊕ κ)).normalizer (momentumIdeal ι c) :=
  mem_normalizer_iff.mpr fun k => by
    rw [hH k]
    exact zero_mem _

/-- The momentum of a cyclic co-ordinate is an integral of the motion. -/
theorem isIntegral_p_of_cyclic {H : PhaseSpace (ι ⊕ κ)} {k : κ}
    (hH : partialDerivation (Sum.inl (Sum.inr k)) H = 0) :
    (PhaseSpace.canonical (ι ⊕ κ)).IsIntegral H (PhaseSpace.p (Sum.inr k)) := by
  unfold PoissonStructure.IsIntegral
  rw [PhaseSpace.canonical_p_bracket, hH, neg_zero]

/-- The momentum of a cyclic co-ordinate is constant along a trajectory. -/
theorem p_eq_algebraMap_of_cyclic {H : PhaseSpace (ι ⊕ κ)} {k : κ}
    (hH : partialDerivation (Sum.inl (Sum.inr k)) H = 0)
    {x : (ι ⊕ κ) ⊕ (ι ⊕ κ) → TimeFunction}
    (hx : IsTrajectory (PhaseSpace.canonical (ι ⊕ κ)) H x) :
    x (Sum.inr (Sum.inr k)) =
      algebraMap ℝ TimeFunction (x (Sum.inr (Sum.inr k)) fun _ => 0) := by
  refine SmoothOperation.ext fun t => ?_
  have h := hx.lift_eq_of_isIntegral (isIntegral_p_of_cyclic hH) t fun _ => 0
  rw [PhaseSpace.p, lift_generator] at h
  rw [h, TimeFunction.algebraMap_apply]

/-- The Routhian reduction in Hamiltonian form (Landau–Lifshitz §41): if the
co-ordinates `q_k` are cyclic and the momenta `p_k` have the values `c_k`, the
remaining co-ordinates of a trajectory form a trajectory of the Hamiltonian at
`p_k = c_k`. -/
theorem isTrajectory_restriction {H : PhaseSpace (ι ⊕ κ)}
    (hH : ∀ k, partialDerivation (Sum.inl (Sum.inr k)) H = 0)
    {x : (ι ⊕ κ) ⊕ (ι ⊕ κ) → TimeFunction}
    (hx : IsTrajectory (PhaseSpace.canonical (ι ⊕ κ)) H x) {c : κ → ℝ}
    (hc : ∀ k, x (Sum.inr (Sum.inr k)) = algebraMap ℝ TimeFunction (c k)) :
    IsTrajectory (PhaseSpace.canonical ι) (restriction ι c H)
      fun a => x (Sum.map Sum.inl Sum.inl a) := by
  have hlift (g : PhaseSpace ι) :
      FreeSmoothRing.lift (fun a => x (Sum.map Sum.inl Sum.inl a)) g =
        FreeSmoothRing.lift x (inclusion ι κ g) :=
    congrArg (fun χ : SmoothRingHom (PhaseSpace ι) TimeFunction => χ g)
      (FreeSmoothRing.hom_ext (f := FreeSmoothRing.lift fun a => x (Sum.map Sum.inl Sum.inl a))
        (g := (FreeSmoothRing.lift x).comp (inclusion ι κ)) fun a => by
          rw [lift_generator, SmoothRingHom.comp_apply, inclusion_generator, lift_generator])
  have hI : ∀ j ∈ momentumIdeal ι c, FreeSmoothRing.lift x j = 0 := fun j hj =>
    SmoothRingHom.eq_zero_of_mem_span (by
      rintro _ ⟨k, rfl⟩
      rw [momentumEquation, SmoothRingHom.map_sub, SmoothRingHom.map_algebraMap, PhaseSpace.p,
        lift_generator, hc, sub_self]) hj
  intro a
  have h0 := hI _ (inclusion_mem_normalizer c (generator a) _
    (sub_inclusion_restriction_mem (mem_normalizer_of_cyclic hH c)))
  rw [(PhaseSpace.canonical (ι ⊕ κ)).toAlmostPoissonStructure.bracket_sub_right,
    SmoothRingHom.map_sub, sub_eq_zero] at h0
  rw [hlift, isPoissonHom_inclusion (generator a) (restriction ι c H), ← h0,
    inclusion_generator]
  exact hx _

/-! ### Canonical co-ordinates

The same reduction for a Poisson C-infinity ring `P` with canonical
co-ordinates: an isomorphism `Φ` of Poisson C-infinity rings from the phase
space to `P`, with inverse `Ψ`. The ideal `I` is generated by the images of the
equations `p_k − c_k`. -/

section Canonical

variable {P : Type*} [CommRing P] [Algebra ℝ P] [SmoothRing P] {π : PoissonStructure P}
  {Φ : SmoothRingHom (PhaseSpace (ι ⊕ κ)) P} {Ψ : SmoothRingHom P (PhaseSpace (ι ⊕ κ))}
  {c : κ → ℝ} {I : Ideal P}

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem map_mem_of_mem_momentumIdeal
    (hI : I = Ideal.span (Set.range fun k => Φ (momentumEquation ι c k)))
    {j : PhaseSpace (ι ⊕ κ)} (hj : j ∈ momentumIdeal ι c) : Φ j ∈ I :=
  SmoothRingHom.mem_of_mem_span (by
    rintro _ ⟨k, rfl⟩
    rw [hI]
    exact Ideal.subset_span ⟨k, rfl⟩) hj

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem apply_mem_momentumIdeal
    (hI : I = Ideal.span (Set.range fun k => Φ (momentumEquation ι c k)))
    (hΨΦ : ∀ g, Ψ (Φ g) = g) {j : P} (hj : j ∈ I) : Ψ j ∈ momentumIdeal ι c := by
  rw [hI] at hj
  exact SmoothRingHom.mem_of_mem_span (by
    rintro _ ⟨k, rfl⟩
    rw [hΨΦ]
    exact Ideal.subset_span ⟨k, rfl⟩) hj

/-- The canonical co-ordinates map the normalizer into the normalizer. -/
theorem map_mem_normalizer
    (hΦ : IsPoissonHom (PhaseSpace.canonical (ι ⊕ κ)).toAlmostPoissonStructure
      π.toAlmostPoissonStructure Φ)
    (hI : I = Ideal.span (Set.range fun k => Φ (momentumEquation ι c k)))
    {g : PhaseSpace (ι ⊕ κ)}
    (hg : g ∈ (PhaseSpace.canonical (ι ⊕ κ)).normalizer (momentumIdeal ι c)) :
    Φ g ∈ π.normalizer I := by
  subst hI
  refine PoissonStructure.mem_normalizer_span ?_
  rintro _ ⟨k, rfl⟩
  rw [← hΦ]
  exact map_mem_of_mem_momentumIdeal rfl (hg _ (Ideal.subset_span ⟨k, rfl⟩))

/-- The inverse of the canonical co-ordinates maps the normalizer into the
normalizer. -/
theorem apply_mem_normalizer
    (hΦ : IsPoissonHom (PhaseSpace.canonical (ι ⊕ κ)).toAlmostPoissonStructure
      π.toAlmostPoissonStructure Φ)
    (hΦΨ : ∀ f, Φ (Ψ f) = f) (hΨΦ : ∀ g, Ψ (Φ g) = g)
    (hI : I = Ideal.span (Set.range fun k => Φ (momentumEquation ι c k)))
    {f : P} (hf : f ∈ π.normalizer I) :
    Ψ f ∈ (PhaseSpace.canonical (ι ⊕ κ)).normalizer (momentumIdeal ι c) := by
  refine PoissonStructure.mem_normalizer_span ?_
  rintro _ ⟨k, rfl⟩
  have h := apply_mem_momentumIdeal hI hΨΦ
    (hf _ (map_mem_of_mem_momentumIdeal hI (Ideal.subset_span ⟨k, rfl⟩)))
  have e : (PhaseSpace.canonical (ι ⊕ κ)).bracket (Ψ f) (momentumEquation ι c k) =
      Ψ (π.bracket f (Φ (momentumEquation ι c k))) := by
    rw [← hΨΦ ((PhaseSpace.canonical (ι ⊕ κ)).bracket (Ψ f) (momentumEquation ι c k)), hΦ, hΦΨ]
  rw [e]
  exact h

/-- The morphism from the phase space of the remaining co-ordinates to the
reduced ring, in canonical co-ordinates. -/
def canonicalReductionHom
    (hΦ : IsPoissonHom (PhaseSpace.canonical (ι ⊕ κ)).toAlmostPoissonStructure
      π.toAlmostPoissonStructure Φ)
    (hI : I = Ideal.span (Set.range fun k => Φ (momentumEquation ι c k))) :
    SmoothRingHom (PhaseSpace ι) (π.Reduction I) :=
  PoissonStructure.toReduction (Φ.comp (inclusion ι κ)) fun g =>
    map_mem_normalizer hΦ hI (inclusion_mem_normalizer c g)

/-- In canonical co-ordinates the reduced ring of the ideal `(p_k − c_k)` is
the phase space of the remaining co-ordinates. -/
theorem canonicalReductionHom_bijective
    (hΦ : IsPoissonHom (PhaseSpace.canonical (ι ⊕ κ)).toAlmostPoissonStructure
      π.toAlmostPoissonStructure Φ)
    (hΦΨ : ∀ f, Φ (Ψ f) = f) (hΨΦ : ∀ g, Ψ (Φ g) = g)
    (hI : I = Ideal.span (Set.range fun k => Φ (momentumEquation ι c k))) :
    Function.Bijective (canonicalReductionHom hΦ hI) :=
  PoissonStructure.toReduction_bijective (r := (restriction ι c).comp Ψ) _
    (fun g => by
      rw [SmoothRingHom.comp_apply, SmoothRingHom.comp_apply, hΨΦ, restriction_inclusion])
    (fun j hj => by
      rw [SmoothRingHom.comp_apply]
      exact restriction_eq_zero_of_mem (apply_mem_momentumIdeal hI hΨΦ hj))
    fun f hf => by
      have h := map_mem_of_mem_momentumIdeal hI
        (sub_inclusion_restriction_mem (apply_mem_normalizer hΦ hΦΨ hΨΦ hI hf))
      simpa only [SmoothRingHom.comp_apply, SmoothRingHom.map_sub, hΦΨ] using h

/-- The identification of the reduced ring preserves the bracket. -/
theorem isPoissonHom_canonicalReductionHom
    (hΦ : IsPoissonHom (PhaseSpace.canonical (ι ⊕ κ)).toAlmostPoissonStructure
      π.toAlmostPoissonStructure Φ)
    (hI : I = Ideal.span (Set.range fun k => Φ (momentumEquation ι c k))) :
    IsPoissonHom (PhaseSpace.canonical ι).toAlmostPoissonStructure
      (π.reduction I).toAlmostPoissonStructure (canonicalReductionHom hΦ hI) :=
  PoissonStructure.isPoissonHom_toReduction _ (hΦ.comp isPoissonHom_inclusion)

/-- The class of an element of the normalizer is its expression in the
canonical co-ordinates at `q_k = 0`, `p_k = c_k`. -/
theorem canonicalReductionHom_restriction
    (hΦ : IsPoissonHom (PhaseSpace.canonical (ι ⊕ κ)).toAlmostPoissonStructure
      π.toAlmostPoissonStructure Φ)
    (hΦΨ : ∀ f, Φ (Ψ f) = f) (hΨΦ : ∀ g, Ψ (Φ g) = g)
    (hI : I = Ideal.span (Set.range fun k => Φ (momentumEquation ι c k)))
    {f : P} (hf : f ∈ π.normalizer I) :
    canonicalReductionHom hΦ hI (restriction ι c (Ψ f)) = π.reductionMap I ⟨f, hf⟩ :=
  PoissonStructure.toReduction_apply_eq _ ((restriction ι c).comp Ψ) hf (by
    have h := map_mem_of_mem_momentumIdeal hI
      (sub_inclusion_restriction_mem (apply_mem_normalizer hΦ hΦΨ hΨΦ hI hf))
    simpa only [SmoothRingHom.comp_apply, SmoothRingHom.map_sub, hΦΨ] using h)

end Canonical

end ProjectAInos.Mechanics.CyclicReduction
