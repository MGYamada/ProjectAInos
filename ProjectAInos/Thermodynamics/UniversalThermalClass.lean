module

public import ProjectAInos.Thermodynamics.ThermalClasses
public import ProjectAInos.Thermodynamics.ThermalJoinCoherence

/-!
# Thermal classes meeting every work fiber

Transversality and the ordering of supporting entropy slopes prevent a thermal
class that meets every work fiber from lying on a single adiabat. This applies
to the component classes of a thermal join whose entire domain is one isotherm.
-/

@[expose] public section

open Set
open scoped NNReal

namespace ProjectAInos.Thermodynamics.Physical.ThermalFamily

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X} (F : ThermalFamily P) {n : ℕ}

/-- A thermal class intersecting every nonempty work fiber contains two
adiabatically inequivalent states. Both energy orientations are permitted. -/
theorem exists_thermal_not_equivalent_of_meets_work_fibers
    (S : SimpleSystem P n) (hS : F.admitted S) (a : S.domain)
    (hfiber : ∀ x : S.domain, ∃ p : S.domain,
      p.val.2 = x.val.2 ∧ F.thermal (S.represent a) (S.represent p)) :
    ∃ p : S.domain, F.thermal (S.represent a) (S.represent p) ∧
      ¬ (P.relation (S.represent a) (S.represent p) ∧
        P.relation (S.represent p) (S.represent a)) := by
  classical
  by_contra! hconstant
  obtain ⟨b, c, hbc, hba, hac⟩ := F.transversality S hS a
  obtain ⟨p, hpwork, hap⟩ := hfiber b
  obtain ⟨q, hqwork, haq⟩ := hfiber c
  have hep := hconstant p hap
  have heq := hconstant q haq
  have hbp : P.relation (S.represent b) (S.represent p) ∧
      ¬ P.relation (S.represent p) (S.represent b) :=
    ⟨P.trans hba.1 hep.1, fun h => hba.2 (P.trans hep.1 h)⟩
  have hqc : P.relation (S.represent q) (S.represent c) ∧
      ¬ P.relation (S.represent c) (S.represent q) :=
    ⟨P.trans heq.2 hac.1, fun h => hac.2 (P.trans h heq.2)⟩
  have hpq : F.thermal (S.represent p) (S.represent q) :=
    F.trans (F.isState_represent S hS p) (F.isState_represent S hS a)
      (F.isState_represent S hS q)
      (F.symm (F.isState_represent S hS a) (F.isState_represent S hS p) hap) haq
  let hlocal := F.localMixtureIntervals_of_axioms S hS
  let s := S.referenceEntropy hlocal b a hba
  obtain ⟨α, hαp, hαq⟩ :=
    (F.thermal_iff_entropySlopes_inter S hS hlocal b a hba p q).mp hpq
  obtain ⟨β, hβb, hβc⟩ :=
    (F.thermal_iff_entropySlopes_inter S hS hlocal b a hba b c).mp hbc
  have hαβ : α = β := by
    rcases S.positive_or_negative a.property with hpos | hneg
    · have hpositive := S.positive_everywhere a.property hpos
      have hbpU : b.val.1 < p.val.1 := by
        apply lt_of_not_ge
        intro h
        apply hbp.2
        exact (S.accessible_iff_signed_energy_le one_ne_zero hpositive
          p.property b.property hpwork).mpr (by simpa using h)
      have hqcU : q.val.1 < c.val.1 := by
        apply lt_of_not_ge
        intro h
        apply hqc.2
        exact (S.accessible_iff_signed_energy_le one_ne_zero hpositive
          c.property q.property hqwork.symm).mpr (by simpa using h)
      exact le_antisymm (S.entropySlopes_antitone s hpwork.symm hbpU hβb hαp)
        (S.entropySlopes_antitone s hqwork hqcU hαq hβc)
    · have hnegative := S.negative_everywhere a.property hneg
      have hpbU : p.val.1 < b.val.1 := by
        apply lt_of_not_ge
        intro h
        apply hbp.2
        exact (S.accessible_iff_signed_energy_le (by norm_num : (-1 : ℝ) ≠ 0) hnegative
          p.property b.property hpwork).mpr (by simpa only [neg_one_mul] using neg_le_neg h)
      have hcqU : c.val.1 < q.val.1 := by
        apply lt_of_not_ge
        intro h
        apply hqc.2
        exact (S.accessible_iff_signed_energy_le (by norm_num : (-1 : ℝ) ≠ 0) hnegative
          c.property q.property hqwork.symm).mpr
            (by simpa only [neg_one_mul] using neg_le_neg h)
      exact le_antisymm (S.entropySlopes_antitone s hqwork.symm hcqU hβc hαq)
        (S.entropySlopes_antitone s hpwork hpbU hαp hβb)
  have hbpthermal : F.thermal (S.represent b) (S.represent p) := by
    apply (F.thermal_iff_entropySlopes_inter S hS hlocal b a hba b p).mpr
    exact ⟨β, hβb, hαβ ▸ hαp⟩
  have habthermal : F.thermal (S.represent a) (S.represent b) :=
    F.trans (F.isState_represent S hS a) (F.isState_represent S hS p)
      (F.isState_represent S hS b) hap
      (F.symm (F.isState_represent S hS b) (F.isState_represent S hS p) hbpthermal)
  exact hba.2 (hconstant b habthermal).1

/-- The nonconstant thermal class supplies an oriented strict reference pair. -/
theorem exists_strict_pair_in_thermal_class_of_meets_work_fibers
    (S : SimpleSystem P n) (hS : F.admitted S) (a : S.domain)
    (hfiber : ∀ x : S.domain, ∃ p : S.domain,
      p.val.2 = x.val.2 ∧ F.thermal (S.represent a) (S.represent p)) :
    ∃ p q : S.domain,
      (P.relation (S.represent p) (S.represent q) ∧
        ¬ P.relation (S.represent q) (S.represent p)) ∧
      F.thermal (S.represent a) (S.represent p) ∧
      F.thermal (S.represent a) (S.represent q) := by
  obtain ⟨b, hab, hne⟩ :=
    F.exists_thermal_not_equivalent_of_meets_work_fibers S hS a hfiber
  rcases S.comparison a b with h | h
  · exact ⟨a, b, ⟨h, fun h' => hne ⟨h, h'⟩⟩,
      F.refl (F.isState_represent S hS a), hab⟩
  · exact ⟨b, a, ⟨h, fun h' => hne ⟨h', h⟩⟩,
      hab, F.refl (F.isState_represent S hS a)⟩

/-- When the join is one thermal class, either component class meets all its
work fibers. The witnesses come from coordinate-preserving thermal splitting. -/
theorem exists_component_classes_meeting_work_fibers_of_universal_join
    {m : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m)
    (hS : F.admitted S) (hT : F.admitted T) (x : S.domain) (y : T.domain)
    (huniversal : ∀ z w : (F.join S T hS hT).system.domain,
      F.thermal ((F.join S T hS hT).system.represent z)
        ((F.join S T hS hT).system.represent w)) :
    ∃ a : S.domain, ∃ b : T.domain,
      F.thermal (S.represent a) (T.represent b) ∧
      (∀ u : S.domain, ∃ p : S.domain,
        p.val.2 = u.val.2 ∧ F.thermal (S.represent a) (S.represent p)) ∧
      (∀ v : T.domain, ∃ q : T.domain,
        q.val.2 = v.val.2 ∧ F.thermal (T.represent b) (T.represent q)) := by
  let J := F.join S T hS hT
  have hJ := F.join_admitted S T hS hT
  let z := J.point (joinedState x y)
  obtain ⟨a, b, _, _, hza, hzb⟩ := F.exists_coherent_split S T hS hT z
  have haz := F.symm (F.isState_represent J.system hJ z)
    (F.isState_represent S hS a) hza
  have hbz := F.symm (F.isState_represent J.system hJ z)
    (F.isState_represent T hT b) hzb
  refine ⟨a, b, F.trans (F.isState_represent S hS a)
    (F.isState_represent J.system hJ z) (F.isState_represent T hT b) haz hzb, ?_, ?_⟩
  · intro u
    let w := J.point (joinedState u y)
    obtain ⟨p, q, hpq, _, hwp, _⟩ := F.exists_coherent_split S T hS hT w
    have hpwork : p.val.2 = u.val.2 := by
      have hwork := congrArg (fun k : J.system.domain => k.val.2) hpq
      change Fin.append p.val.2 q.val.2 = Fin.append u.val.2 y.val.2 at hwork
      funext i
      simpa only [Fin.append_left] using congrFun hwork (Fin.castAdd m i)
    refine ⟨p, hpwork, ?_⟩
    exact F.trans (F.isState_represent S hS a) (F.isState_represent J.system hJ z)
      (F.isState_represent S hS p) haz
      (F.trans (F.isState_represent J.system hJ z) (F.isState_represent J.system hJ w)
        (F.isState_represent S hS p) (huniversal z w) hwp)
  · intro v
    let w := J.point (joinedState x v)
    obtain ⟨p, q, hpq, _, _, hwq⟩ := F.exists_coherent_split S T hS hT w
    have hqwork : q.val.2 = v.val.2 := by
      have hwork := congrArg (fun k : J.system.domain => k.val.2) hpq
      change Fin.append p.val.2 q.val.2 = Fin.append x.val.2 v.val.2 at hwork
      funext i
      simpa only [Fin.append_right] using congrFun hwork (Fin.natAdd n i)
    refine ⟨q, hqwork, ?_⟩
    exact F.trans (F.isState_represent T hT b) (F.isState_represent J.system hJ z)
      (F.isState_represent T hT q) hbz
      (F.trans (F.isState_represent J.system hJ z) (F.isState_represent J.system hJ w)
        (F.isState_represent T hT q) (huniversal z w) hwq)

/-- A universal joined isotherm supplies strict component reference pairs
whose four cross combinations are all in thermal equilibrium. -/
theorem exists_cross_thermal_strict_pairs_of_universal_join
    {m : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m)
    (hS : F.admitted S) (hT : F.admitted T) (x : S.domain) (y : T.domain)
    (huniversal : ∀ z w : (F.join S T hS hT).system.domain,
      F.thermal ((F.join S T hS hT).system.represent z)
        ((F.join S T hS hT).system.represent w)) :
    ∃ a₀ a₁ : S.domain, ∃ b₀ b₁ : T.domain,
      (P.relation (S.represent a₀) (S.represent a₁) ∧
        ¬ P.relation (S.represent a₁) (S.represent a₀)) ∧
      (P.relation (T.represent b₀) (T.represent b₁) ∧
        ¬ P.relation (T.represent b₁) (T.represent b₀)) ∧
      F.thermal (S.represent a₀) (T.represent b₀) ∧
      F.thermal (S.represent a₁) (T.represent b₀) ∧
      F.thermal (S.represent a₀) (T.represent b₁) ∧
      F.thermal (S.represent a₁) (T.represent b₁) := by
  obtain ⟨a, b, hab, hleft, hright⟩ :=
    F.exists_component_classes_meeting_work_fibers_of_universal_join S T hS hT x y huniversal
  obtain ⟨a₀, a₁, ha, haa₀, haa₁⟩ :=
    F.exists_strict_pair_in_thermal_class_of_meets_work_fibers S hS a hleft
  obtain ⟨b₀, b₁, hb, hbb₀, hbb₁⟩ :=
    F.exists_strict_pair_in_thermal_class_of_meets_work_fibers T hT b hright
  have hcross (p : S.domain) (q : T.domain)
      (hap : F.thermal (S.represent a) (S.represent p))
      (hbq : F.thermal (T.represent b) (T.represent q)) :
      F.thermal (S.represent p) (T.represent q) := by
    exact F.trans (F.isState_represent S hS p) (F.isState_represent S hS a)
      (F.isState_represent T hT q)
      (F.symm (F.isState_represent S hS a) (F.isState_represent S hS p) hap)
      (F.trans (F.isState_represent S hS a) (F.isState_represent T hT b)
        (F.isState_represent T hT q) hab hbq)
  exact ⟨a₀, a₁, b₀, b₁, ha, hb, hcross a₀ b₀ haa₀ hbb₀,
    hcross a₁ b₀ haa₁ hbb₀, hcross a₀ b₁ haa₀ hbb₁, hcross a₁ b₁ haa₁ hbb₁⟩

end ProjectAInos.Thermodynamics.Physical.ThermalFamily
