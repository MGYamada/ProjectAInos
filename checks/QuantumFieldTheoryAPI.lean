import ProjectAinos.QuantumFieldTheory.LocalityExamples

open ProjectAinos ProjectAinos.QuantumFieldTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (F : ScalarField H)

example [CompleteSpace H] (f : Test) : (F.operator f).IsClosable :=
  F.operator_closable f

example (Ω : F.domain) (a b : List Test) (f : Test) :
    F.insertionDistribution Ω a b f = F.expectation Ω (a ++ f :: b) :=
  F.insertionDistribution_apply Ω a b f

example {ι : Type*} (Ω : F.domain) (s : Finset ι) (c : ι → ℂ) (w : ι → List Test) :
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (c i) * c j *
      F.expectation Ω (ScalarField.adjointWord (w i) ++ w j)).re :=
  F.word_positivity Ω s c w

example (p : SpecialRelativity.Spacetime) : (pointEvaluation p).IsLocal :=
  pointEvaluation_local p

section Locality

open SpecialRelativity SmoothGeometry SmoothGeometry.Minkowski QuantumMechanics

/-! Causal predicates in time-first coordinates. -/

example (v : Spacetime) :
    intervalQuadratic v = v 0 ^ 2 - v 1 ^ 2 - v 2 ^ 2 - v 3 ^ 2 :=
  intervalQuadratic_spacetime v

example {d : ℕ} : ¬ Spacelike (0 : MinkowskiModel d) := not_spacelike_zero

example {d : ℕ} (v : MinkowskiModel d) : Spacelike (-v) ↔ Spacelike v := spacelike_neg_iff v

example {d : ℕ} : Continuous (fun v : MinkowskiModel d => intervalQuadratic v) :=
  continuous_intervalQuadratic

example {d : ℕ} : IsOpen {v : MinkowskiModel d | Spacelike v} := isOpen_spacelike

example (t : ℝ) : timePoint t = (Pi.single 0 t : Spacetime) := rfl

example (a : ℝ) : spacePoint a = (Pi.single 1 a : Spacetime) := rfl

example (t : ℝ) : intervalQuadratic (timePoint t) = t ^ 2 := intervalQuadratic_timePoint t

example (a : ℝ) : intervalQuadratic (spacePoint a) = -a ^ 2 := intervalQuadratic_spacePoint a

example {t : ℝ} (ht : t ≠ 0) : Timelike (timePoint t) := timelike_timePoint ht

example {a : ℝ} (ha : a ≠ 0) : Spacelike (spacePoint a) := spacelike_spacePoint ha

example (t : ℝ) : ¬ Spacelike (timePoint t) := not_spacelike_timePoint t

/-! Spacelike separation of tests. -/

example {f g : Test} (h : SpacelikeSeparated f g) : SpacelikeSeparated g f := h.symm

example (f g : Test) : SpacelikeSeparated f g ↔ SpacelikeSeparated g f :=
  spacelikeSeparated_comm f g

example (f : Test) : tsupport (conjugate f) = tsupport f := tsupport_conjugate f

example (f g : Test) : SpacelikeSeparated (conjugate f) g ↔ SpacelikeSeparated f g :=
  spacelikeSeparated_conjugate_left f g

example (f g : Test) : SpacelikeSeparated f (conjugate g) ↔ SpacelikeSeparated f g :=
  spacelikeSeparated_conjugate_right f g

example {f g : Test} {x : Spacetime} (hf : x ∈ tsupport f) (hg : x ∈ tsupport g) :
    ¬ SpacelikeSeparated f g :=
  not_spacelikeSeparated_of_mem hf hg

example {f : Test} (h : SpacelikeSeparated f f) : f = 0 := h.eq_zero

/-! Bump tests and their supports. -/

example (p : Spacetime) (r : ℝ) (hr : 0 < r) (x : Spacetime) :
    bump p r hr x =
      (((⟨r / 2, r, half_pos hr, half_lt_self hr⟩ : ContDiffBump p) x : ℝ) : ℂ) :=
  bump_apply p r hr x

example (p : Spacetime) (r : ℝ) (hr : 0 < r) : bump p r hr p = 1 := bump_self p r hr

example (p : Spacetime) (r : ℝ) (hr : 0 < r) :
    tsupport (bump p r hr) = Metric.closedBall p r :=
  tsupport_bump p r hr

example (p : Spacetime) (r : ℝ) (hr : 0 < r) : p ∈ tsupport (bump p r hr) :=
  self_mem_tsupport_bump p r hr

example {p x : Spacetime} {r : ℝ} (hr : 0 < r) (hx : x ∉ Metric.closedBall p r) :
    bump p r hr x = 0 :=
  bump_eq_zero hr hx

example (p q : Spacetime) (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    SpacelikeSeparated (bump p r hr) (bump q s hs) ↔
      ∀ x ∈ Metric.closedBall p r, ∀ y ∈ Metric.closedBall q s, Spacelike (x - y) :=
  spacelikeSeparated_bump_iff p q r s hr hs

example {p q : Spacetime} (h : ¬ Spacelike (p - q)) (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    ¬ SpacelikeSeparated (bump p r hr) (bump q s hs) :=
  not_spacelikeSeparated_bump h r s hr hs

example {p q : Spacetime} (h : Spacelike (p - q)) :
    ∃ (r : ℝ) (hr : 0 < r), SpacelikeSeparated (bump p r hr) (bump q r hr) :=
  exists_spacelikeSeparated_bump h

example {p x : Spacetime} {r : ℝ} (hr : 0 ≤ r) (hx : x ∈ Metric.closedBall p r) (i : Fin 4) :
    |x i - p i| ≤ r :=
  abs_sub_le_of_mem_closedBall hr hx i

/-- Sign-sensitive: a spatial displacement separates the supports. -/
example : SpacelikeSeparated (bump 0 1 one_pos) (bump (spacePoint 5) 1 one_pos) :=
  bump_spacePoint_spacelikeSeparated

/-- Sign-sensitive: a displacement in time gives timelike differences only. -/
example (x y : Spacetime) (hx : x ∈ tsupport (bump 0 1 one_pos))
    (hy : y ∈ tsupport (bump (timePoint 10) 1 one_pos)) : Timelike (x - y) :=
  bump_timePoint_timelike x y hx hy

example : ¬ SpacelikeSeparated (bump 0 1 one_pos) (bump (timePoint 10) 1 one_pos) :=
  bump_timePoint_not_spacelikeSeparated

/-! The two-point field. -/

variable (p q : Spacetime) (A B : H →ₗ[ℂ] H) (hA : A.IsSymmetric) (hB : B.IsSymmetric)

example (f : Test) (ψ : (⊤ : Submodule ℂ H)) :
    (twoPointSmear p q A B f ψ : H) = f p • A ψ + f q • B ψ :=
  twoPointSmear_coe p q A B f ψ

example : (twoPointField p q A B hA hB).domain = ⊤ := rfl

example (f : Test) (ψ : (twoPointField p q A B hA hB).domain) :
    ((twoPointField p q A B hA hB).smear f ψ : H) = f p • A ψ + f q • B ψ :=
  twoPointField_smear_coe p q A B hA hB f ψ

example (f g : Test) (ψ : (twoPointField p q A B hA hB).domain) :
    ((twoPointField p q A B hA hB).smear f ((twoPointField p q A B hA hB).smear g ψ) : H) -
        ((twoPointField p q A B hA hB).smear g ((twoPointField p q A B hA hB).smear f ψ) : H) =
      (f p * g q - f q * g p) • (A (B ψ) - B (A ψ)) :=
  twoPointField_commutator p q A B hA hB f g ψ

example (h : ¬ Spacelike (p - q)) : (twoPointField p q A B hA hB).IsLocal :=
  twoPointField_isLocal hA hB h

example {r : ℝ} (hr : 0 < r) (hq : q ∉ Metric.closedBall p r) (g : Test) (hg : g q = 1)
    (ψ : (twoPointField p q A B hA hB).domain) :
    ((twoPointField p q A B hA hB).smear (bump p r hr)
          ((twoPointField p q A B hA hB).smear g ψ) : H) -
        ((twoPointField p q A B hA hB).smear g
          ((twoPointField p q A B hA hB).smear (bump p r hr) ψ) : H) =
      A (B ψ) - B (A ψ) :=
  twoPointField_commutator_bump hA hB hr hq g hg ψ

example (hAB : A ∘ₗ B ≠ B ∘ₗ A) (h : Spacelike (p - q)) :
    ¬ (twoPointField p q A B hA hB).IsLocal :=
  twoPointField_not_isLocal hA hB hAB h

/-- Sign-sensitive: reversing the causal condition falsifies this equivalence. -/
example (hAB : A ∘ₗ B ≠ B ∘ₗ A) :
    (twoPointField p q A B hA hB).IsLocal ↔ ¬ Spacelike (p - q) :=
  twoPointField_isLocal_iff hA hB hAB

/-! The Pauli instance. -/

example (axis : Fin 3) :
    pauliOperator axis = Matrix.toEuclideanLin (Qubit.pauli axis) := rfl

example (axis : Fin 3) : (pauliOperator axis).IsSymmetric := pauliOperator_isSymmetric axis

example :
    pauliOperator 0 (pauliOperator 2 (EuclideanSpace.single 0 1)) -
        pauliOperator 2 (pauliOperator 0 (EuclideanSpace.single 0 1)) =
      EuclideanSpace.single 1 2 :=
  pauliOperator_commutator

example : pauliOperator 0 ∘ₗ pauliOperator 2 ≠ pauliOperator 2 ∘ₗ pauliOperator 0 :=
  pauliOperator_not_commute

example (p q : Spacetime) :
    pauliField p q = twoPointField p q (pauliOperator 0) (pauliOperator 2)
      (pauliOperator_isSymmetric 0) (pauliOperator_isSymmetric 2) := rfl

example (p q : Spacetime) : (pauliField p q).IsLocal ↔ ¬ Spacelike (p - q) :=
  pauliField_isLocal_iff p q

example : (pauliField 0 (timePoint 10)).IsLocal := pauliField_timePoint_isLocal

example : ¬ (pauliField 0 (spacePoint 5)).IsLocal := pauliField_spacePoint_not_isLocal

example (p q : Spacetime) :
    ((pauliUp p q : (pauliField p q).domain) : Qubit.Hilbert) = EuclideanSpace.single 0 1 := rfl

example : timePoint 10 ∉ Metric.closedBall (0 : Spacetime) 1 := timePoint_notMem_closedBall

example : spacePoint 5 ∉ Metric.closedBall (0 : Spacetime) 1 := spacePoint_notMem_closedBall

example : (EuclideanSpace.single 1 2 : Qubit.Hilbert) ≠ 0 := single_one_two_ne_zero

/-- A local field with a nonzero commutator on timelike separated tests. -/
example :
    ((pauliField 0 (timePoint 10)).smear (bump 0 1 one_pos)
          ((pauliField 0 (timePoint 10)).smear (bump (timePoint 10) 1 one_pos)
            (pauliUp 0 (timePoint 10))) : Qubit.Hilbert) -
        ((pauliField 0 (timePoint 10)).smear (bump (timePoint 10) 1 one_pos)
          ((pauliField 0 (timePoint 10)).smear (bump 0 1 one_pos)
            (pauliUp 0 (timePoint 10))) : Qubit.Hilbert) =
      EuclideanSpace.single 1 2 :=
  pauliField_timePoint_commutator

example :
    (pauliField 0 (timePoint 10)).smear (bump 0 1 one_pos)
        ((pauliField 0 (timePoint 10)).smear (bump (timePoint 10) 1 one_pos)
          (pauliUp 0 (timePoint 10))) ≠
      (pauliField 0 (timePoint 10)).smear (bump (timePoint 10) 1 one_pos)
        ((pauliField 0 (timePoint 10)).smear (bump 0 1 one_pos)
          (pauliUp 0 (timePoint 10))) :=
  pauliField_timePoint_ne

/-- A nonzero commutator on spacelike separated tests: locality fails. -/
example :
    ((pauliField 0 (spacePoint 5)).smear (bump 0 1 one_pos)
          ((pauliField 0 (spacePoint 5)).smear (bump (spacePoint 5) 1 one_pos)
            (pauliUp 0 (spacePoint 5))) : Qubit.Hilbert) -
        ((pauliField 0 (spacePoint 5)).smear (bump (spacePoint 5) 1 one_pos)
          ((pauliField 0 (spacePoint 5)).smear (bump 0 1 one_pos)
            (pauliUp 0 (spacePoint 5))) : Qubit.Hilbert) =
      EuclideanSpace.single 1 2 :=
  pauliField_spacePoint_commutator

example :
    (pauliField 0 (spacePoint 5)).smear (bump 0 1 one_pos)
        ((pauliField 0 (spacePoint 5)).smear (bump (spacePoint 5) 1 one_pos)
          (pauliUp 0 (spacePoint 5))) ≠
      (pauliField 0 (spacePoint 5)).smear (bump (spacePoint 5) 1 one_pos)
        ((pauliField 0 (spacePoint 5)).smear (bump 0 1 one_pos)
          (pauliUp 0 (spacePoint 5))) :=
  pauliField_spacePoint_ne

end Locality
