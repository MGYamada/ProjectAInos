/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
-/
module

public import ProjectAInos.SpecialRelativity.Spacetime
public import Mathlib.Analysis.Distribution.Support
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Scalar smeared fields on a common invariant domain

The tests are complex Schwartz functions on time-first Minkowski spacetime.
An operator is an algebraic endomorphism of a dense domain, with continuous
dependence on the test in each Hilbert-space orbit. Hermiticity on this domain
implies closability as an operator in the Hilbert space. The vacuum word
positivity result concerns finite combinations of smeared insertions.
-/

@[expose] public section
noncomputable section

open scoped SchwartzMap

namespace ProjectAInos.QuantumFieldTheory

open SpecialRelativity SmoothGeometry.Minkowski

abbrev Test := SchwartzMap Spacetime ℂ
abbrev Distribution := TemperedDistribution Spacetime ℂ

/-- Complex conjugation acts real-linearly on the test space. -/
def conjugate : Test →L[ℝ] Test :=
  SchwartzMap.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)

@[simp] theorem conjugate_apply (f : Test) (x : Spacetime) :
    conjugate f x = star (f x) := rfl

@[simp] theorem conjugate_conjugate (f : Test) : conjugate (conjugate f) = f := by
  ext x
  simp

@[simp] theorem conjugate_smul (c : ℂ) (f : Test) :
    conjugate (c • f) = star c • conjugate f := by
  ext x
  simp

/-- Every point in either test's closed support is spacelike to every point in
the other support, using the existing time-first causal convention. -/
def SpacelikeSeparated (f g : Test) : Prop :=
  ∀ x ∈ tsupport f, ∀ y ∈ tsupport g, Spacelike (x - y)

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A Hermitian scalar smeared field. Only orbit maps from the Schwartz space
are continuous by assumption. The state argument lives on the common domain. -/
structure ScalarField where
  domain : Submodule ℂ H
  dense : Dense (domain : Set H)
  smear : Test →ₗ[ℂ] (domain →ₗ[ℂ] domain)
  continuous_orbit : ∀ ψ : domain, Continuous (fun f => (smear f ψ : H))
  hermitian : ∀ (f : Test) (ψ χ : domain),
    inner ℂ (smear f ψ : H) (χ : H) =
      inner ℂ (ψ : H) (smear (conjugate f) χ : H)

namespace ScalarField

variable {H} (F : ScalarField H)

def operator (f : Test) : H →ₗ.[ℂ] H :=
  ⟨F.domain, F.domain.subtype.comp (F.smear f)⟩

@[simp] theorem operator_domain (f : Test) : (F.operator f).domain = F.domain := rfl

theorem formalAdjoint (f : Test) :
    (F.operator f).IsFormalAdjoint (F.operator (conjugate f)) :=
  F.hermitian f

theorem operator_closable [CompleteSpace H] (f : Test) : (F.operator f).IsClosable := by
  have h : F.operator f ≤ (F.operator (conjugate f)).adjoint :=
    (F.formalAdjoint f).symm.le_adjoint F.dense
  exact ((F.operator (conjugate f)).adjoint_isClosed F.dense).isClosable.leIsClosable h

/-- Every fixed matrix element is a continuous complex-linear distribution in
the test argument, with the Hilbert pairing conjugate-linear in its first slot. -/
def matrixElement (ψ χ : F.domain) : Distribution :=
  ContinuousLinearMap.toPointwiseConvergenceCLM _ _ _ _
    { toFun f := inner ℂ (ψ : H) (F.smear f χ : H)
      map_add' f g := by simp [inner_add_right]
      map_smul' c f := by simp [inner_smul_right]
      cont := continuous_const.inner (F.continuous_orbit χ) }

@[simp] theorem matrixElement_apply (ψ χ : F.domain) (f : Test) :
    F.matrixElement ψ χ f = inner ℂ (ψ : H) (F.smear f χ : H) := rfl

/-- Locality for a Hermitian scalar field, as equality on the common domain. -/
def IsLocal : Prop :=
  ∀ f g : Test, SpacelikeSeparated f g → ∀ ψ : F.domain,
    F.smear f (F.smear g ψ) = F.smear g (F.smear f ψ)

/-- A finite ordered product, with the head insertion acting last on the vector. -/
def word (F : ScalarField H) : List Test → F.domain →ₗ[ℂ] F.domain
  | [] => LinearMap.id
  | f :: w => (F.smear f).comp (word F w)

@[simp] theorem word_nil (ψ : F.domain) : F.word [] ψ = ψ := rfl

@[simp] theorem word_cons (f : Test) (w : List Test) (ψ : F.domain) :
    F.word (f :: w) ψ = F.smear f (F.word w ψ) := rfl

theorem word_append (a b : List Test) (ψ : F.domain) :
    F.word (a ++ b) ψ = F.word a (F.word b ψ) := by
  induction a with
  | nil => rfl
  | cons f a ih => simp [ih]

/-- Reversing the order and conjugating the tests gives the formal adjoint
of the corresponding word on the invariant domain. -/
def adjointWord (w : List Test) : List Test := w.reverse.map conjugate

theorem word_adjoint (w : List Test) (ψ χ : F.domain) :
    inner ℂ (F.word w ψ : H) (χ : H) =
      inner ℂ (ψ : H) (F.word (adjointWord w) χ : H) := by
  induction w generalizing χ with
  | nil => rfl
  | cons f w ih =>
    rw [word_cons, F.hermitian, ih]
    simp [adjointWord, F.word_append]

/-- Vacuum expectations of test words. The vacuum normalization and cyclicity
are independent properties of a future Wightman representation. -/
def expectation (Ω : F.domain) (w : List Test) : ℂ :=
  inner ℂ (Ω : H) (F.word w Ω : H)

theorem word_gram (Ω : F.domain) (a b : List Test) :
    inner ℂ (F.word a Ω : H) (F.word b Ω : H) =
      F.expectation Ω (adjointWord a ++ b) := by
  rw [F.word_adjoint, expectation, F.word_append]

/-- Holding the other insertions fixed gives a distribution in the remaining
test. Moving the prefix to the bra uses only the common-domain adjoint law. -/
def insertionDistribution (Ω : F.domain) (a b : List Test) : Distribution :=
  F.matrixElement (F.word (adjointWord a) Ω) (F.word b Ω)

@[simp] theorem insertionDistribution_apply (Ω : F.domain) (a b : List Test) (f : Test) :
    F.insertionDistribution Ω a b f = F.expectation Ω (a ++ f :: b) := by
  rw [insertionDistribution, matrixElement_apply, expectation, F.word_append, word_cons]
  exact (inner_conj_symm (𝕜 := ℂ) _ _).symm.trans
    ((congrArg star (F.word_adjoint a (F.smear f (F.word b Ω)) Ω)).symm.trans
      (inner_conj_symm (𝕜 := ℂ) _ _))

/-- Wightman positivity on finite linear combinations of vacuum words. -/
theorem word_positivity {ι : Type*} (Ω : F.domain) (s : Finset ι)
    (c : ι → ℂ) (w : ι → List Test) :
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (c i) * c j *
      F.expectation Ω (adjointWord (w i) ++ w j)).re := by
  let v : H := ∑ i ∈ s, c i • (F.word (w i) Ω : H)
  have h : inner ℂ v v =
      ∑ i ∈ s, ∑ j ∈ s, star (c i) * c j *
        F.expectation Ω (adjointWord (w i) ++ w j) := by
    simp only [v, sum_inner, inner_sum, inner_smul_left, inner_smul_right, F.word_gram,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change c j * (star (c i) * _) = star (c i) * c j * _
    ring
  rw [← h]
  exact inner_self_nonneg (𝕜 := ℂ)

end ScalarField

/-- Evaluation at a point times the identity gives a simple domain and
conjugation regression on the one-dimensional Hilbert space. -/
def pointEvaluation (p : Spacetime) : ScalarField ℂ where
  domain := ⊤
  dense := by rw [Submodule.top_coe]; exact dense_univ
  smear := (LinearMap.lsmul ℂ _).comp (TemperedDistribution.delta p).toLinearMap
  continuous_orbit ψ := by
    change Continuous (fun f : Test => TemperedDistribution.delta p f • (ψ : ℂ))
    exact (TemperedDistribution.delta p).continuous.smul continuous_const
  hermitian f ψ χ := by
    change inner ℂ ((TemperedDistribution.delta p f) • (ψ : ℂ)) (χ : ℂ) =
      inner ℂ (ψ : ℂ) ((TemperedDistribution.delta p (conjugate f)) • (χ : ℂ))
    simp
    ring

theorem pointEvaluation_local (p : Spacetime) : (pointEvaluation p).IsLocal := by
  intro f g _ ψ
  apply Subtype.ext
  change TemperedDistribution.delta p f • (TemperedDistribution.delta p g • (ψ : ℂ)) =
    TemperedDistribution.delta p g • (TemperedDistribution.delta p f • (ψ : ℂ))
  rw [smul_smul, smul_smul, mul_comm]

end ProjectAInos.QuantumFieldTheory
