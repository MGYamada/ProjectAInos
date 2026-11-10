module

public import ProjectAInos.Thermodynamics.Cancellation
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
public import Mathlib.Algebra.Module.End
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The real vector space of formal thermodynamic differences

The nonnegative scalar action extends through the universal property of the
Grothendieck group, and differences of nonnegative scalars give the real action.
-/

@[expose] public section

open scoped NNReal

namespace ProjectAInos.Thermodynamics

/-- Formal differences of thermodynamic states. -/
abbrev Completion (M : Type*) [AddCommMonoid M] := Algebra.GrothendieckAddGroup M

namespace Completion

variable {M : Type*} [AddCommMonoid M]

/-- The canonical additive inclusion into the group completion. -/
abbrev of : M →+ Completion M := Algebra.GrothendieckAddGroup.of

/-- Additive maps out of the completion are determined on states. -/
theorem hom_ext {G : Type*} [AddCommGroup G] {f g : Completion M →+ G}
    (h : ∀ x, f (of x) = g (of x)) : f = g := by
  apply (Algebra.GrothendieckAddGroup.lift (M := M) (G := G)).symm.injective
  exact AddMonoidHom.ext h

/-- Every formal process is a difference of two states. -/
theorem exists_sub_of (v : Completion M) : ∃ y x : M, v = of y - of x := by
  induction v using AddLocalization.induction_on with
  | H p =>
    refine ⟨p.1, p.2.1, ?_⟩
    simp [of, Algebra.GrothendieckAddGroup.of,
      ← AddLocalization.mk_zero_eq_addMonoidOf_mk, Algebra.GrothendieckAddGroup.mk_sub_mk]

variable [Module ℝ≥0 M]

/-- Nonnegative scaling lifted to additive endomorphisms of the completion. -/
noncomputable def nnrealEnd (a : ℝ≥0) : AddMonoid.End (Completion M) :=
  Algebra.GrothendieckAddGroup.lift
    (of.comp (DistribSMul.toAddMonoidHom M a))

@[simp] theorem nnrealEnd_of (a : ℝ≥0) (x : M) :
    nnrealEnd a (of x) = of (a • x) := by
  change ((Algebra.GrothendieckAddGroup.lift
    (of.comp (DistribSMul.toAddMonoidHom M a))).comp of) x = _
  exact congrArg (fun f : M →+ Completion M => f x)
    ((Algebra.GrothendieckAddGroup.lift (M := M) (G := Completion M)).symm_apply_apply _)

/-- The lifted nonnegative action preserves the semiring operations. -/
noncomputable def nnrealEndHom : ℝ≥0 →+* AddMonoid.End (Completion M) where
  toFun := nnrealEnd
  map_zero' := hom_ext fun x => by
    change nnrealEnd 0 (of x) = 0
    rw [nnrealEnd_of, zero_smul, map_zero]
  map_one' := hom_ext fun x => by
    change nnrealEnd 1 (of x) = of x
    rw [nnrealEnd_of, one_smul]
  map_add' a b := hom_ext fun x => by
    change nnrealEnd (a + b) (of x) = nnrealEnd a (of x) + nnrealEnd b (of x)
    simp only [nnrealEnd_of, add_smul, map_add]
  map_mul' a b := hom_ext fun x => by
    change nnrealEnd (a * b) (of x) = nnrealEnd a (nnrealEnd b (of x))
    simp only [nnrealEnd_of, mul_smul]

private theorem positive_difference (r : ℝ) :
    (r.toNNReal : ℝ) - ((-r).toNNReal : ℝ) = r := by
  by_cases hr : 0 ≤ r
  · simp [Real.coe_toNNReal r hr, Real.toNNReal_of_nonpos (neg_nonpos.mpr hr)]
  · have hr' : r ≤ 0 := le_of_not_ge hr
    simp [Real.toNNReal_of_nonpos hr', Real.coe_toNNReal (-r) (neg_nonneg.mpr hr')]

/-- Extension of a nonnegative scalar map by positive and negative parts. -/
def extendScalars {R : Type*} [Ring R] (f : ℝ≥0 →+* R) (r : ℝ) : R :=
  f r.toNNReal - f (-r).toNNReal

private theorem extendScalars_sub {R : Type*} [Ring R] (f : ℝ≥0 →+* R)
    (a b : ℝ≥0) : extendScalars f ((a : ℝ) - b) = f a - f b := by
  have h : ((a : ℝ) - b).toNNReal + b = (-((a : ℝ) - b)).toNNReal + a := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add]
    linarith [positive_difference ((a : ℝ) - b)]
  have hf := congrArg f h
  simp only [map_add] at hf
  exact (sub_eq_sub_iff_add_eq_add).mpr (by simpa only [add_comm] using hf)

/-- The extension by differences is a ring homomorphism. -/
noncomputable def extendScalarsHom {R : Type*} [Ring R] (f : ℝ≥0 →+* R) :
    ℝ →+* R where
  toFun := extendScalars f
  map_zero' := by simp [extendScalars]
  map_one' := by
    simp [extendScalars, Real.toNNReal_of_nonpos (by norm_num : (-1 : ℝ) ≤ 0)]
  map_add' r s := by
    have hr := positive_difference r
    have hs := positive_difference s
    have hrs : r + s = ((r.toNNReal + s.toNNReal : ℝ≥0) : ℝ) -
        (((-r).toNNReal + (-s).toNNReal : ℝ≥0) : ℝ) := by
      simp only [NNReal.coe_add]
      linarith
    rw [hrs, extendScalars_sub]
    simp only [map_add, extendScalars]
    abel
  map_mul' r s := by
    have hrs : r * s = ((r.toNNReal * s.toNNReal + (-r).toNNReal * (-s).toNNReal : ℝ≥0) : ℝ) -
        ((r.toNNReal * (-s).toNNReal + (-r).toNNReal * s.toNNReal : ℝ≥0) : ℝ) := by
      simp only [NNReal.coe_add, NNReal.coe_mul]
      calc
        r * s = ((r.toNNReal : ℝ) - ((-r).toNNReal : ℝ)) *
            ((s.toNNReal : ℝ) - ((-s).toNNReal : ℝ)) := by
          rw [positive_difference, positive_difference]
        _ = _ := by ring
    rw [hrs, extendScalars_sub]
    simp only [map_add, map_mul, extendScalars]
    simp only [sub_mul, mul_sub]
    abel

/-- The real scalar action as a homomorphism into additive endomorphisms. -/
noncomputable def realEndHom : ℝ →+* AddMonoid.End (Completion M) :=
  extendScalarsHom nnrealEndHom

/-- Canonical real scalar multiplication on formal differences. -/
noncomputable instance : Module ℝ (Completion M) where
  smul r v := realEndHom r v
  one_smul v := by change realEndHom 1 v = v; simp
  mul_smul r s v := by
    change realEndHom (r * s) v = realEndHom r (realEndHom s v)
    rw [map_mul]
    rfl
  smul_zero r := (realEndHom r).map_zero
  smul_add r v w := (realEndHom r).map_add v w
  add_smul r s v := by change realEndHom (r + s) v = _; rw [map_add]; rfl
  zero_smul v := by change realEndHom 0 v = 0; simp

@[simp] theorem coe_smul_eq_nnrealEnd (a : ℝ≥0) (v : Completion M) :
    (a : ℝ) • v = nnrealEnd a v := by
  change extendScalars nnrealEndHom (a : ℝ) v = _
  simp only [extendScalars, Real.toNNReal_coe,
    Real.toNNReal_of_nonpos (neg_nonpos.mpr a.coe_nonneg), map_zero, sub_zero]
  rfl

/-- Any real action agreeing on scaled states agrees on every formal process. -/
theorem realEndHom_unique (f : ℝ →+* AddMonoid.End (Completion M))
    (hf : ∀ (a : ℝ≥0) (x : M), f (a : ℝ) (of x) = of (a • x)) :
    f = realEndHom := by
  have hnonneg (a : ℝ≥0) : f (a : ℝ) = realEndHom (a : ℝ) := by
    apply hom_ext
    intro x
    exact (hf a x).trans (by
      change of (a • x) = (a : ℝ) • (of x : Completion M)
      rw [coe_smul_eq_nnrealEnd, nnrealEnd_of])
  apply RingHom.ext
  intro r
  rw [← positive_difference r, map_sub, map_sub, hnonneg, hnonneg]

set_option backward.isDefEq.respectTransparency false in
/-- The real module structure extending the state's scaling is unique. -/
theorem module_unique (action : Module ℝ (Completion M))
    (h : ∀ (a : ℝ≥0) (x : M),
      (letI := action; (a : ℝ) • (of x : Completion M)) = of (a • x)) :
    action = instModuleReal := by
  have hEnd : (letI := action; Module.toAddMonoidEnd ℝ (Completion M)) = realEndHom :=
    realEndHom_unique _ h
  apply Module.ext'
  intro r v
  exact congrArg (fun f : ℝ →+* AddMonoid.End (Completion M) => f r v) hEnd

/-- The inclusion respects extensive scaling by nonnegative reals. -/
@[simp] theorem of_nnreal_smul (a : ℝ≥0) (x : M) :
    of (a • x) = a • (of x : Completion M) := by
  rw [NNReal.smul_def, coe_smul_eq_nnrealEnd, nnrealEnd_of]

/-- The inclusion as a linear map over nonnegative real scalars. -/
noncomputable def ofLinear : M →ₗ[ℝ≥0] Completion M where
  __ := of
  map_smul' := of_nnreal_smul

omit [Module ℝ≥0 M] in
private theorem lift_add_of {V : Type*} [AddCommGroup V] (f : M →+ V) (x : M) :
    Algebra.GrothendieckAddGroup.lift f (of x) = f x := by
  exact congrArg (fun g : M →+ V => g x)
    ((Algebra.GrothendieckAddGroup.lift (M := M) (G := V)).symm_apply_apply f)

/-- The universal extension of an extensive state function to real formal
differences. -/
noncomputable def liftLinear {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : M →ₗ[ℝ≥0] V) : Completion M →ₗ[ℝ] V where
  __ := Algebra.GrothendieckAddGroup.lift f.toAddMonoidHom
  map_smul' r v := by
    let g := Algebra.GrothendieckAddGroup.lift f.toAddMonoidHom
    have hnn (a : ℝ≥0) (w : Completion M) : g ((a : ℝ) • w) = (a : ℝ) • g w := by
      obtain ⟨y, x, rfl⟩ := exists_sub_of w
      simp only [smul_sub, coe_smul_eq_nnrealEnd, nnrealEnd_of, map_sub]
      simp only [g, lift_add_of, LinearMap.toAddMonoidHom_coe,
        map_smul, NNReal.smul_def]
    change g (r • v) = r • g v
    rw [← positive_difference r, sub_smul, map_sub, hnn, hnn, sub_smul]

@[simp]
theorem liftLinear_of {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : M →ₗ[ℝ≥0] V) (x : M) : liftLinear f (of x) = f x :=
  lift_add_of f.toAddMonoidHom x

/-- A real linear map on the completion is uniquely determined by its values
on the original states. -/
theorem liftLinear_unique {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : M →ₗ[ℝ≥0] V) (g : Completion M →ₗ[ℝ] V)
    (hg : ∀ x, g (of x) = f x) : g = liftLinear f := by
  apply LinearMap.toAddMonoidHom_injective
  exact hom_ext fun x => (hg x).trans (liftLinear_of f x).symm

/-- A faithful state map induces a faithful map on formal differences. -/
theorem liftLinear_injective {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : M →ₗ[ℝ≥0] V) (hf : Function.Injective f) :
    Function.Injective (liftLinear f) := by
  intro v w hvw
  obtain ⟨y, x, rfl⟩ := exists_sub_of v
  obtain ⟨b, a, rfl⟩ := exists_sub_of w
  have hdiff : f y - f x = f b - f a := by
    simpa only [map_sub, liftLinear_of] using hvw
  have hsum : y + a = b + x := hf (by
    simpa only [map_add] using (sub_eq_sub_iff_add_eq_add.mp hdiff))
  apply sub_eq_sub_iff_add_eq_add.mpr
  simpa only [map_add] using congrArg (of : M → Completion M) hsum

/-- A state map whose differences fill the target induces a surjection from
the completion. -/
theorem liftLinear_surjective {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : M →ₗ[ℝ≥0] V) (hf : ∀ v : V, ∃ y x : M, v = f y - f x) :
    Function.Surjective (liftLinear f) := by
  intro v
  obtain ⟨y, x, rfl⟩ := hf v
  exact ⟨of y - of x, by simp only [map_sub, liftLinear_of]⟩

/-- Stability makes the inclusion faithful. -/
theorem of_injective [PartialOrder M] [IsOrderedAddMonoid M] [PosSMulMono ℝ≥0 M]
    (hS : Stability M) : Function.Injective (of : M → Completion M) := by
  let := hS.isOrderedCancelAddMonoid
  exact Algebra.GrothendieckAddGroup.of_injective

end Completion

end ProjectAInos.Thermodynamics
