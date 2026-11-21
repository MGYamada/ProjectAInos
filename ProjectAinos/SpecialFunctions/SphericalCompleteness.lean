/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.SphericalOrthogonality
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Tactic

/-! # Completeness of the spherical harmonics

On the unit sphere the squared radius is one. Repeated Fischer decomposition therefore
expresses every polynomial restriction as a finite sum of harmonics. Polynomial restrictions
separate points, so Stone–Weierstrass gives uniform density. Passing to surface measure gives
the orthogonal Hilbert sum decomposition of real L².
-/

@[expose] public section
noncomputable section

open MvPolynomial MeasureTheory Metric Set
open ProjectAinos.SpecialFunctions.HarmonicPolynomial
namespace ProjectAinos.SpecialFunctions.SphericalHarmonics

private abbrev Poly (d : ℕ) := MvPolynomial (Fin d) ℝ

/-- Polynomial evaluation as a continuous function on the sphere. -/
def onSphere (d : ℕ) : MvPolynomial (Fin d) ℝ →ₐ[ℝ] C(UnitSphere d, ℝ) where
  toFun p := ⟨fun u => eval u.val p, (MvPolynomial.continuous_eval p).comp
    (continuous_pi fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp
      continuous_subtype_val)⟩
  map_one' := by ext; simp
  map_mul' p q := by ext; simp
  map_zero' := by ext; simp
  map_add' p q := by ext; simp
  commutes' a := by ext; simp

/-- Degree-`k` harmonics with the topology of uniform convergence on the sphere. -/
def continuousSpace (d k : ℕ) : Submodule ℝ C(UnitSphere d, ℝ) :=
  (harmonics d k).map ((onSphere d).toLinearMap.comp (homogeneousSubmodule (Fin d) ℝ k).subtype)

private theorem onSphere_radiusSq (d : ℕ) : onSphere d (radiusSq d) = 1 := by
  ext u
  change eval u.val (radiusSq d) = 1
  simp [radiusSq, ← EuclideanSpace.real_norm_sq_eq, norm_eq_of_mem_sphere u]

private theorem homogeneous_mem {d : ℕ} (hd : 0 < d) (k : ℕ) (p : Poly d)
    (hp : p.IsHomogeneous k) : onSphere d p ∈ ⨆ j, continuousSpace d j := by
  induction k using Nat.strong_induction_on generalizing p with
  | h k ih =>
    have mem {q : Poly d} (h : q.IsHomogeneous k) (h' : laplacian d q = 0) :
        onSphere d q ∈ ⨆ j, continuousSpace d j :=
      (le_iSup (continuousSpace d) k : continuousSpace d k ≤ _) ⟨⟨q, h⟩, h', rfl⟩
    by_cases hk : k ≤ 1
    · exact mem hp (laplacian_eq_zero_of_degree_le_one hp hk)
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      obtain ⟨q, hq, _⟩ := existsUnique_fischer hd hp
      have h := Submodule.add_mem _ (mem hq.1 hq.2) (ih j (by omega) q.val q.property)
      simpa [onSphere_radiusSq] using h

private theorem separates (d : ℕ) : (onSphere d).range.SeparatesPoints := by
  intro u v huv
  obtain ⟨i, hi⟩ : ∃ i, u.val i ≠ v.val i := by
    by_contra! h
    exact huv (Subtype.ext (PiLp.ext h))
  refine ⟨_, ⟨onSphere d (X i), ⟨X i, rfl⟩, rfl⟩, ?_⟩
  simpa [onSphere] using hi

/-- Finite sums of harmonic restrictions approximate every real continuous function uniformly. -/
theorem continuousSpace_dense {d : ℕ} (hd : 0 < d) :
    Dense (↑(⨆ j, continuousSpace d j) : Set C(UnitSphere d, ℝ)) := by
  have h := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    (onSphere d).range (separates d)
  apply Dense.mono (s₁ := ((onSphere d).range : Set C(UnitSphere d, ℝ)))
  · rintro f ⟨p, rfl⟩
    rw [← sum_homogeneousComponent p, map_sum]
    exact Submodule.sum_mem _ (fun j _ => homogeneous_mem hd j _ (homogeneousComponent_mem j p))
  · exact dense_iff_closure_eq.mpr (congrArg SetLike.coe h)

/-- The canonical surface measure associated with Euclidean volume in ambient dimension `d`. -/
abbrev surfaceMeasure (d : ℕ) : Measure (UnitSphere d) :=
  (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere

/-- The degree-`k` subspace of real L² for Euclidean surface measure. -/
def l2Space (d k : ℕ) : Submodule ℝ (Lp ℝ 2 (surfaceMeasure d)) :=
  (continuousSpace d k).map (ContinuousMap.toLp 2 (surfaceMeasure d) ℝ).toLinearMap

instance finite_l2Space (d k : ℕ) : FiniteDimensional ℝ (l2Space d k) := by
  let : FiniteDimensional ℝ (homogeneousSubmodule (Fin d) ℝ k) :=
    (Submodule.fg_iff_finiteDimensional _).mp (homogeneousSubmodule_fg _ _ _)
  unfold l2Space continuousSpace
  infer_instance

/-- Each individual L² mode has a unique continuous representative. -/
def representative (d k : ℕ) : l2Space d k →ₗ[ℝ] C(UnitSphere d, ℝ) :=
  (continuousSpace d k).subtype.comp ((continuousSpace d k).equivMapOfInjective
    (ContinuousMap.toLp 2 (surfaceMeasure d) ℝ).toLinearMap
    (ContinuousMap.toLp_injective (surfaceMeasure d))).symm.toLinearMap

@[simp] theorem toLp_representative {d k : ℕ} (f : l2Space d k) :
    ContinuousMap.toLp 2 (surfaceMeasure d) ℝ (representative d k f) = f.val :=
  Submodule.map_equivMapOfInjective_symm_apply _
    (ContinuousMap.toLp_injective (surfaceMeasure d)) _ _

/-- Identify a homogeneous harmonic polynomial with its L² mode by restriction. -/
def harmonicsEquivL2 {d : ℕ} (hd : 0 < d) (k : ℕ) :
    harmonics d k ≃ₗ[ℝ] l2Space d k := by
  let F := (onSphere d).toLinearMap.comp (homogeneousSubmodule (Fin d) ℝ k).subtype
  have hi : Function.Injective F := by
    intro p q h
    apply restrict_injective hd k
    exact funext fun u => DFunLike.congr_fun h u
  exact ((harmonics d k).equivMapOfInjective F hi).trans
    ((continuousSpace d k).equivMapOfInjective
      (ContinuousMap.toLp 2 (surfaceMeasure d) ℝ).toLinearMap
      (ContinuousMap.toLp_injective (surfaceMeasure d)))

/-- The canonical representative of the L² mode is polynomial evaluation on the sphere. -/
theorem representative_harmonicsEquivL2 {d : ℕ} (hd : 0 < d) (k : ℕ) (p : harmonics d k) :
    representative d k (harmonicsEquivL2 hd k p) = onSphere d p.val.val := by
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) (surfaceMeasure d)
  rw [toLp_representative]
  rfl

/-- Passage to L² retains the full dimension of the harmonic polynomials in positive dimension. -/
theorem finrank_l2Space {d : ℕ} (hd : 0 < d) (k : ℕ) :
    Module.finrank ℝ (l2Space d k) = Module.finrank ℝ (harmonics d k) :=
  (harmonicsEquivL2 hd k).finrank_eq.symm

/-- The closed span of all spherical harmonic degrees is real L² of the sphere. -/
theorem l2Space_dense {d : ℕ} (hd : 0 < d) :
    (⨆ j, l2Space d j).topologicalClosure = ⊤ := by
  let T := ContinuousMap.toLp (E := ℝ) 2 (surfaceMeasure d) ℝ
  have hT : DenseRange T := ContinuousMap.toLp_denseRange ℝ _ ℝ (by norm_num)
  have h := hT.dense_image T.continuous (continuousSpace_dense hd)
  change ((⨆ j, (continuousSpace d j).map T.toLinearMap) : Submodule _ _).topologicalClosure = ⊤
  rw [← Submodule.map_iSup]
  exact SetLike.ext' h.closure_eq

/-- Real L² of the unit sphere is the orthogonal Hilbert sum of its harmonic degrees. -/
theorem isHilbertSum {d : ℕ} (hd : 0 < d) :
    IsHilbertSum ℝ (fun k => l2Space d k) (fun k => (l2Space d k).subtypeₗᵢ) := by
  apply IsHilbertSum.mkInternal
  · intro k m hne f g
    obtain ⟨a, ⟨p, hp, rfl⟩, ha⟩ := f.property
    obtain ⟨b, ⟨q, hq, rfl⟩, hb⟩ := g.property
    change inner ℝ f.val g.val = 0
    rw [← ha, ← hb, L2.inner_def]
    have he := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (surfaceMeasure d) (onSphere d p.val)
    have he' := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (surfaceMeasure d) (onSphere d q.val)
    refine (integral_congr_ae ?_).trans (integral_mul_eq_zero hd hne
      (f := restrict d k p) (g := restrict d m q) ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩)
    filter_upwards [he, he'] with u hu hv
    rw [real_inner_comm, RCLike.inner_apply]
    exact congrArg₂ (· * ·) hu hv
  · exact (l2Space_dense hd).ge

end ProjectAinos.SpecialFunctions.SphericalHarmonics
