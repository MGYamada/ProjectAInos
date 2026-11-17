/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothAlgebra.Derivation
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic.Ring

/-!
# Jet C-infinity rings of fields and the total derivatives

A jet C-infinity ring of fields has independent variables indexed by `ι` and dependent
variables indexed by `κ`. It carries commuting vector fields `∂_μ` and `∂ᵃ_K` and elements
`uᵃ_K` dual to the latter, where the multi-index `K` is a multiset of independent variables,
and every element involves finitely many multi-indices. The total derivative
`D_μ F = ∂_μ F + Σ_K Σₐ uᵃ_{μ + K} ∂ᵃ_K F` is then a finite sum.

* `totalDeriv μ` is a vector field with `D_μ uᵃ_K = uᵃ_{μ + K}` (`totalDeriv_u`).
* `dx_totalDeriv`, `d_totalDeriv`: `[∂_ν, D_μ] = 0`, and `[∂ᵇ_L, D_μ] = ∂ᵇ_{L − μ}` if `μ` is
  in `L` and `0` otherwise.
* `totalDeriv_comm`: the total derivatives commute. For one independent variable there is
  nothing to prove; for several this is the statement that makes `D^K` well defined.

Everything here is algebra over an abstract C-infinity ring.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.Variational

open SmoothAlgebra SmoothRing SmoothOperation

/-- A jet C-infinity ring of fields with the independent variables `ι` and the dependent
variables `κ`. The element `u a K` is the derivative of the field `a` with the multi-index
`K`, and `d a K` is the partial derivative with respect to it. -/
structure FieldJetRing (ι κ : Type*) (J : Type*) [CommRing J] [Algebra ℝ J] [SmoothRing J] where
  /-- The partial derivative with respect to an independent variable. -/
  dx : ι → SmoothDerivation J J
  /-- The partial derivative with respect to `u a K`. -/
  d : κ → Multiset ι → SmoothDerivation J J
  /-- The derivative of the field `a` with the multi-index `K`. -/
  u : κ → Multiset ι → J
  /-- Each jet co-ordinate has unit derivative along itself. -/
  d_u_self : ∀ a K, d a K (u a K) = 1
  /-- Each jet co-ordinate is constant along the other jet directions. -/
  d_u_ne : ∀ a K b L, (a, K) ≠ (b, L) → d b L (u a K) = 0
  /-- The jet co-ordinates do not depend explicitly on the independent variables. -/
  dx_u : ∀ μ a K, dx μ (u a K) = 0
  /-- The derivatives with respect to the independent variables commute. -/
  dx_comm : ∀ μ ν (F : J), dx μ (dx ν F) = dx ν (dx μ F)
  /-- They commute with the derivatives with respect to the jet co-ordinates. -/
  dx_d_comm : ∀ μ a K (F : J), dx μ (d a K F) = d a K (dx μ F)
  /-- The derivatives with respect to the jet co-ordinates commute. -/
  d_comm : ∀ a K b L (F : J), d a K (d b L F) = d b L (d a K F)
  /-- Every element involves finitely many multi-indices. -/
  finite_support : ∀ F : J, ∃ S : Finset (Multiset ι), ∀ a K, K ∉ S → d a K F = 0

namespace FieldJetRing

variable {ι κ J : Type*} [CommRing J] [Algebra ℝ J] [SmoothRing J] (R : FieldJetRing ι κ J)

/-- `F` involves only the multi-indices of the finite set `S`. -/
def SupportIn (F : J) (S : Finset (Multiset ι)) : Prop := ∀ a K, K ∉ S → R.d a K F = 0

variable {R}

theorem SupportIn.mono {F : J} {S T : Finset (Multiset ι)} (h : R.SupportIn F S) (hST : S ⊆ T) :
    R.SupportIn F T := fun a K hK => h a K fun hS => hK (hST hS)

theorem SupportIn.d {F : J} {S : Finset (Multiset ι)} (h : R.SupportIn F S) (b : κ)
    (L : Multiset ι) : R.SupportIn (R.d b L F) S := fun a K hK => by
  rw [R.d_comm, h a K hK, map_zero]

theorem SupportIn.dx {F : J} {S : Finset (Multiset ι)} (h : R.SupportIn F S) (μ : ι) :
    R.SupportIn (R.dx μ F) S := fun a K hK => by
  rw [← R.dx_d_comm, h a K hK, map_zero]

theorem SupportIn.add {F G : J} {S : Finset (Multiset ι)} (hF : R.SupportIn F S)
    (hG : R.SupportIn G S) : R.SupportIn (F + G) S := fun a K hK => by
  rw [map_add, hF a K hK, hG a K hK, add_zero]

theorem SupportIn.mul {F G : J} {S : Finset (Multiset ι)} (hF : R.SupportIn F S)
    (hG : R.SupportIn G S) : R.SupportIn (F * G) S := fun a K hK => by
  rw [SmoothDerivation.map_mul, hF a K hK, hG a K hK, smul_zero, smul_zero, add_zero]

theorem SupportIn.sum {α : Type*} {s : Finset α} {F : α → J} {S : Finset (Multiset ι)}
    (h : ∀ c ∈ s, R.SupportIn (F c) S) : R.SupportIn (∑ c ∈ s, F c) S := fun a K hK => by
  rw [map_sum]
  exact Finset.sum_eq_zero fun c hc => h c hc a K hK

theorem SupportIn.op {n : ℕ} {x : Fin n → J} {S : Finset (Multiset ι)}
    (h : ∀ j, R.SupportIn (x j) S) (f : SmoothOperation n) : R.SupportIn (op f x) S :=
  fun a K hK => by
    rw [(R.d a K).chain]
    exact Finset.sum_eq_zero fun j _ => by rw [h j a K hK, smul_zero]

theorem supportIn_u [DecidableEq ι] (a : κ) (K : Multiset ι) : R.SupportIn (R.u a K) {K} :=
  fun b L hL => R.d_u_ne a K b L fun h => hL (by
    rw [Finset.mem_singleton]
    exact (Prod.mk.inj h).2.symm)

variable (R)

theorem exists_supportIn (F : J) : ∃ S, R.SupportIn F S := R.finite_support F

/-- Finitely many elements have a common finite set of multi-indices. -/
theorem exists_supportIn_fin [DecidableEq ι] {n : ℕ} (x : Fin n → J) :
    ∃ S, ∀ j, R.SupportIn (x j) S := by
  choose S hS using fun j => R.exists_supportIn (x j)
  exact ⟨Finset.univ.biUnion S, fun j =>
    (hS j).mono (Finset.subset_biUnion_of_mem S (Finset.mem_univ j))⟩

variable [Fintype κ]

/-- The function underlying the total derivative along the independent variable `μ`. The sum
over the multi-indices has finite support. -/
def totalDerivFun (μ : ι) (F : J) : J :=
  R.dx μ F + ∑ᶠ K : Multiset ι, ∑ a, R.u a (μ ::ₘ K) * R.d a K F

variable {R} in
theorem totalDerivFun_eq_sum (μ : ι) {F : J} {S : Finset (Multiset ι)} (h : R.SupportIn F S) :
    R.totalDerivFun μ F = R.dx μ F + ∑ K ∈ S, ∑ a, R.u a (μ ::ₘ K) * R.d a K F := by
  unfold totalDerivFun
  congr 1
  apply finsum_eq_sum_of_support_subset
  intro K hK
  rw [Function.mem_support] at hK
  by_contra hS
  refine hK (Finset.sum_eq_zero fun a _ => ?_)
  rw [h a K (by simpa using hS), mul_zero]

/-- The chain rule for the total derivative. -/
theorem totalDerivFun_op [DecidableEq ι] (μ : ι) {n : ℕ} (f : SmoothOperation n)
    (x : Fin n → J) :
    R.totalDerivFun μ (op f x) = ∑ j, op (partialDeriv j f) x * R.totalDerivFun μ (x j) := by
  obtain ⟨S, hS⟩ := R.exists_supportIn_fin x
  have key : ∑ K ∈ S, ∑ a, R.u a (μ ::ₘ K) * ∑ j, op (partialDeriv j f) x * R.d a K (x j) =
      ∑ j, op (partialDeriv j f) x * ∑ K ∈ S, ∑ a, R.u a (μ ::ₘ K) * R.d a K (x j) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ) (t := S)]
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => by ring
  rw [totalDerivFun_eq_sum μ (SupportIn.op hS f)]
  simp only [fun j => totalDerivFun_eq_sum μ (hS j), SmoothDerivation.chain, smul_eq_mul,
    mul_add, Finset.sum_add_distrib]
  rw [key]

variable [DecidableEq ι]

/-- The total derivative `D_μ F = ∂_μ F + Σ_K Σₐ uᵃ_{μ + K} ∂ᵃ_K F`, a vector field on the jet
ring. -/
def totalDeriv (μ : ι) : SmoothDerivation J J where
  toFun := R.totalDerivFun μ
  chain' f x := by simpa only [smul_eq_mul] using R.totalDerivFun_op μ f x

variable {R}

theorem totalDeriv_eq_sum (μ : ι) {F : J} {S : Finset (Multiset ι)} (h : R.SupportIn F S) :
    R.totalDeriv μ F = R.dx μ F + ∑ K ∈ S, ∑ a, R.u a (μ ::ₘ K) * R.d a K F :=
  totalDerivFun_eq_sum μ h

/-- A derivation that commutes with all the partial derivatives commutes with a total
derivative up to its values on the jet co-ordinates. -/
theorem apply_totalDeriv (δ : SmoothDerivation J J) (hδx : ∀ ν F, δ (R.dx ν F) = R.dx ν (δ F))
    (hδd : ∀ a K F, δ (R.d a K F) = R.d a K (δ F)) (μ : ι) {F : J} {S : Finset (Multiset ι)}
    (h : R.SupportIn F S) :
    δ (R.totalDeriv μ F) = R.totalDeriv μ (δ F) +
      ∑ K ∈ S, ∑ a, δ (R.u a (μ ::ₘ K)) * R.d a K F := by
  have hδF : R.SupportIn (δ F) S := fun a K hK => by rw [← hδd, h a K hK, map_zero]
  rw [totalDeriv_eq_sum μ h, totalDeriv_eq_sum μ hδF, map_add, map_sum, hδx, add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [δ.map_mul, smul_eq_mul, smul_eq_mul, hδd]
  ring

/-- `[∂_ν, D_μ] = 0`. -/
theorem dx_totalDeriv (ν μ : ι) (F : J) :
    R.dx ν (R.totalDeriv μ F) = R.totalDeriv μ (R.dx ν F) := by
  obtain ⟨S, hS⟩ := R.exists_supportIn F
  rw [apply_totalDeriv (R.dx ν) (fun ρ G => R.dx_comm ν ρ G)
    (fun a K G => R.dx_d_comm ν a K G) μ hS]
  simp [R.dx_u]

/-- `D_μ uᵃ_K = uᵃ_{μ + K}`. -/
theorem totalDeriv_u (μ : ι) (a : κ) (K : Multiset ι) :
    R.totalDeriv μ (R.u a K) = R.u a (μ ::ₘ K) := by
  rw [totalDeriv_eq_sum μ (supportIn_u a K), R.dx_u, zero_add, Finset.sum_singleton,
    Finset.sum_eq_single a]
  · rw [R.d_u_self, mul_one]
  · intro b _ hb
    rw [R.d_u_ne a K b K (fun h => hb (Prod.mk.inj h).1.symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- `[∂ᵇ_L, D_μ] = ∂ᵇ_{L − μ}` if `μ` is in `L`, and `0` otherwise. -/
theorem d_totalDeriv (b : κ) (L : Multiset ι) (μ : ι) (F : J) :
    R.d b L (R.totalDeriv μ F) =
      R.totalDeriv μ (R.d b L F) + if μ ∈ L then R.d b (L.erase μ) F else 0 := by
  obtain ⟨S, hS⟩ := R.exists_supportIn F
  have hS' : R.SupportIn F (insert (L.erase μ) S) := hS.mono (Finset.subset_insert _ _)
  rw [apply_totalDeriv (R.d b L) (fun ν G => (R.dx_d_comm ν b L G).symm)
    (fun a K G => R.d_comm b L a K G) μ hS']
  congr 1
  by_cases hμ : μ ∈ L
  · simp only [hμ, ↓reduceIte]
    rw [Finset.sum_eq_single (L.erase μ)]
    · rw [Finset.sum_eq_single b]
      · rw [Multiset.cons_erase hμ, R.d_u_self, one_mul]
      · intro a _ ha
        rw [R.d_u_ne a _ b L (fun h => ha (Prod.mk.inj h).1), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ b) h
    · intro K _ hK
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [R.d_u_ne a (μ ::ₘ K) b L (fun h => hK ?_), zero_mul]
      have hL : μ ::ₘ K = L := (Prod.mk.inj h).2
      rw [← hL, Multiset.erase_cons_head]
    · intro h
      exact absurd (Finset.mem_insert_self _ _) h
  · simp only [hμ, ↓reduceIte]
    refine Finset.sum_eq_zero fun K _ => Finset.sum_eq_zero fun a _ => ?_
    rw [R.d_u_ne a (μ ::ₘ K) b L (fun h => hμ ?_), zero_mul]
    have hL : μ ::ₘ K = L := (Prod.mk.inj h).2
    rw [← hL]
    exact Multiset.mem_cons_self μ K

/-- The total derivatives commute. -/
theorem totalDeriv_comm (μ ν : ι) (F : J) :
    R.totalDeriv μ (R.totalDeriv ν F) = R.totalDeriv ν (R.totalDeriv μ F) := by
  obtain ⟨S, hS⟩ := R.exists_supportIn F
  have hkey : ∀ μ ν : ι, R.totalDeriv μ (R.totalDeriv ν F) =
      R.dx μ (R.dx ν F) + ∑ K ∈ S, ∑ a, R.u a (μ ::ₘ K) * R.d a K (R.dx ν F) +
        (∑ L ∈ S, ∑ b, R.u b (μ ::ₘ ν ::ₘ L) * R.d b L F +
          ∑ L ∈ S, ∑ b, R.u b (ν ::ₘ L) * R.d b L (R.dx μ F) +
          ∑ L ∈ S, ∑ b, ∑ K ∈ S, ∑ a,
            R.u b (ν ::ₘ L) * (R.u a (μ ::ₘ K) * R.d a K (R.d b L F))) := by
    intro μ ν
    rw [totalDeriv_eq_sum ν hS, map_add, map_sum, totalDeriv_eq_sum μ (hS.dx ν)]
    congr 1
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun L _ => ?_
    rw [map_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [SmoothDerivation.map_mul, smul_eq_mul, smul_eq_mul, totalDeriv_u,
      totalDeriv_eq_sum μ (hS.d b L), R.dx_d_comm, mul_add, Finset.mul_sum]
    simp only [Finset.mul_sum]
    ring
  have hswap : ∀ G : Multiset ι → κ → Multiset ι → κ → J,
      ∑ L ∈ S, ∑ b, ∑ K ∈ S, ∑ a, G L b K a = ∑ K ∈ S, ∑ a, ∑ L ∈ S, ∑ b, G L b K a := by
    intro G
    calc ∑ L ∈ S, ∑ b, ∑ K ∈ S, ∑ a, G L b K a
        = ∑ L ∈ S, ∑ K ∈ S, ∑ b, ∑ a, G L b K a :=
          Finset.sum_congr rfl fun L _ => Finset.sum_comm
      _ = ∑ K ∈ S, ∑ L ∈ S, ∑ b, ∑ a, G L b K a := Finset.sum_comm
      _ = ∑ K ∈ S, ∑ L ∈ S, ∑ a, ∑ b, G L b K a :=
          Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun L _ => Finset.sum_comm
      _ = ∑ K ∈ S, ∑ a, ∑ L ∈ S, ∑ b, G L b K a :=
          Finset.sum_congr rfl fun K _ => Finset.sum_comm
  have hA : ∑ L ∈ S, ∑ b, R.u b (μ ::ₘ ν ::ₘ L) * R.d b L F =
      ∑ L ∈ S, ∑ b, R.u b (ν ::ₘ μ ::ₘ L) * R.d b L F :=
    Finset.sum_congr rfl fun L _ => Finset.sum_congr rfl fun b _ => by
      rw [Multiset.cons_swap]
  have hC : ∑ L ∈ S, ∑ b, ∑ K ∈ S, ∑ a,
        R.u b (ν ::ₘ L) * (R.u a (μ ::ₘ K) * R.d a K (R.d b L F)) =
      ∑ L ∈ S, ∑ b, ∑ K ∈ S, ∑ a,
        R.u b (μ ::ₘ L) * (R.u a (ν ::ₘ K) * R.d a K (R.d b L F)) := by
    rw [hswap]
    refine Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun L _ => Finset.sum_congr rfl fun b _ => ?_
    rw [R.d_comm a K b L]
    ring
  rw [hkey μ ν, hkey ν μ, R.dx_comm μ ν, hA, hC]
  abel

end FieldJetRing

end ProjectAinos.Variational
