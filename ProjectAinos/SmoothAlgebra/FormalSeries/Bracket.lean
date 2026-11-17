/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothAlgebra.FormalSeries.LieExp
import Mathlib.Tactic.Ring

/-!
# The Poisson bracket of formal power series in `q` and `p`

`PhaseSeries` is the ring `ℝ[[q, p]]`, with `q = X 0` and `p = X 1`, and
`bracket f g = ∂f/∂q ∂g/∂p − ∂f/∂p ∂g/∂q`. The bracket is a derivation in
each argument, satisfies the Jacobi identity and lowers the total order by
two. For a series `F` of order at least three the Lie transform
`lieExp (ad F)` is an automorphism of the algebra that preserves the bracket
(`lieAlgEquiv`, `lieExp_ad_bracket`).
-/

@[expose] public section
noncomputable section

open MvPowerSeries

namespace ProjectAinos.SmoothAlgebra.FormalSeries

/-- The formal power series in the coordinate `q = X 0` and the momentum
`p = X 1`. -/
abbrev PhaseSeries : Type := MvPowerSeries (Fin 2) ℝ

theorem pderiv_comm {σ : Type*} (i k : σ) (f : MvPowerSeries σ ℝ) :
    pderiv i (pderiv k f) = pderiv k (pderiv i f) := by
  ext d
  simp only [coeff_pderiv, Finsupp.coe_add, Pi.add_apply]
  rw [add_right_comm d]
  by_cases h : i = k
  · subst h
    ring
  · simp [h, Ne.symm h]
    ring

theorem pderiv_one_zero (f : PhaseSeries) :
    pderiv 1 (pderiv 0 f) = pderiv 0 (pderiv 1 f) :=
  pderiv_comm 1 0 f

/-- The canonical Poisson bracket `∂f/∂q ∂g/∂p − ∂f/∂p ∂g/∂q`. -/
def bracket (f g : PhaseSeries) : PhaseSeries :=
  pderiv 0 f * pderiv 1 g - pderiv 1 f * pderiv 0 g

theorem bracket_self (f : PhaseSeries) : bracket f f = 0 := by
  rw [bracket, mul_comm, sub_self]

theorem bracket_swap (f g : PhaseSeries) : bracket g f = -bracket f g := by
  simp only [bracket]
  ring

theorem bracket_add_left (f g h : PhaseSeries) :
    bracket (f + g) h = bracket f h + bracket g h := by
  simp only [bracket, map_add]
  ring

theorem bracket_add_right (f g h : PhaseSeries) :
    bracket f (g + h) = bracket f g + bracket f h := by
  simp only [bracket, map_add]
  ring

theorem bracket_smul_left (c : ℝ) (f g : PhaseSeries) :
    bracket (c • f) g = c • bracket f g := by
  rw [bracket, bracket, Derivation.map_smul, Derivation.map_smul, smul_mul_assoc,
    smul_mul_assoc, smul_sub]

theorem bracket_smul_right (c : ℝ) (f g : PhaseSeries) :
    bracket f (c • g) = c • bracket f g := by
  rw [bracket, bracket, Derivation.map_smul, Derivation.map_smul, mul_smul_comm,
    mul_smul_comm, smul_sub]

theorem bracket_sub_left (f g h : PhaseSeries) :
    bracket (f - g) h = bracket f h - bracket g h := by
  simp only [bracket, map_sub]
  ring

theorem bracket_sub_right (f g h : PhaseSeries) :
    bracket f (g - h) = bracket f g - bracket f h := by
  simp only [bracket, map_sub]
  ring

theorem bracket_zero_left (g : PhaseSeries) : bracket 0 g = 0 := by
  simp [bracket]

theorem bracket_zero_right (f : PhaseSeries) : bracket f 0 = 0 := by
  simp [bracket]

theorem bracket_neg_right (f g : PhaseSeries) : bracket f (-g) = -bracket f g := by
  simp only [bracket, map_neg]
  ring

theorem pderiv_zero_X_zero : pderiv 0 (X 0 : PhaseSeries) = 1 := pderiv_X_self

theorem pderiv_one_X_one : pderiv 1 (X 1 : PhaseSeries) = 1 := pderiv_X_self

theorem pderiv_zero_X_one : pderiv 0 (X 1 : PhaseSeries) = 0 := pderiv_X_of_ne (by decide)

theorem pderiv_one_X_zero : pderiv 1 (X 0 : PhaseSeries) = 0 := pderiv_X_of_ne (by decide)

theorem bracket_mul_right (f g h : PhaseSeries) :
    bracket f (g * h) = bracket f g * h + g * bracket f h := by
  simp only [bracket, Derivation.leibniz, smul_eq_mul]
  ring

theorem bracket_mul_left (f g h : PhaseSeries) :
    bracket (f * g) h = bracket f h * g + f * bracket g h := by
  simp only [bracket, Derivation.leibniz, smul_eq_mul]
  ring

/-- The Jacobi identity: the bracket with `f` is a derivation of the bracket. -/
theorem bracket_bracket (f g h : PhaseSeries) :
    bracket f (bracket g h) = bracket (bracket f g) h + bracket g (bracket f h) := by
  simp only [bracket, map_sub, Derivation.leibniz, smul_eq_mul, pderiv_one_zero]
  ring

theorem bracket_X_zero_X_one : bracket (X 0 : PhaseSeries) (X 1) = 1 := by
  simp [bracket]

/-- The bracket lowers the total order by at most two. -/
theorem bracket_mem_orderGE {m n : ℕ} {f g : PhaseSeries} (hf : f ∈ orderGE (Fin 2) m)
    (hg : g ∈ orderGE (Fin 2) n) : bracket f g ∈ orderGE (Fin 2) (m + n - 2) := by
  have h1 := mul_mem_orderGE (pderiv_mem_orderGE hf 0) (pderiv_mem_orderGE hg 1)
  have h2 := mul_mem_orderGE (pderiv_mem_orderGE hf 1) (pderiv_mem_orderGE hg 0)
  exact sub_mem (mem_orderGE_of_le h1 (by omega)) (mem_orderGE_of_le h2 (by omega))

/-- The bracket as a bilinear map. -/
def bracketₗ : PhaseSeries →ₗ[ℝ] PhaseSeries →ₗ[ℝ] PhaseSeries :=
  LinearMap.mk₂ ℝ bracket bracket_add_left bracket_smul_left bracket_add_right
    bracket_smul_right

theorem bracketₗ_apply (f g : PhaseSeries) : bracketₗ f g = bracket f g :=
  rfl

/-- The bracket with a fixed series. -/
def ad (F : PhaseSeries) : PhaseSeries →ₗ[ℝ] PhaseSeries := bracketₗ F

theorem ad_apply (F g : PhaseSeries) : ad F g = bracket F g :=
  rfl

theorem ad_add (F G : PhaseSeries) : ad (F + G) = ad F + ad G :=
  map_add bracketₗ F G

/-- The bracket with a series of order `j + 2` raises the order by `j`. -/
theorem raises_ad {j : ℕ} {F : PhaseSeries} (hF : F ∈ orderGE (Fin 2) (j + 2)) :
    Raises (ad F) j :=
  fun _ _ hg => mem_orderGE_of_le (bracket_mem_orderGE hF hg) (by omega)

section LieTransform

variable {j : ℕ} {F : PhaseSeries}

/-- The Lie transform preserves the product. -/
theorem lieExp_ad_mul (hF : F ∈ orderGE (Fin 2) (j + 3)) (f g : PhaseSeries) :
    lieExp (ad F) (f * g) = lieExp (ad F) f * lieExp (ad F) g :=
  lieExp_bilinear (B := LinearMap.mul ℝ PhaseSeries) (c := 0)
    (fun _ _ _ _ hf hg => by simpa using mul_mem_orderGE hf hg)
    (raises_ad (j := j + 1) hF) (Nat.le_add_left 1 j)
    (fun f g => by
      simp only [LinearMap.mul_apply', ad_apply, bracket_mul_right]) f g

/-- The Lie transform preserves the bracket. -/
theorem lieExp_ad_bracket (hF : F ∈ orderGE (Fin 2) (j + 3)) (f g : PhaseSeries) :
    lieExp (ad F) (bracket f g) = bracket (lieExp (ad F) f) (lieExp (ad F) g) :=
  lieExp_bilinear (B := bracketₗ) (c := 2)
    (fun _ _ _ _ hf hg => bracket_mem_orderGE hf hg)
    (raises_ad (j := j + 1) hF) (Nat.le_add_left 1 j)
    (fun f g => bracket_bracket F f g) f g

theorem lieExp_ad_one (hF : F ∈ orderGE (Fin 2) (j + 3)) : lieExp (ad F) 1 = 1 :=
  lieExp_eq_self (raises_ad (j := j + 1) hF) (Nat.le_add_left 1 j)
    (by simp [ad_apply, bracket])

/-- The Lie transform of a series of order at least three, as an automorphism
of the algebra. -/
def lieAlgEquiv (F : PhaseSeries) (hF : F ∈ orderGE (Fin 2) 3) :
    PhaseSeries ≃ₐ[ℝ] PhaseSeries :=
  AlgEquiv.ofBijective
    (AlgHom.ofLinearMap (lieExp (ad F)) (lieExp_ad_one (j := 0) hF)
      (lieExp_ad_mul (j := 0) hF))
    (bijective_lieExp (raises_ad (j := 1) hF) le_rfl)

theorem lieAlgEquiv_apply (F : PhaseSeries) (hF : F ∈ orderGE (Fin 2) 3) (g : PhaseSeries) :
    lieAlgEquiv F hF g = lieExp (ad F) g :=
  rfl

end LieTransform

end ProjectAinos.SmoothAlgebra.FormalSeries
