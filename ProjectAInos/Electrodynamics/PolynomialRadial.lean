module
public import ProjectAInos.External.YM.Maxwell.Exterior

/-! # Scalar and vector-valued homogeneous radial reconstruction

The reconstruction argument is adapted from YM.Maxwell.curl_inverse at the
pinned upstream revision recorded in External/YM/PROVENANCE.md (Apache-2.0).
Here the target is any real normed vector space, including ℝ; a gauge group
and its color space are not prerequisites. This is a polynomial Poincaré
lemma and makes no assertion about global potentials or Lorentzian dynamics.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped ContDiff
namespace ProjectAInos.Electrodynamics.Polynomial
open YM YM.Tensor YM.Analysis YM.Maxwell
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {j : ℕ}

def radial (Q : TwoJet V j) (ν : Axis) (x : E4) : V :=
  (↑(j + 2 : ℕ) : ℝ)⁻¹ • ∑ μ : Axis, x μ • diagonal (Q μ ν) x

def radialCoefficient (Q : TwoJet V j) (ν : Axis) : T E4 V (j + 1) :=
  (↑(j + 2 : ℕ) : ℝ)⁻¹ • ∑ μ : Axis, added (Q μ ν) (compAxis μ)

theorem radialCoefficient_diagonal (Q : TwoJet V j) (ν : Axis) (x : E4) :
    diagonal (radialCoefficient Q ν) x = radial Q ν x := by
  simp only [radialCoefficient, radial, diagonal, smul_apply, sum_apply]
  congr 1
  exact Finset.sum_congr rfl (fun μ _ => added_diag ..)

theorem radial_smooth (Q : TwoJet V j) (ν : Axis) (n : ℕ∞ω) :
    ContDiff ℝ n (radial Q ν) := by
  rw [← funext (radialCoefficient_diagonal Q ν)]
  exact diag_smooth _ n

theorem radial_gauge (Q : TwoJet V j) (h : ClosedJet Q) (x : E4) :
    ∑ ν : Axis, x ν • radial Q ν x = 0 := by
  let t := ∑ ν : Axis, x ν • radial Q ν x
  have he : t = -t := by
    dsimp only [t, radial]
    simp_rw [Finset.smul_sum, ← Finset.sum_neg_distrib, ← smul_neg]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    nth_rw 1 [h.antisymmetric a b]
    simp only [smul_smul, diagonal, neg_apply]
    congr 1
    ring
  have hz : (2 : ℝ) • t = 0 := by rw [two_smul]; nth_rw 1 [he]; simp
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

/-- dA = F with the coefficient 1/(j+2), including j = 0. -/
theorem radial_curl {Q : TwoJet V j} (h : ClosedJet Q) (i l : Axis) (x : E4) :
    grad i (radial Q l) x - grad l (radial Q i) x = diagonal (Q i l) x := by
  let c : ℝ := (j + 2 : ℕ)
  have he (i l : Axis) : grad i (radial Q l) x =
      c⁻¹ • (diagonal (Q i l) x + ∑ k : Axis, x k • grad i (diagonal (Q k l)) x) := by
    rw [← grad_self (fun k => Q k l) i x]
    unfold radial grad D
    rw [fderiv_fun_const_smul]
    · rfl
    exact DifferentiableAt.fun_sum fun k _ => (compAxis k).differentiableAt.smul
      ((diag_smooth _ ∞).differentiable (by simp) _)
  have hz (i l k : Axis) : grad i (diagonal (Q l k)) x = -grad i (diagonal (Q k l)) x := by
    nth_rw 1 [h.antisymmetric l k]
    change fderiv ℝ (-diagonal (Q k l)) x _ = _
    rw [fderiv_neg]
    rfl
  have hw (k : Axis) : grad i (diagonal (Q k l)) x - grad l (diagonal (Q k i)) x =
      grad k (diagonal (Q i l)) x := by
    have H := h.closed k i l x
    conv at H => lhs; arg 1; arg 2; rw [hz]
    rw [← add_right_cancel_iff (a := (-(grad i (diagonal (Q k l)) x) + grad l (diagonal (Q k i)) x))]
    rw [add_assoc] at H
    rw [H]
    abel
  rw [he i l, he l i, ← smul_sub, add_sub_add_comm, ← Finset.sum_sub_distrib]
  simp_rw [← smul_sub, hw, grad_euler (Q i l) (h.coeffSym i l) x]
  rw [show diagonal (Q l i) x = -diagonal (Q i l) x from
    congrArg (fun A : T E4 V j => diagonal A x) (h.antisymmetric l i)]
  rw [sub_neg_eq_add, ← two_smul ℝ, ← add_smul, add_comm (2 : ℝ),
    show (j : ℝ) + 2 = c by push_cast [c]; rfl,
    smul_smul, inv_mul_cancel₀ (by dsimp [c]; positivity), one_smul]

/-- The generic formula agrees exactly with the imported color-valued potential. -/
theorem radial_upstream {G : Gauge} {Q : TwoJet G.Color j} (h : ClosedJet Q)
    (ν : Axis) (x : E4) : radial Q ν x = (contracted h).value ν x :=
  (contracted_diag h ν x).symm

def mapCoefficients (ℓ : V →L[ℝ] ℝ) (Q : TwoJet V j) : TwoJet ℝ j :=
  fun i k => ℓ.compContinuousMultilinearMap (Q i k)

theorem mapCoefficients_diagonal (ℓ : V →L[ℝ] ℝ) (Q : TwoJet V j)
    (i k : Axis) (x : E4) : diagonal (mapCoefficients ℓ Q i k) x = ℓ (diagonal (Q i k) x) := rfl

theorem radial_map (ℓ : V →L[ℝ] ℝ) (Q : TwoJet V j) (ν : Axis) (x : E4) :
    radial (mapCoefficients ℓ Q) ν x = ℓ (radial Q ν x) := by
  simp [radial, mapCoefficients_diagonal]

theorem mapCoefficients_closed (ℓ : V →L[ℝ] ℝ) {Q : TwoJet V j} (h : ClosedJet Q) :
    ClosedJet (mapCoefficients ℓ Q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i k v s
    change ℓ (Q i k (v ∘ s)) = ℓ (Q i k v)
    rw [h.coeffSym]
  · intro i k
    ext v
    change ℓ (Q i k v) = -(ℓ (Q k i v))
    rw [h.antisymmetric]
    simp
  · intro a b c x
    have he (i k l : Axis) : grad i (diagonal (mapCoefficients ℓ Q k l)) x =
        ℓ (grad i (diagonal (Q k l)) x) := by
      have hd := (ℓ.hasFDerivAt.comp x ((diag_smooth (Q k l) ∞).differentiable (by simp) x).hasFDerivAt).fderiv
      change fderiv ℝ (ℓ ∘ diagonal (Q k l)) x (basis i) = _
      rw [hd]
      rfl
    rw [he, he, he, ← map_add, ← map_add, h.closed, map_zero]

end ProjectAInos.Electrodynamics.Polynomial
