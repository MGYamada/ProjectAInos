/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateScalarField

/-!
# The action of a one-form on a fixed coordinate metric

For a coordinate metric `g` on an open set `U`, a field of covectors `A` (a potential) that is
smooth on `U` and a current `j` continuous on `U`, the density
`ℒ(A) = (−¼ F_{ab} F^{ab} − A_b j^b) √|g|` with `F_{ab} = ∂_a A_b − ∂_b A_a` has, for a smooth
variation `η` with compact support in `U`, the relative action
`S[A + εη] − S[A] = ε ∫ η_b (∂_a(√|g| F^{ab}) − √|g| j^b) dx − ¼ ε² ∫ G_{ab} G^{ab} √|g| dx`
with `G = dη` (`potentialAction_eq`). It is stationary under every such `η` if and only if
`∂_a(√|g| F^{ab}) = √|g| j^b` on `U` (`isPotentialStationary_iff`), the Maxwell equation
`∇_a F^{ab} = j^b`.

For a native two-form `F` on `U` with the components `F_{ab}` and a native vector field `J` with
the components `j^b`, this is the native equation `∇_a F^{ab} = J^b` of
`LorentzMetric.twoFormDivergence` (`twoFormDivergence_eq_iff`).
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

namespace CoordinateMetric

variable {U : Opens (MinkowskiModel d)} {g : CoordinateMetric σ d U}

/-- The field `F_{ab} = ∂_a A_b − ∂_b A_a` of a field of covectors. -/
def potentialField (A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ) (z : MinkowskiModel d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.of fun a b => fderiv ℝ (fun w => A w (Pi.single b 1)) z (Pi.single a 1) -
    fderiv ℝ (fun w => A w (Pi.single a 1)) z (Pi.single b 1)

theorem potentialField_antisymm (A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ)
    (z : MinkowskiModel d) (a b : Fin (d + 1)) :
    potentialField A z a b = -potentialField A z b a := by
  simp only [potentialField, Matrix.of_apply]
  ring

variable (g) in
/-- The bilinear invariant `⟨F, G⟩ = F_{ab} G_{ce} g^{ac} g^{be}`. -/
def fieldPairing (F G : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (z : MinkowskiModel d) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ e, (g.coefficient z)⁻¹ a c * (g.coefficient z)⁻¹ b e * (F z a b * G z c e)

variable (g) in
/-- The raised field `F^{ab} = g^{ac} g^{be} F_{ce}`. -/
def raisedField (F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (z : MinkowskiModel d) (a b : Fin (d + 1)) : ℝ :=
  ∑ c, ∑ e, (g.coefficient z)⁻¹ a c * (g.coefficient z)⁻¹ b e * F z c e

variable (g) in
/-- The density `(−¼ F_{ab} F^{ab} − A_b j^b) √|g|` of a potential with the current `j`. -/
def potentialDensity (j : MinkowskiModel d → Fin (d + 1) → ℝ)
    (A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ) (z : MinkowskiModel d) : ℝ :=
  (-(g.fieldPairing (potentialField A) (potentialField A) z / 4) -
    ∑ b, A z (Pi.single b 1) * j z b) * densityOf g.coefficient z

variable (g) in
/-- The relative action `S[A + εη] − S[A]`. -/
def potentialAction (j : MinkowskiModel d → Fin (d + 1) → ℝ)
    (A η : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ) (ε : ℝ) : ℝ :=
  ∫ x, (g.potentialDensity j (fun z => A z + ε • η z) x - g.potentialDensity j A x)

variable (g) in
/-- The Euler–Lagrange expression `∂_a(√|g| F^{ab}) − √|g| j^b`. -/
def potentialEuler (j : MinkowskiModel d → Fin (d + 1) → ℝ)
    (A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ) (z : MinkowskiModel d) (b : Fin (d + 1)) :
    ℝ :=
  ∑ a, fderiv ℝ (fun w => densityOf g.coefficient w * g.raisedField (potentialField A) w a b) z
    (Pi.single a 1) - densityOf g.coefficient z * j z b

variable {A η : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ}

theorem differentiableAt_component (hA : ContDiffOn ℝ ∞ A U) {z : MinkowskiModel d} (hz : z ∈ U)
    (v : MinkowskiModel d) : DifferentiableAt ℝ (fun w => A w v) z :=
  (((hA.clm_apply contDiffOn_const).contDiffAt (U.isOpen.mem_nhds hz))).differentiableAt
    (by simp)

theorem component_eventually_zero {z : MinkowskiModel d} (hz : z ∉ tsupport η)
    (v : MinkowskiModel d) : (fun w => η w v) =ᶠ[𝓝 z] fun _ => 0 := by
  filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hz] with w hw
  simp [image_eq_zero_of_notMem_tsupport hw]

theorem potentialField_of_notMem {z : MinkowskiModel d} (hz : z ∉ tsupport η) :
    potentialField η z = 0 := by
  ext a b
  simp only [potentialField, Matrix.of_apply, (component_eventually_zero hz _).fderiv_eq,
    fderiv_const_apply, Matrix.zero_apply, zero_apply, sub_self]

/-- The field of `A + εη` is `F + ε G`. -/
theorem potentialField_add (hA : ContDiffOn ℝ ∞ A U) (hη : ContDiff ℝ ∞ η)
    (hKU : tsupport η ⊆ U) (ε : ℝ) (z : MinkowskiModel d) :
    potentialField (fun w => A w + ε • η w) z = potentialField A z + ε • potentialField η z := by
  by_cases hz : z ∈ U
  · have hηd (v : MinkowskiModel d) : DifferentiableAt ℝ (fun w => η w v) z :=
      ((hη.clm_apply contDiff_const).differentiable (by simp)) z
    have hfd (v : MinkowskiModel d) : fderiv ℝ (fun w => (A w + ε • η w) v) z =
        fderiv ℝ (fun w => A w v) z + ε • fderiv ℝ (fun w => η w v) z := by
      simp only [add_apply, smul_apply, smul_eq_mul]
      rw [fderiv_fun_add (differentiableAt_component hA hz v) ((hηd v).const_mul ε),
        fderiv_const_mul (hηd v)]
    ext a b
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    simp only [potentialField, Matrix.of_apply]
    rw [hfd, hfd]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  · have hzK : z ∉ tsupport η := fun h' => hz (hKU h')
    have heq (v : MinkowskiModel d) : (fun w => (A w + ε • η w) v) =ᶠ[𝓝 z] fun w => A w v := by
      filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hzK] with w hw
      simp [image_eq_zero_of_notMem_tsupport hw]
    rw [potentialField_of_notMem hzK, smul_zero, add_zero]
    ext a b
    simp only [potentialField, Matrix.of_apply]
    rw [(heq _).fderiv_eq, (heq _).fderiv_eq]

theorem fieldPairing_add_smul (F G : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (ε : ℝ) (z : MinkowskiModel d) :
    g.fieldPairing (fun w => F w + ε • G w) (fun w => F w + ε • G w) z =
      g.fieldPairing F F z + ε * (g.fieldPairing F G z + g.fieldPairing G F z) +
        ε ^ 2 * g.fieldPairing G G z := by
  have hterm (a b c e : Fin (d + 1)) : (g.coefficient z)⁻¹ a c * (g.coefficient z)⁻¹ b e *
      ((F z a b + ε * G z a b) * (F z c e + ε * G z c e)) =
      (g.coefficient z)⁻¹ a c * (g.coefficient z)⁻¹ b e * (F z a b * F z c e) +
        ε * ((g.coefficient z)⁻¹ a c * (g.coefficient z)⁻¹ b e * (F z a b * G z c e) +
          (g.coefficient z)⁻¹ a c * (g.coefficient z)⁻¹ b e * (G z a b * F z c e)) +
        ε ^ 2 * ((g.coefficient z)⁻¹ a c * (g.coefficient z)⁻¹ b e * (G z a b * G z c e)) := by
    ring
  simp only [fieldPairing, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hterm,
    Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Exchanging two pairs of finite sums. -/
theorem sum4_swap_pairs {n : ℕ} (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, f a b c e = ∑ c, ∑ e, ∑ a, ∑ b, f a b c e :=
  calc ∑ a, ∑ b, ∑ c, ∑ e, f a b c e = ∑ a, ∑ c, ∑ b, ∑ e, f a b c e :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ e, f a b c e := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ e, ∑ b, f a b c e :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ e, ∑ a, ∑ b, f a b c e := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem fieldPairing_comm {z : MinkowskiModel d} (hz : z ∈ U)
    (F G : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    g.fieldPairing G F z = g.fieldPairing F G z := by
  have hAs (e₁ e₂ : Fin (d + 1)) : (g.coefficient z)⁻¹ e₁ e₂ = (g.coefficient z)⁻¹ e₂ e₁ :=
    g.coefficient_inv_symmetric hz e₁ e₂
  set h : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ := fun a b c e =>
    (g.coefficient z)⁻¹ a c * (g.coefficient z)⁻¹ b e * (F z a b * G z c e) with hh
  unfold fieldPairing
  calc ∑ a, ∑ b, ∑ c, ∑ e, (g.coefficient z)⁻¹ a c * (g.coefficient z)⁻¹ b e *
        (G z a b * F z c e) = ∑ a, ∑ b, ∑ c, ∑ e, h c e a b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => by
            simp only [hh]
            rw [hAs c a, hAs e b]
            ring
    _ = ∑ a, ∑ c, ∑ b, ∑ e, h c e a b := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ e, h c e a b := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ e, ∑ b, h c e a b :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ e, ∑ a, ∑ b, h c e a b := Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- **The relative density is a quadratic polynomial in `ε`.** -/
theorem potentialDensity_sub (hA : ContDiffOn ℝ ∞ A U) (hη : ContDiff ℝ ∞ η)
    (hKU : tsupport η ⊆ U) (j : MinkowskiModel d → Fin (d + 1) → ℝ) (ε : ℝ)
    (z : MinkowskiModel d) :
    g.potentialDensity j (fun w => A w + ε • η w) z - g.potentialDensity j A z =
      (ε * (-(g.fieldPairing (potentialField A) (potentialField η) z / 2) -
          ∑ b, η z (Pi.single b 1) * j z b) -
        ε ^ 2 * (g.fieldPairing (potentialField η) (potentialField η) z / 4)) *
        densityOf g.coefficient z := by
  have hF : potentialField (fun w => A w + ε • η w) =
      fun w => potentialField A w + ε • potentialField η w :=
    funext fun w => potentialField_add hA hη hKU ε w
  have hcross : g.fieldPairing (potentialField η) (potentialField A) z =
      g.fieldPairing (potentialField A) (potentialField η) z := by
    by_cases hz : z ∈ U
    · exact fieldPairing_comm hz _ _
    · have hzK : z ∉ tsupport η := fun h' => hz (hKU h')
      simp [fieldPairing, potentialField_of_notMem hzK]
  have hsrc : ∑ b, (A z + ε • η z) (Pi.single b 1) * j z b =
      ∑ b, A z (Pi.single b 1) * j z b + ε * ∑ b, η z (Pi.single b 1) * j z b := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
  simp only [potentialDensity, hF, fieldPairing_add_smul, hcross, hsrc]
  ring

theorem contDiffOn_potentialField (hA : ContDiffOn ℝ ∞ A U) (a b : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => potentialField A z a b) U := by
  have h (v w : MinkowskiModel d) : ContDiffOn ℝ ∞ (fun z => fderiv ℝ (fun y => A y v) z w) U :=
    ((hA.clm_apply contDiffOn_const).fderiv_of_isOpen U.isOpen (m := ∞) (by simp)).clm_apply
      contDiffOn_const
  simp only [potentialField, Matrix.of_apply]
  exact (h _ _).sub (h _ _)

theorem contDiffOn_fieldPairing {F G : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hF : ∀ a b, ContDiffOn ℝ ∞ (fun z => F z a b) U)
    (hG : ∀ a b, ContDiffOn ℝ ∞ (fun z => G z a b) U) :
    ContDiffOn ℝ ∞ (g.fieldPairing F G) U := by
  unfold fieldPairing
  exact ContDiffOn.sum fun a _ => ContDiffOn.sum fun b _ => ContDiffOn.sum fun c _ =>
    ContDiffOn.sum fun e _ => ((g.contDiffOn_coefficient_inv a c).mul
      (g.contDiffOn_coefficient_inv b e)).mul ((hF a b).mul (hG c e))

theorem contDiffOn_raisedField {F : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hF : ∀ a b, ContDiffOn ℝ ∞ (fun z => F z a b) U) (a b : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => g.raisedField F z a b) U := by
  unfold raisedField
  exact ContDiffOn.sum fun c _ => ContDiffOn.sum fun e _ =>
    ((g.contDiffOn_coefficient_inv a c).mul (g.contDiffOn_coefficient_inv b e)).mul (hF c e)

/-- The pairing with an antisymmetric field: `⟨F, dη⟩ = 2 F^{ce} ∂_c η_e`. -/
theorem fieldPairing_potentialField {z : MinkowskiModel d} (hz : z ∈ U) :
    g.fieldPairing (potentialField A) (potentialField η) z =
      2 * ∑ c, ∑ e, g.raisedField (potentialField A) z c e *
        fderiv ℝ (fun w => η w (Pi.single e 1)) z (Pi.single c 1) := by
  have hAs (e₁ e₂ : Fin (d + 1)) : (g.coefficient z)⁻¹ e₁ e₂ = (g.coefficient z)⁻¹ e₂ e₁ :=
    g.coefficient_inv_symmetric hz e₁ e₂
  have hraise : g.fieldPairing (potentialField A) (potentialField η) z =
      ∑ c, ∑ e, g.raisedField (potentialField A) z c e * potentialField η z c e := by
    unfold fieldPairing raisedField
    simp only [Finset.sum_mul]
    rw [sum4_swap_pairs]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        rw [hAs a c, hAs b e]
        ring
  have hanti (c e : Fin (d + 1)) : g.raisedField (potentialField A) z c e =
      -g.raisedField (potentialField A) z e c := by
    unfold raisedField
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => by
      rw [potentialField_antisymm A z b a]
      ring
  rw [hraise]
  simp only [potentialField, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib]
  have hswap : ∑ c, ∑ e, g.raisedField (potentialField A) z c e *
      fderiv ℝ (fun w => η w (Pi.single c 1)) z (Pi.single e 1) =
      -∑ c, ∑ e, g.raisedField (potentialField A) z c e *
        fderiv ℝ (fun w => η w (Pi.single e 1)) z (Pi.single c 1) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun c _ => by
      rw [hanti c e]
      ring
  rw [hswap]
  ring

theorem contDiffOn_density_raisedField (hA : ContDiffOn ℝ ∞ A U) (a b : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun w => densityOf g.coefficient w * g.raisedField (potentialField A) w a b)
      U :=
  contDiffOn_densityOf.mul (contDiffOn_raisedField (contDiffOn_potentialField hA) a b)

theorem continuousOn_potentialEuler (hA : ContDiffOn ℝ ∞ A U)
    {j : MinkowskiModel d → Fin (d + 1) → ℝ} (hj : ∀ b, ContinuousOn (fun z => j z b) U)
    (b : Fin (d + 1)) : ContinuousOn (fun z => g.potentialEuler j A z b) U := by
  unfold potentialEuler
  exact (continuousOn_finsetSum _ fun a _ =>
    (((contDiffOn_density_raisedField hA a b).fderiv_of_isOpen U.isOpen (m := ∞)
      (by simp)).clm_apply contDiffOn_const).continuousOn).sub
    (contDiffOn_densityOf.continuousOn.mul (hj b))

/-- **The first variation of the action of a potential**:
`d/dε (S[A + εη] − S[A]) = ∫ η_b (∂_a(√|g| F^{ab}) − √|g| j^b) dx` at `ε = 0`. -/
theorem hasDerivAt_potentialAction (hA : ContDiffOn ℝ ∞ A U) (hη : ContDiff ℝ ∞ η)
    (hK : HasCompactSupport η) (hKU : tsupport η ⊆ U) {j : MinkowskiModel d → Fin (d + 1) → ℝ}
    (hj : ∀ b, ContinuousOn (fun z => j z b) U) :
    HasDerivAt (g.potentialAction j A η)
      (∑ b, ∫ x, η x (Pi.single b 1) * g.potentialEuler j A x b) 0 := by
  have hint (F : MinkowskiModel d → ℝ) (hF : ContinuousOn F U)
      (h0 : ∀ x ∉ tsupport η, F x = 0) : Integrable F :=
    integrable_of_continuousOn hK hKU hF h0
  have hηc (v : MinkowskiModel d) : ContDiff ℝ ∞ (fun z => η z v) :=
    hη.clm_apply contDiff_const
  have hdη (v w : MinkowskiModel d) : ContDiff ℝ ∞ (fun z => fderiv ℝ (fun y => η y v) z w) :=
    ((hηc v).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hFA := contDiffOn_potentialField hA
  have hFη := contDiffOn_potentialField (U := U) hη.contDiffOn
  have hG0 (x : MinkowskiModel d) (hx : x ∉ tsupport η) :
      g.fieldPairing (potentialField A) (potentialField η) x = 0 := by
    simp [fieldPairing, potentialField_of_notMem hx]
  have hGG0 (x : MinkowskiModel d) (hx : x ∉ tsupport η) :
      g.fieldPairing (potentialField η) (potentialField η) x = 0 := by
    simp [fieldPairing, potentialField_of_notMem hx]
  set f₁ : MinkowskiModel d → ℝ := fun z =>
    (-(g.fieldPairing (potentialField A) (potentialField η) z / 2) -
      ∑ b, η z (Pi.single b 1) * j z b) * densityOf g.coefficient z with hf₁
  set f₂ : MinkowskiModel d → ℝ := fun z =>
    g.fieldPairing (potentialField η) (potentialField η) z / 4 * densityOf g.coefficient z
    with hf₂
  have hI₁ : Integrable f₁ := hint f₁
    ((((contDiffOn_fieldPairing hFA hFη).continuousOn.div_const 2).neg.sub
      (continuousOn_finsetSum _ fun b _ => (hηc _).continuous.continuousOn.mul (hj b))).mul
        contDiffOn_densityOf.continuousOn)
    fun x hx => by simp [f₁, hG0 x hx, image_eq_zero_of_notMem_tsupport hx]
  have hI₂ : Integrable f₂ := hint f₂
    (((contDiffOn_fieldPairing hFη hFη).continuousOn.div_const 4).mul
      contDiffOn_densityOf.continuousOn)
    fun x hx => by simp [f₂, hGG0 x hx]
  have hact : g.potentialAction j A η = fun ε => (ε * ∫ x, f₁ x) - ε ^ 2 * ∫ x, f₂ x := by
    funext ε
    unfold potentialAction
    rw [integral_congr_ae (Filter.Eventually.of_forall fun x =>
      potentialDensity_sub hA hη hKU j ε x)]
    rw [show (fun x => (ε * (-(g.fieldPairing (potentialField A) (potentialField η) x / 2) -
        ∑ b, η x (Pi.single b 1) * j x b) - ε ^ 2 *
          (g.fieldPairing (potentialField η) (potentialField η) x / 4)) *
            densityOf g.coefficient x) = fun x => ε * f₁ x - ε ^ 2 * f₂ x from
      funext fun x => by simp only [hf₁, hf₂]; ring,
      integral_sub (hI₁.const_mul ε) (hI₂.const_mul _), integral_const_mul, integral_const_mul]
  rw [hact]
  have hd : HasDerivAt (fun ε : ℝ => (ε * ∫ x, f₁ x) - ε ^ 2 * ∫ x, f₂ x)
      (1 * (∫ x, f₁ x) - ((2 : ℕ) * (0 : ℝ) ^ (2 - 1)) * ∫ x, f₂ x) 0 :=
    ((hasDerivAt_id (0 : ℝ)).mul_const (∫ x, f₁ x)).sub
      ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (∫ x, f₂ x))
  refine hd.congr_deriv ?_
  norm_num
  -- integration by parts
  set R : Fin (d + 1) → Fin (d + 1) → MinkowskiModel d → ℝ := fun c e w =>
    densityOf g.coefficient w * g.raisedField (potentialField A) w c e with hR
  have hRc (c e : Fin (d + 1)) : ContDiffOn ℝ ∞ (R c e) U := contDiffOn_density_raisedField hA c e
  have hpt (x : MinkowskiModel d) : f₁ x = ∑ e, (-∑ c, R c e x *
      fderiv ℝ (fun w => η w (Pi.single e 1)) x (Pi.single c 1) -
        η x (Pi.single e 1) * j x e * densityOf g.coefficient x) := by
    by_cases hx : x ∈ U
    · rw [hf₁]
      dsimp only
      rw [fieldPairing_potentialField hx, Finset.sum_sub_distrib]
      have h1 : ∑ e, -∑ c, R c e x * fderiv ℝ (fun w => η w (Pi.single e 1)) x (Pi.single c 1) =
          -(∑ c, ∑ e, g.raisedField (potentialField A) x c e *
            fderiv ℝ (fun w => η w (Pi.single e 1)) x (Pi.single c 1)) *
            densityOf g.coefficient x := by
        rw [Finset.sum_neg_distrib, neg_mul, Finset.sum_mul, Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun c _ => by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun e _ => by simp only [hR]; ring
      have h2 : ∑ e, η x (Pi.single e 1) * j x e * densityOf g.coefficient x =
          (∑ b, η x (Pi.single b 1) * j x b) * densityOf g.coefficient x := by
        rw [Finset.sum_mul]
      rw [h1, h2]
      ring
    · have hxK : x ∉ tsupport η := fun h' => hx (hKU h')
      simp [hf₁, hG0 x hxK, image_eq_zero_of_notMem_tsupport hxK,
        (component_eventually_zero hxK _).fderiv_eq]
  have hdR (c e : Fin (d + 1)) : ContinuousOn (fun x => fderiv ℝ (R c e) x (Pi.single c 1)) U :=
    (((hRc c e).fderiv_of_isOpen U.isOpen (m := ∞) (by simp)).clm_apply
      contDiffOn_const).continuousOn
  have hz1 (x : MinkowskiModel d) (hx : x ∉ tsupport η) (v w : MinkowskiModel d) :
      fderiv ℝ (fun y => η y v) x w = 0 := by
    rw [(component_eventually_zero hx v).fderiv_eq]
    simp
  have hIa (c e : Fin (d + 1)) : Integrable fun x =>
      R c e x * fderiv ℝ (fun w => η w (Pi.single e 1)) x (Pi.single c 1) :=
    hint _ ((hRc c e).continuousOn.mul (hdη _ _).continuous.continuousOn) fun x hx => by
      simp [hz1 x hx]
  have hIb (e : Fin (d + 1)) : Integrable fun x =>
      η x (Pi.single e 1) * j x e * densityOf g.coefficient x :=
    hint _ (((hηc _).continuous.continuousOn.mul (hj e)).mul contDiffOn_densityOf.continuousOn)
      fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx]
  have hIc (c e : Fin (d + 1)) : Integrable fun x =>
      fderiv ℝ (R c e) x (Pi.single c 1) * η x (Pi.single e 1) :=
    hint _ ((hdR c e).mul (hηc _).continuous.continuousOn) fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport hx]
  have htsc (v : MinkowskiModel d) : tsupport (fun w => η w v) ⊆ tsupport η :=
    closure_mono fun w hw h0 => hw (by simp [h0])
  have hibp (c e : Fin (d + 1)) : ∫ x, R c e x *
      fderiv ℝ (fun w => η w (Pi.single e 1)) x (Pi.single c 1) =
      -∫ x, fderiv ℝ (R c e) x (Pi.single c 1) * η x (Pi.single e 1) :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hIc c e) (hIa c e)
      (hint _ ((hRc c e).continuousOn.mul (hηc _).continuous.continuousOn) fun x hx => by
        simp [image_eq_zero_of_notMem_tsupport hx])
      (fun x hx => ((hRc c e).contDiffAt (U.isOpen.mem_nhds (hKU (htsc _ hx)))).differentiableAt
        (by simp))
      (fun x _ => ((hηc _).differentiable (by simp)) x)
  have hneg' (e : Fin (d + 1)) : Integrable fun x => -∑ c, R c e x *
      fderiv ℝ (fun w => η w (Pi.single e 1)) x (Pi.single c 1) :=
    (integrable_finsetSum _ fun c _ => hIa c e).neg
  have he (e : Fin (d + 1)) : ∫ x, (-∑ c, R c e x *
      fderiv ℝ (fun w => η w (Pi.single e 1)) x (Pi.single c 1) -
        η x (Pi.single e 1) * j x e * densityOf g.coefficient x) =
      ∫ x, η x (Pi.single e 1) * g.potentialEuler j A x e := by
    have hS : Integrable fun x => ∑ c, R c e x *
        fderiv ℝ (fun w => η w (Pi.single e 1)) x (Pi.single c 1) :=
      integrable_finsetSum _ fun c _ => hIa c e
    have hneg : Integrable fun x => -∑ c, R c e x *
        fderiv ℝ (fun w => η w (Pi.single e 1)) x (Pi.single c 1) := hS.neg
    have hS3 : Integrable fun x => ∑ c, fderiv ℝ (R c e) x (Pi.single c 1) *
        η x (Pi.single e 1) := integrable_finsetSum _ fun c _ => hIc c e
    rw [integral_sub hneg (hIb e), integral_neg, integral_finsetSum _ fun c _ => hIa c e]
    simp only [hibp, Finset.sum_neg_distrib, neg_neg]
    rw [← integral_finsetSum _ fun c _ => hIc c e, ← integral_sub hS3 (hIb e)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [potentialEuler, hR]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    · ring
  have hsub (e : Fin (d + 1)) : Integrable fun x => -∑ c, R c e x *
      fderiv ℝ (fun w => η w (Pi.single e 1)) x (Pi.single c 1) -
        η x (Pi.single e 1) * j x e * densityOf g.coefficient x := (hneg' e).sub (hIb e)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finsetSum _ fun e _ => hsub e]
  exact Finset.sum_congr rfl fun e _ => he e

/-- **The Maxwell equations from the action.** The action of a potential is stationary under
every smooth variation with compact support in `U` if and only if
`∂_a(√|g| F^{ab}) = √|g| j^b` on `U`. -/
theorem isPotentialStationary_iff (hA : ContDiffOn ℝ ∞ A U)
    {j : MinkowskiModel d → Fin (d + 1) → ℝ} (hj : ∀ b, ContinuousOn (fun z => j z b) U) :
    (∀ η : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ U → HasDerivAt (g.potentialAction j A η) 0 0) ↔
      ∀ z ∈ U, ∀ b, g.potentialEuler j A z b = 0 := by
  constructor
  · intro hst z hz b
    have hfc := continuousOn_potentialEuler (g := g) hA hj b
    have htest : ∀ φ : MinkowskiModel d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ U → ∫ x, φ x • g.potentialEuler j A x b = 0 := by
      intro φ hφ hφK hφU
      set η : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ := fun x =>
        φ x • (ContinuousLinearMap.proj b : MinkowskiModel d →L[ℝ] ℝ) with hη
      have hηv (x v : MinkowskiModel d) : η x v = φ x * v b := by
        simp [hη, smul_eq_mul]
      have hηs : Function.support η ⊆ Function.support φ := fun x hx h0 => hx (by
        ext v
        simp [hηv, h0])
      have hηc : ContDiff ℝ ∞ η := by
        refine contDiff_clm_apply_iff.mpr fun v => ?_
        simp only [hηv]
        exact hφ.mul contDiff_const
      have hηK : HasCompactSupport η := hφK.mono' (hηs.trans (subset_tsupport φ))
      have hηU : tsupport η ⊆ U := (closure_mono hηs).trans hφU
      have h0 := (hasDerivAt_potentialAction hA hηc hηK hηU hj).unique (hst η hηc hηK hηU)
      simp only [hηv, Pi.single_apply] at h0
      simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul] at h0
      rw [Finset.sum_eq_single b] at h0
      · simpa [smul_eq_mul] using h0
      · intro e _ he
        simp [Ne.symm he]
      · simp
    have hae := U.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hfc.locallyIntegrableOn U.isOpen.measurableSet) htest
    exact Measure.eqOn_open_of_ae_eq (μ := volume)
      ((ae_restrict_iff' U.isOpen.measurableSet).mpr hae) U.isOpen hfc continuousOn_const hz
  · intro h0 η hη hK hKU
    have hd := hasDerivAt_potentialAction (g := g) hA hη hK hKU hj
    have hz : ∀ b, (fun x => η x (Pi.single b 1) * g.potentialEuler j A x b) = fun _ => 0 := by
      intro b
      funext x
      by_cases hx : x ∈ U
      · rw [h0 x hx b, mul_zero]
      · simp [image_eq_zero_of_notMem_tsupport fun h' => hx (hKU h')]
    simp only [hz, integral_zero, Finset.sum_const_zero] at hd
    exact hd

end CoordinateMetric

/-! ### Two-forms on the co-ordinate fields -/

section TwoForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

theorem alternatingTwo_swap (f : V [⋀^Fin 2]→L[ℝ] ℝ) (v w : V) : f ![v, w] = -f ![w, v] := by
  have h := f.toAlternatingMap.map_swap ![w, v] (show (0 : Fin 2) ≠ 1 by decide)
  have hv : ![w, v] ∘ Equiv.swap (0 : Fin 2) 1 = ![v, w] := by
    ext i
    fin_cases i <;> rfl
  rw [hv] at h
  exact h

theorem alternatingTwo_sum_left (f : V [⋀^Fin 2]→L[ℝ] ℝ) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (u : ι → V) (y : V) :
    f ![∑ a ∈ s, c a • u a, y] = ∑ a ∈ s, c a * f ![u a, y] := by
  let L : V →ₗ[ℝ] ℝ :=
    { toFun := fun x => f ![x, y]
      map_add' := fun x x' => f.vecCons_add _ x x'
      map_smul' := fun r x => f.vecCons_smul _ r x }
  have h := map_sum L (fun a => c a • u a) s
  simp only [map_smul, smul_eq_mul] at h
  exact h

theorem alternatingTwo_sum_right (f : V [⋀^Fin 2]→L[ℝ] ℝ) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (u : ι → V) (x : V) :
    f ![x, ∑ b ∈ s, c b • u b] = ∑ b ∈ s, c b * f ![x, u b] := by
  rw [alternatingTwo_swap, alternatingTwo_sum_left, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun b _ => by rw [alternatingTwo_swap f x (u b)]; ring

end TwoForm

namespace CoordinateMetric

variable {U : Opens (MinkowskiModel d)} {g : CoordinateMetric σ d U}
  {A : MinkowskiModel d → MinkowskiModel d →L[ℝ] ℝ}

/-- The raised components of a native two-form in the inclusion chart. -/
theorem raisedTwoFormComponent_eq
    (F : DifferentialForm.SmoothForm 𝓘(ℝ, MinkowskiModel d) U 2) (x y : U) (i k : Fin (d + 1)) :
    g.toLorentzMetric.raisedTwoFormComponent F (physicalChart x) y i k =
      ∑ a, ∑ b, (g.coefficient y)⁻¹ a i * (g.coefficient y)⁻¹ b k *
        F y ![Pi.single a 1, Pi.single b 1] := by
  have he := physicalChart_mem x
  have hy : y ∈ (physicalChart x).source := by simp
  rw [raisedTwoFormComponent, g.toLorentzMetric.chartRaisedCovector_eq_sum he hy,
    g.toLorentzMetric.chartRaisedCovector_eq_sum he hy, alternatingTwo_sum_left]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [alternatingTwo_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [chartInverse_physicalChart, chartInverse_physicalChart]
  have ha : (chartField (physicalChart x) (Pi.single a 1) y : MinkowskiModel d) = Pi.single a 1 :=
    physicalChart_chartField x y _
  have hb : (chartField (physicalChart x) (Pi.single b 1) y : MinkowskiModel d) = Pi.single b 1 :=
    physicalChart_chartField x y _
  rw [ha, hb]
  ring

/-- **The native divergence of a two-form with the components of `dA`.** -/
theorem twoFormDivergence_component (hA : ContDiffOn ℝ ∞ A U)
    (F : DifferentialForm.SmoothForm 𝓘(ℝ, MinkowskiModel d) U 2)
    (hF : ∀ (y : U) (a b : Fin (d + 1)), F y ![Pi.single a 1, Pi.single b 1] =
      potentialField A y a b) (x : U) (b : Fin (d + 1)) :
    (g.toLorentzMetric.twoFormDivergence F x : MinkowskiModel d) b =
      (densityOf g.coefficient x)⁻¹ * ∑ a, fderiv ℝ (fun w => densityOf g.coefficient w *
        g.raisedField (potentialField A) w a b) x (Pi.single a 1) := by
  have he := physicalChart_mem x
  have hx : x ∈ (physicalChart x).source := by simp
  have h := g.toLorentzMetric.twoFormDivergence_density F he hx b
  rw [physicalChart_tangentMap] at h
  rw [h, toLorentzMetric_chartDensity]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  have hfun : (fun y : U => g.toLorentzMetric.chartDensity (physicalChart x) y *
      g.toLorentzMetric.raisedTwoFormComponent F (physicalChart x) y a b) =
      fun y : U => densityOf g.coefficient y * g.raisedField (potentialField A) y a b := by
    funext y
    rw [toLorentzMetric_chartDensity, raisedTwoFormComponent_eq, raisedField]
    congr 1
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => by
      rw [hF y c e, g.coefficient_inv_symmetric y.property c a,
        g.coefficient_inv_symmetric y.property e b]
  rw [hfun, mvfderiv_val x x (((contDiffOn_density_raisedField hA a b).contDiffAt
    (U.isOpen.mem_nhds x.property)).differentiableAt (by simp))]

/-- **The Euler–Lagrange equation of the potential is the native Maxwell equation**
`∇_a F^{ab} = J^b`, for a native two-form `F` with the components of `dA` and a native vector field
`J` with the components `j`. -/
theorem twoFormDivergence_eq_iff (hA : ContDiffOn ℝ ∞ A U)
    (F : DifferentialForm.SmoothForm 𝓘(ℝ, MinkowskiModel d) U 2)
    (hF : ∀ (y : U) (a b : Fin (d + 1)), F y ![Pi.single a 1, Pi.single b 1] =
      potentialField A y a b)
    (J : ∀ y : U, TangentSpace 𝓘(ℝ, MinkowskiModel d) y)
    {j : MinkowskiModel d → Fin (d + 1) → ℝ}
    (hJ : ∀ (y : U) b, (J y : MinkowskiModel d) b = j y b) :
    g.toLorentzMetric.twoFormDivergence F = J ↔ ∀ z ∈ U, ∀ b, g.potentialEuler j A z b = 0 := by
  have hpos (y : U) := densityOf_pos (g := g) y.property
  constructor
  · intro h z hz b
    have h1 := twoFormDivergence_component (g := g) hA F hF ⟨z, hz⟩ b
    rw [h, hJ] at h1
    rw [potentialEuler]
    have h2 := congrArg (fun r => densityOf g.coefficient z * r) h1
    simp only at h2
    rw [← mul_assoc, mul_inv_cancel₀ (hpos ⟨z, hz⟩).ne', one_mul] at h2
    rw [← h2]
    ring
  · intro h
    funext y
    funext b
    rw [twoFormDivergence_component (g := g) hA F hF y b, hJ]
    have h1 := h y y.property b
    rw [potentialEuler, sub_eq_zero] at h1
    rw [h1, ← mul_assoc, inv_mul_cancel₀ (hpos y).ne', one_mul]

end CoordinateMetric

end ProjectAinos.SmoothGeometry
