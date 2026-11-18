/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.EinsteinEquation
public import ProjectAinos.SmoothGeometry.Lorentzian.ChartDerivatives
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateTangent

/-!
# Orthonormal frames and the tetrad form of the curvature

Landau–Lifshitz, §98. An orthonormal frame of a Lorentz metric `g` on an open set `W` is a
family of smooth vector fields `E_a` with `g(E_a, E_b) = η_{ab}` on `W` (`OrthonormalFrame`);
`η_{aa} = lorentzSign σ a` and `η_{ab} = 0` for `a ≠ b`.

* `sum_coord_smul`, `form_eq_sum`: every tangent vector is `Σ_a η_{aa} g(v, E_a) E_a`, and
  `g(u, w) = Σ_a η_{aa} g(u, E_a) g(w, E_a)`.
* `rotation_antisymm`, `commutator_eq`, `rotation_eq`: the rotation coefficients
  `γ_{abc} = g(∇_{E_c} E_a, E_b)` are antisymmetric in `a, b`, the commutator coefficients
  `λ_{abc} = g(E_a, [E_b, E_c])` are `γ_{abc} − γ_{acb}`, and
  `γ_{abc} = ½ (λ_{abc} + λ_{bca} − λ_{cab})`.
* `curvatureComponent_eq`: **the curvature in the frame** (Cartan's second structure equation in
  components), `R_{abck} = E_c(γ_{bak}) − E_k(γ_{bac}) −
  Σ_f η_{ff} (γ_{bfk} γ_{afc} − γ_{bfc} γ_{afk} + λ_{fck} γ_{baf})` with
  `R_{abck} = g(R(E_c, E_k) E_b, E_a)` and the curvature convention of `curvature`.
* `ricci_field`, `scalarCurvature_eq`, `bilinear_ext`: the Ricci tensor is
  `Ric(E_b, E_k) = Σ_i η_{ii} R_{ikib}`, the scalar curvature is `Σ_i η_{ii} Ric(E_i, E_i)`, and
  a bilinear form is determined by its frame components.
* `ricci_field_eq`, `einstein_eq_iff`, `satisfiesEinstein_iff_frames`: **the tetrad form of the
  Einstein equations**, with the Ricci tensor in the rotation coefficients and their frame
  derivatives; the equations hold if and only if their frame components hold in the frames of a
  cover.
* `transition_orthonormal`: the transition matrix between two orthonormal frames is a Lorentz
  matrix.
* `CoordinateMetric.minkowskiFrame`: the coordinate fields are an orthonormal frame of the
  Minkowski coordinate metric.
-/

@[expose] public section

noncomputable section

open Bundle FiberBundle VectorField Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

namespace LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "E" => MinkowskiModel d
local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

/-- A smooth frame on an open set `W` that is orthonormal for `g`: `g(E_a, E_b) = η_{ab}`. -/
structure OrthonormalFrame (g : LorentzMetric σ d M) (W : Set M) where
  /-- The vector fields of the frame. -/
  field : Fin (d + 1) → ∀ x : M, TangentSpace 𝓘(ℝ, MinkowskiModel d) x
  /-- The set of the frame is open. -/
  isOpen : IsOpen W
  /-- The fields are smooth on `W`. -/
  smooth : ∀ a, ∀ x ∈ W, ContMDiffAt 𝓘(ℝ, MinkowskiModel d)
    (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) ∞ (T% (field a)) x
  /-- The frame is orthonormal on `W`. -/
  orthonormal : ∀ x ∈ W, ∀ a b, g.form x (field a x) (field b x) =
    if a = b then lorentzSign σ a else 0

namespace OrthonormalFrame

variable {g : LorentzMetric σ d M} {W : Set M} (F : OrthonormalFrame g W) {x : M}

local instance (x : M) : FiniteDimensional ℝ (TM x) :=
  inferInstanceAs (FiniteDimensional ℝ (MinkowskiModel d))

theorem mdiff (hx : x ∈ W) (a : Fin (d + 1)) :
    MDifferentiableAt I ((I).prod I) (T% (F.field a)) x :=
  (F.smooth a x hx).mdifferentiableAt (by simp)

/-- The frame coordinates `v ↦ (η_{aa} g(v, E_a))_a` at a point. -/
def coord (x : M) : TM x →L[ℝ] E :=
  ContinuousLinearMap.pi fun a => lorentzSign σ a • (g.form x).flip (F.field a x)

@[simp] theorem coord_apply (x : M) (v : TM x) (a : Fin (d + 1)) :
    F.coord x v a = lorentzSign σ a * g.form x v (F.field a x) := by
  simp [coord]

/-- The vector `Σ_a c_a E_a` of frame coordinates `c`. -/
def combine (x : M) : E →L[ℝ] TM x :=
  ∑ a, (ContinuousLinearMap.proj a : E →L[ℝ] ℝ).smulRight (F.field a x)

theorem combine_apply (x : M) (c : E) : F.combine x c = ∑ a, c a • F.field a x := by
  simp [combine]

theorem coord_combine (hx : x ∈ W) (c : E) : F.coord x (F.combine x c) = c := by
  funext b
  rw [coord_apply, combine_apply, map_sum, _root_.sum_apply]
  simp only [map_smul, smul_apply, smul_eq_mul, F.orthonormal x hx]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← mul_assoc, mul_comm (lorentzSign σ b) (c b), mul_assoc, lorentzSign_sq, mul_one]

/-- **Expansion in an orthonormal frame**: `v = Σ_a η_{aa} g(v, E_a) E_a`. -/
theorem sum_coord_smul (hx : x ∈ W) (v : TM x) : ∑ a, F.coord x v a • F.field a x = v := by
  have hinj : Function.Injective (F.combine x) := fun c c' h => by
    rw [← F.coord_combine hx c, ← F.coord_combine hx c', h]
  have hsurj : Function.Surjective (F.combine x).toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj
  obtain ⟨c, rfl⟩ := hsurj v
  change ∑ a, F.coord x (F.combine x c) a • F.field a x = F.combine x c
  rw [F.coord_combine hx, combine_apply]

theorem combine_coord (hx : x ∈ W) (v : TM x) : F.combine x (F.coord x v) = v := by
  rw [combine_apply, F.sum_coord_smul hx]

/-- The frame coordinates as an equivalence of the tangent space with the model. -/
def coordEquiv (hx : x ∈ W) : TM x ≃L[ℝ] E :=
  ContinuousLinearEquiv.equivOfInverse (F.coord x) (F.combine x) (F.combine_coord hx)
    (F.coord_combine hx)

@[simp] theorem coordEquiv_apply (hx : x ∈ W) (v : TM x) : F.coordEquiv hx v = F.coord x v :=
  rfl

theorem coordEquiv_symm_single (hx : x ∈ W) (a : Fin (d + 1)) :
    (F.coordEquiv hx).symm (Pi.single a 1) = F.field a x := by
  change F.combine x (Pi.single a 1) = _
  rw [combine_apply]
  simp [Pi.single_apply, ite_smul]

/-- The metric in an orthonormal frame: `g(u, w) = Σ_a η_{aa} g(u, E_a) g(w, E_a)`. -/
theorem form_eq_sum (hx : x ∈ W) (u w : TM x) :
    g.form x u w = ∑ a, lorentzSign σ a * g.form x u (F.field a x) * g.form x w (F.field a x) := by
  conv_lhs => rw [← F.sum_coord_smul hx u]
  rw [map_sum, _root_.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, smul_apply, smul_eq_mul, coord_apply, g.symmetric x (F.field a x)]

/-- **A bilinear form is determined by its frame components.** -/
theorem bilinear_ext (hx : x ∈ W) {B B' : TM x →L[ℝ] TM x →L[ℝ] ℝ}
    (h : ∀ a b, B (F.field a x) (F.field b x) = B' (F.field a x) (F.field b x)) : B = B' := by
  ext u v
  rw [← F.sum_coord_smul hx u, ← F.sum_coord_smul hx v]
  simp only [map_sum, map_smul, _root_.sum_apply, smul_apply, h]

/-! ### Rotation and commutator coefficients -/

/-- The rotation coefficients `γ_{abc} = g(∇_{E_c} E_a, E_b)`. -/
def rotation (a b c : Fin (d + 1)) (x : M) : ℝ :=
  g.form x (g.covariantField (F.field c) (F.field a) x) (F.field b x)

/-- The commutator coefficients `λ_{abc} = g(E_a, [E_b, E_c])`. -/
def commutator (a b c : Fin (d + 1)) (x : M) : ℝ :=
  g.form x (F.field a x) (mlieBracket I (F.field b) (F.field c) x)

/-- The rotation coefficients are antisymmetric in their first two indices. -/
theorem rotation_antisymm (hx : x ∈ W) (a b c : Fin (d + 1)) :
    F.rotation a b c x = -F.rotation b a c x := by
  have hm := g.leviCivita_metricCompatible (F.field c x) (F.mdiff hx a) (F.mdiff hx b)
  have hconst : (fun y => g.form y (F.field a y) (F.field b y)) =ᶠ[𝓝 x]
      fun _ => if a = b then lorentzSign σ a else 0 :=
    eventually_of_mem (F.isOpen.mem_nhds hx) fun y hy => F.orthonormal y hy a b
  rw [mvfderiv_congr_of_eventuallyEq (d := d) hconst, mvfderiv_const, zero_apply] at hm
  unfold rotation covariantField
  rw [g.symmetric x (g.leviCivita (F.field b) x (F.field c x))]
  linarith

/-- The commutator coefficients from the rotation coefficients: `λ_{abc} = γ_{abc} − γ_{acb}`. -/
theorem commutator_eq (hx : x ∈ W) (a b c : Fin (d + 1)) :
    F.commutator a b c x = F.rotation a b c x - F.rotation a c b x := by
  have ht := g.covariantField_commutator (F.mdiff hx b) (F.mdiff hx c)
  unfold commutator
  rw [← ht, map_sub, g.symmetric x (F.field a x), g.symmetric x (F.field a x)]
  change F.rotation c a b x - F.rotation b a c x = _
  rw [F.rotation_antisymm hx c a b, F.rotation_antisymm hx b a c]
  ring

/-- The rotation coefficients from the commutator coefficients:
`γ_{abc} = ½ (λ_{abc} + λ_{bca} − λ_{cab})`. -/
theorem rotation_eq (hx : x ∈ W) (a b c : Fin (d + 1)) :
    F.rotation a b c x =
      (F.commutator a b c x + F.commutator b c a x - F.commutator c a b x) / 2 := by
  rw [F.commutator_eq hx, F.commutator_eq hx, F.commutator_eq hx,
    F.rotation_antisymm hx b a c, F.rotation_antisymm hx c a b, F.rotation_antisymm hx c b a]
  ring

/-! ### Curvature in the frame -/

theorem coord_field (hx : x ∈ W) (b : Fin (d + 1)) : F.coord x (F.field b x) = Pi.single b 1 := by
  rw [← F.coordEquiv_symm_single hx b]
  exact F.coord_combine hx _

/-- The frame components `R_{abck} = g(R(E_c, E_k) E_b, E_a)` of the curvature. -/
def curvatureComponent (a b c k : Fin (d + 1)) (x : M) : ℝ :=
  g.form x (g.curvature x (F.field c x) (F.field k x) (F.field b x)) (F.field a x)

theorem form_covariantField_covariantField (hx : x ∈ W) (a b c k : Fin (d + 1)) :
    g.form x (g.covariantField (F.field c) (g.covariantField (F.field k) (F.field b)) x)
        (F.field a x) =
      mvfderiv I (F.rotation b a k) x (F.field c x) -
        ∑ f, lorentzSign σ f * F.rotation b f k x * F.rotation a f c x := by
  have hY : MDifferentiableAt I ((I).prod I)
      (T% (g.covariantField (F.field k) (F.field b))) x :=
    (g.contMDiffAt_covariantField (n := 1) ((F.smooth k x hx).of_le (by simp))
      ((F.smooth b x hx).of_le (by simp))).mdifferentiableAt one_ne_zero
  have hm := g.leviCivita_metricCompatible (F.field c x) hY (F.mdiff hx a)
  have hsum := F.form_eq_sum hx (g.covariantField (F.field k) (F.field b) x)
    (g.leviCivita (F.field a) x (F.field c x))
  change mvfderiv I (F.rotation b a k) x (F.field c x) = _ + _ at hm
  rw [hm, hsum]
  simp only [rotation, covariantField, g.symmetric x (g.leviCivita (F.field a) x (F.field c x))]
  ring

theorem form_covariantField_bracket (hx : x ∈ W) (a b c k : Fin (d + 1)) :
    g.form x (g.covariantField (mlieBracket I (F.field c) (F.field k)) (F.field b) x)
        (F.field a x) =
      ∑ f, lorentzSign σ f * F.commutator f c k x * F.rotation b a f x := by
  have hexp := F.sum_coord_smul hx (mlieBracket I (F.field c) (F.field k) x)
  unfold covariantField
  conv_lhs => rw [← hexp]
  rw [map_sum, map_sum, _root_.sum_apply]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [map_smul, map_smul, smul_apply, smul_eq_mul, coord_apply]
  simp only [commutator, rotation, covariantField, g.symmetric x (F.field f x)]

/-- **The curvature in an orthonormal frame** (Cartan's second structure equation in
components): `R_{abck} = E_c(γ_{bak}) − E_k(γ_{bac}) −
Σ_f η_{ff} (γ_{bfk} γ_{afc} − γ_{bfc} γ_{afk} + λ_{fck} γ_{baf})`. -/
theorem curvatureComponent_eq (hx : x ∈ W) (a b c k : Fin (d + 1)) :
    F.curvatureComponent a b c k x =
      mvfderiv I (F.rotation b a k) x (F.field c x) -
        mvfderiv I (F.rotation b a c) x (F.field k x) -
        ∑ f, lorentzSign σ f * (F.rotation b f k x * F.rotation a f c x -
          F.rotation b f c x * F.rotation a f k x + F.commutator f c k x * F.rotation b a f x) := by
  have hR := g.curvature_apply ((F.smooth c x hx).of_le (by simp))
    ((F.smooth k x hx).of_le (by simp)) ((F.smooth b x hx).of_le (by simp))
  unfold curvatureComponent
  rw [hR, curvatureField, map_sub, map_sub, sub_apply, sub_apply,
    F.form_covariantField_covariantField hx, F.form_covariantField_covariantField hx,
    F.form_covariantField_bracket hx]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← mul_assoc]
  ring

/-! ### Ricci and Einstein tensors in the frame -/

/-- The Ricci tensor in an orthonormal frame: `Ric(u, v) = Σ_i η_{ii} g(R(E_i, u) v, E_i)`. -/
theorem ricci_eq_sum_frame (hx : x ∈ W) (u v : TM x) :
    g.ricci x u v =
      ∑ i, lorentzSign σ i * g.form x (g.curvature x (F.field i x) u v) (F.field i x) := by
  rw [g.ricci_eq_sum x (F.coordEquiv hx)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [F.coordEquiv_symm_single hx, coordEquiv_apply, coord_apply]

/-- The frame components of the Ricci tensor: `Ric(E_b, E_k) = Σ_i η_{ii} R_{ikib}`. -/
theorem ricci_field (hx : x ∈ W) (b k : Fin (d + 1)) :
    g.ricci x (F.field b x) (F.field k x) =
      ∑ i, lorentzSign σ i * F.curvatureComponent i k i b x :=
  F.ricci_eq_sum_frame hx _ _

/-- **The Ricci tensor in the rotation coefficients**:
`Ric(E_b, E_k) = Σ_i η_{ii} (E_i(γ_{kib}) − E_b(γ_{kii}) −
Σ_f η_{ff} (γ_{kfb} γ_{ifi} − γ_{kfi} γ_{ifb} + λ_{fib} γ_{kif}))`. -/
theorem ricci_field_eq (hx : x ∈ W) (b k : Fin (d + 1)) :
    g.ricci x (F.field b x) (F.field k x) =
      ∑ i, lorentzSign σ i * (mvfderiv I (F.rotation k i b) x (F.field i x) -
        mvfderiv I (F.rotation k i i) x (F.field b x) -
        ∑ f, lorentzSign σ f * (F.rotation k f b x * F.rotation i f i x -
          F.rotation k f i x * F.rotation i f b x +
            F.commutator f i b x * F.rotation k i f x)) := by
  rw [F.ricci_field hx]
  simp only [F.curvatureComponent_eq hx]

/-- The scalar curvature in an orthonormal frame: `R = Σ_i η_{ii} Ric(E_i, E_i)`. -/
theorem scalarCurvature_eq (hx : x ∈ W) :
    g.scalarCurvature x = ∑ i, lorentzSign σ i * g.ricci x (F.field i x) (F.field i x) := by
  have hinv (i j : Fin (d + 1)) : g.inverseComponent x (F.coordEquiv hx) i j =
      lorentzSign σ j * if i = j then 1 else 0 := by
    have hcov : Tensor.coordinateCovector x (F.coordEquiv hx) j =
        g.flat x (lorentzSign σ j • F.field j x) := by
      ext v
      rw [Tensor.coordinateCovector_apply, coordEquiv_apply, coord_apply, flat_apply, map_smul,
        smul_apply, smul_eq_mul, g.symmetric x v]
    unfold inverseComponent
    rw [hcov, sharp_flat, coordEquiv_apply, map_smul, F.coord_field hx, Pi.smul_apply,
      Pi.single_apply, smul_eq_mul]
  rw [g.scalarCurvature_eq_sum x (F.coordEquiv hx)]
  simp only [F.coordEquiv_symm_single hx, hinv, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The frame components of the Einstein tensor: `G_{ab} = Ric_{ab} − ½ R η_{ab}`. -/
theorem einstein_field (hx : x ∈ W) (a b : Fin (d + 1)) :
    g.einstein x (F.field a x) (F.field b x) =
      g.ricci x (F.field a x) (F.field b x) -
        g.scalarCurvature x / 2 * if a = b then lorentzSign σ a else 0 := by
  rw [einstein_apply, F.orthonormal x hx]

/-- **The Einstein equations in an orthonormal frame**: at a point of the frame,
`G + Λ g = κ T` if and only if `G_{ab} + Λ η_{ab} = κ T_{ab}` for all frame indices. -/
theorem einstein_eq_iff (hx : x ∈ W) (κ Λ : ℝ) (T : TM x →L[ℝ] TM x →L[ℝ] ℝ) :
    g.einstein x + Λ • g.form x = κ • T ↔ ∀ a b,
      g.einstein x (F.field a x) (F.field b x) + Λ * (if a = b then lorentzSign σ a else 0) =
        κ * T (F.field a x) (F.field b x) := by
  constructor
  · intro h a b
    have h' := congrArg (fun B : TM x →L[ℝ] TM x →L[ℝ] ℝ => B (F.field a x) (F.field b x)) h
    simpa only [add_apply, smul_apply, smul_eq_mul, F.orthonormal x hx] using h'
  · intro h
    apply F.bilinear_ext hx
    intro a b
    simp only [add_apply, smul_apply, smul_eq_mul, F.orthonormal x hx]
    exact h a b

/-- **The Einstein equations in orthonormal frames**: for frames whose open sets cover `M`, the
Einstein equations hold if and only if their frame components hold in every frame. -/
theorem _root_.ProjectAinos.SmoothGeometry.LorentzMetric.satisfiesEinstein_iff_frames
    {ι : Type*} {V : ι → Set M} (G : ∀ i, OrthonormalFrame g (V i)) (hcov : ∀ x, ∃ i, x ∈ V i)
    (κ Λ : ℝ) (T : Tensor.SmoothBilinear («I» := I) (M := M)) :
    g.SatisfiesEinstein κ Λ T ↔ ∀ i, ∀ x ∈ V i, ∀ a b,
      g.einstein x ((G i).field a x) ((G i).field b x) +
          Λ * (if a = b then lorentzSign σ a else 0) =
        κ * T x ((G i).field a x) ((G i).field b x) := by
  constructor
  · intro h i x hx
    exact ((G i).einstein_eq_iff hx κ Λ (T x)).mp (h x)
  · intro h x
    obtain ⟨i, hx⟩ := hcov x
    exact ((G i).einstein_eq_iff hx κ Λ (T x)).mpr (h i x hx)

/-! ### Change of frame -/

/-- **The transition matrix between two orthonormal frames is a Lorentz matrix**: with
`Λ_{ab} = η_{aa} g(E'_b, E_a)`, `Σ_a η_{aa} Λ_{ab} Λ_{ak} = η_{bk}`. -/
theorem transition_orthonormal {W' : Set M} (F' : OrthonormalFrame g W') (hx : x ∈ W)
    (hx' : x ∈ W') (b k : Fin (d + 1)) :
    ∑ a, lorentzSign σ a * F.coord x (F'.field b x) a * F.coord x (F'.field k x) a =
      if b = k then lorentzSign σ b else 0 := by
  rw [← F'.orthonormal x hx' b k, F.form_eq_sum hx]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [coord_apply]
  linear_combination (lorentzSign σ a * g.form x (F'.field b x) (F.field a x) *
    g.form x (F'.field k x) (F.field a x)) * lorentzSign_sq σ a

end OrthonormalFrame

end LorentzMetric

namespace CoordinateMetric

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

/-- **The coordinate fields of the Minkowski coordinate metric are an orthonormal frame.** -/
def minkowskiFrame (U : Opens (MinkowskiModel d)) :
    (minkowski σ d U).toLorentzMetric.OrthonormalFrame univ where
  field a := fun _ => (Pi.single a 1 : MinkowskiModel d)
  isOpen := isOpen_univ
  smooth a x _ := by
    refine (chartField_contMDiffAt (physicalChart_mem x)
      (by simp : x ∈ (physicalChart x).source) (Pi.single a 1)).congr_of_eventuallyEq
      (Eventually.of_forall fun y => ?_)
    exact congrArg (TotalSpace.mk' (MinkowskiModel d) y) (physicalChart_chartField x y _).symm
  orthonormal x _ a b := by
    change minkowskiForm σ d (Pi.single a 1) (Pi.single b 1) = _
    rw [minkowskiForm_apply]
    by_cases h : a = b
    · subst h
      simp [Pi.single_apply]
    · simp [Pi.single_apply, h]
      intro hba
      exact absurd hba.symm h

end CoordinateMetric

end ProjectAinos.SmoothGeometry
