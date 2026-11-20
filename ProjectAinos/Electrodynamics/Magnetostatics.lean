/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Electrostatics
public import ProjectAinos.Electrodynamics.SourceCovariance
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic

/-!
# The constant magnetic field

The units have `curl B − ∂_t E = j` and `B = curl a`, so the vector potential of a static current
`j` solves `Δa = −j` in the Coulomb gauge `div a = 0` (Landau–Lifshitz, *The Classical Theory of
Fields*, §43). Space is `EuclideanSpace ℝ (Fin 3)`, `Minkowski.Space 3`, and a vector field on
space is a function `E3 → Fin 3 → ℝ`. `partial3 f i` is the derivative `∂ᵢf` along the axis `i`,
and `div3`, `curl3` are the divergence and the curl in space.

* `div3_curl3`: `div curl a = 0`, and `curl3_curl3`: `curl curl a = ∇ div a − Δa`, for a `C²`
  field.
* `vectorPotential j`: the Newton potential `aᵢ = N[jᵢ]` of each component of the current.
  `div3_vectorPotential`: a conserved current, `div j = 0`, gives the Coulomb gauge `div a = 0`;
  `laplacian_vectorPotential`: `Δa = −j`.
* `magneticField3 j = curl a`: `curl3_magneticField3` is the equation `curl B = j` and
  `div3_magneticField3` is `div B = 0`; `tendsto_magneticField3`: `B → 0` at infinity.
* `magneticField3_eq_biotSavart`: **the law of Biot and Savart**
  `B(x) = ∫ j(y) × (x − y)/(4π‖x − y‖³) dy` outside a ball that contains the support.
* `maxwell_staticVector`: on space-time the potential `A = a · dx` (`magnetostaticPotential`)
  satisfies the four equations of Maxwell with the static current `(0, j)`, and
  `excitation_staticVector` is the equation `d(−⋆F) = −ι_k vol` of the forms.
* Uniqueness: `vectorPotential_unique` (`Δa′ = −j` and `a′ → 0`), `vectorPotential_unique_of_curl`
  (`div a′ = 0`, `curl curl a′ = j` and `a′ → 0`), and `magneticField3_unique` for the field:
  a `C²` field with `div B′ = 0`, `curl B′ = j` and `B′ → 0` is `magneticField3 j`.
* The instance `ringCurrent = curl(ψ e_z)` of a bump function `ψ` is a smooth current of compact
  support with `div j = 0` (`div3_ringCurrent`), and it is not zero (`ringCurrent_ne_zero`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real
open scoped Topology Laplacian ContDiff

namespace ProjectAinos.Electrodynamics.Magnetostatics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Potential
  SmoothGeometry.DifferentialForm SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Derivatives in space -/

/-- The partial derivative `∂ᵢf` of a function on space along the axis `i`. -/
def partial3 (f : E3 → ℝ) (i : Fin 3) : E3 → ℝ :=
  fun x => fderiv ℝ f x (EuclideanSpace.single i 1)

/-- The divergence `div f = Σᵢ ∂ᵢfᵢ` of a vector field on space. -/
def div3 (f : E3 → Fin 3 → ℝ) (x : E3) : ℝ :=
  ∑ i, partial3 (fun y => f y i) i x

/-- The curl `curl f = ∇ × f` of a vector field on space. -/
def curl3 (f : E3 → Fin 3 → ℝ) (x : E3) : Fin 3 → ℝ :=
  ![partial3 (fun y => f y 2) 1 x - partial3 (fun y => f y 1) 2 x,
    partial3 (fun y => f y 0) 2 x - partial3 (fun y => f y 2) 0 x,
    partial3 (fun y => f y 1) 0 x - partial3 (fun y => f y 0) 1 x]

/-- The first component of the curl. -/
theorem curl3_apply_zero (f : E3 → Fin 3 → ℝ) (x : E3) :
    curl3 f x 0 = partial3 (fun y => f y 2) 1 x - partial3 (fun y => f y 1) 2 x :=
  rfl

/-- The second component of the curl. -/
theorem curl3_apply_one (f : E3 → Fin 3 → ℝ) (x : E3) :
    curl3 f x 1 = partial3 (fun y => f y 0) 2 x - partial3 (fun y => f y 2) 0 x :=
  rfl

/-- The third component of the curl. -/
theorem curl3_apply_two (f : E3 → Fin 3 → ℝ) (x : E3) :
    curl3 f x 2 = partial3 (fun y => f y 1) 0 x - partial3 (fun y => f y 0) 1 x :=
  rfl

/-- The Laplacian in the co-ordinates is `Σₖ ∂ₖ∂ₖ f`. -/
theorem coordLaplacian_eq_sum_partial3 (f : E3 → ℝ) (x : E3) :
    coordLaplacian f x = ∑ k, partial3 (partial3 f k) k x :=
  rfl

/-- A partial derivative of a `Cⁿ` function is `Cᵐ` when `m + 1 ≤ n`. -/
theorem contDiff_partial3 {f : E3 → ℝ} {m n : WithTop ℕ∞} (hf : ContDiff ℝ n f)
    (hmn : m + 1 ≤ n) (i : Fin 3) : ContDiff ℝ m (partial3 f i) :=
  (hf.fderiv_right hmn).clm_apply contDiff_const

/-- A partial derivative of a `C²` function is differentiable. -/
theorem differentiable_partial3 {f : E3 → ℝ} (hf : ContDiff ℝ 2 f) (i : Fin 3) :
    Differentiable ℝ (partial3 f i) :=
  (contDiff_partial3 (m := 1) hf (by norm_num) i).differentiable (by norm_num)

/-- **The second partial derivatives of a `C²` function commute**, `∂ₖ∂ₗf = ∂ₗ∂ₖf`. -/
theorem partial3_comm {f : E3 → ℝ} (hf : ContDiff ℝ 2 f) (k l : Fin 3) (x : E3) :
    partial3 (partial3 f l) k x = partial3 (partial3 f k) l x := by
  unfold partial3
  rw [fderiv_fderiv_apply hf.contDiffAt, fderiv_fderiv_apply hf.contDiffAt]
  exact hf.contDiffAt.isSymmSndFDerivAt (by simp) _ _

/-- The partial derivative of a difference. -/
theorem partial3_sub {f g : E3 → ℝ} {x : E3} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    partial3 (fun y => f y - g y) i x = partial3 f i x - partial3 g i x := by
  unfold partial3
  rw [fderiv_fun_sub hf hg]
  rfl

/-- The partial derivative vanishes outside the closed support. -/
theorem partial3_eq_zero_of_notMem_tsupport {f : E3 → ℝ} {x : E3} (hx : x ∉ tsupport f)
    (i : Fin 3) : partial3 f i x = 0 := by
  have hf : f =ᶠ[𝓝 x] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hx
  unfold partial3
  rw [hf.fderiv_eq]
  simp

/-- The partial derivatives of the components of a `C²` field on the curl. -/
theorem partial3_curl3 {a : E3 → Fin 3 → ℝ} (ha : ContDiff ℝ 2 a) (k : Fin 3) (x : E3) :
    partial3 (fun y => curl3 a y 0) k x = partial3 (partial3 (fun z => a z 2) 1) k x -
        partial3 (partial3 (fun z => a z 1) 2) k x ∧
      partial3 (fun y => curl3 a y 1) k x = partial3 (partial3 (fun z => a z 0) 2) k x -
        partial3 (partial3 (fun z => a z 2) 0) k x ∧
      partial3 (fun y => curl3 a y 2) k x = partial3 (partial3 (fun z => a z 1) 0) k x -
        partial3 (partial3 (fun z => a z 0) 1) k x := by
  have hd (i l : Fin 3) : DifferentiableAt ℝ (partial3 (fun z => a z i) l) x :=
    differentiable_partial3 (contDiff_pi.mp ha i) l x
  exact ⟨partial3_sub (hd 2 1) (hd 1 2) k, partial3_sub (hd 0 2) (hd 2 0) k,
    partial3_sub (hd 1 0) (hd 0 1) k⟩

/-- The partial derivative of the divergence of a `C²` field. -/
theorem partial3_div3 {a : E3 → Fin 3 → ℝ} (ha : ContDiff ℝ 2 a) (k : Fin 3) (x : E3) :
    partial3 (div3 a) k x = ∑ l, partial3 (partial3 (fun z => a z l) l) k x := by
  have hd (l : Fin 3) : HasFDerivAt (partial3 (fun z => a z l) l)
      (fderiv ℝ (partial3 (fun z => a z l) l) x) x :=
    (differentiable_partial3 (contDiff_pi.mp ha l) l x).hasFDerivAt
  have h : HasFDerivAt (div3 a) (∑ l, fderiv ℝ (partial3 (fun z => a z l) l) x) x :=
    HasFDerivAt.fun_sum fun l _ => hd l
  change fderiv ℝ (div3 a) x _ = _
  rw [h.fderiv, _root_.sum_apply]
  rfl

/-- **`div curl a = 0`** for a `C²` field. -/
theorem div3_curl3 {a : E3 → Fin 3 → ℝ} (ha : ContDiff ℝ 2 a) (x : E3) :
    div3 (curl3 a) x = 0 := by
  obtain ⟨h0, -, -⟩ := partial3_curl3 ha 0 x
  obtain ⟨-, h1, -⟩ := partial3_curl3 ha 1 x
  obtain ⟨-, -, h2⟩ := partial3_curl3 ha 2 x
  have hc (i : Fin 3) := partial3_comm (contDiff_pi.mp ha i)
  rw [div3, Fin.sum_univ_three, h0, h1, h2]
  linarith [hc 2 0 1 x, hc 1 0 2 x, hc 0 1 2 x]

/-- **`curl curl a = ∇ div a − Δa`** for a `C²` field. -/
theorem curl3_curl3 {a : E3 → Fin 3 → ℝ} (ha : ContDiff ℝ 2 a) (x : E3) (i : Fin 3) :
    curl3 (curl3 a) x i = partial3 (div3 a) i x - coordLaplacian (fun y => a y i) x := by
  have hc (l : Fin 3) := partial3_comm (contDiff_pi.mp ha l)
  obtain ⟨-, d01, d02⟩ := partial3_curl3 ha 0 x
  obtain ⟨d10, -, d12⟩ := partial3_curl3 ha 1 x
  obtain ⟨d20, d21, -⟩ := partial3_curl3 ha 2 x
  have e0 : curl3 (curl3 a) x 0 = ∑ l, partial3 (partial3 (fun z => a z l) l) 0 x -
      ∑ k, partial3 (partial3 (fun z => a z 0) k) k x := by
    rw [curl3_apply_zero, d12, d21, Fin.sum_univ_three, Fin.sum_univ_three]
    linarith [hc 1 1 0 x, hc 2 2 0 x]
  have e1 : curl3 (curl3 a) x 1 = ∑ l, partial3 (partial3 (fun z => a z l) l) 1 x -
      ∑ k, partial3 (partial3 (fun z => a z 1) k) k x := by
    rw [curl3_apply_one, d20, d02, Fin.sum_univ_three, Fin.sum_univ_three]
    linarith [hc 2 2 1 x, hc 0 0 1 x]
  have e2 : curl3 (curl3 a) x 2 = ∑ l, partial3 (partial3 (fun z => a z l) l) 2 x -
      ∑ k, partial3 (partial3 (fun z => a z 2) k) k x := by
    rw [curl3_apply_two, d01, d10, Fin.sum_univ_three, Fin.sum_univ_three]
    linarith [hc 0 0 2 x, hc 1 1 2 x]
  rw [partial3_div3 ha, coordLaplacian_eq_sum_partial3]
  fin_cases i
  exacts [e0, e1, e2]

/-- The curl of a `Cⁿ` field is `Cᵐ` when `m + 1 ≤ n`. -/
theorem contDiff_curl3 {f : E3 → Fin 3 → ℝ} {m n : WithTop ℕ∞} (hf : ContDiff ℝ n f)
    (hmn : m + 1 ≤ n) : ContDiff ℝ m (curl3 f) := by
  have hp (i l : Fin 3) : ContDiff ℝ m (partial3 (fun y => f y i) l) :=
    contDiff_partial3 (contDiff_pi.mp hf i) hmn l
  refine contDiff_pi.mpr fun i => ?_
  fin_cases i
  · exact (hp 2 1).sub (hp 1 2)
  · exact (hp 0 2).sub (hp 2 0)
  · exact (hp 1 0).sub (hp 0 1)

/-- The curl vanishes outside the closed support. -/
theorem curl3_eq_zero_of_notMem_tsupport {f : E3 → Fin 3 → ℝ} {x : E3} (hx : x ∉ tsupport f) :
    curl3 f x = 0 := by
  have hc (i : Fin 3) : x ∉ tsupport fun y => f y i := fun h =>
    hx (tsupport_comp_subset (g := fun v : Fin 3 → ℝ => v i) rfl f h)
  have h (i l : Fin 3) := partial3_eq_zero_of_notMem_tsupport (hc i) l
  funext i
  fin_cases i <;> simp [curl3, h]

/-- The curl of a field of compact support has a compact support. -/
theorem hasCompactSupport_curl3 {f : E3 → Fin 3 → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (curl3 f) :=
  hf.mono' fun _ hx => by_contra fun h => hx (curl3_eq_zero_of_notMem_tsupport h)

/-! ### The vector potential -/

/-- A component of a field of compact support has a compact support. -/
theorem hasCompactSupport_component {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j)
    (i : Fin 3) : HasCompactSupport fun y => j y i :=
  hcj.comp_left (g := fun v : Fin 3 → ℝ => v i) rfl

/-- The Newton potential of a finite sum of continuous densities of compact support is the sum
of the potentials. -/
theorem newtonPotential_finsetSum {ι : Type*} (s : Finset ι) {ρ : ι → E3 → ℝ}
    (hc : ∀ i ∈ s, HasCompactSupport (ρ i)) (hρ : ∀ i ∈ s, Continuous (ρ i)) (x : E3) :
    newtonPotential (fun y => ∑ i ∈ s, ρ i y) x = ∑ i ∈ s, newtonPotential (ρ i) x := by
  simp only [newtonPotential_apply, Finset.mul_sum]
  exact integral_finsetSum s fun i hi => integrable_newtonKernel_mul (hc i hi) (hρ i hi) x

/-- The Newton potential of the zero density is zero. -/
theorem newtonPotential_zero (x : E3) : newtonPotential (fun _ => 0) x = 0 := by
  simp [newtonPotential_apply]

/-- The vector potential `aᵢ = N[jᵢ]` of a current, `a(x) = ∫ j(y)/(4π‖x − y‖) dy`. -/
def vectorPotential (j : E3 → Fin 3 → ℝ) (x : E3) (i : Fin 3) : ℝ :=
  newtonPotential (fun y => j y i) x

/-- The vector potential of a `Cⁿ` current of compact support is `Cⁿ`. -/
theorem contDiff_vectorPotential {j : E3 → Fin 3 → ℝ} {n : ℕ∞} (hcj : HasCompactSupport j)
    (hj : ContDiff ℝ n j) : ContDiff ℝ n (vectorPotential j) :=
  contDiff_pi.mpr fun i =>
    contDiff_newtonPotential (hasCompactSupport_component hcj i) (contDiff_pi.mp hj i)

/-- The vector potential of a `C²` current of compact support is `C²`. -/
theorem contDiff_two_vectorPotential {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j)
    (hj : ContDiff ℝ 2 j) : ContDiff ℝ 2 (vectorPotential j) :=
  contDiff_pi.mpr fun i =>
    contDiff_two_newtonPotential (hasCompactSupport_component hcj i) (contDiff_pi.mp hj i)

/-- A partial derivative of the vector potential is the potential of the partial derivative of
the current. -/
theorem partial3_vectorPotential {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j)
    (hj : ContDiff ℝ 1 j) (i k : Fin 3) :
    partial3 (fun y => vectorPotential j y i) k = newtonPotential (partial3 (fun z => j z i) k) :=
  funext fun x =>
    fderiv_newtonPotential_apply (hasCompactSupport_component hcj i) (contDiff_pi.mp hj i) x _

/-- The divergence of the vector potential is the potential of the divergence of the current. -/
theorem div3_vectorPotential_eq {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j)
    (hj : ContDiff ℝ 1 j) (x : E3) : div3 (vectorPotential j) x = newtonPotential (div3 j) x := by
  have hc (i : Fin 3) : HasCompactSupport (partial3 (fun z => j z i) i) :=
    (hasCompactSupport_component hcj i).fderiv_apply (𝕜 := ℝ) _
  have hρ (i : Fin 3) : Continuous (partial3 (fun z => j z i) i) :=
    (contDiff_partial3 (m := 0) (contDiff_pi.mp hj i) (by norm_num) i).continuous
  rw [div3, Finset.sum_congr rfl fun i _ => congrFun (partial3_vectorPotential hcj hj i i) x,
    ← newtonPotential_finsetSum _ (fun i _ => hc i) (fun i _ => hρ i)]
  rfl

/-- **The Coulomb gauge**: the vector potential of a conserved current, `div j = 0`, satisfies
`div a = 0`. -/
theorem div3_vectorPotential {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j)
    (hj : ContDiff ℝ 1 j) (hdiv : ∀ x, div3 j x = 0) (x : E3) : div3 (vectorPotential j) x = 0 := by
  rw [div3_vectorPotential_eq hcj hj, show div3 j = fun _ => 0 from funext hdiv,
    newtonPotential_zero]

/-- **The equation of the vector potential**: `Δa = −j` for a `C²` current of compact support. -/
theorem laplacian_vectorPotential {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j)
    (hj : ContDiff ℝ 2 j) (x : E3) (i : Fin 3) :
    Δ (fun y => vectorPotential j y i) x = -j x i :=
  laplacian_newtonPotential (hasCompactSupport_component hcj i) (contDiff_pi.mp hj i) x

/-- The equation `Δa = −j` with the Laplacian in the co-ordinates. -/
theorem coordLaplacian_vectorPotential {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j)
    (hj : ContDiff ℝ 2 j) (x : E3) (i : Fin 3) :
    coordLaplacian (fun y => vectorPotential j y i) x = -j x i := by
  rw [coordLaplacian_eq_laplacian
    ((contDiff_pi.mp (contDiff_two_vectorPotential hcj hj) i).contDiffAt)]
  exact laplacian_vectorPotential hcj hj x i

/-- The vector potential tends to `0` at infinity. -/
theorem tendsto_vectorPotential {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j)
    (hj : Continuous j) (i : Fin 3) :
    Tendsto (fun y => vectorPotential j y i) (cocompact E3) (𝓝 0) :=
  tendsto_newtonPotential_cocompact (continuous_apply i |>.comp hj)
    (hasCompactSupport_component hcj i)

/-! ### The magnetic field -/

/-- The magnetic field `B = curl a` of a static current. -/
def magneticField3 (j : E3 → Fin 3 → ℝ) : E3 → Fin 3 → ℝ :=
  curl3 (vectorPotential j)

/-- **`div B = 0`** for the field of a `C²` current of compact support. -/
theorem div3_magneticField3 {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j)
    (hj : ContDiff ℝ 2 j) (x : E3) : div3 (magneticField3 j) x = 0 :=
  div3_curl3 (contDiff_two_vectorPotential hcj hj) x

/-- **The equation of the static field**, `curl B = j`, for a conserved `C²` current of compact
support. -/
theorem curl3_magneticField3 {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j)
    (hj : ContDiff ℝ 2 j) (hdiv : ∀ x, div3 j x = 0) (x : E3) :
    curl3 (magneticField3 j) x = j x := by
  have hj1 : ContDiff ℝ 1 j := hj.of_le (by norm_num)
  have hdiva : div3 (vectorPotential j) = fun _ => 0 :=
    funext (div3_vectorPotential hcj hj1 hdiv)
  funext i
  rw [magneticField3, curl3_curl3 (contDiff_two_vectorPotential hcj hj),
    coordLaplacian_vectorPotential hcj hj, hdiva]
  simp [partial3]

/-- The field is `Cⁿ` for a `Cⁿ⁺¹` current of compact support. -/
theorem contDiff_magneticField3 {j : E3 → Fin 3 → ℝ} {n : ℕ∞} (hcj : HasCompactSupport j)
    (hj : ContDiff ℝ (n + 1 : ℕ∞) j) : ContDiff ℝ n (magneticField3 j) :=
  contDiff_curl3 (contDiff_vectorPotential hcj hj) (by exact_mod_cast le_rfl)

/-- The field components are Newton potentials of the derivatives of the current. -/
theorem magneticField3_apply {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j)
    (hj : ContDiff ℝ 1 j) (x : E3) :
    magneticField3 j x = ![newtonPotential (partial3 (fun z => j z 2) 1) x -
        newtonPotential (partial3 (fun z => j z 1) 2) x,
      newtonPotential (partial3 (fun z => j z 0) 2) x -
        newtonPotential (partial3 (fun z => j z 2) 0) x,
      newtonPotential (partial3 (fun z => j z 1) 0) x -
        newtonPotential (partial3 (fun z => j z 0) 1) x] := by
  simp only [magneticField3, curl3, partial3_vectorPotential hcj hj]

/-- The field of a `C¹` current of compact support tends to `0` at infinity. -/
theorem tendsto_magneticField3 {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j)
    (hj : ContDiff ℝ 1 j) (i : Fin 3) :
    Tendsto (fun y => magneticField3 j y i) (cocompact E3) (𝓝 0) := by
  have ht (i k : Fin 3) : Tendsto (newtonPotential (partial3 (fun z => j z i) k))
      (cocompact E3) (𝓝 0) :=
    tendsto_newtonPotential_cocompact
      (contDiff_partial3 (m := 0) (contDiff_pi.mp hj i) (by norm_num) k).continuous
      ((hasCompactSupport_component hcj i).fderiv_apply (𝕜 := ℝ) _)
  simp only [magneticField3_apply hcj hj]
  fin_cases i
  · simpa using (ht 2 1).sub (ht 1 2)
  · simpa using (ht 0 2).sub (ht 2 0)
  · simpa using (ht 1 0).sub (ht 0 1)

/-! ### The law of Biot and Savart -/

/-- Outside a ball `‖y‖ ≤ a` that contains the support of a continuous current, a partial
derivative of the vector potential is `∂ₗaₖ(x) = ∫ jₖ(y) ∂ₗK(x − y) dy`, with an integrable
integrand. -/
theorem partial3_vectorPotential_of_lt {j : E3 → Fin 3 → ℝ} (hj : Continuous j)
    (hcj : HasCompactSupport j) {a : ℝ} (ha : tsupport j ⊆ closedBall 0 a) {x : E3}
    (hx : a < ‖x‖) (k l : Fin 3) :
    Integrable (fun y => j y k * fderiv ℝ newtonKernel (x - y) (EuclideanSpace.single l 1)) ∧
      partial3 (fun y => vectorPotential j y k) l x =
        ∫ y, j y k * fderiv ℝ newtonKernel (x - y) (EuclideanSpace.single l 1) := by
  have hρ : Continuous fun y => j y k := (continuous_apply k).comp hj
  have hcρ := hasCompactSupport_component hcj k
  have hak : tsupport (fun y => j y k) ⊆ closedBall 0 a :=
    (tsupport_comp_subset (g := fun v : Fin 3 → ℝ => v k) rfl j).trans ha
  have hd : 0 < ‖x‖ - a := by linarith
  have hφ : Integrable fun y => j y k • fderiv ℝ newtonKernel (x - y) := by
    refine Integrable.mono' ((hρ.abs.mul (continuous_const (y := (4 * π * (‖x‖ - a) ^ 2)⁻¹))
      ).integrable_of_hasCompactSupport hcρ.abs.mul_right) (hρ.aestronglyMeasurable.smul
        ((measurable_fderiv ℝ newtonKernel).comp
          (measurable_const.sub measurable_id)).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    by_cases hy : j y k = 0
    · simp [hy]
    · have hya : ‖y‖ ≤ a := by simpa using hak (subset_tsupport _ hy)
      have hxy : ‖x‖ - a ≤ ‖x - y‖ := by linarith [norm_sub_norm_le x y]
      have hne : x - y ≠ 0 := norm_pos_iff.mp (hd.trans_le hxy)
      rw [norm_smul, norm_fderiv_newtonKernel hne, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) ?_) (abs_nonneg _)
      have : (‖x‖ - a) ^ 2 ≤ ‖x - y‖ ^ 2 := pow_le_pow_left₀ hd.le hxy 2
      nlinarith [pi_pos]
  refine ⟨hφ.apply_continuousLinearMap _, ?_⟩
  change fderiv ℝ (newtonPotential fun y => j y k) x _ = _
  rw [(hasFDerivAt_newtonPotential_of_lt hρ hcρ hak hx).fderiv,
    ContinuousLinearMap.integral_apply hφ]
  rfl

/-- **The law of Biot and Savart** outside the support: for a `C¹` current of compact support in
the ball `‖y‖ ≤ a`, `B(x) = ∫ j(y) × (x − y)/(4π‖x − y‖³) dy` for `‖x‖ > a`. -/
theorem magneticField3_eq_biotSavart {j : E3 → Fin 3 → ℝ} (hj : Continuous j)
    (hcj : HasCompactSupport j) {a : ℝ} (ha : tsupport j ⊆ closedBall 0 a) {x : E3}
    (hx : a < ‖x‖) (i : Fin 3) :
    magneticField3 j x i =
      ∫ y, crossProduct (j y) (WithLp.ofLp (x - y)) i / (4 * π * ‖x - y‖ ^ 3) := by
  have hd : 0 < ‖x‖ - a := by linarith
  have hp := partial3_vectorPotential_of_lt hj hcj ha hx
  have hK (y : E3) (hy : j y ≠ 0) (l : Fin 3) :
      fderiv ℝ newtonKernel (x - y) (EuclideanSpace.single l 1) =
        -(x - y) l / (4 * π * ‖x - y‖ ^ 3) := by
    have hya : ‖y‖ ≤ a := by simpa using ha (subset_tsupport _ hy)
    have hne : x - y ≠ 0 := norm_pos_iff.mp (hd.trans_le (by linarith [norm_sub_norm_le x y]))
    rw [(hasFDerivAt_newtonKernel hne).fderiv]
    simp [EuclideanSpace.inner_single_right]
    ring
  have key (k l m n : Fin 3) (hlm : ∀ y, crossProduct (j y) (WithLp.ofLp (x - y)) i =
      j y m * (x - y) n - j y k * (x - y) l) :
      partial3 (fun y => vectorPotential j y k) l x - partial3 (fun y => vectorPotential j y m) n x
        = ∫ y, crossProduct (j y) (WithLp.ofLp (x - y)) i / (4 * π * ‖x - y‖ ^ 3) := by
    rw [(hp k l).2, (hp m n).2, ← integral_sub (hp k l).1 (hp m n).1]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : j y = 0
    · simp [hy]
    · simp only [hK y hy, hlm]
      ring
  fin_cases i
  · exact key 2 1 1 2 fun y => by simp [cross_apply]
  · exact key 0 2 2 0 fun y => by simp [cross_apply]
  · exact key 1 0 0 1 fun y => by simp [cross_apply]

/-! ### Uniqueness -/

/-- **Uniqueness of the vector potential**: a `C²` solution of `Δa′ = −j` that tends to `0` at
infinity is the vector potential. -/
theorem vectorPotential_unique {j a : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j)
    (hj : ContDiff ℝ 2 j) (ha : ContDiff ℝ 2 a) (hΔ : ∀ x i, Δ (fun y => a y i) x = -j x i)
    (hlim : ∀ i, Tendsto (fun y => a y i) (cocompact E3) (𝓝 0)) : a = vectorPotential j := by
  funext x i
  have h := eq_newtonPotential_of_tendsto (hasCompactSupport_component hcj i)
    (contDiff_pi.mp hj i) (contDiff_pi.mp ha i) (fun x => by rw [hΔ, neg_neg]) (hlim i)
  exact congrFun h x

/-- **Uniqueness in the Coulomb gauge**: a `C²` potential with `div a′ = 0` and
`curl curl a′ = j` that tends to `0` at infinity is the vector potential. -/
theorem vectorPotential_unique_of_curl {j a : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j)
    (hj : ContDiff ℝ 2 j) (ha : ContDiff ℝ 2 a) (hdiv : ∀ x, div3 a x = 0)
    (hcurl : ∀ x, curl3 (curl3 a) x = j x)
    (hlim : ∀ i, Tendsto (fun y => a y i) (cocompact E3) (𝓝 0)) : a = vectorPotential j := by
  refine vectorPotential_unique hcj hj ha (fun x i => ?_) hlim
  have h := curl3_curl3 ha x i
  rw [hcurl, show div3 a = fun _ => 0 from funext hdiv] at h
  rw [← coordLaplacian_eq_laplacian (contDiff_pi.mp ha i).contDiffAt]
  simp [partial3] at h
  linarith

/-- A `C²` field with `div B = 0` and `curl B = j` has the Laplacian `ΔB = −curl j`. -/
theorem coordLaplacian_of_div_curl {j B : E3 → Fin 3 → ℝ} (hB : ContDiff ℝ 2 B)
    (hdiv : ∀ x, div3 B x = 0) (hcurl : ∀ x, curl3 B x = j x) (x : E3) (i : Fin 3) :
    coordLaplacian (fun y => B y i) x = -curl3 j x i := by
  have h := curl3_curl3 hB x i
  rw [show curl3 B = j from funext hcurl, show div3 B = fun _ => 0 from funext hdiv] at h
  simp [partial3] at h
  linarith

/-- **Uniqueness of the static field**: for a conserved `C³` current of compact support, a `C²`
field with `div B′ = 0` and `curl B′ = j` that tends to `0` at infinity is `magneticField3 j`. -/
theorem magneticField3_unique {j B : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j)
    (hj : ContDiff ℝ 3 j) (hdivj : ∀ x, div3 j x = 0) (hB : ContDiff ℝ 2 B)
    (hdiv : ∀ x, div3 B x = 0) (hcurl : ∀ x, curl3 B x = j x)
    (hlim : ∀ i, Tendsto (fun y => B y i) (cocompact E3) (𝓝 0)) : B = magneticField3 j := by
  have hj2 : ContDiff ℝ 2 j := hj.of_le (by norm_num)
  have hj1 : ContDiff ℝ 1 j := hj.of_le (by norm_num)
  have hM : ContDiff ℝ 2 (magneticField3 j) :=
    contDiff_magneticField3 (n := 2) hcj (by exact_mod_cast hj)
  funext x i
  have hBi := contDiff_pi.mp hB i
  have hMi := contDiff_pi.mp hM i
  have h := eq_zero_of_harmonic_of_tendsto (u := (fun y => B y i) - fun y => magneticField3 j y i)
    (hBi.sub hMi) (fun y => ?_) ?_
  · exact sub_eq_zero.mp (congrFun h x)
  · rw [ContDiffAt.laplacian_sub hBi.contDiffAt hMi.contDiffAt,
      ← coordLaplacian_eq_laplacian hBi.contDiffAt, ← coordLaplacian_eq_laplacian hMi.contDiffAt,
      coordLaplacian_of_div_curl hB hdiv hcurl,
      coordLaplacian_of_div_curl hM (div3_magneticField3 hcj hj2)
        (curl3_magneticField3 hcj hj2 hdivj)]
    simp
  · have h1 := (hlim i).sub (tendsto_magneticField3 hcj hj1 i)
    rw [sub_zero] at h1
    exact h1

/-! ### The potential on space-time -/

/-- The four-potential `A = a · dx` of the vector potential of a static current. -/
def magnetostaticPotential (j : E3 → Fin 3 → ℝ) : Potential :=
  potentialOf 0 fun y => vectorPotential j (space y)

/-- The four-potential is `Σᵢ aᵢ dxⁱ`. -/
theorem magnetostaticPotential_eq (j : E3 → Fin 3 → ℝ) :
    magnetostaticPotential j = fun y => ∑ i : Fin 3,
      vectorPotential j (space y) i • oneCovector.symm (ContinuousLinearMap.proj i.succ) := by
  funext y
  simp [magnetostaticPotential, potentialOf]

/-- The four-potential of a `Cⁿ` current of compact support is `Cⁿ`. -/
theorem contDiff_magnetostaticPotential {j : E3 → Fin 3 → ℝ} {n : ℕ∞}
    (hcj : HasCompactSupport j) (hj : ContDiff ℝ n j) :
    ContDiff ℝ n (magnetostaticPotential j) := by
  have ha := contDiff_vectorPotential hcj hj
  rw [magnetostaticPotential_eq]
  exact ContDiff.sum fun i _ =>
    ((contDiff_pi.mp ha i).comp space.contDiff).smul contDiff_const

/-- The derivative of the four-potential of a `C¹` current of compact support. -/
theorem hasFDerivAt_magnetostaticPotential {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j)
    (hj : ContDiff ℝ 1 j) (y : Spacetime) :
    HasFDerivAt (magnetostaticPotential j) (∑ i : Fin 3,
      ((fderiv ℝ (fun z => vectorPotential j z i) (space y)).comp
        (space : Spacetime →L[ℝ] Space 3)).smulRight
          (oneCovector.symm (ContinuousLinearMap.proj i.succ))) y := by
  have ha := contDiff_vectorPotential (n := 1) hcj (by exact_mod_cast hj)
  rw [magnetostaticPotential_eq]
  refine HasFDerivAt.fun_sum fun i _ => ?_
  exact ((((contDiff_pi.mp ha i).differentiable (by norm_num) (space y)).hasFDerivAt.comp y
    space.hasFDerivAt)).smul_const (oneCovector.symm (ContinuousLinearMap.proj i.succ))

/-- The field of `a · dx`: `F(v, w) = Σᵢ (Daᵢ(v⃗) wⁱ − Daᵢ(w⃗) vⁱ)`. -/
theorem fieldTensor_magnetostaticPotential_apply {j : E3 → Fin 3 → ℝ}
    (hcj : HasCompactSupport j) (hj : ContDiff ℝ 1 j) (y v w : Spacetime) :
    fieldTensor (magnetostaticPotential j) y ![v, w] =
      ∑ i : Fin 3, (fderiv ℝ (fun z => vectorPotential j z i) (space y) (space v) * w i.succ -
        fderiv ℝ (fun z => vectorPotential j z i) (space y) (space w) * v i.succ) := by
  rw [fieldTensor_apply, (hasFDerivAt_magnetostaticPotential hcj hj y).fderiv,
    Finset.sum_sub_distrib]
  simp

/-- The space part of the axis `1` of space-time is the axis `0` of space. -/
theorem space_single_one : space (Pi.single 1 1 : Spacetime) = EuclideanSpace.single 0 1 :=
  Electrostatics.space_pi_single_succ 0

/-- The space part of the axis `2` of space-time is the axis `1` of space. -/
theorem space_single_two : space (Pi.single 2 1 : Spacetime) = EuclideanSpace.single 1 1 :=
  Electrostatics.space_pi_single_succ 1

/-- The space part of the axis `3` of space-time is the axis `2` of space. -/
theorem space_single_three : space (Pi.single 3 1 : Spacetime) = EuclideanSpace.single 2 1 :=
  Electrostatics.space_pi_single_succ 2

/-- The field of `a · dx` has no electric part. -/
theorem electricField_magnetostaticPotential {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j)
    (hj : ContDiff ℝ 1 j) (i : Fin 3) (y : Spacetime) :
    electricField (fieldTensor (magnetostaticPotential j)) i y = 0 := by
  rw [electricField, electricVector_apply, component,
    fieldTensor_magnetostaticPotential_apply hcj hj, Electrostatics.space_pi_single_zero]
  simp [Fin.succ_ne_zero]

/-- The magnetic part of the field of `a · dx` is `B = curl a` at the position of the event. -/
theorem magneticField_magnetostaticPotential {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j)
    (hj : ContDiff ℝ 1 j) (i : Fin 3) (y : Spacetime) :
    magneticField (fieldTensor (magnetostaticPotential j)) i y = magneticField3 j (space y) i := by
  rw [magneticField]
  fin_cases i <;>
    simp [magneticVector, component, fieldTensor_magnetostaticPotential_apply hcj hj,
      Fin.sum_univ_three, space_single_one, space_single_two, space_single_three,
      magneticField3, curl3, partial3, Pi.single_apply]

/-- The curl on space-time of a static field is the curl in space at the position. -/
theorem curl_comp_space {f : E3 → Fin 3 → ℝ} (hf : Differentiable ℝ f) (y : Spacetime) :
    curl (fun i z => f (space z) i) y = curl3 f (space y) := by
  have hd (i : Fin 3) : DifferentiableAt ℝ (fun x => f x i) (space y) :=
    differentiable_pi.mp hf i (space y)
  funext i
  fin_cases i <;>
    simp [curl, curl3, partialAt, partial3, Electrostatics.fderiv_comp_space_apply (hd _),
      space_single_one, space_single_two, space_single_three]

/-- **The equations of Maxwell for a static current**: for a conserved `C²` current of compact
support the field of `A = a · dx` satisfies `div B = 0`, `∂_t B + curl E = 0`, `div E = 0` and
`curl B − ∂_t E = j` at every event, with the current at the position of the event. -/
theorem maxwell_staticVector {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j)
    (hj : ContDiff ℝ 2 j) (hdiv : ∀ x, div3 j x = 0) (y : Spacetime) :
    (divergence3 (magneticField (fieldTensor (magnetostaticPotential j))) y = 0 ∧
      ∀ i, partialAt (magneticField (fieldTensor (magnetostaticPotential j)) i) 0 y +
        curl (electricField (fieldTensor (magnetostaticPotential j))) y i = 0) ∧
    (divergence3 (electricField (fieldTensor (magnetostaticPotential j))) y = 0 ∧
      ∀ i, curl (magneticField (fieldTensor (magnetostaticPotential j))) y i -
        partialAt (electricField (fieldTensor (magnetostaticPotential j)) i) 0 y =
          j (space y) i) := by
  have hj1 : ContDiff ℝ 1 j := hj.of_le (by norm_num)
  have hA : ContDiff ℝ 2 (magnetostaticPotential j) :=
    contDiff_magnetostaticPotential (n := 2) hcj (by exact_mod_cast hj)
  have hE : electricField (fieldTensor (magnetostaticPotential j)) = fun _ _ => 0 := by
    funext i z
    exact electricField_magnetostaticPotential hcj hj1 i z
  have hB : magneticField (fieldTensor (magnetostaticPotential j)) =
      fun i z => magneticField3 j (space z) i := by
    funext i z
    exact magneticField_magnetostaticPotential hcj hj1 i z
  have hM : Differentiable ℝ (magneticField3 j) :=
    (contDiff_magneticField3 (n := 1) hcj (by exact_mod_cast hj)).differentiable (by norm_num)
  refine ⟨homogeneous_fieldTensor isOpen_univ hA.contDiffOn (mem_univ y), ?_, fun i => ?_⟩
  · rw [hE]
    simp [divergence3, partialAt]
  · rw [hB, hE, curl_comp_space hM, curl3_magneticField3 hcj hj hdiv]
    simp [partialAt]

/-- **The equation of the excitation for a static current**: the field of `A = a · dx` satisfies
`d(−⋆F) = −ι_k vol` with the current `k = (0, j ∘ space)` of space-time. -/
theorem excitation_staticVector {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j)
    (hj : ContDiff ℝ 2 j) (hdiv : ∀ x, div3 j x = 0) (y : Spacetime) :
    exteriorDerivative (fun z => -star (fieldTensor (magnetostaticPotential j) z)) y =
      SourcedAction.matterCurrentForm (fun z => (Fin.cons 0 (j (space z)) : Spacetime)) y := by
  have hA : ContDiff ℝ 2 (magnetostaticPotential j) :=
    contDiff_magnetostaticPotential (n := 2) hcj (by exact_mod_cast hj)
  obtain ⟨-, hdivE, hcurl⟩ := maxwell_staticVector hcj hj hdiv y
  exact excitation_of_inhomogeneous
    (differentiableAt_fieldTensor isOpen_univ hA.contDiffOn (mem_univ y)) (by simpa using hdivE)
    (fun i => by simpa using hcurl i)

/-! ### An instance -/

/-- The bump function `ψ` on space that is `1` on the unit ball and `0` outside the ball of
radius `2`. -/
def bumpFunction : ContDiffBump (0 : E3) :=
  ⟨1, 2, zero_lt_one, one_lt_two⟩

/-- The field `ψ e_z` of the bump function along the third axis. -/
def bumpField (x : E3) : Fin 3 → ℝ :=
  ![0, 0, bumpFunction x]

/-- The field `ψ e_z` is smooth. -/
theorem contDiff_bumpField : ContDiff ℝ ∞ bumpField := by
  refine contDiff_pi.mpr fun i => ?_
  fin_cases i
  · exact contDiff_const
  · exact contDiff_const
  · exact bumpFunction.contDiff

/-- The field `ψ e_z` has a compact support. -/
theorem hasCompactSupport_bumpField : HasCompactSupport bumpField :=
  bumpFunction.hasCompactSupport.comp_left (g := fun t : ℝ => ![0, 0, t]) (by simp)

/-- The ring current `j = curl(ψ e_z) = (∂_y ψ, −∂_x ψ, 0)` of the bump function, which circulates
about the third axis. -/
def ringCurrent : E3 → Fin 3 → ℝ :=
  curl3 bumpField

/-- The ring current is smooth. -/
theorem contDiff_ringCurrent : ContDiff ℝ ∞ ringCurrent :=
  contDiff_curl3 contDiff_bumpField (by simp)

/-- The ring current has a compact support. -/
theorem hasCompactSupport_ringCurrent : HasCompactSupport ringCurrent :=
  hasCompactSupport_curl3 hasCompactSupport_bumpField

/-- The ring current is conserved, `div j = 0`. -/
theorem div3_ringCurrent (x : E3) : div3 ringCurrent x = 0 :=
  div3_curl3 (contDiff_bumpField.of_le (by simp)) x

/-- The second component of the ring current is `−∂_x ψ`. -/
theorem ringCurrent_apply_one (x : E3) : ringCurrent x 1 = -partial3 bumpFunction 0 x := by
  rw [ringCurrent, curl3_apply_one]
  simp [bumpField, partial3]

/-- The ring current is not zero. -/
theorem ringCurrent_ne_zero : ringCurrent ≠ 0 := by
  intro h
  have hd (x : E3) : partial3 bumpFunction 0 x = 0 := by
    have := congrFun (congrFun h x) 1
    rw [ringCurrent_apply_one] at this
    simpa using this
  set e : E3 := EuclideanSpace.single 0 1
  set g : ℝ → ℝ := fun t => bumpFunction (t • e)
  have hg (t : ℝ) : HasDerivAt g 0 t := by
    have h1 : HasDerivAt (fun s : ℝ => s • e) e t := by
      simpa using (hasDerivAt_id t).smul_const e
    have h2 := (bumpFunction.contDiff (n := 1).differentiable (by norm_num) (t • e)).hasFDerivAt
    have h3 := h2.comp_hasDerivAt t h1
    have h4 : fderiv ℝ bumpFunction (t • e) e = 0 := hd (t • e)
    rw [h4] at h3
    exact h3
  have hconst := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt)
    (fun t => (hg t).deriv) 0 3
  have h0 : g 0 = 1 := by
    simp only [g, zero_smul]
    exact bumpFunction.one_of_mem_closedBall (by simp [bumpFunction])
  have h3 : g 3 = 0 := by
    simp only [g]
    refine bumpFunction.zero_of_le_dist ?_
    simp [bumpFunction, e, norm_smul]
    norm_num
  rw [h0, h3] at hconst
  exact one_ne_zero hconst

end ProjectAinos.Electrodynamics.Magnetostatics
