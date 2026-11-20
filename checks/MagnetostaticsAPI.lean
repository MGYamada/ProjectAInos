/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.Electrodynamics.Magnetostatics
import ProjectAinos.Electrodynamics.MagneticMoment

/-! Public consumers of magnetostatics (Landau–Lifshitz §§43–44): the vector potential of a
conserved current in Coulomb gauge with `Δa = −j`, `curl B = j`, `div B = 0`, uniqueness, the
Biot–Savart law outside the source and Maxwell's equations on space-time, with a ring-current
instance; and the magnetic moment with the moment identities, the dipole far field, stationary
flows with a rigidly rotating instance, the ratio `e/2m` and the torque in a uniform field.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/

noncomputable section

section Magnetostatics

open MeasureTheory Filter Set Metric Real

open scoped Topology Laplacian ContDiff

namespace ProjectAinos.Electrodynamics.Magnetostatics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Potential
  SmoothGeometry.DifferentialForm SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (f : E3 → ℝ) (i : Fin 3) :
    E3 → ℝ :=
  partial3 f i

example (f : E3 → Fin 3 → ℝ) (x : E3) :
    ℝ :=
  div3 f x

example (f : E3 → Fin 3 → ℝ) (x : E3) :
    Fin 3 → ℝ :=
  curl3 f x

example (f : E3 → Fin 3 → ℝ) (x : E3) :
    curl3 f x 0 = partial3 (fun y => f y 2) 1 x - partial3 (fun y => f y 1) 2 x :=
  curl3_apply_zero f x

example (f : E3 → Fin 3 → ℝ) (x : E3) :
    curl3 f x 1 = partial3 (fun y => f y 0) 2 x - partial3 (fun y => f y 2) 0 x :=
  curl3_apply_one f x

example (f : E3 → Fin 3 → ℝ) (x : E3) :
    curl3 f x 2 = partial3 (fun y => f y 1) 0 x - partial3 (fun y => f y 0) 1 x :=
  curl3_apply_two f x

example (f : E3 → ℝ) (x : E3) :
    coordLaplacian f x = ∑ k, partial3 (partial3 f k) k x :=
  coordLaplacian_eq_sum_partial3 f x

example {f : E3 → ℝ} {m n : WithTop ℕ∞} (hf : ContDiff ℝ n f) (hmn : m + 1 ≤ n) (i : Fin 3) :
    ContDiff ℝ m (partial3 f i) :=
  contDiff_partial3 hf hmn i

example {f : E3 → ℝ} (hf : ContDiff ℝ 2 f) (i : Fin 3) :
    Differentiable ℝ (partial3 f i) :=
  differentiable_partial3 hf i

example {f : E3 → ℝ} (hf : ContDiff ℝ 2 f) (k l : Fin 3) (x : E3) :
    partial3 (partial3 f l) k x = partial3 (partial3 f k) l x :=
  partial3_comm hf k l x

example {f g : E3 → ℝ} {x : E3} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (i : Fin 3) :
    partial3 (fun y => f y - g y) i x = partial3 f i x - partial3 g i x :=
  partial3_sub hf hg i

example {f : E3 → ℝ} {x : E3} (hx : x ∉ tsupport f) (i : Fin 3) :
    partial3 f i x = 0 :=
  partial3_eq_zero_of_notMem_tsupport hx i

example {a : E3 → Fin 3 → ℝ} (ha : ContDiff ℝ 2 a) (k : Fin 3) (x : E3) :
    partial3 (fun y => curl3 a y 0) k x = partial3 (partial3 (fun z => a z 2) 1) k x -
        partial3 (partial3 (fun z => a z 1) 2) k x ∧
      partial3 (fun y => curl3 a y 1) k x = partial3 (partial3 (fun z => a z 0) 2) k x -
        partial3 (partial3 (fun z => a z 2) 0) k x ∧
      partial3 (fun y => curl3 a y 2) k x = partial3 (partial3 (fun z => a z 1) 0) k x -
        partial3 (partial3 (fun z => a z 0) 1) k x :=
  partial3_curl3 ha k x

example {a : E3 → Fin 3 → ℝ} (ha : ContDiff ℝ 2 a) (k : Fin 3) (x : E3) :
    partial3 (div3 a) k x = ∑ l, partial3 (partial3 (fun z => a z l) l) k x :=
  partial3_div3 ha k x

example {a : E3 → Fin 3 → ℝ} (ha : ContDiff ℝ 2 a) (x : E3) :
    div3 (curl3 a) x = 0 :=
  div3_curl3 ha x

example {a : E3 → Fin 3 → ℝ} (ha : ContDiff ℝ 2 a) (x : E3) (i : Fin 3) :
    curl3 (curl3 a) x i = partial3 (div3 a) i x - coordLaplacian (fun y => a y i) x :=
  curl3_curl3 ha x i

example {f : E3 → Fin 3 → ℝ} {m n : WithTop ℕ∞} (hf : ContDiff ℝ n f) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (curl3 f) :=
  contDiff_curl3 hf hmn

example {f : E3 → Fin 3 → ℝ} {x : E3} (hx : x ∉ tsupport f) :
    curl3 f x = 0 :=
  curl3_eq_zero_of_notMem_tsupport hx

example {f : E3 → Fin 3 → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (curl3 f) :=
  hasCompactSupport_curl3 hf

example {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j) (i : Fin 3) :
    HasCompactSupport fun y => j y i :=
  hasCompactSupport_component hcj i

example {ι : Type*} (s : Finset ι) {ρ : ι → E3 → ℝ} (hc : ∀ i ∈ s, HasCompactSupport (ρ i))
    (hρ : ∀ i ∈ s, Continuous (ρ i)) (x : E3) :
    newtonPotential (fun y => ∑ i ∈ s, ρ i y) x = ∑ i ∈ s, newtonPotential (ρ i) x :=
  newtonPotential_finsetSum s hc hρ x

example (x : E3) :
    newtonPotential (fun _ => 0) x = 0 :=
  newtonPotential_zero x

example (j : E3 → Fin 3 → ℝ) (x : E3) (i : Fin 3) :
    ℝ :=
  vectorPotential j x i

example {j : E3 → Fin 3 → ℝ} {n : ℕ∞} (hcj : HasCompactSupport j) (hj : ContDiff ℝ n j) :
    ContDiff ℝ n (vectorPotential j) :=
  contDiff_vectorPotential hcj hj

example {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j) (hj : ContDiff ℝ 2 j) :
    ContDiff ℝ 2 (vectorPotential j) :=
  contDiff_two_vectorPotential hcj hj

example {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j) (hj : ContDiff ℝ 1 j) (i k : Fin 3) :
    partial3 (fun y => vectorPotential j y i) k = newtonPotential (partial3 (fun z => j z i) k) :=
  partial3_vectorPotential hcj hj i k

example {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j) (hj : ContDiff ℝ 1 j) (x : E3) :
    div3 (vectorPotential j) x = newtonPotential (div3 j) x :=
  div3_vectorPotential_eq hcj hj x

example {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j) (hj : ContDiff ℝ 1 j)
    (hdiv : ∀ x, div3 j x = 0) (x : E3) :
    div3 (vectorPotential j) x = 0 :=
  div3_vectorPotential hcj hj hdiv x

example {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j) (hj : ContDiff ℝ 2 j) (x : E3)
    (i : Fin 3) :
    Δ (fun y => vectorPotential j y i) x = -j x i :=
  laplacian_vectorPotential hcj hj x i

example {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j) (hj : ContDiff ℝ 2 j) (x : E3)
    (i : Fin 3) :
    coordLaplacian (fun y => vectorPotential j y i) x = -j x i :=
  coordLaplacian_vectorPotential hcj hj x i

example {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j) (hj : Continuous j) (i : Fin 3) :
    Tendsto (fun y => vectorPotential j y i) (cocompact E3) (𝓝 0) :=
  tendsto_vectorPotential hcj hj i

example (j : E3 → Fin 3 → ℝ) :
    E3 → Fin 3 → ℝ :=
  magneticField3 j

example {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j) (hj : ContDiff ℝ 2 j) (x : E3) :
    div3 (magneticField3 j) x = 0 :=
  div3_magneticField3 hcj hj x

example {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j) (hj : ContDiff ℝ 2 j)
    (hdiv : ∀ x, div3 j x = 0) (x : E3) :
    curl3 (magneticField3 j) x = j x :=
  curl3_magneticField3 hcj hj hdiv x

example {j : E3 → Fin 3 → ℝ} {n : ℕ∞} (hcj : HasCompactSupport j) (hj : ContDiff ℝ (n + 1 : ℕ∞) j) :
    ContDiff ℝ n (magneticField3 j) :=
  contDiff_magneticField3 hcj hj

example {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j) (hj : ContDiff ℝ 1 j) (x : E3) :
    magneticField3 j x = ![newtonPotential (partial3 (fun z => j z 2) 1) x -
        newtonPotential (partial3 (fun z => j z 1) 2) x,
      newtonPotential (partial3 (fun z => j z 0) 2) x -
        newtonPotential (partial3 (fun z => j z 2) 0) x,
      newtonPotential (partial3 (fun z => j z 1) 0) x -
        newtonPotential (partial3 (fun z => j z 0) 1) x] :=
  magneticField3_apply hcj hj x

example {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j) (hj : ContDiff ℝ 1 j) (i : Fin 3) :
    Tendsto (fun y => magneticField3 j y i) (cocompact E3) (𝓝 0) :=
  tendsto_magneticField3 hcj hj i

example {j : E3 → Fin 3 → ℝ} (hj : Continuous j) (hcj : HasCompactSupport j) {a : ℝ}
    (ha : tsupport j ⊆ closedBall 0 a) {x : E3} (hx : a < ‖x‖) (k l : Fin 3) :
    Integrable (fun y => j y k * fderiv ℝ newtonKernel (x - y) (EuclideanSpace.single l 1)) ∧
      partial3 (fun y => vectorPotential j y k) l x =
        ∫ y, j y k * fderiv ℝ newtonKernel (x - y) (EuclideanSpace.single l 1) :=
  partial3_vectorPotential_of_lt hj hcj ha hx k l

example {j : E3 → Fin 3 → ℝ} (hj : Continuous j) (hcj : HasCompactSupport j) {a : ℝ}
    (ha : tsupport j ⊆ closedBall 0 a) {x : E3} (hx : a < ‖x‖) (i : Fin 3) :
    magneticField3 j x i =
      ∫ y, crossProduct (j y) (WithLp.ofLp (x - y)) i / (4 * π * ‖x - y‖ ^ 3) :=
  magneticField3_eq_biotSavart hj hcj ha hx i

example {j a : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j) (hj : ContDiff ℝ 2 j)
    (ha : ContDiff ℝ 2 a) (hΔ : ∀ x i, Δ (fun y => a y i) x = -j x i)
    (hlim : ∀ i, Tendsto (fun y => a y i) (cocompact E3) (𝓝 0)) :
    a = vectorPotential j :=
  vectorPotential_unique hcj hj ha hΔ hlim

example {j a : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j) (hj : ContDiff ℝ 2 j)
    (ha : ContDiff ℝ 2 a) (hdiv : ∀ x, div3 a x = 0) (hcurl : ∀ x, curl3 (curl3 a) x = j x)
    (hlim : ∀ i, Tendsto (fun y => a y i) (cocompact E3) (𝓝 0)) :
    a = vectorPotential j :=
  vectorPotential_unique_of_curl hcj hj ha hdiv hcurl hlim

example {j B : E3 → Fin 3 → ℝ} (hB : ContDiff ℝ 2 B) (hdiv : ∀ x, div3 B x = 0)
    (hcurl : ∀ x, curl3 B x = j x) (x : E3) (i : Fin 3) :
    coordLaplacian (fun y => B y i) x = -curl3 j x i :=
  coordLaplacian_of_div_curl hB hdiv hcurl x i

example {j B : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j) (hj : ContDiff ℝ 3 j)
    (hdivj : ∀ x, div3 j x = 0) (hB : ContDiff ℝ 2 B) (hdiv : ∀ x, div3 B x = 0)
    (hcurl : ∀ x, curl3 B x = j x) (hlim : ∀ i, Tendsto (fun y => B y i) (cocompact E3) (𝓝 0)) :
    B = magneticField3 j :=
  magneticField3_unique hcj hj hdivj hB hdiv hcurl hlim

example (j : E3 → Fin 3 → ℝ) :
    Potential :=
  magnetostaticPotential j

example (j : E3 → Fin 3 → ℝ) :
    magnetostaticPotential j = fun y => ∑ i : Fin 3,
      vectorPotential j (space y) i • oneCovector.symm (ContinuousLinearMap.proj i.succ) :=
  magnetostaticPotential_eq j

example {j : E3 → Fin 3 → ℝ} {n : ℕ∞} (hcj : HasCompactSupport j) (hj : ContDiff ℝ n j) :
    ContDiff ℝ n (magnetostaticPotential j) :=
  contDiff_magnetostaticPotential hcj hj

example {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j) (hj : ContDiff ℝ 1 j) (y : Spacetime) :
    HasFDerivAt (magnetostaticPotential j) (∑ i : Fin 3,
      ((fderiv ℝ (fun z => vectorPotential j z i) (space y)).comp
        (space : Spacetime →L[ℝ] Space 3)).smulRight
          (oneCovector.symm (ContinuousLinearMap.proj i.succ))) y :=
  hasFDerivAt_magnetostaticPotential hcj hj y

example {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j) (hj : ContDiff ℝ 1 j) (y v w : Spacetime) :
    fieldTensor (magnetostaticPotential j) y ![v, w] =
      ∑ i : Fin 3, (fderiv ℝ (fun z => vectorPotential j z i) (space y) (space v) * w i.succ -
        fderiv ℝ (fun z => vectorPotential j z i) (space y) (space w) * v i.succ) :=
  fieldTensor_magnetostaticPotential_apply hcj hj y v w

example :
    space (Pi.single 1 1 : Spacetime) = EuclideanSpace.single 0 1 :=
  space_single_one

example :
    space (Pi.single 2 1 : Spacetime) = EuclideanSpace.single 1 1 :=
  space_single_two

example :
    space (Pi.single 3 1 : Spacetime) = EuclideanSpace.single 2 1 :=
  space_single_three

example {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j) (hj : ContDiff ℝ 1 j) (i : Fin 3)
    (y : Spacetime) :
    electricField (fieldTensor (magnetostaticPotential j)) i y = 0 :=
  electricField_magnetostaticPotential hcj hj i y

example {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j) (hj : ContDiff ℝ 1 j) (i : Fin 3)
    (y : Spacetime) :
    magneticField (fieldTensor (magnetostaticPotential j)) i y = magneticField3 j (space y) i :=
  magneticField_magnetostaticPotential hcj hj i y

example {f : E3 → Fin 3 → ℝ} (hf : Differentiable ℝ f) (y : Spacetime) :
    curl (fun i z => f (space z) i) y = curl3 f (space y) :=
  curl_comp_space hf y

example {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j) (hj : ContDiff ℝ 2 j)
    (hdiv : ∀ x, div3 j x = 0) (y : Spacetime) :
    (divergence3 (magneticField (fieldTensor (magnetostaticPotential j))) y = 0 ∧
      ∀ i, partialAt (magneticField (fieldTensor (magnetostaticPotential j)) i) 0 y +
        curl (electricField (fieldTensor (magnetostaticPotential j))) y i = 0) ∧
    (divergence3 (electricField (fieldTensor (magnetostaticPotential j))) y = 0 ∧
      ∀ i, curl (magneticField (fieldTensor (magnetostaticPotential j))) y i -
        partialAt (electricField (fieldTensor (magnetostaticPotential j)) i) 0 y =
          j (space y) i) :=
  maxwell_staticVector hcj hj hdiv y

example {j : E3 → Fin 3 → ℝ} (hcj : HasCompactSupport j) (hj : ContDiff ℝ 2 j)
    (hdiv : ∀ x, div3 j x = 0) (y : Spacetime) :
    exteriorDerivative (fun z => -star (fieldTensor (magnetostaticPotential j) z)) y =
      SourcedAction.matterCurrentForm (fun z => (Fin.cons 0 (j (space z)) : Spacetime)) y :=
  excitation_staticVector hcj hj hdiv y

example :
    ContDiffBump (0 : E3) :=
  bumpFunction

example (x : E3) :
    Fin 3 → ℝ :=
  bumpField x

example :
    ContDiff ℝ ∞ bumpField :=
  contDiff_bumpField

example :
    HasCompactSupport bumpField :=
  hasCompactSupport_bumpField

example :
    E3 → Fin 3 → ℝ :=
  ringCurrent

example :
    ContDiff ℝ ∞ ringCurrent :=
  contDiff_ringCurrent

example :
    HasCompactSupport ringCurrent :=
  hasCompactSupport_ringCurrent

example (x : E3) :
    div3 ringCurrent x = 0 :=
  div3_ringCurrent x

example (x : E3) :
    ringCurrent x 1 = -partial3 bumpFunction 0 x :=
  ringCurrent_apply_one x

example :
    ringCurrent ≠ 0 :=
  ringCurrent_ne_zero

end ProjectAinos.Electrodynamics.Magnetostatics

end Magnetostatics

section MagneticMoment

open MeasureTheory Filter Set Metric Real Matrix

open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics.MagneticMoment

open SmoothGeometry SmoothGeometry.Potential Magnetostatics

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example {f : E3 → ℝ} {j : E3 → Fin 3 → ℝ} (hf : ContDiff ℝ 1 f) (hj : ContDiff ℝ 1 j)
    (hcj : HasCompactSupport j) :
    ∫ x, f x * div3 j x = -∫ x, ∑ l, partial3 f l x * j x l :=
  integral_mul_div3 hf hj hcj

example (i l : Fin 3) (x : E3) :
    partial3 (fun y : E3 => y i) l x = if i = l then 1 else 0 :=
  partial3_coord i l x

example (i : Fin 3) :
    ContDiff ℝ ∞ fun y : E3 => y i :=
  contDiff_coord i

example {j : E3 → Fin 3 → ℝ} (hj : Continuous j) (hcj : HasCompactSupport j) (k i : Fin 3) :
    Integrable fun y : E3 => y k * j y i :=
  integrable_coord_mul hj hcj k i

example {j : E3 → Fin 3 → ℝ} (hj : ContDiff ℝ 1 j) (hcj : HasCompactSupport j)
    (hdiv : ∀ x, div3 j x = 0) (i : Fin 3) :
    ∫ x, j x i = 0 :=
  integral_current_eq_zero hj hcj hdiv i

example (j : E3 → Fin 3 → ℝ) (i k : Fin 3) :
    ℝ :=
  firstMoment j i k

example {j : E3 → Fin 3 → ℝ} (hj : ContDiff ℝ 1 j) (hcj : HasCompactSupport j)
    (hdiv : ∀ x, div3 j x = 0) (i k : Fin 3) :
    ∫ y, (y i * j y k + y k * j y i) = 0 :=
  integral_moment_symm hj hcj hdiv i k

example {j : E3 → Fin 3 → ℝ} (hj : ContDiff ℝ 1 j) (hcj : HasCompactSupport j)
    (hdiv : ∀ x, div3 j x = 0) (i k : Fin 3) :
    firstMoment j i k = -firstMoment j k i :=
  firstMoment_antisymm hj hcj hdiv i k

example {j : E3 → Fin 3 → ℝ} (hj : ContDiff ℝ 1 j) (hcj : HasCompactSupport j)
    (hdiv : ∀ x, div3 j x = 0) (i : Fin 3) :
    firstMoment j i i = 0 :=
  firstMoment_self hj hcj hdiv i

example (j : E3 → Fin 3 → ℝ) :
    Fin 3 → ℝ :=
  magneticMoment j

example {j : E3 → Fin 3 → ℝ} (hj : Continuous j) (hcj : HasCompactSupport j) :
    magneticMoment j = ![(firstMoment j 2 1 - firstMoment j 1 2) / 2,
      (firstMoment j 0 2 - firstMoment j 2 0) / 2,
      (firstMoment j 1 0 - firstMoment j 0 1) / 2] :=
  magneticMoment_eq hj hcj

example {j : E3 → Fin 3 → ℝ} (hj : ContDiff ℝ 1 j) (hcj : HasCompactSupport j)
    (hdiv : ∀ x, div3 j x = 0) (v : Fin 3 → ℝ) (i : Fin 3) :
    (magneticMoment j ⨯₃ v) i = ∑ k, v k * firstMoment j i k :=
  cross_magneticMoment_apply hj hcj hdiv v i

example {j : E3 → Fin 3 → ℝ} (hj : ContDiff ℝ 1 j) (hcj : HasCompactSupport j)
    (hdiv : ∀ x, div3 j x = 0) (x : E3) (i : Fin 3) :
    ∫ y, j y i * inner ℝ x y = (magneticMoment j ⨯₃ WithLp.ofLp x) i :=
  integral_mul_inner hj hcj hdiv x i

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (x : E3) :
    Integrable fun y => ρ y * newtonKernel (x - y) :=
  integrable_mul_newtonKernel_sub hρ hcρ x

example {j : E3 → Fin 3 → ℝ} (hj : ContDiff ℝ 1 j) (hcj : HasCompactSupport j)
    (hdiv : ∀ x, div3 j x = 0) {a : ℝ} (ha : tsupport j ⊆ closedBall 0 a) {x : E3} (hx : a < ‖x‖) :
    ‖vectorPotential j x - (4 * π * ‖x‖ ^ 3)⁻¹ • (magneticMoment j ⨯₃ WithLp.ofLp x)‖ ≤
      (∫ y, ‖j y‖ * ‖y‖ ^ 2) / (4 * π * (‖x‖ - a) ^ 3) :=
  norm_vectorPotential_sub_dipole_le hj hcj hdiv ha hx

example {f : E3 → Fin 3 → ℝ} (hf : Differentiable ℝ f) (c : ℝ) (x : E3) :
    div3 (fun y => c • f y) x = c * div3 f x :=
  div3_const_smul hf c x

namespace StationaryFlow

example (F : StationaryFlow) (e m : ℝ) :
    E3 → Fin 3 → ℝ :=
  current F e m

example (F : StationaryFlow) (e m : ℝ) :
    ContDiff ℝ ∞ (F.current e m) :=
  contDiff_current F e m

example (F : StationaryFlow) (e m : ℝ) :
    HasCompactSupport (F.current e m) :=
  hasCompactSupport_current F e m

example (F : StationaryFlow) (e m : ℝ) (x : E3) :
    div3 (F.current e m) x = 0 :=
  div3_current F e m x

example (F : StationaryFlow) :
    Fin 3 → ℝ :=
  angularMomentum F

end StationaryFlow

example (F : StationaryFlow) (e m : ℝ) :
    magneticMoment (F.current e m) = (e / (2 * m)) • F.angularMomentum :=
  magneticMoment_flow F e m

example :
    ContDiffBump (0 : ℝ) :=
  bumpProfile

example (x : E3) :
    ℝ :=
  radialDensity x

example :
    ContDiff ℝ ∞ radialDensity :=
  contDiff_radialDensity

example :
    HasCompactSupport radialDensity :=
  hasCompactSupport_radialDensity

example (x v : E3) :
    fderiv ℝ radialDensity x v = 2 * deriv bumpProfile (‖x‖ ^ 2) * inner ℝ x v :=
  fderiv_radialDensity_apply x v

example (Ω : Fin 3 → ℝ) :
    E3 →L[ℝ] Fin 3 → ℝ :=
  rigidVelocity Ω

example (Ω : Fin 3 → ℝ) (x : E3) :
    rigidVelocity Ω x = Ω ⨯₃ WithLp.ofLp x :=
  rigidVelocity_apply Ω x

example (Ω : Fin 3 → ℝ) :
    StationaryFlow :=
  rigidRotation Ω

example {j : E3 → Fin 3 → ℝ} (hj : ContDiff ℝ 1 j) (hcj : HasCompactSupport j)
    (hdiv : ∀ x, div3 j x = 0) (B₀ : Fin 3 → ℝ) :
    (fun i => ∫ y, (j y ⨯₃ B₀) i) = 0 :=
  force_uniformField hj hcj hdiv B₀

example {j : E3 → Fin 3 → ℝ} (hj : ContDiff ℝ 1 j) (hcj : HasCompactSupport j)
    (hdiv : ∀ x, div3 j x = 0) (B₀ : Fin 3 → ℝ) :
    (fun i => ∫ y, (WithLp.ofLp y ⨯₃ (j y ⨯₃ B₀)) i) = magneticMoment j ⨯₃ B₀ :=
  torque_uniformField hj hcj hdiv B₀

end ProjectAinos.Electrodynamics.MagneticMoment

end MagneticMoment
