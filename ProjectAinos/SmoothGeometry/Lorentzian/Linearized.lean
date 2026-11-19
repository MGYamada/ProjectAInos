/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateEinsteinEquation
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateKilling
public import ProjectAinos.SmoothGeometry.Minkowski.Matrix

/-!
# The linearized Einstein operator about flat space-time

On the model space `MinkowskiModel d`, let `η = diag(lorentzSign σ i)` be the Minkowski
coefficients (`Minkowski.metricMatrix σ d`) and `h` a field of coefficient matrices, smooth and
symmetric on an open set `U`. Since `η^{ij} = η_{ij}`, the factors `η^{aa}` are
`lorentzSign σ a`. Write `∂_a ∂_b f = secondPartial f x a b` (the derivative of `fderiv`); it is
linear on functions smooth at `x` (`secondPartial_add`, `secondPartial_sum_mul`, …), symmetric
(`secondPartial_comm`), and the inner derivatives of `∂_a ∂_b (∂_c f)` commute
(`secondPartial_fderiv_swap`).

* `linearizedChristoffel`: `δΓ^k_{ij} = ½ η^{kk} (∂_i h_{jk} + ∂_j h_{ki} − ∂_k h_{ij})`, the
  derivative in `ε` at `0` of the Christoffel symbols of `η + ε h`
  (`hasDerivAt_christoffelOf_linear`).
* `linearizedRicci`:
  `δR_{jk} = ½ Σ_i η^{ii} (∂_i∂_j h_{ik} + ∂_i∂_k h_{ij} − ∂_i∂_i h_{jk} − ∂_j∂_k h_{ii})`.
  **The derivative theorem** `hasDerivAt_ricciOf_linear`: for `x ∈ U`, it is the derivative in
  `ε` at `0` of `ricciOf (η + ε h)`. The proof is the first variation `hasDerivAt_familyRicci`
  for the family `linearFamily σ h (ε, z) = η + ε h(z)`: the flat Christoffel symbols vanish, and
  the variation of the Christoffel symbols is `linearizedChristoffel`.
* `linearizedScalar`, `linearizedEinstein`: the trace `η^{aa} δR_{aa}` and
  `δG_{jk} = δR_{jk} − ½ η_{jk} δR`, the derivatives of `scalarOf` and `einsteinOf`
  (`hasDerivAt_scalarOf_linear`, `hasDerivAt_einsteinOf_linear`).
* **Actual metrics.** If `|h_{ij}| ≤ M` on `U`, then `η + ε h` has the Lorentz signature on `U`
  for `|ε| (d + 1)² M < 1` (`isAdmissible_linear`): it is the coordinate metric `linearMetric`.
  `linearMetricFamily` extends these metrics by `η` to all `ε`, and
  `hasDerivAt_ricci_linearMetricFamily`, `hasDerivAt_einstein_linearMetricFamily` state that
  `δR` and `δG` are the derivatives of the native Ricci and Einstein tensors of this family of
  Lorentz metrics on the manifold `U`.
* **Gauge invariance.** For components `ξ^k` smooth on `U`, the Lie derivative of `η` is
  `(L_ξ η)_{ij} = ∂_i ξ_j + ∂_j ξ_i` with `ξ_j = η_{jj} ξ^j` (`lieOf_metricMatrix`), and
  `δR(h + L_ξ η) = δR(h)` (`linearizedRicci_add_lie`, `linearizedEinstein_add_lie`).
* **Harmonic gauge.** With the trace `tr h = η^{ab} h_{ab}` (`flatTrace`), the trace reverse
  `h̄ = h − ½ η tr h` (`traceReverse`) and `□ = Σ_a η^{aa} ∂_a ∂_a` (`flatBox`), the gauge
  condition `Σ_a η^{aa} ∂_a h̄_{ab} = 0` on `U` (`IsHarmonicGauge`) gives `δR_{jk} = −½ □h_{jk}`
  (`linearizedRicci_of_isHarmonicGauge`) and `δG_{jk} = −½ □h̄_{jk}`
  (`linearizedEinstein_of_isHarmonicGauge`). `isHarmonicGauge_zero` is the trivial instance;
  the plane waves of `GeneralRelativity/WeakWaves.lean` are the nontrivial ones. The trace and
  the trace reverse are linear (`flatTrace_add`, `traceReverse_smul`, …),
  `tr h̄ = (1 − (d + 1)/2) tr h` (`flatTrace_traceReverse`), and in four dimensions the trace
  reverse is an involution (`traceReverse_traceReverse`).
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

namespace CoordinateMetric

/-! ### Second partial derivatives -/

section SecondPartial

variable {f g : MinkowskiModel d → ℝ} {x : MinkowskiModel d}

/-- The second partial derivative `∂_a ∂_b f = ∂_a (∂_b f)` of a function on the model. -/
def secondPartial (f : MinkowskiModel d → ℝ) (x : MinkowskiModel d) (a b : Fin (d + 1)) : ℝ :=
  fderiv ℝ (fun z => fderiv ℝ f z (Pi.single b 1)) x (Pi.single a 1)

/-- A partial derivative of a function that is smooth at `x` is smooth at `x`. -/
theorem contDiffAt_fderiv_apply (hf : ContDiffAt ℝ ∞ f x) (v : MinkowskiModel d) :
    ContDiffAt ℝ ∞ (fun z => fderiv ℝ f z v) x :=
  (hf.fderiv_right (by simp)).clm_apply contDiffAt_const

/-- A function that is smooth at `x` is differentiable near `x`. -/
theorem eventually_differentiableAt (hf : ContDiffAt ℝ ∞ f x) :
    ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ f z := by
  have h1 : ContDiffAt ℝ 1 f x := hf.of_le (by simp)
  exact (h1.eventually (by simp)).mono fun _ hz => hz.differentiableAt one_ne_zero

/-- A partial derivative of a function that is smooth at `x` is differentiable at `x`. -/
theorem differentiableAt_partial (hf : ContDiffAt ℝ ∞ f x) (v : MinkowskiModel d) :
    DifferentiableAt ℝ (fun z => fderiv ℝ f z v) x :=
  (contDiffAt_fderiv_apply hf v).differentiableAt (by simp)

/-- The derivative of a linear combination `Σ_i c_i f_i`. -/
theorem fderiv_sum_mul_apply {ι : Type} (s : Finset ι) {F : ι → MinkowskiModel d → ℝ}
    (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) x) (c : ι → ℝ) (v : MinkowskiModel d) :
    fderiv ℝ (fun z => ∑ i ∈ s, c i * F i z) x v = ∑ i ∈ s, c i * fderiv ℝ (F i) x v := by
  rw [fderiv_fun_sum fun i hi => (hF i hi).const_mul (c i), _root_.sum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [fderiv_const_mul (hF i hi), _root_.smul_apply, smul_eq_mul]

/-- Second partial derivatives only depend on the germ of the function. -/
theorem secondPartial_congr (hfg : f =ᶠ[𝓝 x] g) (a b : Fin (d + 1)) :
    secondPartial f x a b = secondPartial g x a b := by
  have hev : (fun z => fderiv ℝ f z (Pi.single b 1)) =ᶠ[𝓝 x]
      fun z => fderiv ℝ g z (Pi.single b 1) :=
    hfg.eventuallyEq_nhds.mono fun z hz => by dsimp only; rw [hz.fderiv_eq]
  rw [secondPartial, hev.fderiv_eq]
  rfl

/-- The second partial derivatives of a constant vanish. -/
@[simp] theorem secondPartial_const (c : ℝ) (a b : Fin (d + 1)) :
    secondPartial (fun _ => c) x a b = 0 := by
  simp [secondPartial]

/-- Second partial derivatives are additive on functions smooth at the point. -/
theorem secondPartial_add (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (a b : Fin (d + 1)) :
    secondPartial (fun z => f z + g z) x a b = secondPartial f x a b + secondPartial g x a b := by
  have hev : (fun z => fderiv ℝ (fun w => f w + g w) z (Pi.single b 1)) =ᶠ[𝓝 x]
      fun z => fderiv ℝ f z (Pi.single b 1) + fderiv ℝ g z (Pi.single b 1) := by
    filter_upwards [eventually_differentiableAt hf, eventually_differentiableAt hg] with z hfz hgz
    rw [fderiv_fun_add hfz hgz, _root_.add_apply]
  rw [secondPartial, hev.fderiv_eq, fderiv_fun_add (differentiableAt_partial hf _)
    (differentiableAt_partial hg _), _root_.add_apply]
  rfl

/-- Second partial derivatives of a difference. -/
theorem secondPartial_sub (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (a b : Fin (d + 1)) :
    secondPartial (fun z => f z - g z) x a b = secondPartial f x a b - secondPartial g x a b := by
  have hev : (fun z => fderiv ℝ (fun w => f w - g w) z (Pi.single b 1)) =ᶠ[𝓝 x]
      fun z => fderiv ℝ f z (Pi.single b 1) - fderiv ℝ g z (Pi.single b 1) := by
    filter_upwards [eventually_differentiableAt hf, eventually_differentiableAt hg] with z hfz hgz
    rw [fderiv_fun_sub hfz hgz, _root_.sub_apply]
  rw [secondPartial, hev.fderiv_eq, fderiv_fun_sub (differentiableAt_partial hf _)
    (differentiableAt_partial hg _), _root_.sub_apply]
  rfl

/-- Second partial derivatives commute with constant factors. -/
theorem secondPartial_const_mul (hf : ContDiffAt ℝ ∞ f x) (c : ℝ) (a b : Fin (d + 1)) :
    secondPartial (fun z => c * f z) x a b = c * secondPartial f x a b := by
  have hev : (fun z => fderiv ℝ (fun w => c * f w) z (Pi.single b 1)) =ᶠ[𝓝 x]
      fun z => c * fderiv ℝ f z (Pi.single b 1) := by
    filter_upwards [eventually_differentiableAt hf] with z hfz
    rw [fderiv_const_mul hfz, _root_.smul_apply, smul_eq_mul]
  rw [secondPartial, hev.fderiv_eq, fderiv_const_mul (differentiableAt_partial hf _),
    _root_.smul_apply, smul_eq_mul]
  rfl

/-- The second partial derivatives of a finite linear combination. -/
theorem secondPartial_sum_mul {ι : Type} (s : Finset ι) {F : ι → MinkowskiModel d → ℝ}
    (hF : ∀ i ∈ s, ContDiffAt ℝ ∞ (F i) x) (c : ι → ℝ) (a b : Fin (d + 1)) :
    secondPartial (fun z => ∑ i ∈ s, c i * F i z) x a b =
      ∑ i ∈ s, c i * secondPartial (F i) x a b := by
  have hev : (fun z => fderiv ℝ (fun w => ∑ i ∈ s, c i * F i w) z (Pi.single b 1)) =ᶠ[𝓝 x]
      fun z => ∑ i ∈ s, c i * fderiv ℝ (F i) z (Pi.single b 1) := by
    filter_upwards [(Filter.eventually_all_finset s).2
      fun i hi => eventually_differentiableAt (hF i hi)] with z hz
    exact fderiv_sum_mul_apply s hz c _
  rw [secondPartial, hev.fderiv_eq,
    fderiv_sum_mul_apply s (fun i hi => differentiableAt_partial (hF i hi) _) c]
  rfl

/-- **Second partial derivatives commute** at a point where the function is `C²`. -/
theorem secondPartial_comm (hf : ContDiffAt ℝ 2 f x) (a b : Fin (d + 1)) :
    secondPartial f x a b = secondPartial f x b a := by
  have hsymm := hf.isSymmSndFDerivAt (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have key (v w : MinkowskiModel d) :
      fderiv ℝ (fun z => fderiv ℝ f z w) x v = fderiv ℝ (fderiv ℝ f) x v w := by
    rw [fderiv_clm_apply hd (differentiableAt_const w)]
    simp
  rw [secondPartial, secondPartial, key, key]
  exact hsymm _ _

/-- The two inner derivatives of a third partial derivative commute. -/
theorem secondPartial_fderiv_swap (hf : ContDiffAt ℝ ∞ f x) (a b c : Fin (d + 1)) :
    secondPartial (fun z => fderiv ℝ f z (Pi.single c 1)) x a b =
      secondPartial (fun z => fderiv ℝ f z (Pi.single b 1)) x a c := by
  have hev : (fun z => fderiv ℝ (fun w => fderiv ℝ f w (Pi.single c 1)) z (Pi.single b 1))
      =ᶠ[𝓝 x] fun z => fderiv ℝ (fun w => fderiv ℝ f w (Pi.single b 1)) z (Pi.single c 1) := by
    have h2 : ContDiffAt ℝ 2 f x := hf.of_le (by simp)
    filter_upwards [h2.eventually (by simp)] with z hz
    exact secondPartial_comm hz b c
  rw [secondPartial, hev.fderiv_eq]
  rfl

end SecondPartial

/-! ### The Minkowski coefficients -/

section Flat

/-- The entries `η_{ij} = δ_{ij} η_{ii}` of the Minkowski coefficients. -/
theorem metricMatrix_apply (i j : Fin (d + 1)) :
    Minkowski.metricMatrix σ d i j = if i = j then lorentzSign σ i else 0 :=
  Matrix.diagonal_apply _ _ _

/-- The Minkowski coefficients are their own inverse: `η^{ij} = η_{ij}`. -/
theorem metricMatrix_inv : (Minkowski.metricMatrix σ d)⁻¹ = Minkowski.metricMatrix σ d :=
  Matrix.inv_eq_left_inv (Minkowski.metricMatrix_mul_self σ)

/-- Contracting with the Minkowski coefficients picks one entry: `η_{kl} X^l = η_{kk} X^k`. -/
theorem sum_metricMatrix_mul (X : Fin (d + 1) → ℝ) (k : Fin (d + 1)) :
    ∑ l, Minkowski.metricMatrix σ d k l * X l = lorentzSign σ k * X k := by
  simp [metricMatrix_apply]

/-- `η^{aa} η_{ab} X_a = X_b`. -/
theorem sum_lorentzSign_mul_metricMatrix (X : Fin (d + 1) → ℝ) (b : Fin (d + 1)) :
    ∑ a, lorentzSign σ a * (Minkowski.metricMatrix σ d a b * X a) = X b := by
  simp [metricMatrix_apply, ← mul_assoc]

end Flat

/-! ### The family `η + ε h` and the variation of the Christoffel symbols -/

section Christoffel

variable {h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}

variable (σ) in
/-- The family `η + ε h(z)` of coefficients, as a function of `(ε, z)`. -/
def linearFamily (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (p : ℝ × MinkowskiModel d) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Minkowski.metricMatrix σ d + p.1 • h p.2

/-- The entries `η_{ij} + ε h_{ij}(z)` of the family. -/
theorem linearFamily_apply (p : ℝ × MinkowskiModel d) (i j : Fin (d + 1)) :
    linearFamily σ h p i j = Minkowski.metricMatrix σ d i j + p.1 * h p.2 i j := by
  simp [linearFamily]

/-- At `ε = 0` the family is `η`. -/
theorem linearFamily_zero (z : MinkowskiModel d) :
    linearFamily σ h (0, z) = Minkowski.metricMatrix σ d := by
  simp [linearFamily]

/-- The family is smooth in `(ε, z)` where `h` is smooth. -/
theorem contDiffAt_linearFamily (hh : ∀ i j, ContDiffAt ℝ ∞ (fun z => h z i j) x) (ε : ℝ)
    (i j : Fin (d + 1)) : ContDiffAt ℝ ∞ (fun q => linearFamily σ h q i j) (ε, x) := by
  have e : (fun q => linearFamily σ h q i j) =
      fun q : ℝ × MinkowskiModel d => Minkowski.metricMatrix σ d i j + q.1 * h q.2 i j :=
    funext fun q => linearFamily_apply q i j
  rw [e]
  exact contDiffAt_const.add (contDiffAt_fst.mul ((hh i j).comp (ε, x) contDiffAt_snd))

/-- At `ε = 0` the determinant of the family does not vanish. -/
theorem linearFamily_det_zero (z : MinkowskiModel d) : (linearFamily σ h (0, z)).det ≠ 0 := by
  rw [linearFamily_zero]
  exact Minkowski.metricMatrix_det_ne_zero σ

/-- At `ε = 0` the Christoffel symbols of the family vanish: `η` is constant. -/
@[simp] theorem familyChristoffel_linearFamily_zero (z : MinkowskiModel d) (k i j : Fin (d + 1)) :
    familyChristoffel (linearFamily σ h) (0, z) k i j = 0 := by
  simp [familyChristoffel, linearFamily]

/-- At `ε = 0` the Ricci tensor of the family vanishes. -/
@[simp] theorem familyRicci_linearFamily_zero (z : MinkowskiModel d) (j k : Fin (d + 1)) :
    familyRicci (linearFamily σ h) (0, z) j k = 0 := by
  simp [familyRicci, linearFamily]

variable (σ) in
/-- The linearized Christoffel symbols
`δΓ^k_{ij} = ½ η^{kk} (∂_i h_{jk} + ∂_j h_{ki} − ∂_k h_{ij})`, in the index order of
`christoffelOf`; for symmetric `h` this is `½ η^{kk} (∂_i h_{kj} + ∂_j h_{ki} − ∂_k h_{ij})`. -/
def linearizedChristoffel (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (k i j : Fin (d + 1)) : ℝ :=
  lorentzSign σ k * (fderiv ℝ (fun z => h z j k) x (Pi.single i 1) +
    fderiv ℝ (fun z => h z k i) x (Pi.single j 1) -
    fderiv ℝ (fun z => h z i j) x (Pi.single k 1)) / 2

/-- **The variation of the Christoffel symbols about flat space-time.** -/
theorem hasDerivAt_christoffelOf_linear (hh : ∀ i j, ContDiffAt ℝ ∞ (fun z => h z i j) x)
    (k i j : Fin (d + 1)) :
    HasDerivAt (fun ε => familyChristoffel (linearFamily σ h) (ε, x) k i j)
      (linearizedChristoffel σ h x k i j) 0 := by
  have hd (a b : Fin (d + 1)) : DifferentiableAt ℝ (fun z => h z a b) x :=
    (hh a b).differentiableAt (by simp)
  have hfd (ε : ℝ) (a b c : Fin (d + 1)) :
      fderiv ℝ (fun z => linearFamily σ h (ε, z) a b) x (Pi.single c 1) =
        ε * fderiv ℝ (fun z => h z a b) x (Pi.single c 1) := by
    have e : (fun z => linearFamily σ h (ε, z) a b) =
        fun z => Minkowski.metricMatrix σ d a b + ε * h z a b :=
      funext fun z => linearFamily_apply (ε, z) a b
    rw [e, fderiv_const_add, fderiv_const_mul (hd a b), _root_.smul_apply,
      smul_eq_mul]
  set A : Fin (d + 1) → ℝ := fun l => fderiv ℝ (fun z => h z j l) x (Pi.single i 1) +
    fderiv ℝ (fun z => h z l i) x (Pi.single j 1) - fderiv ℝ (fun z => h z i j) x (Pi.single l 1)
  have hform : (fun ε => familyChristoffel (linearFamily σ h) (ε, x) k i j) =
      fun ε => ∑ l, (linearFamily σ h (ε, x))⁻¹ k l * (ε * A l) / 2 := by
    funext ε
    simp only [familyChristoffel, christoffelOf, hfd, A]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have hinv (l : Fin (d + 1)) : HasDerivAt (fun ε => (linearFamily σ h (ε, x))⁻¹ k l)
      (deriv (fun ε => (linearFamily σ h (ε, x))⁻¹ k l) 0) 0 := by
    have hc := (contDiffAt_familyInv (fun a b => contDiffAt_linearFamily (σ := σ) hh 0 a b)
      (linearFamily_det_zero x) k l).comp (0 : ℝ)
      ((contDiffAt_id (𝕜 := ℝ)).prodMk (contDiffAt_const (c := x)))
    exact (hc.differentiableAt (by simp)).hasDerivAt
  rw [hform]
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun l _ =>
    ((hinv l).fun_mul ((hasDerivAt_id' (0 : ℝ)).mul_const (A l))).div_const 2
  convert hsum using 1
  simp only [zero_mul, mul_zero, zero_add, one_mul, linearFamily_zero, metricMatrix_inv]
  rw [← Finset.sum_div, sum_metricMatrix_mul]
  simp only [A, linearizedChristoffel]

end Christoffel

/-! ### The linearized Ricci and Einstein tensors -/

section Ricci

variable {h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}

variable (σ) in
/-- The linearized Ricci tensor
`δR_{jk} = ½ Σ_i η^{ii} (∂_i∂_j h_{ik} + ∂_i∂_k h_{ij} − ∂_i∂_i h_{jk} − ∂_j∂_k h_{ii})`. -/
def linearizedRicci (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (j k : Fin (d + 1)) : ℝ :=
  ∑ i, lorentzSign σ i * (secondPartial (fun z => h z i k) x i j +
    secondPartial (fun z => h z i j) x i k - secondPartial (fun z => h z j k) x i i -
    secondPartial (fun z => h z i i) x j k) / 2

variable (σ) in
/-- The linearized scalar curvature `δR = η^{aa} δR_{aa}`. -/
def linearizedScalar (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) : ℝ :=
  ∑ a, lorentzSign σ a * linearizedRicci σ h x a a

variable (σ) in
/-- The linearized Einstein tensor `δG_{jk} = δR_{jk} − ½ δR η_{jk}`. -/
def linearizedEinstein (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (j k : Fin (d + 1)) : ℝ :=
  linearizedRicci σ h x j k - linearizedScalar σ h x / 2 * Minkowski.metricMatrix σ d j k

/-- The derivative of `c (P + Q − R)/2`. -/
theorem fderiv_christoffelForm {P Q R : MinkowskiModel d → ℝ} (hP : DifferentiableAt ℝ P x)
    (hQ : DifferentiableAt ℝ Q x) (hR : DifferentiableAt ℝ R x) (c : ℝ) (v : MinkowskiModel d) :
    fderiv ℝ (fun z => c * (P z + Q z - R z) / 2) x v =
      c * (fderiv ℝ P x v + fderiv ℝ Q x v - fderiv ℝ R x v) / 2 := by
  have e : (fun z => c * (P z + Q z - R z) / 2) = fun z => c / 2 * (P z + Q z - R z) :=
    funext fun z => by ring
  rw [e, fderiv_const_mul ((hP.fun_add hQ).fun_sub hR), fderiv_fun_sub (hP.fun_add hQ) hR,
    fderiv_fun_add hP hQ]
  simp only [_root_.smul_apply, _root_.add_apply, _root_.sub_apply, smul_eq_mul]
  ring

/-- The linearized Ricci tensor through the linearized Christoffel symbols:
`δR_{jk} = ∂_i δΓ^i_{jk} − ∂_j δΓ^i_{ik}`. -/
theorem linearizedRicci_eq_christoffel {U : Opens (MinkowskiModel d)}
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) (hx : x ∈ U) (j k : Fin (d + 1)) :
    linearizedRicci σ h x j k = ∑ i,
      (fderiv ℝ (fun z => linearizedChristoffel σ h z i j k) x (Pi.single i 1) -
        fderiv ℝ (fun z => linearizedChristoffel σ h z i i k) x (Pi.single j 1)) := by
  have hc (a b : Fin (d + 1)) : ContDiffAt ℝ ∞ (fun z => h z a b) x :=
    (hh a b).contDiffAt (U.isOpen.mem_nhds hx)
  have hd (a b : Fin (d + 1)) (v : MinkowskiModel d) :
      DifferentiableAt ℝ (fun z => fderiv ℝ (fun w => h w a b) z v) x :=
    differentiableAt_partial (hc a b) v
  have hsym (a b c e : Fin (d + 1)) :
      secondPartial (fun z => h z a b) x c e = secondPartial (fun z => h z b a) x c e :=
    secondPartial_congr (Filter.eventually_of_mem (U.isOpen.mem_nhds hx)
      fun z hz => hs z hz a b) c e
  unfold linearizedRicci linearizedChristoffel
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_christoffelForm (hd _ _ _) (hd _ _ _) (hd _ _ _),
    fderiv_christoffelForm (hd _ _ _) (hd _ _ _) (hd _ _ _)]
  change _ = lorentzSign σ i * (secondPartial (fun z => h z k i) x i j +
      secondPartial (fun z => h z i j) x i k - secondPartial (fun z => h z j k) x i i) / 2 -
    lorentzSign σ i * (secondPartial (fun z => h z k i) x j i +
      secondPartial (fun z => h z i i) x j k - secondPartial (fun z => h z i k) x j i) / 2
  rw [hsym k i, hsym k i]
  ring

/-- The variation of the Ricci tensor of the family `η + ε h` is the linearized Ricci tensor. -/
theorem familyRicciDeriv_linearFamily {U : Opens (MinkowskiModel d)}
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) (hx : x ∈ U) (j k : Fin (d + 1)) :
    familyRicciDeriv (linearFamily σ h) x j k = linearizedRicci σ h x j k := by
  have hc (z : MinkowskiModel d) (hz : z ∈ U) (a b : Fin (d + 1)) :
      ContDiffAt ℝ ∞ (fun w => h w a b) z :=
    (hh a b).contDiffAt (U.isOpen.mem_nhds hz)
  have hΓ (z : MinkowskiModel d) (hz : z ∈ U) (a b c : Fin (d + 1)) :
      ContDiffAt ℝ ∞ (fun q => familyChristoffel (linearFamily σ h) q a b c) ((0 : ℝ), z) :=
    contDiffAt_familyChristoffel (fun a b => contDiffAt_linearFamily (hc z hz) 0 a b)
      (linearFamily_det_zero z) a b c
  have hδ (z : MinkowskiModel d) (hz : z ∈ U) (a b c : Fin (d + 1)) :
      familyChristoffelDeriv (linearFamily σ h) z a b c = linearizedChristoffel σ h z a b c :=
    (hasDerivAt_familyChristoffel (hΓ z hz a b c)).unique
      (hasDerivAt_christoffelOf_linear (hc z hz) a b c)
  have hev (a b c : Fin (d + 1)) :
      (fun z => familyChristoffelDeriv (linearFamily σ h) z a b c) =ᶠ[𝓝 x]
        fun z => linearizedChristoffel σ h z a b c :=
    Filter.eventually_of_mem (U.isOpen.mem_nhds hx) fun z hz => hδ z hz a b c
  rw [linearizedRicci_eq_christoffel hh hs hx, familyRicciDeriv]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [familyChristoffel_linearFamily_zero, mul_zero, zero_mul, add_zero, sub_zero,
    Finset.sum_const_zero, (hev _ _ _).fderiv_eq]

/-- **The derivative theorem.** The derivative in `ε` at `0` of the Ricci tensor of `η + ε h`
is the linearized Ricci tensor. -/
theorem hasDerivAt_ricciOf_linear {U : Opens (MinkowskiModel d)}
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) (hx : x ∈ U) (j k : Fin (d + 1)) :
    HasDerivAt (fun ε : ℝ => ricciOf (fun z => Minkowski.metricMatrix σ d + ε • h z) x j k)
      (linearizedRicci σ h x j k) 0 := by
  have hc (a b : Fin (d + 1)) : ContDiffAt ℝ ∞ (fun w => h w a b) x :=
    (hh a b).contDiffAt (U.isOpen.mem_nhds hx)
  have hΓ (a b c : Fin (d + 1)) :
      ContDiffAt ℝ ∞ (fun q => familyChristoffel (linearFamily σ h) q a b c) ((0 : ℝ), x) :=
    contDiffAt_familyChristoffel (fun a b => contDiffAt_linearFamily hc 0 a b)
      (linearFamily_det_zero x) a b c
  rw [← familyRicciDeriv_linearFamily hh hs hx]
  exact hasDerivAt_familyRicci hΓ j k

/-- The derivative in `ε` at `0` of the scalar curvature of `η + ε h`. -/
theorem hasDerivAt_scalarOf_linear {U : Opens (MinkowskiModel d)}
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) (hx : x ∈ U) :
    HasDerivAt (fun ε : ℝ => scalarOf (fun z => Minkowski.metricMatrix σ d + ε • h z) x)
      (linearizedScalar σ h x) 0 := by
  have hc (a b : Fin (d + 1)) : ContDiffAt ℝ ∞ (fun w => h w a b) x :=
    (hh a b).contDiffAt (U.isOpen.mem_nhds hx)
  have hΓ (a b c : Fin (d + 1)) :
      ContDiffAt ℝ ∞ (fun q => familyChristoffel (linearFamily σ h) q a b c) ((0 : ℝ), x) :=
    contDiffAt_familyChristoffel (fun a b => contDiffAt_linearFamily hc 0 a b)
      (linearFamily_det_zero x) a b c
  have hQ (a c : Fin (d + 1)) : HasDerivAt (fun ε => (linearFamily σ h (ε, x))⁻¹ a c)
      (Matrix.of (fun a c => deriv (fun ε => (linearFamily σ h (ε, x))⁻¹ a c) 0) a c) 0 := by
    have hinv := (contDiffAt_familyInv (fun a b => contDiffAt_linearFamily (σ := σ) hc 0 a b)
      (linearFamily_det_zero x) a c).comp (0 : ℝ)
      ((contDiffAt_id (𝕜 := ℝ)).prodMk (contDiffAt_const (c := x)))
    exact (hinv.differentiableAt (by simp)).hasDerivAt
  have h1 := hasDerivAt_familyScalar hΓ hQ
  simp only [familyRicciDeriv_linearFamily hh hs hx, familyRicci_linearFamily_zero, zero_mul,
    add_zero, linearFamily_zero, metricMatrix_inv] at h1
  have hval : linearizedScalar σ h x =
      ∑ a, ∑ c, linearizedRicci σ h x a c * Minkowski.metricMatrix σ d a c := by
    rw [linearizedScalar]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a (fun b _ hb => by simp [metricMatrix_apply, Ne.symm hb])
      (fun h => absurd (Finset.mem_univ a) h), metricMatrix_apply, ite_eq_left rfl, mul_comm]
  rw [hval]
  exact h1

/-- The derivative in `ε` at `0` of the Einstein tensor of `η + ε h`. -/
theorem hasDerivAt_einsteinOf_linear {U : Opens (MinkowskiModel d)}
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) (hx : x ∈ U) (j k : Fin (d + 1)) :
    HasDerivAt (fun ε : ℝ => einsteinOf (fun z => Minkowski.metricMatrix σ d + ε • h z) x j k)
      (linearizedEinstein σ h x j k) 0 := by
  have hC : HasDerivAt (fun ε : ℝ => (Minkowski.metricMatrix σ d + ε • h x) j k) (h x j k) 0 := by
    have e : (fun ε : ℝ => (Minkowski.metricMatrix σ d + ε • h x) j k) =
        fun ε => Minkowski.metricMatrix σ d j k + ε * h x j k :=
      funext fun ε => by simp
    rw [e]
    convert ((hasDerivAt_id' (0 : ℝ)).mul_const (h x j k)).const_add
      (Minkowski.metricMatrix σ d j k) using 1
    ring
  have h1 := (hasDerivAt_ricciOf_linear (σ := σ) hh hs hx j k).fun_sub
    (((hasDerivAt_scalarOf_linear (σ := σ) hh hs hx).div_const 2).fun_mul hC)
  unfold einsteinOf
  convert h1 using 1
  simp [linearizedEinstein]

end Ricci

/-! ### Actual metrics -/

section Metric

variable {U : Opens (MinkowskiModel d)}
  {h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}

variable (σ) in
/-- **Small perturbations of flat space-time are Lorentz metrics.** If `h` is symmetric and
`|h_{ij}| ≤ M` on `U`, then `η + ε h` has the Lorentz signature on `U` for
`|ε| (d + 1)² M < 1`. -/
theorem isAdmissible_linear (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) {M : ℝ}
    (hM : ∀ z ∈ U, ∀ i j, |h z i j| ≤ M) {ε : ℝ} (hε : |ε| * (((d : ℝ) + 1) ^ 2 * M) < 1) :
    (minkowski σ d U).IsAdmissible (coefficientForm h) ε := by
  intro x hx
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x hx 0 0)
  have hsym : ∀ v w, (minkowskiForm σ d + ε • coefficientForm h x) v w =
      (minkowskiForm σ d + ε • coefficientForm h x) w v := by
    intro v w
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
      coefficientForm_apply, minkowskiForm_symmetric σ v w]
    congr 2
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hs x hx k i]
    ring
  have hB : ∀ u, |(minkowskiForm σ d + ε • coefficientForm h x) u u - minkowskiForm σ d u u| ≤
      (|ε| * (((d : ℝ) + 1) ^ 2 * M)) * ‖u‖ ^ 2 := by
    intro u
    have hb := Minkowski.abs_apply_self_le (ε • coefficientForm h x) u
    simp only [_root_.smul_apply, smul_eq_mul, coefficientForm_single] at hb
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
      add_sub_cancel_left]
    refine hb.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
    calc ∑ i, ∑ j, |ε * h x i j| ≤ ∑ _i : Fin (d + 1), ∑ _j : Fin (d + 1), |ε| * M :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hM x hx i j) (abs_nonneg ε)
      _ = |ε| * (((d : ℝ) + 1) ^ 2 * M) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  refine Minkowski.exists_lorentzFrame_of_near σ (ContinuousLinearEquiv.refl ℝ _)
    (fun v w => rfl) hsym (by positivity) hB ?_
  have hn : ‖((ContinuousLinearEquiv.refl ℝ (MinkowskiModel d)).symm :
      MinkowskiModel d →L[ℝ] MinkowskiModel d)‖ ≤ 1 := by
    rw [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl]
    exact ContinuousLinearMap.norm_id_le
  have hn2 : ‖((ContinuousLinearEquiv.refl ℝ (MinkowskiModel d)).symm :
      MinkowskiModel d →L[ℝ] MinkowskiModel d)‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg ((ContinuousLinearEquiv.refl ℝ (MinkowskiModel d)).symm :
      MinkowskiModel d →L[ℝ] MinkowskiModel d)]
  have hδ0 : 0 ≤ |ε| * (((d : ℝ) + 1) ^ 2 * M) := by positivity
  nlinarith

variable (σ) in
/-- For a bounded symmetric `h`, `η + ε h` has the Lorentz signature on `U` for all `ε`
near `0`. -/
theorem eventually_isAdmissible_linear (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) {M : ℝ}
    (hM : ∀ z ∈ U, ∀ i j, |h z i j| ≤ M) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), (minkowski σ d U).IsAdmissible (coefficientForm h) ε := by
  have hcont : Continuous fun ε : ℝ => |ε| * (((d : ℝ) + 1) ^ 2 * M) :=
    continuous_abs.mul continuous_const
  have ht : Filter.Tendsto (fun ε : ℝ => |ε| * (((d : ℝ) + 1) ^ 2 * M)) (𝓝 0) (𝓝 0) := by
    have := hcont.tendsto 0
    simp only [abs_zero, zero_mul] at this
    exact this
  filter_upwards [ht.eventually (gt_mem_nhds zero_lt_one)] with ε hε
  exact isAdmissible_linear σ hs hM hε

variable (σ) in
/-- The coordinate metric `η + ε h` on `U`, for an admissible `ε`. -/
def linearMetric (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) (ε : ℝ)
    (hε : (minkowski σ d U).IsAdmissible (coefficientForm h) ε) : CoordinateMetric σ d U :=
  (minkowski σ d U).addVariation (coefficientForm h) (contDiffOn_coefficientForm hh) ε hε

/-- The coefficients of `linearMetric` are `η + ε h`. -/
theorem coefficient_linearMetric (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) (ε : ℝ)
    (hε : (minkowski σ d U).IsAdmissible (coefficientForm h) ε) :
    (linearMetric σ hh ε hε).coefficient = fun z => Minkowski.metricMatrix σ d + ε • h z := by
  rw [linearMetric, addVariation_coefficient]
  funext z
  have hf : formCoeff (coefficientForm h) z = h z := by
    ext i j
    simp [formCoeff, coefficientForm_single]
  rw [variationFamily, minkowski_coefficient, hf]
  rfl

open Classical in
variable (σ) in
/-- The family of coordinate metrics `η + ε h` on `U`: `linearMetric` for an admissible `ε`, and
`η` otherwise. -/
def linearMetricFamily (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) (ε : ℝ) :
    CoordinateMetric σ d U :=
  if hε : (minkowski σ d U).IsAdmissible (coefficientForm h) ε then linearMetric σ hh ε hε
  else minkowski σ d U

/-- For a bounded symmetric `h`, the coefficients of the family are `η + ε h` for all `ε`
near `0`. -/
theorem eventually_coefficient_linearMetricFamily
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i)
    {M : ℝ} (hM : ∀ z ∈ U, ∀ i j, |h z i j| ≤ M) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), (linearMetricFamily σ hh ε).coefficient =
      fun z => Minkowski.metricMatrix σ d + ε • h z := by
  filter_upwards [eventually_isAdmissible_linear σ hs hM] with ε hε
  rw [linearMetricFamily, dite_eq_left hε, coefficient_linearMetric]

/-- **The linearized Ricci tensor is the derivative of the Ricci tensor of an actual family of
Lorentz metrics**: of the native Ricci tensor of `linearMetricFamily`, on the co-ordinate
fields. -/
theorem hasDerivAt_ricci_linearMetricFamily
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i)
    {M : ℝ} (hM : ∀ z ∈ U, ∀ i j, |h z i j| ≤ M) (x : U) (j k : Fin (d + 1)) :
    HasDerivAt (fun ε => (linearMetricFamily σ hh ε).toLorentzMetric.ricci x
        (chartField (physicalChart x) (Pi.single j 1) x)
        (chartField (physicalChart x) (Pi.single k 1) x))
      (linearizedRicci σ h x j k) 0 := by
  refine (hasDerivAt_ricciOf_linear hh hs x.property j k).congr_of_eventuallyEq ?_
  filter_upwards [eventually_coefficient_linearMetricFamily hh hs hM] with ε hε
  rw [toLorentzMetric_ricci_chartField, hε]

/-- The linearized Einstein tensor is the derivative of the native Einstein tensor of
`linearMetricFamily`, on the co-ordinate fields. -/
theorem hasDerivAt_einstein_linearMetricFamily
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i)
    {M : ℝ} (hM : ∀ z ∈ U, ∀ i j, |h z i j| ≤ M) (x : U) (j k : Fin (d + 1)) :
    HasDerivAt (fun ε => (linearMetricFamily σ hh ε).toLorentzMetric.einstein x
        (chartField (physicalChart x) (Pi.single j 1) x)
        (chartField (physicalChart x) (Pi.single k 1) x))
      (linearizedEinstein σ h x j k) 0 := by
  refine (hasDerivAt_einsteinOf_linear hh hs x.property j k).congr_of_eventuallyEq ?_
  filter_upwards [eventually_coefficient_linearMetricFamily hh hs hM] with ε hε
  rw [toLorentzMetric_einstein_chartField, hε]

end Metric

/-! ### Gauge invariance -/

section Gauge

variable {h h' : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}

/-- The Lie derivative of the Minkowski coefficients along the field with the components `ξ^k`:
`(L_ξ η)_{ij} = ∂_i ξ_j + ∂_j ξ_i` with `ξ_j = η_{jj} ξ^j`. -/
theorem lieOf_metricMatrix (ξ : MinkowskiModel d → MinkowskiModel d) (y : MinkowskiModel d)
    (i j : Fin (d + 1)) :
    lieOf (fun _ => Minkowski.metricMatrix σ d) ξ y i j =
      lorentzSign σ j * fderiv ℝ (fun z => ξ z j) y (Pi.single i 1) +
        lorentzSign σ i * fderiv ℝ (fun z => ξ z i) y (Pi.single j 1) := by
  simp [lieOf, metricMatrix_apply]

/-- The linearized Ricci tensor is additive. -/
theorem linearizedRicci_add (hh : ∀ i j, ContDiffAt ℝ ∞ (fun z => h z i j) x)
    (hh' : ∀ i j, ContDiffAt ℝ ∞ (fun z => h' z i j) x) (j k : Fin (d + 1)) :
    linearizedRicci σ (fun z => h z + h' z) x j k =
      linearizedRicci σ h x j k + linearizedRicci σ h' x j k := by
  unfold linearizedRicci
  simp only [Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [secondPartial_add (hh _ _) (hh' _ _), secondPartial_add (hh _ _) (hh' _ _),
    secondPartial_add (hh _ _) (hh' _ _), secondPartial_add (hh _ _) (hh' _ _)]
  ring

/-- **The gauge terms have no linearized curvature**: `δR(L_ξ η) = 0`. -/
theorem linearizedRicci_lie {ξ : MinkowskiModel d → MinkowskiModel d}
    (hξ : ∀ m, ContDiffAt ℝ ∞ (fun z => ξ z m) x) (j k : Fin (d + 1)) :
    linearizedRicci σ (fun z => Matrix.of (lieOf (fun _ => Minkowski.metricMatrix σ d) ξ z)) x
      j k = 0 := by
  have hp (m c : Fin (d + 1)) :
      ContDiffAt ℝ ∞ (fun z => fderiv ℝ (fun w => ξ w m) z (Pi.single c 1)) x :=
    contDiffAt_fderiv_apply (hξ m) _
  have hcm (m c : Fin (d + 1)) (s : ℝ) :
      ContDiffAt ℝ ∞ (fun z => s * fderiv ℝ (fun w => ξ w m) z (Pi.single c 1)) x :=
    contDiffAt_const.mul (hp m c)
  have hG (a b e c : Fin (d + 1)) :
      secondPartial (fun z => Matrix.of (lieOf (fun _ => Minkowski.metricMatrix σ d) ξ z) a b)
        x e c =
      lorentzSign σ b * secondPartial (fun z => fderiv ℝ (fun w => ξ w b) z (Pi.single a 1))
          x e c +
        lorentzSign σ a * secondPartial (fun z => fderiv ℝ (fun w => ξ w a) z (Pi.single b 1))
          x e c := by
    simp only [Matrix.of_apply, lieOf_metricMatrix]
    rw [secondPartial_add (hcm _ _ _) (hcm _ _ _), secondPartial_const_mul (hp _ _),
      secondPartial_const_mul (hp _ _)]
  have hin (m a b c : Fin (d + 1)) :=
    secondPartial_fderiv_swap (f := fun w => ξ w m) (x := x) (hξ m) a b c
  have hout (m a b c : Fin (d + 1)) :=
    secondPartial_comm (f := fun z => fderiv ℝ (fun w => ξ w m) z (Pi.single c 1))
      ((hp m c).of_le (by simp)) a b
  unfold linearizedRicci
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hG, hG, hG, hG, hin k i j i, hin j i k i, hin i i k j, hout i i j k, hin i j i k]
  ring

/-- **Gauge invariance of the linearized Ricci tensor**: for components `ξ^k` smooth on `U`,
`δR(h + L_ξ η) = δR(h)`. -/
theorem linearizedRicci_add_lie {U : Opens (MinkowskiModel d)}
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) {ξ : MinkowskiModel d → MinkowskiModel d}
    (hξ : ContDiffOn ℝ ∞ ξ U) (hx : x ∈ U) (j k : Fin (d + 1)) :
    linearizedRicci σ
        (fun z => h z + Matrix.of (lieOf (fun _ => Minkowski.metricMatrix σ d) ξ z)) x j k =
      linearizedRicci σ h x j k := by
  have hξx (m : Fin (d + 1)) : ContDiffAt ℝ ∞ (fun z => ξ z m) x :=
    contDiffAt_pi.1 (hξ.contDiffAt (U.isOpen.mem_nhds hx)) m
  have hL (a b : Fin (d + 1)) : ContDiffAt ℝ ∞
      (fun z => Matrix.of (lieOf (fun _ => Minkowski.metricMatrix σ d) ξ z) a b) x := by
    simp only [Matrix.of_apply, lieOf_metricMatrix]
    exact (contDiffAt_const.mul (contDiffAt_fderiv_apply (hξx b) _)).add
      (contDiffAt_const.mul (contDiffAt_fderiv_apply (hξx a) _))
  rw [linearizedRicci_add (fun a b => (hh a b).contDiffAt (U.isOpen.mem_nhds hx)) hL,
    linearizedRicci_lie hξx, add_zero]

/-- Gauge invariance of the linearized Einstein tensor. -/
theorem linearizedEinstein_add_lie {U : Opens (MinkowskiModel d)}
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) {ξ : MinkowskiModel d → MinkowskiModel d}
    (hξ : ContDiffOn ℝ ∞ ξ U) (hx : x ∈ U) (j k : Fin (d + 1)) :
    linearizedEinstein σ
        (fun z => h z + Matrix.of (lieOf (fun _ => Minkowski.metricMatrix σ d) ξ z)) x j k =
      linearizedEinstein σ h x j k := by
  simp only [linearizedEinstein, linearizedScalar, linearizedRicci_add_lie hh hξ hx]

end Gauge

/-! ### The harmonic gauge -/

section Harmonic

variable {h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}

variable (σ) in
/-- The trace `tr A = η^{ab} A_{ab}` of a matrix with the Minkowski coefficients. -/
def flatTrace (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) : ℝ :=
  ∑ a, lorentzSign σ a * A a a

variable (σ) in
/-- The trace reverse `Ā = A − ½ η tr A`. -/
def traceReverse (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  A - (flatTrace σ A / 2) • Minkowski.metricMatrix σ d

/-- The entries `Ā_{ab} = A_{ab} − ½ tr A η_{ab}` of the trace reverse. -/
theorem traceReverse_apply (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (a b : Fin (d + 1)) :
    traceReverse σ A a b = A a b - flatTrace σ A / 2 * Minkowski.metricMatrix σ d a b := by
  simp [traceReverse]

/-- The trace is additive. -/
theorem flatTrace_add (A B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    flatTrace σ (A + B) = flatTrace σ A + flatTrace σ B := by
  simp [flatTrace, mul_add, Finset.sum_add_distrib]

/-- The trace is homogeneous. -/
theorem flatTrace_smul (c : ℝ) (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    flatTrace σ (c • A) = c * flatTrace σ A := by
  simp only [flatTrace, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- The trace reverse is additive. -/
theorem traceReverse_add (A B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    traceReverse σ (A + B) = traceReverse σ A + traceReverse σ B :=
  Matrix.ext fun i j => by
    simp only [traceReverse_apply, Matrix.add_apply, flatTrace_add]
    ring

/-- The trace reverse is homogeneous. -/
theorem traceReverse_smul (c : ℝ) (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    traceReverse σ (c • A) = c • traceReverse σ A :=
  Matrix.ext fun i j => by
    simp only [traceReverse_apply, Matrix.smul_apply, smul_eq_mul, flatTrace_smul]
    ring

/-- The trace of the trace reverse: `tr Ā = (1 − (d + 1)/2) tr A`. -/
theorem flatTrace_traceReverse (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    flatTrace σ (traceReverse σ A) = (1 - ((d : ℝ) + 1) / 2) * flatTrace σ A := by
  have h (a : Fin (d + 1)) : lorentzSign σ a * traceReverse σ A a a =
      lorentzSign σ a * A a a - flatTrace σ A / 2 := by
    rw [traceReverse_apply, metricMatrix_apply, ite_eq_left rfl]
    linear_combination (-(flatTrace σ A / 2)) * lorentzSign_sq σ a
  have hA : ∑ a, lorentzSign σ a * A a a = flatTrace σ A := rfl
  rw [flatTrace, Finset.sum_congr rfl fun a _ => h a, Finset.sum_sub_distrib, hA]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- In four dimensions the trace reverse is an involution: `tr Ā = −tr A` and `Ā̄ = A`. -/
theorem traceReverse_traceReverse (A : Matrix (Fin 4) (Fin 4) ℝ) :
    traceReverse σ (traceReverse σ A) = A :=
  Matrix.ext fun i j => by
    rw [traceReverse_apply, flatTrace_traceReverse, traceReverse_apply]
    norm_num
    ring

variable (σ) in
/-- The flat wave operator `□f = Σ_a η^{aa} ∂_a ∂_a f`. -/
def flatBox (f : MinkowskiModel d → ℝ) (x : MinkowskiModel d) : ℝ :=
  ∑ a, lorentzSign σ a * secondPartial f x a a

variable (σ) in
/-- The harmonic gauge `Σ_a η^{aa} ∂_a h̄_{ab} = 0` on `U`. -/
def IsHarmonicGauge (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (U : Opens (MinkowskiModel d)) : Prop :=
  ∀ x ∈ U, ∀ b, ∑ a, lorentzSign σ a *
    fderiv ℝ (fun z => traceReverse σ (h z) a b) x (Pi.single a 1) = 0

/-- The trivial instance: `h = 0` is in harmonic gauge. -/
theorem isHarmonicGauge_zero (U : Opens (MinkowskiModel d)) : IsHarmonicGauge σ (fun _ => 0) U := by
  intro x _ b
  simp [traceReverse_apply, flatTrace]

/-- The trace of a field smooth at `x` is smooth at `x`. -/
theorem contDiffAt_flatTrace (hh : ∀ i j, ContDiffAt ℝ ∞ (fun z => h z i j) x) :
    ContDiffAt ℝ ∞ (fun z => flatTrace σ (h z)) x := by
  simp only [flatTrace]
  exact ContDiffAt.sum fun a _ => contDiffAt_const.mul (hh a a)

/-- The second derivatives of the trace are the traces of the second derivatives. -/
theorem secondPartial_flatTrace (hh : ∀ i j, ContDiffAt ℝ ∞ (fun z => h z i j) x)
    (a b : Fin (d + 1)) :
    secondPartial (fun z => flatTrace σ (h z)) x a b =
      ∑ c, lorentzSign σ c * secondPartial (fun z => h z c c) x a b := by
  simp only [flatTrace]
  exact secondPartial_sum_mul Finset.univ (fun c _ => hh c c) _ a b

/-- In harmonic gauge, `Σ_a η^{aa} ∂_a h_{ab} = ½ ∂_b tr h` on `U`. -/
theorem sum_fderiv_of_isHarmonicGauge {U : Opens (MinkowskiModel d)}
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) (hg : IsHarmonicGauge σ h U)
    {z : MinkowskiModel d} (hz : z ∈ U) (b : Fin (d + 1)) :
    ∑ a, lorentzSign σ a * fderiv ℝ (fun w => h w a b) z (Pi.single a 1) =
      1 / 2 * fderiv ℝ (fun w => flatTrace σ (h w)) z (Pi.single b 1) := by
  have hc (i j : Fin (d + 1)) : ContDiffAt ℝ ∞ (fun w => h w i j) z :=
    (hh i j).contDiffAt (U.isOpen.mem_nhds hz)
  have hd (i j : Fin (d + 1)) : DifferentiableAt ℝ (fun w => h w i j) z :=
    (hc i j).differentiableAt (by simp)
  have ht : DifferentiableAt ℝ (fun w => flatTrace σ (h w)) z :=
    (contDiffAt_flatTrace hc).differentiableAt (by simp)
  have h0 := hg z hz b
  have hfd (a : Fin (d + 1)) :
      fderiv ℝ (fun w => traceReverse σ (h w) a b) z (Pi.single a 1) =
        fderiv ℝ (fun w => h w a b) z (Pi.single a 1) - Minkowski.metricMatrix σ d a b *
          (1 / 2 * fderiv ℝ (fun w => flatTrace σ (h w)) z (Pi.single a 1)) := by
    have e : (fun w => traceReverse σ (h w) a b) = fun w => h w a b -
        Minkowski.metricMatrix σ d a b * (1 / 2 * flatTrace σ (h w)) :=
      funext fun w => by rw [traceReverse_apply]; ring
    rw [e, fderiv_fun_sub (hd a b) ((ht.const_mul _).const_mul _),
      fderiv_const_mul (ht.const_mul _), fderiv_const_mul ht]
    simp only [_root_.sub_apply, _root_.smul_apply, smul_eq_mul]
  simp only [hfd, mul_sub, Finset.sum_sub_distrib, sum_lorentzSign_mul_metricMatrix
    (fun a => 1 / 2 * fderiv ℝ (fun w => flatTrace σ (h w)) z (Pi.single a 1)) b] at h0
  linarith

/-- In harmonic gauge, `Σ_i η^{ii} ∂_i ∂_j h_{ik} = ½ ∂_j ∂_k tr h`. -/
theorem sum_secondPartial_of_isHarmonicGauge {U : Opens (MinkowskiModel d)}
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) (hg : IsHarmonicGauge σ h U)
    (hx : x ∈ U) (j k : Fin (d + 1)) :
    ∑ i, lorentzSign σ i * secondPartial (fun z => h z i k) x i j =
      1 / 2 * secondPartial (fun z => flatTrace σ (h z)) x j k := by
  have hc (i l : Fin (d + 1)) : ContDiffAt ℝ ∞ (fun w => h w i l) x :=
    (hh i l).contDiffAt (U.isOpen.mem_nhds hx)
  have hev : (fun z => ∑ i, lorentzSign σ i * fderiv ℝ (fun w => h w i k) z (Pi.single i 1))
      =ᶠ[𝓝 x] fun z => 1 / 2 * fderiv ℝ (fun w => flatTrace σ (h w)) z (Pi.single k 1) :=
    Filter.eventually_of_mem (U.isOpen.mem_nhds hx)
      fun z hz => sum_fderiv_of_isHarmonicGauge hh hg hz k
  have hl : ∑ i, lorentzSign σ i * secondPartial (fun z => h z i k) x i j =
      fderiv ℝ (fun z => ∑ i, lorentzSign σ i * fderiv ℝ (fun w => h w i k) z (Pi.single i 1))
        x (Pi.single j 1) := by
    rw [fderiv_sum_mul_apply Finset.univ
      (fun i _ => differentiableAt_partial (hc i k) _)]
    exact Finset.sum_congr rfl fun i _ => by rw [secondPartial_comm ((hc i k).of_le (by simp))]; rfl
  rw [hl, hev.fderiv_eq, fderiv_const_mul
    (differentiableAt_partial (contDiffAt_flatTrace hc) _),
    _root_.smul_apply, smul_eq_mul]
  rfl

/-- **The linearized Ricci tensor in harmonic gauge**: `δR_{jk} = −½ □h_{jk}`. -/
theorem linearizedRicci_of_isHarmonicGauge {U : Opens (MinkowskiModel d)}
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) (hg : IsHarmonicGauge σ h U)
    (hx : x ∈ U) (j k : Fin (d + 1)) :
    linearizedRicci σ h x j k = -flatBox σ (fun z => h z j k) x / 2 := by
  have hc (i l : Fin (d + 1)) : ContDiffAt ℝ ∞ (fun w => h w i l) x :=
    (hh i l).contDiffAt (U.isOpen.mem_nhds hx)
  have h1 := sum_secondPartial_of_isHarmonicGauge hh hg hx j k
  have h2 := sum_secondPartial_of_isHarmonicGauge hh hg hx k j
  have h3 := secondPartial_flatTrace (σ := σ) hc j k
  rw [secondPartial_comm ((contDiffAt_flatTrace hc).of_le (by simp)) k j] at h2
  have hsplit : linearizedRicci σ h x j k =
      ((∑ i, lorentzSign σ i * secondPartial (fun z => h z i k) x i j) +
        (∑ i, lorentzSign σ i * secondPartial (fun z => h z i j) x i k) -
        flatBox σ (fun z => h z j k) x -
        ∑ i, lorentzSign σ i * secondPartial (fun z => h z i i) x j k) / 2 := by
    rw [linearizedRicci, flatBox, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit, h1, h2, ← h3]
  ring

/-- The wave operator of the trace reverse: `□h̄_{jk} = □h_{jk} − ½ η_{jk} Σ_a η^{aa} □h_{aa}`. -/
theorem flatBox_traceReverse (hh : ∀ i j, ContDiffAt ℝ ∞ (fun z => h z i j) x)
    (j k : Fin (d + 1)) :
    flatBox σ (fun z => traceReverse σ (h z) j k) x = flatBox σ (fun z => h z j k) x -
      Minkowski.metricMatrix σ d j k / 2 *
        ∑ a, lorentzSign σ a * flatBox σ (fun z => h z a a) x := by
  have e : (fun z => traceReverse σ (h z) j k) =
      fun z => h z j k - Minkowski.metricMatrix σ d j k / 2 * flatTrace σ (h z) :=
    funext fun z => by rw [traceReverse_apply]; ring
  have hb (c : Fin (d + 1)) : secondPartial (fun z => traceReverse σ (h z) j k) x c c =
      secondPartial (fun z => h z j k) x c c - Minkowski.metricMatrix σ d j k / 2 *
        ∑ a, lorentzSign σ a * secondPartial (fun z => h z a a) x c c := by
    rw [e, secondPartial_sub (hh j k) (contDiffAt_const.mul (contDiffAt_flatTrace hh)),
      secondPartial_const_mul (contDiffAt_flatTrace hh), secondPartial_flatTrace hh]
  simp only [flatBox, hb, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring

/-- **The linearized Einstein tensor in harmonic gauge**: `δG_{jk} = −½ □h̄_{jk}`. -/
theorem linearizedEinstein_of_isHarmonicGauge {U : Opens (MinkowskiModel d)}
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) (hg : IsHarmonicGauge σ h U)
    (hx : x ∈ U) (j k : Fin (d + 1)) :
    linearizedEinstein σ h x j k = -flatBox σ (fun z => traceReverse σ (h z) j k) x / 2 := by
  have hc (i l : Fin (d + 1)) : ContDiffAt ℝ ∞ (fun w => h w i l) x :=
    (hh i l).contDiffAt (U.isOpen.mem_nhds hx)
  rw [flatBox_traceReverse hc, linearizedEinstein, linearizedScalar]
  simp only [linearizedRicci_of_isHarmonicGauge hh hg hx]
  have hterm (a : Fin (d + 1)) : lorentzSign σ a * (-flatBox σ (fun z => h z a a) x / 2) =
      -1 / 2 * (lorentzSign σ a * flatBox σ (fun z => h z a a) x) := by ring
  simp only [hterm, ← Finset.mul_sum]
  ring

end Harmonic

end CoordinateMetric

end ProjectAinos.SmoothGeometry
