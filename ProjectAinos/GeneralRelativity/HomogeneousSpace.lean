/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateFrame
public import ProjectAinos.GeneralRelativity.FLRW
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Homogeneous cosmological models

Landau–Lifshitz, §116, in the co-ordinates `(t, x¹, x², x³) = (x 0, x 1, x 2, x 3)`, the
signature `(−+++)` and `c = 1`.

An **invariant frame** (`InvariantFrame`) on a nonempty open set `V` of the spatial co-ordinates
is a triple of vector fields `X_a` with components smooth on `V`, a dual triple of one-forms
`ω^a` (`ω^a(X_b) = δ^a_b`), and constants `C^c_{ab}` with `[X_a, X_b] = Σ_c C^c_{ab} X_c` on `V`.
For a homogeneous space these are the generators of the motions and the structure constants of
their group; here the frame is given as data and no group is constructed.

The model (`Data`) adds an open set `I` of times and a **triad** `e(t)`, an invertible matrix
smooth on `I` with the inverse `f(t)`, also smooth. The metric is
`ds² = −dt² + Σ_k (θ^k)²` with the spatial coframe `θ^k = Σ_a e_{ka}(t) ω^a`, that is
`γ_{ab}(t) = Σ_k e_{ka} e_{kb}` in the invariant frame (L&L (116.1) in the synchronous
reference system).

* `metric`: the Lorentz metric on the domain `t ∈ I`, `x ∈ V`.
* `frameField`, `form_frameField`, `frame`: `E₀ = ∂_t` and `E_i = Σ_a f_{ai}(t) X_a` are an
  orthonormal frame.
* `bracket_zero_succ`, `bracket_succ_succ`, `commutator_frame`: the commutators
  `[E₀, E_j] = Σ_a ḟ_{aj} X_a` and `[E_i, E_j] = Σ_c (Σ_{ab} f_{ai} f_{bj} C^c_{ab}) X_c`, so the
  commutator coefficients `λ_{abc} = g(E_a, [E_b, E_c])` are functions of the time alone (`lam`):
  `λ_{k0j} = (e ḟ)_{kj}` and `λ_{kij} = Σ_c e_{kc} Σ_{ab} f_{ai} f_{bj} C^c_{ab}`.
* `ricci_frame`: **the reduction of the Ricci tensor**. Its frame components at a point are
  `frameRicci` at the time of the point, an expression in the commutator coefficients and their
  time derivatives (Cartan's structure equations with `γ_{abc} = ½ (λ_{abc} + λ_{bca} − λ_{cab})`).
* `ricci_eq_zero_iff`: **the vacuum equations reduce to ordinary differential equations**: the
  Ricci tensor vanishes on the whole domain if and only if `frameRicci t b k = 0` for all times
  `t ∈ I`.
* `fluid`, `einstein_iff`: with a comoving perfect fluid `T = (ρ + p) u ⊗ u + p g`, `u = ∂_t`,
  the Einstein equations `G + Λ g = κ T` hold on the domain if and only if the frame equations
  `R_{ab} − ½ R η_{ab} + Λ η_{ab} = κ diag(ρ, p, p, p)_{ab}` hold for all `t ∈ I`.
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap Set TopologicalSpace Filter
open scoped ContDiff Topology Manifold

namespace ProjectAinos.GeneralRelativity.HomogeneousSpace

open SmoothGeometry CoordinateMetric LorentzMetric

local notation "E" => MinkowskiModel 3

/-! ### Space and space-time -/

/-- The spatial co-ordinates `(x¹, x², x³)` of a point. -/
def spatial : E →L[ℝ] (Fin 3 → ℝ) := ContinuousLinearMap.pi fun α => proj α.succ

@[simp] theorem spatial_apply (z : E) (α : Fin 3) : spatial z α = z α.succ := rfl

/-- A spatial vector as a vector of space-time with zero time component. -/
def ofSpatial : (Fin 3 → ℝ) →L[ℝ] E :=
  ContinuousLinearMap.pi fun i => Fin.cases (motive := fun _ => (Fin 3 → ℝ) →L[ℝ] ℝ) 0
    (fun α => proj α) i

@[simp] theorem ofSpatial_zero (v : Fin 3 → ℝ) : ofSpatial v 0 = 0 := rfl

@[simp] theorem ofSpatial_succ (v : Fin 3 → ℝ) (α : Fin 3) : ofSpatial v α.succ = v α := rfl

@[simp] theorem spatial_ofSpatial (v : Fin 3 → ℝ) : spatial (ofSpatial v) = v := rfl

/-- The unit vector `∂_t`. -/
def timeUnit : E := Pi.single 0 1

@[simp] theorem timeUnit_zero : timeUnit 0 = 1 := by simp [timeUnit]

@[simp] theorem timeUnit_succ (α : Fin 3) : timeUnit α.succ = 0 := by simp [timeUnit]

@[simp] theorem spatial_timeUnit : spatial timeUnit = 0 := by
  funext α
  simp

/-! ### Invariant frames and the data -/

/-- **An invariant frame** on a nonempty open set `V` of the spatial co-ordinates: vector fields
`X_a` (`field a`) and one-forms `ω^a` (`coframe a`) with components smooth on `V`, dual to each
other, and constants `C^c_{ab}` (`C c a b`) with `[X_a, X_b] = Σ_c C^c_{ab} X_c` on `V`, the
bracket being `[X, Y]^α = X^β ∂_β Y^α − Y^β ∂_β X^α`. -/
structure InvariantFrame where
  /-- The open set of the spatial co-ordinates. -/
  V : Set (Fin 3 → ℝ)
  /-- The set is open. -/
  isOpen : IsOpen V
  /-- The set is nonempty. -/
  nonempty : V.Nonempty
  /-- The components `X_a^α` of the frame. -/
  field : Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ)
  /-- The components `ω^a_α` of the dual coframe. -/
  coframe : Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ)
  /-- The structure constants `C^c_{ab}`, indexed `C c a b`. -/
  C : Fin 3 → Fin 3 → Fin 3 → ℝ
  /-- The fields are smooth on `V`. -/
  smooth_field : ∀ a, ContDiffOn ℝ ∞ (field a) V
  /-- The one-forms are smooth on `V`. -/
  smooth_coframe : ∀ a, ContDiffOn ℝ ∞ (coframe a) V
  /-- Duality: `ω^a(X_b) = δ^a_b`. -/
  coframe_field : ∀ s ∈ V, ∀ a b, ∑ α, coframe a s α * field b s α = if a = b then 1 else 0
  /-- The brackets: `[X_a, X_b] = Σ_c C^c_{ab} X_c`. -/
  bracket : ∀ s ∈ V, ∀ a b,
    fderiv ℝ (field b) s (field a s) - fderiv ℝ (field a) s (field b s) = ∑ c, C c a b • field c s

/-- **The data of a homogeneous model**: an invariant frame, an open set `I` of times and a
triad `e(t)` (`triad t k a = e_{ka}`), smooth on `I`, with an inverse `f(t)` (`triadInv`), smooth
on `I`. The spatial metric is `γ_{ab} = Σ_k e_{ka} e_{kb}` in the invariant frame. -/
structure Data where
  /-- The invariant frame. -/
  F : InvariantFrame
  /-- The open set of times. -/
  I : Set ℝ
  /-- The set of times is open. -/
  isOpen_I : IsOpen I
  /-- The triad `e(t)`. -/
  triad : ℝ → Matrix (Fin 3) (Fin 3) ℝ
  /-- Its inverse `f(t)`. -/
  triadInv : ℝ → Matrix (Fin 3) (Fin 3) ℝ
  /-- The triad is smooth on `I`. -/
  smooth_triad : ∀ k a, ContDiffOn ℝ ∞ (fun t => triad t k a) I
  /-- The inverse is smooth on `I`. -/
  smooth_triadInv : ∀ a i, ContDiffOn ℝ ∞ (fun t => triadInv t a i) I
  /-- `e(t) f(t) = 1` on `I`. -/
  triad_mul : ∀ t ∈ I, triad t * triadInv t = 1

namespace Data

variable (D : Data)

/-- The domain `t ∈ I`, `x ∈ V`. -/
def domain : Opens E :=
  ⟨{z | z 0 ∈ D.I ∧ spatial z ∈ D.F.V},
    (D.isOpen_I.preimage (continuous_apply 0)).inter (D.F.isOpen.preimage spatial.continuous)⟩

variable {D}

theorem time_mem {z : E} (hz : z ∈ D.domain) : z 0 ∈ D.I := hz.1

theorem spatial_mem {z : E} (hz : z ∈ D.domain) : spatial z ∈ D.F.V := hz.2

/-- The point with the time `t` and the spatial co-ordinates `s`. -/
def point (t : ℝ) (s : Fin 3 → ℝ) : E := Fin.cons t s

@[simp] theorem point_zero (t : ℝ) (s : Fin 3 → ℝ) : point t s 0 = t := rfl

@[simp] theorem spatial_point (t : ℝ) (s : Fin 3 → ℝ) : spatial (point t s) = s := rfl

theorem point_mem {t : ℝ} {s : Fin 3 → ℝ} (ht : t ∈ D.I) (hs : s ∈ D.F.V) :
    point t s ∈ D.domain := ⟨ht, hs⟩

/-- `f(t) e(t) = 1` on `I`. -/
theorem triadInv_mul {t : ℝ} (ht : t ∈ D.I) : D.triadInv t * D.triad t = 1 :=
  mul_eq_one_comm.mp (D.triad_mul t ht)

/-! ### The metric -/

variable (D) in
/-- The spatial orthonormal coframe `θ^k_α(z) = Σ_a e_{ka}(t) ω^a_α(x)`. -/
def theta (z : E) (k α : Fin 3) : ℝ := ∑ a, D.triad (z 0) k a * D.F.coframe a (spatial z) α

variable (D) in
/-- The one-form `θ^k` at a point, on space-time vectors. -/
def thetaForm (z : E) (k : Fin 3) : E →L[ℝ] ℝ := ∑ α, D.theta z k α • (proj α.succ : E →L[ℝ] ℝ)

theorem thetaForm_apply (z v : E) (k : Fin 3) :
    D.thetaForm z k v = ∑ α, D.theta z k α * v α.succ := by
  simp [thetaForm, _root_.sum_apply, smul_eq_mul]

variable (D) in
/-- The form `−dt ⊗ dt + Σ_k θ^k ⊗ θ^k` at a point. -/
def form (z : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  -((proj 0 : E →L[ℝ] ℝ).smulRight (proj 0 : E →L[ℝ] ℝ)) +
    ∑ k, (D.thetaForm z k).smulRight (D.thetaForm z k)

theorem form_apply (z v w : E) :
    D.form z v w = -(v 0 * w 0) + ∑ k, D.thetaForm z k v * D.thetaForm z k w := by
  simp [form, _root_.sum_apply, smul_eq_mul]

theorem form_symm (z v w : E) : D.form z v w = D.form z w v := by
  rw [form_apply, form_apply]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem contDiffOn_time_triad (k a : Fin 3) :
    ContDiffOn ℝ ∞ (fun z : E => D.triad (z 0) k a) D.domain :=
  (D.smooth_triad k a).comp (contDiff_apply ℝ (fun _ => ℝ) 0).contDiffOn fun _ hz => time_mem hz

theorem contDiffOn_coframe (a α : Fin 3) :
    ContDiffOn ℝ ∞ (fun z : E => D.F.coframe a (spatial z) α) D.domain := by
  have h := (D.F.smooth_coframe a).comp spatial.contDiff.contDiffOn fun _ hz => spatial_mem hz
  exact (contDiff_apply ℝ (fun _ : Fin 3 => ℝ) α).comp_contDiffOn h

theorem contDiffOn_theta (k α : Fin 3) :
    ContDiffOn ℝ ∞ (fun z : E => D.theta z k α) D.domain := by
  unfold theta
  exact ContDiffOn.sum fun a _ => (contDiffOn_time_triad k a).mul (contDiffOn_coframe a α)

theorem contDiffOn_form : ContDiffOn ℝ ∞ D.form D.domain := by
  refine contDiffOn_clm_apply.mpr fun v => contDiffOn_clm_apply.mpr fun w => ?_
  simp only [form_apply, thetaForm_apply]
  refine contDiffOn_const.add (ContDiffOn.sum fun k _ => ?_)
  exact (ContDiffOn.sum fun α _ => (contDiffOn_theta k α).mul contDiffOn_const).mul
    (ContDiffOn.sum fun α _ => (contDiffOn_theta k α).mul contDiffOn_const)

/-- `θ^k(X_c) = e_{kc}`. -/
theorem theta_field {z : E} (hz : z ∈ D.domain) (k c : Fin 3) :
    ∑ α, D.theta z k α * D.F.field c (spatial z) α = D.triad (z 0) k c := by
  have hd := D.F.coframe_field (spatial z) (spatial_mem hz)
  simp only [theta, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum, hd, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- `θ^k` on a combination of the frame: `θ^k(Σ_c μ_c X_c) = Σ_c e_{kc} μ_c`. -/
theorem thetaForm_ofSpatial {z : E} (hz : z ∈ D.domain) (k : Fin 3) (μ : Fin 3 → ℝ) :
    D.thetaForm z k (ofSpatial (∑ c, μ c • D.F.field c (spatial z))) =
      ∑ c, D.triad (z 0) k c * μ c := by
  rw [thetaForm_apply]
  simp only [ofSpatial_succ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← theta_field hz k c, Finset.sum_mul]
  exact Finset.sum_congr rfl fun α _ => by ring

open Matrix in
/-- `θ` is injective on spatial vectors: if `θ^k(v) = 0` for all `k`, then `v = 0`. -/
theorem eq_zero_of_theta {z : E} (hz : z ∈ D.domain) {v : Fin 3 → ℝ}
    (hv : ∀ k, ∑ α, D.theta z k α * v α = 0) : v = 0 := by
  set W : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun a α => D.F.coframe a (spatial z) α
  set X : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun α b => D.F.field b (spatial z) α
  have hWX : W * X = 1 := by
    ext a b
    simp only [W, X, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    exact D.F.coframe_field _ (spatial_mem hz) a b
  have hXW : X * W = 1 := mul_eq_one_comm.mp hWX
  have hθ : D.triad (z 0) *ᵥ (W *ᵥ v) = 0 := by
    funext k
    have h := hv k
    simp only [theta, Finset.sum_mul] at h
    rw [Finset.sum_comm] at h
    simp only [Matrix.mulVec, dotProduct, W, Matrix.of_apply, Pi.zero_apply, Finset.mul_sum]
    rw [← h]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun α _ => by ring
  have hWv : W *ᵥ v = 0 := by
    have h := congrArg (fun u => D.triadInv (z 0) *ᵥ u) hθ
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h
    rwa [← Matrix.mul_assoc, triadInv_mul (time_mem hz), Matrix.one_mul] at h
  have h := congrArg (fun u => X *ᵥ u) hWv
  simpa [Matrix.mulVec_mulVec, hXW] using h

variable (D) in
/-- **The metric of the homogeneous model** `ds² = −dt² + Σ_k (θ^k)²` on the domain. -/
def metric : CoordinateMetric .timeNegative 3 D.domain :=
  ofCriterion D.form contDiffOn_form (fun z _ v w => form_symm z v w)
    (fun z _ => by
      rw [form_apply]
      simp [thetaForm_apply, LorentzConvention.timeSign_timeNegative])
    (fun z hz v hv => by
      rw [form_apply]
      simp only [Fin.cons_zero, mul_zero, neg_zero, zero_add,
        LorentzConvention.timeSign_timeNegative,
        neg_neg, one_mul, thetaForm_apply, Fin.cons_succ]
      by_contra hlt
      have hle := not_lt.mp hlt
      have hzero : ∀ k, ∑ α, D.theta z k α * v α = 0 := by
        have hsq : ∀ k ∈ Finset.univ, 0 ≤ (∑ α, D.theta z k α * v α) *
            (∑ α, D.theta z k α * v α) := fun k _ => mul_self_nonneg _
        have h0 := (Finset.sum_eq_zero_iff_of_nonneg hsq).mp
          (le_antisymm hle (Finset.sum_nonneg hsq))
        intro k
        exact mul_self_eq_zero.mp (h0 k (Finset.mem_univ k))
      exact hv (eq_zero_of_theta hz hzero))

@[simp] theorem metric_form : (metric D).form = D.form := rfl

/-! ### The orthonormal frame -/

variable (D) in
/-- The components of the frame `E₀ = ∂_t`, `E_i = Σ_a f_{ai}(t) X_a`. -/
def frameField (a : Fin 4) (z : E) : E :=
  Fin.cases (motive := fun _ => E) timeUnit
    (fun i => ofSpatial (∑ b, D.triadInv (z 0) b i • D.F.field b (spatial z))) a

@[simp] theorem frameField_zero (z : E) : D.frameField 0 z = timeUnit := rfl

@[simp] theorem frameField_succ (i : Fin 3) (z : E) :
    D.frameField i.succ z = ofSpatial (∑ b, D.triadInv (z 0) b i • D.F.field b (spatial z)) :=
  rfl

theorem thetaForm_timeUnit (z : E) (k : Fin 3) : D.thetaForm z k timeUnit = 0 := by
  simp [thetaForm_apply]

/-- `θ^k(E_i) = δ^k_i`. -/
theorem thetaForm_frameField_succ {z : E} (hz : z ∈ D.domain) (k i : Fin 3) :
    D.thetaForm z k (D.frameField i.succ z) = if k = i then 1 else 0 := by
  rw [frameField_succ, thetaForm_ofSpatial hz]
  have h := congrFun (congrFun (D.triad_mul _ (time_mem hz)) k) i
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

/-- **The frame is orthonormal**: `g(E_a, E_b) = η_{ab}`. -/
theorem form_frameField {z : E} (hz : z ∈ D.domain) (a b : Fin 4) :
    D.form z (D.frameField a z) (D.frameField b z) =
      if a = b then lorentzSign .timeNegative a else 0 := by
  rw [form_apply]
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
  · simp [thetaForm_timeUnit, lorentzSign, LorentzConvention.timeSign_timeNegative]
  · simp [thetaForm_timeUnit, (Fin.succ_ne_zero j).symm]
  · simp [thetaForm_timeUnit, Fin.succ_ne_zero i]
  · simp only [frameField_succ, ofSpatial_zero, mul_zero, neg_zero, zero_add]
    simp only [← frameField_succ, thetaForm_frameField_succ hz, mul_ite, mul_one, mul_zero]
    by_cases h : i = j
    · subst h
      simp [lorentzSign, LorentzConvention.timeSign_timeNegative, Fin.succ_ne_zero]
    · simp [h, Ne.symm h, Fin.succ_inj, Finset.sum_ite_eq', Finset.mem_univ]

/-! ### Derivatives of the frame -/

theorem hasDerivAt_triadInv {t : ℝ} (ht : t ∈ D.I) (a i : Fin 3) :
    HasDerivAt (fun s => D.triadInv s a i) (deriv (fun s => D.triadInv s a i) t) t :=
  FLRW.hasDerivAt_of_contDiffOn D.isOpen_I (D.smooth_triadInv a i) ht

theorem differentiableAt_field {z : E} (hz : z ∈ D.domain) (b : Fin 3) :
    DifferentiableAt ℝ (D.F.field b) (spatial z) :=
  ((D.F.smooth_field b).differentiableOn (by simp) _ (spatial_mem hz)).differentiableAt
    (D.F.isOpen.mem_nhds (spatial_mem hz))

theorem contDiffOn_field (b : Fin 3) :
    ContDiffOn ℝ ∞ (fun z : E => D.F.field b (spatial z)) D.domain :=
  (D.F.smooth_field b).comp spatial.contDiff.contDiffOn fun _ hz => spatial_mem hz

theorem contDiffOn_time_triadInv (a i : Fin 3) :
    ContDiffOn ℝ ∞ (fun z : E => D.triadInv (z 0) a i) D.domain :=
  (D.smooth_triadInv a i).comp (contDiff_apply ℝ (fun _ => ℝ) 0).contDiffOn
    fun _ hz => time_mem hz

/-- The components of the frame are smooth on the domain. -/
theorem contDiffOn_frameField (a : Fin 4) : ContDiffOn ℝ ∞ (D.frameField a) D.domain := by
  refine Fin.cases ?_ (fun i => ?_) a
  · exact contDiffOn_const
  · exact ofSpatial.contDiff.comp_contDiffOn
      (ContDiffOn.sum fun b _ => (contDiffOn_time_triadInv b i).smul (contDiffOn_field b))

/-- The derivative of `E_i = Σ_b f_{bi}(t) X_b(x)` along `v`. -/
theorem fderiv_frameField_succ {z : E} (hz : z ∈ D.domain) (i : Fin 3) (v : E) :
    fderiv ℝ (D.frameField i.succ) z v =
      ofSpatial (∑ b, ((deriv (fun s => D.triadInv s b i) (z 0) * v 0) • D.F.field b (spatial z) +
        D.triadInv (z 0) b i • fderiv ℝ (D.F.field b) (spatial z) (spatial v))) := by
  have hb (b : Fin 3) := (FLRW.hasFDerivAt_time (hasDerivAt_triadInv (time_mem hz) b i)).smul
    ((differentiableAt_field hz b).hasFDerivAt.comp z spatial.hasFDerivAt)
  have h : HasFDerivAt (D.frameField i.succ) _ z :=
    ofSpatial.hasFDerivAt.comp z (HasFDerivAt.fun_sum (u := Finset.univ) fun b _ => hb b)
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_sum, Finset.sum_apply,
    add_apply, smul_apply, smulRight_apply, proj_apply, smul_eq_mul, Function.comp_apply]
  congr 1
  exact Finset.sum_congr rfl fun b _ => by rw [add_comm]

/-- The time component of a frame field: `E_a⁰ = δ_{a0}`. -/
theorem frameField_apply_zero (a : Fin 4) (z : E) :
    D.frameField a z 0 = if a = 0 then 1 else 0 := by
  refine Fin.cases ?_ (fun i => ?_) a
  · simp
  · simp [Fin.succ_ne_zero]

/-! ### Brackets and commutator coefficients -/

theorem bracket_zero_zero (z : E) :
    lieBracketOf (D.frameField 0) (D.frameField 0) z = 0 := by
  simp [lieBracketOf, show D.frameField 0 = fun _ => timeUnit from rfl]

/-- `[E₀, E_j] = Σ_b ḟ_{bj} X_b`. -/
theorem bracket_zero_succ {z : E} (hz : z ∈ D.domain) (j : Fin 3) :
    lieBracketOf (D.frameField 0) (D.frameField j.succ) z =
      ofSpatial (∑ b, deriv (fun s => D.triadInv s b j) (z 0) • D.F.field b (spatial z)) := by
  have h0 : fderiv ℝ (D.frameField 0) z = 0 := by
    rw [show D.frameField 0 = fun _ => timeUnit from rfl]
    exact fderiv_const_apply _
  rw [lieBracketOf, fderiv_frameField_succ hz, h0]
  simp

/-- `[E_i, E₀] = −Σ_b ḟ_{bi} X_b`. -/
theorem bracket_succ_zero {z : E} (hz : z ∈ D.domain) (i : Fin 3) :
    lieBracketOf (D.frameField i.succ) (D.frameField 0) z =
      -ofSpatial (∑ b, deriv (fun s => D.triadInv s b i) (z 0) • D.F.field b (spatial z)) := by
  rw [← bracket_zero_succ hz i, lieBracketOf, lieBracketOf, neg_sub]

/-- `[E_i, E_j] = Σ_c (Σ_{ab} f_{ai} f_{bj} C^c_{ab}) X_c`. -/
theorem bracket_succ_succ {z : E} (hz : z ∈ D.domain) (i j : Fin 3) :
    lieBracketOf (D.frameField i.succ) (D.frameField j.succ) z =
      ofSpatial (∑ c, (∑ a, ∑ b, D.triadInv (z 0) a i * D.triadInv (z 0) b j * D.F.C c a b) •
        D.F.field c (spatial z)) := by
  rw [lieBracketOf, fderiv_frameField_succ hz, fderiv_frameField_succ hz, ← map_sub]
  congr 1
  funext α
  have key (a b : Fin 3) :
      fderiv ℝ (D.F.field b) (spatial z) (D.F.field a (spatial z)) α -
          fderiv ℝ (D.F.field a) (spatial z) (D.F.field b (spatial z)) α =
        ∑ c, D.F.C c a b * D.F.field c (spatial z) α := by
    have h := congrFun (D.F.bracket (spatial z) (spatial_mem hz) a b) α
    simpa [Finset.sum_apply] using h
  simp only [frameField_succ, ofSpatial_zero, mul_zero, zero_smul, zero_add, spatial_ofSpatial,
    map_sum, map_smul, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hR : ∑ c, (∑ a, ∑ b, D.triadInv (z 0) a i * D.triadInv (z 0) b j * D.F.C c a b) *
        D.F.field c (spatial z) α =
      ∑ a, ∑ b, D.triadInv (z 0) a i * D.triadInv (z 0) b j *
        (fderiv ℝ (D.F.field b) (spatial z) (D.F.field a (spatial z)) α -
          fderiv ℝ (D.F.field a) (spatial z) (D.F.field b (spatial z)) α) := by
    simp only [key, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
  rw [hR]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
  · exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- `g(E₀, w) = 0` for a spatial vector `w`. -/
theorem form_timeUnit_ofSpatial (z : E) (w : Fin 3 → ℝ) : D.form z timeUnit (ofSpatial w) = 0 := by
  simp [form_apply, thetaForm_timeUnit]

/-- `g(E_k, w) = θ^k(w)` for a spatial vector `w`. -/
theorem form_frameField_succ_ofSpatial {z : E} (hz : z ∈ D.domain) (k : Fin 3)
    (w : Fin 3 → ℝ) :
    D.form z (D.frameField k.succ z) (ofSpatial w) = D.thetaForm z k (ofSpatial w) := by
  rw [form_apply, frameField_succ, ofSpatial_zero, ofSpatial_zero, mul_zero, neg_zero, zero_add]
  simp only [← frameField_succ, thetaForm_frameField_succ hz, ite_mul, one_mul, zero_mul]
  simp

variable (D) in
/-- The rate `K_{kj} = (e ḟ)_{kj} = Σ_q e_{kq} ḟ_{qj}`: `λ_{k0j} = K_{kj}`. -/
def velocity (t : ℝ) (k j : Fin 3) : ℝ :=
  ∑ q, D.triad t k q * deriv (fun s => D.triadInv s q j) t

variable (D) in
/-- The spatial commutator coefficients `λ_{kij} = Σ_c e_{kc} Σ_{ab} f_{ai} f_{bj} C^c_{ab}`. -/
def spatialStructure (t : ℝ) (k i j : Fin 3) : ℝ :=
  ∑ c, D.triad t k c * ∑ a, ∑ b, D.triadInv t a i * D.triadInv t b j * D.F.C c a b

variable (D) in
/-- **The commutator coefficients of the frame**, functions of the time:
`λ_{0bc} = 0`, `λ_{k00} = 0`, `λ_{k0j} = K_{kj}`, `λ_{ki0} = −K_{ki}` and
`λ_{kij} = spatialStructure`. -/
def lam (t : ℝ) (a b c : Fin 4) : ℝ :=
  Fin.cases (motive := fun _ => ℝ) 0 (fun k =>
    Fin.cases (motive := fun _ => ℝ)
      (Fin.cases (motive := fun _ => ℝ) 0 (fun j => D.velocity t k j) c)
      (fun i => Fin.cases (motive := fun _ => ℝ) (-D.velocity t k i)
        (fun j => D.spatialStructure t k i j) c) b) a

@[simp] theorem lam_zero (t : ℝ) (b c : Fin 4) : D.lam t 0 b c = 0 := rfl

@[simp] theorem lam_succ_zero_zero (t : ℝ) (k : Fin 3) : D.lam t k.succ 0 0 = 0 := rfl

@[simp] theorem lam_succ_zero_succ (t : ℝ) (k j : Fin 3) :
    D.lam t k.succ 0 j.succ = D.velocity t k j := rfl

@[simp] theorem lam_succ_succ_zero (t : ℝ) (k i : Fin 3) :
    D.lam t k.succ i.succ 0 = -D.velocity t k i := rfl

@[simp] theorem lam_succ_succ_succ (t : ℝ) (k i j : Fin 3) :
    D.lam t k.succ i.succ j.succ = D.spatialStructure t k i j := rfl

/-- **The commutator coefficients** `g(E_a, [E_b, E_c])` at a point of the domain are the
coefficients `lam` at its time. -/
theorem commutator_frame {z : E} (hz : z ∈ D.domain) (a b c : Fin 4) :
    D.form z (D.frameField a z) (lieBracketOf (D.frameField b) (D.frameField c) z) =
      D.lam (z 0) a b c := by
  refine Fin.cases ?_ (fun k => ?_) a
  · refine Fin.cases ?_ (fun i => ?_) b <;> refine Fin.cases ?_ (fun j => ?_) c
    · simp [bracket_zero_zero]
    · simp [bracket_zero_succ hz, form_timeUnit_ofSpatial]
    · simp [bracket_succ_zero hz, form_timeUnit_ofSpatial]
    · simp [bracket_succ_succ hz, form_timeUnit_ofSpatial]
  · refine Fin.cases ?_ (fun i => ?_) b <;> refine Fin.cases ?_ (fun j => ?_) c
    · simp [bracket_zero_zero]
    · rw [bracket_zero_succ hz, form_frameField_succ_ofSpatial hz, thetaForm_ofSpatial hz,
        lam_succ_zero_succ, velocity]
    · rw [bracket_succ_zero hz, map_neg, form_frameField_succ_ofSpatial hz,
        thetaForm_ofSpatial hz, lam_succ_succ_zero, velocity]
    · rw [bracket_succ_succ hz, form_frameField_succ_ofSpatial hz, thetaForm_ofSpatial hz,
        lam_succ_succ_succ, spatialStructure]

theorem contDiffOn_velocity (k j : Fin 3) : ContDiffOn ℝ ∞ (fun t => D.velocity t k j) D.I :=
  ContDiffOn.sum fun q _ => (D.smooth_triad k q).mul
    (FLRW.contDiffOn_deriv_of_contDiffOn D.isOpen_I (D.smooth_triadInv q j))

theorem contDiffOn_spatialStructure (k i j : Fin 3) :
    ContDiffOn ℝ ∞ (fun t => D.spatialStructure t k i j) D.I :=
  ContDiffOn.sum fun c _ => (D.smooth_triad k c).mul (ContDiffOn.sum fun a _ =>
    ContDiffOn.sum fun b _ => ((D.smooth_triadInv a i).mul (D.smooth_triadInv b j)).mul
      contDiffOn_const)

/-- The commutator coefficients are smooth functions of the time on `I`. -/
theorem contDiffOn_lam (a b c : Fin 4) : ContDiffOn ℝ ∞ (fun t => D.lam t a b c) D.I := by
  refine Fin.cases ?_ (fun k => ?_) a
  · exact contDiffOn_const
  · refine Fin.cases ?_ (fun i => ?_) b <;> refine Fin.cases ?_ (fun j => ?_) c
    · exact contDiffOn_const
    · exact contDiffOn_velocity k j
    · exact (contDiffOn_velocity k i).neg
    · exact contDiffOn_spatialStructure k i j

/-! ### The Ricci tensor -/

variable (D) in
/-- **The orthonormal frame** `E₀ = ∂_t`, `E_i = Σ_a f_{ai} X_a` of the metric, on the whole
domain (the base point `y` only fixes the chart of the components). -/
def frame (y : D.domain) : (metric D).toLorentzMetric.OrthonormalFrame (univ : Set D.domain) :=
  orthonormalFrameOf (metric D) y D.frameField contDiffOn_frameField
    fun _ hz a b => form_frameField hz a b

variable (D) in
/-- The rotation coefficients `γ_{abc} = ½ (λ_{abc} + λ_{bca} − λ_{cab})` at the time `t`. -/
def rot (t : ℝ) (a b c : Fin 4) : ℝ := (D.lam t a b c + D.lam t b c a - D.lam t c a b) / 2

variable (D) in
/-- **The frame components of the Ricci tensor at the time `t`**:
`R_{bk} = Σ_i η_{ii} (δ_{i0} γ̇_{kib} − δ_{b0} γ̇_{kii} −
Σ_f η_{ff} (γ_{kfb} γ_{ifi} − γ_{kfi} γ_{ifb} + λ_{fib} γ_{kif}))`, the dot being `d/dt`. -/
def frameRicci (t : ℝ) (b k : Fin 4) : ℝ :=
  ∑ i, lorentzSign .timeNegative i *
    ((if i = 0 then deriv (fun s => D.rot s k i b) t else 0) -
      (if b = 0 then deriv (fun s => D.rot s k i i) t else 0) -
      ∑ f, lorentzSign .timeNegative f * (D.rot t k f b * D.rot t i f i -
        D.rot t k f i * D.rot t i f b + D.lam t f i b * D.rot t k i f))

theorem contDiffOn_rot (a b c : Fin 4) : ContDiffOn ℝ ∞ (fun t => D.rot t a b c) D.I :=
  (((contDiffOn_lam a b c).add (contDiffOn_lam b c a)).sub (contDiffOn_lam c a b)).div_const 2

/-- The derivative of a rotation coefficient, a function of the time, along `v`. -/
theorem fderiv_rotationOf {z : E} (hz : z ∈ D.domain) (a b c : Fin 4) (v : E) :
    fderiv ℝ (rotationOf (fun a b c (y : E) => D.lam (y 0) a b c) a b c) z v =
      deriv (fun s => D.rot s a b c) (z 0) * v 0 := by
  have h := FLRW.hasFDerivAt_time (FLRW.hasDerivAt_of_contDiffOn D.isOpen_I
    (contDiffOn_rot a b c) (time_mem hz))
  rw [show rotationOf (fun a b c (y : E) => D.lam (y 0) a b c) a b c =
    fun y : E => D.rot (y 0) a b c from rfl, h.fderiv]
  simp [smul_eq_mul]

/-- **The reduction of the Ricci tensor**: its frame components at a point of the domain are
`frameRicci` at the time of the point. -/
theorem ricci_frame (y : D.domain) (b k : Fin 4) :
    (metric D).toLorentzMetric.ricci y ((frame D y).field b y) ((frame D y).field k y) =
      D.frameRicci ((y : E) 0) b k := by
  have hΛ (a b c : Fin 4) : ContDiffOn ℝ ∞ (fun z : E => D.lam (z 0) a b c) D.domain :=
    (contDiffOn_lam a b c).comp (contDiff_apply ℝ (fun _ => ℝ) 0).contDiffOn
      fun _ hz => time_mem hz
  have hcomm : ∀ z ∈ D.domain, ∀ a b c, (metric D).form z (D.frameField a z)
      (lieBracketOf (D.frameField b) (D.frameField c) z) = D.lam (z 0) a b c :=
    fun z hz a b c => commutator_frame hz a b c
  refine (ricci_orthonormalFrameOf (metric D) y (ξ := D.frameField) contDiffOn_frameField
    (fun _ hz a b => form_frameField hz a b) hΛ hcomm y b k).trans ?_
  rw [ricciOfFrame, frameRicci]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_rotationOf y.property, fderiv_rotationOf y.property, frameField_apply_zero,
    frameField_apply_zero]
  simp only [mul_ite, mul_one, mul_zero]
  rfl

/-- The point of the domain with the time `t` and the spatial co-ordinates `s`. -/
def pointOf {t : ℝ} {s : Fin 3 → ℝ} (ht : t ∈ D.I) (hs : s ∈ D.F.V) : D.domain :=
  ⟨point t s, point_mem ht hs⟩

/-- **The vacuum equations reduce to ordinary differential equations**: the Ricci tensor
vanishes on the domain if and only if `frameRicci t b k = 0` for all `t ∈ I`. -/
theorem ricci_eq_zero_iff :
    (∀ y : D.domain, (metric D).toLorentzMetric.ricci y = 0) ↔
      ∀ t ∈ D.I, ∀ b k, D.frameRicci t b k = 0 := by
  constructor
  · intro h t ht b k
    obtain ⟨s, hs⟩ := D.F.nonempty
    have h' := ricci_frame (pointOf ht hs) b k
    rw [h (pointOf ht hs), zero_apply, zero_apply] at h'
    simpa [pointOf] using h'.symm
  · intro h y
    refine (frame D y).bilinear_ext (mem_univ y) fun b k => ?_
    rw [ricci_frame]
    exact h _ (time_mem y.property) b k

/-! ### Matter: a comoving perfect fluid -/

variable (D) in
/-- The comoving perfect fluid `T(v, w) = (ρ + p) g(u, v) g(u, w) + p g(v, w)` with
`u = E₀ = ∂_t`. -/
def fluid (ρ p : ℝ → ℝ) (y : D.domain) :
    TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ :=
  (ρ ((y : E) 0) + p ((y : E) 0)) •
      ((metric D).toLorentzMetric.form y ((frame D y).field 0 y)).smulRight
        ((metric D).toLorentzMetric.form y ((frame D y).field 0 y)) +
    p ((y : E) 0) • (metric D).toLorentzMetric.form y

variable (D) in
/-- The scalar curvature `R = Σ_i η_{ii} R_{ii}` at the time `t`. -/
def frameScalar (t : ℝ) : ℝ := ∑ i, lorentzSign .timeNegative i * D.frameRicci t i i

/-- The frame components `diag(ρ, p, p, p)` of the comoving fluid. -/
def fluidFrame (ρ p : ℝ → ℝ) (t : ℝ) (a b : Fin 4) : ℝ :=
  if a = b then (if a = 0 then ρ t else p t) else 0

/-- **The Einstein equations with a comoving perfect fluid reduce to ordinary differential
equations**: `G + Λ g = κ T` holds on the domain if and only if
`R_{ab} − ½ R η_{ab} + Λ η_{ab} = κ diag(ρ, p, p, p)_{ab}` for all `t ∈ I`. -/
theorem einstein_iff (κ Λ : ℝ) (ρ p : ℝ → ℝ) :
    (∀ y : D.domain, (metric D).toLorentzMetric.einstein y +
        Λ • (metric D).toLorentzMetric.form y = κ • D.fluid ρ p y) ↔
      ∀ t ∈ D.I, ∀ a b, D.frameRicci t a b -
          D.frameScalar t / 2 * (if a = b then lorentzSign .timeNegative a else 0) +
          Λ * (if a = b then lorentzSign .timeNegative a else 0) =
        κ * fluidFrame ρ p t a b := by
  have hpoint (y : D.domain) : (metric D).toLorentzMetric.einstein y +
      Λ • (metric D).toLorentzMetric.form y = κ • D.fluid ρ p y ↔
      ∀ a b, D.frameRicci ((y : E) 0) a b -
          D.frameScalar ((y : E) 0) / 2 * (if a = b then lorentzSign .timeNegative a else 0) +
          Λ * (if a = b then lorentzSign .timeNegative a else 0) =
        κ * fluidFrame ρ p ((y : E) 0) a b := by
    rw [(frame D y).einstein_eq_iff (mem_univ y)]
    have hR : (metric D).toLorentzMetric.scalarCurvature y = D.frameScalar ((y : E) 0) := by
      rw [(frame D y).scalarCurvature_eq (mem_univ y), frameScalar]
      simp only [ricci_frame]
    have hT (a b : Fin 4) : D.fluid ρ p y ((frame D y).field a y) ((frame D y).field b y) =
        fluidFrame ρ p ((y : E) 0) a b := by
      simp only [fluid, add_apply, smul_apply, smulRight_apply, smul_eq_mul,
        (frame D y).orthonormal y (mem_univ y), fluidFrame]
      refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
      · simp [lorentzSign, LorentzConvention.timeSign_timeNegative]
      · simp [(Fin.succ_ne_zero j).symm]
      · simp [Fin.succ_ne_zero i, (Fin.succ_ne_zero i).symm]
      · by_cases h : i = j
        · subst h
          simp [lorentzSign, LorentzConvention.timeSign_timeNegative, Fin.succ_ne_zero,
            (Fin.succ_ne_zero i).symm]
        · simp [h, (Fin.succ_ne_zero i).symm]
    simp only [(frame D y).einstein_field (mem_univ y), ricci_frame, hR, hT]
  constructor
  · intro h t ht a b
    obtain ⟨s, hs⟩ := D.F.nonempty
    simpa [pointOf] using (hpoint (pointOf ht hs)).mp (h _) a b
  · intro h y
    exact (hpoint y).mpr (h _ (time_mem y.property))

end Data

end ProjectAinos.GeneralRelativity.HomogeneousSpace
