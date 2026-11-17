/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.OneDimension.ActionAngle
public import ProjectAInos.Variational.ParametricIntegralOn

/-!
# Families of wells with a parameter

A smooth family of potentials `V(s, x)` with a parameter `s` in a space of
finite dimension, and a smooth level `ℰ(s)`.

* `contDiff_wellFactor_family`: the factor of the well is smooth in the
  parameter, the two points and the position together.
* `IsWell.exists_family_param`: the turning points of a well of one parameter
  extend to smooth functions of the parameter on an open set, with wells
  between them.
* `contDiffOn_orbitRate_family`, `contDiffOn_orbitMomentum_family_param`: the
  rate and the momentum on the level curves are smooth in the parameter and the
  angle; hence the period and the area are smooth functions of the parameter
  (`contDiffOn_orbitPeriod_family`, `contDiffOn_orbitArea_family`).
-/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory
open scoped Real ContDiff Topology

namespace ProjectAInos.Mechanics.OneDim

open SmoothAlgebra

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {V : P × ℝ → ℝ}

/-- The derivative of a family of functions in the position. -/
def slopeOf (V : P × ℝ → ℝ) (w : P × ℝ) : ℝ := fderiv ℝ V w (0, 1)

theorem contDiff_slopeOf (hV : ContDiff ℝ ∞ V) : ContDiff ℝ ∞ (slopeOf V) :=
  (hV.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem hasDerivAt_slice (hV : ContDiff ℝ ∞ V) (s : P) (x : ℝ) :
    HasDerivAt (fun y => V (s, y)) (slopeOf V (s, x)) x := by
  have h1 : HasFDerivAt V (fderiv ℝ V (s, x)) (s, x) :=
    (hV.differentiable (by simp) (s, x)).hasFDerivAt
  have h2 : HasDerivAt (fun y : ℝ => ((s, y) : P × ℝ)) ((0 : P), (1 : ℝ)) x :=
    (hasDerivAt_const x s).prodMk (hasDerivAt_id x)
  exact HasFDerivAt.comp_hasDerivAt x h1 h2

theorem deriv_slice (hV : ContDiff ℝ ∞ V) (s : P) :
    deriv (fun y => V (s, y)) = fun x => slopeOf V (s, x) :=
  funext fun x => (hasDerivAt_slice hV s x).deriv

theorem deriv_deriv_slice (hV : ContDiff ℝ ∞ V) (s : P) :
    deriv (deriv (fun y => V (s, y))) = fun x => slopeOf (slopeOf V) (s, x) := by
  rw [deriv_slice hV s]
  exact deriv_slice (contDiff_slopeOf hV) s

theorem contDiff_slice (hV : ContDiff ℝ ∞ V) (s : P) : ContDiff ℝ ∞ fun y => V (s, y) :=
  hV.comp (contDiff_const.prodMk contDiff_id)

variable [FiniteDimensional ℝ P]

/-- The factor of the well is smooth in the parameter, the two points and the
position. -/
theorem contDiff_wellFactor_family (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ fun r : P × ℝ × ℝ × ℝ =>
      wellFactor (fun y => V (r.1, y)) r.2.1 r.2.2.1 r.2.2.2 := by
  have hV2 : ContDiff ℝ ∞ (slopeOf (slopeOf V)) := contDiff_slopeOf (contDiff_slopeOf hV)
  have hF : ContDiff ℝ ∞ fun q : ((P × ℝ × ℝ × ℝ) × ℝ) × ℝ =>
      slopeOf (slopeOf V) (q.1.1.1, q.1.1.2.1 + q.1.2 * (q.1.1.2.2.1 - q.1.1.2.1) +
        q.2 * ((1 - q.1.2) * (q.1.1.2.2.2 - q.1.1.2.1))) :=
    hV2.comp (by fun_prop)
  have hinner : ContDiff ℝ ∞ fun q : (P × ℝ × ℝ × ℝ) × ℝ => ∫ u in (0 : ℝ)..1,
      slopeOf (slopeOf V) (q.1.1, q.1.2.1 + q.2 * (q.1.2.2.1 - q.1.2.1) +
        u * ((1 - q.2) * (q.1.2.2.2 - q.1.2.1))) :=
    contDiff_infty_parametric_intervalIntegral hF 0 1
  have hG : ContDiff ℝ ∞ fun q : (P × ℝ × ℝ × ℝ) × ℝ => (1 - q.2) * ∫ u in (0 : ℝ)..1,
      slopeOf (slopeOf V) (q.1.1, q.1.2.1 + q.2 * (q.1.2.2.1 - q.1.2.1) +
        u * ((1 - q.2) * (q.1.2.2.2 - q.1.2.1))) :=
    (contDiff_const.sub contDiff_snd).mul hinner
  have hmain := contDiff_infty_parametric_intervalIntegral hG 0 1
  have heq : (fun r : P × ℝ × ℝ × ℝ =>
      wellFactor (fun y => V (r.1, y)) r.2.1 r.2.2.1 r.2.2.2) =
      fun r => ∫ t in (0 : ℝ)..1, (1 - t) * ∫ u in (0 : ℝ)..1,
        slopeOf (slopeOf V) (r.1, r.2.1 + t * (r.2.2.1 - r.2.1) +
          u * ((1 - t) * (r.2.2.2 - r.2.1))) := by
    funext r
    rw [wellFactor, dividedDifference₂, deriv_deriv_slice hV r.1]
  rw [heq]
  exact hmain

/-- A simple point of a level is a smooth function of the parameter. -/
theorem exists_level_point_family (hV : ContDiff ℝ ∞ V) {ℰ : P → ℝ} (hℰ : ContDiff ℝ ∞ ℰ)
    {s₀ : P} {x₀ : ℝ} (hx₀ : V (s₀, x₀) = ℰ s₀) (hd : slopeOf V (s₀, x₀) ≠ 0) :
    ∃ (J : Set P) (ξ : P → ℝ), IsOpen J ∧ s₀ ∈ J ∧ ξ s₀ = x₀ ∧ ContDiffOn ℝ ∞ ξ J ∧
      ∀ s ∈ J, V (s, ξ s) = ℰ s := by
  obtain ⟨f, hfdef⟩ : ∃ f : P × ℝ → ℝ, f = fun v => V v - ℰ v.1 := ⟨_, rfl⟩
  have hf : ContDiff ℝ ∞ f := by
    rw [hfdef]
    exact hV.sub (hℰ.comp contDiff_fst)
  have hfd : ∀ v : P × ℝ, fderiv ℝ f v ∘L ContinuousLinearMap.inr ℝ P ℝ =
      slopeOf V v • ContinuousLinearMap.id ℝ ℝ := by
    intro v
    have h1 : HasFDerivAt (fun y : ℝ => f (v.1, y)) (fderiv ℝ f v ∘L
        ContinuousLinearMap.inr ℝ P ℝ) v.2 :=
      HasFDerivAt.comp (g := f) (f := fun y : ℝ => (v.1, y)) v.2
        (hf.differentiable (by simp) v).hasFDerivAt (hasFDerivAt_prodMk_right v.1 v.2)
    have h2 : HasDerivAt (fun y : ℝ => f (v.1, y)) (slopeOf V v) v.2 := by
      rw [hfdef]
      exact (hasDerivAt_slice hV v.1 v.2).sub_const (ℰ v.1)
    have h3 := h1.unique h2.hasFDerivAt
    rw [h3]
    ext
    simp
  have hopen : IsOpen {v : P × ℝ | slopeOf V v ≠ 0} :=
    isOpen_ne_fun (contDiff_slopeOf hV).continuous continuous_const
  have hinv : ∀ v ∈ {v : P × ℝ | slopeOf V v ≠ 0},
      (fderiv ℝ f v ∘L ContinuousLinearMap.inr ℝ P ℝ).IsInvertible := by
    intro v hv
    rw [hfd v]
    refine ContinuousLinearMap.IsInvertible.of_inverse
      (g := (slopeOf V v)⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_
    · ext
      simp
      exact inv_mul_cancel₀ hv
    · ext
      simp
      exact mul_inv_cancel₀ hv
  have hcomplete : CompleteSpace P := FiniteDimensional.complete ℝ P
  obtain ⟨J, ξ, hJ, hs₀, hξ₀, hξ, hsol⟩ := exists_contDiffOn_implicitFunction (f := f)
    hopen hf.contDiffOn hinv (u := (s₀, x₀)) hd
  refine ⟨J, ξ, hJ, hs₀, hξ₀, hξ, fun s hs => ?_⟩
  have h := (hsol s hs).2
  rw [hfdef] at h
  change V (s, ξ s) - ℰ s = V (s₀, x₀) - ℰ s₀ at h
  rw [hx₀, sub_self, sub_eq_zero] at h
  exact h

/-- The turning points of a well are smooth functions of the parameter, and the
nearby parameters have wells between them. -/
theorem IsWell.exists_family_param (hV : ContDiff ℝ ∞ V) {ℰ : P → ℝ} (hℰ : ContDiff ℝ ∞ ℰ)
    {s₀ : P} {a₀ b₀ : ℝ} (h : IsWell (fun y => V (s₀, y)) (ℰ s₀) a₀ b₀) :
    ∃ (J : Set P) (α β : P → ℝ), IsOpen J ∧ s₀ ∈ J ∧ α s₀ = a₀ ∧ β s₀ = b₀ ∧
      ContDiffOn ℝ ∞ α J ∧ ContDiffOn ℝ ∞ β J ∧
        ∀ s ∈ J, IsWell (fun y => V (s, y)) (ℰ s) (α s) (β s) := by
  have hU₀ := contDiff_slice hV s₀
  have hda : slopeOf V (s₀, a₀) < 0 := by
    have := h.deriv_left
    rwa [deriv_slice hV s₀] at this
  have hdb : 0 < slopeOf V (s₀, b₀) := by
    have := h.deriv_right
    rwa [deriv_slice hV s₀] at this
  obtain ⟨Ja, α, hJa, hsa, hα₀, hα, hαV⟩ := exists_level_point_family hV hℰ h.left hda.ne
  obtain ⟨Jb, β, hJb, hsb, hβ₀, hβ, hβV⟩ := exists_level_point_family hV hℰ h.right hdb.ne'
  have hJ₀ : IsOpen (Ja ∩ Jb) := hJa.inter hJb
  have hs₀ : s₀ ∈ Ja ∩ Jb := ⟨hsa, hsb⟩
  have hαc : ContinuousOn α (Ja ∩ Jb) := hα.continuousOn.mono inter_subset_left
  have hβc : ContinuousOn β (Ja ∩ Jb) := hβ.continuousOn.mono inter_subset_right
  have hαat : ContinuousAt α s₀ := hαc.continuousAt (hJ₀.mem_nhds hs₀)
  have hβat : ContinuousAt β s₀ := hβc.continuousAt (hJ₀.mem_nhds hs₀)
  have hWc : ContinuousOn
      (fun v : P × ℝ => wellFactor (fun y => V (v.1, y)) (α v.1) (β v.1) v.2)
      (Prod.fst ⁻¹' (Ja ∩ Jb)) := by
    have hmap : ContinuousOn (fun v : P × ℝ => (v.1, α v.1, β v.1, v.2))
        (Prod.fst ⁻¹' (Ja ∩ Jb)) :=
      continuousOn_fst.prodMk ((hαc.comp continuousOn_fst fun v hv => hv).prodMk
        ((hβc.comp continuousOn_fst fun v hv => hv).prodMk continuousOn_snd))
    exact Continuous.comp_continuousOn
      (g := fun r : P × ℝ × ℝ × ℝ => wellFactor (fun y => V (r.1, y)) r.2.1 r.2.2.1 r.2.2.2)
      (f := fun v : P × ℝ => (v.1, α v.1, β v.1, v.2))
      (contDiff_wellFactor_family hV).continuous hmap
  have hO : IsOpen ((Prod.fst ⁻¹' (Ja ∩ Jb) : Set (P × ℝ)) ∩
      (fun v : P × ℝ => wellFactor (fun y => V (v.1, y)) (α v.1) (β v.1) v.2) ⁻¹' Ioi 0) :=
    hWc.isOpen_inter_preimage (hJ₀.preimage continuous_fst) isOpen_Ioi
  have hbase : ∀ x ∈ uIcc (α s₀) (β s₀), (s₀, x) ∈
      (Prod.fst ⁻¹' (Ja ∩ Jb) : Set (P × ℝ)) ∩
        (fun v : P × ℝ => wellFactor (fun y => V (v.1, y)) (α v.1) (β v.1) v.2) ⁻¹' Ioi 0 := by
    intro x hx
    rw [hα₀, hβ₀, uIcc_of_le h.lt.le] at hx
    refine ⟨hs₀, ?_⟩
    change 0 < wellFactor (fun y => V (s₀, y)) (α s₀) (β s₀) x
    rw [hα₀, hβ₀]
    exact h.wellFactor_pos hU₀ hx
  have hev := Variational.eventually_uIcc_mem_open hαat hβat hO hbase
  have hlt : ∀ᶠ s in 𝓝 s₀, α s < β s := by
    have h1 : ContinuousAt (fun s => β s - α s) s₀ := hβat.sub hαat
    have h2 : 0 < β s₀ - α s₀ := by rw [hα₀, hβ₀]; exact sub_pos.mpr h.lt
    exact (h1.eventually (lt_mem_nhds h2)).mono fun s hs => sub_pos.mp hs
  have hsc : Continuous (slopeOf V) := (contDiff_slopeOf hV).continuous
  have hda' : ∀ᶠ s in 𝓝 s₀, slopeOf V (s, α s) < 0 := by
    have h1 : ContinuousAt (fun s => slopeOf V (s, α s)) s₀ :=
      hsc.continuousAt.comp (continuousAt_id.prodMk hαat)
    have h2 : (fun s => slopeOf V (s, α s)) s₀ < 0 := by
      change slopeOf V (s₀, α s₀) < 0
      rw [hα₀]
      exact hda
    exact h1.eventually (gt_mem_nhds h2)
  have hdb' : ∀ᶠ s in 𝓝 s₀, 0 < slopeOf V (s, β s) := by
    have h1 : ContinuousAt (fun s => slopeOf V (s, β s)) s₀ :=
      hsc.continuousAt.comp (continuousAt_id.prodMk hβat)
    have h2 : 0 < (fun s => slopeOf V (s, β s)) s₀ := by
      change 0 < slopeOf V (s₀, β s₀)
      rw [hβ₀]
      exact hdb
    exact h1.eventually (lt_mem_nhds h2)
  have hmemJ : ∀ᶠ s in 𝓝 s₀, s ∈ Ja ∩ Jb := hJ₀.mem_nhds hs₀
  obtain ⟨J, hJsub, hJ, hsJ⟩ := eventually_nhds_iff.mp
    (hmemJ.and (hev.and (hlt.and (hda'.and hdb'))))
  refine ⟨J, α, β, hJ, hsJ, hα₀, hβ₀, hα.mono fun s hs => (hJsub s hs).1.1,
    hβ.mono fun s hs => (hJsub s hs).1.2, fun s hs => ?_⟩
  obtain ⟨hsJ₀, hpos, hsl, hsa', hsb'⟩ := hJsub s hs
  refine isWell_of_wellFactor_pos (contDiff_slice hV s) hsl (hαV s hsJ₀.1) (hβV s hsJ₀.2)
    (by rw [deriv_slice hV s]; exact hsa') (by rw [deriv_slice hV s]; exact hsb') fun x hx => ?_
  have hx' : x ∈ uIcc (α s) (β s) := by rwa [uIcc_of_le hsl.le]
  exact (hpos x hx').2

/-! ### Smooth dependence on the parameter and the angle -/

section Family

variable {ℰ : P → ℝ} {J : Set P} {α β : P → ℝ} {m : ℝ}

omit [FiniteDimensional ℝ P] in
theorem contDiffOn_orbitPosition_family (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J) :
    ContDiffOn ℝ ∞ (fun p : P × ℝ => orbitPosition (α p.1) (β p.1) p.2) (Prod.fst ⁻¹' J) := by
  have hαO : ContDiffOn ℝ ∞ (fun p : P × ℝ => α p.1) (Prod.fst ⁻¹' J) :=
    hα.comp contDiffOn_fst fun p hp => hp
  have hβO : ContDiffOn ℝ ∞ (fun p : P × ℝ => β p.1) (Prod.fst ⁻¹' J) :=
    hβ.comp contDiffOn_fst fun p hp => hp
  have hcos : ContDiffOn ℝ ∞ (fun p : P × ℝ => Real.cos p.2) (Prod.fst ⁻¹' J) :=
    (Real.contDiff_cos.comp contDiff_snd).contDiffOn
  exact ((hαO.add hβO).div_const 2).sub (((hβO.sub hαO).div_const 2).mul hcos)

theorem contDiffOn_wellFactor_orbit (hV : ContDiff ℝ ∞ V) (hα : ContDiffOn ℝ ∞ α J)
    (hβ : ContDiffOn ℝ ∞ β J) :
    ContDiffOn ℝ ∞ (fun p : P × ℝ => wellFactor (fun y => V (p.1, y)) (α p.1) (β p.1)
      (orbitPosition (α p.1) (β p.1) p.2)) (Prod.fst ⁻¹' J) := by
  have hαO : ContDiffOn ℝ ∞ (fun p : P × ℝ => α p.1) (Prod.fst ⁻¹' J) :=
    hα.comp contDiffOn_fst fun p hp => hp
  have hβO : ContDiffOn ℝ ∞ (fun p : P × ℝ => β p.1) (Prod.fst ⁻¹' J) :=
    hβ.comp contDiffOn_fst fun p hp => hp
  exact (contDiff_wellFactor_family hV).comp_contDiffOn
    (contDiffOn_fst.prodMk (hαO.prodMk (hβO.prodMk (contDiffOn_orbitPosition_family hα hβ))))

/-- The momentum on the level curves of a family of wells is smooth in the
parameter and the angle. -/
theorem contDiffOn_orbitMomentum_family_param (hV : ContDiff ℝ ∞ V) (m : ℝ)
    (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ s ∈ J, IsWell (fun y => V (s, y)) (ℰ s) (α s) (β s)) :
    ContDiffOn ℝ ∞ (fun p : P × ℝ =>
      orbitMomentum m (fun y => V (p.1, y)) (α p.1) (β p.1) p.2) (Prod.fst ⁻¹' J) := by
  have hαO : ContDiffOn ℝ ∞ (fun p : P × ℝ => α p.1) (Prod.fst ⁻¹' J) :=
    hα.comp contDiffOn_fst fun p hp => hp
  have hβO : ContDiffOn ℝ ∞ (fun p : P × ℝ => β p.1) (Prod.fst ⁻¹' J) :=
    hβ.comp contDiffOn_fst fun p hp => hp
  have hsin : ContDiffOn ℝ ∞ (fun p : P × ℝ => Real.sin p.2) (Prod.fst ⁻¹' J) :=
    (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  exact (contDiffOn_const.mul (((hβO.sub hαO).div_const 2).mul hsin)).mul
    ((contDiffOn_wellFactor_orbit hV hα hβ).sqrt fun p hp =>
      ((hw p.1 hp).wellFactor_orbitPosition_pos (contDiff_slice hV p.1) p.2).ne')

/-- The rate on the level curves of a family of wells is smooth in the
parameter and the angle. -/
theorem contDiffOn_orbitRate_family (hV : ContDiff ℝ ∞ V) (m : ℝ)
    (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ s ∈ J, IsWell (fun y => V (s, y)) (ℰ s) (α s) (β s)) :
    ContDiffOn ℝ ∞ (fun p : P × ℝ =>
      orbitRate m (fun y => V (p.1, y)) (α p.1) (β p.1) p.2) (Prod.fst ⁻¹' J) :=
  contDiffOn_const.div
    ((contDiffOn_wellFactor_orbit hV hα hβ).sqrt fun p hp =>
      ((hw p.1 hp).wellFactor_orbitPosition_pos (contDiff_slice hV p.1) p.2).ne')
    fun p hp => (Real.sqrt_pos.mpr
      ((hw p.1 hp).wellFactor_orbitPosition_pos (contDiff_slice hV p.1) p.2)).ne'

/-- The integral over a period of a smooth function of the parameter and the
position is a smooth function of the parameter. -/
theorem contDiffOn_integral_orbitRate_mul (hV : ContDiff ℝ ∞ V) (m : ℝ) (hJ : IsOpen J)
    (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ s ∈ J, IsWell (fun y => V (s, y)) (ℰ s) (α s) (β s)) {g : P × ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) :
    ContDiffOn ℝ ∞ (fun s => ∫ θ in (0 : ℝ)..2 * π,
      orbitRate m (fun y => V (s, y)) (α s) (β s) θ *
        g (s, orbitPosition (α s) (β s) θ)) J :=
  Variational.contDiffOn_parametric_intervalIntegral
    (f := fun p : P × ℝ => orbitRate m (fun y => V (p.1, y)) (α p.1) (β p.1) p.2 *
      g (p.1, orbitPosition (α p.1) (β p.1) p.2))
    (hJ.preimage continuous_fst)
    ((contDiffOn_orbitRate_family hV m hα hβ hw).mul
      (hg.comp_contDiffOn (contDiffOn_fst.prodMk (contDiffOn_orbitPosition_family hα hβ))))
    fun _ hs _ _ => hs

/-- The period is a smooth function of the parameter. -/
theorem contDiffOn_orbitPeriod_family (hV : ContDiff ℝ ∞ V) (m : ℝ) (hJ : IsOpen J)
    (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ s ∈ J, IsWell (fun y => V (s, y)) (ℰ s) (α s) (β s)) :
    ContDiffOn ℝ ∞ (fun s => orbitPeriod m (fun y => V (s, y)) (α s) (β s)) J :=
  Variational.contDiffOn_parametric_intervalIntegral
    (f := fun p : P × ℝ => orbitRate m (fun y => V (p.1, y)) (α p.1) (β p.1) p.2)
    (hJ.preimage continuous_fst) (contDiffOn_orbitRate_family hV m hα hβ hw)
    fun _ hs _ _ => hs

/-- The area is a smooth function of the parameter. -/
theorem contDiffOn_orbitArea_family (hV : ContDiff ℝ ∞ V) (m : ℝ) (hJ : IsOpen J)
    (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ s ∈ J, IsWell (fun y => V (s, y)) (ℰ s) (α s) (β s)) :
    ContDiffOn ℝ ∞ (fun s => orbitArea m (fun y => V (s, y)) (α s) (β s)) J := by
  have hαO : ContDiffOn ℝ ∞ (fun p : P × ℝ => α p.1) (Prod.fst ⁻¹' J) :=
    hα.comp contDiffOn_fst fun p hp => hp
  have hβO : ContDiffOn ℝ ∞ (fun p : P × ℝ => β p.1) (Prod.fst ⁻¹' J) :=
    hβ.comp contDiffOn_fst fun p hp => hp
  have hsin : ContDiffOn ℝ ∞ (fun p : P × ℝ => Real.sin p.2) (Prod.fst ⁻¹' J) :=
    (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  exact Variational.contDiffOn_parametric_intervalIntegral
    (f := fun p : P × ℝ => orbitMomentum m (fun y => V (p.1, y)) (α p.1) (β p.1) p.2 *
      ((β p.1 - α p.1) / 2 * Real.sin p.2))
    (hJ.preimage continuous_fst)
    ((contDiffOn_orbitMomentum_family_param hV m hα hβ hw).mul
      (((hβO.sub hαO).div_const 2).mul hsin))
    fun _ hs _ _ => hs

end Family

/-! ### The derivative of the area in a real parameter -/

section RealParameter

variable {V : ℝ × ℝ → ℝ} {m : ℝ} {J : Set ℝ} {ℰ α β : ℝ → ℝ}

/-- The derivative in a real parameter of the identity `p²/2m + V(r, x) = ℰ(r)`
on the level curves of a family of wells. -/
theorem orbitMomentum_mul_deriv_param (hV : ContDiff ℝ ∞ V) (hm : 0 < m) (hJ : IsOpen J)
    (hw : ∀ r ∈ J, IsWell (fun y => V (r, y)) (ℰ r) (α r) (β r)) {r₀ : ℝ} (hr₀ : r₀ ∈ J)
    {ℰ' α' β' PE : ℝ} (hℰ : HasDerivAt ℰ ℰ' r₀) (hα : HasDerivAt α α' r₀)
    (hβ : HasDerivAt β β' r₀) {θ : ℝ}
    (hPE : HasDerivAt (fun r => orbitMomentum m (fun y => V (r, y)) (α r) (β r) θ) PE r₀) :
    orbitMomentum m (fun y => V (r₀, y)) (α r₀) (β r₀) θ * PE / m +
      (slopeOf V (r₀, orbitPosition (α r₀) (β r₀) θ) *
          ((α' + β') / 2 - (β' - α') / 2 * Real.cos θ) +
        fderiv ℝ V (r₀, orbitPosition (α r₀) (β r₀) θ) (1, 0)) = ℰ' := by
  have h1 := (hPE.mul hPE).div_const (2 * m)
  have hcurve : HasDerivAt (fun r : ℝ => ((r, orbitPosition (α r) (β r) θ) : ℝ × ℝ))
      ((1 : ℝ), (α' + β') / 2 - (β' - α') / 2 * Real.cos θ) r₀ :=
    (hasDerivAt_id r₀).prodMk (hasDerivAt_orbitPosition_energy hα hβ θ)
  have h2 := HasFDerivAt.comp_hasDerivAt r₀
    (hV.differentiable (by simp) (r₀, orbitPosition (α r₀) (β r₀) θ)).hasFDerivAt hcurve
  have h3 := h1.add h2
  have hev : ℰ =ᶠ[𝓝 r₀] fun r =>
      orbitMomentum m (fun y => V (r, y)) (α r) (β r) θ *
          orbitMomentum m (fun y => V (r, y)) (α r) (β r) θ / (2 * m) +
        V (r, orbitPosition (α r) (β r) θ) :=
    Filter.eventually_of_mem (hJ.mem_nhds hr₀) fun r hr => by
      have he := (hw r hr).orbit_energy (contDiff_slice hV r) hm θ
      rw [pow_two] at he
      exact he.symm
  have h4 := (h3.congr_of_eventuallyEq hev).unique hℰ
  have hsplit : fderiv ℝ V (r₀, orbitPosition (α r₀) (β r₀) θ)
      ((1 : ℝ), (α' + β') / 2 - (β' - α') / 2 * Real.cos θ) =
      fderiv ℝ V (r₀, orbitPosition (α r₀) (β r₀) θ) (1, 0) +
        ((α' + β') / 2 - (β' - α') / 2 * Real.cos θ) *
          slopeOf V (r₀, orbitPosition (α r₀) (β r₀) θ) := by
    have e : (((1 : ℝ), (α' + β') / 2 - (β' - α') / 2 * Real.cos θ) : ℝ × ℝ) =
        ((1 : ℝ), (0 : ℝ)) +
          ((α' + β') / 2 - (β' - α') / 2 * Real.cos θ) • ((0 : ℝ), (1 : ℝ)) := by
      simp
    rw [e, map_add, map_smul, smul_eq_mul, slopeOf]
  rw [hsplit] at h4
  linear_combination h4

/-- The derivative of the area along a family of wells with a real parameter:
`dA/dr = ∮ (ℰ′ − ∂V/∂r) dt`. -/
theorem hasDerivAt_orbitArea_family (hV : ContDiff ℝ ∞ V) (hm : 0 < m) (hJ : IsOpen J)
    (hℰ : ContDiffOn ℝ ∞ ℰ J) (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ r ∈ J, IsWell (fun y => V (r, y)) (ℰ r) (α r) (β r)) {r₀ : ℝ} (hr₀ : r₀ ∈ J) :
    HasDerivAt (fun r => orbitArea m (fun y => V (r, y)) (α r) (β r))
      (∫ θ in (0 : ℝ)..2 * π, orbitRate m (fun y => V (r₀, y)) (α r₀) (β r₀) θ *
        (deriv ℰ r₀ - fderiv ℝ V (r₀, orbitPosition (α r₀) (β r₀) θ) (1, 0))) r₀ := by
  have h₀ := hw r₀ hr₀
  have hU₀ := contDiff_slice hV r₀
  have hαd : HasDerivAt α (deriv α r₀) r₀ :=
    ((hα.contDiffAt (hJ.mem_nhds hr₀)).differentiableAt (by simp)).hasDerivAt
  have hβd : HasDerivAt β (deriv β r₀) r₀ :=
    ((hβ.contDiffAt (hJ.mem_nhds hr₀)).differentiableAt (by simp)).hasDerivAt
  have hℰd : HasDerivAt ℰ (deriv ℰ r₀) r₀ :=
    ((hℰ.contDiffAt (hJ.mem_nhds hr₀)).differentiableAt (by simp)).hasDerivAt
  have hO : IsOpen (Prod.fst ⁻¹' J : Set (ℝ × ℝ)) := hJ.preimage continuous_fst
  have hαO : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => α p.1) (Prod.fst ⁻¹' J) :=
    hα.comp contDiffOn_fst fun p hp => hp
  have hβO : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => β p.1) (Prod.fst ⁻¹' J) :=
    hβ.comp contDiffOn_fst fun p hp => hp
  have hsin : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Real.sin p.2) (Prod.fst ⁻¹' J) :=
    (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  have hP := contDiffOn_orbitMomentum_family_param hV m hα hβ hw
  have hF : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      orbitMomentum m (fun y => V (p.1, y)) (α p.1) (β p.1) p.2 *
        ((β p.1 - α p.1) / 2 * Real.sin p.2)) (Prod.fst ⁻¹' J) :=
    hP.mul (((hβO.sub hαO).div_const 2).mul hsin)
  have hline : ∀ θ : ℝ, HasDerivAt (fun r : ℝ => (r, θ)) ((1 : ℝ), (0 : ℝ)) r₀ := fun θ =>
    (hasDerivAt_id r₀).prodMk (hasDerivAt_const r₀ θ)
  have hPE : ∀ θ : ℝ, HasDerivAt
      (fun r => orbitMomentum m (fun y => V (r, y)) (α r) (β r) θ)
      (fderiv ℝ (fun p : ℝ × ℝ =>
        orbitMomentum m (fun y => V (p.1, y)) (α p.1) (β p.1) p.2) (r₀, θ) (1, 0)) r₀ := by
    intro θ
    have hd : DifferentiableAt ℝ (fun p : ℝ × ℝ =>
        orbitMomentum m (fun y => V (p.1, y)) (α p.1) (β p.1) p.2) (r₀, θ) :=
      (hP.contDiffAt (hO.mem_nhds (show (r₀, θ) ∈ Prod.fst ⁻¹' J from hr₀))).differentiableAt
        (by simp)
    exact HasFDerivAt.comp_hasDerivAt (f := fun r : ℝ => (r, θ)) r₀ hd.hasFDerivAt (hline θ)
  have hr : HasDerivAt (fun r => (β r - α r) / 2) ((deriv β r₀ - deriv α r₀) / 2) r₀ :=
    (hβd.sub hαd).div_const 2
  have henergy := fun θ : ℝ =>
    orbitMomentum_mul_deriv_param hV hm hJ hw hr₀ hℰd hαd hβd (hPE θ)
  have hD : ∀ θ ∈ uIcc (0 : ℝ) (2 * π), HasDerivAt
      (fun r => (fun p : ℝ × ℝ => orbitMomentum m (fun y => V (p.1, y)) (α p.1) (β p.1) p.2 *
        ((β p.1 - α p.1) / 2 * Real.sin p.2)) (r, θ))
      ((fun θ => fderiv ℝ (fun p : ℝ × ℝ =>
          orbitMomentum m (fun y => V (p.1, y)) (α p.1) (β p.1) p.2) (r₀, θ) (1, 0) *
            ((β r₀ - α r₀) / 2 * Real.sin θ) +
        orbitMomentum m (fun y => V (r₀, y)) (α r₀) (β r₀) θ *
          ((deriv β r₀ - deriv α r₀) / 2 * Real.sin θ)) θ) r₀ :=
    fun θ _ => (hPE θ).mul (hr.mul_const (Real.sin θ))
  have hmain := Variational.hasDerivAt_intervalIntegral_of_contDiffAt
    (fun θ _ => (hF.contDiffAt (hO.mem_nhds (show (r₀, θ) ∈ Prod.fst ⁻¹' J from hr₀))).of_le
      (by simp)) hD
  refine hmain.congr_deriv ?_
  have hG : ∀ θ : ℝ, HasDerivAt
      (fun θ => orbitMomentum m (fun y => V (r₀, y)) (α r₀) (β r₀) θ *
        ((deriv α r₀ + deriv β r₀) / 2 - (deriv β r₀ - deriv α r₀) / 2 * Real.cos θ))
      (-(orbitRate m (fun y => V (r₀, y)) (α r₀) (β r₀) θ *
            slopeOf V (r₀, orbitPosition (α r₀) (β r₀) θ)) *
          ((deriv α r₀ + deriv β r₀) / 2 - (deriv β r₀ - deriv α r₀) / 2 * Real.cos θ) +
        orbitMomentum m (fun y => V (r₀, y)) (α r₀) (β r₀) θ *
          ((deriv β r₀ - deriv α r₀) / 2 * Real.sin θ)) θ := by
    intro θ
    have hx : HasDerivAt (fun θ : ℝ => (deriv α r₀ + deriv β r₀) / 2 -
        (deriv β r₀ - deriv α r₀) / 2 * Real.cos θ)
        ((deriv β r₀ - deriv α r₀) / 2 * Real.sin θ) θ := by
      refine (((Real.hasDerivAt_cos θ).const_mul ((deriv β r₀ - deriv α r₀) / 2)).const_sub
        ((deriv α r₀ + deriv β r₀) / 2)).congr_deriv ?_
      ring
    have hp := h₀.hasDerivAt_orbitMomentum hU₀ m θ
    rw [deriv_slice hV r₀] at hp
    exact hp.mul hx
  have hpt : ∀ θ : ℝ,
      fderiv ℝ (fun p : ℝ × ℝ =>
          orbitMomentum m (fun y => V (p.1, y)) (α p.1) (β p.1) p.2) (r₀, θ) (1, 0) *
          ((β r₀ - α r₀) / 2 * Real.sin θ) +
        orbitMomentum m (fun y => V (r₀, y)) (α r₀) (β r₀) θ *
          ((deriv β r₀ - deriv α r₀) / 2 * Real.sin θ) =
      orbitRate m (fun y => V (r₀, y)) (α r₀) (β r₀) θ *
          (deriv ℰ r₀ - fderiv ℝ V (r₀, orbitPosition (α r₀) (β r₀) θ) (1, 0)) +
        (-(orbitRate m (fun y => V (r₀, y)) (α r₀) (β r₀) θ *
              slopeOf V (r₀, orbitPosition (α r₀) (β r₀) θ)) *
            ((deriv α r₀ + deriv β r₀) / 2 - (deriv β r₀ - deriv α r₀) / 2 * Real.cos θ) +
          orbitMomentum m (fun y => V (r₀, y)) (α r₀) (β r₀) θ *
            ((deriv β r₀ - deriv α r₀) / 2 * Real.sin θ)) := by
    intro θ
    have htan := h₀.orbitRate_mul_orbitMomentum hU₀ hm θ
    have hen := henergy θ
    rw [← htan]
    linear_combination (orbitRate m (fun y => V (r₀, y)) (α r₀) (β r₀) θ) * hen
  have hcrate : Continuous (orbitRate m (fun y => V (r₀, y)) (α r₀) (β r₀)) :=
    (h₀.contDiff_orbitRate hU₀ m).continuous
  have hcX : Continuous fun θ => orbitPosition (α r₀) (β r₀) θ :=
    (contDiff_orbitPosition _ _).continuous
  have hcDV : Continuous fun θ => fderiv ℝ V (r₀, orbitPosition (α r₀) (β r₀) θ) (1, 0) :=
    ((hV.continuous_fderiv (by simp)).comp (continuous_const.prodMk hcX)).clm_apply
      continuous_const
  have hcslope : Continuous fun θ => slopeOf V (r₀, orbitPosition (α r₀) (β r₀) θ) :=
    (contDiff_slopeOf hV).continuous.comp (continuous_const.prodMk hcX)
  have hc1 : Continuous fun θ => orbitRate m (fun y => V (r₀, y)) (α r₀) (β r₀) θ *
      (deriv ℰ r₀ - fderiv ℝ V (r₀, orbitPosition (α r₀) (β r₀) θ) (1, 0)) :=
    hcrate.mul (continuous_const.sub hcDV)
  have hcG : Continuous fun θ =>
      -(orbitRate m (fun y => V (r₀, y)) (α r₀) (β r₀) θ *
            slopeOf V (r₀, orbitPosition (α r₀) (β r₀) θ)) *
          ((deriv α r₀ + deriv β r₀) / 2 - (deriv β r₀ - deriv α r₀) / 2 * Real.cos θ) +
        orbitMomentum m (fun y => V (r₀, y)) (α r₀) (β r₀) θ *
          ((deriv β r₀ - deriv α r₀) / 2 * Real.sin θ) :=
    ((hcrate.mul hcslope).neg.mul (continuous_const.sub
      (continuous_const.mul Real.continuous_cos))).add
        ((h₀.continuous_orbitMomentum hU₀ m).mul (continuous_const.mul Real.continuous_sin))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 2 * π)
    (fun θ _ => hG θ) (hcG.intervalIntegrable _ _)
  have hzero : orbitMomentum m (fun y => V (r₀, y)) (α r₀) (β r₀) (2 * π) = 0 := by
    have e : (2 * π : ℝ) = 0 + 2 * π := by ring
    rw [e, orbitMomentum_add_two_pi, orbitMomentum_zero]
  rw [intervalIntegral.integral_congr fun θ _ => hpt θ,
    intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hcG.intervalIntegrable _ _),
    hftc, hzero, orbitMomentum_zero]
  ring

end RealParameter

/-! ### The derivative of the area in a direction of the parameter -/

section Directional

variable {ℰ : P → ℝ} {J : Set P} {α β : P → ℝ} {m : ℝ}

omit [FiniteDimensional ℝ P] in
theorem hasDerivAt_line (s₀ u : P) : HasDerivAt (fun r : ℝ => s₀ + r • u) u 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add s₀

omit [FiniteDimensional ℝ P] in
/-- The derivative of the area along a line of parameters. -/
theorem hasDerivAt_orbitArea_line (hV : ContDiff ℝ ∞ V) (hm : 0 < m) (hJ : IsOpen J)
    (hℰ : ContDiff ℝ ∞ ℰ) (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ s ∈ J, IsWell (fun y => V (s, y)) (ℰ s) (α s) (β s)) {s₀ : P} (hs₀ : s₀ ∈ J)
    (u : P) :
    HasDerivAt (fun r : ℝ => orbitArea m (fun y => V (s₀ + r • u, y)) (α (s₀ + r • u))
        (β (s₀ + r • u)))
      (∫ θ in (0 : ℝ)..2 * π, orbitRate m (fun y => V (s₀, y)) (α s₀) (β s₀) θ *
        (fderiv ℝ ℰ s₀ u - fderiv ℝ V (s₀, orbitPosition (α s₀) (β s₀) θ) (u, 0))) 0 := by
  have hline : ContDiff ℝ ∞ fun r : ℝ => s₀ + r • u :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hVL : ContDiff ℝ ∞ fun q : ℝ × ℝ => V (s₀ + q.1 • u, q.2) :=
    hV.comp ((contDiff_const.add (contDiff_fst.smul contDiff_const)).prodMk contDiff_snd)
  have hJL : IsOpen ((fun r : ℝ => s₀ + r • u) ⁻¹' J) := hJ.preimage hline.continuous
  have h0 : (0 : ℝ) ∈ (fun r : ℝ => s₀ + r • u) ⁻¹' J := by
    simpa using hs₀
  have h := hasDerivAt_orbitArea_family (V := fun q : ℝ × ℝ => V (s₀ + q.1 • u, q.2))
    (ℰ := fun r => ℰ (s₀ + r • u)) (α := fun r => α (s₀ + r • u))
    (β := fun r => β (s₀ + r • u)) hVL hm hJL (hℰ.comp hline).contDiffOn
    (hα.comp hline.contDiffOn fun r hr => hr) (hβ.comp hline.contDiffOn fun r hr => hr)
    (fun r hr => hw (s₀ + r • u) hr) h0
  have hℰd : deriv (fun r : ℝ => ℰ (s₀ + r • u)) 0 = fderiv ℝ ℰ s₀ u := by
    have h1 : HasFDerivAt ℰ (fderiv ℝ ℰ s₀) (s₀ + (0 : ℝ) • u) := by
      simpa using (hℰ.differentiable (by simp) s₀).hasFDerivAt
    exact (HasFDerivAt.comp_hasDerivAt (0 : ℝ) h1 (hasDerivAt_line s₀ u)).deriv
  have hVd : ∀ x : ℝ, fderiv ℝ (fun q : ℝ × ℝ => V (s₀ + q.1 • u, q.2)) (0, x) (1, 0) =
      fderiv ℝ V (s₀, x) (u, 0) := by
    intro x
    have h1 : HasDerivAt (fun r : ℝ => ((r, x) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) 0 :=
      (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) x)
    have h2 := HasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (hVL.differentiable (by simp) ((0 : ℝ), x)).hasFDerivAt h1
    have h3 : HasDerivAt (fun r : ℝ => ((s₀ + r • u, x) : P × ℝ)) (u, (0 : ℝ)) 0 :=
      (hasDerivAt_line s₀ u).prodMk (hasDerivAt_const (0 : ℝ) x)
    have h4 : HasFDerivAt V (fderiv ℝ V (s₀, x)) (s₀ + (0 : ℝ) • u, x) := by
      simpa using (hV.differentiable (by simp) (s₀, x)).hasFDerivAt
    have h5 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h4 h3
    exact h2.unique h5
  simp only [zero_smul, add_zero] at h
  rw [hℰd] at h
  simp only [hVd] at h
  exact h

/-- The derivative of the area as a function of the parameter:
`dA(u) = ∮ (dℰ(u) − ∂V/∂s (u)) dt`. -/
theorem fderiv_orbitArea_family (hV : ContDiff ℝ ∞ V) (hm : 0 < m) (hJ : IsOpen J)
    (hℰ : ContDiff ℝ ∞ ℰ) (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ s ∈ J, IsWell (fun y => V (s, y)) (ℰ s) (α s) (β s)) {s₀ : P} (hs₀ : s₀ ∈ J)
    (u : P) :
    fderiv ℝ (fun s => orbitArea m (fun y => V (s, y)) (α s) (β s)) s₀ u =
      ∫ θ in (0 : ℝ)..2 * π, orbitRate m (fun y => V (s₀, y)) (α s₀) (β s₀) θ *
        (fderiv ℝ ℰ s₀ u - fderiv ℝ V (s₀, orbitPosition (α s₀) (β s₀) θ) (u, 0)) := by
  have hA : DifferentiableAt ℝ (fun s => orbitArea m (fun y => V (s, y)) (α s) (β s)) s₀ :=
    ((contDiffOn_orbitArea_family hV m hJ hα hβ hw).contDiffAt
      (hJ.mem_nhds hs₀)).differentiableAt (by simp)
  have h1 : HasFDerivAt (fun s => orbitArea m (fun y => V (s, y)) (α s) (β s))
      (fderiv ℝ (fun s => orbitArea m (fun y => V (s, y)) (α s) (β s)) s₀)
      (s₀ + (0 : ℝ) • u) := by
    simpa using hA.hasFDerivAt
  have h2 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h1 (hasDerivAt_line s₀ u)
  exact h2.unique (hasDerivAt_orbitArea_line hV hm hJ hℰ hα hβ hw hs₀ u)

end Directional

end ProjectAInos.Mechanics.OneDim
