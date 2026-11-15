import HodgeLean.Adapters.KleimanProductIntersectionChart
import HodgeLean.Adapters.KleimanProductLocal
import HodgeLean.Adapters.KleimanSubmersionAnalysis
import HodgeLean.Adapters.KleimanSubmersionLocal

/-! # Submersion of the transverse chart pair

At a point of a component of a transverse translated intersection that avoids the three singular
loci, the pair of normal maps of the two primes is a submersion. The proof compares the
analytic differentials of the pair with the étale coordinates of the smooth intersection scheme.
-/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Filter
open Topology
open scoped ContDiff Manifold

namespace HodgeLean.Adapters

/-- Chart existence at a point of one intersection component off both singular loci and off the
other components, inside a prescribed open neighborhood of the point.
Source: SGA 1, Exposé XII, 3.1; the holomorphic implicit function theorem; Hartshorne,
*Algebraic Geometry*, I, 1.5. -/
theorem hc9k_exists_transverse_chart_in
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p q : ℕ) (x y : X.left) (hx : Order.coheight x = p) (hy : Order.coheight y = q)
    (w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme)
    (_hw : closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left y).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left y).subscheme)
    (a : ComplexPoint X)
    (ha : a ∈ cycleComponentAnalyticClosedSupport X
      ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w))
    (hax : a ∉ cycleComponentSingularAnalyticClosedFiltration X x 0)
    (hay : a ∉ cycleComponentSingularAnalyticClosedFiltration X y 0)
    (hunique : ∀ w' : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
      closure ({w'} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left y).subscheme →
      a ∈ cycleComponentAnalyticClosedSupport X
        ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w') → w' = w)
    (B : Opens (ComplexPoint X)) (haB : a ∈ B) :
    ∃ (U : Opens (ComplexPoint X)) (_ : a ∈ U) (_ : U ≤ B) (f : C(U, Fin p → ℂ))
      (h : C(U, Fin q → ℂ)),
      (∀ u : U, f u = 0 ↔ u.1 ∈ cycleComponentAnalyticClosedSupport X x) ∧
      ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin p → ℂ) ω f ∧
      (∀ u : U, f u = 0 →
        Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin p → ℂ) f u)) ∧
      (∀ u : U, h u = 0 ↔ u.1 ∈ cycleComponentAnalyticClosedSupport X y) ∧
      ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin q → ℂ) ω h ∧
      (∀ u : U, h u = 0 →
        Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin q → ℂ) h u)) ∧
      (∀ u : U, hc9k_appendCoordinates f h u = 0 ↔
        u.1 ∈ cycleComponentAnalyticClosedSupport X
          ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w)) := by
  classical
  let I := ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y
  have haxy := hc9k_charts_intersection_support_le X x y w ha
  obtain ⟨Vx, haVx, gx, hgx0, hgx⟩ :=
    hc9k_exists_component_normalMap X d p x hx a haxy.1 hax
  obtain ⟨Vy, haVy, gy, hgy0, hgy⟩ :=
    hc9k_exists_component_normalMap X d q y hy a haxy.2 hay
  let := ccm12_isNoetherian X
  have hfin := ccm11_intersection_components_finite X.left (ccm3_primeIdeal X.left x)
    (ccm3_primeIdeal X.left y)
  let T : Set I.subscheme := {w' | closure ({w'} : Set I.subscheme) ∈
    irreducibleComponents I.subscheme ∧ w' ≠ w}
  have hT : T.Finite := hfin.subset fun w' hw' => hw'.1
  let C : Set (ComplexPoint X) := ⋃ w' ∈ T,
    (cycleComponentAnalyticClosedSupport X (I.subschemeι w') : Set (ComplexPoint X))
  have hC : IsClosed C := hT.isClosed_biUnion fun w' _ =>
    (cycleComponentAnalyticClosedSupport X (I.subschemeι w')).isClosed
  let O : Opens (ComplexPoint X) := ⟨Cᶜ, hC.isOpen_compl⟩
  let U := Vx ⊓ Vy ⊓ O ⊓ B
  have haO : a ∈ O := by
    intro haC
    obtain ⟨w', hw'T, haw'⟩ := Set.mem_iUnion₂.mp haC
    exact hw'T.2 (hunique w' hw'T.1 haw')
  have haU : a ∈ U := ⟨⟨⟨haVx, haVy⟩, haO⟩, haB⟩
  obtain ⟨f, hfg, hf0, hfhol, hfsub⟩ :=
    hc9k_restrict_normalMap X d p x Vx U (inf_le_left.trans (inf_le_left.trans inf_le_left)) gx
      hgx0 hgx
  obtain ⟨h, hhg, hh0, hhhol, hhsub⟩ :=
    hc9k_restrict_normalMap X d q y Vy U (inf_le_left.trans (inf_le_left.trans inf_le_right)) gy
      hgy0 hgy
  refine ⟨U, haU, inf_le_right, f, h, hf0, hfhol, hfsub, hh0, hhhol, hhsub, fun u => ?_⟩
  change Fin.append (f u) (h u) = 0 ↔ _
  rw [hc9k_append_eq_zero_iff, hf0, hh0]
  constructor
  · rintro ⟨hux, huy⟩
    obtain ⟨w', hw', huw'⟩ := hc9k_mem_some_component_support X x y u.1 hux huy
    by_cases hww : w' = w
    · exact hww ▸ huw'
    · exact absurd (Set.mem_iUnion₂.mpr ⟨w', ⟨hw', hww⟩, huw'⟩) u.2.1.2
  · intro huw
    exact hc9k_charts_intersection_support_le X x y w huw

/-- A map on a complex manifold, holomorphic near a point with surjective manifold derivative
there, has surjective derivative in the chart at the point. -/
theorem hc9k_chart_rep_fderiv_ambient {d c : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) ω M] (g : M → Fin c → ℂ)
    (x : M)
    (hg : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin c → ℂ) ω g x)
    (hsub : Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin c → ℂ) g x)) :
    DifferentiableAt ℂ (fun w => g ((chartAt (Fin d → ℂ) x).symm w))
      (chartAt (Fin d → ℂ) x x) ∧
    Function.Surjective (fderiv ℂ (fun w => g ((chartAt (Fin d → ℂ) x).symm w))
      (chartAt (Fin d → ℂ) x x)) := by
  have hm : MDifferentiableAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin c → ℂ) g x :=
    hg.mdifferentiableAt (by simp)
  have hd := hm.differentiableWithinAt_writtenInExtChartAt
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp, modelWithCornersSelf_coe, Set.range_id, differentiableWithinAt_univ,
    extChartAt_coe_symm, extChartAt_coe, modelWithCornersSelf_coe_symm, Function.comp_id] at hd
  refine ⟨hd, ?_⟩
  rw [hm.mfderiv] at hsub
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp, modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ,
    extChartAt_coe_symm, extChartAt_coe, modelWithCornersSelf_coe_symm, Function.comp_id] at hsub
  exact hsub

/-- The analytic half of the transverse-submersion lemma. Suppose a smooth complex scheme `Y`
maps to `X` with image in `S_x ∩ S_y`, through a point over `a`, and suppose on a Zariski open
around `a` every chart coordinate of `X` at `a`, times a function nonvanishing at `a`, is a
combination of functions `u_j` minus their values at `a`, plus a function vanishing on `S_x` and a
function vanishing on `S_y`, where the `u_j` restrict on `Y` to its chart coordinates. If `S_w`
has a holomorphic normal map at `a` and `(f, h)` cuts out `S_w` near `a`, then `(f, h)` is a
submersion at `a`. -/
theorem hc9k_pair_submersion_of_local_data
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] (p q : ℕ)
    (Sx Sy Sw : Set (ComplexPoint X))
    (U : Opens (ComplexPoint X))
    (f : C(U, Fin p → ℂ)) (hfzero : ∀ u : U, f u = 0 ↔ u.1 ∈ Sx)
    (hfhol : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin p → ℂ) ω f)
    (hfsub : ∀ u : U, f u = 0 →
      Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin p → ℂ) f u))
    (h : C(U, Fin q → ℂ)) (hhzero : ∀ u : U, h u = 0 ↔ u.1 ∈ Sy)
    (hhhol : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin q → ℂ) ω h)
    (hhsub : ∀ u : U, h u = 0 →
      Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin q → ℂ) h u))
    (hzero : ∀ u : U, hc9k_appendCoordinates f h u = 0 ↔ u.1 ∈ Sw)
    (a : U) (ha : hc9k_appendCoordinates f h a = 0)
    (Vw : Opens (ComplexPoint X)) (haVw : a.1 ∈ Vw) (gw : ComplexPoint X → Fin (p + q) → ℂ)
    (hgw0 : ∀ y ∈ Vw, gw y = 0 ↔ y ∈ Sw)
    (hgw : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin (p + q) → ℂ) ω gw a.1 ∧
      Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin (p + q) → ℂ) gw a.1))
    (n : ℕ) (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension n Y.hom] (j : Y ⟶ X)
    (zY : ComplexPoint Y) (hjz : Point.map j zY = a.1)
    (hjS : ∀ yy : ComplexPoint Y, Point.map j yy ∈ Sx ∧ Point.map j yy ∈ Sy)
    (W : X.left.Opens) (haW : a.1 ∈ Point.overOpen W)
    (σ : Fin d → Γ(X.left, W)) (u : Fin n → Γ(X.left, W))
    (b : Fin d → Fin n → Γ(X.left, W))
    (α β : Fin d → Γ(X.left, W))
    (hσ : ∀ k, Point.evaluate W (σ k) a.1 ≠ 0)
    (hrel : ∀ k, ∀ pt ∈ Point.overOpen W, pt ∈ (localChart X d a.1).source →
      Point.evaluate W (σ k) pt * (localChart X d a.1 pt k - localChart X d a.1 a.1 k) =
        ∑ i, Point.evaluate W (b k i) pt *
            (Point.evaluate W (u i) pt - Point.evaluate W (u i) a.1) +
          Point.evaluate W (α k) pt + Point.evaluate W (β k) pt)
    (hα : ∀ k, ∀ pt ∈ Point.overOpen W, pt ∈ Sx → Point.evaluate W (α k) pt = 0)
    (hβ : ∀ k, ∀ pt ∈ Point.overOpen W, pt ∈ Sy → Point.evaluate W (β k) pt = 0)
    (hu : ∀ i, ∀ᶠ v in 𝓝 (localChart Y n zY zY),
      Point.evaluate W (u i) (Point.map j ((localChart Y n zY).symm v)) = v i) :
    Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin (p + q) → ℂ)
      (hc9k_appendCoordinates f h) a) := by
  classical
  -- charts at `a`
  let e := localChart X d a.1
  let C := chartAt (Fin d → ℂ) a
  let w₀ := e a.1
  have hae : a.1 ∈ e.source := mem_localChart_source X d a.1
  have hw₀t : w₀ ∈ e.target := e.map_source hae
  have hCa : C a = w₀ := rfl
  have haC : a ∈ C.source := mem_chart_source _ a
  have hCt : C.target ∈ 𝓝 w₀ := C.open_target.mem_nhds (C.map_source haC)
  have hCs : ∀ w ∈ C.target, ((C.symm w : U) : ComplexPoint X) = e.symm w :=
    fun w hw => (e.subtypeRestr_symm_eqOn ⟨a⟩ hw).symm
  have hCw₀ : C.symm w₀ = a := C.left_inv haC
  have hew₀ : e.symm w₀ = a.1 := e.left_inv hae
  have hesymm : Tendsto e.symm (𝓝 w₀) (𝓝 a.1) := by
    have := e.continuousAt_symm hw₀t
    rwa [ContinuousAt, hew₀] at this
  have hevW : ∀ᶠ w in 𝓝 w₀, e.symm w ∈ Point.overOpen W :=
    hesymm.eventually ((Point.isOpen_overOpen W).mem_nhds haW)
  have hevS : ∀ᶠ w in 𝓝 w₀, e.symm w ∈ e.source :=
    hesymm.eventually (e.open_source.mem_nhds hae)
  have hevT : ∀ᶠ w in 𝓝 w₀, w ∈ e.target := e.open_target.mem_nhds hw₀t
  have haW' : e.symm w₀ ∈ Point.overOpen W := hew₀ ▸ haW
  -- evaluated sections are analytic in the chart
  have hev : ∀ s : Γ(X.left, W), AnalyticAt ℂ (fun w => Point.evaluate W s (e.symm w)) w₀ :=
    fun s => analyticAt_localChart_symm_evaluate X d a.1 hw₀t W s haW'
  -- the zero conditions at `a`
  have ha' : Fin.append (f a) (h a) = 0 := ha
  rw [hc9k_append_eq_zero_iff] at ha'
  -- chart representatives of `f`, `h` and the pair
  let F : (Fin d → ℂ) → Fin p → ℂ := fun w => f (C.symm w)
  let H : (Fin d → ℂ) → Fin q → ℂ := fun w => h (C.symm w)
  let P : (Fin d → ℂ) → Fin (p + q) → ℂ := fun w => hc9k_appendCoordinates f h (C.symm w)
  have hPhol := hc9k_appendCoordinates_contMDiff f h hfhol hhhol
  have hP := hc9k_chart_rep_hasStrictFDerivAt U (hc9k_appendCoordinates f h) hPhol a
  have hF := hc9k_chart_rep_hasStrictFDerivAt U f hfhol a
  have hH := hc9k_chart_rep_hasStrictFDerivAt U h hhhol a
  have hFs := (hc9k_chart_rep_fderiv U f hfhol a (hfsub a ha'.1)).2
  have hHs := (hc9k_chart_rep_fderiv U h hhhol a (hhsub a ha'.2)).2
  let P' := fderiv ℂ P w₀
  let F' := fderiv ℂ F w₀
  let H' := fderiv ℂ H w₀
  -- the derivative of the pair has the derivatives of `f` and `h` as blocks
  let head : (Fin (p + q) → ℂ) →L[ℂ] (Fin p → ℂ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.castAdd q i)
  let tail : (Fin (p + q) → ℂ) →L[ℂ] (Fin q → ℂ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.natAdd p i)
  have hFP : F = fun w => head (P w) := by
    funext w
    funext i
    change f (C.symm w) i = Fin.append (f (C.symm w)) (h (C.symm w)) (Fin.castAdd q i)
    rw [Fin.append_left]
  have hHP : H = fun w => tail (P w) := by
    funext w
    funext i
    change h (C.symm w) i = Fin.append (f (C.symm w)) (h (C.symm w)) (Fin.natAdd p i)
    rw [Fin.append_right]
  have hF'P : F' = head.comp P' := by
    have h1 : HasFDerivAt F (head.comp P') w₀ := by
      rw [hFP]
      exact head.hasFDerivAt.comp w₀ hP.hasFDerivAt
    exact h1.fderiv
  have hH'P : H' = tail.comp P' := by
    have h1 : HasFDerivAt H (tail.comp P') w₀ := by
      rw [hHP]
      exact tail.hasFDerivAt.comp w₀ hP.hasFDerivAt
    exact h1.fderiv
  have hFw₀ : F w₀ = 0 := by
    change f (C.symm w₀) = 0
    rw [hCw₀]
    exact ha'.1
  have hHw₀ : H w₀ = 0 := by
    change h (C.symm w₀) = 0
    rw [hCw₀]
    exact ha'.2
  -- functions vanishing on `S_x` or `S_y` have derivative vanishing on the kernels
  have hαker : ∀ k ξ, F' ξ = 0 →
      fderiv ℂ (fun w => Point.evaluate W (α k) (e.symm w)) w₀ ξ = 0 := by
    intro k ξ hξ
    refine hc9k_fderiv_eq_zero_of_mem_ker F F' w₀ hF (LinearMap.range_eq_top.mpr hFs) _
      (hev (α k)).differentiableAt ?_ ξ hξ
    filter_upwards [hCt, hevW] with w hwC hwW hFw
    rw [hFw₀] at hFw
    apply hα k _ hwW
    rw [← hCs w hwC]
    exact (hfzero _).mp hFw
  have hβker : ∀ k ξ, H' ξ = 0 →
      fderiv ℂ (fun w => Point.evaluate W (β k) (e.symm w)) w₀ ξ = 0 := by
    intro k ξ hξ
    refine hc9k_fderiv_eq_zero_of_mem_ker H H' w₀ hH (LinearMap.range_eq_top.mpr hHs) _
      (hev (β k)).differentiableAt ?_ ξ hξ
    filter_upwards [hCt, hevW] with w hwC hwW hHw
    rw [hHw₀] at hHw
    apply hβ k _ hwW
    rw [← hCs w hwC]
    exact (hhzero _).mp hHw
  -- the functions `u`
  let Û : (Fin d → ℂ) → Fin n → ℂ := fun w i => Point.evaluate W (u i) (e.symm w)
  have hÛ : AnalyticAt ℂ Û w₀ := AnalyticAt.pi fun i => hev (u i)
  let Û' := fderiv ℂ Û w₀
  have hÛi : ∀ i, HasFDerivAt (fun w => Point.evaluate W (u i) (e.symm w))
      ((ContinuousLinearMap.proj i).comp Û') w₀ :=
    hasFDerivAt_pi'.mp hÛ.differentiableAt.hasFDerivAt
  -- a vector killed by the pair and by the `u` vanishes
  have hkey : ∀ ξ, P' ξ = 0 → Û' ξ = 0 → ξ = 0 := by
    intro ξ hPξ hUξ
    have hFξ : F' ξ = 0 := by rw [hF'P]; simp [hPξ]
    have hHξ : H' ξ = 0 := by rw [hH'P]; simp [hPξ]
    funext k
    let L : (Fin d → ℂ) → ℂ := fun w => Point.evaluate W (σ k) (e.symm w) * (w k - w₀ k)
    let R : (Fin d → ℂ) → ℂ := fun w =>
      ∑ i, Point.evaluate W (b k i) (e.symm w) *
          (Point.evaluate W (u i) (e.symm w) - Point.evaluate W (u i) a.1) +
        Point.evaluate W (α k) (e.symm w) + Point.evaluate W (β k) (e.symm w)
    have hLR : L =ᶠ[𝓝 w₀] R := by
      filter_upwards [hevW, hevS, hevT] with w hwW hwS hwT
      have := hrel k (e.symm w) hwW hwS
      rw [e.right_inv hwT] at this
      exact this
    have hL : HasFDerivAt L
        (Point.evaluate W (σ k) (e.symm w₀) • (ContinuousLinearMap.proj k) +
          (w₀ k - w₀ k) • fderiv ℂ (fun w => Point.evaluate W (σ k) (e.symm w)) w₀)
        w₀ :=
      (hev (σ k)).differentiableAt.hasFDerivAt.mul
        ((hasFDerivAt_apply k w₀).sub_const (w₀ k))
    have hR : HasFDerivAt R
        ((∑ i, (Point.evaluate W (b k i) (e.symm w₀) • (ContinuousLinearMap.proj i).comp Û' +
            (Point.evaluate W (u i) (e.symm w₀) - Point.evaluate W (u i) a.1) •
              fderiv ℂ (fun w => Point.evaluate W (b k i) (e.symm w)) w₀)) +
          fderiv ℂ (fun w => Point.evaluate W (α k) (e.symm w)) w₀ +
          fderiv ℂ (fun w => Point.evaluate W (β k) (e.symm w)) w₀) w₀ := by
      refine ((HasFDerivAt.fun_sum fun i _ => ?_).fun_add
        (hev (α k)).differentiableAt.hasFDerivAt).fun_add (hev (β k)).differentiableAt.hasFDerivAt
      exact (hev (b k i)).differentiableAt.hasFDerivAt.mul ((hÛi i).sub_const _)
    have hEq := hL.unique (hR.congr_of_eventuallyEq hLR)
    have h1 := congrArg (fun M => M ξ) hEq
    simp only [add_apply, smul_apply, FunLike.coe_sum, Finset.sum_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.proj_apply, sub_self,
      zero_smul, add_zero, hew₀, hUξ, Pi.zero_apply, Finset.sum_const_zero,
      hαker k ξ hFξ, hβker k ξ hHξ, smul_eq_mul, mul_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_left (hσ k)
  have hK :
      Module.finrank ℂ (LinearMap.ker (P' : (Fin d → ℂ) →ₗ[ℂ] Fin (p + q) → ℂ)) ≤ n :=
    hc9k_finrank_le_of_inf_ker _ (Û' : (Fin d → ℂ) →ₗ[ℂ] Fin n → ℂ)
      fun ξ hξ hU => hkey ξ hξ hU
  -- the dimension count from the chart of `Y` and the normal map of `S_w`
  let eY := localChart Y n zY
  let v₀ := eY zY
  have hzY : zY ∈ eY.source := mem_localChart_source Y n zY
  have hv₀t : v₀ ∈ eY.target := eY.map_source hzY
  let J : (Fin n → ℂ) → ComplexPoint X := fun v => Point.map j (eY.symm v)
  have hJv₀ : J v₀ = a.1 := by
    change Point.map j (eY.symm (eY zY)) = a.1
    rw [eY.left_inv hzY, hjz]
  have hJt : Tendsto J (𝓝 v₀) (𝓝 a.1) := by
    have h1 := (Point.continuous_map j).continuousAt.comp (eY.continuousAt_symm hv₀t)
    have h2 : ContinuousAt J v₀ := h1
    rw [ContinuousAt, hJv₀] at h2
    exact h2
  let ψ : (Fin n → ℂ) → Fin d → ℂ := fun v => e (J v)
  have hψ : AnalyticAt ℂ ψ v₀ := by
    have hmap : Point.map j (eY.symm v₀) ∈ (localChart X d (Point.map j zY)).source := by
      rw [hjz]
      change J v₀ ∈ e.source
      rw [hJv₀]
      exact hae
    have := analyticAt_localChart_symm_map Y X j n d zY hv₀t hmap
    simp only [hjz] at this
    exact this
  have hψv₀ : ψ v₀ = w₀ := by
    change e (J v₀) = e a.1
    rw [hJv₀]
  have hJS : ∀ᶠ v in 𝓝 v₀, J v ∈ e.source := hJt.eventually (e.open_source.mem_nhds hae)
  have hJU : ∀ᶠ v in 𝓝 v₀, J v ∈ U := hJt.eventually (U.isOpen.mem_nhds a.2)
  have hJV : ∀ᶠ v in 𝓝 v₀, J v ∈ Vw := hJt.eventually (Vw.isOpen.mem_nhds haVw)
  have hUψ : (fun v => Û (ψ v)) =ᶠ[𝓝 v₀] id := by
    filter_upwards [hJS, eventually_all.mpr hu] with v hvS hvu
    funext i
    change Point.evaluate W (u i) (e.symm (e (J v))) = v i
    rw [e.left_inv hvS]
    exact hvu i
  let ψ' := fderiv ℂ ψ v₀
  have hÛψ : HasFDerivAt Û Û' (ψ v₀) := by
    rw [hψv₀]
    exact hÛ.differentiableAt.hasFDerivAt
  have hcomp : Û'.comp ψ' = ContinuousLinearMap.id ℂ (Fin n → ℂ) :=
    ((hÛψ.comp v₀ hψ.differentiableAt.hasFDerivAt).congr_of_eventuallyEq
      hUψ.symm).unique (hasFDerivAt_id v₀)
  have hψinj : Function.Injective ψ' := by
    intro v₁ v₂ hv
    have := congrArg Û' hv
    simpa only [← ContinuousLinearMap.comp_apply, hcomp, ContinuousLinearMap.id_apply] using this
  obtain ⟨hGd, hGs⟩ := hc9k_chart_rep_fderiv_ambient gw a.1 hgw.1 hgw.2
  let G : (Fin d → ℂ) → Fin (p + q) → ℂ := fun w => gw (e.symm w)
  let G' := fderiv ℂ G w₀
  have hGψ : (fun v => G (ψ v)) =ᶠ[𝓝 v₀] fun _ => 0 := by
    filter_upwards [hJS, hJU, hJV] with v hvS hvU hvV
    change gw (e.symm (e (J v))) = 0
    rw [e.left_inv hvS]
    apply (hgw0 _ hvV).mpr
    apply (hzero ⟨J v, hvU⟩).mp
    change Fin.append (f ⟨J v, hvU⟩) (h ⟨J v, hvU⟩) = 0
    rw [hc9k_append_eq_zero_iff]
    exact ⟨(hfzero _).mpr (hjS _).1, (hhzero _).mpr (hjS _).2⟩
  have hGψ' : G'.comp ψ' = 0 := by
    have hGd' : HasFDerivAt G G' (ψ v₀) := by
      rw [hψv₀]
      exact hGd.hasFDerivAt
    exact ((hGd'.comp v₀ hψ.differentiableAt.hasFDerivAt).congr_of_eventuallyEq
      hGψ.symm).unique (hasFDerivAt_const 0 v₀)
  have hdim := hc9k_add_le_of_injective_into_ker (ψ' : (Fin n → ℂ) →ₗ[ℂ] Fin d → ℂ)
    (G' : (Fin d → ℂ) →ₗ[ℂ] Fin (p + q) → ℂ) hψinj hGs
    (LinearMap.ext fun v => congrArg (fun M => M v) hGψ')
  -- conclusion
  apply hc9k_mfderiv_surjective_of_chart_rep U _ hPhol a
  apply hc9k_surjective_of_finrank_ker (P' : (Fin d → ℂ) →ₗ[ℂ] Fin (p + q) → ℂ)
  simp only [Module.finrank_fin_fun]
  omega

/-- At a zero of a chart pair on a component of a transverse translated intersection, off the
singular loci of both primes and of the component, the pair is a submersion.
Source: Kleiman, Compositio Math. 28 (1974), Theorem 2; Stacks Project, Tag 02GU; SGA 1,
Exposé XII, Proposition 3.1. -/
theorem hc9k_transverse_chart_submersion_of_charts
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p q : ℕ) (x y : X.left) (hx : Order.coheight x = p) (hy : Order.coheight y = q)
    (t : ComplexPoint X) (ht : t ∈ hc9k_transverseLocus X x y)
    (w : (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme)
    (hw : closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme)
    (U : Opens (ComplexPoint X))
    (f : C(U, Fin p → ℂ))
    (hfzero : ∀ u : U, f u = 0 ↔ u.1 ∈ cycleComponentAnalyticClosedSupport X x)
    (hfhol : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin p → ℂ) ω f)
    (hfsub : ∀ u : U, f u = 0 →
      Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin p → ℂ) f u))
    (h : C(U, Fin q → ℂ))
    (hhzero : ∀ u : U,
      h u = 0 ↔ u.1 ∈ cycleComponentAnalyticClosedSupport X (hc9k_translatePoint X t y))
    (hhhol : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin q → ℂ) ω h)
    (hhsub : ∀ u : U, h u = 0 →
      Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin q → ℂ) h u))
    (hzero : ∀ u : U, hc9k_appendCoordinates f h u = 0 ↔
      u.1 ∈ cycleComponentAnalyticClosedSupport X
        ((ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι w))
    (a : U) (ha : hc9k_appendCoordinates f h a = 0)
    (hax : a.1 ∉ cycleComponentSingularAnalyticClosedFiltration X x 0)
    (hay : a.1 ∉ cycleComponentSingularAnalyticClosedFiltration X
      (hc9k_translatePoint X t y) 0)
    (haw : a.1 ∉ cycleComponentSingularAnalyticClosedFiltration X
      ((ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι w) 0) :
    Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin (p + q) → ℂ)
      (hc9k_appendCoordinates f h) a) := by
  have ha' : Fin.append (f a) (h a) = 0 := ha
  rw [hc9k_append_eq_zero_iff] at ha'
  have haxS := (hfzero a).mp ha'.1
  have hayS := (hhzero a).mp ha'.2
  have hawS := (hzero a).mp ha
  have hcod : Order.coheight ((ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι w) = p + q := by
    have := ht.1 w hw
    rw [hx, hy] at this
    exact_mod_cast this
  obtain ⟨Vw, haVw, gw, hgw0, hgw⟩ :=
    hc9k_exists_component_normalMap X d (p + q) _ hcod a.1 hawS haw
  obtain ⟨n, Y, hY, j, zY, hjz, hjS, W, haW, σ, u, b, α, β, hσ, hrel, hα, hβ, hu⟩ :=
    hc9k_transverse_local_data X d x (hc9k_translatePoint X t y) ht.2 a.1 haxS hayS hax hay
  exact hc9k_pair_submersion_of_local_data X d p q _ _ _ U f hfzero hfhol hfsub h hhzero hhhol
    hhsub hzero a ha Vw haVw gw hgw0 (hgw a.1 haVw) n Y j zY hjz hjS W haW σ u b α β hσ hrel
    hα hβ hu

end HodgeLean.Adapters
