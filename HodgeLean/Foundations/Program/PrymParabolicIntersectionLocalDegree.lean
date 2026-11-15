import HodgeLean.Foundations.Program.PrymParabolicIntersectionLocalLift

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity
open scoped Topology
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

set_option backward.isDefEq.respectTransparency false in
theorem hga_localClass_of_inverseChart_germ {T : Type} [TopologicalSpace T]
    (y : T) (e : OpenPartialHomeomorph T (Fin 1 → ℂ)) (hy : y ∈ e.source)
    (he0 : e y = 0) (F : puncturedPair ℂ 1 ⟶ pointComplementPair y)
    (hF : Filter.EventuallyEq (𝓝 (0 : Fin 1 → ℂ))
      (fun z ↦ TopPair.Hom.fst F z) (fun z ↦ e.symm z)) :
    relativeHomologyMap ℤ 2 F (standardComplexLocalClass ℤ 1) =
      b6m_localClassOfChart ℤ 1 e y hy := by
  let r := chartRadius 1 e y hy
  let B := OpenPartialHomeomorph.univBall (0 : Fin 1 → ℂ) r
  let A := centeredComplexEmbeddingPair 1 B
    (continuous_complexUnivBall 1 0 r) (injective_complexUnivBall 1 0 r) 0
  have hB0 : B 0 = 0 := OpenPartialHomeomorph.univBall_apply_zero _ _
  have hp : relativeHomologyMap ℤ 2 A (standardComplexLocalClass ℤ 1) =
      standardComplexLocalClass ℤ 1 :=
    b6m_centeredUnivBall_preserves_localClass ℤ 1 0 r (chartRadius_pos 1 e y hy) 0
  have ht : Filter.Tendsto (fun z : Fin 1 → ℂ ↦ B z) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun z : Fin 1 → ℂ ↦ B z) := continuous_complexUnivBall 1 0 r
    simpa only [hB0] using hc.tendsto 0
  have hm : relativeHomologyMap ℤ 2 (A ≫ F) =
      relativeHomologyMap ℤ 2 (chartModelEmbeddingPair 1 e y hy) := by
    apply hga_local_maps_eq_of_eventuallyEq ℤ y 1 2
    filter_upwards [ht.eventually hF] with z hz
    change TopPair.Hom.fst F (B (z + 0) - B 0) = chartModelEmbedding 1 e y hy z
    rw [add_zero, hB0, sub_zero]
    change TopPair.Hom.fst F (B z) =
      e.symm (OpenPartialHomeomorph.univBall (e y) r z)
    rw [he0]
    exact hz
  have h := congrArg (fun m ↦ m (standardComplexLocalClass ℤ 1)) hm
  simpa only [relativeHomologyMap_comp, LinearMap.comp_apply, hp,
    b6m_localClassOfChart] using h

set_option backward.isDefEq.respectTransparency false in
theorem hga_scalarChart_localClass_eq (R : Type) [CommRing R]
    {T : Type} [TopologicalSpace T] (e e' : OpenPartialHomeomorph T ℂ)
    (x : T) (hx : x ∈ e.source) (hx' : x ∈ e'.source)
    (ρ : ℂ) (hρ : ρ ≠ 0)
    (hraw : HasDerivAt (fun z : ℂ ↦ e' (e.symm z)) ρ (e x)) :
    b6m_localClassOfChart R 1 (hga_complexCoordinateChart e) x
      (by simpa only [hga_complexCoordinateChart_source] using hx) =
    b6m_localClassOfChart R 1 (hga_complexCoordinateChart e') x
      (by simpa only [hga_complexCoordinateChart_source] using hx') := by
  let E := b6m_surfaceCoordinateEquiv
  let A : ℂ →L[ℂ] ℂ := ContinuousLinearMap.toSpanSingleton ℂ ρ
  let L := E.toContinuousLinearMap.comp (A.comp E.symm.toContinuousLinearMap)
  have hA : Function.Injective A := by
    intro a b hab
    change a * ρ = b * ρ at hab
    exact mul_right_cancel₀ hρ hab
  have hL : Function.Injective L := E.injective.comp (hA.comp E.symm.injective)
  have hraw' : HasFDerivAt (fun z : ℂ ↦ e' (e.symm z)) A (E.symm (E (e x))) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hraw.hasFDerivAt
  have hderiv := E.hasFDerivAt.comp (E (e x))
    (hraw'.comp (E (e x)) E.symm.hasFDerivAt)
  apply b6m_localClassOfChart_eq_of_hasFDerivAt_transition R 1
    (hga_complexCoordinateChart e) (hga_complexCoordinateChart e') x _ _ L hL
  apply (piHasFDerivAt_iff_normed 1 _ L _).mpr
  exact hderiv

set_option backward.isDefEq.respectTransparency false in
open scoped Manifold ContDiff in
theorem hga_biholomorphic_chart_localClass {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T]
    [IsManifold 𝓘(ℂ, ℂ) ω T] (q : OpenPartialHomeomorph ℂ T) (h0 : 0 ∈ q.source)
    (hq : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω q 0)
    (hi : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω q.symm (q 0)) :
    b6m_localClassOfChart ℤ 1 (hga_complexCoordinateChart q.symm) (q 0)
      (by simpa only [hga_complexCoordinateChart_source, OpenPartialHomeomorph.symm_source]
        using q.map_source h0) =
      b6m_surfaceLocalClass ℤ (q 0) := by
  let E := chartAt ℂ (q 0)
  have hx : q 0 ∈ E.source := mem_chart_source ℂ (q 0)
  have hE : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω E (q 0) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (q 0)) hx
  let A := q.trans E
  have hA0 : 0 ∈ A.source := ⟨h0, hx⟩
  have hf : DifferentiableAt ℂ A 0 :=
    (hE.comp 0 hq).contDiffAt.differentiableAt (by norm_num)
  have hEi : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω E.symm (E (q 0)) :=
    (contMDiffOn_chart_symm (I := 𝓘(ℂ, ℂ)) (n := ω) (x := q 0)).contMDiffAt
      (E.open_target.mem_nhds (E.map_source hx))
  have hi' : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω q.symm (E.symm (E (q 0))) := by
    rw [E.left_inv hx]
    exact hi
  have hg : DifferentiableAt ℂ A.symm (A 0) :=
    (hi'.comp (E (q 0)) hEi).contDiffAt.differentiableAt (by norm_num)
  have hn := hga_complexChart_deriv_ne_zero A 0 hA0 hf hg
  have hd : HasDerivAt (fun z : ℂ ↦ E (q z)) (deriv A 0) (q.symm (q 0)) := by
    rw [q.left_inv h0]
    exact hf.hasDerivAt
  exact hga_scalarChart_localClass_eq ℤ q.symm E (q 0) (q.map_source h0) hx _ hn hd

set_option backward.isDefEq.respectTransparency false in
open scoped Manifold ContDiff in
theorem hga_planeLift_localClass {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T]
    [IsManifold 𝓘(ℂ, ℂ) ω T] [CompactSpace T] [ConnectedSpace T]
    (y : T) (e : C(ℂ, T)) (he0 : e 0 = y) (k : T → OnePoint ℂ)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k) (c : ℂ)
    (hp : ∀ᶠ z : ℂ in 𝓝 0, k (e z) = ((z + c : ℂ) : OnePoint ℂ))
    (F : puncturedPair ℂ 1 ⟶ pointComplementPair y)
    (hFe : ∀ z : Fin 1 → ℂ, TopPair.Hom.fst F z = e (z 0)) :
    relativeHomologyMap ℤ 2 F (standardComplexLocalClass ℤ 1) =
      b6m_surfaceLocalClass ℤ y := by
  obtain ⟨q, hq0, hqe0, hqe, hq, hi⟩ := hga_holomorphic_lift_coordinates e k hk c hp
  have hqy : q 0 = y := hqe0.trans he0
  let E := hga_complexCoordinateChart q.symm
  have hy : y ∈ E.source := by
    rw [hga_complexCoordinateChart_source, OpenPartialHomeomorph.symm_source, ← hqy]
    exact q.map_source hq0
  have hEy : E y = 0 := by
    funext i
    change q.symm y = 0
    rw [← hqy, q.left_inv hq0]
  have hF : Filter.EventuallyEq (𝓝 (0 : Fin 1 → ℂ))
      (fun z ↦ TopPair.Hom.fst F z) (fun z ↦ E.symm z) := by
    filter_upwards [((continuous_apply (0 : Fin 1)).tendsto (0 : Fin 1 → ℂ)).eventually hqe]
      with z hz
    rw [hFe]
    change e (z 0) = q (z 0)
    exact hz.symm
  have hi' : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω q.symm (q 0) := by
    simpa only [hqe0] using hi
  have hn := hga_biholomorphic_chart_localClass q hq0 hq hi'
  apply (hga_localClass_of_inverseChart_germ y E hy hEy F hF).trans
  cases hqy
  exact hn

#print axioms hga_planeLift_localClass

#print axioms hga_biholomorphic_chart_localClass

#print axioms hga_scalarChart_localClass_eq

#print axioms hga_localClass_of_inverseChart_germ
end HodgeLean.Foundations.Program
