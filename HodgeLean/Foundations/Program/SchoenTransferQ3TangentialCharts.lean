import HodgeLean.Foundations.Program.SchoenTransferQ3TangentialSections
import HodgeLean.Adapters.NormalConeB4aGysinBridge2DifferentialComparison
import HodgeLean.Adapters.CycleClassSmoothCharts

/-! Ambient affine sections which read as the actual support coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Topology Filter
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Coordinates on a smooth support lift to ambient affine sections whose
analytic readings agree with the coordinates on a neighbourhood. -/
theorem s4_q3_support_coordinates_ambient_sections
    {D W : Over (Spec ↧ℂ)} (r : ℕ) [SmoothOfRelativeDimension r D.hom]
    (j : D ⟶ W) [IsClosedImmersion j.left] (x : ComplexPoint D) :
    ∃ (U : W.left.Opens) (_ : IsAffineOpen U) (hxU : j.left x.underlying ∈ U)
      (g : Fin r → Γ(W.left, U)),
      (fun b i => Point.evaluate (j.left ⁻¹ᵁ U) (j.left.app U (g i))
        ((localChart D r x).symm b)) =ᶠ[𝓝 ((localChart D r x) x)]
        (fun b => b) := by
  let χ := localChart D r x
  let D₀ := ComplexPoint.localEtaleCoordinates D r x
  let V : D.left.Opens := D₀.ambientCoordinateOpen
  let s : Fin r → Γ(D.left, V) := fun i => D₀.ambientCoordinateSection i
  have hxχ : x ∈ χ.source := mem_localChart_source D r x
  have hV : ∀ p ∈ χ.source, p.underlying ∈ V := by
    intro p hp
    have h := ComplexPoint.mem_coordinateNeighborhood_of_mem_localChart_source D r x p hp
    have heq : V = D₀.neighborhood := Scheme.Opens.ι_image_top _
    rwa [heq]
  have hxV : x.underlying ∈ V := hV x hxχ
  obtain ⟨U, hU, hxU, g, hg⟩ :=
    a3b4g_closed_immersion_affine_germ_lifts_core j.left x.underlying r
      (fun i => D.left.presheaf.germ V x.underlying hxV (s i))
  have hev (i : Fin r) :
      (fun b => Point.evaluate (j.left ⁻¹ᵁ U) (j.left.app U (g i)) (χ.symm b))
        =ᶠ[𝓝 (χ x)] (fun b => b i) := by
    have hgerm := (Scheme.Hom.germ_stalkMap_apply j.left U x.underlying hxU (g i)).symm.trans (hg i)
    obtain ⟨V₀, hxV₀, iU, iV, heq⟩ := TopCat.Presheaf.germ_eq D.left.presheaf
      x.underlying hxU hxV (j.left.app U (g i)) (s i) hgerm
    have hcont : ContinuousAt χ.symm (χ x) := χ.continuousAt_symm (χ.map_source hxχ)
    have hxV₀' : χ.symm (χ x) ∈ Point.overOpen (X := D) V₀ := by
      rw [χ.left_inv hxχ]
      exact hxV₀
    have h : (fun b => Point.evaluate (j.left ⁻¹ᵁ U) (j.left.app U (g i)) (χ.symm b))
        =ᶠ[𝓝 (χ x)] (fun b => Point.evaluate V (s i) (χ.symm b)) := by
      filter_upwards [hcont.preimage_mem_nhds ((Point.isOpen_overOpen V₀).mem_nhds hxV₀')]
        with b hb
      rw [Point.evaluate_res (X := D) iU.le (j.left.app U (g i)) _ hb,
        Point.evaluate_res (X := D) iV.le (s i) _ hb]
      have h1 : homOfLE iU.le = iU := Subsingleton.elim _ _
      have h2 : homOfLE iV.le = iV := Subsingleton.elim _ _
      rw [h1, h2, heq]
    filter_upwards [h, χ.open_target.mem_nhds (χ.map_source hxχ)] with b hb hbt
    rw [hb, ← ComplexPoint.localChart_apply_component_eq_evaluate D r x
      (χ.symm b) (χ.map_target hbt) i]
    exact congrFun (χ.right_inv hbt) i
  refine ⟨U, hU, hxU, g, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hev] with b hb
  exact funext hb

/-- The same ambient sections give an invertible analytic tangential map on
an etale source support, through the actual composite section pullback. -/
theorem s4_q3_etale_support_coordinate_pullback
    {C D W : Over (Spec ↧ℂ)} (r : ℕ)
    [SmoothOfRelativeDimension r C.hom] [SmoothOfRelativeDimension r D.hom]
    (f : C ⟶ D) [Etale f.left] (j : D ⟶ W) [IsClosedImmersion j.left]
    (x : ComplexPoint C) :
    ∃ (U : W.left.Opens) (_ : IsAffineOpen U)
      (hxU : (f.left ≫ j.left) x.underlying ∈ U) (g : Fin r → Γ(W.left, U)),
      fderiv ℂ (fun b i => Point.evaluate (j.left ⁻¹ᵁ U) (j.left.app U (g i))
        ((localChart D r (Point.map f x)).symm b))
        ((localChart D r (Point.map f x)) (Point.map f x)) =
          ContinuousLinearMap.id ℂ (Fin r → ℂ) ∧
      Function.Bijective (fderiv ℂ
        (fun b i => Point.evaluate ((f.left ≫ j.left) ⁻¹ᵁ U)
          ((f.left ≫ j.left).app U (g i)) ((localChart C r x).symm b))
        ((localChart C r x) x)) := by
  obtain ⟨U, hU, hxU, g, hg⟩ := s4_q3_support_coordinates_ambient_sections r j (Point.map f x)
  let χC := localChart C r x
  let χD := localChart D r (Point.map f x)
  let F := inclusionInComplexCharts D C f r r x
  have hxC : x ∈ χC.source := mem_localChart_source C r x
  have hxD : Point.map f x ∈ χD.source := mem_localChart_source D r (Point.map f x)
  have hcont : ContinuousAt (fun b => Point.map f (χC.symm b)) (χC x) :=
    (Point.continuous_map f).continuousAt.comp (χC.continuousAt_symm (χC.map_source hxC))
  have hnear : ∀ᶠ b in 𝓝 (χC x), Point.map f (χC.symm b) ∈ χD.source := by
    apply hcont.preimage_mem_nhds
    rw [χC.left_inv hxC]
    exact χD.open_source.mem_nhds hxD
  have htend : Tendsto F (𝓝 (χC x)) (𝓝 (χD (Point.map f x))) := by
    have hh := (analyticAt_inclusionInComplexCharts D C f r r x).continuousAt.tendsto
    simpa only [F, χC, χD, inclusionInComplexCharts_at_center] using hh
  have hsource :
      (fun b i => Point.evaluate ((f.left ≫ j.left) ⁻¹ᵁ U)
        ((f.left ≫ j.left).app U (g i)) (χC.symm b)) =ᶠ[𝓝 (χC x)] F := by
    filter_upwards [hg.comp_tendsto htend, hnear] with b hb hbd
    funext i
    have hh := congrFun hb i
    change Point.evaluate (j.left ⁻¹ᵁ U) (j.left.app U (g i)) (χD.symm (F b)) = F b i at hh
    change Point.evaluate (j.left ⁻¹ᵁ U) (j.left.app U (g i))
      (χD.symm (χD (Point.map f (χC.symm b)))) = F b i at hh
    rw [χD.left_inv hbd] at hh
    rw [Point.evaluate_map f (j.left ⁻¹ᵁ U) (j.left.app U (g i))] at hh
    exact hh
  refine ⟨U, hU, hxU, g, ?_, ?_⟩
  · exact hg.fderiv_eq.trans fderiv_id
  · rw [hsource.fderiv_eq]
    exact ccm5_etale_chart_derivative_bijective C D f r r x


end HodgeLean.Foundations.Program
