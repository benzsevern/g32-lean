import HodgeLean.Foundations.Program.CompensationAssemblyProjectionSupport
import HodgeLean.Adapters.CycleClassDivisorProduct4

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

theorem cq_component_class_supported
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) {p : ℕ} (hx : Order.coheight x = p) :
    ∃ c : RelativeCohomology ℚ
        (TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
          ((cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X))ᶜ)) (2 * p),
      relativeCohomologyToAbsolute ℚ _ (2 * p) c =
        cupComparison X (2 * p) (cycleComponentSheafClass X x hx) := by
  refine ⟨ccm16_supportedComparison X (cycleComponentAnalyticClosedSupport X x) (2 * p)
    (cycleComponentSupportedInjectiveClass X x hx), ?_⟩
  exact (ccm16_supportedComparison_forget X (cycleComponentAnalyticClosedSupport X x)
    (2 * p) (cycleComponentSupportedInjectiveClass X x hx)).trans
      (bh11_cupComparison_eq_raw X (2 * p)
        (cycleComponentSheafClass X x hx)).symm

theorem cq_component_class_pullback_zero
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) {p : ℕ} (hx : Order.coheight x = p)
    (T : TopCat.{0}) (f : T ⟶ TopCat.of (ComplexPoint X))
    (hf : ∀ t, f t ∉ cycleComponentAnalyticClosedSupport X x) :
    cohomologyMap ℚ (2 * p) f
      (cupComparison X (2 * p) (cycleComponentSheafClass X x hx)) = 0 := by
  let P := TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
    ((cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X))ᶜ)
  let g : T ⟶ P.snd := TopCat.ofHom
    ⟨fun t => ⟨f t, hf t⟩, f.hom.continuous.subtype_mk _⟩
  obtain ⟨c, hc⟩ := cq_component_class_supported X x hx
  have hfactor : g ≫ P.map = f := rfl
  rw [← hc, ← hfactor]
  change (cohomologyMap ℚ (2 * p) (g ≫ P.map))
    (relativeCohomologyToAbsolute ℚ P (2 * p) c) = 0
  rw [cohomologyMap_comp, LinearMap.comp_apply,
    cq_relative_absolute_restriction_zero, map_zero]

theorem cq_component_support_map
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (x : X.left) (z : ComplexPoint X)
    (hz : z ∈ cycleComponentAnalyticClosedSupport X x) :
    Point.map f z ∈ cycleComponentAnalyticClosedSupport Z (f.left x) := by
  change z.underlying ∈ closure {x} at hz
  change f.left z.underlying ∈ closure {f.left x}
  exact specializes_iff_mem_closure.mp
    ((specializes_iff_mem_closure.mpr hz).map f.left.continuous)

end HodgeLean.Foundations.Program
