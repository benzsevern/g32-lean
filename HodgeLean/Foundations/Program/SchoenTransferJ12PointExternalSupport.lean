import HodgeLean.Foundations.Program.SchoenTransferJ12GraphComponentSupport
import HodgeLean.Adapters.CycleClassFlatComparisonDefs
import HodgeLean.RealDefs.Port.AlgebraicGeometry.ComplexPoint.ClosedImmersion

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory TopologicalSpace
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- The external support of a complex point and a source component is its constant-graph support.
Source: Hartshorne, Algebraic Geometry, II.3, closed point fibres and closed immersions. -/
theorem s4_selected_point_external_support
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ A) (e : ComplexPoint A) (he : ∀ b : ComplexPoint Y, Point.map f b = e)
    (z : Y.left) :
    ccm4_inverseAnalyticSupport (fst A Y) (cycleComponentAnalyticClosedSupport A e.underlying) ⊓
      ccm4_inverseAnalyticSupport (snd A Y) (cycleComponentAnalyticClosedSupport Y z) =
      cycleComponentAnalyticClosedSupport (A ⊗ Y) ((lift f (𝟙 Y)).left z) := by
  have heclosed : IsClosed ({e.underlying} : Set A.left) :=
    ((pointEquivClosedPoint A.hom) ⟨e.left, by simp⟩).2
  have hepoint (a : ComplexPoint A) :
      a ∈ cycleComponentAnalyticClosedSupport A e.underlying ↔ a = e := by
    change a.underlying ∈ closure {e.underlying} ↔ a = e
    rw [heclosed.closure_eq, Set.mem_singleton_iff]
    exact ⟨fun h => underlying_injective_of_locallyOfFiniteType h,
      congrArg Point.underlying⟩
  let g : Y ⟶ A ⊗ Y := lift f (𝟙 Y)
  have hg1 (b : ComplexPoint Y) : Point.map (fst A Y) (Point.map g b) = Point.map f b := by
    change (b ≫ g) ≫ fst A Y = b ≫ f
    rw [Category.assoc, lift_fst]
  have hg2 (b : ComplexPoint Y) : Point.map (snd A Y) (Point.map g b) = b := by
    change (b ≫ g) ≫ snd A Y = b
    rw [Category.assoc, lift_snd, Category.comp_id]
  apply SetLike.coe_injective
  rw [s4_selected_graph_component_support A Y f z]
  ext a
  change (Point.map (fst A Y) a ∈ cycleComponentAnalyticClosedSupport A e.underlying ∧
    Point.map (snd A Y) a ∈ cycleComponentAnalyticClosedSupport Y z) ↔ _
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨Point.map (snd A Y) a, hb, ?_⟩
    apply (complexPointProdHomeomorph A Y).injective
    apply Prod.ext
    · change Point.map (fst A Y) (Point.map g (Point.map (snd A Y) a)) = Point.map (fst A Y) a
      rw [hg1, he, (hepoint _).mp ha]
    · change Point.map (snd A Y) (Point.map g (Point.map (snd A Y) a)) = Point.map (snd A Y) a
      exact hg2 _
  · rintro ⟨b, hb, rfl⟩
    refine ⟨(hepoint _).mpr ((hg1 b).trans (he b)), ?_⟩
    rw [hg2]
    exact hb

#print axioms s4_selected_point_external_support
end HodgeLean.Foundations.Program
