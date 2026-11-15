import HodgeLean.Foundations.Program.SchoenTransferJ12CurveSumSmooth
import HodgeLean.Foundations.Program.CompensationAssemblyPullback
import HodgeLean.RealDefs.TopDegreeRank

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] homPullback algebraicCycleClassSpan

/-- The mixed divisor class obtained from addition with an arbitrary curve map.
Source: Birkenhake–Lange, Complex Abelian Varieties, §2.5, the theorem of the square. -/
def s4_selected_curve_mixed_divisor
    (A Y : Over (Spec ↧ℂ)) [GrpObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ A) (pol : HQ A 2) : HQ (A ⊗ Y) 2 :=
  homPullback (s4_selected_curve_add_map A Y f) 2 pol -
    homPullback (fst A Y) 2 pol -
      homPullback (snd A Y) 2 (homPullback f 2 pol)

/-- The mixed class is algebraic using smooth pullback and the top degree of the actual curve.
Source: Fulton, Intersection Theory, §§1.7 and 19.1;
Griffiths–Harris, Principles of Algebraic Geometry, Ch. 0 §4. -/
theorem s4_selected_curve_mixed_divisor_mem
    (A Y : Over (Spec ↧ℂ)) [GrpObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1)
    (f : Y ⟶ A) (pol : HQ A 2) (hpol : pol ∈ cfd_cycleSpan A 1) :
    s4_selected_curve_mixed_divisor A Y f pol ∈ cfd_cycleSpan (A ⊗ Y) 1 := by
  letI : SmoothOfRelativeDimension 1 Y.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (f := Y.hom)
    rwa [hdim] at h
  letI : Smooth (s4_selected_curve_add_map A Y f).left :=
    s4_selected_curve_add_smooth A Y f
  letI : Smooth (fst A Y).left := by
    change Smooth (Limits.pullback.fst A.hom Y.hom)
    infer_instance
  letI : Smooth (snd A Y).left := by
    change Smooth (Limits.pullback.snd A.hom Y.hom)
    infer_instance
  have hY : homPullback f 2 pol ∈ algebraicCycleClassSpan Y 1 := by
    rw [j5d_algebraicCycleClassSpan_one_eq_top complexPointsPreconnected Y]
    trivial
  have hsum := cq_smooth_pullback_span_core (s4_selected_curve_add_map A Y f) 1
    (Submodule.mem_map_of_mem hpol)
  have hfst := cq_smooth_pullback_span_core (fst A Y) 1
    (Submodule.mem_map_of_mem hpol)
  have hsnd := cq_smooth_pullback_span_core (snd A Y) 1
    (Submodule.mem_map_of_mem hY)
  exact Submodule.sub_mem _ (Submodule.sub_mem _ hsum hfst) hsnd

#print axioms s4_selected_curve_mixed_divisor_mem
end HodgeLean.Foundations.Program
