import HodgeLean.Foundations.Program.SchoenTransferJ12CupSubfamilyZero
import HodgeLean.RealDefs.TopDegreeRank

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- More than two factors from one actual curve coordinate annihilate an ordered degree-one cup.
Source: the curve top-degree bound and the embedded subfamily cup calculation. -/
theorem s4_selected_curve_subfamily_zero
    (Y T : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (hdim : TopologicalSpace.dim Y.left = 1)
    (m n : ℕ) (hm : 2 < m) (e : Fin m → Fin n) (he : Function.Injective e)
    (f : T ⟶ Y) (w : Fin m → HQ Y 1) (v : Fin n → HQ T 1)
    (hv : ∀ i, v (e i) = homPullback f 1 (w i)) :
    (cupProductOf T).cupMulti n v = 0 := by
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective e he
  letI : SmoothOfRelativeDimension 1 Y.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (f := Y.hom)
    rwa [hdim] at h
  letI := j5d_subsingleton_HQ_of_lt Y 1 (m := m) (by omega)
  exact s4_selected_cup_subfamily_zero Y T m n hmn e he f w v hv
    (Subsingleton.elim _ _)

#print axioms s4_selected_curve_subfamily_zero
end HodgeLean.Foundations.Program
