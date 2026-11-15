import HodgeLean.Foundations.Program.SchoenTransferDefs
import HodgeLean.Adapters.CycleClassFlatPullback

/-! A nonzero inverse-image cycle detects an altered multiplicity.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open scoped Classical
namespace HodgeLean.Foundations.Program

/-- Changing the coefficient of the actual identity inverse image changes the cycle.
Source: Fulton, Intersection Theory, second edition, §1.7. -/
theorem s4_q3a_local_multiplicities_falsification :
    let P := Over.mk (𝟙 (Spec (CommRingCat.of ℂ)))
    let x := Point.underlying (𝟙 P : ComplexPoint P)
    ccm3_flatPullback (𝟙 P.left)
      (Function.locallyFinsuppWithin.single x (2 : ℚ)) ≠
      Function.locallyFinsuppWithin.single x (3 : ℚ) := by
  dsimp only
  rw [ccm3_flatPullback_id]
  intro h
  have he := congrArg (fun z => z (Point.underlying
    (𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of ℂ)))) :
      ComplexPoint (Over.mk (𝟙 (Spec (CommRingCat.of ℂ))))))) h
  norm_num at he

example := s4_q3a_local_multiplicities_falsification
#print axioms s4_q3a_local_multiplicities_falsification
end HodgeLean.Foundations.Program
