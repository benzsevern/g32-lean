import HodgeLean.Foundations.QuotientDuality.ProperCycleChainHomology
import Mathlib.Algebra.Homology.CochainComplexPlus

/-! # Actual bounded truncations of the original chain sheaf complex
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original rational chain sheaf cochain complex truncated at minus the specified ambient dimension, retained as an actual bounded-below complex for the original derived support functor.
Source: CochainComplex.truncGE; CochainComplex.Plus.
HC no distance; AV milestone no distance. -/
def properCycle_bounded_chain_sheaf (X : TopCat.{0}) (N : ℕ) :
    CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  ⟨(singularChainSheafCochainComplex ℚ X).truncGE (-(N : ℤ)),
    ⟨-(N : ℤ), inferInstance⟩⟩

example (X : TopCat.{0}) (N : ℕ) :
    (properCycle_bounded_chain_sheaf X N).obj =
      (singularChainSheafCochainComplex ℚ X).truncGE (-(N : ℤ)) := rfl

end HodgeLean.Foundations.QuotientDuality
