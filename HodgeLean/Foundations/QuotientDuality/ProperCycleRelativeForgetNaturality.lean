import HodgeLean.Foundations.QuotientDuality.ProperCycleDefs

/-! # Forgetting relative support along the original pair maps -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal map forgetting relative support commutes with pullback by every actual pair map.
Source: Hatcher, Algebraic Topology, section 3.1, naturality of the relative chain projection.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_forget_naturality {P Q : TopPair.{0}}
    (f : P ⟶ Q) (n : ℕ) (a : RelativeCohomology ℚ Q n) :
    relativeCohomologyToAbsolute ℚ P n (relativeCohomologyMap ℚ n f a) =
      cohomologyMap ℚ n (TopPair.Hom.fst f) (relativeCohomologyToAbsolute ℚ Q n a) := by
  have hd := congrArg HomologicalComplex.linearDualMap
    (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) f)
  rw [HomologicalComplex.linearDualMap_comp, HomologicalComplex.linearDualMap_comp] at hd
  have hh := congrArg (fun u => HomologicalComplex.homologyMap u n) hd
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hh
  exact ConcreteCategory.congr_hom hh a

end HodgeLean.Foundations.QuotientDuality
