import HodgeLean.Foundations.BundleResolution.ChernTensorDegreeSplittingHelpers
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Exactness of actual rational chain tensor products

Every rational vector-space short exact sequence splits. Applying those
splittings degreewise gives short exactness of the actual total tensor sequence.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory MonoidalCategory HomologicalComplex
namespace HodgeLean.Foundations.BundleResolution

theorem i1_tensorRightShortComplex_shortExact
    (S : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ)) (hS : S.ShortExact)
    (L : ChainComplex (ModuleCat ℚ) ℕ) : (i1_tensorRightShortComplex S L).ShortExact := by
  let d (p : ℕ) : (S.map (eval (ModuleCat ℚ) (ComplexShape.down ℕ) p)).Splitting :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS p).splittingOfProjective
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact (i1_tensorRightDegreeSplitting S L d n).shortExact

end HodgeLean.Foundations.BundleResolution
