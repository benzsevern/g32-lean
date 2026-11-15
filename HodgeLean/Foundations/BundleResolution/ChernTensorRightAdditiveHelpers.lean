import HodgeLean.Foundations.BundleResolution.ChernTensorChainDegreeHelpers

/-! # Additivity of tensoring actual rational chain complexes

The degreewise family calculation supplies additivity of the actual
right tensor functor on rational chain complexes.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory MonoidalCategory
namespace HodgeLean.Foundations.BundleResolution

theorem i1_tensorRight_additive (L : ChainComplex (ModuleCat ℚ) ℕ) :
    (tensorRight L).Additive where
  map_add := by
    intro K K' f g
    apply HomologicalComplex.hom_ext
    intro n
    change ((f + g) ▷ L).f n = (f ▷ L).f n + (g ▷ L).f n
    rw [i1_tensorRight_degree, i1_tensorRight_degree, i1_tensorRight_degree]
    exact i1_tensorDegreeMapLeft_add K K' L (fun p => (f.f p).hom)
      (fun p => (g.f p).hom) n

end HodgeLean.Foundations.BundleResolution
