import HodgeLean.Foundations.Singular.ProductProjections
import HodgeLean.Foundations.Singular.ProductNaturality

/-! Naturality of the actual tensor bidegree projections. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace HodgeLean.Foundations.Singular

/-- Tensor bidegree projections intertwine the actual maps induced by maps on the factors.
Source: Hatcher, Algebraic Topology, §3.2, functoriality of the tensor complex. -/
theorem tensorChainProjection_naturality
    {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') (p q n : ℕ) :
    (rationalTensorChainMap f g).f n ≫ tensorChainProjection X' Y' p q n =
      tensorChainProjection X Y p q n ≫ ((rationalChainMap f).f p ⊗ₘ (rationalChainMap g).f q) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro r s hrs
  change r + s = n at hrs
  change tensorChainInclusion X Y r s n hrs ≫ _ = _
  rw [← Category.assoc, tensorChainInclusion_naturality, Category.assoc]
  by_cases h : r = p ∧ s = q
  · rcases h with ⟨rfl, rfl⟩
    rw [tensorChainInclusion_projection_self, Category.comp_id,
      ← Category.assoc, tensorChainInclusion_projection_self]
    erw [Category.id_comp]
  · rw [tensorChainInclusion_projection_other X' Y' p q r s n hrs h, comp_zero,
      ← Category.assoc, tensorChainInclusion_projection_other X Y p q r s n hrs h, zero_comp]

#print axioms tensorChainProjection_naturality
end HodgeLean.Foundations.Singular
