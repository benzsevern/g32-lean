import HodgeLean.Foundations.Singular.ProductUniversalGenerators

/-! Differential compatibility for extension from actual product models. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- Actual rational singular chain maps commute with the boundary on each chain.
Source: Hatcher, Algebraic Topology, §2.1, functoriality of singular chains. -/
theorem rationalChainMap_boundary
    {X Y : TopCat.{0}} (f : X ⟶ Y) (i j : ℕ) (z : (rationalChains X).X i) :
    ((rationalChains Y).d i j).hom (((rationalChainMap f).f i).hom z) =
      ((rationalChainMap f).f j).hom (((rationalChains X).d i j).hom z) :=
  congrArg (fun k => ModuleCat.Hom.hom k z) ((rationalChainMap f).comm i j)

/-- Actual tensor chain maps commute with the boundary on each total chain.
Source: Hatcher, Algebraic Topology, §3.2, functoriality of tensor chain complexes. -/
theorem rationalTensorChainMap_boundary
    {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') (i j : ℕ)
    (z : (rationalTensorChains X Y).X i) :
    ((rationalTensorChains X' Y').d i j).hom (((rationalTensorChainMap f g).f i).hom z) =
      ((rationalTensorChainMap f g).f j).hom (((rationalTensorChains X Y).d i j).hom z) :=
  congrArg (fun k => ModuleCat.Hom.hom k z) ((rationalTensorChainMap f g).comm i j)

#print axioms rationalTensorChainMap_boundary
#print axioms rationalChainMap_boundary
end HodgeLean.Foundations.Singular
