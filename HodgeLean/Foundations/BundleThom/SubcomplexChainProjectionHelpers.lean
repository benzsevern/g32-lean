import HodgeLean.Foundations.BundleThom.ChainSquareHomologyComparisonHelpers

/-! # Projecting actual subcomplex chains to a fixed target

HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- A supplied simplicial projection restricts to chains of each actual subcomplex.
Source: Hatcher, Algebraic Topology, §2.1, chain functoriality. -/
def i1_subcomplexChainProjection {X Y : SSet} (p : X ⟶ Y) (U : X.Subcomplex) :
    SSet.chainComplex U (ModuleCat.of ℚ ℚ) ⟶ SSet.chainComplex Y (ModuleCat.of ℚ ℚ) :=
  SSet.chainComplexMap (U.ι ≫ p) (ModuleCat.of ℚ ℚ)

/-- Subcomplex chain projections commute with actual subcomplex inclusions.
Source: Hatcher, Algebraic Topology, §2.1, naturality of chain restrictions. -/
theorem i1_subcomplexChainProjection_naturality {X Y : SSet} (p : X ⟶ Y)
    (U V : X.Subcomplex) (h : U ≤ V) :
    SSet.chainComplexMap (SSet.Subcomplex.homOfLE h) (ModuleCat.of ℚ ℚ) ≫
        i1_subcomplexChainProjection p V = i1_subcomplexChainProjection p U := by
  let F : SSet ⥤ ChainComplex (ModuleCat ℚ) ℕ :=
    (SSet.chainComplexFunctor.{0,0,1} (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  change F.map (SSet.Subcomplex.homOfLE h) ≫ F.map (V.ι ≫ p) = F.map (U.ι ≫ p)
  rw [← Functor.map_comp]
  rfl

end HodgeLean.Foundations.BundleThom
