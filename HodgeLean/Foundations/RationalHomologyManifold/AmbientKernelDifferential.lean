import HodgeLean.Foundations.RationalHomologyManifold.AmbientCochainKernel

/-! The actual ambient coboundary of a local-kernel section.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Inclusion of the actual presheaf kernel carries its differential to the literal singular coboundary.
Source: Bredon, Sheaf Theory, second edition, VI.12; the kernel subcomplex of ambient cochain restriction.
HC no distance; AV milestone no distance.
-/
theorem ambientLocalZeroPresheaf_coboundary (X : TopCat.{0}) (p : ℕ) (U : Opens X)
    (b : ((ambientLocalZeroPresheafComplex X).X p).obj (Opposite.op U)) :
    (((kernel.ι (ambientCochainPresheafComplexRestriction X)).f (p + 1)).app (Opposite.op U))
        (((ambientLocalZeroPresheafComplex X).d p (p + 1)).app (Opposite.op U) b) =
      coboundary ℚ p (((kernel.ι (ambientCochainPresheafComplexRestriction X)).f p).app (Opposite.op U) b) := by
  have h := congrArg (fun f => f.app (Opposite.op U))
    ((kernel.ι (ambientCochainPresheafComplexRestriction X)).comm p (p + 1))
  exact (ConcreteCategory.congr_hom h b).symm

#print axioms ambientLocalZeroPresheaf_coboundary
end HodgeLean.Foundations.RationalHomologyManifold
