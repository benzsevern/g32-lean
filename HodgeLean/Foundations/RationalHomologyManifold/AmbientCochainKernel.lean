import HodgeLean.Foundations.RationalHomologyManifold.AmbientCochainComplex

/-! The actual kernel of ambient-to-local singular cochain restriction.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Take the actual kernel of the restriction map of singular cochain presheaf complexes.
Source: Bredon, Sheaf Theory, second edition, VI.12; the local zero-cochain kernel complex.
HC no distance; AV milestone no distance.
-/
def ambientLocalZeroPresheafComplex (X : TopCat.{0}) :
    CochainComplex (TopCat.Presheaf AddCommGrpCat.{0} X) ℕ :=
  kernel (ambientCochainPresheafComplexRestriction X)

#print axioms ambientLocalZeroPresheafComplex
/-- Every actual kernel section restricts to zero in the existing local singular cochain presheaf.
Source: Bredon, Sheaf Theory, second edition, VI.12; the kernel condition for ambient restriction.
HC no distance; AV milestone no distance.
-/
theorem ambientLocalZeroPresheaf_restriction_zero (X : TopCat.{0}) (p : ℕ) (U : Opens X)
    (b : ((ambientLocalZeroPresheafComplex X).X p).obj (Opposite.op U)) :
    (ambientCochainPresheafRestriction X p).app (Opposite.op U)
      (((kernel.ι (ambientCochainPresheafComplexRestriction X)).f p).app (Opposite.op U) b) = 0 := by
  have h := congrArg (fun f => (f.f p).app (Opposite.op U))
    (kernel.condition (ambientCochainPresheafComplexRestriction X))
  exact ConcreteCategory.congr_hom h b

#print axioms ambientLocalZeroPresheaf_restriction_zero
end HodgeLean.Foundations.RationalHomologyManifold
