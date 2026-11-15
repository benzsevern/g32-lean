import HodgeLean.Foundations.QuotientDuality.LocalOrientationSheaf
import HodgeLean.RealDefs.Port.AlgebraicTopology.Singular.Sheaf.ChainOrientation

/-! The actual local orientation identifies the surviving homology of the chain sheaf. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

variable (X : TopCat.{0}) [T2Space X] (n : ℕ) (o : LocalRationalOrientation X n)

include o in
theorem localOrientationHomologySheaf_concentrated (i : ℕ) (hi : i ≠ n) :
    IsZero (singularChainHomologySheaf ℚ X i) := by
  apply singularChainHomologySheaf_isZero_of_localHomology_isZero
  intro x
  letI := o.vanishes x i hi
  exact ModuleCat.isZero_of_subsingleton _

local instance localOrientationDerivedCategory :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  HasDerivedCategory.standard _

def localOrientationDerivedSingleIso :
    DerivedCategory.Q.obj (singularChainSheafCochainComplex ℚ X) ≅
      (DerivedCategory.singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} X) (-(n : ℤ))).obj
        𝓒(X; ℚ) :=
  singularChainSheafDerivedSingleOrientationIso ℚ X n
    (fun i hi x => by
      letI := o.vanishes x i hi
      exact ModuleCat.isZero_of_subsingleton _)
    (localOrientationHomologySheafIso X n o).symm

#print axioms localOrientationHomologySheaf_concentrated
#print axioms localOrientationDerivedSingleIso
end HodgeLean.Foundations.QuotientDuality
