import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionPresheaf

/-! Subdivision on the actual relative-chain sheaf complex.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Exact sheafification carries the supported subdivision operator to the actual chain sheaf.
Source: Bredon, Sheaf Theory, second edition, V.9 and VI.12; subdivision of supported chains.
HC no distance; AV milestone no distance.
-/
def sheafSubdivision (X : TopCat.{0}) :
    singularChainSheafComplex ℚ X ⟶ singularChainSheafComplex ℚ X :=
  ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.down ℕ)).map (presheafSubdivision X)

#print axioms sheafSubdivision
/-- The actual chain-sheaf subdivision is homotopic to the identity.
Source: Bredon, Sheaf Theory, second edition, V.9 and VI.12; subdivision invariance of the chain sheaf.
HC no distance; AV milestone no distance.
-/
def sheafSubdivisionHomotopy (X : TopCat.{0}) :
    Homotopy (sheafSubdivision X) (𝟙 (singularChainSheafComplex ℚ X)) :=
  ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapHomotopy
    (presheafSubdivisionHomotopy X)).trans
      (Homotopy.ofEq
        (((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.down ℕ)).map_id (singularChainPresheafComplex ℚ X)))

#print axioms sheafSubdivisionHomotopy
/-- Sheaf subdivision acts identically on every actual chain-homology sheaf.
Source: Bredon, Sheaf Theory, second edition, V.9 and VI.12; subdivision invariance.
HC no distance; AV milestone no distance.
-/
theorem sheafSubdivision_homology (X : TopCat.{0}) (n : ℕ) :
    HomologicalComplex.homologyMap (sheafSubdivision X) n = 𝟙 _ := by
  simpa only [HomologicalComplex.homologyMap_id] using
    (sheafSubdivisionHomotopy X).homologyMap_eq n

#print axioms sheafSubdivision_homology
/-- Subdivision of the actual chain sheaf is a quasi-isomorphism.
Source: Bredon, Sheaf Theory, second edition, V.9 and VI.12; subdivision invariance.
HC no distance; AV milestone no distance.
-/
theorem sheafSubdivision_quasiIso (X : TopCat.{0}) : QuasiIso (sheafSubdivision X) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, sheafSubdivision_homology]
  infer_instance

#print axioms sheafSubdivision_quasiIso
end HodgeLean.Foundations.RationalHomologyManifold
