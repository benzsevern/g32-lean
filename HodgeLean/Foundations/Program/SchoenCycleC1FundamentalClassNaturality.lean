import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSupportNeighborhood

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- Restriction of an absolute fundamental class to a point-complement pair
commutes with the actual map of pairs and its underlying continuous map. -/
theorem s2e_c1_relative_homology_projection_naturality
    (R : Type) [CommRing R] {X Y : TopPair} (f : X ⟶ Y) (n : ℕ)
    (α : Homology R X.fst n) :
    relativeHomologyMap R n f ((relativeHomologyProjection R X n).hom α) =
      (relativeHomologyProjection R Y n).hom (homologyMap R n (TopPair.Hom.fst f) α) := by
  let φ := (relativeChainFunctor R).map f
  have hnat := TopPair.Homotopy.relativeChainProjection_naturality (R := R) f
  change (HomologicalComplex.homologyMap φ n).hom
    ((HomologicalComplex.homologyMap (relativeChainProjection R X) n).hom α) = _
  rw [b6m_homologyMap_hom_comp_apply, hnat]
  rw [← b6m_homologyMap_hom_comp_apply]
  rfl

end HodgeLean.Foundations.Program
