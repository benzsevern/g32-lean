import HodgeLean.Foundations.QuotientDuality.LocalCapDuality

/-! # Finite triangulated spaces and singular localization

The triangulation is geometric data. Local homology and the cap map retain
the existing singular-chain definitions.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- An actual finite Euclidean simplicial realization of the specified space.
Source: Hatcher, Algebraic Topology, Appendix A, polyhedra.
HC no distance; AV milestone no distance.
-/
structure FiniteTriangulation (X : TopCat.{0}) where
  ambient : ℕ
  complex : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin ambient))
  finite_faces : complex.faces.Finite
  realization : complex.space ≃ₜ X

example (X : TopCat.{0}) (t : FiniteTriangulation X) :
    Function.Bijective t.realization := t.realization.bijective

/-- The actual global-to-local singular homology map, without a gluing premise.
Source: Hatcher, Algebraic Topology, section 3.3, local orientations.
HC no distance; AV milestone no distance.
-/
def localization (X : TopCat.{0}) (n : ℕ) :
    Homology ℚ X n →ₗ[ℚ] (∀ x : X,
      HodgeLean.Foundations.QuotientDuality.orientationGroup X n x) where
  toFun c x := HodgeLean.Foundations.QuotientDuality.localOrientation X n c x
  map_add' c d := by
    funext x
    exact map_add (relativeHomologyProjection ℚ (pointComplementPair x) n).hom c d
  map_smul' r c := by
    funext x
    exact map_smul (relativeHomologyProjection ℚ (pointComplementPair x) n).hom r c

example (X : TopCat.{0}) (n : ℕ) (c : Homology ℚ X n) (r : ℚ) (x : X) :
    localization X n (r • c) x = r • localization X n c x :=
  congrFun (map_smul (localization X n) r c) x

end HodgeLean.Foundations.RationalHomologyManifold
