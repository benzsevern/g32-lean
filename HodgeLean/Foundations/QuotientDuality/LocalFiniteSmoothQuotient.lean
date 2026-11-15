import HodgeLean.Foundations.QuotientDuality.LocalSmoothOrbitOrientation
import HodgeLean.Foundations.QuotientDuality.LocalClosedOrbitHomeomorph
import HodgeLean.Foundations.QuotientDuality.LocalHomeomorphOrientation
import HodgeLean.Foundations.QuotientDuality.LocalBasisTransport

/-! Actual finite algebraic quotient maps carry coherent complex local orientations. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

theorem finite_smooth_quotient_coherent_orientation
    (X Y : Over (Spec ↧ℂ))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (G : Type) [Group G] [Fintype G] [MulAction G (ComplexPoint X)]
    [ContinuousConstSMul G (ComplexPoint X)]
    (σ : G → (X ≅ X))
    (ha : ∀ (g : G) (x : ComplexPoint X), g • x = Point.map (σ g).hom x)
    (q : X ⟶ Y) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ (g : G) (x : ComplexPoint X), Point.map q (g • x) = Point.map q x)
    (horbit : ∀ x y, Point.map q x = Point.map q y → ∃ g : G, g • x = y) :
    Nonempty (LocalRationalOrientation (TopCat.of (ComplexPoint Y)) (2 * d)) := by
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  letI : T2Space (ComplexPoint Y) := f4_t2Space Y
  letI : SecondCountableTopology (ComplexPoint X) := f4_secondCountable X
  letI : SecondCountableTopology (ComplexPoint Y) := f4_secondCountable Y
  letI : LocallyCompactSpace (ComplexPoint X) := an_locallyCompactSpace (f4_analytification X)
  letI : LocallyCompactSpace (ComplexPoint Y) := an_locallyCompactSpace (f4_analytification Y)
  letI : PseudoMetrizableSpace (ComplexPoint X) := inferInstance
  letI : PseudoMetrizableSpace (ComplexPoint Y) := inferInstance
  obtain ⟨H, hH⟩ := closed_orbit_quotient_homeomorph G (ComplexPoint X) (ComplexPoint Y)
    (Point.map q) (Point.continuous_map q) (f4_isProperMap_of_isProper q).isClosedMap
    hsurj hinv horbit
  let Q := orbitSpace G (TopCat.of (ComplexPoint X))
  letI : T2Space Q := H.isEmbedding.t2Space
  letI : PseudoMetrizableSpace Q := H.isInducing.pseudoMetrizableSpace
  obtain ⟨oQ⟩ := smooth_finite_orbit_coherent_orientation X d G σ ha
    (homeomorph_contractible_basis H (HodgeLean.Foundations.ComplexTopology.finiteType_basis Y))
  exact homeomorph_transport_coherent_orientation Q (TopCat.of (ComplexPoint Y)) H (2 * d) oQ

#print axioms finite_smooth_quotient_coherent_orientation
end HodgeLean.Foundations.QuotientDuality
