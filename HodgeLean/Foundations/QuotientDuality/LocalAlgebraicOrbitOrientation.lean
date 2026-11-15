import HodgeLean.Foundations.QuotientDuality.LocalQuotientOrientation
import HodgeLean.Foundations.QuotientDuality.LocalSmoothOrientation
import HodgeLean.Foundations.QuotientDuality.LocalSmoothAutomorphism
import HodgeLean.Foundations.Analytic.Analytification
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Basis

/-! Coherent orientations of actual finite algebraic orbit spaces of smooth projective schemes. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

theorem smooth_algebraic_orbit_orientation
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (G : Type) [Group G] [Fintype G] [MulAction G (ComplexPoint X)]
    [ContinuousConstSMul G (ComplexPoint X)]
    [T2Space (orbitSpace G (TopCat.of (ComplexPoint X)))]
    [PseudoMetrizableSpace (orbitSpace G (TopCat.of (ComplexPoint X)))]
    (σ : G → (X ≅ X))
    (ha : ∀ (g : G) (x : ComplexPoint X), g • x = Point.map (σ g).hom x)
    (hQ : ∀ (x : orbitSpace G (TopCat.of (ComplexPoint X)))
      (U : Opens (orbitSpace G (TopCat.of (ComplexPoint X)))), x ∈ U →
      ∃ V : Opens (orbitSpace G (TopCat.of (ComplexPoint X))), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (k : ℕ) (hk : 0 < k) :
    ∃ (cX : Homology ℚ (TopCat.of (ComplexPoint X)) (2 * d))
      (oQ : LocalRationalOrientation (orbitSpace G (TopCat.of (ComplexPoint X))) (2 * d))
      (cQ : Homology ℚ (orbitSpace G (TopCat.of (ComplexPoint X))) (2 * d)),
      (∀ x, localOrientation (TopCat.of (ComplexPoint X)) (2 * d) cX x =
        complexLocalOrientation X d x) ∧
      homologyMap ℚ (2 * d) (orbitMap G (TopCat.of (ComplexPoint X))) cX = (k : ℚ) • cQ ∧
      ∀ x, localOrientation (orbitSpace G (TopCat.of (ComplexPoint X))) (2 * d) cQ x = oQ.generator x := by
  letI : SecondCountableTopology (ComplexPoint X) := f4_secondCountable X
  letI : PseudoMetrizableSpace (ComplexPoint X) := inferInstance
  obtain ⟨c, hc⟩ := smooth_projective_absolute_fundamental X d
  have hgen : ∀ x, Function.Bijective (orientationLine (TopCat.of (ComplexPoint X)) (2 * d) c x) := by
    intro x
    change Function.Bijective (LinearMap.toSpanSingleton ℚ _
      (localOrientation (TopCat.of (ComplexPoint X)) (2 * d) c x))
    rw [hc x]
    exact (smoothLocalRationalOrientation X d).generates x
  have hp : ∀ g, homologyMap ℚ (2 * d) (deckMap G (TopCat.of (ComplexPoint X)) g) c = c := by
    intro g
    have hf : deckMap G (TopCat.of (ComplexPoint X)) g =
        TopCat.ofHom (Point.continuousMap (σ g⁻¹).hom) := by
      ext x
      exact congrArg Over.Hom.left (ha g⁻¹ x)
    rw [hf]
    exact smooth_projective_fundamental_iso_invariant X d c hc (σ g⁻¹)
  obtain ⟨oQ, cQ, hdegree, hcQ⟩ := quotient_coherent_orientation G
    (TopCat.of (ComplexPoint X)) (HodgeLean.Foundations.ComplexTopology.finiteType_basis X)
    hQ (2 * d) c hgen (smoothLocalRationalOrientation X d).vanishes hp k hk
  exact ⟨c, oQ, cQ, hc, hdegree, hcQ⟩

#print axioms smooth_algebraic_orbit_orientation
end HodgeLean.Foundations.QuotientDuality
