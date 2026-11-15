import HodgeLean.Foundations.QuotientDuality.LocalOrbitCoherentOrientation
import HodgeLean.Foundations.QuotientDuality.LocalSmoothOrientation
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Basis
import HodgeLean.Foundations.Analytic.Analytification
import HodgeLean.RealDefs.Port.AlgebraicGeometry.ComplexPoint.CoclassSchemeIso

/-! Coherent orientations of finite algebraic quotients of smooth noncompact charts. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

theorem smooth_finite_orbit_coherent_orientation
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (G : Type) [Group G] [Fintype G] [MulAction G (ComplexPoint X)]
    [ContinuousConstSMul G (ComplexPoint X)] [PseudoMetrizableSpace (ComplexPoint X)]
    [T2Space (orbitSpace G (TopCat.of (ComplexPoint X)))]
    [PseudoMetrizableSpace (orbitSpace G (TopCat.of (ComplexPoint X)))]
    (σ : G → (X ≅ X))
    (ha : ∀ (g : G) (x : ComplexPoint X), g • x = Point.map (σ g).hom x)
    (hQ : ∀ (x : orbitSpace G (TopCat.of (ComplexPoint X)))
      (U : Opens (orbitSpace G (TopCat.of (ComplexPoint X)))), x ∈ U →
      ∃ V : Opens (orbitSpace G (TopCat.of (ComplexPoint X))), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U) :
    Nonempty (LocalRationalOrientation (orbitSpace G (TopCat.of (ComplexPoint X))) (2 * d)) := by
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  apply finite_orbit_coherent_orientation G (TopCat.of (ComplexPoint X))
    (HodgeLean.Foundations.ComplexTopology.finiteType_basis X) hQ
    (2 * d) (smoothLocalRationalOrientation X d)
  intro g x
  have hH : (Homeomorph.smul (g⁻¹) : ComplexPoint X ≃ₜ ComplexPoint X) =
      Point.isoMapHomeomorph (σ g⁻¹) := Homeomorph.ext (ha g⁻¹)
  change relativeHomologyMap ℚ (2 * d)
    (pointComplementHomeomorphPairMap (Homeomorph.smul (g⁻¹)) x)
    (complexLocalOrientation X d x) = complexLocalOrientation X d ((Homeomorph.smul (g⁻¹)) x)
  rw [hH]
  exact complexSchemeIsoPointPairMap_localClass X X (σ g⁻¹) d x

#print axioms smooth_finite_orbit_coherent_orientation
end HodgeLean.Foundations.QuotientDuality
