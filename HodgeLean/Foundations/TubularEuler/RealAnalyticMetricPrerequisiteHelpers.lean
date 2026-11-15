import HodgeLean.Foundations.TubularEuler.NormalGeometryInputs
import HodgeLean.Foundations.Analytic.Analytification

/-! # Analytic manifold prerequisites for ambient metric existence

The original complex charts give a real analytic atlas. Finite type and
separation supply the countability and separation properties of its topology.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler

theorem complexPoint_isRealAnalyticManifold
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    IsManifold 𝓘(ℝ, Fin d → ℂ) ω (ComplexPoint X) := by
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨z, rfl⟩ ⟨z', rfl⟩
  have h := (ComplexPoint.contDiffOn_localChart_transition X d z z').restrict_scalars ℝ
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    CompTriple.comp_eq, Function.id_comp, Function.comp_id, Set.preimage_id,
    Set.range_id, Set.inter_univ] using h

theorem ambientMetric_secondCountable
    (W : Over (Spec (CommRingCat.of ℂ))) [LocallyOfFiniteType W.hom]
    [QuasiCompact W.hom] {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v] :
    SecondCountableTopology (ComplexPoint (Over.mk (v ≫ W.hom))) := by
  letI : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian W.hom
  letI : QuasiCompact v := inferInstance
  letI : LocallyOfFiniteType (Over.mk (v ≫ W.hom)).hom := by
    change LocallyOfFiniteType (v ≫ W.hom)
    infer_instance
  letI : QuasiCompact (Over.mk (v ≫ W.hom)).hom := by
    change QuasiCompact (v ≫ W.hom)
    infer_instance
  exact HodgeLean.Foundations.Analytic.f4_secondCountable (Over.mk (v ≫ W.hom))

theorem ambientMetric_t2Space
    (W : Over (Spec (CommRingCat.of ℂ))) [LocallyOfFiniteType W.hom]
    [IsSeparated W.hom] {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v] :
    T2Space (ComplexPoint (Over.mk (v ≫ W.hom))) := by
  letI : LocallyOfFiniteType (Over.mk (v ≫ W.hom)).hom := by
    change LocallyOfFiniteType (v ≫ W.hom)
    infer_instance
  letI : IsSeparated (Over.mk (v ≫ W.hom)).hom := by
    change IsSeparated (v ≫ W.hom)
    infer_instance
  exact HodgeLean.Foundations.Analytic.f4_t2Space (Over.mk (v ≫ W.hom))

#print axioms ambientMetric_t2Space

#print axioms ambientMetric_secondCountable

#print axioms complexPoint_isRealAnalyticManifold

end HodgeLean.Foundations.TubularEuler
