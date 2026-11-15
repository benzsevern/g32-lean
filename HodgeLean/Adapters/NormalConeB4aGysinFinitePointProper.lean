import HodgeLean.Adapters.NormalConeB4aGysinFinitePointCompact
import HodgeLean.Adapters.NormalConeB4aDefs
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Analytic

/-- A finite algebra over a finite type complex algebra induces a proper
map on complex evaluations in their analytic topologies. -/
theorem a3b4a_gysin_finite_evaluation_isProperMap
    {B T : Type} [CommRing B] [CommRing T] [Algebra ℂ B] [Algebra ℂ T]
    [Algebra B T] [IsScalarTower ℂ B T] [Algebra.FiniteType ℂ B] [Module.Finite B T] :
    IsProperMap (fun w : T →ₐ[ℂ] ℂ => w.comp (IsScalarTower.toAlgHom ℂ B T)) := by
  let q := ComplexPoint.affineSpecStructureMap B
  haveI : LocallyOfFiniteType q := by
    change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℂ B)))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  haveI : QuasiCompact q := inferInstance
  haveI : IsSeparated q := inferInstance
  letI : LocallyOfFiniteType (Over.mk q).hom := ‹LocallyOfFiniteType q›
  letI : QuasiCompact (Over.mk q).hom := ‹QuasiCompact q›
  letI : IsSeparated (Over.mk q).hom := ‹IsSeparated q›
  letI : LocallyCompactSpace (ComplexPoint (Over.mk q)) :=
    an_locallyCompactSpace (f4_analytification (Over.mk q))
  letI : LocallyCompactSpace (B →ₐ[ℂ] ℂ) :=
    (ComplexPoint.affineSpecHomeomorph B).symm.isOpenEmbedding.locallyCompactSpace
  letI : T2Space (B →ₐ[ℂ] ℂ) :=
    (a3b4a_gysin_algHom_isClosedEmbedding B).isEmbedding.t2Space
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨?_, fun K hK => a3b4a_gysin_finite_evaluation_compact_preimage K hK⟩
  apply continuous_induced_rng.mpr
  exact continuous_pi fun b => ComplexPoint.continuous_affineAlgebraHom_apply T (algebraMap B T b)

end HodgeLean.Adapters
