import HodgeLean.Foundations.Program.SchoenTransferQ3SupportOpenDiagram

/-! Finite-type instances on the actual composed ambient and support opens. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The actual open immersion into a finite-type separated complex scheme
supplies the finite-type, compactness and separation instances used by the
local normal comparison. -/
theorem s4_q3_finite_type_instances_of_open_immersion
    {Y X : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (a : Y ⟶ X) [IsOpenImmersion a.left] :
    LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom ∧ IsSeparated Y.hom ∧ IsNoetherian Y.left := by
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : IsNoetherian X.left := {}
  letI : NoetherianSpace Y.left := a.left.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  letI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian a.left
  letI : IsNoetherian Y.left := {}
  have hft : LocallyOfFiniteType Y.hom := by rw [← Over.w a]; infer_instance
  have hsep : IsSeparated Y.hom := by rw [← Over.w a]; infer_instance
  exact ⟨hft, inferInstance, hsep, inferInstance⟩

end HodgeLean.Foundations.Program
