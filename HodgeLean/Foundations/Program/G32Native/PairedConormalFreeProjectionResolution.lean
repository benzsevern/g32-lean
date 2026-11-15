import HodgeLean.Foundations.BundleThom.FreeSheafProjectionHelpers
/-! # Exact coordinate resolution of finite free module sheaves -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.Program.G32Native

/-- The supplied coordinate projections and summand injections resolve the actual free identity. -/
theorem conormal_free_projection_resolution (T : Scheme.{0}) (k : ℕ) :
    ∑ i : Fin k, i1_freeSheafProjection T k i ≫
      SheafOfModules.ιFree (R := T.ringCatSheaf) i =
        𝟙 (SheafOfModules.free (R := T.ringCatSheaf) (Fin k)) := by
  apply (SheafOfModules.isColimitFreeCofan (R := T.ringCatSheaf) (Fin k)).hom_ext
  intro j
  change SheafOfModules.ιFree (R := T.ringCatSheaf) j.as ≫ _ =
    SheafOfModules.ιFree (R := T.ringCatSheaf) j.as ≫ 𝟙 _
  rw [Category.comp_id, Preadditive.comp_sum]
  simp only [← Category.assoc, i1_freeSheafProjection_generator]
  simp only [ite_comp, Category.id_comp, zero_comp]
  erw [Finset.sum_ite_eq]
  rw [if_pos (Finset.mem_univ j.as)]

end HodgeLean.Foundations.Program.G32Native
