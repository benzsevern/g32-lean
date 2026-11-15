import HodgeLean.Foundations.Program.SchoenCycleC1NormalModelHelpers
import HodgeLean.Foundations.Program.SchoenRetainedQuotientNormality
import HodgeLean.Foundations.Program.SchoenTowerDefs

/-! Initial normalization with the retained base and generic coordinates. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The finite normal model identifies the specified initial normalization. -/
theorem g32w_initial_normalization
    (W₀ B₀ B : Over (Spec ↧ℂ)) [IsIntegral W₀.left]
    (hnormal : ∀ x : W₀.left, IsIntegrallyClosed (W₀.left.presheaf.stalk x))
    (β₀ : W₀ ⟶ B₀) [IsFinite β₀.left] (e₀ : B ≅ B₀)
    (η : Spec W₀.left.functionField ⟶ B.left) [QuasiCompact η] [QuasiSeparated η]
    (hη : η ≫ e₀.hom.left =
      W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ β₀.left) :
    ∃ eW : s2b_normalizationOver B η ≅ W₀,
      eW.hom ≫ β₀ = s2b_normalizationMap B η ≫ e₀.hom ∧
      η.toNormalization ≫ eW.hom.left =
        W₀.left.fromSpecStalk (genericPoint W₀.left) := by
  let j := W₀.left.fromSpecStalk (genericPoint W₀.left)
  let π := β₀.left ≫ e₀.inv.left
  haveI : IsDominant j := s2_genericPointMorphism_dominant W₀.left
  have hf : η = j ≫ π := by
    dsimp only [j, π]
    rw [← Category.assoc, ← hη]
    simp only [Category.assoc, ← Over.comp_left, e₀.hom_inv_id, Over.id_left, Category.comp_id]
  obtain ⟨E, hgen, hbase⟩ := s2e_c1_normalization_iso_of_normal_model η j π hf
    (fun x => ⟨inferInstance, hnormal x⟩) (s2_genericPointMorphism_birational W₀.left)
  have hb : E.hom ≫ β₀.left = η.fromNormalization ≫ e₀.hom.left := by
    rw [← hbase]
    dsimp only [π]
    simp only [Category.assoc, ← Over.comp_left, e₀.inv_hom_id,
      Over.id_left, Category.comp_id]
  let f : s2b_normalizationOver B η ⟶ W₀ := Over.homMk E.hom (by
    change E.hom ≫ W₀.hom = η.fromNormalization ≫ B.hom
    rw [← Over.w β₀, ← Category.assoc, hb, Category.assoc, Over.w e₀.hom])
  haveI : IsIso f := by
    haveI : IsIso ((Over.forget (Spec ↧ℂ)).map f) :=
      show IsIso E.hom from inferInstance
    exact isIso_of_reflects_iso f (Over.forget (Spec ↧ℂ))
  exact ⟨asIso f, Over.OverMorphism.ext hb, hgen⟩

end HodgeLean.Foundations.Program
