import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Tensor.Monoidal

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace HodgeLean.Foundations.Program.G32Native

/-- An inverse tensor factor cancels two successive right tensor functors. -/
def pairedC3TensorCancelIso {C : Type*} [Category* C] [MonoidalCategory C]
    {L N : C} (e : L ⊗ N ≅ 𝟙_ C) :
    tensorRight L ⋙ tensorRight N ≅ 𝟭 C :=
  (tensorRightTensor L N).symm ≪≫
    (tensoringRight C).mapIso e ≪≫ rightUnitorNatIso C

/-- A section after tensoring descends through a specified inverse tensor factor.
The section identity concerns the original projection. -/
theorem paired_c3_section_of_tensor_section {C : Type*} [Category* C] [MonoidalCategory C]
    {A B L N : C} (e : L ⊗ N ≅ 𝟙_ C) (p : A ⟶ B)
    (s : (tensorRight L).obj B ⟶ (tensorRight L).obj A)
    (hs : s ≫ (tensorRight L).map p = 𝟙 _) :
    ∃ t : B ⟶ A, t ≫ p = 𝟙 _ := by
  let η := pairedC3TensorCancelIso e
  refine ⟨(η.app B).inv ≫ (tensorRight N).map s ≫ (η.app A).hom, ?_⟩
  have hn := η.hom.naturality p
  change (tensorRight N).map ((tensorRight L).map p) ≫ (η.app B).hom =
    (η.app A).hom ≫ p at hn
  rw [Category.assoc, Category.assoc, ← hn, ← Category.assoc _ _ (η.app B).hom,
    ← Functor.map_comp, hs, (tensorRight N).map_id]
  simp

end HodgeLean.Foundations.Program.G32Native
