import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Equivalence

/-! # Actual module pullback along a specified scheme isomorphism -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual module pullback along a scheme isomorphism is an equivalence,
using the original pullback composition and identity comparisons. -/
theorem paired_module_pullback_isEquivalence {X Y : Scheme} (e : X ≅ Y) :
    (Scheme.Modules.pullback e.hom).IsEquivalence :=
  Functor.IsEquivalence.mk' (Scheme.Modules.pullback e.inv)
    ((Scheme.Modules.pullbackComp e.inv e.hom ≪≫
      Scheme.Modules.pullbackCongr e.inv_hom_id ≪≫ Scheme.Modules.pullbackId Y).symm)
    (Scheme.Modules.pullbackComp e.hom e.inv ≪≫
      Scheme.Modules.pullbackCongr e.hom_inv_id ≪≫ Scheme.Modules.pullbackId X)

/-- Full faithful transport reflects an actual section of a morphism. -/
theorem paired_section_of_map_section {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) [F.Full] [F.Faithful] {P Q : C} (g : P ⟶ Q)
    (s : F.obj Q ⟶ F.obj P) (hs : s ≫ F.map g = 𝟙 _) :
    ∃ t : Q ⟶ P, t ≫ g = 𝟙 _ := by
  refine ⟨F.preimage s, ?_⟩
  apply F.map_injective
  rw [F.map_comp, F.map_preimage, F.map_id]
  exact hs

end HodgeLean.Foundations.Program.G32Native
