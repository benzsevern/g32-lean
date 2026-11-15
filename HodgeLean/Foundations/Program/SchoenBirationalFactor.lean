import HodgeLean.Foundations.Program.SchoenGenericPointMorphisms

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A dominant intermediate factor of an actual birational composite is birational. -/
theorem s2_birational_of_dominant_factor {X Y Z : Scheme.{0}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) [IsDominant f] (g : Y ⟶ Z)
    (h : zmtiso_IsBirational (f ≫ g)) : zmtiso_IsBirational g := by
  have hf := s2_dominant_genericPoint f
  have hg : g (f (genericPoint X)) = genericPoint Z := h.1
  have hgen : g (genericPoint Y) = genericPoint Z := by rw [← hf]; exact hg
  refine ⟨hgen, ?_⟩
  haveI : IsSimpleRing (Y.presheaf.stalk (f (genericPoint X))) := by
    rw [hf]
    change IsSimpleRing Y.functionField
    infer_instance
  haveI : IsSimpleRing (Z.presheaf.stalk (g (f (genericPoint X)))) := by
    rw [hg]
    change IsSimpleRing Z.functionField
    infer_instance
  haveI : IsIso (g.stalkMap (f (genericPoint X)) ≫ f.stalkMap (genericPoint X)) := by
    rw [← Scheme.Hom.stalkMap_comp]
    exact h.2
  have hb := ConcreteCategory.bijective_of_isIso
    (g.stalkMap (f (genericPoint X)) ≫ f.stalkMap (genericPoint X))
  have hsurj : Function.Surjective (g.stalkMap (f (genericPoint X))).hom := by
    intro y
    obtain ⟨z, hz⟩ := hb.2 ((f.stalkMap (genericPoint X)).hom y)
    exact ⟨z, (f.stalkMap (genericPoint X)).hom.injective hz⟩
  have hi : IsIso (g.stalkMap (f (genericPoint X))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨(g.stalkMap (f (genericPoint X))).hom.injective, hsurj⟩
  rw [← hf]
  exact hi

end HodgeLean.Foundations.Program
