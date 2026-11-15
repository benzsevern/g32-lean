import HodgeLean.Foundations.Program.SchoenIntegralBirationalIso

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace HodgeLean.Foundations.Program

/-- An actual dominant morphism between integral schemes takes the generic point to the generic point. -/
theorem s2_dominant_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  apply IsGenericPoint.eq _ (genericPoint_spec Y)
  simpa only [Set.image_univ, f.denseRange.closure_range] using
    (genericPoint_spec X).image f.continuous

/-- The actual spectrum of the generic local ring maps dominantly to its integral scheme. -/
theorem s2_genericPointMorphism_dominant (X : Scheme.{0}) [IsIntegral X] :
    IsDominant (X.fromSpecStalk (genericPoint X)) := by
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.Subset.antisymm (Set.subset_univ _)
  rw [← (genericPoint_spec X).def]
  apply closure_mono
  rintro x rfl
  exact ⟨closedPoint X.functionField, Scheme.fromSpecStalk_closedPoint⟩

/-- The actual spectrum of the function field is birational to its integral scheme. -/
theorem s2_genericPointMorphism_birational (X : Scheme.{0}) [IsIntegral X] :
    zmtiso_IsBirational (X.fromSpecStalk (genericPoint X)) := by
  let f := X.fromSpecStalk (genericPoint X)
  haveI : IsDominant f := s2_genericPointMorphism_dominant X
  have hgen := s2_dominant_genericPoint f
  refine ⟨hgen, ?_⟩
  haveI : IsSimpleRing (X.presheaf.stalk (f (genericPoint (Spec X.functionField)))) := by
    rw [hgen]
    change IsSimpleRing X.functionField
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨(f.stalkMap _).hom.injective, f.stalkMap_surjective _⟩

end HodgeLean.Foundations.Program
