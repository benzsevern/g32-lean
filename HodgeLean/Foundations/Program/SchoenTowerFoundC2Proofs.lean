import HodgeLean.Foundations.Program.SchoenGenericPointMorphisms

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The deck isomorphism induces a unique pullback isomorphism on the retained field.
Source: EGA I, Chapter I, 2.4, functoriality of local rings; Mathlib,
`Scheme.SpecMap_stalkMap_fromSpecStalk`. -/
theorem s2t_functionField_deck_aux (W : Scheme.{0}) [IsIntegral W]
    (d : W ≅ W) :
    ∃! e : W.functionField ≅ W.functionField,
      Spec.map e.hom ≫ W.fromSpecStalk (genericPoint W) =
        W.fromSpecStalk (genericPoint W) ≫ d.hom := by
  have hg := s2_dominant_genericPoint d.hom
  let e : W.functionField ≅ W.functionField :=
    eqToIso (congrArg (fun x => W.presheaf.stalk x) hg.symm) ≪≫
      asIso (d.hom.stalkMap (genericPoint W))
  have he : Spec.map e.hom ≫ W.fromSpecStalk (genericPoint W) =
      W.fromSpecStalk (genericPoint W) ≫ d.hom := by
    dsimp [e]
    rw [Spec.map_comp, Category.assoc]
    have ht : ∀ (x y : W) (h : x = y),
        Spec.map (eqToHom (congrArg (fun z => W.presheaf.stalk z) h)) ≫
          W.fromSpecStalk x = W.fromSpecStalk y := by
      intro x y h
      subst y
      simp
    rw [ht _ _ hg.symm, Scheme.SpecMap_stalkMap_fromSpecStalk]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply Quiver.Hom.op_inj
  apply Scheme.Spec.map_injective
  apply (cancel_mono (W.fromSpecStalk (genericPoint W))).mp
  exact he'.trans he.symm

end HodgeLean.Foundations.Program
