import HodgeLean.Foundations.Program.SchoenTowerL1bKummerAction

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Generic pullback intertwines the actual section germs with regular pullback. -/
theorem s2v_l1b_functionFieldPullback_germ
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f]
    (U : X.Opens) (V : Y.Opens) [Nonempty U] [Nonempty V]
    (hUV : U ≤ f ⁻¹ᵁ V) :
    Y.germToFunctionField V ≫ s2v_l1b_functionFieldPullback f =
      f.appLE V U hUV ≫ X.germToFunctionField U := by
  have hg := s2_dominant_genericPoint f
  have hx : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hy : f (genericPoint X) ∈ V := hUV hx
  have he : Y.germToFunctionField V ≫
      eqToHom (congrArg (fun y => Y.presheaf.stalk y) hg.symm) =
      Y.presheaf.germ V (f (genericPoint X)) hy := by
    generalize f (genericPoint X) = y at hg hy ⊢
    subst y
    simp only [eqToHom_refl, Category.comp_id]
  rw [s2v_l1b_functionFieldPullback, ← Category.assoc, he, f.germ_stalkMap]
  rw [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res]

end HodgeLean.Foundations.Program
