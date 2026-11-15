import HodgeLean.Foundations.Program.SchoenCycleC1GenericLocalFieldSquare

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Local stalk compatibility determines rational pullback of the original
sections on every nonempty inverse-image open. -/
theorem s2e_c1_rational_section_pullback
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    (φ : Y.functionField →+* X.functionField)
    (hφ : ∀ (p : X) (r : Y.presheaf.stalk (f p)),
      φ (algebraMap (Y.presheaf.stalk (f p)) Y.functionField r) =
        algebraMap (X.presheaf.stalk p) X.functionField ((f.stalkMap p).hom r))
    (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] (s : Γ(Y, U)) :
    φ (Y.germToFunctionField U s) =
      X.germToFunctionField (f ⁻¹ᵁ U) (f.app U s) := by
  obtain ⟨p, hp⟩ := ‹Nonempty (f ⁻¹ᵁ U)›
  have he := hφ p (Y.presheaf.germ U (f p) hp s)
  rw [Scheme.algebraMap_germ_eq_germToFunctionField] at he
  rw [← ConcreteCategory.comp_apply, f.germ_stalkMap U p hp,
    ConcreteCategory.comp_apply, Scheme.algebraMap_germ_eq_germToFunctionField] at he
  exact he

end HodgeLean.Foundations.Program
