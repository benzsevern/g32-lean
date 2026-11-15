import HodgeLean.Foundations.Program.G32Native.EulerModel.ProjectiveCoordinatePermutation

/-! # Specified coordinate isomorphisms on the actual complex projective schemes -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual projective complex-base-change maps retain composition of the specified integral maps. -/
theorem projectiveCoordinateBaseChange_comp {X Y Z : Scheme.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    s2e_projectiveBaseChange f ≫ s2e_projectiveBaseChange g =
      s2e_projectiveBaseChange (f ≫ g) := by
  apply pullback.hom_ext
  · simp only [s2e_projectiveBaseChange, Category.assoc, pullback.lift_fst]
  · simp only [s2e_projectiveBaseChange, Category.assoc, pullback.lift_snd_assoc,
      pullback.lift_snd]

#print axioms projectiveCoordinateBaseChange_comp
/-- Complex base change retains the identity on the actual projective pullback. -/
theorem projectiveCoordinateBaseChange_id (X : Scheme.{0}) :
    s2e_projectiveBaseChange (𝟙 X) =
      𝟙 (pullback (terminal.from (Spec ↧ℂ)) (terminal.from X)) := by
  apply pullback.hom_ext
  · simp only [s2e_projectiveBaseChange, pullback.lift_fst, Category.id_comp]
  · simp only [s2e_projectiveBaseChange, pullback.lift_snd, Category.comp_id, Category.id_comp]

#print axioms projectiveCoordinateBaseChange_id
/-- The actual complex projective coordinate isomorphism over the original complex base. -/
def complexProjectiveCoordinateIso {ι κ : Type} (e : ι ≃ κ) :
    Over.mk (ProjectiveSpace.toBase ι (Spec ↧ℂ)) ≅
      Over.mk (ProjectiveSpace.toBase κ (Spec ↧ℂ)) := by
  let E := integralProjectiveCoordinateIso e
  refine
    { hom := Over.homMk (s2e_projectiveBaseChange E.hom) (by exact pullback.lift_fst _ _ _)
      inv := Over.homMk (s2e_projectiveBaseChange E.inv) (by exact pullback.lift_fst _ _ _)
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Over.OverMorphism.ext
    change s2e_projectiveBaseChange E.hom ≫ s2e_projectiveBaseChange E.inv = 𝟙 _
    rw [projectiveCoordinateBaseChange_comp, E.hom_inv_id, projectiveCoordinateBaseChange_id]
  · apply Over.OverMorphism.ext
    change s2e_projectiveBaseChange E.inv ≫ s2e_projectiveBaseChange E.hom = 𝟙 _
    rw [projectiveCoordinateBaseChange_comp, E.inv_hom_id, projectiveCoordinateBaseChange_id]

#print axioms complexProjectiveCoordinateIso
end HodgeLean.Foundations.Program.G32Native.EulerModel
