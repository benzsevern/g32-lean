import HodgeLean.Foundations.Program.SchoenComplexPowerModels
import HodgeLean.Foundations.Program.SchoenSegrePowerImmersion

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Foundations HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual complex Segre morphism from the retained projective-space power to its tuple-coordinate projective space. -/
def s2_complexSegreMap (d n : ℕ) :
    g3_power ((s2_terminalBaseChange (Spec ↧ℂ)).obj (g3c_P d)) n ⟶
      (s2_terminalBaseChange (Spec ↧ℂ)).obj
        (Proj (homogeneousSubmodule (Fin n → Fin (d + 1)) (ULift.{0} ℤ))) :=
  (s2_segrePowerComplexIso d n).hom ≫
    (s2_terminalBaseChange (Spec ↧ℂ)).map (s2_segrePowerMap d n)

/-- The actual complex Segre morphism is a scheme closed immersion. -/
theorem s2_complexSegreMap_isClosedImmersion (d n : ℕ) :
    IsClosedImmersion (s2_complexSegreMap d n).left := by
  letI := s2_segrePowerMap_isClosedImmersion d n
  letI := s2_terminalBaseChange_map_isClosedImmersion (Spec ↧ℂ) (s2_segrePowerMap d n)
  haveI : IsIso (s2_segrePowerComplexIso d n).hom.left := by
    change IsIso ((Over.forget (Spec ↧ℂ)).map (s2_segrePowerComplexIso d n).hom)
    infer_instance
  change IsClosedImmersion ((s2_segrePowerComplexIso d n).hom.left ≫
    ((s2_terminalBaseChange (Spec ↧ℂ)).map (s2_segrePowerMap d n)).left)
  exact IsClosedImmersion.comp _ _

/-- The actual complex Segre morphism intertwines retained factor permutations with base-changed graded coordinate maps. -/
theorem s2_complexSegreMap_permute (d n : ℕ) (σ : Equiv.Perm (Fin n)) :
    s2_permute ((s2_terminalBaseChange (Spec ↧ℂ)).obj (g3c_P d)) n σ ≫
        s2_complexSegreMap d n =
      s2_complexSegreMap d n ≫ (s2_terminalBaseChange (Spec ↧ℂ)).map
        (s2_segreCoordinateMap (ULift.{0} ℤ) d n σ) := by
  unfold s2_complexSegreMap
  rw [← Category.assoc, s2_segrePowerComplexIso_permute, Category.assoc,
    ← Functor.map_comp, s2_segrePowerMap_permute, Functor.map_comp, Category.assoc]

end HodgeLean.Foundations.Program
