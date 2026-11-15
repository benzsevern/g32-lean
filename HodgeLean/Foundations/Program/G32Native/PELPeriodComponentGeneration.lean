import HodgeLean.Foundations.Program.G32Native.PELSplitHodgeContainment
import HodgeLean.Foundations.Program.G32Native.PELPeriodCircleComparison
import HodgeLean.Foundations.Program.G32Native.PELPeriodGroupGeneration

noncomputable section
open HodgeLean.Foundations
open scoped Quaternion
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- The full rank-three quaternionic period component generates the connected
D-linear polarization-isometry group inside the independently constructed
family Hodge group. The family's geometric fields retain all period points;
no Hodge-group comparison is a field of those data.
Source: Abdulali, Annals of Mathematics 155 (2002), Proposition 2.3.1,
p. 919, §§3.2–3.3, pp. 920–921, and §4, p. 922. -/
theorem pel_period_component_generates_aux (R : PELSplitReference) (F : PELSplitFamily R) :
    pelGenericGroup (R.form.map (algebraMap ℚ ℂ))
      (Set.range fun i : Fin 4 =>
        (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map
          (algebraMap ℚ ℂ)) ⊆ F.genericGroup := by
  apply pel_period_matrix_generation_aux R F.genericGroup
    (pel_family_group_isRatAlg F.hodgeGroup
      (fun z => g2_isRatAlgSubgroup_hodgeGroup _ _ (F.basis z)))
  intro z G hG
  exact hG.2 z (pel_period_matrix_mem_hodgeGroup_aux R F z)

/-- Identification of the independently defined marked family Hodge group.
Source: Abdulali, Annals of Mathematics 155 (2002), Proposition 2.3.1,
p. 919, and §4, p. 922. -/
theorem pel_family_group_identification (R : PELSplitReference) (F : PELSplitFamily R) :
    F.genericGroup = pelGenericGroup (R.form.map (algebraMap ℚ ℂ))
      (Set.range fun i : Fin 4 =>
        (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map
          (algebraMap ℚ ℂ)) :=
  Set.Subset.antisymm F.genericGroup_subset_isometries (pel_period_component_generates_aux R F)

/-- A member with the generic family Hodge group has the identified PEL group.
The generic-member premise compares to the independent family construction.
Source: Abdulali, Annals of Mathematics 155 (2002), Proposition 2.3.1,
p. 919, and §4, p. 922. -/
theorem pel_general_member_hodge_group (R : PELSplitReference) (F : PELSplitFamily R)
    (z : PELSplitComponent R) (hgeneral : F.hodgeGroup z = F.genericGroup) :
    F.hodgeGroup z = pelGenericGroup (R.form.map (algebraMap ℚ ℂ))
      (Set.range fun i : Fin 4 =>
        (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map
          (algebraMap ℚ ℂ)) :=
  hgeneral.trans (pel_family_group_identification R F)

#print axioms pel_period_component_generates_aux
#print axioms pel_family_group_identification
#print axioms pel_general_member_hodge_group
end HodgeLean.Foundations.Program.GeneralTypeIII
