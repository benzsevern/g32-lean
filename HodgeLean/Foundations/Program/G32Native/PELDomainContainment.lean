import HodgeLean.Foundations.Program.G32Native.PELDomainCircle
import HodgeLean.Foundations.Program.G32Native.PELHodgeGroupContainment
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

noncomputable section
open HodgeLean.Foundations
open scoped Quaternion
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- Every domain Hodge group is contained in the connected PEL group.
Source: Abdulali, Annals of Mathematics 155 (2002), §§2.1–2.2. -/
theorem pelDomainHodgeGroup_subset_isometries (R : PELSplitReference)
    (z : PELSplitDomain R) :
    pelDomainHodgeGroup R z ⊆ pelGenericGroup (R.form.map (algebraMap ℚ ℂ))
      (Set.range fun i : Fin 4 =>
        (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map
          (algebraMap ℚ ℂ)) := by
  let G := pelIsometryGroup (R.form.map (algebraMap ℚ ℂ))
    (Set.range fun i : Fin 4 =>
      (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map (algebraMap ℚ ℂ))
  have ha : g2_IsRatAlgSubgroup (G.carrier : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ)) := by
    simpa only [G, ← Set.range_comp, Function.comp_def] using
      pelIsometryGroup_isRatAlg R.form (Set.range fun i : Fin 4 =>
        R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i))
  have hJ : (z.J.map (algebraMap ℝ ℂ)) * (z.J.map (algebraMap ℝ ℂ)) = -1 := by
    rw [← Matrix.map_mul, z.square, Matrix.map_neg, Matrix.map_one] <;> simp
  have hmap (M : Matrix (Fin 12) (Fin 12) ℚ) :
      (M.map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ) = M.map (algebraMap ℚ ℂ) := by
    ext i j
    simp only [Matrix.map_apply, ← IsScalarTower.algebraMap_apply ℚ ℝ ℂ]
  have hΩ : (z.J.map (algebraMap ℝ ℂ)).transpose * R.form.map (algebraMap ℚ ℂ) *
      z.J.map (algebraMap ℝ ℂ) = R.form.map (algebraMap ℚ ℂ) := by
    have h := congrArg (fun M : Matrix (Fin 12) (Fin 12) ℝ => M.map (algebraMap ℝ ℂ)) z.isometry
    simpa only [Matrix.map_mul, Matrix.transpose_map, hmap] using h
  have hs : pelDomainHodgeGroup R z ⊆ G.carrier := by
    apply Set.sInter_subset_of_mem
    refine ⟨ha, ?_⟩
    rintro g ⟨c, hc⟩
    obtain ⟨t, rfl⟩ := Circle.exp_surjective c
    have he : (g : Matrix (Fin 12) (Fin 12) ℂ) =
        pelCircleMatrix (z.J.map (algebraMap ℝ ℂ)) (-t) := by
      rw [hc, pelDomain_circle_matrix]
      simp [Circle.coe_exp, Complex.exp_mul_I, pelCircleMatrix, sub_eq_add_neg]
    apply (mem_pelIsometryGroup _ _ _).mpr
    rw [he]
    refine ⟨pelCircleMatrix_isometry _ _ hJ hΩ _, ?_⟩
    rintro T ⟨i, rfl⟩
    apply pelCircleMatrix_commute
    have h := congrArg (fun M : Matrix (Fin 12) (Fin 12) ℝ => M.map (algebraMap ℝ ℂ))
      (z.commute (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i))
    simpa only [Matrix.map_mul, hmap] using h
  exact @IsPreconnected.subset_connectedComponentIn _ (g1_zariski ℂ 12)
    _ _ _ (@IsConnected.isPreconnected _ (g1_zariski ℂ 12) _
      (g2_hodgeGroup_isConnected _ _ R.basis))
    (g2_isRatAlgSubgroup_hodgeGroup _ _ R.basis).2.1 hs

#print axioms pelDomainHodgeGroup_subset_isometries
end HodgeLean.Foundations.Program.GeneralTypeIII
