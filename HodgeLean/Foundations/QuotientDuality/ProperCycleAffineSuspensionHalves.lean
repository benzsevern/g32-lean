import HodgeLean.Foundations.QuotientDuality.ProperCycleAffineSuspensionCoordinates

/-! # The actual signed two-half relative suspension cycle
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original standard local cycle in ordered real product coordinates. -/
def properCycle_real_suspension_original_cycle (d : ℕ) :
    ModuleCat.of ℚ ℚ ⟶ ((relativeChainFunctor ℚ).obj (properCycle_affine_suspension_pair d)).cycles (d+1) :=
  standardLocalCycle ℚ (d+1) ≫ HomologicalComplex.cyclesMap
    ((relativeChainFunctor ℚ).map (properCycle_real_suspension_pair_iso d).hom) (d+1)

/-- The signed sum of the actual two halves, expressed as the original cycle plus its explicit boundary. -/
def properCycle_real_suspension_halves_cycle (d : ℕ) :
    ModuleCat.of ℚ ℚ ⟶ ((relativeChainFunctor ℚ).obj (properCycle_affine_suspension_pair d)).cycles (d+1) :=
  properCycle_real_suspension_original_cycle d +
    (-1 : ℤ) ^ (d+1) • (properCycle_affine_suspension_chain d ≫
      ((relativeChainFunctor ℚ).obj (properCycle_affine_suspension_pair d)).toCycles (d+2) (d+1))

/-- The actual chain of this cycle is the signed sum of the specified upper and lower faces. -/
theorem properCycle_real_suspension_halves_cycle_inclusion (d : ℕ) :
    properCycle_real_suspension_halves_cycle d ≫
      ((relativeChainFunctor ℚ).obj (properCycle_affine_suspension_pair d)).iCycles (d+1) =
    properCycle_affine_suspension_face_chain d (Fin.castSucc (Fin.last (d+1))) +
      (-1 : ℤ) ^ (d+1) • properCycle_affine_suspension_face_chain d 0 := by
  rw [properCycle_real_suspension_halves_cycle, Preadditive.add_comp, Preadditive.zsmul_comp,
    Category.assoc, HomologicalComplex.toCycles_i,
    properCycle_real_suspension_original_cycle, Category.assoc, HomologicalComplex.cyclesMap_i,
    ← Category.assoc, standardLocalCycle, HomologicalComplex.liftCycles_i,
    properCycle_real_suspension_original_chain]
  have h := properCycle_real_suspension_halves_difference d
  simpa only [add_comm] using (sub_eq_iff_eq_add.mp h).symm

/-- The explicit splitting boundary vanishes under the original homology projection. -/
theorem properCycle_real_suspension_halves_homology_projection (d : ℕ) :
    properCycle_real_suspension_halves_cycle d ≫
      ((relativeChainFunctor ℚ).obj (properCycle_affine_suspension_pair d)).homologyπ (d+1) =
    properCycle_real_suspension_original_cycle d ≫
      ((relativeChainFunctor ℚ).obj (properCycle_affine_suspension_pair d)).homologyπ (d+1) := by
  rw [properCycle_real_suspension_halves_cycle, Preadditive.add_comp, Preadditive.zsmul_comp,
    Category.assoc, HomologicalComplex.toCycles_comp_homologyπ, comp_zero, smul_zero, add_zero]

/-- The signed two-half class is the original standard local class in ordered real coordinates. -/
theorem properCycle_real_suspension_halves_class (d : ℕ) :
    ((properCycle_real_suspension_halves_cycle d ≫
      ((relativeChainFunctor ℚ).obj (properCycle_affine_suspension_pair d)).homologyπ (d+1)).hom) 1 =
    relativeHomologyMap ℚ (d+1) (properCycle_real_suspension_pair_iso d).hom
      (standardLocalClass ℚ (d+1)) := by
  rw [properCycle_real_suspension_halves_homology_projection]
  have hmor : properCycle_real_suspension_original_cycle d ≫
      ((relativeChainFunctor ℚ).obj (properCycle_affine_suspension_pair d)).homologyπ (d+1) =
    standardLocalCycle ℚ (d+1) ≫ (standardLocalRelativeChainComplex ℚ (d+1)).homologyπ (d+1) ≫
      HomologicalComplex.homologyMap
        ((relativeChainFunctor ℚ).map (properCycle_real_suspension_pair_iso d).hom) (d+1) := by
    rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc]
    rfl
  exact ConcreteCategory.congr_hom hmor 1

end HodgeLean.Foundations.QuotientDuality
