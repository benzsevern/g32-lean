import HodgeLean.Foundations.QuotientDuality.ProperCycleAffineSuspensionChains

/-! # Ordered real coordinates for the affine suspension cycle
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Ordered real coordinates split off the first coordinate without permuting the others. -/
def properCycle_real_suspension_coordinates (d : ℕ) :
    (Fin (d+1) → ℝ) ≃ₜ (ℝ × (Fin d → ℝ)) where
  toFun z := (z 0, fun j => z j.succ)
  invFun z := Fin.cons z.1 z.2
  left_inv z := by funext i; exact Fin.cases rfl (fun j => rfl) i
  right_inv z := by apply Prod.ext <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro i
    exact Fin.cases continuous_fst (fun j => (continuous_apply j).comp continuous_snd) i

/-- The ordered real coordinate homeomorphism retains the literal point-complement pair. -/
def properCycle_real_suspension_pair_iso (d : ℕ) :
    puncturedPair ℝ (d+1) ≅ properCycle_affine_suspension_pair d :=
  TopPair.isoOfSubset (properCycle_real_suspension_coordinates d) (by
    intro z
    change properCycle_real_suspension_coordinates d z ≠ 0 ↔ z ≠ 0
    exact not_congr ((properCycle_real_suspension_coordinates d).injective.eq_iff' rfl))

/-- The ordered coordinates send the original standard local chain to the exact original face of the split. -/
theorem properCycle_real_suspension_original_chain (d : ℕ) :
    standardLocalChain ℚ (d+1) ≫
      ((relativeChainFunctor ℚ).map (properCycle_real_suspension_pair_iso d).hom).f (d+1) =
      properCycle_affine_suspension_face_chain d (Fin.last (d+2)) := by
  rw [standardLocalChain, standardLocalProjection, Category.assoc, ← HomologicalComplex.comp_f,
    TopPair.Homotopy.relativeChainProjection_naturality,
    HomologicalComplex.comp_f, ← Category.assoc]
  change (_ ≫ (SSet.chainComplexMap
    (TopCat.toSSet.map (TopPair.Hom.fst (properCycle_real_suspension_pair_iso d).hom))
    (ModuleCat.of ℚ ℚ)).f (d+1)) ≫ _ = _
  rw [standardAmbientSimplexChain, SSet.ι_chainComplexMap_f]
  unfold properCycle_affine_suspension_face_chain
  congr 2
  apply ((properCycle_affine_suspension_pair d).fst.toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  exact (properCycle_affine_suspension_original_face d t).symm

/-- The original face retains its zero relative differential under the ordered suspension coordinates. -/
theorem properCycle_real_suspension_original_boundary (d : ℕ) :
    properCycle_affine_suspension_face_chain d (Fin.last (d+2)) ≫
      ((relativeChainFunctor ℚ).obj (properCycle_affine_suspension_pair d)).d (d+1) d = 0 := by
  rw [← properCycle_real_suspension_original_chain, Category.assoc,
    ((relativeChainFunctor ℚ).map (properCycle_real_suspension_pair_iso d).hom).comm (d+1) d,
    ← Category.assoc, standardLocalChain_boundary_succ, CategoryTheory.Limits.zero_comp]

/-- The signed sum of the two halves differs from the original by the explicit splitting boundary. -/
theorem properCycle_real_suspension_halves_difference (d : ℕ) :
    properCycle_affine_suspension_face_chain d (Fin.castSucc (Fin.last (d+1))) +
        (-1 : ℤ) ^ (d+1) • properCycle_affine_suspension_face_chain d 0 -
          properCycle_affine_suspension_face_chain d (Fin.last (d+2)) =
      (-1 : ℤ) ^ (d+1) • (properCycle_affine_suspension_chain d ≫
        ((relativeChainFunctor ℚ).obj (properCycle_affine_suspension_pair d)).d (d+2) (d+1)) := by
  rw [properCycle_affine_suspension_chain_boundary, smul_add, smul_add, smul_smul, smul_smul]
  have hs : (-1 : ℤ) ^ (d+1) * (-1) ^ (d+1) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have ht : (-1 : ℤ) ^ (d+1) * (-1) ^ (d+2) = -1 := by
    change (-1 : ℤ) ^ (d+1) * (-1) ^ ((d+1)+1) = -1
    rw [pow_succ (-1 : ℤ) (d+1), ← mul_assoc, hs, one_mul]
  rw [hs, ht, one_smul, neg_one_smul]
  abel

end HodgeLean.Foundations.QuotientDuality
