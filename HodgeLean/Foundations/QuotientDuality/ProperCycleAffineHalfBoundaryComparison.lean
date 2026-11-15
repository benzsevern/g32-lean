import HodgeLean.Foundations.QuotientDuality.ProperCycleAffineLowerBoundary

/-! # The same actual equator in both half-ray relative quotients
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
open scoped Simplicial
namespace HodgeLean.Foundations.QuotientDuality

/-- The two original face indices select the very same singular equatorial simplex. -/
theorem properCycle_affine_half_equator_face_identity (d : ℕ) :
    (TopCat.toSSet.obj (properCycle_affine_suspension_pair d).fst).δ (0 : Fin (d+2))
      ((TopCat.toSSet.obj (properCycle_affine_suspension_pair d).fst).δ
        (Fin.castSucc (Fin.last (d+1))) (properCycle_affine_suspension_simplex d)) =
    (TopCat.toSSet.obj (properCycle_affine_suspension_pair d).fst).δ
      (Fin.castSucc (Fin.last d))
      ((TopCat.toSSet.obj (properCycle_affine_suspension_pair d).fst).δ
        (0 : Fin (d+3)) (properCycle_affine_suspension_simplex d)) := by
  exact ConcreteCategory.congr_hom
    ((TopCat.toSSet.obj (properCycle_affine_suspension_pair d).fst).δ_comp_δ
      (i := 0) (j := Fin.castSucc (Fin.last d)) (Fin.zero_le _))
    (properCycle_affine_suspension_simplex d)

/-- The actual axis-complement pair maps to the upper-half-ray complement by the identity on points. -/
def properCycle_equator_to_upper_half_ray_pair (d : ℕ) :
    properCycle_real_equator_pair d ⟶ properCycle_real_upper_half_ray_pair d :=
  TopPair.ofSubsetHom (𝟙 _) (fun _ hz h => hz h.2)

/-- The actual axis-complement pair maps to the lower-half-ray complement by the identity on points. -/
def properCycle_equator_to_lower_half_ray_pair (d : ℕ) :
    properCycle_real_equator_pair d ⟶ properCycle_real_lower_half_ray_pair d :=
  TopPair.ofSubsetHom (𝟙 _) (fun _ hz h => hz h.2)

/-- The original equatorial chain maps to the exact surviving upper-half boundary face. -/
theorem properCycle_equator_chain_to_upper_boundary (d : ℕ) :
    properCycle_real_equator_face_chain d ≫
      ((relativeChainFunctor ℚ).map (properCycle_equator_to_lower_half_ray_pair d)).f d =
      properCycle_affine_upper_relative_face d 0 := by
  rw [properCycle_real_equator_face_chain, Category.assoc, ← HomologicalComplex.comp_f,
    TopPair.Homotopy.relativeChainProjection_naturality,
    HomologicalComplex.comp_f, ← Category.assoc]
  change (_ ≫ (SSet.chainComplexMap
    (TopCat.toSSet.map (TopPair.Hom.fst (properCycle_equator_to_lower_half_ray_pair d)))
      (ModuleCat.of ℚ ℚ)).f d) ≫ _ = _
  rw [SSet.ι_chainComplexMap_f]
  rfl

/-- The very same original equatorial chain maps to the surviving lower-half boundary face. -/
theorem properCycle_equator_chain_to_lower_boundary (d : ℕ) :
    properCycle_real_equator_face_chain d ≫
      ((relativeChainFunctor ℚ).map (properCycle_equator_to_upper_half_ray_pair d)).f d =
      properCycle_affine_lower_relative_face d (Fin.castSucc (Fin.last d)) := by
  rw [properCycle_real_equator_face_chain, Category.assoc, ← HomologicalComplex.comp_f,
    TopPair.Homotopy.relativeChainProjection_naturality,
    HomologicalComplex.comp_f, ← Category.assoc]
  change (_ ≫ (SSet.chainComplexMap
    (TopCat.toSSet.map (TopPair.Hom.fst (properCycle_equator_to_upper_half_ray_pair d)))
      (ModuleCat.of ℚ ℚ)).f d) ≫ _ = _
  rw [SSet.ι_chainComplexMap_f]
  unfold properCycle_affine_lower_relative_face
  congr 2
  exact properCycle_affine_half_equator_face_identity d

/-- The signed lower half from the original decomposition has negative equatorial differential. -/
theorem properCycle_affine_signed_lower_boundary (d : ℕ) :
    ((-1 : ℤ) ^ (d+1) • properCycle_affine_lower_relative_chain d) ≫
        ((relativeChainFunctor ℚ).obj (properCycle_real_upper_half_ray_pair d)).d (d+1) d =
      -(properCycle_real_equator_face_chain d ≫
        ((relativeChainFunctor ℚ).map (properCycle_equator_to_upper_half_ray_pair d)).f d) := by
  rw [Preadditive.zsmul_comp, properCycle_affine_lower_relative_boundary, smul_smul]
  have hs : (-1 : ℤ) ^ d * (-1) ^ d = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have ht : (-1 : ℤ) ^ (d+1) * (-1) ^ d = -1 := by
    rw [pow_succ]
    calc
      _ = ((-1 : ℤ) ^ d * (-1) ^ d) * (-1) := by ac_rfl
      _ = -1 := by rw [hs, one_mul]
  rw [ht, neg_one_smul, properCycle_equator_chain_to_lower_boundary]

end HodgeLean.Foundations.QuotientDuality
