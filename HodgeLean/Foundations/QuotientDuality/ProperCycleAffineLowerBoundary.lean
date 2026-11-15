import HodgeLean.Foundations.QuotientDuality.ProperCycleAffineUpperBoundary

/-! # The lower affine half in its actual half-ray relative quotient
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular Convexity
open scoped Simplicial
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual relative pair complementary to the upper real half ray. -/
abbrev properCycle_real_upper_half_ray_pair (d : ℕ) : TopPair :=
  TopPair.ofSubset (X := TopCat.of (ℝ × (Fin d → ℝ))) {z | 0 ≤ z.1 ∧ z.2 = 0}ᶜ

/-- A non-equatorial lower face as a simplex in the actual upper-half-ray complement. -/
def properCycle_affine_lower_subspace_face (d : ℕ) (i : Fin (d+2))
    (hi : i ≠ Fin.castSucc (Fin.last d)) :
    (TopCat.toSSet.obj (properCycle_real_upper_half_ray_pair d).snd) _⦋d⦌ :=
  ((properCycle_real_upper_half_ray_pair d).snd.toSSetObjEquiv _).symm
    ⟨fun t => ⟨properCycle_affine_suspension_split d
        (StdSimplex.map (0 : Fin (d+3)).succAbove (StdSimplex.map i.succAbove t)),
      properCycle_affine_lower_boundary_upper_complement d _ i hi
        (stdSimplex_map_succAbove_self_zero d i t)⟩, by fun_prop⟩

/-- The actual inclusion recovers the specified lower boundary face chain. -/
theorem properCycle_affine_lower_subspace_face_inclusion (d : ℕ) (i : Fin (d+2))
    (hi : i ≠ Fin.castSucc (Fin.last d)) :
    (TopCat.toSSet.obj (properCycle_real_upper_half_ray_pair d).snd).ιChainComplex
        (properCycle_affine_lower_subspace_face d i hi) ≫
      ((chainPairFunctor ℚ).obj (properCycle_real_upper_half_ray_pair d)).hom.f d =
    (TopCat.toSSet.obj (properCycle_real_upper_half_ray_pair d).fst).ιChainComplex
      ((TopCat.toSSet.obj (properCycle_real_upper_half_ray_pair d).fst).δ i
        ((TopCat.toSSet.obj (properCycle_real_upper_half_ray_pair d).fst).δ
          (0 : Fin (d+3)) (properCycle_affine_suspension_simplex d))) := by
  change _ ≫ (SSet.chainComplexMap
    (TopCat.toSSet.map (properCycle_real_upper_half_ray_pair d).map) (ModuleCat.of ℚ ℚ)).f d = _
  rw [SSet.ι_chainComplexMap_f]
  rfl

/-- Every non-equatorial lower boundary face vanishes in the original upper-half-ray quotient. -/
theorem properCycle_affine_lower_face_projection_zero (d : ℕ) (i : Fin (d+2))
    (hi : i ≠ Fin.castSucc (Fin.last d)) :
    (TopCat.toSSet.obj (properCycle_real_upper_half_ray_pair d).fst).ιChainComplex
      ((TopCat.toSSet.obj (properCycle_real_upper_half_ray_pair d).fst).δ i
        ((TopCat.toSSet.obj (properCycle_real_upper_half_ray_pair d).fst).δ
          (0 : Fin (d+3)) (properCycle_affine_suspension_simplex d))) ≫
      (relativeChainProjection ℚ (properCycle_real_upper_half_ray_pair d)).f d = 0 := by
  rw [← properCycle_affine_lower_subspace_face_inclusion d i hi, Category.assoc,
    ← HomologicalComplex.comp_f, subspaceChainMap_relativeChainProjection,
    HomologicalComplex.zero_f, comp_zero]

/-- The lower half as a chain in the original upper-half-ray relative quotient. -/
def properCycle_affine_lower_relative_chain (d : ℕ) :
    ModuleCat.of ℚ ℚ ⟶ ((relativeChainFunctor ℚ).obj (properCycle_real_upper_half_ray_pair d)).X (d+1) :=
  (TopCat.toSSet.obj (properCycle_real_upper_half_ray_pair d).fst).ιChainComplex
    ((TopCat.toSSet.obj (properCycle_real_upper_half_ray_pair d).fst).δ
      (0 : Fin (d+3)) (properCycle_affine_suspension_simplex d)) ≫
    (relativeChainProjection ℚ (properCycle_real_upper_half_ray_pair d)).f (d+1)

/-- A lower boundary face in the original upper-half-ray quotient. -/
def properCycle_affine_lower_relative_face (d : ℕ) (i : Fin (d+2)) :
    ModuleCat.of ℚ ℚ ⟶ ((relativeChainFunctor ℚ).obj (properCycle_real_upper_half_ray_pair d)).X d :=
  (TopCat.toSSet.obj (properCycle_real_upper_half_ray_pair d).fst).ιChainComplex
    ((TopCat.toSSet.obj (properCycle_real_upper_half_ray_pair d).fst).δ i
      ((TopCat.toSSet.obj (properCycle_real_upper_half_ray_pair d).fst).δ
        (0 : Fin (d+3)) (properCycle_affine_suspension_simplex d))) ≫
    (relativeChainProjection ℚ (properCycle_real_upper_half_ray_pair d)).f d

/-- The actual lower relative differential is the equatorial face with its original alternating sign. -/
theorem properCycle_affine_lower_relative_boundary (d : ℕ) :
    properCycle_affine_lower_relative_chain d ≫
      ((relativeChainFunctor ℚ).obj (properCycle_real_upper_half_ray_pair d)).d (d+1) d =
      (-1 : ℤ) ^ d • properCycle_affine_lower_relative_face d (Fin.castSucc (Fin.last d)) := by
  have hb := SSet.ιChainComplex_d
    (TopCat.toSSet.obj (properCycle_real_upper_half_ray_pair d).fst) (ModuleCat.of ℚ ℚ)
    ((TopCat.toSSet.obj (properCycle_real_upper_half_ray_pair d).fst).δ
      (0 : Fin (d+3)) (properCycle_affine_suspension_simplex d))
  rw [properCycle_affine_lower_relative_chain, Category.assoc,
    (relativeChainProjection ℚ (properCycle_real_upper_half_ray_pair d)).comm (d+1) d,
    ← Category.assoc]
  erw [hb, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp]
  change (∑ i : Fin (d+2), (-1 : ℤ) ^ i.val • properCycle_affine_lower_relative_face d i) = _
  rw [Fin.sum_univ_succAbove _ (Fin.castSucc (Fin.last d))]
  have hz : ∑ j : Fin (d+1), (-1 : ℤ) ^ ((Fin.castSucc (Fin.last d)).succAbove j).val •
      properCycle_affine_lower_relative_face d ((Fin.castSucc (Fin.last d)).succAbove j) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    change _ • (_ ≫ _) = 0
    rw [properCycle_affine_lower_face_projection_zero d _ (Fin.succAbove_ne _ _), smul_zero]
  simp only [Fin.val_castSucc, Fin.val_last, hz, add_zero]

end HodgeLean.Foundations.QuotientDuality
