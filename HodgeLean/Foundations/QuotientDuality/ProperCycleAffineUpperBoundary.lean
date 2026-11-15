import HodgeLean.Foundations.QuotientDuality.ProperCycleAffineHalfSpaceFaces

/-! # The upper affine half in its actual half-ray relative quotient
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular Convexity
open scoped Simplicial
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual relative pair complementary to the lower real half ray. -/
abbrev properCycle_real_lower_half_ray_pair (d : ℕ) : TopPair :=
  TopPair.ofSubset (X := TopCat.of (ℝ × (Fin d → ℝ))) {z | z.1 ≤ 0 ∧ z.2 = 0}ᶜ

/-- A non-equatorial face of the upper half as a simplex in the actual lower-half-ray complement. -/
def properCycle_affine_upper_subspace_face (d : ℕ) (i : Fin (d+2)) (hi : i ≠ 0) :
    (TopCat.toSSet.obj (properCycle_real_lower_half_ray_pair d).snd) _⦋d⦌ :=
  ((properCycle_real_lower_half_ray_pair d).snd.toSSetObjEquiv _).symm
    ⟨fun t => ⟨properCycle_affine_suspension_split d
        (StdSimplex.map (Fin.castSucc (Fin.last (d+1))).succAbove (StdSimplex.map i.succAbove t)),
      properCycle_affine_upper_boundary_lower_complement d _ i hi
        (stdSimplex_map_succAbove_self_zero d i t)⟩, by fun_prop⟩

/-- The actual subspace inclusion retains the specified boundary face chain of the upper half. -/
theorem properCycle_affine_upper_subspace_face_inclusion (d : ℕ) (i : Fin (d+2)) (hi : i ≠ 0) :
    (TopCat.toSSet.obj (properCycle_real_lower_half_ray_pair d).snd).ιChainComplex
        (properCycle_affine_upper_subspace_face d i hi) ≫
      ((chainPairFunctor ℚ).obj (properCycle_real_lower_half_ray_pair d)).hom.f d =
    (TopCat.toSSet.obj (properCycle_real_lower_half_ray_pair d).fst).ιChainComplex
      ((TopCat.toSSet.obj (properCycle_real_lower_half_ray_pair d).fst).δ i
        ((TopCat.toSSet.obj (properCycle_real_lower_half_ray_pair d).fst).δ
          (Fin.castSucc (Fin.last (d+1))) (properCycle_affine_suspension_simplex d))) := by
  change _ ≫ (SSet.chainComplexMap
    (TopCat.toSSet.map (properCycle_real_lower_half_ray_pair d).map) (ModuleCat.of ℚ ℚ)).f d = _
  rw [SSet.ι_chainComplexMap_f]
  rfl

/-- Every non-equatorial upper boundary face vanishes in the original half-ray quotient. -/
theorem properCycle_affine_upper_face_projection_zero (d : ℕ) (i : Fin (d+2)) (hi : i ≠ 0) :
    (TopCat.toSSet.obj (properCycle_real_lower_half_ray_pair d).fst).ιChainComplex
      ((TopCat.toSSet.obj (properCycle_real_lower_half_ray_pair d).fst).δ i
        ((TopCat.toSSet.obj (properCycle_real_lower_half_ray_pair d).fst).δ
          (Fin.castSucc (Fin.last (d+1))) (properCycle_affine_suspension_simplex d))) ≫
      (relativeChainProjection ℚ (properCycle_real_lower_half_ray_pair d)).f d = 0 := by
  rw [← properCycle_affine_upper_subspace_face_inclusion d i hi, Category.assoc,
    ← HomologicalComplex.comp_f, subspaceChainMap_relativeChainProjection,
    HomologicalComplex.zero_f, comp_zero]

/-- The upper half as a chain in the original lower-half-ray relative quotient. -/
def properCycle_affine_upper_relative_chain (d : ℕ) :
    ModuleCat.of ℚ ℚ ⟶ ((relativeChainFunctor ℚ).obj (properCycle_real_lower_half_ray_pair d)).X (d+1) :=
  (TopCat.toSSet.obj (properCycle_real_lower_half_ray_pair d).fst).ιChainComplex
    ((TopCat.toSSet.obj (properCycle_real_lower_half_ray_pair d).fst).δ
      (Fin.castSucc (Fin.last (d+1))) (properCycle_affine_suspension_simplex d)) ≫
    (relativeChainProjection ℚ (properCycle_real_lower_half_ray_pair d)).f (d+1)

/-- A boundary face of the upper half in the same actual relative quotient. -/
def properCycle_affine_upper_relative_face (d : ℕ) (i : Fin (d+2)) :
    ModuleCat.of ℚ ℚ ⟶ ((relativeChainFunctor ℚ).obj (properCycle_real_lower_half_ray_pair d)).X d :=
  (TopCat.toSSet.obj (properCycle_real_lower_half_ray_pair d).fst).ιChainComplex
    ((TopCat.toSSet.obj (properCycle_real_lower_half_ray_pair d).fst).δ i
      ((TopCat.toSSet.obj (properCycle_real_lower_half_ray_pair d).fst).δ
        (Fin.castSucc (Fin.last (d+1))) (properCycle_affine_suspension_simplex d))) ≫
    (relativeChainProjection ℚ (properCycle_real_lower_half_ray_pair d)).f d

/-- The actual upper relative differential is its equatorial face, with positive coefficient. -/
theorem properCycle_affine_upper_relative_boundary (d : ℕ) :
    properCycle_affine_upper_relative_chain d ≫
      ((relativeChainFunctor ℚ).obj (properCycle_real_lower_half_ray_pair d)).d (d+1) d =
      properCycle_affine_upper_relative_face d 0 := by
  have hb :
      (TopCat.toSSet.obj (properCycle_real_lower_half_ray_pair d).fst).ιChainComplex
          ((TopCat.toSSet.obj (properCycle_real_lower_half_ray_pair d).fst).δ
            (Fin.castSucc (Fin.last (d+1))) (properCycle_affine_suspension_simplex d)) ≫
        ((chainPairFunctor ℚ).obj (properCycle_real_lower_half_ray_pair d)).right.d (d+1) d =
      ∑ i : Fin (d+2), (-1) ^ i.val •
        (TopCat.toSSet.obj (properCycle_real_lower_half_ray_pair d).fst).ιChainComplex
          ((TopCat.toSSet.obj (properCycle_real_lower_half_ray_pair d).fst).δ i
            ((TopCat.toSSet.obj (properCycle_real_lower_half_ray_pair d).fst).δ
              (Fin.castSucc (Fin.last (d+1))) (properCycle_affine_suspension_simplex d))) :=
    SSet.ιChainComplex_d _ (ModuleCat.of ℚ ℚ) _
  rw [properCycle_affine_upper_relative_chain, Category.assoc,
    (relativeChainProjection ℚ (properCycle_real_lower_half_ray_pair d)).comm (d+1) d,
    ← Category.assoc]
  erw [hb, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp]
  change (∑ i : Fin (d+2), (-1 : ℤ) ^ i.val • properCycle_affine_upper_relative_face d i) = _
  rw [Fin.sum_univ_succ]
  have hz : ∑ j : Fin (d+1), (-1 : ℤ) ^ j.succ.val •
      properCycle_affine_upper_relative_face d j.succ = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    change _ • (_ ≫ _) = 0
    rw [properCycle_affine_upper_face_projection_zero d j.succ (Fin.succ_ne_zero _), smul_zero]
  simp only [Fin.val_zero, pow_zero, one_smul, hz, add_zero]

end HodgeLean.Foundations.QuotientDuality
