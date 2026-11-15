import HodgeLean.Foundations.QuotientDuality.ProperCycleAffineSuspensionSplit

/-! # The relative boundary chains of the affine suspension split
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular Convexity
open scoped Simplicial
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual point-complement pair in the real suspension product. -/
abbrev properCycle_affine_suspension_pair (d : ℕ) : TopPair :=
  TopPair.ofSubset (X := TopCat.of (ℝ × (Fin d → ℝ))) ({0}ᶜ : Set (ℝ × (Fin d → ℝ)))

/-- The extra-midpoint splitting simplex, regarded as an actual singular simplex. -/
def properCycle_affine_suspension_simplex (d : ℕ) :
    (TopCat.toSSet.obj (properCycle_affine_suspension_pair d).fst) _⦋d+2⦌ :=
  ((properCycle_affine_suspension_pair d).fst.toSSetObjEquiv _).symm
    ⟨properCycle_affine_suspension_split d, properCycle_continuous_affine_suspension_split d⟩

/-- Each irrelevant side face is a singular simplex in the actual punctured product. -/
def properCycle_affine_suspension_subspace_face (d : ℕ) (j : Fin d) :
    (TopCat.toSSet.obj (properCycle_affine_suspension_pair d).snd) _⦋d+1⦌ :=
  ((properCycle_affine_suspension_pair d).snd.toSSetObjEquiv _).symm
    ⟨fun t => ⟨properCycle_affine_suspension_split d
        (StdSimplex.map (Fin.castSucc (Fin.castSucc j.succ)).succAbove t),
      properCycle_affine_suspension_side_face_ne_zero d _ j
        (stdSimplex_map_succAbove_self_zero (d+1) _ t)⟩, by fun_prop⟩

/-- The actual punctured-space inclusion recovers the corresponding face chain. -/
theorem properCycle_affine_suspension_side_face_inclusion (d : ℕ) (j : Fin d) :
    (TopCat.toSSet.obj (properCycle_affine_suspension_pair d).snd).ιChainComplex
        (properCycle_affine_suspension_subspace_face d j) ≫
      ((chainPairFunctor ℚ).obj (properCycle_affine_suspension_pair d)).hom.f (d+1) =
    (TopCat.toSSet.obj (properCycle_affine_suspension_pair d).fst).ιChainComplex
      ((TopCat.toSSet.obj (properCycle_affine_suspension_pair d).fst).δ
        (Fin.castSucc (Fin.castSucc j.succ)) (properCycle_affine_suspension_simplex d)) := by
  change _ ≫ (SSet.chainComplexMap
    (TopCat.toSSet.map (properCycle_affine_suspension_pair d).map)
    (ModuleCat.of ℚ ℚ)).f (d+1) = _
  rw [SSet.ι_chainComplexMap_f]
  rfl

/-- Each irrelevant side face vanishes in the actual relative suspension chain complex. -/
theorem properCycle_affine_suspension_side_face_projection (d : ℕ) (j : Fin d) :
    (TopCat.toSSet.obj (properCycle_affine_suspension_pair d).fst).ιChainComplex
      ((TopCat.toSSet.obj (properCycle_affine_suspension_pair d).fst).δ
        (Fin.castSucc (Fin.castSucc j.succ)) (properCycle_affine_suspension_simplex d)) ≫
      (relativeChainProjection ℚ (properCycle_affine_suspension_pair d)).f (d+1) = 0 := by
  rw [← properCycle_affine_suspension_side_face_inclusion, Category.assoc,
    ← HomologicalComplex.comp_f, subspaceChainMap_relativeChainProjection,
    HomologicalComplex.zero_f, comp_zero]

/-- The splitting simplex in its literal relative chain quotient. -/
def properCycle_affine_suspension_chain (d : ℕ) :
    ModuleCat.of ℚ ℚ ⟶ ((relativeChainFunctor ℚ).obj (properCycle_affine_suspension_pair d)).X (d+2) :=
  (TopCat.toSSet.obj (properCycle_affine_suspension_pair d).fst).ιChainComplex
    (properCycle_affine_suspension_simplex d) ≫
      (relativeChainProjection ℚ (properCycle_affine_suspension_pair d)).f (d+2)

/-- A face of the splitting simplex in the same original relative quotient. -/
def properCycle_affine_suspension_face_chain (d : ℕ) (i : Fin (d+3)) :
    ModuleCat.of ℚ ℚ ⟶ ((relativeChainFunctor ℚ).obj (properCycle_affine_suspension_pair d)).X (d+1) :=
  (TopCat.toSSet.obj (properCycle_affine_suspension_pair d).fst).ιChainComplex
    ((TopCat.toSSet.obj (properCycle_affine_suspension_pair d).fst).δ i
      (properCycle_affine_suspension_simplex d)) ≫
    (relativeChainProjection ℚ (properCycle_affine_suspension_pair d)).f (d+1)

/-- The actual relative differential retains exactly the lower, upper and original faces with their original signs. -/
theorem properCycle_affine_suspension_chain_boundary (d : ℕ) :
    properCycle_affine_suspension_chain d ≫
      ((relativeChainFunctor ℚ).obj (properCycle_affine_suspension_pair d)).d (d+2) (d+1) =
    properCycle_affine_suspension_face_chain d 0 +
      (-1 : ℤ) ^ (d+1) • properCycle_affine_suspension_face_chain d (Fin.castSucc (Fin.last (d+1))) +
      (-1 : ℤ) ^ (d+2) • properCycle_affine_suspension_face_chain d (Fin.last (d+2)) := by
  have hb :
      (TopCat.toSSet.obj (properCycle_affine_suspension_pair d).fst).ιChainComplex
          (properCycle_affine_suspension_simplex d) ≫
        ((chainPairFunctor ℚ).obj (properCycle_affine_suspension_pair d)).right.d (d+2) (d+1) =
      ∑ i : Fin (d+3), (-1) ^ i.val •
        (TopCat.toSSet.obj (properCycle_affine_suspension_pair d).fst).ιChainComplex
          ((TopCat.toSSet.obj (properCycle_affine_suspension_pair d).fst).δ i
            (properCycle_affine_suspension_simplex d)) :=
    SSet.ιChainComplex_d _ (ModuleCat.of ℚ ℚ) _
  rw [properCycle_affine_suspension_chain, Category.assoc,
    (relativeChainProjection ℚ (properCycle_affine_suspension_pair d)).comm (d+2) (d+1),
    ← Category.assoc]
  erw [hb, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp]
  change (∑ i : Fin (d+3), (-1 : ℤ) ^ i.val • properCycle_affine_suspension_face_chain d i) = _
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  have hz : ∑ j : Fin d, (-1 : ℤ) ^ j.succ.val •
      properCycle_affine_suspension_face_chain d (Fin.castSucc (Fin.castSucc j.succ)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    change _ • (_ ≫ _) = 0
    rw [properCycle_affine_suspension_side_face_projection, smul_zero]
  simpa only [Fin.castSucc_zero, Fin.val_castSucc, Fin.val_last, Fin.val_zero, pow_zero, one_smul, hz, add_zero]

end HodgeLean.Foundations.QuotientDuality
