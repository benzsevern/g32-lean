import HodgeLean.Foundations.Program.G32Native.EulerModel.LocalOrientationFold

/-! # Relative singular chains of the repeated-vertex orientation simplex -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Convexity AlgebraicTopology.Singular
open scoped Simplicial
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual singular simplex with the inserted repeated-vertex pattern. -/
def foldedOrientationSingularSimplex (d i : ℕ) (hi : i + 1 < d) :
    (TopCat.toSSet.obj (puncturedPair ℝ d).fst) _⦋d + 1⦌ :=
  ((puncturedPair ℝ d).fst.toSSetObjEquiv _).symm (foldedOrientationSimplex d i hi)

/-- An omitted-coordinate face as an actual singular simplex in the punctured space. -/
def foldedOrientationPuncturedFace (d i : ℕ) (hi : i + 1 < d)
    (a : Fin (d + 2)) (hai : a.val ≠ i) (ha₂ : a.val ≠ i + 2) :
    (TopCat.toSSet.obj (puncturedPair ℝ d).snd) _⦋d⦌ :=
  ((puncturedPair ℝ d).snd.toSSetObjEquiv _).symm
    ⟨fun t => ⟨foldedOrientationSimplex d i hi (StdSimplex.map a.succAbove t),
      foldedOrientationSimplex_face_ne_zero d i hi a hai ha₂ t⟩, by fun_prop⟩

/-- The rational ambient chain of one face of the repeated-vertex simplex. -/
def foldedOrientationAmbientFace (d i : ℕ) (hi : i + 1 < d) (a : Fin (d + 2)) :
    ModuleCat.of ℚ ℚ ⟶ ((chainPairFunctor ℚ).obj (puncturedPair ℝ d)).right.X d :=
  (TopCat.toSSet.obj (puncturedPair ℝ d).fst).ιChainComplex
    ((TopCat.toSSet.obj (puncturedPair ℝ d).fst).δ a (foldedOrientationSingularSimplex d i hi))

/-- The rational chain of an omitted-coordinate face in the punctured subspace. -/
def foldedOrientationSubspaceFace (d i : ℕ) (hi : i + 1 < d)
    (a : Fin (d + 2)) (hai : a.val ≠ i) (ha₂ : a.val ≠ i + 2) :
    ModuleCat.of ℚ ℚ ⟶ ((chainPairFunctor ℚ).obj (puncturedPair ℝ d)).left.X d :=
  (TopCat.toSSet.obj (puncturedPair ℝ d).snd).ιChainComplex
    (foldedOrientationPuncturedFace d i hi a hai ha₂)

/-- The punctured face chain includes as precisely the specified ambient face. -/
theorem foldedOrientationFace_inclusion (d i : ℕ) (hi : i + 1 < d)
    (a : Fin (d + 2)) (hai : a.val ≠ i) (ha₂ : a.val ≠ i + 2) :
    foldedOrientationSubspaceFace d i hi a hai ha₂ ≫
        ((chainPairFunctor ℚ).obj (puncturedPair ℝ d)).hom.f d =
      foldedOrientationAmbientFace d i hi a := by
  change (TopCat.toSSet.obj (puncturedPair ℝ d).snd).ιChainComplex
      (foldedOrientationPuncturedFace d i hi a hai ha₂) ≫
    (SSet.chainComplexMap (TopCat.toSSet.map (puncturedPair ℝ d).map)
      (ModuleCat.of ℚ ℚ)).f d = _
  rw [SSet.ι_chainComplexMap_f]
  rfl

#print axioms foldedOrientationFace_inclusion

/-- Every omitted-coordinate face is zero in the actual relative chain quotient. -/
theorem foldedOrientationFace_projection_zero (d i : ℕ) (hi : i + 1 < d)
    (a : Fin (d + 2)) (hai : a.val ≠ i) (ha₂ : a.val ≠ i + 2) :
    foldedOrientationAmbientFace d i hi a ≫ (standardLocalProjection ℚ d).f d = 0 := by
  rw [← foldedOrientationFace_inclusion d i hi a hai ha₂, Category.assoc,
    ← HomologicalComplex.comp_f, standardLocalProjection,
    subspaceChainMap_relativeChainProjection, HomologicalComplex.zero_f, comp_zero]

#print axioms foldedOrientationFace_projection_zero

/-- The relative chain of the inserted repeated-vertex simplex. -/
def foldedOrientationRelativeChain (d i : ℕ) (hi : i + 1 < d) :
    ModuleCat.of ℚ ℚ ⟶ (standardLocalRelativeChainComplex ℚ d).X (d + 1) :=
  (TopCat.toSSet.obj (puncturedPair ℝ d).fst).ιChainComplex
    (foldedOrientationSingularSimplex d i hi) ≫ (standardLocalProjection ℚ d).f (d + 1)

/-- The actual relative boundary is the signed sum of the original affine face chains. -/
theorem foldedOrientationRelativeChain_boundary (d i : ℕ) (hi : i + 1 < d) :
    foldedOrientationRelativeChain d i hi ≫
        (standardLocalRelativeChainComplex ℚ d).d (d + 1) d =
      ∑ a : Fin (d + 2), (-1 : ℤ) ^ a.val •
        (foldedOrientationAmbientFace d i hi a ≫ (standardLocalProjection ℚ d).f d) := by
  have hb : (TopCat.toSSet.obj (puncturedPair ℝ d).fst).ιChainComplex
      (foldedOrientationSingularSimplex d i hi) ≫
      ((chainPairFunctor ℚ).obj (puncturedPair ℝ d)).right.d (d + 1) d =
      ∑ a : Fin (d + 2), (-1 : ℤ) ^ a.val • foldedOrientationAmbientFace d i hi a :=
    SSet.ιChainComplex_d (TopCat.toSSet.obj (puncturedPair ℝ d).fst)
      (ModuleCat.of ℚ ℚ) (foldedOrientationSingularSimplex d i hi)
  unfold foldedOrientationRelativeChain
  rw [Category.assoc, (standardLocalProjection ℚ d).comm (d + 1) d,
    ← Category.assoc, hb, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp]

#print axioms foldedOrientationRelativeChain_boundary

/-- Only the two distinguished faces survive, with exactly the same boundary sign. -/
theorem foldedOrientationRelativeChain_boundary_pair (d i : ℕ) (hi : i + 1 < d) :
    foldedOrientationRelativeChain d i hi ≫
        (standardLocalRelativeChainComplex ℚ d).d (d + 1) d =
      (-1 : ℤ) ^ i •
        ((foldedOrientationAmbientFace d i hi ⟨i, by omega⟩ ≫ (standardLocalProjection ℚ d).f d) +
          (foldedOrientationAmbientFace d i hi ⟨i + 2, by omega⟩ ≫ (standardLocalProjection ℚ d).f d)) := by
  classical
  let a₀ : Fin (d + 2) := ⟨i, by omega⟩
  let a₂ : Fin (d + 2) := ⟨i + 2, by omega⟩
  have hne : a₀ ≠ a₂ := by
    intro h
    have hval := congrArg Fin.val h
    dsimp [a₀, a₂] at hval
    omega
  rw [foldedOrientationRelativeChain_boundary]
  have hsum : (∑ a : Fin (d + 2), (-1 : ℤ) ^ a.val •
        (foldedOrientationAmbientFace d i hi a ≫ (standardLocalProjection ℚ d).f d)) =
      ∑ a ∈ ({a₀, a₂} : Finset (Fin (d + 2))), (-1 : ℤ) ^ a.val •
        (foldedOrientationAmbientFace d i hi a ≫ (standardLocalProjection ℚ d).f d) := by
    symm
    apply Finset.sum_subset (by simp)
    intro a ha hnot
    have hna : a ≠ a₀ ∧ a ≠ a₂ := by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hnot
    have hai : a.val ≠ i := fun h => hna.1 (Fin.ext h)
    have ha₂ : a.val ≠ i + 2 := fun h => hna.2 (Fin.ext h)
    rw [foldedOrientationFace_projection_zero d i hi a hai ha₂, smul_zero]
  rw [hsum, Finset.sum_pair hne]
  simp only [a₀, a₂]
  rw [pow_add]
  norm_num

#print axioms foldedOrientationRelativeChain_boundary_pair

/-- The second distinguished ambient face chain is the specified standard orientation chain. -/
theorem foldedOrientationAmbientFace_right (d i : ℕ) (hi : i + 1 < d) :
    foldedOrientationAmbientFace d i hi ⟨i + 2, by omega⟩ =
      standardAmbientSimplexChain ℚ d := by
  unfold foldedOrientationAmbientFace standardAmbientSimplexChain
  congr 1
  apply ((puncturedPair ℝ d).fst.toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  exact foldedOrientationSimplex_face_right d i hi t

#print axioms foldedOrientationAmbientFace_right
end HodgeLean.Foundations.Program.G32Native.EulerModel
