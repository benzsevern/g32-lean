import HodgeLean.Foundations.QuotientDuality.ProperCycleAffineLocalNormalization

/-! # The relative cycle of the simplex and its boundary
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular Convexity
open scoped Simplicial
namespace HodgeLean.Foundations.QuotientDuality

/-- The identity singular simplex of the actual barycentric simplex. -/
def properCycle_affine_identity_simplex (d : ℕ) :
    (TopCat.toSSet.obj (properCycle_affine_boundary_pair d).fst) _⦋d⦌ :=
  ((properCycle_affine_boundary_pair d).fst.toSSetObjEquiv _).symm (ContinuousMap.id _)

/-- A face of the simplex regarded as a singular simplex in its boundary subspace. -/
def properCycle_affine_boundary_face (n : ℕ) (i : Fin (n+2)) :
    (TopCat.toSSet.obj (properCycle_affine_boundary_pair (n+1)).snd) _⦋n⦌ :=
  ((properCycle_affine_boundary_pair (n+1)).snd.toSSetObjEquiv _).symm
    ⟨fun t => ⟨StdSimplex.map i.succAbove t,
      ⟨i, stdSimplex_map_succAbove_self_zero n i t⟩⟩, by fun_prop⟩

/-- The original boundary inclusion sends each boundary simplex to the corresponding face. -/
theorem properCycle_affine_boundary_face_inclusion (n : ℕ) (i : Fin (n+2)) :
    (TopCat.toSSet.obj (properCycle_affine_boundary_pair (n+1)).snd).ιChainComplex
        (properCycle_affine_boundary_face n i) ≫
      ((chainPairFunctor ℚ).obj (properCycle_affine_boundary_pair (n+1))).hom.f n =
    (TopCat.toSSet.obj (properCycle_affine_boundary_pair (n+1)).fst).ιChainComplex
      ((TopCat.toSSet.obj (properCycle_affine_boundary_pair (n+1)).fst).δ i
        (properCycle_affine_identity_simplex (n+1))) := by
  change _ ≫ (SSet.chainComplexMap
    (TopCat.toSSet.map (properCycle_affine_boundary_pair (n+1)).map)
    (ModuleCat.of ℚ ℚ)).f n = _
  rw [SSet.ι_chainComplexMap_f]
  rfl

/-- The identity simplex in the actual relative chain complex of its boundary pair. -/
def properCycle_affine_boundary_chain (d : ℕ) :
    ModuleCat.of ℚ ℚ ⟶ ((relativeChainFunctor ℚ).obj (properCycle_affine_boundary_pair d)).X d :=
  (TopCat.toSSet.obj (properCycle_affine_boundary_pair d).fst).ιChainComplex
    (properCycle_affine_identity_simplex d) ≫
      (relativeChainProjection ℚ (properCycle_affine_boundary_pair d)).f d

/-- Every face of the identity simplex vanishes in the boundary quotient. -/
theorem properCycle_affine_boundary_face_projection (n : ℕ) (i : Fin (n+2)) :
    (TopCat.toSSet.obj (properCycle_affine_boundary_pair (n+1)).fst).ιChainComplex
      ((TopCat.toSSet.obj (properCycle_affine_boundary_pair (n+1)).fst).δ i
        (properCycle_affine_identity_simplex (n+1))) ≫
      (relativeChainProjection ℚ (properCycle_affine_boundary_pair (n+1))).f n = 0 := by
  rw [← properCycle_affine_boundary_face_inclusion, Category.assoc,
    ← HomologicalComplex.comp_f, subspaceChainMap_relativeChainProjection,
    HomologicalComplex.zero_f, comp_zero]

/-- The identity simplex has zero differential in its actual relative boundary quotient. -/
theorem properCycle_affine_boundary_chain_boundary (d : ℕ) :
    properCycle_affine_boundary_chain d ≫
      ((relativeChainFunctor ℚ).obj (properCycle_affine_boundary_pair d)).d d
        ((ComplexShape.down ℕ).next d) = 0 := by
  cases d with
  | zero => simp
  | succ n =>
    have hb :
        (TopCat.toSSet.obj (properCycle_affine_boundary_pair (n+1)).fst).ιChainComplex
            (properCycle_affine_identity_simplex (n+1)) ≫
          ((chainPairFunctor ℚ).obj (properCycle_affine_boundary_pair (n+1))).right.d (n+1) n =
        ∑ i : Fin (n+2), (-1) ^ i.val •
          (TopCat.toSSet.obj (properCycle_affine_boundary_pair (n+1)).fst).ιChainComplex
            ((TopCat.toSSet.obj (properCycle_affine_boundary_pair (n+1)).fst).δ i
              (properCycle_affine_identity_simplex (n+1))) :=
      SSet.ιChainComplex_d _ (ModuleCat.of ℚ ℚ) _
    rw [ChainComplex.next_nat_succ, properCycle_affine_boundary_chain, Category.assoc,
      (relativeChainProjection ℚ (properCycle_affine_boundary_pair (n+1))).comm (n+1) n,
      ← Category.assoc]
    erw [hb, Preadditive.sum_comp]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Preadditive.zsmul_comp, properCycle_affine_boundary_face_projection, smul_zero]

/-- The identity simplex as a cycle in its original relative chain complex. -/
def properCycle_affine_boundary_cycle (d : ℕ) :
    ModuleCat.of ℚ ℚ ⟶ ((relativeChainFunctor ℚ).obj (properCycle_affine_boundary_pair d)).cycles d :=
  ((relativeChainFunctor ℚ).obj (properCycle_affine_boundary_pair d)).liftCycles
    (properCycle_affine_boundary_chain d) ((ComplexShape.down ℕ).next d) rfl
    (properCycle_affine_boundary_chain_boundary d)

/-- The original unit-coefficient relative fundamental class of the simplex and its boundary. -/
def properCycle_affine_boundary_class (d : ℕ) :
    RelativeHomology ℚ (properCycle_affine_boundary_pair d) d :=
  ((properCycle_affine_boundary_cycle d ≫
    ((relativeChainFunctor ℚ).obj (properCycle_affine_boundary_pair d)).homologyπ d).hom) 1

/-- The map at parameter one sends the identity relative chain to the original standard local chain. -/
theorem properCycle_affine_boundary_chain_map_one (d : ℕ) :
    properCycle_affine_boundary_chain d ≫
      ((relativeChainFunctor ℚ).map (properCycle_scaled_affine_pair d 1 zero_lt_one)).f d =
    standardLocalChain ℚ d := by
  rw [properCycle_affine_boundary_chain, Category.assoc, ← HomologicalComplex.comp_f,
    TopPair.Homotopy.relativeChainProjection_naturality]
  rw [HomologicalComplex.comp_f, ← Category.assoc]
  change (_ ≫ (SSet.chainComplexMap
    (TopCat.toSSet.map (TopPair.Hom.fst (properCycle_scaled_affine_pair d 1 zero_lt_one)))
    (ModuleCat.of ℚ ℚ)).f d) ≫ _ = _
  rw [SSet.ι_chainComplexMap_f]
  congr 2
  apply ((puncturedPair ℝ d).fst.toSSetObjEquiv _).injective
  change (⟨properCycle_scaled_affine_simplex d 1, _⟩ : C(_, _)) = _
  exact ContinuousMap.ext (congrFun (properCycle_scaled_affine_simplex_one d))

/-- The relative cycle map at parameter one retains the specified standard local cycle. -/
theorem properCycle_affine_boundary_cycle_map_one (d : ℕ) :
    properCycle_affine_boundary_cycle d ≫
      HomologicalComplex.cyclesMap
        ((relativeChainFunctor ℚ).map (properCycle_scaled_affine_pair d 1 zero_lt_one)) d =
      standardLocalCycle ℚ d := by
  apply (cancel_mono ((standardLocalRelativeChainComplex ℚ d).iCycles d)).mp
  rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc,
    properCycle_affine_boundary_cycle, HomologicalComplex.liftCycles_i,
    standardLocalCycle, HomologicalComplex.liftCycles_i]
  exact properCycle_affine_boundary_chain_map_one d

/-- The parameter-one image has exactly the original unit coefficient in local homology. -/
theorem properCycle_affine_boundary_class_map_one (d : ℕ) :
    relativeHomologyMap ℚ d (properCycle_scaled_affine_pair d 1 zero_lt_one)
      (properCycle_affine_boundary_class d) = standardLocalClass ℚ d := by
  have hmor : properCycle_affine_boundary_cycle d ≫
      ((relativeChainFunctor ℚ).obj (properCycle_affine_boundary_pair d)).homologyπ d ≫
        HomologicalComplex.homologyMap
          ((relativeChainFunctor ℚ).map (properCycle_scaled_affine_pair d 1 zero_lt_one)) d =
      standardLocalCycle ℚ d ≫ (standardLocalRelativeChainComplex ℚ d).homologyπ d := by
    rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc,
      properCycle_affine_boundary_cycle_map_one]
  exact ConcreteCategory.congr_hom hmor 1

/-- Positive vertex changes retain the coefficient of the specified standard local class. -/
theorem properCycle_affine_boundary_class_map_positive (d : ℕ) (a : ℝ) (ha : 0 < a) :
    relativeHomologyMap ℚ d (properCycle_scaled_affine_pair d a ha)
      (properCycle_affine_boundary_class d) = standardLocalClass ℚ d :=
  (properCycle_scaled_affine_pair_homology d d a ha _).trans
    (properCycle_affine_boundary_class_map_one d)

end HodgeLean.Foundations.QuotientDuality
