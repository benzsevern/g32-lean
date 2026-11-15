import HodgeLean.Foundations.QuotientDuality.ProperCycleAffineSuspensionHalves

/-! # The normalized equatorial relative class of the affine split
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original relative pair complementary to the entire real suspension axis. -/
abbrev properCycle_real_equator_pair (d : ℕ) : TopPair :=
  TopPair.ofSubset (X := TopCat.of (ℝ × (Fin d → ℝ))) {z | z.2 ≠ 0}

/-- The actual equatorial inclusion of the original punctured coordinate pair. -/
def properCycle_real_equator_section (d : ℕ) :
    puncturedPair ℝ d ⟶ properCycle_real_equator_pair d :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨fun z => (0,z), by fun_prop⟩) (fun _ hz => hz)

/-- The actual tangential projection from the equatorial relative pair. -/
def properCycle_real_equator_projection (d : ℕ) :
    properCycle_real_equator_pair d ⟶ puncturedPair ℝ d :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) (fun _ hz => hz)

/-- The equatorial inclusion followed by tangential projection is the original identity of pairs. -/
theorem properCycle_real_equator_section_projection (d : ℕ) :
    properCycle_real_equator_section d ≫ properCycle_real_equator_projection d =
      𝟙 (puncturedPair ℝ d) := by
  ext z : 2 <;> rfl

/-- Tangential projection of every positive affine equatorial class retains the specified local coefficient one. -/
theorem properCycle_real_equator_class_projection (d : ℕ) (a : ℝ) (ha : 0 < a) :
    relativeHomologyMap ℚ d (properCycle_real_equator_projection d)
      (relativeHomologyMap ℚ d (properCycle_real_equator_section d)
        (relativeHomologyMap ℚ d (properCycle_scaled_affine_pair d a ha)
          (properCycle_affine_boundary_class d))) = standardLocalClass ℚ d := by
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp,
    properCycle_real_equator_section_projection, relativeHomologyMap_id,
    LinearMap.id_apply, properCycle_affine_boundary_class_map_positive]

/-- The actual common face of the two suspension halves, in the axis-complement relative quotient. -/
def properCycle_real_equator_face_chain (d : ℕ) :
    ModuleCat.of ℚ ℚ ⟶ ((relativeChainFunctor ℚ).obj (properCycle_real_equator_pair d)).X d :=
  (TopCat.toSSet.obj (properCycle_real_equator_pair d).fst).ιChainComplex
    ((TopCat.toSSet.obj (properCycle_real_equator_pair d).fst).δ (0 : Fin (d+2))
      ((TopCat.toSSet.obj (properCycle_real_equator_pair d).fst).δ
        (Fin.castSucc (Fin.last (d+1))) (properCycle_affine_suspension_simplex d))) ≫
      (relativeChainProjection ℚ (properCycle_real_equator_pair d)).f d

/-- The original identity relative chain maps to the literal equatorial face with parameter one half. -/
theorem properCycle_real_equator_face_chain_map (d : ℕ) :
    properCycle_affine_boundary_chain d ≫
      ((relativeChainFunctor ℚ).map
        (properCycle_scaled_affine_pair d (1/2) (by norm_num) ≫
          properCycle_real_equator_section d)).f d = properCycle_real_equator_face_chain d := by
  rw [properCycle_affine_boundary_chain, Category.assoc, ← HomologicalComplex.comp_f,
    TopPair.Homotopy.relativeChainProjection_naturality,
    HomologicalComplex.comp_f, ← Category.assoc]
  change (_ ≫ (SSet.chainComplexMap
    (TopCat.toSSet.map (TopPair.Hom.fst
      (properCycle_scaled_affine_pair d (1/2) (by norm_num) ≫ properCycle_real_equator_section d)))
    (ModuleCat.of ℚ ℚ)).f d) ≫ _ = _
  rw [SSet.ι_chainComplexMap_f]
  unfold properCycle_real_equator_face_chain
  congr 2
  apply ((properCycle_real_equator_pair d).fst.toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  exact (properCycle_affine_suspension_equator d t).symm

/-- The actual common face as a relative cycle, supplied by the identity boundary-pair cycle. -/
def properCycle_real_equator_face_cycle (d : ℕ) :
    ModuleCat.of ℚ ℚ ⟶ ((relativeChainFunctor ℚ).obj (properCycle_real_equator_pair d)).cycles d :=
  properCycle_affine_boundary_cycle d ≫ HomologicalComplex.cyclesMap
    ((relativeChainFunctor ℚ).map
      (properCycle_scaled_affine_pair d (1/2) (by norm_num) ≫ properCycle_real_equator_section d)) d

/-- The cycle inclusion is the literal equatorial face chain with its original coefficient. -/
theorem properCycle_real_equator_face_cycle_inclusion (d : ℕ) :
    properCycle_real_equator_face_cycle d ≫
      ((relativeChainFunctor ℚ).obj (properCycle_real_equator_pair d)).iCycles d =
      properCycle_real_equator_face_chain d := by
  rw [properCycle_real_equator_face_cycle, Category.assoc, HomologicalComplex.cyclesMap_i,
    ← Category.assoc, properCycle_affine_boundary_cycle, HomologicalComplex.liftCycles_i]
  exact properCycle_real_equator_face_chain_map d

/-- Tangential projection of the literal equatorial cycle has precisely the specified local coefficient one. -/
theorem properCycle_real_equator_face_class_projection (d : ℕ) :
    relativeHomologyMap ℚ d (properCycle_real_equator_projection d)
      (((properCycle_real_equator_face_cycle d ≫
        ((relativeChainFunctor ℚ).obj (properCycle_real_equator_pair d)).homologyπ d).hom) 1) =
      standardLocalClass ℚ d := by
  have hmor : properCycle_real_equator_face_cycle d ≫
      ((relativeChainFunctor ℚ).obj (properCycle_real_equator_pair d)).homologyπ d =
    properCycle_affine_boundary_cycle d ≫
      ((relativeChainFunctor ℚ).obj (properCycle_affine_boundary_pair d)).homologyπ d ≫
        HomologicalComplex.homologyMap
          ((relativeChainFunctor ℚ).map
            (properCycle_scaled_affine_pair d (1/2) (by norm_num) ≫
              properCycle_real_equator_section d)) d := by
    rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc]
    rfl
  have hc := ConcreteCategory.congr_hom hmor 1
  change ((properCycle_real_equator_face_cycle d ≫ _).hom) 1 =
    relativeHomologyMap ℚ d
      (properCycle_scaled_affine_pair d (1/2) (by norm_num) ≫ properCycle_real_equator_section d)
      (properCycle_affine_boundary_class d) at hc
  refine (congrArg (relativeHomologyMap ℚ d (properCycle_real_equator_projection d)) hc).trans ?_
  rw [relativeHomologyMap_comp, LinearMap.comp_apply]
  exact properCycle_real_equator_class_projection d (1/2) (by norm_num)

end HodgeLean.Foundations.QuotientDuality
