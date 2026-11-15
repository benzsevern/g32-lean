import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexOpenExcision
import HodgeLean.Foundations.QuotientDuality.ProperCycleAffineConnectingValue

/-! # The actual right quotient comparison with the original punctured product
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual union pair maps to the original punctured product by the identity on points. -/
def properCycle_affine_half_ray_union_to_point (d : ℕ) :
    TopPair.ofSubset (X := TopCat.of (ℝ × (Fin d → ℝ)))
      ({z | 0 ≤ z.1 ∧ z.2 = 0}ᶜ ∪ {z | z.1 ≤ 0 ∧ z.2 = 0}ᶜ) ⟶
      properCycle_affine_suspension_pair d :=
  TopPair.ofSubsetHom (𝟙 _) (fun z hz =>
    (properCycle_half_ray_complement_union (Fin d → ℝ) 0) ▸ hz)

/-- The specified original right comparison uses the actual small-chain and union quotient maps. -/
def properCycle_affine_half_ray_right_comparison (d : ℕ) :
    (properCycle_affine_half_ray_sequence d).X₃ ⟶
      (relativeChainFunctor ℚ).obj (properCycle_affine_suspension_pair d) :=
  (properCycle_subset_union_subcomplex_triad_iso (TopCat.of (ℝ × (Fin d → ℝ)))
    {z | 0 ≤ z.1 ∧ z.2 = 0}ᶜ {z | z.1 ≤ 0 ∧ z.2 = 0}ᶜ).hom ≫
  triadToUnionRelativeChainMap ℚ (TopCat.of (ℝ × (Fin d → ℝ)))
    {z | 0 ≤ z.1 ∧ z.2 = 0}ᶜ {z | z.1 ≤ 0 ∧ z.2 = 0}ᶜ ≫
  (relativeChainFunctor ℚ).map (properCycle_affine_half_ray_union_to_point d)

/-- The actual right comparison retains precisely the original ambient projection. -/
theorem properCycle_affine_half_ray_right_projection (d : ℕ) :
    cokernel.π (SSet.chainComplexMap
      (properCycle_affine_upper_half_subcomplex d ⊔ properCycle_affine_lower_half_subcomplex d).ι
        (ModuleCat.of ℚ ℚ)) ≫ properCycle_affine_half_ray_right_comparison d =
      relativeChainProjection ℚ (properCycle_affine_suspension_pair d) := by
  rw [properCycle_affine_half_ray_right_comparison, ← Category.assoc,
    properCycle_subset_union_subcomplex_triad_projection, ← Category.assoc,
    triadRelativeChainProjection_triadToUnionRelativeChainMap,
    TopPair.Homotopy.relativeChainProjection_naturality]
  change (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map
    (𝟙 (TopCat.of (ℝ × (Fin d → ℝ))))) ≫ _ = _
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- The first middle leg followed by the actual right comparison retains the original ambient projection. -/
theorem properCycle_affine_half_ray_right_inl_projection (d : ℕ) :
    relativeChainProjection ℚ (properCycle_real_upper_half_ray_pair d) ≫
      (properCycle_affine_half_ray_upper_iso d).inv ≫ biprod.inl ≫
        (properCycle_affine_half_ray_sequence d).g ≫ properCycle_affine_half_ray_right_comparison d =
      relativeChainProjection ℚ (properCycle_affine_suspension_pair d) := by
  rw [← properCycle_subset_subcomplex_relative_projection (TopCat.of (ℝ × (Fin d → ℝ)))
    {z | 0 ≤ z.1 ∧ z.2 = 0}ᶜ, Category.assoc, Iso.hom_inv_id_assoc]
  dsimp only [properCycle_affine_half_ray_sequence, properCycle_subcomplex_quotient_sequence]
  rw [biprod.inl_desc_assoc, ← Category.assoc, properCycle_subcomplex_quotient_projection,
    properCycle_affine_half_ray_right_projection]

/-- The second middle leg followed by the same actual right comparison retains the original ambient projection. -/
theorem properCycle_affine_half_ray_right_inr_projection (d : ℕ) :
    relativeChainProjection ℚ (properCycle_real_lower_half_ray_pair d) ≫
      (properCycle_affine_half_ray_lower_iso d).inv ≫ biprod.inr ≫
        (properCycle_affine_half_ray_sequence d).g ≫ properCycle_affine_half_ray_right_comparison d =
      relativeChainProjection ℚ (properCycle_affine_suspension_pair d) := by
  rw [← properCycle_subset_subcomplex_relative_projection (TopCat.of (ℝ × (Fin d → ℝ)))
    {z | z.1 ≤ 0 ∧ z.2 = 0}ᶜ, Category.assoc, Iso.hom_inv_id_assoc]
  dsimp only [properCycle_affine_half_ray_sequence, properCycle_subcomplex_quotient_sequence]
  rw [biprod.inr_desc_assoc, ← Category.assoc, properCycle_subcomplex_quotient_projection,
    properCycle_affine_half_ray_right_projection]

/-- The right quotient lift maps to the exact original signed two-half chain. -/
theorem properCycle_affine_half_ray_right_chain_original (d : ℕ) :
    properCycle_affine_half_ray_right_chain d ≫
        (properCycle_affine_half_ray_right_comparison d).f (d+1) =
      properCycle_real_suspension_halves_cycle d ≫
        ((relativeChainFunctor ℚ).obj (properCycle_affine_suspension_pair d)).iCycles (d+1) := by
  have hp := congrArg (fun m => m.f (d+1)) (properCycle_affine_half_ray_right_inl_projection d)
  have hq := congrArg (fun m => m.f (d+1)) (properCycle_affine_half_ray_right_inr_projection d)
  simp only [HomologicalComplex.comp_f] at hp hq
  rw [properCycle_real_suspension_halves_cycle_inclusion,
    properCycle_affine_half_ray_right_chain, properCycle_affine_half_ray_middle_chain]
  simp only [Preadditive.add_comp, Preadditive.zsmul_comp,
    properCycle_affine_lower_relative_chain, properCycle_affine_upper_relative_chain,
    Category.assoc, hp, hq]
  change (-1 : ℤ) ^ (d+1) • properCycle_affine_suspension_face_chain d 0 +
      properCycle_affine_suspension_face_chain d (Fin.castSucc (Fin.last (d+1))) = _
  exact add_comm _ _

/-- The actual right comparison sends the prescribed lift to the original signed two-half cycle. -/
theorem properCycle_affine_half_ray_right_cycle_original (d : ℕ) :
    properCycle_affine_half_ray_right_cycle d ≫
        HomologicalComplex.cyclesMap (properCycle_affine_half_ray_right_comparison d) (d+1) =
      properCycle_real_suspension_halves_cycle d := by
  apply (cancel_mono
    (((relativeChainFunctor ℚ).obj (properCycle_affine_suspension_pair d)).iCycles (d+1))).mp
  rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc,
    properCycle_affine_half_ray_right_cycle, HomologicalComplex.liftCycles_i,
    properCycle_affine_half_ray_right_chain_original]

/-- The actual right quotient lift has exactly the specified standard local class in the original punctured product. -/
theorem properCycle_affine_half_ray_right_class_standard (d : ℕ) :
    (HomologicalComplex.homologyMap (properCycle_affine_half_ray_right_comparison d) (d+1)).hom
      (((properCycle_affine_half_ray_right_cycle d ≫
        (properCycle_affine_half_ray_sequence d).X₃.homologyπ (d+1)).hom) 1) =
      relativeHomologyMap ℚ (d+1) (properCycle_real_suspension_pair_iso d).hom
        (standardLocalClass ℚ (d+1)) := by
  have hm : (properCycle_affine_half_ray_right_cycle d ≫
      (properCycle_affine_half_ray_sequence d).X₃.homologyπ (d+1)) ≫
        HomologicalComplex.homologyMap (properCycle_affine_half_ray_right_comparison d) (d+1) =
      properCycle_real_suspension_halves_cycle d ≫
        ((relativeChainFunctor ℚ).obj (properCycle_affine_suspension_pair d)).homologyπ (d+1) := by
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc,
      properCycle_affine_half_ray_right_cycle_original]
  exact (ConcreteCategory.congr_hom hm 1).trans (properCycle_real_suspension_halves_class d)

/-- The literal union-to-point pair map is an isomorphism retaining the actual identity on points. -/
theorem properCycle_affine_half_ray_union_to_point_isIso (d : ℕ) :
    IsIso (properCycle_affine_half_ray_union_to_point d) := by
  let e : TopPair.ofSubset (X := TopCat.of (ℝ × (Fin d → ℝ)))
      ({z | 0 ≤ z.1 ∧ z.2 = 0}ᶜ ∪ {z | z.1 ≤ 0 ∧ z.2 = 0}ᶜ) ≅
        properCycle_affine_suspension_pair d :=
    TopPair.isoOfSubset (Homeomorph.refl _) (by
      rw [properCycle_half_ray_complement_union]
      intro z
      rfl)
  have he : properCycle_affine_half_ray_union_to_point d = e.hom := by
    ext z : 2 <;> rfl
  rw [he]
  infer_instance

/-- Actual open-half-ray excision makes the specified right comparison a quasi-isomorphism. -/
theorem properCycle_affine_half_ray_right_quasiIso (d : ℕ) :
    QuasiIso (properCycle_affine_half_ray_right_comparison d) := by
  let X := TopCat.of (ℝ × (Fin d → ℝ))
  let P : Set X := {z | 0 ≤ z.1 ∧ z.2 = 0}ᶜ
  let Q : Set X := {z | z.1 ≤ 0 ∧ z.2 = 0}ᶜ
  have hP : IsOpen P := ((isClosed_le continuous_const continuous_fst).inter
    (isClosed_singleton.preimage continuous_snd)).isOpen_compl
  have hQ : IsOpen Q := ((isClosed_le continuous_fst continuous_const).inter
    (isClosed_singleton.preimage continuous_snd)).isOpen_compl
  letI : QuasiIso (triadToUnionRelativeChainMap ℚ X P Q) :=
    triadToUnionRelativeChainMap_quasiIso_of_isOpen X P Q hP hQ
  letI : IsIso (properCycle_affine_half_ray_union_to_point d) :=
    properCycle_affine_half_ray_union_to_point_isIso d
  unfold properCycle_affine_half_ray_right_comparison
  infer_instance

/-- The actual right comparison identifies quotient homology with the original punctured product homology. -/
def properCycle_affine_half_ray_right_homology_iso (d n : ℕ) :
    (properCycle_affine_half_ray_sequence d).X₃.homology n ≅
      RelativeHomology ℚ (properCycle_affine_suspension_pair d) n := by
  letI := properCycle_affine_half_ray_right_quasiIso d
  exact asIso (HomologicalComplex.homologyMap (properCycle_affine_half_ray_right_comparison d) n)

/-- Inverse excision sends the specified standard local class to the exact original two-half lift. -/
theorem properCycle_affine_half_ray_inverse_standard (d : ℕ) :
    (properCycle_affine_half_ray_right_homology_iso d (d+1)).inv.hom
      (relativeHomologyMap ℚ (d+1) (properCycle_real_suspension_pair_iso d).hom
        (standardLocalClass ℚ (d+1))) =
      (((properCycle_affine_half_ray_right_cycle d ≫
        (properCycle_affine_half_ray_sequence d).X₃.homologyπ (d+1)).hom) 1) := by
  let e := properCycle_affine_half_ray_right_homology_iso d (d+1)
  have h := properCycle_affine_half_ray_right_class_standard d
  change e.hom.hom (((properCycle_affine_half_ray_right_cycle d ≫
    (properCycle_affine_half_ray_sequence d).X₃.homologyπ (d+1)).hom) 1) = _ at h
  calc
    _ = e.inv.hom (e.hom.hom (((properCycle_affine_half_ray_right_cycle d ≫
        (properCycle_affine_half_ray_sequence d).X₃.homologyπ (d+1)).hom) 1)) :=
      congrArg e.inv.hom h.symm
    _ = _ := ConcreteCategory.congr_hom e.hom_inv_id _

end HodgeLean.Foundations.QuotientDuality
