import HodgeLean.Foundations.QuotientDuality.ProperCycleDisjointSmallChains

/-! # Actual singular and image-subcomplex Mayer--Vietoris comparisons -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original singular small-chain sequence is the literal image-subcomplex sequence through its original singular image isomorphisms.
Source: Hatcher, Algebraic Topology, section 2.2, the small singular-chain sequence.
HC no distance; AV milestone no distance. -/
def properCycle_singular_subcomplex_mv_iso
    (X : TopCat.{0}) (U V : Set X) :
    singularMayerVietorisShortComplex X U V ≅
      subcomplexMayerVietorisShortComplex (subsetSingularSubcomplex X U) (subsetSingularSubcomplex X V) := by
  let C := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  let eI := subsetSingularIso X (U ∩ V) ≪≫
    SSet.Subcomplex.eqToIso (subsetSingularSubcomplex_inter X U V)
  let eU := subsetSingularIso X U
  let eV := subsetSingularIso X V
  refine ShortComplex.isoMk (C.mapIso eI)
    (biprod.mapIso (C.mapIso eU) (C.mapIso eV)) (Iso.refl _) ?_ ?_
  · apply biprod.hom_ext
    · simp only [biprod.mapIso, Category.assoc, singularMayerVietorisShortComplex,
        subcomplexMayerVietorisShortComplex, CommSq.shortComplex_f,
        biprod.lift_fst, biprod.lift_fst_assoc, biprod.map_fst]
      change C.map eI.hom ≫ C.map _ = C.map _ ≫ C.map eU.hom
      rw [← C.map_comp, ← C.map_comp]
      congr 1
    · simp only [biprod.mapIso, Category.assoc, singularMayerVietorisShortComplex,
        subcomplexMayerVietorisShortComplex, CommSq.shortComplex_f,
        biprod.lift_snd, biprod.lift_snd_assoc, biprod.map_snd,
        Preadditive.comp_neg, Preadditive.neg_comp]
      congr 1
      change C.map eI.hom ≫ C.map _ = C.map _ ≫ C.map eV.hom
      rw [← C.map_comp, ← C.map_comp]
      congr 1
  · erw [Category.comp_id]
    apply biprod.hom_ext'
    · simp only [biprod.mapIso, singularMayerVietorisShortComplex, subcomplexMayerVietorisShortComplex,
        CommSq.shortComplex_g, biprod.inl_map_assoc, biprod.inl_desc_assoc, biprod.inl_desc]
      change C.map eU.hom ≫ C.map _ = C.map _
      rw [← C.map_comp]
      rfl
    · simp only [biprod.mapIso, singularMayerVietorisShortComplex, subcomplexMayerVietorisShortComplex,
        CommSq.shortComplex_g, biprod.inr_map_assoc, biprod.inr_desc_assoc, biprod.inr_desc]
      change C.map eV.hom ≫ C.map _ = C.map _
      rw [← C.map_comp]
      rfl

/-- The original singular Mayer--Vietoris isomorphism commutes with the literal ambient diagonal diagram.
Source: Hatcher, Algebraic Topology, section 2.2, natural small-chain inclusions.
HC no distance; AV milestone no distance. -/
lemma properCycle_singular_subcomplex_mv_ambient
    (X : TopCat.{0}) (U V : Set X) :
    (properCycle_singular_subcomplex_mv_iso X U V).hom ≫
        properCycle_subcomplex_mv_to_ambient X (subsetSingularSubcomplex X U) (subsetSingularSubcomplex X V) =
      ProperCycleRelativeMV.subsetMayerVietorisToAmbient X U V := by
  let C := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  apply ShortComplex.hom_ext
  · change C.map ((subsetSingularIso X (U ∩ V) ≪≫
        SSet.Subcomplex.eqToIso (subsetSingularSubcomplex_inter X U V)).hom) ≫
      C.map _ = C.map _
    rw [← C.map_comp]
    congr 1
  · change biprod.map (C.map (subsetSingularIso X U).hom) (C.map (subsetSingularIso X V).hom) ≫
      biprod.map (C.map (subsetSingularSubcomplex X U).ι) (C.map (subsetSingularSubcomplex X V).ι) =
        biprod.map _ _
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst, biprod.map_fst_assoc]
      exact congrArg (fun m => biprod.fst ≫ m) (properCycle_subset_singular_chain_iso_inclusion X U)
    · simp only [Category.assoc, biprod.map_snd, biprod.map_snd_assoc]
      exact congrArg (fun m => biprod.snd ≫ m) (properCycle_subset_singular_chain_iso_inclusion X V)
  · change 𝟙 _ ≫ C.map _ = twoSubsetSmallChainInclusion X U V
    rw [Category.id_comp]
    rfl

/-- The original relative singular Mayer--Vietoris sequence is the constructed literal relative subcomplex quotient sequence.
Source: Hatcher, Algebraic Topology, section 2.2, relative small-chain comparison.
HC no distance; AV milestone no distance. -/
def properCycle_relative_singular_subcomplex_mv_iso
    (X : TopCat.{0}) (U V : Set X) :
    ProperCycleRelativeMV.relativeMayerVietorisSmallShortComplex X U V ≅
      properCycle_subcomplex_quotient_sequence (subsetSingularSubcomplex X U) (subsetSingularSubcomplex X V) := by
  let f := (properCycle_singular_subcomplex_mv_iso X U V).hom
  let g := properCycle_subcomplex_mv_to_ambient X (subsetSingularSubcomplex X U) (subsetSingularSubcomplex X V)
  letI : Epi f := by dsimp [f]; infer_instance
  exact (cokernelIsoOfEq (properCycle_singular_subcomplex_mv_ambient X U V)).symm ≪≫
    cokernelEpiComp f g ≪≫
      properCycle_subcomplex_mv_sequence_iso X (subsetSingularSubcomplex X U) (subsetSingularSubcomplex X V)

/-- The constructed comparison identifies the original relative singular connecting map with the actual quotient-sequence connecting map.
Source: Hatcher, Algebraic Topology, section 2.2, naturality of relative Mayer--Vietoris boundaries.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_singular_subcomplex_mv_connecting
    (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    (ProperCycleRelativeMV.relativeMayerVietorisSmallShortComplex_shortExact X U V).δ
        (n + 1) n (by simp) ≫
        HomologicalComplex.homologyMap (properCycle_relative_singular_subcomplex_mv_iso X U V).hom.τ₁ n =
      HomologicalComplex.homologyMap (properCycle_relative_singular_subcomplex_mv_iso X U V).hom.τ₃ (n + 1) ≫
        (properCycle_subcomplex_quotient_sequence_shortExact X
          (subsetSingularSubcomplex X U) (subsetSingularSubcomplex X V)).δ (n + 1) n (by simp) := by
  exact HomologicalComplex.HomologySequence.δ_naturality
    (properCycle_relative_singular_subcomplex_mv_iso X U V).hom
    (ProperCycleRelativeMV.relativeMayerVietorisSmallShortComplex_shortExact X U V)
    (properCycle_subcomplex_quotient_sequence_shortExact X
      (subsetSingularSubcomplex X U) (subsetSingularSubcomplex X V)) (n + 1) n (by simp)

end HodgeLean.Foundations.QuotientDuality
