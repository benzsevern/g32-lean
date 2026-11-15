import HodgeLean.Foundations.QuotientDuality.ProperCycleRealCapProjection
import HodgeLean.Foundations.QuotientDuality.ProperCycleRealSupportRightChain

/-! # The actual upper cap source in original relative coordinates
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual right source refinement followed by the original right chain comparison retains the literal ambient projection to the intersected zero-slice complement.
Source: properCycle_subcomplex_quotient_projection; properCycle_real_support_right_chain_projection.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_cap_source_refinement_right_projection
    (Y : TopCat.{0}) (S T : Set Y) :
    let X := TopCat.of (ℝ × Y)
    let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
    let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
    let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
    cokernel.π (SSet.chainComplexMap (A ⊔ (P ⊔ Q)).ι (ModuleCat.of ℚ ℚ)) ≫
        (properCycle_real_cap_source_refinement Y S T).τ₃ ≫
        properCycle_real_support_right_chain_map Y (S ∩ T) =
      relativeChainProjection ℚ (TopPair.ofSubset (X := X)
        {z | z.1 = 0 ∧ z.2 ∈ S ∩ T}ᶜ) := by
  dsimp only
  let X := TopCat.of (ℝ × Y)
  let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
  let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
  let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
  let P' := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ S ∩ T}ᶜ
  let Q' := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ S ∩ T}ᶜ
  have hle : A ⊔ (P ⊔ Q) ≤ P' ⊔ Q' := by
    apply sup_le
    · exact le_trans (properCycle_subset_subcomplex_mono X
        (show Prod.snd ⁻¹' Sᶜ ⊆ {z : X | 0 ≤ z.1 ∧ z.2 ∈ S ∩ T}ᶜ from
          fun _ hz hp => hz hp.2.1)) le_sup_left
    · apply sup_le
      · exact le_trans (properCycle_subset_subcomplex_mono X
          (show {z : X | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ ⊆
            {z | 0 ≤ z.1 ∧ z.2 ∈ S ∩ T}ᶜ from fun _ hz hp => hz ⟨hp.1, hp.2.2⟩)) le_sup_left
      · exact le_trans (properCycle_subset_subcomplex_mono X
          (show {z : X | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ ⊆
            {z | z.1 ≤ 0 ∧ z.2 ∈ S ∩ T}ᶜ from fun _ hz hp => hz ⟨hp.1, hp.2.2⟩)) le_sup_right
  have ht : (properCycle_real_cap_source_refinement Y S T).τ₃ =
      properCycle_subcomplex_quotient_map hle := by
    dsimp only [properCycle_real_cap_source_refinement, ShortComplex.comp_τ₃,
      properCycle_fixed_subcomplex_sequence_iso, ShortComplex.isoMk,
      properCycle_subcomplex_mv_refinement, properCycle_subcomplex_quotient_iso_of_eq,
      id_eq, ShortComplex.homMk, ShortComplex.Hom.comp]
    erw [properCycle_subcomplex_quotient_map_comp]
  rw [ht, ← Category.assoc, properCycle_subcomplex_quotient_projection]
  exact properCycle_real_support_right_chain_projection Y (S ∩ T)

/-- Both actual half-ray singular subcomplexes lie in the singular subcomplex of the zero-slice complement.
Source: properCycle_real_half_ray_support_union; properCycle_subset_subcomplex_mono.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_half_ray_union_subcomplex_le (Y : TopCat.{0}) (T : Set Y) :
    let X := TopCat.of (ℝ × Y)
    subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ ⊔
        subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ ≤
      subsetSingularSubcomplex X {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ := by
  dsimp only
  apply sup_le
  · exact properCycle_subset_subcomplex_mono _
      ((Set.subset_union_left : {z : ℝ × Y | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ ⊆
        {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ ∪ {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ).trans
          (properCycle_real_half_ray_support_union Y T).le)
  · exact properCycle_subset_subcomplex_mono _
      ((Set.subset_union_right : {z : ℝ × Y | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ ⊆
        {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ ∪ {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ).trans
          (properCycle_real_half_ray_support_union Y T).le)

/-- The actual upper cap source maps to the original normal/zero-slice triad by the literal quotient inclusion.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3; properCycle_real_half_ray_union_subcomplex_le; properCycle_subset_union_subcomplex_triad_iso.
HC no distance; AV milestone no distance. -/
def properCycle_real_cap_upper_triad_map (Y : TopCat.{0}) (S T : Set Y) :
    let X := TopCat.of (ℝ × Y)
    let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
    let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
    let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
    (properCycle_fixed_subcomplex_sequence A P Q).X₃ ⟶
      triadRelativeChainComplex ℚ X (Prod.snd ⁻¹' Sᶜ) {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ :=
  properCycle_subcomplex_quotient_map
    (sup_le_sup_left (properCycle_real_half_ray_union_subcomplex_le Y T)
      (subsetSingularSubcomplex (TopCat.of (ℝ × Y)) (Prod.snd ⁻¹' Sᶜ))) ≫
    (properCycle_subset_union_subcomplex_triad_iso (TopCat.of (ℝ × Y))
      (Prod.snd ⁻¹' Sᶜ) {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ).hom

/-- The actual upper cap triad map retains the literal ambient sum-relative projection.
Source: properCycle_subcomplex_quotient_projection; properCycle_subset_union_subcomplex_triad_projection.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_cap_upper_triad_projection (Y : TopCat.{0}) (S T : Set Y) :
    let X := TopCat.of (ℝ × Y)
    let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
    let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
    let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
    cokernel.π (SSet.chainComplexMap (A ⊔ (P ⊔ Q)).ι (ModuleCat.of ℚ ℚ)) ≫
        properCycle_real_cap_upper_triad_map Y S T =
      triadRelativeChainProjection ℚ X (Prod.snd ⁻¹' Sᶜ) {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ := by
  dsimp only
  rw [properCycle_real_cap_upper_triad_map, ← Category.assoc,
    properCycle_subcomplex_quotient_projection, properCycle_subset_union_subcomplex_triad_projection]

/-- The actual right support chain comparison is precisely quotient inclusion followed by the original zero-slice relative comparison.
Source: properCycle_real_support_right_chain_projection; properCycle_subcomplex_quotient_projection; properCycle_subset_subcomplex_relative_projection.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_support_right_chain_quotient (Y : TopCat.{0}) (T : Set Y) :
    properCycle_real_support_right_chain_map Y T =
      properCycle_subcomplex_quotient_map (properCycle_real_half_ray_union_subcomplex_le Y T) ≫
        (properCycle_subset_subcomplex_relative_iso (TopCat.of (ℝ × Y))
          {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ).hom := by
  let X := TopCat.of (ℝ × Y)
  let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
  let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
  apply (cancel_epi (cokernel.π (SSet.chainComplexMap (P ⊔ Q).ι (ModuleCat.of ℚ ℚ)))).mp
  rw [properCycle_real_support_right_chain_projection Y T, ← Category.assoc,
    properCycle_subcomplex_quotient_projection, properCycle_subset_subcomplex_relative_projection]

/-- The actual upper quotient cap agrees with the original normal/zero-slice triad cap through its literal source and target chain comparisons.
Source: properCycle_subcomplex_cap_homology_inclusion; properCycle_subcomplex_original_triad_cap_homology; properCycle_real_support_right_chain_quotient.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_upper_triad_cap_homology
    (Y : TopCat.{0}) (S T : Set Y) (p q : ℕ) (hp : Even p)
    (φ : RelativeCochain ℚ (TopPair.ofSubset (X := TopCat.of (ℝ × Y)) (Prod.snd ⁻¹' Sᶜ)) p)
    (hφ : relativeCoboundary ℚ (TopPair.ofSubset (X := TopCat.of (ℝ × Y)) (Prod.snd ⁻¹' Sᶜ)) p φ = 0) :
    let X := TopCat.of (ℝ × Y)
    let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
    let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
    let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
    let ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) p :=
      ⟨relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) (Prod.snd ⁻¹' Sᶜ)) p φ,
        (relativeCochainToAbsolute_coboundary ℚ
          (TopPair.ofSubset (X := X) (Prod.snd ⁻¹' Sᶜ)) p φ).symm.trans
          ((congrArg (relativeCochainToAbsolute ℚ
            (TopPair.ofSubset (X := X) (Prod.snd ⁻¹' Sᶜ)) (p+1)) hφ).trans (map_zero _))⟩
    properCycle_subcomplex_cap_homology_map A (P ⊔ Q) p q hp ψ.1
        (properCycle_relative_cochain_subcomplex_zero X (Prod.snd ⁻¹' Sᶜ) p φ) ψ.2 ≫
        HomologicalComplex.homologyMap (properCycle_real_support_right_chain_map Y T) q =
      HomologicalComplex.homologyMap (properCycle_real_cap_upper_triad_map Y S T) (p+q) ≫
        ModuleCat.ofHom (triadCapHomologyMap ℚ X (Prod.snd ⁻¹' Sᶜ)
          {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ p q φ hφ) := by
  dsimp only
  let X := TopCat.of (ℝ × Y)
  let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
  let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
  let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
  let U := subsetSingularSubcomplex X {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ
  let hU := properCycle_real_half_ray_union_subcomplex_le Y T
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ)
  let I := (H (p+q)).mapIso (properCycle_subset_union_subcomplex_triad_iso X
    (Prod.snd ⁻¹' Sᶜ) {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ)
  let V := HomologicalComplex.homologyMap
    (properCycle_subset_subcomplex_relative_iso X {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ).hom q
  let χ := relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) (Prod.snd ⁻¹' Sᶜ)) p φ
  have hA : AlgebraicTopology.Simplicial.cochainMap ℚ A.ι p χ = 0 :=
    properCycle_relative_cochain_subcomplex_zero X (Prod.snd ⁻¹' Sᶜ) p φ
  have hχ : AlgebraicTopology.Simplicial.coboundary ℚ p χ = 0 :=
    (relativeCochainToAbsolute_coboundary ℚ
      (TopPair.ofSubset (X := X) (Prod.snd ⁻¹' Sᶜ)) p φ).symm.trans
      ((congrArg (relativeCochainToAbsolute ℚ
        (TopPair.ofSubset (X := X) (Prod.snd ⁻¹' Sᶜ)) (p+1)) hφ).trans (map_zero _))
  let Kold := properCycle_subcomplex_cap_homology_map A (P ⊔ Q) p q hp χ hA hχ
  let Knew := properCycle_subcomplex_cap_homology_map A U p q hp χ hA hχ
  let qs := HomologicalComplex.homologyMap
    (properCycle_subcomplex_quotient_map (sup_le_sup_left hU A)) (p+q)
  let qt := HomologicalComplex.homologyMap (properCycle_subcomplex_quotient_map hU) q
  have hi := properCycle_subcomplex_cap_homology_inclusion A (P ⊔ Q) U hU p q hp χ hA hχ
  change Kold ≫ qt = qs ≫ Knew at hi
  have ho := properCycle_subcomplex_original_triad_cap_homology X (Prod.snd ⁻¹' Sᶜ)
    {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ p q hp φ hφ
  have ho' := congrArg (fun m => I.hom ≫ m) ho
  change I.hom ≫ (I.inv ≫ Knew ≫ V) = _ at ho'
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at ho'
  have ht : HomologicalComplex.homologyMap (properCycle_real_support_right_chain_map Y T) q =
      qt ≫ V := by
    rw [properCycle_real_support_right_chain_quotient, HomologicalComplex.homologyMap_comp]
  have hs : HomologicalComplex.homologyMap (properCycle_real_cap_upper_triad_map Y S T) (p+q) =
      qs ≫ I.hom := by
    rw [properCycle_real_cap_upper_triad_map, HomologicalComplex.homologyMap_comp]
    rfl
  rw [ht, hs]
  change Kold ≫ (qt ≫ V) = (qs ≫ I.hom) ≫ _
  rw [← Category.assoc, hi, Category.assoc, ho']
  simp only [Category.assoc]
  rfl

/-- The union of the actual normal and zero-slice complements is the intersected zero-slice complement, through the literal identity point map.
Source: Hatcher, Algebraic Topology, section 2.2, relative triad supports; De Morgan's law.
HC no distance; AV milestone no distance. -/
def properCycle_real_cap_upper_union_iso (Y : TopCat.{0}) (S T : Set Y) :
    TopPair.ofSubset (X := TopCat.of (ℝ × Y))
      ((Prod.snd ⁻¹' Sᶜ) ∪ {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ) ≅
    TopPair.ofSubset (X := TopCat.of (ℝ × Y))
      {z | z.1 = 0 ∧ z.2 ∈ S ∩ T}ᶜ :=
  TopPair.isoOfSubset (Homeomorph.refl _) (by
    classical
    intro z
    change ¬ (z.1 = 0 ∧ (z.2 ∈ S ∧ z.2 ∈ T)) ↔
      (z.2 ∉ S ∨ ¬ (z.1 = 0 ∧ z.2 ∈ T))
    tauto)

/-- Actual right source refinement and right support comparison coincide with the original upper triad-to-union map in the specified zero-slice relative coordinates.
Source: properCycle_real_cap_source_refinement_right_projection; properCycle_real_cap_upper_triad_projection; relativeChainProjection_naturality.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_cap_upper_source_comparison (Y : TopCat.{0}) (S T : Set Y) :
    (properCycle_real_cap_source_refinement Y S T).τ₃ ≫
        properCycle_real_support_right_chain_map Y (S ∩ T) =
      properCycle_real_cap_upper_triad_map Y S T ≫
        triadToUnionRelativeChainMap ℚ (TopCat.of (ℝ × Y)) (Prod.snd ⁻¹' Sᶜ)
          {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ ≫
        (relativeChainFunctor ℚ).map (properCycle_real_cap_upper_union_iso Y S T).hom := by
  let X := TopCat.of (ℝ × Y)
  let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
  let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
  let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
  let π := cokernel.π (SSet.chainComplexMap (A ⊔ (P ⊔ Q)).ι (ModuleCat.of ℚ ℚ))
  apply (cancel_epi π).mp
  rw [properCycle_real_cap_source_refinement_right_projection Y S T]
  have h := congrArg (fun m => m ≫
    triadToUnionRelativeChainMap ℚ X (Prod.snd ⁻¹' Sᶜ) {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ ≫
      (relativeChainFunctor ℚ).map (properCycle_real_cap_upper_union_iso Y S T).hom)
    (properCycle_real_cap_upper_triad_projection Y S T)
  simp only [← Category.assoc] at h
  rw [triadRelativeChainProjection_triadToUnionRelativeChainMap] at h
  have hn := TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ)
    (properCycle_real_cap_upper_union_iso Y S T).hom
  change relativeChainProjection ℚ (TopPair.ofSubset (X := X)
      ((Prod.snd ⁻¹' Sᶜ) ∪ {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ)) ≫
      (relativeChainFunctor ℚ).map (properCycle_real_cap_upper_union_iso Y S T).hom =
    (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map (𝟙 X)) ≫
      relativeChainProjection ℚ (TopPair.ofSubset (X := X)
        {z | z.1 = 0 ∧ z.2 ∈ S ∩ T}ᶜ) at hn
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at hn
  simpa only [Category.assoc] using hn.symm.trans h.symm

/-- The upper transported cap is the original normal/zero-slice triad cap through the specified union-relative source comparison.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3; properCycle_real_cap_upper_source_comparison; properCycle_real_upper_triad_cap_homology.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_upper_support_cap_comparison
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T)
    (p q : ℕ) (hp : Even p)
    (φ : RelativeCochain ℚ (TopPair.ofSubset (X := TopCat.of (ℝ × Y)) (Prod.snd ⁻¹' Sᶜ)) p)
    (hφ : relativeCoboundary ℚ (TopPair.ofSubset (X := TopCat.of (ℝ × Y)) (Prod.snd ⁻¹' Sᶜ)) p φ = 0) :
    let X := TopCat.of (ℝ × Y)
    let χ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) p :=
      ⟨relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) (Prod.snd ⁻¹' Sᶜ)) p φ,
        (relativeCochainToAbsolute_coboundary ℚ
          (TopPair.ofSubset (X := X) (Prod.snd ⁻¹' Sᶜ)) p φ).symm.trans
          ((congrArg (relativeCochainToAbsolute ℚ
            (TopPair.ofSubset (X := X) (Prod.snd ⁻¹' Sᶜ)) (p+1)) hφ).trans (map_zero _))⟩
    HomologicalComplex.homologyMap (triadToUnionRelativeChainMap ℚ X (Prod.snd ⁻¹' Sᶜ)
        {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ) (p+q+1) ≫
        HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
          (properCycle_real_cap_upper_union_iso Y S T).hom) (p+q+1) ≫
        properCycle_real_upper_support_cap Y S T hS hT p q hp χ.1
          (properCycle_relative_cochain_subcomplex_zero X (Prod.snd ⁻¹' Sᶜ) p φ) χ.2 =
      ModuleCat.ofHom (triadCapHomologyMap ℚ X (Prod.snd ⁻¹' Sᶜ)
        {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ p (q+1) φ hφ) := by
  dsimp only
  letI := properCycle_real_cap_refinement_right_isIso Y S T hS hT (p+q)
  let X := TopCat.of (ℝ × Y)
  let A : Set X := Prod.snd ⁻¹' Sᶜ
  let B : Set X := {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ
  have hAo : IsOpen A := hS.isOpen_compl.preimage continuous_snd
  have hBo : IsOpen B := ((isClosed_eq continuous_fst continuous_const).inter
    (hT.preimage continuous_snd)).isOpen_compl
  letI := triadToUnionRelativeChainMap_quasiIso_of_isOpen X A B hAo hBo
  let J := HomologicalComplex.homologyMap (properCycle_real_cap_upper_triad_map Y S T) (p+q+1)
  let E := HomologicalComplex.homologyMap (triadToUnionRelativeChainMap ℚ X A B) (p+q+1) ≫
    HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
      (properCycle_real_cap_upper_union_iso Y S T).hom) (p+q+1)
  letI : IsIso E := by dsimp only [E]; infer_instance
  let r := HomologicalComplex.homologyMap (properCycle_real_cap_source_refinement Y S T).τ₃ (p+q+1)
  let Rs := properCycle_real_support_right_iso Y (S ∩ T) (hS.inter hT) (p+q+1)
  let Rt := properCycle_real_support_right_iso Y T hT (q+1)
  let χ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) p :=
    ⟨relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) A) p φ,
      (relativeCochainToAbsolute_coboundary ℚ (TopPair.ofSubset (X := X) A) p φ).symm.trans
        ((congrArg (relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) A) (p+1)) hφ).trans (map_zero _))⟩
  let hA := properCycle_relative_cochain_subcomplex_zero X A p φ
  let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
  let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
  let K := properCycle_subcomplex_cap_homology_map (subsetSingularSubcomplex X A)
    (P ⊔ Q) p (q+1) hp χ.1 hA χ.2
  let C := ModuleCat.ofHom (triadCapHomologyMap ℚ X A B p (q+1) φ hφ)
  have hs := congrArg (fun m => HomologicalComplex.homologyMap m (p+q+1))
    (properCycle_real_cap_upper_source_comparison Y S T)
  simp only [HomologicalComplex.homologyMap_comp] at hs
  rw [← properCycle_real_support_right_iso_homology Y (S ∩ T) (hS.inter hT) (p+q+1)] at hs
  change r ≫ Rs.hom = J ≫ E at hs
  letI : IsIso J := IsIso.of_isIso_fac_right hs.symm
  have ho := properCycle_real_upper_triad_cap_homology Y S T p (q+1) hp φ hφ
  rw [← properCycle_real_support_right_iso_homology Y T hT (q+1)] at ho
  change K ≫ Rt.hom = J ≫ C at ho
  change E ≫ (Rs.inv ≫ inv r ≫ K ≫ Rt.hom) = C
  apply (cancel_epi J).mp
  calc
    _ = (J ≫ E) ≫ (Rs.inv ≫ inv r ≫ K ≫ Rt.hom) := by simp only [Category.assoc]
    _ = (r ≫ Rs.hom) ≫ (Rs.inv ≫ inv r ≫ K ≫ Rt.hom) := by rw [← hs]
    _ = K ≫ Rt.hom := by simp only [Category.assoc, Iso.hom_inv_id_assoc, IsIso.hom_inv_id_assoc]
    _ = _ := ho

end HodgeLean.Foundations.QuotientDuality
