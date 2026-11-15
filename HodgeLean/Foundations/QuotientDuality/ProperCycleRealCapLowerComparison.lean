import HodgeLean.Foundations.QuotientDuality.ProperCycleRealCapSupportCoordinates
import HodgeLean.Foundations.QuotientDuality.ProperCycleUnionRelativeSubcomplexCap
import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexCapExcision

/-! # The actual lower normal cap in original triad coordinates
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original left cap source is the original triad for the two inverse-image support complements, using the actual half-ray intersection equality.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3; properCycle_real_half_ray_support_intersection; properCycle_subset_union_subcomplex_triad_iso.
HC no distance; AV milestone no distance. -/
def properCycle_real_cap_lower_triad_iso (Y : TopCat.{0}) (S T : Set Y) :
    let X := TopCat.of (ℝ × Y)
    let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
    let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
    let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
    (properCycle_fixed_subcomplex_sequence A P Q).X₁ ≅
      triadRelativeChainComplex ℚ X (Prod.snd ⁻¹' Sᶜ) (Prod.snd ⁻¹' Tᶜ) := by
  dsimp only
  let X := TopCat.of (ℝ × Y)
  let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
  have hI : subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ ⊓
      subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ =
      subsetSingularSubcomplex X (Prod.snd ⁻¹' Tᶜ) := by
    rw [← subsetSingularSubcomplex_inter, properCycle_real_half_ray_support_intersection]
  exact properCycle_subcomplex_quotient_iso_of_eq (congrArg (A ⊔ ·) hI) ≪≫
    properCycle_subset_union_subcomplex_triad_iso X (Prod.snd ⁻¹' Sᶜ) (Prod.snd ⁻¹' Tᶜ)

/-- The original lower cap triad comparison retains the literal ambient sum-relative projection.
Source: properCycle_subcomplex_quotient_projection; properCycle_subset_union_subcomplex_triad_projection.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_cap_lower_triad_projection (Y : TopCat.{0}) (S T : Set Y) :
    let X := TopCat.of (ℝ × Y)
    let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
    let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
    let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
    cokernel.π (SSet.chainComplexMap (A ⊔ (P ⊓ Q)).ι (ModuleCat.of ℚ ℚ)) ≫
        (properCycle_real_cap_lower_triad_iso Y S T).hom =
      triadRelativeChainProjection ℚ X (Prod.snd ⁻¹' Sᶜ) (Prod.snd ⁻¹' Tᶜ) := by
  dsimp only
  unfold properCycle_real_cap_lower_triad_iso
  dsimp only [id_eq]
  rw [Iso.trans_hom, ← Category.assoc]
  dsimp only [properCycle_subcomplex_quotient_iso_of_eq]
  rw [properCycle_subcomplex_quotient_projection, properCycle_subset_union_subcomplex_triad_projection]

/-- The actual lower quotient cap is the original inverse-image triad cap through the specified source and target comparisons.
Source: properCycle_subcomplex_cap_homology_inclusion; properCycle_subcomplex_original_triad_cap_homology.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_lower_triad_cap_homology
    (Y : TopCat.{0}) (S T : Set Y) (p q : ℕ) (hp : Even p)
    (φ : RelativeCochain ℚ (TopPair.ofSubset (X := TopCat.of (ℝ × Y))
      (Prod.snd ⁻¹' Sᶜ)) p)
    (hφ : relativeCoboundary ℚ (TopPair.ofSubset (X := TopCat.of (ℝ × Y))
      (Prod.snd ⁻¹' Sᶜ)) p φ = 0) :
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
    HomologicalComplex.homologyMap (properCycle_real_cap_lower_triad_iso Y S T).inv (p+q) ≫
        properCycle_subcomplex_cap_homology_map A (P ⊓ Q) p q hp ψ.1
          (properCycle_relative_cochain_subcomplex_zero X (Prod.snd ⁻¹' Sᶜ) p φ) ψ.2 ≫
        HomologicalComplex.homologyMap (properCycle_real_support_left_iso Y T).hom q =
      ModuleCat.ofHom (triadCapHomologyMap ℚ X (Prod.snd ⁻¹' Sᶜ)
        (Prod.snd ⁻¹' Tᶜ) p q φ hφ) := by
  dsimp only
  let X := TopCat.of (ℝ × Y)
  let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
  let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
  let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
  let U := subsetSingularSubcomplex X (Prod.snd ⁻¹' Tᶜ)
  have hI : P ⊓ Q = U := by
    rw [← subsetSingularSubcomplex_inter, properCycle_real_half_ray_support_intersection]
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ)
  let Es := (H (p+q)).mapIso
    (properCycle_subcomplex_quotient_iso_of_eq (congrArg (A ⊔ ·) hI))
  let Et := (H q).mapIso (properCycle_subcomplex_quotient_iso_of_eq hI)
  let I := (H (p+q)).mapIso
    (properCycle_subset_union_subcomplex_triad_iso X (Prod.snd ⁻¹' Sᶜ) (Prod.snd ⁻¹' Tᶜ))
  let V := HomologicalComplex.homologyMap
    (properCycle_subset_subcomplex_relative_iso X (Prod.snd ⁻¹' Tᶜ)).hom q
  let χ := relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) (Prod.snd ⁻¹' Sᶜ)) p φ
  have hA : AlgebraicTopology.Simplicial.cochainMap ℚ A.ι p χ = 0 :=
    properCycle_relative_cochain_subcomplex_zero X (Prod.snd ⁻¹' Sᶜ) p φ
  have hχ : AlgebraicTopology.Simplicial.coboundary ℚ p χ = 0 :=
    (relativeCochainToAbsolute_coboundary ℚ
      (TopPair.ofSubset (X := X) (Prod.snd ⁻¹' Sᶜ)) p φ).symm.trans
      ((congrArg (relativeCochainToAbsolute ℚ
        (TopPair.ofSubset (X := X) (Prod.snd ⁻¹' Sᶜ)) (p+1)) hφ).trans (map_zero _))
  let Kold := properCycle_subcomplex_cap_homology_map A (P ⊓ Q) p q hp χ hA hχ
  let Knew := properCycle_subcomplex_cap_homology_map A U p q hp χ hA hχ
  have hi := properCycle_subcomplex_cap_homology_inclusion A (P ⊓ Q) U hI.le p q hp χ hA hχ
  change Kold ≫ Et.hom = Es.hom ≫ Knew at hi
  have ho := properCycle_subcomplex_original_triad_cap_homology X
    (Prod.snd ⁻¹' Sᶜ) (Prod.snd ⁻¹' Tᶜ) p q hp φ hφ
  have hJ : HomologicalComplex.homologyMap
      (properCycle_real_cap_lower_triad_iso Y S T).inv (p+q) = I.inv ≫ Es.inv := by
    unfold properCycle_real_cap_lower_triad_iso
    dsimp only [id_eq]
    rw [Iso.trans_inv, HomologicalComplex.homologyMap_comp]
    rfl
  have hL : HomologicalComplex.homologyMap
      (properCycle_real_support_left_iso Y T).hom q = Et.hom ≫ V := by
    unfold properCycle_real_support_left_iso
    dsimp only [id_eq]
    rw [Iso.trans_hom, HomologicalComplex.homologyMap_comp]
    rfl
  rw [hJ, hL]
  change (I.inv ≫ Es.inv) ≫ Kold ≫ (Et.hom ≫ V) = _
  calc
    _ = I.inv ≫ Es.inv ≫ (Kold ≫ Et.hom) ≫ V := by simp only [Category.assoc]
    _ = I.inv ≫ Es.inv ≫ (Es.hom ≫ Knew) ≫ V := by rw [hi]
    _ = I.inv ≫ Knew ≫ V := by simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = _ := ho

/-- The actual left source refinement followed by its specified relative comparison retains the literal ambient projection to the intersected-support complement.
Source: properCycle_subcomplex_quotient_projection; properCycle_real_support_left_projection.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_cap_source_refinement_left_projection
    (Y : TopCat.{0}) (S T : Set Y) :
    let X := TopCat.of (ℝ × Y)
    let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
    let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
    let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
    cokernel.π (SSet.chainComplexMap (A ⊔ (P ⊓ Q)).ι (ModuleCat.of ℚ ℚ)) ≫
        (properCycle_real_cap_source_refinement Y S T).τ₁ ≫
        (properCycle_real_support_left_iso Y (S ∩ T)).hom =
      relativeChainProjection ℚ (TopPair.ofSubset (X := X) (Prod.snd ⁻¹' (S ∩ T)ᶜ)) := by
  dsimp only
  let X := TopCat.of (ℝ × Y)
  let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
  let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
  let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
  let P' := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ S ∩ T}ᶜ
  let Q' := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ S ∩ T}ᶜ
  have hle : A ⊔ (P ⊓ Q) ≤ P' ⊓ Q' := by
    apply sup_le
    · exact le_inf
        (properCycle_subset_subcomplex_mono X
          (show Prod.snd ⁻¹' Sᶜ ⊆ {z : X | 0 ≤ z.1 ∧ z.2 ∈ S ∩ T}ᶜ from
            fun _ hz hp => hz hp.2.1))
        (properCycle_subset_subcomplex_mono X
          (show Prod.snd ⁻¹' Sᶜ ⊆ {z : X | z.1 ≤ 0 ∧ z.2 ∈ S ∩ T}ᶜ from
            fun _ hz hp => hz hp.2.1))
    · exact inf_le_inf
        (properCycle_subset_subcomplex_mono X
          (show {z : X | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ ⊆
            {z | 0 ≤ z.1 ∧ z.2 ∈ S ∩ T}ᶜ from fun _ hz hp => hz ⟨hp.1, hp.2.2⟩))
        (properCycle_subset_subcomplex_mono X
          (show {z : X | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ ⊆
            {z | z.1 ≤ 0 ∧ z.2 ∈ S ∩ T}ᶜ from fun _ hz hp => hz ⟨hp.1, hp.2.2⟩))
  have ht : (properCycle_real_cap_source_refinement Y S T).τ₁ =
      properCycle_subcomplex_quotient_map hle := by
    dsimp only [properCycle_real_cap_source_refinement, ShortComplex.comp_τ₁,
      properCycle_fixed_subcomplex_sequence_iso, ShortComplex.isoMk,
      properCycle_subcomplex_mv_refinement, properCycle_subcomplex_quotient_iso_of_eq,
      id_eq, ShortComplex.homMk, ShortComplex.Hom.comp]
    erw [properCycle_subcomplex_quotient_map_comp]
  rw [ht, ← Category.assoc, properCycle_subcomplex_quotient_projection]
  exact properCycle_real_support_left_projection Y (S ∩ T)

/-- Literal base projection sends the union of the two inverse-image support complements to the complement of the intersected base support.
Source: Hatcher, Algebraic Topology, section 2.1, maps of relative pairs.
HC no distance; AV milestone no distance. -/
def properCycle_real_cap_lower_base_pair (Y : TopCat.{0}) (S T : Set Y) :
    TopPair.ofSubset (X := TopCat.of (ℝ × Y))
      ((Prod.snd ⁻¹' Sᶜ) ∪ (Prod.snd ⁻¹' Tᶜ)) ⟶
    TopPair.ofSubset (X := Y) (S ∩ T)ᶜ :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩)
    (fun _ hz hst => hz.elim (fun hs => hs hst.1) (fun ht => ht hst.2))

/-- Actual left refinement, relative comparison and base projection agree with the original lower triad-to-union map followed by the literal base pair map.
Source: properCycle_real_cap_source_refinement_left_projection; properCycle_real_cap_lower_triad_projection; relativeChainProjection_naturality.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_cap_lower_source_base_comparison (Y : TopCat.{0}) (S T : Set Y) :
    (properCycle_real_cap_source_refinement Y S T).τ₁ ≫
        (properCycle_real_support_left_iso Y (S ∩ T)).hom ≫
        (relativeChainFunctor ℚ).map (properCycle_product_support_projection ℝ Y (S ∩ T)) =
      (properCycle_real_cap_lower_triad_iso Y S T).hom ≫
        triadToUnionRelativeChainMap ℚ (TopCat.of (ℝ × Y)) (Prod.snd ⁻¹' Sᶜ) (Prod.snd ⁻¹' Tᶜ) ≫
        (relativeChainFunctor ℚ).map (properCycle_real_cap_lower_base_pair Y S T) := by
  let X := TopCat.of (ℝ × Y)
  let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
  let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
  let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
  let π := cokernel.π (SSet.chainComplexMap (A ⊔ (P ⊓ Q)).ι (ModuleCat.of ℚ ℚ))
  let fI := properCycle_product_support_projection ℝ Y (S ∩ T)
  let fU := properCycle_real_cap_lower_base_pair Y S T
  apply (cancel_epi π).mp
  calc
    _ = relativeChainProjection ℚ
        (TopPair.ofSubset (X := X) (Prod.snd ⁻¹' (S ∩ T)ᶜ)) ≫
          (relativeChainFunctor ℚ).map fI := by
      simpa only [Category.assoc] using congrArg
        (fun m => m ≫ (relativeChainFunctor ℚ).map fI)
        (properCycle_real_cap_source_refinement_left_projection Y S T)
    _ = (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map
          (TopPair.Hom.fst fI)) ≫ relativeChainProjection ℚ (TopPair.ofSubset (X := Y) (S ∩ T)ᶜ) :=
      TopPair.Homotopy.relativeChainProjection_naturality fI
    _ = relativeChainProjection ℚ (TopPair.ofSubset (X := X)
        ((Prod.snd ⁻¹' Sᶜ) ∪ (Prod.snd ⁻¹' Tᶜ))) ≫
          (relativeChainFunctor ℚ).map fU :=
      (TopPair.Homotopy.relativeChainProjection_naturality fU).symm
    _ = _ := by
      have h := congrArg (fun m => m ≫
        triadToUnionRelativeChainMap ℚ X (Prod.snd ⁻¹' Sᶜ) (Prod.snd ⁻¹' Tᶜ) ≫
        (relativeChainFunctor ℚ).map fU) (properCycle_real_cap_lower_triad_projection Y S T)
      simp only [← Category.assoc] at h
      rw [triadRelativeChainProjection_triadToUnionRelativeChainMap] at h
      simpa only [Category.assoc] using h.symm

/-- The union of the support complements is the complement of their intersection, through the literal identity point map.
Source: Hatcher, Algebraic Topology, section 2.1, relative pairs; De Morgan's law.
HC no distance; AV milestone no distance. -/
def properCycle_support_complement_union_iso (Y : TopCat.{0}) (S T : Set Y) :
    TopPair.ofSubset (X := Y) (Sᶜ ∪ Tᶜ) ≅ TopPair.ofSubset (X := Y) (S ∩ T)ᶜ :=
  TopPair.isoOfSubset (Homeomorph.refl _) (by
    intro y
    change ¬ (y ∈ S ∧ y ∈ T) ↔ (y ∉ S ∨ y ∉ T)
    exact not_and_or)

/-- The actual refined lower source projection factors through the original triad projection to the base and its literal complement-union identification.
Source: properCycle_real_cap_lower_source_base_comparison; properCycle_triad_map_union_comparison.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_cap_lower_source_base_triad (Y : TopCat.{0}) (S T : Set Y) :
    let X := TopCat.of (ℝ × Y)
    let f : X ⟶ Y := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩
    (properCycle_real_cap_source_refinement Y S T).τ₁ ≫
        (properCycle_real_support_left_iso Y (S ∩ T)).hom ≫
        (relativeChainFunctor ℚ).map (properCycle_product_support_projection ℝ Y (S ∩ T)) =
      (properCycle_real_cap_lower_triad_iso Y S T).hom ≫
        properCycle_triad_relative_chain_map f (Prod.snd ⁻¹' Sᶜ) (Prod.snd ⁻¹' Tᶜ)
          Sᶜ Tᶜ (fun _ h => h) (fun _ h => h) ≫
        triadToUnionRelativeChainMap ℚ Y Sᶜ Tᶜ ≫
        (relativeChainFunctor ℚ).map (properCycle_support_complement_union_iso Y S T).hom := by
  dsimp only
  let X := TopCat.of (ℝ × Y)
  let f : X ⟶ Y := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩
  let fU := TopPair.ofSubsetHom f
    (show Set.MapsTo f ((Prod.snd ⁻¹' Sᶜ) ∪ (Prod.snd ⁻¹' Tᶜ)) (Sᶜ ∪ Tᶜ) from
      fun _ h => h.elim Or.inl Or.inr)
  have he : fU ≫ (properCycle_support_complement_union_iso Y S T).hom =
      properCycle_real_cap_lower_base_pair Y S T := by
    ext z : 2 <;> rfl
  dsimp only [fU] at he
  have h := properCycle_triad_map_union_comparison f (Prod.snd ⁻¹' Sᶜ) (Prod.snd ⁻¹' Tᶜ)
    Sᶜ Tᶜ (fun _ h => h) (fun _ h => h)
  have h2 := congrArg (fun m => m ≫
    (relativeChainFunctor ℚ).map (properCycle_support_complement_union_iso Y S T).hom) h
  rw [properCycle_real_cap_lower_source_base_comparison]
  simpa only [Category.assoc, ← CategoryTheory.Functor.map_comp, he] using
    congrArg (fun m => (properCycle_real_cap_lower_triad_iso Y S T).hom ≫ m) h2.symm

end HodgeLean.Foundations.QuotientDuality
