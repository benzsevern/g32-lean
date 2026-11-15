import HodgeLean.Foundations.QuotientDuality.ProperCycleRealSupportTransport

/-! # Naturality of the specified real support suspension comparisons
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original left half-ray comparison commutes with the actual sequence transport and literal normal-pair map.
Source: properCycle_subcomplex_quotient_morphism_projection; properCycle_real_support_left_projection; relativeChainProjection_naturality.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_support_left_transport
    {X Y : TopCat.{0}} (f : X ⟶ Y) (T : Set X) (U : Set Y) (h : Set.MapsTo f Tᶜ Uᶜ) :
    (properCycle_real_support_sequence_map f T U h).τ₁ ≫ (properCycle_real_support_left_iso Y U).hom =
      (properCycle_real_support_left_iso X T).hom ≫
        (relativeChainFunctor ℚ).map (properCycle_real_support_normal_pair_map f T U h) := by
  let AX := TopCat.of (ℝ × X)
  let AY := TopCat.of (ℝ × Y)
  let PX := subsetSingularSubcomplex AX {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
  let QX := subsetSingularSubcomplex AX {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
  let PY := subsetSingularSubcomplex AY {z | 0 ≤ z.1 ∧ z.2 ∈ U}ᶜ
  let QY := subsetSingularSubcomplex AY {z | z.1 ≤ 0 ∧ z.2 ∈ U}ᶜ
  let πX := cokernel.π (SSet.chainComplexMap (PX ⊓ QX).ι (ModuleCat.of ℚ ℚ))
  let πY := cokernel.π (SSet.chainComplexMap (PY ⊓ QY).ι (ModuleCat.of ℚ ℚ))
  let F := SSet.chainComplexMap (TopCat.toSSet.map (properCycle_real_support_product_map f))
    (ModuleCat.of ℚ ℚ)
  have ht : πX ≫ (properCycle_real_support_sequence_map f T U h).τ₁ = F ≫ πY := by
    dsimp only [πX, πY, properCycle_real_support_sequence_map, properCycle_subcomplex_mv_morphism,
      id_eq, ShortComplex.homMk]
    exact properCycle_subcomplex_quotient_morphism_projection _ _ _ _
  apply (cancel_epi πX).mp
  calc
    _ = (F ≫ πY) ≫ (properCycle_real_support_left_iso Y U).hom := by
      simpa only [Category.assoc] using congrArg (fun m => m ≫ (properCycle_real_support_left_iso Y U).hom) ht
    _ = F ≫ relativeChainProjection ℚ (TopPair.ofSubset (X := AY) (Prod.snd ⁻¹' Uᶜ)) := by
      rw [Category.assoc, properCycle_real_support_left_projection Y U]
    _ = relativeChainProjection ℚ (TopPair.ofSubset (X := AX) (Prod.snd ⁻¹' Tᶜ)) ≫
        (relativeChainFunctor ℚ).map (properCycle_real_support_normal_pair_map f T U h) :=
      (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ)
        (properCycle_real_support_normal_pair_map f T U h)).symm
    _ = _ := by
      have hx := congrArg (fun m => m ≫
        (relativeChainFunctor ℚ).map (properCycle_real_support_normal_pair_map f T U h))
        (properCycle_real_support_left_projection X T)
      simpa only [Category.assoc] using hx.symm

/-- The original right half-ray comparison commutes with the actual sequence transport and literal zero-slice pair map.
Source: properCycle_subcomplex_quotient_morphism_projection; properCycle_real_support_right_chain_projection; relativeChainProjection_naturality.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_support_right_transport
    {X Y : TopCat.{0}} (f : X ⟶ Y) (T : Set X) (U : Set Y) (h : Set.MapsTo f Tᶜ Uᶜ) :
    (properCycle_real_support_sequence_map f T U h).τ₃ ≫ properCycle_real_support_right_chain_map Y U =
      properCycle_real_support_right_chain_map X T ≫
        (relativeChainFunctor ℚ).map (properCycle_real_support_zero_pair_map f T U h) := by
  let AX := TopCat.of (ℝ × X)
  let AY := TopCat.of (ℝ × Y)
  let PX := subsetSingularSubcomplex AX {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
  let QX := subsetSingularSubcomplex AX {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
  let PY := subsetSingularSubcomplex AY {z | 0 ≤ z.1 ∧ z.2 ∈ U}ᶜ
  let QY := subsetSingularSubcomplex AY {z | z.1 ≤ 0 ∧ z.2 ∈ U}ᶜ
  let πX := cokernel.π (SSet.chainComplexMap (PX ⊔ QX).ι (ModuleCat.of ℚ ℚ))
  let πY := cokernel.π (SSet.chainComplexMap (PY ⊔ QY).ι (ModuleCat.of ℚ ℚ))
  let F := SSet.chainComplexMap (TopCat.toSSet.map (properCycle_real_support_product_map f))
    (ModuleCat.of ℚ ℚ)
  have ht : πX ≫ (properCycle_real_support_sequence_map f T U h).τ₃ = F ≫ πY := by
    dsimp only [πX, πY, properCycle_real_support_sequence_map, properCycle_subcomplex_mv_morphism,
      id_eq, ShortComplex.homMk]
    exact properCycle_subcomplex_quotient_morphism_projection _ _ _ _
  apply (cancel_epi πX).mp
  calc
    _ = (F ≫ πY) ≫ properCycle_real_support_right_chain_map Y U := by
      simpa only [Category.assoc] using congrArg (fun m => m ≫ properCycle_real_support_right_chain_map Y U) ht
    _ = F ≫ relativeChainProjection ℚ (TopPair.ofSubset (X := AY) {z | z.1 = 0 ∧ z.2 ∈ U}ᶜ) := by
      rw [Category.assoc, properCycle_real_support_right_chain_projection Y U]
    _ = relativeChainProjection ℚ (TopPair.ofSubset (X := AX) {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ) ≫
        (relativeChainFunctor ℚ).map (properCycle_real_support_zero_pair_map f T U h) :=
      (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ)
        (properCycle_real_support_zero_pair_map f T U h)).symm
    _ = _ := by
      have hx := congrArg (fun m => m ≫
        (relativeChainFunctor ℚ).map (properCycle_real_support_zero_pair_map f T U h))
        (properCycle_real_support_right_chain_projection X T)
      simpa only [Category.assoc] using hx.symm

/-- The literal normal-pair transport commutes with the actual base projection as an equality of original relative pair maps.
Source: Hatcher, Algebraic Topology, section 2.1, functorial relative pairs; product projection.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_support_projection_pair_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) (T : Set X) (U : Set Y) (h : Set.MapsTo f Tᶜ Uᶜ) :
    properCycle_real_support_normal_pair_map f T U h ≫ properCycle_product_support_projection ℝ Y U =
      properCycle_product_support_projection ℝ X T ≫ TopPair.ofSubsetHom f h := by
  ext z : 2 <;> rfl

/-- The original base-projection homology isomorphisms are natural for the literal normal-pair transport.
Source: properCycle_real_support_projection_pair_naturality; original relative homology functoriality.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_support_projection_homology_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) (T : Set X) (U : Set Y) (h : Set.MapsTo f Tᶜ Uᶜ) (n : ℕ) :
    HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
        (properCycle_real_support_normal_pair_map f T U h)) n ≫
        (properCycle_product_support_homology_iso ℝ Y U n).hom =
      (properCycle_product_support_homology_iso ℝ X T n).hom ≫
        HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f h)) n := by
  have hc := (relativeChainFunctor ℚ).congr_map
    (properCycle_real_support_projection_pair_naturality f T U h)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hc
  have hh := congrArg (fun m => HomologicalComplex.homologyMap m n) hc
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hh
  exact hh

end HodgeLean.Foundations.QuotientDuality
