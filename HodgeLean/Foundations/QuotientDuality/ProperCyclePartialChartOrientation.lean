import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalTriadNaturality

/-! # Actual restricted product-chart orientation maps -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal product-chart point map retains the original compressed complex orientation on every smaller open neighborhood.
Source: Hatcher, Algebraic Topology, section 3.3, naturality of chart orientations.
HC no distance; AV milestone no distance. -/
lemma properCycle_restricted_product_chart_orientation
    {M : TopCat.{0}} [T1Space M] (r d : ℕ)
    (e : OpenPartialHomeomorph M ((Fin r → ℂ) × (Fin d → ℂ)))
    (x : M) (hx : x ∈ e.source) (hex : e x = (0, 0))
    (W : Set M) (hW : W ⊆ e.source) (hWo : IsOpen W) (hxW : x ∈ W) :
    let L : ((Fin r → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (r + d) → ℂ) :=
      ContinuousLinearEquiv.ofFinrankEq
        (by simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin])
    let φ := e.trans L.toHomeomorph.toOpenPartialHomeomorph
    let fP : neighborhoodPointComplementPair W x ⟶ pointComplementPair ((0, 0) : (Fin r → ℂ) × (Fin d → ℂ)) :=
      TopPair.ofSubsetHom
        (TopCat.ofHom ⟨fun w => e w.val, (e.continuousOn.mono hW).domRestrict⟩)
        (fun w hw he => hw (e.injOn (hW w.property) hx (he.trans hex.symm)))
    relativeHomologyMap ℚ (2 * (r + d)) fP
      ((neighborhoodPointComplementRelativeHomologyIso W x hWo hxW (2 * (r + d))).inv.hom
        (localClassOfChart (r + d) φ x ⟨hx, Set.mem_univ _⟩)) =
      properCycle_complex_product_standard_orientation r d := by
  dsimp only
  let L : ((Fin r → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (r + d) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq
      (by simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin])
  let φ := e.trans L.toHomeomorph.toOpenPartialHomeomorph
  have hxφ : x ∈ φ.source := ⟨hx, Set.mem_univ _⟩
  have hWφ : W ⊆ φ.source := fun w hw => ⟨hW hw, Set.mem_univ _⟩
  have hφ : φ x = 0 := by change L (e x) = 0; rw [hex]; exact map_zero L
  let fP : neighborhoodPointComplementPair W x ⟶ pointComplementPair ((0, 0) : (Fin r → ℂ) × (Fin d → ℂ)) :=
    TopPair.ofSubsetHom
      (TopCat.ofHom ⟨fun w => e w.val, (e.continuousOn.mono hW).domRestrict⟩)
      (fun w hw he => hw (e.injOn (hW w.property) hx (he.trans hex.symm)))
  let i : pointComplementPair ((0, 0) : (Fin r → ℂ) × (Fin d → ℂ)) ≅ puncturedPair ℂ (r + d) :=
    TopPair.isoOfSubset L.toHomeomorph (by
      intro z
      change L z ≠ 0 ↔ z ≠ 0
      exact not_congr (L.injective.eq_iff' (map_zero L)))
  let j : puncturedPair ℂ (r + d) ≅ pointComplementPair (φ x) :=
    TopPair.isoOfSubset (Homeomorph.refl _) (by rw [hφ]; intro z; rfl)
  have hf : fP ≫ i.hom ≫ j.hom =
      properCycle_restricted_chart_point_pair_map (r + d) φ x hxφ W hWφ := by
    ext z : 2 <;> rfl
  have hi := ConcreteCategory.bijective_of_isIso
    (HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map (i.hom ≫ j.hom)) (2 * (r + d)))
  apply hi.injective
  change relativeHomologyMap ℚ (2 * (r + d)) (i.hom ≫ j.hom) _ =
    relativeHomologyMap ℚ (2 * (r + d)) (i.hom ≫ j.hom) _
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, hf]
  rw [properCycle_restricted_chart_local_class_normalization]
  have hor : relativeHomologyMap ℚ (2 * (r + d)) i.inv
      (standardComplexLocalClass ℚ (r + d)) = properCycle_complex_product_standard_orientation r d := by
    rw [properCycle_complex_product_orientation_chart_class]
    exact properCycle_homeomorph_zero_chart_local_class (r + d)
      (M := TopCat.of ((Fin r → ℂ) × (Fin d → ℂ))) L.toHomeomorph (0, 0) (map_zero L)
  rw [← hor, ← LinearMap.comp_apply, ← relativeHomologyMap_comp]
  have hid : i.inv ≫ (i.hom ≫ j.hom) = j.hom := by simp only [Iso.inv_hom_id_assoc]
  rw [hid]
  have hj : translationPointComplementPairMap (Fin (r + d) → ℂ) (φ x) = j.hom := by
    ext z : 2
    · apply Subtype.ext; change z.val + φ x = z.val; rw [hφ, add_zero]
    · change (show Fin (r + d) → ℂ from z) + φ x = z; rw [hφ, add_zero]
  rw [hj]

end HodgeLean.Foundations.QuotientDuality
