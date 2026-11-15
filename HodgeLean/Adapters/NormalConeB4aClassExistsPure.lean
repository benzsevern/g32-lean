import HodgeLean.Adapters.NormalConeB4aClassRegularExtension
import HodgeLean.Adapters.NormalConeB4aClassMultiplicityLocal
import HodgeLean.Adapters.NormalConeB4aClassOpenExtension

/-! # Cycle-class existence under a component codimension bound

Route: extend the regular normalized class, use local constancy of
multiplicity in every tested chart, and detect its normalization across the
higher-codimension boundary by relative restriction injectivity.
-/
noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Foundations.Analytic

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A cycle all of whose components have codimension at least `c` has a
supported class satisfying the full frozen normalization predicate. -/
theorem a3b4a_cycleClass_exists_of_codimension
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [Smooth q]
    [QuasiCompact q] [IsSeparated q] (γ : AlgebraicCycle Z ℚ) (c : ℕ)
    (hc : ∀ ξ ∈ γ.support, (c : ℕ∞) ≤ Order.coheight ξ) :
    ∃ β : RelativeCohomology ℚ
      (TopPair.ofSubset (X := a3b4_an q) (a3b4_cycleSupport q γ)ᶜ) (2 * c),
      a3b4_IsCycleClass q γ c β := by
  letI : LocallyOfFiniteType (Over.mk q).hom := inferInstanceAs (LocallyOfFiniteType q)
  letI : IsSeparated (Over.mk q).hom := ‹IsSeparated q›
  letI : QuasiCompact (Over.mk q).hom := ‹QuasiCompact q›
  letI : T2Space (ComplexPoint (Over.mk q)) := f4_t2Space (Over.mk q)
  letI : SecondCountableTopology (ComplexPoint (Over.mk q)) := f4_secondCountable (Over.mk q)
  letI : LocallyCompactSpace (ComplexPoint (Over.mk q)) :=
    an_locallyCompactSpace (f4_analytification (Over.mk q))
  letI (V : Opens (ComplexPoint (Over.mk q))) : ParacompactSpace V :=
    a3b4a_class_openParacompact q V
  let X := a3b4_an q
  let S : Closeds X := ⟨a3b4_cycleSupport q γ, a3b4a_classSupport_isClosed q γ⟩
  let B := a3b4a_classRegularBoundary q γ c
  let B' : Closeds X := B.preimage (ComplexPoint.continuous_underlying_to_zariski (Over.mk q))
  have hBS : B' ≤ S := fun _ hx => a3b4a_classRegularBoundary_le q γ c hx
  have hBc := a3b4a_classRegularBoundary_coheight q γ c hc
  have hlower (j : ℕ) (hj : j < 2 * c) : IsZero (supportRelativeCohomologySheaf X S j) :=
    a3b4a_classSheaf_purity_vanishing q (a3b4a_classAlgebraicSupport q γ) c
      (a3b4a_classAlgebraicSupport_coheight q γ c hc) j hj
  obtain ⟨β, hβ⟩ := a3b4a_classRegular_extension q γ c hc
  refine ⟨β, ?_⟩
  intro r e hS x hx hxS he
  obtain ⟨W, hWe, hxW, hmult⟩ := a3b4a_classMultiplicity_locally_constant q γ e he hS x hx hxS
  refine ⟨W, hWe, W.isOpen, hxW, ?_⟩
  letI : LocallyCompactSpace W := W.isOpen.isOpenEmbedding_subtypeVal.locallyCompactSpace
  letI (V : Opens W) : LocallyCompactSpace V := V.isOpen.isOpenEmbedding_subtypeVal.locallyCompactSpace
  letI (V : Opens W) : ParacompactSpace V := inferInstance
  let m := a3b4_multiplicity q γ x
  let δ := relativeCohomologyMap ℚ (2 * c) (a3b4_neighborhoodPairMap (W : Set X) S) β -
    m • chartNormalProjectionCoclass (Fin r → ℂ) c e S hS W hWe
  apply sub_eq_zero.mp
  change δ = 0
  apply a3b4a_classRelative_eq_zero_of_boundary_restriction X S B' hBS W (2 * c)
    (fun j hj => a3b4a_classRelative_purity_vanishing q B (c + 1) hBc W j (by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      omega)) δ
  let O : Opens X := W ⊓ B'.compl
  have hOW : O ≤ W := inf_le_left
  let α := relativeCohomologyMap ℚ (2 * c) (a3b4_neighborhoodPairMap (O : Set X) S) β -
    m • chartNormalProjectionCoclass (Fin r → ℂ) c e S hS O (fun _ h => hWe (hOW h))
  have hδα : relativeCohomologyMap ℚ (2 * c)
      (neighborhoodSupportInclusionPairMap hOW (S : Set X)) δ = α := by
    dsimp only [δ, α]
    rw [map_sub, map_smul, a3b4a_classLocal_restriction_comp, chartNormalProjectionCoclass_restrict]
  change relativeCohomologyMap ℚ (2 * c)
    (neighborhoodSupportInclusionPairMap hOW (S : Set X)) δ = 0
  rw [hδα]
  have hH (j : ℕ) (hj : j < 2 * c) : IsZero
      ((O.isOpenEmbedding.sheafPullback AddCommGrpCat).obj (supportRelativeCohomologySheaf X S j)) :=
    (O.isOpenEmbedding.sheafPullback AddCommGrpCat).map_isZero (hlower j hj)
  apply ccm5_relativeGerms_injective_of_lowerVanishing X S O (2 * c) hH
  funext y
  dsimp only
  have hzero : supportRelativeCohomologyGerm X S (2 * c) O y.1 y.2 0 = 0 := by
    simp only [supportRelativeCohomologyGerm, map_zero]
  rw [hzero]
  by_cases hyS : y.1 ∈ S
  · obtain ⟨Q, hQe, hyQ, hQ⟩ := hβ y.1 hyS y.2.2 r e he hS (hWe y.2.1)
    let T : Opens X := Q ⊓ O
    have hyT : y.1 ∈ T := ⟨hyQ, y.2⟩
    have hTO : T ≤ O := inf_le_right
    have hTQ : T ≤ Q := inf_le_left
    have hnorm := a3b4a_classLocal_normalization_mono e (S : Set X) hS hTQ hQe β
      (a3b4_multiplicity q γ y.1) hQ
    have hα : relativeCohomologyMap ℚ (2 * c)
        (neighborhoodSupportInclusionPairMap hTO (S : Set X)) α = 0 := by
      dsimp only [α]
      rw [map_sub, map_smul, a3b4a_classLocal_restriction_comp,
        chartNormalProjectionCoclass_restrict, hnorm, hmult y.1 y.2.1 hyS]
      exact sub_self _
    rw [← supportRelativeCohomologyGerm_restrict X S (2 * c) hTO y.1 hyT, hα]
    simp only [supportRelativeCohomologyGerm, map_zero]
  · exact supportRelativeCohomologyGerm_eq_zero_of_not_mem X S (2 * c)
      S.isClosed O y.1 y.2 hyS α

end HodgeLean.Adapters
