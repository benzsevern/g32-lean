import HodgeLean.Foundations.QuotientDuality.ProperCycleOriginalCapSupportRecurrence

/-! # Original cohomology cap recurrence through actual support suspension
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original cohomology caps retain the specified signed support recurrence under literal normal-class pullback.
Source: properCycle_original_triad_support_cap_recurrence; properCycle_relative_pullback_cochain_comparison.
HC no distance; AV milestone no distance. -/
theorem properCycle_cohomology_triad_support_cap_recurrence
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T)
    (p q : ℕ) (hp : Even p)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := Y) Sᶜ) p) :
    letI := triadToUnionRelativeChainMap_quasiIso_of_isOpen Y Sᶜ Tᶜ hS.isOpen_compl hT.isOpen_compl
    let EB := asIso (HomologicalComplex.homologyMap
      (triadToUnionRelativeChainMap ℚ Y Sᶜ Tᶜ) (p+q)) ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) (p+q)).mapIso
        ((relativeChainFunctor ℚ).mapIso (properCycle_support_complement_union_iso Y S T))
    let X := TopCat.of (ℝ × Y)
    let b := relativeCohomologyMap ℚ p (properCycle_product_support_projection ℝ Y S) a
    ModuleCat.ofHom (triadCapCohomologyLinear ℚ X (Prod.snd ⁻¹' Sᶜ)
        {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ p (q+1) b) ≫
        (properCycle_real_support_suspension_iso Y T hT q).hom =
      HomologicalComplex.homologyMap (triadToUnionRelativeChainMap ℚ X (Prod.snd ⁻¹' Sᶜ)
        {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ) (p+q+1) ≫
        HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
          (properCycle_real_cap_upper_union_iso Y S T).hom) (p+q+1) ≫
        (properCycle_real_support_suspension_iso Y (S ∩ T) (hS.inter hT) (p+q)).hom ≫
        EB.inv ≫ ModuleCat.ofHom (triadCapCohomologyLinear ℚ Y Sᶜ Tᶜ p q a) := by
  let SQ := ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := Y) Sᶜ)).sc p
  let P := TopPair.ofSubset (X := TopCat.of (ℝ × Y)) (Prod.snd ⁻¹' Sᶜ)
  let SP := ((relativeChainFunctor ℚ).obj P).sc p
  obtain ⟨u, rfl⟩ := (relativeCochainCohomologyEquiv ℚ (TopPair.ofSubset (X := Y) Sᶜ) p).surjective a
  obtain ⟨φ, rfl⟩ := SQ.linearDual.moduleCatHomologyClass_surjective u
  let f := properCycle_product_support_projection ℝ Y S
  let F := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) p).map
    ((relativeChainFunctor ℚ).map f)
  let τ := ShortComplex.moduleCatCycleMap (ShortComplex.linearDualMap F) φ
  have ha : relativeCohomologyMap ℚ p f
      (relativeCochainCohomologyEquiv ℚ (TopPair.ofSubset (X := Y) Sᶜ) p
        (SQ.linearDual.moduleCatHomologyClass φ)) =
      relativeCochainCohomologyEquiv ℚ P p (SP.linearDual.moduleCatHomologyClass τ) := by
    have h := congrArg (relativeCochainCohomologyEquiv ℚ P p)
      (properCycle_relative_pullback_cochain_comparison f p (SQ.linearDual.moduleCatHomologyClass φ))
    rw [LinearEquiv.apply_symm_apply, ShortComplex.moduleCatHomologyClass_naturality] at h
    exact h
  dsimp only
  rw [ha]
  erw [triadCapCohomologyLinear_on_cycle, triadCapCohomologyLinear_on_cycle]
  exact properCycle_original_triad_support_cap_recurrence Y S T hS hT p q hp
    (relativeCohomologyCycleToCocycle ℚ (TopPair.ofSubset (X := Y) Sᶜ) p φ)

end HodgeLean.Foundations.QuotientDuality
