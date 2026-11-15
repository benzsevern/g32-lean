import HodgeLean.Foundations.QuotientDuality.ProperCycleUnionRelativeCapNaturality
import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexOriginalCap
import HodgeLean.Foundations.QuotientDuality.ProperCycleTriadUnionQuotientComparison

/-! # The actual union-relative cap through original subcomplex quotients
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual union-relative cap is the original subcomplex cap through the specified open-triad source excision and target relative comparison.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3; properCycle_subcomplex_original_triad_cap_homology; unionRelativeTriadCapCohomologyLinear_on_comparison.
HC no distance; AV milestone no distance. -/
theorem properCycle_union_relative_subcomplex_cap_comparison
    (X : TopCat.{0}) (A B : Set X) (hAo : IsOpen A) (hBo : IsOpen B)
    (p q : ℕ) (hp : Even p)
    (φ : LinearMap.ker ((((relativeChainFunctor ℚ).obj
      (TopPair.ofSubset (X := X) A)).sc p).linearDual.g.hom)) :
    let C := ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) A)).sc p
    let ψ := relativeCohomologyCycleToCocycle ℚ (TopPair.ofSubset (X := X) A) p φ
    let χ := relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) A) p ψ.1
    let hχ : AlgebraicTopology.Simplicial.coboundary ℚ p χ = 0 :=
      (relativeCochainToAbsolute_coboundary ℚ (TopPair.ofSubset (X := X) A) p ψ.1).symm.trans
        ((congrArg (relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) A) (p+1)) ψ.2).trans
          (map_zero _))
    (properCycle_subset_union_quotient_homology_iso X A B hAo hBo (p+q)).inv ≫
        properCycle_subcomplex_cap_homology_map (subsetSingularSubcomplex X A)
          (subsetSingularSubcomplex X B) p q hp χ
          (properCycle_relative_cochain_subcomplex_zero X A p ψ.1) hχ ≫
        HomologicalComplex.homologyMap (properCycle_subset_subcomplex_relative_iso X B).hom q =
      ModuleCat.ofHom (unionRelativeTriadCapCohomologyLinear ℚ X A B p q
        (triadToUnionRelativeChainMap_quasiIso_of_isOpen X A B hAo hBo)
        (relativeCochainCohomologyEquiv ℚ (TopPair.ofSubset (X := X) A) p
          (C.linearDual.moduleCatHomologyClass φ))) := by
  dsimp only
  let C := ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) A)).sc p
  let a := relativeCochainCohomologyEquiv ℚ (TopPair.ofSubset (X := X) A) p
    (C.linearDual.moduleCatHomologyClass φ)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) (p+q)
  let I := H.mapIso (properCycle_subset_union_subcomplex_triad_iso X A B)
  let E := properCycle_subset_union_quotient_homology_iso X A B hAo hBo (p+q)
  let U := HomologicalComplex.homologyMap (triadToUnionRelativeChainMap ℚ X A B) (p+q)
  have hu : U ≫ ModuleCat.ofHom (unionRelativeTriadCapCohomologyLinear ℚ X A B p q
      (triadToUnionRelativeChainMap_quasiIso_of_isOpen X A B hAo hBo) a) =
      ModuleCat.ofHom (triadCapCohomologyLinear ℚ X A B p q a) := by
    apply ModuleCat.hom_ext
    ext z
    exact unionRelativeTriadCapCohomologyLinear_on_comparison ℚ X A B p q _ a z
  have ho := properCycle_subcomplex_original_triad_cap_homology X A B p q hp
    (relativeCohomologyCycleToCocycle ℚ (TopPair.ofSubset (X := X) A) p φ).1
    (relativeCohomologyCycleToCocycle ℚ (TopPair.ofSubset (X := X) A) p φ).2
  have ha : ModuleCat.ofHom (triadCapCohomologyLinear ℚ X A B p q a) =
      ModuleCat.ofHom (triadRelativeCohomologyCycleCapLinear ℚ X A B p q φ) := by
    erw [triadCapCohomologyLinear_on_cycle]
  change E.inv ≫ _ ≫ _ = _
  apply (cancel_epi E.hom).mp
  apply (cancel_epi I.inv).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change I.inv ≫ _ ≫ _ = I.inv ≫ (I.hom ≫ U) ≫ _
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  exact ho.trans (ha.symm.trans hu.symm)

end HodgeLean.Foundations.QuotientDuality
