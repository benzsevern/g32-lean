import HodgeLean.Foundations.QuotientDuality.ProperCycleTriadMapExcision

/-! # Actual relative cap naturality through original open-triad excision
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The cap on the actual union-relative homology groups is natural under the literal maps of both open subspaces, using the original excision maps.
Source: Hatcher, Algebraic Topology, section 3.3; properCycle_triad_cap_naturality; properCycle_triad_map_union_comparison.
HC no distance; AV milestone no distance. -/
theorem properCycle_union_relative_cap_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set X) (C D : Set Y)
    (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D)
    (hAo : IsOpen A) (hBo : IsOpen B) (hCo : IsOpen C) (hDo : IsOpen D)
    (p q : ℕ) (a : RelativeCohomology ℚ (TopPair.ofSubset (X := Y) C) p)
    (z : RelativeHomology ℚ (TopPair.ofSubset (X := X) (A ∪ B)) (p+q)) :
    let fU := TopPair.ofSubsetHom f (show Set.MapsTo f (A ∪ B) (C ∪ D) from
      fun _ h => h.elim (fun h => Or.inl (hA h)) (fun h => Or.inr (hB h)))
    relativeHomologyMap ℚ q (TopPair.ofSubsetHom f hB)
      (unionRelativeTriadCapCohomologyLinear ℚ X A B p q
        (triadToUnionRelativeChainMap_quasiIso_of_isOpen X A B hAo hBo)
        (relativeCohomologyMap ℚ p (TopPair.ofSubsetHom f hA) a) z) =
      unionRelativeTriadCapCohomologyLinear ℚ Y C D p q
        (triadToUnionRelativeChainMap_quasiIso_of_isOpen Y C D hCo hDo) a
        (relativeHomologyMap ℚ (p+q) fU z) := by
  dsimp only
  let fU := TopPair.ofSubsetHom f (show Set.MapsTo f (A ∪ B) (C ∪ D) from
    fun _ h => h.elim (fun h => Or.inl (hA h)) (fun h => Or.inr (hB h)))
  let e := triadUnionExcisionHomologyEquiv ℚ X A B (p+q)
    (triadToUnionRelativeChainMap_quasiIso_of_isOpen X A B hAo hBo)
  obtain ⟨w, hw⟩ := e.surjective z
  change triadToUnionRelativeHomologyMap ℚ X A B (p+q) w = z at hw
  rw [← hw, unionRelativeTriadCapCohomologyLinear_on_comparison]
  have hc := congrArg (fun m => HomologicalComplex.homologyMap m (p+q))
    (properCycle_triad_map_union_comparison f A B C D hA hB)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hc
  have hv := ConcreteCategory.congr_hom hc w
  change triadToUnionRelativeHomologyMap ℚ Y C D (p+q)
      ((HomologicalComplex.homologyMap
        (properCycle_triad_relative_chain_map f A B C D hA hB) (p+q)).hom w) =
    relativeHomologyMap ℚ (p+q) fU (triadToUnionRelativeHomologyMap ℚ X A B (p+q) w) at hv
  rw [← hv, unionRelativeTriadCapCohomologyLinear_on_comparison]
  exact properCycle_triad_cap_naturality f A B C D hA hB p q a w

end HodgeLean.Foundations.QuotientDuality
