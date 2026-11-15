import HodgeLean.Foundations.QuotientDuality.OrientationInvariantHomology

/-! Maps from fixed chain complexes and their homology comparisons. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace HodgeLean.Foundations.QuotientDuality

variable (G : Type) [Group G]

abbrev invariantChainComplex (K : ChainComplex (ModuleCat ℚ) ℕ) (ρ : G →* End K) :=
  ((Rep.invariantsFunctor ℚ G).mapHomologicalComplex (.down ℕ)).obj
    (equivariantChainComplex G K ρ)

abbrev invariantChainInclusion (K : ChainComplex (ModuleCat ℚ) ℕ) (ρ : G →* End K) :
    invariantChainComplex G K ρ ⟶ K :=
  (NatTrans.mapHomologicalComplex (invariantsInclusionNat G) (.down ℕ)).app
    (equivariantChainComplex G K ρ)

lemma invariant_map_quasiIso [Fintype G] {K L : ChainComplex (ModuleCat ℚ) ℕ}
    (ρ : G →* End K) (f : K ⟶ L)
    (hf : ∀ i, Function.Bijective (fun z : (complexHomologyRepresentation G K ρ i).invariants =>
      (HomologicalComplex.homologyMap f i).hom z.1)) :
    QuasiIso (invariantChainInclusion G K ρ ≫ f) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective (HomologicalComplex.homologyMap
    (invariantChainInclusion G K ρ ≫ f) i).hom
  have heq : (HomologicalComplex.homologyMap (invariantChainInclusion G K ρ ≫ f) i).hom =
      ((HomologicalComplex.homologyMap f i).hom.comp
        (complexHomologyRepresentation G K ρ i).invariants.subtype).comp
          (fixedHomologyIso G K ρ i).hom.hom := by
    apply LinearMap.ext
    intro z
    have hc := ConcreteCategory.congr_hom (fixedHomologyIso_inclusion G K ρ i) z
    rw [HomologicalComplex.homologyMap_comp]
    change (HomologicalComplex.homologyMap f i).hom
      ((HomologicalComplex.homologyMap (invariantChainInclusion G K ρ) i).hom z) = _
    exact congrArg (HomologicalComplex.homologyMap f i).hom hc.symm
  rw [heq]
  exact (hf i).comp (fixedHomologyIso G K ρ i).toLinearEquiv.bijective

lemma invariant_map_homology [Fintype G] {K L : ChainComplex (ModuleCat ℚ) ℕ}
    (ρ : G →* End K) (f : K ⟶ L) (i : ℕ) :
    (HomologicalComplex.homologyMap (invariantChainInclusion G K ρ ≫ f) i).hom =
      ((HomologicalComplex.homologyMap f i).hom.comp
        (complexHomologyRepresentation G K ρ i).invariants.subtype).comp
          (fixedHomologyIso G K ρ i).hom.hom := by
  apply LinearMap.ext
  intro z
  have hc := ConcreteCategory.congr_hom (fixedHomologyIso_inclusion G K ρ i) z
  rw [HomologicalComplex.homologyMap_comp]
  change (HomologicalComplex.homologyMap f i).hom
    ((HomologicalComplex.homologyMap (invariantChainInclusion G K ρ) i).hom z) = _
  exact congrArg (HomologicalComplex.homologyMap f i).hom hc.symm

lemma invariant_map_fixed_bijective [Fintype G] {K L : ChainComplex (ModuleCat ℚ) ℕ}
    (ρ : G →* End K) (f : K ⟶ L)
    [QuasiIso (invariantChainInclusion G K ρ ≫ f)] (i : ℕ) :
    Function.Bijective (fun z : (complexHomologyRepresentation G K ρ i).invariants =>
      (HomologicalComplex.homologyMap f i).hom z.1) := by
  have hb : Function.Bijective
      (HomologicalComplex.homologyMap (invariantChainInclusion G K ρ ≫ f) i).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  rw [invariant_map_homology] at hb
  have h := hb.comp (fixedHomologyIso G K ρ i).toLinearEquiv.symm.bijective
  change Function.Bijective (fun z => (HomologicalComplex.homologyMap f i).hom
    ((fixedHomologyIso G K ρ i).toLinearEquiv
      ((fixedHomologyIso G K ρ i).toLinearEquiv.symm z)).1) at h
  simpa only [LinearEquiv.apply_symm_apply] using h

end HodgeLean.Foundations.QuotientDuality
