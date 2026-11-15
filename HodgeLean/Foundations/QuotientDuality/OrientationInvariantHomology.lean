import HodgeLean.Foundations.QuotientDuality.OrientationEquivariantComplex

/-! Comparison of fixed chain complexes with fixed homology classes. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace HodgeLean.Foundations.QuotientDuality

variable (G : Type) [Group G]

def invariantsInclusionNat :
    Rep.invariantsFunctor ℚ G ⟶ forget₂ (Rep ℚ G) (ModuleCat ℚ) where
  app A := ModuleCat.ofHom A.ρ.invariants.subtype
  naturality X Y f := by ext x; rfl

lemma homology_invariants_inclusion_injective [Fintype G]
    (E : ChainComplex (Rep ℚ G) ℕ) (i : ℕ) :
    Function.Injective (HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex (invariantsInclusionNat G) (.down ℕ)).app E) i).hom := by
  letI := rational_invariants_preserves_homology G
  let τ := invariantsInclusionNat G
  change Function.Injective (ShortComplex.homologyMap ((E.sc i).mapNatTrans τ)).hom
  haveI : Mono (τ.app (E.sc i).homology) :=
    (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  have h := ShortComplex.homologyMap_mapNatTrans (S := E.sc i) τ
  haveI : Mono (ShortComplex.homologyMap ((E.sc i).mapNatTrans τ)) := by
    rw [h]
    infer_instance
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

def fixedHomologyIso [Fintype G] (K : ChainComplex (ModuleCat ℚ) ℕ)
    (ρ : G →* End K) (i : ℕ) :
    (((Rep.invariantsFunctor ℚ G).mapHomologicalComplex (.down ℕ)).obj
      (equivariantChainComplex G K ρ)).homology i ≅
        ModuleCat.of ℚ (complexHomologyRepresentation G K ρ i).invariants := by
  letI := rational_invariants_preserves_homology G
  exact ((equivariantChainComplex G K ρ).sc i).mapHomologyIso (Rep.invariantsFunctor ℚ G) ≪≫
    (Rep.invariantsFunctor ℚ G).mapIso (equivariantHomologyIso G K ρ i).symm

lemma fixedHomologyIso_inclusion [Fintype G] (K : ChainComplex (ModuleCat ℚ) ℕ)
    (ρ : G →* End K) (i : ℕ) :
    (fixedHomologyIso G K ρ i).hom ≫
        ModuleCat.ofHom (complexHomologyRepresentation G K ρ i).invariants.subtype =
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (invariantsInclusionNat G) (.down ℕ)).app
          (equivariantChainComplex G K ρ)) i := by
  letI := rational_invariants_preserves_homology G
  let E := equivariantChainComplex G K ρ
  let I := Rep.invariantsFunctor ℚ G
  let τ := invariantsInclusionNat G
  let e := equivariantHomologyIso G K ρ i
  change (((E.sc i).mapHomologyIso I).hom ≫ I.map e.inv) ≫
    τ.app (Rep.of (complexHomologyRepresentation G K ρ i)) = _
  rw [Category.assoc, τ.naturality e.inv]
  exact (ShortComplex.homologyMap_mapNatTrans (S := E.sc i) τ).symm

end HodgeLean.Foundations.QuotientDuality
