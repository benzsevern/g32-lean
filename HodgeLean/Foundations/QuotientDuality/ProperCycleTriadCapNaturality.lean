import HodgeLean.Foundations.QuotientDuality.ProperCycleTriadMap

/-! # Original cap naturality for actual maps of both triad subspaces -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original ambient lift of a relative cap is natural under the original map of pairs.
Source: Hatcher, Algebraic Topology, section 3.3, naturality of cap representatives.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_cap_lift_naturality
    {P Q : TopPair.{0}} (f : P ⟶ Q) (p q : ℕ) (φ : RelativeCochain ℚ Q p) :
    ModuleCat.ofHom (relativeCapLift ℚ P p q ((((relativeChainFunctor ℚ).map f).f p).hom.dualMap φ)) ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst f)) (ModuleCat.of ℚ ℚ)).f q =
      (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst f)) (ModuleCat.of ℚ ℚ)).f (p + q) ≫
        ModuleCat.ofHom (relativeCapLift ℚ Q p q φ) := by
  apply ModuleCat.hom_ext
  ext c
  change ((SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst f)) (ModuleCat.of ℚ ℚ)).f q).hom
      (AlgebraicTopology.Simplicial.cap ℚ p q
        (relativeCochainToAbsolute ℚ P p ((((relativeChainFunctor ℚ).map f).f p).hom.dualMap φ)) c) =
    AlgebraicTopology.Simplicial.cap ℚ p q (relativeCochainToAbsolute ℚ Q p φ)
      (((SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst f)) (ModuleCat.of ℚ ℚ)).f (p + q)).hom c)
  rw [properCycle_relative_cochain_to_absolute_naturality]
  exact AlgebraicTopology.Simplicial.cap_naturality ℚ _ p q _ c

/-- The original triad cap is natural on chains under an actual map preserving both subspaces.
Source: Hatcher, Algebraic Topology, section 3.3, triad cap naturality.
HC no distance; AV milestone no distance. -/
lemma properCycle_triad_cap_chain_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set X) (C D : Set Y)
    (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D) (p q : ℕ)
    (φ : RelativeCochain ℚ (TopPair.ofSubset (X := Y) C) p) :
    triadCapHom ℚ X A B p q
        ((((relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f hA)).f p).hom.dualMap φ) ≫
        ((relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f hB)).f q =
      (properCycle_triad_relative_chain_map f A B C D hA hB).f (p + q) ≫
        triadCapHom ℚ Y C D p q φ := by
  let fA := TopPair.ofSubsetHom f hA
  let fB := TopPair.ofSubsetHom f hB
  have hp := congrArg (fun m => m.f (p + q))
    (properCycle_triad_relative_chain_projection_naturality f A B C D hA hB)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at hp
  have ht := congrArg
    (fun m : SingularChainComplex ℚ X ⟶ (relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := Y) D) => m.f q)
    (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) fB)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at ht
  apply Cofork.IsColimit.hom_ext (triadRelativeChainProjectionComponentIsCokernel ℚ X A B (p + q))
  change (triadRelativeChainProjection ℚ X A B).f (p + q) ≫
      (triadCapHom ℚ X A B p q _ ≫ _) =
    (triadRelativeChainProjection ℚ X A B).f (p + q) ≫
      ((properCycle_triad_relative_chain_map f A B C D hA hB).f (p + q) ≫ _)
  rw [← Category.assoc, triadRelativeChainProjection_triadCapHom,
    ← Category.assoc, hp, Category.assoc, triadRelativeChainProjection_triadCapHom]
  change (ModuleCat.ofHom (relativeCapLift ℚ (TopPair.ofSubset (X := X) A) p q _) ≫
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) B)).f q) ≫ _ =
    (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f (p + q) ≫
      (ModuleCat.ofHom (relativeCapLift ℚ (TopPair.ofSubset (X := Y) C) p q φ) ≫
        (relativeChainProjection ℚ (TopPair.ofSubset (X := Y) D)).f q)
  rw [Category.assoc, ht, ← Category.assoc]
  erw [properCycle_relative_cap_lift_naturality fA p q φ]
  rw [Category.assoc]
  rfl

end HodgeLean.Foundations.QuotientDuality
