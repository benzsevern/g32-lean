import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeCochainNaturality

/-! # Naturality of the literal relative cap chain map -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original relative cap map commutes with actual maps of pairs, with the cochain pulled back through the literal relative chain map.
Source: Hatcher, Algebraic Topology, section 3.3, naturality of relative cap products.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_cap_chain_naturality
    {P Q : TopPair.{0}} (f : P ⟶ Q) (p q : ℕ) (φ : RelativeCochain ℚ Q p) :
    relativeCapHom ℚ P p q ((((relativeChainFunctor ℚ).map f).f p).hom.dualMap φ) ≫
      (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst f)) (ModuleCat.of ℚ ℚ)).f q =
      ((relativeChainFunctor ℚ).map f).f (p + q) ≫ relativeCapHom ℚ Q p q φ := by
  apply Cofork.IsColimit.hom_ext
    (relativeChainProjectionComponentIsCokernelForCap ℚ P (p + q))
  change (relativeChainProjection ℚ P).f (p + q) ≫
      (relativeCapHom ℚ P p q _ ≫ _) =
    (relativeChainProjection ℚ P).f (p + q) ≫
      (((relativeChainFunctor ℚ).map f).f (p + q) ≫ relativeCapHom ℚ Q p q φ)
  have hp := congrArg
    (fun g : SingularChainComplex ℚ P.fst ⟶ (relativeChainFunctor ℚ).obj Q => g.f (p + q))
    (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) f)
  change (relativeChainProjection ℚ P).f (p + q) ≫
    ((relativeChainFunctor ℚ).map f).f (p + q) =
      (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst f)) (ModuleCat.of ℚ ℚ)).f
        (p + q) ≫ (relativeChainProjection ℚ Q).f (p + q) at hp
  rw [← Category.assoc, relativeChainProjection_relativeCapHom,
    ← Category.assoc, hp, Category.assoc, relativeChainProjection_relativeCapHom]
  apply ModuleCat.hom_ext
  ext c
  change _ = AlgebraicTopology.Simplicial.cap ℚ p q (relativeCochainToAbsolute ℚ Q p φ) _
  change ((SSet.chainComplexMap _ (ModuleCat.of ℚ ℚ)).f q).hom
    (AlgebraicTopology.Simplicial.cap ℚ p q
      (relativeCochainToAbsolute ℚ P p _) c) = _
  rw [properCycle_relative_cochain_to_absolute_naturality]
  exact AlgebraicTopology.Simplicial.cap_naturality ℚ _ p q _ c

end HodgeLean.Foundations.QuotientDuality
