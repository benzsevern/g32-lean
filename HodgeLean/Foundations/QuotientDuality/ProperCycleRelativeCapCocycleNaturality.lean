import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeCapChainNaturality
import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeCoboundaryNaturality

/-! # Naturality of the actual relative cap pairing on cocycles -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original relative cap pairing on homology is natural for actual maps of pairs and the induced relative cocycle pullback.
Source: Hatcher, Algebraic Topology, section 3.3, naturality of relative cap products.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_cap_cocycle_naturality
    {P Q : TopPair.{0}} (f : P ⟶ Q) (p q : ℕ)
    (φ : RelativeCochain ℚ Q p) (hφ : relativeCoboundary ℚ Q p φ = 0) :
    let ψ : RelativeCocycle ℚ P p :=
      ⟨(((relativeChainFunctor ℚ).map f).f p).hom.dualMap φ, by
        change relativeCoboundary ℚ P p _ = 0
        rw [properCycle_relative_coboundary_naturality, hφ, map_zero]⟩
    ∀ c : RelativeHomology ℚ P (p + q),
      homologyMap ℚ q (TopPair.Hom.fst f) (relativeCapHomologyMap ℚ P p q ψ.1 ψ.2 c) =
        relativeCapHomologyMap ℚ Q p q φ hφ (relativeHomologyMap ℚ (p + q) f c) := by
  let ψ : RelativeCocycle ℚ P p :=
    ⟨(((relativeChainFunctor ℚ).map f).f p).hom.dualMap φ, by
      change relativeCoboundary ℚ P p _ = 0
      rw [properCycle_relative_coboundary_naturality, hφ, map_zero]⟩
  dsimp only
  intro c
  let FN := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) (p + q)).map
    ((relativeChainFunctor ℚ).map f)
  let FQ := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) q).map
    (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst f)) (ModuleCat.of ℚ ℚ))
  let CP := relativeCapShortComplexHom ℚ P p q ψ.1 ψ.2
  let CQ := relativeCapShortComplexHom ℚ Q p q φ hφ
  have hh : ShortComplex.homologyMap (CP ≫ FQ) = ShortComplex.homologyMap (FN ≫ CQ) := by
    apply AlgebraicTopology.Simplicial.homologyMap_eq_of_τ₂_eq
    change CP.τ₂ ≫ FQ.τ₂ = FN.τ₂ ≫ CQ.τ₂
    rw [relativeCapShortComplexHom_τ₂, relativeCapShortComplexHom_τ₂]
    exact properCycle_relative_cap_chain_naturality f p q φ
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp] at hh
  exact ConcreteCategory.congr_hom hh c

end HodgeLean.Foundations.QuotientDuality
