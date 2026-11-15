import HodgeLean.Foundations.QuotientDuality.RetainedCycleGradedCap
import HodgeLean.RealDefs.Port.AlgebraicTopology.Singular.Sheaf.ChainHomology

noncomputable section
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual ambient cap operation as a morphism of the chain-sheaf homology short complexes. -/
def retainedChainSheafCapShortComplex (X : TopCat.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : Simplicial.coboundary ℚ p φ = 0) :
    (singularChainSheafComplex ℚ X).sc (p + q) ⟶ (singularChainSheafComplex ℚ X).sc q :=
  retainedGradedCapShortComplexMap (singularChainSheafComplex ℚ X) p
    (fun j => retainedChainSheafAmbientCap X p j φ) (by
      intro j
      simpa only [singularChainSheafComplex_d] using
        retained_chain_sheaf_ambient_cap_boundary X p j φ hφ) q

/-- The sheaf short-complex construction retains the exact actual cap operation. -/
theorem retained_chain_sheaf_cap_short_complex_middle (X : TopCat.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : Simplicial.coboundary ℚ p φ = 0) :
    (retainedChainSheafCapShortComplex X p q φ hφ).τ₂ = retainedChainSheafAmbientCap X p q φ :=
  retained_graded_cap_short_complex_map_middle _ _ _ _ _

/-- Cap by the specified ambient cocycle on the actual chain-homology sheaves. -/
def retainedChainSheafCapHomology (X : TopCat.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : Simplicial.coboundary ℚ p φ = 0) :
    singularChainHomologySheaf ℚ X (p + q) ⟶ singularChainHomologySheaf ℚ X q :=
  ShortComplex.homologyMap (retainedChainSheafCapShortComplex X p q φ hφ)

/-- The homology-sheaf cap map is induced by the constructed map on actual cycles. -/
theorem retained_chain_sheaf_cap_homology_cycles (X : TopCat.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : Simplicial.coboundary ℚ p φ = 0) :
    (singularChainSheafComplex ℚ X).homologyπ (p + q) ≫
      retainedChainSheafCapHomology X p q φ hφ =
    ShortComplex.cyclesMap (retainedChainSheafCapShortComplex X p q φ hφ) ≫
      (singularChainSheafComplex ℚ X).homologyπ q :=
  ShortComplex.homologyπ_naturality (retainedChainSheafCapShortComplex X p q φ hφ)

end HodgeLean.Foundations.QuotientDuality
