import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenCoverHomologyVanishing
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.Contractible

/-! # Ordinary homology of the actual empty and contractible cover pieces -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular Convexity
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual empty topological space has zero ordinary rational homology in every degree.
Source: Hatcher, Algebraic Topology, section 2.1, the singular chains of the empty space.
HC no distance; AV milestone no distance. -/
lemma properCycle_empty_homology_subsingleton
    (X : TopCat.{0}) [IsEmpty X] (n : ℕ) : Subsingleton (Homology ℚ X n) := by
  have hz : IsZero (SingularChainComplex ℚ X) := by
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.hom_ext
    intro j
    apply SSet.chainComplex_hom_ext
    intro σ
    exact isEmptyElim ((X.toSSetObjEquiv _ σ) StdSimplex.barycenter)
  exact ModuleCat.subsingleton_of_isZero
    ((HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map_isZero hz)

/-- An actual contractible cover piece has zero ordinary rational homology in every positive degree.
Source: Hatcher, Algebraic Topology, section 2.1, homotopy invariance and the point computation.
HC no distance; AV milestone no distance. -/
lemma properCycle_contractible_homology_subsingleton
    (X : TopCat.{0}) [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (Homology ℚ X n) :=
  ModuleCat.subsingleton_of_isZero
    ((singularChainComplex_exactAt_of_contractible ℚ X n hn).isZero_homology)

end HodgeLean.Foundations.QuotientDuality
