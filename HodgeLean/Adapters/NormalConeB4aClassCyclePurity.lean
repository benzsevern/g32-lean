import HodgeLean.Adapters.NormalConeB4aClassPurityGlobal
import HodgeLean.Adapters.NormalConeB4aClassDetection

/-! # Lower vanishing for the frozen cycle-support pair -/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace

/-- The rational cohomology of the frozen cycle-support pair vanishes below
twice the lower bound on its component codimensions. -/
theorem a3b4a_classSupport_vanishing_below_codimension
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [Smooth q]
    [QuasiCompact q] [IsSeparated q] (γ : AlgebraicCycle Z ℚ) (c : ℕ)
    (hc : ∀ ξ ∈ γ.support, (c : ℕ∞) ≤ Order.coheight ξ)
    (n : ℕ) (hn : n < 2 * c) :
    IsZero (RelativeCohomology ℚ
      (TopPair.ofSubset (X := a3b4_an q) (a3b4_cycleSupport q γ)ᶜ) n) := by
  have hzero := a3b4a_classRelative_purity_vanishing q
    (a3b4a_classAlgebraicSupport q γ) c
    (a3b4a_classAlgebraicSupport_coheight q γ c hc) ⊤ n hn
  letI : Subsingleton (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (Set.univ : Set (ComplexPoint (Over.mk q)))
        (a3b4_cycleSupport q γ)) n) := ModuleCat.subsingleton_of_isZero hzero
  letI := (a3b4a_classLocal_restrict_univ_injective (a3b4_cycleSupport q γ) n).subsingleton
  exact ModuleCat.isZero_of_subsingleton _

end HodgeLean.Adapters
