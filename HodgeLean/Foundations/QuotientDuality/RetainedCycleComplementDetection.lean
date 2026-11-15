import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectionDetection
import HodgeLean.Adapters.NormalConeB4aClassPurityGlobal
import HodgeLean.Adapters.NormalConeB4aClassDetection

/-! Homology detection away from a higher-codimension algebraic centre. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Removing an algebraic centre of sufficiently large coheight preserves injectivity in the tested homology degree. -/
lemma retained_complement_homology_injective_of_coheight
    {Z : Scheme.{0}} (q : Z ⟶ Spec ↧ℂ) [Smooth q] [QuasiCompact q] [IsSeparated q]
    (B : Closeds Z) (c n : ℕ) (hc : ∀ z ∈ B, (c : ℕ∞) ≤ Order.coheight z)
    (hn : n+1 < 2*c) :
    Function.Injective (homologyMap ℚ n
      (TopPair.ofSubset (X := a3b4_an q)
        (Point.underlying ⁻¹' (B : Set Z))ᶜ).map) := by
  let S : Set (ComplexPoint (Over.mk q)) := Point.underlying ⁻¹' (B : Set Z)
  let P := TopPair.ofSubset (X := a3b4_an q) Sᶜ
  have hz := a3b4a_classRelative_purity_vanishing q B c hc ⊤ (n+1) hn
  letI : Subsingleton (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (Set.univ : Set (ComplexPoint (Over.mk q))) S) (n+1)) :=
    ModuleCat.subsingleton_of_isZero hz
  letI : Subsingleton (RelativeCohomology ℚ P (n+1)) :=
    (a3b4a_classLocal_restrict_univ_injective S (n+1)).subsingleton
  exact retained_homology_inclusion_injective_of_relative_vanishing P n

end HodgeLean.Foundations.QuotientDuality
