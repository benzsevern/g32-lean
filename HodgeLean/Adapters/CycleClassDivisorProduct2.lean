import HodgeLean.Adapters.CycleClassDivisorProduct2Proofs
import HodgeLean.Adapters.CycleClassDivisorProduct2Examples

/-! # Small relative chains: frozen excision specification

An implication from closedness of the two supports: the canonical quotient
comparison is a quasi-isomorphism. The quotient and its descended cup cochain
are constructed independently. Dual transport, cohomology descent and the
absolute cohomology compatibility law remain separate work.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Adapters

/-- Subdivision in the open complement union identifies small relative chains
with genuine relative chains up to quasi-isomorphism.
Source: Hatcher, Algebraic Topology, §2.1, excision by subdivision;
Spanier, Algebraic Topology, chapters 4–5; Bredon, Topology and Geometry, IV.17. -/
theorem ccm14_relativeComparison_quasiIso (Y : TopCat.{0}) (S T : Set Y)
    (hS : IsClosed S) (hT : IsClosed T) :
    QuasiIso (ccm14_relativeComparison Y S T) :=
  ccm14_relativeComparison_quasiIso_aux Y S T hS hT

/-- Source: full supports on a point, with empty complement union. -/
example : QuasiIso (ccm14_relativeComparison (TopCat.of PUnit) Set.univ Set.univ) :=
  ccm14_relativeComparison_quasiIso _ _ _ isClosed_univ isClosed_univ

/-- Source: a closed proper support on the discrete two-point space. -/
example : QuasiIso (ccm14_relativeComparison ccm14_twoPoints {true} {true}) := by
  have h : IsClosed ({true} : Set ccm14_twoPoints) := by
    change @IsClosed Bool ⊥ {true}
    exact isClosed_discrete _
  exact ccm14_relativeComparison_quasiIso _ _ _ h h

end HodgeLean.Adapters
