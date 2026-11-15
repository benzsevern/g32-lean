import HodgeLean.Adapters.CycleClassDivisorProduct3AbsoluteProofs

/-! # Relative cup and absolute compatibility: frozen specification

Implication from closed supports: inverse dual excision transports the quotient
of the descended Alexander–Whitney cochains to genuine relative cohomology.
The five public laws are proof obligations. The product is assembled from the
actual cochain, cycle quotients and comparison inverse. Supported transport and
normalization against the sheaf product remain separate work.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Adapters

/-- Dualizing the small-chain excision comparison over the rational field preserves cohomology.
Source: Hatcher, Algebraic Topology, §3.2; Spanier, Algebraic Topology, chapter 5;
Bredon, Topology and Geometry, VI.4. -/
theorem ccm15_dualComparison_quasiIso (Y : TopCat.{0}) (S T : Set Y)
    (hS : IsClosed S) (hT : IsClosed T) :
    QuasiIso (HomologicalComplex.linearDualMap (ccm14_relativeComparison Y S T)) :=
  ccm15_dualComparison_quasiIso_aux Y S T hS hT

/-- The actual descended cup of relative cycles is a small relative cycle.
Source: Hatcher, Algebraic Topology, §3.2; Spanier, Algebraic Topology, chapter 5;
Bredon, Topology and Geometry, VI.4. -/
theorem ccm15_smallCup_closed (Y : TopCat.{0}) (S T : Set Y) (p q : ℕ)
    (u : LinearMap.ker (ccm15_relativeDual Y S p).g.hom)
    (v : LinearMap.ker (ccm15_relativeDual Y T q).g.hom) :
    ccm15_smallCupLinear Y S T p q u.1 v.1 ∈
      LinearMap.ker (ccm15_smallDual Y S T (p + q)).g.hom :=
  ccm15_smallCup_closed_aux Y S T p q u v

/-- A boundary in the first argument and a cycle in the second give a boundary.
Source: Hatcher, Algebraic Topology, §3.2; Spanier, Algebraic Topology, chapter 5;
Bredon, Topology and Geometry, VI.4. -/
theorem ccm15_smallCup_boundary_left (Y : TopCat.{0}) (S T : Set Y) (p q : ℕ)
    (u : (ccm15_relativeDual Y S p).X₁)
    (v : LinearMap.ker (ccm15_relativeDual Y T q).g.hom) :
    ccm15_smallCupLinear Y S T p q ((ccm15_relativeDual Y S p).f.hom u) v.1 ∈
      LinearMap.range (ccm15_smallDual Y S T (p + q)).f.hom :=
  ccm15_smallCup_boundary_left_aux Y S T p q u v

/-- A cycle in the first argument and a boundary in the second give a boundary.
Source: Hatcher, Algebraic Topology, §3.2; Spanier, Algebraic Topology, chapter 5;
Bredon, Topology and Geometry, VI.4. -/
theorem ccm15_smallCup_boundary_right (Y : TopCat.{0}) (S T : Set Y) (p q : ℕ)
    (u : LinearMap.ker (ccm15_relativeDual Y S p).g.hom)
    (v : (ccm15_relativeDual Y T q).X₁) :
    ccm15_smallCupLinear Y S T p q u.1 ((ccm15_relativeDual Y T q).f.hom v) ∈
      LinearMap.range (ccm15_smallDual Y S T (p + q)).f.hom :=
  ccm15_smallCup_boundary_right_aux Y S T p q u v

/-- Forgetting relative supports recovers the existing absolute singular cup product.
Source: Hatcher, Algebraic Topology, §3.2; Spanier, Algebraic Topology, chapter 5;
Bredon, Topology and Geometry, VI.4. -/
theorem ccm15_relativeCup_absolute (Y : TopCat.{0}) (S T : Closeds Y) (p q : ℕ)
    (u : RelativeCohomology ℚ (TopPair.ofSubset (S : Set Y)ᶜ) p)
    (v : RelativeCohomology ℚ (TopPair.ofSubset (T : Set Y)ᶜ) q) :
    relativeCohomologyToAbsolute ℚ
      (TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ) (p + q)
        (ccm15_relativeCup Y S T p q u v) =
      HodgeLean.Foundations.Singular.cup Y rfl
        (relativeCohomologyToAbsolute ℚ (TopPair.ofSubset (S : Set Y)ᶜ) p u)
        (relativeCohomologyToAbsolute ℚ (TopPair.ofSubset (T : Set Y)ᶜ) q v) :=
  ccm15_relativeCup_absolute_aux Y S T p q u v

end HodgeLean.Adapters
