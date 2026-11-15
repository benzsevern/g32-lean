import HodgeLean.Foundations.RationalHomologyManifold.CompactAmbientCycle
import HodgeLean.Foundations.RationalHomologyManifold.CompactBoundaryNeighborhood
import HodgeLean.Foundations.RationalHomologyManifold.AmbientSubdivisionPointBoundary

/-! Ambient primitives near compact supports from actual local sheaf-boundary witnesses.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- An ambient sheaf cycle with local sheaf primitives near a compact support has an actual subdivided ambient primitive on a neighborhood.
Source: Bredon, Sheaf Theory, second edition, V.9, V.16 and VI.12; compact point detection and local supported-chain primitives.
HC no distance; AV milestone no distance.
-/
theorem compact_sheaf_boundary_ambient_primitive (X : TopCat.{0}) [T2Space X]
    (t : FiniteTriangulation X) (n m : ℕ) (o : LocalRationalOrientation X (n + 1))
    (U : Opens X) (K : Set X) (hK : IsCompact K) (hKU : K ⊆ U)
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hcycle : (((subdivisionLimitSheafComplex X).d (n + 1) n).hom.app (Opposite.op U))
      ((subdivisionAmbientSectionMap X (n + 1) U m).hom z) = 0)
    (hlocal : ∀ x ∈ K, ∃ (V : Opens X)
      (s : ((subdivisionLimitSheafComplex X).X (n + 2)).obj.obj (Opposite.op V)), x ∈ V ∧
      (((subdivisionLimitSheafComplex X).d (n + 2) (n + 1)).hom.app (Opposite.op V)) s =
        (subdivisionAmbientSectionMap X (n + 1) V m).hom z) :
    ∃ (R : ℕ) (b : (SingularChainComplex ℚ X).X (n + 2)) (V : Opens X), K ⊆ V ∧
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ)).f (n + 1)
          ((rationalSubdivisionIterate X R).f (n + 1) z) =
        (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ)).f (n + 1)
          ((SingularChainComplex ℚ X).d (n + 2) (n + 1) b) := by
  obtain ⟨R, hR⟩ := compact_ambient_sheaf_cycle_relative_representative X n m U K hK hKU z hcycle
  refine ⟨R, ?_⟩
  apply compact_subdivided_point_boundaries_ambient_primitive X t (n + 1) o K hK
    ((rationalSubdivisionIterate X R).f (n + 1) z) hR
  intro x hx
  obtain ⟨V, s, hxV, hs⟩ := hlocal x hx
  have ht := ConcreteCategory.congr_hom
    (subdivisionAmbientSectionMap_transition X (n + 1) V m R) z
  change (subdivisionAmbientSectionMap X (n + 1) V (m + R)).hom
      ((rationalSubdivisionIterate X R).f (n + 1) z) =
    (subdivisionAmbientSectionMap X (n + 1) V m).hom z at ht
  exact subdivisionAmbientSection_sheaf_primitive_point_boundary X (n + 1) (m + R) V
    ((rationalSubdivisionIterate X R).f (n + 1) z) s (hs.trans ht.symm) x hxV

#print axioms compact_sheaf_boundary_ambient_primitive
/-- At or above the orientation degree, local sheaf boundaries have actual subdivided ambient primitives near compact supports.
Source: Bredon, Sheaf Theory, second edition, V.9, V.16 and VI.12; compact point detection and local supported-chain primitives.
HC no distance; AV milestone no distance.
-/
theorem compact_sheaf_boundary_ambient_primitive_of_le (X : TopCat.{0}) [T2Space X]
    (t : FiniteTriangulation X) (N n m : ℕ) (o : LocalRationalOrientation X N) (hN : N ≤ n + 1)
    (U : Opens X) (K : Set X) (hK : IsCompact K) (hKU : K ⊆ U)
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hcycle : (((subdivisionLimitSheafComplex X).d (n + 1) n).hom.app (Opposite.op U))
      ((subdivisionAmbientSectionMap X (n + 1) U m).hom z) = 0)
    (hlocal : ∀ x ∈ K, ∃ (V : Opens X)
      (s : ((subdivisionLimitSheafComplex X).X (n + 2)).obj.obj (Opposite.op V)), x ∈ V ∧
      (((subdivisionLimitSheafComplex X).d (n + 2) (n + 1)).hom.app (Opposite.op V)) s =
        (subdivisionAmbientSectionMap X (n + 1) V m).hom z) :
    ∃ (R : ℕ) (b : (SingularChainComplex ℚ X).X (n + 2)) (V : Opens X), K ⊆ V ∧
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ)).f (n + 1)
          ((rationalSubdivisionIterate X R).f (n + 1) z) =
        (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ)).f (n + 1)
          ((SingularChainComplex ℚ X).d (n + 2) (n + 1) b) := by
  obtain hlt | heq := lt_or_eq_of_le hN
  · obtain ⟨R, hR⟩ := compact_ambient_sheaf_cycle_relative_representative X n m U K hK hKU z hcycle
    obtain ⟨b, V, hKV, hb⟩ := compact_relative_cycle_ambient_boundary_above_orientation
      X t N o K hK (n + 1) hlt ((rationalSubdivisionIterate X R).f (n + 1) z) hR
    exact ⟨R, b, V, hKV, hb⟩
  · subst N
    exact compact_sheaf_boundary_ambient_primitive X t n m o U K hK hKU z hcycle hlocal

#print axioms compact_sheaf_boundary_ambient_primitive_of_le
end HodgeLean.Foundations.RationalHomologyManifold
