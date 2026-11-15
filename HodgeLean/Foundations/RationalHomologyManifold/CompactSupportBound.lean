import HodgeLean.Foundations.RationalHomologyManifold.OpenHomologyBound
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.Euclidean

/-! Finite-dimensional control of singular homology along compact subsets.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Relative singular groups along compact subsets have a uniform ambient-dimension bound.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; finite-polyhedron dimension bound.
HC no distance; AV milestone no distance.
-/
theorem finiteTriangulation_compact_support_bound (X : TopCat.{0}) [T2Space X]
    (t : FiniteTriangulation X) (B : Set X) (hB : IsCompact B)
    (i : ℕ) (hi : t.ambient + 1 < i) :
    Subsingleton (RelativeHomology ℚ (TopPair.ofSubset (X := X) Bᶜ) i) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  let P := TopPair.ofSubset (X := X) Bᶜ
  have hX : Subsingleton (Homology ℚ X (n + 1)) :=
    finiteTriangulation_open_homology_bound X t X (𝟙 X)
      Topology.IsOpenEmbedding.id (n + 1) (by omega)
  have hU : Subsingleton (Homology ℚ P.snd n) :=
    finiteTriangulation_open_homology_bound X t P.snd P.map
      hB.isClosed.isOpen_compl.isOpenEmbedding_subtypeVal n (by omega)
  exact ModuleCat.subsingleton_of_isZero
    ((relativeSingular_homology_exact_relative P n).isZero_of_both_isZero
      (@ModuleCat.isZero_of_subsingleton ℚ _ (Homology ℚ X (n + 1)) hX)
      (@ModuleCat.isZero_of_subsingleton ℚ _ (Homology ℚ P.snd n) hU))

#print axioms finiteTriangulation_compact_support_bound
end HodgeLean.Foundations.RationalHomologyManifold
