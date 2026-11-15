import HodgeLean.RealDefs.ComplexFundamentalClassProofs
import HodgeLean.RealDefs.FundamentalClass.Point
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.Euclidean

/-! Homology bounds from compact support bounds on compact real-charted spaces.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular HodgeLean.RealDefs
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- A compact real-charted space has no absolute homology above its chart dimension.
Source: Hatcher, Algebraic Topology, Lemma 3.27; take support equal to the whole space.
HC no distance; AV milestone no distance.
-/
theorem compact_charted_homology_bound (M : TopCat.{0}) [CompactSpace M] [T2Space M]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (n : ℕ) (hn : Module.finrank ℝ E = n) [ChartedSpace E M] (i : ℕ) (hi : n < i) :
    Subsingleton (Homology ℚ M i) := by
  let P := TopPair.ofSubset (X := M) ((Set.univ : Set M)ᶜ)
  letI : IsIso (relativeChainProjection ℚ P) :=
    isIso_relativeChainProjection _ ⟨fun y => y.property trivial⟩
  letI : IsIso (relativeHomologyProjection ℚ P i) := by
    unfold relativeHomologyProjection
    infer_instance
  have hp : Function.Injective (relativeHomologyProjection ℚ P i).hom :=
    ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).1
  have hv := (j5c_compact_manifold_aux (M := M) (E := E) hn isCompact_univ).1 i hi
  letI : Subsingleton (RelativeHomology ℚ P i) := hv
  exact hp.subsingleton

#print axioms compact_charted_homology_bound
/-- An open subset of a compact real-charted space has the same upper homology bound.
Source: Hatcher, Algebraic Topology, Lemma 3.27 and the long exact sequence of a pair.
HC no distance; AV milestone no distance.
-/
theorem compact_charted_open_homology_bound (M : TopCat.{0}) [CompactSpace M] [T2Space M]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (n : ℕ) (hn : Module.finrank ℝ E = n) [ChartedSpace E M] (U : TopologicalSpace.Opens M)
    (i : ℕ) (hi : n < i) : Subsingleton (Homology ℚ (TopCat.of U) i) := by
  let P := TopPair.ofSubset (X := M) (U : Set M)
  have hB : IsCompact ((U : Set M)ᶜ) := U.isOpen.isClosed_compl.isCompact
  have hv := (j5c_compact_manifold_aux (M := M) (E := E) hn hB).1 (i + 1) (by omega)
  have hR : Subsingleton (RelativeHomology ℚ P (i + 1)) := by
    simpa only [compl_compl] using hv
  have hM := compact_charted_homology_bound M n hn i hi
  exact ModuleCat.subsingleton_of_isZero
    (((relativeChainShortComplex_shortExact ℚ P).homology_exact₁ (i + 1) i rfl).isZero_of_both_isZero
        (@ModuleCat.isZero_of_subsingleton ℚ _ (RelativeHomology ℚ P (i + 1)) hR)
        (@ModuleCat.isZero_of_subsingleton ℚ _ (Homology ℚ M i) hM))

#print axioms compact_charted_open_homology_bound
end HodgeLean.Foundations.RationalHomologyManifold
