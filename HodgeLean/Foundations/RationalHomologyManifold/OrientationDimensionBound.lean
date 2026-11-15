import HodgeLean.Foundations.RationalHomologyManifold.CompactDetection

/-! Compact-support bounds in the intrinsic orientation dimension.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular HodgeLean.RealDefs
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Relative homology along compact subsets vanishes above the orientation dimension.
Source: Bredon, Sheaf Theory, second edition, V.9 and V.16; compact-support descent.
HC no distance; AV milestone no distance.
-/
theorem relativeHomology_above_orientation (X : TopCat.{0}) [T2Space X]
    (t : FiniteTriangulation X) (n : ℕ) (o : LocalRationalOrientation X n)
    (A : Set X) (hA : IsCompact A) (i : ℕ) (hi : n < i) :
    Subsingleton (RelativeHomology ℚ (TopPair.ofSubset (X := X) Aᶜ) i) := by
  have hd := compact_detection_of_uniform_bound X i (t.ambient + 1)
    (fun x j hj => o.vanishes x j (by omega))
    (finiteTriangulation_compact_support_bound X t) A hA
  have hz (c : RelativeHomology ℚ (TopPair.ofSubset (X := X) Aᶜ) i) : c = 0 := by
    apply hd c
    intro x hx
    exact @Subsingleton.elim _ (o.vanishes x i (by omega)) _ _
  exact ⟨fun c d => (hz c).trans (hz d).symm⟩

#print axioms relativeHomology_above_orientation
/-- Absolute homology of a compact finite polyhedron vanishes above its orientation dimension.
Source: Bredon, Sheaf Theory, second edition, V.9 and V.16; compact-support descent.
HC no distance; AV milestone no distance.
-/
theorem homology_above_orientation (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (t : FiniteTriangulation X) (n : ℕ) (o : LocalRationalOrientation X n)
    (i : ℕ) (hi : n < i) : Subsingleton (Homology ℚ X i) := by
  let P := TopPair.ofSubset (X := X) (Set.univ : Set X)ᶜ
  letI : IsIso (relativeChainProjection ℚ P) :=
    isIso_relativeChainProjection _ ⟨fun y => y.property trivial⟩
  letI : IsIso (relativeHomologyProjection ℚ P i) := by
    unfold relativeHomologyProjection
    infer_instance
  have hp := ((ConcreteCategory.isIso_iff_bijective
    (relativeHomologyProjection ℚ P i)).mp inferInstance).1
  letI := relativeHomology_above_orientation X t n o Set.univ isCompact_univ i hi
  exact ⟨fun c d => hp (Subsingleton.elim _ _)⟩

#print axioms homology_above_orientation
/-- Rational cohomology vanishes above the orientation dimension.
Source: Bredon, Sheaf Theory, second edition, V.9 and V.16; rational universal coefficients.
HC no distance; AV milestone no distance.
-/
theorem cohomology_above_orientation (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (t : FiniteTriangulation X) (n : ℕ) (o : LocalRationalOrientation X n)
    (i : ℕ) (hi : n < i) : Subsingleton (Cohomology ℚ X i) := by
  letI := homology_above_orientation X t n o i hi
  refine ⟨fun a b => (cohomologyEquivDualHomology ℚ X i).injective ?_⟩
  ext z
  rw [show z = 0 from Subsingleton.elim _ _]
  exact (map_zero _).trans (map_zero _).symm

#print axioms cohomology_above_orientation
end HodgeLean.Foundations.RationalHomologyManifold
