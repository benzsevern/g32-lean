import HodgeLean.Adapters.NormalConeB4aClassDimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.SmoothPair.OpenTransport

/-! # Local lower vanishing along the regular layer of an algebraic support

Route: realize the smooth stratum as a closed immersion in the complement of
the singular remainder. Its affine neighborhoods have the normal codimension
bound from the support dimension calculation. Transport their normal pairs
back to the original ambient complex points.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace

set_option backward.isDefEq.respectTransparency false in
/-- Each point of the regular support layer has cofinally small neighborhoods
with vanishing relative cohomology below twice the support codimension. -/
theorem a3b4a_classLayer_exists_relative_vanishing
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) (d c : ℕ)
    [SmoothOfRelativeDimension d q] [LocallyOfFiniteType q]
    (S : Closeds Z) (hc : ∀ z ∈ S, (c : ℕ∞) ≤ Order.coheight z)
    (y : ComplexPoint (Over.mk q)) (hy : y.underlying ∈ S)
    (hyNext : y.underlying ∉ reducedClosedSingularRemainder q S)
    (V : Opens (ComplexPoint (Over.mk q))) (hyV : y ∈ V) :
    ∃ W : Opens (ComplexPoint (Over.mk q)), W ≤ V ∧ y ∈ W ∧
      ∀ n : ℕ, n < 2 * c → IsZero (RelativeCohomology ℚ
        (neighborhoodSupportComplementPair (W : Set (ComplexPoint (Over.mk q)))
          (Point.underlying ⁻¹' (S : Set Z))) n) := by
  let X := Over.mk q
  let Y := Over.mk (reducedClosedSmoothPieceι q S ≫ q)
  let j : Y ⟶ X := Over.homMk (reducedClosedSmoothPieceι q S) rfl
  letI : LocallyOfFiniteType X.hom := ‹LocallyOfFiniteType q›
  letI : LocallyOfFiniteType Y.hom := inferInstanceAs
    (LocallyOfFiniteType (reducedClosedSmoothPieceι q S ≫ q))
  letI : IsImmersion j.left := inferInstanceAs (IsImmersion (reducedClosedSmoothPieceι q S))
  have hyr : y ∈ Set.range (Point.map j) := by
    rw [ComplexPoint.range_map_of_isImmersion]
    change y.underlying ∈ Set.range (reducedClosedSmoothPieceι q S)
    rw [reducedClosedSmoothPiece_range]
    exact ⟨hy, hyNext⟩
  obtain ⟨z, rfl⟩ := hyr
  let B := (reducedClosedStructureMap q S).smoothLocus
  let O := closedImmersionSourceOpenTarget (reducedClosedSubschemeι S) B
  let OX := ComplexPoint.openScheme X O
  let i₀ := closedImmersionSourceOpenLift (reducedClosedSubschemeι S) B
  have hi : i₀ ≫ OX.hom = Y.hom := by
    change i₀ ≫ (O.ι ≫ q) = (B.ι ≫ reducedClosedSubschemeι S) ≫ q
    rw [← Category.assoc, closedImmersionSourceOpenLift_ι]
  let i : Y ⟶ OX := Over.homMk i₀ hi
  letI : IsClosedImmersion i.left :=
    closedImmersionSourceOpenLift_isClosedImmersion (reducedClosedSubschemeι S) B
  letI : SmoothOfRelativeDimension d OX.hom := by
    change SmoothOfRelativeDimension d (O.ι ≫ q)
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d O.ι q
  letI : LocallyOfFiniteType OX.hom := inferInstanceAs (LocallyOfFiniteType (O.ι ≫ q))
  obtain ⟨A, hA, hzA, m, hcodim, hdim⟩ :=
    a3b4a_classStratum_exists_smooth_relativeDimension q d c S hc z.underlying
  letI : SmoothOfRelativeDimension m (ComplexPoint.openScheme Y A).hom := hdim
  let zA := ComplexPoint.asOpenPoint Y A z hzA
  let f := Point.map (ComplexPoint.openInclusion X O)
  have hS : f ⁻¹' (Point.underlying ⁻¹' (S : Set Z)) = Set.range (Point.map i) := by
    rw [ComplexPoint.range_map_of_isImmersion_of_comm OX Y i]
    change _ = (Point.underlying : ComplexPoint OX → OX.left) ⁻¹' Set.range i₀
    rw [range_closedImmersionSourceOpenLift, range_reducedClosedSubschemeι]
    rfl
  have he : f (Point.map (ComplexPoint.openInclusion Y A ≫ i) zA) = Point.map j z := by
    apply Over.OverMorphism.ext
    change (zA.left ≫ (A.ι ≫ i₀)) ≫ O.ι = z.left ≫ reducedClosedSmoothPieceι q S
    rw [Category.assoc, Category.assoc, closedImmersionSourceOpenLift_ι,
      ← Category.assoc]
    exact congrArg (fun g => g ≫ reducedClosedSmoothPieceι q S)
      (ComplexPoint.liftToOpen_fac Y A z hzA)
  obtain ⟨W, hWV, hzW, hW⟩ := ComplexPoint.exists_smoothClosedSourceOpenImageNeighborhood
    OX Y i m d f (ComplexPoint.isOpenEmbedding_map_open X O)
      (Point.underlying ⁻¹' (S : Set Z)) hS A zA V (he ▸ hyV)
  refine ⟨W, hWV, he ▸ hzW, fun n hn => ?_⟩
  exact hW n (by omega)

end HodgeLean.Adapters
