import HodgeLean.Foundations.Program.SchoenCycleStep1
import HodgeLean.Foundations.Program.SchoenCycleBranchAffineImage

/-! # Complex points in finite branch images -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A complex point in the scheme image range lifts to an actual complex point.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.3, points over an algebraically closed field. -/
theorem s2e_complexPoint_lift_of_mem_range
    {X' X : Over (Spec ↧ℂ)} [LocallyOfFiniteType X'.hom]
    (π : X' ⟶ X) (x : ComplexPoint X)
    (hx : x.underlying ∈ Set.range π.left) :
    ∃ z : ComplexPoint X', Point.map π z = x := by
  haveI : LocallyOfFiniteType (π.left ≫ X.hom) := by
    rw [Over.w π]
    infer_instance
  letI : LocallyOfFiniteType π.left := locallyOfFiniteType_of_comp π.left X.hom
  let P : Over (Spec ↧ℂ) := Over.mk (pullback.snd π.left x.left)
  letI : MorphismProperty.IsStableUnderBaseChangeAlong
      (P := @LocallyOfFiniteType) x.left := {
    of_isPullback pb h :=
      locallyOfFiniteType_isStableUnderBaseChange.of_isPullback pb h }
  haveI : LocallyOfFiniteType (pullback.snd π.left x.left) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  haveI : LocallyOfFiniteType P.hom := by
    change LocallyOfFiniteType (pullback.snd π.left x.left)
    infer_instance
  obtain ⟨y, hy⟩ := hx
  have hy' : π.left y = x.left (IsLocalRing.closedPoint ℂ) := hy
  obtain ⟨p, -, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := π.left) (g := x.left) y (IsLocalRing.closedPoint ℂ) hy'
  have hP : (Set.univ : Set P.left).Nonempty := ⟨p, Set.mem_univ _⟩
  haveI : JacobsonSpace P.left := LocallyOfFiniteType.jacobsonSpace P.hom
  obtain ⟨q, -, hq⟩ := (jacobsonSpace_iff_locallyClosed.mp inferInstance)
    Set.univ hP isOpen_univ.isLocallyClosed
  let z : ComplexPoint P := Over.homMk
    ((pointEquivClosedPoint P.hom).symm ⟨q, hq⟩).1
    ((pointEquivClosedPoint P.hom).symm ⟨q, hq⟩).2
  let j : P ⟶ X' := Over.homMk (pullback.fst π.left x.left) (by
    change pullback.fst π.left x.left ≫ X'.hom = pullback.snd π.left x.left
    rw [← Over.w π, ← Category.assoc, pullback.condition, Category.assoc, x.w]
    change pullback.snd π.left x.left ≫ 𝟙 _ = pullback.snd π.left x.left
    simp)
  refine ⟨Point.map j z, ?_⟩
  apply Over.OverMorphism.ext
  change z.left ≫ pullback.fst π.left x.left ≫ π.left = x.left
  rw [pullback.condition, ← Category.assoc]
  have hz := z.w
  change z.left ≫ pullback.snd π.left x.left = 𝟙 _ at hz
  rw [hz, Category.id_comp]

end HodgeLean.Foundations.Program
