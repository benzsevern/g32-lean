import Mathlib.Analysis.Complex.Polynomial.Basic
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Separated

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Finitely many nonidentity symmetries of an integral separated complex scheme
have a common rational point moved by every symmetry. -/
theorem s2v_l1b_exists_point_moved_by_finite_family
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsSeparated X.hom]
    [LocallyOfFiniteType X.hom]
    (I : Type) [Finite I] (a : I → (X ⟶ X))
    (hne : ∀ i, a i ≠ 𝟙 X) :
    ∃ x : ComplexPoint X, ∀ i, Point.map (a i) x ≠ x := by
  classical
  let F (i : I) : Set X.left := Set.range (equalizer.ι (a i) (𝟙 X)).left
  have hF (i : I) : IsClosed (F i) :=
    (Scheme.Hom.isClosedEmbedding _).isClosed_range
  have hproper (i : I) : (F i)ᶜ.Nonempty := by
    by_contra hempty
    haveI : Surjective (equalizer.ι (a i) (𝟙 X)).left := ⟨by
      intro x
      have : x ∉ (F i)ᶜ := fun hx => hempty ⟨x, hx⟩
      exact not_not.mp this⟩
    haveI : IsIso (equalizer.ι (a i) (𝟙 X)).left :=
      isIso_of_isClosedImmersion_of_surjective _
    apply hne i
    apply Over.OverMorphism.ext
    apply (cancel_epi (equalizer.ι (a i) (𝟙 X)).left).mp
    exact congrArg Over.Hom.left (equalizer.condition _ _)
  letI := Fintype.ofFinite I
  have hinter : ∀ s : Finset I, (⋂ i ∈ s, (F i)ᶜ).Nonempty := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.notMem_empty, Set.iInter_of_empty,
        Set.iInter_univ] using (Set.univ_nonempty : (Set.univ : Set X.left).Nonempty)
    | @insert i s hi ih =>
      rw [Finset.set_biInter_insert]
      exact nonempty_preirreducible_inter (hF i).isOpen_compl
        (isOpen_biInter_finset fun j _ => (hF j).isOpen_compl) (hproper i) ih
  let U : Set X.left := ⋂ i, (F i)ᶜ
  have hU : IsOpen U := isOpen_iInter_of_finite fun i => (hF i).isOpen_compl
  have hUn : U.Nonempty := by simpa only [Finset.mem_univ, Set.iInter_true] using hinter Finset.univ
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints hUn hU.isLocallyClosed
  let x : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom z hzc)
    (pointOfClosedPoint_comp X.hom z hzc)
  refine ⟨x, ?_⟩
  intro i hi
  have hf : x ≫ a i = x ≫ 𝟙 X := hi.trans (Category.comp_id x).symm
  have hzF : z ∈ F i := by
    refine ⟨(equalizer.lift x hf).left (IsLocalRing.closedPoint ℂ), ?_⟩
    change ((equalizer.lift x hf) ≫ equalizer.ι (a i) (𝟙 X)).left
      (IsLocalRing.closedPoint ℂ) = z
    rw [equalizer.lift_ι]
    exact pointOfClosedPoint_apply X.hom z hzc _
  exact (Set.mem_iInter.mp hz i) hzF

end HodgeLean.Foundations.Program
