import HodgeLean.Adapters.NormalConeB4aClassSupport
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.DimensionFormula
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.Dimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.SingularLocusDimension

/-! # Dimension bounds for nonprojective algebraic supports

Route: map specialization chains from the reduced support into the ambient
scheme, then combine their lengths with the ambient height-coheight bound.
No integrality or projectivity of the ambient scheme is needed.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- A closed support of codimension at least `c` in a smooth `d`-dimensional
complex scheme has algebraic dimension at most `d - c`. -/
theorem a3b4a_classSupport_dimension_le
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) (d c : ℕ)
    [SmoothOfRelativeDimension d q] (S : Closeds Z)
    (hc : ∀ z ∈ S, (c : ℕ∞) ≤ Order.coheight z) :
    topologicalKrullDim (reducedClosedSubscheme S) ≤ (d - c : ℕ) := by
  rw [Scheme.topologicalKrullDim_eq_orderKrullDim]
  let f := reducedClosedSubschemeι S
  have hiff (a b : reducedClosedSubscheme S) : f a ≤ f b ↔ a ≤ b := by
    rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
    exact f.isClosedEmbedding.isInducing.specializes_iff
  have hstrict : StrictMono f := fun a b hab =>
    lt_iff_le_not_ge.mpr ⟨(hiff a b).mpr hab.le, fun h => hab.not_ge ((hiff b a).mp h)⟩
  have hheight (a : reducedClosedSubscheme S) : Order.height (f a) ≤ d - c := by
    have haS : f a ∈ S := (range_reducedClosedSubschemeι S).le ⟨a, rfl⟩
    apply ENat.le_sub_of_add_le_right (by simp)
    calc
      Order.height (f a) + c ≤ Order.height (f a) + Order.coheight (f a) :=
        add_le_add le_rfl (hc _ haS)
      _ ≤ d := SmoothOfRelativeDimension.height_add_coheight_le_complex (f := q) (d := d) _
  cases isEmpty_or_nonempty (reducedClosedSubscheme S) with
  | inl h =>
    rw [Order.krullDim_eq_bot]
    exact bot_le
  | inr h =>
    rw [Order.krullDim_eq_iSup_length]
    apply WithBot.coe_le_coe.mpr
    refine iSup_le fun l => ?_
    exact (Order.length_le_height_last (p := l.map f hstrict)).trans (hheight l.last)

/-- The smooth stratum has fixed-dimensional affine neighborhoods whose normal
codimension is at least the lower bound on the algebraic support. -/
theorem a3b4a_classStratum_exists_smooth_relativeDimension
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) (d c : ℕ)
    [SmoothOfRelativeDimension d q] [LocallyOfFiniteType q] (S : Closeds Z)
    (hc : ∀ z ∈ S, (c : ℕ∞) ≤ Order.coheight z)
    (z : reducedClosedSmoothPiece q S) :
    ∃ (U : (reducedClosedSmoothPiece q S).Opens) (_ : IsAffineOpen U), z ∈ U ∧
      ∃ m : ℕ, c ≤ d - m ∧
        SmoothOfRelativeDimension m (U.ι ≫ reducedClosedSmoothPieceι q S ≫ q) := by
  have hdim : topologicalKrullDim (reducedClosedSmoothPiece q S) ≤ (d - c : ℕ) :=
    ((reducedClosedStructureMap q S).smoothLocus.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans
      (a3b4a_classSupport_dimension_le q d c S hc)
  have hlt : topologicalKrullDim (reducedClosedSmoothPiece q S) < (d - c + 1 : ℕ) :=
    hdim.trans_lt (by exact_mod_cast Nat.lt_succ_self (d - c))
  obtain ⟨U, hU, hzU, m, hm, hstd⟩ :=
    Smooth.exists_affine_relativeDimension_lt_of_topologicalKrullDim_lt
      (reducedClosedSmoothPieceι q S ≫ q) hlt z
  have hzS : reducedClosedSmoothPieceι q S z ∈ S :=
    ((reducedClosedSmoothPiece_range q S).le ⟨z, rfl⟩).1
  have hcd : c ≤ d := by
    have h := (hc _ hzS).trans
      (SmoothOfRelativeDimension.coheight_le_complex (f := q) (d := d) _)
    exact_mod_cast h
  refine ⟨U, hU, hzU, m, by omega, ?_⟩
  exact smoothOfRelativeDimension_affineOpen_of_isStandardSmooth
    (reducedClosedSmoothPieceι q S ≫ q) hU hstd

end HodgeLean.Adapters
