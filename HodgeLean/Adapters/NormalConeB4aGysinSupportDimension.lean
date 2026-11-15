import HodgeLean.Adapters.NormalConeB4aClassDimension

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- An algebraic ambient dimension bound and a support codimension bound give
the corresponding reduced support dimension bound, without smoothness. -/
theorem a3b4a_gysin_support_dimension_of_ambient_bound
    {Z : Scheme.{0}} (D c : ℕ) (S : Closeds Z)
    (hD : topologicalKrullDim Z ≤ (D : ℕ))
    (hc : ∀ z ∈ S, (c : ℕ∞) ≤ Order.coheight z) :
    topologicalKrullDim (reducedClosedSubscheme S) ≤ (D - c : ℕ) := by
  rw [Scheme.topologicalKrullDim_eq_orderKrullDim] at hD ⊢
  let f := reducedClosedSubschemeι S
  have hiff (a b : reducedClosedSubscheme S) : f a ≤ f b ↔ a ≤ b := by
    rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
    exact f.isClosedEmbedding.isInducing.specializes_iff
  have hstrict : StrictMono f := fun a b hab =>
    lt_iff_le_not_ge.mpr ⟨(hiff a b).mpr hab.le, fun h => hab.not_ge ((hiff b a).mp h)⟩
  have hheight (a : reducedClosedSubscheme S) : Order.height (f a) ≤ D - c := by
    have haS : f a ∈ S := (range_reducedClosedSubschemeι S).le ⟨a, rfl⟩
    haveI : Nonempty Z := ⟨f a⟩
    have hpoint : (↑(Order.height (f a) + Order.coheight (f a)) : WithBot ℕ∞) ≤
        Order.krullDim Z := by
      rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
      exact WithBot.coe_le_coe.mpr (le_iSup
        (fun z : Z => Order.height z + Order.coheight z) (f a))
    apply ENat.le_sub_of_add_le_right (by simp)
    calc
      Order.height (f a) + c ≤ Order.height (f a) + Order.coheight (f a) :=
        add_le_add le_rfl (hc _ haS)
      _ ≤ D := WithBot.coe_le_coe.mp (hpoint.trans hD)
  cases isEmpty_or_nonempty (reducedClosedSubscheme S) with
  | inl h =>
    rw [Order.krullDim_eq_bot]
    exact bot_le
  | inr h =>
    rw [Order.krullDim_eq_iSup_length]
    apply WithBot.coe_le_coe.mpr
    refine iSup_le fun l => ?_
    exact (Order.length_le_height_last (p := l.map f hstrict)).trans (hheight l.last)

/-- Smooth support pieces have affine parameter neighborhoods with the expected
upper dimension bound whenever the ambient algebraic dimension is bounded. -/
theorem a3b4a_gysin_support_piece_affine_dimension_bound
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q]
    (D c : ℕ) (S : Closeds Z) (hD : topologicalKrullDim Z ≤ (D : ℕ))
    (hc : ∀ z ∈ S, (c : ℕ∞) ≤ Order.coheight z)
    (z : reducedClosedSmoothPiece q S) :
    ∃ (U : (reducedClosedSmoothPiece q S).Opens) (_ : IsAffineOpen U), z ∈ U ∧
      ∃ m : ℕ, m ≤ D - c ∧
        SmoothOfRelativeDimension m (U.ι ≫ reducedClosedSmoothPieceι q S ≫ q) := by
  have hdim : topologicalKrullDim (reducedClosedSmoothPiece q S) ≤ (D - c : ℕ) :=
    ((reducedClosedStructureMap q S).smoothLocus.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans
      (a3b4a_gysin_support_dimension_of_ambient_bound D c S hD hc)
  have hlt : topologicalKrullDim (reducedClosedSmoothPiece q S) < (D - c + 1 : ℕ) :=
    hdim.trans_lt (by exact_mod_cast Nat.lt_succ_self (D - c))
  obtain ⟨U, hU, hzU, m, hm, hstd⟩ :=
    Smooth.exists_affine_relativeDimension_lt_of_topologicalKrullDim_lt
      (reducedClosedSmoothPieceι q S ≫ q) hlt z
  refine ⟨U, hU, hzU, m, by omega, ?_⟩
  exact smoothOfRelativeDimension_affineOpen_of_isStandardSmooth
    (reducedClosedSmoothPieceι q S ≫ q) hU hstd

end HodgeLean.Adapters
