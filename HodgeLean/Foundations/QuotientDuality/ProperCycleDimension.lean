import HodgeLean.Foundations.QuotientDuality.ProperCycleDefs

/-! # Dimension calculations for proper cycle transfer -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

lemma properCycle_height_generic (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [LocallyOfFiniteType X.hom] :
    Order.height (genericPoint X.left) = (TopologicalSpace.dim X.left : ℕ∞) := by
  obtain ⟨-, n, hn, -⟩ := a1d_height_eq_trdeg (genericPoint X.left)
  have hd : TopologicalSpace.dim X.left = n := by
    rw [TopologicalSpace.dim_eq_krullDim, ← Order.height_top_eq_krullDim]
    change (Order.height (genericPoint X.left)).toNat = n
    rw [hn]
    rfl
  rw [hd, hn]

lemma properCycle_coheight_of_degree {X Y : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (hdim : TopologicalSpace.dim X.left = TopologicalSpace.dim Y.left)
    (x : X.left) (hd : 0 < a1p_degree f.left x) :
    Order.coheight (f.left x) = Order.coheight x := by
  have hh := (a1p_degree_pos_iff f x).mp hd
  have hx := a2r_height_add_coheight X x
  have hy := a2r_height_add_coheight Y (f.left x)
  rw [hh] at hy
  have he : Order.height x + Order.coheight (f.left x) =
      Order.height x + Order.coheight x := by
    rw [hy, hx, properCycle_height_generic X, properCycle_height_generic Y, hdim]
  obtain ⟨-, n, hn, -⟩ := a1d_height_eq_trdeg x
  rw [hn] at he
  exact WithTop.add_left_cancel (ENat.natCast_ne_top n) he

lemma properCycle_pushforward_coheight {X Y : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [QuasiCompact f.left]
    (hdim : TopologicalSpace.dim X.left = TopologicalSpace.dim Y.left)
    (γ : AlgebraicCycle X.left ℚ) (k : ℕ)
    (hc : ∀ x ∈ γ.support, Order.coheight x = k) :
    ∀ y ∈ (a1p_pushforward f.left γ).support, Order.coheight y = k := by
  intro y hy
  change a1p_pushforward f.left γ y ≠ 0 at hy
  obtain ⟨x, hxy, hx⟩ := exists_ne_zero_of_finsum_mem_ne_zero hy
  have hxy : f.left x = y := hxy
  have hc0 : γ x ≠ 0 := fun h => hx (by rw [h, zero_mul])
  have hd : 0 < a1p_degree f.left x :=
    Nat.pos_of_ne_zero fun h => hx (by simp [h])
  rw [← hxy, properCycle_coheight_of_degree f hdim x hd]
  exact hc x hc0

open scoped BigOperators

lemma properCycle_weighted_sum_coheight {X : Scheme.{0}} {I : Type} [Fintype I]
    (γ : I → AlgebraicCycle X ℚ) (q : I → ℚ) (k : ℕ)
    (hc : ∀ i x, x ∈ (γ i).support → Order.coheight x = k) :
    ∀ x ∈ (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)).support,
      Order.coheight x = k := by
  classical
  intro x hx
  change (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) x ≠ 0 at hx
  have hs : (∑ i, q i * γ i x) ≠ 0 := by
    simpa only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
      Function.locallyFinsuppWithin.mapRange_apply] using hx
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  exact hc i x (right_ne_zero_of_mul hi)

lemma properCycle_weighted_pushforward_coheight {X Y : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [QuasiCompact f.left]
    (hdim : TopologicalSpace.dim X.left = TopologicalSpace.dim Y.left)
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ) (q : I → ℚ) (k : ℕ)
    (hc : ∀ i x, x ∈ (γ i).support → Order.coheight x = k) :
    ∀ y ∈ (a1p_pushforward f.left
      (∑ i, (γ i).mapRange (q i * ·) (mul_zero _))).support,
      Order.coheight y = k :=
  properCycle_pushforward_coheight f hdim _ k (properCycle_weighted_sum_coheight γ q k hc)

end HodgeLean.Foundations.QuotientDuality
