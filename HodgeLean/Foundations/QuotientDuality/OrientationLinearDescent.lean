import HodgeLean.Foundations.QuotientDuality.OrientationDefs
import HodgeLean.Foundations.QuotientDuality.OrientationAveraging
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Universal-coefficient descent in the homology direction. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

lemma homology_surjective_of_cohomology_injective {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) (hf : Function.Injective (cohomologyMap ℚ n f)) :
    Function.Surjective (homologyMap ℚ n f) := by
  apply LinearMap.dualMap_injective_iff.mp
  intro a b hab
  let eY := cohomologyEquivDualHomology ℚ Y n
  apply eY.symm.injective
  apply hf
  apply (cohomologyEquivDualHomology ℚ X n).injective
  ext z
  have hz := LinearMap.congr_fun hab z
  simpa only [eY, cohomologyEquivDualHomology_cohomologyMap,
    LinearEquiv.apply_symm_apply, LinearMap.dualMap_apply] using hz

lemma orbit_homology_invariant_kernel (G : Type) [Group G] [Fintype G]
    (X : TopCat.{0}) [MulAction G X] [ContinuousConstSMul G X] (n : ℕ)
    (hdescent : ∀ u : Cohomology ℚ X n,
      (∀ g, deckRepresentation G X n g u = u) →
        ∃ v, cohomologyMap ℚ n (orbitMap G X) v = u)
    (z : Homology ℚ X n)
    (hfixed : ∀ g, homologyMap ℚ n (deckMap G X g) z = z)
    (hz : homologyMap ℚ n (orbitMap G X) z = 0) : z = 0 := by
  classical
  apply (Module.forall_dual_apply_eq_zero_iff ℚ z).mp
  intro φ
  let u := (cohomologyEquivDualHomology ℚ X n).symm φ
  let N := ∑ g : G, deckRepresentation G X n g u
  have hN : ∀ g, deckRepresentation G X n g N = N := by
    intro g
    simp only [N, map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun h => by
      change (deckRepresentation G X n g) ((deckRepresentation G X n h) u) =
        (deckRepresentation G X n (g * h)) u
      rw [map_mul]
      rfl)
  obtain ⟨v, hv⟩ := hdescent N hN
  have heval : cohomologyEquivDualHomology ℚ X n N z =
      (Fintype.card G : ℚ) * φ z := by
    calc
      _ = ∑ g : G, φ z := by
        simp only [N, map_sum, LinearMap.sum_apply]
        apply Finset.sum_congr rfl
        intro g _
        change cohomologyEquivDualHomology ℚ X n
          (cohomologyMap ℚ n (deckMap G X g) u) z = φ z
        rw [cohomologyEquivDualHomology_cohomologyMap, hfixed]
        exact LinearMap.congr_fun
          ((cohomologyEquivDualHomology ℚ X n).apply_symm_apply φ) z
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hzero : cohomologyEquivDualHomology ℚ X n N z = 0 := by
    rw [← hv, cohomologyEquivDualHomology_cohomologyMap, hz, map_zero]
  have hcard : (Fintype.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact (mul_eq_zero.mp (heval.symm.trans hzero)).resolve_left hcard

lemma finite_quotient_homology_invariant_kernel (G : Type) [Group G] [Fintype G]
    (X : TopCat.{0}) [MulAction G X] [ContinuousConstSMul G X] (n : ℕ)
    (Y : TopCat.{0}) (q : X ⟶ Y)
    (hdescent : ∀ u : Cohomology ℚ X n,
      (∀ g, deckRepresentation G X n g u = u) →
        ∃ v, cohomologyMap ℚ n q v = u)
    (z : Homology ℚ X n)
    (hfixed : ∀ g, homologyMap ℚ n (deckMap G X g) z = z)
    (hz : homologyMap ℚ n q z = 0) : z = 0 := by
  classical
  apply (Module.forall_dual_apply_eq_zero_iff ℚ z).mp
  intro φ
  let u := (cohomologyEquivDualHomology ℚ X n).symm φ
  let N := ∑ g : G, deckRepresentation G X n g u
  have hN : ∀ g, deckRepresentation G X n g N = N := by
    intro g
    simp only [N, map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun h => by
      change (deckRepresentation G X n g) ((deckRepresentation G X n h) u) =
        (deckRepresentation G X n (g * h)) u
      rw [map_mul]
      rfl)
  obtain ⟨v, hv⟩ := hdescent N hN
  have heval : cohomologyEquivDualHomology ℚ X n N z =
      (Fintype.card G : ℚ) * φ z := by
    calc
      _ = ∑ g : G, φ z := by
        simp only [N, map_sum, LinearMap.sum_apply]
        apply Finset.sum_congr rfl
        intro g _
        change cohomologyEquivDualHomology ℚ X n
          (cohomologyMap ℚ n (deckMap G X g) u) z = φ z
        rw [cohomologyEquivDualHomology_cohomologyMap, hfixed]
        exact LinearMap.congr_fun
          ((cohomologyEquivDualHomology ℚ X n).apply_symm_apply φ) z
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hzero : cohomologyEquivDualHomology ℚ X n N z = 0 := by
    rw [← hv, cohomologyEquivDualHomology_cohomologyMap, hz, map_zero]
  have hcard : (Fintype.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact (mul_eq_zero.mp (heval.symm.trans hzero)).resolve_left hcard


lemma homology_deck_mul (G : Type) [Group G] (X : TopCat.{0})
    [MulAction G X] [ContinuousConstSMul G X] (n : ℕ) (g h : G) (z : Homology ℚ X n) :
    homologyMap ℚ n (deckMap G X g) (homologyMap ℚ n (deckMap G X h) z) =
      homologyMap ℚ n (deckMap G X (h * g)) z := by
  have hm : deckMap G X h ≫ deckMap G X g = deckMap G X (h * g) := by
    ext x
    change g⁻¹ • (h⁻¹ • x) = (h * g)⁻¹ • x
    rw [mul_inv_rev, mul_smul]
  rw [← LinearMap.comp_apply, ← homologyMap_comp, hm]

lemma finite_quotient_homology_fixed_lift (G : Type) [Group G] [Fintype G]
    (X Y : TopCat.{0}) [MulAction G X] [ContinuousConstSMul G X]
    (q : X ⟶ Y) (hi : ∀ g, deckMap G X g ≫ q = q) (n : ℕ)
    (hsurj : Function.Surjective (homologyMap ℚ n q)) (y : Homology ℚ Y n) :
    ∃ z : Homology ℚ X n, homologyMap ℚ n q z = y ∧
      ∀ g, homologyMap ℚ n (deckMap G X g) z = z := by
  obtain ⟨x, hx⟩ := hsurj y
  let a : G → Module.End ℚ (Homology ℚ X n) := fun g => homologyMap ℚ n (deckMap G X g)
  have hmul : ∀ g h z, a g (a h z) = a (h * g) z := homology_deck_mul G X n
  have hqa : ∀ g z, homologyMap ℚ n q (a g z) = homologyMap ℚ n q z := by
    intro g z
    change homologyMap ℚ n q (homologyMap ℚ n (deckMap G X g) z) = _
    rw [← LinearMap.comp_apply, ← homologyMap_comp, hi]
  refine ⟨inverseActionAverage a x, ?_, ?_⟩
  · rw [inverseActionAverage_preserves_map a (homologyMap ℚ n q) hqa, hx]
  · intro g
    exact inverseActionAverage_fixed a hmul x g

end HodgeLean.Foundations.QuotientDuality
