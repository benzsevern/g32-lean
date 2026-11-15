import HodgeLean.Foundations.QuotientDuality.PersistencePatchNeighbourhood
import HodgeLean.Foundations.QuotientDuality.PersistenceFiniteCoverPatch

/-! Actual finite patch assembly on the whole ambient space. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_finite_patch_assembly
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (A : Set X) (O : ι → Set X) (R : ι → C(X, X))
    (G : ∀ i, ContinuousMap.Homotopy (ContinuousMap.id X) (R i))
    (hO : ∀ i, IsOpen (O i)) (hcover : ∀ a ∈ A, ∃ i, a ∈ O i)
    (hG : ∀ i (t : unitInterval) a, a ∈ A → G i (t, a) = a)
    (hret : ∀ i x, x ∈ O i → R i x ∈ A) :
    ∃ N : Set X, IsOpen N ∧ A ⊆ N ∧ ∃ (r : C(X, X))
      (H : ContinuousMap.Homotopy (ContinuousMap.id X) r),
      (∀ (t : unitInterval) a, a ∈ A → H (t, a) = a) ∧ ∀ x ∈ N, r x ∈ A := by
  classical
  let l : List ι := Finset.univ.toList
  have hR : ∀ i a, a ∈ A → R i a = a := by
    intro i a ha
    have h := hG i 1 a ha
    rw [(G i).apply_one] at h
    exact h
  refine ⟨persistencePatchNeighbourhood O R l,
    persistence_patch_neighbourhood_isOpen O R hO l, ?_,
    persistencePatchComposite R l, persistencePatchCompositeHomotopy R G l,
    persistence_patch_composite_homotopy_fixed A R G hG l,
    persistence_patch_neighbourhood_endpoint A O R hR hret l⟩
  intro a ha
  obtain ⟨i, hai⟩ := hcover a ha
  exact persistence_patch_neighbourhood_contains A O R hR l a ha
    ⟨i, by simp [l], hai⟩

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint in
lemma persistence_finite_cover_closed_locus_ambient_deformation
    (W B E : Over (Spec ↧ℂ)) [IsProjective B.hom]
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ W) [IsClosedImmersion j.left] :
    let A := Set.range (Point.map j)
    ∃ N : Set (ComplexPoint W), IsOpen N ∧ A ⊆ N ∧
      ∃ (r : C(ComplexPoint W, ComplexPoint W))
        (H : ContinuousMap.Homotopy (ContinuousMap.id (ComplexPoint W)) r),
        (∀ (t : unitInterval) a, a ∈ A → H (t, a) = a) ∧ ∀ x ∈ N, r x ∈ A := by
  obtain ⟨s, O, R, G, hO, hcover, hG, hret⟩ :=
    persistence_finite_cover_closed_locus_finite_patches W B E β j
  exact persistence_finite_patch_assembly _ O R G hO hcover hG hret

end HodgeLean.Foundations.QuotientDuality
