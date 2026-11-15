import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPullbackOrderedSections
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSubtypeTotalExtension

/-! Actual ordered root extensions have total representatives and Boolean graphs on the whole face hull. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_total_face_sections {n m r : ℕ}
    (s : Finset (EuclideanSpace ℝ (Fin n)))
    (hs : AffineIndependent ℝ ((↑) : s → EuclideanSpace ℝ (Fin n)))
    (k : convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))) → EuclideanSpace ℝ (Fin m))
    (hk : Continuous k)
    (C : Set (EuclideanSpace ℝ (Fin m))) (ψ : Fin r → C → ℝ)
    (hψ : ∀ j, Continuous (ψ j)) (horder : ∀ y, StrictMono (fun j => ψ j y))
    (hmaps : ∀ x : intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))),
      k ⟨x.val, intrinsicInterior_subset x.property⟩ ∈ C)
    (Q : Polynomial (MvPolynomial (Fin m) ℝ)) (hQ : Q.Monic)
    (hroot : ∀ j (y : C), Q.eval₂ (MvPolynomial.eval (fun i => y.val i)) (ψ j y) = 0)
    (K : s2v_t11b_Formula (n + m))
    (hK : ∀ z, z ∈ K.realize ↔ ∃ x : convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))),
      (∀ i, z (Fin.castAdd m i) = x.val i) ∧ (∀ i, z (Fin.natAdd n i) = k x i))
    (G : Fin r → s2v_t11b_Formula (m + 1))
    (hG : ∀ j z, z ∈ (G j).realize ↔ ∃ y : C,
      (∀ i, z i.succ = y.val i) ∧ z 0 = ψ j y) :
    ∃ f : Fin r → EuclideanSpace ℝ (Fin n) → ℝ,
    ∃ H : Fin r → s2v_t11b_Formula (n + 1),
      (∀ j, ContinuousOn (f j) (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))))) ∧
      (∀ x ∈ convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))), Monotone (fun j => f j x)) ∧
      (∀ x ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))), StrictMono (fun j => f j x)) ∧
      (∀ j (x : intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))))),
        f j x.val = ψ j ⟨k ⟨x.val, intrinsicInterior_subset x.property⟩, hmaps x⟩) ∧
      (∀ j (x : convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))),
        Q.eval₂ (MvPolynomial.eval (fun i => k x i)) (f j x.val) = 0) ∧
      (∀ j z, z ∈ (H j).realize ↔ ∃ x ∈ convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))),
        z 0 = f j x ∧ (∀ i, z i.succ = x i)) := by
  obtain ⟨g, hg, hmono, hagree, hroots, R, H, hR, hclosure, hH⟩ :=
    s2v_hardt6rb_pullback_ordered_sections s hs k hk C ψ hψ horder hmaps Q hQ hroot K hK G hG
  choose f hf he using fun j =>
    s2v_hardt6rb_subtype_total_extension _ (g j) (hg j)
  have hagree' (j : Fin r) (x : intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))))) :
      f j x.val = ψ j ⟨k ⟨x.val, intrinsicInterior_subset x.property⟩, hmaps x⟩ :=
    (he j ⟨x.val, intrinsicInterior_subset x.property⟩).trans (hagree j x)
  refine ⟨f, H, hf, ?_, ?_, hagree', ?_, ?_⟩
  · intro x hx a b hab
    change f a x ≤ f b x
    rw [he a ⟨x, hx⟩, he b ⟨x, hx⟩]
    exact hmono ⟨x, hx⟩ hab
  · intro x hx a b hab
    change f a x < f b x
    rw [hagree' a ⟨x, hx⟩, hagree' b ⟨x, hx⟩]
    exact horder _ hab
  · intro j x
    rw [he j x]
    exact hroots j x
  · intro j z
    rw [hH j z]
    constructor
    · rintro ⟨x, hx, ht⟩
      exact ⟨x.val, x.property, ht.trans (he j x).symm, hx⟩
    · rintro ⟨x, hx, ht, hz⟩
      exact ⟨⟨x, hx⟩, hz, ht.trans (he j ⟨x, hx⟩)⟩

end HodgeLean.Foundations.Program
