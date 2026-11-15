import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPullbackSectionExtension
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSimplexExtensionOrder

/-! Actual ordered CAD sections pull back and extend simultaneously over a base simplex. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_pullback_ordered_sections {n m r : ℕ}
    (s : Finset (EuclideanSpace ℝ (Fin n)))
    (hs : AffineIndependent ℝ ((↑) : s → EuclideanSpace ℝ (Fin n)))
    (k : convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))) → EuclideanSpace ℝ (Fin m))
    (hk : Continuous k)
    (C : Set (EuclideanSpace ℝ (Fin m))) (ψ : Fin r → C → ℝ) (hψ : ∀ j, Continuous (ψ j))
    (horder : ∀ y, StrictMono (fun j => ψ j y))
    (hmaps : ∀ x : intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))),
      k ⟨x.val, intrinsicInterior_subset x.property⟩ ∈ C)
    (Q : Polynomial (MvPolynomial (Fin m) ℝ)) (hQ : Q.Monic)
    (hroot : ∀ j (y : C), Q.eval₂ (MvPolynomial.eval (fun i => y.val i)) (ψ j y) = 0)
    (K : s2v_t11b_Formula (n + m))
    (hK : ∀ z, z ∈ K.realize ↔ ∃ x : convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))),
      (∀ i, z (Fin.castAdd m i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = k x i))
    (G : Fin r → s2v_t11b_Formula (m + 1))
    (hG : ∀ j z, z ∈ (G j).realize ↔ ∃ y : C,
      (∀ i, z i.succ = y.val i) ∧ z 0 = ψ j y) :
    ∃ g : Fin r → convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))) → ℝ, (∀ j, Continuous (g j)) ∧
      (∀ x, Monotone (fun j => g j x)) ∧
      (∀ j (x : intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))))),
        g j ⟨x.val, intrinsicInterior_subset x.property⟩ =
          ψ j ⟨k ⟨x.val, intrinsicInterior_subset x.property⟩, hmaps x⟩) ∧
      (∀ j x, Q.eval₂ (MvPolynomial.eval (fun i => k x i)) (g j x) = 0) ∧
      ∃ R H : Fin r → s2v_t11b_Formula (n + 1),
        (∀ j z, z ∈ (R j).realize ↔
          ∃ x : intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))),
            (∀ i, z i.succ = x.val i) ∧
            z 0 = ψ j ⟨k ⟨x.val, intrinsicInterior_subset x.property⟩, hmaps x⟩) ∧
        (∀ j, (H j).realize = closure (R j).realize) ∧
        (∀ j z, z ∈ (H j).realize ↔
          ∃ x : convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))),
            (∀ i, z i.succ = x.val i) ∧ z 0 = g j x) := by
  choose g hg hagree hroots R H hR hclosure hH using fun j =>
    s2v_hardt6rb_pullback_section_extension s hs k hk C (ψ j) (hψ j) hmaps Q hQ
      (hroot j) K hK (G j) (hG j)
  refine ⟨g, hg, ?_, hagree, hroots, R, H, hR, hclosure, hH⟩
  intro x i j hij
  apply s2v_hardt6rb_simplex_extension_order s (g i) (g j) (hg i) (hg j) ?_ x
  intro y
  rw [hagree i y, hagree j y]
  exact (horder _).monotone hij

end HodgeLean.Foundations.Program
