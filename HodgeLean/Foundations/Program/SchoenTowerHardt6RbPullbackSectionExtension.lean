import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFaceSectionGraph
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSubtypeTotalExtension
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbMonicSimplexSectionExtension
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSimplexExtensionConstraint

/-! Actual root sections pulled back through base simplex maps extend with constructed Boolean graphs. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_pullback_section_extension {n m : ℕ}
    (s : Finset (EuclideanSpace ℝ (Fin n)))
    (hs : AffineIndependent ℝ ((↑) : s → EuclideanSpace ℝ (Fin n)))
    (k : convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))) → EuclideanSpace ℝ (Fin m))
    (hk : Continuous k)
    (C : Set (EuclideanSpace ℝ (Fin m))) (ψ : C → ℝ) (hψ : Continuous ψ)
    (hmaps : ∀ x : intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))),
      k ⟨x.val, intrinsicInterior_subset x.property⟩ ∈ C)
    (Q : Polynomial (MvPolynomial (Fin m) ℝ)) (hQ : Q.Monic)
    (hroot : ∀ y : C, Q.eval₂ (MvPolynomial.eval (fun i => y.val i)) (ψ y) = 0)
    (K : s2v_t11b_Formula (n + m))
    (hK : ∀ z, z ∈ K.realize ↔ ∃ x : convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))),
      (∀ i, z (Fin.castAdd m i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = k x i))
    (G : s2v_t11b_Formula (m + 1))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ y : C,
      (∀ i, z i.succ = y.val i) ∧ z 0 = ψ y) :
    ∃ g : convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))) → ℝ, Continuous g ∧
      (∀ x : intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))),
        g ⟨x.val, intrinsicInterior_subset x.property⟩ =
          ψ ⟨k ⟨x.val, intrinsicInterior_subset x.property⟩, hmaps x⟩) ∧
      (∀ x, Q.eval₂ (MvPolynomial.eval (fun i => k x i)) (g x) = 0) ∧
      ∃ R H : s2v_t11b_Formula (n + 1),
        (∀ z, z ∈ R.realize ↔
          ∃ x : intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))),
            (∀ i, z i.succ = x.val i) ∧
            z 0 = ψ ⟨k ⟨x.val, intrinsicInterior_subset x.property⟩, hmaps x⟩) ∧
        H.realize = closure R.realize ∧
        (∀ z, z ∈ H.realize ↔
          ∃ x : convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))),
            (∀ i, z i.succ = x.val i) ∧ z 0 = g x) := by
  let A := convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))
  let U := intrinsicInterior ℝ A
  let c : U → ℝ := fun x => ψ ⟨k ⟨x.val, intrinsicInterior_subset x.property⟩, hmaps x⟩
  have hki : Continuous (fun x : U => k ⟨x.val, intrinsicInterior_subset x.property⟩) :=
    hk.comp (continuous_inclusion intrinsicInterior_subset)
  have hc : Continuous c := hψ.comp (hki.subtype_mk hmaps)
  obtain ⟨f, hf, hfeq⟩ := s2v_hardt6rb_subtype_total_extension U c hc
  obtain ⟨k₀, hk₀, hkeq⟩ := s2v_hardt6rb_subtype_total_extension A
    (fun x i => k x i) ((PiLp.continuous_ofLp 2 (fun _ : Fin m => ℝ)).comp hk)
  obtain ⟨R, hR⟩ := s2v_hardt6rb_open_face_section_graph s hs k C ψ hmaps K hK G hG
  have hRf : ∀ z, z ∈ R.realize ↔ ∃ x : U,
      (∀ i, z i.succ = x.val i) ∧ z 0 = f x.val := by
    intro z
    rw [hR]
    apply exists_congr
    intro x
    rw [hfeq x]
  have hrootf : ∀ x ∈ U, Q.eval₂ (MvPolynomial.eval (k₀ x)) (f x) = 0 := by
    intro x hx
    rw [hfeq ⟨x, hx⟩, hkeq ⟨x, intrinsicInterior_subset hx⟩]
    exact hroot ⟨k ⟨x, intrinsicInterior_subset hx⟩, hmaps ⟨x, hx⟩⟩
  obtain ⟨g, hg, hagree, H, hclosure, hH⟩ :=
    s2v_hardt6rb_monic_simplex_section_extension s f hf k₀ hk₀ Q hQ hrootf R hRf
  refine ⟨g, hg, ?_, ?_, R, H, hR, hclosure, hH⟩
  · intro x
    exact (hagree x).trans (hfeq x)
  · have hr : ∀ x : A, Q.eval₂ (MvPolynomial.eval (k₀ x.val)) (g x) = 0 := by
      apply s2v_hardt6rb_simplex_extension_constraint s g hg
        (fun z => Q.eval₂ (MvPolynomial.eval (k₀ z.1)) z.2)
        (s2v_hardt6rb_polynomial_family_continuous A k₀ hk₀ Q)
      intro x
      rw [hagree x]
      exact hrootf x.val x.property
    intro x
    simpa only [hkeq x] using hr x

end HodgeLean.Foundations.Program
