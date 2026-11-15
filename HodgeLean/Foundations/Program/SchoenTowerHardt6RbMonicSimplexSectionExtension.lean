import HodgeLean.Foundations.Program.SchoenTowerHardt6RbMonicRootBound

/-! Monic polynomial families supply nonzero specializations at every simplex boundary point. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_monic_simplex_section_extension {n m : ℕ}
    (s : Finset (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContinuousOn f (intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))))))
    (k : EuclideanSpace ℝ (Fin n) → Fin m → ℝ)
    (hk : ContinuousOn k (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))))
    (Q : Polynomial (MvPolynomial (Fin m) ℝ)) (hQ : Q.Monic)
    (hroot : ∀ x ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))),
      Q.eval₂ (MvPolynomial.eval (k x)) (f x) = 0)
    (G : s2v_t11b_Formula (n + 1))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))),
      (∀ i, z i.succ = x.val i) ∧ z 0 = f x.val) :
    ∃ g : convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))) → ℝ, Continuous g ∧
      (∀ x : intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))),
        g ⟨x.val, intrinsicInterior_subset x.property⟩ = f x.val) ∧
      ∃ H : s2v_t11b_Formula (n + 1), H.realize = closure G.realize ∧
        ∀ z, z ∈ H.realize ↔ ∃ a : convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))),
          (∀ i, z i.succ = a.val i) ∧ z 0 = g a := by
  obtain ⟨b, hb⟩ := s2v_hardt6rb_monic_root_bound _
    (s.finite_toSet.isCompact_convexHull ℝ) k hk Q hQ
  have hbound : ∀ x ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))),
      f x ∈ Set.Icc (-b) b := fun x hx => hb x (intrinsicInterior_subset hx) (f x) (hroot x hx)
  apply s2v_hardt6rb_simplex_section_graph_extension s f hf (-b) b hbound
    (fun z => Q.eval₂ (MvPolynomial.eval (k z.1)) z.2)
    (s2v_hardt6rb_polynomial_family_continuous _ k hk Q) hroot ?_ G hG
  intro a ha
  refine ⟨Q.map (MvPolynomial.eval (k a)), Polynomial.map_monic_ne_zero hQ, ?_⟩
  intro t
  exact Polynomial.eval₂_eq_eval_map _

end HodgeLean.Foundations.Program
