import HodgeLean.Foundations.Program.SchoenTowerHardtCad5GraphImages

/-! Actual Boolean map graphs construct actual Boolean images of arbitrary Boolean source subsets. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_actual_image_formula {n q : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin q))
    (A : Set (EuclideanSpace ℝ (Fin n)))
    (G : s2v_t11b_Formula (n + q))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x ∈ A,
      (∀ i, z (Fin.castAdd q i) = x i) ∧
      (∀ i, z (Fin.natAdd n i) = f x i))
    (U : s2v_t11b_Formula n) (hU : U.realize ⊆ A) :
    ∃ B : s2v_t11b_Formula q, B.realize = f '' U.realize := by
  obtain ⟨B, hB⟩ := s2v_hardt_cad5_relation_image_formula U G
  refine ⟨B, ?_⟩
  ext y
  rw [hB y]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨a, _, ha, hy⟩ := (hG _).mp hx
    simp only [PiLp.toLp_apply, Fin.append_left, Fin.append_right] at ha hy
    have hxa : x.val = a := by ext i; exact ha i
    refine ⟨x.val, x.property, ?_⟩
    ext i
    rw [hxa]
    exact (hy i).symm
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx⟩, (hG _).mpr ⟨x, hU hx, ?_, ?_⟩⟩
    · intro i
      simp only [PiLp.toLp_apply, Fin.append_left]
    · intro i
      simp only [PiLp.toLp_apply, Fin.append_right]

end HodgeLean.Foundations.Program
