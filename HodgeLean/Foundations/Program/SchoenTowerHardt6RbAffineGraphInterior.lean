import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAffineInteriorImage

/-! Intrinsic interiors of affine graph carriers, including wholly collapsed bands. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_affine_graph_interior {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C : Set E) (hC : Convex ℝ C) (l : E →ᵃ[ℝ] ℝ) :
    intrinsicInterior ℝ {p : E × ℝ | p.1 ∈ C ∧ p.2 = l p.1} =
      {p : E × ℝ | p.1 ∈ intrinsicInterior ℝ C ∧ p.2 = l p.1} := by
  let f : E →ᵃ[ℝ] E × ℝ := (AffineMap.id ℝ E).prod l
  let g : E × ℝ →ᵃ[ℝ] E := (LinearMap.fst ℝ E ℝ).toAffineMap
  let G : Set (E × ℝ) := {p | p.1 ∈ C ∧ p.2 = l p.1}
  have hf : f '' C = G := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, rfl⟩
    · rintro ⟨hp, he⟩
      exact ⟨p.1, hp, Prod.ext rfl he.symm⟩
  have hg : g '' G = C := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp.1
    · intro hx
      exact ⟨(x, l x), ⟨hx, rfl⟩, rfl⟩
  ext p
  constructor
  · intro hp
    have hx := s2v_hardt6rb_affine_interior_image G g (hg.symm ▸ hC) hp
    rw [hg] at hx
    exact ⟨hx, (intrinsicInterior_subset hp).2⟩
  · rintro ⟨hp, he⟩
    have hx := s2v_hardt6rb_affine_interior_image C f (hC.affine_image f) hp
    rw [hf] at hx
    have hp' : f p.1 = p := Prod.ext rfl he.symm
    exact hp' ▸ hx

end HodgeLean.Foundations.Program
