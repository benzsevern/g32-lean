import HodgeLean.Foundations.Program.SchoenTowerL1bActionVectorChart

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- The centered scalar representative of a homeomorphism between
one-coordinate vector charts. -/
def s2v_l1b_action_vectorConjugacy
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (e : OpenPartialHomeomorph M (Fin 1 → ℂ))
    (d : OpenPartialHomeomorph N (Fin 1 → ℂ)) (E : M ≃ₜ N) (x : M) :
    OpenPartialHomeomorph ℂ ℂ :=
  s2v_l1b_action_centeredConjugacy (s2v_l1b_action_vectorChart_scalar e)
    (s2v_l1b_action_vectorChart_scalar d) E x

/-- Both coordinate values of the actual representative lie in their
genuine translated chart targets. -/
theorem s2v_l1b_action_vectorConjugacy_domains
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (e : OpenPartialHomeomorph M (Fin 1 → ℂ))
    (d : OpenPartialHomeomorph N (Fin 1 → ℂ)) (E : M ≃ₜ N) (x : M)
    (z : ℂ) (hz : z ∈ (s2v_l1b_action_vectorConjugacy e d E x).source) :
    b6m_surfaceCoordinateEquiv z + e x ∈ e.target ∧
      b6m_surfaceCoordinateEquiv (s2v_l1b_action_vectorConjugacy e d E x z) + d (E x) ∈ d.target := by
  have hs : z ∈ (s2v_l1b_action_centerChart (s2v_l1b_action_vectorChart_scalar e) x).target := hz.1
  have ht : s2v_l1b_action_vectorConjugacy e d E x z ∈
      (s2v_l1b_action_centerChart (s2v_l1b_action_vectorChart_scalar d) (E x)).target :=
    ((s2v_l1b_action_vectorConjugacy e d E x).map_source hz).1.1
  rw [s2v_l1b_action_vectorChart_centered_target] at hs ht
  exact ⟨hs, ht⟩

/-- The inverse-chart diagram for the actual centered homeomorphism
commutes on its genuine source. -/
theorem s2v_l1b_action_vectorConjugacy_inverse_diagram
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (e : OpenPartialHomeomorph M (Fin 1 → ℂ))
    (d : OpenPartialHomeomorph N (Fin 1 → ℂ)) (E : M ≃ₜ N) (x : M)
    (z : ℂ) (hz : z ∈ (s2v_l1b_action_vectorConjugacy e d E x).source) :
    d.symm (b6m_surfaceCoordinateEquiv (s2v_l1b_action_vectorConjugacy e d E x z) + d (E x)) =
      E (e.symm (b6m_surfaceCoordinateEquiv z + e x)) := by
  let C := s2v_l1b_action_centerChart (s2v_l1b_action_vectorChart_scalar e) x
  let D := s2v_l1b_action_centerChart (s2v_l1b_action_vectorChart_scalar d) (E x)
  have hm : E (C.symm z) ∈ D.source := hz.2.2
  have hi : D.symm (s2v_l1b_action_vectorConjugacy e d E x z) = E (C.symm z) :=
    D.left_inv hm
  dsimp only [C, D] at hi
  rw [s2v_l1b_action_vectorChart_centered_inverse,
    s2v_l1b_action_vectorChart_centered_inverse] at hi
  exact hi

end HodgeLean.Foundations.Program
