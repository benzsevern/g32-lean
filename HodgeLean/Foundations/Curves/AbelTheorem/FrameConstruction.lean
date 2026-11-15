import HodgeLean.Foundations.Curves.AbelTheorem.LatticeLoops
import HodgeLean.Foundations.Curves.AbelTheorem.SymplecticBasis

noncomputable section
open HodgeLean.Foundations.Program
open Module Manifold
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

theorem curve_integral_symplectic_basis (h : finrank ℂ E = 1) :
    ∃ (g : ℕ) (b : Basis (Fin g ⊕ Fin g) ℤ (b3_periodLattice E C))
      (Q : LinearMap.BilinForm ℤ (b3_periodLattice E C)),
      b3_IsIntersectionForm E Q ∧
      (∀ i j, Q (b (.inl i)) (b (.inr j)) = if i = j then 1 else 0) ∧
      (∀ i j, Q (b (.inl i)) (b (.inl j)) = 0) ∧
      (∀ i j, Q (b (.inr i)) (b (.inr j)) = 0) := by
  letI := b3_periodLattice_finite (E := E) (C := C) h
  letI := b3_periodLattice_free (E := E) (C := C)
  obtain ⟨Q, hQ⟩ := b3_exists_intersectionForm (E := E) (C := C) h
  obtain ⟨g, b, hab, haa, hbb⟩ := integral_symplectic_basis Q
    (b3_intersectionForm_isRiemannForm h Q hQ).alt
    (b3_intersectionForm_bijective h Q hQ).2
  exact ⟨g, b, Q, hQ, hab, haa, hbb⟩

theorem curve_symplectic_genus (h : finrank ℂ E = 1) {g : ℕ}
    (b : Basis (Fin g ⊕ Fin g) ℤ (b3_periodLattice E C)) :
    g = finrank ℂ (b3_HolForm E C) := by
  have hb := Module.finrank_eq_card_basis b
  rw [b3_finrank_periodLattice h] at hb
  simp only [Fintype.card_sum, Fintype.card_fin] at hb
  omega

end HodgeLean.Foundations.Curves.AbelTheorem
