import HodgeLean.Foundations.Program.PrymVariationCentreDefs

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

theorem b63d_centre_transport_helper (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    (s : V) (x : b6m_H1 (b63l_parameterFibre b C V hV s)) :
    b6m_H1Equiv (b6m_transport b C ⟨s.val, hV s.property⟩ ⟨t.val, hV t.property⟩)
      (b63d_centre b C hC V hV s x) =
    b63d_centre b C hC V hV t
      (b6m_H1Equiv (b6m_transport b C ⟨s.val, hV s.property⟩ ⟨t.val, hV t.property⟩) x) := by
  classical
  simp only [b63d_centre, LinearMap.sum_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro g hg
  split_ifs with h
  · exact (b6m_homology_equivariant b b4b_Group C hC
      ⟨s.val, hV s.property⟩ ⟨t.val, hV t.property⟩ g x).2
  · simp

end HodgeLean.Foundations.Program
