import HodgeLean.Foundations.Program.UniversalFamilyB60cFixedChart

noncomputable section
open scoped TensorProduct Matrix ComplexOrder
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

/-- The Riemann relations and balanced eigenspaces reconstruct the fixed bounded chart. -/
theorem b60c_fixed_filtration_chart
    (F : Submodule ℂ (ℂ ⊗[ℤ] b60_Lattice))
    (hdim : Module.finrank ℂ F = 6)
    (hneg : Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace b60_omegaC
      (-Complex.I * (Real.sqrt 3 : ℂ))) = 3)
    (hpos : Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace b60_omegaC
      (Complex.I * (Real.sqrt 3 : ℂ))) = 3)
    (hR : b2_IsRiemannForm b60_Lattice F b60_E) :
    ∃ τ : g32m_Domain, F = b60_F τ := by
  classical
  let N := F ⊓ Module.End.eigenspace b60_omegaC (-Complex.I * (Real.sqrt 3 : ℂ))
  let P := F ⊓ Module.End.eigenspace b60_omegaC (Complex.I * (Real.sqrt 3 : ℂ))
  obtain ⟨A, hA, hN⟩ := b60c_negative_plane_graph N hneg inf_le_right
    (fun x hx hne => hR.positive x hx.1 hne)
  let z := b60c_matrixCoordinates A
  have hz : g32m_toMat z = A := b60c_toMat_matrixCoordinates A
  have hzmem : z ∈ g32m_Domain := by
    change z ∈ (g32m_Domain : Set (Fin 9 → ℂ))
    rw [g32m_domain_coe]
    change (1 - (g32m_toMat z)ᴴ * g32m_toMat z).PosDef
    rwa [hz]
  let τ : g32m_Domain := ⟨z, hzmem⟩
  let G := Submodule.span ℂ (Set.range fun i : Fin 3 => b60_frame z (1, i))
  have hnframe (i : Fin 3) : b60_frame z (0, i) ∈ N := by
    rw [hN]
    simpa [b60_frame, hz] using (Submodule.subset_span
      (show b60_eigen (-1) (Fin.castAdd 3 i) +
        ∑ j : Fin 3, A j i • b60_eigen (-1) (Fin.natAdd 3 j) ∈
        Set.range (fun i : Fin 3 => b60_eigen (-1) (Fin.castAdd 3 i) +
          ∑ j : Fin 3, A j i • b60_eigen (-1) (Fin.natAdd 3 j)) from ⟨i, rfl⟩))
  have hple : P ≤ G := by
    intro x hx
    have hxe := Module.End.mem_eigenspace_iff.mp hx.2
    have hiso (i : Fin 3) : b60_E.baseChange ℂ
        (b60_eigen (-1) (Fin.castAdd 3 i) +
          ∑ j : Fin 3, A j i • b60_eigen (-1) (Fin.natAdd 3 j)) x = 0 := by
      simpa [b60_frame, hz] using hR.isotropic _ (hnframe i).1 x hx.1
    have heq := b60c_opposite_graph_equations A x hxe hiso
    rw [b60c_positive_graph_reconstruction A x hxe heq]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    have hg : b60_frame z (1, j) ∈ G := Submodule.subset_span ⟨j, rfl⟩
    simpa [b60_frame, hz] using hg
  have hgdim : Module.finrank ℂ G = 3 := by
    have hli : LinearIndependent ℂ (fun i : Fin 3 => b60_frame z (1, i)) := by
      simpa only [Function.comp_def] using (b60_frame_independent z).comp
        (fun i : Fin 3 => (1, i)) (by intro i j h; exact congrArg Prod.snd h)
    simpa only [Fintype.card_fin] using finrank_span_eq_card hli
  have hpEq : P = G := Submodule.eq_of_le_of_finrank_eq hple (hpos.trans hgdim.symm)
  have hle : b60_F z ≤ F := by
    rw [b60_F, Submodule.span_le]
    rintro _ ⟨⟨a, i⟩, rfl⟩
    fin_cases a
    · exact (hnframe i).1
    · have hg : b60_frame z (1, i) ∈ G := Submodule.subset_span ⟨i, rfl⟩
      rw [← hpEq] at hg
      exact hg.1
  refine ⟨τ, (Submodule.eq_of_le_of_finrank_eq hle ?_).symm⟩
  rw [hdim, b60_F, finrank_span_eq_card (b60_frame_independent z)]
  decide

#print axioms b60c_fixed_filtration_chart

end HodgeLean.Foundations.Program
