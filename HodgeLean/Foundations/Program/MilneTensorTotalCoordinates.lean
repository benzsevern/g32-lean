import HodgeLean.Foundations.Program.MilneTensorTotalOrbit

noncomputable section
namespace HodgeLean.Foundations.Program
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem m1b_totalOrbitExtension_coordinate_transport (e : V ≃ₗ[ℂ] W)
    (B : LinearMap.BilinForm ℂ V) {r n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → V) ℂ)
    (hf : ∀ u ∈ m1b_isometries B, ∀ v, f (fun j => m1b_copies r u (v j)) = f v)
    (Q : LinearMap.BilinForm ℂ V) (hQ : Q ∈ Set.range (m1b_formTransport B))
    (v : Fin n → Fin r → W) :
    m1b_totalOrbitExtension (B.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap)
      (f.compLinearMap (fun _ => (m1b_copiesEquiv e r).symm.toLinearMap))
      (Q.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap) v =
        m1b_totalOrbitExtension B f Q (fun j c => e.symm (v j c)) := by
  obtain ⟨d, rfl⟩ := hQ
  rw [← m1b_formTransport_conjugate e B d,
    m1b_totalOrbitExtension_eval _ _ (m1b_multilinear_invariant_transport e B f hf),
    m1b_totalOrbitExtension_eval B f hf d]
  change f (fun j c => e.symm (e (d.symm (e.symm (v j c))))) =
    f (fun j c => d.symm (e.symm (v j c)))
  simp only [LinearEquiv.symm_apply_apply]

end HodgeLean.Foundations.Program
