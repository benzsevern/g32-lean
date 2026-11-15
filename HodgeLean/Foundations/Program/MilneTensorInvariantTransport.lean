import HodgeLean.Foundations.Program.MilneTensorOrbit

noncomputable section
namespace HodgeLean.Foundations.Program
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem m1b_multilinear_invariant_transport (e : V ≃ₗ[ℂ] W)
    (B : LinearMap.BilinForm ℂ V) {r n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → V) ℂ)
    (hf : ∀ u ∈ m1b_isometries B, ∀ v, f (fun i => m1b_copies r u (v i)) = f v)
    (u : W →ₗ[ℂ] W)
    (hu : u ∈ m1b_isometries (B.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap))
    (v : Fin n → Fin r → W) :
    (f.compLinearMap (fun _ => (m1b_copiesEquiv e r).symm.toLinearMap))
      (fun i => m1b_copies r u (v i)) =
      (f.compLinearMap (fun _ => (m1b_copiesEquiv e r).symm.toLinearMap)) v := by
  rw [← m1b_isometries_conj e B] at hu
  obtain ⟨g, hg, rfl⟩ := hu
  have h := hf g hg (fun i c => e.symm (v i c))
  change f (fun i c => g (e.symm (v i c))) = f (fun i c => e.symm (v i c)) at h
  change f (fun i c => e.symm (e (g (e.symm (v i c))))) =
    f (fun i c => e.symm (v i c))
  simpa only [LinearEquiv.symm_apply_apply] using h

theorem m1b_formTransport_conjugate (e : V ≃ₗ[ℂ] W)
    (B : LinearMap.BilinForm ℂ V) (d : V ≃ₗ[ℂ] V) :
    m1b_formTransport (B.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap)
      ((e.symm.trans d).trans e) =
        (m1b_formTransport B d).compl₁₂ e.symm.toLinearMap e.symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change B (e.symm (e (d.symm (e.symm x)))) (e.symm (e (d.symm (e.symm y)))) =
    B (d.symm (e.symm x)) (d.symm (e.symm y))
  simp only [LinearEquiv.symm_apply_apply]

theorem m1b_orbitExtension_coordinate_transport (e : V ≃ₗ[ℂ] W)
    (B : LinearMap.BilinForm ℂ V) {r n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → V) ℂ)
    (hf : ∀ u ∈ m1b_isometries B, ∀ v, f (fun i => m1b_copies r u (v i)) = f v)
    (d : V ≃ₗ[ℂ] V) (v : Fin n → Fin r → V) :
    m1b_orbitExtension (B.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap)
      (f.compLinearMap (fun _ => (m1b_copiesEquiv e r).symm.toLinearMap))
      ⟨m1b_formTransport (B.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap)
        ((e.symm.trans d).trans e), ⟨((e.symm.trans d).trans e), rfl⟩⟩
      (fun i c => e (v i c)) =
        m1b_orbitExtension B f ⟨m1b_formTransport B d, ⟨d, rfl⟩⟩ v := by
  rw [m1b_orbitExtension_eval _ _ (m1b_multilinear_invariant_transport e B f hf) _
    ((e.symm.trans d).trans e) rfl,
    m1b_orbitExtension_eval B f hf _ d rfl]
  change f (fun i c => e.symm (e (d.symm (e.symm (e (v i c)))))) =
    f (fun i c => d.symm (v i c))
  simp only [LinearEquiv.symm_apply_apply]

end HodgeLean.Foundations.Program
