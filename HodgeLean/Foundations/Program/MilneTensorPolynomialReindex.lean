import HodgeLean.Foundations.Program.MilneTensorOrbitReindex

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

set_option maxHeartbeats 400000 in
theorem m1b_polynomial_extension_reindex {r n : ℕ} (e : ι ≃ κ)
    (B : LinearMap.BilinForm ℂ (κ → ℂ))
    (hpoly : ∀ g : MultilinearMap ℂ (fun _ : Fin n => Fin r → κ → ℂ) ℂ,
      (∀ u ∈ m1b_isometries B, ∀ v, g (fun t => m1b_copies r u (v t)) = g v) →
      ∃ P : MvPolynomial ((κ × κ) ⊕ (Fin n × (Fin r × κ))) ℂ,
        ∀ (s : (κ → ℂ) ≃ₗ[ℂ] (κ → ℂ)) (w : Fin n → Fin r → κ → ℂ),
          MvPolynomial.eval (Sum.elim
            (fun ij => m1b_formTransport B s (Pi.single ij.1 1) (Pi.single ij.2 1))
            (fun tc => w tc.1 tc.2.1 tc.2.2)) P = g (fun t c => s.symm (w t c)))
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → ι → ℂ) ℂ)
    (hf : ∀ u ∈ m1b_isometries (B.compl₁₂
      (LinearEquiv.funCongrLeft ℂ ℂ e).symm.toLinearMap
      (LinearEquiv.funCongrLeft ℂ ℂ e).symm.toLinearMap), ∀ v,
      f (fun t => m1b_copies r u (v t)) = f v) :
    ∃ q : MvPolynomial ((ι × ι) ⊕ (Fin n × (Fin r × ι))) ℂ,
      ∀ (t : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)) (v : Fin n → Fin r → ι → ℂ),
        MvPolynomial.eval (Sum.elim
          (fun ij => m1b_formTransport (B.compl₁₂
            (LinearEquiv.funCongrLeft ℂ ℂ e).symm.toLinearMap
            (LinearEquiv.funCongrLeft ℂ ℂ e).symm.toLinearMap) t
            (Pi.single ij.1 1) (Pi.single ij.2 1))
          (fun tc => v tc.1 tc.2.1 tc.2.2)) q = f (fun j c => t.symm (v j c)) := by
  let d := LinearEquiv.funCongrLeft ℂ ℂ e
  let Bt := B.compl₁₂ d.symm.toLinearMap d.symm.toLinearMap
  let g := f.compLinearMap (fun _ => (m1b_copiesEquiv d.symm r).symm.toLinearMap)
  have hb : Bt.compl₁₂ d.toLinearMap d.toLinearMap = B := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change B (d.symm (d x)) (d.symm (d y)) = B x y
    simp only [LinearEquiv.symm_apply_apply]
  have hg : ∀ u ∈ m1b_isometries B, ∀ v, g (fun j => m1b_copies r u (v j)) = g v := by
    intro u hu v
    apply m1b_multilinear_invariant_transport d.symm Bt f hf u _ v
    simpa only [LinearEquiv.symm_symm, hb] using hu
  obtain ⟨P, hP⟩ := hpoly g hg
  obtain ⟨q, hq⟩ := m1b_orbit_polynomial_reindex e B g P hP
  refine ⟨q, ?_⟩
  intro t v
  have h := hq t v
  change MvPolynomial.eval _ q = f (fun j c => d (d.symm (t.symm (v j c)))) at h
  simpa only [LinearEquiv.apply_symm_apply] using h

end HodgeLean.Foundations.Program
