import HodgeLean.Foundations.Program.MilneTensorOrbitReindex

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

set_option maxHeartbeats 400000 in
theorem m1b_standard_polynomial_extension_reindex {r n : ℕ} (e : ι ≃ κ)
    (hpoly : ∀ g : MultilinearMap ℂ (fun _ : Fin n => Fin r → κ → ℂ) ℂ,
      (∀ u ∈ m1b_isometries (1 : Matrix κ κ ℂ).toBilin', ∀ v,
        g (fun t => m1b_copies r u (v t)) = g v) →
      ∃ P : MvPolynomial ((κ × κ) ⊕ (Fin n × (Fin r × κ))) ℂ,
        ∀ (s : (κ → ℂ) ≃ₗ[ℂ] (κ → ℂ)) (w : Fin n → Fin r → κ → ℂ),
          MvPolynomial.eval (Sum.elim
            (fun ij => m1b_formTransport (1 : Matrix κ κ ℂ).toBilin' s
              (Pi.single ij.1 1) (Pi.single ij.2 1))
            (fun tc => w tc.1 tc.2.1 tc.2.2)) P = g (fun t c => s.symm (w t c)))
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → ι → ℂ) ℂ)
    (hf : ∀ u ∈ m1b_isometries (1 : Matrix ι ι ℂ).toBilin', ∀ v,
      f (fun t => m1b_copies r u (v t)) = f v) :
    ∃ q : MvPolynomial ((ι × ι) ⊕ (Fin n × (Fin r × ι))) ℂ,
      ∀ (t : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)) (v : Fin n → Fin r → ι → ℂ),
        MvPolynomial.eval (Sum.elim
          (fun ij => m1b_formTransport (1 : Matrix ι ι ℂ).toBilin' t
            (Pi.single ij.1 1) (Pi.single ij.2 1))
          (fun tc => v tc.1 tc.2.1 tc.2.2)) q = f (fun j c => t.symm (v j c)) := by
  let d := LinearEquiv.funCongrLeft ℂ ℂ e
  let g := f.compLinearMap (fun _ => (m1b_copiesEquiv d.symm r).symm.toLinearMap)
  have hb : (1 : Matrix ι ι ℂ).toBilin'.compl₁₂ d.toLinearMap d.toLinearMap =
      (1 : Matrix κ κ ℂ).toBilin' := m1b_coordinateReindex_standard e.symm
  have hg : ∀ u ∈ m1b_isometries (1 : Matrix κ κ ℂ).toBilin', ∀ v,
      g (fun j => m1b_copies r u (v j)) = g v := by
    intro u hu v
    apply m1b_multilinear_invariant_transport d.symm (1 : Matrix ι ι ℂ).toBilin' f hf u _ v
    simpa only [LinearEquiv.symm_symm, hb] using hu
  obtain ⟨P, hP⟩ := hpoly g hg
  obtain ⟨q, hq⟩ := m1b_orbit_polynomial_reindex e (1 : Matrix κ κ ℂ).toBilin' g P hP
  rw [m1b_coordinateReindex_standard] at hq
  refine ⟨q, ?_⟩
  intro t v
  have h := hq t v
  change MvPolynomial.eval _ q = f (fun j c => d (d.symm (t.symm (v j c)))) at h
  simpa only [LinearEquiv.apply_symm_apply] using h

end HodgeLean.Foundations.Program
