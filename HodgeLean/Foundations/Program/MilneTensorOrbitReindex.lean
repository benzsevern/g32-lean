import HodgeLean.Foundations.Program.MilneTensorCoordinateReindex

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

set_option maxHeartbeats 400000 in
theorem m1b_orbit_polynomial_reindex {r n : ℕ} (e : ι ≃ κ)
    (B : LinearMap.BilinForm ℂ (κ → ℂ))
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → κ → ℂ) ℂ)
    (p : MvPolynomial ((κ × κ) ⊕ (Fin n × (Fin r × κ))) ℂ)
    (hp : ∀ (s : (κ → ℂ) ≃ₗ[ℂ] (κ → ℂ)) (w : Fin n → Fin r → κ → ℂ),
      MvPolynomial.eval (Sum.elim
        (fun ij => m1b_formTransport B s (Pi.single ij.1 1) (Pi.single ij.2 1))
        (fun tc => w tc.1 tc.2.1 tc.2.2)) p = f (fun j c => s.symm (w j c))) :
    ∃ q : MvPolynomial ((ι × ι) ⊕ (Fin n × (Fin r × ι))) ℂ,
      ∀ (t : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)) (v : Fin n → Fin r → ι → ℂ),
        MvPolynomial.eval (Sum.elim
          (fun ij => m1b_formTransport
            (B.compl₁₂ (LinearEquiv.funCongrLeft ℂ ℂ e).symm.toLinearMap
              (LinearEquiv.funCongrLeft ℂ ℂ e).symm.toLinearMap) t
            (Pi.single ij.1 1) (Pi.single ij.2 1))
          (fun tc => v tc.1 tc.2.1 tc.2.2)) q =
            f (fun j c => (LinearEquiv.funCongrLeft ℂ ℂ e).symm (t.symm (v j c))) := by
  let d := LinearEquiv.funCongrLeft ℂ ℂ e
  let R : ((κ × κ) ⊕ (Fin n × (Fin r × κ))) →
      ((ι × ι) ⊕ (Fin n × (Fin r × ι))) :=
    Sum.map (Prod.map e.symm e.symm) (Prod.map id (Prod.map id e.symm))
  refine ⟨MvPolynomial.rename R p, ?_⟩
  intro t v
  let s := (d.trans t).trans d.symm
  let w : Fin n → Fin r → κ → ℂ := fun j c => d.symm (v j c)
  rw [MvPolynomial.eval_rename]
  have hx :
      Sum.elim
        (fun ij => m1b_formTransport (B.compl₁₂ d.symm.toLinearMap d.symm.toLinearMap) t
          (Pi.single ij.1 1) (Pi.single ij.2 1))
        (fun tc : Fin n × (Fin r × ι) => v tc.1 tc.2.1 tc.2.2) ∘ R =
      Sum.elim (fun ij => m1b_formTransport B s (Pi.single ij.1 1) (Pi.single ij.2 1))
        (fun tc : Fin n × (Fin r × κ) => w tc.1 tc.2.1 tc.2.2) := by
    funext z
    cases z with
    | inl ij =>
      change B (d.symm (t.symm (Pi.single (e.symm ij.1) 1)))
        (d.symm (t.symm (Pi.single (e.symm ij.2) 1))) =
          B (d.symm (t.symm (d (Pi.single ij.1 1))))
            (d.symm (t.symm (d (Pi.single ij.2 1))))
      rw [m1b_coordinateReindex_basis, m1b_coordinateReindex_basis]
    | inr tc => rfl
  rw [hx, hp]
  change f (fun j c => d.symm (t.symm (d (d.symm (v j c))))) =
    f (fun j c => d.symm (t.symm (v j c)))
  simp only [LinearEquiv.apply_symm_apply]

end HodgeLean.Foundations.Program
