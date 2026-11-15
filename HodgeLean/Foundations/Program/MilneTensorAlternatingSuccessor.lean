import HodgeLean.Foundations.Program.MilneTensorAlternatingInduction

noncomputable section
namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
theorem m1b_alternating_pair_successor {d r n : ℕ} (hd : 0 < d)
    (B : LinearMap.BilinForm ℂ (Fin d → ℂ)) (hB : B.Nondegenerate) (haB : ∀ x, B x x = 0)
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → Fin 2 ⊕ Fin d → ℂ) ℂ)
    (hf : ∀ u ∈ m1b_isometries ((m1b_prodBilin m1b_pairForm B).compl₁₂
      (m1b_pairCoordinates d).toLinearMap (m1b_pairCoordinates d).toLinearMap),
      ∀ v, f (fun t => m1b_copies r u (v t)) = f v)
    (hsmall : ∀ m (g : MultilinearMap ℂ (fun _ : Fin m => Fin r → Fin d → ℂ) ℂ),
      (∀ u ∈ m1b_isometries B, ∀ v, g (fun t => m1b_copies r u (v t)) = g v) →
      ∃ P : MvPolynomial ((Fin d × Fin d) ⊕ (Fin m × (Fin r × Fin d))) ℂ,
        ∀ (e : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d → ℂ)) (v : Fin m → Fin r → Fin d → ℂ),
          MvPolynomial.eval (Sum.elim
            (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1))
            (fun tc => v tc.1 tc.2.1 tc.2.2)) P = g (fun t c => e.symm (v t c))) :
    ∃ P : MvPolynomial (((Fin 2 ⊕ Fin d) × (Fin 2 ⊕ Fin d)) ⊕
      (Fin n × (Fin r × (Fin 2 ⊕ Fin d)))) ℂ,
      ∀ (t : (Fin 2 ⊕ Fin d → ℂ) ≃ₗ[ℂ] (Fin 2 ⊕ Fin d → ℂ))
        (v : Fin n → Fin r → Fin 2 ⊕ Fin d → ℂ),
          MvPolynomial.eval (Sum.elim
            (fun ij => m1b_formTransport ((m1b_prodBilin m1b_pairForm B).compl₁₂
              (m1b_pairCoordinates d).toLinearMap (m1b_pairCoordinates d).toLinearMap) t
              (Pi.single ij.1 1) (Pi.single ij.2 1))
            (fun tc => v tc.1 tc.2.1 tc.2.2)) P = f (fun j c => t.symm (v j c)) := by
  let c := m1b_pairCoordinates d
  let Bp := m1b_prodBilin m1b_pairForm B
  let Br := Bp.compl₁₂ c.toLinearMap c.toLinearMap
  let g := f.compLinearMap (fun _ => (m1b_copiesEquiv c r).symm.toLinearMap)
  have hb : Br.compl₁₂ c.symm.toLinearMap c.symm.toLinearMap = Bp := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change Bp (c (c.symm x)) (c (c.symm y)) = Bp x y
    simp only [LinearEquiv.apply_symm_apply]
  have hg : ∀ u ∈ m1b_isometries Bp, ∀ v,
      g (fun t => m1b_copies r u (v t)) = g v := by
    intro u hu v
    apply m1b_multilinear_invariant_transport c Br f hf u _ v
    rwa [hb]
  obtain ⟨P, hP⟩ := m1b_alternating_pair_induction_step hd B hB haB g hg hsmall
  refine ⟨P, ?_⟩
  intro t v
  have h := hP t v
  change MvPolynomial.eval _ P = f (fun j a => c.symm (c (t.symm (v j a)))) at h
  simpa only [LinearEquiv.symm_apply_apply] using h

end HodgeLean.Foundations.Program
