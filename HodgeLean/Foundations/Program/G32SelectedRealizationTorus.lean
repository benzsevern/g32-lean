import HodgeLean.Foundations.Program.RelativeTorusKernel

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem g32y_torusHom_comp {L₁ L₂ L₃ : Type*}
    [AddCommGroup L₁] [AddCommGroup L₂] [AddCommGroup L₃]
    (F₁ : Submodule ℂ (ℂ ⊗[ℤ] L₁)) (F₂ : Submodule ℂ (ℂ ⊗[ℤ] L₂))
    (F₃ : Submodule ℂ (ℂ ⊗[ℤ] L₃)) (f : L₁ →+ L₂) (g : L₂ →+ L₃)
    (hf : F₁ ≤ F₂.comap (b2_cplxMap f)) (hg : F₂ ≤ F₃.comap (b2_cplxMap g))
    (hgf : F₁ ≤ F₃.comap (b2_cplxMap (g.comp f))) (x : b2_torus L₁ F₁) :
    b2_torusHom F₂ F₃ g hg (b2_torusHom F₁ F₂ f hf x) =
      b2_torusHom F₁ F₃ (g.comp f) hgf x := by
  induction x using QuotientAddGroup.induction_on with
  | H x =>
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      change QuotientAddGroup.mk (Submodule.Quotient.mk
        (b2_cplxMap g (b2_cplxMap f x))) =
          QuotientAddGroup.mk (Submodule.Quotient.mk (b2_cplxMap (g.comp f) x))
      congr 2
      induction x using TensorProduct.inductionOn with
      | tmul c x => rfl
      | add x y hx hy => simp only [map_add, hx, hy]

theorem g32y_torusHom_nsmul {L : Type*} [AddCommGroup L]
    (F : Submodule ℂ (ℂ ⊗[ℤ] L)) (n : ℕ)
    (hf : F ≤ F.comap (b2_cplxMap (n • AddMonoidHom.id L)))
    (x : b2_torus L F) :
    b2_torusHom F F (n • AddMonoidHom.id L) hf x = n • x := by
  have hlin : b2_cplxMap (n • AddMonoidHom.id L) = n • LinearMap.id := by
    ext c l
    simp [b2_cplxMap]
  induction x using QuotientAddGroup.induction_on with
  | H x =>
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      let Q : (ℂ ⊗[ℤ] L) →+ b2_torus L F :=
        (QuotientAddGroup.mk' _).comp F.mkQ.toAddMonoidHom
      change Q (b2_cplxMap (n • AddMonoidHom.id L) x) = n • Q x
      rw [hlin, LinearMap.smul_apply, LinearMap.id_apply]
      exact Q.map_nsmul n x

end HodgeLean.Foundations.Program
