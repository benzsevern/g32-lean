import HodgeLean.Foundations.Program.CurveJacobianAFunctor

/-! # Track B3, side lane: integral adjoints -/

noncomputable section

open scoped TensorProduct

namespace HodgeLean.Foundations.Program

/-- A unimodular bilinear form transports the transpose of an additive map back to the lattice. -/
theorem CurveJacobianSide_exists_adjoint
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (Q : LinearMap.BilinForm ℤ M) (hQ : Function.Bijective Q)
    (Q' : LinearMap.BilinForm ℤ N) (g : M →ₗ[ℤ] N) :
    ∃ h : N →+ M, ∀ a b, Q (h a) b = Q' a (g b) := by
  let e : M ≃ₗ[ℤ] Module.Dual ℤ M := LinearEquiv.ofBijective Q hQ
  let t : N →ₗ[ℤ] Module.Dual ℤ M :=
    { toFun := fun a ↦
        { toFun := fun b ↦ Q' a (g b)
          map_add' := fun b c ↦ by rw [map_add, map_add]
          map_smul' := fun n b ↦ by
            rw [g.map_smul, (Q' a).map_smul]
            rfl }
      map_add' := fun a c ↦ by ext b; rw [map_add]; rfl
      map_smul' := fun n a ↦ by
        ext b
        simp only [LinearMap.smul_apply, RingHom.id_apply]
        exact LinearMap.congr_fun (Q'.map_smul n a) (g b) }
  let h : N →+ M := (e.symm.toLinearMap.comp t).toAddMonoidHom
  refine ⟨h, fun a b ↦ ?_⟩
  change Q (e.symm (t a)) b = Q' a (g b)
  rw [show Q (e.symm (t a)) = t a from e.apply_symm_apply (t a)]
  rfl

/-- The integral adjoint identity extends to the complexified lattices. -/
theorem CurveJacobianSide_baseChange_adjoint
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (Q : LinearMap.BilinForm ℤ M) (Q' : LinearMap.BilinForm ℤ N)
    (g : M →+ N) (h : N →+ M) (hadj : ∀ a b, Q (h a) b = Q' a (g b))
    (a : ℂ ⊗[ℤ] N) (b : ℂ ⊗[ℤ] M) :
    Q.baseChange ℂ (b2_cplxMap h a) b = Q'.baseChange ℂ a (b2_cplxMap g b) := by
  induction a using TensorProduct.inductionOn generalizing b with
  | tmul z a =>
    induction b using TensorProduct.inductionOn with
    | tmul w b =>
      rw [b2_cplxMap, b2_cplxMap, LinearMap.baseChange_tmul,
        LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul,
        LinearMap.BilinForm.baseChange_tmul]
      exact congrArg (fun n : ℤ ↦ n • (z * w)) (hadj a b)
    | add x y hx hy => simp only [map_add, hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- The right orthogonal of the Hodge filtration for a Riemann form is the filtration itself. -/
theorem CurveJacobianSide_mem_of_orthogonal
    {M : Type*} [AddCommGroup M] [Module.Free ℤ M]
    (F : Submodule ℂ (ℂ ⊗[ℤ] M)) (Q : LinearMap.BilinForm ℤ M)
    (hF : b2_IsWeightOne M F) (hQ : b2_IsRiemannForm M F Q)
    (x : ℂ ⊗[ℤ] M) (hx : ∀ y ∈ F, Q.baseChange ℂ x y = 0) : x ∈ F := by
  have hmem : x ∈ F ⊔ b2_conjSubmodule M F := hF.sup_eq_top ▸ Submodule.mem_top
  obtain ⟨f, hf, g, hg, rfl⟩ := Submodule.mem_sup.1 hmem
  have hcg : b2_conj M g ∈ F := b2a_conj_mem_of_mem_conjSubmodule hg
  have hzero : Q.baseChange ℂ (b2_conj M g) g = 0 := by
    have hx' := hx _ hcg
    rw [map_add, LinearMap.add_apply, hQ.isotropic f hf _ hcg, zero_add] at hx'
    rw [b2a_baseChange_skew Q hQ.alt, hx', neg_zero]
  have hcg0 : b2_conj M g = 0 := by
    by_contra hn
    have hp := hQ.positive _ hcg hn
    rw [b2a_conj_conj, hzero, mul_zero, Complex.zero_re] at hp
    exact lt_irrefl _ hp
  have hg0 : g = 0 := by
    rw [← b2a_conj_conj g, hcg0, map_zero]
  simpa [hg0] using hf

/-- Adjoint maps between polarized weight-one lattices preserve their Hodge filtrations. -/
theorem CurveJacobianSide_adjoint_preserves_filtration
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module.Free ℤ M]
    (F : Submodule ℂ (ℂ ⊗[ℤ] M)) (F' : Submodule ℂ (ℂ ⊗[ℤ] N))
    (Q : LinearMap.BilinForm ℤ M) (Q' : LinearMap.BilinForm ℤ N)
    (hF : b2_IsWeightOne M F) (hQ : b2_IsRiemannForm M F Q)
    (hQ' : b2_IsRiemannForm N F' Q') (g : M →+ N) (h : N →+ M)
    (hg : F ≤ F'.comap (b2_cplxMap g))
    (hadj : ∀ a b, Q (h a) b = Q' a (g b)) :
    F' ≤ F.comap (b2_cplxMap h) := by
  intro a ha
  rw [Submodule.mem_comap]
  refine CurveJacobianSide_mem_of_orthogonal F Q hF hQ _ fun b hb ↦ ?_
  rw [CurveJacobianSide_baseChange_adjoint Q Q' g h hadj]
  exact hQ'.isotropic a ha _ (hg hb)

end HodgeLean.Foundations.Program
