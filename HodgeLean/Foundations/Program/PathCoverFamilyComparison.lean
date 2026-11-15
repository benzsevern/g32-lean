import HodgeLean.Foundations.Program.PathCoverFamilyAnalytic

noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs
open HodgeLean.Foundations HodgeLean.Foundations.Symplectic HodgeLean.Adapters TopologicalSpace
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000

section Model
variable (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
  (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
  (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q)
  (A : Λ →ₗ[ℤ] Λ) (hsq : ∀ l, A.toAddMonoidHom (A.toAddMonoidHom l) = (-3 : ℤ) • l)
  (hφ : F ≤ F.comap (b2_cplxMap A.toAddMonoidHom))
local notation "P" => b63g2_sixfold Λ F hF Q hQ A.toAddMonoidHom hsq hφ

def b65z_model_marking (m : (ℚ ⊗[ℤ] Λ) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (τ : g32m_Domain) : HQ (b60b_univ τ).X 1 ≃ₗ[ℚ] HQ (P).X 1 := by
  exact (b64e_model_rational b60_Lattice _ (b60_weight_one τ)
    b60_E ((b60_riemann_iff τ).2 τ.property)).symm.trans
      (m.symm.trans (b64e_model_rational Λ F hF Q hQ))

local notation "mark" => b65z_model_marking Λ F hF Q hQ A hsq hφ

set_option maxHeartbeats 400000 in
theorem b65z_model_marking_complexification
    (m : (ℚ ⊗[ℤ] Λ) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (τ : g32m_Domain) (x : ℂ ⊗[ℤ] b60_Lattice) :
    (mark m τ).toLinearMap.baseChange ℂ (b60b_homologyCohomologyEquiv τ x) =
      b64d_model_homologyCohomology Λ F hF Q hQ ((b64b_complexMarking Λ m).symm x) := by
  have hu := b64e_model_rational_extension b60_Lattice _ (b60_weight_one τ)
    b60_E ((b60_riemann_iff τ).2 τ.property)
  rw [eq_of_heq (b64d_model_homologyCohomology_specializes τ)] at hu
  have hr := b64e_model_rational_extension Λ F hF Q hQ
  rw [← LinearEquiv.coe_baseChange]
  unfold b65z_model_marking
  dsimp only [b60b_univ, b60b_model, b63g2_sixfold]
  rw [LinearEquiv.baseChange_trans, LinearEquiv.baseChange_trans,
    LinearEquiv.baseChange_symm, hu, hr]
  exact congrArg (fun z => b64d_model_homologyCohomology Λ F hF Q hQ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ Λ
      (LinearEquiv.baseChange ℚ ℂ _ _ m.symm
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ b60_Lattice).symm z))))
    ((b60b_homologyCohomologyEquiv τ).symm_apply_apply x)

set_option maxHeartbeats 400000 in
theorem b65z_model_marking_action
    (m : (ℚ ⊗[ℤ] Λ) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m (A.baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hskew : ∀ x y, Q (A x) y = -Q x (A y)) (τ : g32m_Domain) :
    ∀ x, mark m τ ((b60b_univ τ).W.J x) = (P).W.J (mark m τ x) := by
  let u := b60b_homologyCohomologyEquiv τ
  let r := b64d_model_homologyCohomology Λ F hF Q hQ
  let c := b64b_complexMarking Λ m
  let e := (mark m τ).toLinearMap.baseChange ℂ
  let ju := (b60b_univ τ).W.J.baseChange ℂ
  let jr := (P).W.J.baseChange ℂ
  have he (z) : e (u z) = r (c.symm z) :=
    b65z_model_marking_complexification Λ F hF Q hQ A hsq hφ m τ z
  have hu (z) : ju (u z) = -u (b60_omegaC z) := by
    rw [b60b_homologyCohomology_intertwines, neg_neg]
    rfl
  have hr (z) : r (A.baseChange ℂ z) = -jr (r z) :=
    b64d_model_homologyCohomology_intertwines Λ F hF Q hQ A.toAddMonoidHom hskew z
  have hc (z) : c.symm (b60_omegaC z) = A.baseChange ℂ (c.symm z) := by
    apply c.injective
    rw [c.apply_symm_apply]
    have h := b64b_complex_intertwines Λ A m hJ (c.symm z)
    exact (h.trans (congrArg b60_omegaC (c.apply_symm_apply z))).symm
  intro x
  apply Module.Flat.tensorProduct_mk_injective ℚ (HQ (P).X 1) ℂ
  change e (ju ((1 : ℂ) ⊗ₜ[ℚ] x)) = jr (e ((1 : ℂ) ⊗ₜ[ℚ] x))
  obtain ⟨z, hz⟩ := u.surjective ((1 : ℂ) ⊗ₜ[ℚ] x)
  rw [← hz, hu, map_neg, he, hc, hr, neg_neg, he]

set_option maxHeartbeats 400000 in
theorem b65z_model_marking_filtration
    (m : (ℚ ⊗[ℤ] Λ) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice)) (τ : g32m_Domain)
    (hchart : b60_F τ = F.map (b64b_complexMarking Λ m).toLinearMap) :
    (b60c_F (b60b_univ τ)).map ((mark m τ).toLinearMap.baseChange ℂ) = b60c_F P := by
  let u := b60b_homologyCohomologyEquiv τ
  let r := b64d_model_homologyCohomology Λ F hF Q hQ
  let c := b64b_complexMarking Λ m
  let e := (mark m τ).toLinearMap.baseChange ℂ
  have hu : (b60_F τ).map u.toLinearMap = b60c_F (b60b_univ τ) :=
    b60b_homologyCohomology_F τ
  have hr : F.map r.toLinearMap = b60c_F P :=
    b64d_model_homologyCohomology_F Λ F hF Q hQ
  have he : e.comp u.toLinearMap = r.toLinearMap.comp c.symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    exact b65z_model_marking_complexification Λ F hF Q hQ A hsq hφ m τ x
  change (b60c_F (b60b_univ τ)).map e = _
  apply Eq.trans ?_ hr
  rw [← hu, ← Submodule.map_comp, he, hchart]
  rw [Submodule.map_comp]
  have hid : c.symm.toLinearMap.comp c.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    exact c.symm_apply_apply
  have hcancel : (F.map c.toLinearMap).map c.symm.toLinearMap = F := by
    rw [← Submodule.map_comp, hid, Submodule.map_id]
  exact congrArg (Submodule.map r.toLinearMap) hcancel


end Model
end HodgeLean.Foundations.Program
