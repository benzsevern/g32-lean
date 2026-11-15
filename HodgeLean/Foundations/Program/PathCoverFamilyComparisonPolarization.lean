import HodgeLean.Foundations.Program.PathCoverFamilyComparison
import HodgeLean.Foundations.Program.PathCoverFamilyUniversalComparison

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

local notation "mark" => b65z_model_marking Λ F hF Q hQ A hsq hφ

set_option maxHeartbeats 400000 in
theorem b65z_model_nondegenerate :
    IsNondegenerate (polarizationVec (torusCohomology_cupProductOf (P).X) (P).pol) := by
  dsimp only [b63g2_sixfold, b63g_modelClass]
  exact b2_abelian_nondegenerate (P).X (b63g_modelForm Λ F hF Q hQ)
    (b63g_modelForm_riemann Λ F hF Q hQ)

set_option maxHeartbeats 400000 in
theorem b65z_model_marking_on_rational
    (m : (ℚ ⊗[ℤ] Λ) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (τ : g32m_Domain) (z : ℚ ⊗[ℤ] b60_Lattice) :
    mark m τ (b64e_model_rational b60_Lattice (b60_F τ) (b60_weight_one τ) b60_E
      ((b60_riemann_iff τ).2 τ.property) z) = b64e_model_rational Λ F hF Q hQ (m.symm z) := by
  dsimp only [b65z_model_marking, b60b_univ, b60b_model, b63g2_sixfold,
    LinearEquiv.trans_apply]
  rw [LinearEquiv.symm_apply_apply]

set_option maxHeartbeats 400000 in
theorem b65z_model_marking_dual_form
    (m : (ℚ ⊗[ℤ] Λ) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hpair : ∀ x y, b60_E.baseChange ℚ (m x) (m y) = Q.baseChange ℚ x y)
    (τ : g32m_Domain)
    (nr : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf (P).X) (P).pol)) :
    ∀ x y, HodgeLean.Foundations.Symplectic.dualForm nr (mark m τ x) (mark m τ y) =
      HodgeLean.Foundations.Symplectic.dualForm ((b60b_member τ).nondegenerate) x y := by
  let eu := b64e_model_rational b60_Lattice (b60_F τ) (b60_weight_one τ)
    b60_E ((b60_riemann_iff τ).2 τ.property)
  let er := b64e_model_rational Λ F hF Q hQ
  intro x y
  obtain ⟨a, rfl⟩ := eu.surjective x
  obtain ⟨b, rfl⟩ := eu.surjective y
  have he (z) : mark m τ (eu z) = er (m.symm z) :=
    b65z_model_marking_on_rational Λ F hF Q hQ A hsq hφ m τ z
  have hr (v w) : HodgeLean.Foundations.Symplectic.dualForm nr (er v) (er w) =
      Q.baseChange ℚ v w := b64e_model_rational_form Λ F hF Q hQ v w
  rw [he, he, hr, b65z_universal_rational_form τ a b]
  have h := hpair (m.symm a) (m.symm b)
  rw [m.apply_symm_apply, m.apply_symm_apply] at h
  exact h.symm

set_option maxHeartbeats 400000 in
set_option maxRecDepth 2000 in
theorem b65z_model_marking_polarization
    (m : (ℚ ⊗[ℤ] Λ) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hpair : ∀ x y, b60_E.baseChange ℚ (m x) (m y) = Q.baseChange ℚ x y)
    (τ : g32m_Domain) :
    exteriorPower.map 2 (mark m τ).toLinearMap
      (polarizationVec (torusCohomology_cupProductOf (b60b_univ τ).X) (b60b_univ τ).pol) =
        polarizationVec (torusCohomology_cupProductOf (P).X) (P).pol := by
  letI := (torusCohomology_cupProductOf (b60b_univ τ).X).finite
  letI := (torusCohomology_cupProductOf (P).X).finite
  exact b60c_bivector_map_of_dualForm (mark m τ) ((b60b_member τ).nondegenerate)
    (b65z_model_nondegenerate Λ F hF Q hQ A hsq hφ)
    (b65z_model_marking_dual_form Λ F hF Q hQ A hsq hφ m hpair τ
      (b65z_model_nondegenerate Λ F hF Q hQ A hsq hφ))

set_option maxHeartbeats 400000 in
theorem b65z_model_kIsog
    (m : (ℚ ⊗[ℤ] Λ) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m (A.baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hskew : ∀ x y, Q (A x) y = -Q x (A y))
    (hpair : ∀ x y, b60_E.baseChange ℚ (m x) (m y) = Q.baseChange ℚ x y)
    (τ : g32m_Domain)
    (hchart : b60_F τ = F.map (b64b_complexMarking Λ m).toLinearMap) :
    g32t_KIsog P (b60b_univ τ) := by
  obtain ⟨N, hN, f, hf, hi, _, hfJ, hfpol⟩ :=
    b60c_uniformization P τ (mark m τ)
      (b65z_model_marking_action Λ F hF Q hQ A hsq hφ m hJ hskew τ)
      (b65z_model_marking_filtration Λ F hF Q hQ A hsq hφ m τ hchart)
      (b65z_model_marking_polarization Λ F hF Q hQ A hsq hφ m hpair τ)
  refine ⟨f, hf, hi, hfJ, (N : ℚ) ^ 2, ?_, hfpol⟩
  exact pow_pos (Nat.cast_pos.mpr hN) 2

end Model
end HodgeLean.Foundations.Program
