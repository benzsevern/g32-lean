import HodgeLean.Foundations.Program.PeriodMarkingEigen
import HodgeLean.Foundations.Program.PeriodMarkingReal

noncomputable section
open scoped TensorProduct Manifold ContDiff
open HodgeLean.Foundations.WeilHermitian HodgeLean.Foundations.HermitianForm
namespace HodgeLean.Foundations.Program

theorem b64b_signature_of_centre_ranks (M : Type*) [AddCommGroup M]
    [Module.Free ℤ M] [Module.Finite ℤ M]
    (Q : LinearMap.BilinForm ℤ M)
    (J : {J : Module.End ℚ (ℚ ⊗[ℤ] M) // J ∘ₗ J = (-3 : ℚ) • LinearMap.id})
    (hskew : ∀ x y, Q.baseChange ℚ (J.1 x) y = -Q.baseChange ℚ x (J.1 y))
    (A : M →ₗ[ℤ] M) (hA : A.baseChange ℚ = J.1)
    (F : Submodule ℂ (ℂ ⊗[ℤ] M))
    (hW : b2_IsWeightOne M F) (hR : b2_IsRiemannForm M F Q)
    (hdim : Module.finrank ℂ F = 6)
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (Z : Module.End ℂ W) (I : (ℂ ⊗[ℤ] M) →ₗ[ℂ] W) (hI : Function.Injective I)
    (hcompat : ∀ x, I (A.baseChange ℂ x) = I x + (2 : ℂ) • Z (I x))
    (hneg : Module.finrank ℂ ↥(F ⊓ (Module.End.eigenspace Z
      (star HodgeLean.Papers.g32h_omega)).comap I) = 3)
    (hpos : Module.finrank ℂ ↥(F ⊓ (Module.End.eigenspace Z
      HodgeLean.Papers.g32h_omega).comap I) = 3) :
    hermSignature (b64b_latticeH M Q J hskew) = (3, 3) := by
  have hn : Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (-Complex.I * (Real.sqrt 3 : ℂ))) = 3 := by
    rw [← b64b_conjugate_root_eigenvalue,
      b64b_eigenspace_affine_pullback _ Z I hI hcompat]
    exact hneg
  have hp : Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (Complex.I * (Real.sqrt 3 : ℂ))) = 3 := by
    rw [← b64b_root_eigenvalue, b64b_eigenspace_affine_pullback _ Z I hI hcompat]
    exact hpos
  obtain ⟨e⟩ := b64b_hermitian_real_isometry M Q J hskew A hA
  have hs := b64b_real_signature M Q A F hW hR hdim hn hp
  unfold hermSignature
  rw [QuadraticMap.Equivalent.sigPos_eq ⟨e⟩,
    QuadraticMap.Equivalent.sigNeg_eq ⟨e⟩, hs.1, hs.2]

theorem b64b_signature_of_period_data (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ : b3_IsIntersectionForm ℂ Q)
    (M : Type*) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (e : M ≃ₗ[ℤ] b63l_periodLattice C) (A : M →ₗ[ℤ] M)
    (hA : ∀ x, (e (A x)).val = b63d_periodOperator C hG (e x).val)
    (E : LinearMap.BilinForm ℤ M)
    (hE : E = (b63l_periodQ C Q).compl₁₂ e.toLinearMap e.toLinearMap)
    (J : {J : Module.End ℚ (ℚ ⊗[ℤ] M) // J ∘ₗ J = (-3 : ℚ) • LinearMap.id})
    (hAJ : A.baseChange ℚ = J.1)
    (hskew : ∀ x y, E.baseChange ℚ (J.1 x) y = -E.baseChange ℚ x (J.1 y))
    (hdim : Module.finrank ℂ (b63l_periodF C) = 6)
    (hneg : Module.finrank ℂ (b63d_eigenF C hG (star HodgeLean.Papers.g32h_omega)) = 3)
    (hpos : Module.finrank ℂ (b63d_eigenF C hG HodgeLean.Papers.g32h_omega) = 3) :
    hermSignature (b64b_latticeH M E J hskew) = (3, 3) := by
  subst E
  let eC := e.baseChange ℤ ℂ M (b63l_periodLattice C)
  let F := (b63l_periodF C).comap eC.toLinearMap
  obtain ⟨_, hW, hR⟩ := b63l_image_riemann C hG Q hQ
  have hW' := b63e_weightOne_comap e _ hW
  have hR' := b63e_riemann_comap e _ _ hR
  have hd : Module.finrank ℂ F = 6 := by
    have he := (Submodule.comap_equiv_self_of_inj_of_le (p := b63l_periodF C)
      eC.injective (by rw [LinearMap.range_eq_top.mpr eC.surjective]; exact le_top)).finrank_eq
    exact he.trans hdim
  have hn : Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (-Complex.I * (Real.sqrt 3 : ℂ))) = 3 := by
    rw [← b64b_conjugate_root_eigenvalue]
    exact (b64b_period_eigen_rank C hG e A hA _).trans hneg
  have hp : Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (Complex.I * (Real.sqrt 3 : ℂ))) = 3 := by
    rw [← b64b_root_eigenvalue]
    exact (b64b_period_eigen_rank C hG e A hA _).trans hpos
  obtain ⟨a⟩ := b64b_hermitian_real_isometry M _ J hskew A hAJ
  have hs := b64b_real_signature M _ A F hW' hR' hd hn hp
  unfold hermSignature
  rw [QuadraticMap.Equivalent.sigPos_eq ⟨a⟩,
    QuadraticMap.Equivalent.sigNeg_eq ⟨a⟩, hs.1, hs.2]

end HodgeLean.Foundations.Program
