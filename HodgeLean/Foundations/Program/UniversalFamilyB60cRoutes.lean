import HodgeLean.Foundations.Program.UniversalFamilyB60cSignature
import HodgeLean.Foundations.Program.UniversalFamilyB60cPeriod
import HodgeLean.Foundations.Program.UniversalFamilyB60cRationalPeriod
import HodgeLean.Papers.QuasiInverseDerive
import HodgeLean.Adapters.GagaMaps
import HodgeLean.Adapters.AbelianHomPullbackDegrees
import HodgeLean.Foundations.Program.UniversalFamilyB60cHom
import HodgeLean.Foundations.Program.UniversalFamilyB60cIsogeny

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.HermitianForm
namespace HodgeLean.Foundations.Program

/-- Identify the member filtration with holomorphic period classes. -/
theorem b60c_F_eq_holomorphic (P : g32t_Sixfold) :
    b60c_F P = complexHolomorphicH1 P.X := by
  change cohomologyHodgePiece P.X 1 (1, 0) = _
  rw [spec_g4_cohomologyHodgePiece_one_eq]
  simp only [latticeHodgePieces, ite_true]

/-- A rational Hodge equivalence between two abelian varieties has a positive integral multiple
realized by an algebraic group homomorphism. -/
theorem b60c_hodgeHom_realization (P : g32t_Sixfold) (τ : g32m_Domain)
    (e : HQ (b60b_univ τ).X 1 ≃ₗ[ℚ] HQ P.X 1)
    (hF : (b60c_F (b60b_univ τ)).map (e.toLinearMap.baseChange ℂ) = b60c_F P) :
    ∃ N : ℕ, 0 < N ∧ ∃ f : P.X ⟶ (b60b_univ τ).X,
      IsMonHom f ∧ (∀ x, homPullback f 1 x = (N : ℚ) • e x) := by
  rw [b60c_F_eq_holomorphic, b60c_F_eq_holomorphic] at hF
  obtain ⟨N, hN, f, hf, h⟩ :=
    b60c_hom_of_holomorphic P.X (b60b_univ τ).X e.toLinearMap hF.le
  exact ⟨N, hN, f, hf, fun x => LinearMap.congr_fun h x⟩

#print axioms b60c_hodgeHom_realization

/-- A homomorphism whose degree-one pullback is a nonzero multiple of an equivalence is an
isogeny on complex points. -/
theorem b60c_isogeny_of_homPullback_equiv (P : g32t_Sixfold) (τ : g32m_Domain)
    (e : HQ (b60b_univ τ).X 1 ≃ₗ[ℚ] HQ P.X 1) (N : ℕ) (hN : 0 < N)
    (f : P.X ⟶ (b60b_univ τ).X) (hf : IsMonHom f)
    (hfe : ∀ x, homPullback f 1 x = (N : ℚ) • e x) :
    ccm2_IsogenyOnPoints f := by
  haveI : IsMonHom f := hf
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hb : Function.Bijective (homPullback f 1) := by
    constructor
    · intro x y h
      apply e.injective
      rw [hfe, hfe] at h
      exact (smul_right_injective _ hNq) h
    · intro y
      refine ⟨e.symm ((N : ℚ)⁻¹ • y), ?_⟩
      rw [hfe, e.apply_symm_apply, smul_smul, mul_inv_cancel₀ hNq, one_smul]
  exact b60c_isogeny_of_equiv P.X (b60b_univ τ).X f
    (LinearEquiv.ofBijective (homPullback f 1) hb) rfl

#print axioms b60c_isogeny_of_homPullback_equiv

set_option maxRecDepth 10000
/-- Degree-two pullback is the exterior square of degree-one pullback under the torus
cohomology comparison. -/
theorem b60c_homPullback_polarization (P : g32t_Sixfold) (τ : g32m_Domain)
    (e : HQ (b60b_univ τ).X 1 ≃ₗ[ℚ] HQ P.X 1) (N : ℕ)
    (f : P.X ⟶ (b60b_univ τ).X) (hf : IsMonHom f)
    (hfe : ∀ x, homPullback f 1 x = (N : ℚ) • e x)
    (hpol : exteriorPower.map 2 e.toLinearMap
      (polarizationVec (torusCohomology_cupProductOf (b60b_univ τ).X) (b60b_univ τ).pol) =
      polarizationVec (torusCohomology_cupProductOf P.X) P.pol) :
    homPullback f 2 (b60b_univ τ).pol = ((N : ℚ) ^ 2) • P.pol := by
  let X := (b60b_univ τ).X
  let hTX := torusCohomology_cupProductOf X
  let hTP := torusCohomology_cupProductOf P.X
  have hmap : homPullback f 1 = (N : ℚ) • e.toLinearMap := by
    ext x
    exact hfe x
  rw [spec_homPullback_eq_cupWedgeEquiv f 2, LinearMap.comp_apply,
    LinearMap.comp_apply]
  change hTP.cupWedgeEquiv 2
      (exteriorPower.map 2 (homPullback f 1) (polarizationVec hTX (b60b_univ τ).pol)) = _
  rw [hmap, exteriorPower_map_smul, LinearMap.smul_apply, hpol, map_smul,
    polarizationVec, LinearEquiv.apply_symm_apply]

end HodgeLean.Foundations.Program
