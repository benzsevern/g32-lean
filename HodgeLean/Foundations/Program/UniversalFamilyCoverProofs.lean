import HodgeLean.Foundations.Program.UniversalFamilyB60cRoutes
import HodgeLean.Adapters.PolarizedHodgeAbelian
import HodgeLean.Foundations.HermitianClassC8

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.HermitianForm
namespace HodgeLean.Foundations.Program

theorem b60c_signature_aux (P : g32t_Sixfold) (hP : g32t_IsMember P) :
    hermSignature (b60c_H P hP) = (3, 3) := by
  exact b60c_signature_from_member P hP

theorem b60c_landherr_aux (P : g32t_Sixfold) (hP : g32t_IsMember P) :
    ∃ e : b60c_V P ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
        (Fin 6 → QuadraticAlgebra ℚ (-3) 0),
      ∀ x y, b60_H (e x) (e y) = b60c_H P hP x y := by
  let hT := torusCohomology_cupProductOf P.X
  letI := hT.finite
  have hh : (b60c_H P hP).IsSymm :=
    WeilHermitian.isSymm_weilHermitian (isAlt_polarizationForm hT hP.nondegenerate)
  have hn : (b60c_H P hP).Nondegenerate :=
    WeilHermitian.nondegenerate_weilHermitian
      (nondegenerate_polarizationForm hT hP.nondegenerate)
  have hrank : Module.finrank (QuadraticAlgebra ℚ (-3) 0) (b60c_V P) = 6 := by
    have hQ : Module.finrank ℚ (HQ P.X 1) = 12 := by
      simpa [hT, hP.dim_eq] using hT.finrank_eq
    have hK : 2 * Module.finrank (QuadraticAlgebra ℚ (-3) 0) (b60c_V P) =
        Module.finrank ℚ (HQ P.X 1) := by
      simpa [b60c_V] using WeilHermitian.finrank_withJ (b60c_J P)
    omega
  have hdet : detClass (b60c_H P hP) hh hn =
      ((Units.mk0 (-2 : ℚ) (by norm_num) : ℚˣ) :
        ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) := by
    have hd := hP.datum
    simpa [g32t_disc, weilDatumClass, WeilHermitian.weilDetClass, b60c_H, b60c_J,
      classNegTwo, hT] using hd
  simpa [b60_H] using
    (HermitianClass.hermClass_rank_six_standard (b60c_V P) (b60c_H P hP)
      hh hn hrank (b60c_signature_aux P hP) hdet)

#print axioms b60c_landherr_aux

theorem b60c_period_coordinate (P : g32t_Sixfold) (hP : g32t_IsMember P) :
    ∃ τ : g32m_Domain, ∃ e : HQ (b60b_univ τ).X 1 ≃ₗ[ℚ] HQ P.X 1,
      (∀ x, e ((b60b_univ τ).W.J x) = P.W.J (e x)) ∧
      (b60c_F (b60b_univ τ)).map (e.toLinearMap.baseChange ℂ) = b60c_F P ∧
      exteriorPower.map 2 e.toLinearMap
        (polarizationVec (torusCohomology_cupProductOf (b60b_univ τ).X) (b60b_univ τ).pol) =
        polarizationVec (torusCohomology_cupProductOf P.X) P.pol := by
  let υ : g32m_Domain := ⟨0, g32m_zero_mem⟩
  obtain ⟨eυ, heυ⟩ := b60c_landherr_aux (b60b_univ υ) (b60b_member υ)
  obtain ⟨eP, heP⟩ := b60c_landherr_aux P hP
  obtain ⟨e, hJ, hpol⟩ := b60c_marking_of_common_model (b60b_univ υ) P
    (b60b_member υ) hP eυ eP heυ heP
  exact b60c_period_of_rational_marking P hP υ e hJ hpol

theorem b60c_period_realization_aux (P : g32t_Sixfold) (hP : g32t_IsMember P) :
    ∃ τ : g32m_Domain, ∃ e : HQ (b60b_univ τ).X 1 ≃ₗ[ℚ] HQ P.X 1,
      (∀ x, e ((b60b_univ τ).W.J x) = P.W.J (e x)) ∧
      (b60c_F (b60b_univ τ)).map (e.toLinearMap.baseChange ℂ) = b60c_F P ∧
      exteriorPower.map 2 e.toLinearMap
        (polarizationVec (torusCohomology_cupProductOf (b60b_univ τ).X) (b60b_univ τ).pol) =
        polarizationVec (torusCohomology_cupProductOf P.X) P.pol := by
  exact b60c_period_coordinate P hP

theorem b60c_uniformization_aux (P : g32t_Sixfold) (τ : g32m_Domain)
    (e : HQ (b60b_univ τ).X 1 ≃ₗ[ℚ] HQ P.X 1)
    (hJ : ∀ x, e ((b60b_univ τ).W.J x) = P.W.J (e x))
    (hF : (b60c_F (b60b_univ τ)).map (e.toLinearMap.baseChange ℂ) = b60c_F P)
    (hpol : exteriorPower.map 2 e.toLinearMap
      (polarizationVec (torusCohomology_cupProductOf (b60b_univ τ).X) (b60b_univ τ).pol) =
      polarizationVec (torusCohomology_cupProductOf P.X) P.pol) :
    ∃ N : ℕ, 0 < N ∧ ∃ f : P.X ⟶ (b60b_univ τ).X,
      IsMonHom f ∧ ccm2_IsogenyOnPoints f ∧
      (∀ x, homPullback f 1 x = (N : ℚ) • e x) ∧
      (∀ x, homPullback f 1 ((b60b_univ τ).W.J x) = P.W.J (homPullback f 1 x)) ∧
      homPullback f 2 (b60b_univ τ).pol = ((N : ℚ) ^ 2) • P.pol := by
  obtain ⟨N, hN, f, hf, hfe⟩ := b60c_hodgeHom_realization P τ e hF
  have hi := b60c_isogeny_of_homPullback_equiv P τ e N hN f hf hfe
  refine ⟨N, hN, f, hf, hi, hfe, ?_,
    b60c_homPullback_polarization P τ e N f hf hfe hpol⟩
  intro x
  rw [hfe, hfe, hJ, map_smul]

set_option maxRecDepth 2000 in
theorem b60c_cover_aux (P : g32t_Sixfold) (hP : g32t_IsMember P) :
    ∃ τ : g32m_Domain, g32t_KIsog P (b60b_univ τ) := by
  obtain ⟨τ, e, hJ, hF, hpol⟩ := b60c_period_realization_aux P hP
  obtain ⟨N, hN, f, hf, hi, hfe, hfJ, hfpol⟩ :=
    b60c_uniformization_aux P τ e hJ hF hpol
  refine ⟨τ, ?_⟩
  dsimp only [g32t_KIsog]
  refine ⟨f, hf, hi, hfJ, (N : ℚ) ^ 2, ?_, hfpol⟩
  have hNq : (0 : ℚ) < N := Nat.cast_pos.mpr hN
  simpa only [pow_two] using mul_pos hNq hNq

theorem b60c_family_aux : ∃ F : g32m_UniversalFamily, F.univ = b60b_univ := by
  exact ⟨⟨b60b_univ, b60b_member, b60c_cover_aux⟩, rfl⟩

end HodgeLean.Foundations.Program
