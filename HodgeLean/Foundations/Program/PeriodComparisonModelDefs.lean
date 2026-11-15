import HodgeLean.Foundations.Program.UniversalFamilyB60bTransport

/-! # B6-4d stage 1: comparison for a B5 model

The implication from integral Riemann data to a specified complex comparison uses the
B5 period marking and the musical map of the transported form.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The polarization comparison for the theta model, with its original integral form.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §§1.2–1.3, §2.2;
B5 `b5_periodEquiv` and `b5_period_filtration`. -/
def b64d_model_homologyCohomology (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
    letI := b5_smooth Λ F hF Q hQ
    letI := b5_projective Λ F hF Q hQ
    ℂ ⊗[ℤ] Λ ≃ₗ[ℂ] ℂ ⊗[ℚ] HQ (b5_model Λ F hF Q) 1 :=
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
  letI := b5_smooth Λ F hF Q hQ
  letI := b5_projective Λ F hF Q hQ
  let X := b5_model Λ F hF Q
  let e := b5_periodEquiv Λ F hF Q hQ
  let R := b4b_transportForm Λ X e Q
  let hR := b4b_transportForm_riemann_aux Λ X e F
    (b5_period_filtration Λ F hF Q hQ) Q hQ
  let em := LinearEquiv.baseChange ℤ ℂ _ _ e.toIntLinearEquiv
  let hflat := b2bpol_flat_bijective (b2_abelianLattice X) R
    (fun u hu ↦ b2_riemannForm_nondegenerate (b2_abelianF X) R
      (b2_abelianF_isWeightOne X) hR u hu)
  let emus := LinearEquiv.ofBijective (b2bpol_musical (b2_abelianLattice X) R)
    (b2bpol_musical_bijective (b2_abelianLattice X) R hflat)
  let ep := LinearEquiv.baseChange ℚ ℂ _ _ (b60b_periodLinearEquiv X)
  em.trans (emus.trans ep.symm)

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (x : ℂ ⊗[ℤ] Λ) :
    (b64d_model_homologyCohomology Λ F hF Q hQ).symm
      (b64d_model_homologyCohomology Λ F hF Q hQ x) = x :=
  (b64d_model_homologyCohomology Λ F hF Q hQ).symm_apply_apply x

/-- Concrete inputs have rank twelve and a nonidentity lattice action. -/
example :
    Module.finrank ℤ b60_Lattice = 12 ∧
    b2_IsWeightOne b60_Lattice (b60_F 0) ∧
    b2_IsRiemannForm b60_Lattice (b60_F 0) b60_E ∧
    b60_omega ≠ LinearMap.id := by
  refine ⟨b60b_lattice_finrank, b60_weight_one ⟨0, g32m_zero_mem⟩,
    (b60_riemann_iff 0).2 g32m_zero_mem, ?_⟩
  intro h
  have he := congrArg (fun f : b60_Lattice →ₗ[ℤ] b60_Lattice ↦
    f (fun _ ↦ 1) (0, 0)) h
  norm_num [b60_omega] at he

/-- Both eigenparts of the filtration at the origin have positive dimension. -/
example :
    Module.finrank ℂ ↥(b60_F 0 ⊓ Module.End.eigenspace b60_omegaC
      (Complex.I * (Real.sqrt 3 : ℂ))) = 3 ∧
    Module.finrank ℂ ↥(b60_F 0 ⊓ Module.End.eigenspace b60_omegaC
      (-Complex.I * (Real.sqrt 3 : ℂ))) = 3 := b60_weil_dimensions 0

end HodgeLean.Foundations.Program
