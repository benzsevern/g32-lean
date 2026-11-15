import HodgeLean.Foundations.Program.SchoenCycleAffineFormalPullback

/-! # Affine adic bijections from the actual formal stalk pullback -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Bijectivity of the actual geometric formal pullback transports to the
canonical adic map of the specified affine section algebras. -/
theorem s2e_c1_affine_adic_bijective_of_formal_pullback
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    (f : X ⟶ Y) [IsFinite f.left]
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    (x : X.left) (hx : x ∈ f.left ⁻¹ᵁ U)
    (hcx : IsClosed ({x} : Set X.left)) (hcy : IsClosed ({f.left x} : Set Y.left))
    (hbij : Function.Bijective (s2e_formal_stalk_pullback X Y f x)) :
    let W := f.left ⁻¹ᵁ U
    letI := s2e_step1_sectionAlgebra Y U
    letI := s2e_step1_sectionAlgebra X W
    letI : Algebra Γ(Y.left, U) Γ(X.left, W) := (f.left.app U).hom.toAlgebra
    letI := s2e_complex_section_app_tower X Y f U
    letI : Algebra ℂ (X.left.presheaf.stalk x) := (HodgeLean.Foundations.Curves.stalkC x).toAlgebra
    letI : Algebra ℂ (Y.left.presheaf.stalk (f.left x)) :=
      (HodgeLean.Foundations.Curves.stalkC (f.left x)).toAlgebra
    let p := (hU.primeIdealOf ⟨f.left x, hx⟩).asIdeal
    let I := ((hU.preimage f.left).primeIdealOf ⟨x, hx⟩).asIdeal
    let φ := (Algebra.ofId Γ(Y.left, U) Γ(X.left, W)).restrictScalars ℂ
    ∃ hφ : ∀ N a, a ∈ p ^ N → φ a ∈ I ^ N,
      Function.Bijective (s2e_adic_algebra_map p I φ hφ) := by
  dsimp only
  let W := f.left ⁻¹ᵁ U
  letI := s2e_step1_sectionAlgebra Y U
  letI := s2e_step1_sectionAlgebra X W
  letI : Algebra Γ(Y.left, U) Γ(X.left, W) := (f.left.app U).hom.toAlgebra
  letI := s2e_complex_section_app_tower X Y f U
  letI : Algebra ℂ (X.left.presheaf.stalk x) := (HodgeLean.Foundations.Curves.stalkC x).toAlgebra
  letI : Algebra ℂ (Y.left.presheaf.stalk (f.left x)) :=
    (HodgeLean.Foundations.Curves.stalkC (f.left x)).toAlgebra
  obtain ⟨hφ, hcomm⟩ := s2e_affine_formal_pullback X Y f U hU x hx hcx hcy
  let E := s2e_complex_affine_point_adic_equiv X W (hU.preimage f.left) x hx hcx
  let F := s2e_complex_affine_point_adic_equiv Y U hU (f.left x) hx hcy
  refine ⟨hφ, ?_, ?_⟩
  · intro v w hvw
    apply F.injective
    apply hbij.injective
    exact (DFunLike.congr_fun hcomm v).trans
      ((congrArg E hvw).trans (DFunLike.congr_fun hcomm w).symm)
  · intro y
    obtain ⟨w, hw⟩ := hbij.surjective (E y)
    obtain ⟨z, rfl⟩ := F.surjective w
    refine ⟨z, E.injective ?_⟩
    exact (DFunLike.congr_fun hcomm z).symm.trans hw

end HodgeLean.Foundations.Program
