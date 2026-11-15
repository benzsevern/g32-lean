import HodgeLean.Foundations.Program.CompensationAssemblyAffineEtale

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
theorem cq_finite_smooth_integral_etale {X Y : Scheme.{0}}
    [IsIntegral X] [IsIntegral Y] (sY : Y ⟶ Spec ↧ℂ)
    (f : X ⟶ Y) [IsFinite f] [Smooth f] [IsDominant f] : Etale f := by
  choose U hU hyU hsub using fun y : Y =>
    exists_isAffineOpen_mem_and_subset (show y ∈ (⊤ : Y.Opens) from trivial)
  have hcover : ⨆ y, U y = ⊤ := by
    apply le_antisymm le_top
    intro y hy
    exact Opens.mem_iSup.mpr ⟨y, hyU y⟩
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Etale) U hcover
  intro y
  let V := U y
  letI : Nonempty V.toScheme := ⟨⟨y, hyU y⟩⟩
  letI : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  letI : IsAffine V.toScheme := hU y
  obtain ⟨x, hx⟩ := f.denseRange.exists_mem_open V.isOpen ⟨y, hyU y⟩
  letI : Nonempty (f ⁻¹ᵁ V).toScheme := ⟨⟨x, hx⟩⟩
  letI : IsIntegral (f ⁻¹ᵁ V).toScheme := isIntegral_of_isOpenImmersion (f ⁻¹ᵁ V).ι
  letI : IsAffine (f ⁻¹ᵁ V).toScheme := (hU y).preimage f
  exact cq_finite_smooth_affine_integral_etale (V.ι ≫ sY) (f ∣_ V)

theorem cq_primeProjection_finite_etale_neighborhood (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hA : TopologicalSpace.dim A.left = 6) (hY : TopologicalSpace.dim Y.left = 2)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = 5)
    (himage : Order.coheight ((fst A Y).left x) = 3) :
    ∃ U : (a2r_component A ((fst A Y).left x)).left.Opens,
      genericPoint (a2r_component A ((fst A Y).left x)).left ∈ U ∧
      Dense (U : Set (a2r_component A ((fst A Y).left x)).left) ∧
      IsFinite ((cq_primeProjection A Y x).left ∣_ U) ∧
      Etale ((cq_primeProjection A Y x).left ∣_ U) := by
  obtain ⟨U, hU, hUd, hfinite, hsmooth⟩ :=
    cq_primeProjection_finite_smooth_neighborhood A Y hA hY x hx himage
  let f := (cq_primeProjection A Y x).left
  letI : IsDominant f := cq_primeProjection_dominant A Y x
  letI : Nonempty U.toScheme := ⟨⟨_, hU⟩⟩
  letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  obtain ⟨z, hz⟩ := f.denseRange.exists_mem_open U.isOpen ⟨_, hU⟩
  letI : Nonempty (f ⁻¹ᵁ U).toScheme := ⟨⟨z, hz⟩⟩
  letI : IsIntegral (f ⁻¹ᵁ U).toScheme := isIntegral_of_isOpenImmersion (f ⁻¹ᵁ U).ι
  letI : IsFinite (f ∣_ U) := hfinite
  letI : Smooth (f ∣_ U) := hsmooth
  letI : IsDominant (f ∣_ U) :=
    IsZariskiLocalAtTarget.restrict (P := @IsDominant) (inferInstance : IsDominant f) U
  exact ⟨U, hU, hUd, hfinite, cq_finite_smooth_integral_etale
    (U.ι ≫ (a2r_component A ((fst A Y).left x)).hom) (f ∣_ U)⟩

end HodgeLean.Foundations.Program
