import HodgeLean.Foundations.Program.UniversalFamilyB60cHom
import HodgeLean.Adapters.TorusCohomologyChecks
import HodgeLean.Adapters.CycleClassPullbackDefs
import HodgeLean.Foundations.Program.UniversalFamilyB60cPoints

noncomputable section
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- Compare dimensions of the holomorphic summands using the rational equivalence,
then transport the resulting equality by its inverse. -/
theorem b60c_inverse_holomorphic
    (X Y : Over (Spec ↧ℂ)) [GrpObj X] [GrpObj Y]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (e : HQ Y 1 ≃ₗ[ℚ] HQ X 1)
    (he : (complexHolomorphicH1 Y).map (e.toLinearMap.baseChange ℂ) ≤
      complexHolomorphicH1 X) :
    (complexHolomorphicH1 X).map (e.symm.toLinearMap.baseChange ℂ) ≤
      complexHolomorphicH1 Y := by
  letI := (finiteBetti_abelian X).finite 1
  letI := (finiteBetti_abelian Y).finite 1
  let eC := LinearEquiv.baseChange ℚ ℂ _ _ e
  have hd : dim Y.left = dim X.left := by
    have h := e.finrank_eq
    rw [finrank_HQ_abelian, finrank_HQ_abelian, Nat.choose_one_right,
      Nat.choose_one_right] at h
    omega
  have hEq : (complexHolomorphicH1 Y).map eC.toLinearMap = complexHolomorphicH1 X := by
    apply Submodule.eq_of_le_of_finrank_eq he
    exact (eC.finrank_map_eq _).trans ((spec_complexH1_dimension Y).1.trans
      (hd.trans (spec_complexH1_dimension X).1.symm))
  rintro _ ⟨v, hv, rfl⟩
  rw [← hEq] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  change eC.symm (eC w) ∈ complexHolomorphicH1 Y
  rw [eC.symm_apply_apply]
  exact hw

#print axioms b60c_inverse_holomorphic

/-- Realize the inverse rational map, identify both composites by faithful degree-one
pullback, and apply the torsion argument. -/
theorem b60c_isogeny_of_equiv
    (X Y : Over (Spec ↧ℂ)) [GrpObj X] [GrpObj Y]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : X ⟶ Y) [IsMonHom f] (e : HQ Y 1 ≃ₗ[ℚ] HQ X 1)
    (he : homPullback f 1 = e.toLinearMap) : ccm2_IsogenyOnPoints f := by
  haveI : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  haveI : IsCommMonObj Y := isCommMonObj_of_complexSelfProductIntegral Y
    (complexSelfProductIntegral_of_isIntegral Y)
  have hhol : (complexHolomorphicH1 Y).map (e.toLinearMap.baseChange ℂ) ≤
      complexHolomorphicH1 X := by
    rw [← he]
    exact (spec_homPullback_hodge f).1
  obtain ⟨n, hn, g, hg, hge⟩ := b60c_hom_of_holomorphic Y X e.symm.toLinearMap
    (b60c_inverse_holomorphic X Y e hhol)
  haveI : IsMonHom g := hg
  have hfg : homPullback (f ≫ g) 1 = (n : ℚ) • LinearMap.id := by
    rw [spec_homPullback_comp, he, hge]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
      map_smul, LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  have hgf : homPullback (g ≫ f) 1 = (n : ℚ) • LinearMap.id := by
    rw [spec_homPullback_comp, he, hge]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.id_apply]
  exact b60c_isogeny_of_point_composites X Y f g n hn
    (b60c_points_of_scalar_pullback X (f ≫ g) n hfg)
    (b60c_points_of_scalar_pullback Y (g ≫ f) n hgf)

#print axioms b60c_isogeny_of_equiv

end HodgeLean.Foundations.Program
