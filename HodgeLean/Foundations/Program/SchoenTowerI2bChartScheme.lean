import HodgeLean.Foundations.Program.SchoenTowerI2bChartFreeness
import HodgeLean.Foundations.Program.SchoenCycleAffineIdeals

/-! Affine scheme transport for the algebraic blowup charts.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A free image ideal in affine ring coordinates gives the actual pullback ideal its rank-one test.
Source: affine ideal pullback and transport of a free ideal through the coordinate isomorphism. -/
theorem s2v_i2b_affine_pullback_ideal_free
    {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (I : Y.IdealSheafData) {A : Type*} [CommRing A]
    (e : Γ(X, ⊤) ≃+* A)
    (hfree : Nonempty ((Ideal.map (e.toRingHom.comp f.appTop.hom)
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩)) ≃ₗ[A] A)) :
    Nonempty (((I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩) ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤)) := by
  rw [s2e_affine_comap_ideal]
  have h := s2v_i2b_free_ideal_map_equiv e.symm _ hfree
  rw [Ideal.map_map] at h
  have he : (e.symm : A →+* Γ(X, ⊤)).comp
      (e.toRingHom.comp f.appTop.hom) = f.appTop.hom := by
    ext a
    exact e.symm_apply_apply _
  exact (congrArg (fun c : Γ(Y, ⊤) →+* Γ(X, ⊤) =>
    Nonempty ((Ideal.map c (I.ideal ⟨⊤, isAffineOpen_top Y⟩)) ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤))) he).mp h


/-- The canonical map from a spectrum to an affine scheme induces the specified ring map.
Source: the global-section formula for the affine adjunction and naturality of the spectrum counit. -/
theorem s2v_i2b_affine_chart_appTop
    (U : Scheme) [IsAffine U] {A : Type*} [CommRing A]
    (c : Γ(U, ⊤) →+* A) :
    (Spec.map (CommRingCat.ofHom c) ≫ U.isoSpec.inv).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom = CommRingCat.ofHom c := by
  let f := Spec.map (CommRingCat.ofHom c) ≫ U.isoSpec.inv
  have hcomp : f ≫ U.isoSpec.hom = Spec.map (CommRingCat.ofHom c) := by
    dsimp only [f]
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have htop := congrArg Scheme.Hom.appTop hcomp
  rw [Scheme.Hom.comp_appTop] at htop
  have hU : U.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(U, ⊤)).hom := by
    change U.toSpecΓ.appTop = _
    exact Scheme.toSpecΓ_appTop U
  rw [hU] at htop
  apply (cancel_epi (Scheme.ΓSpecIso Γ(U, ⊤)).hom).mp
  rw [← Category.assoc, htop]
  exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom c)

end HodgeLean.Foundations.Program
