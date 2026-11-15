import HodgeLean.Foundations.Program.SchoenTowerL1aIdealPullback
import HodgeLean.Foundations.Program.SchoenTowerL1aCoefficientHelpers

/-! # Local principal ideal comparison for L1a

Implication from compatible affine principal equations to the equality of
restricted scheme ideal sheaves. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A commuting affine chart with a product equation gives the local scheme ideal identity.
Source: Hartshorne, Algebraic Geometry, II.5–6, local equations of divisor pullback. -/
theorem s2v_l1a_local_principal_ideal_comparison
    {X Y U V : Scheme} [IsAffine U] [IsAffine V]
    {ι : Type*} [Fintype ι]
    (γ : X ⟶ Y) (u : U ⟶ Y) (v : V ⟶ X) [IsOpenImmersion v]
    (q : V ⟶ U) (hsquare : v ≫ γ = q ≫ u)
    (I : Y.IdealSheafData) (J : ι → X.IdealSheafData)
    (c : Γ(U, ⊤)) (z : ι → Γ(V, ⊤))
    (hI : (I.comap u).ideal ⟨⊤, isAffineOpen_top U⟩ = Ideal.span {c})
    (hJ : ∀ j, ((J j).comap v).ideal ⟨⊤, isAffineOpen_top V⟩ = Ideal.span {z j})
    (hc : q.appTop.hom c = ∏ j, z j) :
    (I.comap γ).comap v = (∏ j, J j).comap v := by
  rw [← Scheme.IdealSheafData.comap_comp I v γ, hsquare,
    Scheme.IdealSheafData.comap_comp,
    s2v_l1a_open_ideal_pullback_prod v Finset.univ J]
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [s2v_l1a_affine_ideal_pullback, hI, Ideal.map_span,
    Set.image_singleton, hc]
  change _ = Scheme.IdealSheafData.equivOfIsAffine (∏ j, (J j).comap v)
  rw [map_prod]
  change _ = ∏ j, ((J j).comap v).ideal ⟨⊤, isAffineOpen_top V⟩
  simp_rw [hJ]
  exact (Ideal.prod_span_singleton Finset.univ z).symm

end HodgeLean.Foundations.Program
