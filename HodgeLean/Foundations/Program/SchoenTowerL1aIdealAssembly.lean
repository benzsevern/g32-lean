import HodgeLean.Foundations.Program.SchoenTowerL1aLocalIdealComparison
import HodgeLean.Foundations.Program.SchoenTowerL1aIdealLocality

/-! # Global assembly of compatible principal equations

Implication from an affine cover carrying compatible principal equations to
the global ideal-sheaf comparison. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Compatible local product equations on an affine open cover give the global ideal comparison.
Source: Hartshorne, Algebraic Geometry, II.5–6, local equations and ideal-sheaf locality. -/
theorem s2v_l1a_ideal_comparison_of_principal_cover
    {X Y : Scheme} {κ ι : Type*} [Fintype ι]
    (γ : X ⟶ Y) (I : Y.IdealSheafData) (J : ι → X.IdealSheafData)
    (U V : κ → Scheme) [∀ k, IsAffine (U k)] [∀ k, IsAffine (V k)]
    (u : ∀ k, U k ⟶ Y) (v : ∀ k, V k ⟶ X) [∀ k, IsOpenImmersion (v k)]
    (q : ∀ k, V k ⟶ U k) (hsquare : ∀ k, v k ≫ γ = q k ≫ u k)
    (hcover : ∀ x : X, ∃ k, x ∈ Set.range (v k))
    (c : ∀ k, Γ(U k, ⊤)) (z : ∀ k, ι → Γ(V k, ⊤))
    (hI : ∀ k, (I.comap (u k)).ideal ⟨⊤, isAffineOpen_top (U k)⟩ = Ideal.span {c k})
    (hJ : ∀ k j, ((J j).comap (v k)).ideal ⟨⊤, isAffineOpen_top (V k)⟩ =
      Ideal.span {z k j})
    (hc : ∀ k, (q k).appTop.hom (c k) = ∏ j, z k j) :
    I.comap γ = ∏ j, J j := by
  apply s2v_l1a_ideal_eq_of_affine_open_cover V v hcover
  intro k
  exact s2v_l1a_local_principal_ideal_comparison γ (u k) (v k) (q k)
    (hsquare k) I J (c k) (z k) (hI k) (hJ k) (hc k)

end HodgeLean.Foundations.Program
