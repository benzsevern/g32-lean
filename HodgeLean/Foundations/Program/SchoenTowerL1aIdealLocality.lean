import HodgeLean.Foundations.Program.SchoenTowerL1aIdealPullback

/-! # Ideal-sheaf locality for L1a

Implication from equality on an affine open cover to equality of the ambient
ideal sheaves. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Equality of pullbacks on an affine open cover detects equality of ideal sheaves.
Source: Hartshorne, Algebraic Geometry, II.5, locality of ideal sheaves. -/
theorem s2v_l1a_ideal_eq_of_affine_open_cover
    {X : Scheme} {ι : Type*} (V : ι → Scheme) [∀ i, IsAffine (V i)]
    (v : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (v i)]
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (v i))
    (I J : X.IdealSheafData) (heq : ∀ i, I.comap (v i) = J.comap (v i)) :
    I = J := by
  let U (i : ι) : X.affineOpens :=
    ⟨v i ''ᵁ ⊤, (isAffineOpen_top (V i)).image_of_isOpenImmersion (v i)⟩
  have hU : ⨆ i, (U i).1 = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, y, rfl⟩ := hcover x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ⟨y, trivial, rfl⟩⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U hU
  intro i
  have hlocal := congrArg
    (fun K : (V i).IdealSheafData => K.ideal ⟨⊤, isAffineOpen_top (V i)⟩) (heq i)
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hlocal
  exact Ideal.comap_injective_of_surjective ((v i).appIso ⊤).inv.hom
    ((v i).appIso ⊤).symm.commRingCatIsoToRingEquiv.surjective hlocal

end HodgeLean.Foundations.Program
