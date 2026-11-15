import HodgeLean.Foundations.Program.SchoenTowerL1bKummerUnits

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Principal equations restrict along inclusions of affine opens. -/
theorem s2v_l1b_principal_restrict
    (X : Scheme) (I : X.IdealSheafData) (U V : X.affineOpens)
    (hUV : U.1 ≤ V.1) (g : Γ(X, V))
    (hg : I.ideal V = Ideal.span {g}) :
    I.ideal U = Ideal.span {(X.presheaf.map (homOfLE hUV).op).hom g} := by
  rw [← I.map_ideal hUV, hg, Ideal.map_span, Set.image_singleton]
  rfl

/-- Finitely many local principal equations share an affine neighborhood inside any prescribed open. -/
theorem s2v_l1b_simultaneous_principal_neighborhood
    (X : Scheme) {J : Type*} [Finite J] (I : J → X.IdealSheafData)
    (x : X) (V : X.Opens) (hxV : x ∈ V)
    (hI : ∀ j, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ g : Γ(X, U), (I j).ideal U = Ideal.span {g}) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ V ∧
      ∃ g : J → Γ(X, U), ∀ j, (I j).ideal U = Ideal.span {g j} := by
  classical
  choose W hxW g hg using hI
  let O : X.Opens := ⟨⋂ j, (W j).1,
    isOpen_iInter_of_finite fun j => (W j).1.isOpen⟩
  have hxO : x ∈ O := Set.mem_iInter.mpr hxW
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ V ⊓ O from ⟨hxV, hxO⟩)
  have hUW (j : J) : U ≤ (W j).1 := fun z hz =>
    Set.mem_iInter.mp (hUV hz).2 j
  refine ⟨⟨U, hU⟩, hxU, fun z hz => (hUV hz).1,
    (fun j => (X.presheaf.map (homOfLE (hUW j)).op).hom (g j)), ?_⟩
  intro j
  exact s2v_l1b_principal_restrict X (I j) ⟨U, hU⟩ (W j) (hUW j) (g j) (hg j)

end HodgeLean.Foundations.Program
