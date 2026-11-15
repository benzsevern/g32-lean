import HodgeLean.Foundations.Program.SchoenTowerI2aReesCartierTest

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every nonzero actual affine Rees chart factors through the retained
universal blowup over the same base, using its verified ideal-sheaf Cartier test.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13;
Stacks Project, Tag 01OF, universal property of blowing up. -/
theorem s2v_i2a_rees_chart_to_retained_blowup
    (Q : Scheme.{0}) (Y B : Over Q) (b : B ⟶ Y) (K : Y.left.IdealSheafData)
    (huniv : ∀ (T : Over Q) (f : T ⟶ Y),
      (∀ p : T.left, ∃ U : T.left.affineOpens, p ∈ U.1 ∧
        Nonempty (((K.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! v : T ⟶ B, v ≫ b = f)
    (R : Type) [CommRing R] [IsDomain R] (π : Spec (CommRingCat.of R) ⟶ Q)
    (u : Over.mk π ⟶ Y) (I : Ideal R) (x : R) (hxI : x ∈ I) (hx : x ≠ 0)
    (hK : (K.comap u.left).ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩ =
      I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :
    let C := s2t_reesChart I x
    let f := Spec.map (CommRingCat.ofHom (algebraMap R C))
    ∃! v : Over.mk (f ≫ π) ⟶ B,
      v ≫ b = Over.homMk f rfl ≫ u := by
  intro C f
  apply huniv
  intro p
  have H := s2v_i2a_rees_spectrum_cartier_test R I x hxI hx (K.comap u.left) hK p
  change ∃ U : (Spec (CommRingCat.of C)).affineOpens, p ∈ U.1 ∧
    Nonempty (((K.comap (f ≫ u.left)).ideal U) ≃ₗ[Γ(Spec (CommRingCat.of C), U)]
      Γ(Spec (CommRingCat.of C), U))
  rw [Scheme.IdealSheafData.comap_comp]
  exact H

end HodgeLean.Foundations.Program
