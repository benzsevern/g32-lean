import HodgeLean.Foundations.Program.SchoenTowerI2aReesCartierImage
import HodgeLean.Foundations.Program.SchoenTowerI2aCartierCoefficientTransport
import HodgeLean.Foundations.Program.SchoenCycleAffineIdeals

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual Rees spectrum satisfies the ideal-sheaf Cartier test used by
the retained blowup universal property, with its coefficient projection retained.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13;
Mathlib, `Scheme.ΓSpecIso_inv_naturality`. -/
theorem s2v_i2a_rees_spectrum_cartier_test
    (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (x : R)
    (hxI : x ∈ I) (hx : x ≠ 0)
    (K : (Spec (CommRingCat.of R)).IdealSheafData)
    (hK : K.ideal ⟨⊤, isAffineOpen_top _⟩ =
      I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :
    let C := s2t_reesChart I x
    let f := Spec.map (CommRingCat.ofHom (algebraMap R C))
    ∀ p : Spec (CommRingCat.of C), ∃ U : (Spec (CommRingCat.of C)).affineOpens,
      p ∈ U.1 ∧ Nonempty (((K.comap f).ideal U) ≃ₗ[Γ(Spec (CommRingCat.of C), U)]
        Γ(Spec (CommRingCat.of C), U)) := by
  intro C f p
  refine ⟨⟨⊤, isAffineOpen_top _⟩, trivial, ?_⟩
  rw [s2e_affine_comap_ideal f K, hK, Ideal.map_map]
  have hn : f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom =
      (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom.comp (algebraMap R C) := by
    exact congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R C))).symm
  rw [hn, ← Ideal.map_map]
  exact s2v_i2a_cartier_ideal_ring_equiv
    (Scheme.ΓSpecIso (CommRingCat.of C)).symm.commRingCatIsoToRingEquiv _
    (s2v_i2a_rees_chart_cartier_image R I x hxI hx)

end HodgeLean.Foundations.Program
