import HodgeLean.Foundations.Program.SchoenTowerI2bChartScheme

/-! The coefficient ideal of the canonical selected chart.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
namespace HodgeLean.Foundations.Program

/-- The actual canonical chart sends the selected centre to the free algebraic centre ideal.
Source: the affine chart section formula and the regular selected-pair calculation. -/
theorem s2v_i2b_canonical_chart_coordinate_ideal_free
    (U : Scheme) [IsAffine U] (I : U.IdealSheafData) (u v : Γ(U, ⊤))
    (hI : I.ideal ⟨⊤, isAffineOpen_top U⟩ = Ideal.span {u, v})
    (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(U, ⊤) [v, u]) :
    let Q := s2v_L1bChart u v
    letI : CommRing Q := inferInstanceAs (CommRing (s2v_L1bChart u v))
    let q : Polynomial Γ(U, ⊤) →+* Q := Ideal.Quotient.mk _
    let c := q.comp Polynomial.C
    let f := Spec.map (CommRingCat.ofHom c) ≫ U.isoSpec.inv
    Nonempty ((Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of Q)).hom.hom.comp f.appTop.hom)
      (I.ideal ⟨⊤, isAffineOpen_top U⟩)) ≃ₗ[Q] Q) := by
  dsimp only
  let Q := s2v_L1bChart u v
  letI : CommRing Q := inferInstanceAs (CommRing (s2v_L1bChart u v))
  let q : Polynomial Γ(U, ⊤) →+* Q := Ideal.Quotient.mk _
  let c := q.comp Polynomial.C
  let f := Spec.map (CommRingCat.ofHom c) ≫ U.isoSpec.inv
  change Nonempty ((Ideal.map ((f.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Q)).hom).hom)
    (I.ideal ⟨⊤, isAffineOpen_top U⟩)) ≃ₗ[Q] Q)
  rw [s2v_i2b_affine_chart_appTop U c, hI, Ideal.map_span, Set.image_pair]
  exact s2v_i2b_regular_pair_chart_centre_free u v hreg

end HodgeLean.Foundations.Program
