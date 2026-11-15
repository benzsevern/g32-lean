import HodgeLean.Foundations.Program.SchoenTowerI2bChartCoordinateFreeness
import Mathlib.Analysis.Complex.Basic

/-! Constructing actual retained blowup maps from the algebraic charts.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
namespace HodgeLean.Foundations.Program

/-- The retained universal property sends each regular selected algebraic chart to the actual upper stage.
Source: the rank-one ideal criterion and the supplied invertible-ideal mapping property. -/
theorem s2v_i2b_retained_blowup_chart_lift
    (X Y U : Over (Spec ↧ℂ)) [IsAffine U.left]
    (a : U ⟶ X) (b : Y ⟶ X) (I : X.left.IdealSheafData)
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ X),
      (∀ x : T.left, ∃ V : T.left.affineOpens, x ∈ V.1 ∧
        Nonempty (((I.comap f.left).ideal V) ≃ₗ[Γ(T.left, V)] Γ(T.left, V))) →
      ∃! g : T ⟶ Y, g ≫ b = f)
    (u v : Γ(U.left, ⊤))
    (hI : (I.comap a.left).ideal ⟨⊤, isAffineOpen_top U.left⟩ = Ideal.span {u, v})
    (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(U.left, ⊤) [v, u]) :
    let Q := s2v_L1bChart u v
    letI : CommRing Q := inferInstanceAs (CommRing (s2v_L1bChart u v))
    let q : Polynomial Γ(U.left, ⊤) →+* Q := Ideal.Quotient.mk _
    let f := Spec.map (CommRingCat.ofHom (q.comp Polynomial.C)) ≫ U.left.isoSpec.inv
    ∃ g : Spec (CommRingCat.of Q) ⟶ Y.left, g ≫ b.left = f ≫ a.left := by
  dsimp only
  let Q := s2v_L1bChart u v
  letI : CommRing Q := inferInstanceAs (CommRing (s2v_L1bChart u v))
  let q : Polynomial Γ(U.left, ⊤) →+* Q := Ideal.Quotient.mk _
  let c := q.comp Polynomial.C
  let f : Spec (CommRingCat.of Q) ⟶ U.left :=
    Spec.map (CommRingCat.ofHom c) ≫ U.left.isoSpec.inv
  let T : Over (Spec ↧ℂ) := Over.mk (f ≫ U.hom)
  letI : IsAffine T.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of Q)))
  let F : T ⟶ X := Over.homMk (f ≫ a.left) (by
    rw [Category.assoc, a.w]
    rfl)
  have hcoord := s2v_i2b_canonical_chart_coordinate_ideal_free U.left
    (I.comap a.left) u v hI hreg
  have hfree := s2v_i2b_affine_pullback_ideal_free f (I.comap a.left)
    (Scheme.ΓSpecIso (CommRingCat.of Q)).commRingCatIsoToRingEquiv hcoord
  obtain ⟨g, hg, _⟩ := hblowup T F (by
    intro x
    refine ⟨⟨⊤, isAffineOpen_top T.left⟩, by trivial, ?_⟩
    change Nonempty (((I.comap (f ≫ a.left)).ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of Q))⟩)
      ≃ₗ[Γ(Spec (CommRingCat.of Q), ⊤)] Γ(Spec (CommRingCat.of Q), ⊤))
    rw [Scheme.IdealSheafData.comap_comp]
    exact hfree)
  exact ⟨g.left, congrArg (fun h : T ⟶ X => h.left) hg⟩

end HodgeLean.Foundations.Program
