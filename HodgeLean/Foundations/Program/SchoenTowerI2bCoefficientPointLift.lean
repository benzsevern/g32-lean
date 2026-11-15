import HodgeLean.Foundations.Program.SchoenTowerI2bChartLiftComparison
import HodgeLean.Foundations.Program.SchoenTowerI2bCoefficientOpens

/-! Lifting an actual coefficient-open point through a selected chart.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
namespace HodgeLean.Foundations.Program

/-- A point on the unit-coefficient open is an actual image point of the selected chart lift.
Source: the coefficient ratio, Cartier restriction, and uniqueness of the retained lift. -/
theorem s2v_i2b_coefficient_point_chart_lift
    (X Y U V : Over (Spec ↧ℂ)) [IsAffine U.left] [IsAffine V.left]
    (a : U ⟶ X) (b : Y ⟶ X) (t : V ⟶ U) (j : V ⟶ Y)
    (hj : j ≫ b = t ≫ a) (I : X.left.IdealSheafData)
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ X),
      (∀ x : T.left, ∃ W : T.left.affineOpens, x ∈ W.1 ∧
        Nonempty (((I.comap f.left).ideal W) ≃ₗ[Γ(T.left, W)] Γ(T.left, W))) →
      ∃! g : T ⟶ Y, g ≫ b = f)
    (J : V.left.IdealSheafData) (hJ : J = I.comap (j ≫ b).left)
    (u v : Γ(U.left, ⊤))
    (hu : t.left.appTop.hom u ∈ J.ideal ⟨⊤, isAffineOpen_top V.left⟩)
    (hv : t.left.appTop.hom v ∈ J.ideal ⟨⊤, isAffineOpen_top V.left⟩)
    (e : (J.ideal ⟨⊤, isAffineOpen_top V.left⟩) ≃ₗ[Γ(V.left, ⊤)] Γ(V.left, ⊤))
    (y : V.left) (hy : y ∈ V.left.basicOpen (e ⟨t.left.appTop.hom v, hv⟩)) :
    let Q := s2v_L1bChart u v
    letI : CommRing Q := inferInstanceAs (CommRing (s2v_L1bChart u v))
    let q : Polynomial Γ(U.left, ⊤) →+* Q := Ideal.Quotient.mk _
    let f := Spec.map (CommRingCat.ofHom (q.comp Polynomial.C)) ≫ U.left.isoSpec.inv
    ∀ g : Spec (CommRingCat.of Q) ⟶ Y.left, g ≫ b.left = f ≫ a.left →
      ∃ z : Spec (CommRingCat.of Q), g z = j.left y := by
  dsimp only
  intro g hg
  let d := e ⟨t.left.appTop.hom v, hv⟩
  let W := V.left.basicOpen d
  let T : Over (Spec ↧ℂ) := Over.mk (W.ι ≫ V.hom)
  letI : IsAffine T.left := inferInstanceAs (IsAffine W.toScheme)
  let k : T ⟶ V := Over.homMk W.ι rfl
  let tW := k ≫ t
  let jW := k ≫ j
  have hjW : jW ≫ b = tW ≫ a := by
    simp only [jW, tW, Category.assoc, hj]
  have hunit : IsUnit (W.ι.appTop.hom d) := s2v_i2b_basicOpen_inclusion_unit V.left d
  obtain ⟨s, hs⟩ := s2v_i2b_invertible_ideal_localized_ratio
    (J.ideal ⟨⊤, isAffineOpen_top V.left⟩)
    (t.left.appTop.hom u) (t.left.appTop.hom v) hu hv e W.ι.appTop.hom hunit
  let sT : Γ(T.left, ⊤) := s
  have hsW : tW.left.appTop.hom u = sT * tW.left.appTop.hom v := by
    change (W.ι ≫ t.left).appTop.hom u = s * (W.ι ≫ t.left).appTop.hom v
    rw [Scheme.Hom.comp_appTop]
    exact hs
  have hfreeW := s2v_i2b_cartier_free_on_basicOpen_source V.left J ⟨e⟩ d
  have hIdeal : I.comap (jW ≫ b).left = J.comap W.ι := by
    rw [hJ, ← Scheme.IdealSheafData.comap_comp]
    congr 1
  have hlocal : ∀ x : T.left, ∃ A : T.left.affineOpens, x ∈ A.1 ∧
      Nonempty (((I.comap (jW ≫ b).left).ideal A) ≃ₗ[Γ(T.left, A)] Γ(T.left, A)) := by
    intro x
    refine ⟨⟨⊤, isAffineOpen_top T.left⟩, by trivial, ?_⟩
    rw [hIdeal]
    exact hfreeW
  obtain ⟨l, hl⟩ := s2v_i2b_actual_chart_lift_comparison X Y U T a b tW jW hjW I
    hblowup hlocal u v sT hsW g hg
  let z : W.toScheme := ⟨y, hy⟩
  refine ⟨l z, ?_⟩
  have hp := congrArg (fun h : T.left ⟶ Y.left => h z) hl
  change g (l z) = j.left y at hp
  exact hp

end HodgeLean.Foundations.Program
