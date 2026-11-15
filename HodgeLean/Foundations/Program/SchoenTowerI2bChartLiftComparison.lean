import HodgeLean.Foundations.Program.SchoenTowerI2bChartRatios
import Mathlib.Analysis.Complex.Basic

/-! Identifying affine ratio factorizations with the actual retained lift.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
namespace HodgeLean.Foundations.Program

/-- The ratio factorization agrees with an actual upper-stage map by uniqueness in the retained universal property.
Source: the affine chart factorization and uniqueness of the supplied invertible-ideal lift. -/
theorem s2v_i2b_actual_chart_lift_comparison
    (X Y U V : Over (Spec ↧ℂ)) [IsAffine U.left] [IsAffine V.left]
    (a : U ⟶ X) (b : Y ⟶ X) (t : V ⟶ U) (j : V ⟶ Y)
    (hj : j ≫ b = t ≫ a) (I : X.left.IdealSheafData)
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ X),
      (∀ x : T.left, ∃ W : T.left.affineOpens, x ∈ W.1 ∧
        Nonempty (((I.comap f.left).ideal W) ≃ₗ[Γ(T.left, W)] Γ(T.left, W))) →
      ∃! g : T ⟶ Y, g ≫ b = f)
    (hfree : ∀ x : V.left, ∃ W : V.left.affineOpens, x ∈ W.1 ∧
      Nonempty (((I.comap (j ≫ b).left).ideal W) ≃ₗ[Γ(V.left, W)] Γ(V.left, W)))
    (u v : Γ(U.left, ⊤)) (s : Γ(V.left, ⊤))
    (hs : t.left.appTop.hom u = s * t.left.appTop.hom v) :
    let Q := s2v_L1bChart u v
    letI : CommRing Q := inferInstanceAs (CommRing (s2v_L1bChart u v))
    let q : Polynomial Γ(U.left, ⊤) →+* Q := Ideal.Quotient.mk _
    let f := Spec.map (CommRingCat.ofHom (q.comp Polynomial.C)) ≫ U.left.isoSpec.inv
    ∀ g : Spec (CommRingCat.of Q) ⟶ Y.left, g ≫ b.left = f ≫ a.left →
      ∃ l : V.left ⟶ Spec (CommRingCat.of Q), l ≫ g = j.left := by
  dsimp only
  intro g hg
  obtain ⟨l, hl⟩ := s2v_i2b_affine_chart_ratio_factor t.left u v s hs
  have hbase : (l ≫ g) ≫ b.left = j.left ≫ b.left := by
    rw [Category.assoc, hg, ← Category.assoc, hl]
    exact (congrArg (fun h : V ⟶ X => h.left) hj).symm
  let j' : V ⟶ Y := Over.homMk (l ≫ g) (by
    calc
      (l ≫ g) ≫ Y.hom = ((l ≫ g) ≫ b.left) ≫ X.hom := by simp only [Category.assoc, b.w]
      _ = (j.left ≫ b.left) ≫ X.hom := by rw [hbase]
      _ = V.hom := by rw [Category.assoc, b.w, j.w])
  have hfac : j' ≫ b = j ≫ b := by
    apply Over.OverMorphism.ext
    exact hbase
  obtain ⟨k, hk, huniq⟩ := hblowup V (j ≫ b) hfree
  have he : j' = j := (huniq j' hfac).trans (huniq j rfl).symm
  exact ⟨l, congrArg (fun h : V ⟶ Y => h.left) he⟩

end HodgeLean.Foundations.Program
