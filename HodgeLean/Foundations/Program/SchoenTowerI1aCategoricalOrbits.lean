import HodgeLean.Foundations.Program.SchoenTowerI1aPreProofs

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_projective_categorical_orbits
    (X Y : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (p : X ⟶ Y) (hpinv : ∀ g, a g ≫ p = p)
    (hp : ∀ (T : Over (Spec ↧ℂ)) (f : X ⟶ T),
      (∀ g, a g ≫ f = f) → ∃! v : Y ⟶ T, p ≫ v = f)
    (x y : ComplexPoint X) :
    Point.map p x = Point.map p y ↔ ∃ g, Point.map (a g) x = y := by
  obtain ⟨Q, q, hfin, hsurj, hinv, hcharts⟩ := s2v_i1a_pre_glue_aux X G a ha1 hamul
  letI := hfin
  letI := hsurj
  have hq : ∀ (T : Over (Spec ↧ℂ)) (f : X ⟶ T),
      (∀ g, a g ≫ f = f) → ∃! v : Q ⟶ T, q ≫ v = f :=
    fun T f hf => s2v_i1a_pre_glued_descent_aux X G a ha1 hamul Q q hinv hcharts T f hf
  obtain ⟨e, he, _⟩ := s2v_i1a_pre_categorical_identification_aux
    X G a ha1 hamul Q Y q p hinv hpinv hq hp
  constructor
  · intro hxy
    have hqxy : Point.map q x = Point.map q y := by
      apply (cancel_mono e.hom).mp
      simpa only [Point.map, Category.assoc, he] using hxy
    exact (s2v_i1a_pre_glued_orbits_aux X G a ha1 hamul Q q hinv hcharts x y).mp hqxy
  · rintro ⟨g, hg⟩
    rw [← hg]
    change x ≫ p = (x ≫ a g) ≫ p
    rw [Category.assoc, hpinv]

end HodgeLean.Foundations.Program
