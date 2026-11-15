import HodgeLean.Foundations.Program.SchoenTowerL1bKummerPointQuotient

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A finite invariant map onto a smooth complex target with the specified
finite-group point orbits has the categorical descent property. -/
theorem s2v_l1b_categorical_quotient_of_point_orbits
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (f : X ⟶ Y) [IsFinite f.left]
    (hsurj : Function.Surjective (Point.map f))
    (hinv : ∀ g, (ρ g).asIso.hom ≫ f = f)
    (horbit : ∀ x y : ComplexPoint X,
      Point.map f x = Point.map f y ↔ ∃ g, Point.map (ρ g).asIso.hom x = y) :
    ∀ (T : Over (Spec ↧ℂ)) (g : X ⟶ T),
      (∀ i, (ρ i).asIso.hom ≫ g = g) → ∃! u : Y ⟶ T, f ≫ u = g := by
  obtain ⟨Q, q, hQ, hproj, hfin, hqsurj, hqinv, hqorbit, hq, _⟩ :=
    s2_finiteAction_projectiveQuotient X G ρ
  letI := hQ
  letI := hproj
  letI := hfin
  obtain ⟨d, hd, _⟩ := hq Y f hinv
  haveI : IsProper (d.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  haveI : IsProper d.left := IsProper.of_comp d.left Y.hom
  have hbij : Function.Bijective (Point.map d) := by
    constructor
    · intro x y hxy
      obtain ⟨x', rfl⟩ := hqsurj x
      obtain ⟨y', rfl⟩ := hqsurj y
      have hfxy : Point.map f x' = Point.map f y' := by
        simpa only [Point.map, Category.assoc, hd] using hxy
      obtain ⟨g, hg⟩ := (horbit x' y').mp hfxy
      exact (hqorbit x' y').mpr ⟨g, hg⟩
    · intro y
      obtain ⟨x, hx⟩ := hsurj y
      exact ⟨Point.map q x, by simpa only [Point.map, Category.assoc, hd] using hx⟩
  haveI : IsIso d.left := s2v_l1b_isIso_of_point_bijective Q Y d hbij
  let e : Q ≅ Y := Over.isoMk (asIso d.left) (Over.w d)
  have he : e.hom = d := by ext; rfl
  haveI : IsIso d := he ▸ e.isIso_hom
  intro T g hg
  obtain ⟨v, hv, huniq⟩ := hq T g hg
  refine ⟨inv d ≫ v, ?_, ?_⟩
  · change f ≫ (inv d ≫ v) = g
    rw [← hd, Category.assoc, IsIso.hom_inv_id_assoc, hv]
  · intro u hu
    apply (cancel_epi d).mp
    rw [IsIso.hom_inv_id_assoc]
    apply huniq
    rw [← Category.assoc, hd, hu]

end HodgeLean.Foundations.Program
