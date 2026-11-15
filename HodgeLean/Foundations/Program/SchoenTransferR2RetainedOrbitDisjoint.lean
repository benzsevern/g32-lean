import HodgeLean.Foundations.Program.SchoenCycleC1OrbitAssemblyHelpers

/-! # Disjoint deck translates of the retained section

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- Free fibres separate the translates of the specified retained section,
without choosing another component.
Source: Schoen (1988), §1, finite cyclic covers and their free fibres.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_retained_orbit_disjoint
    {Q P W B : Over (Spec ↧ℂ)} [LocallyOfFiniteType W.hom]
    (eQ : Q ≅ P) (ℓ : P ⟶ B) [IsClosedImmersion ℓ.left]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left]
    (β : W ⟶ B) (hproj : ι ≫ β = eQ.hom ≫ ℓ)
    (δ : W ⟶ W) (hd : δ ≫ β = β) (m : ℕ) (hm : m ≠ 0)
    (horder : End.of δ ^ m = 1)
    (hfibre : ∀ x : ComplexPoint P,
      ∃ z : ComplexPoint W, Point.map β z = Point.map ℓ x ∧
        Function.Injective (fun t : Fin m => Point.map (End.of δ ^ t.val).asHom z) ∧
        ∀ v : ComplexPoint W, Point.map β v = Point.map ℓ x →
          ∃ t : Fin m, Point.map (End.of δ ^ t.val).asHom z = v) :
    ∀ t u : Fin m, t ≠ u →
      Disjoint (Set.range (ι ≫ (End.of δ ^ t.val).asHom).left)
        (Set.range (ι ≫ (End.of δ ^ u.val).asHom).left) := by
  let c (t : Fin m) := ι ≫ (End.of δ ^ t.val).asHom
  have hc (t : Fin m) : IsClosedImmersion (c t).left :=
    s2e_translated_component_isClosedImmersion ι δ hm horder t.val
  have hcb (t : Fin m) : c t ≫ β = eQ.hom ≫ ℓ := by
    rw [Category.assoc, s2e_c1_generator_power_over β δ hd, hproj]
  have hinj (x : ComplexPoint Q) : Function.Injective
      (fun t : Fin m => Point.map (End.of δ ^ t.val).asHom (Point.map ι x)) := by
    obtain ⟨z, hz, hi, he⟩ := hfibre (Point.map eQ.hom x)
    apply (s2e_c1_deck_fibre_rebase β δ hd m hm horder
      (Point.map ℓ (Point.map eQ.hom x)) z hz hi he _ ?_).1
    rw [← Point.map_comp_apply, hproj]
    rfl
  haveI : Mono ℓ := Over.mono_of_mono_left ℓ
  intro t u htu
  have hdispoints : Disjoint (Set.range (Point.map (c t))) (Set.range (Point.map (c u))) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx⟩ ⟨y, hy⟩
    have hxy : Point.map (eQ.hom ≫ ℓ) x = Point.map (eQ.hom ≫ ℓ) y := by
      calc
        _ = Point.map β (Point.map (c t) x) := by
          rw [← Point.map_comp_apply, hcb]
        _ = Point.map β (Point.map (c u) y) :=
          congrArg (Point.map β) (hx.trans hy.symm)
        _ = _ := by rw [← Point.map_comp_apply, hcb]
    have heq : x = y := map_injective_of_mono (eQ.hom ≫ ℓ) hxy
    subst y
    exact htu (hinj x (hx.trans hy.symm))
  letI := hc t
  letI := hc u
  apply s2e_c11_complex_points_detect_intersection_aux W
    (Set.range (c t).left) (Set.range (c u).left)
    (c t).left.isClosedEmbedding.isClosed_range (c u).left.isClosedEmbedding.isClosed_range
  rw [← ComplexPoint.range_map_of_isImmersion_of_comm W Q (c t),
    ← ComplexPoint.range_map_of_isImmersion_of_comm W Q (c u)]
  exact hdispoints

#print axioms s4_assembly_retained_orbit_disjoint
end HodgeLean.Foundations.Program
