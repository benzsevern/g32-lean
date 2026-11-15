import HodgeLean.Foundations.Program.SchoenCycleC1FibreOrbitHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1SliceHelpers

/-! # Assembly of the actual component orbit -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- Actual etale slice splitting and free exhaustive fibres assemble the
scheme-point component orbit of a specified generator. -/
theorem s2e_c1_component_orbit_of_slice_fibres
    (k m : ℕ) (hm : m ≠ 0) (W B : Over (Spec ↧ℂ))
    [LocallyOfFiniteType W.hom]
    (β : W ⟶ B) [IsFinite β.left]
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B)
    [IsClosedImmersion ℓ.left]
    [Etale (pullback.snd β.left ℓ.left)]
    [Surjective (pullback.snd β.left ℓ.left)]
    (d : W ⟶ W) (hd : d ≫ β = β) (horder : End.of d ^ m = 1)
    (hfibre : ∀ x : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))),
      ∃ z : ComplexPoint W, Point.map β z = Point.map ℓ x ∧
        Function.Injective (fun t : Fin m => Point.map (End.of d ^ t.val).asHom z) ∧
        (∀ v : ComplexPoint W, Point.map β v = Point.map ℓ x →
          ∃ t : Fin m, Point.map (End.of d ^ t.val).asHom z = v)) :
    ∃ ι : (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) ⟶ W,
      IsClosedImmersion ι.left ∧ ι ≫ β = ℓ ∧
      (∀ t : Fin m, IsClosedImmersion (ι ≫ (End.of d ^ t.val).asHom).left) ∧
      (∀ t u : Fin m, t ≠ u →
        Disjoint (Set.range (ι ≫ (End.of d ^ t.val).asHom).left)
          (Set.range (ι ≫ (End.of d ^ u.val).asHom).left)) ∧
      (∀ w : W.left, β.left w ∈ Set.range ℓ.left ↔
        ∃ t : Fin m, w ∈ Set.range (ι ≫ (End.of d ^ t.val).asHom).left) := by
  let P := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  haveI : LocallyOfFiniteType P.hom :=
    inferInstanceAs (LocallyOfFiniteType (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
  obtain ⟨n, hn, s, hs, hsec, _, hex⟩ := s2e_c1_slice_sections k W B β ℓ
  let ι := s ⟨0, hn⟩
  haveI : IsClosedImmersion ι.left := hs ⟨0, hn⟩
  have hι : ι ≫ β = ℓ := hsec ⟨0, hn⟩
  let c (t : Fin m) := ι ≫ (End.of d ^ t.val).asHom
  have hc (t : Fin m) : IsClosedImmersion (c t).left :=
    s2e_translated_component_isClosedImmersion ι d hm horder t.val
  have hcb (t : Fin m) : c t ≫ β = ℓ := by
    change (ι ≫ (End.of d ^ t.val).asHom) ≫ β = ℓ
    rw [Category.assoc, s2e_c1_generator_power_over β d hd, hι]
  have horbit (x : ComplexPoint P) :
      Function.Injective (fun t : Fin m => Point.map (End.of d ^ t.val).asHom (Point.map ι x)) ∧
      (∀ v : ComplexPoint W, Point.map β v = Point.map ℓ x →
        ∃ t : Fin m, Point.map (End.of d ^ t.val).asHom (Point.map ι x) = v) := by
    obtain ⟨z, hz, hi, he⟩ := hfibre x
    apply s2e_c1_deck_fibre_rebase β d hd m hm horder (Point.map ℓ x) z hz hi he
    rw [← Point.map_comp_apply, hι]
  haveI : Mono ℓ := Over.mono_of_mono_left ℓ
  have hdispoints (t u : Fin m) (htu : t ≠ u) :
      Disjoint (Set.range (Point.map (c t))) (Set.range (Point.map (c u))) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx⟩ ⟨y, hy⟩
    have hxy : Point.map ℓ x = Point.map ℓ y := by
      calc
        Point.map ℓ x = Point.map β (Point.map (c t) x) := by
          rw [← Point.map_comp_apply, hcb]
        _ = Point.map β (Point.map (c u) y) := congrArg (Point.map β) (hx.trans hy.symm)
        _ = Point.map ℓ y := by rw [← Point.map_comp_apply, hcb]
    have heq : x = y := map_injective_of_mono ℓ hxy
    subst y
    exact htu ((horbit x).1 (hx.trans hy.symm))
  refine ⟨ι, inferInstance, hι, hc, ?_, ?_⟩
  · intro t u htu
    haveI := hc t
    haveI := hc u
    apply s2e_c11_complex_points_detect_intersection_aux W
      (Set.range (c t).left) (Set.range (c u).left)
      (c t).left.isClosedEmbedding.isClosed_range
      (c u).left.isClosedEmbedding.isClosed_range
    rw [show Point.underlying ⁻¹' Set.range (c t).left = Set.range (Point.map (c t)) from
      (range_map_of_closedImmersion (c t)).symm,
      show Point.underlying ⁻¹' Set.range (c u).left = Set.range (Point.map (c u)) from
      (range_map_of_closedImmersion (c u)).symm]
    exact hdispoints t u htu
  · intro w
    constructor
    · intro hw
      obtain ⟨j, x, hx⟩ := (hex w).mp hw
      let A (t : Fin m) : Set P.left := (s j).left ⁻¹' Set.range (c t).left
      have hA (t : Fin m) : IsClosed (A t) := by
        haveI := hc t
        exact (c t).left.isClosedEmbedding.isClosed_range.preimage (s j).left.continuous
      have hcover : ∀ y : ComplexPoint P, ∃ t : Fin m, y.underlying ∈ A t := by
        intro y
        have hsy : Point.map β (Point.map (s j) y) = Point.map ℓ y := by
          rw [← Point.map_comp_apply, hsec]
        obtain ⟨t, ht⟩ := (horbit y).2 (Point.map (s j) y) hsy
        haveI := hc t
        have hr : Point.map (s j) y ∈ Set.range (Point.map (c t)) := ⟨y, ht⟩
        rw [range_map_of_closedImmersion (c t)] at hr
        change (Point.map (s j) y).underlying ∈ Set.range (c t).left at hr
        refine ⟨t, ?_⟩
        change (s j).left y.underlying ∈ Set.range (c t).left
        simpa only [Point.underlying_map] using hr
      obtain ⟨t, ht⟩ := s2e_c11_complex_points_detect_complement_aux P m A hA hcover x
      exact ⟨t, hx ▸ ht⟩
    · rintro ⟨t, x, rfl⟩
      refine ⟨x, ?_⟩
      exact (congrArg (fun f : P ⟶ B => f.left x) (hcb t)).symm

end HodgeLean.Foundations.Program
