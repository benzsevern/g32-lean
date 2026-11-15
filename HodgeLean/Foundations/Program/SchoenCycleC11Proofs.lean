import HodgeLean.Foundations.Program.SchoenCycleGeometryDefs
import HodgeLean.Foundations.Program.SchoenCycleC11PreProofs
import HodgeLean.Foundations.Program.SchoenCycleC11AffineAssemblyHelpers

/-! # Finite etale covers of projective space
Implication from an actual finite etale surjection to disjoint scheme sections
whose ranges exhaust the source. Branch avoidance and residual deck transport
are later units. HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A finite etale projective-space cover has actual disjoint copies of its base.
Source: Schoen (1988), printed p. 15, etale cover over the lifted projective slice;
Hartshorne, Algebraic Geometry, Appendix B, comparison with complex topology. -/
theorem s2e_chain_projective_etale_sections_aux
    (k : ℕ) (W : Over (Spec ↧ℂ))
    (β : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsFinite β.left] [Etale β.left] [Surjective β.left] :
    ∃ (n : ℕ) (_ : 0 < n)
      (ι : Fin n → (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ W)),
      (∀ i, IsClosedImmersion (ι i).left) ∧
      (∀ i, ι i ≫ β = 𝟙 _) ∧
      (∀ i j, i ≠ j → Disjoint (Set.range (ι i).left) (Set.range (ι j).left)) ∧
      (∀ w : W.left, ∃ i, w ∈ Set.range (ι i).left) := by
  classical
  have : LocallyOfFiniteType
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom :=
    inferInstanceAs (LocallyOfFiniteType (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
  have : LocallyOfFiniteType W.hom := by
    rw [← Over.w β]
    change LocallyOfFiniteType (β.left ≫ ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    infer_instance
  obtain ⟨hcover, hfin⟩ := s2e_c11_projective_finite_etale_analytic_cover k W β
  obtain ⟨hsc, hlpc⟩ := s2e_c11_projective_simply_connected_aux k
  have := hsc
  have := hlpc
  obtain ⟨n, hn, e, he⟩ := s2e_c11_finite_cover_trivialization_aux
    (Point.map β) hcover
    (s2e_c11_finite_surjective_complex_points_aux W _ β) hfin
  obtain ⟨s, hs, hdis, hex⟩ := s2e_c11_trivialization_sections
    (Point.map β) e he
  choose ι hι hsec using fun i ↦
    s2e_c11_projective_section_algebraization_aux k W β (s i) (s i).continuous (hs i)
  refine ⟨n, hn, ι, s2e_c11_sections_scheme_assembly_aux k n W β ι hsec ?_ ?_⟩
  · intro i j hij
    rw [hι i, hι j]
    exact hdis i j hij
  · intro w
    obtain ⟨i, hi⟩ := hex w
    exact ⟨i, (hι i).symm ▸ hi⟩

end HodgeLean.Foundations.Program
