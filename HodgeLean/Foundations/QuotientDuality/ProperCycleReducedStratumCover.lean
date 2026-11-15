import HodgeConjecture.Lemmas.AlgebraicGeometry.Stratification.ClosedFiltration
import HodgeConjecture.Lemmas.AlgebraicGeometry.Stratification.Analytification

/-! # Actual complex points on the finite reduced smooth strata -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Every original complex point of a closed support comes from one actual smooth stratum of its finite reduced filtration.
Source: EGA IV, 6.12.5 and 17.5.1, generic smoothness and Noetherian induction;
Hartshorne, Algebraic Geometry, II.3.
HC no distance; AV milestone no distance. -/
lemma properCycle_reduced_stratum_complex_cover
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [NoetherianSpace X.left]
    (S : Closeds X.left) (x : ComplexPoint X) (hx : x.underlying ∈ S) :
    ∃ k < (reducedSmoothStratification X.hom S).length,
      ∃ z : ComplexPoint (Over.mk
        (reducedClosedSmoothPieceι X.hom (reducedSmoothClosedFiltration X.hom S k) ≫ X.hom)),
        Point.map (reducedClosedSmoothPieceMap X (reducedSmoothClosedFiltration X.hom S k)) z = x := by
  classical
  have hend : x.underlying ∉ reducedSmoothClosedFiltration X.hom S
      (reducedSmoothStratification X.hom S).length := by
    rw [reducedSmoothClosedFiltration_length]
    exact Set.notMem_empty _
  have hex : ∃ k : ℕ, x.underlying ∉ reducedSmoothClosedFiltration X.hom S k := ⟨_, hend⟩
  have hm0 : Nat.find hex ≠ 0 := by
    intro hm
    have hh := Nat.find_spec hex
    rw [hm, reducedSmoothClosedFiltration_zero] at hh
    exact hh hx
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hkle : Nat.find hex ≤ (reducedSmoothStratification X.hom S).length :=
    Nat.find_le (h := hex) hend
  have hklt : k < (reducedSmoothStratification X.hom S).length := by omega
  have hmem : x.underlying ∈ reducedSmoothClosedFiltration X.hom S k := by
    by_contra hn
    exact Nat.find_min hex (by omega) hn
  have hnot : x.underlying ∉ reducedSmoothClosedFiltration X.hom S (k + 1) := by
    simpa only [hk] using Nat.find_spec hex
  refine ⟨k, hklt, ?_⟩
  change x ∈ Set.range (Point.map (reducedClosedSmoothPieceMap X
    (reducedSmoothClosedFiltration X.hom S k)))
  rw [range_map_of_isImmersion X]
  change x.underlying ∈ Set.range
    (reducedClosedSmoothPieceι X.hom (reducedSmoothClosedFiltration X.hom S k))
  rw [reducedSmoothClosedFiltration_layer]
  exact ⟨hmem, hnot⟩

end HodgeLean.Foundations.QuotientDuality
