import HodgeLean.Foundations.QuotientDuality.ProperCycleRealSuspensionCoordinateNormalization
import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedCapSuspension

/-! # Literal real coordinates for the iterated complex normal product
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Consecutive normal real coordinates followed by successive literal head splittings give coordinates on the actual iterated real product.
Source: AlgebraicTopology.Singular.complexRealHomeomorph; properCycle_real_suspension_coordinates.
HC no distance; AV milestone no distance. -/
def properCycle_iterated_real_local_coordinates (d : ℕ) :
    (n : ℕ) → (Fin (d*2+n) → ℝ) ≃ₜ
      properCycle_real_support_space (TopCat.of (Fin d → ℂ)) n
  | 0 => (complexRealHomeomorph d).symm
  | n+1 => (properCycle_real_suspension_coordinates (d*2+n)).trans
      ((Homeomorph.refl ℝ).prodCongr (properCycle_iterated_real_local_coordinates d n))

/-- The literal iterated coordinates identify the point normal support with the original real origin.
Source: properCycle_iterated_real_local_coordinates; Complex.piCoordCLE.map_eq_zero_iff.
HC no distance; AV milestone no distance. -/
theorem properCycle_iterated_real_local_coordinates_point (d n : ℕ) :
    (properCycle_iterated_real_local_coordinates d n) ⁻¹'
      properCycle_real_point_support (TopCat.of (Fin d → ℂ)) {0} n =
      ({0} : Set (Fin (d*2+n) → ℝ)) := by
  induction n with
  | zero =>
    ext z
    exact (Complex.piCoordCLE d).symm.map_eq_zero_iff
  | succ n ih =>
    ext z
    change (z 0 = 0 ∧
      properCycle_iterated_real_local_coordinates d n (fun j => z j.succ) ∈
        properCycle_real_point_support (TopCat.of (Fin d → ℂ)) {0} n) ↔ z = 0
    have ht : properCycle_iterated_real_local_coordinates d n (fun j => z j.succ) ∈
        properCycle_real_point_support (TopCat.of (Fin d → ℂ)) {0} n ↔
        (fun j : Fin (d*2+n) => z j.succ) = 0 := Set.ext_iff.mp ih _
    rw [ht]
    constructor
    · rintro ⟨hz, ht⟩
      funext i
      exact Fin.cases hz (fun j => congrFun ht j) i
    · intro hz
      subst z
      exact ⟨rfl, rfl⟩

/-- The literal iterated coordinates give an actual isomorphism from the original punctured real pair to the recursive point-support pair.
Source: properCycle_iterated_real_local_coordinates_point; AlgebraicTopology.Singular.TopPair.isoOfSubset.
HC no distance; AV milestone no distance. -/
def properCycle_iterated_real_local_pair_iso (d n : ℕ) :
    puncturedPair ℝ (d*2+n) ≅
      TopPair.ofSubset (X := properCycle_real_support_space (TopCat.of (Fin d → ℂ)) n)
        (properCycle_real_point_support (TopCat.of (Fin d → ℂ)) {0} n)ᶜ :=
  TopPair.isoOfSubset (properCycle_iterated_real_local_coordinates d n)
    (fun z => not_congr (Set.ext_iff.mp (properCycle_iterated_real_local_coordinates_point d n) z))

/-- The literal iterated coordinate map preserves the original support complements.
Source: properCycle_iterated_real_local_coordinates_point.
HC no distance; AV milestone no distance. -/
theorem properCycle_iterated_real_local_complement_map (d n : ℕ) :
    Set.MapsTo
      (TopCat.ofHom ⟨properCycle_iterated_real_local_coordinates d n,
        (properCycle_iterated_real_local_coordinates d n).continuous⟩)
      ({0} : Set (Fin (d*2+n) → ℝ))ᶜ
      (properCycle_real_point_support (TopCat.of (Fin d → ℂ)) {0} n)ᶜ := by
  intro z hz hm
  exact hz ((Set.ext_iff.mp (properCycle_iterated_real_local_coordinates_point d n) z).mp hm)

/-- The successor point-pair comparison is exactly the original head-coordinate comparison followed by literal real-product base transport.
Source: properCycle_iterated_real_local_coordinates; properCycle_real_support_zero_pair_map.
HC no distance; AV milestone no distance. -/
theorem properCycle_iterated_real_local_pair_succ (d n : ℕ) :
    (properCycle_real_suspension_pair_iso (d*2+n)).hom ≫
      (properCycle_real_point_support_pair_iso (TopCat.of (Fin (d*2+n) → ℝ))).inv ≫
      properCycle_real_support_zero_pair_map
        (TopCat.ofHom ⟨properCycle_iterated_real_local_coordinates d n,
          (properCycle_iterated_real_local_coordinates d n).continuous⟩)
        {0} (properCycle_real_point_support (TopCat.of (Fin d → ℂ)) {0} n)
        (properCycle_iterated_real_local_complement_map d n) =
      (properCycle_iterated_real_local_pair_iso d (n+1)).hom := by
  ext z : 2 <;> rfl

end HodgeLean.Foundations.QuotientDuality
