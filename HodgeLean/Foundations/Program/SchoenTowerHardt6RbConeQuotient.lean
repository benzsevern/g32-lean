import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCompactIntrinsicBoundary
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCompactRayEndpoint
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbConeFiberEquality
import Mathlib.Topology.Order.Compact

/-! Compact convex carriers are actual quotient cones over their intrinsic boundaries. -/
noncomputable section
namespace HodgeLean.Foundations.Program
open Topology

theorem s2v_hardt6rb_cone_quotient {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C : Set E) (hcompact : IsCompact C) (hconv : Convex ℝ C)
    (a : E) (ha : a ∈ intrinsicInterior ℝ C) (hne : (C \ intrinsicInterior ℝ C).Nonempty) :
    ∃ p : ↥(C \ intrinsicInterior ℝ C) × Set.Icc (0 : ℝ) 1 → C,
      IsQuotientMap p ∧
      (∀ z, (p z).val = AffineMap.lineMap a z.1.val z.2.val) ∧
      (∀ z w, p z = p w ↔ z.2 = w.2 ∧ (z.2.val = 0 ∨ z.1 = w.1)) := by
  letI : CompactSpace ↥(C \ intrinsicInterior ℝ C) :=
    isCompact_iff_compactSpace.mp (s2v_hardt6rb_compact_intrinsic_boundary C hcompact)
  let p : ↥(C \ intrinsicInterior ℝ C) × Set.Icc (0 : ℝ) 1 → C := fun z =>
    ⟨AffineMap.lineMap a z.1.val z.2.val,
      hconv.segment_subset (intrinsicInterior_subset ha) z.1.property.1
        (lineMap_mem_segment ℝ a z.1.val z.2.property)⟩
  have hp : Continuous p := by
    apply Continuous.subtype_mk
    simp only [AffineMap.lineMap_apply_module']
    exact ((continuous_subtype_val.comp continuous_snd).smul
      ((continuous_subtype_val.comp continuous_fst).sub continuous_const)).add continuous_const
  have hs : Function.Surjective p := by
    intro x
    by_cases hxa : x.val = a
    · obtain ⟨y, hy⟩ := hne
      refine ⟨(⟨y, hy⟩, ⟨0, le_rfl, zero_le_one⟩), Subtype.ext ?_⟩
      exact (AffineMap.lineMap_apply_zero a y).trans hxa.symm
    · obtain ⟨y, hy, t, ht, he⟩ := s2v_hardt6rb_compact_ray_endpoint C hcompact a
        (intrinsicInterior_subset ha) x.val x.property hxa
      exact ⟨(⟨y, hy⟩, ⟨t, ht⟩), Subtype.ext he⟩
  refine ⟨p, hp.isClosedMap.isQuotientMap hp hs, fun _ => rfl, ?_⟩
  intro z w
  change (⟨AffineMap.lineMap a z.1.val z.2.val, _⟩ : C) =
    ⟨AffineMap.lineMap a w.1.val w.2.val, _⟩ ↔ _
  rw [Subtype.ext_iff, s2v_hardt6rb_cone_fiber_equality C hconv a ha z.1.property w.1.property
    z.2.property.1 w.2.property.1]
  constructor
  · rintro ⟨ht, hx⟩
    exact ⟨Subtype.ext ht, hx.imp id Subtype.ext⟩
  · rintro ⟨ht, hx⟩
    exact ⟨congrArg Subtype.val ht, hx.imp id (congrArg Subtype.val)⟩

end HodgeLean.Foundations.Program
