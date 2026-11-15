import HodgeLean.Foundations.AbelianQuotient.IntegralInverse

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.AbelianQuotient

/-- The point kernel identity makes the subvariety map trivial after projection. -/
theorem quotient_composition_one {A : Variety} {S : Subvariety A} (q : Projection S)
    (hk : {a : ComplexPoint A.X | Point.map q.map.hom a = 1} =
      Set.range (Point.map S.inclusion.hom)) :
    S.inclusion.hom ≫ q.map.hom = (1 : S.B.X ⟶ q.Q.X) := by
  apply abq_over_hom_ext_of_point_map
  funext s
  have hs : Point.map S.inclusion.hom s ∈
      {a : ComplexPoint A.X | Point.map q.map.hom a = 1} := by
    rw [hk]
    exact ⟨s, rfl⟩
  rw [Point.map_comp_apply]
  change Point.map q.map.hom (Point.map S.inclusion.hom s) = s ≫ (1 : S.B.X ⟶ q.Q.X)
  rw [MonObj.comp_one]
  exact hs

/-- A quotient pullback restricts to zero on its kernel subvariety. -/
theorem quotient_range_le_kernel {A : Variety} {S : Subvariety A} (q : Projection S)
    (hk : {a : ComplexPoint A.X | Point.map q.map.hom a = 1} =
      Set.range (Point.map S.inclusion.hom)) :
    LinearMap.range (homPullback q.map.hom 1) ≤
      LinearMap.ker (homPullback S.inclusion.hom 1) := by
  rintro _ ⟨x, rfl⟩
  change (homPullback S.inclusion.hom 1) ((homPullback q.map.hom 1) x) = 0
  rw [← LinearMap.comp_apply, ← spec_homPullback_comp,
    quotient_composition_one q hk, spec_homPullback_one, LinearMap.zero_apply]

set_option maxRecDepth 2000 in
/-- The H¹ multiplication equation follows from its algebraic multiplication identity. -/
theorem multiplication_section_pullback {A B : Variety} (f : Hom A B) (s : Hom B A)
    (N : ℕ) (h : s.hom ≫ f.hom = (multiplication B N).hom) :
    (homPullback s.hom 1).comp (homPullback f.hom 1) =
      (N : ℚ) • (LinearMap.id : HQ B.X 1 →ₗ[ℚ] HQ B.X 1) := by
  rw [← spec_homPullback_comp, h, multiplication_nat_hom,
    spec_homPullback_zpow, spec_homPullback_id, Int.cast_natCast]

/-- For a finite-kernel surjection the integral inverse supplies a multiplication section. -/
theorem isogeny_multiplication_section {A B : Variety} (f : Hom A B)
    (hi : ccm2_IsogenyOnPoints f.hom) :
    ∃ (N : ℕ) (s : Hom B A), 0 < N ∧
      s.hom ≫ f.hom = (multiplication B N).hom ∧
      (homPullback s.hom 1).comp (homPullback f.hom 1) =
        (N : ℚ) • (LinearMap.id : HQ B.X 1 →ₗ[ℚ] HQ B.X 1) := by
  obtain ⟨N, s, hN, h, _⟩ := integral_inverse A B f.hom inferInstance hi
  exact ⟨N, s, hN, h, multiplication_section_pullback f s N h⟩

end HodgeLean.Foundations.AbelianQuotient
