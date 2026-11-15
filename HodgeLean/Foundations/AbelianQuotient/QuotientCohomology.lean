import HodgeLean.Foundations.AbelianQuotient.QuotientPeriods

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

/-- Every rational class vanishing on the kernel subvariety descends through projection. -/
theorem quotient_kernel_le_range {A : Variety} {S : Subvariety A} (q : Projection S)
    (hs : Function.Surjective (Point.map q.map.hom))
    (hk : {a : ComplexPoint A.X | Point.map q.map.hom a = 1} =
      Set.range (Point.map S.inclusion.hom)) :
    LinearMap.ker (homPullback S.inclusion.hom 1) ≤
      LinearMap.range (homPullback q.map.hom 1) := by
  intro x hx
  change homPullback S.inclusion.hom 1 x = 0 at hx
  obtain ⟨I, hI⟩ := spec_abelianHom_analyticRepresentation S.inclusion.hom
  obtain ⟨Q, hQ⟩ := spec_abelianHom_analyticRepresentation q.map.hom
  let φ : abelianPeriodLattice A.X →+ abelianPeriodLattice q.Q.X :=
    { toFun := fun l => ⟨Q l, homPullback_analyticRepresentation_mem_lattice q.map.hom Q hQ l⟩
      map_zero' := Subtype.ext (map_zero Q)
      map_add' := fun l m => Subtype.ext (map_add Q (l : Fin (dim A.X.left) → ℂ)
        (m : Fin (dim A.X.left) → ℂ)) }
  obtain ⟨N, ψ, hN, hψ⟩ := lattice_multiple_lift q.map hs Q hQ
  have hφψ : ∀ l, φ (ψ l) = N • l := by
    intro l
    apply Subtype.ext
    exact hψ l
  obtain ⟨eA, heA⟩ := spec_abelianPeriod_equiv A.X
  obtain ⟨eQ, heQ⟩ := spec_abelianPeriod_equiv q.Q.X
  have hχ : ∀ l, φ l = 0 → eA x l = 0 := by
    intro l hl
    have hQl : Q l = 0 := congrArg Subtype.val hl
    rw [heA]
    exact quotient_kernel_period_zero q hk I Q hI hQ x hx l hQl
  obtain ⟨chiQ, hchiQ⟩ := character_descent_of_multiple φ ψ N hN hφψ (eA x) hχ
  refine ⟨eQ.symm chiQ, ?_⟩
  apply abelianPeriod_injective A.X
  funext l
  rw [abelianPeriod_homPullback_analyticRepresentation q.map.hom Q hQ]
  change abelianPeriod q.Q.X (eQ.symm chiQ) (φ l) = abelianPeriod A.X x l
  rw [← heQ, eQ.apply_symm_apply, hchiQ, heA]

end HodgeLean.Foundations.AbelianQuotient
