import HodgeLean.Foundations.AbelianQuotient.LatticeNaturality
import HodgeLean.Foundations.AbelianQuotient.QuotientFactorTangent

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

/-- Surjectivity on periods removes the finite ambiguity in a tangent-kernel description. -/
theorem point_kernel_of_period_surjective {A B : Variety} (S : Subvariety A) (q : Hom A B)
    (hs : S.inclusion.hom ≫ q.hom = (1 : S.B.X ⟶ B.X))
    (I : (Fin (dim S.B.X.left) → ℂ) →ₗ[ℂ] (Fin (dim A.X.left) → ℂ))
    (Q : (Fin (dim A.X.left) → ℂ) →ₗ[ℂ] (Fin (dim B.X.left) → ℂ))
    (hI : ∀ v, Additive.toMul (complexExponential A.X (dim A.X.left) (I v)) =
      Point.map S.inclusion.hom (Additive.toMul
        (complexExponential S.B.X (dim S.B.X.left) v)))
    (hQ : ∀ v, Additive.toMul (complexExponential B.X (dim B.X.left) (Q v)) =
      Point.map q.hom (Additive.toMul (complexExponential A.X (dim A.X.left) v)))
    (ψ : abelianPeriodLattice A.X →+ abelianPeriodLattice B.X)
    (hψs : Function.Surjective ψ)
    (hψ : ∀ x l, abelianPeriod A.X (homPullback q.hom 1 x) l = abelianPeriod B.X x (ψ l))
    (hker : ∀ v, Q v = 0 → v ∈ LinearMap.range I) :
    {a : ComplexPoint A.X | Point.map q.hom a = 1} = Set.range (Point.map S.inclusion.hom) := by
  ext a
  constructor
  · intro hqa
    obtain ⟨v, hv⟩ := surjective_complexExponential A.X (dim A.X.left) (Additive.ofMul a)
    have hqv : Q v ∈ abelianPeriodLattice B.X := by
      change complexExponential B.X (dim B.X.left) (Q v) = 0
      apply Additive.toMul.injective
      rw [hQ, hv]
      exact hqa
    obtain ⟨l, hl⟩ := hψs (⟨Q v, hqv⟩ : abelianPeriodLattice B.X)
    have hQl : Q l = Q v :=
      (analytic_lattice_map_eq q Q hQ ψ hψ l).trans (congrArg Subtype.val hl)
    have hzero : Q (v - (l : Fin (dim A.X.left) → ℂ)) = 0 := by
      rw [map_sub, hQl, sub_self]
    obtain ⟨w, hw⟩ := hker _ hzero
    refine ⟨Additive.toMul (complexExponential S.B.X (dim S.B.X.left) w), ?_⟩
    rw [← hI, hw]
    change Additive.toMul (complexExponentialHom A.X (dim A.X.left)
      (v - (l : Fin (dim A.X.left) → ℂ))) = a
    rw [map_sub]
    have hl0 : complexExponential A.X (dim A.X.left) l = 0 := l.property
    change Additive.toMul (complexExponential A.X (dim A.X.left) v -
      complexExponential A.X (dim A.X.left) l) = a
    rw [hl0, sub_zero, hv]
    rfl
  · rintro ⟨s, rfl⟩
    change Point.map q.hom (Point.map S.inclusion.hom s) = 1
    rw [← Point.map_comp_apply, hs]
    exact MonObj.comp_one s

end HodgeLean.Foundations.AbelianQuotient
