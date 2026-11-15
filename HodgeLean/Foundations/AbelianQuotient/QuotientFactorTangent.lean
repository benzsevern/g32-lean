import HodgeLean.Foundations.AbelianQuotient.ComplementMap
import HodgeLean.Foundations.AbelianQuotient.QuotientTangent

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

set_option maxRecDepth 2000 in
/-- A factor of the difference map has tangent kernel contained in the original subvariety. -/
theorem kernel_of_difference_factor {A B : Variety} (S : Subvariety A)
    (N : ℕ) (hN : 0 < N) (r : Hom A S.B) (q : Hom A B) (i : Hom B A)
    (hqi : q.hom ≫ i.hom = (complementMap S N r).hom)
    (I : (Fin (dim S.B.X.left) → ℂ) →ₗ[ℂ] (Fin (dim A.X.left) → ℂ))
    (Q : (Fin (dim A.X.left) → ℂ) →ₗ[ℂ] (Fin (dim B.X.left) → ℂ))
    (hI : ∀ v, Additive.toMul (complexExponential A.X (dim A.X.left) (I v)) =
      Point.map S.inclusion.hom (Additive.toMul
        (complexExponential S.B.X (dim S.B.X.left) v)))
    (hQ : ∀ v, Additive.toMul (complexExponential B.X (dim B.X.left) (Q v)) =
      Point.map q.hom (Additive.toMul (complexExponential A.X (dim A.X.left) v)))
    {v : Fin (dim A.X.left) → ℂ} (hv : Q v = 0) : v ∈ LinearMap.range I := by
  have : Countable (abelianPeriodLattice A.X) :=
    (abelianLatticeBasis A.X).equivFun.toEquiv.countable_iff.mpr inferInstance
  have hNv : (N : ℂ) • v ∈ LinearMap.range I := by
    apply mem_range_of_countable_lifts (abelianPeriodLattice A.X) I ((N : ℂ) • v)
    intro t
    let a := Additive.toMul (complexExponential A.X (dim A.X.left) (t • v))
    have hqa : Point.map q.hom a = 1 := by
      rw [← hQ, map_smul, hv, smul_zero, complexExponential_zero]
      rfl
    have hea : Point.map (complementMap S N r).hom a = 1 := by
      rw [← hqi, Point.map_comp_apply, hqa]
      exact MonObj.one_comp i.hom
    change a ≫ ((multiplication A N).hom / (r.hom ≫ S.inclusion.hom)) = 1 at hea
    rw [GrpObj.comp_div, multiplication_nat_hom, GrpObj.comp_zpow,
      Category.comp_id, zpow_natCast, ← Category.assoc] at hea
    have heq := div_eq_one.mp hea
    change a ^ N = Point.map S.inclusion.hom (Point.map r.hom a) at heq
    obtain ⟨w, hw⟩ := surjective_complexExponential S.B.X (dim S.B.X.left)
      (Additive.ofMul (Point.map r.hom a))
    refine ⟨w, ?_⟩
    have hexp : complexExponential A.X (dim A.X.left) (t • ((N : ℂ) • v)) =
        complexExponential A.X (dim A.X.left) (I w) := by
      apply Additive.toMul.injective
      rw [hI, hw]
      change Additive.toMul (complexExponential A.X (dim A.X.left) (t • ((N : ℂ) • v))) =
        Point.map S.inclusion.hom (Point.map r.hom a)
      have ht : t • ((N : ℂ) • v) = N • (t • v) := by
        rw [smul_comm, Nat.cast_smul_eq_nsmul]
      rw [ht]
      exact (congrArg Additive.toMul
        ((complexExponentialHom A.X (dim A.X.left)).map_nsmul N (t • v))).trans heq
    change complexExponentialHom A.X (dim A.X.left) (t • ((N : ℂ) • v) - I w) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hexp
  obtain ⟨w, hw⟩ := hNv
  refine ⟨(N : ℂ)⁻¹ • w, ?_⟩
  rw [map_smul, hw, smul_smul,
    inv_mul_cancel₀ (show (N : ℂ) ≠ 0 by exact_mod_cast hN.ne'), one_smul]

end HodgeLean.Foundations.AbelianQuotient
