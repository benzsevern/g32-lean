import HodgeLean.Foundations.AbelianQuotient.H1Helpers
import HodgeLean.Foundations.AbelianQuotient.Surjectivity

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

/-- Countably many translates of a complex linear subspace contain no additional complex line. -/
theorem mem_range_of_countable_lifts {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (L : Submodule ℤ V) [Countable L] (I : W →ₗ[ℂ] V) (v : V)
    (h : ∀ t : ℂ, ∃ w, t • v - I w ∈ L) : v ∈ LinearMap.range I := by
  by_contra hv
  choose w hw using h
  let ψ : ℂ → L := fun t => ⟨t • v - I (w t), hw t⟩
  have hψ : Function.Injective ψ := by
    intro t s hts
    have he : t • v - I (w t) = s • v - I (w s) := congrArg Subtype.val hts
    by_contra hne
    have hne' : t - s ≠ 0 := sub_ne_zero.mpr hne
    apply hv
    refine ⟨(t - s)⁻¹ • (w t - w s), ?_⟩
    rw [map_smul, map_sub, inv_smul_eq_iff₀ hne', sub_smul]
    linear_combination (norm := module) -he
  have : Countable ℂ := hψ.countable
  exact not_countable_complex Set.countable_univ

/-- A tangent vector killed by projection comes from the retained kernel subvariety. -/
theorem quotient_tangent_kernel {A : Variety} {S : Subvariety A} (q : Projection S)
    (hk : {a : ComplexPoint A.X | Point.map q.map.hom a = 1} =
      Set.range (Point.map S.inclusion.hom))
    (I : (Fin (dim S.B.X.left) → ℂ) →ₗ[ℂ] (Fin (dim A.X.left) → ℂ))
    (Q : (Fin (dim A.X.left) → ℂ) →ₗ[ℂ] (Fin (dim q.Q.X.left) → ℂ))
    (hI : ∀ v, Additive.toMul (complexExponential A.X (dim A.X.left) (I v)) =
      Point.map S.inclusion.hom (Additive.toMul
        (complexExponential S.B.X (dim S.B.X.left) v)))
    (hQ : ∀ v, Additive.toMul (complexExponential q.Q.X (dim q.Q.X.left) (Q v)) =
      Point.map q.map.hom (Additive.toMul (complexExponential A.X (dim A.X.left) v)))
    {v : Fin (dim A.X.left) → ℂ} (hv : Q v = 0) : v ∈ LinearMap.range I := by
  have : Countable (abelianPeriodLattice A.X) :=
    (abelianLatticeBasis A.X).equivFun.toEquiv.countable_iff.mpr inferInstance
  apply mem_range_of_countable_lifts (abelianPeriodLattice A.X) I v
  intro t
  have ht : Additive.toMul (complexExponential A.X (dim A.X.left) (t • v)) ∈
      Set.range (Point.map S.inclusion.hom) := by
    rw [← hk]
    change Point.map q.map.hom _ = 1
    rw [← hQ, map_smul, hv, smul_zero, complexExponential_zero]
    rfl
  obtain ⟨s, hs⟩ := ht
  obtain ⟨w, hw⟩ := surjective_complexExponential S.B.X (dim S.B.X.left) (Additive.ofMul s)
  refine ⟨w, ?_⟩
  have hexp : complexExponential A.X (dim A.X.left) (t • v) =
      complexExponential A.X (dim A.X.left) (I w) := by
    apply Additive.toMul.injective
    rw [hI, hw]
    exact hs.symm
  change complexExponentialHom A.X (dim A.X.left) (t • v - I w) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr hexp

end HodgeLean.Foundations.AbelianQuotient
