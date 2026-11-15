import HodgeLean.Foundations.AbelianQuotient.QuotientTangent

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

/-- A complex line cannot be contained in a countable integer submodule unless it is zero. -/
theorem eq_zero_of_all_smul_mem {V : Type*} [AddCommGroup V] [Module ℂ V]
    (L : Submodule ℤ V) [Countable L] (v : V) (h : ∀ t : ℂ, t • v ∈ L) : v = 0 := by
  have hv := mem_range_of_countable_lifts L (0 : V →ₗ[ℂ] V) v
    (fun t => ⟨0, by simpa only [LinearMap.zero_apply, sub_zero] using h t⟩)
  obtain ⟨w, hw⟩ := hv
  exact hw.symm

/-- A map annihilating the point kernel annihilates the kernel of the analytic representation. -/
theorem analytic_kernel_of_point_kernel {A B T : Variety} (S : Subvariety A)
    (q : Hom A B) (f : Hom A T)
    (hk : {a : ComplexPoint A.X | Point.map q.hom a = 1} =
      Set.range (Point.map S.inclusion.hom))
    (hf : S.inclusion.hom ≫ f.hom = (1 : S.B.X ⟶ T.X))
    (Q : (Fin (dim A.X.left) → ℂ) →ₗ[ℂ] (Fin (dim B.X.left) → ℂ))
    (F : (Fin (dim A.X.left) → ℂ) →ₗ[ℂ] (Fin (dim T.X.left) → ℂ))
    (hQ : ∀ v, Additive.toMul (complexExponential B.X (dim B.X.left) (Q v)) =
      Point.map q.hom (Additive.toMul (complexExponential A.X (dim A.X.left) v)))
    (hF : ∀ v, Additive.toMul (complexExponential T.X (dim T.X.left) (F v)) =
      Point.map f.hom (Additive.toMul (complexExponential A.X (dim A.X.left) v))) :
    ∀ v, Q v = 0 → F v = 0 := by
  intro v hv
  have : Countable (abelianPeriodLattice T.X) :=
    (abelianLatticeBasis T.X).equivFun.toEquiv.countable_iff.mpr inferInstance
  have hpts : ∀ t : ℂ, Point.map f.hom
      (Additive.toMul (complexExponential A.X (dim A.X.left) (t • v))) = 1 := by
    intro t
    have htS : Additive.toMul (complexExponential A.X (dim A.X.left) (t • v)) ∈
        Set.range (Point.map S.inclusion.hom) := by
      rw [← hk]
      change Point.map q.hom _ = 1
      rw [← hQ, map_smul, hv, smul_zero, complexExponential_zero]
      rfl
    obtain ⟨s, hs⟩ := htS
    rw [← hs, ← Point.map_comp_apply, hf]
    exact MonObj.comp_one s
  apply eq_zero_of_all_smul_mem (abelianPeriodLattice T.X) (F v)
  intro t
  change complexExponential T.X (dim T.X.left) (t • F v) = 0
  apply Additive.toMul.injective
  rw [← F.map_smul t v, hF, hpts]
  rfl

end HodgeLean.Foundations.AbelianQuotient
