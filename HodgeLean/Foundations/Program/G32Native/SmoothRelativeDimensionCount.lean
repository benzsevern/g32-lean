import HodgeLean.Ported.Hironaka.Scheme.Snc.RelativeDimensionConstant

/-! Recover constant smooth relative dimension from its pointwise dimension count. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A constant dimension count on a smooth scheme determines its relative dimension. -/
theorem g32l4_smoothOfRelativeDimension_of_dimCount
    {k : Type*} [Field k] [PerfectField k] {X : Scheme}
    (f : X ⟶ Spec (.of k)) [Smooth f] (n : ℕ)
    (h : ∀ x : X, dimCount f x = n) : SmoothOfRelativeDimension n f := by
  apply smoothOfRelativeDimension_of_forall_exists_affineOpen f n
  intro x
  obtain ⟨V, hV, hxV, m, hstd⟩ := exists_affineOpen_isStandardSmoothOfRelativeDimension' f x
  have hm : dimCount f x = m :=
    ringKrullDim_stalk_add_trdeg_of_isStandardSmoothOfRelativeDimension f m hV hxV hstd
  have hmn : m = n := by
    have heq := hm.symm.trans (h x)
    exact_mod_cast heq
  subst m
  exact ⟨V, hV, hxV, hstd⟩

end HodgeLean.Foundations.Program
