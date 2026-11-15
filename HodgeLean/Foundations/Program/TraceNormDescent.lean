module

public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Equiv.Basic

public section
namespace HodgeLean.Foundations.Program

/-- A trace norm gives descent of every class on which the norm is multiplication by its degree.
Source: Bredon, Introduction to Compact Transformation Groups (1972),
Chapter III, section 7, rational averaging. -/
theorem additive_descent_of_trace_norm
    {U V I J : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup I] [AddCommGroup J]
    (f : U →+ V) (i : U ≃+ I) (j : V →+ J) (hj : Function.Injective j)
    (t : V →+ I) (l : I →+ J) (N : V →+ V)
    (hfi : ∀ x, j (f x) = l (i x)) (hNl : ∀ x, l (t x) = j (N x))
    (d : ℕ) (hd : Function.Bijective (fun x : V => d • x))
    (z : V) (hz : N z = d • z) : ∃ x, f x = z := by
  obtain ⟨w, hw⟩ := hd.surjective z
  change d • w = z at hw
  have hNw : N w = z := hd.injective (by
    rw [← map_nsmul, hw, hz])
  refine ⟨i.symm (t w), hj ?_⟩
  rw [hfi, i.apply_symm_apply, hNl, hNw]

end HodgeLean.Foundations.Program
