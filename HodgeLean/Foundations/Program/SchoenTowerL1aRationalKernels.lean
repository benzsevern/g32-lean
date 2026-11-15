import Mathlib.RingTheory.Ideal.Maps

/-! # Kernels of rational evaluation maps

Rational evaluation maps sharing the actual constant section map are
determined by their kernels. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Evaluation maps with the same actual constants and the same kernel are equal.
Source: Hartshorne, Algebraic Geometry, II.2, rational points and residue fields. -/
theorem s2v_l1a_rational_evaluations_eq_of_kernel_eq
    {R K : Type*} [CommRing R] [CommRing K]
    (c : K →+* R) (f g : R →+* K)
    (hf : f.comp c = RingHom.id K) (hg : g.comp c = RingHom.id K)
    (hker : RingHom.ker f = RingHom.ker g) : f = g := by
  have hf' (k : K) : f (c k) = k := DFunLike.congr_fun hf k
  have hg' (k : K) : g (c k) = k := DFunLike.congr_fun hg k
  apply RingHom.ext
  intro r
  have hr : r - c (f r) ∈ RingHom.ker f := by
    change f (r - c (f r)) = 0
    rw [map_sub, hf', sub_self]
  rw [hker] at hr
  change g (r - c (f r)) = 0 at hr
  rw [map_sub, hg', sub_eq_zero] at hr
  exact hr.symm

end HodgeLean.Foundations.Program
