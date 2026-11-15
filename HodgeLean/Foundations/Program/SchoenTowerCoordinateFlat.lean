import HodgeLean.Foundations.Program.SchoenTowerCoordinateUnramified
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Flat.TorsionFree

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeLean.Foundations.Program

/-- Over an algebraically closed field, a nonzero differential detects a transcendental element
in a domain.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 5, integral elements. -/
theorem s2t_transcendental_of_nonzero_derivation {K A M : Type*}
    [Field K] [IsAlgClosed K] [CommRing A] [IsDomain A] [Algebra K A]
    [AddCommGroup M] [Module K M] [Module A M] (D : Derivation K A M)
    (g : A) (hg : D g ≠ 0) : Transcendental K g := by
  intro h
  have hi := h.isIntegral
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hi)
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one K g hdeg
  apply hg
  rw [← hc, D.map_algebraMap]

/-- A polynomial coordinate with a nonzero differential in a domain is flat over an
algebraically closed coefficient field.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 3.7; torsion-free
modules over a principal ideal domain are flat. -/
theorem s2t_polynomial_flat_of_nonzero_differential {K A M : Type*}
    [Field K] [IsAlgClosed K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra (Polynomial K) A] [IsScalarTower K (Polynomial K) A]
    [AddCommGroup M] [Module K M] [Module A M] (D : Derivation K A M)
    (hg : D (algebraMap (Polynomial K) A Polynomial.X) ≠ 0) :
    Module.Flat (Polynomial K) A := by
  have ht := s2t_transcendental_of_nonzero_derivation D _ hg
  have heval : Polynomial.aeval (algebraMap (Polynomial K) A Polynomial.X) =
      IsScalarTower.toAlgHom K (Polynomial K) A := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X]
    rfl
  have hinj : Function.Injective (algebraMap (Polynomial K) A) := by
    change Function.Injective (IsScalarTower.toAlgHom K (Polynomial K) A)
    rw [← heval]
    exact transcendental_iff_injective.mp ht
  letI : Module.IsTorsionFree (Polynomial K) A :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  infer_instance

end HodgeLean.Foundations.Program
