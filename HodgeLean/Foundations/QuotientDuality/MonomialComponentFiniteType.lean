import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.CoordinateRootCover
import Mathlib.RingTheory.FiniteType

/-! Finite type over the retained chart for the smooth polynomial-root component. -/
noncomputable section
set_option maxHeartbeats 400000
open AlgebraicGeometry.TameMonomialCover.Helpers
namespace HodgeLean.Foundations.QuotientDuality

theorem root_component_finiteType_over_chart
    (k R A : Type*) [CommRing k] [CommRing R] [CommRing A] [Algebra k R]
    (n m : ℕ) (c : MvPolynomial (Fin n) k →ₐ[k] R)
    (i : R →+* A) (b : ULift.{0} (MvPolynomial (Fin n) k) →+* A) (hb : b.Etale)
    (hparam : b.comp (rootParameterMap k n m).toRingHom = i.comp c.toRingHom) :
    i.FiniteType := by
  let B := ULift.{0} (MvPolynomial (Fin n) k)
  letI : Algebra.FiniteType k B := Algebra.FiniteType.of_surjective
    (ULift.algEquiv.symm.toAlgHom : MvPolynomial (Fin n) k →ₐ[k] B)
    (ULift.algEquiv.symm.surjective)
  have hbase : (algebraMap k B).FiniteType := RingHom.finiteType_algebraMap.mpr inferInstance
  have hbft : b.FiniteType := by
    letI : Algebra B A := b.toAlgebra
    letI : Algebra.Etale B A := hb.toAlgebra
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hcoeff : i.comp (algebraMap k R) = b.comp (algebraMap k B) := by
    ext a
    have hC : rootParameterMap k n m (MvPolynomial.C a) = algebraMap k B a := by
      rw [rootParameterMap, AlgHom.comp_apply, MvPolynomial.expand_C]
      rfl
    change i (algebraMap k R a) = b (algebraMap k B a)
    calc
      _ = i (c (MvPolynomial.C a)) := congrArg i (c.commutes a).symm
      _ = b (rootParameterMap k n m (MvPolynomial.C a)) :=
        (RingHom.congr_fun hparam (MvPolynomial.C a)).symm
      _ = _ := congrArg b hC
  apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap k R)
  rw [hcoeff]
  exact hbft.comp hbase

#print axioms root_component_finiteType_over_chart
end HodgeLean.Foundations.QuotientDuality
