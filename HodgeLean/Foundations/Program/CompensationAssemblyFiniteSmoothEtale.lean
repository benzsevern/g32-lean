import HodgeLean.Foundations.Program.CompensationAssemblyFiniteDegree
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Flat.Stability

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
open scoped TensorProduct nonZeroDivisors
namespace HodgeLean.Foundations.Program

theorem cq_finite_smooth_domain_etale (R B : Type) [CommRing R] [IsDomain R]
    [CharZero R] [CommRing B] [IsDomain B] [Algebra R B]
    [Module.Finite R B] [Algebra.Smooth R B]
    (hinj : Function.Injective (algebraMap R B)) : Algebra.Etale R B := by
  let K := FractionRing R
  let C := K ⊗[R] B
  letI : Algebra B C := Algebra.TensorProduct.rightAlgebra
  have hS : Algebra.algebraMapSubmonoid B R⁰ ≤ B⁰ :=
    map_le_nonZeroDivisors_of_injective (algebraMap R B) hinj le_rfl
  letI : IsLocalization (Algebra.algebraMapSubmonoid B R⁰) C :=
    (Algebra.isLocalization_iff_isPushout R⁰ K).mpr inferInstance
  letI : IsDomain C := IsLocalization.isDomain_of_le_nonZeroDivisors C hS
  letI : Field C :=
    (isField_of_isIntegral_of_isField' (R := K) (S := C) (Field.toIsField K)).toField
  letI : Algebra.FormallyUnramified K C := Algebra.FormallyUnramified.of_isSeparable K C
  letI : Module.Flat R (KaehlerDifferential R B) :=
    Module.Flat.trans R B (KaehlerDifferential R B)
  have he := KaehlerDifferential.tensorKaehlerEquivBase R K B C
  letI : Subsingleton (K ⊗[R] KaehlerDifferential R B) := he.toEquiv.subsingleton
  have hi := Module.Flat.tensorProduct_mk_injective (R := R) (S := K)
    (M := KaehlerDifferential R B)
  letI : Algebra.FormallyUnramified R B := ⟨hi.subsingleton⟩
  exact Algebra.Etale.of_formallyUnramified_of_flat

end HodgeLean.Foundations.Program
