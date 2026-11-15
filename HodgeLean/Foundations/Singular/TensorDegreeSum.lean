import HodgeLean.Foundations.Singular.RationalTensorZero
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.Finset.NatAntidiagonal

/-! The actual total tensor chain degree as its finite direct sum of bidegrees. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct DirectSum
namespace HodgeLean.Foundations.Singular

/-- The finite set of actual bidegrees in a total chain degree.
Source: Hatcher, Algebraic Topology, §3.2, the total tensor complex. -/
abbrev tensorDegreeIndex (n : ℕ) := ↥(Finset.antidiagonal n)

/-- The actual tensor factor associated to one bidegree of two rational complexes.
Source: Hatcher, Algebraic Topology, §3.2, the total tensor complex. -/
abbrev tensorDegreeFactor (K L : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (a : tensorDegreeIndex n) := K.X a.1.1 ⊗[ℚ] L.X a.1.2

/-- Map the actual total tensor chain degree to the finite direct sum of its bidegrees.
Source: Hatcher, Algebraic Topology, §3.2, the direct-sum description of the tensor complex. -/
def tensorDegreeToSum (K L : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    (HomologicalComplex.tensorObj K L).X n →ₗ[ℚ]
      ⨁ a : tensorDegreeIndex n, tensorDegreeFactor K L n a :=
  (HomologicalComplex.mapBifunctorDesc (K₁ := K) (K₂ := L)
    (F := curriedTensor (ModuleCat ℚ)) (c := ComplexShape.down ℕ)
    (fun p q hpq => ModuleCat.ofHom
      (DirectSum.lof ℚ (tensorDegreeIndex n) (tensorDegreeFactor K L n)
        ⟨(p, q), Finset.mem_antidiagonal.mpr hpq⟩))).hom

/-- Map the finite sum of actual bidegrees into the actual total tensor chain degree.
Source: Hatcher, Algebraic Topology, §3.2, the direct-sum description of the tensor complex. -/
def tensorDegreeFromSum (K L : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    (⨁ a : tensorDegreeIndex n, tensorDegreeFactor K L n a) →ₗ[ℚ]
      (HomologicalComplex.tensorObj K L).X n :=
  DirectSum.toModule ℚ (tensorDegreeIndex n) _ (fun a =>
    (HomologicalComplex.ιTensorObj K L a.1.1 a.1.2 n (Finset.mem_antidiagonal.mp a.2)).hom)

/-- Each actual tensor inclusion maps to its corresponding finite direct-sum inclusion.
Source: Hatcher, Algebraic Topology, §3.2, the direct-sum tensor complex. -/
theorem tensorDegreeToSum_inclusion (K L : ChainComplex (ModuleCat ℚ) ℕ)
    (p q n : ℕ) (hpq : p + q = n) :
    (tensorDegreeToSum K L n).comp (HomologicalComplex.ιTensorObj K L p q n hpq).hom =
      DirectSum.lof ℚ (tensorDegreeIndex n) (tensorDegreeFactor K L n)
        ⟨(p, q), Finset.mem_antidiagonal.mpr hpq⟩ := by
  exact congrArg ModuleCat.Hom.hom (HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat ℚ)) (c := ComplexShape.down ℕ)
    (fun r s hrs => ModuleCat.ofHom
      (DirectSum.lof ℚ (tensorDegreeIndex n) (tensorDegreeFactor K L n)
        ⟨(r, s), Finset.mem_antidiagonal.mpr hrs⟩)) p q hpq)

/-- The map from the finite tensor bidegree sum evaluates each summand by its actual total inclusion.
Source: Hatcher, Algebraic Topology, §3.2, the direct-sum tensor complex. -/
theorem tensorDegreeFromSum_lof (K L : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (a : tensorDegreeIndex n) (z : tensorDegreeFactor K L n a) :
    tensorDegreeFromSum K L n (DirectSum.lof ℚ (tensorDegreeIndex n) (tensorDegreeFactor K L n) a z) =
      (HomologicalComplex.ιTensorObj K L a.1.1 a.1.2 n (Finset.mem_antidiagonal.mp a.2)).hom z :=
  DirectSum.toModule_lof ℚ a z

/-- The finite bidegree reconstruction recovers every actual total tensor chain.
Source: Hatcher, Algebraic Topology, §3.2, the direct-sum tensor complex. -/
theorem tensorDegreeFromSum_toSum (K L : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    (tensorDegreeFromSum K L n).comp (tensorDegreeToSum K L n) = LinearMap.id := by
  have he : ModuleCat.ofHom (tensorDegreeToSum K L n) ≫
      ModuleCat.ofHom (tensorDegreeFromSum K L n) =
      𝟙 ((HomologicalComplex.tensorObj K L).X n) := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change tensorDegreeFromSum K L n
      (tensorDegreeToSum K L n ((HomologicalComplex.ιTensorObj K L p q n hpq).hom z)) =
        (HomologicalComplex.ιTensorObj K L p q n hpq).hom z
    have h := LinearMap.congr_fun (tensorDegreeToSum_inclusion K L p q n hpq) z
    change tensorDegreeToSum K L n ((HomologicalComplex.ιTensorObj K L p q n hpq).hom z) = _ at h
    rw [h]
    exact tensorDegreeFromSum_lof K L n ⟨(p, q), Finset.mem_antidiagonal.mpr hpq⟩ z
  exact congrArg ModuleCat.Hom.hom he

/-- Passing through the actual total tensor degree recovers every finite bidegree sum.
Source: Hatcher, Algebraic Topology, §3.2, the direct-sum tensor complex. -/
theorem tensorDegreeToSum_fromSum (K L : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    (tensorDegreeToSum K L n).comp (tensorDegreeFromSum K L n) = LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro a
  apply LinearMap.ext
  intro z
  change tensorDegreeToSum K L n
    (tensorDegreeFromSum K L n (DirectSum.lof ℚ (tensorDegreeIndex n) (tensorDegreeFactor K L n) a z)) =
      DirectSum.lof ℚ (tensorDegreeIndex n) (tensorDegreeFactor K L n) a z
  rw [tensorDegreeFromSum_lof]
  exact LinearMap.congr_fun
    (tensorDegreeToSum_inclusion K L a.1.1 a.1.2 n (Finset.mem_antidiagonal.mp a.2)) z

/-- The actual total tensor chain degree is linearly equivalent to its finite sum of tensor bidegrees.
Source: Hatcher, Algebraic Topology, §3.2, the direct-sum tensor complex. -/
def tensorDegreeSumEquiv (K L : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    (HomologicalComplex.tensorObj K L).X n ≃ₗ[ℚ]
      ⨁ a : tensorDegreeIndex n, tensorDegreeFactor K L n a where
  toLinearMap := tensorDegreeToSum K L n
  invFun := tensorDegreeFromSum K L n
  left_inv z := LinearMap.congr_fun (tensorDegreeFromSum_toSum K L n) z
  right_inv z := LinearMap.congr_fun (tensorDegreeToSum_fromSum K L n) z

#print axioms tensorDegreeSumEquiv
#print axioms tensorDegreeToSum_fromSum
#print axioms tensorDegreeFromSum_toSum
#print axioms tensorDegreeFromSum_lof
#print axioms tensorDegreeToSum
#print axioms tensorDegreeFromSum
#print axioms tensorDegreeToSum_inclusion
end HodgeLean.Foundations.Singular
