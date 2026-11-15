import HodgeLean.Foundations.Singular.RationalTensorCohomologyEvaluation
import HodgeLean.Foundations.Singular.RationalTensorDualClass
import HodgeLean.Foundations.Singular.RationalHomologyDualClass
import HodgeLean.Foundations.Singular.TensorScalarCycle

/-! The actual algebraic tensor-cohomology comparison on represented tensor classes. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
open scoped TensorProduct DirectSum
namespace HodgeLean.Foundations.Singular

set_option backward.isDefEq.respectTransparency false in
/-- The actual algebraic tensor-cohomology equivalence sends a represented pure summand to its scalar tensor cocycle class.
Source: Hatcher, Algebraic Topology, §3.2, the field-coefficient cohomology tensor pairing. -/
theorem rationalTensorCohomologyEquiv_class (K L : ChainComplex (ModuleCat ℚ) ℕ)
    (hK : ∀ p : ℕ, Module.Finite ℚ (K.sc p).linearDual.homology) (p q : ℕ)
    (φ : LinearMap.ker (K.sc p).f.hom.dualMap) (ψ : LinearMap.ker (L.sc q).f.hom.dualMap) :
    rationalTensorCohomologyEquiv K L hK (p + q)
      (DirectSum.lof ℚ (tensorDegreeIndex (p + q))
        (fun a => (K.sc a.1.1).linearDual.homology ⊗[ℚ] (L.sc a.1.2).linearDual.homology)
        ⟨(p, q), Finset.mem_antidiagonal.mpr rfl⟩
        ((K.sc p).linearDual.moduleCatHomologyClass φ ⊗ₜ[ℚ]
          (L.sc q).linearDual.moduleCatHomologyClass ψ)) =
      ((HomologicalComplex.tensorObj K L).sc (p + q)).linearDual.moduleCatHomologyClass
        (tensorScalarCycle K L p q φ ψ) := by
  letI (r : ℕ) : Module.Finite ℚ (K.sc r).linearDual.homology := hK r
  let a : tensorDegreeIndex (p + q) := ⟨(p, q), Finset.mem_antidiagonal.mpr rfl⟩
  let α := (K.sc p).linearDual.moduleCatHomologyClass φ
  let β := (L.sc q).linearDual.moduleCatHomologyClass ψ
  let x := DirectSum.lof ℚ (tensorDegreeIndex (p + q))
    (fun a => (K.sc a.1.1).linearDual.homology ⊗[ℚ] (L.sc a.1.2).linearDual.homology) a (α ⊗ₜ[ℚ] β)
  apply (rationalTensorDualHomologyEquiv K L (p + q)).injective
  let f := rationalTensorDualHomologyEquiv K L (p + q) (rationalTensorCohomologyEquiv K L hK (p + q) x)
  let g := rationalTensorDualHomologyEquiv K L (p + q)
    (((HomologicalComplex.tensorObj K L).sc (p + q)).linearDual.moduleCatHomologyClass
      (tensorScalarCycle K L p q φ ψ))
  change f = g
  suffices he : ModuleCat.ofHom f = ModuleCat.ofHom g from congrArg ModuleCat.Hom.hom he
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := rationalHomologyComplex K) (K₂ := rationalHomologyComplex L)
    (F := CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat ℚ)) (c := ComplexShape.down ℕ)
  intro r s hrs
  change r + s = p + q at hrs
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro u v
  let b : tensorDegreeIndex (p + q) := ⟨(r, s), Finset.mem_antidiagonal.mpr hrs⟩
  have hf := rationalTensorCohomologyEquiv_evaluate K L hK (p + q) x b (u ⊗ₜ[ℚ] v)
  have hg := rationalTensorDualHomologyEquiv_class K L r s (p + q) hrs
    (tensorScalarCycle K L p q φ ψ) u v
  change f ((HomologicalComplex.ιTensorObj (rationalHomologyComplex K) (rationalHomologyComplex L)
    r s (p + q) hrs).hom (u ⊗ₜ[ℚ] v)) =
    rationalTensorCohomologyFactorEquiv K L (p + q) b (x b) (u ⊗ₜ[ℚ] v) at hf
  change g ((HomologicalComplex.ιTensorObj (rationalHomologyComplex K) (rationalHomologyComplex L)
    r s (p + q) hrs).hom (u ⊗ₜ[ℚ] v)) =
    tensorScalarCochain K L p q φ.1 ψ.1 ((HomologicalComplex.ιTensorObj K L r s (p + q) hrs).hom
      (rationalHomologyInclusion K r u ⊗ₜ[ℚ] rationalHomologyInclusion L s v)) at hg
  change f ((HomologicalComplex.ιTensorObj (rationalHomologyComplex K) (rationalHomologyComplex L)
    r s (p + q) hrs).hom (u ⊗ₜ[ℚ] v)) =
    g ((HomologicalComplex.ιTensorObj (rationalHomologyComplex K) (rationalHomologyComplex L)
      r s (p + q) hrs).hom (u ⊗ₜ[ℚ] v))
  rw [hf, hg]
  by_cases h : r = p ∧ s = q
  · rcases h with ⟨hr, hs⟩
    subst r
    subst s
    have hx : x b = α ⊗ₜ[ℚ] β := DirectSum.of_eq_same a _
    rw [hx]
    calc
      _ = rationalHomologyDualEquiv K p α u * rationalHomologyDualEquiv L q β v :=
        rationalTensorCohomologyFactorEquiv_tmul K L (p + q) b α β u v
      _ = φ.1 (rationalHomologyInclusion K p u) * ψ.1 (rationalHomologyInclusion L q v) :=
        congrArg₂ (fun c d : ℚ => c * d) (rationalHomologyDualEquiv_class K p φ u)
          (rationalHomologyDualEquiv_class L q ψ v)
      _ = _ := (tensorScalarCochain_self K L p q φ.1 ψ.1 _ _).symm
  · have hba : b ≠ a := by
      intro he
      apply h
      exact ⟨congrArg (fun i : tensorDegreeIndex (p + q) => i.1.1) he,
        congrArg (fun i : tensorDegreeIndex (p + q) => i.1.2) he⟩
    have hx : x b = 0 := DirectSum.of_eq_of_ne a b _ hba
    rw [hx, map_zero, LinearMap.zero_apply]
    exact (tensorScalarCochain_other K L p q r s hrs h φ.1 ψ.1 _ _).symm

#print axioms rationalTensorCohomologyEquiv_class
end HodgeLean.Foundations.Singular
