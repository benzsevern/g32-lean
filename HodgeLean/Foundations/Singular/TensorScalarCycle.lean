import HodgeLean.Foundations.Singular.TensorScalarCocycle
import HodgeConjecture.Lemmas.Algebra.Homology.LinearDualNaturality

/-! Actual tensor dual cycles represented by products of factor cocycles. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- The canonical actual tensor cocycle represented by two closed rational factor cochains.
Source: Hatcher, Algebraic Topology, §3.2, the cohomology tensor pairing. -/
def tensorScalarCycle (K L : ChainComplex (ModuleCat ℚ) ℕ) (p q : ℕ)
    (φ : LinearMap.ker (K.sc p).f.hom.dualMap) (ψ : LinearMap.ker (L.sc q).f.hom.dualMap) :
    LinearMap.ker ((HomologicalComplex.tensorObj K L).sc (p + q)).f.hom.dualMap :=
  ⟨tensorScalarCochain K L p q φ.1 ψ.1, by
    change ((HomologicalComplex.tensorObj K L).d
      ((ComplexShape.down ℕ).prev (p + q)) (p + q)).hom.dualMap _ = 0
    rw [ChainComplex.prev]
    apply tensorScalarCochain_cocycle
    · have hφ := φ.property
      change (K.d ((ComplexShape.down ℕ).prev p) p).hom.dualMap φ.1 = 0 at hφ
      rw [ChainComplex.prev] at hφ
      exact hφ
    · have hψ := ψ.property
      change (L.d ((ComplexShape.down ℕ).prev q) q).hom.dualMap ψ.1 = 0 at hψ
      rw [ChainComplex.prev] at hψ
      exact hψ⟩

#print axioms tensorScalarCycle
end HodgeLean.Foundations.Singular
