import HodgeLean.Foundations.Singular.ProductChains
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-! Homotopy equivalences of the actual rational tensor chain complexes. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.MonoidalCategory
namespace HodgeLean.Foundations.Singular

/-- Tensoring actual rational chain homotopy equivalences gives a chain homotopy equivalence.
Source: Hatcher, Algebraic Topology, §3.2, tensor products of chain homotopies. -/
def tensorComplexHomotopyEquiv
    {K K' L L' : ChainComplex (ModuleCat ℚ) ℕ}
    (e : HomotopyEquiv K K') (f : HomotopyEquiv L L') :
    HomotopyEquiv (HomologicalComplex.tensorObj K L) (HomologicalComplex.tensorObj K' L') where
  hom := HomologicalComplex.tensorHom e.hom f.hom
  inv := HomologicalComplex.tensorHom e.inv f.inv
  homotopyHomInvId := by
    have hcomp : HomologicalComplex.tensorHom e.hom f.hom ≫
        HomologicalComplex.tensorHom e.inv f.inv =
        HomologicalComplex.tensorHom (e.hom ≫ e.inv) (f.hom ≫ f.inv) :=
      MonoidalCategory.tensorHom_comp_tensorHom e.hom f.hom e.inv f.inv
    refine (Homotopy.ofEq hcomp).trans ?_
    exact (HomologicalComplex.mapBifunctorMapHomotopy₁ e.homotopyHomInvId
      (f.hom ≫ f.inv) (curriedTensor (ModuleCat ℚ)) (ComplexShape.down ℕ)).trans
        ((HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 K) f.homotopyHomInvId
          (curriedTensor (ModuleCat ℚ)) (ComplexShape.down ℕ)).trans
            (Homotopy.ofEq (MonoidalCategory.id_tensorHom_id K L)))
  homotopyInvHomId := by
    have hcomp : HomologicalComplex.tensorHom e.inv f.inv ≫
        HomologicalComplex.tensorHom e.hom f.hom =
        HomologicalComplex.tensorHom (e.inv ≫ e.hom) (f.inv ≫ f.hom) :=
      MonoidalCategory.tensorHom_comp_tensorHom e.inv f.inv e.hom f.hom
    refine (Homotopy.ofEq hcomp).trans ?_
    exact (HomologicalComplex.mapBifunctorMapHomotopy₁ e.homotopyInvHomId
      (f.inv ≫ f.hom) (curriedTensor (ModuleCat ℚ)) (ComplexShape.down ℕ)).trans
        ((HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 K') f.homotopyInvHomId
          (curriedTensor (ModuleCat ℚ)) (ComplexShape.down ℕ)).trans
            (Homotopy.ofEq (MonoidalCategory.id_tensorHom_id K' L')))

#print axioms tensorComplexHomotopyEquiv
end HodgeLean.Foundations.Singular
