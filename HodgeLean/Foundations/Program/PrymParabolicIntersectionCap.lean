import HodgeLean.Foundations.Program.PrymParabolicIntersectionDefs

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular
open scoped Simplicial
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
theorem hga_cup_eq_cap_evaluation {R : Type} [CommRing R] (T : TopCat.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain R (TopCat.toSSet.obj T) p)
    (ψ : Simplicial.Cochain R (TopCat.toSSet.obj T) q) :
    HodgeLean.Foundations.Singular.cupCochain T p q φ ψ =
      ψ.comp (Simplicial.cap R p q φ) := by
  have h : ModuleCat.ofHom (HodgeLean.Foundations.Singular.cupCochain T p q φ ψ) =
      ModuleCat.ofHom (ψ.comp (Simplicial.cap R p q φ)) := by
    apply SSet.chainComplex_hom_ext
    intro σ
    refine ModuleCat.hom_ext (LinearMap.ext fun a ↦ ?_)
    have hi : ((TopCat.toSSet.obj T).ιChainComplex (R := ModuleCat.of R R) σ).hom a =
        a • Simplicial.chainOfSimplex R σ := by
      rw [Simplicial.chainOfSimplex, ← map_smul]
      simp
    change HodgeLean.Foundations.Singular.cupCochain T p q φ ψ
        (((TopCat.toSSet.obj T).ιChainComplex (R := ModuleCat.of R R) σ).hom a) =
      ψ (Simplicial.cap R p q φ
        (((TopCat.toSSet.obj T).ιChainComplex (R := ModuleCat.of R R) σ).hom a))
    rw [hi]
    simp only [map_smul, Simplicial.cap_chainOfSimplex,
      HodgeLean.Foundations.Singular.cupCochain_apply_simplex, smul_eq_mul]
  exact congrArg ModuleCat.Hom.hom h

set_option backward.isDefEq.respectTransparency false in
/-- The degree-one cycle obtained by capping the lifted orientation cycle with a cocycle.
Source: Hatcher, *Algebraic Topology*, §3.3, cap product boundary formula. -/
def hga_cap_fundCycle {T : Type} [TopologicalSpace T] (F : hg8_DeltaMap b4b_root T)
    (φ : Simplicial.Cochain ℤ (TopCat.toSSet.obj (TopCat.of T)) 1)
    (hφ : φ.comp (Simplicial.boundary ℤ 1) = 0) :
    LinearMap.ker ((SingularChainComplex ℤ (TopCat.of T)).sc 1).g.hom :=
  ⟨Simplicial.cap ℤ 1 1 φ (hga_fundChain F), by
    change ((SingularChainComplex ℤ (TopCat.of T)).d 1 ((ComplexShape.down ℕ).next 1)).hom _ = 0
    rw [ChainComplex.next_nat_succ 0]
    change Simplicial.boundary ℤ 0 (Simplicial.cap ℤ 1 1 φ (hga_fundChain F)) = 0
    rw [Simplicial.boundary_cap_eq_of_cocycle ℤ 1 0 φ hφ]
    have hd : Simplicial.boundary ℤ 1 (hga_fundChain F) = 0 := hga_d_fundChain F 1
    rw [hd, map_zero, smul_zero]⟩

theorem hga_cup_fundChain_eq_cap_class {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap b4b_root T)
    (φ ψ : Simplicial.Cochain ℤ (TopCat.toSSet.obj (TopCat.of T)) 1)
    (hφ : φ.comp (Simplicial.boundary ℤ 1) = 0)
    (l : b6m_H1 T →ₗ[ℤ] ℤ)
    (hψ : ∀ z : LinearMap.ker ((SingularChainComplex ℤ (TopCat.of T)).sc 1).g.hom,
      ψ z.1 = l (((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass z)) :
    HodgeLean.Foundations.Singular.cupCochain (TopCat.of T) 1 1 φ ψ (hga_fundChain F) =
      l (((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass
        (hga_cap_fundCycle F φ hφ)) := by
  rw [hga_cup_eq_cap_evaluation]
  exact hψ (hga_cap_fundCycle F φ hφ)

#print axioms hga_cup_fundChain_eq_cap_class
#print axioms hga_cap_fundCycle
#print axioms hga_cup_eq_cap_evaluation
end HodgeLean.Foundations.Program
