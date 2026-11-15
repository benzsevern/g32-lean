import HodgeLean.Foundations.Program.PrymParabolicIntersectionOrientation
import HodgeLean.Foundations.Program.PrymParabolicIntersectionLocalChains

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity
namespace HodgeLean.Foundations.Program

theorem hga_triangle_face_ne_interior {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (hσ : Function.Injective σ)
    (b : StdSimplex ℝ (Fin 3)) (hb : ∀ k, 0 < b.weights k)
    (k : Fin 3) (t : unitInterval) : hg5_face σ k t ≠ σ b := by
  intro h
  change σ (StdSimplex.map k.succAbove (StdSimplex.homeomorphI.symm t)) = σ b at h
  have hw := congrArg (fun a : StdSimplex ℝ (Fin 3) ↦ a.weights k) (hσ h)
  rw [hg5_face_w k t k] at hw
  simp only [ite_true] at hw
  have hp := hb k
  linarith

set_option backward.isDefEq.respectTransparency false in
theorem hga_triangle_boundary_in_complement {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (y : T)
    (hy : ∀ (k : Fin 3) (t : unitInterval), hg5_face σ k t ≠ y) :
    ∃ u : Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of ({y}ᶜ : Set T))) 1,
      hg8_chainMap ⟨Subtype.val, continuous_subtype_val⟩ 1 u =
        Simplicial.boundary ℤ 1 (Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex σ)) := by
  classical
  let f (k : Fin 3) : C(unitInterval, ({y}ᶜ : Set T)) :=
    ⟨fun t ↦ ⟨hg5_face σ k t, hy k t⟩,
      (hg5_face σ k).continuous.subtype_mk _⟩
  have hm (k : Fin 3) : hg8_chainMap ⟨Subtype.val, continuous_subtype_val⟩ 1
      (Simplicial.chainOfSimplex ℤ (b3Rest2_pathSimplex (f k))) =
      Simplicial.chainOfSimplex ℤ
        ((TopCat.toSSet.obj (TopCat.of T)).δ k (b3Rest2_triSimplex σ)) := by
    change ((SSet.chainComplexMap
      (TopCat.toSSet.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩))
      (ModuleCat.of ℤ ℤ)).f 1).hom _ = _
    rw [Simplicial.chainOfSimplex_map, hg5_delta_face]
    rfl
  refine ⟨∑ k : Fin 3, (-1 : ℤ) ^ k.val •
    Simplicial.chainOfSimplex ℤ (b3Rest2_pathSimplex (f k)), ?_⟩
  rw [Simplicial.boundary_chainOfSimplex]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ,
    pow_zero, pow_one, pow_succ, neg_mul, mul_neg, neg_neg, mul_one, one_mul,
    one_smul, neg_smul, one_zsmul, neg_one_zsmul, map_add, map_neg, hm]

set_option backward.isDefEq.respectTransparency false in
theorem hga_triangle_relative_cycle {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (y : T)
    (hy : ∀ (k : Fin 3) (t : unitInterval), hg5_face σ k t ≠ y) :
    let P := TopPair.ofSubset (X := TopCat.of T) ({y}ᶜ : Set T)
    (((relativeChainFunctor ℤ).obj P).sc 2).g.hom
      (((relativeChainProjection ℤ P).f 2).hom
        (Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex σ))) = 0 := by
  intro P
  obtain ⟨u, hu⟩ := hga_triangle_boundary_in_complement σ y hy
  let K := (relativeChainFunctor ℤ).obj P
  change (K.d 2 ((ComplexShape.down ℕ).next 2)).hom _ = 0
  rw [ChainComplex.next_nat_succ 1]
  have hd := congrArg (fun m ↦ m.hom
    (Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex σ))) ((relativeChainProjection ℤ P).comm 2 1)
  change (K.d 2 1).hom (((relativeChainProjection ℤ P).f 2).hom _) =
    ((relativeChainProjection ℤ P).f 1).hom
      (Simplicial.boundary ℤ 1 (Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex σ))) at hd
  rw [hd]
  have h := congrArg (fun m ↦ (m.f 1).hom u)
    (subspaceChainMap_relativeChainProjection ℤ P)
  exact (congrArg ((relativeChainProjection ℤ P).f 1).hom hu.symm).trans h

#print axioms hga_triangle_face_ne_interior
#print axioms hga_triangle_boundary_in_complement
#print axioms hga_triangle_relative_cycle

end HodgeLean.Foundations.Program
