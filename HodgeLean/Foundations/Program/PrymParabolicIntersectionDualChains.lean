import HodgeLean.Foundations.Program.PrymParabolicIntersectionDualSpokes
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cLocalLifting

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity
namespace HodgeLean.Foundations.Program

theorem hga_triangle_contractible : ContractibleSpace (StdSimplex ℝ (Fin 3)) := by
  let r : C(ℂ, StdSimplex ℝ (Fin 3)) := ⟨hga_triangleRetraction, hga_continuous_triangleRetraction⟩
  let i : C(StdSimplex ℝ (Fin 3), ℂ) := ⟨hga_triangleCoordinate, by
    unfold hga_triangleCoordinate
    fun_prop⟩
  have hc := ((id_nullhomotopic ℂ).comp_left i).comp_right r
  have hid : r.comp ((ContinuousMap.id ℂ).comp i) = ContinuousMap.id (StdSimplex ℝ (Fin 3)) := by
    apply ContinuousMap.ext
    intro a
    exact hga_triangleRetraction_coordinate a
  rw [hid] at hc
  exact (contractible_iff_id_nullhomotopic _).mpr hc

set_option backward.isDefEq.respectTransparency false in
theorem hga_triangle_cycle_bounds
    (z : Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of (StdSimplex ℝ (Fin 3)))) 1)
    (hz : Simplicial.boundary ℤ 0 z = 0) :
    ∃ w : Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of (StdSimplex ℝ (Fin 3)))) 2,
      Simplicial.boundary ℤ 1 w = z := by
  letI := hga_triangle_contractible
  let K := SingularChainComplex ℤ (TopCat.of (StdSimplex ℝ (Fin 3)))
  have hzero : Subsingleton (Homology ℤ (TopCat.of (StdSimplex ℝ (Fin 3))) 1) :=
    ModuleCat.subsingleton_of_isZero (b6m_contractible_homology_isZero ℤ _ 1 one_ne_zero)
  have hz' : z ∈ LinearMap.ker (K.sc 1).g.hom := by
    change (K.d 1 ((ComplexShape.down ℕ).next 1)).hom z = 0
    rw [ChainComplex.next_nat_succ 0]
    exact hz
  obtain ⟨w, hw⟩ := hga_boundary_of_class_zero (K.sc 1) ⟨z, hz'⟩ (hzero.elim _ _)
  let hp := ChainComplex.prev ℕ 1
  refine ⟨(K.XIsoOfEq hp).hom.hom w, ?_⟩
  have hd := congrArg (fun m ↦ m.hom w) (K.XIsoOfEq_hom_comp_d hp 1)
  exact hd.trans hw

theorem hga_path_boundary {T : Type} [TopologicalSpace T] (e : C(unitInterval, T)) :
    Simplicial.boundary ℤ 0 (Simplicial.chainOfSimplex ℤ (b3Rest2_pathSimplex e)) =
      Simplicial.chainOfSimplex ℤ (hg5_pointSimplex (e 1)) -
        Simplicial.chainOfSimplex ℤ (hg5_pointSimplex (e 0)) := by
  rw [Simplicial.boundary_chainOfSimplex, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, hg5_delta_path_zero,
    hg5_delta_path_one, neg_one_smul, sub_eq_add_neg]
  erw [one_smul]

#print axioms hga_path_boundary
#print axioms hga_triangle_cycle_bounds
#print axioms hga_triangle_contractible
end HodgeLean.Foundations.Program
