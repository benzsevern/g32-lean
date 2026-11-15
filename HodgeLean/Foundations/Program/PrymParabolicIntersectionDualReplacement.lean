import HodgeLean.Foundations.Program.PrymParabolicIntersectionDualChains

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity
namespace HodgeLean.Foundations.Program

/-- A barycentric dual spoke inside a realized triangle.
Source: Hatcher, *Algebraic Topology*, §3.3, dual cell decomposition. -/
def hga_dualSpoke {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (k : Fin 3) : C(unitInterval, T) :=
  σ.comp ⟨hga_dualPoint k, hga_dualPoint_continuous k⟩

/-- The second half of a parametrized edge, from its midpoint to its target.
Source: Hatcher, *Algebraic Topology*, §2.1, subdivision of singular paths. -/
def hga_edgeTail {T : Type} [TopologicalSpace T] (e : C(unitInterval, T)) : C(unitInterval, T) :=
  e.comp ⟨fun t ↦ ⟨((t : ℝ) + 1) / 2, by
      constructor <;> nlinarith [t.property.1, t.property.2]⟩,
    ((continuous_subtype_val.add continuous_const).div_const 2).subtype_mk _⟩

theorem hga_dualSpoke_boundary {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (k : Fin 3) :
    Simplicial.boundary ℤ 0 (Simplicial.chainOfSimplex ℤ (b3Rest2_pathSimplex (hga_dualSpoke σ k))) =
      Simplicial.chainOfSimplex ℤ (hg5_pointSimplex (σ (hga_triangleRetraction 0))) -
        Simplicial.chainOfSimplex ℤ (hg5_pointSimplex
          (hg5_face σ k ⟨1 / 2, by constructor <;> norm_num⟩)) := by
  rw [hga_path_boundary]
  change Simplicial.chainOfSimplex ℤ (hg5_pointSimplex (σ (hga_dualPoint k 1))) -
    Simplicial.chainOfSimplex ℤ (hg5_pointSimplex (σ (hga_dualPoint k 0))) = _
  rw [hga_dualPoint_barycentre, hga_dualPoint_midpoint]
  rfl

theorem hga_edgeTail_boundary {T : Type} [TopologicalSpace T] (e : C(unitInterval, T)) :
    Simplicial.boundary ℤ 0 (Simplicial.chainOfSimplex ℤ (b3Rest2_pathSimplex (hga_edgeTail e))) =
      Simplicial.chainOfSimplex ℤ (hg5_pointSimplex (e 1)) -
        Simplicial.chainOfSimplex ℤ (hg5_pointSimplex
          (e ⟨1 / 2, by constructor <;> norm_num⟩)) := by
  rw [hga_path_boundary]
  have h1 : hga_edgeTail e 1 = e 1 := by
    change e ⟨((1 : ℝ) + 1) / 2, _⟩ = e 1
    congr 1
    apply Subtype.ext
    norm_num
  have h0 : hga_edgeTail e 0 = e ⟨1 / 2, by constructor <;> norm_num⟩ := by
    change e ⟨((0 : ℝ) + 1) / 2, _⟩ = _
    congr 1
    apply Subtype.ext
    norm_num
  rw [h1, h0]

/-- The signed combination of three paths with coefficients on the corresponding faces.
Source: Hatcher, *Algebraic Topology*, §2.1, the alternating triangle boundary. -/
def hga_trianglePathChain {T : Type} [TopologicalSpace T]
    (e : Fin 3 → C(unitInterval, T)) (α : Fin 3 → ℤ) :
    Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of T)) 1 :=
  α 0 • Simplicial.chainOfSimplex ℤ (b3Rest2_pathSimplex (e 0)) -
    α 1 • Simplicial.chainOfSimplex ℤ (b3Rest2_pathSimplex (e 1)) +
    α 2 • Simplicial.chainOfSimplex ℤ (b3Rest2_pathSimplex (e 2))

set_option backward.isDefEq.respectTransparency false in
theorem hga_triangle_cap_correction_cycle {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (α : Fin 3 → ℤ)
    (hα : α 0 - α 1 + α 2 = 0) :
    Simplicial.boundary ℤ 0
      (α 2 • Simplicial.chainOfSimplex ℤ (b3Rest2_pathSimplex (hg5_face σ 0)) -
        hga_trianglePathChain (hga_dualSpoke σ) α +
        hga_trianglePathChain (fun k ↦ hga_edgeTail (hg5_face σ k)) α) = 0 := by
  simp only [hga_trianglePathChain, map_add, map_sub, map_smul, map_zsmul,
    hga_dualSpoke_boundary, hga_edgeTail_boundary]
  rw [hga_path_boundary]
  have h00 : hg5_face σ 0 0 = σ (StdSimplex.single 1) := by
    change σ (StdSimplex.map _ (StdSimplex.homeomorphI.symm 0)) = _
    rw [StdSimplex.homeomorphI_symm_zero, StdSimplex.map_single]
    rfl
  have h01 : hg5_face σ 0 1 = σ (StdSimplex.single 2) := by
    change σ (StdSimplex.map _ (StdSimplex.homeomorphI.symm 1)) = _
    rw [StdSimplex.homeomorphI_symm_one, StdSimplex.map_single]
    rfl
  have h11 : hg5_face σ 1 1 = σ (StdSimplex.single 2) := by
    change σ (StdSimplex.map _ (StdSimplex.homeomorphI.symm 1)) = _
    rw [StdSimplex.homeomorphI_symm_one, StdSimplex.map_single]
    rfl
  have h21 : hg5_face σ 2 1 = σ (StdSimplex.single 1) := by
    change σ (StdSimplex.map _ (StdSimplex.homeomorphI.symm 1)) = _
    rw [StdSimplex.homeomorphI_symm_one, StdSimplex.map_single]
    rfl
  rw [h00, h01, h11, h21]
  have ha : α 1 = α 0 + α 2 := by omega
  rw [ha]
  simp only [add_zsmul, zsmul_sub]
  abel

theorem hga_pathChain_map {T T' : Type} [TopologicalSpace T] [TopologicalSpace T']
    (f : C(T, T')) (e : C(unitInterval, T)) :
    hg8_chainMap f 1 (Simplicial.chainOfSimplex ℤ (b3Rest2_pathSimplex e)) =
      Simplicial.chainOfSimplex ℤ (b3Rest2_pathSimplex (f.comp e)) := by
  exact Simplicial.chainOfSimplex_map ℤ (TopCat.toSSet.map (TopCat.ofHom f)) _

set_option backward.isDefEq.respectTransparency false in
theorem hga_triangle_cap_correction_bounds {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (α : Fin 3 → ℤ)
    (hα : α 0 - α 1 + α 2 = 0) :
    ∃ w : Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of T)) 2,
      Simplicial.boundary ℤ 1 w =
        α 2 • Simplicial.chainOfSimplex ℤ (b3Rest2_pathSimplex (hg5_face σ 0)) -
          hga_trianglePathChain (hga_dualSpoke σ) α +
          hga_trianglePathChain (fun k ↦ hga_edgeTail (hg5_face σ k)) α := by
  let S := StdSimplex ℝ (Fin 3)
  let e := ContinuousMap.id S
  obtain ⟨w, hw⟩ := hga_triangle_cycle_bounds _ (hga_triangle_cap_correction_cycle e α hα)
  refine ⟨hg8_chainMap σ 2 w, ?_⟩
  have hc := ConcreteCategory.congr_hom
    ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom σ)) (ModuleCat.of ℤ ℤ)).comm 2 1) w
  change Simplicial.boundary ℤ 1 (hg8_chainMap σ 2 w) =
    hg8_chainMap σ 1 (Simplicial.boundary ℤ 1 w) at hc
  rw [hc, hw]
  simp only [hga_trianglePathChain, map_add, map_sub, map_zsmul, hga_pathChain_map]
  rfl

#print axioms hga_triangle_cap_correction_bounds
#print axioms hga_pathChain_map
#print axioms hga_triangle_cap_correction_cycle
#print axioms hga_trianglePathChain
#print axioms hga_edgeTail_boundary
#print axioms hga_dualSpoke_boundary
#print axioms hga_dualSpoke
#print axioms hga_edgeTail
end HodgeLean.Foundations.Program
