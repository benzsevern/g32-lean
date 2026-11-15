import HodgeLean.Foundations.Program.PrymParabolicIntersectionCap
import HodgeLean.Foundations.Program.PrymParabolicIntersectionIntegralCup

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- The cellular cap chain, with the front-edge value multiplying the back edge.
Source: Hatcher, *Algebraic Topology*, §3.3, simplicial cap product. -/
def hga_cellCap {G : Type} [Group G] {r : ℕ} (g : Fin r → G)
    (α : hg2_Edge G r → ℤ) : (hg2_Tri G r →₀ ℤ) →ₗ[ℤ] (hg2_Edge G r →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun τ ↦ Finsupp.single (hg2_face0 g τ) (α (hg2_face2 τ)))

theorem hga_cellCap_evaluation {G : Type} [Group G] [Fintype G] {r : ℕ}
    (g : Fin r → G) (α β : hg2_Edge G r → ℤ) :
    (Finsupp.linearCombination ℤ β) (hga_cellCap g α hg2_orient) =
      hga_cupEval ℤ g α β := by
  have h : (Finsupp.linearCombination ℤ β).comp (hga_cellCap g α) =
      Finsupp.linearCombination ℤ (fun τ ↦ α (hg2_face2 τ) * β (hg2_face0 g τ)) := by
    ext τ
    simp [hga_cellCap]
  simpa only [LinearMap.comp_apply, Finsupp.linearCombination_apply, smul_eq_mul, hga_cupEval, Int.cast_id]
    using LinearMap.congr_fun h hg2_orient

theorem hga_cellular_boundary_evaluation {G : Type} [Group G] {r : ℕ}
    (g : Fin r → G) (β : hg2_Vert g → ℤ) (z : hg2_Edge G r →₀ ℤ) :
    (Finsupp.linearCombination ℤ β) (hg2_bd1 ℤ g z) =
      (Finsupp.linearCombination ℤ (hg2_delta0 ℤ ℤ g β)) z := by
  have h : (Finsupp.linearCombination ℤ β).comp (hg2_bd1 ℤ g) =
      Finsupp.linearCombination ℤ (hg2_delta0 ℤ ℤ g β) := by
    ext ε
    simp [hg2_bd1, hg2_delta0, LinearMap.funLeft]
  exact LinearMap.congr_fun h z

theorem hga_cellCap_cycle (α : hg2_Edge b4b_Group 13 → ℤ)
    (hα : hg2_delta1 ℤ ℤ b4b_root α = 0) :
    hg2_bd1 ℤ b4b_root (hga_cellCap b4b_root α hg2_orient) = 0 := by
  classical
  ext v
  have h := hga_cellular_boundary_evaluation b4b_root (fun w ↦ if w = v then 1 else 0)
    (hga_cellCap b4b_root α hg2_orient)
  rw [hga_cellCap_evaluation, hga_integral_cup_coboundary_right α hα] at h
  simpa [Finsupp.linearCombination_apply, Finsupp.sum] using h

set_option backward.isDefEq.respectTransparency false in
theorem hga_cellCap_realization {G : Type} [Group G] {r : ℕ} {g : Fin r → G}
    {T : Type} [TopologicalSpace T] (F : hg8_DeltaMap g T)
    (φ : Simplicial.Cochain ℤ (TopCat.toSSet.obj (TopCat.of T)) 1)
    (z : hg2_Tri G r →₀ ℤ) :
    hg5_chain1 F.edge (hga_cellCap g
      (fun ε ↦ φ (hg5_chain1 F.edge (Finsupp.single ε 1))) z) =
      Simplicial.cap ℤ 1 1 φ (hg5_chain2 F.tri z) := by
  have hfront : Simplicial.frontInclusion 1 1 = SimplexCategory.δ (2 : Fin 3) := by
    ext i
    fin_cases i <;> rfl
  have hback : Simplicial.backInclusion 1 1 = SimplexCategory.δ (0 : Fin 3) := by
    ext i
    fin_cases i <;> rfl
  have h : (hg5_chain1 F.edge).comp (hga_cellCap g
      (fun ε ↦ φ (hg5_chain1 F.edge (Finsupp.single ε 1)))) =
      (Simplicial.cap ℤ 1 1 φ).comp (hg5_chain2 F.tri) := by
    ext τ
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, hga_cellCap, Finsupp.linearCombination_single, one_smul,
      hg5_chain1, hg5_chain2, Simplicial.cap_chainOfSimplex,
      Simplicial.frontFace, Simplicial.backFace, hfront, hback]
    rw [show (TopCat.toSSet.obj (TopCat.of T)).map (SimplexCategory.δ (2 : Fin 3)).op
        (b3Rest2_triSimplex (F.tri τ)) = b3Rest2_pathSimplex (F.edge (hg2_face2 τ)) from
          (hg5_delta_face (F.tri τ) 2).trans (congrArg b3Rest2_pathSimplex (F.faces τ).2.2)]
    rw [show (TopCat.toSSet.obj (TopCat.of T)).map (SimplexCategory.δ (0 : Fin 3)).op
        (b3Rest2_triSimplex (F.tri τ)) = b3Rest2_pathSimplex (F.edge (hg2_face0 g τ)) from
          (hg5_delta_face (F.tri τ) 0).trans (congrArg b3Rest2_pathSimplex (F.faces τ).1)]
  exact LinearMap.congr_fun h z

set_option backward.isDefEq.respectTransparency false in
theorem hga_cellCap_homology {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap b4b_root T)
    (φ : Simplicial.Cochain ℤ (TopCat.toSSet.obj (TopCat.of T)) 1)
    (hφ : φ.comp (Simplicial.boundary ℤ 1) = 0) :
    let α := fun ε ↦ φ (hg5_chain1 F.edge (Finsupp.single ε 1))
    hg8_H1map F (Submodule.Quotient.mk
      ⟨hga_cellCap b4b_root α hg2_orient,
        hga_cellCap_cycle α (hga_restriction_cocycle F φ hφ)⟩) =
      ((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass
        (hga_cap_fundCycle F φ hφ) := by
  intro α
  change ((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass
    (hg8_cycle1 F ⟨hga_cellCap b4b_root α hg2_orient, _⟩) = _
  congr 1
  apply Subtype.ext
  exact hga_cellCap_realization F φ hg2_orient

#print axioms hga_cellCap_homology
#print axioms hga_cellCap_realization
#print axioms hga_cellCap_cycle
#print axioms hga_cellular_boundary_evaluation
#print axioms hga_cellCap
#print axioms hga_cellCap_evaluation
end HodgeLean.Foundations.Program
