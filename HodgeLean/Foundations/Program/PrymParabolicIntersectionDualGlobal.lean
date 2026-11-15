import HodgeLean.Foundations.Program.PrymParabolicIntersectionDualReplacement
import HodgeLean.Foundations.Program.PrymParabolicIntersectionCellCap

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity
namespace HodgeLean.Foundations.Program

/-- Values of an edge cochain on the three ordered faces of a triangle.
Source: Hatcher, *Algebraic Topology*, §2.1, simplicial face convention. -/
def hga_faceValues {G : Type} [Group G] {r : ℕ} (g : Fin r → G)
    (α : hg2_Edge G r → ℤ) (τ : hg2_Tri G r) : Fin 3 → ℤ :=
  ![α (hg2_face0 g τ), α (hg2_face1 τ), α (hg2_face2 τ)]

/-- The dual-spoke chain of a cellular two-chain with coefficients from an edge cochain.
Source: Hatcher, *Algebraic Topology*, §3.3, barycentric dual cells. -/
def hga_dualChain {G : Type} [Group G] {r : ℕ} {g : Fin r → G}
    {T : Type} [TopologicalSpace T] (F : hg8_DeltaMap g T) (α : hg2_Edge G r → ℤ) :
    (hg2_Tri G r →₀ ℤ) →ₗ[ℤ] Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of T)) 1 :=
  Finsupp.linearCombination ℤ (fun τ ↦
    hga_trianglePathChain (hga_dualSpoke (F.tri τ)) (hga_faceValues g α τ))

/-- The midpoint-to-target correction on a cellular one-chain.
Source: Hatcher, *Algebraic Topology*, §3.3, comparison of cap and dual-cell chains. -/
def hga_edgeTailChain {G : Type} [Group G] {r : ℕ} {g : Fin r → G}
    {T : Type} [TopologicalSpace T] (F : hg8_DeltaMap g T) (α : hg2_Edge G r → ℤ) :
    (hg2_Edge G r →₀ ℤ) →ₗ[ℤ] Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of T)) 1 :=
  Finsupp.linearCombination ℤ (fun ε ↦
    α ε • Simplicial.chainOfSimplex ℤ (b3Rest2_pathSimplex (hga_edgeTail (F.edge ε))))

set_option backward.isDefEq.respectTransparency false in
theorem hga_dualChain_comparison {G : Type} [Group G] {r : ℕ} {g : Fin r → G}
    {T : Type} [TopologicalSpace T] (F : hg8_DeltaMap g T)
    (α : hg2_Edge G r → ℤ) (hα : hg2_delta1 ℤ ℤ g α = 0) (z : hg2_Tri G r →₀ ℤ) :
    ∃ w : Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of T)) 2,
      Simplicial.boundary ℤ 1 w = hg5_chain1 F.edge (hga_cellCap g α z) -
        hga_dualChain F α z + hga_edgeTailChain F α (hg2_bd2 ℤ g z) := by
  have hlocal (τ : hg2_Tri G r) := hga_triangle_cap_correction_bounds (F.tri τ)
    (hga_faceValues g α τ) (show α (hg2_face0 g τ) - α (hg2_face1 τ) + α (hg2_face2 τ) = 0 from
      congrFun hα τ)
  choose w hw using hlocal
  let W := Finsupp.linearCombination ℤ w
  have he : (Simplicial.boundary ℤ 1).comp W =
      (hg5_chain1 F.edge).comp (hga_cellCap g α) - hga_dualChain F α +
        (hga_edgeTailChain F α).comp (hg2_bd2 ℤ g) := by
    ext τ
    have hh := hw τ
    unfold hga_trianglePathChain at hh
    dsimp only at hh
    rw [(F.faces τ).1, (F.faces τ).2.1, (F.faces τ).2.2] at hh
    simp [W, hga_cellCap, hga_dualChain, hga_edgeTailChain, hg2_bd2, hg5_chain1,
      hga_faceValues, hga_trianglePathChain] at hh ⊢
    rw [hh]
    congr 2
    exact (int_smul_eq_zsmul (inferInstance : Module ℤ
      (Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of T)) 1)) _ _).symm
  exact ⟨W z, LinearMap.congr_fun he z⟩

theorem hga_dual_fundChain_comparison {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap b4b_root T)
    (φ : Simplicial.Cochain ℤ (TopCat.toSSet.obj (TopCat.of T)) 1)
    (hφ : φ.comp (Simplicial.boundary ℤ 1) = 0) :
    ∃ w : Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of T)) 2,
      Simplicial.boundary ℤ 1 w = Simplicial.cap ℤ 1 1 φ (hga_fundChain F) -
        hga_dualChain F (fun ε ↦ φ (hg5_chain1 F.edge (Finsupp.single ε 1))) hg2_orient := by
  obtain ⟨w, hw⟩ := hga_dualChain_comparison F _ (hga_restriction_cocycle F φ hφ) hg2_orient
  rw [hga_bd2_orient, map_zero, add_zero, hga_cellCap_realization] at hw
  exact ⟨w, hw⟩

theorem hga_cup_fundChain_eq_dual_evaluation {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap b4b_root T)
    (φ ψ : Simplicial.Cochain ℤ (TopCat.toSSet.obj (TopCat.of T)) 1)
    (hφ : φ.comp (Simplicial.boundary ℤ 1) = 0)
    (hψ : ψ.comp (Simplicial.boundary ℤ 1) = 0) :
    HodgeLean.Foundations.Singular.cupCochain (TopCat.of T) 1 1 φ ψ (hga_fundChain F) =
      ψ (hga_dualChain F (fun ε ↦ φ (hg5_chain1 F.edge (Finsupp.single ε 1))) hg2_orient) := by
  obtain ⟨w, hw⟩ := hga_dual_fundChain_comparison F φ hφ
  have he := LinearMap.congr_fun hψ w
  change ψ (Simplicial.boundary ℤ 1 w) = 0 at he
  rw [hw, map_sub] at he
  rw [hga_cup_eq_cap_evaluation]
  exact sub_eq_zero.mp he

set_option backward.isDefEq.respectTransparency false in
theorem hga_dual_fundChain_cycle {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap b4b_root T)
    (φ : Simplicial.Cochain ℤ (TopCat.toSSet.obj (TopCat.of T)) 1)
    (hφ : φ.comp (Simplicial.boundary ℤ 1) = 0) :
    Simplicial.boundary ℤ 0
      (hga_dualChain F (fun ε ↦ φ (hg5_chain1 F.edge (Finsupp.single ε 1))) hg2_orient) = 0 := by
  obtain ⟨w, hw⟩ := hga_dual_fundChain_comparison F φ hφ
  have hd := ConcreteCategory.congr_hom ((SingularChainComplex ℤ (TopCat.of T)).d_comp_d 2 1 0) w
  change Simplicial.boundary ℤ 0 (Simplicial.boundary ℤ 1 w) = 0 at hd
  have hc := (hga_cap_fundCycle F φ hφ).property
  change ((SingularChainComplex ℤ (TopCat.of T)).d 1 ((ComplexShape.down ℕ).next 1)).hom _ = 0 at hc
  rw [ChainComplex.next_nat_succ 0] at hc
  change Simplicial.boundary ℤ 0 (Simplicial.cap ℤ 1 1 φ (hga_fundChain F)) = 0 at hc
  rw [hw, map_sub, hc, zero_sub, neg_eq_zero] at hd
  exact hd

set_option backward.isDefEq.respectTransparency false in
/-- The barycentric dual cycle associated to an integral cocycle on the filled surface.
Source: Hatcher, *Algebraic Topology*, §3.3, dual cells and cap products. -/
def hga_dual_fundCycle {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap b4b_root T)
    (φ : Simplicial.Cochain ℤ (TopCat.toSSet.obj (TopCat.of T)) 1)
    (hφ : φ.comp (Simplicial.boundary ℤ 1) = 0) :
    LinearMap.ker ((SingularChainComplex ℤ (TopCat.of T)).sc 1).g.hom :=
  ⟨hga_dualChain F (fun ε ↦ φ (hg5_chain1 F.edge (Finsupp.single ε 1))) hg2_orient, by
    change ((SingularChainComplex ℤ (TopCat.of T)).d 1 ((ComplexShape.down ℕ).next 1)).hom _ = 0
    rw [ChainComplex.next_nat_succ 0]
    exact hga_dual_fundChain_cycle F φ hφ⟩

set_option backward.isDefEq.respectTransparency false in
theorem hga_cap_eq_dual_homology {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap b4b_root T)
    (φ : Simplicial.Cochain ℤ (TopCat.toSSet.obj (TopCat.of T)) 1)
    (hφ : φ.comp (Simplicial.boundary ℤ 1) = 0) :
    ((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass (hga_cap_fundCycle F φ hφ) =
      ((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass (hga_dual_fundCycle F φ hφ) := by
  obtain ⟨w, hw⟩ := hga_dual_fundChain_comparison F φ hφ
  have hz := hg8_class_eq_zero_of_d (SingularChainComplex ℤ (TopCat.of T)) 1
    (hga_cap_fundCycle F φ hφ - hga_dual_fundCycle F φ hφ) w hw
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

#print axioms hga_cap_eq_dual_homology
#print axioms hga_dual_fundCycle
#print axioms hga_dual_fundChain_cycle
#print axioms hga_cup_fundChain_eq_dual_evaluation
#print axioms hga_dual_fundChain_comparison
#print axioms hga_dualChain_comparison
#print axioms hga_faceValues
#print axioms hga_dualChain
#print axioms hga_edgeTailChain
end HodgeLean.Foundations.Program
