import HodgeLean.Foundations.Program.PrymParabolicIntersectionDualGlobal
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cLoopRepresentatives

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
theorem hga_contractible_cycle_bounds {X : Type} [TopologicalSpace X] [ContractibleSpace X]
    (z : Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of X)) 1)
    (hz : Simplicial.boundary ℤ 0 z = 0) :
    ∃ w : Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of X)) 2,
      Simplicial.boundary ℤ 1 w = z := by
  let K := SingularChainComplex ℤ (TopCat.of X)
  have hzero : Subsingleton (Homology ℤ (TopCat.of X) 1) :=
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

set_option backward.isDefEq.respectTransparency false in
/-- Two paths with the same ends inside the image of a contractible space have the same class in
the chain quotient. -/
theorem hga_pathChain_contractible {X T : Type} [TopologicalSpace X] [TopologicalSpace T]
    [ContractibleSpace X] (j : C(X, T)) (g h : C(unitInterval, X)) (h0 : g 0 = h 0)
    (h1 : g 1 = h 1) : b6m_pathChain (j.comp g) = b6m_pathChain (j.comp h) := by
  let c := Simplicial.chainOfSimplex ℤ (b3Rest2_pathSimplex g) -
    Simplicial.chainOfSimplex ℤ (b3Rest2_pathSimplex h)
  have hc : Simplicial.boundary ℤ 0 c = 0 := by
    simp only [c, map_sub, hga_path_boundary, h0, h1, sub_self]
  obtain ⟨w, hw⟩ := hga_contractible_cycle_bounds c hc
  have hm := ConcreteCategory.congr_hom
    ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom j)) (ModuleCat.of ℤ ℤ)).comm 2 1) w
  change Simplicial.boundary ℤ 1 (hg8_chainMap j 2 w) = hg8_chainMap j 1 (Simplicial.boundary ℤ 1 w)
    at hm
  rw [hw] at hm
  simp only [c, map_sub, hga_pathChain_map] at hm
  apply sub_eq_zero.mp
  unfold b6m_pathChain
  rw [← map_sub, ← hm]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact ⟨_, rfl⟩

/-- A path and its reparametrization by an endpoint-preserving self-map of `[0, 1]` have the same
class in the chain quotient. -/
theorem hga_pathChain_reparam {T : Type} [TopologicalSpace T] (g : C(unitInterval, T))
    (φ : C(unitInterval, unitInterval)) (h0 : φ 0 = 0) (h1 : φ 1 = 1) :
    b6m_pathChain (g.comp φ) = b6m_pathChain g := by
  haveI : ContractibleSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, le_rfl, zero_le_one⟩
  have := hga_pathChain_contractible g φ (ContinuousMap.id _) h0 h1
  simpa using this

/-- Two paths that agree pointwise have the same class. -/
theorem hga_pathChain_congr {T : Type} [TopologicalSpace T] {g h : C(unitInterval, T)}
    (hgh : ∀ t, g t = h t) : b6m_pathChain g = b6m_pathChain h := by
  rw [ContinuousMap.ext hgh]

#print axioms hga_pathChain_congr
#print axioms hga_pathChain_reparam
#print axioms hga_pathChain_contractible
#print axioms hga_contractible_cycle_bounds
end HodgeLean.Foundations.Program
