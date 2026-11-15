import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.HolomorphicInverse
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceRemmertProper

/-! # Holomorphic maps defined by coordinate functions

HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Classical
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Set Filter Topology HodgeLean.Foundations.Analytic
namespace AlgebraicGeometry.SingularCycles

/-- Holomorphic coordinate functions define a holomorphic map to complex affine space.
Source: Grauert–Remmert, Coherent Analytic Sheaves, §1.1.5; composition of local analytic extensions. -/
theorem holomorphic_map_euclid {M : Type*} [TopologicalSpace M] (S : an_ReducedSpace M)
    {n : ℕ} (f : M → (Fin n → ℂ)) (hf : Continuous f)
    (hcoords : ∀ j, S.IsHolFun (fun x : (Set.univ : Set M) => f x j)) :
    an_IsHom S (an_euclidSpace n) f := by
  refine ⟨hf, ?_⟩
  intro V hV g hg
  apply holFun_of_local S
  intro x
  obtain ⟨N, hNo, hxN, G, hG, hgeq⟩ := hg ⟨f x, x.2⟩ PUnit.unit (Set.mem_univ _)
  let W : Set M := f ⁻¹' ((V ∩ N) ∩ {w | AnalyticAt ℂ G w})
  have hW : IsOpen W := ((hV.inter hNo).inter (isOpen_analyticAt ℂ G)).preimage hf
  have hWV : W ⊆ f ⁻¹' V := fun y hy => hy.1.1
  have hxW : (x : M) ∈ W := ⟨⟨x.2, hxN⟩, hG⟩
  refine ⟨W, hWV, hW, hxW, ?_⟩
  have hc : ∀ j, S.IsHolFun (fun y : W => f y j) := fun j =>
    anb_isHolFun_restrict S.atlas (Set.subset_univ W) (hcoords j)
  have hcomp := holFun_analytic_comp S (fun y : W => f y) hc G (fun y => y.2.2)
  have heq : (fun y : W => g ⟨f y, hWV y.2⟩) = (fun y : W => G (f y)) := by
    funext y
    exact hgeq ⟨f y, hWV y.2⟩ ⟨y.2.1.2, Set.mem_univ _⟩
  rw [heq]
  exact hcomp

/-- A holomorphic function on an open domain is globally holomorphic on that open subspace.
Source: Grauert–Remmert, Coherent Analytic Sheaves, §1.1.5; open atlas restriction. -/
theorem open_holFun_univ {M : Type*} [TopologicalSpace M] (S : an_ReducedSpace M)
    {U : Set M} (hU : IsOpen U) (g : U → ℂ) (hg : S.IsHolFun g) :
    (anrem_openSpace S hU).IsHolFun (fun y : (Set.univ : Set U) => g y) := by
  intro x i hxi
  obtain ⟨N, hNo, hxN, G, hG, heq⟩ := hg x.1 i hxi
  refine ⟨Subtype.val ⁻¹' N, hNo.preimage continuous_subtype_val, hxN, G, hG, ?_⟩
  intro y hy
  exact heq y.1 hy

end AlgebraicGeometry.SingularCycles
