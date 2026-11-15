import HodgeLean.Foundations.Program.SchoenCycleFiniteQuotientTopology
import Mathlib.Topology.Algebra.ConstMulAction

/-! # Local stabilizer orbits in the actual quotient
Only stabilizers identify points in sufficiently small neighborhoods.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open TopologicalSpace Filter
namespace HodgeLean.Foundations.Program

/-- The actual scheme symmetries act on complex points with the stated order.
Source: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, third edition,
Chapter 1, section 1, finite-group actions on quotient fibres. -/
@[instance_reducible]
def s2e_quotientPointMulAction (X : Over (Spec ↧ℂ))
    (G : Type) [Group G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u) :
    MulAction G (ComplexPoint X) where
  smul g x := Point.map (a g) x
  one_smul x := by change Point.map (a 1) x = x; rw [ha1, Point.map_id]
  mul_smul g h x := by
    change Point.map (a (g * h)) x = Point.map (a g) (Point.map (a h) x)
    rw [hamul, Point.map_comp_apply]

example (X : Over (Spec ↧ℂ))
    (G : Type) [Group G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (g : G) (x : ComplexPoint X) :
    letI := s2e_quotientPointMulAction X G a ha1 hamul
    g • x = Point.map (a g) x := rfl

/-- Inside arbitrarily small stabilizer-invariant neighborhoods, quotient fibres
are already orbits of the stabilizer of the marked point.
Source: Bredon, Introduction to Compact Transformation Groups (1972),
Chapter I, section 3, local finite orbit spaces; Mumford--Fogarty--Kirwan,
Geometric Invariant Theory, third edition, Chapter 1, section 1. -/
theorem s2e_finite_quotient_local_stabilizer_orbits
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [IsIntegral Y.left] [IsProjective Y.hom]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (S : Over (Spec ↧ℂ)) (f : X ⟶ S),
      (∀ u, a u ≫ f = f) → ∃! g : Y ⟶ S, q ≫ g = f)
    (x₀ : ComplexPoint X) (N : Opens (ComplexPoint X)) (hx₀ : x₀ ∈ N) :
    ∃ U : Opens (ComplexPoint X), x₀ ∈ U ∧ U ≤ N ∧
      (∀ g, Point.map (a g) x₀ = x₀ → ∀ x ∈ U, Point.map (a g) x ∈ U) ∧
      ∀ x ∈ U, ∀ y ∈ U, Point.map q x = Point.map q y →
        ∃ g : G, Point.map (a g) x₀ = x₀ ∧ Point.map (a g) x = y := by
  letI := s2e_quotientPointMulAction X G a ha1 hamul
  letI : ContinuousConstSMul G (ComplexPoint X) := ⟨fun g => Point.continuous_map (a g)⟩
  have : Surjective q.left :=
    s2e_step1_surjective_of_complexPoint_surjective X Y q hsurj
  obtain ⟨V, hV, hdis⟩ := ProperlyDiscontinuousSMul.exists_nhds_disjoint_image G x₀
  obtain ⟨O, hOV, hO, hxO⟩ := mem_nhds_iff.mp
    (inter_mem hV (N.isOpen.mem_nhds hx₀))
  let K := MulAction.stabilizer G x₀
  let W : Set (ComplexPoint X) := ⋂ g : K, ((g : G) • ·) ⁻¹' O
  have hWopen : IsOpen W :=
    isOpen_iInter_of_finite fun g => hO.preimage (continuous_const_smul (g : G))
  have hxW : x₀ ∈ W := by
    apply Set.mem_iInter.mpr
    intro g
    change (g : G) • x₀ ∈ O
    have hg : (g : G) • x₀ = x₀ := g.property
    rw [hg]
    exact hxO
  have hWO : W ⊆ O := by
    intro x hx
    have h := Set.mem_iInter.mp hx (1 : K)
    change (1 : G) • x ∈ O at h
    rw [one_smul] at h
    exact h
  refine ⟨⟨W, hWopen⟩, hxW, (fun x hx => (hOV (hWO hx)).2), ?_, ?_⟩
  · intro g hg x hx
    have hgK : g ∈ K := hg
    let k : K := ⟨g, hgK⟩
    apply Set.mem_iInter.mpr
    intro h
    change (h : G) • (g • x) ∈ O
    rw [← mul_smul]
    exact Set.mem_iInter.mp hx (h * k)
  · intro x hx y hy hxy
    obtain ⟨g, hg⟩ :=
      s2e_step1_finite_quotient_point_orbits X Y G a ha1 hamul q hinv hquot x y hxy
    refine ⟨g, ?_, hg⟩
    by_contra hne
    exact Set.disjoint_left.mp (hdis g hne)
      ⟨x, (hOV (hWO hx)).1, hg⟩ (hOV (hWO hy)).1

end HodgeLean.Foundations.Program
