import HodgeLean.Foundations.Program.PrymParabolicIntersectionWedgeTransport
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cHolomorphic
import HodgeLean.Foundations.Program.RiemannRochProofs

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

set_option backward.isDefEq.respectTransparency false in
theorem hga_holomorphic_plane_lift {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T]
    [IsManifold 𝓘(ℂ, ℂ) ω T] [CompactSpace T] [ConnectedSpace T]
    (U : TopologicalSpace.Opens ℂ) (e : C(U, T)) (k : T → OnePoint ℂ)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k) (c : ℂ)
    (hp : ∀ z : U, k (e z) = ((z.val + c : ℂ) : OnePoint ℂ))
    (x y : U) (hxy : x ≠ y) : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e := by
  have hi (a b : U) (h : k (e a) = k (e b)) : a = b := by
    rw [hp, hp] at h
    apply Subtype.ext
    exact add_right_cancel (OnePoint.coe_injective h)
  have he : Function.Injective e := fun a b h ↦ hi a b (congrArg k h)
  have hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun z : U ↦ ((z.val + c : ℂ) : OnePoint ℂ)) :=
    b4cov_coe_contMDiff.comp (contMDiff_subtype_val.add contMDiff_const)
  exact b6m_contMDiff_of_injective_comp e e.continuous he _ k hf hk
    ⟨e x, e y, fun h ↦ hxy (hi x y h)⟩ hp

set_option backward.isDefEq.respectTransparency false in
open scoped Topology in
theorem hga_holomorphic_lift_germ {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T]
    [IsManifold 𝓘(ℂ, ℂ) ω T] [CompactSpace T] [ConnectedSpace T]
    (e : C(ℂ, T)) (k : T → OnePoint ℂ)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k) (c : ℂ)
    (hp : ∀ᶠ z : ℂ in 𝓝 0, k (e z) = ((z + c : ℂ) : OnePoint ℂ)) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e 0 := by
  obtain ⟨S, hS, hSo, h0⟩ := mem_nhds_iff.mp hp
  let U : TopologicalSpace.Opens ℂ := ⟨S, hSo⟩
  let eU : C(U, T) := e.comp ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := (infinite_of_mem_nhds (0 : ℂ) (hSo.mem_nhds h0)).nontrivial
  have hh : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω eU :=
    hga_holomorphic_plane_lift U eU k hk c (fun z ↦ hS z.property)
      ⟨x, hx⟩ ⟨y, hy⟩ (fun h ↦ hxy (congrArg Subtype.val h))
  exact contMDiffAt_subtype_iff.mp (hh ⟨0, h0⟩)

set_option backward.isDefEq.respectTransparency false in
open scoped Topology in
theorem hga_holomorphic_lift_coordinates {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T]
    [IsManifold 𝓘(ℂ, ℂ) ω T] [CompactSpace T] [ConnectedSpace T]
    (e : C(ℂ, T)) (k : T → OnePoint ℂ)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k) (c : ℂ)
    (hp : ∀ᶠ z : ℂ in 𝓝 0, k (e z) = ((z + c : ℂ) : OnePoint ℂ)) :
    ∃ q : OpenPartialHomeomorph ℂ T, 0 ∈ q.source ∧ q 0 = e 0 ∧
      Filter.EventuallyEq (𝓝 0) (q : ℂ → T) e ∧
      ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω q 0 ∧
      ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω q.symm (e 0) := by
  obtain ⟨S, hS, hSo, h0⟩ := mem_nhds_iff.mp hp
  have hi : Set.InjOn e S := by
    intro a ha b hb hab
    have h := congrArg k hab
    rw [hS ha, hS hb] at h
    exact add_right_cancel (OnePoint.coe_injective h)
  exact RiemannRochTop_injective_holomorphic_coordinates e 0
    (hga_holomorphic_lift_germ e k hk c hp) S (hSo.mem_nhds h0) hi

#print axioms hga_holomorphic_lift_coordinates

#print axioms hga_holomorphic_lift_germ

#print axioms hga_holomorphic_plane_lift
end HodgeLean.Foundations.Program
