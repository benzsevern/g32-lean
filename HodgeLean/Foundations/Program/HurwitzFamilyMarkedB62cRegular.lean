import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSphere

noncomputable section

namespace HodgeLean.Foundations.Program

open Manifold
open scoped Manifold ContDiff Topology

theorem b6m_dense_preimage_of_localHomeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (s : Set X)
    (hs : Dense s) (hso : IsOpen s) (hf : IsLocalHomeomorphOn f s)
    (U : Set Y) (hU : Dense U) : Dense (s ∩ f ⁻¹' U) := by
  apply dense_iff_inter_open.mpr
  intro V hV hVn
  obtain ⟨x, hxV, hxs⟩ := hs.inter_open_nonempty V hV hVn
  obtain ⟨e, hxe, he⟩ := hf x hxs
  have ho : IsOpen (e '' (V ∩ s ∩ e.source)) :=
    e.isOpen_image_of_subset_source ((hV.inter hso).inter e.open_source)
      (fun _ h ↦ h.2)
  obtain ⟨y, ⟨z, hz, rfl⟩, hy⟩ := hU.inter_open_nonempty _ ho
    ⟨e x, x, ⟨⟨hxV, hxs⟩, hxe⟩, rfl⟩
  refine ⟨z, hz.1.1, hz.1.2, ?_⟩
  change f z ∈ U
  rw [he]
  exact hy

theorem b6m_holomorphic_dense_preimage {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (f : C → D) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hnc : ∃ x y, f x ≠ f y) (U : Set D) (hU : Dense U) :
    Dense ({x | mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x ≠ 0} ∩ f ⁻¹' U) := by
  haveI : Nontrivial C := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨x, y, fun h ↦ hxy (congrArg f h)⟩
  have hfin := b4cov_critical_finite (E := ℂ) (E' := ℂ) (by simp) f hf hnc
  have hd : Dense {x | mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x ≠ 0} := by
    simpa only [Set.sdiff_eq, Set.univ_inter, Set.compl_setOf] using
      dense_univ.sdiff_finite hfin
  exact b6m_dense_preimage_of_localHomeomorph f _ hd hfin.isClosed.isOpen_compl
    (b4cov_isLocalHomeomorphOn (by simp) (by simp) f hf) U hU

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b6m_filling_orientation_dense_open {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [T2Space D] [CompactSpace D] [ConnectedSpace D]
    (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart) (ht : t ∈ b6t_polydisc b)
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (hfn : ∃ x y, f x ≠ f y) (hkn : ∃ x y, k x ≠ k y)
    (e : C ≃ₜ D) (he : ∀ x, k (e x) = b6t_sphere b t (f x)) :
    ∃ V : Set C, IsOpen V ∧ Dense V ∧ ∀ x ∈ V,
      MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e x ∧ ∀ v w : ℂ,
        SignType.sign (b3_orient ℂ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e x v)
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e x w)) = SignType.sign (b3_orient ℂ v w) := by
  haveI : Nontrivial C := by
    obtain ⟨x, y, hxy⟩ := hfn
    exact ⟨x, y, fun h ↦ hxy (congrArg f h)⟩
  let U : Set (OnePoint ℂ) := {x | ∃ z : ℂ, (z : OnePoint ℂ) = x ∧
    ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b}
  let A : Set C := {x | mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x ≠ 0} ∩ f ⁻¹' U
  let B : Set C := e ⁻¹' {y | mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) k y = 0}
  have hff := b4cov_critical_finite (E := ℂ) (E' := ℂ) (by simp) f hf hfn
  have hkf := b4cov_critical_finite (E := ℂ) (E' := ℂ) (by simp) k hk hkn
  have hB : B.Finite := Set.Finite.preimage e.injective.injOn hkf
  have hA : IsOpen A := hff.isClosed.isOpen_compl.inter
    (hf.continuous.isOpen_preimage U (b6m_sphere_regular_open_dense b).1)
  have hd : Dense A := b6m_holomorphic_dense_preimage f hf hfn U
    (b6m_sphere_regular_open_dense b).2
  refine ⟨A \ B, hA.sdiff hB.isClosed, hd.sdiff_finite hB, ?_⟩
  intro x hx
  obtain ⟨z, hz, hzr⟩ := hx.1.2
  exact b6m_filling_comparison_regular b t hb ht f k hf hk e he x z hz.symm
    hzr hx.1.1 hx.2

end HodgeLean.Foundations.Program
