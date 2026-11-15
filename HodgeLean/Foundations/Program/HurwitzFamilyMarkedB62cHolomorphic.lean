import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cExtension

noncomputable section

namespace HodgeLean.Foundations.Program

open Manifold Filter Topology Set
open scoped Manifold ContDiff Topology

theorem b6m_analyticAt_of_comp {g k : ℂ → ℂ} {z : ℂ}
    (hg : ContinuousAt g z) (hk : AnalyticAt ℂ k (g z))
    (hkd : fderiv ℂ k (g z) ≠ 0) (hkg : AnalyticAt ℂ (k ∘ g) z) :
    AnalyticAt ℂ g z := by
  obtain ⟨s, hs, _, _, hsk⟩ := b4cov_exists_localInverse (by simp) (by simp) hk hkd
  have heq : g =ᶠ[𝓝 z] s ∘ (k ∘ g) := by
    filter_upwards [hg.eventually hsk] with w hw
    exact hw.symm
  exact (hs.comp (f := k ∘ g) (x := z) hkg).congr heq.symm

theorem b6m_contMDiffAt_of_unramified_comp {C D X : Type}
    [TopologicalSpace C] [TopologicalSpace D] [TopologicalSpace X]
    [ChartedSpace ℂ C] [ChartedSpace ℂ D] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [IsManifold 𝓘(ℂ, ℂ) ω X]
    (e : C → D) (he : Continuous e) (f : C → X) (k : D → X)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (hp : ∀ x, k (e x) = f x) (x : C)
    (hkd : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) k (e x) ≠ 0) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e x := by
  let φ := extChartAt 𝓘(ℂ, ℂ) x
  let ψ := extChartAt 𝓘(ℂ, ℂ) (e x)
  let G := writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x e
  let K := writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (e x) k
  have hGx : G (φ x) = ψ (e x) := by
    change ψ (e (φ.symm (φ x))) = ψ (e x)
    rw [show φ.symm (φ x) = x from extChartAt_to_inv x]
  have hφ : Tendsto φ.symm (𝓝 (φ x)) (𝓝 x) := by
    have hc := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℂ, ℂ)) (n := ω) x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))).continuousAt
    simpa only [extChartAt_to_inv] using hc.tendsto
  have heφ : Tendsto (e ∘ φ.symm) (𝓝 (φ x)) (𝓝 (e x)) :=
    he.continuousAt.tendsto.comp hφ
  have hGc : ContinuousAt G (φ x) := by
    change Tendsto G (𝓝 (φ x)) (𝓝 (G (φ x)))
    rw [hGx]
    exact (contMDiffAt_extChartAt (I := 𝓘(ℂ, ℂ)) (n := ω) (x := e x)).continuousAt.tendsto.comp heφ
  have hK : AnalyticAt ℂ K (G (φ x)) := by
    rw [hGx]
    exact b4cov_analyticOnNhd k hk (e x) _ (b4cov_mem_good k (e x))
  have hKd : fderiv ℂ K (G (φ x)) ≠ 0 := by
    rw [hGx]
    exact hkd ∘ (b4cov_mfderiv_eq_zero_iff k hk (e x) (e x)
      (mem_extChartAt_source _) (mem_extChartAt_source _)).mpr
  have heq : K ∘ G =ᶠ[𝓝 (φ x)] writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x f := by
    have hsrc : ψ.source ∈ 𝓝 (e x) := extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) (e x)
    filter_upwards [heφ.eventually hsrc] with z hz
    change e (φ.symm z) ∈ ψ.source at hz
    change extChartAt 𝓘(ℂ, ℂ) (k (e x)) (k (ψ.symm (ψ (e (φ.symm z))))) = _
    rw [ψ.left_inv hz, hp, hp]
    rfl
  have hKG : AnalyticAt ℂ (K ∘ G) (φ x) :=
    (b4cov_analyticOnNhd f hf x _ (b4cov_mem_good f x)).congr heq.symm
  have hG := b6m_analyticAt_of_comp hGc hK hKd hKG
  rw [contMDiffAt_iff]
  refine ⟨he.continuousAt, ?_⟩
  simpa only [G, φ, writtenInExtChartAt, modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ]
    using hG.contDiffAt

theorem b6m_contMDiff_of_finite_exceptional {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    (g : C → D) (hg : Continuous g) (S : Set C) (hS : S.Finite)
    (hhol : ∀ x ∉ S, ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g x) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g := by
  intro x
  let φ := extChartAt 𝓘(ℂ, ℂ) x
  let ψ := extChartAt 𝓘(ℂ, ℂ) (g x)
  let G := writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x g
  have hGx : G (φ x) = ψ (g x) := by
    change ψ (g (φ.symm (φ x))) = ψ (g x)
    rw [show φ.symm (φ x) = x from extChartAt_to_inv x]
  have hφ : Tendsto φ.symm (𝓝 (φ x)) (𝓝 x) := by
    have hc := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℂ, ℂ)) (n := ω) x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))).continuousAt
    simpa only [extChartAt_to_inv] using hc.tendsto
  have hgφ : Tendsto (g ∘ φ.symm) (𝓝 (φ x)) (𝓝 (g x)) :=
    hg.continuousAt.tendsto.comp hφ
  have hGc : ContinuousAt G (φ x) := by
    change Tendsto G (𝓝 (φ x)) (𝓝 (G (φ x)))
    rw [hGx]
    exact (contMDiffAt_extChartAt (I := 𝓘(ℂ, ℂ)) (n := ω) (x := g x)).continuousAt.tendsto.comp hgφ
  have hA : AnalyticAt ℂ G (φ x) := by
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ hGc
    have havoid : (φ '' S \ {φ x})ᶜ ∈ 𝓝 (φ x) :=
      (hS.image φ).sdiff.isClosed.isOpen_compl.mem_nhds (by simp)
    have hsrc : ψ.source ∈ 𝓝 (g x) := extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) (g x)
    have htgt : φ.target ∈ 𝓝 (φ x) :=
      (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)
    filter_upwards [nhdsWithin_le_nhds havoid, nhdsWithin_le_nhds (hgφ.eventually hsrc),
      nhdsWithin_le_nhds htgt, self_mem_nhdsWithin] with z hz hzg hzt hzne
    have hzS : φ.symm z ∉ S := by
      intro hy
      exact hz ⟨⟨φ.symm z, hy, φ.right_inv hzt⟩, hzne⟩
    have hφhol : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω φ.symm z :=
      (contMDiffOn_extChartAt_symm x).contMDiffAt ((isOpen_extChartAt_target x).mem_nhds hzt)
    have hghol := (hhol (φ.symm z) hzS).comp z hφhol
    have hzg' : g (φ.symm z) ∈ (chartAt ℂ (g x)).source := by
      change g (φ.symm z) ∈ (extChartAt 𝓘(ℂ, ℂ) (g x)).source at hzg
      rwa [extChartAt_source] at hzg
    have hψhol : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω ψ (g (φ.symm z)) :=
      contMDiffAt_extChartAt' hzg'
    have hGhol : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω G z := hψhol.comp z hghol
    exact (contMDiffAt_iff_contDiffAt.mp hGhol).differentiableAt (by simp)
  rw [contMDiffAt_iff]
  refine ⟨hg.continuousAt, ?_⟩
  simpa only [G, φ, writtenInExtChartAt, modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ]
    using hA.contDiffAt

theorem b6m_contMDiff_of_injective_comp {C D X : Type}
    [TopologicalSpace C] [TopologicalSpace D] [TopologicalSpace X]
    [ChartedSpace ℂ C] [ChartedSpace ℂ D] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [IsManifold 𝓘(ℂ, ℂ) ω X] [CompactSpace D] [ConnectedSpace D]
    (e : C → D) (he : Continuous e) (hei : Function.Injective e)
    (f : C → X) (k : D → X)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (hnc : ∃ y z, k y ≠ k z) (hp : ∀ x, k (e x) = f x) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e := by
  have hfin := b4cov_critical_finite (E := ℂ) (E' := ℂ) (by simp) k hk hnc
  apply b6m_contMDiff_of_finite_exceptional e he
    (e ⁻¹' {y | mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) k y = 0})
    (Set.Finite.preimage hei.injOn hfin)
  intro x hx
  exact b6m_contMDiffAt_of_unramified_comp e he f k hf hk hp x hx

end HodgeLean.Foundations.Program
