import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bBranchRoot

noncomputable section
open Filter Manifold
open scoped Topology ContDiff Manifold

namespace HodgeLean.Foundations.Program

theorem b6a_lift_chart_contDiffAt (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C] (f : C → OnePoint ℂ) (n : C → ℕ) (hn : ∀ x, 0 < n x)
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hA : ∀ q, q ∈ (A q).source)
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val)
    (hfree : ∀ q, f q.2 ∉ Set.range (b6_branch b) →
      ∀ y ∈ (A q).source, b6a_map b f y = ((A q y).2 : OnePoint ℂ))
    (hmark : ∀ q (j : Fin 13), f q.2 = b6_branch b j →
      (A q q).2 = 0 ∧ ∀ y ∈ (A q).source,
        b6a_map b f y = b6a_value y.1.val j ((A q y).2 ^ n q.2))
    (H : b6t_polydisc b × C → b6t_polydisc b × C) (hc : Continuous H)
    (hHparam : ∀ y, (H y).1 = y.1) (hHf : ∀ y, f (H y).2 = f y.2)
    (q : b6t_polydisc b × C) :
    ContDiffAt ℂ ω (fun z ↦ A (H q) (H ((A q).symm z))) (A q q) := by
  let T := fun z ↦ A (H q) (H ((A q).symm z))
  have hq := (A q).map_source (hA q)
  have hleft := (A q).left_inv (hA q)
  have hsymm := (A q).continuousAt_symm hq
  have hdom : ∀ᶠ z in 𝓝 (A q q), z ∈ (A q).target ∧
      H ((A q).symm z) ∈ (A (H q)).source := by
    apply Filter.Eventually.and ((A q).open_target.mem_nhds hq)
    have hh : ContinuousAt (fun z ↦ H ((A q).symm z)) (A q q) :=
      hc.continuousAt.comp (f := (A q).symm) hsymm
    have hh' : Tendsto (fun z ↦ H ((A q).symm z)) (𝓝 (A q q)) (𝓝 (H q)) := by
      simpa only [ContinuousAt, hleft] using hh
    exact hh' ((A (H q)).open_source.mem_nhds (hA (H q)))
  have hT : ∀ᶠ z in 𝓝 (A q q), ContinuousAt T z := by
    filter_upwards [hdom] with z hz
    exact ((A (H q)).continuousAt hz.2).comp (f := fun w ↦ H ((A q).symm w))
      (hc.continuousAt.comp (f := (A q).symm) ((A q).continuousAt_symm hz.1))
  have hfst : ∀ᶠ z in 𝓝 (A q q), (T z).1 = z.1 := by
    filter_upwards [hdom] with z hz
    change (A (H q) (H ((A q).symm z))).1 = z.1
    rw [hparam _ _ hz.2, hHparam]
    rw [← hparam q _ ((A q).map_target hz.1), (A q).right_inv hz.1]
  have hTf : ContDiffAt ℂ ω (fun z ↦ (T z).1) (A q q) :=
    contDiffAt_fst.congr_of_eventuallyEq hfst
  suffices hs : ContDiffAt ℂ ω (fun z ↦ (T z).2) (A q q) by
    exact hTf.prodMk hs
  have hmap (y : b6t_polydisc b × C) : b6a_map b f (H y) = b6a_map b f y := by
    simp only [b6a_map, hHparam, hHf]
  by_cases hm : f q.2 ∈ Set.range (b6_branch b)
  · obtain ⟨j, hj⟩ := hm
    have hj' : f (H q).2 = b6_branch b j := (hHf q).trans hj.symm
    have hp : ∀ᶠ z in 𝓝 (A q q), (T z).2 ^ n (H q).2 = z.2 ^ n q.2 := by
      filter_upwards [hdom] with z hz
      have h := (hmark (H q) j hj').2 _ hz.2
      rw [hmap, (hmark q j hj.symm).2 _ ((A q).map_target hz.1),
        (A q).right_inv hz.1, hHparam] at h
      exact (b6a_value_injective ((A q).symm z).1.val j h).symm
    have hz : A q q = ((A q q).1, (0 : ℂ)) := Prod.ext rfl (hmark q j hj.symm).1
    rw [hz] at hT hp ⊢
    exact b6a_contDiffAt_root_product_monomial (fun z ↦ (T z).2) _ _ _ (hn _)
      (hT.mono fun z hz ↦ hz.snd) hp
  · have hm' : f (H q).2 ∉ Set.range (b6_branch b) := by rwa [hHf]
    apply contDiffAt_snd.congr_of_eventuallyEq
    filter_upwards [hdom] with z hz
    apply OnePoint.coe_injective
    rw [← hfree (H q) hm' _ hz.2, hmap,
      hfree q hm _ ((A q).map_target hz.1), (A q).right_inv hz.1]

theorem b6a_lift_contMDiff (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    (f : C → OnePoint ℂ) (n : C → ℕ) (hn : ∀ x, 0 < n x)
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hA : ∀ q, q ∈ (A q).source ∧
      A q ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val)
    (hfree : ∀ q, f q.2 ∉ Set.range (b6_branch b) →
      ∀ y ∈ (A q).source, b6a_map b f y = ((A q y).2 : OnePoint ℂ))
    (hmark : ∀ q (j : Fin 13), f q.2 = b6_branch b j →
      (A q q).2 = 0 ∧ ∀ y ∈ (A q).source,
        b6a_map b f y = b6a_value y.1.val j ((A q y).2 ^ n q.2))
    (H : b6t_polydisc b × C → b6t_polydisc b × C) (hc : Continuous H)
    (hHparam : ∀ y, (H y).1 = y.1) (hHf : ∀ y, f (H y).2 = f y.2) :
    ContMDiff 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω H := by
  intro q
  let T := fun z ↦ A (H q) (H ((A q).symm z))
  have hT : ContDiffAt ℂ ω T (A q q) :=
    b6a_lift_chart_contDiffAt b C f n hn A (fun q ↦ (hA q).1)
      hparam hfree hmark H hc hHparam hHf q
  have hchart : ContMDiffAt 𝓘(ℂ, (Fin 10 → ℂ) × ℂ)
      𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (A q) q :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (hA q).2) (hA q).1
  have hTq : T (A q q) = A (H q) (H q) := by
    dsimp [T]
    rw [(A q).left_inv (hA q).1]
  have hinv : ContMDiffAt 𝓘(ℂ, (Fin 10 → ℂ) × ℂ)
      𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (A (H q)).symm (T (A q q)) := by
    rw [hTq]
    exact contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (hA (H q)).2)
      ((A (H q)).map_source (hA (H q)).1)
  apply (hinv.comp q (hT.contMDiffAt.comp q hchart)).congr_of_eventuallyEq
  filter_upwards [(A q).open_source.mem_nhds (hA q).1,
    hc.continuousAt ((A (H q)).open_source.mem_nhds (hA (H q)).1)] with y hy hHy
  change H y = (A (H q)).symm (A (H q) (H ((A q).symm (A q y))))
  rw [(A q).left_inv hy, (A (H q)).left_inv hHy]

end HodgeLean.Foundations.Program
