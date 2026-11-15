import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bProjection

noncomputable section

open scoped Manifold ContDiff
open Manifold
open Filter

namespace HodgeLean.Foundations.Program

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

noncomputable def b6a_sliceChart (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C]
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val)
    (t : b6t_polydisc b) (x : C) : OpenPartialHomeomorph C ℂ where
  toFun y := (A (t, x) (t, y)).2
  invFun z := ((A (t, x)).symm (t.val, z)).2
  source := {y | (t, y) ∈ (A (t, x)).source}
  target := {z | (t.val, z) ∈ (A (t, x)).target}
  map_source' y hy := by
    have hm := (A (t, x)).map_source hy
    have he : A (t, x) (t, y) = (t.val, (A (t, x) (t, y)).2) :=
      Prod.ext (hparam (t, x) (t, y) hy) rfl
    exact he ▸ hm
  map_target' z hz := by
    have hm := (A (t, x)).symm.map_source hz
    have hr := (A (t, x)).right_inv hz
    have hp := hparam (t, x) ((A (t, x)).symm (t.val, _)) hm
    have hp' : ((A (t, x)).symm (t.val, z)).1 = t := by
      apply Subtype.ext
      exact hp.symm.trans (congrArg Prod.fst hr)
    have he : (t, ((A (t, x)).symm (t.val, z)).2) =
        (A (t, x)).symm (t.val, z) := Prod.ext hp'.symm rfl
    exact he ▸ hm
  left_inv' y hy := by
    have he : A (t, x) (t, y) = (t.val, (A (t, x) (t, y)).2) :=
      Prod.ext (hparam (t, x) (t, y) hy) rfl
    have h := (A (t, x)).left_inv hy
    rw [he] at h
    exact congrArg Prod.snd h
  right_inv' z hz := by
    have hm := (A (t, x)).symm.map_source hz
    have hr := (A (t, x)).right_inv hz
    have hp := hparam (t, x) ((A (t, x)).symm (t.val, z)) hm
    have hp' : ((A (t, x)).symm (t.val, z)).1 = t := by
      apply Subtype.ext
      exact hp.symm.trans (congrArg Prod.fst hr)
    have h := (A (t, x)).right_inv hz
    have he : (t, ((A (t, x)).symm (t.val, z)).2) =
        (A (t, x)).symm (t.val, z) := Prod.ext hp'.symm rfl
    exact congrArg Prod.snd ((congrArg (fun p ↦ A (t, x) p) he).trans h)
  continuousOn_toFun :=
    continuous_snd.continuousOn.comp
      ((A (t, x)).continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn
        (fun _ hy ↦ hy)) (fun _ hy ↦ (A (t, x)).map_source hy)
  continuousOn_invFun :=
    continuous_snd.continuousOn.comp
      ((A (t, x)).symm.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn (fun _ hz ↦ hz))
      (fun _ hz ↦ (A (t, x)).symm.map_source hz)
  open_source := (A (t, x)).open_source.preimage (continuous_const.prodMk continuous_id)
  open_target := (A (t, x)).open_target.preimage (continuous_const.prodMk continuous_id)

noncomputable def b6a_sliceChartedSpace (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C]
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hA : ∀ q, q ∈ (A q).source)
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val)
    (t : b6t_polydisc b) : ChartedSpace ℂ C where
  atlas := Set.range (b6a_sliceChart b C A hparam t)
  chartAt := b6a_sliceChart b C A hparam t
  mem_chart_source x := hA (t, x)
  chart_mem_atlas x := ⟨x, rfl⟩

theorem b6a_sliceChart_mem_atlas (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C]
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hA : ∀ q, q ∈ (A q).source)
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val)
    (t : b6t_polydisc b) (x : C) :
    letI := b6a_sliceChartedSpace b C A hA hparam t
    b6a_sliceChart b C A hparam t x ∈ atlas ℂ C := by
  exact ⟨x, rfl⟩

theorem b6a_slice_transition_apply (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C]
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val)
    (t : b6t_polydisc b) (x x' : C) (z : ℂ)
    (hz : z ∈ (b6a_sliceChart b C A hparam t x).target) :
    ((b6a_sliceChart b C A hparam t x).symm.trans
      (b6a_sliceChart b C A hparam t x')) z =
      (((A (t, x)).symm.trans (A (t, x'))) (t.val, z)).2 := by
  have hm := (A (t, x)).symm.map_source hz
  have hr := (A (t, x)).right_inv hz
  have hp := hparam (t, x) ((A (t, x)).symm (t.val, z)) hm
  have hp' : ((A (t, x)).symm (t.val, z)).1 = t := by
    apply Subtype.ext
    exact hp.symm.trans (congrArg Prod.fst hr)
  change (A (t, x') (t, ((A (t, x)).symm (t.val, z)).2)).2 =
    (A (t, x') ((A (t, x)).symm (t.val, z))).2
  congr 2
  exact Prod.ext hp'.symm rfl

theorem b6a_slice_transition_contDiff (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hA : ∀ q, q ∈ (A q).source ∧
      A q ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val)
    (t : b6t_polydisc b) (x x' : C) :
    ContDiffOn ℂ ω ((b6a_sliceChart b C A hparam t x).symm.trans
      (b6a_sliceChart b C A hparam t x'))
      ((b6a_sliceChart b C A hparam t x).symm.trans
        (b6a_sliceChart b C A hparam t x')).source := by
  let T := (A (t, x)).symm.trans (A (t, x'))
  have hg := (contDiffGroupoid ω 𝓘(ℂ, (Fin 10 → ℂ) × ℂ)).compatible
    (hA (t, x)).2 (hA (t, x')).2
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hg
  have hT : ContDiffOn ℂ ω T T.source := by
    simpa [contDiffPregroupoid, T] using hg.1
  have hmaps : Set.MapsTo (fun z : ℂ ↦ (t.val, z))
      ((b6a_sliceChart b C A hparam t x).symm.trans
        (b6a_sliceChart b C A hparam t x')).source T.source := by
    intro z hz
    have hz₁ : z ∈ (b6a_sliceChart b C A hparam t x).target := hz.1
    have hm := (A (t, x)).symm.map_source hz₁
    have hr := (A (t, x)).right_inv hz₁
    have hp := hparam (t, x) ((A (t, x)).symm (t.val, z)) hm
    have hp' : ((A (t, x)).symm (t.val, z)).1 = t := by
      apply Subtype.ext
      exact hp.symm.trans (congrArg Prod.fst hr)
    refine ⟨hz₁, ?_⟩
    have he : (t, ((A (t, x)).symm (t.val, z)).2) =
        (A (t, x)).symm (t.val, z) := Prod.ext hp'.symm rfl
    change (A (t, x)).symm (t.val, z) ∈ (A (t, x')).source
    exact he ▸ hz.2
  have hc := hT.comp
    (contDiff_const.prodMk contDiff_id).contDiffOn hmaps
  have hv := contDiff_snd.comp_contDiffOn hc
  apply hv.congr
  intro z hz
  simpa [T, Function.comp_def] using
    b6a_slice_transition_apply b C A hparam t x x' z hz.1

theorem b6a_slice_isManifold (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hA : ∀ q, q ∈ (A q).source ∧
      A q ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val)
    (t : b6t_polydisc b) :
    letI : ChartedSpace ℂ C :=
      b6a_sliceChartedSpace b C A (fun q ↦ (hA q).1) hparam t
    IsManifold 𝓘(ℂ, ℂ) ω C := by
  letI := b6a_sliceChartedSpace b C A (fun q ↦ (hA q).1) hparam t
  apply isManifold_of_contDiffOn 𝓘(ℂ, ℂ) ω C
  rintro e e' ⟨x, rfl⟩ ⟨x', rfl⟩
  simpa using b6a_slice_transition_contDiff b C A hA hparam t x x'

theorem b6a_slice_inclusion_contMDiff (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hA : ∀ q, q ∈ (A q).source ∧
      A q ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val)
    (t : b6t_polydisc b) :
    letI : ChartedSpace ℂ C :=
      b6a_sliceChartedSpace b C A (fun q ↦ (hA q).1) hparam t
    letI : IsManifold 𝓘(ℂ, ℂ) ω C := b6a_slice_isManifold b C A hA hparam t
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : C ↦ (t, x)) := by
  letI : ChartedSpace ℂ C :=
    b6a_sliceChartedSpace b C A (fun q ↦ (hA q).1) hparam t
  letI : IsManifold 𝓘(ℂ, ℂ) ω C := b6a_slice_isManifold b C A hA hparam t
  intro x
  let S := b6a_sliceChart b C A hparam t x
  let E := A (t, x)
  have hS : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω S x :=
    contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (b6a_sliceChart_mem_atlas b C A
        (fun q ↦ (hA q).1) hparam t x)) (hA (t, x)).1
  have hxcoord : E (t, x) = (t.val, S x) :=
    Prod.ext (hparam (t, x) (t, x) (hA (t, x)).1) rfl
  have hEinv : ContMDiffAt 𝓘(ℂ, (Fin 10 → ℂ) × ℂ)
      𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω E.symm (t.val, S x) := by
    rw [← hxcoord]
    exact contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (hA (t, x)).2) (E.map_source (hA (t, x)).1)
  have hemb : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun z : ℂ ↦ (t.val, z)) :=
    (contDiff_const.prodMk contDiff_id).contMDiff
  have hc := hEinv.comp x (hemb.contMDiffAt.comp x hS)
  apply hc.congr_of_eventuallyEq
  filter_upwards [S.open_source.mem_nhds (hA (t, x)).1] with y hy
  have he : E (t, y) = (t.val, S y) := Prod.ext (hparam (t, x) (t, y) hy) rfl
  simpa [Function.comp_def, E, S, he] using (E.left_inv hy).symm

theorem b6a_slice_map_contMDiff (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hA : ∀ q, q ∈ (A q).source ∧
      A q ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val)
    (F : b6t_polydisc b × C → OnePoint ℂ)
    (hF : ContMDiff 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω F)
    (t : b6t_polydisc b) :
    letI : ChartedSpace ℂ C :=
      b6a_sliceChartedSpace b C A (fun q ↦ (hA q).1) hparam t
    letI : IsManifold 𝓘(ℂ, ℂ) ω C := b6a_slice_isManifold b C A hA hparam t
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ F (t, x)) := by
  letI : ChartedSpace ℂ C :=
    b6a_sliceChartedSpace b C A (fun q ↦ (hA q).1) hparam t
  letI : IsManifold 𝓘(ℂ, ℂ) ω C := b6a_slice_isManifold b C A hA hparam t
  exact hF.comp (b6a_slice_inclusion_contMDiff b C A hA hparam t)

theorem b6a_slice_vertical_map_contMDiff (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hA : ∀ q, q ∈ (A q).source ∧
      A q ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val)
    (K : b6t_polydisc b × C → b6t_polydisc b × C)
    (k : C → C) (hK : ∀ t x, K (t, x) = (t, k x))
    (hKdiff : ContMDiff 𝓘(ℂ, (Fin 10 → ℂ) × ℂ)
      𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω K)
    (t : b6t_polydisc b) :
    letI : ChartedSpace ℂ C :=
      b6a_sliceChartedSpace b C A (fun q ↦ (hA q).1) hparam t
    letI : IsManifold 𝓘(ℂ, ℂ) ω C := b6a_slice_isManifold b C A hA hparam t
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k := by
  letI : ChartedSpace ℂ C :=
    b6a_sliceChartedSpace b C A (fun q ↦ (hA q).1) hparam t
  letI : IsManifold 𝓘(ℂ, ℂ) ω C := b6a_slice_isManifold b C A hA hparam t
  intro x
  let S' := b6a_sliceChart b C A hparam t (k x)
  let E' := A (t, k x)
  have hinc := b6a_slice_inclusion_contMDiff b C A hA hparam t
  have htot := hKdiff.contMDiffAt.comp x hinc.contMDiffAt
  have hE' : ContMDiffAt 𝓘(ℂ, (Fin 10 → ℂ) × ℂ)
      𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω E' (K (t, x)) := by
    rw [hK]
    exact contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (hA (t, k x)).2) (hA (t, k x)).1
  have hcoord := hE'.comp x htot
  have hvert := (contDiff_snd.contMDiff.contMDiffAt.comp x hcoord)
  have hycoord : E' (t, k x) = (t.val, S' (k x)) :=
    Prod.ext (hparam (t, k x) (t, k x) (hA (t, k x)).1) rfl
  have hS'inv : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω S'.symm
      ((E' (t, k x)).2) := by
    rw [hycoord]
    exact contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (b6a_sliceChart_mem_atlas b C A
        (fun q ↦ (hA q).1) hparam t (k x)))
      (S'.map_source (hA (t, k x)).1)
  have hvpoint : (Prod.snd ∘ E' ∘ K ∘ fun y : C ↦ (t, y)) x =
      (E' (t, k x)).2 := by simp [hK]
  rw [← hvpoint] at hS'inv
  have hc := hS'inv.comp x hvert
  apply hc.congr_of_eventuallyEq
  have hev : ∀ᶠ y in nhds x, K (t, y) ∈ E'.source :=
    (hKdiff.continuous.comp hinc.continuous).continuousAt.preimage_mem_nhds
      (E'.open_source.mem_nhds (by simpa [hK] using (hA (t, k x)).1))
  filter_upwards [hev] with y hy
  have hky : K (t, y) = (t, k y) := hK t y
  have hy' : (t, k y) ∈ E'.source := hky ▸ hy
  have he' : E' (t, k y) = (t.val, S' (k y)) :=
    Prod.ext (hparam (t, k x) (t, k y) hy') rfl
  simpa [Function.comp_def, E', S', hky, he'] using (S'.left_inv hy').symm

end HodgeLean.Foundations.Program
