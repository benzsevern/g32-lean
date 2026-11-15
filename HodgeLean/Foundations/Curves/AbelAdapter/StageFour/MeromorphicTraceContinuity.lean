import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.FiberSumEnumeration
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.FiniteSumNeighborhood

noncomputable section
open HodgeLean.Foundations.Program Filter Set
open scoped Manifold ContDiff Topology
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

/-- Source: Forster, Lectures on Riemann Surfaces, §17, local degree and continuity of fiber sums. -/
theorem meromorphicFiberSum_continuous
    {E C A : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [AddCommGroup A] [TopologicalSpace A] [ContinuousAdd A]
    (h : Module.finrank ℂ E = 1) (f : b4c_MeroFun E C) (hnc : ∃ x y, f x ≠ f y)
    (a : C → A) (ha : Continuous a) : Continuous (meromorphicFiberSum h f hnc a) := by
  classical
  letI := b4cov_sphChartedSpace
  letI := b4cov_sph_isManifold
  apply continuous_iff_continuousAt.mpr
  intro y
  apply continuousAt_def.mpr
  intro O hO
  have hfin := b4_fiber_finite_aux h (by simp : Module.finrank ℂ ℂ = 1) f f.property.1 hnc y
  let I := {x : C // f x = y}
  letI : Fintype I := hfin.fintype
  let p : I → C := Subtype.val
  have hp : ∀ i, f (p i) = y := fun i ↦ i.property
  have hpr : (f : C → OnePoint ℂ) ⁻¹' {y} = range p := by
    ext x
    exact ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, fun ⟨i, hix⟩ ↦ hix ▸ i.property⟩
  let n : I → ℕ := fun i ↦ b4_ramIndex E ℂ f (p i)
  let K := (i : I) × Fin (n i)
  have hsum : meromorphicFiberSum h f hnc a y = ∑ i : I, n i • a (p i) := by
    have hs := weightedFiber_sum_of_weighted_enumeration
      (meromorphicMultiplicity (E := E) f) f y hfin p Subtype.val_injective hpr a
    simpa only [meromorphicFiberSum, meromorphicFiber, meromorphicMultiplicity,
      natCast_zsmul, n] using hs
  have hcopy : (∑ k : K, a (p k.1)) = meromorphicFiberSum h f hnc a y := by
    rw [Fintype.sum_sigma]
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using hsum.symm
  have hO' : O ∈ 𝓝 (∑ k : K, a (p k.1)) := by rw [hcopy]; exact hO
  obtain ⟨V, hV, hVO⟩ := finite_sum_neighborhood (fun k : K ↦ a (p k.1)) O hO'
  let N : I → Set C := fun i ↦ ⋂ j : Fin (n i), a ⁻¹' V ⟨i, j⟩
  have hN : ∀ i, N i ∈ 𝓝 (p i) := by
    intro i
    apply Filter.iInter_mem.mpr
    intro j
    exact ha.continuousAt (hV ⟨i, j⟩)
  obtain ⟨S, hS, hSdisj⟩ := hfin.t2_separation
  choose B hBN hBo hpB W hW hzero hcount using fun i ↦
    b4cov_local_degree h (by simp : Module.finrank ℂ ℂ = 1) f f.property.1 hnc (p i)
      (N i ∩ S (p i)) (Filter.inter_mem (hN i) ((hS (p i)).2.mem_nhds (hS (p i)).1))
  let U : Set C := ⋃ i, B i
  have hUo : IsOpen U := isOpen_iUnion hBo
  have hclosed : IsClosed (f '' Uᶜ) := (hUo.isClosed_compl.isCompact.image f.property.1.continuous).isClosed
  have hyU : y ∉ f '' Uᶜ := by
    rintro ⟨x, hx, hxy⟩
    let i : I := ⟨x, hxy⟩
    exact hx (mem_iUnion.mpr ⟨i, hpB i⟩)
  have havoid : ∀ᶠ z in 𝓝 y, z ∉ f '' Uᶜ := hclosed.isOpen_compl.mem_nhds hyU
  have hWall : ∀ᶠ z in 𝓝 y, ∀ i, z ∈ W i :=
    Filter.eventually_all.mpr (fun i ↦ hp i ▸ hW i)
  filter_upwards [havoid, hWall] with z hz hzw
  change meromorphicFiberSum h f hnc a z ∈ O
  by_cases hzy : z = y
  · exact hzy ▸ mem_of_mem_nhds hO
  have hfinz := b4_fiber_finite_aux h (by simp : Module.finrank ℂ ℂ = 1) f f.property.1 hnc z
  let T : I → Set C := fun i ↦ (f : C → OnePoint ℂ) ⁻¹' {z} ∩ B i
  have hTf : ∀ i, (T i).Finite := fun _ ↦ hfinz.subset inter_subset_left
  letI : ∀ i, Fintype (T i) := fun i ↦ (hTf i).fintype
  have hcard : ∀ i, Fintype.card (T i) = n i := by
    intro i
    have hc := (hcount i z (hzw i) (hp i ▸ hzy)).1
    simpa only [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] using hc
  let e : ∀ i, Fin (n i) ≃ T i := fun i ↦ (Fintype.equivFinOfCardEq (hcard i)).symm
  let v : K → C := fun k ↦ (e k.1 k.2).val
  have hvB : ∀ k, v k ∈ B k.1 := fun k ↦ (e k.1 k.2).property.2
  have hvf : ∀ k, f (v k) = z := fun k ↦ (e k.1 k.2).property.1
  have hv : Function.Injective v := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ heq
    have hii : i = i' := by
      by_contra hne
      have hpp : p i ≠ p i' := fun he ↦ hne (Subtype.ext he)
      have hdS := hSdisj (hp i) (hp i') hpp
      have hleft := (hBN i (hvB ⟨i, j⟩)).2
      have hright := (hBN i' (hvB ⟨i', j'⟩)).2
      exact Set.disjoint_left.mp hdS hleft (heq.symm ▸ hright)
    subst i'
    have hjj : j = j' := (e i).injective (Subtype.ext heq)
    exact congrArg (Sigma.mk i) hjj
  have hvr : (f : C → OnePoint ℂ) ⁻¹' {z} = range v := by
    ext x
    constructor
    · intro hfx
      have hxU : x ∈ U := by
        by_contra hx
        exact hz ⟨x, hx, hfx⟩
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hxU
      let t : T i := ⟨x, hfx, hxi⟩
      exact ⟨⟨i, (e i).symm t⟩, congrArg Subtype.val ((e i).apply_symm_apply t)⟩
    · rintro ⟨k, rfl⟩
      exact hvf k
  have hw : ∀ x, f x = z → meromorphicMultiplicity (E := E) f x = 1 := by
    intro x hfx
    obtain ⟨k, rfl⟩ := hvr ▸ (show x ∈ (f : C → OnePoint ℂ) ⁻¹' {z} from hfx)
    change (b4_ramIndex E ℂ f (v k) : ℤ) = 1
    rw [(hcount k.1 z (hzw k.1) (hp k.1 ▸ hzy)).2 (v k) (hvB k) (hvf k)]
    rfl
  have htrace : meromorphicFiberSum h f hnc a z = ∑ k : K, a (v k) :=
    weightedFiber_sum_of_enumeration (meromorphicMultiplicity (E := E) f) f z hfinz v hv hvr hw a
  rw [htrace]
  apply hVO
  intro k
  exact mem_iInter.mp (hBN k.1 (hvB k)).1 k.2

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
