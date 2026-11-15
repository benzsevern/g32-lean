import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cFilling

noncomputable section

namespace HodgeLean.Foundations.Program

open Filter Topology Set
open scoped Topology

theorem b6m_connected_filter_finite_cluster {Y : Type} [TopologicalSpace Y]
    [CompactSpace Y] [T2Space Y] (F : Filter Y) [F.NeBot]
    (hconn : ∀ V ∈ F, ∃ S ∈ F, IsPreconnected S ∧ S ⊆ V)
    (hfin : {y | ClusterPt y F}.Finite) : ∃ y, F ≤ 𝓝 y := by
  obtain ⟨y, hy⟩ := exists_clusterPt_of_compactSpace F
  refine ⟨y, le_nhds_of_unique_clusterPt ?_⟩
  intro z hz
  by_contra hzy
  obtain ⟨V, W, hV, hW, hyV, hrestW, hVW⟩ :=
    normal_separation (isClosed_singleton : IsClosed ({y} : Set Y))
      hfin.sdiff.isClosed
      (by simp : Disjoint ({y} : Set Y) ({q | ClusterPt q F} \ {y}))
  have hcover : {q | ClusterPt q F} ⊆ V ∪ W := by
    intro q hq
    by_cases hqy : q = y
    · exact Or.inl (hyV (by simpa [hqy]))
    · exact Or.inr (hrestW ⟨hq, hqy⟩)
  have hmem : V ∪ W ∈ F :=
    (isCompact_univ.le_nhdsSet_of_clusterPt (s' := {q | ClusterPt q F})
      univ_mem (fun _ _ h ↦ h)) ((hV.union hW).mem_nhdsSet.mpr hcover)
  obtain ⟨S, hS, hSc, hSVW⟩ := hconn _ hmem
  obtain ⟨v, hvV, hvS⟩ := clusterPt_iff_nonempty.mp hy
    (hV.mem_nhds (hyV (mem_singleton y))) hS
  obtain ⟨w, hwW, hwS⟩ := clusterPt_iff_nonempty.mp hz
    (hW.mem_nhds (hrestW ⟨hz, hzy⟩)) hS
  exact Set.disjoint_left.mp hVW
    (hSc.subset_left_of_subset_union hV hW hVW hSVW ⟨v, hvS, hvV⟩ hwS) hwW

theorem b6m_connected_filter_finite_fibre {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [CompactSpace Y] [T2Space Y]
    (F : Filter Y) [F.NeBot]
    (hconn : ∀ V ∈ F, ∃ S ∈ F, IsPreconnected S ∧ S ⊆ V)
    (k : Y → X) (hk : Continuous k) (x : X) (hfin : (k ⁻¹' {x}).Finite)
    (ht : Tendsto k F (𝓝 x)) : ∃ y, k y = x ∧ F ≤ 𝓝 y := by
  have hcluster : ∀ y, ClusterPt y F → k y = x := by
    intro y hy
    exact eq_of_nhds_neBot (hy.map hk.continuousAt ht)
  have hfinite : {y | ClusterPt y F}.Finite := hfin.subset (fun y hy ↦ hcluster y hy)
  obtain ⟨y, hy⟩ := b6m_connected_filter_finite_cluster F hconn hfinite
  exact ⟨y, hcluster y (ClusterPt.of_le_nhds hy), hy⟩

theorem b6m_puncture_connected_filter {U C : Type} [TopologicalSpace U]
    [TopologicalSpace C] [T1Space C] (ι : U → C) (hi : IsOpenEmbedding ι)
    (hfin : (range ι)ᶜ.Finite) (x : C) (hx : x ∉ range ι)
    (hgood : b4cov_GoodPoint x) :
    ∀ V ∈ comap ι (𝓝 x), ∃ S ∈ comap ι (𝓝 x), IsPreconnected S ∧ S ⊆ V := by
  intro V hV
  obtain ⟨N, hN, hNV⟩ := mem_comap.mp hV
  have havoid : ((range ι)ᶜ \ {x})ᶜ ∈ 𝓝 x :=
    hfin.sdiff.isClosed.isOpen_compl.mem_nhds (by simp)
  obtain ⟨T, hTN, hTo, hxT, hTc, _⟩ := hgood _ (inter_mem hN havoid)
  have hTr : T \ {x} ⊆ range ι := by
    intro y hy
    by_contra hyr
    exact (hTN hy.1).2 ⟨hyr, hy.2⟩
  refine ⟨ι ⁻¹' (T \ {x}), ?_,
    hTc.preimage_of_isOpenMap hi.injective hi.isOpenMap hTr, ?_⟩
  · apply mem_comap.mpr
    refine ⟨T, hTo.mem_nhds hxT, ?_⟩
    intro u hu
    refine ⟨hu, ?_⟩
    intro heq
    exact hx ⟨u, heq⟩
  · intro u hu
    exact hNV (hTN hu.1).1

theorem b6m_puncture_map_limit {U C D X : Type}
    [TopologicalSpace U] [TopologicalSpace C] [TopologicalSpace D] [TopologicalSpace X]
    [T1Space C] [CompactSpace D] [T2Space D] [T2Space X]
    (ι : U → C) (hi : IsOpenEmbedding ι) (hdense : DenseRange ι)
    (hfin : (range ι)ᶜ.Finite) (j : U → D) (hj : Continuous j)
    (f : C → X) (hf : Continuous f) (k : D → X) (hk : Continuous k)
    (hp : ∀ u, k (j u) = f (ι u))
    (x : C) (hx : x ∉ range ι) (hgood : b4cov_GoodPoint x)
    (hkfin : (k ⁻¹' {f x}).Finite) :
    ∃ y, k y = f x ∧ Tendsto j (comap ι (𝓝 x)) (𝓝 y) := by
  have hdi : IsDenseInducing ι := ⟨hi.isEmbedding.isInducing, hdense⟩
  haveI := hdi.comap_nhds_neBot x
  have hconn := b6m_puncture_connected_filter ι hi hfin x hx hgood
  refine b6m_connected_filter_finite_fibre (map j (comap ι (𝓝 x))) ?_ k hk (f x) hkfin ?_
  · intro V hV
    obtain ⟨S, hS, hSc, hSV⟩ := hconn (j ⁻¹' V) hV
    exact ⟨j '' S, image_mem_map hS, hSc.image j hj.continuousOn,
      image_subset_iff.mpr hSV⟩
  · rw [tendsto_map'_iff]
    have heq : k ∘ j = f ∘ ι := funext hp
    rw [heq]
    exact hf.continuousAt.tendsto.comp tendsto_comap

theorem b6m_continuous_filling_extension {U C D X : Type}
    [TopologicalSpace U] [TopologicalSpace C] [TopologicalSpace D] [TopologicalSpace X]
    [T1Space C] [CompactSpace D] [T2Space D] [T2Space X]
    (ι : U → C) (hi : IsOpenEmbedding ι) (hdense : DenseRange ι)
    (hfin : (range ι)ᶜ.Finite) (hgood : ∀ x : C, b4cov_GoodPoint x)
    (j : U → D) (hj : Continuous j)
    (f : C → X) (hf : Continuous f) (k : D → X) (hk : Continuous k)
    (hp : ∀ u, k (j u) = f (ι u)) (hkfin : ∀ x, (k ⁻¹' {x}).Finite) :
    ∃ e : C(C, D), (∀ u, e (ι u) = j u) ∧ ∀ x, k (e x) = f x := by
  have hdi : IsDenseInducing ι := ⟨hi.isEmbedding.isInducing, hdense⟩
  have hlim : ∀ x, ∃ y, Tendsto j (comap ι (𝓝 x)) (𝓝 y) := by
    intro x
    by_cases hx : x ∈ range ι
    · obtain ⟨u, rfl⟩ := hx
      refine ⟨j u, ?_⟩
      rw [← hdi.nhds_eq_comap]
      exact hj.continuousAt
    · obtain ⟨y, _, hy⟩ := b6m_puncture_map_limit ι hi hdense hfin j hj f hf k hk hp
        x hx (hgood x) (hkfin (f x))
      exact ⟨y, hy⟩
  let e : C(C, D) := ⟨hdi.extend j, hdi.continuous_extend hlim⟩
  have hei : ∀ u, e (ι u) = j u := hdi.extend_eq hj
  refine ⟨e, hei, ?_⟩
  have heq : k ∘ e = f := hdense.equalizer (hk.comp e.continuous) hf (by
    funext u
    exact (congrArg k (hei u)).trans (hp u))
  exact congrFun heq

theorem b6m_topological_filling_comparison {U C D X : Type}
    [TopologicalSpace U] [TopologicalSpace C] [TopologicalSpace D] [TopologicalSpace X]
    [CompactSpace C] [T2Space C] [CompactSpace D] [T2Space D] [T2Space X]
    (ι : U → C) (hi : IsOpenEmbedding ι) (hidense : DenseRange ι)
    (hifin : (range ι)ᶜ.Finite) (hC : ∀ x : C, b4cov_GoodPoint x)
    (j : U → D) (hj : IsOpenEmbedding j) (hjdense : DenseRange j)
    (hjfin : (range j)ᶜ.Finite) (hD : ∀ x : D, b4cov_GoodPoint x)
    (f : C → X) (hf : Continuous f) (k : D → X) (hk : Continuous k)
    (hp : ∀ u, k (j u) = f (ι u))
    (hffin : ∀ x, (f ⁻¹' {x}).Finite) (hkfin : ∀ x, (k ⁻¹' {x}).Finite) :
    ∃ e : C ≃ₜ D, (∀ u, e (ι u) = j u) ∧ (∀ x, k (e x) = f x) ∧
      ∀ e' : C(C, D), (∀ u, e' (ι u) = j u) → ∀ x, e' x = e x := by
  obtain ⟨a, hai, hak⟩ := b6m_continuous_filling_extension
    ι hi hidense hifin hC j hj.continuous f hf k hk hp hkfin
  obtain ⟨c, hcj, hcf⟩ := b6m_continuous_filling_extension
    j hj hjdense hjfin hD ι hi.continuous k hk f hf (fun u ↦ (hp u).symm) hffin
  have hca : ∀ x, c (a x) = x := by
    have h := hidense.equalizer (c.continuous.comp a.continuous) continuous_id (by
      funext u
      change c (a (ι u)) = ι u
      rw [hai, hcj])
    exact congrFun h
  have hac : ∀ x, a (c x) = x := by
    have h := hjdense.equalizer (a.continuous.comp c.continuous) continuous_id (by
      funext u
      change a (c (j u)) = j u
      rw [hcj, hai])
    exact congrFun h
  let e : C ≃ₜ D :=
    { toFun := a
      invFun := c
      left_inv := hca
      right_inv := hac
      continuous_toFun := a.continuous
      continuous_invFun := c.continuous }
  refine ⟨e, hai, hak, ?_⟩
  intro e' he'
  exact congrFun (hidense.equalizer e'.continuous a.continuous (by
    funext u
    exact (he' u).trans (hai u).symm))

end HodgeLean.Foundations.Program
