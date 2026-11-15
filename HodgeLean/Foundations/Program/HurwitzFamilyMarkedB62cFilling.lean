import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cCover

noncomputable section

namespace HodgeLean.Foundations.Program

open Filter Topology Manifold
open scoped Topology Manifold ContDiff
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b6m_filling_nonconstant {X U C : Type} [Infinite X]
    (B : Set X) (hB : B.Finite) (π : U → ↥(Bᶜ)) (hπ : Function.Surjective π)
    (f : C → X) (ι : U → C) (hp : ∀ u, f (ι u) = π u) :
    ∃ c d, f c ≠ f d := by
  obtain ⟨y, hy⟩ := hB.infinite_compl.nonempty
  obtain ⟨z, hz, hzy⟩ := hB.infinite_compl.exists_notMem_finite (Set.finite_singleton y)
  obtain ⟨uy, huy⟩ := hπ ⟨y, hy⟩
  obtain ⟨uz, huz⟩ := hπ ⟨z, hz⟩
  refine ⟨ι uy, ι uz, ?_⟩
  rw [hp, hp]
  intro h
  have heq : (⟨y, hy⟩ : ↥(Bᶜ)) = ⟨z, hz⟩ :=
    huy.symm.trans ((Subtype.ext h).trans huz)
  exact hzy (by simpa using (congrArg Subtype.val heq).symm)

theorem b6m_filling_denseRange {C U : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (B : Set (OnePoint ℂ)) (hB : B.Finite)
    (π : U → ↥(Bᶜ)) (hπ : Function.Surjective π)
    (f : C → OnePoint ℂ) (ι : U → C)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hr : Set.range ι = f ⁻¹' Bᶜ) (hp : ∀ u, f (ι u) = π u) :
    DenseRange ι := by
  have hnc := b6m_filling_nonconstant B hB π hπ f ι hp
  haveI : Nontrivial C := by
    obtain ⟨c, d, hcd⟩ := hnc
    exact ⟨c, d, fun h ↦ hcd (congrArg f h)⟩
  have hfin : (f ⁻¹' B).Finite :=
    hB.preimage' fun y _ ↦ b4_fiber_finite (E := ℂ) (E' := ℂ)
      (by simp) (by simp) f hf hnc y
  change Dense (Set.range ι)
  rw [hr, Set.preimage_compl]
  simpa only [Set.sdiff_eq, Set.univ_inter] using dense_univ.sdiff_finite hfin

theorem b6m_lift_into_embedding {U W D : Type}
    [TopologicalSpace U] [TopologicalSpace W] [TopologicalSpace D]
    (j : W → D) (hj : IsEmbedding j) (a : U → D) (ha : Continuous a)
    (hr : ∀ u, a u ∈ Set.range j) :
    ∃ c : C(U, W), ∀ u, j (c u) = a u := by
  classical
  choose c hc using hr
  refine ⟨⟨c, hj.continuous_iff.mpr ?_⟩, hc⟩
  have he : j ∘ c = a := funext hc
  rw [he]
  exact ha

theorem b6m_filling_maps_eq {X U W C D : Type}
    [TopologicalSpace X] [TopologicalSpace U] [TopologicalSpace W]
    [TopologicalSpace C] [TopologicalSpace D] [PreconnectedSpace U] [T2Space D]
    (B : Set X) (π : U → ↥(Bᶜ)) (ρ : W → ↥(Bᶜ)) (hρ : IsCoveringMap ρ)
    (f : C → X) (k : D → X) (ι : U → C) (j : W → D)
    (hi : Continuous ι) (hdense : DenseRange ι) (hj : IsEmbedding j)
    (hrj : Set.range j = k ⁻¹' Bᶜ)
    (hpi : ∀ u, f (ι u) = π u) (hpj : ∀ w, k (j w) = ρ w)
    (e e' : C(C, D)) (he : ∀ x, k (e x) = f x) (he' : ∀ x, k (e' x) = f x)
    (u : U) (hu : e (ι u) = e' (ι u)) : e = e' := by
  have hr (a : C(C, D)) (ha : ∀ x, k (a x) = f x) :
      ∀ z, a (ι z) ∈ Set.range j := by
    intro z
    rw [hrj]
    change k (a (ι z)) ∈ Bᶜ
    rw [ha, hpi]
    exact (π z).property
  obtain ⟨a, ha⟩ := b6m_lift_into_embedding j hj (e ∘ ι) (e.continuous.comp hi) (hr e he)
  obtain ⟨a', ha'⟩ := b6m_lift_into_embedding j hj (e' ∘ ι) (e'.continuous.comp hi) (hr e' he')
  have hpa : ∀ z, ρ (a z) = π z := by
    intro z
    apply Subtype.ext
    rw [← hpj, ha]
    exact (he (ι z)).trans (hpi z)
  have hpa' : ∀ z, ρ (a' z) = π z := by
    intro z
    apply Subtype.ext
    rw [← hpj, ha']
    exact (he' (ι z)).trans (hpi z)
  have hsame := hρ.eq_of_comp_eq a.continuous a'.continuous
    (by funext z; exact (hpa z).trans (hpa' z).symm)
    u (hj.injective ((ha u).trans (hu.trans (ha' u).symm)))
  apply DFunLike.ext'
  apply hdense.equalizer e.continuous e'.continuous
  funext z
  exact (ha z).symm.trans ((congrArg j (congrFun hsame z)).trans (ha' z))

end HodgeLean.Foundations.Program
