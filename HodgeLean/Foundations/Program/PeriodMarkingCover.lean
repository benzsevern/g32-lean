import HodgeLean.Foundations.Program.PeriodMarkingMonodromy
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cCover
import HodgeLean.Foundations.Program.HurwitzPrymCovConnected

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b64b_galois_finite_fibres {G Y : Type*} {C : Type} [Group G] [Finite G] [MulAction G C]
    (f : C → Y) (hgal : b4_IsGaloisCover G f) (y : Y) : (f ⁻¹' {y}).Finite := by
  classical
  by_cases h : ∃ x, f x = y
  · obtain ⟨x, hx⟩ := h
    apply (Set.finite_range (fun g : G => g • x)).subset
    intro z hz
    obtain ⟨g, hg⟩ := hgal.2 x z (hx.trans hz.symm)
    exact ⟨g, hg⟩
  · have he : f ⁻¹' {y} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact h ⟨x, hx⟩
    rw [he]
    exact Set.finite_empty

theorem b64b_galois_punctured_connected {G Y U : Type*} {C : Type}
    [Group G] [Finite G] [MulAction G C]
    [TopologicalSpace C] [ChartedSpace ℂ C] [T1Space C] [ConnectedSpace C]
    [TopologicalSpace U] (u : U)
    (f : C → Y) (hgal : b4_IsGaloisCover G f) (S : Set Y) (hS : S.Finite)
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hrange : Set.range ι = f ⁻¹' Sᶜ) : ConnectedSpace U := by
  have hfin : (Set.range ι)ᶜ.Finite := by
    rw [hrange, Set.preimage_compl, compl_compl]
    exact hS.preimage' (fun y _ => b64b_galois_finite_fibres f hgal y)
  have hp : IsPreconnected (Set.range ι) := by
    have h := b4cov_isPreconnected_diff_finite isOpen_univ
      (isPreconnected_univ : IsPreconnected (Set.univ : Set C)) hfin
      (fun x _ => b4cov_goodPoint (E := ℂ) (by simp) x)
    simpa only [← Set.compl_eq_univ_sdiff, compl_compl] using h
  have hpU : IsPreconnected (Set.univ : Set U) := by
    rw [← hι.isEmbedding.isInducing.isPreconnected_image, Set.image_univ]
    exact hp
  exact { isPreconnected_univ := hpU, toNonempty := ⟨u⟩ }

end HodgeLean.Foundations.Program
