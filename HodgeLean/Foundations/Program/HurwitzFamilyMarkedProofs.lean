import HodgeLean.Foundations.Program.HurwitzFamilyMarkedDefs
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cFilling
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cHolomorphic
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cIntersection
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cPeriodTransport
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cRadial
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cRealLoops
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSphere
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cRegular
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cFlatPaths
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSegments
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cMatchedLoops
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cGeneric
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cMatchedTransverse
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSurfaceLifting

/-! # B6-2c: proof obligations for marked filling and integral transport -/

noncomputable section
open Manifold CategoryTheory AlgebraicTopology.Singular
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b6m_marked_rex_aux (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G : Type) [Group G] [Finite G] (x₀ : b6t_punctured b)
    (φ : FundamentalGroup (b6t_punctured b) x₀ →* Gᵐᵒᵖ)
    (hφ : Function.Surjective φ) :
    ∃ (U : Type) (_ : TopologicalSpace U) (_ : MulAction G U)
      (_ : ConnectedSpace U) (π : U → b6t_punctured b)
      (hπ : IsQuotientCoveringMap π G) (u₀ : π ⁻¹' {x₀}),
      hπ.fundamentalGroupToMulOpposite u₀ = φ ∧
      ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace ℂ C)
        (_ : IsManifold 𝓘(ℂ, ℂ) ω C) (_ : T2Space C) (_ : CompactSpace C)
        (_ : ConnectedSpace C) (_ : MulAction G C) (f : C → OnePoint ℂ) (ι : U → C),
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f ∧ b4_IsGaloisCover G f ∧
        Function.Surjective f ∧
        (∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) ∧
        Topology.IsOpenEmbedding ι ∧ Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ ∧
        (∀ u, f (ι u) = π u) ∧ (∀ (g : G) (u : U), ι (g • u) = g • ι u) := by
  let B : Set (OnePoint ℂ) := Set.range (b6_branch b)
  have hB : B.Finite := Set.finite_range _
  obtain ⟨U, instTop, instAction, π, hπ, instConnected, u₀, hu₀⟩ :=
    b4_exists_galoisCovering (E' := ℂ) (Y := OnePoint ℂ) (by simp) B hB x₀ φ hφ
  letI : TopologicalSpace U := instTop
  letI : MulAction G U := instAction
  letI : ConnectedSpace U := instConnected
  obtain ⟨C, instCTop, instChart, instMan, instT2, instCompact, instCConnected,
      instNonempty, instCAction, f, ι, haction, hf, hgal, hι, hirange, hιf, hιG⟩ :=
    b4_extend_galoisCovering (E := ℂ) (E' := ℂ) (Y := OnePoint ℂ) (by simp)
      (by simp) B hB π hπ
  letI : TopologicalSpace C := instCTop
  letI : ChartedSpace ℂ C := instChart
  letI : IsManifold (modelWithCornersSelf ℂ ℂ) ω C := instMan
  letI : T2Space C := instT2
  letI : CompactSpace C := instCompact
  letI : ConnectedSpace C := instCConnected
  letI : MulAction G C := instCAction
  have hInf : Bᶜ.Infinite := hB.infinite_compl
  obtain ⟨y, hy⟩ := hInf.nonempty
  obtain ⟨z, hz, hzy⟩ := hInf.exists_notMem_finite (Set.finite_singleton y)
  obtain ⟨uy, huy⟩ := hπ.surjective ⟨y, hy⟩
  obtain ⟨uz, huz⟩ := hπ.surjective ⟨z, hz⟩
  have hnc : ∃ c d, f c ≠ f d := by
    refine ⟨ι uy, ι uz, ?_⟩
    rw [hιf, hιf]
    intro h
    have hsub : π uy = π uz := Subtype.ext h
    have heq : (⟨y, hy⟩ : {q : OnePoint ℂ // q ∈ Bᶜ}) = ⟨z, hz⟩ :=
      huy.symm.trans (hsub.trans huz)
    exact hzy (by simpa using (congrArg Subtype.val heq).symm)
  have hsurj : Function.Surjective f :=
    b4_surjective (E := ℂ) (E' := ℂ) (by simp) (by simp) f hf hnc
  refine ⟨U, instTop, instAction, instConnected, π, hπ, u₀, hu₀, C, instCTop,
    instChart, instMan, instT2, instCompact, instCConnected, instCAction, f, ι, hf,
    hgal, hsurj, haction, hι, ?_, hιf, hιG⟩
  simpa [B] using hirange

theorem b6m_filling_unique_aux (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G : Type) [Group G] [Finite G] (U : Type) [TopologicalSpace U]
    [MulAction G U] [ConnectedSpace U] (π : U → b6t_punctured b)
    (hπ : IsQuotientCoveringMap π G)
    (C D : Type) [TopologicalSpace C] [TopologicalSpace D]
    [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [T2Space C] [T2Space D] [CompactSpace C] [CompactSpace D]
    [ConnectedSpace C] [ConnectedSpace D] [MulAction G C] [MulAction G D]
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ) (ι : U → C) (j : U → D)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (hι : Topology.IsOpenEmbedding ι) (hj : Topology.IsOpenEmbedding j)
    (hrι : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ)
    (hrj : Set.range j = k ⁻¹' (Set.range (b6_branch b))ᶜ)
    (hpι : ∀ u, f (ι u) = π u) (hpj : ∀ u, k (j u) = π u)
    (heι : ∀ (g : G) (u : U), ι (g • u) = g • ι u)
    (hej : ∀ (g : G) (u : U), j (g • u) = g • j u)
    (haC : ∀ g : G, Continuous (fun x : C ↦ g • x))
    (haD : ∀ g : G, Continuous (fun x : D ↦ g • x)) :
    ∃ e : C ≃ₜ D,
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e ∧
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e.symm ∧
      (∀ u, e (ι u) = j u) ∧ (∀ x, k (e x) = f x) ∧
      (∀ (g : G) (x : C), e (g • x) = g • e x) ∧
      ∀ e' : C ≃ₜ D, (∀ u, e' (ι u) = j u) → e' = e := by
  let B : Set (OnePoint ℂ) := Set.range (b6_branch b)
  have hB : B.Finite := Set.finite_range _
  have hfnc := b6m_filling_nonconstant B hB π hπ.surjective f ι hpι
  have hknc := b6m_filling_nonconstant B hB π hπ.surjective k j hpj
  have hff : ∀ y, (f ⁻¹' {y}).Finite :=
    b4_fiber_finite (E := ℂ) (E' := ℂ) (by simp) (by simp) f hf hfnc
  have hkf : ∀ y, (k ⁻¹' {y}).Finite :=
    b4_fiber_finite (E := ℂ) (E' := ℂ) (by simp) (by simp) k hk hknc
  have hidense := b6m_filling_denseRange B hB π hπ.surjective f ι hf hrι hpι
  have hjdense := b6m_filling_denseRange B hB π hπ.surjective k j hk hrj hpj
  have hifin : (Set.range ι)ᶜ.Finite := by
    rw [hrι, ← Set.preimage_compl, compl_compl]
    exact hB.preimage' (fun y _ ↦ hff y)
  have hjfin : (Set.range j)ᶜ.Finite := by
    rw [hrj, ← Set.preimage_compl, compl_compl]
    exact hB.preimage' (fun y _ ↦ hkf y)
  obtain ⟨e, hei, hek, huniq⟩ := b6m_topological_filling_comparison
    ι hι hidense hifin (b4cov_goodPoint (E := ℂ) (by simp))
    j hj hjdense hjfin (b4cov_goodPoint (E := ℂ) (by simp))
    f hf.continuous k hk.continuous (fun u ↦ (hpj u).trans (hpι u).symm) hff hkf
  have hehol := b6m_contMDiff_of_injective_comp e e.continuous e.injective
    f k hf hk hknc hek
  have heihol := b6m_contMDiff_of_injective_comp e.symm e.symm.continuous e.symm.injective
    k f hk hf hfnc (fun y ↦ by simpa only [e.apply_symm_apply] using (hek (e.symm y)).symm)
  refine ⟨e, hehol, heihol, hei, hek, ?_, ?_⟩
  · intro g
    have h := hidense.equalizer (e.continuous.comp (haC g))
      ((haD g).comp e.continuous) (by
        funext u
        change e (g • ι u) = g • e (ι u)
        rw [← heι, hei, hej, hei])
    exact congrFun h
  · intro e' he'
    ext x
    exact huniq ⟨e', e'.continuous⟩ he' x

theorem b6m_fibre_marking_aux (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b)
    (G : Type) [Group G] [Finite G] (U : Type) [TopologicalSpace U]
    [MulAction G U] [ConnectedSpace U] (π : U → b6t_punctured b)
    (hπ : IsQuotientCoveringMap π G) (x₀ : b6t_punctured b) (u₀ : π ⁻¹' {x₀})
    (hx₀ : (x₀ : OnePoint ℂ) ∉ ⋃ i : Fin 10,
      ((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall (b i) (b6t_radius b))
    (γ : Fin 13 → FundamentalGroup (b6t_punctured b) x₀)
    (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C]
    [ConnectedSpace C] [MulAction G C] (f : C → OnePoint ℂ) (ι : U → C)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (ha : ∀ g : G, Continuous (fun x : C ↦ g • x))
    (hι : Topology.IsOpenEmbedding ι)
    (hr : Set.range ι = f ⁻¹' (Set.range (b6_branch t))ᶜ)
    (hp : ∀ u, f (ι u) = b6t_projection b t π u)
    (he : ∀ (g : G) (u : U), ι (g • u) = g • ι u) :
    b4_IsGaloisCover G f ∧ Function.Surjective f ∧
    ∃ e : b6t_punctured b ≃ₜ b6t_punctured t,
      (∀ x, (e x : OnePoint ℂ) = b6t_sphere b t x) ∧
      (e x₀ : OnePoint ℂ) = x₀ ∧
      ((hπ.homeomorph_comp e).fundamentalGroupToMulOpposite
        ⟨u₀.val, congrArg e u₀.property⟩).comp
        (FundamentalGroup.map ⟨e, e.continuous⟩ x₀) =
        hπ.fundamentalGroupToMulOpposite u₀ ∧
      (∀ i, (hπ.homeomorph_comp e).fundamentalGroupToMulOpposite
        ⟨u₀.val, congrArg e u₀.property⟩
        (FundamentalGroup.map ⟨e, e.continuous⟩ x₀ (γ i)) =
          hπ.fundamentalGroupToMulOpposite u₀ (γ i)) ∧
      ∃ (D : Type) (_ : TopologicalSpace D) (_ : ChartedSpace ℂ D)
        (_ : IsManifold 𝓘(ℂ, ℂ) ω D) (_ : T2Space D) (_ : CompactSpace D)
        (_ : ConnectedSpace D) (_ : MulAction G D) (k : D → OnePoint ℂ) (j : U → D),
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k ∧ b4_IsGaloisCover G k ∧
        Function.Surjective k ∧
        (∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : D ↦ g • x)) ∧
        Topology.IsOpenEmbedding j ∧ Set.range j = k ⁻¹' (Set.range (b6_branch t))ᶜ ∧
        (∀ u, k (j u) = e (π u)) ∧ (∀ (g : G) (u : U), j (g • u) = g • j u) ∧
        ∃ E : C ≃ₜ D, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω E ∧
          ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω E.symm ∧
          (∀ u, E (ι u) = j u) ∧ (∀ x, k (E x) = f x) ∧
          (∀ (g : G) (x : C), E (g • x) = g • E x) := by
  obtain ⟨e, hes, hex, hm⟩ := b6t_monodromy b hb t ht G U π hπ x₀ u₀ hx₀
  let p : U → b6t_punctured t := e ∘ π
  have hpc : IsQuotientCoveringMap p G := hπ.homeomorph_comp e
  have hpi : ∀ u, f (ι u) = p u := by
    intro u
    rw [hp]
    exact (hes (π u)).symm
  obtain ⟨D, instTop, instChart, instMan, instT2, instCompact, instConnected,
      instNonempty, instAction, k, j, haction, hk, hgal, hj, hrj, hpj, hej⟩ :=
    b4_extend_galoisCovering (E := ℂ) (E' := ℂ) (Y := OnePoint ℂ)
      (by simp) (by simp) (Set.range (b6_branch t)) (Set.finite_range _) p hpc
  letI : TopologicalSpace D := instTop
  letI : ChartedSpace ℂ D := instChart
  letI : IsManifold 𝓘(ℂ, ℂ) ω D := instMan
  letI : T2Space D := instT2
  letI : CompactSpace D := instCompact
  letI : ConnectedSpace D := instConnected
  letI : MulAction G D := instAction
  have hnc := b6m_filling_nonconstant (Set.range (b6_branch t)) (Set.finite_range _)
    p hpc.surjective k j hpj
  have hks : Function.Surjective k :=
    b4_surjective (E := ℂ) (E' := ℂ) (by simp) (by simp) k hk hnc
  obtain ⟨E, hE, hEi, hEj, hEk, hEg, _⟩ :=
    b6m_filling_unique_aux t ((b6t_polydisc_neighbourhood b hb).2.2.2 ht)
      G U p hpc C D f k ι j hf hk hι hj hr hrj hpi hpj he hej ha
      (fun g ↦ (haction g).continuous)
  have hfg : b4_IsGaloisCover G f := by
    constructor
    · intro g x
      rw [← hEk, hEg, hgal.1, hEk]
    · intro x y hxy
      obtain ⟨g, hg⟩ := hgal.2 (E x) (E y) (by rw [hEk, hEk, hxy])
      exact ⟨g, E.injective ((hEg g x).trans hg)⟩
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨d, hd⟩ := hks y
    refine ⟨E.symm d, ?_⟩
    rw [← hEk, E.apply_symm_apply, hd]
  refine ⟨hfg, hfs, e, hes, hex, hm, ?_, D, instTop, instChart, instMan,
    instT2, instCompact, instConnected, instAction, k, j, hk, hgal, hks, haction,
    hj, hrj, hpj, hej, E, hE, hEi, hEj, hEk, hEg⟩
  intro i
  exact DFunLike.congr_fun hm (γ i)

theorem b6m_based_filling_comparison_aux (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G : Type) [Group G] [Finite G] (U W : Type)
    [TopologicalSpace U] [TopologicalSpace W] [MulAction G U] [MulAction G W]
    [ConnectedSpace U] [ConnectedSpace W]
    (π : U → b6t_punctured b) (ρ : W → b6t_punctured b)
    (hπ : IsQuotientCoveringMap π G) (hρ : IsQuotientCoveringMap ρ G)
    (x₀ : b6t_punctured b) (u₀ : π ⁻¹' {x₀}) (w₀ : ρ ⁻¹' {x₀})
    (hmono : hπ.fundamentalGroupToMulOpposite u₀ = hρ.fundamentalGroupToMulOpposite w₀)
    (C D : Type) [TopologicalSpace C] [TopologicalSpace D]
    [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [T2Space C] [T2Space D] [CompactSpace C] [CompactSpace D]
    [ConnectedSpace C] [ConnectedSpace D] [MulAction G C] [MulAction G D]
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ) (ι : U → C) (j : W → D)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (hι : Topology.IsOpenEmbedding ι) (hj : Topology.IsOpenEmbedding j)
    (hrι : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ)
    (hrj : Set.range j = k ⁻¹' (Set.range (b6_branch b))ᶜ)
    (hpι : ∀ u, f (ι u) = π u) (hpj : ∀ w, k (j w) = ρ w)
    (heι : ∀ (g : G) (u : U), ι (g • u) = g • ι u)
    (hej : ∀ (g : G) (w : W), j (g • w) = g • j w)
    (haC : ∀ g : G, Continuous (fun x : C ↦ g • x))
    (haD : ∀ g : G, Continuous (fun x : D ↦ g • x)) :
    ∃ a : U ≃ₜ W, a u₀.val = w₀.val ∧
      (∀ u, ρ (a u) = π u) ∧ (∀ (g : G) (u : U), a (g • u) = g • a u) ∧
      ∃ e : C ≃ₜ D,
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e ∧
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e.symm ∧
        (∀ u, e (ι u) = j (a u)) ∧ (∀ x, k (e x) = f x) ∧
        (∀ (g : G) (x : C), e (g • x) = g • e x) ∧
        e (ι u₀.val) = j w₀.val ∧
        ∀ e' : C ≃ₜ D, (∀ x, k (e' x) = f x) →
          e' (ι u₀.val) = j w₀.val → e' = e := by
  obtain ⟨a, hau, hap, hag, _⟩ := b6m_punctured_based_comparison b hπ hρ u₀ w₀ hmono
  have hja : Topology.IsOpenEmbedding (j ∘ a) := hj.comp a.isOpenEmbedding
  have hrja : Set.range (j ∘ a) = k ⁻¹' (Set.range (b6_branch b))ᶜ := by
    rw [Set.range_comp, a.surjective.range_eq, Set.image_univ, hrj]
  have hpja : ∀ u, k ((j ∘ a) u) = π u := by
    intro u
    exact (hpj (a u)).trans (congrArg Subtype.val (hap u))
  have heja : ∀ (g : G) (u : U), (j ∘ a) (g • u) = g • (j ∘ a) u := by
    intro g u
    change j (a (g • u)) = g • j (a u)
    rw [hag, hej]
  obtain ⟨e, he, hei, heja', hek, heg, _⟩ :=
    b6m_filling_unique_aux b hb G U π hπ C D f k ι (j ∘ a) hf hk hι hja
      hrι hrja hpι hpja heι heja haC haD
  have heb : e (ι u₀.val) = j w₀.val := (heja' u₀.val).trans (congrArg j hau)
  refine ⟨a, hau, hap, hag, e, he, hei, heja', hek, heg, heb, ?_⟩
  intro e' he' he'b
  have hdense := b6m_filling_denseRange (Set.range (b6_branch b)) (Set.finite_range _)
    π hπ.surjective f ι hf hrι hpι
  have heq := b6m_filling_maps_eq (Set.range (b6_branch b)) π ρ hρ.isCoveringMap
    f k ι j hι.continuous hdense hj.isEmbedding hrj hpι hpj
    ⟨e', e'.continuous⟩ ⟨e, e.continuous⟩ he' hek u₀.val (he'b.trans heb.symm)
  ext x
  exact DFunLike.congr_fun heq x

theorem b6m_filled_transport_aux (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (C : Type) [TopologicalSpace C] (f : C → OnePoint ℂ)
    (U : Type) (π : U → b6t_punctured b) (ι : U → C)
    (hp : ∀ u, f (ι u) = π u)
    (s t : b6t_polydisc b) :
    (∀ u, b6m_transport b C s t ⟨(s, ι u), rfl⟩ = ⟨(t, ι u), rfl⟩) ∧
    (∀ u, b6a_map b f (b6m_transport b C s t ⟨(s, ι u), rfl⟩).val =
      b6t_projection b t.val π u) ∧
    (∃ e : OnePoint ℂ ≃ₜ OnePoint ℂ,
      (∀ z, e z = b6t_sphere b t.val z) ∧
      ∀ x : b6m_Fibre b C ⟨b, (b6t_polydisc_neighbourhood b hb).1⟩,
        b6a_map b f (b6m_transport b C ⟨b, (b6t_polydisc_neighbourhood b hb).1⟩ t x).val =
          e (b6a_map b f x.val)) ∧
    (b6m_H1Equiv (b6m_transport b C s t)).toLinearMap =
      homologyMap ℤ 1 (TopCat.ofHom
        ⟨b6m_transport b C s t, (b6m_transport b C s t).continuous⟩) := by
  refine ⟨fun u ↦ rfl, fun u ↦ ?_, ?_, rfl⟩
  · change b6t_sphere b t.val (f (ι u)) = b6t_sphere b t.val (π u)
    rw [hp]
  · obtain ⟨e, he⟩ := b6t_homeomorph b hb t.val t.property
    refine ⟨e, he, fun x ↦ ?_⟩
    rcases x with ⟨⟨q, c⟩, hq⟩
    cases hq
    change b6t_sphere b t.val (f c) = e (b6t_sphere b b (f c))
    rw [he, b6t_identity]
    rfl

theorem b6m_homology_equivariant_aux (b : Fin 10 → ℂ) (G C : Type) [Group G]
    [TopologicalSpace C] [MulAction G C]
    (hC : ∀ g : G, Continuous (fun x : C ↦ g • x))
    (s t : b6t_polydisc b) (g : G) (x : b6m_H1 (b6m_Fibre b C s)) :
    (∀ q : b6m_Fibre b C s,
      b6m_transport b C s t (b6m_deck b G C hC s g q) =
        b6m_deck b G C hC t g (b6m_transport b C s t q)) ∧
    b6m_H1Equiv (b6m_transport b C s t)
      (homologyMap ℤ 1 (TopCat.ofHom (b6m_deck b G C hC s g)) x) =
      homologyMap ℤ 1 (TopCat.ofHom (b6m_deck b G C hC t g))
        (b6m_H1Equiv (b6m_transport b C s t) x) := by
  constructor
  · intro q
    rfl
  · let T : TopCat.of (b6m_Fibre b C s) ⟶ TopCat.of (b6m_Fibre b C t) :=
      TopCat.ofHom ⟨b6m_transport b C s t, (b6m_transport b C s t).continuous⟩
    let Ds : TopCat.of (b6m_Fibre b C s) ⟶ TopCat.of (b6m_Fibre b C s) :=
      TopCat.ofHom (b6m_deck b G C hC s g)
    let Dt : TopCat.of (b6m_Fibre b C t) ⟶ TopCat.of (b6m_Fibre b C t) :=
      TopCat.ofHom (b6m_deck b G C hC t g)
    have hc : Ds ≫ T = T ≫ Dt := by
      ext q
      rfl
    let F := (AlgebraicTopology.singularHomologyFunctor.{0} (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)
    have hm := congrArg (fun k ↦ (F.map k).hom x) hc
    change (F.map T).hom ((F.map Ds).hom x) = (F.map Dt).hom ((F.map T).hom x)
    simpa only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] using hm

theorem b6m_H1Equiv_trans_aux {A B C : Type}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (e : A ≃ₜ B) (f : B ≃ₜ C) :
    (b6m_H1Equiv e).trans (b6m_H1Equiv f) = b6m_H1Equiv (e.trans f) := by
  let E : TopCat.of A ⟶ TopCat.of B := TopCat.ofHom ⟨e, e.continuous⟩
  let F : TopCat.of B ⟶ TopCat.of C := TopCat.ofHom ⟨f, f.continuous⟩
  let H := (AlgebraicTopology.singularHomologyFunctor.{0} (ModuleCat.{0} ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  ext x
  change (H.map F).hom ((H.map E).hom x) = (H.map (E ≫ F)).hom x
  rw [Functor.map_comp]
  rfl

theorem b6m_H1Equiv_symm_aux {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) : (b6m_H1Equiv e).symm = b6m_H1Equiv e.symm := by
  rfl

theorem b6m_H1Equiv_refl_aux (A : Type) [TopologicalSpace A] :
    b6m_H1Equiv (Homeomorph.refl A) = LinearEquiv.refl ℤ (b6m_H1 A) := by
  ext x
  let H := (AlgebraicTopology.singularHomologyFunctor.{0} (ModuleCat.{0} ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  have h := H.map_id (TopCat.of A)
  exact congrArg (fun k ↦ k.hom x) h

theorem b6m_coordinate_transport_aux (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C] (s t : b6t_polydisc b) :
    ((b6m_coordinate b C s).symm.trans (b6m_transport b C s t)).trans
      (b6m_coordinate b C t) = Homeomorph.refl C := by
  ext x
  rfl

theorem b6m_transport_trans_aux (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C] (s t u : b6t_polydisc b) :
    (b6m_transport b C s t).trans (b6m_transport b C t u) =
      b6m_transport b C s u := by
  ext x
  rfl

theorem b6m_H1_coordinate_naturality_aux (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C] (s t : b6t_polydisc b) :
    (b6m_H1Equiv (b6m_transport b C s t)).trans
      (b6m_H1Equiv (b6m_coordinate b C t)) = b6m_H1Equiv (b6m_coordinate b C s) := by
  rw [b6m_H1Equiv_trans_aux]
  congr 1

theorem b6m_homology_trivialization_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (s : b6t_polydisc b) :
    (∀ t : b6t_polydisc b,
      ((b6m_H1Equiv (b6m_coordinate b C s)).symm.trans
        (b6m_H1Equiv (b6m_transport b C s t))).trans
        (b6m_H1Equiv (b6m_coordinate b C t)) = LinearEquiv.refl ℤ (b6m_H1 C)) ∧
    IsLocallyConstant (fun t : b6t_polydisc b ↦
      ((b6m_H1Equiv (b6m_coordinate b C s)).symm.trans
        (b6m_H1Equiv (b6m_transport b C s t))).trans
        (b6m_H1Equiv (b6m_coordinate b C t))) ∧
    (∀ t u : b6t_polydisc b,
      (b6m_H1Equiv (b6m_transport b C s t)).trans
        (b6m_H1Equiv (b6m_transport b C t u)) =
          b6m_H1Equiv (b6m_transport b C s u)) ∧
    ∃ η : b6m_integralLocalSystem b C ≅
        (Functor.const (FundamentalGroupoid (b6t_polydisc b))).obj (b6m_H1 C),
      ∀ t : b6t_polydisc b, (η.hom.app (.mk t)).hom =
        (b6m_H1Equiv (b6m_coordinate b C t)).toLinearMap := by
  have htriv : ∀ t : b6t_polydisc b,
      ((b6m_H1Equiv (b6m_coordinate b C s)).symm.trans
        (b6m_H1Equiv (b6m_transport b C s t))).trans
        (b6m_H1Equiv (b6m_coordinate b C t)) = LinearEquiv.refl ℤ (b6m_H1 C) := by
    intro t
    rw [b6m_H1Equiv_symm_aux, b6m_H1Equiv_trans_aux, b6m_H1Equiv_trans_aux,
      b6m_coordinate_transport_aux, b6m_H1Equiv_refl_aux]
  refine ⟨htriv, ?_, ?_, ?_⟩
  · rw [show (fun t : b6t_polydisc b ↦
        ((b6m_H1Equiv (b6m_coordinate b C s)).symm.trans
          (b6m_H1Equiv (b6m_transport b C s t))).trans
          (b6m_H1Equiv (b6m_coordinate b C t))) =
        Function.const _ (LinearEquiv.refl ℤ (b6m_H1 C)) by
      funext t
      exact htriv t]
    exact IsLocallyConstant.const _
  · intro t u
    rw [b6m_H1Equiv_trans_aux, b6m_transport_trans_aux]
  · let η : b6m_integralLocalSystem b C ≅
        (Functor.const (FundamentalGroupoid (b6t_polydisc b))).obj (b6m_H1 C) :=
      NatIso.ofComponents
        (fun t ↦ (b6m_H1Equiv (b6m_coordinate b C t.as)).toModuleIso)
        (by
          intro X Y f
          have h := congrArg LinearEquiv.toLinearMap
            (b6m_H1_coordinate_naturality_aux b C X.as Y.as)
          change (b6m_H1Equiv (b6m_transport b C X.as Y.as)).toModuleIso.hom ≫
              (b6m_H1Equiv (b6m_coordinate b C Y.as)).toModuleIso.hom =
            (b6m_H1Equiv (b6m_coordinate b C X.as)).toModuleIso.hom ≫ 𝟙 _
          rw [Category.comp_id]
          apply ModuleCat.hom_ext
          exact h)
    exact ⟨η, fun t ↦ rfl⟩

theorem b6m_period_comparison_aux (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C] :
    ∃ P : b6m_H1 C ≃ₗ[ℤ] b3_periodLattice ℂ C,
      ∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ := by
  exact b6m_period_comparison_of_integral_cycle_lifting C
    (b6m_surface_integral_cycle_lifting C)

theorem b6m_intersection_transport_aux (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b)
    (C D : Type) [TopologicalSpace C] [TopologicalSpace D]
    [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [T2Space C] [T2Space D] [CompactSpace C] [CompactSpace D]
    [ConnectedSpace C] [ConnectedSpace D]
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k) (hs : Function.Surjective f)
    (e : C ≃ₜ D) (he : ∀ x, k (e x) = b6t_sphere b t (f x))
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ : b3_IsIntersectionForm ℂ Q)
    (R : LinearMap.BilinForm ℤ (b3_periodLattice ℂ D)) (hR : b3_IsIntersectionForm ℂ R) :
    ∃ (P : b6m_H1 C ≃ₗ[ℤ] b3_periodLattice ℂ C)
      (S : b6m_H1 D ≃ₗ[ℤ] b3_periodLattice ℂ D),
      (∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ) ∧
      (∀ γ : b3_SmoothLoop ℂ D, S (b6m_loopClass D γ) = b3_latticePeriod ℂ D γ) ∧
      ∀ x y : b6m_H1 C,
        R (S (b6m_H1Equiv e x)) (S (b6m_H1Equiv e y)) = Q (P x) (P y) := by
  obtain ⟨P, hP⟩ := b6m_period_comparison_aux C
  obtain ⟨S, hS⟩ := b6m_period_comparison_aux D
  obtain ⟨p, hp⟩ := hs ((0 : ℂ) : OnePoint ℂ)
  obtain ⟨q, hq⟩ := hs ((1 : ℂ) : OnePoint ℂ)
  have hpq : f p ≠ f q := by
    rw [hp, hq]
    exact fun h ↦ zero_ne_one (OnePoint.coe_injective h)
  obtain ⟨E, hE⟩ := b6t_homeomorph b hb t ht
  have hkpq : k (e p) ≠ k (e q) := by
    rw [he, he, ← hE, ← hE]
    exact fun h ↦ hpq (E.injective h)
  exact ⟨P, S, hP, hS, b6m_filling_pairing_transport b t hb ht f k hf hk
    ⟨p, q, hpq⟩ ⟨e p, e q, hkpq⟩ e he P.toLinearMap hP S.toLinearMap hS Q hQ R hR⟩

end HodgeLean.Foundations.Program
