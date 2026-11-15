import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bRoot
import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bAtlasExistence
import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bProperAction
import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bCompatibility
import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bProjection
import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bHolomorphic
import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bSlice
import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bTopology
import Mathlib.Geometry.Manifold.Submersion

/-! # B6-2b: moving branched covers and their analytic total space

Implication from a finite-group quotient covering of a punctured normalized sphere
to a filled, marked local analytic family. Comparison with independently selected
B4 fibres and homology transport belong to B6-2c.
HC no distance; AV milestone no distance.
-/

noncomputable section

open scoped Manifold ContDiff
open Manifold

namespace HodgeLean.Foundations.Program

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b6a_power_holomorphic_aux (i : Fin 10) (e : ℕ) :
    ContDiff ℂ ω (b6a_power i e) := by
  unfold b6a_power
  fun_prop

theorem b6a_power_derivative_aux (i : Fin 10) (e : ℕ) (he : 0 < e) (t : Fin 10 → ℂ) (w : ℂ) :
    HasDerivAt (fun z : ℂ ↦ (b6a_power i e (t, z)).2) ((e : ℂ) * w ^ (e - 1)) w ∧
      (((e : ℂ) * w ^ (e - 1) = 0) ↔ 1 < e ∧ w = 0) := by
  constructor
  · simpa [b6a_power] using (hasDerivAt_pow e w).const_add (t i)
  · constructor
    · intro hz
      have he_one : 1 < e := by
        by_contra h
        have : e = 1 := by omega
        subst e
        simp at hz
      have hw : w = 0 := by
        by_contra hw
        exact (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt he)) (pow_ne_zero _ hw)) hz
      exact ⟨he_one, hw⟩
    · rintro ⟨he_one, rfl⟩
      simp [Nat.sub_ne_zero_iff_lt.mpr he_one]

theorem b6a_root_transition_aux (s : Set ((Fin 10 → ℂ) × ℂ)) (hs : IsOpen s)
    (h r : ((Fin 10 → ℂ) × ℂ) → ℂ) (hh : ContDiffOn ℂ ω h s)
    (hr : ContinuousOn r s) (e : ℕ) (he : 0 < e)
    (hne : ∀ q ∈ s, r q ≠ 0) (hpow : ∀ q ∈ s, r q ^ e = h q) :
    ContDiffOn ℂ ω r s := by
  exact contDiffOn_of_continuousOn_pow_eq s hs h r hh hr e he hne hpow

theorem b6a_fill_transport_aux (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G : Type) [Group G] [Finite G] (U : Type) [TopologicalSpace U]
    [MulAction G U] [ConnectedSpace U] (π : U → b6t_punctured b)
    (hπ : IsQuotientCoveringMap π G)
    (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b) :
    ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace ℂ C)
      (_ : IsManifold 𝓘(ℂ, ℂ) ω C) (_ : T2Space C) (_ : CompactSpace C)
      (_ : ConnectedSpace C) (_ : MulAction G C) (f : C → OnePoint ℂ) (ι : U → C),
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f ∧ b4_IsGaloisCover G f ∧
      Function.Surjective f ∧
      (∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) ∧
      Topology.IsOpenEmbedding ι ∧
      Set.range ι = f ⁻¹' (Set.range (b6_branch t))ᶜ ∧
      (∀ u, f (ι u) = b6t_projection b t π u) ∧
      (∀ (g : G) (u : U), ι (g • u) = g • ι u) := by
  obtain ⟨e, _, hecover, heproj, _, _⟩ := b6t_cover b hb t ht G U π hπ
  let B : Set (OnePoint ℂ) := Set.range (b6_branch t)
  have hB : B.Finite := Set.finite_range _
  obtain ⟨C, instTop, instChart, instMan, instT2, instCompact, instConnected,
      instNonempty, instAction, f, ι, haction, hf, hgal, hi, hirange, hιf, hιG⟩ :=
    b4_extend_galoisCovering (E := ℂ) (E' := ℂ) (Y := OnePoint ℂ) (by simp)
      (by simp) B hB (e ∘ π) hecover
  letI : TopologicalSpace C := instTop
  letI : ChartedSpace ℂ C := instChart
  letI : IsManifold 𝓘(ℂ, ℂ) ω C := instMan
  letI : T2Space C := instT2
  letI : CompactSpace C := instCompact
  letI : ConnectedSpace C := instConnected
  letI : Nonempty C := instNonempty
  letI : MulAction G C := instAction
  have hInf : Bᶜ.Infinite := hB.infinite_compl
  obtain ⟨y, hy⟩ := hInf.nonempty
  obtain ⟨z, hz, hzy⟩ := hInf.exists_notMem_finite (Set.finite_singleton y)
  have hyz : y ≠ z := by
    intro h
    exact hzy (h ▸ Set.mem_singleton y)
  obtain ⟨uy, huy⟩ := hecover.surjective ⟨y, hy⟩
  obtain ⟨uz, huz⟩ := hecover.surjective ⟨z, hz⟩
  have hnc : ∃ x x', f x ≠ f x' := by
    refine ⟨ι uy, ι uz, ?_⟩
    rw [hιf, hιf]
    intro h
    have hsub : (e ∘ π) uy = (e ∘ π) uz := Subtype.ext h
    have heq : (⟨y, hy⟩ : {x : OnePoint ℂ // x ∈ Bᶜ}) = ⟨z, hz⟩ :=
      huy.symm.trans (hsub.trans huz)
    exact hyz (congrArg Subtype.val heq)
  have hsurj : Function.Surjective f :=
    b4_surjective (E := ℂ) (E' := ℂ) (by simp) (by simp) f hf hnc
  refine ⟨C, instTop, instChart, instMan, instT2, instCompact, instConnected,
    instAction, f, ι, hf, hgal, hsurj, haction, hi, ?_, ?_, hιG⟩
  · simpa [B] using hirange
  · intro u
    exact (hιf u).trans (heproj u)


theorem b6a_chart_compatibility_aux (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C] [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hA : ∀ q, q ∈ (A q).source ∧
      A q ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (hb : b ∈ b6_chart) (G U : Type) [Group G] [Finite G]
    [TopologicalSpace U] [MulAction G U] [ConnectedSpace U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G)
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    (f : C → OnePoint ℂ) (ι : U → C)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hgal : b4_IsGaloisCover G f) (hsurj : Function.Surjective f)
    (hact : ∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (hι : Topology.IsOpenEmbedding ι)
    (hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ)
    (hproj : ∀ u, f (ι u) = π u)
    (hequiv : ∀ (g : G) (u : U), ι (g • u) = g • ι u)
    (n : C → ℕ) (hn : ∀ x, 0 < n x)
    (hunram : ∀ x, f x ∉ Set.range (b6_branch b) → n x = 1)
    (hlocal : ∀ x (j : Fin 13), f x = b6_branch b j →
      ∃ P : OpenPartialHomeomorph C ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ C ∧ P x = 0 ∧
        (∀ y ∈ P.source, f y = b6a_value b j (P y ^ n x)) ∧
        ∀ g : MulAction.stabilizer G x, ∃ ζ : ℂ, ζ ^ n x = 1 ∧
          Set.MapsTo (fun y : C ↦ (g : G) • y) P.source P.source ∧
          ∀ y ∈ P.source, P ((g : G) • y) = ζ * P y)
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val)
    (hfree : ∀ q, f q.2 ∉ Set.range (b6_branch b) →
      ∀ y ∈ (A q).source, b6a_map b f y = ((A q y).2 : OnePoint ℂ))
    (hmark : ∀ q (j : Fin 13), f q.2 = b6_branch b j →
      (A q q).2 = 0 ∧ ∀ y ∈ (A q).source,
        b6a_map b f y = b6a_value y.1.val j ((A q y).2 ^ n q.2)) :
    ∀ q q', ContDiffOn ℂ ω ((A q).symm.trans (A q'))
      ((A q).symm.trans (A q')).source := by
  exact b6a_transitions_contDiffOn b hb C f n hn A hparam hfree
    (fun q j hj ↦ (hmark q j hj).2)

theorem b6a_total_map_holomorphic_aux (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C] [ChartedSpace ℂ C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    (f : C → OnePoint ℂ)
    (hb : b ∈ b6_chart) (G U : Type) [Group G] [Finite G]
    [TopologicalSpace U] [MulAction G U] [ConnectedSpace U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G)
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C]
    [ConnectedSpace C] [MulAction G C] (ι : U → C)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hgal : b4_IsGaloisCover G f) (hsurj : Function.Surjective f)
    (hact : ∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (hι : Topology.IsOpenEmbedding ι)
    (hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ)
    (hproj : ∀ u, f (ι u) = π u)
    (hequiv : ∀ (g : G) (u : U), ι (g • u) = g • ι u)
    (n : C → ℕ) (hn : ∀ x, 0 < n x)
    (hunram : ∀ x, f x ∉ Set.range (b6_branch b) → n x = 1)
    (hlocal : ∀ x (j : Fin 13), f x = b6_branch b j →
      ∃ P : OpenPartialHomeomorph C ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ C ∧ P x = 0 ∧
        (∀ y ∈ P.source, f y = b6a_value b j (P y ^ n x)) ∧
        ∀ g : MulAction.stabilizer G x, ∃ ζ : ℂ, ζ ^ n x = 1 ∧
          Set.MapsTo (fun y : C ↦ (g : G) • y) P.source P.source ∧
          ∀ y ∈ P.source, P ((g : G) • y) = ζ * P y)
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hA : ∀ q, q ∈ (A q).source ∧
      A q ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val)
    (hfree : ∀ q, f q.2 ∉ Set.range (b6_branch b) →
      ∀ y ∈ (A q).source, b6a_map b f y = ((A q y).2 : OnePoint ℂ))
    (hmark : ∀ q (j : Fin 13), f q.2 = b6_branch b j →
      (A q q).2 = 0 ∧ ∀ y ∈ (A q).source,
        b6a_map b f y = b6a_value y.1.val j ((A q y).2 ^ n q.2)) :
    ContMDiff 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω (b6a_map b f) := by
  exact b6a_map_contMDiff_of_local_formulas b C f n A hA hparam hfree
    (fun q j hj ↦ (hmark q j hj).2)

theorem b6a_family_projection_aux (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    (hb : b ∈ b6_chart) (G U : Type) [Group G] [Finite G]
    [TopologicalSpace U] [MulAction G U] [ConnectedSpace U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G)
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    (f : C → OnePoint ℂ) (ι : U → C)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hgal : b4_IsGaloisCover G f) (hsurj : Function.Surjective f)
    (hact : ∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (hι : Topology.IsOpenEmbedding ι)
    (hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ)
    (hproj : ∀ u, f (ι u) = π u)
    (hequiv : ∀ (g : G) (u : U), ι (g • u) = g • ι u)
    (n : C → ℕ) (hn : ∀ x, 0 < n x)
    (hunram : ∀ x, f x ∉ Set.range (b6_branch b) → n x = 1)
    (hlocal : ∀ x (j : Fin 13), f x = b6_branch b j →
      ∃ P : OpenPartialHomeomorph C ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ C ∧ P x = 0 ∧
        (∀ y ∈ P.source, f y = b6a_value b j (P y ^ n x)) ∧
        ∀ g : MulAction.stabilizer G x, ∃ ζ : ℂ, ζ ^ n x = 1 ∧
          Set.MapsTo (fun y : C ↦ (g : G) • y) P.source P.source ∧
          ∀ y ∈ P.source, P ((g : G) • y) = ζ * P y)
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hA : ∀ q, q ∈ (A q).source ∧
      A q ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val)
    (hfree : ∀ q, f q.2 ∉ Set.range (b6_branch b) →
      ∀ y ∈ (A q).source, b6a_map b f y = ((A q y).2 : OnePoint ℂ))
    (hmark : ∀ q (j : Fin 13), f q.2 = b6_branch b j →
      (A q q).2 = 0 ∧ ∀ y ∈ (A q).source,
        b6a_map b f y = b6a_value y.1.val j ((A q y).2 ^ n q.2)) :
    ContMDiff 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, Fin 10 → ℂ) ω
        (fun q : b6t_polydisc b × C ↦ q.1.val) ∧
      IsSubmersion 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, Fin 10 → ℂ) ω
        (fun q : b6t_polydisc b × C ↦ q.1.val) := by
  have h := b6a_submersion_of_parameter_charts b C A hA hparam
  exact ⟨h.contMDiff, h⟩


theorem b6a_fibre_geometry_aux (b : Fin 10 → ℂ) (G U C : Type)
    [Group G] [TopologicalSpace U] [MulAction G U] [TopologicalSpace C]
    [MulAction G C] (π : U → b6t_punctured b) (f : C → OnePoint ℂ) (ι : U → C)
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (hb : b ∈ b6_chart) [Finite G] [ConnectedSpace U]
    (hπ : IsQuotientCoveringMap π G)
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hgal : b4_IsGaloisCover G f) (hsurj : Function.Surjective f)
    (hact : ∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (hι : Topology.IsOpenEmbedding ι)
    (hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ)
    (hproj : ∀ u, f (ι u) = π u)
    (hequiv : ∀ (g : G) (u : U), ι (g • u) = g • ι u)
    (n : C → ℕ) (hn : ∀ x, 0 < n x)
    (hunram : ∀ x, f x ∉ Set.range (b6_branch b) → n x = 1)
    (hlocal : ∀ x (j : Fin 13), f x = b6_branch b j →
      ∃ P : OpenPartialHomeomorph C ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ C ∧ P x = 0 ∧
        (∀ y ∈ P.source, f y = b6a_value b j (P y ^ n x)) ∧
        ∀ g : MulAction.stabilizer G x, ∃ ζ : ℂ, ζ ^ n x = 1 ∧
          Set.MapsTo (fun y : C ↦ (g : G) • y) P.source P.source ∧
          ∀ y ∈ P.source, P ((g : G) • y) = ζ * P y)
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hA : ∀ q, q ∈ (A q).source ∧
      A q ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val)
    (hfree : ∀ q, f q.2 ∉ Set.range (b6_branch b) →
      ∀ y ∈ (A q).source, b6a_map b f y = ((A q y).2 : OnePoint ℂ))
    (hmark : ∀ q (j : Fin 13), f q.2 = b6_branch b j →
      (A q q).2 = 0 ∧ ∀ y ∈ (A q).source,
        b6a_map b f y = b6a_value y.1.val j ((A q y).2 ^ n q.2)) :
    ∀ t : b6t_polydisc b,
          ∃ (_ : ChartedSpace ℂ C) (_ : IsManifold 𝓘(ℂ, ℂ) ω C),
            ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ b6a_map b f (t, x)) ∧
            ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (fun x : C ↦ (t, x)) ∧
            b4_IsGaloisCover G (fun x : C ↦ b6a_map b f (t, x)) ∧
            Function.Surjective (fun x : C ↦ b6a_map b f (t, x)) ∧
            (∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) ∧
            Set.range ι = (fun x : C ↦ b6a_map b f (t, x)) ⁻¹'
              (Set.range (b6_branch t.val))ᶜ ∧
            (∀ u, b6a_map b f (t, ι u) = b6t_projection b t.val π u) := by
  intro t
  have htotalAction : ∀ g : G,
      ContMDiff 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
        (fun q : b6t_polydisc b × C ↦ (q.1, g • q.2)) :=
    (b6a_family_proper_action_aux b G C hb U π hπ f ι hf hgal hsurj hact hι
      hrange hproj hequiv n hn hunram hlocal A hA hparam hfree hmark).2
  let slice : ChartedSpace ℂ C :=
    b6a_sliceChartedSpace b C A (fun q ↦ (hA q).1) hparam t
  letI : ChartedSpace ℂ C := slice
  let man : IsManifold 𝓘(ℂ, ℂ) ω C := b6a_slice_isManifold b C A hA hparam t
  letI : IsManifold 𝓘(ℂ, ℂ) ω C := man
  refine ⟨slice, man, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact b6a_slice_map_contMDiff b C A hA hparam (b6a_map b f)
      (b6a_map_contMDiff_of_local_formulas b C f n A hA hparam hfree
        (fun q j hj ↦ (hmark q j hj).2)) t
  · exact b6a_slice_inclusion_contMDiff b C A hA hparam t
  · exact b6a_fibre_galois b hb G C f hgal t
  · exact b6a_fibre_surjective b hb C f hsurj t
  · intro g
    apply b6a_slice_vertical_map_contMDiff b C A hA hparam
      (fun q : b6t_polydisc b × C ↦ (q.1, g • q.2)) (fun x : C ↦ g • x)
      (fun _ _ ↦ rfl)
    exact htotalAction g
  · exact b6a_fibre_punctured_range b hb U C f ι hrange t
  · exact b6a_fibre_projection b U C π f ι hproj t

#print axioms b6a_analytic_atlas_aux
#print axioms b6a_chart_compatibility_aux
#print axioms b6a_total_map_holomorphic_aux
#print axioms b6a_family_projection_aux
#print axioms b6a_family_proper_action_aux
#print axioms b6a_fibre_geometry_aux

end HodgeLean.Foundations.Program
