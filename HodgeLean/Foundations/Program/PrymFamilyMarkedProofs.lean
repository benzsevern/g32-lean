import HodgeLean.Foundations.Program.PrymFamilyMarkedCharts

/-! # B6-3g, part 5: proof obligations

One auxiliary statement for each public statement of `PrymFamilyMarked.lean`, with its body.
The fibre structure uses the atlas of `PrymFamilyMarkedAtlas.lean` and the charts of
`PrymFamilyMarkedCharts.lean`; the branch set uses the stabilizer criterion
`b63g5_two_le_ramIndex_iff` below.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.AppellHumbert HodgeLean.Papers
open scoped TensorProduct Manifold ContDiff
open Filter Topology

namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b63g5_fibre_structure_aux (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C] (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hgal : b4_IsGaloisCover b4b_Group f)
    (hact : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V) :
    ∃ (_ : ChartedSpace ℂ (b63l_parameterFibre b C V hV t))
      (_ : IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)),
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t) ∧
      ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
        (fun x : b63l_parameterFibre b C V hV t ↦ g • x) := by
  have ht : t.val ∈ b6t_polydisc b := hV t.property
  obtain ⟨E, hE⟩ := b6t_homeomorph b hb t.val ht
  set co := b6m_coordinate b C ⟨t.val, ht⟩
  have hco : ∀ q : b63l_parameterFibre b C V hV t, co q = q.val.2 := fun _ ↦ rfl
  set F := b63d_projection b C f V hV t
  have hF : ∀ q, F q = E (f (co q)) := fun q ↦ by
    rw [hE, hco]
    change b6t_sphere b q.val.1.val (f q.val.2) = _
    rw [q.property]
  obtain ⟨x₀⟩ := (inferInstance : Nonempty C)
  have hnc0 : ∃ a a', f a ≠ f a' := b4cov_nonconst_of_galois (Module.finrank_self ℂ) f hgal x₀
  have hFc : Continuous F := by
    have : F = E ∘ f ∘ co := funext hF
    rw [this]
    exact E.continuous.comp (hf.continuous.comp co.continuous)
  have hncF : ∀ q, ¬ ∀ᶠ q' in 𝓝 q, F q' = F q := by
    intro q h
    obtain ⟨a, a', haa⟩ := hnc0
    apply haa
    refine b4cov_const_of_eventuallyConst f hf (co q) ?_ a a'
    have h1 := co.symm.continuous.continuousAt.preimage_mem_nhds
      (by rw [co.symm_apply_apply]; exact h)
    filter_upwards [h1] with y hy
    have hy' : F (co.symm y) = F q := hy
    rw [hF, hF, co.apply_symm_apply] at hy'
    exact E.injective hy'
  have hcover : ∀ q, ∃ φ : OpenPartialHomeomorph (b63l_parameterFibre b C V hV t) ℂ,
      q ∈ φ.source ∧ ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (F ∘ φ.symm) φ.target := by
    intro q
    obtain ⟨e, w, he, hyw, hw0, hwf⟩ := b63g5_normal_form f hf hnc0 (co q)
    set p := f (co q)
    obtain ⟨h0H, hH0⟩ := b63g5_shift_zero E p
    obtain ⟨κ, hκ, hbd⟩ := b63g5_shift_bound b hb t.val ht E hE p
    obtain ⟨K, hK0, hK⟩ := b63g5_root_chart (b63g5_shift E p) h0H hH0 hκ hbd he
    set ψ₀ := chartAt ℂ p
    set ψ₁ := chartAt ℂ (E p)
    set d := ψ₁ (E p)
    let φ := co.toOpenPartialHomeomorph.trans (w.trans K)
    have hφsrc : ∀ q', q' ∈ φ.source ↔ co q' ∈ w.source ∧ w (co q') ∈ K.source := by
      intro q'
      simp [φ]
    have hφapp : ∀ q', φ q' = K (w (co q')) := fun q' ↦ rfl
    refine ⟨φ, (hφsrc q).2 ⟨hyw, by rw [hw0]; exact hK0⟩, ?_⟩
    have key : ∀ u ∈ φ.target, F (φ.symm u) = ψ₁.symm (u ^ e + d) ∧ u ^ e + d ∈ ψ₁.target := by
      intro u hu
      set q' := φ.symm u
      have hq' : q' ∈ φ.source := φ.map_target hu
      have hu' : φ q' = u := φ.right_inv hu
      obtain ⟨hyy, hv⟩ := (hφsrc q').1 hq'
      set yy := co q'
      set v := w yy
      obtain ⟨hfyy, hψ₀⟩ := hwf yy hyy
      obtain ⟨hvH, hKv⟩ := hK v hv
      obtain ⟨-, hEsrc⟩ := b63g5_shift_source E p hvH
      have hinv : ψ₀.symm (ψ₀ p + v ^ e) = f yy := by
        rw [← hψ₀, ψ₀.left_inv hfyy]
      rw [hinv] at hEsrc
      have hshift := b63g5_shift_apply E p (v ^ e)
      have hKu : K v = u := by rw [← hu', hφapp]
      rw [hinv, ← hKv, hKu] at hshift
      have hval : u ^ e + d = ψ₁ (E (f yy)) := by rw [hshift]; ring
      refine ⟨?_, ?_⟩
      · rw [hval, ψ₁.left_inv hEsrc, hF]
      · rw [hval]; exact ψ₁.map_source hEsrc
    have hpoly : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun u : ℂ ↦ u ^ e + d) :=
      ((contDiff_id.pow e).add contDiff_const).contMDiff
    refine ((contMDiffOn_chart_symm (I := 𝓘(ℂ, ℂ)) (x := E p)).comp hpoly.contMDiffOn
      (fun u hu ↦ (key u hu).2)).congr fun u hu ↦ ?_
    exact (key u hu).1
  obtain ⟨cs, hman, hFm, hT⟩ := b63g5_exists_structure F hFc hncF hcover
  refine ⟨cs, hman, hFm, fun g ↦ hT _ ?_ (MulAction.injective g) fun q ↦ ?_⟩
  · change Continuous fun q : b63l_parameterFibre b C V hV t ↦
      (⟨(⟨t.val, ht⟩, g • q.val.2), rfl⟩ : b63l_parameterFibre b C V hV t)
    exact (continuous_const.prodMk ((hact g).continuous.comp
      (continuous_snd.comp continuous_subtype_val))).subtype_mk _
  · rw [hF, hF]
    exact congrArg E (hgal.1 g (co q))

theorem b63g5_fibre_filling_aux (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) {U C : Type} [TopologicalSpace U]
    [TopologicalSpace C] (f : C → OnePoint ℂ) (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V) :
    Topology.IsOpenEmbedding (b63g5_fibreMap b ι V hV t) ∧
      Set.range (b63g5_fibreMap b ι V hV t) =
        b63d_projection b C f V hV t ⁻¹' (Set.range (b6_branch t.val))ᶜ := by
  obtain ⟨e, he⟩ := b6t_homeomorph b hb t.val (hV t.property)
  have hmarks := b6t_marks b hb t.val (hV t.property)
  refine ⟨?_, ?_⟩
  · have : b63g5_fibreMap b ι V hV t =
        (b6m_coordinate b C ⟨t.val, hV t.property⟩).symm ∘ ι := rfl
    rw [this]
    exact (b6m_coordinate b C ⟨t.val, hV t.property⟩).symm.isOpenEmbedding.comp hι
  · ext q
    have hq : q = (b6m_coordinate b C ⟨t.val, hV t.property⟩).symm q.val.2 :=
      ((b6m_coordinate b C _).symm_apply_apply q).symm
    have hpq : b63d_projection b C f V hV t q = b6t_sphere b t.val (f q.val.2) := by
      change b6t_sphere b q.val.1.val (f q.val.2) = _
      rw [q.property]
    have key : (∃ j, b6_branch t.val j = b6t_sphere b t.val (f q.val.2)) ↔
        ∃ j, b6_branch b j = f q.val.2 := by
      constructor
      · rintro ⟨j, hj⟩
        refine ⟨j, e.injective ?_⟩
        rw [he, he, hmarks]; exact hj
      · rintro ⟨j, hj⟩
        exact ⟨j, by rw [← hmarks, hj]⟩
    constructor
    · rintro ⟨u, rfl⟩
      have hu : ι u ∈ Set.range ι := ⟨u, rfl⟩
      rw [hrange] at hu
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_range] at hu ⊢
      change ¬ ∃ j, b6_branch t.val j = b6t_sphere b t.val (f (ι u))
      exact fun h ↦ hu (key.1 h)
    · intro hq'
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_range] at hq'
      rw [hpq] at hq'
      have : q.val.2 ∈ Set.range ι := by
        rw [hrange]
        exact fun h ↦ hq' (key.2 h)
      obtain ⟨u, hu⟩ := this
      refine ⟨u, ?_⟩
      rw [hq]
      change (b6m_coordinate b C _).symm (ι u) = _
      rw [hu]

theorem b63g5_fibre_galois_aux (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (C : Type) [MulAction b4b_Group C]
    (f : C → OnePoint ℂ) (hgal : b4_IsGaloisCover b4b_Group f) (hsurj : Function.Surjective f)
    (hfree : ∀ x, f x ∉ Set.range (b6_branch b) → MulAction.stabilizer b4b_Group x = ⊥)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V) :
    b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t) ∧
      Function.Surjective (b63d_projection b C f V hV t) ∧
      ∀ x, b63d_projection b C f V hV t x ∉ Set.range (b6_branch t.val) →
        MulAction.stabilizer b4b_Group x = ⊥ := by
  obtain ⟨e, he⟩ := b6t_homeomorph b hb t.val (hV t.property)
  have hmarks := b6t_marks b hb t.val (hV t.property)
  have hproj : ∀ q : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t q = e (f q.val.2) := fun q ↦ by
    rw [he]
    change b6t_sphere b q.val.1.val (f q.val.2) = _
    rw [q.property]
  have hq : ∀ q : b63l_parameterFibre b C V hV t,
      q = ⟨(⟨t.val, hV t.property⟩, q.val.2), rfl⟩ := fun q ↦
    Subtype.ext (Prod.ext q.property rfl)
  refine ⟨⟨fun g q ↦ ?_, fun q q' h ↦ ?_⟩, fun y ↦ ?_, fun q hq' ↦ ?_⟩
  · rw [hproj, hproj]
    exact congrArg e (hgal.1 g q.val.2)
  · rw [hproj, hproj] at h
    obtain ⟨g, hg⟩ := hgal.2 _ _ (e.injective h)
    refine ⟨g, ?_⟩
    rw [hq q']
    apply Subtype.ext
    exact Prod.ext rfl hg
  · obtain ⟨x, hx⟩ := hsurj (e.symm y)
    refine ⟨⟨(⟨t.val, hV t.property⟩, x), rfl⟩, ?_⟩
    refine (hproj _).trans ?_
    change e (f x) = y
    rw [hx, e.apply_symm_apply]
  · have hx : f q.val.2 ∉ Set.range (b6_branch b) := by
      rintro ⟨j, hj⟩
      apply hq'
      refine ⟨j, ?_⟩
      rw [hproj, he, ← hj, hmarks]
    have hs := hfree _ hx
    rw [eq_bot_iff] at hs ⊢
    intro g hg
    apply hs
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    exact congrArg (fun q : b63l_parameterFibre b C V hV t ↦ q.val.2) hg

/-- For a holomorphic Galois cover by a finite group acting faithfully and holomorphically on a
connected Hausdorff surface, the ramification index is at least two exactly at the points with
nontrivial stabilizer. -/
theorem b63g5_two_le_ramIndex_iff {X G : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] [ConnectedSpace X] [Group G] [Finite G]
    [MulAction G X] [FaithfulSMul G X]
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : X ↦ g • x))
    (p : X → OnePoint ℂ) (hp : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω p) (hgal : b4_IsGaloisCover G p)
    (x : X) : 2 ≤ b4_ramIndex ℂ ℂ p x ↔ MulAction.stabilizer G x ≠ ⊥ := by
  have hE : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  have hnc := b4cov_nonconst_of_galois hE p hgal x
  have hpos := b4cov_ramIndex_pos p hp hnc x
  constructor
  · intro h2 hbot
    obtain ⟨N₁, hN₁, hsep⟩ := b4cov_exists_separating hG x
    obtain ⟨U, hUN, hUo, hxU, V, hV, hzero, hcount⟩ :=
      b4cov_local_degree hE hE p hp hnc x N₁ hN₁
    have hgood : U ∩ p ⁻¹' V ∈ 𝓝 x :=
      Filter.inter_mem (hUo.mem_nhds hxU) (hp.continuous.continuousAt.preimage_mem_nhds hV)
    obtain ⟨U', hU'sub, -, -, -, z, hzU', hzx⟩ := b4cov_goodPoint hE x _ hgood
    obtain ⟨hzU, hzV⟩ := hU'sub hzU'
    have hpz : p z ≠ p x := fun h ↦ hzx (hzero z hzU h)
    obtain ⟨hcard, -⟩ := hcount (p z) hzV hpz
    have h1 : 1 < (p ⁻¹' {p z} ∩ U).ncard := by omega
    obtain ⟨a, b, ⟨hap, haU⟩, ⟨hbp, hbU⟩, hab⟩ := (Set.one_lt_ncard_iff (Set.finite_of_ncard_pos (by omega))).1 h1
    obtain ⟨g, hg⟩ := hgal.2 a b (hap.trans hbp.symm)
    have hgx : g • x = x := hsep a (hUN haU) g (hg ▸ hUN hbU)
    have : g = 1 := by
      have hm : g ∈ MulAction.stabilizer G x := hgx
      rw [hbot] at hm
      exact hm
    exact hab (by rw [← hg, this, one_smul])
  · intro hne
    obtain ⟨k, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hkx : (k : G) • x = x := k.2
    have hk1' : (k : G) ≠ 1 := fun h ↦ hk1 (Subtype.ext h)
    by_contra hlt
    have he1 : b4_ramIndex ℂ ℂ p x = 1 := by omega
    have hiso := b4cov_fixed_isolated hE hG x k hkx hk1'
    obtain ⟨U, -, hUo, hxU, V, hV, hzero, hcount⟩ :=
      b4cov_local_degree hE hE p hp hnc x Set.univ Filter.univ_mem
    have hkU : (fun z : X ↦ (k : G) • z) ⁻¹' U ∈ 𝓝 x :=
      (hG k).continuous.continuousAt.preimage_mem_nhds (by rw [hkx]; exact hUo.mem_nhds hxU)
    have hgood : U ∩ p ⁻¹' V ∩ (fun z : X ↦ (k : G) • z) ⁻¹' U ∩
        {z | (k : G) • z = z → z = x} ∈ 𝓝 x :=
      Filter.inter_mem (Filter.inter_mem (Filter.inter_mem (hUo.mem_nhds hxU)
        (hp.continuous.continuousAt.preimage_mem_nhds hV)) hkU) hiso
    obtain ⟨U', hU'sub, -, -, -, z, hzU', hzx⟩ := b4cov_goodPoint hE x _ hgood
    obtain ⟨⟨⟨hzU, hzV⟩, hkzU⟩, hfix⟩ := hU'sub hzU'
    have hpz : p z ≠ p x := fun h ↦ hzx (hzero z hzU h)
    obtain ⟨hcard, -⟩ := hcount (p z) hzV hpz
    rw [he1] at hcard
    obtain ⟨w, hw⟩ := Set.ncard_eq_one.1 hcard
    have hz : z ∈ p ⁻¹' {p z} ∩ U := ⟨rfl, hzU⟩
    have hkz : (k : G) • z ∈ p ⁻¹' {p z} ∩ U := ⟨hgal.1 k z, hkzU⟩
    rw [hw] at hz hkz
    have : (k : G) • z = z := (Set.mem_singleton_iff.1 hkz).trans (Set.mem_singleton_iff.1 hz).symm
    exact hzx (hfix this)

theorem b63g5_fibre_branch_aux (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (C : Type) [TopologicalSpace C]
    [T2Space C] [ConnectedSpace C] [MulAction b4b_Group C] [FaithfulSMul b4b_Group C]
    (f : C → OnePoint ℂ) (hgal : b4_IsGaloisCover b4b_Group f) (hsurj : Function.Surjective f)
    (hfree : ∀ x, f x ∉ Set.range (b6_branch b) → MulAction.stabilizer b4b_Group x = ⊥)
    (hstab : ∀ j : Fin 13, ∃ x, f x = b6_branch b j ∧ MulAction.stabilizer b4b_Group x ≠ ⊥)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x)) :
    b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val) := by
  obtain ⟨hgal', -, hfree'⟩ := b63g5_fibre_galois_aux b hb C f hgal hsurj hfree V hV t
  have hmarks := b6t_marks b hb t.val (hV t.property)
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hq' := (b63g5_two_le_ramIndex_iff hG _ hk hgal' q).1 hq
    by_contra hy
    exact hq' (hfree' q hy)
  · rintro ⟨j, rfl⟩
    obtain ⟨x, hx, hxs⟩ := hstab j
    let q : b63l_parameterFibre b C V hV t := ⟨(⟨t.val, hV t.property⟩, x), rfl⟩
    refine ⟨q, (b63g5_two_le_ramIndex_iff hG _ hk hgal' q).2 ?_, ?_⟩
    · obtain ⟨k, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hxs
      refine (Subgroup.ne_bot_iff_exists_ne_one).2 ⟨⟨k, ?_⟩, fun h ↦ hk1 ?_⟩
      · rw [MulAction.mem_stabilizer_iff]
        apply Subtype.ext
        exact Prod.ext rfl k.2
      · have h' := congrArg (fun r : MulAction.stabilizer b4b_Group q ↦ (r : b4b_Group)) h
        exact Subtype.ext h'
    · change b6t_sphere b t.val (f x) = _
      rw [hx, hmarks]

theorem b63g5_fibre_lift_aux (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ : b6t_punctured mr_base) (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i))
    (C : Type) [TopologicalSpace C] [MulAction b4b_Group C] (f : C → OnePoint ℂ) (ι : U → C)
    (hι : Continuous ι) (hproj : ∀ u, f (ι u) = π u)
    (hequiv : ∀ (g : b4b_Group) (u : U), ι (g • u) = g • ι u)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V) (i : Fin 13) :
    ∃ Γ : C(unitInterval, b63l_parameterFibre mr_base C V hV t),
      Γ 0 = b63g5_fibreMap mr_base ι V hV t u₀ ∧
      (∀ s : unitInterval, b63d_projection mr_base C f V hV t (Γ s) = mr_curve i s) ∧
      Γ 1 = b4b_root i • Γ 0 := by
  obtain ⟨c, hcs, hc⟩ := hγ i
  have hcov := hπ.isCoveringMap
  let L := hcov.liftPath c.toContinuousMap u₀.1 (c.source.trans u₀.2.symm)
  have hL1 : L 1 = b4b_root i • u₀.1 := by
    have h1 := hcov.monodromy_eq_apply_one (γ := c) (e := u₀) (Γ := L)
      (hcov.liftPath_lifts _ _ _) (hcov.liftPath_zero _ _ _)
    have h2 := hπ.unop_fundamentalGroupToMulOpposite_smul (e := u₀) (γ := γ i)
    rw [hroot, MulOpposite.unop_op] at h2
    change L 1 = _
    rw [← h1, h2, ← hc]
    rfl
  have hL0 : L 0 = u₀.1 := hcov.liftPath_zero _ _ _
  have hLs : ∀ s, π (L s) = c s := fun s ↦ congrFun (hcov.liftPath_lifts _ _ _) s
  have hfix := (b6t_fixed mr_base mr_base_mem_chart t.val (hV t.property)).2.2.2
  have havoid := mr_curve_avoids t.val (hV t.property)
  refine ⟨⟨fun s ↦ b63g5_fibreMap mr_base ι V hV t (L s), ?_⟩, ?_, fun s ↦ ?_, ?_⟩
  · exact ((b6m_coordinate mr_base C _).symm.continuous.comp hι).comp L.continuous
  · change b63g5_fibreMap mr_base ι V hV t (L 0) = _
    rw [hL0]
  · change b6t_sphere mr_base t.val (f (ι (L s))) = _
    rw [hproj, hLs, hcs]
    exact hfix _ (havoid i s).2
  · change b63g5_fibreMap mr_base ι V hV t (L 1) = b4b_root i • b63g5_fibreMap mr_base ι V hV t (L 0)
    rw [hL1, hL0]
    apply Subtype.ext
    exact Prod.ext rfl (hequiv _ _)

theorem b63g5_fibre_rot_aux (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ : b6t_punctured mr_base) (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i))
    (C : Type) [TopologicalSpace C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C] [FaithfulSMul b4b_Group C] (f : C → OnePoint ℂ) (ι : U → C)
    (hι : Continuous ι) (hproj : ∀ u, f (ι u) = π u)
    (hequiv : ∀ (g : b4b_Group) (u : U), ι (g • u) = g • ι u)
    (hgal : b4_IsGaloisCover b4b_Group f) (hsurj : Function.Surjective f)
    (hfree : ∀ x, f x ∉ Set.range (b6_branch mr_base) → MulAction.stabilizer b4b_Group x = ⊥)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection mr_base C f V hV t))
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre mr_base C V hV t ↦ g • x)) :
    ∀ i : Fin 13, ∃ x : b63l_parameterFibre mr_base C V hV t,
      b63d_projection mr_base C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i) := by
  intro i
  have hb : mr_base ∈ b6_chart := mr_base_mem_chart
  have ht : t.val ∈ b6t_polydisc mr_base := hV t.property
  have h0 : mr_curve 12 ((0 : unitInterval) : ℝ) = ((mr_basePoint : ℂ) : OnePoint ℂ) := by
    simp [mr_curve, mr_outer, mr_basePoint]
  have hmem : ((mr_basePoint : ℂ) : OnePoint ℂ) ∈ b6t_punctured t.val := by
    have h := (mr_curve_avoids t.val ht 12 0).1
    rw [h0] at h
    exact h
  let y₁ : b6t_punctured t.val := ⟨_, hmem⟩
  have hex := fun j : Fin 13 ↦ (mr_loop_existsUnique t.val ht y₁ rfl j).exists
  choose γ' hγ' using hex
  obtain ⟨c, hc, hcγ⟩ := hγ' i
  obtain ⟨Γ, -, hΓ, hΓ1⟩ :=
    b63g5_fibre_lift_aux U π hπ y₀ u₀ γ hγ hroot C f ι hι hproj hequiv V hV t i
  obtain ⟨hgal', -, hfree'⟩ := b63g5_fibre_galois_aux mr_base hb C f hgal hsurj hfree V hV t
  exact mr_loops_positive t.val ht y₁ γ' hγ' (b63l_parameterFibre mr_base C V hV t) b4b_Group
    hG (b63d_projection mr_base C f V hV t) hk hgal' hfree' i c hcγ Γ (b4b_root i)
    (fun s ↦ (hΓ s).trans (hc s).symm) hΓ1

end HodgeLean.Foundations.Program
