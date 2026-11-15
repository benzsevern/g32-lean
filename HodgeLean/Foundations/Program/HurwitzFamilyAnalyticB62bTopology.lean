import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticDefs

noncomputable section

namespace HodgeLean.Foundations.Program

theorem b6a_cover_nonempty (b : Fin 10 → ℂ) (G U : Type)
    [Group G] [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G) : Nonempty U := by
  have hfinite : (Set.range (b6_branch b)).Finite := Set.finite_range _
  obtain ⟨y, hy⟩ := hfinite.infinite_compl.nonempty
  obtain ⟨u, _⟩ := hπ.surjective (⟨y, hy⟩ : b6t_punctured b)
  exact ⟨u⟩

theorem b6a_punctured_nonempty (b : Fin 10 → ℂ) : Nonempty (b6t_punctured b) := by
  have hfinite : (Set.range (b6_branch b)).Finite := Set.finite_range _
  obtain ⟨y, hy⟩ := hfinite.infinite_compl.nonempty
  exact ⟨⟨y, hy⟩⟩

theorem b6a_isOpen_punctured (b : Fin 10 → ℂ) : IsOpen (b6t_punctured b) :=
  (Set.finite_range (b6_branch b)).isClosed.isOpen_compl

noncomputable def b6a_puncturedValHom (b : Fin 10 → ℂ) :
    OpenPartialHomeomorph (b6t_punctured b) (OnePoint ℂ) :=
  let s : TopologicalSpace.Opens (OnePoint ℂ) :=
    ⟨b6t_punctured b, b6a_isOpen_punctured b⟩
  s.openPartialHomeomorphSubtypeCoe (b6a_punctured_nonempty b)

@[simp] theorem b6a_puncturedValHom_apply (b : Fin 10 → ℂ) (y : b6t_punctured b) :
    b6a_puncturedValHom b y = y.val := rfl

noncomputable def b6a_finiteSphereChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ :=
  (OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph ((↑) : ℂ → OnePoint ℂ)).symm

@[simp] theorem b6a_finiteSphereChart_apply (z : ℂ) :
    b6a_finiteSphereChart (z : OnePoint ℂ) = z := by
  exact OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph_left_inv _

@[simp] theorem b6a_finiteSphereChart_symm_apply (z : ℂ) :
    b6a_finiteSphereChart.symm z = (z : OnePoint ℂ) := rfl

@[simp] theorem b6a_finiteSphereChart_source :
    b6a_finiteSphereChart.source = Set.range ((↑) : ℂ → OnePoint ℂ) := by
  simp [b6a_finiteSphereChart]

@[simp] theorem b6a_finiteSphereChart_target :
    b6a_finiteSphereChart.target = Set.univ := rfl

noncomputable def b6a_puncturedComplexChart (b : Fin 10 → ℂ) :
    OpenPartialHomeomorph (b6t_punctured b) ℂ :=
  (b6a_puncturedValHom b).trans b6a_finiteSphereChart

@[simp] theorem b6a_puncturedComplexChart_source (b : Fin 10 → ℂ) :
    (b6a_puncturedComplexChart b).source = Set.univ := by
  ext y
  simp only [b6a_puncturedComplexChart, OpenPartialHomeomorph.trans_source,
    Set.mem_inter_iff, Set.mem_preimage, Set.mem_univ, iff_true]
  constructor
  · exact Set.mem_univ y
  · rcases y with ⟨y, hy⟩
    have hy_ne : y ≠ OnePoint.infty := by
      intro h
      apply hy
      refine ⟨12, ?_⟩
      simpa [h] using (show b6_branch b 12 = OnePoint.infty by rfl)
    obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hy_ne
    exact ⟨z, Set.mem_univ z, rfl⟩

@[simp] theorem b6a_puncturedComplexChart_apply (b : Fin 10 → ℂ)
    (z : ℂ) (hz : (z : OnePoint ℂ) ∈ b6t_punctured b) :
    b6a_puncturedComplexChart b ⟨z, hz⟩ = z := by
  simp [b6a_puncturedComplexChart]

theorem b6a_puncturedComplexChart_coe (b : Fin 10 → ℂ) (y : b6t_punctured b) :
    ((b6a_puncturedComplexChart b y : ℂ) : OnePoint ℂ) = y.val := by
  rcases y with ⟨y, hy⟩
  have hy_ne : y ≠ OnePoint.infty := by
    intro h
    apply hy
    refine ⟨12, ?_⟩
    simpa [h] using (show b6_branch b 12 = OnePoint.infty by rfl)
  obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hy_ne
  simp

noncomputable def b6a_coverChart (b : Fin 10 → ℂ) (G U : Type)
    [Group G] [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G) (u : U) :
    OpenPartialHomeomorph U (b6t_punctured b) :=
  (hπ.isCoveringMap.isLocalHomeomorph u).choose

theorem b6a_mem_coverChart_source (b : Fin 10 → ℂ) (G U : Type)
    [Group G] [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G) (u : U) :
    u ∈ (b6a_coverChart b G U π hπ u).source :=
  (hπ.isCoveringMap.isLocalHomeomorph u).choose_spec.1

theorem b6a_coverChart_eq (b : Fin 10 → ℂ) (G U : Type)
    [Group G] [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G) (u : U) :
    π = b6a_coverChart b G U π hπ u :=
  (hπ.isCoveringMap.isLocalHomeomorph u).choose_spec.2

noncomputable def b6a_openEmbeddingInverse (U C : Type)
    [TopologicalSpace U] [TopologicalSpace C] [Nonempty U]
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι) : OpenPartialHomeomorph C U :=
  (hι.toOpenPartialHomeomorph ι).symm

@[simp] theorem b6a_openEmbeddingInverse_source (U C : Type)
    [TopologicalSpace U] [TopologicalSpace C] [Nonempty U]
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι) :
    (b6a_openEmbeddingInverse U C ι hι).source = Set.range ι := by
  simp [b6a_openEmbeddingInverse]

theorem b6a_openEmbeddingInverse_apply (U C : Type)
    [TopologicalSpace U] [TopologicalSpace C] [Nonempty U]
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι) (u : U) :
    b6a_openEmbeddingInverse U C ι hι (ι u) = u := by
  exact hι.toOpenPartialHomeomorph_left_inv ι

noncomputable def b6a_unramifiedChart (b : Fin 10 → ℂ) (G U C : Type)
    [Group G] [TopologicalSpace U] [MulAction G U] [TopologicalSpace C] [Nonempty U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G)
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι) (u : U) :
    OpenPartialHomeomorph C (b6t_punctured b) :=
  (b6a_openEmbeddingInverse U C ι hι).trans (b6a_coverChart b G U π hπ u)

theorem b6a_mem_unramifiedChart_source (b : Fin 10 → ℂ) (G U C : Type)
    [Group G] [TopologicalSpace U] [MulAction G U] [TopologicalSpace C] [Nonempty U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G)
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι) (u : U) :
    ι u ∈ (b6a_unramifiedChart b G U C π hπ ι hι u).source := by
  simp [b6a_unramifiedChart, b6a_openEmbeddingInverse_apply,
    b6a_mem_coverChart_source]

theorem b6a_unramifiedChart_apply (b : Fin 10 → ℂ) (G U C : Type)
    [Group G] [TopologicalSpace U] [MulAction G U] [TopologicalSpace C] [Nonempty U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G)
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι) (u u' : U) :
    b6a_unramifiedChart b G U C π hπ ι hι u (ι u') = π u' := by
  simp [b6a_unramifiedChart, b6a_openEmbeddingInverse_apply, ← b6a_coverChart_eq]

noncomputable def b6a_unramifiedComplexChart (b : Fin 10 → ℂ) (G U C : Type)
    [Group G] [TopologicalSpace U] [MulAction G U] [TopologicalSpace C] [Nonempty U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G)
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι) (u : U) :
    OpenPartialHomeomorph C ℂ :=
  (b6a_unramifiedChart b G U C π hπ ι hι u).trans (b6a_puncturedComplexChart b)

theorem b6a_unramifiedComplexChart_coe (b : Fin 10 → ℂ) (G U C : Type)
    [Group G] [TopologicalSpace U] [MulAction G U] [TopologicalSpace C] [Nonempty U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G)
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι) (u u' : U) :
    ((b6a_unramifiedComplexChart b G U C π hπ ι hι u (ι u') : ℂ) : OnePoint ℂ) =
      (π u').val := by
  rw [b6a_unramifiedComplexChart, OpenPartialHomeomorph.trans_apply,
    b6a_unramifiedChart_apply]
  exact b6a_puncturedComplexChart_coe b (π u')

noncomputable def b6a_parameterChart (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) :
    OpenPartialHomeomorph (b6t_polydisc b) (Fin 10 → ℂ) :=
  let h := b6t_polydisc_neighbourhood b hb
  let s : TopologicalSpace.Opens (Fin 10 → ℂ) := ⟨b6t_polydisc b, h.2.2.1⟩
  s.openPartialHomeomorphSubtypeCoe h.2.1.to_subtype

@[simp] theorem b6a_parameterChart_apply (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (t : b6t_polydisc b) : b6a_parameterChart b hb t = t.val := rfl

@[simp] theorem b6a_parameterChart_source (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) :
    (b6a_parameterChart b hb).source = Set.univ := rfl

noncomputable def b6a_productChart (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (C : Type) [TopologicalSpace C] (P : OpenPartialHomeomorph C ℂ) :
    OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ) :=
  (b6a_parameterChart b hb).prod P

@[simp] theorem b6a_productChart_apply (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (C : Type) [TopologicalSpace C] (P : OpenPartialHomeomorph C ℂ)
    (q : b6t_polydisc b × C) :
    b6a_productChart b hb C P q = (q.1.val, P q.2) := rfl

@[simp] theorem b6a_productChart_source (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (C : Type) [TopologicalSpace C] (P : OpenPartialHomeomorph C ℂ) :
    (b6a_productChart b hb C P).source = Set.univ ×ˢ P.source := by
  ext q
  simp [b6a_productChart]

theorem b6a_projection_proper (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C] [CompactSpace C] :
    IsProperMap (fun q : b6t_polydisc b × C ↦ q.1) :=
  isProperMap_fst_of_compactSpace

theorem b6a_total_action_eq (b : Fin 10 → ℂ) (G C : Type)
    [Group G] [TopologicalSpace C] [MulAction G C] (g : G) :
    (fun q : b6t_polydisc b × C ↦ (q.1, g • q.2)) =
      Prod.map id (fun x : C ↦ g • x) := rfl

theorem b6a_total_action_preserves_map (b : Fin 10 → ℂ) (G C : Type)
    [Group G] [MulAction G C] (f : C → OnePoint ℂ)
    (hgal : b4_IsGaloisCover G f) (g : G) (q : b6t_polydisc b × C) :
    b6a_map b f (q.1, g • q.2) = b6a_map b f q := by
  simp only [b6a_map, hgal.1 g q.2]

def b6a_sphereTransport (b : Fin 10 → ℂ) :
    b6t_polydisc b × OnePoint ℂ → b6t_polydisc b × OnePoint ℂ :=
  fun q ↦ (q.1, b6t_sphere b q.1.val q.2)

theorem b6a_sphereTransport_continuous (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) :
    Continuous (b6a_sphereTransport b) :=
  continuous_fst.prodMk (b6t_continuous b hb)

theorem b6a_sphereTransport_bijective (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) :
    Function.Bijective (b6a_sphereTransport b) := by
  constructor
  · rintro ⟨t, x⟩ ⟨t', x'⟩ h
    have ht : t = t' := congrArg Prod.fst h
    subst t'
    obtain ⟨e, he⟩ := b6t_homeomorph b hb t.val t.property
    refine Prod.ext rfl ?_
    apply e.injective
    simpa [b6a_sphereTransport, he] using congrArg Prod.snd h
  · rintro ⟨t, y⟩
    obtain ⟨e, he⟩ := b6t_homeomorph b hb t.val t.property
    refine ⟨(t, e.symm y), ?_⟩
    simp [b6a_sphereTransport, ← he]

theorem b6a_sphereTransport_isProperMap (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) :
    IsProperMap (b6a_sphereTransport b) := by
  apply isProperMap_of_comp_of_t2 (b6a_sphereTransport_continuous b hb) continuous_fst
  simpa [Function.comp_def, b6a_sphereTransport] using
    (isProperMap_fst_of_compactSpace :
      IsProperMap (fun q : b6t_polydisc b × OnePoint ℂ ↦ q.1))

theorem b6a_sphereTransport_isHomeomorph (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) :
    IsHomeomorph (b6a_sphereTransport b) :=
  isHomeomorph_iff_continuous_isClosedMap_bijective.2
    ⟨b6a_sphereTransport_continuous b hb,
      (b6a_sphereTransport_isProperMap b hb).isClosedMap,
      b6a_sphereTransport_bijective b hb⟩

theorem b6a_fibre_surjective (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (C : Type) (f : C → OnePoint ℂ) (hf : Function.Surjective f)
    (t : b6t_polydisc b) :
    Function.Surjective (fun x : C ↦ b6a_map b f (t, x)) := by
  intro y
  obtain ⟨z, hz⟩ := (b6t_homeomorph b hb t.val t.property).choose.surjective y
  obtain ⟨x, rfl⟩ := hf z
  exact ⟨x, by
    simpa [b6a_map, (b6t_homeomorph b hb t.val t.property).choose_spec] using hz⟩

theorem b6a_fibre_galois (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G C : Type) [Group G] [MulAction G C] (f : C → OnePoint ℂ)
    (hf : b4_IsGaloisCover G f) (t : b6t_polydisc b) :
    b4_IsGaloisCover G (fun x : C ↦ b6a_map b f (t, x)) := by
  obtain ⟨e, he⟩ := b6t_homeomorph b hb t.val t.property
  constructor
  · intro g x
    simp only [b6a_map, hf.1 g x]
  · intro x x' h
    apply hf.2 x x'
    apply e.injective
    simpa [b6a_map, he] using h

theorem b6a_fibre_branch_preimage (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (C : Type) (f : C → OnePoint ℂ) (t : b6t_polydisc b) :
    (fun x : C ↦ b6a_map b f (t, x)) ⁻¹' (Set.range (b6_branch t.val)) =
      f ⁻¹' (Set.range (b6_branch b)) := by
  ext x
  constructor
  · rintro ⟨j, hj⟩
    change b6_branch t.val j = b6t_sphere b t.val (f x) at hj
    refine ⟨j, ?_⟩
    apply (b6t_homeomorph b hb t.val t.property).choose.injective
    rw [(b6t_homeomorph b hb t.val t.property).choose_spec,
      (b6t_homeomorph b hb t.val t.property).choose_spec]
    exact (b6t_marks b hb t.val t.property j).trans hj
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    change b6_branch t.val j = b6t_sphere b t.val (f x)
    rw [← hj]
    exact (b6t_marks b hb t.val t.property j).symm

theorem b6a_fibre_punctured_range (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (U C : Type) (f : C → OnePoint ℂ) (ι : U → C)
    (hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ)
    (t : b6t_polydisc b) :
    Set.range ι = (fun x : C ↦ b6a_map b f (t, x)) ⁻¹'
      (Set.range (b6_branch t.val))ᶜ := by
  rw [Set.preimage_compl, b6a_fibre_branch_preimage b hb C f t]
  exact hrange

theorem b6a_fibre_projection (b : Fin 10 → ℂ) (U C : Type)
    (π : U → b6t_punctured b) (f : C → OnePoint ℂ) (ι : U → C)
    (hproj : ∀ u, f (ι u) = π u) (t : b6t_polydisc b) :
    ∀ u, b6a_map b f (t, ι u) = b6t_projection b t.val π u := by
  intro u
  simp [b6a_map, b6t_projection, hproj]

noncomputable def b6a_sphereTransportHomeomorph (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) :
    b6t_polydisc b × OnePoint ℂ ≃ₜ b6t_polydisc b × OnePoint ℂ :=
  IsHomeomorph.homeomorph (b6a_sphereTransport b) (b6a_sphereTransport_isHomeomorph b hb)

@[simp] theorem b6a_sphereTransportHomeomorph_apply (b : Fin 10 → ℂ)
    (hb : b ∈ b6_chart) (q : b6t_polydisc b × OnePoint ℂ) :
    b6a_sphereTransportHomeomorph b hb q =
      (q.1, b6t_sphere b q.1.val q.2) := rfl

noncomputable def b6a_planeTransportHom (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) :
    OpenPartialHomeomorph (b6t_polydisc b × ℂ) (b6t_polydisc b × ℂ) :=
  ((OpenPartialHomeomorph.refl (b6t_polydisc b)).prod b6a_finiteSphereChart.symm).trans
    ((b6a_sphereTransportHomeomorph b hb).toOpenPartialHomeomorph.trans
      ((OpenPartialHomeomorph.refl (b6t_polydisc b)).prod b6a_finiteSphereChart))

@[simp] theorem b6a_planeTransportHom_apply (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (t : b6t_polydisc b) (z : ℂ) :
    b6a_planeTransportHom b hb (t, z) = (t, b6t_plane b t.val z) := by
  simp [b6a_planeTransportHom, b6t_sphere]

@[simp] theorem b6a_planeTransportHom_source (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) :
    (b6a_planeTransportHom b hb).source = Set.univ := by
  ext q
  rcases q with ⟨t, z⟩
  simp [b6a_planeTransportHom, b6t_sphere]

noncomputable def b6a_totalUnramifiedChart (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G U C : Type) [Group G] [TopologicalSpace U] [MulAction G U]
    [TopologicalSpace C] [Nonempty U] (π : U → b6t_punctured b)
    (hπ : IsQuotientCoveringMap π G) (ι : U → C)
    (hι : Topology.IsOpenEmbedding ι) (u : U) :
    OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ) :=
  (((OpenPartialHomeomorph.refl (b6t_polydisc b)).prod
      (b6a_unramifiedComplexChart b G U C π hπ ι hι u)).trans
    (b6a_planeTransportHom b hb)).trans
      ((b6a_parameterChart b hb).prod (OpenPartialHomeomorph.refl ℂ))

theorem b6a_totalUnramifiedChart_apply (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G U C : Type) [Group G] [TopologicalSpace U] [MulAction G U]
    [TopologicalSpace C] [Nonempty U] (π : U → b6t_punctured b)
    (hπ : IsQuotientCoveringMap π G) (ι : U → C)
    (hι : Topology.IsOpenEmbedding ι) (u u' : U) (t : b6t_polydisc b) :
    b6a_totalUnramifiedChart b hb G U C π hπ ι hι u (t, ι u') =
      (t.val, b6t_plane b t.val
        (b6a_unramifiedComplexChart b G U C π hπ ι hι u (ι u'))) := by
  simp [b6a_totalUnramifiedChart]

theorem b6a_totalUnramifiedChart_map (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G U C : Type) [Group G] [TopologicalSpace U] [MulAction G U]
    [TopologicalSpace C] [Nonempty U] (π : U → b6t_punctured b)
    (hπ : IsQuotientCoveringMap π G) (ι : U → C)
    (hι : Topology.IsOpenEmbedding ι) (f : C → OnePoint ℂ)
    (hf : ∀ u, f (ι u) = π u) (u : U) (q : b6t_polydisc b × C)
    (hq : q ∈ (b6a_totalUnramifiedChart b hb G U C π hπ ι hι u).source) :
    b6a_map b f q =
      ((b6a_totalUnramifiedChart b hb G U C π hπ ι hι u q).2 : OnePoint ℂ) := by
  have hx : q.2 ∈ Set.range ι := by
    have h := hq.1.1.2.1.1
    change q.2 ∈ (b6a_openEmbeddingInverse U C ι hι).source at h
    simpa only [b6a_openEmbeddingInverse_source] using h
  obtain ⟨v, hv⟩ := hx
  rcases q with ⟨t, x⟩
  dsimp at hv
  subst x
  rw [b6a_totalUnramifiedChart_apply]
  change b6t_sphere b t.val (f (ι v)) = _
  rw [hf v, ← b6a_unramifiedComplexChart_coe b G U C π hπ ι hι u v]
  rfl

theorem b6a_constant_fibre_not_surjective (b : Fin 10 → ℂ) (C : Type)
    (y : OnePoint ℂ) (t : b6t_polydisc b) :
    ¬ Function.Surjective (fun x : C ↦ b6a_map b (fun _ : C ↦ y) (t, x)) := by
  intro h
  obtain ⟨z, hz⟩ := exists_ne (b6t_sphere b t.val y)
  obtain ⟨x, hx⟩ := h z
  exact hz hx.symm

end HodgeLean.Foundations.Program
