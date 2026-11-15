import HodgeLean.Foundations.Program.ComponentTransportDefs
import HodgeLean.Foundations.Program.NamedLoopFamilyCover

/-! # Certified chain: edges, walks and local continuation
Single edges between retained charts, finite walks of edges and their conversion to a
`b65y_HurwitzChain`; the glue of two retained charts whose transported covers have equal based
monodromy at a common configuration; continuation of a retained chart to a configuration of its
polydisc. No lattice comparison is part of this data.
HC no distance; AV milestone no distance.
-/
noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

/-- One edge of a geometric chart chain: a common configuration of the two polydiscs and an
equivariant biholomorphism of the two filled fibres there.
Source: `b65y_HurwitzChain`; G32 v0.16, §3.1 and proof of Lemma 3.4. -/
structure b65y_Edge (d₀ d₁ : b65y_Chart) where
  t : b6t_polydisc d₀.1
  ht₁ : t.val ∈ b6t_polydisc d₁.1
  glue : b65z_fibre d₀.1 d₀.2.2.C t ≃ₜ b65z_fibre d₁.1 d₁.2.2.C ⟨t.val, ht₁⟩
  hol : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω glue
  inv_hol : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω glue.symm
  equivariant : ∀ (g : b4b_Group) x, glue (g • x) = g • glue x

/-- The identity edge of a chart at its own centre. -/
def b65y_Edge.refl (d : b65y_Chart) : b65y_Edge d d where
  t := b65z_s₀ d.1
  ht₁ := b65z_centre_mem d.1
  glue := Homeomorph.refl _
  hol := contMDiff_id
  inv_hol := contMDiff_id
  equivariant _ _ := rfl

/-- A finite walk of edges between retained charts.
Source: `b65y_HurwitzChain`; finite composition of chart edges. -/
inductive b65y_Walk : b65y_Chart → b65y_Chart → Type 1
  | nil (d : b65y_Chart) : b65y_Walk d d
  | cons {d₀ d₁ d₂ : b65y_Chart} : b65y_Edge d₀ d₁ → b65y_Walk d₁ d₂ → b65y_Walk d₀ d₂

/-- Concatenation of walks. -/
def b65y_Walk.append : {d₀ d₁ d₂ : b65y_Chart} → b65y_Walk d₀ d₁ → b65y_Walk d₁ d₂ →
    b65y_Walk d₀ d₂
  | _, _, _, .nil _, w => w
  | _, _, _, .cons e v, w => .cons e (v.append w)

example (d : b65y_Chart) : b65y_Walk d d := .cons (b65y_Edge.refl d) (.nil d)

/-- Prepending an edge to a chart chain. -/
def b65y_chainCons (d : b65y_Chart) (H : b65y_HurwitzChain) (E : b65y_Edge d (H.chart 0)) :
    b65y_HurwitzChain where
  n := H.n + 1
  chart := Fin.cons (α := fun _ ↦ b65y_Chart) d H.chart
  overlap i := Fin.cases (motive := fun i : Fin (H.n + 1) ↦ {t : Fin 10 → ℂ //
      t ∈ b6t_polydisc (Fin.cons (α := fun _ ↦ b65y_Chart) d H.chart i.castSucc : b65y_Chart).1 ∧
      t ∈ b6t_polydisc (Fin.cons (α := fun _ ↦ b65y_Chart) d H.chart i.succ : b65y_Chart).1})
    ⟨E.t.val, E.t.property, E.ht₁⟩ (fun j ↦ H.overlap j) i
  glue i := by
    induction i using Fin.cases with
    | zero => exact E.glue
    | succ j => exact H.glue j
  hol i := by
    induction i using Fin.cases with
    | zero => exact E.hol
    | succ j => exact H.hol j
  inv_hol i := by
    induction i using Fin.cases with
    | zero => exact E.inv_hol
    | succ j => exact H.inv_hol j
  equivariant i := by
    induction i using Fin.cases with
    | zero => exact E.equivariant
    | succ j => exact H.equivariant j

/-- A walk of edges gives a geometric chart chain with the same end charts.
Source: `b65y_HurwitzChain`; induction on the walk. -/
theorem b65y_chain_of_walk {d₀ d₁ : b65y_Chart} (w : b65y_Walk d₀ d₁) :
    ∃ H : b65y_HurwitzChain, H.chart 0 = d₀ ∧ H.chart (Fin.last H.n) = d₁ := by
  induction w with
  | nil d =>
    exact ⟨⟨0, fun _ ↦ d, (fun i ↦ i.elim0), (fun i ↦ i.elim0), (fun i ↦ i.elim0),
      (fun i ↦ i.elim0), (fun i ↦ i.elim0)⟩, rfl, rfl⟩
  | @cons a b c E v ih =>
    obtain ⟨H, h0, h1⟩ := ih
    subst h0 h1
    exact ⟨b65y_chainCons a H E, rfl, rfl⟩

/-- Two retained charts whose transported covers have equal based monodromy at a common
configuration are joined by an edge there.
Source: `b6m_based_filling_comparison` (Hatcher, Theorem 1.38; Forster, Theorem 8.4);
`b63g5_fibre_filling`; Harris–Morrison, *Moduli of Curves*, §1.G. -/
theorem b65y_edge_of_monodromy {c₁ c₂ : Fin 10 → ℂ} {g₁ g₂ : Fin 13 → b4b_Group}
    (D₁ : b65z_SharedFamily c₁ g₁) (D₂ : b65z_SharedFamily c₂ g₂)
    (t : b6t_polydisc c₁) (ht₂ : t.val ∈ b6t_polydisc c₂)
    (e₁ : b6t_punctured c₁ ≃ₜ b6t_punctured t.val)
    (he₁ : ∀ x, (e₁ x : OnePoint ℂ) = b6t_sphere c₁ t.val x)
    (e₂ : b6t_punctured c₂ ≃ₜ b6t_punctured t.val)
    (he₂ : ∀ x, (e₂ x : OnePoint ℂ) = b6t_sphere c₂ t.val x)
    (x : b6t_punctured t.val) (u₁ : (e₁ ∘ D₁.atlas.π) ⁻¹' {x})
    (u₂ : (e₂ ∘ D₂.atlas.π) ⁻¹' {x})
    (h : (D₁.atlas.hπ.homeomorph_comp e₁).fundamentalGroupToMulOpposite u₁ =
      (D₂.atlas.hπ.homeomorph_comp e₂).fundamentalGroupToMulOpposite u₂) :
    Nonempty (b65y_Edge ⟨c₁, g₁, D₁⟩ ⟨c₂, g₂, D₂⟩) := by
  have hb : t.val ∈ b6_chart := (b6t_polydisc_neighbourhood c₁ D₁.atlas.hb).2.2.2 t.property
  obtain ⟨hι₁, hr₁⟩ := b63g5_fibre_filling c₁ D₁.atlas.hb D₁.atlas.f D₁.atlas.ι D₁.atlas.hι
    D₁.atlas.hrange (b6t_polydisc c₁) (Subset.refl _) t
  obtain ⟨hι₂, hr₂⟩ := b63g5_fibre_filling c₂ D₂.atlas.hb D₂.atlas.f D₂.atlas.ι D₂.atlas.hι
    D₂.atlas.hrange (b6t_polydisc c₂) (Subset.refl _) ⟨t.val, ht₂⟩
  obtain ⟨-, -, -, -, E, hE, hE', -, -, hEg, -⟩ := b6m_based_filling_comparison t.val hb
    b4b_Group D₁.atlas.U D₂.atlas.U (e₁ ∘ D₁.atlas.π) (e₂ ∘ D₂.atlas.π)
    (D₁.atlas.hπ.homeomorph_comp e₁) (D₂.atlas.hπ.homeomorph_comp e₂) x u₁ u₂ h
    (b65z_fibre c₁ D₁.C t) (b65z_fibre c₂ D₂.C ⟨t.val, ht₂⟩)
    (b63d_projection c₁ D₁.C D₁.atlas.f (b6t_polydisc c₁) (Subset.refl _) t)
    (b63d_projection c₂ D₂.C D₂.atlas.f (b6t_polydisc c₂) (Subset.refl _) ⟨t.val, ht₂⟩)
    (b63g5_fibreMap c₁ D₁.atlas.ι (b6t_polydisc c₁) (Subset.refl _) t)
    (b63g5_fibreMap c₂ D₂.atlas.ι (b6t_polydisc c₂) (Subset.refl _) ⟨t.val, ht₂⟩)
    (D₁.hk t) (D₂.hk ⟨t.val, ht₂⟩) hι₁ hι₂ hr₁ hr₂
    (fun u ↦ by
      simp only [b63d_projection, b63g5_fibreMap, b6a_map, Function.comp_apply, he₁,
        D₁.atlas.hproj])
    (fun u ↦ by
      simp only [b63d_projection, b63g5_fibreMap, b6a_map, Function.comp_apply, he₂,
        D₂.atlas.hproj])
    (fun g u ↦ Subtype.ext (Prod.ext rfl (D₁.atlas.hequiv g u)))
    (fun g u ↦ Subtype.ext (Prod.ext rfl (D₂.atlas.hequiv g u)))
    (fun g ↦ (D₁.hG t g).continuous) (fun g ↦ (D₂.hG ⟨t.val, ht₂⟩ g).continuous)
  exact ⟨⟨t, ht₂, E, hE, hE', hEg⟩⟩

/-- Continuation of a retained chart to a configuration of its polydisc: a retained chart at
that configuration whose cover is the radially transported cover, with the same based monodromy,
joined to the given chart by an edge.
Source: `b65w_family_of_cover`, `b65z_rot_transfer`, `b6t_punctured_homeomorph`,
`b65y_edge_of_monodromy`; Harris–Morrison, *Moduli of Curves*, §1.G. -/
theorem b65y_edge_step {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (hne : ∀ j, g j ≠ 1)
    (D : b65z_SharedFamily c g) (s : b6t_polydisc c)
    (y₀ : b6t_punctured c) (u₀ : D.atlas.π ⁻¹' {y₀}) :
    ∃ e : b6t_punctured c ≃ₜ b6t_punctured s.val,
      (∀ x, (e x : OnePoint ℂ) = b6t_sphere c s.val x) ∧
    ∃ D' : b65z_SharedFamily s.val g, ∃ u : D'.atlas.π ⁻¹' {e y₀},
      D'.atlas.hπ.fundamentalGroupToMulOpposite u =
        (D.atlas.hπ.homeomorph_comp e).fundamentalGroupToMulOpposite
          ⟨u₀.val, congrArg e u₀.property⟩ ∧
      Nonempty (b65y_Edge ⟨c, g, D⟩ ⟨s.val, g, D'⟩) := by
  have hc : c ∈ b6_chart := D.atlas.hb
  have hs : s.val ∈ b6_chart := (b6t_polydisc_neighbourhood c hc).2.2.2 s.property
  obtain ⟨e, he⟩ := b6t_punctured_homeomorph c hc s.val s.property
  refine ⟨e, he, ?_⟩
  have hπ' := D.atlas.hπ.homeomorph_comp e
  obtain ⟨hι₀, hr₀⟩ := b63g5_fibre_filling c hc D.atlas.f D.atlas.ι D.atlas.hι
    D.atlas.hrange (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)
  obtain ⟨-, hfreeC⟩ := rf8_filling_stabilizers c D.atlas.U D.C D.atlas.π D.atlas.hπ u₀.val
    D.atlas.f D.atlas.ι D.atlas.hι.injective D.atlas.hrange D.atlas.hequiv
  obtain ⟨-, -, hfree₀⟩ := b63g5_fibre_galois c hc D.C D.atlas.f D.atlas.hgal D.atlas.hsurj
    hfreeC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)
  have hpos : ∀ (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
      [T2Space C] [CompactSpace C] [ConnectedSpace C] [MulAction b4b_Group C]
      [FaithfulSMul b4b_Group C],
      (∀ k : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ k • x)) →
      ∀ f : C → OnePoint ℂ, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f → b4_IsGaloisCover b4b_Group f →
      (∀ x, f x ∉ Set.range (b6_branch s.val) → MulAction.stabilizer b4b_Group x = ⊥) →
      ∀ ι : D.atlas.U → C, Continuous ι → (∀ u, f (ι u) = (e ∘ D.atlas.π) u) →
      (∀ (k : b4b_Group) (u : D.atlas.U), ι (k • u) = k • ι u) →
      ∀ j, ∃ x, f x = b6_branch s.val j ∧ b4_IsRotGen ℂ x (g j) := by
    intro C _ _ _ _ _ _ _ _ hG₂ f₂ hf₂ hgal₂ hfree₂ ι₂ hι₂ hfι₂ hιeq₂ j
    exact b65z_rot_transfer c hc g s.val s.property D.atlas.π D.atlas.hπ
      (D.hG (b65z_s₀ c))
      (b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c))
      (D.hk (b65z_s₀ c)) (D.hgal (b65z_s₀ c)) hfree₀
      (b63g5_fibreMap c D.atlas.ι (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c))
      hι₀.continuous
      (fun u ↦ by
        simp only [b63d_projection, b63g5_fibreMap, b6a_map, D.atlas.hproj]
        exact congrFun (b6t_identity c) _)
      (fun k u ↦ Subtype.ext (Prod.ext rfl (D.atlas.hequiv k u)))
      (D.hrot (b65z_s₀ c)) hG₂ f₂ hf₂ hgal₂ hfree₂ ι₂ hι₂
      (fun u ↦ by rw [hfι₂ u, Function.comp_apply, he]) hιeq₂ j
  obtain ⟨D', u, hu⟩ := b65w_family_of_cover s.val hs g hne D.atlas.U (e ∘ D.atlas.π) hπ' hpos
    (e y₀) ⟨u₀.val, congrArg e u₀.property⟩
  refine ⟨D', u, hu, ?_⟩
  obtain ⟨e₂, he₂⟩ := b6t_punctured_homeomorph s.val hs s.val (b65z_centre_mem s.val)
  have he₂id : e₂ = Homeomorph.refl _ := by
    ext x
    rw [he₂, b6t_identity]
    rfl
  subst he₂id
  exact b65y_edge_of_monodromy D D' s (b65z_centre_mem s.val) e he (Homeomorph.refl _) he₂
    (e y₀) ⟨u₀.val, congrArg e u₀.property⟩ u hu.symm

/-- Two retained charts at one centre with equal based monodromy at lifts of a common point are
joined by an edge at the centre.
Source: `b65y_edge_of_monodromy`; `b6t_identity`. -/
theorem b65y_edge_terminal {c : Fin 10 → ℂ} {g₁ g₂ : Fin 13 → b4b_Group}
    (D₁ : b65z_SharedFamily c g₁) (D₂ : b65z_SharedFamily c g₂)
    (y : b6t_punctured c) (u₁ : D₁.atlas.π ⁻¹' {y}) (u₂ : D₂.atlas.π ⁻¹' {y})
    (h : D₁.atlas.hπ.fundamentalGroupToMulOpposite u₁ =
      D₂.atlas.hπ.fundamentalGroupToMulOpposite u₂) :
    Nonempty (b65y_Edge ⟨c, g₁, D₁⟩ ⟨c, g₂, D₂⟩) := by
  obtain ⟨e, he⟩ := b6t_punctured_homeomorph c D₁.atlas.hb c (b65z_centre_mem c)
  have heid : e = Homeomorph.refl _ := by
    ext x
    rw [he, b6t_identity]
    rfl
  subst heid
  exact b65y_edge_of_monodromy D₁ D₂ (b65z_s₀ c) (b65z_centre_mem c) (Homeomorph.refl _) he
    (Homeomorph.refl _) he y u₁ u₂ h

/-- Monodromy of a cover composed with a homeomorphism of its base.
Source: Mathlib `IsCoveringMap.monodromy_eq_of_map_eq`, `map_liftPathQuotient`. -/
theorem b65y_homeomorph_comp_monodromy
    {X Y U G : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace U]
    [Group G] [MulAction G U] (p : U → X) (hp : IsQuotientCoveringMap p G)
    (e : X ≃ₜ Y) (x : X) (u : p ⁻¹' {x}) :
    ((hp.homeomorph_comp e).fundamentalGroupToMulOpposite
      ⟨u.val, congrArg e u.property⟩).comp
      (FundamentalGroup.map ⟨e, e.continuous⟩ x) =
      hp.fundamentalGroupToMulOpposite u := by
  ext γ
  rw [MonoidHom.comp_apply]
  rw [IsQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_iff]
  let m := hp.isCoveringMap.monodromy γ.asHom u
  let m' : (e ∘ p) ⁻¹' {e x} := ⟨m.val, congrArg e m.property⟩
  change ((hp.fundamentalGroupToMulOpposite u γ).unop • u.val) =
    ((hp.homeomorph_comp e).isCoveringMap.monodromy
      ((FundamentalGroup.map ⟨e, e.continuous⟩ x) γ).asHom
      ⟨u.val, congrArg e u.property⟩).val
  rw [hp.unop_fundamentalGroupToMulOpposite_smul]
  change m.val = _
  have hm : (hp.homeomorph_comp e).isCoveringMap.monodromy
      ((FundamentalGroup.map ⟨e, e.continuous⟩ x) γ).asHom
      ⟨u.val, congrArg e u.property⟩ = m' := by
    apply (hp.homeomorph_comp e).isCoveringMap.monodromy_eq_of_map_eq
      (hp.isCoveringMap.liftPathQuotient γ.asHom u)
    change (hp.isCoveringMap.liftPathQuotient γ.asHom u).map
      ((⟨e, e.continuous⟩ : C(X, Y)).comp ⟨p, hp.continuous⟩) = _
    rw [Path.Homotopic.Quotient.map_comp, hp.isCoveringMap.map_liftPathQuotient]
    exact Path.Homotopic.Quotient.map_cast γ.asHom
  exact congrArg Subtype.val hm.symm

/-- The fundamental-group map of a composite homeomorphism.
Source: Mathlib `FundamentalGroup.map`; functoriality of the fundamental groupoid. -/
theorem b65y_map_trans {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (Φ : X ≃ₜ Y) (e : Y ≃ₜ Z) (y : X) :
    FundamentalGroup.map ⟨Φ.trans e, (Φ.trans e).continuous⟩ y =
      (FundamentalGroup.map ⟨e, e.continuous⟩ (Φ y)).comp
        (FundamentalGroup.map ⟨Φ, Φ.continuous⟩ y) := by
  ext a
  obtain ⟨γ, hγ⟩ := Quotient.exists_rep a.asHom
  have ha : a = FundamentalGroup.fromPath ⟦γ⟧ := by
    rw [show (⟦γ⟧ : Path.Homotopic.Quotient _ _) = a.asHom from hγ]
  subst ha
  rfl

/-- The fundamental-group map of the identity homeomorphism. -/
theorem b65y_map_refl {X : Type} [TopologicalSpace X] (y : X) :
    FundamentalGroup.map ⟨Homeomorph.refl X, (Homeomorph.refl X).continuous⟩ y =
      MonoidHom.id _ := by
  ext a
  obtain ⟨γ, hγ⟩ := Quotient.exists_rep a.asHom
  have ha : a = FundamentalGroup.fromPath ⟦γ⟧ := by
    rw [show (⟦γ⟧ : Path.Homotopic.Quotient _ _) = a.asHom from hγ]
  subst ha
  rfl

/-- The composite of the radial pushes along a finite sequence of configurations.
Source: `b6t_sphere`; finite composition. -/
def b65y_radial (c : ℕ → Fin 10 → ℂ) : ℕ → OnePoint ℂ → OnePoint ℂ
  | 0 => id
  | k + 1 => b6t_sphere (c k) (c (k + 1)) ∘ b65y_radial c k

example (c : ℕ → Fin 10 → ℂ) : b65y_radial c 0 = id := rfl

/-- Continuation of a retained chart along a finite sequence of configurations, each in the
polydisc of the previous one: a walk of retained charts whose last cover carries the based
monodromy of the first through the composite radial homeomorphism.
Source: `b65y_edge_step`, `b65y_homeomorph_comp_monodromy`; Harris–Morrison, *Moduli of
Curves*, §1.G. -/
theorem b65y_walk_radial {g : Fin 13 → b4b_Group} (hne : ∀ j, g j ≠ 1)
    (c : ℕ → Fin 10 → ℂ) (N : ℕ) (hc : ∀ k < N, c (k + 1) ∈ b6t_polydisc (c k))
    (D₀ : b65z_SharedFamily (c 0) g) (y₀ : b6t_punctured (c 0)) (u₀ : D₀.atlas.π ⁻¹' {y₀}) :
    ∃ Φ : b6t_punctured (c 0) ≃ₜ b6t_punctured (c N),
      (∀ x, (Φ x : OnePoint ℂ) = b65y_radial c N x) ∧
    ∃ D : b65z_SharedFamily (c N) g, ∃ u : D.atlas.π ⁻¹' {Φ y₀},
      (D.atlas.hπ.fundamentalGroupToMulOpposite u).comp
        (FundamentalGroup.map ⟨Φ, Φ.continuous⟩ y₀) =
        D₀.atlas.hπ.fundamentalGroupToMulOpposite u₀ ∧
      Nonempty (b65y_Walk ⟨c 0, g, D₀⟩ ⟨c N, g, D⟩) := by
  induction N with
  | zero =>
    refine ⟨Homeomorph.refl _, fun x ↦ rfl, D₀, u₀, ?_, ⟨.nil _⟩⟩
    rw [b65y_map_refl]
    rfl
  | succ N ih =>
    obtain ⟨Φ, hΦ, D, u, hmon, ⟨w⟩⟩ := ih (fun k hk ↦ hc k (by omega))
    obtain ⟨e, he, D', u', hu', ⟨E⟩⟩ :=
      b65y_edge_step hne D ⟨c (N + 1), hc N (by omega)⟩ (Φ y₀) u
    refine ⟨Φ.trans e, fun x ↦ ?_, D', u', ?_, ⟨w.append (.cons E (.nil _))⟩⟩
    · change (e (Φ x) : OnePoint ℂ) = b6t_sphere (c N) (c (N + 1)) (b65y_radial c N x)
      rw [he, hΦ]
    · rw [b65y_map_trans]
      change ((D'.atlas.hπ.fundamentalGroupToMulOpposite u').comp
        (FundamentalGroup.map ⟨e, e.continuous⟩ (Φ y₀))).comp
          (FundamentalGroup.map ⟨Φ, Φ.continuous⟩ y₀) = _
      rw [hu', b65y_homeomorph_comp_monodromy _ D.atlas.hπ, hmon]

/-- The fundamental-group map of a homeomorphism is onto.
Source: `RiemannRochTop_homeomorph_pi1_map`; Mathlib `FundamentalGroupoidFunctor.equivOfHomotopyEquiv`. -/
theorem b65y_map_surjective {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (Φ : X ≃ₜ Y) (y : X) :
    Function.Surjective (FundamentalGroup.map ⟨Φ, Φ.continuous⟩ y) := by
  obtain ⟨χ, hχ⟩ := RiemannRochTop_homeomorph_pi1_map Φ y
  intro b
  obtain ⟨a, rfl⟩ := χ.surjective b
  refine ⟨a, ?_⟩
  obtain ⟨γ, hγ⟩ := Quotient.exists_rep a.asHom
  have ha : a = FundamentalGroup.fromPath ⟦γ⟧ := by
    rw [show (⟦γ⟧ : Path.Homotopic.Quotient _ _) = a.asHom from hγ]
  rw [ha, hχ]
  rfl

/-- A finite radial sequence of configurations whose composite carries the based monodromy of
the first retained chart to that of a given retained chart at the last configuration yields a
walk between the two charts.
Source: `b65y_walk_radial`, `b65y_edge_terminal`, `b65y_map_surjective`. -/
theorem b65y_walk_of_radial {g₁ g₂ : Fin 13 → b4b_Group} (hne : ∀ j, g₁ j ≠ 1)
    {c₀ c₁ : Fin 10 → ℂ} (c : ℕ → Fin 10 → ℂ) (N : ℕ) (h0 : c 0 = c₀) (hN : c N = c₁)
    (hc : ∀ k < N, c (k + 1) ∈ b6t_polydisc (c k))
    (D₀ : b65z_SharedFamily c₀ g₁) (D : b65z_SharedFamily c₁ g₂)
    (y₀ : b6t_punctured c₀) (u₀ : D₀.atlas.π ⁻¹' {y₀})
    (Φ : b6t_punctured c₀ ≃ₜ b6t_punctured c₁)
    (hΦ : ∀ x, (Φ x : OnePoint ℂ) = b65y_radial c N x)
    (w : D.atlas.π ⁻¹' {Φ y₀})
    (hw : (D.atlas.hπ.fundamentalGroupToMulOpposite w).comp
      (FundamentalGroup.map ⟨Φ, Φ.continuous⟩ y₀) =
      D₀.atlas.hπ.fundamentalGroupToMulOpposite u₀) :
    Nonempty (b65y_Walk ⟨c₀, g₁, D₀⟩ ⟨c₁, g₂, D⟩) := by
  subst h0 hN
  obtain ⟨Φ', hΦ', D', u', hmon, ⟨wk⟩⟩ := b65y_walk_radial hne c N hc D₀ y₀ u₀
  have hΦΦ : Φ' = Φ := by
    ext x
    rw [hΦ', hΦ]
  subst hΦΦ
  have heq : D'.atlas.hπ.fundamentalGroupToMulOpposite u' =
      D.atlas.hπ.fundamentalGroupToMulOpposite w := by
    ext a
    obtain ⟨b, rfl⟩ := b65y_map_surjective Φ' y₀ a
    have h1 := DFunLike.congr_fun hmon b
    have h2 := DFunLike.congr_fun hw b
    simp only [MonoidHom.comp_apply] at h1 h2
    rw [h1, h2]
  obtain ⟨E⟩ := b65y_edge_terminal D' D (Φ' y₀) u' w heq
  exact ⟨wk.append (.cons E (.nil _))⟩

/-- The common radius is continuous on the normalized chart.
Source: `b6t_radius`; `b6t_discs`; Mathlib `ContinuousAt.inv₀`. -/
theorem b65y_radius_continuousOn : ContinuousOn b6t_radius b6_chart := by
  intro b hb
  apply ContinuousAt.continuousWithinAt
  obtain ⟨hr, h01, hdisj⟩ := b6t_discs b hb
  have hb0 : ∀ i, b i ≠ 0 := fun i h ↦ (h01 i).1 (by simp [h, (le_of_lt hr)])
  have hb1 : ∀ i, b i - 1 ≠ 0 := fun i h ↦ (h01 i).2 (by
    rw [sub_eq_zero] at h
    simp [h, (le_of_lt hr)])
  have hbij : ∀ i j, i ≠ j → dist (b i) (b j) ≠ 0 := by
    intro i j hij h
    rw [dist_eq_zero] at h
    exact Set.disjoint_iff.1 (hdisj hij) ⟨Metric.mem_closedBall_self (le_of_lt hr),
      by rw [h]; exact Metric.mem_closedBall_self (le_of_lt hr)⟩
  have hpos : 0 < 4 * (1 + ∑ i : Fin 10, (‖b i‖⁻¹ + ‖b i - 1‖⁻¹ +
      ∑ j : Fin 10, if i = j then 0 else (dist (b i) (b j))⁻¹)) := by
    apply mul_pos (by norm_num)
    have : 0 ≤ ∑ i : Fin 10, (‖b i‖⁻¹ + ‖b i - 1‖⁻¹ +
        ∑ j : Fin 10, if i = j then (0 : ℝ) else (dist (b i) (b j))⁻¹) := by
      apply Finset.sum_nonneg
      intro i _
      have : 0 ≤ ∑ j : Fin 10, if i = j then (0 : ℝ) else (dist (b i) (b j))⁻¹ :=
        Finset.sum_nonneg fun j _ ↦ by split_ifs <;> positivity
      positivity
    linarith
  unfold b6t_radius
  refine ContinuousAt.inv₀ ?_ hpos.ne'
  refine continuousAt_const.mul (continuousAt_const.add ?_)
  refine tendsto_finsetSum _ fun i _ ↦ ?_
  have c1 : ContinuousAt (fun t : Fin 10 → ℂ ↦ ‖t i‖⁻¹) b :=
    ContinuousAt.inv₀ (continuous_apply i).norm.continuousAt (norm_ne_zero_iff.2 (hb0 i))
  have c2 : ContinuousAt (fun t : Fin 10 → ℂ ↦ ‖t i - 1‖⁻¹) b := by
    have hc : Continuous fun t : Fin 10 → ℂ ↦ ‖t i - 1‖ :=
      ((continuous_apply i).sub continuous_const).norm
    exact ContinuousAt.inv₀ hc.continuousAt (norm_ne_zero_iff.2 (hb1 i))
  refine (c1.add c2).add ?_
  refine tendsto_finsetSum _ fun j _ ↦ ?_
  by_cases hij : i = j
  · simp only [hij, if_true]
    exact continuousAt_const
  · simp only [hij, if_false]
    exact ContinuousAt.inv₀ ((continuous_apply i).dist (continuous_apply j)).continuousAt
      (hbij i j hij)

/-- A path of normalized configurations has a finite uniform subdivision in which every
configuration lies in the polydisc of the previous one.
Source: `b65y_radius_continuousOn`; compactness of the unit interval, uniform continuity. -/
theorem b65y_path_subdivision (γ : C(unitInterval, Fin 10 → ℂ)) (hγ : ∀ τ, γ τ ∈ b6_chart) :
    ∃ N : ℕ, 0 < N ∧ ∀ k < N,
      γ (Set.projIcc 0 1 zero_le_one (((k : ℝ) + 1) / N)) ∈
        b6t_polydisc (γ (Set.projIcc 0 1 zero_le_one ((k : ℝ) / N))) := by
  have hcont : Continuous fun τ ↦ b6t_radius (γ τ) :=
    b65y_radius_continuousOn.comp_continuous γ.continuous hγ
  obtain ⟨τ₀, -, hτ₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hcont.continuousOn
  set ρ := b6t_radius (γ τ₀)
  have hρ : 0 < ρ := (b6t_discs _ (hγ τ₀)).1
  obtain ⟨δ, hδ, hγδ⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous γ.continuous) ρ hρ
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨N + 1, Nat.succ_pos N, fun k hk ↦ ?_⟩
  have hN1 : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hk1 : ((k : ℝ) + 1) / (N + 1 : ℕ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · rw [div_le_one hN1]
      exact_mod_cast hk
  have hk0 : (k : ℝ) / (N + 1 : ℕ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · rw [div_le_one hN1]
      exact_mod_cast hk.le
  have hd : dist (Set.projIcc 0 1 zero_le_one (((k : ℝ) + 1) / (N + 1 : ℕ)))
      (Set.projIcc 0 1 zero_le_one ((k : ℝ) / (N + 1 : ℕ))) < δ := by
    rw [Set.projIcc_of_mem _ hk1, Set.projIcc_of_mem _ hk0, Subtype.dist_eq]
    change |((k : ℝ) + 1) / (N + 1 : ℕ) - (k : ℝ) / (N + 1 : ℕ)| < δ
    rw [← sub_div, add_sub_cancel_left, abs_of_pos (by positivity)]
    calc (1 : ℝ) / (N + 1 : ℕ) = 1 / ((N : ℝ) + 1) := by push_cast; rfl
      _ < δ := hN
  have hlt := hγδ hd
  intro i
  rw [Metric.mem_ball]
  exact lt_of_le_of_lt (dist_le_pi_dist _ _ i)
    (lt_of_lt_of_le hlt (hτ₀ (Set.mem_univ _)))

attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

/-- The certified chain from a radial sequence of configurations from `mr_base` to the G32
centre whose composite carries the based monodromy of the retained reference family to that of
the given family at the centre.
Source: `b65y_walk_of_radial`, `b65y_chain_of_walk`; `b63d_root_nielsen`,
`b65z_nielsen_ne_one`; G32 v0.16, §3.1 and proof of Lemma 3.4. -/
theorem b65y_certified_chain_of_radial (p : Fin 12 → ℂ)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (R : rf8_SharedFamily) (v₀ : R.atlas.π ⁻¹' {b63gP_basePoint})
    (c : ℕ → Fin 10 → ℂ) (N : ℕ) (h0 : c 0 = mr_base) (hN : c N = b65z_centre p)
    (hc : ∀ k < N, c (k + 1) ∈ b6t_polydisc (c k))
    (Φ : b6t_punctured mr_base ≃ₜ b6t_punctured (b65z_centre p))
    (hΦ : ∀ x, (Φ x : OnePoint ℂ) = b65y_radial c N x)
    (w : D.atlas.π ⁻¹' {Φ b63gP_basePoint})
    (hw : (D.atlas.hπ.fundamentalGroupToMulOpposite w).comp
      (FundamentalGroup.map ⟨Φ, Φ.continuous⟩ b63gP_basePoint) =
      R.atlas.hπ.fundamentalGroupToMulOpposite v₀) :
    ∃ H : b65y_HurwitzChain,
      H.chart 0 = (⟨mr_base, b4b_root, b65z_ofRetained R⟩ : b65y_Chart) ∧
      H.chart (Fin.last H.n) = (⟨b65z_centre p, g, D⟩ : b65y_Chart) := by
  have hne : ∀ j, b4b_root j ≠ 1 := b65z_nielsen_ne_one b4b_root b63d_root_nielsen
  obtain ⟨wk⟩ := b65y_walk_of_radial hne c N h0 hN hc (b65z_ofRetained R) D b63gP_basePoint
    v₀ Φ hΦ w hw
  exact b65y_chain_of_walk wk

/-- The composite radial push along a finite radial sequence restricts to a homeomorphism of
the punctured spheres.
Source: `b6t_punctured_homeomorph`, `b6t_polydisc_neighbourhood`. -/
theorem b65y_radial_homeomorph (c : ℕ → Fin 10 → ℂ) (N : ℕ) {c₀ c₁ : Fin 10 → ℂ}
    (h0 : c 0 = c₀) (hN : c N = c₁) (hc₀ : c₀ ∈ b6_chart)
    (hc : ∀ k < N, c (k + 1) ∈ b6t_polydisc (c k)) :
    ∃ Φ : b6t_punctured c₀ ≃ₜ b6t_punctured c₁,
      ∀ x, (Φ x : OnePoint ℂ) = b65y_radial c N x := by
  subst h0 hN
  induction N with
  | zero => exact ⟨Homeomorph.refl _, fun x ↦ rfl⟩
  | succ N ih =>
    obtain ⟨Φ, hΦ⟩ := ih (fun k hk ↦ hc k (by omega))
    have hmem : ∀ k ≤ N, c k ∈ b6_chart := by
      intro k hk
      induction k with
      | zero => exact hc₀
      | succ k ihk =>
        exact (b6t_polydisc_neighbourhood (c k) (ihk (by omega))).2.2.2 (hc k (by omega))
    obtain ⟨e, he⟩ := b6t_punctured_homeomorph (c N) (hmem N le_rfl) (c (N + 1)) (hc N (by omega))
    refine ⟨Φ.trans e, fun x ↦ ?_⟩
    change (e (Φ x) : OnePoint ℂ) = b6t_sphere (c N) (c (N + 1)) (b65y_radial c N x)
    rw [he, hΦ]

/-- The uniform samples of a path of configurations.
Source: `Set.projIcc`; uniform subdivision of the unit interval. -/
def b65y_sample (γ : C(unitInterval, Fin 10 → ℂ)) (N : ℕ) (k : ℕ) : Fin 10 → ℂ :=
  γ (Set.projIcc 0 1 zero_le_one ((k : ℝ) / N))

example (γ : C(unitInterval, Fin 10 → ℂ)) (N : ℕ) :
    b65y_sample γ N 0 = γ (Set.projIcc 0 1 zero_le_one 0) := by simp [b65y_sample]

/-- The certified chain from a path of normalized configurations from `mr_base` to the G32
centre, provided that for the uniform subdivisions of the path the composite radial
homeomorphism carries the based monodromy of the retained reference family to that of the
given family at the centre.
Source: `b65y_path_subdivision`, `b65y_certified_chain_of_radial`; G32 v0.16, §3.1 and proof of
Lemma 3.4. -/
theorem b65y_certified_chain_of_path (p : Fin 12 → ℂ)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (R : rf8_SharedFamily) (v₀ : R.atlas.π ⁻¹' {b63gP_basePoint})
    (γ : C(unitInterval, Fin 10 → ℂ)) (hγ : ∀ τ, γ τ ∈ b6_chart)
    (hγ0 : γ 0 = mr_base) (hγ1 : γ 1 = b65z_centre p)
    (hmon : ∀ N : ℕ, 0 < N →
      (∀ k < N, b65y_sample γ N (k + 1) ∈ b6t_polydisc (b65y_sample γ N k)) →
      ∀ Φ : b6t_punctured mr_base ≃ₜ b6t_punctured (b65z_centre p),
        (∀ x, (Φ x : OnePoint ℂ) = b65y_radial (b65y_sample γ N) N x) →
        ∃ w : D.atlas.π ⁻¹' {Φ b63gP_basePoint},
          (D.atlas.hπ.fundamentalGroupToMulOpposite w).comp
            (FundamentalGroup.map ⟨Φ, Φ.continuous⟩ b63gP_basePoint) =
          R.atlas.hπ.fundamentalGroupToMulOpposite v₀) :
    ∃ H : b65y_HurwitzChain,
      H.chart 0 = (⟨mr_base, b4b_root, b65z_ofRetained R⟩ : b65y_Chart) ∧
      H.chart (Fin.last H.n) = (⟨b65z_centre p, g, D⟩ : b65y_Chart) := by
  obtain ⟨N, hN, hsub⟩ := b65y_path_subdivision γ hγ
  have hc : ∀ k < N, b65y_sample γ N (k + 1) ∈ b6t_polydisc (b65y_sample γ N k) := by
    intro k hk
    have h := hsub k hk
    simp only [b65y_sample, Nat.cast_add, Nat.cast_one]
    exact h
  have h0 : b65y_sample γ N 0 = mr_base := by
    simp only [b65y_sample, Nat.cast_zero, zero_div, Set.projIcc_left]
    exact hγ0
  have hN1 : b65y_sample γ N N = b65z_centre p := by
    have : ((N : ℝ) / N) = 1 := div_self (by exact_mod_cast hN.ne')
    simp only [b65y_sample, this, Set.projIcc_right]
    exact hγ1
  obtain ⟨Φ, hΦ⟩ := b65y_radial_homeomorph (b65y_sample γ N) N h0 hN1 mr_base_mem_chart hc
  obtain ⟨w, hw⟩ := hmon N hN hc Φ hΦ
  exact b65y_certified_chain_of_radial p g D R v₀ (b65y_sample γ N) N h0 hN1 hc Φ hΦ w hw

end HodgeLean.Foundations.Program
