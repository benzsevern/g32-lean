import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian15
import HodgeLean.Adapters.ExpHolomorphic
import HodgeLean.Adapters.CycleClassSmoothCharts
import HodgeLean.Adapters.AutomorphyLineBundleOnXDefs
import HodgeLean.Adapters.UniformizationBiholomorphic

/-! # Algebraic boundary covers

Implication from the actual component coheight to a codimension-two cover of
its singular boundary upstairs. Component smooth dimensions are obtained from
the existing algebraic dimension theorem, before countable chart assembly.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open TopologicalSpace Set Filter Topology
open scoped Manifold ContDiff CategoryTheory.MonObj
open HodgeLean.RealDefs
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Adapters

/-- The smooth part of an algebraic component has countably many charts of its actual complex dimension.
Source: `cycleComponentSmoothLocus_smoothOfRelativeDimension`, complex manifold charts,
and second countability of the locally closed analytic support. -/
theorem bh15_component_smooth_cover_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) (q : ℕ) (hx : Order.coheight x = q) :
    ∃ (U : ℕ → Set (Fin (dim X.left - q) → ℂ))
      (g : ℕ → (Fin (dim X.left - q) → ℂ) → ComplexPoint X),
      (∀ j, IsOpen (U j)) ∧
      (∀ j, ContMDiffOn 𝓘(ℂ, Fin (dim X.left - q) → ℂ)
        𝓘(ℂ, Fin (dim X.left) → ℂ) ω (g j) (U j)) ∧
      cycleComponentSmoothSupport X x = ⋃ j, g j '' U j := by
  classical
  let Y := cycleComponentSmoothLocusOver X x
  let m := dim X.left - q
  letI : SmoothOfRelativeDimension m Y.hom :=
    cycleComponentSmoothLocus_smoothOfRelativeDimension X x hx
  let d := dim X.left
  letI : SmoothOfRelativeDimension d X.hom := inferInstance
  letI : SecondCountableTopology (ComplexPoint X) :=
    ChartedSpace.secondCountable_of_sigmaCompact (Fin d → ℂ) (ComplexPoint X)
  let U := cycleComponentSmoothLocusAmbientOpen X x
  let A := openScheme X U
  let i : Y ⟶ A := cycleComponentSmoothLocusClosedLiftOver X x
  let j : A ⟶ X := openInclusion X U
  have hi : IsEmbedding (Point.map i) :=
    (ComplexPoint.isClosedEmbedding_map_of_closedImmersion i).isEmbedding
  have hj : IsEmbedding (Point.map j) :=
    (ComplexPoint.isOpenEmbedding_map_open X U).isEmbedding
  letI : SecondCountableTopology (ComplexPoint Y) :=
    (hj.comp hi).secondCountableTopology
  obtain ⟨s, hs, hsc⟩ := TopologicalSpace.countable_cover_nhds
    (fun y : ComplexPoint Y ↦ chart_source_mem_nhds (Fin m → ℂ) y)
  have hsne : s.Nonempty := by
    let y : ComplexPoint Y := Classical.choice
      (nonempty_complexPoint_cycleComponentSmoothLocusOver X x)
    have : y ∈ (⋃ z ∈ s, (chartAt (Fin m → ℂ) z).source) := by
      rw [hsc]
      exact mem_univ y
    obtain ⟨z, hz, -⟩ := Set.mem_iUnion₂.mp this
    exact ⟨z, hz⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ → s, Function.Surjective a :=
    Set.Countable.exists_surjective hsne hs
  let e : ℕ → OpenPartialHomeomorph (ComplexPoint Y) (Fin m → ℂ) :=
    fun n ↦ chartAt (Fin m → ℂ) (a n).1
  let U : ℕ → Set (Fin m → ℂ) := fun n ↦ (e n).target
  let k : Y ⟶ X := i ≫ j
  have hk : k = openInclusion (Over.mk (cycleComponentι X.left x ≫ X.hom))
      ((cycleComponentι X.left x ≫ X.hom).smoothLocus) ≫
        Over.homMk (cycleComponentι X.left x) rfl := by
    apply Over.OverMorphism.ext
    exact cycleComponentSmoothLocusClosedLift_ι X x
  let g : ℕ → (Fin m → ℂ) → ComplexPoint X :=
    fun n ↦ Point.map k ∘ (e n).symm
  refine ⟨U, g, fun n ↦ (e n).open_target, ?_, ?_⟩
  · intro n
    have hkdiff : ContMDiffOn (modelWithCornersSelf ℂ (Fin m → ℂ))
        (modelWithCornersSelf ℂ (Fin d → ℂ)) ω (Point.map k) univ :=
      (spec_contMDiff_pointMap Y X m d k).contMDiffOn
    exact hkdiff.comp
      (contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (a n).1))
      (fun _ _ ↦ mem_univ _)
  · apply Set.Subset.antisymm
    · rintro p ⟨z, hz, rfl⟩
      let C := Over.mk (cycleComponentι X.left x ≫ X.hom)
      let UC := (cycleComponentι X.left x ≫ X.hom).smoothLocus
      let w : ComplexPoint (openScheme C UC) := (openEquiv C UC).symm ⟨z, hz⟩
      have hw : Point.map (openInclusion C UC) w = z :=
        congrArg Subtype.val ((openEquiv C UC).apply_symm_apply ⟨z, hz⟩)
      have hp : Point.map k w = cycleComponentMap X x z := by
        change w ≫ k = cycleComponentMap X x z
        rw [hk, ← Category.assoc]
        change Point.map (Over.homMk (cycleComponentι X.left x) rfl)
          (Point.map (openInclusion C UC) w) = cycleComponentMap X x z
        rw [hw]
        rfl
      have hwcover : w ∈ ⋃ n, (e n).source := by
        have hw' : w ∈ (⋃ z ∈ s, (chartAt (Fin m → ℂ) z).source) := by
          rw [hsc]
          exact mem_univ w
        obtain ⟨z, hzs, hwz⟩ := Set.mem_iUnion₂.mp hw'
        obtain ⟨n, hn⟩ := ha ⟨z, hzs⟩
        refine mem_iUnion.mpr ⟨n, ?_⟩
        simpa [e, congrArg Subtype.val hn] using hwz
      obtain ⟨n, hwn⟩ := mem_iUnion.mp hwcover
      refine mem_iUnion.mpr ⟨n, ?_⟩
      refine ⟨e n w, (e n).map_source hwn, ?_⟩
      change Point.map k ((e n).symm (e n w)) = cycleComponentMap X x z
      rw [(e n).left_inv hwn, hp]
    · rintro p hp
      obtain ⟨n, hn⟩ := mem_iUnion.mp hp
      obtain ⟨t, ht, rfl⟩ := hn
      change Point.map k ((e n).symm t) ∈ cycleComponentSmoothSupport X x
      rw [hk]
      change cycleComponentMap X x
        (Point.map (openInclusion (Over.mk (cycleComponentι X.left x ≫ X.hom))
          ((cycleComponentι X.left x ≫ X.hom).smoothLocus)) ((e n).symm t)) ∈
            cycleComponentSmoothSupport X x
      refine ⟨_, ?_, rfl⟩
      exact (openEquiv (Over.mk (cycleComponentι X.left x ≫ X.hom))
        ((cycleComponentι X.left x ≫ X.hom).smoothLocus) ((e n).symm t)).2

private theorem bh15_manifold_union_cover (n q : ℕ) (M : Type*)
    [TopologicalSpace M] [ChartedSpace (Fin n → ℂ) M]
    (d₀ d₁ : ℕ → ℕ) (U₀ : ∀ j, Set (Fin (d₀ j) → ℂ))
    (U₁ : ∀ j, Set (Fin (d₁ j) → ℂ))
    (g₀ : ∀ j, (Fin (d₀ j) → ℂ) → M)
    (g₁ : ∀ j, (Fin (d₁ j) → ℂ) → M)
    (hd₀ : ∀ j, (U₀ j).Nonempty → d₀ j + q ≤ n)
    (hd₁ : ∀ j, (U₁ j).Nonempty → d₁ j + q ≤ n)
    (hU₀ : ∀ j, IsOpen (U₀ j)) (hU₁ : ∀ j, IsOpen (U₁ j))
    (hg₀ : ∀ j, ContMDiffOn 𝓘(ℂ, Fin (d₀ j) → ℂ) 𝓘(ℂ, Fin n → ℂ) ω (g₀ j) (U₀ j))
    (hg₁ : ∀ j, ContMDiffOn 𝓘(ℂ, Fin (d₁ j) → ℂ) 𝓘(ℂ, Fin n → ℂ) ω (g₁ j) (U₁ j)) :
    ∃ (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
      (g : ∀ j, (Fin (d j) → ℂ) → M),
      (∀ j, (U j).Nonempty → d j + q ≤ n) ∧
      (∀ j, IsOpen (U j)) ∧
      (∀ j, ContMDiffOn 𝓘(ℂ, Fin (d j) → ℂ) 𝓘(ℂ, Fin n → ℂ) ω (g j) (U j)) ∧
      (⋃ j, g₀ j '' U₀ j) ∪ (⋃ j, g₁ j '' U₁ j) = ⋃ j, g j '' U j := by
  let d : ℕ ⊕ ℕ → ℕ := Sum.elim d₀ d₁
  let U : ∀ j, Set (Fin (d j) → ℂ) := Sum.rec U₀ U₁
  let g : ∀ j, (Fin (d j) → ℂ) → M := Sum.rec g₀ g₁
  let e := Equiv.natSumNatEquivNat.symm
  refine ⟨fun j => d (e j), fun j => U (e j), fun j => g (e j), ?_, ?_, ?_, ?_⟩
  · have hd : ∀ k, (U k).Nonempty → d k + q ≤ n := by
      intro k
      cases k with
      | inl k => exact hd₀ k
      | inr k => exact hd₁ k
    exact fun j => hd (e j)
  · have ho : ∀ k, IsOpen (U k) := by
      intro k
      cases k with
      | inl k => exact hU₀ k
      | inr k => exact hU₁ k
    exact fun j => ho (e j)
  · have hg : ∀ k, ContMDiffOn 𝓘(ℂ, Fin (d k) → ℂ) 𝓘(ℂ, Fin n → ℂ)
        ω (g k) (U k) := by
      intro k
      cases k with
      | inl k => exact hg₀ k
      | inr k => exact hg₁ k
    exact fun j => hg (e j)
  · exact (Set.iUnion_sum (s := fun k => g k '' U k)).symm.trans
      (e.surjective.iUnion_comp (fun k => g k '' U k)).symm

private theorem bh15_component_boundary_subset (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    (cycleComponentSingularAmbientClosedFiltration X x 0 : Set X.left) ⊆
      closure ({x} : Set X.left) := by
  rintro z ⟨y, _, rfl⟩
  rw [← range_cycleComponentι X.left x]
  exact ⟨y, rfl⟩

private theorem bh15_component_support_split (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    cycleComponentSupport X x = cycleComponentSmoothSupport X x ∪
      (cycleComponentSingularAnalyticClosedFiltration X x 0 : Set (ComplexPoint X)) := by
  ext z
  constructor
  · intro hz
    by_cases hb : z ∈ cycleComponentSingularAnalyticClosedFiltration X x 0
    · exact Or.inr hb
    · left
      let p := cycleComponentComplexPointLift X x z hz
      refine ⟨p, ?_, cycleComponentMap_lift X x z hz⟩
      by_contra hp
      apply hb
      refine ⟨p.underlying, hp, ?_⟩
      exact congrArg Point.underlying (cycleComponentMap_lift X x z hz)
  · rintro (⟨p, _, rfl⟩ | hb)
    · change cycleComponentι X.left x p.underlying ∈ closure ({x} : Set X.left)
      rw [← range_cycleComponentι X.left x]
      exact ⟨p.underlying, rfl⟩
    · exact bh15_component_boundary_subset X x hb

/-- An algebraic coheight bound transfers to the parameter dimensions of a countable manifold-valued cover.
This is the algebraic-to-analytic intermediate used for the singular boundary.
Source: `bh15_component_smooth_cover`, Noetherian induction as in
`ccm5_closed_supportH_subsingleton_of_coheight`, and the component dimension formula. -/
theorem bh15_algebraic_coheight_cover_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds X.left) (q : ℕ)
    (hc : ∀ z ∈ S, (q : ℕ∞) ≤ Order.coheight z) :
    ∃ (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
      (g : ∀ j, (Fin (d j) → ℂ) → ComplexPoint X),
      (∀ j, (U j).Nonempty → d j + q ≤ dim X.left) ∧
      (∀ j, IsOpen (U j)) ∧
      (∀ j, ContMDiffOn 𝓘(ℂ, Fin (d j) → ℂ)
        𝓘(ℂ, Fin (dim X.left) → ℂ) ω (g j) (U j)) ∧
      (Point.underlying : ComplexPoint X → X.left) ⁻¹' (S : Set X.left) =
        ⋃ j, g j '' U j := by
  classical
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : IsNoetherian X.left := { }
  revert hc
  induction S using (wellFounded_lt (α := Closeds X.left)).induction with
  | h S ih =>
    intro hc
    by_cases hSbot : S = ⊥
    · subst S
      let : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
      obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints
        (X := X.left) (Z := Set.univ) Set.univ_nonempty isOpen_univ.isLocallyClosed
      let w := (pointEquivClosedPoint X.hom).symm ⟨x, hx⟩
      let z : ComplexPoint X := Over.homMk w.1 w.2
      refine ⟨fun _ => 0, fun _ => ∅, fun _ _ => z, ?_, ?_, ?_, ?_⟩
      · intro j hj
        exact hj.elim (fun _ h => h.elim)
      · exact fun _ => isOpen_empty
      · exact fun _ => contMDiffOn_empty
      · simp only [Closeds.coe_bot, preimage_empty, image_empty, iUnion_empty]
    obtain ⟨x, B, hS, hBS, _hxB⟩ := ccm5_closed_generic_split X.left S hSbot
    let C : Closeds X.left := ⟨closure ({x} : Set X.left), isClosed_closure⟩
    let D := cycleComponentSingularAmbientClosedFiltration X x 0
    have hCS : C ≤ S := by rw [hS]; exact le_sup_left
    have hxC : x ∈ C := subset_closure (Set.mem_singleton x)
    have hxS : x ∈ S := hCS hxC
    have hDC : D ≤ C := bh15_component_boundary_subset X x
    have hDS : D < S := lt_of_le_of_ne (hDC.trans hCS) (by
      intro he
      apply ccm5_generic_not_mem_singularBoundary X x
      change x ∈ D
      rw [he]
      exact hxS)
    have hbound := SmoothOfRelativeDimension.coheight_le_complex
      (f := X.hom) (d := dim X.left) x
    have hfin : Order.coheight x ≠ ⊤ := ne_of_lt
      (lt_of_le_of_lt hbound (WithTop.coe_lt_top _))
    let r := (Order.coheight x).toNat
    have hr : Order.coheight x = r := (ENat.natCast_toNat hfin).symm
    have hqr : q ≤ r := by
      have hh := hc x hxS
      rw [hr] at hh
      exact_mod_cast hh
    have hrn : r ≤ dim X.left := by
      rw [hr] at hbound
      exact_mod_cast hbound
    obtain ⟨U₀, g₀, ho₀, hg₀, he₀⟩ := bh15_component_smooth_cover_aux X x r hr
    obtain ⟨d₁, U₁, g₁, hd₁, ho₁, hg₁, he₁⟩ :=
      ih D hDS (fun z hz => hc z (hDS.le hz))
    obtain ⟨d₂, U₂, g₂, hd₂, ho₂, hg₂, he₂⟩ :=
      ih B hBS (fun z hz => hc z (hBS.le hz))
    obtain ⟨d₃, U₃, g₃, hd₃, ho₃, hg₃, he₃⟩ :=
      bh15_manifold_union_cover (dim X.left) q (ComplexPoint X)
        (fun _ => dim X.left - r) d₁ U₀ U₁ g₀ g₁
        (fun _ _ => by omega) hd₁ ho₀ ho₁ hg₀ hg₁
    obtain ⟨d, U, g, hd, ho, hg, he⟩ :=
      bh15_manifold_union_cover (dim X.left) q (ComplexPoint X)
        d₃ d₂ U₃ U₂ g₃ g₂ hd₃ hd₂ ho₃ ho₂ hg₃ hg₂
    refine ⟨d, U, g, hd, ho, hg, ?_⟩
    rw [← he, ← he₃, ← he₀, ← he₁, ← he₂]
    change (Point.underlying : ComplexPoint X → X.left) ⁻¹' (S : Set X.left) =
      (cycleComponentSmoothSupport X x ∪
        (cycleComponentSingularAnalyticClosedFiltration X x 0 : Set (ComplexPoint X))) ∪
        Point.underlying ⁻¹' (B : Set X.left)
    rw [← bh15_component_support_split X x, hS]
    rfl

/-- The exponential preimage of a prime divisor singular boundary has a countable codimension-two cover.
Source: `ccm5_singularBoundary_coheight_lower_bound`, `bh15_algebraic_coheight_cover`,
`spec_complexExponential_localBiholomorph`, and `bh15_lift_cover`. -/
theorem bh15_boundary_stratification_aux (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) (hx : Order.coheight x = 1) :
    ∃ (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
      (g : ∀ j, (Fin (d j) → ℂ) → (Fin (dim X.left) → ℂ)),
      (∀ j, (U j).Nonempty → d j + 2 ≤ dim X.left) ∧
      (∀ j, IsOpen (U j)) ∧
      (∀ j, DifferentiableOn ℂ (g j) (U j)) ∧
      abelianExp X ⁻¹'
        (cycleComponentSingularAnalyticClosedFiltration X x 0 :
          Set (ComplexPoint X)) = ⋃ j, g j '' U j := by
  let S := cycleComponentSingularAmbientClosedFiltration X x 0
  have hc : ∀ z ∈ S, ((2 : ℕ) : ℕ∞) ≤ Order.coheight z := by
    intro z hz
    have h := ccm5_singularBoundary_coheight_lower_bound X 1 x z hx hz
    norm_num at h ⊢
    exact h
  obtain ⟨d, U, g, hd, hU, hg, hcover⟩ :=
    bh15_algebraic_coheight_cover_aux X S 2 hc
  letI : IsCommMonObj X :=
    HodgeLean.Foundations.isCommMonObj_of_complexSelfProductIntegral X
      (HodgeLean.Foundations.complexSelfProductIntegral_of_isIntegral X)
  have hrel : SmoothOfRelativeDimension (dim X.left) X.hom :=
    SmoothOfRelativeDimension.of_isIntegral X.hom
  have hloc : ∀ p, ∃ e : OpenPartialHomeomorph (Fin (dim X.left) → ℂ) (ComplexPoint X),
      p ∈ e.source ∧ EqOn (abelianExp X) e e.source ∧
      ContMDiffOn 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω
        e.symm e.target := by
    intro p
    obtain ⟨e, hp, he, hs⟩ :=
      spec_complexExponential_localBiholomorph X (dim X.left) p
    refine ⟨e, hp, ?_, hs⟩
    intro w hw
    change (HodgeLean.Foundations.complexExponential X (dim X.left) w).toMul = e w
    exact he hw
  obtain ⟨σ, V, h, hVU, hV, hh, -, hlift⟩ :=
    bh15_lift_cover (dim X.left) (ComplexPoint X) (abelianExp X) hloc d U g hU hg
  refine ⟨fun j ↦ d (σ j), V, h, ?_, hV, hh, ?_⟩
  · intro j hj
    obtain ⟨t, ht⟩ := hj
    exact hd (σ j) ⟨t, hVU j ht⟩
  · rw [← hlift, ← hcover]
    rfl

/-- Critical zeros together with the exponential singular boundary have a countable codimension-two cover.
Source: `bh15_critical_stratification`, `bh15_boundary_stratification`, and `bh15_union_cover`. -/
theorem bh15_critical_boundary_stratification_aux (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) (hx : Order.coheight x = 1)
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt (dim X.left) p)) :
    ∃ (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
      (g : ∀ j, (Fin (d j) → ℂ) → (Fin (dim X.left) → ℂ)),
      (∀ j, (U j).Nonempty → d j + 2 ≤ dim X.left) ∧
      (∀ j, IsOpen (U j)) ∧
      (∀ j, DifferentiableOn ℂ (g j) (U j)) ∧
      ({p | f p = 0 ∧ fderiv ℂ f p = 0} ∪
        abelianExp X ⁻¹' (cycleComponentSingularAnalyticClosedFiltration X x 0 :
          Set (ComplexPoint X))) = ⋃ j, g j '' U j := by
  obtain ⟨d₀, U₀, g₀, hd₀, hU₀, hg₀, hcrit⟩ :=
    bh15_critical_stratification (dim X.left) f hf hred
  obtain ⟨d₁, U₁, g₁, hd₁, hU₁, hg₁, hboundary⟩ :=
    bh15_boundary_stratification_aux X x hx
  exact bh15_union_cover (dim X.left)
    {p | f p = 0 ∧ fderiv ℂ f p = 0}
    (abelianExp X ⁻¹' (cycleComponentSingularAnalyticClosedFiltration X x 0 :
      Set (ComplexPoint X)))
    d₀ d₁ U₀ U₁ g₀ g₁ hd₀ hd₁ hU₀ hU₁ hg₀ hg₁ hcrit hboundary

end HodgeLean.Adapters
