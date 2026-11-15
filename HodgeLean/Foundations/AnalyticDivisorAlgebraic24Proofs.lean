import HodgeLean.Foundations.AnalyticDivisorAlgebraic24Defs
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Analysis.Polynomial.CauchyBound
import HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersion.AnalyticLeftInverse
import HodgeLean.Adapters.UniformizationBiholomorphic
import HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersion.HolomorphicCharts
import HodgeLean.Foundations.Curves.CubicS13Defs
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.NormalGeometry

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic24
open Filter Set Topology
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Foundations HodgeLean.Adapters HodgeLean.RealDefs
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic21
open HodgeLean.Foundations.AnalyticDivisorAlgebraic22
open scoped Manifold CategoryTheory.MonObj

open HodgeLean.Foundations.AnalyticDivisorAlgebraic23

theorem gaga24_chart_dimension_aux {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ F] (a : E) (b : F) (u : E → F) (v : F → E)
    (hu : AnalyticAt ℂ u a) (hv : AnalyticAt ℂ v b)
    (hab : u a = b) (hba : v b = a)
    (hvu : ∀ᶠ z in 𝓝 a, v (u z) = z) (huv : ∀ᶠ z in 𝓝 b, u (v z) = z) :
    Module.finrank ℂ E = Module.finrank ℂ F := by
  have hdu := hu.differentiableAt.hasFDerivAt
  have hdv := hv.differentiableAt.hasFDerivAt
  have hdv' : HasFDerivAt v (fderiv ℂ v b) (u a) := hab.symm ▸ hdv
  have hcE := hdv'.comp a hdu
  have hdu' : HasFDerivAt u (fderiv ℂ u a) (v b) := hba.symm ▸ hdu
  have hcF := hdu'.comp b hdv
  have hcompE : (fderiv ℂ v b).comp (fderiv ℂ u a) = ContinuousLinearMap.id ℂ E := by
    rw [← hcE.fderiv]
    have hlocal : (v ∘ u) =ᶠ[𝓝 a] id := hvu
    simpa only [fderiv_id] using hlocal.fderiv_eq (𝕜 := ℂ)
  have hcompF : (fderiv ℂ u a).comp (fderiv ℂ v b) = ContinuousLinearMap.id ℂ F := by
    rw [← hcF.fderiv]
    have hlocal : (u ∘ v) =ᶠ[𝓝 b] id := huv
    simpa only [fderiv_id] using hlocal.fderiv_eq (𝕜 := ℂ)
  have hinjU : Function.Injective (fderiv ℂ u a) := by
    intro x y hxy
    calc
      x = ((fderiv ℂ v b).comp (fderiv ℂ u a)) x := by rw [hcompE]; rfl
      _ = ((fderiv ℂ v b).comp (fderiv ℂ u a)) y := by
        simp only [ContinuousLinearMap.comp_apply, hxy]
      _ = y := by rw [hcompE]; rfl
  have hinjV : Function.Injective (fderiv ℂ v b) := by
    intro x y hxy
    calc
      x = ((fderiv ℂ u a).comp (fderiv ℂ v b)) x := by rw [hcompF]; rfl
      _ = ((fderiv ℂ u a).comp (fderiv ℂ v b)) y := by
        simp only [ContinuousLinearMap.comp_apply, hxy]
      _ = y := by rw [hcompF]; rfl
  apply Nat.le_antisymm
  · exact LinearMap.finrank_le_finrank_of_injective hinjU
  · exact LinearMap.finrank_le_finrank_of_injective hinjV

theorem gaga24_regular_identity {g : ℕ} {R A : Set (Fin g → ℂ)}
    (hc : IsConnected R)
    (hloc : ∀ x ∈ R, ∃ (U : Set (Fin g → ℂ)) (P : (Fin g → ℂ) → ℂ),
      IsOpen U ∧ x ∈ U ∧ AnalyticOnNhd ℂ P U ∧
      ∀ y ∈ U, (y ∈ R ↔ y ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero P))
    (hA : IsClosedAnalytic (Fin g → ℂ) A)
    (hne : (interior (((↑) : R → (Fin g → ℂ)) ⁻¹' A)).Nonempty) : R ⊆ A := by
  let Z : Set R := ((↑) : R → (Fin g → ℂ)) ⁻¹' A
  have : ConnectedSpace R := isConnected_iff_connectedSpace.mp hc
  have hZc : IsClosed Z := hA.isClosed.preimage continuous_subtype_val
  have hclosed : closure (interior Z) ⊆ interior Z := by
    intro x hx
    have hxA : (x : Fin g → ℂ) ∈ A :=
      hZc.closure_subset (closure_mono interior_subset hx)
    obtain ⟨U, P, hUo, hxU, hPa, he⟩ := hloc x x.property
    obtain ⟨W, hWo, hxW, -, n, F, hF, hAF⟩ := hA.2 x hxA
    simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
      OpenPartialHomeomorph.refl_symm, id_eq] at hxW hAF
    obtain ⟨G, k, r, hr, hG0, hk, hk0, hGa, hGR, hrecover⟩ :=
      gaga21_br_regular_graph_chart (hUo.inter hWo) (hPa.mono inter_subset_left)
        (show (x : Fin g → ℂ) ∈
          AnalyticDivisorAlgebraic20.gaga20_regularZero P ∩ (U ∩ W) from
          ⟨(he x hxU).mp x.property, hxU, hxW⟩)
    have hGmem : ∀ t ∈ Metric.ball 0 r, G t ∈ R :=
      fun t ht ↦ (he _ (hGR ht).2.1).mpr (hGR ht).1
    let T : Set R := {y | k y ∈ Metric.ball 0 r ∧ G (k y) = y}
    have hT : T ∈ 𝓝 x := by
      filter_upwards [continuous_subtype_val.continuousAt.eventually hrecover,
        continuous_subtype_val.continuousAt.eventually ((hUo.inter hWo).mem_nhds ⟨hxU, hxW⟩)]
        with y hy hyUW
      exact ⟨hy.1, hy.2 ⟨(he y hyUW.1).mp y.property, hyUW⟩⟩
    obtain ⟨y, hyI, hyT⟩ :=
      ((mem_closure_iff_frequently.mp hx).and_eventually hT).exists
    obtain ⟨O, hOy, hOZ⟩ := (mem_nhds_subtype R y Z).mp
      (mem_interior_iff_mem_nhds.mp hyI)
    have hvan : ∀ i, EqOn (fun t ↦ F i (G t)) 0 (Metric.ball 0 r) := by
      intro i
      have ha : AnalyticOnNhd ℂ (fun t ↦ F i (G t)) (Metric.ball 0 r) :=
        fun t ht ↦ (hF i _ (hGR ht).2.2).comp (hGa t ht)
      apply ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball _ _).isPreconnected hyT.1
      have hGy : Tendsto G (𝓝 (k y)) (𝓝 (y : Fin g → ℂ)) := by
        simpa only [ContinuousAt, hyT.2] using (hGa _ hyT.1).continuousAt
      filter_upwards [hGy.eventually hOy, Metric.isOpen_ball.mem_nhds hyT.1] with t htO ht
      exact (hAF _ (hGR ht).2.2).mp (hOZ (show (⟨G t, hGmem t ht⟩ : R) ∈
        ((↑) : R → (Fin g → ℂ)) ⁻¹' O from htO)) i
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hT] with y hy
    change (y : Fin g → ℂ) ∈ A
    rw [← hy.2]
    exact (hAF _ (hGR hy.1).2.2).mpr (fun i ↦ hvan i hy.1)
  have heq : interior Z = univ :=
    (show IsClopen (interior Z) from
      ⟨closure_subset_iff_isClosed.mp hclosed, isOpen_interior⟩).eq_univ hne
  intro x hx
  have hxI : (⟨x, hx⟩ : R) ∈ interior Z := by rw [heq]; exact mem_univ _
  exact interior_subset (s := Z) hxI

/-- Every algebraic singular-filtration remainder is closed analytic in the ambient space.
Source: Serre, Géométrie algébrique et géométrie analytique, §2, no. 5;
`AnalyticDivisorAlgebraic.spec_isClosedAnalytic_preimage_underlying`. -/
theorem gaga24_singular_filtration_isClosedAnalytic
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (k : ℕ) :
    IsClosedAnalytic (Fin (dim X.left) → ℂ)
      (cycleComponentSingularAnalyticClosedFiltration X x k : Set (ComplexPoint X)) := by
  exact AnalyticDivisorAlgebraic.spec_isClosedAnalytic_preimage_underlying X
    (cycleComponentSingularAmbientClosedFiltration X x k).isClosed

theorem gaga24_closed_eq_of_complexPoint_preimage_eq
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] {C D : Set X.left}
    (hC : IsClosed C) (hD : IsClosed D)
    (h : (Point.underlying : ComplexPoint X → X.left) ⁻¹' C =
      (Point.underlying : ComplexPoint X → X.left) ⁻¹' D) : C = D := by
  let : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  apply Set.Subset.antisymm
  · rw [← hC.closure_eq,
      ← JacobsonSpace.closure_inter_closedPoints_eq_closure hC.isLocallyClosed]
    apply hD.closure_subset_iff.mpr
    rintro x ⟨hxC, hxc⟩
    let q := (pointEquivClosedPoint X.hom).symm ⟨x, hxc⟩
    let p : ComplexPoint X := Over.homMk q.1 q.2
    have hp : p.underlying = x := pointOfClosedPoint_apply X.hom x hxc _
    have hpC : p.underlying ∈ C := hp.symm ▸ hxC
    have hpD : p.underlying ∈ D := by
      rw [← mem_preimage, ← h]
      exact hpC
    exact hp ▸ hpD
  · rw [← hD.closure_eq,
      ← JacobsonSpace.closure_inter_closedPoints_eq_closure hD.isLocallyClosed]
    apply hC.closure_subset_iff.mpr
    rintro x ⟨hxD, hxc⟩
    let q := (pointEquivClosedPoint X.hom).symm ⟨x, hxc⟩
    let p : ComplexPoint X := Over.homMk q.1 q.2
    have hp : p.underlying = x := pointOfClosedPoint_apply X.hom x hxc _
    have hpD : p.underlying ∈ D := hp.symm ▸ hxD
    have hpC : p.underlying ∈ C := by
      rw [← mem_preimage, h]
      exact hpD
    exact hp ▸ hpC

theorem gaga24_singular_locus_proper
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) :
    ¬ closure ({x} : Set X.left) ⊆
      (cycleComponentSingularAmbientClosedFiltration X x 0 : Set X.left) := by
  intro h
  obtain ⟨y, hy⟩ := (dense_cycleComponent_smoothLocus X x).nonempty
  have hyC : cycleComponentι X.left x y ∈ closure ({x} : Set X.left) := by
    rw [← range_cycleComponentι X.left x]
    exact ⟨y, rfl⟩
  obtain ⟨z, hz, he⟩ := h hyC
  have hzy : z = y := (cycleComponentι X.left x).isClosedEmbedding.injective he
  subst z
  exact hz hy

theorem gaga24_singular_support_proper
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) :
    ¬ cycleComponentSupport X x ⊆
      (cycleComponentSingularAnalyticClosedFiltration X x 0 : Set (ComplexPoint X)) := by
  intro h
  apply gaga24_singular_locus_proper X x
  have he : closure ({x} : Set X.left) ∩
      (cycleComponentSingularAmbientClosedFiltration X x 0 : Set X.left) =
        closure ({x} : Set X.left) := by
    apply gaga24_closed_eq_of_complexPoint_preimage_eq X
      (isClosed_closure.inter (cycleComponentSingularAmbientClosedFiltration X x 0).isClosed)
      isClosed_closure
    exact inter_eq_left.mpr h
  exact inter_eq_left.mp he

theorem gaga24_regular_complement_dense {g : ℕ} {R A : Set (Fin g → ℂ)}
    (hc : IsConnected R)
    (hloc : ∀ x ∈ R, ∃ (U : Set (Fin g → ℂ)) (P : (Fin g → ℂ) → ℂ),
      IsOpen U ∧ x ∈ U ∧ AnalyticOnNhd ℂ P U ∧
      ∀ y ∈ U, (y ∈ R ↔ y ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero P))
    (hA : IsClosedAnalytic (Fin g → ℂ) A) (hproper : ¬ R ⊆ A) :
    Dense ((((↑) : R → (Fin g → ℂ)) ⁻¹' A)ᶜ) := by
  apply interior_eq_empty_iff_dense_compl.mp
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hne
  exact hproper (gaga24_regular_identity hc hloc hA hne)

theorem gaga24_regular_complement_closure {g : ℕ} {R A : Set (Fin g → ℂ)}
    (hc : IsConnected R)
    (hloc : ∀ x ∈ R, ∃ (U : Set (Fin g → ℂ)) (P : (Fin g → ℂ) → ℂ),
      IsOpen U ∧ x ∈ U ∧ AnalyticOnNhd ℂ P U ∧
      ∀ y ∈ U, (y ∈ R ↔ y ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero P))
    (hA : IsClosedAnalytic (Fin g → ℂ) A) (hproper : ¬ R ⊆ A) :
    closure (R \ A) = closure R := by
  have hd := gaga24_regular_complement_dense hc hloc hA hproper
  apply Subset.antisymm (closure_mono sdiff_subset)
  apply closure_minimal _ isClosed_closure
  intro z hz
  have hzcl := image_closure_subset_closure_image continuous_subtype_val
    (show z ∈ ((↑) : R → (Fin g → ℂ)) ''
      closure ((((↑) : R → (Fin g → ℂ)) ⁻¹' A)ᶜ) from
      ⟨⟨z, hz⟩, hd ⟨z, hz⟩, rfl⟩)
  have he : ((↑) : R → (Fin g → ℂ)) ''
      ((((↑) : R → (Fin g → ℂ)) ⁻¹' A)ᶜ) = R \ A := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.property, hw⟩
    · rintro ⟨hyR, hyA⟩
      exact ⟨⟨y, hyR⟩, hyA, rfl⟩
  rwa [he] at hzcl

theorem gaga24_regular_carrier_equation {g : ℕ} {J : Type}
    {V : J → Set (Fin g → ℂ)} {f : J → (Fin g → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f) (C : gaga21_GlobalComponent V f)
    {x : Fin g → ℂ}
    (hx : x ∈ gaga21_regularSupport V f ∩ gaga21_componentCarrier C) :
    ∃ (U : Set (Fin g → ℂ)) (P : (Fin g → ℂ) → ℂ),
      IsOpen U ∧ x ∈ U ∧ AnalyticOnNhd ℂ P U ∧
      ∀ y ∈ U, (y ∈ gaga21_regularSupport V f ∩ gaga21_componentCarrier C ↔
        y ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero P) := by
  obtain ⟨hxs, P, hPa, hP0, hPd, he⟩ := hx.1
  have hev : ∀ᶠ y in 𝓝 x, AnalyticAt ℂ P y ∧ fderiv ℂ P y ≠ 0 ∧
      (y ∈ localDivisorSupport V f ↔ P y = 0) ∧
      (y ∈ gaga21_regularSupport V f → y ∈ gaga21_componentCarrier C) := by
    filter_upwards [hPa.eventually_analyticAt,
      hPa.fderiv.continuousAt.eventually_ne hPd, he,
      gaga21_b2_regular_carrier_local hD C hx.1] with y ha hd he hc
    exact ⟨ha, hd, he, fun hy ↦ (hc hy).mpr hx.2⟩
  obtain ⟨U, hU, hUo, hxU⟩ := eventually_nhds_iff.mp hev
  refine ⟨U, P, hUo, hxU, fun y hy ↦ (hU y hy).1, fun y hy ↦ ?_⟩
  constructor
  · intro hyr
    exact ⟨(hU y hy).2.2.1.mp hyr.1.1, (hU y hy).2.1⟩
  · intro hyr
    have hyR : y ∈ gaga21_regularSupport V f := by
      refine ⟨(hU y hy).2.2.1.mpr hyr.1, P, (hU y hy).1, hyr.1, hyr.2, ?_⟩
      filter_upwards [hUo.mem_nhds hy] with z hz
      exact (hU z hz).2.2.1
    exact ⟨hyR, (hU y hy).2.2.2 hyR⟩

theorem gaga24_carrier_complement_closure {g : ℕ} {J : Type}
    {V : J → Set (Fin g → ℂ)} {f : J → (Fin g → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f) (C : gaga21_GlobalComponent V f)
    {A : Set (Fin g → ℂ)} (hA : IsClosedAnalytic (Fin g → ℂ) A)
    (hproper : ¬ gaga21_componentCarrier C ⊆ A) :
    closure (gaga21_componentCarrier C \ A) = closure (gaga21_componentCarrier C) := by
  have happ := gaga21_b2_carrier_approximation hD C
  have hreg : ¬ gaga21_regularSupport V f ∩ gaga21_componentCarrier C ⊆ A := by
    intro h
    exact hproper (happ.trans (hA.isClosed.closure_subset_iff.mpr h))
  have he := gaga24_regular_complement_closure
    (gaga21_b2_regular_connected hD C) (fun x hx ↦ gaga24_regular_carrier_equation hD C hx)
    hA hreg
  apply Subset.antisymm (closure_mono sdiff_subset)
  apply closure_minimal _ isClosed_closure
  apply happ.trans
  rw [← he]
  exact closure_mono (fun y hy ↦ ⟨hy.1.2, hy.2⟩)

theorem gaga24_abelianExp_preimage_isClosedAnalytic
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {A : Set (ComplexPoint X)}
    (hA : IsClosedAnalytic (Fin (dim X.left) → ℂ) A) :
    IsClosedAnalytic (Fin (dim X.left) → ℂ) (abelianExp X ⁻¹' A) ∧
      ∀ v : Fin (dim X.left) → ℂ, ∀ l : abelianPeriodLattice X,
        (v + l ∈ abelianExp X ⁻¹' A ↔ v ∈ abelianExp X ⁻¹' A) := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  have := spec_lieGroup_complexPoint X (dim X.left)
  refine ⟨AnalyticDivisorAlgebraic3.spec_isClosedAnalytic_preimage
    (spec_contMDiff_complexExponential X (dim X.left)) hA, ?_⟩
  intro v l
  change abelianExp X (v + l) ∈ A ↔ abelianExp X v ∈ A
  rw [abelianExp_add_lattice X v l]

theorem gaga24_descended_complement_closure
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (O : (gaga22_descendedOnX X hD hper).Component)
    {A : Set (ComplexPoint X)} (hA : IsClosedAnalytic (Fin (dim X.left) → ℂ) A)
    (hproper : ¬ (gaga22_descendedOnX X hD hper).carrier O ⊆ A) :
    closure ((gaga22_descendedOnX X hD hper).carrier O \ A) =
      closure ((gaga22_descendedOnX X hD hper).carrier O) := by
  have hpre : ¬ gaga21_componentCarrier (Quotient.out O) ⊆ abelianExp X ⁻¹' A := by
    intro h
    apply hproper
    rintro z ⟨v, hv, rfl⟩
    exact h hv
  have he := gaga24_carrier_complement_closure hD (Quotient.out O)
    (gaga24_abelianExp_preimage_isClosedAnalytic X hA).1 hpre
  change closure (abelianExp X '' gaga21_componentCarrier (Quotient.out O) \ A) =
    closure (abelianExp X '' gaga21_componentCarrier (Quotient.out O))
  rw [← image_sdiff_preimage, ← closure_image_closure (continuous_abelianExp X), he,
    closure_image_closure (continuous_abelianExp X)]

theorem gaga24_smooth_support_eq_sdiff
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) :
    cycleComponentSmoothSupport X x = cycleComponentSupport X x \
      (cycleComponentSingularAnalyticClosedFiltration X x 0 : Set (ComplexPoint X)) := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    constructor
    · change cycleComponentι X.left x p.underlying ∈ closure ({x} : Set X.left)
      rw [← range_cycleComponentι X.left x]
      exact ⟨p.underlying, rfl⟩
    · rintro ⟨y, hy, he⟩
      change cycleComponentι X.left x y = cycleComponentι X.left x p.underlying at he
      have he' := (cycleComponentι X.left x).isClosedEmbedding.injective he
      subst y
      exact hy hp
  · rintro ⟨hzC, hzS⟩
    let p := cycleComponentComplexPointLift X x z hzC
    refine ⟨p, ?_, cycleComponentMap_lift X x z hzC⟩
    by_contra hp
    apply hzS
    refine ⟨p.underlying, hp, ?_⟩
    exact congrArg Point.underlying (cycleComponentMap_lift X x z hzC)

/-- Analytic smooth-locus density for the algebraic carrier of a descended divisor orbit.
Source: Chirka, Complex Analytic Sets, §2.3 and §5.1;
`gaga21_b2_carrier_approximation` and `gaga22_chow_support`. -/
theorem gaga24_smooth_dense_orbit
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C)
    (O : (gaga22_descendedOnX X hD hper).Component) :
    Dense (cycleComponentSmoothAnalyticLocus X (gaga23_point X hD hper hChow O)) := by
  let x := gaga23_point X hD hper hChow O
  have he : (gaga22_descendedOnX X hD hper).carrier O = cycleComponentSupport X x := by
    have h := (gaga22_chow_support X hD hper hChow).2.choose_spec.2.1 O
    change _ = (Point.underlying : ComplexPoint X → X.left) ⁻¹' closure ({x} : Set X.left)
    rw [show closure ({x} : Set X.left) = gaga23_carrier X hD hper hChow O from
      h.2.1.closure_genericPoint h.1]
    exact h.2.2.1
  have hp : ¬ (gaga22_descendedOnX X hD hper).carrier O ⊆
      (cycleComponentSingularAnalyticClosedFiltration X x 0 : Set (ComplexPoint X)) := by
    rw [he]
    exact gaga24_singular_support_proper X x
  have hc := gaga24_descended_complement_closure X hD hper O
    (gaga24_singular_filtration_isClosedAnalytic X x 0) hp
  rw [he, ← gaga24_smooth_support_eq_sdiff X x] at hc
  let i : Over.mk (cycleComponentι X.left x ≫ X.hom) ⟶ X :=
    Over.homMk (cycleComponentι X.left x) rfl
  let : IsClosedImmersion i.left :=
    inferInstanceAs (IsClosedImmersion (cycleComponentι X.left x))
  have hi : IsClosedEmbedding (cycleComponentMap X x) :=
    isClosedEmbedding_map_of_closedImmersion i
  intro z
  rw [hi.isInducing.closure_eq_preimage_closure_image]
  change cycleComponentMap X x z ∈ closure (cycleComponentSmoothSupport X x)
  rw [hc]
  apply subset_closure
  change cycleComponentι X.left x z.underlying ∈ closure ({x} : Set X.left)
  rw [← range_cycleComponentι X.left x]
  exact ⟨z.underlying, rfl⟩

/-- An open polynomial-coordinate projection makes the nonvanishing locus of every
nonzero algebraic element analytically dense.
Source: `IsAlgebraic.exists_nonzero_coeff_and_aeval_eq_zero` and
`MvPolynomial.dense_complex_nonzero`. -/
theorem gaga24_dense_nonvanishing_of_open_projection
    {n : ℕ} (T : Type) [CommRing T] [IsDomain T] [Algebra ℂ T]
    [Algebra (ComplexAlgHom.complexPolynomialRing n) T]
    [IsScalarTower ℂ (ComplexAlgHom.complexPolynomialRing n) T]
    (hopen : IsOpenMap (fun v : T →ₐ[ℂ] ℂ ↦
      ComplexAlgHom.mvPolynomialAlgHomHomeomorph n
        (ComplexAlgHom.etaleBaseAlgHom T v)))
    (b : T) (hb : b ≠ 0)
    (halg : IsAlgebraic (ComplexAlgHom.complexPolynomialRing n) b) :
    Dense {v : T →ₐ[ℂ] ℂ | v b ≠ 0} := by
  obtain ⟨p, hp0, hp⟩ := halg.exists_nonzero_coeff_and_aeval_eq_zero
    (mem_nonZeroDivisors_of_ne_zero hb)
  rw [dense_iff_inter_open]
  intro O hO hOne
  let q := fun v : T →ₐ[ℂ] ℂ ↦
    ComplexAlgHom.mvPolynomialAlgHomHomeomorph n
      (ComplexAlgHom.etaleBaseAlgHom T v)
  obtain ⟨w, ⟨v, hvO, hvw⟩, hw⟩ :=
    (MvPolynomial.dense_complex_nonzero (p.coeff 0) hp0).inter_open_nonempty
      (q '' O) (hopen O hO) (hOne.image q)
  refine ⟨v, hvO, ?_⟩
  intro hvb
  have hkill := Polynomial.map_coeff_zero_eq_zero_of_map_eq_zero hp
    (ComplexAlgHom.etaleBaseAlgHom T v).toRingHom v.toRingHom rfl hvb
  have heq : MvPolynomial.aeval (q v) = ComplexAlgHom.etaleBaseAlgHom T v :=
    (ComplexAlgHom.mvPolynomialAlgHomHomeomorph n).symm_apply_apply _
  have heval := congrArg (fun f : ComplexAlgHom.complexPolynomialRing n →ₐ[ℂ] ℂ ↦
    f (p.coeff 0)) heq
  have hz : (MvPolynomial.aeval (q v)) (p.coeff 0) = 0 := heval.trans hkill
  exact hw (hvw ▸ hz)

open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
  HodgeLean.Foundations.AnalyticDivisorAlgebraic4 in
theorem gaga24_root_mem_closure_over_base {n d : ℕ}
    {a : Fin d → (Fin n → ℂ) → ℂ} {B : Set (Fin n → ℂ)}
    {z : Fin n → ℂ} {w : ℂ} (ha : ∀ j, AnalyticAt ℂ (a j) z)
    (hz : z ∈ closure B) (hw : monicInLast a (z, w) = 0) :
    (z, w) ∈ closure {y : (Fin n → ℂ) × ℂ | y.1 ∈ B ∧ monicInLast a y = 0} := by
  rw [Metric.mem_closure_iff] at hz ⊢
  intro ε hε
  obtain ⟨m, hm⟩ := laneC_order_monicInLast_natCast a z w
  have hm0 : m ≠ 0 := by
    intro h
    have horder := analyticOrderAt_ne_zero.mpr
      ⟨(laneC_analyticAt_monicInLast ha w).comp₂ analyticAt_const analyticAt_id, hw⟩
    exact horder (hm.trans (by rw [h]; rfl))
  obtain ⟨r, hr, hrε, δ, hδ, -, -, hcount⟩ :=
    spec_exists_zeroCount_eq_order (laneC_analyticAt_monicInLast ha w) hm hε
  obtain ⟨z', hzB, hzz'⟩ := hz (min δ ε) (lt_min hδ hε)
  have hball : z' ∈ Metric.ball z δ := by
    rw [Metric.mem_ball, dist_comm]
    exact hzz'.trans_le (min_le_left _ _)
  have hc := hcount z' hball
  obtain ⟨w', hw', hw'0⟩ : ∃ w' ∈ Metric.ball w r,
      analyticOrderNatAt (fun v ↦ monicInLast a (z', v)) w' ≠ 0 := by
    apply exists_ne_zero_of_finsum_mem_ne_zero
    rw [← zeroCount, hc]
    exact hm0
  refine ⟨(z', w'), ⟨hzB, apply_eq_zero_of_analyticOrderNatAt_ne_zero
    (f := fun v ↦ monicInLast a (z', v)) hw'0⟩, ?_⟩
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨hzz'.trans_le (min_le_right _ _), by
    rw [dist_comm]
    exact (Metric.mem_ball.mp hw').trans hrε⟩

open HodgeLean.Foundations.AnalyticDivisorAlgebraic4 in
/-- Projection from a monic analytic polynomial zero set is open, including at multiple roots.
Source: `gaga24_root_mem_closure_over_base`. -/
theorem gaga24_monic_zero_projection_open {n d : ℕ}
    (a : Fin d → (Fin n → ℂ) → ℂ) (ha : ∀ j z, AnalyticAt ℂ (a j) z) :
    IsOpenMap (fun y : {y : (Fin n → ℂ) × ℂ | monicInLast a y = 0} ↦ y.val.1) := by
  intro O hO
  rw [← isClosed_compl_iff, ← closure_subset_iff_isClosed]
  intro z hz hzO
  obtain ⟨y, hyO, rfl⟩ := hzO
  let B := (Prod.fst ∘ Subtype.val '' O)ᶜ
  have hc := gaga24_root_mem_closure_over_base (fun j ↦ ha j y.val.1) hz y.property
  have he : ((↑) : {y : (Fin n → ℂ) × ℂ | monicInLast a y = 0} →
      (Fin n → ℂ) × ℂ) '' {u | u.val.1 ∈ B} =
      {u : (Fin n → ℂ) × ℂ | u.1 ∈ B ∧ monicInLast a u = 0} := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨hv, v.property⟩
    · rintro ⟨hu, hp⟩
      exact ⟨⟨u, hp⟩, hu, rfl⟩
  have hycl : y ∈ closure {u : {y : (Fin n → ℂ) × ℂ | monicInLast a y = 0} |
      u.val.1 ∈ B} := by
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, he]
    exact hc
  have hsub : {u : {y : (Fin n → ℂ) × ℂ | monicInLast a y = 0} |
      u.val.1 ∈ B} ⊆ Oᶜ := by
    intro u hu huO
    exact hu ⟨u, huO, rfl⟩
  exact (hO.isClosed_compl.closure_subset (closure_mono hsub hycl)) hyO

/-- Complex algebra homomorphisms form a closed subset of the space of all functions.
Source: the closed equations for preservation of ring operations and scalars. -/
theorem gaga24_algHom_isClosedEmbedding (T : Type) [CommRing T] [Algebra ℂ T] :
    IsClosedEmbedding (fun v : T →ₐ[ℂ] ℂ ↦ (v : T → ℂ)) := by
  refine ⟨⟨⟨rfl⟩, fun a b h ↦ AlgHom.ext (congrFun h)⟩, ?_⟩
  have he : Set.range (fun v : T →ₐ[ℂ] ℂ ↦ (v : T → ℂ)) =
      {f : T → ℂ | f 0 = 0 ∧ f 1 = 1 ∧
        (∀ x y, f (x + y) = f x + f y) ∧
        (∀ x y, f (x * y) = f x * f y) ∧
        ∀ c : ℂ, f (algebraMap ℂ T c) = c} := by
    ext f
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v.map_zero, v.map_one, v.map_add, v.map_mul, v.commutes⟩
    · rintro ⟨h0, h1, ha, hm, hc⟩
      let v : T →ₐ[ℂ] ℂ :=
        { toFun := f
          map_zero' := h0
          map_one' := h1
          map_add' := ha
          map_mul' := hm
          commutes' := hc }
      exact ⟨v, rfl⟩
  rw [he]
  simp only [setOf_and, setOf_forall]
  exact (isClosed_eq (continuous_apply 0) continuous_const).inter
    ((isClosed_eq (continuous_apply 1) continuous_const).inter
      ((isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
        isClosed_eq (continuous_apply (x + y))
          ((continuous_apply x).add (continuous_apply y))).inter
        ((isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
          isClosed_eq (continuous_apply (x * y))
            ((continuous_apply x).mul (continuous_apply y))).inter
          (isClosed_iInter fun c ↦
            isClosed_eq (continuous_apply (algebraMap ℂ T c)) continuous_const))))

/-- An integral coordinate is uniformly bounded above compact sets of base points.
Source: Cauchy's bound for roots of monic polynomials. -/
theorem gaga24_integral_coordinate_bound
    (R T : Type) [CommRing R] [CommRing T] [Algebra ℂ R] [Algebra ℂ T]
    [Algebra R T] [IsScalarTower ℂ R T]
    (K : Set (R →ₐ[ℂ] ℂ)) (hK : IsCompact K)
    (b : T) (hb : IsIntegral R b) :
    ∃ M : NNReal, ∀ v : T →ₐ[ℂ] ℂ,
      v.comp (IsScalarTower.toAlgHom ℂ R T) ∈ K → ‖v b‖₊ ≤ M := by
  classical
  obtain ⟨p, hp, hpb⟩ := hb
  let B : (R →ₐ[ℂ] ℂ) → NNReal :=
    fun u ↦ (Finset.range p.natDegree).sup (fun i ↦ ‖u (p.coeff i)‖₊) + 1
  have hB : Continuous B :=
    (Continuous.finset_sup_apply fun i _ ↦
      (continuous_affineAlgebraHom_apply R (p.coeff i)).nnnorm).add continuous_const
  obtain ⟨M, hM⟩ := hK.bddAbove_image hB.continuousOn
  refine ⟨M, fun v hv ↦ le_trans ?_ (hM (mem_image_of_mem B hv))⟩
  let u := v.comp (IsScalarTower.toAlgHom ℂ R T)
  have hroot : (p.map u.toRingHom).IsRoot (v b) := by
    change (p.map u.toRingHom).eval (v b) = 0
    rw [Polynomial.eval_map]
    have he := congrArg v hpb
    change v.toRingHom (Polynomial.eval₂ (algebraMap R T) b p) = v 0 at he
    rw [Polynomial.hom_eval₂] at he
    exact he.trans v.map_zero
  have hbound := hroot.norm_lt_cauchyBound (hp.map u.toRingHom).ne_zero
  have heq : (p.map u.toRingHom).cauchyBound = B u := by
    simp only [Polynomial.cauchyBound, (hp.map u.toRingHom).leadingCoeff,
      nnnorm_one, div_one, hp.natDegree_map, Polynomial.coeff_map, B]
    rfl
  rw [heq] at hbound
  exact hbound.le

/-- Restriction along an integral algebra has compact inverse images of compact sets
of complex points.
Source: Cauchy's root bound and Tychonoff's compactness theorem. -/
theorem gaga24_integral_restriction_compact
    (R T : Type) [CommRing R] [CommRing T] [Algebra ℂ R] [Algebra ℂ T]
    [Algebra R T] [IsScalarTower ℂ R T] [Algebra.IsIntegral R T]
    (K : Set (R →ₐ[ℂ] ℂ)) (hK : IsCompact K) :
    IsCompact ((fun v : T →ₐ[ℂ] ℂ ↦
      v.comp (IsScalarTower.toAlgHom ℂ R T)) ⁻¹' K) := by
  classical
  let q : (T →ₐ[ℂ] ℂ) → (R →ₐ[ℂ] ℂ) :=
    fun v ↦ v.comp (IsScalarTower.toAlgHom ℂ R T)
  have hq : Continuous q := by
    rw [continuous_induced_rng]
    exact continuous_pi fun r ↦ continuous_affineAlgebraHom_apply T (algebraMap R T r)
  letI : T2Space (R →ₐ[ℂ] ℂ) :=
    (gaga24_algHom_isClosedEmbedding R).isEmbedding.t2Space
  choose M hM using fun b : T ↦
    gaga24_integral_coordinate_bound R T K hK b (Algebra.IsIntegral.isIntegral b)
  have hbox : IsCompact (Set.pi univ (fun b : T ↦ Metric.closedBall (0 : ℂ) (M b))) :=
    isCompact_univ_pi fun b ↦ isCompact_closedBall 0 (M b)
  apply ((gaga24_algHom_isClosedEmbedding T).isCompact_preimage hbox).of_isClosed_subset
    (hK.isClosed.preimage hq)
  intro v hv b _
  rw [Metric.mem_closedBall, dist_zero_right]
  exact_mod_cast hM b v hv

/-- Integral polynomial-coordinate projections on complex points are proper.
Source: compact inverse images from integral equations and Cauchy's root bound. -/
theorem gaga24_integral_projection_proper
    {n : ℕ} (T : Type) [CommRing T] [Algebra ℂ T]
    [Algebra (ComplexAlgHom.complexPolynomialRing n) T]
    [IsScalarTower ℂ (ComplexAlgHom.complexPolynomialRing n) T]
    [Algebra.IsIntegral (ComplexAlgHom.complexPolynomialRing n) T] :
    IsProperMap (fun v : T →ₐ[ℂ] ℂ ↦
      ComplexAlgHom.mvPolynomialAlgHomHomeomorph n
        (ComplexAlgHom.etaleBaseAlgHom T v)) := by
  let e := ComplexAlgHom.mvPolynomialAlgHomHomeomorph n
  have hq : Continuous (ComplexAlgHom.etaleBaseAlgHom (n := n) T) := by
    rw [continuous_induced_rng]
    exact continuous_pi fun r ↦ continuous_affineAlgebraHom_apply T
      (algebraMap (ComplexAlgHom.complexPolynomialRing n) T r)
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨e.continuous.comp hq, fun K hK ↦ ?_⟩
  exact gaga24_integral_restriction_compact
    (ComplexAlgHom.complexPolynomialRing n) T (e ⁻¹' K)
      (e.isClosedEmbedding.isCompact_preimage hK)

/-- Complex points extend across an injective integral map of finite-type complex algebras.
Source: the lying-over theorem and the weak Nullstellensatz. -/
theorem gaga24_integral_restriction_surjective
    (R T : Type) [CommRing R] [CommRing T] [Algebra ℂ R] [Algebra ℂ T]
    [Algebra R T] [IsScalarTower ℂ R T] [Algebra.IsIntegral R T]
    [Algebra.FiniteType ℂ T]
    (hinj : Function.Injective (algebraMap R T)) :
    Function.Surjective (fun v : T →ₐ[ℂ] ℂ ↦
      v.comp (IsScalarTower.toAlgHom ℂ R T)) := by
  intro u
  have hu : Function.Surjective u :=
    fun c ↦ ⟨algebraMap ℂ R c, u.commutes c⟩
  letI : (RingHom.ker u.toRingHom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective u.toRingHom hu
  obtain ⟨Q, hQ, hQR⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := T)
      (RingHom.ker u.toRingHom)
      (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  letI : Q.IsMaximal := hQ
  letI : Field (T ⧸ Q) := Ideal.Quotient.field Q
  letI : Module.Finite ℂ (T ⧸ Q) :=
    finite_of_finite_type_of_isJacobsonRing ℂ (T ⧸ Q)
  let e : ℂ ≃ₐ[ℂ] T ⧸ Q :=
    AlgEquiv.ofBijective (Algebra.ofId ℂ (T ⧸ Q))
      IsAlgClosed.algebraMap_bijective_of_isIntegral
  let v : T →ₐ[ℂ] ℂ := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ Q)
  refine ⟨v, AlgHom.ext fun r ↦ ?_⟩
  have hmem : r - algebraMap ℂ R (u r) ∈ RingHom.ker u.toRingHom := by
    change u (r - algebraMap ℂ R (u r)) = 0
    rw [map_sub, u.commutes]
    exact sub_self _
  rw [← hQR] at hmem
  have hzero : Ideal.Quotient.mk Q (algebraMap R T r -
      algebraMap ℂ T (u r)) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa only [Ideal.mem_comap, map_sub, ← IsScalarTower.algebraMap_apply ℂ R T] using hmem
  have heq : Ideal.Quotient.mk Q (algebraMap R T r) =
      algebraMap ℂ (T ⧸ Q) (u r) := by
    rw [map_sub, sub_eq_zero] at hzero
    exact hzero
  change e.symm (Ideal.Quotient.mk Q (algebraMap R T r)) = u r
  rw [heq]
  exact e.symm.commutes (u r)

/-- A finite algebra has finitely many complex points above each fixed base point.
Source: finiteness of the prime-spectrum fibers of a finite algebra. -/
theorem gaga24_finite_restriction_fiber
    (R T : Type) [CommRing R] [CommRing T] [Algebra ℂ R] [Algebra ℂ T]
    [Algebra R T] [IsScalarTower ℂ R T] [Module.Finite R T]
    (u : R →ₐ[ℂ] ℂ) :
    {v : T →ₐ[ℂ] ℂ | v.comp (IsScalarTower.toAlgHom ℂ R T) = u}.Finite := by
  let k : (T →ₐ[ℂ] ℂ) → PrimeSpectrum T :=
    fun v ↦ ⟨RingHom.ker v.toRingHom, RingHom.ker_isPrime v.toRingHom⟩
  have hk : Function.Injective k := by
    intro v w h
    apply AlgHom.ext
    intro b
    have hker : RingHom.ker v.toRingHom = RingHom.ker w.toRingHom :=
      congrArg PrimeSpectrum.asIdeal h
    have hmem : b - algebraMap ℂ T (v b) ∈ RingHom.ker v.toRingHom := by
      change v (b - algebraMap ℂ T (v b)) = 0
      rw [map_sub, v.commutes]
      exact sub_self _
    rw [hker] at hmem
    change w (b - algebraMap ℂ T (v b)) = 0 at hmem
    rw [map_sub, w.commutes] at hmem
    exact (sub_eq_zero.mp hmem).symm
  let P : PrimeSpectrum R := ⟨RingHom.ker u.toRingHom, RingHom.ker_isPrime u.toRingHom⟩
  apply ((Algebra.QuasiFinite.finite_comap_preimage_singleton (S := T) P).preimage hk.injOn).subset
  intro v hv
  change PrimeSpectrum.comap (algebraMap R T) (k v) = P
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap R T) (RingHom.ker v.toRingHom) = RingHom.ker u.toRingHom
  exact congrArg (fun f : R →ₐ[ℂ] ℂ ↦ RingHom.ker f.toRingHom) hv

/-- One algebra element distinguishes a chosen complex point from every other point
in a finite set.
Source: a vector space over an infinite field is not a finite union of proper subspaces. -/
theorem gaga24_separate_finite_points
    (T : Type) [CommRing T] [Algebra ℂ T]
    (S : Set (T →ₐ[ℂ] ℂ)) (hS : S.Finite) (u : T →ₐ[ℂ] ℂ) :
    ∃ b : T, ∀ v ∈ S, v b = u b → v = u := by
  classical
  let F := S \ {u}
  have hF : F.Finite := hS.subset sdiff_subset
  letI : Fintype F := hF.fintype
  obtain ⟨b, hb⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun v : F ↦ v.val.toLinearMap - u.toLinearMap) (fun v ↦ by
      by_contra! h
      have heq : v.val = u := AlgHom.ext fun t ↦ sub_eq_zero.mp (h t)
      exact v.property.2 (Set.mem_singleton_iff.mpr heq))
  refine ⟨b, fun v hv heq ↦ ?_⟩
  by_contra hne
  exact hb ⟨v, hv, hne⟩ (sub_eq_zero.mpr heq)

/-- Closure can be lifted through a closed map at any point with a singleton fiber.
Source: closed maps send the closure of a set onto a set containing the closure of its image. -/
theorem gaga24_mem_closure_of_singleton_fiber
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {f : A → B} (hf : IsClosedMap f) (x : A)
    (hx : ∀ y, f y = f x → y = x) {S : Set A}
    (h : f x ∈ closure (f '' S)) : x ∈ closure S := by
  obtain ⟨y, hy, he⟩ := hf.closure_image_subset S h
  exact hx y he ▸ hy

/-- Each specialized root of an integral element's minimal polynomial is realized
by a complex point of the finite-type algebra.
Source: the minimal-polynomial presentation and integral lying over. -/
theorem gaga24_minpoly_root_lift
    (R T : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing T] [IsDomain T] [Algebra ℂ R] [Algebra ℂ T]
    [Algebra R T] [IsScalarTower ℂ R T] [Algebra.IsIntegral R T]
    [Module.IsTorsionFree R T] [Algebra.FiniteType ℂ T]
    (b : T) (u : R →ₐ[ℂ] ℂ) (w : ℂ)
    (hw : (minpoly R b).eval₂ u.toRingHom w = 0) :
    ∃ v : T →ₐ[ℂ] ℂ, v.comp (IsScalarTower.toAlgHom ℂ R T) = u ∧ v b = w := by
  let S := Algebra.adjoin R ({b} : Set T)
  let e := (minpoly.equivAdjoin (Algebra.IsIntegral.isIntegral (R := R) b)).restrictScalars ℂ
  let l := AdjoinRoot.liftAlgHom (minpoly R b) u w hw
  let a : S →ₐ[ℂ] ℂ := l.comp e.symm.toAlgHom
  letI : Algebra.IsIntegral S T :=
    ⟨fun t ↦ (Algebra.IsIntegral.isIntegral (R := R) t).tower_top⟩
  obtain ⟨v, hv⟩ := gaga24_integral_restriction_surjective S T Subtype.val_injective a
  have hval (s : S) : v s = a s := congrArg (fun f : S →ₐ[ℂ] ℂ ↦ f s) hv
  refine ⟨v, AlgHom.ext fun r ↦ ?_, ?_⟩
  · have h := hval (algebraMap R S r)
    change v (algebraMap R T r) = u r
    rw [show a (algebraMap R S r) = u r from ?_] at h
    · exact h
    change l (e.symm (algebraMap R S r)) = u r
    rw [show e.symm (algebraMap R S r) =
      algebraMap R (AdjoinRoot (minpoly R b)) r from
        (minpoly.equivAdjoin (Algebra.IsIntegral.isIntegral (R := R) b)).symm.commutes r]
    exact AdjoinRoot.liftAlgHom_of _ _ _ _ _
  · let s : S := ⟨b, Algebra.self_mem_adjoin_singleton R b⟩
    have hs : e (AdjoinRoot.root (minpoly R b)) = s := by
      change AdjoinRoot.Minpoly.toAdjoin R b (AdjoinRoot.root (minpoly R b)) = s
      simp only [AdjoinRoot.Minpoly.coe_toAdjoin, AdjoinRoot.liftAlgHom_root]
      rfl
    have h := hval s
    rw [show a s = w from ?_] at h
    · exact h
    change l (e.symm s) = w
    rw [← hs, e.symm_apply_apply]
    exact AdjoinRoot.liftAlgHom_root _ _ _ _

/-- Roots of a monic polynomial over a complex polynomial ring can be approximated
over any base set accumulating at their base point.
Source: local constancy of zero count for monic analytic polynomial families. -/
theorem gaga24_polynomial_root_mem_closure {n : ℕ}
    (p : Polynomial (ComplexAlgHom.complexPolynomialRing n)) (hp : p.Monic)
    {B : Set (Fin n → ℂ)} {z : Fin n → ℂ} {w : ℂ}
    (hz : z ∈ closure B) (hw : p.eval₂ (MvPolynomial.aeval z).toRingHom w = 0) :
    (z, w) ∈ closure {y : (Fin n → ℂ) × ℂ |
      y.1 ∈ B ∧ p.eval₂ (MvPolynomial.aeval y.1).toRingHom y.2 = 0} := by
  let a : Fin p.natDegree → (Fin n → ℂ) → ℂ :=
    fun j z ↦ MvPolynomial.aeval z (p.coeff j)
  have he (y : (Fin n → ℂ) × ℂ) :
      p.eval₂ (MvPolynomial.aeval y.1).toRingHom y.2 =
      AnalyticDivisorAlgebraic4.monicInLast a y := by
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ,
      Polynomial.coeff_natDegree, hp.leadingCoeff, map_one, one_mul]
    simp only [AnalyticDivisorAlgebraic4.monicInLast, a, Fin.sum_univ_eq_sum_range]
    change (∑ i ∈ Finset.range p.natDegree,
      (MvPolynomial.aeval y.1) (p.coeff i) * y.2 ^ i) + y.2 ^ p.natDegree =
      y.2 ^ p.natDegree + ∑ i : Fin p.natDegree,
        (MvPolynomial.aeval y.1) (p.coeff i) * y.2 ^ (i : ℕ)
    rw [Fin.sum_univ_eq_sum_range
      (fun i ↦ (MvPolynomial.aeval y.1) (p.coeff i) * y.2 ^ i), add_comm]
  have hw' : AnalyticDivisorAlgebraic4.monicInLast a (z, w) = 0 :=
    (he (z, w)).symm.trans hw
  have hs : {y : (Fin n → ℂ) × ℂ |
      y.1 ∈ B ∧ p.eval₂ (MvPolynomial.aeval y.1).toRingHom y.2 = 0} =
      {y : (Fin n → ℂ) × ℂ |
        y.1 ∈ B ∧ AnalyticDivisorAlgebraic4.monicInLast a y = 0} := by
    ext y
    change (_ ∧ _) ↔ (_ ∧ _)
    rw [he y]
  rw [hs]
  apply gaga24_root_mem_closure_over_base (a := a) (fun j ↦ ?_) hz hw'
  exact AnalyticAt.aeval_mvPolynomial
    (fun i ↦ (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt z)
    (p.coeff j)

/-- Closure in polynomial coordinates lifts to every point of a finite integral domain.
Source: minimal-polynomial root approximation, lying over, and properness. -/
theorem gaga24_finite_projection_closure
    {n : ℕ} (T : Type) [CommRing T] [IsDomain T] [Algebra ℂ T]
    [Algebra (ComplexAlgHom.complexPolynomialRing n) T]
    [IsScalarTower ℂ (ComplexAlgHom.complexPolynomialRing n) T]
    [Module.Finite (ComplexAlgHom.complexPolynomialRing n) T]
    [Module.IsTorsionFree (ComplexAlgHom.complexPolynomialRing n) T]
    (x : T →ₐ[ℂ] ℂ) (B : Set (Fin n → ℂ))
    (hx : ComplexAlgHom.mvPolynomialAlgHomHomeomorph n
      (ComplexAlgHom.etaleBaseAlgHom T x) ∈ closure B) :
    x ∈ closure ((fun v : T →ₐ[ℂ] ℂ ↦
      ComplexAlgHom.mvPolynomialAlgHomHomeomorph n
        (ComplexAlgHom.etaleBaseAlgHom T v)) ⁻¹' B) := by
  let R := ComplexAlgHom.complexPolynomialRing n
  let e := ComplexAlgHom.mvPolynomialAlgHomHomeomorph n
  let q := fun v : T →ₐ[ℂ] ℂ ↦ e (ComplexAlgHom.etaleBaseAlgHom T v)
  letI : Algebra.FiniteType ℂ T := Algebra.FiniteType.trans (R := ℂ) (S := R) (A := T) inferInstance inferInstance
  obtain ⟨b, hb⟩ := gaga24_separate_finite_points T
    {v | ComplexAlgHom.etaleBaseAlgHom T v = ComplexAlgHom.etaleBaseAlgHom T x}
    (gaga24_finite_restriction_fiber R T (ComplexAlgHom.etaleBaseAlgHom T x)) x
  let h := fun v : T →ₐ[ℂ] ℂ ↦ (q v, v b)
  have hproper : IsProperMap q := gaga24_integral_projection_proper T
  have hc : Continuous h :=
    hproper.continuous.prodMk (continuous_affineAlgebraHom_apply T b)
  have hh : IsClosedMap h :=
    (isProperMap_of_comp_of_t2 hc continuous_fst hproper).isClosedMap
  have hsingle : ∀ y, h y = h x → y = x := by
    intro y hy
    apply hb y
    · exact e.injective (congrArg Prod.fst hy)
    · exact congrArg Prod.snd hy
  apply gaga24_mem_closure_of_singleton_fiber hh x hsingle
  let p := minpoly R b
  have hp : p.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral b)
  have he (v : T →ₐ[ℂ] ℂ) :
      MvPolynomial.aeval (q v) = ComplexAlgHom.etaleBaseAlgHom T v :=
    e.symm_apply_apply _
  have hroot : p.eval₂ (MvPolynomial.aeval (q x)).toRingHom (x b) = 0 := by
    rw [he]
    have hz := minpoly.aeval R b
    rw [Polynomial.aeval_def] at hz
    have hv := congrArg x.toRingHom hz
    rw [Polynomial.hom_eval₂, map_zero] at hv
    exact hv
  have hcl := gaga24_polynomial_root_mem_closure p hp hx hroot
  apply closure_mono (s := {y : (Fin n → ℂ) × ℂ |
    y.1 ∈ B ∧ p.eval₂ (MvPolynomial.aeval y.1).toRingHom y.2 = 0}) ?_ hcl
  rintro ⟨z, w⟩ ⟨hz, hw⟩
  obtain ⟨v, hv, hvb⟩ := gaga24_minpoly_root_lift R T b (MvPolynomial.aeval z) w hw
  have hvz : q v = z := by
    change e (ComplexAlgHom.etaleBaseAlgHom T v) = z
    rw [show ComplexAlgHom.etaleBaseAlgHom T v = MvPolynomial.aeval z from hv]
    exact e.apply_symm_apply z
  exact ⟨v, show q v ∈ B from hvz.symm ▸ hz, Prod.ext hvz hvb⟩

/-- A finite integral-domain polynomial projection is analytically open.
Source: root approximation at a separating integral element in each fiber. -/
theorem gaga24_finite_projection_open
    {n : ℕ} (T : Type) [CommRing T] [IsDomain T] [Algebra ℂ T]
    [Algebra (ComplexAlgHom.complexPolynomialRing n) T]
    [IsScalarTower ℂ (ComplexAlgHom.complexPolynomialRing n) T]
    [Module.Finite (ComplexAlgHom.complexPolynomialRing n) T]
    [Module.IsTorsionFree (ComplexAlgHom.complexPolynomialRing n) T] :
    IsOpenMap (fun v : T →ₐ[ℂ] ℂ ↦
      ComplexAlgHom.mvPolynomialAlgHomHomeomorph n
        (ComplexAlgHom.etaleBaseAlgHom T v)) := by
  let q := fun v : T →ₐ[ℂ] ℂ ↦
    ComplexAlgHom.mvPolynomialAlgHomHomeomorph n (ComplexAlgHom.etaleBaseAlgHom T v)
  intro O hO
  rw [← isClosed_compl_iff, ← closure_subset_iff_isClosed]
  intro z hz hzO
  obtain ⟨x, hxO, rfl⟩ := hzO
  have hc := gaga24_finite_projection_closure T x (q '' O)ᶜ hz
  have hsub : q ⁻¹' (q '' O)ᶜ ⊆ Oᶜ :=
    fun v hv hvO ↦ hv ⟨v, hvO, rfl⟩
  exact (hO.isClosed_compl.closure_subset (closure_mono hsub hc)) hxO

/-- Nonzero functions on every integral finite-type complex algebra have dense
nonvanishing locus, including at singular points.
Source: Noether normalization and openness of finite polynomial projections. -/
theorem gaga24_finiteType_dense_nonvanishing
    (T : Type) [CommRing T] [IsDomain T] [Algebra ℂ T]
    [Algebra.FiniteType ℂ T] (b : T) (hb : b ≠ 0) :
    Dense {v : T →ₐ[ℂ] ℂ | v b ≠ 0} := by
  obtain ⟨N⟩ := Algebra.exists_complexNoetherNormalization T
  let R := ComplexAlgHom.complexPolynomialRing N.dimension
  letI : Algebra R T := N.hom.toAlgebra
  letI : Module.Finite R T := N.finite
  letI : IsScalarTower ℂ R T := IsScalarTower.of_algebraMap_eq' N.hom.comp_algebraMap.symm
  letI : FaithfulSMul R T :=
    (faithfulSMul_iff_algebraMap_injective R T).mpr N.injective
  exact gaga24_dense_nonvanishing_of_open_projection (n := N.dimension) T
    (gaga24_finite_projection_open (n := N.dimension) T) b hb
    (Algebra.IsIntegral.isIntegral b).isAlgebraic

/-- Nonzero global functions on an integral affine complex scheme of finite type
have analytically dense nonvanishing locus.
Source: Noether normalization and the affine complex-point homeomorphism. -/
theorem gaga24_affine_dense_evaluate
    (X : Over (Spec ↧ℂ)) [IsAffine X.left] [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] (r : Γ(X.left, ⊤)) (hr : r ≠ 0) :
    Dense {z : ComplexPoint X | Point.evaluate ⊤ r z ≠ 0} := by
  let A := Γ(X.left, ⊤)
  let φ : ↧ℂ ⟶ A := (Scheme.ΓSpecIso ↧ℂ).inv ≫ X.hom.appTop
  letI : Algebra ℂ A := φ.hom.toAlgebra
  have he : X.left.toSpecΓ ≫ affineSpecStructureMap A = X.hom := by
    apply ext_to_Spec
    exact ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ
  let e := asIso X.left.toSpecΓ
  have hf : affineSpecStructureMap A = e.inv ≫ X.hom := by
    rw [← he]
    change affineSpecStructureMap A = e.inv ≫ e.hom ≫ affineSpecStructureMap A
    rw [Iso.inv_hom_id_assoc]
  letI : LocallyOfFiniteType (affineSpecStructureMap A) := by rw [hf]; infer_instance
  letI : Algebra.FiniteType ℂ A := by
    apply RingHom.finiteType_algebraMap.mp
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := CommRingCat.ofHom (algebraMap ℂ A))).mp
        (inferInstanceAs (LocallyOfFiniteType (affineSpecStructureMap A)))
  let E := (Point.isoMapHomeomorph (Over.isoMk e he)).trans (affineSpecHomeomorph A)
  have hE (z : ComplexPoint X) : E z r = Point.evaluate ⊤ r z := by
    change affineSpecEquiv A (Point.map (Over.homMk X.left.toSpecΓ he) z) r = _
    rw [affineSpecEquiv_apply, Point.evaluate_map]
    change Point.evaluate ⊤
      (X.left.toSpecΓ.appTop ((Scheme.ΓSpecIso ↧A).inv r)) z = _
    rw [Scheme.toSpecΓ_appTop]
    have h := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso ↧A).inv_hom_id) r
    exact congrArg (fun s ↦ Point.evaluate ⊤ s z) h
  have hd := E.isOpenQuotientMap.dense_preimage_iff.mpr
    (gaga24_finiteType_dense_nonvanishing A r hr)
  simpa only [Set.preimage_ofPred_eq, hE] using hd

/-- Every nonempty Zariski open of an integral finite-type complex scheme is analytically dense.
Source: affine nonvanishing density and affine open neighborhoods. -/
theorem gaga24_dense_overOpen (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    (U : X.left.Opens) [Nonempty U] :
    Dense (Point.overOpen U : Set (ComplexPoint X)) := by
  rw [dense_iff_inter_open]
  intro O hO hOne
  obtain ⟨z, hzO⟩ := hOne
  obtain ⟨D, hD, hzD', -⟩ := exists_isAffineOpen_mem_and_subset
    (X := X.left) (x := z.underlying) (U := ⊤) trivial
  letI : IsAffine D.toScheme := hD
  letI : IsAffine (ComplexPoint.openScheme X D).left := hD
  letI : Nonempty D := ⟨⟨z.underlying, hzD'⟩⟩
  letI : Nonempty (ComplexPoint.openScheme X D).left := ⟨⟨z.underlying, hzD'⟩⟩
  letI : IsIntegral (ComplexPoint.openScheme X D).left :=
    isIntegral_of_isOpenImmersion D.ι
  letI : LocallyOfFiniteType (ComplexPoint.openScheme X D).hom :=
    inferInstanceAs (LocallyOfFiniteType (D.ι ≫ X.hom))
  have hzD : z ∈ Point.overOpen D :=
    hzD'
  let zD := ComplexPoint.asOpenPoint X D z hzD
  have hmapzD : Point.map (ComplexPoint.openInclusion X D) zD = z := by
    exact congrArg Subtype.val
      ((ComplexPoint.openHomeomorph X D).apply_symm_apply ⟨z, hzD⟩)
  let W : Set (ComplexPoint (ComplexPoint.openScheme X D)) :=
    Point.map (ComplexPoint.openInclusion X D) ⁻¹' O
  have hWopen : IsOpen W :=
    hO.preimage (ComplexPoint.isOpenEmbedding_map_open X D).continuous
  have hzDW : zD ∈ W := by
    change Point.map (ComplexPoint.openInclusion X D) zD ∈ O
    rwa [hmapzD]
  obtain ⟨uU⟩ : Nonempty U := inferInstance
  obtain ⟨u, huD, huU⟩ : ((D : Set X.left) ∩ U).Nonempty :=
    nonempty_preirreducible_inter D.2 U.2
      ⟨z.underlying, hzD'⟩ ⟨uU.1, uU.2⟩
  let uD : D := ⟨u, huD⟩
  have huPre : uD ∈ D.ι ⁻¹ᵁ U := huU
  obtain ⟨r, hrle, hur⟩ :=
    (isAffineOpen_top D.toScheme).exists_basicOpen_le
      (V := D.ι ⁻¹ᵁ U) ⟨uD, huPre⟩ trivial
  have hopen : D.toScheme.basicOpen r ≠ ⊥ := by
    intro hbot
    rw [hbot] at hur
    exact hur
  have hr : r ≠ 0 := by
    intro h
    apply hopen
    subst r
    exact Scheme.basicOpen_zero _ _
  obtain ⟨y, hyW, hynz⟩ :=
    (gaga24_affine_dense_evaluate (ComplexPoint.openScheme X D) r hr).inter_open_nonempty W hWopen ⟨zD, hzDW⟩
  have hyBasic : y ∈ Point.overOpen (D.toScheme.basicOpen r) :=
    (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
      (X := ComplexPoint.openScheme X D) (U := ⊤) r y trivial).2 hynz
  refine ⟨Point.map (ComplexPoint.openInclusion X D) y, hyW, ?_⟩
  change (Point.map (ComplexPoint.openInclusion X D) y).underlying ∈ U
  rw [Point.underlying_map]
  exact hrle hyBasic


theorem gaga24_smooth_dense_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    Dense (cycleComponentSmoothAnalyticLocus X x) := by
  obtain ⟨y, hy⟩ := (dense_cycleComponent_smoothLocus X x).nonempty
  letI : Nonempty (cycleComponentι X.left x ≫ X.hom).smoothLocus := ⟨⟨y, hy⟩⟩
  let Y := Over.mk (cycleComponentι X.left x ≫ X.hom)
  letI : IsIntegral Y.left := inferInstanceAs (IsIntegral (cycleComponent X.left x))
  letI : LocallyOfFiniteType Y.hom :=
    inferInstanceAs (LocallyOfFiniteType (cycleComponentι X.left x ≫ X.hom))
  exact gaga24_dense_overOpen Y (cycleComponentι X.left x ≫ X.hom).smoothLocus

theorem gaga24_proper_aux (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C)
    (O : (gaga22_descendedOnX X hD hper).Component) :
    gaga23_carrier X hD hper hChow O ≠ univ ∧
      1 ≤ Order.coheight (gaga23_point X hD hper hChow O) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, (0 : Fin (dim X.left) → ℂ) ∈ V i := by
    exact mem_iUnion.mp (hD.2.1.symm ▸ mem_univ 0)
  obtain ⟨y, hyV, hyf⟩ : ∃ y, y ∈ V i ∧ f i y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hD.2.2.2.1 i 0 hi (by
      filter_upwards [(hD.1 i).mem_nhds hi] with y hy
      exact h y hy)
  have hyS : y ∉ localDivisorSupport V f := by
    intro hy
    exact hyf ((spec_mem_localDivisorSupport_iff hD i y hyV).mp hy)
  have hproper : gaga23_carrier X hD hper hChow O ≠ univ := by
    intro hfull
    change (gaga22_chow_support X hD hper hChow).2.choose O = univ at hfull
    have hexp : abelianExp X y ∈ (gaga22_descendedOnX X hD hper).carrier O := by
      rw [(gaga22_chow_support X hD hper hChow).2.choose_spec.2.1 O |>.2.2.1,
        hfull]
      exact mem_univ _
    obtain ⟨z, hzC, hzy⟩ := hexp
    have hzS : z ∈ localDivisorSupport V f :=
      gaga21_b2_carrier_support hD (Quotient.out O) hzC
    let l : abelianPeriodLattice X := ⟨y - z, sub_mem_of_abelianExp_eq X hzy⟩
    have hyl : y = z + (l : Fin (dim X.left) → ℂ) := by
      simp [l]
    apply hyS
    rw [hyl, gaga22_localDivisorSupport_add_iff
      (abelianPeriodLattice X).toAddSubgroup hD hper l z]
    exact hzS
  refine ⟨hproper, Order.one_le_iff_pos.mpr ?_⟩
  rw [Order.coheight_pos]
  intro hmax
  have hzero : Order.coheight (gaga23_point X hD hper hChow O) = 0 :=
    Order.coheight_eq_zero.mpr hmax
  have hpoint : gaga23_point X hD hper hChow O = genericPoint X.left :=
    eq_genericPoint_of_coheight_zero _ hzero
  apply hproper
  have hclosure :=
    ((gaga22_chow_support X hD hper hChow).2.choose_spec.2.1 O).2.1.closure_genericPoint
      ((gaga22_chow_support X hD hper hChow).2.choose_spec.2.1 O).1
  change closure ({gaga23_point X hD hper hChow O} : Set X.left) =
    gaga23_carrier X hD hper hChow O at hclosure
  rw [hpoint, genericPoint_closure] at hclosure
  exact hclosure.symm

private theorem gaga24_exp_carrier_iff_eventually (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (O : (gaga22_descendedOnX X hD hper).Component)
    {p : Fin (dim X.left) → ℂ}
    (hpR : p ∈ gaga21_regularSupport V f)
    (hpC : p ∈ gaga21_componentCarrier (Quotient.out O)) :
    ∀ᶠ z in 𝓝 p, abelianExp X z ∈ (gaga22_descendedOnX X hD hper).carrier O ↔
      z ∈ gaga21_componentCarrier (Quotient.out O) := by
  let Λ := (abelianPeriodLattice X).toAddSubgroup
  filter_upwards [gaga23_eventually_carrier_incident hD p] with z hinc
  constructor
  · rintro ⟨w, hwC, hwz⟩
    let l : Λ := ⟨w - z, sub_mem_of_abelianExp_eq X hwz.symm⟩
    let C' := gaga22_translateComponent Λ hD hper (-l) (Quotient.out O)
    have hzC' : z ∈ gaga21_componentCarrier C' := by
      rw [gaga22_carrier_translate Λ hD hper (-l) (Quotient.out O)]
      refine ⟨w, hwC, ?_⟩
      simp only [l, AddSubgroup.coe_neg]
      abel
    have hpC' := hinc C' hzC'
    obtain ⟨a, ha, hap⟩ := hpC
    obtain ⟨b, hb, hbp⟩ := hpC'
    have hab : Quotient.mk (gaga21_componentSetoid V f) a =
        Quotient.mk (gaga21_componentSetoid V f) b :=
      gaga21_f2_regular_class hD a b (hbp.trans hap.symm) (hap ▸ hpR)
    have hCC' : Quotient.out O = C' := ha.symm.trans (hab.trans hb)
    rwa [← hCC'] at hzC'
  · intro hzC
    exact ⟨z, hzC, rfl⟩

theorem gaga24_common_regular_aux (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C)
    (O : (gaga22_descendedOnX X hD hper).Component) :
    ∃ (p : Fin (dim X.left) → ℂ) (g : (Fin (dim X.left) → ℂ) → ℂ),
      abelianExp X p ∈ cycleComponentSmoothSupport X (gaga23_point X hD hper hChow O) ∧
      AnalyticAt ℂ g p ∧ g p = 0 ∧ fderiv ℂ g p ≠ 0 ∧
      (∀ᶠ z in 𝓝 p, g z = 0 ↔ abelianExp X z ∈
        gaga23_componentSupport X (gaga23_point X hD hper hChow O)) := by
  classical
  let C : gaga21_GlobalComponent V f := Quotient.out O
  obtain ⟨p₀, hpR, hpC⟩ := (gaga21_carrier_geometry hD C).2.2.2.1.nonempty
  have hpR' := hpR
  obtain ⟨-, g, hga, hg0, hgd, hsupport⟩ := hpR'
  obtain ⟨N, hN, hNo, hpN⟩ := eventually_nhds_iff.mp
    (hga.eventually_analyticAt.and
      ((hga.fderiv.continuousAt.eventually_ne hgd).and hsupport))
  have hCsupport : ∀ᶠ z in 𝓝 p₀,
      z ∈ gaga21_componentCarrier C ↔ z ∈ localDivisorSupport V f := by
    filter_upwards [hNo.mem_nhds hpN,
      gaga21_b2_regular_carrier_local hD C hpR] with z hzN hclass
    constructor
    · intro hzC
      exact gaga21_b2_carrier_support hD C hzC
    · intro hz
      have hzr : z ∈ gaga21_regularSupport V f := by
        refine ⟨hz, g, (hN z hzN).1, (hN z hzN).2.2.mp hz, (hN z hzN).2.1, ?_⟩
        exact Filter.Eventually.mono (hNo.mem_nhds hzN) fun y hy ↦ (hN y hy).2.2
      apply (hclass hzr).mpr
      exact hpC
  have horbit := gaga24_exp_carrier_iff_eventually X hD hper O hpR hpC
  have hlocal : ∀ᶠ z in 𝓝 p₀, g z = 0 ↔
      abelianExp X z ∈ (gaga22_descendedOnX X hD hper).carrier O := by
    filter_upwards [hsupport, hCsupport, horbit] with z hs hc ho
    exact hs.symm.trans (hc.symm.trans ho.symm)
  have hcarrier : (gaga22_descendedOnX X hD hper).carrier O =
      gaga23_componentSupport X (gaga23_point X hD hper hChow O) := by
    unfold gaga23_componentSupport gaga23_point
    let h := gaga22_chow_support X hD hper hChow
    rw [(h.2.choose_spec.2.1 O).2.1.closure_genericPoint (h.2.choose_spec.2.1 O).1]
    exact (h.2.choose_spec.2.1 O).2.2.1
  have hexpC : abelianExp X p₀ ∈
      gaga23_componentSupport X (gaga23_point X hD hper hChow O) := by
    rw [← hcarrier]
    exact ⟨p₀, hpC, rfl⟩
  have hexpCycle : abelianExp X p₀ ∈
      cycleComponentSupport X (gaga23_point X hD hper hChow O) := hexpC
  let q₀ := cycleComponentComplexPointLift X (gaga23_point X hD hper hChow O)
    (abelianExp X p₀) hexpCycle
  letI : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  obtain ⟨e, hpSource, he, hs⟩ :=
    spec_complexExponential_localBiholomorph X (dim X.left) p₀
  have hexpTarget : abelianExp X p₀ ∈ e.target := by
    change (complexExponential X (dim X.left) p₀).toMul ∈ e.target
    simpa only [he hpSource] using e.map_source hpSource
  have heinv : e.symm (abelianExp X p₀) = p₀ := by
    change e.symm (complexExponential X (dim X.left) p₀).toMul = p₀
    rw [show (complexExponential X (dim X.left) p₀).toMul = e p₀ from he hpSource]
    exact e.left_inv hpSource
  have hgood : ∀ᶠ q in 𝓝 q₀,
      let p := e.symm (cycleComponentMap X (gaga23_point X hD hper hChow O) q)
      cycleComponentMap X (gaga23_point X hD hper hChow O) q ∈ e.target ∧
      p ∈ e.source ∧ AnalyticAt ℂ g p ∧ fderiv ℂ g p ≠ 0 ∧
        (∀ᶠ z in 𝓝 p, g z = 0 ↔ abelianExp X z ∈
          gaga23_componentSupport X (gaga23_point X hD hper hChow O)) := by
    have hmap : Tendsto (cycleComponentMap X (gaga23_point X hD hper hChow O))
        (𝓝 q₀) (𝓝 (abelianExp X p₀)) := by
      rw [← cycleComponentMap_lift X (gaga23_point X hD hper hChow O)
        (abelianExp X p₀) hexpCycle]
      exact (Point.continuous_map _).continuousAt
    have hinv : Tendsto (fun q ↦ e.symm (cycleComponentMap X
        (gaga23_point X hD hper hChow O) q)) (𝓝 q₀) (𝓝 p₀) := by
      rw [← heinv]
      exact (e.continuousAt_symm hexpTarget).tendsto.comp hmap
    have hfinal : ∀ᶠ z in 𝓝 p₀, g z = 0 ↔ abelianExp X z ∈
        gaga23_componentSupport X (gaga23_point X hD hper hChow O) := by
      filter_upwards [hlocal] with z hz
      rwa [← hcarrier]
    obtain ⟨M, hM, hMo, hpM⟩ := eventually_nhds_iff.mp hfinal
    filter_upwards [hmap.eventually (e.open_target.mem_nhds hexpTarget),
      hinv.eventually (e.open_source.mem_nhds hpSource),
      hinv.eventually hga.eventually_analyticAt,
      hinv.eventually (hga.fderiv.continuousAt.eventually_ne hgd),
      hinv.eventually (hMo.mem_nhds hpM)] with q hqt hqs hqa hqd hqM
    dsimp only
    exact ⟨hqt, hqs, hqa, hqd,
      Filter.Eventually.mono (hMo.mem_nhds hqM) fun z hz ↦ hM z hz⟩
  obtain ⟨q, hqSmooth, hqgood⟩ :=
    (gaga24_smooth_dense_aux X (gaga23_point X hD hper hChow O)).inter_nhds_nonempty hgood
  let p := e.symm (cycleComponentMap X (gaga23_point X hD hper hChow O) q)
  have hpExp : abelianExp X p =
      cycleComponentMap X (gaga23_point X hD hper hChow O) q := by
    change (complexExponential X (dim X.left) p).toMul = _
    rw [show (complexExponential X (dim X.left) p).toMul = e p from he hqgood.2.1]
    exact e.right_inv hqgood.1
  have hpComp : abelianExp X p ∈
      gaga23_componentSupport X (gaga23_point X hD hper hChow O) := by
    rw [hpExp]
    change (cycleComponentMap X (gaga23_point X hD hper hChow O) q).underlying ∈
      closure ({gaga23_point X hD hper hChow O} : Set X.left)
    exact q.underlying.property
  refine ⟨p, g, ?_, hqgood.2.2.1, hqgood.2.2.2.2.self_of_nhds.mpr hpComp,
    hqgood.2.2.2.1, hqgood.2.2.2.2⟩
  refine ⟨q, hqSmooth, ?_⟩
  exact hpExp.symm

private theorem gaga24_regular_graph_chart_analytic_inverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {P : E → ℂ} {x : E} (hP : AnalyticAt ℂ P x) (hPx : P x = 0)
    (hderiv : fderiv ℂ P x ≠ 0) :
    ∃ (g : LinearMap.ker (fderiv ℂ P x : E →ₗ[ℂ] ℂ) → E)
      (k : E → LinearMap.ker (fderiv ℂ P x : E →ₗ[ℂ] ℂ)),
      g 0 = x ∧ AnalyticAt ℂ g 0 ∧ AnalyticAt ℂ k x ∧ k x = 0 ∧
      (∀ᶠ y in 𝓝 x, P y = 0 → g (k y) = y) ∧
      (∀ t, k (g t) = t) ∧ (∀ᶠ t in 𝓝 0, P (g t) = 0) := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, fderiv ℂ P x v ≠ 0 := by
    by_contra hn
    apply hderiv
    ext w
    simpa only [zero_apply] using not_exists_not.mp hn w
  obtain ⟨e, he⟩ := AnalyticDivisorAlgebraic3.spec_exists_prodKerEquiv
    (fderiv ℂ P x) hv
  obtain ⟨ψ, hψ, hψ0, hgraph⟩ :=
    AnalyticDivisorAlgebraic3.spec_exists_analytic_graph hP hPx hv
  let K := LinearMap.ker (fderiv ℂ P x : E →ₗ[ℂ] ℂ)
  let g : K → E := fun t ↦ x + (t : E) + ψ t • v
  let k : E → K := fun y ↦ (e.symm (y - x)).1
  have hg0 : g 0 = x := by simp [g, hψ0]
  have hga : AnalyticAt ℂ g 0 :=
    (analyticAt_const.add (K.subtypeL.analyticAt 0)).add (hψ.smul analyticAt_const)
  have hka : AnalyticAt ℂ k x := by
    exact analyticAt_fst.comp
      ((e.symm.analyticAt _).comp (analyticAt_id.sub analyticAt_const))
  have hk0 : k x = 0 := by simp [k]
  have hkg : ∀ t, k (g t) = t := by
    intro t
    have hrep : g t - x = e (t, ψ t) := by
      rw [he]
      dsimp [g]
      abel
    change (e.symm (g t - x)).1 = t
    rw [hrep, e.symm_apply_apply]
  have hPg : ∀ᶠ t in 𝓝 0, P (g t) = 0 := by
    have ht : Tendsto (fun t : K ↦ (t, ψ t)) (𝓝 0) (𝓝 0) := by
      simpa only [hψ0, id_eq, Prod.mk_zero_zero] using
        (continuousAt_id.prodMk hψ.continuousAt).tendsto
    filter_upwards [ht.eventually hgraph] with t ht
    exact ht.mpr rfl
  refine ⟨g, k, hg0, hga, hka, hk0, ?_, hkg, hPg⟩
  have hevent : Tendsto (fun y ↦ e.symm (y - x)) (𝓝 x) (𝓝 0) := by
    have ht : ContinuousAt (fun y ↦ e.symm (y - x)) x :=
      (e.symm.continuous.comp (continuous_id.sub continuous_const)).continuousAt
    simpa only [ContinuousAt, sub_self, map_zero] using ht
  filter_upwards [hevent.eventually hgraph] with y hy
  intro hPy
  have hrep : x + ((e.symm (y - x)).1 : E) + (e.symm (y - x)).2 • v = y := by
    rw [add_assoc, ← he, e.apply_symm_apply, add_sub_cancel]
  have hψy := hy.mp (hrep.symm ▸ hPy)
  change x + ((e.symm (y - x)).1 : E) + ψ ((e.symm (y - x)).1) • v = y
  rw [hψy, hrep]

private theorem gaga24_dimension_of_flattening
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    {P : E → ℂ} {x : E} (hP : AnalyticAt ℂ P x) (hPx : P x = 0)
    (hderiv : fderiv ℂ P x ≠ 0)
    (e : OpenPartialHomeomorph E (F × G)) (hx : x ∈ e.source) (b : F)
    (he : e x = (b, 0)) (hea : AnalyticAt ℂ e x)
    (heia : AnalyticAt ℂ e.symm (b, 0))
    (hzero : ∀ᶠ y in 𝓝 x, P y = 0 ↔ (e y).2 = 0) :
    Module.finrank ℂ F + 1 = Module.finrank ℂ E := by
  obtain ⟨g, k, hg0, hga, hka, hk0, hgk, hkg, hPg⟩ :=
    gaga24_regular_graph_chart_analytic_inverse hP hPx hderiv
  let K := LinearMap.ker (fderiv ℂ P x : E →ₗ[ℂ] ℂ)
  let u : K → F := fun t ↦ (e (g t)).1
  let v : F → K := fun s ↦ k (e.symm (s, 0))
  have heinv : e.symm (b, 0) = x := by rw [← he, e.left_inv hx]
  have hu : AnalyticAt ℂ u 0 := by
    exact analyticAt_fst.comp ((hg0 ▸ hea).comp hga)
  have hv : AnalyticAt ℂ v b := by
    have hk : AnalyticAt ℂ k (e.symm (b, 0)) := by rwa [heinv]
    exact hk.comp (f := fun s : F ↦ e.symm (s, (0 : G))) (heia.comp (f := fun s : F ↦ (s, (0 : G))) (analyticAt_id.prod analyticAt_const))
  have hu0 : u 0 = b := by dsimp [u]; rw [hg0, he]
  have hvb : v b = 0 := by dsimp [v]; rw [heinv, hk0]
  have hgt : Tendsto g (𝓝 0) (𝓝 x) := by
    simpa only [hg0] using hga.continuousAt.tendsto
  have hit : Tendsto (fun s : F ↦ e.symm (s, 0)) (𝓝 b) (𝓝 x) := by
    have hh : ContinuousAt (fun s : F ↦ e.symm (s, (0 : G))) b :=
      heia.continuousAt.comp (f := fun s : F ↦ (s, (0 : G)))
        (continuousAt_id.prodMk continuousAt_const)
    simpa only [heinv] using hh.tendsto
  have hbt : (b, (0 : G)) ∈ e.target := he ▸ e.map_source hx
  have hpair : ∀ᶠ s : F in 𝓝 b, (s, (0 : G)) ∈ e.target :=
    (continuousAt_id.prodMk continuousAt_const).eventually (e.open_target.mem_nhds hbt)
  have hvu : ∀ᶠ t in 𝓝 (0 : K), v (u t) = t := by
    filter_upwards [hgt.eventually hzero, hPg,
      hgt.eventually (e.open_source.mem_nhds hx)] with t ht hPt hst
    have hz : (e (g t)).2 = 0 := ht.mp hPt
    have hp : ((e (g t)).1, (0 : G)) = e (g t) := by
      rw [← hz]
    change k (e.symm ((e (g t)).1, 0)) = t
    rw [hp, e.left_inv hst, hkg]
  have huv : ∀ᶠ s in 𝓝 b, u (v s) = s := by
    filter_upwards [hit.eventually hzero, hit.eventually hgk, hpair] with s hs hgs hst
    have hPs : P (e.symm (s, 0)) = 0 := hs.mpr (by rw [e.right_inv hst])
    change (e (g (k (e.symm (s, 0))))).1 = s
    rw [hgs hPs, e.right_inv hst]
  have hd := gaga24_chart_dimension_aux (0 : K) b u v hu hv hu0 hvb hvu huv
  rw [← hd]
  exact Module.Dual.finrank_ker_add_one_of_ne_zero
    (show (fderiv ℂ P x : E →ₗ[ℂ] ℂ) ≠ 0 from fun h ↦ hderiv (by ext t; exact congrFun (congrArg DFunLike.coe h) t))

private theorem gaga24_analytic_open_chart_inverse
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (U : X.left.Opens) [SmoothOfRelativeDimension d (openScheme X U).hom]
    (z : ComplexPoint (openScheme X U))
    (e : OpenPartialHomeomorph (ComplexPoint (openScheme X U)) (ComplexPoint X))
    (hez : z ∈ e.source) (he : ∀ y, e y = Point.map (openInclusion X U) y) :
    AnalyticAt ℂ
      (fun v ↦ localChart (openScheme X U) d z
        (e.symm ((localChart X d (e z)).symm v)))
      (localChart X d (e z) (e z)) := by
  let Y := openScheme X U
  let a := localChart X d (e z)
  let c := localChart Y d z
  let D := localEtaleCoordinates Y d z
  have hz : z ∈ c.source := mem_localChart_source Y d z
  have hza : e z ∈ a.source := mem_localChart_source X d (e z)
  have hzat : a (e z) ∈ a.target := a.map_source hza
  have hinv : e.symm (a.symm (a (e z))) = z := by
    rw [a.left_inv hza, e.left_inv hez]
  have hc : ContinuousAt (fun v ↦ e.symm (a.symm v)) (a (e z)) := by
    apply (e.continuousAt_symm (e.map_source hez)).comp_of_eq (a.continuousAt_symm hzat)
    exact a.left_inv hza
  have hcs : ∀ᶠ v in 𝓝 (a (e z)), e.symm (a.symm v) ∈ c.source := by
    apply hc.eventually
    dsimp only
    rw [hinv]
    exact c.open_source.mem_nhds hz
  have hes : ∀ᶠ v in 𝓝 (a (e z)), a.symm v ∈ e.target := by
    apply (a.continuousAt_symm hzat).eventually
    rw [a.left_inv hza]
    exact e.open_target.mem_nhds (e.map_source hez)
  apply AnalyticAt.pi
  intro j
  let V := D.ambientCoordinateOpen
  let s := D.ambientCoordinateSection j
  have hzV : z.underlying ∈ V := by
    simpa only [V, D, LocalEtaleCoordinates.ambientCoordinateOpen,
      Scheme.Opens.ι_image_top, Point.overOpen, Set.mem_ofPred_eq] using
      mem_localEtaleCoordinates Y d z
  have hzW : a.symm (a (e z)) ∈ Point.overOpen (U.ι ''ᵁ V) := by
    rw [a.left_inv hza, he]
    exact ⟨z.underlying, hzV, rfl⟩
  have ha := analyticAt_localChart_symm_evaluate X d (e z) hzat
    (U.ι ''ᵁ V) ((U.ι.appIso V).inv s) hzW
  apply ha.congr
  filter_upwards [hcs, hes] with v hv hve
  change _ = c (e.symm (a.symm v)) j
  rw [localChart_apply_component_eq_evaluate Y d z _ hv j]
  have hmap : Point.map (openInclusion X U) (e.symm (a.symm v)) = a.symm v := by
    rw [← he, e.right_inv hve]
  nth_rw 1 [← hmap]
  exact evaluate_openEquiv X U s _

open scoped ContDiff

private theorem gaga24_contMDiff_open_inverse
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (U : X.left.Opens) [SmoothOfRelativeDimension d (openScheme X U).hom]
    (z : ComplexPoint (openScheme X U))
    (e : OpenPartialHomeomorph (ComplexPoint (openScheme X U)) (ComplexPoint X))
    (hez : z ∈ e.source) (he : ∀ y, e y = Point.map (openInclusion X U) y) :
    ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω e.symm (e z) := by
  rw [contMDiffAt_iff]
  refine ⟨e.continuousAt_symm (e.map_source hez), ?_⟩
  have ha := gaga24_analytic_open_chart_inverse X d U z e hez he
  simp only [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_coe, Set.range_id,
    PartialEquiv.coe_trans, PartialEquiv.coe_trans_symm,
    OpenPartialHomeomorph.coe_toPartialEquiv_symm, OpenPartialHomeomorph.coe_toPartialEquiv]
  change ContDiffWithinAt ℂ ω
    (fun v ↦ localChart (openScheme X U) d (e.symm (e z))
      (e.symm ((localChart X d (e z)).symm v))) _ _
  rw [e.left_inv hez]
  exact ha.contDiffAt.contDiffWithinAt

private theorem gaga24_smooth_point_lift
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) (p : ComplexPoint X) (hp : p ∈ cycleComponentSmoothSupport X x) :
    ∃ z : ComplexPoint (cycleComponentSmoothLocusOver X x),
      Point.map (openInclusion X (cycleComponentSmoothLocusAmbientOpen X x))
        (Point.map (cycleComponentSmoothLocusClosedLiftOver X x) z) = p := by
  obtain ⟨q, hq, hqp⟩ := hp
  let C := Over.mk (cycleComponentι X.left x ≫ X.hom)
  let U := (cycleComponentι X.left x ≫ X.hom).smoothLocus
  let z : ComplexPoint (openScheme C U) := (openEquiv C U).symm ⟨q, hq⟩
  have hz : Point.map (openInclusion C U) z = q :=
    congrArg Subtype.val ((openEquiv C U).apply_symm_apply ⟨q, hq⟩)
  refine ⟨z, ?_⟩
  have hf : cycleComponentSmoothLocusClosedLiftOver X x ≫
      openInclusion X (cycleComponentSmoothLocusAmbientOpen X x) =
      openInclusion C U ≫ Over.homMk (cycleComponentι X.left x) rfl := by
    apply Over.OverMorphism.ext
    exact cycleComponentSmoothLocusClosedLift_ι X x
  change (z ≫ cycleComponentSmoothLocusClosedLiftOver X x) ≫
    openInclusion X (cycleComponentSmoothLocusAmbientOpen X x) = p
  erw [Category.assoc, hf, ← Category.assoc]
  change Point.map (Over.homMk (cycleComponentι X.left x) rfl)
    (Point.map (openInclusion C U) z) = p
  rw [hz]
  exact hqp

theorem gaga24_component_dimension_aux (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C)
    (O : (gaga22_descendedOnX X hD hper).Component) :
    ∃ m : ℕ, SmoothOfRelativeDimension m
      (cycleComponentSmoothLocusOver X (gaga23_point X hD hper hChow O)).hom ∧ m + 1 = dim X.left := by
  classical
  let x := gaga23_point X hD hper hChow O
  obtain ⟨p, P, hp, hP, hPx, hdP, hzero⟩ :=
    gaga24_common_regular_aux X hD hper hChow O
  obtain ⟨z, hz⟩ := gaga24_smooth_point_lift X x (abelianExp X p) hp
  let Y := cycleComponentSmoothLocusOver X x
  let U := cycleComponentSmoothLocusAmbientOpen X x
  let A := openScheme X U
  let i : Y ⟶ A := cycleComponentSmoothLocusClosedLiftOver X x
  let j : A ⟶ X := openInclusion X U
  let q : ComplexPoint A := Point.map i z
  have hxfin : Order.coheight x ≠ ⊤ := ne_top_of_le_ne_top (by simp)
    (SmoothOfRelativeDimension.coheight_le_complex (f := X.hom) (d := dim X.left) x)
  let m := dim X.left - (Order.coheight x).toNat
  have hm : SmoothOfRelativeDimension m Y.hom :=
    cycleComponentSmoothLocus_smoothOfRelativeDimension X x (ENat.natCast_toNat hxfin).symm
  let : SmoothOfRelativeDimension m Y.hom := hm
  let d := dim X.left
  let : SmoothOfRelativeDimension d A.hom := inferInstance
  letI : Nonempty (ComplexPoint A) := ⟨q⟩
  let o := (isOpenEmbedding_map_open X U).toOpenPartialHomeomorph (Point.map j)
  have ho : ∀ y, o y = Point.map j y := fun _ ↦ rfl
  have hqo : q ∈ o.source := Set.mem_univ q
  have hqp : o q = abelianExp X p := hz
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  obtain ⟨a, hpa, ha, hai⟩ := spec_complexExponential_localBiholomorph X d p
  have hap : a p = o q := (ha hpa).symm.trans hqp.symm
  have haexp : ∀ y ∈ a.source, a y = abelianExp X y := fun y hy ↦ (ha hy).symm
  let c := localChart A d q
  let N := closedImmersionNormalCoordinateChange A Y i m d z
  let H := closedImmersionHolomorphicFlatteningChart A Y i m d z
  let b := localChart Y m z z
  have hqH : q ∈ H.source := closedImmersionHolomorphicFlatteningChart_mem_source A Y i m d z
  have hHb : H q = (b, 0) := closedImmersionHolomorphicFlatteningChart_center A Y i m d z
  let e := a.trans (o.symm.trans H)
  have hpe : p ∈ e.source := by
    refine ⟨hpa, ?_, ?_⟩
    · change a p ∈ o.target
      rw [hap]
      exact o.map_source hqo
    · change o.symm (a p) ∈ H.source
      rw [hap, o.left_inv hqo]
      exact hqH
  have hep : e p = (b, 0) := by
    change H (o.symm (a p)) = _
    rw [hap, o.left_inv hqo, hHb]
  have hqa : q ∈ c.source := mem_localChart_source A d q
  have hc : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω c q :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) hqa
  have hci : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω c.symm (c q) :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) (c.map_source hqa)
  have hN : AnalyticAt ℂ N (c q) := analyticAt_closedImmersionNormalCoordinateChange A Y i m d z
  have hNi : AnalyticAt ℂ N.symm (b, 0) :=
    analyticAt_closedImmersionNormalCoordinateChange_symm A Y i m d z
  have hNcenter : N (c q) = (b, 0) := closedImmersionNormalCoordinateChange_center A Y i m d z
  have hNinv : N.symm (b, 0) = c q := by
    rw [← hNcenter, N.left_inv (closedImmersionNormalCoordinateChange_mem_source A Y i m d z)]
  have hH : ContMDiffAt 𝓘(ℂ, Fin d → ℂ)
      𝓘(ℂ, (Fin m → ℂ) × (Fin (d - m) → ℂ)) ω H q :=
    hN.contDiffAt.contMDiffAt.comp q hc
  have hHi : ContMDiffAt 𝓘(ℂ, (Fin m → ℂ) × (Fin (d - m) → ℂ))
      𝓘(ℂ, Fin d → ℂ) ω H.symm (b, 0) := by
    have hc' : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω c.symm (N.symm (b, 0)) := by
      rwa [hNinv]
    exact hc'.comp (b, 0) hNi.contDiffAt.contMDiffAt
  have hoa := gaga24_contMDiff_open_inverse X d U q o hqo ho
  have ho' : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω o q :=
    (spec_contMDiff_pointMap A X d d j).contMDiffAt
  have haa : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω a p := by
    apply (spec_contMDiff_complexExponential X d).contMDiffAt.congr_of_eventuallyEq
    filter_upwards [a.open_source.mem_nhds hpa] with t ht
    exact (ha ht).symm
  have hea : AnalyticAt ℂ e p := by
    have hoap : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω o.symm (a p) := by
      rwa [hap]
    have hHp : ContMDiffAt 𝓘(ℂ, Fin d → ℂ)
        𝓘(ℂ, (Fin m → ℂ) × (Fin (d - m) → ℂ)) ω H (o.symm (a p)) := by
      rwa [hap, o.left_inv hqo]
    exact ((hHp.comp p (hoap.comp p haa)).contDiffAt).analyticAt
  have heia : AnalyticAt ℂ e.symm (b, 0) := by
    have hHinv : H.symm (b, 0) = q := by rw [← hHb, H.left_inv hqH]
    have hoH : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω o (H.symm (b, 0)) := by
      rwa [hHinv]
    have hai' : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω a.symm (o (H.symm (b, 0))) := by
      rw [hHinv, ← hap]
      exact (hai _ (a.map_source hpa)).contMDiffAt (a.open_target.mem_nhds (a.map_source hpa))
    exact ((hai'.comp (b, 0) (hoH.comp (b, 0) hHi)).contDiffAt).analyticAt
  have hze : ∀ᶠ y in 𝓝 p, P y = 0 ↔ (e y).2 = 0 := by
    filter_upwards [hzero, e.open_source.mem_nhds hpe] with y hy hye
    have hrange := closedImmersionHolomorphicFlatteningChart_mem_range_iff A Y i m d z
      (o.symm (a y)) hye.2.2
    change P y = 0 ↔ (H (o.symm (a y))).2 = 0
    rw [← hrange]
    rw [cycleComponentSmoothLocusClosedLift_complexPoints_range]
    change P y = 0 ↔ Point.map j (o.symm (a y)) ∈ cycleComponentSupport X x
    have hyo : a y ∈ o.target := hye.2.1
    have hya : y ∈ a.source := hye.1
    rw [← ho, o.right_inv hyo, haexp y hya]
    exact hy
  refine ⟨m, hm, ?_⟩
  have heq := gaga24_dimension_of_flattening hP hPx hdP e hpe b hep hea heia hze
  simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using heq

theorem gaga24_codim_aux (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C)
    (O : (gaga22_descendedOnX X hD hper).Component) :
    Order.coheight (gaga23_point X hD hper hChow O) = 1 := by
  let x := gaga23_point X hD hper hChow O
  have hle : Order.coheight x ≤ dim X.left :=
    SmoothOfRelativeDimension.coheight_le_complex
      (f := X.hom) (d := dim X.left) x
  have hfin : Order.coheight x ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by simp) hle
  let p := (Order.coheight x).toNat
  have hp : Order.coheight x = p := (ENat.natCast_toNat hfin).symm
  obtain ⟨m, hm, hm1⟩ := gaga24_component_dimension_aux X hD hper hChow O
  have hsub : SmoothOfRelativeDimension (dim X.left - p)
      (cycleComponentSmoothLocusOver X x).hom :=
    cycleComponentSmoothLocus_smoothOfRelativeDimension X x hp
  obtain ⟨y, hy⟩ := (dense_cycleComponent_smoothLocus X x).nonempty
  letI : Nonempty (cycleComponentSmoothLocusOver X x).left := ⟨⟨y, hy⟩⟩
  letI : IsIntegral (cycleComponentSmoothLocusOver X x).left :=
    isIntegral_of_isOpenImmersion
      (cycleComponentι X.left x ≫ X.hom).smoothLocus.ι
  have heq : m = dim X.left - p := by
    letI := hm
    letI : Smooth (cycleComponentSmoothLocusOver X x).hom :=
      SmoothOfRelativeDimension.smooth m (cycleComponentSmoothLocusOver X x).hom
    have hm' := SmoothOfRelativeDimension.dim_eq
      (cycleComponentSmoothLocusOver X x).hom m
    letI := hsub
    have hsub' := SmoothOfRelativeDimension.dim_eq
      (cycleComponentSmoothLocusOver X x).hom (dim X.left - p)
    exact hm'.symm.trans hsub'
  have hp_le : p ≤ dim X.left := by
    rw [hp] at hle
    exact_mod_cast hle
  have : p = 1 := by omega
  calc
    Order.coheight (gaga23_point X hD hper hChow O) = (p : ℕ∞) := hp
    _ = 1 := by simp [this]

theorem gaga24_algebraization_aux (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C) :
    Nonempty (gaga24_Algebraization X V f) := by
  classical
  let N := gaga23_schemeEnumeration X hD hper hChow
  let x := fun i : Fin N.1 ↦ gaga23_point X hD hper hChow (N.2 i)
  let mult := fun i : Fin N.1 ↦
    (gaga22_descendedOnX X hD hper).multiplicity (N.2 i)
  obtain ⟨_, hinj, hpos, hsupp⟩ := gaga23_indexing_aux X hD hper hChow
  refine ⟨⟨N.1, x, hinj, ?_, mult, hpos, hsupp, ?_⟩⟩
  · intro i
    exact gaga24_codim_aux X hD hper hChow (N.2 i)
  · intro j p hp
    let A := gaga23_factorization (f j) p
      (hD.2.2.1 j p hp) (hD.2.2.2.1 j p hp)
    refine ⟨fun i ↦ gaga23_group A.factors
      (gaga23_label (abelianPeriodLattice X).toAddSubgroup
        hD hper j p hp A) (N.2 i), ?_⟩
    exact gaga23_local_equations_aux X hD hper hChow j p hp

private lemma eventually_zero_fin_one_of_analyticAt_of_accPt
    {f : (Fin 1 → ℂ) → ℂ} {x : Fin 1 → ℂ} (hf : AnalyticAt ℂ f x)
    (hacc : AccPt x (Filter.principal {z | f z = 0})) : ∀ᶠ z in nhds x, f z = 0 := by
  let L : (Fin 1 → ℂ) ≃L[ℂ] ℂ := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
  let g : ℂ → ℂ := fun z ↦ f (L.symm z)
  have hg : AnalyticAt ℂ g (L x) :=
    hf.comp_of_eq (L.symm.analyticAt (L x)) (by simp [g])
  have hset : L '' {z | f z = 0} = {z | g z = 0} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [g]
    · intro hz
      refine ⟨L.symm z, ?_, by simp⟩
      simpa [g] using hz
  have haccg : AccPt (L x) (Filter.principal {z | g z = 0}) := by
    have hm := hacc.map L.continuous.continuousAt L.injective
    rwa [Filter.map_principal, hset] at hm
  have hfreq : ∃ᶠ z in nhdsWithin (L x) ({L x}ᶜ), g z = 0 := by
    exact accPt_iff_frequently_nhdsNE.mp haccg
  have hevg : ∀ᶠ z in nhds (L x), g z = 0 :=
    hg.frequently_zero_iff_eventually_zero.mp hfreq
  have hpull := L.continuous.continuousAt.eventually hevg
  simpa only [g, ContinuousLinearEquiv.symm_apply_apply] using hpull

private lemma eventually_zero_fin_of_dim_one_of_analyticAt_of_accPt
    {d : ℕ} (hd : d = 1) {f : (Fin d → ℂ) → ℂ} {x : Fin d → ℂ}
    (hf : AnalyticAt ℂ f x) (hacc : AccPt x (Filter.principal {z | f z = 0})) :
    ∀ᶠ z in nhds x, f z = 0 := by
  subst d
  exact eventually_zero_fin_one_of_analyticAt_of_accPt hf hacc

/-- Set-level Chow for the fixed smooth projective cubic.
Source: Serre, Géométrie algébrique et géométrie analytique, Théorème 3;
Forster, Lectures on Riemann Surfaces, §1 (identity theorem). -/
theorem gaga24_curve_chow_aux (Z : Set (ComplexPoint Curves.E))
    (hZ : IsClosedAnalytic (Fin (dim Curves.E.left) → ℂ) Z) :
    ∃ C : Set Curves.E.left, IsClosed C ∧
      Z = (Point.underlying : ComplexPoint Curves.E → Curves.E.left) ⁻¹' C := by
  haveI : ConnectedSpace (ComplexPoint Curves.E) := connectedSpace_complexPoint Curves.E
  have hfinite_or_univ : Z.Finite ∨ Z = univ := by
    by_cases hfin : Z.Finite
    · exact Or.inl hfin
    · right
      have hinf : Z.Infinite := hfin
      obtain ⟨x, -, hxacc⟩ :=
        hinf.exists_accPt_of_subset_isCompact (K := univ) isCompact_univ Z.subset_univ
      have hxZ : x ∈ Z := hZ.isClosed.closure_subset hxacc.clusterPt.mem_closure
      obtain ⟨U, hUo, hxU, hUt, n, f, hf, hlocal⟩ := hZ.2 x hxZ
      let e := chartAt (Fin (dim Curves.E.left) → ℂ) x
      have hfacc (i : Fin n) : AccPt (e x) (Filter.principal {z | f i z = 0}) := by
        rw [accPt_iff_nhds]
        intro W hW
        have hpre : e.source ∩ e ⁻¹' (W ∩ U) ∈ nhds x :=
          inter_mem (e.open_source.mem_nhds (mem_chart_source _ x))
            (e.continuousAt (mem_chart_source _ x) (inter_mem hW (hUo.mem_nhds hxU)))
        obtain ⟨y, hy, hyne⟩ := (accPt_iff_nhds.mp hxacc) _ hpre
        refine ⟨e y, ⟨hy.1.2.1, ?_⟩, ?_⟩
        · exact (hlocal (e y) hy.1.2.2).mp
            (by simpa [e, e.left_inv hy.1.1] using hy.2) i
        · exact fun heq ↦ hyne (e.injOn hy.1.1 (mem_chart_source _ x) heq)
      have hall : ∀ᶠ z in nhds (e x), ∀ i, f i z = 0 := by
        rw [Filter.eventually_all]
        exact fun i ↦ eventually_zero_fin_of_dim_one_of_analyticAt_of_accPt Curves.E_dim
          (hf i (e x) hxU) (hfacc i)
      have hnear : Z ∈ nhds x := by
        have hzero : {z | ∀ i, f i z = 0} ∈ nhds (e x) := hall
        have hchart : e ⁻¹' (U ∩ {z | ∀ i, f i z = 0}) ∈ nhds x :=
          e.continuousAt (mem_chart_source _ x) (inter_mem (hUo.mem_nhds hxU) hzero)
        refine mem_of_superset (inter_mem (e.open_source.mem_nhds (mem_chart_source _ x)) hchart) ?_
        intro y hy
        have heyU : e y ∈ U := hy.2.1
        simpa [e, e.left_inv hy.1] using (hlocal (e y) heyU).mpr (by simpa using hy.2.2)
      exact hZ.eq_univ_of_nonempty_interior ⟨x, mem_interior_iff_mem_nhds.mpr hnear⟩
  rcases hfinite_or_univ with hfin | rfl
  · let C : Set Curves.E.left := Point.underlying '' Z
    refine ⟨C, ?_, ?_⟩
    · rw [show C = ⋃ z : Z, ({z.1.underlying} : Set Curves.E.left) by
          ext y; simp [C]]
      letI : Finite Z := hfin
      apply isClosed_iUnion_of_finite
      intro z
      exact ((pointEquivClosedPoint Curves.E.hom) ⟨z.1.left, Over.w z.1⟩).2
    · apply Set.Subset.antisymm
      · intro z hz
        exact ⟨z, hz, rfl⟩
      · rintro z ⟨w, hw, hzw⟩
        have : z = w := by
          apply Over.OverMorphism.ext
          exact ext_of_apply_closedPoint_eq Curves.E.hom (Over.w z) (Over.w w) hzw.symm
        simpa [this] using hw
  · exact ⟨univ, isClosed_univ, by simp⟩

end HodgeLean.Foundations.AnalyticDivisorAlgebraic24
