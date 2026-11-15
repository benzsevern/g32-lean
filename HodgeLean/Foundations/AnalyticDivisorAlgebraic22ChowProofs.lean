import HodgeLean.Foundations.AnalyticDivisorAlgebraic22ChowDefs

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic22
open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic21
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Foundations HodgeLean.Adapters HodgeLean.RealDefs
open scoped Manifold CategoryTheory.MonObj

private theorem gaga22_isClosedAnalytic_iUnion_of_locallyFinite
    {E M A : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] {Z : A → Set M}
    (hlf : LocallyFinite Z) (hZ : ∀ a, IsClosedAnalytic E (Z a)) :
    IsClosedAnalytic E (⋃ a, Z a) := by
  classical
  refine ⟨hlf.isClosed_iUnion (fun a ↦ (hZ a).isClosed), fun x hx ↦ ?_⟩
  obtain ⟨t, htx, htfin⟩ := hlf x
  obtain ⟨N, hNt, hNo, hxN⟩ := mem_nhds_iff.mp htx
  let s : Finset A := htfin.toFinset
  have hxs : x ∈ ⋃ a ∈ s, Z a := by
    obtain ⟨a, hxa⟩ := mem_iUnion.mp hx
    exact mem_iUnion₂.mpr ⟨a, htfin.mem_toFinset.mpr ⟨x, hxa, hNt hxN⟩, hxa⟩
  have hs := IsClosedAnalytic.biUnion_finset s (fun a _ ↦ hZ a)
  obtain ⟨U, hUo, hxU, hUt, n, F, hF, hUF⟩ := hs.2 x hxs
  let e := chartAt E x
  refine ⟨U ∩ (e.target ∩ e.symm ⁻¹' N),
    hUo.inter (e.isOpen_inter_preimage_symm hNo),
    ⟨hxU, mem_chart_target E x, by
      change e.symm (e x) ∈ N
      rw [e.left_inv (mem_chart_source E x)]
      exact hxN⟩,
    inter_subset_left.trans hUt, n, F, fun i ↦ (hF i).mono inter_subset_left,
    fun z hz ↦ ?_⟩
  rw [← hUF z hz.1]
  constructor
  · intro hall
    obtain ⟨a, hza⟩ := mem_iUnion.mp hall
    have hat : a ∈ s := htfin.mem_toFinset.mpr ⟨e.symm z, hza, hNt hz.2.2⟩
    exact mem_iUnion₂.mpr ⟨a, hat, hza⟩
  · rintro h
    obtain ⟨a, -, hza⟩ := mem_iUnion₂.mp h
    exact mem_iUnion.mpr ⟨a, hza⟩

private theorem gaga22_componentCarrier_isClosedAnalytic {g : ℕ} {J : Type}
    {V : J → Set (Fin g → ℂ)} {f : J → (Fin g → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f) (C : gaga21_GlobalComponent V f) :
    IsClosedAnalytic (Fin g → ℂ) (gaga21_componentCarrier C) := by
  classical
  rw [isClosedAnalytic_iff_finite]
  refine ⟨?_, fun q hq ↦ ?_⟩
  · have hc := (gaga21_carrier_geometry hD C).2.2.1
    have hi := isClosed_univ.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.mp hc
    simpa using hi
  obtain ⟨i, hi⟩ : ∃ i, q ∈ V i := by
    exact mem_iUnion.mp (hD.2.1.symm ▸ mem_univ q)
  obtain ⟨k, a, hk, ha, hlocal, -⟩ := (gaga21_carrier_geometry hD C).2.2.2.2.2.2 q hq i hi
  have hev : ∀ᶠ y in 𝓝 q,
      (∀ j, AnalyticAt ℂ (a j).factor y) ∧
        (y ∈ gaga21_componentCarrier C ↔ ∃ j, (a j).factor y = 0) := by
    filter_upwards [eventually_all.mpr (fun j ↦ (ha j).1.symm ▸
      (a j).factor_data (a j).selected |>.1.eventually_analyticAt),
      hlocal] with y hy hylocal
    exact ⟨hy, hylocal⟩
  obtain ⟨U, hUsub, hUo, hqU⟩ := mem_nhds_iff.mp hev
  refine ⟨U, hUo, ?_, ?_, Unit, inferInstance,
    fun _ y ↦ ∏ j, (a j).factor y, ?_, fun z hz ↦ ?_⟩
  · simpa only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq] using hqU
  · simpa only [chartAt_self_eq, OpenPartialHomeomorph.refl_target, subset_univ]
  · intro _ z hz
    exact Finset.analyticAt_fun_prod _ (fun j _ ↦ (hUsub hz).1 j)
  · change z ∈ gaga21_componentCarrier C ↔ ∀ _ : Unit, ∏ j, (a j).factor z = 0
    rw [(hUsub hz).2, Finset.prod_eq_zero_iff]
    simp only [Finset.mem_univ, true_and, forall_const]

private def gaga22_orbitCarrier {g : ℕ} {J : Type}
    {V : J → Set (Fin g → ℂ)} {f : J → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (O : gaga22_ComponentOrbit Λ hD hper) : Set (Fin g → ℂ) :=
  ⋃ C : {C : gaga21_GlobalComponent V f |
    Quotient.mk (gaga22_orbitSetoid Λ hD hper) C = O}, gaga21_componentCarrier C.1

private theorem gaga22_orbitCarrier_isClosedAnalytic {g : ℕ} {J : Type}
    {V : J → Set (Fin g → ℂ)} {f : J → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (O : gaga22_ComponentOrbit Λ hD hper) :
    IsClosedAnalytic (Fin g → ℂ) (gaga22_orbitCarrier Λ hD hper O) := by
  let Z := fun C : gaga21_GlobalComponent V f ↦ gaga21_componentCarrier C
  have hlf : LocallyFinite Z := fun q ↦ gaga21_finite_incidence hD q (mem_univ q)
  apply gaga22_isClosedAnalytic_iUnion_of_locallyFinite
    (hlf.comp_injective Subtype.val_injective)
  exact fun C ↦ gaga22_componentCarrier_isClosedAnalytic hD C.1

private theorem gaga22_orbitCarrier_add_mem {g : ℕ} {J : Type}
    {V : J → Set (Fin g → ℂ)} {f : J → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (O : gaga22_ComponentOrbit Λ hD hper) (v : Fin g → ℂ)
    (hv : v ∈ gaga22_orbitCarrier Λ hD hper O) (l : Λ) :
    v + l ∈ gaga22_orbitCarrier Λ hD hper O := by
  letI := gaga22_componentAction Λ hD hper
  obtain ⟨C, hvC⟩ := mem_iUnion.mp hv
  refine mem_iUnion.mpr ⟨⟨l +ᵥ C.1, ?_⟩, ?_⟩
  · calc
      Quotient.mk (gaga22_orbitSetoid Λ hD hper) (l +ᵥ C.1) =
          Quotient.mk (gaga22_orbitSetoid Λ hD hper) C.1 := by
            apply Quotient.sound
            change l +ᵥ C.1 ∈ AddAction.orbit Λ C.1
            exact AddAction.mem_orbit C.1 l
      _ = O := C.2
  · change v + l ∈ gaga21_componentCarrier (gaga22_translateComponent Λ hD hper l C.1)
    rw [gaga22_carrier_translate Λ hD hper l C.1]
    exact ⟨v, hvC, rfl⟩

private theorem gaga22_abelianExp_orbitCarrier (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (O : gaga22_ComponentOrbit (abelianPeriodLattice X).toAddSubgroup hD hper) :
    abelianExp X '' gaga22_orbitCarrier (abelianPeriodLattice X).toAddSubgroup hD hper O =
      (gaga22_descendedOnX X hD hper).carrier O := by
  let Λ := (abelianPeriodLattice X).toAddSubgroup
  letI := gaga22_componentAction Λ hD hper
  apply subset_antisymm
  · rintro x ⟨v, hv, rfl⟩
    obtain ⟨C, hvC⟩ := mem_iUnion.mp hv
    have hrel : (gaga22_orbitSetoid Λ hD hper).r C.1 (Quotient.out O) :=
      Quotient.exact (C.2.trans (Quotient.out_eq O).symm)
    change C.1 ∈ AddAction.orbit Λ (Quotient.out O) at hrel
    obtain ⟨l, hl⟩ := AddAction.mem_orbit_iff.mp hrel
    rw [← hl] at hvC
    change v ∈ gaga21_componentCarrier
      (gaga22_translateComponent Λ hD hper l (Quotient.out O)) at hvC
    rw [gaga22_carrier_translate Λ hD hper l (Quotient.out O)] at hvC
    obtain ⟨w, hw, rfl⟩ := hvC
    exact ⟨w, hw, (abelianExp_add_lattice X w l).symm⟩
  · rintro x ⟨v, hv, rfl⟩
    refine ⟨v, mem_iUnion.mpr ⟨⟨Quotient.out O, Quotient.out_eq O⟩, hv⟩, rfl⟩

private theorem gaga22_descendedOnX_carrier_isClosedAnalytic
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (O : (gaga22_descendedOnX X hD hper).Component) :
    IsClosedAnalytic (Fin (dim X.left) → ℂ)
      ((gaga22_descendedOnX X hD hper).carrier O) := by
  rw [← gaga22_abelianExp_orbitCarrier X hD hper O]
  exact spec_isClosedAnalytic_abelianExp_image X _
    (gaga22_orbitCarrier_isClosedAnalytic _ hD hper O)
    (gaga22_orbitCarrier_add_mem _ hD hper O)

private theorem gaga22_closed_eq_of_complexPoint_preimage_eq
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] {C D : Set X.left}
    (hC : IsClosed C) (hD : IsClosed D)
    (h : (Point.underlying : ComplexPoint X → X.left) ⁻¹' C =
      (Point.underlying : ComplexPoint X → X.left) ⁻¹' D) : C = D := by
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
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

private theorem gaga22_descendedOnX_support
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p) :
    (∀ O, 0 < (gaga22_descendedOnX X hD hper).multiplicity O) ∧
    (⋃ O, (gaga22_descendedOnX X hD hper).carrier O) =
      abelianExp X '' localDivisorSupport V f ∧
    Function.Injective (gaga22_descendedOnX X hD hper).carrier := by
  let Λ := (abelianPeriodLattice X).toAddSubgroup
  obtain ⟨hpos, hsupp, hinj⟩ := gaga22_descended_support Λ hD hper
  refine ⟨hpos, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨O, v, hv, rfl⟩ := mem_iUnion.mp hx
      have hp : (QuotientAddGroup.mk : (Fin (dim X.left) → ℂ) → _ ⧸ Λ) v ∈ ⋃ O,
          (gaga22_descendedDivisor Λ hD hper).carrier O :=
        mem_iUnion.mpr ⟨O, ⟨v, hv, rfl⟩⟩
      rw [hsupp] at hp
      obtain ⟨w, hw, heq⟩ := hp
      exact ⟨w, hw, (abelianExp_eq_iff_proj_eq X w v).2 heq⟩
    · rintro ⟨v, hv, rfl⟩
      have hp : (QuotientAddGroup.mk : (Fin (dim X.left) → ℂ) → _ ⧸ Λ) v ∈
          (QuotientAddGroup.mk : (Fin (dim X.left) → ℂ) → _ ⧸ Λ) '' localDivisorSupport V f :=
        ⟨v, hv, rfl⟩
      rw [← hsupp] at hp
      obtain ⟨O, w, hw, heq⟩ := mem_iUnion.mp hp
      exact mem_iUnion.mpr ⟨O, ⟨w, hw, (abelianExp_eq_iff_proj_eq X w v).2 heq⟩⟩
  · intro O P hOP
    apply hinj
    ext q
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective q
    constructor
    · rintro ⟨w, hw, heq⟩
      have : abelianExp X w = abelianExp X v := (abelianExp_eq_iff_proj_eq X w v).2 heq
      have hvP : abelianExp X v ∈ (gaga22_descendedOnX X hD hper).carrier P := hOP ▸ ⟨w, hw, this⟩
      obtain ⟨u, hu, hueq⟩ := hvP
      exact ⟨u, hu, (abelianExp_eq_iff_proj_eq X u v).1 hueq⟩
    · rintro ⟨w, hw, heq⟩
      have : abelianExp X w = abelianExp X v := (abelianExp_eq_iff_proj_eq X w v).2 heq
      have hvO : abelianExp X v ∈ (gaga22_descendedOnX X hD hper).carrier O := hOP.symm ▸ ⟨w, hw, this⟩
      obtain ⟨u, hu, hueq⟩ := hvO
      exact ⟨u, hu, (abelianExp_eq_iff_proj_eq X u v).1 hueq⟩

private theorem gaga22_chow_closed_irreducible
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    {Z : Set (ComplexPoint X)} {C : Set X.left}
    (hC : IsClosed C)
    (hZ : Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C)
    (hne : Z.Nonempty)
    (hcover : ∀ A B : Set (ComplexPoint X),
      IsClosedAnalytic (Fin (dim X.left) → ℂ) A →
      IsClosedAnalytic (Fin (dim X.left) → ℂ) B →
      Z ⊆ A ∪ B → Z ⊆ A ∨ Z ⊆ B) :
    IsIrreducible C := by
  refine ⟨?_, (isPreirreducible_iff_isClosed_union_isClosed.mpr fun A B hA hB hsub ↦ ?_)⟩
  · obtain ⟨z, hz⟩ := hne
    exact ⟨z.underlying, hZ.subset hz⟩
  have hZA : IsClosedAnalytic (Fin (dim X.left) → ℂ)
      ((Point.underlying : ComplexPoint X → X.left) ⁻¹' A) :=
    AnalyticDivisorAlgebraic.spec_isClosedAnalytic_preimage_underlying X hA
  have hZB : IsClosedAnalytic (Fin (dim X.left) → ℂ)
      ((Point.underlying : ComplexPoint X → X.left) ⁻¹' B) :=
    AnalyticDivisorAlgebraic.spec_isClosedAnalytic_preimage_underlying X hB
  have hpull : Z ⊆
      (Point.underlying : ComplexPoint X → X.left) ⁻¹' A ∪
        (Point.underlying : ComplexPoint X → X.left) ⁻¹' B := by
    rw [hZ]
    exact preimage_mono hsub
  rcases hcover _ _ hZA hZB hpull with hleft | hright
  · left
    have he : C ∩ A = C := by
      apply gaga22_closed_eq_of_complexPoint_preimage_eq X (hC.inter hA) hC
      rw [preimage_inter, ← hZ]
      exact Set.inter_eq_left.mpr hleft
    exact fun x hx ↦ (he.symm ▸ hx).2
  · right
    have he : C ∩ B = C := by
      apply gaga22_closed_eq_of_complexPoint_preimage_eq X (hC.inter hB) hC
      rw [preimage_inter, ← hZ]
      exact Set.inter_eq_left.mpr hright
    exact fun x hx ↦ (he.symm ▸ hx).2

private theorem gaga22_abelianExp_preimage_isClosedAnalytic
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

private theorem gaga22_regular_carrier_equation {g : ℕ} {J : Type}
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

private theorem gaga22_regular_identity {g : ℕ} {R A : Set (Fin g → ℂ)}
    (hc : IsConnected R)
    (hloc : ∀ x ∈ R, ∃ (U : Set (Fin g → ℂ)) (P : (Fin g → ℂ) → ℂ),
      IsOpen U ∧ x ∈ U ∧ AnalyticOnNhd ℂ P U ∧
      ∀ y ∈ U, (y ∈ R ↔ y ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero P))
    (hA : IsClosedAnalytic (Fin g → ℂ) A)
    (hne : (interior (((↑) : R → (Fin g → ℂ)) ⁻¹' A)).Nonempty) : R ⊆ A := by
  let Z : Set R := ((↑) : R → (Fin g → ℂ)) ⁻¹' A
  haveI : ConnectedSpace R := isConnected_iff_connectedSpace.mp hc
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

private theorem gaga22_carrier_analytic_cover {g : ℕ} {J : Type}
    {V : J → Set (Fin g → ℂ)} {f : J → (Fin g → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f) (C : gaga21_GlobalComponent V f)
    {A B : Set (Fin g → ℂ)}
    (hA : IsClosedAnalytic (Fin g → ℂ) A) (hB : IsClosedAnalytic (Fin g → ℂ) B)
    (hcover : gaga21_componentCarrier C ⊆ A ∪ B) :
    gaga21_componentCarrier C ⊆ A ∨ gaga21_componentCarrier C ⊆ B := by
  let R := gaga21_regularSupport V f ∩ gaga21_componentCarrier C
  have hd : gaga21_componentCarrier C ⊆ closure R :=
    gaga21_b2_carrier_approximation hD C
  by_cases hRA : R ⊆ A
  · exact Or.inl (hd.trans (closure_minimal hRA hA.isClosed))
  · right
    obtain ⟨x, hxR, hxA⟩ := Set.not_subset.mp hRA
    have hopen : IsOpen (((↑) : R → (Fin g → ℂ)) ⁻¹' A)ᶜ :=
      (hA.isClosed.preimage continuous_subtype_val).isOpen_compl
    have hsub : (((↑) : R → (Fin g → ℂ)) ⁻¹' A)ᶜ ⊆
        ((↑) : R → (Fin g → ℂ)) ⁻¹' B := by
      intro y hy
      exact (hcover y.property.2).resolve_left hy
    have hRB : R ⊆ B := gaga22_regular_identity
      (gaga21_carrier_regular_connected_aux hD C).1
      (fun y hy ↦ gaga22_regular_carrier_equation hD C hy) hB
      ⟨⟨x, hxR⟩, interior_mono hsub (mem_interior_iff_mem_nhds.mpr (hopen.mem_nhds hxA))⟩
    exact hd.trans (closure_minimal hRB hB.isClosed)

private theorem gaga22_descendedOnX_analytic_cover
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (O : (gaga22_descendedOnX X hD hper).Component)
    {A B : Set (ComplexPoint X)}
    (hA : IsClosedAnalytic (Fin (dim X.left) → ℂ) A)
    (hB : IsClosedAnalytic (Fin (dim X.left) → ℂ) B)
    (hcover : (gaga22_descendedOnX X hD hper).carrier O ⊆ A ∪ B) :
    (gaga22_descendedOnX X hD hper).carrier O ⊆ A ∨
      (gaga22_descendedOnX X hD hper).carrier O ⊆ B := by
  have hpull : gaga21_componentCarrier (Quotient.out O) ⊆
      abelianExp X ⁻¹' A ∪ abelianExp X ⁻¹' B :=
    fun x hx ↦ hcover ⟨x, hx, rfl⟩
  rcases gaga22_carrier_analytic_cover hD (Quotient.out O)
      (gaga22_abelianExp_preimage_isClosedAnalytic X hA).1
      (gaga22_abelianExp_preimage_isClosedAnalytic X hB).1 hpull with h | h
  · exact Or.inl (by rintro x ⟨v, hv, rfl⟩; exact h hv)
  · exact Or.inr (by rintro x ⟨v, hv, rfl⟩; exact h hv)

theorem gaga22_chow_support_aux (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C) :
    Finite (gaga22_descendedOnX X hD hper).Component ∧
    ∃ C : (gaga22_descendedOnX X hD hper).Component → Set X.left,
      Function.Injective C ∧
      (∀ O, IsClosed (C O) ∧ IsIrreducible (C O) ∧
        (gaga22_descendedOnX X hD hper).carrier O =
          (Point.underlying : ComplexPoint X → X.left) ⁻¹' C O ∧
        0 < (gaga22_descendedOnX X hD hper).multiplicity O) ∧
      abelianExp X '' localDivisorSupport V f =
        ⋃ O, (Point.underlying : ComplexPoint X → X.left) ⁻¹' C O := by
  classical
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  letI : CompactSpace ((Fin (dim X.left) → ℂ) ⧸
      (abelianPeriodLattice X).toAddSubgroup) :=
    compact_complexExponentialQuotient X (dim X.left)
  refine ⟨gaga22_finite_orbits (abelianPeriodLattice X).toAddSubgroup hD hper, ?_⟩
  choose C hC hCeq using fun O ↦ hChow _
    (gaga22_descendedOnX_carrier_isClosedAnalytic X hD hper O)
  obtain ⟨hpos, hsupp, hinj⟩ := gaga22_descendedOnX_support X hD hper
  refine ⟨C, ?_, ?_, ?_⟩
  · intro O P hOP
    apply hinj
    rw [hCeq O, hCeq P, hOP]
  · intro O
    refine ⟨hC O, ?_, hCeq O, hpos O⟩
    apply gaga22_chow_closed_irreducible X (hC O) (hCeq O)
    · exact ((gaga21_carrier_geometry hD (Quotient.out O)).1).image (abelianExp X)
    · intro A B hA hB hcover
      exact gaga22_descendedOnX_analytic_cover X hD hper O hA hB hcover
  · rw [← hsupp]
    exact iUnion_congr hCeq

end HodgeLean.Foundations.AnalyticDivisorAlgebraic22
