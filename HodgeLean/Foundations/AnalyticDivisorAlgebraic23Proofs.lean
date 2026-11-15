import HodgeLean.Foundations.AnalyticDivisorAlgebraic23Defs

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic23
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

theorem gaga23_indexing_aux (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C) :
    let N := gaga23_schemeEnumeration X hD hper hChow
    let x := fun i : Fin N.1 ↦ gaga23_point X hD hper hChow (N.2 i)
    let mult := fun i : Fin N.1 ↦ (gaga22_descendedOnX X hD hper).multiplicity (N.2 i)
    (∀ i, closure ({x i} : Set X.left) = gaga23_carrier X hD hper hChow (N.2 i)) ∧
    Function.Injective x ∧
    (∀ i, 0 < mult i) ∧
    abelianExp X '' localDivisorSupport V f = ⋃ i, gaga23_componentSupport X (x i) := by
  classical
  dsimp only
  let h := gaga22_chow_support X hD hper hChow
  let N := gaga23_schemeEnumeration X hD hper hChow
  have hclosure (i : Fin N.1) :
      closure ({gaga23_point X hD hper hChow (N.2 i)} : Set X.left) =
        gaga23_carrier X hD hper hChow (N.2 i) := by
    exact (h.2.choose_spec.2.1 (N.2 i)).2.1.closure_genericPoint
      (h.2.choose_spec.2.1 (N.2 i)).1
  refine ⟨hclosure, ?_, ?_, ?_⟩
  · intro i k hik
    apply N.2.injective
    apply h.2.choose_spec.1
    exact (hclosure i).symm.trans ((congrArg closure (congrArg singleton hik)).trans
      (hclosure k))
  · intro i
    exact (h.2.choose_spec.2.1 (N.2 i)).2.2.2
  · rw [h.2.choose_spec.2.2]
    ext z
    simp only [mem_iUnion]
    constructor
    · rintro ⟨O, hz⟩
      refine ⟨N.2.symm O, ?_⟩
      simp only [N, Equiv.apply_symm_apply]
      change z ∈ (Point.underlying : ComplexPoint X → X.left) ⁻¹'
        closure ({gaga23_point X hD hper hChow O} : Set X.left)
      have hcO := hclosure (N.2.symm O)
      rw [N.2.apply_symm_apply] at hcO
      rw [hcO]
      exact hz
    · rintro ⟨i, hz⟩
      refine ⟨N.2 i, ?_⟩
      change z ∈ (Point.underlying : ComplexPoint X → X.left) ⁻¹'
        closure ({gaga23_point X hD hper hChow (N.2 i)} : Set X.left) at hz
      rw [hclosure i] at hz
      exact hz

theorem gaga23_group_weights_aux {d : ℕ} {J : Type}
    {V : J → Set (Fin d → ℂ)} {f : J → (Fin d → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin d → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (j : J) (p : Fin d → ℂ) (hp : p ∈ V j)
    (A : gaga23_Factorization (f j) p) :
    ∀ a : Fin A.count,
      A.exponents a = (gaga22_descendedDivisor Λ hD hper).multiplicity
        (gaga23_label Λ hD hper j p hp A a) := by
  intro a
  calc
    A.exponents a = (gaga21_gluedDivisor V f).multiplicity
        (Quotient.mk _ (gaga23_occurrence j p hp A a)) :=
      (gaga21_glued_multiplicity hD (gaga23_occurrence j p hp A a)).symm
    _ = (gaga22_descendedDivisor Λ hD hper).multiplicity
        (gaga23_label Λ hD hper j p hp A a) :=
      (gaga22_descended_representative Λ hD hper
        (Quotient.mk _ (gaga23_occurrence j p hp A a))).2.symm

private theorem gaga23_irreducible_germ {d : ℕ} {p : Fin d → ℂ}
    {f : (Fin d → ℂ) → ℂ} (hf : AnalyticAt ℂ f p) (hi : IsIrreducibleAt f p) :
    Irreducible (⟨Filter.Germ.ofFun f, f, hf, rfl⟩ : AnalyticGermAt d p) := by
  constructor
  · intro hu
    exact (hu.map (analyticGermAtValue d p)).ne_zero hi.1
  · intro a b hab
    obtain ⟨g, hg, hga⟩ := a.2
    obtain ⟨h, hh, hhb⟩ := b.2
    have he : f =ᶠ[𝓝 p] fun z ↦ g z * h z := by
      apply Filter.Germ.coe_eq.mp
      calc
        Filter.Germ.ofFun f = (a * b).1 := congrArg Subtype.val hab
        _ = a.1 * b.1 := rfl
        _ = Filter.Germ.ofFun g * Filter.Germ.ofFun h := congrArg₂ (· * ·) hga.symm hhb.symm
        _ = Filter.Germ.ofFun (fun z ↦ g z * h z) := rfl
    rcases hi.2 g h hg hh he with hg0 | hh0
    · left
      apply isUnit_iff_exists_inv.mpr
      let v : AnalyticGermAt d p :=
        ⟨Filter.Germ.ofFun (fun z ↦ (g z)⁻¹), fun z ↦ (g z)⁻¹, hg.inv hg0, rfl⟩
      refine ⟨v, Subtype.ext ?_⟩
      change a.1 * v.1 = 1
      rw [← hga]
      exact Filter.Germ.coe_eq.mpr ((hg.continuousAt.eventually_ne hg0).mono
        fun z hz ↦ mul_inv_cancel₀ hz)
    · right
      apply isUnit_iff_exists_inv.mpr
      let v : AnalyticGermAt d p :=
        ⟨Filter.Germ.ofFun (fun z ↦ (h z)⁻¹), fun z ↦ (h z)⁻¹, hh.inv hh0, rfl⟩
      refine ⟨v, Subtype.ext ?_⟩
      change b.1 * v.1 = 1
      rw [← hhb]
      exact Filter.Germ.coe_eq.mpr ((hh.continuousAt.eventually_ne hh0).mono
        fun z hz ↦ mul_inv_cancel₀ hz)

theorem gaga23_group_squarefree_aux {d : ℕ} {I : Type} (f : (Fin d → ℂ) → ℂ)
    (p : Fin d → ℂ) (A : gaga23_Factorization f p) (label : Fin A.count → I) :
    ∃ hg : ∀ i, AnalyticAt ℂ (gaga23_group A.factors label i) p,
      ∀ i, Squarefree (⟨Filter.Germ.ofFun (gaga23_group A.factors label i),
        gaga23_group A.factors label i, hg i, rfl⟩ : AnalyticGermAt d p) := by
  classical
  let hg : ∀ i, AnalyticAt ℂ (gaga23_group A.factors label i) p := fun i ↦ by
    change AnalyticAt ℂ (fun z ↦ ∏ a ∈ Finset.univ.filter (fun a ↦ label a = i),
      A.factors a z) p
    exact Finset.analyticAt_fun_prod _ fun a ha ↦ (A.factor_data a).1
  refine ⟨hg, fun i ↦ ?_⟩
  obtain ⟨e, -⟩ := AnalyticDivisorAlgebraic11.spec_germ_translation_equiv d p
  letI : UniqueFactorizationMonoid (AnalyticGermAt d p) :=
    e.symm.toMulEquiv.uniqueFactorizationMonoid
      (AnalyticDivisorAlgebraic6.spec_analyticGerm_ufd d)
  let G : Fin A.count → AnalyticGermAt d p := fun a ↦
    ⟨Filter.Germ.ofFun (A.factors a), A.factors a, (A.factor_data a).1, rfl⟩
  have hirr : ∀ a, Irreducible (G a) := fun a ↦
    gaga23_irreducible_germ (A.factor_data a).1 (A.factor_data a).2.1
  have hcop : Pairwise (fun a b ↦ IsRelPrime (G a) (G b)) := by
    intro a b hab
    apply (hirr a).isRelPrime_iff_not_dvd.mpr
    rintro ⟨c, hc⟩
    obtain ⟨C, hC, hcC⟩ := c.2
    apply A.coprime hab
    refine ⟨A.factors a, fun _ ↦ 1, C, (A.factor_data a).1, analyticAt_const, hC,
      (A.factor_data a).2.1.1, Eventually.of_forall (fun z ↦ (mul_one _).symm), ?_⟩
    apply Filter.Germ.coe_eq.mp
    calc
      Filter.Germ.ofFun (A.factors b) = (G b).1 := rfl
      _ = (G a * c).1 := congrArg Subtype.val hc
      _ = (G a).1 * c.1 := rfl
      _ = Filter.Germ.ofFun (A.factors a) * Filter.Germ.ofFun C :=
        congrArg₂ (· * ·) rfl hcC.symm
      _ = Filter.Germ.ofFun (fun z ↦ A.factors a z * C z) := rfl
  have hs : Squarefree (∏ a ∈ Finset.univ.filter (fun a ↦ label a = i), G a) :=
    Finset.squarefree_prod_of_pairwise_isCoprime
      (fun a _ b _ hab ↦ hcop hab) (fun a _ ↦ (hirr a).squarefree)
  convert hs using 1
  apply Subtype.ext
  dsimp only [G]
  have hval : (∏ a ∈ Finset.univ.filter (fun a ↦ label a = i),
      (⟨Filter.Germ.ofFun (A.factors a), A.factors a, (A.factor_data a).1, rfl⟩ :
        AnalyticGermAt d p)).1 =
      ∏ a ∈ Finset.univ.filter (fun a ↦ label a = i),
        Filter.Germ.ofFun (A.factors a) := by
    change (analyticGermAtSubring d p).subtype
      (∏ a ∈ Finset.univ.filter (fun a ↦ label a = i),
        (⟨Filter.Germ.ofFun (A.factors a), A.factors a, (A.factor_data a).1, rfl⟩ :
          AnalyticGermAt d p)) = _
    rw [map_prod]
    rfl
  rw [hval, ← Germ.coe_prod]
  apply Filter.Germ.coe_eq.mpr
  have hgroup : gaga23_group A.factors label i =
      fun z ↦ ∏ a ∈ Finset.univ.filter (fun a ↦ label a = i), A.factors a z := rfl
  rw [hgroup]
  exact Eventually.of_forall fun z ↦ by simp only [Finset.prod_apply]

theorem gaga23_component_factor_germ {d : ℕ} {J : Type}
    {V : J → Set (Fin d → ℂ)} {f : J → (Fin d → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f) (j : J) (p : Fin d → ℂ) (hp : p ∈ V j)
    (A : gaga23_Factorization (f j) p) (C : gaga21_GlobalComponent V f)
    (hpC : p ∈ gaga21_componentCarrier C) :
    ∀ᶠ z in 𝓝 p, z ∈ gaga21_componentCarrier C ↔
      ∃ a : Fin A.count,
        Quotient.mk (gaga21_componentSetoid V f) (gaga23_occurrence j p hp A a) = C ∧
          A.factors a z = 0 := by
  classical
  obtain ⟨k, b, _, hb, hlocal, hmatch⟩ :=
    (gaga21_carrier_geometry hD C).2.2.2.2.2.2 p hpC j hp
  have hfactor : ∀ r : Fin k, ∃ a : Fin A.count,
      AreAssociatedAt (b r).factor (A.factors a) p := by
    intro r
    have hz := gaga21_d2_factor_zero_chart hD (b r) j ((hb r).1 ▸ hp)
    obtain ⟨s, hs, hdiv⟩ := gaga21_br_nullstellensatz p (b r).factor (f j)
      ((hb r).1 ▸ (b r).factor_data (b r).selected |>.1) (hD.2.2.1 j p hp)
      ((hb r).1 ▸ (b r).factor_data (b r).selected |>.2.1) (by simpa only [(hb r).1] using hz)
    obtain ⟨a, c, hc, hac⟩ := gaga21_d2_prime_factor
      ((hb r).1 ▸ (b r).factor_data (b r).selected |>.1)
      ((hb r).1 ▸ (b r).factor_data (b r).selected |>.2.1) hs hdiv
      A.unit_analytic A.unit_ne (fun a ↦ (A.factor_data a).1) A.factorization
    exact ⟨a, gaga21_d2_associated_of_divides
      ((hb r).1 ▸ (b r).factor_data (b r).selected |>.1)
      ((hb r).1 ▸ (b r).factor_data (b r).selected |>.2.1)
      (A.factor_data a).2.1 hc hac⟩
  choose idx hidx using hfactor
  have hassoc : ∀ a : Fin A.count,
      Quotient.mk (gaga21_componentSetoid V f) (gaga23_occurrence j p hp A a) = C →
        ∃ r, AreAssociatedAt (A.factors a) (b r).factor p := by
    intro a ha
    exact (hmatch (gaga23_occurrence j p hp A a) rfl rfl).mp ha
  have hzero : ∀ a r, AreAssociatedAt (A.factors a) (b r).factor p →
      ∀ᶠ z in 𝓝 p, (A.factors a z = 0 ↔ (b r).factor z = 0) := by
    intro a r h
    obtain ⟨u, hu, hu0, he⟩ := h
    filter_upwards [he, hu.continuousAt.eventually_ne hu0] with z hez huz
    rw [hez, mul_eq_zero, or_iff_right huz]
  have hforward : ∀ r, ∀ᶠ z in 𝓝 p,
      ((b r).factor z = 0 ↔ A.factors (idx r) z = 0) := fun r ↦
    hzero (idx r) r (gaga21_br_associated_symm (hidx r)) |>.mono fun _ h ↦ h.symm
  have hback : ∀ a r, ∀ᶠ z in 𝓝 p,
      AreAssociatedAt (A.factors a) (b r).factor p →
        (A.factors a z = 0 ↔ (b r).factor z = 0) := by
    intro a r
    by_cases h : AreAssociatedAt (A.factors a) (b r).factor p
    · exact (hzero a r h).mono fun _ hz _ ↦ hz
    · exact Eventually.of_forall fun _ ha ↦ (h ha).elim
  filter_upwards [hlocal,
    eventually_all.mpr hforward,
    eventually_all.mpr (fun a ↦ eventually_all.mpr (hback a))]
    with z hz hforward hback
  constructor
  · intro hzC
    obtain ⟨r, hr⟩ := hz.mp hzC
    refine ⟨idx r, ?_, ?_⟩
    · exact (hmatch (gaga23_occurrence j p hp A (idx r)) rfl rfl).mpr
        ⟨r, gaga21_br_associated_symm (hidx r)⟩
    · exact (hforward r).mp hr
  · rintro ⟨a, haC, haz⟩
    obtain ⟨r, har⟩ := hassoc a haC
    exact hz.mpr ⟨r, (hback a r har).mp haz⟩

theorem gaga23_eventually_carrier_incident {d : ℕ} {J : Type}
    {V : J → Set (Fin d → ℂ)} {f : J → (Fin d → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f) (p : Fin d → ℂ) :
    ∀ᶠ z in 𝓝 p, ∀ C : gaga21_GlobalComponent V f,
      z ∈ gaga21_componentCarrier C → p ∈ gaga21_componentCarrier C := by
  classical
  obtain ⟨W, hW, hfin⟩ := gaga21_finite_incidence hD p (mem_univ p)
  let S := {C : gaga21_GlobalComponent V f |
    (gaga21_componentCarrier C ∩ W).Nonempty}
  have hclosed (C : gaga21_GlobalComponent V f) :
      IsClosed (gaga21_componentCarrier C) := by
    have h := (gaga21_carrier_geometry hD C).2.2.1
    simpa using h
  have hev : ∀ C ∈ S, ∀ᶠ z in 𝓝 p,
      z ∈ gaga21_componentCarrier C → p ∈ gaga21_componentCarrier C := by
    intro C _
    by_cases hpC : p ∈ gaga21_componentCarrier C
    · exact Eventually.of_forall fun _ _ ↦ hpC
    · filter_upwards [(hclosed C).isOpen_compl.mem_nhds hpC] with z hz
      exact fun hzC ↦ (hz hzC).elim
  filter_upwards [hW, hfin.eventually_all.mpr hev] with z hzW hz C hzC
  exact hz C ⟨z, hzC, hzW⟩ hzC

theorem gaga23_group_zeros_aux {d : ℕ} {J : Type}
    {V : J → Set (Fin d → ℂ)} {f : J → (Fin d → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin d → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (j : J) (p : Fin d → ℂ) (hp : p ∈ V j)
    (A : gaga23_Factorization (f j) p) :
    ∀ O : gaga22_ComponentOrbit Λ hD hper,
      (∀ᶠ z in 𝓝 p,
        gaga23_group A.factors (gaga23_label Λ hD hper j p hp A) O z = 0 ↔
          QuotientAddGroup.mk z ∈ (gaga22_descendedDivisor Λ hD hper).carrier O) ∧
      (QuotientAddGroup.mk p ∉ (gaga22_descendedDivisor Λ hD hper).carrier O →
        gaga23_group A.factors (gaga23_label Λ hD hper j p hp A) O p ≠ 0) := by
  classical
  intro O
  let π : (Fin d → ℂ) → (Fin d → ℂ) ⧸ Λ := QuotientAddGroup.mk
  have horbit (z : Fin d → ℂ) :
      π z ∈ (gaga22_descendedDivisor Λ hD hper).carrier O ↔
        ∃ C : gaga21_GlobalComponent V f,
          Quotient.mk (gaga22_orbitSetoid Λ hD hper) C = O ∧
            z ∈ gaga21_componentCarrier C := by
    constructor
    · intro hz
      change π z ∈ π '' gaga21_componentCarrier (Quotient.out O) at hz
      obtain ⟨x, hx, hxz⟩ := hz
      have hl : z - x ∈ Λ := QuotientAddGroup.eq_iff_sub_mem.mp hxz.symm
      let l : Λ := ⟨z - x, hl⟩
      let C := gaga22_translateComponent Λ hD hper l (Quotient.out O)
      refine ⟨C, ?_, ?_⟩
      · rw [← Quotient.out_eq O]
        apply Quotient.sound
        letI := gaga22_componentAction Λ hD hper
        exact AddAction.mem_orbit (Quotient.out O) l
      · rw [gaga22_carrier_translate Λ hD hper l]
        refine ⟨x, hx, ?_⟩
        simp only [l, AddSubgroup.coe_mk]
        abel
    · rintro ⟨C, hCO, hzC⟩
      rw [← hCO, (gaga22_descended_representative Λ hD hper C).1]
      exact ⟨z, hzC, rfl⟩
  obtain ⟨W, hW, hfin⟩ := gaga21_finite_incidence hD p (mem_univ p)
  let S := {C : gaga21_GlobalComponent V f |
    (gaga21_componentCarrier C ∩ W).Nonempty}
  have hlocal : ∀ C ∈ S, ∀ᶠ z in 𝓝 p,
      p ∈ gaga21_componentCarrier C →
        (z ∈ gaga21_componentCarrier C ↔ ∃ a : Fin A.count,
          Quotient.mk (gaga21_componentSetoid V f) (gaga23_occurrence j p hp A a) = C ∧
            A.factors a z = 0) := by
    intro C _
    by_cases hpC : p ∈ gaga21_componentCarrier C
    · exact (gaga23_component_factor_germ hD j p hp A C hpC).mono fun _ h _ ↦ h
    · exact Eventually.of_forall fun _ h ↦ (hpC h).elim
  have hall := hfin.eventually_all.mpr hlocal
  have hinc := gaga23_eventually_carrier_incident hD p
  have hgerm : ∀ᶠ z in 𝓝 p, ∀ a : Fin A.count,
      A.factors a z = 0 → z ∈ gaga21_componentCarrier
        (Quotient.mk (gaga21_componentSetoid V f) (gaga23_occurrence j p hp A a)) :=
    eventually_all.mpr fun a : Fin A.count ↦ by
      have hg := gaga21_br_germ_in_carrier hD (gaga23_occurrence j p hp A a)
      change ∀ᶠ z in 𝓝 p, A.factors a z = 0 → z ∈ gaga21_componentCarrier
        (Quotient.mk (gaga21_componentSetoid V f) (gaga23_occurrence j p hp A a)) at hg
      exact hg
  have heq : ∀ᶠ z in 𝓝 p,
      gaga23_group A.factors (gaga23_label Λ hD hper j p hp A) O z = 0 ↔
        π z ∈ (gaga22_descendedDivisor Λ hD hper).carrier O := by
    filter_upwards [hW, hall, hinc, hgerm] with z hzW hloc hincident hcarrier
    rw [horbit]
    simp only [gaga23_group, Finset.prod_eq_zero_iff, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, haO, haz⟩
      let C := Quotient.mk (gaga21_componentSetoid V f) (gaga23_occurrence j p hp A a)
      refine ⟨C, haO, ?_⟩
      exact hcarrier a haz
    · rintro ⟨C, hCO, hzC⟩
      have hCS : C ∈ S := ⟨z, hzC, hzW⟩
      obtain ⟨a, haC, haz⟩ := (hloc C hCS (hincident C hzC)).mp hzC
      have haO : gaga23_label Λ hD hper j p hp A a = O := by
        change Quotient.mk (gaga22_orbitSetoid Λ hD hper)
          (Quotient.mk (gaga21_componentSetoid V f) (gaga23_occurrence j p hp A a)) = O
        rw [haC]
        exact hCO
      exact ⟨a, haO, haz⟩
  refine ⟨heq, ?_⟩
  intro hpO hzero
  have := heq.self_of_nhds
  exact hpO (this.mp hzero)

theorem gaga23_group_associated_aux {d : ℕ} {J : Type}
    {V : J → Set (Fin d → ℂ)} {f : J → (Fin d → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin d → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    [CompactSpace ((Fin d → ℂ) ⧸ Λ)]
    (j : J) (p : Fin d → ℂ) (hp : p ∈ V j)
    (A : gaga23_Factorization (f j) p) :
    let N := gaga23_enumeration Λ hD hper
    AreAssociatedAt (f j) (fun z ↦ ∏ i : Fin N.1,
      gaga23_group A.factors (gaga23_label Λ hD hper j p hp A) (N.2 i) z ^
        (gaga22_descendedDivisor Λ hD hper).multiplicity (N.2 i)) p := by
  classical
  let N := gaga23_enumeration Λ hD hper
  let mult : gaga22_ComponentOrbit Λ hD hper → ℕ := fun O ↦
    (gaga22_descendedDivisor Λ hD hper).multiplicity O
  change AreAssociatedAt (f j) (fun z ↦ ∏ i : Fin N.1,
    gaga23_group A.factors (gaga23_label Λ hD hper j p hp A) (N.2 i) z ^
      mult (N.2 i)) p
  letI := Fintype.ofEquiv (Fin N.1) N.2
  refine ⟨A.unit, A.unit_analytic, A.unit_ne, A.factorization.trans ?_⟩
  exact Eventually.of_forall fun z ↦ congrArg (A.unit z * ·) (by
    change (∏ a, A.factors a z ^ A.exponents a) = ∏ i : Fin N.1,
      gaga23_group A.factors (gaga23_label Λ hD hper j p hp A) (N.2 i) z ^
        mult (N.2 i)
    calc
      _ = ∏ a, A.factors a z ^ mult (gaga23_label Λ hD hper j p hp A a) := by
        apply Finset.prod_congr rfl
        intro a _
        rw [gaga23_group_weights_aux Λ hD hper j p hp A a]
      _ = ∏ O : gaga22_ComponentOrbit Λ hD hper,
          ∏ a ∈ Finset.univ.filter (fun a ↦
            gaga23_label Λ hD hper j p hp A a = O),
            A.factors a z ^ mult (gaga23_label Λ hD hper j p hp A a) :=
        (Finset.prod_fiberwise Finset.univ
          (gaga23_label Λ hD hper j p hp A)
          (fun a ↦ A.factors a z ^ mult (gaga23_label Λ hD hper j p hp A a))).symm
      _ = ∏ O : gaga22_ComponentOrbit Λ hD hper,
          gaga23_group A.factors (gaga23_label Λ hD hper j p hp A) O z ^ mult O := by
        refine Finset.prod_congr rfl ?_
        intro O _
        rw [gaga23_group, ← Finset.prod_pow]
        simp only [Finset.prod_filter]
        apply Finset.prod_congr rfl
        intro a _
        by_cases ha : gaga23_label Λ hD hper j p hp A a = O
        · rw [if_pos ha, if_pos ha, ha]
        · rw [if_neg ha, if_neg ha]
      _ = _ := (Equiv.prod_comp N.2 _).symm)

private theorem gaga23_mk_mem_iff_exp_mem (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (O : (gaga22_descendedOnX X hD hper).Component)
    (z : Fin (dim X.left) → ℂ) :
    QuotientAddGroup.mk z ∈
        (gaga22_descendedDivisor (abelianPeriodLattice X).toAddSubgroup hD hper).carrier O ↔
      abelianExp X z ∈ (gaga22_descendedOnX X hD hper).carrier O := by
  constructor
  · rintro ⟨w, hw, heq⟩
    exact ⟨w, hw, (abelianExp_eq_iff_proj_eq X w z).2 heq⟩
  · rintro ⟨w, hw, heq⟩
    exact ⟨w, hw, (abelianExp_eq_iff_proj_eq X w z).1 heq⟩

theorem gaga23_local_equations_aux (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C)
    (j : J) (p : Fin (dim X.left) → ℂ) (hp : p ∈ V j) :
    let N := gaga23_schemeEnumeration X hD hper hChow
    let A := gaga23_factorization (f j) p (hD.2.2.1 j p hp) (hD.2.2.2.1 j p hp)
    let g := fun i : Fin N.1 ↦ gaga23_group A.factors
      (gaga23_label (abelianPeriodLattice X).toAddSubgroup hD hper j p hp A) (N.2 i)
    ∃ hg : ∀ i, AnalyticAt ℂ (g i) p,
      (∀ i, Squarefree (⟨Filter.Germ.ofFun (g i), g i, hg i, rfl⟩ :
        AnalyticGermAt (dim X.left) p)) ∧
      (∀ i, ∀ᶠ z in 𝓝 p, g i z = 0 ↔ abelianExp X z ∈
        gaga23_componentSupport X (gaga23_point X hD hper hChow (N.2 i))) ∧
      AreAssociatedAt (f j) (fun z ↦ ∏ i, g i z ^
        (gaga22_descendedOnX X hD hper).multiplicity (N.2 i)) p := by
  classical
  letI : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  letI : CompactSpace ((Fin (dim X.left) → ℂ) ⧸
      (abelianPeriodLattice X).toAddSubgroup) :=
    compact_complexExponentialQuotient X (dim X.left)
  let N := gaga23_schemeEnumeration X hD hper hChow
  let A := gaga23_factorization (f j) p (hD.2.2.1 j p hp) (hD.2.2.2.1 j p hp)
  let label := gaga23_label (abelianPeriodLattice X).toAddSubgroup hD hper j p hp A
  let g := fun i : Fin N.1 ↦ gaga23_group A.factors label (N.2 i)
  obtain ⟨hg, hsq⟩ := gaga23_group_squarefree_aux (f j) p A label
  refine ⟨fun i ↦ hg (N.2 i), fun i ↦ hsq (N.2 i), ?_, ?_⟩
  · intro i
    filter_upwards [(gaga23_group_zeros_aux
      (abelianPeriodLattice X).toAddSubgroup hD hper j p hp A (N.2 i)).1] with z hz
    rw [hz, gaga23_mk_mem_iff_exp_mem X hD hper (N.2 i) z]
    change abelianExp X z ∈ (gaga22_descendedOnX X hD hper).carrier (N.2 i) ↔
      abelianExp X z ∈ gaga23_componentSupport X
        (gaga23_point X hD hper hChow (N.2 i))
    unfold gaga23_componentSupport
    rw [(gaga23_indexing_aux X hD hper hChow).1 i]
    change abelianExp X z ∈ (gaga22_descendedOnX X hD hper).carrier (N.2 i) ↔
      abelianExp X z ∈ (Point.underlying : ComplexPoint X → X.left) ⁻¹'
        gaga23_carrier X hD hper hChow (N.2 i)
    unfold gaga23_carrier
    rw [← (gaga22_chow_support X hD hper hChow).2.choose_spec.2.1 (N.2 i) |>.2.2.1]
  · exact gaga23_group_associated_aux
      (abelianPeriodLattice X).toAddSubgroup hD hper j p hp A

theorem gaga23_algebraization_without_codim_aux (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C) :
    ∃ (n : ℕ) (x : Fin n → X.left) (mult : Fin n → ℕ),
      Function.Injective x ∧
      (∀ i, 0 < mult i) ∧
      (abelianExp X '' localDivisorSupport V f = ⋃ i, gaga23_componentSupport X (x i)) ∧
      (∀ j p, p ∈ V j →
        ∃ (g : Fin n → (Fin (dim X.left) → ℂ) → ℂ)
          (hg : ∀ i, AnalyticAt ℂ (g i) p),
          (∀ i, Squarefree (⟨Filter.Germ.ofFun (g i), g i, hg i, rfl⟩ :
            AnalyticGermAt (dim X.left) p)) ∧
          (∀ i, ∀ᶠ z in 𝓝 p, g i z = 0 ↔
            abelianExp X z ∈ gaga23_componentSupport X (x i)) ∧
          AreAssociatedAt (f j) (fun z ↦ ∏ i, g i z ^ mult i) p) := by
  classical
  let N := gaga23_schemeEnumeration X hD hper hChow
  let x := fun i : Fin N.1 ↦ gaga23_point X hD hper hChow (N.2 i)
  let mult := fun i : Fin N.1 ↦ (gaga22_descendedOnX X hD hper).multiplicity (N.2 i)
  obtain ⟨_, hinj, hpos, hsupp⟩ := gaga23_indexing_aux X hD hper hChow
  refine ⟨N.1, x, mult, hinj, hpos, hsupp, ?_⟩
  intro j p hp
  let A := gaga23_factorization (f j) p (hD.2.2.1 j p hp) (hD.2.2.2.1 j p hp)
  refine ⟨fun i ↦ gaga23_group A.factors
    (gaga23_label (abelianPeriodLattice X).toAddSubgroup hD hper j p hp A) (N.2 i), ?_⟩
  exact gaga23_local_equations_aux X hD hper hChow j p hp

end HodgeLean.Foundations.AnalyticDivisorAlgebraic23
