import HodgeLean.Foundations.Analytic.AnalytificationDefs
import HodgeLean.Foundations.Analytic.AnalytificationAn5
import HodgeLean.Foundations.Analytic.AnalytificationAn2Range
import HodgeLean.Foundations.Analytic.AnalytificationAnDbl
import HodgeLean.Foundations.Analytic.AnalytificationChowProjective
import HodgeLean.Foundations.Analytic.AnalytificationChow3Lemma
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpace
import HodgeLean.Foundations.AnalyticDivisorAlgebraicProofs
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Proof obligations for the analytification specification

The statements about the analytification take the four proofs of `f4_an` (covering, Hausdorff,
second countable, analytic atlas) as arguments; any two proofs of the same proposition are equal,
so these are statements about the one space `f4_analytification` of the frozen file. -/

noncomputable section

open Set Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry.ComplexPoint
open scoped ContDiff Manifold CategoryTheory.MonObj TensorProduct

namespace HodgeLean.Foundations.Analytic

/-! ### Charts and the space -/

theorem f4_an2_continuous_toFun {X : Over (Spec ↧ℂ)} (r : f4_RawChart X) :
    Continuous (r.dom.domRestrict r.toFun) := by
  rw [continuous_pi_iff]
  intro a
  rw [continuous_def]
  intro V hV
  let W : Set (ComplexPoint X) :=
    Point.overOpen r.U.1 ∩ Point.evaluate r.U.1 (r.coord a) ⁻¹' V
  have hW : IsOpen W :=
    Point.isOpen_overOpen_inter_preimage r.U.1 (r.coord a) V hV
  convert hW.preimage continuous_subtype_val using 1
  ext z
  simp [W, f4_RawChart.toFun]

theorem f4_isEmbedding_of_generates_aux {X : Over (Spec ↧ℂ)} (r : f4_RawChart X)
    (hr : r.Generates) : IsEmbedding (r.dom.domRestrict r.toFun) := by
  letI : Algebra ℂ Γ(r.U.1.toScheme, ⊤) :=
    ((Scheme.ΓSpecIso ↧ℂ).inv ≫ (r.U.1.ι ≫ X.hom).appTop).hom.toAlgebra
  let c : Fin r.n → Γ(r.U.1.toScheme, ⊤) :=
    fun i ↦ (AnalytificationAn2_sectionIso r.U).hom (r.coord i)
  let e := AnalytificationAn2_openPointAlgHomHomeomorph r.U
  have hc : IsEmbedding (fun φ : Γ(r.U.1.toScheme, ⊤) →ₐ[ℂ] ℂ ↦
      fun i ↦ φ (c i)) := by
    apply AnalytificationAn2_isEmbedding_coordinates c
    intro s
    obtain ⟨p, hp⟩ := hr ((AnalytificationAn2_sectionIso r.U).inv s)
    refine ⟨p, fun φ ↦ ?_⟩
    let z := e.symm φ
    have hs := AnalytificationAn2_openPointAlgHomHomeomorph_apply r.U z
      ((AnalytificationAn2_sectionIso r.U).inv s)
    have hcoord (i : Fin r.n) :=
      AnalytificationAn2_openPointAlgHomHomeomorph_apply r.U z (r.coord i)
    rw [e.apply_symm_apply] at hs hcoord
    have hs' : φ s = Point.evaluate r.U.1
        ((AnalytificationAn2_sectionIso r.U).inv s) z.1 := by simpa using hs
    rw [hs', hp z.1 z.2]
    apply congrArg (fun v ↦ MvPolynomial.eval v p)
    funext i
    exact (hcoord i).symm
  have he := hc.comp e.isEmbedding
  convert he using 1
  funext z i
  exact (AnalytificationAn2_openPointAlgHomHomeomorph_apply r.U z (r.coord i)).symm

theorem f4_image_eq_of_isPresentation_aux {X : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom]
    (r : f4_RawChart X) (hr : r.IsPresentation) :
    r.toFun '' r.dom = an_zeroLocus univ r.eqns := by
  letI : Algebra ℂ Γ(r.U.1.toScheme, ⊤) :=
    ((Scheme.ΓSpecIso ↧ℂ).inv ≫ (r.U.1.ι ≫ X.hom).appTop).hom.toAlgebra
  let c : Fin r.n → Γ(r.U.1.toScheme, ⊤) :=
    fun i ↦ (AnalytificationAn2_sectionIso r.U).hom (r.coord i)
  let e := AnalytificationAn2_openPointAlgHomHomeomorph r.U
  have hgen : ∀ s : Γ(r.U.1.toScheme, ⊤), ∃ p : MvPolynomial (Fin r.n) ℂ,
      ∀ φ : Γ(r.U.1.toScheme, ⊤) →ₐ[ℂ] ℂ,
        φ s = MvPolynomial.eval (fun i ↦ φ (c i)) p := by
    intro s
    obtain ⟨p, hp⟩ := hr.1 ((AnalytificationAn2_sectionIso r.U).inv s)
    refine ⟨p, fun φ ↦ ?_⟩
    let z := e.symm φ
    have hs := AnalytificationAn2_openPointAlgHomHomeomorph_apply r.U z
      ((AnalytificationAn2_sectionIso r.U).inv s)
    have hcoord (i : Fin r.n) :=
      AnalytificationAn2_openPointAlgHomHomeomorph_apply r.U z (r.coord i)
    rw [e.apply_symm_apply] at hs hcoord
    have hs' : φ s = Point.evaluate r.U.1
        ((AnalytificationAn2_sectionIso r.U).inv s) z.1 := by simpa using hs
    rw [hs', hp z.1 z.2]
    apply congrArg (fun v ↦ MvPolynomial.eval v p)
    funext i
    exact (hcoord i).symm
  have hrel (p : MvPolynomial (Fin r.n) ℂ) :
      (∀ φ : Γ(r.U.1.toScheme, ⊤) →ₐ[ℂ] ℂ,
        MvPolynomial.eval (fun i ↦ φ (c i)) p = 0) ↔
          p ∈ Ideal.span (range r.eqn) := by
    rw [← hr.2 p]
    constructor
    · intro h z hz
      let zu : {z : ComplexPoint X // z ∈ r.dom} := ⟨z, hz⟩
      have hc (i : Fin r.n) :=
        AnalytificationAn2_openPointAlgHomHomeomorph_apply r.U zu (r.coord i)
      have heq : (fun i ↦ (e zu) (c i)) = r.toFun z := by
        funext i
        exact hc i
      have hh := h (e zu)
      rw [heq] at hh
      exact hh
    · intro h φ
      let z := e.symm φ
      have hc (i : Fin r.n) :=
        AnalytificationAn2_openPointAlgHomHomeomorph_apply r.U z (r.coord i)
      rw [e.apply_symm_apply] at hc
      have heq : (fun i ↦ φ (c i)) = r.toFun z.1 := by
        funext i
        exact hc i
      rw [heq]
      exact h z.1 z.2
  have H := AnalytificationAn2_range_coordinates c r.eqn hgen hrel
  rw [show an_zeroLocus univ r.eqns =
      {w | ∀ j, MvPolynomial.eval w (r.eqn j) = 0} by
    ext w
    simp only [an_zeroLocus, mem_univ, true_and, mem_setOf_eq]
    constructor
    · intro h j
      exact congrFun h j
    · intro h
      funext j
      exact h j]
  rw [← H]
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨e ⟨z, hz⟩, ?_⟩
    funext i
    exact AnalytificationAn2_openPointAlgHomHomeomorph_apply r.U ⟨z, hz⟩ (r.coord i)
  · rintro ⟨φ, rfl⟩
    let z := e.symm φ
    refine ⟨z.1, z.2, ?_⟩
    funext i
    have hc := AnalytificationAn2_openPointAlgHomHomeomorph_apply r.U z (r.coord i)
    rw [e.apply_symm_apply] at hc
    exact hc.symm

theorem f4_exists_presentation_aux (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (U : X.left.affineOpens) : ∃ r : f4_RawChart X, r.U = U ∧ r.IsPresentation := by
  let e : U.1 ≤ X.hom ⁻¹ᵁ ⊤ := by simp
  letI : Algebra ℂ Γ(X.left, U.1) :=
    ((Scheme.ΓSpecIso ↧ℂ).inv ≫ X.hom.appLE ⊤ U.1 e).hom.toAlgebra
  have hft : Algebra.FiniteType ℂ Γ(X.left, U.1) := by
    refine RingHom.finiteType_algebraMap.mp ?_
    change ((X.hom.appLE ⊤ U.1 e).hom.comp (Scheme.ΓSpecIso ↧ℂ).inv.hom).FiniteType
    exact RingHom.FiniteType.comp
      (X.hom.finiteType_appLE (isAffineOpen_top _) U.2 e)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso ↧ℂ).inv).2)
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  let coord : Fin n → Γ(X.left, U.1) := fun a ↦ φ (MvPolynomial.X a)
  let I : Ideal (MvPolynomial (Fin n) ℂ) :=
    { carrier := {p | ∀ z : ComplexPoint X, z ∈ Point.overOpen U.1 →
          MvPolynomial.eval (fun a ↦ Point.evaluate U.1 (coord a) z) p = 0}
      zero_mem' := fun _ _ ↦ map_zero _
      add_mem' := fun hp hq z hz ↦ by rw [map_add, hp z hz, hq z hz, add_zero]
      smul_mem' := fun p q hq z hz ↦ by rw [smul_eq_mul, map_mul, hq z hz, mul_zero] }
  have hIfg : I.FG := IsNoetherian.noetherian I
  obtain ⟨k, eqn, heqn⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hIfg
  let r : f4_RawChart X := ⟨U, n, coord, k, eqn⟩
  refine ⟨r, rfl, ?_, fun p ↦ ?_⟩
  · intro s
    obtain ⟨p, hp⟩ := hφ s
    refine ⟨p, fun z hz ↦ ?_⟩
    let ev : Γ(X.left, U.1) →ₐ[ℂ] ℂ :=
      { (Point.evaluationHom U.1 ⟨z, hz⟩).hom with
        commutes' := fun c ↦ by
          change Point.evaluationHom U.1 ⟨z, hz⟩ (algebraMap ℂ Γ(X.left, U.1) c) =
            algebraMap ℂ ℂ c
          rw [Point.evaluationHom_apply]
          change Point.evaluate U.1 (algebraMap ℂ Γ(X.left, U.1) c) z = c
          let q := (Scheme.ΓSpecIso ↧ℂ).inv c
          calc
            _ = Point.evaluate (X.hom ⁻¹ᵁ ⊤) (X.hom.app ⊤ q) z := by
              rw [Point.evaluate_res e (X.hom.app ⊤ q) z hz]
              rfl
            _ = Point.evaluate ⊤ q (Point.map (f4_toPoint X) z) :=
              (Point.evaluate_map (f4_toPoint X) ⊤ q z).symm
            _ = c := by
              rw [evaluate_top_eq_appTop]
              rw [Subsingleton.elim (Point.map (f4_toPoint X) z) (𝟙 f4_point)]
              change (Scheme.ΓSpecIso ↧ℂ).hom
                (Scheme.Hom.appTop (𝟙 (Spec ↧ℂ)) q) = c
              rw [Scheme.Hom.id_appTop]
              dsimp [q]
              exact (Scheme.ΓSpecIso ↧ℂ).inv_hom_id_apply c }
    have hev (q : MvPolynomial (Fin n) ℂ) :
        ev (φ q) = MvPolynomial.eval (fun a ↦ ev (coord a)) q := by
      induction q using MvPolynomial.induction_on with
      | C c => simp
      | add p q hp hq => simp only [map_add, hp, hq]
      | mul_X p a hp => simp only [map_mul, hp, coord, MvPolynomial.eval_mul,
          MvPolynomial.eval_X]
    rw [← hp]
    rw [← Point.evaluationHom_apply U.1 ⟨z, hz⟩ (φ p)]
    change ev (φ p) = _
    rw [hev]
    have hw : (fun a ↦ ev (coord a)) = r.toFun z := by
      funext a
      change Point.evaluationHom U.1 ⟨z, hz⟩ (coord a) =
        Point.evaluate U.1 (coord a) z
      exact Point.evaluationHom_apply U.1 ⟨z, hz⟩ (coord a)
    rw [hw]
  · change p ∈ I ↔ p ∈ Ideal.span (range eqn)
    rw [← heqn]

theorem f4_covers_aux (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] :
    ∀ z : ComplexPoint X, ∃ r : f4_AdmChart X, z ∈ r.1.dom := by
  intro z
  obtain ⟨U, hU, hzU, -⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open (mem_univ z.underlying) isOpen_univ
  obtain ⟨Ua, hUa, rfl⟩ := hU
  let Uaff : X.left.affineOpens := ⟨Ua, hUa⟩
  obtain ⟨r, hrU, hr⟩ := f4_exists_presentation_aux X Uaff
  have hadm : r.IsAdmissible :=
    ⟨hr.1, f4_isEmbedding_of_generates_aux r hr.1,
      f4_image_eq_of_isPresentation_aux r hr⟩
  refine ⟨⟨r, hadm⟩, ?_⟩
  change z.underlying ∈ r.U.1
  rw [hrU]
  exact hzU

theorem f4_atlas_isAnalytic_aux (X : Over (Spec ↧ℂ))
    (h : ∀ z : ComplexPoint X, ∃ r : f4_AdmChart X, z ∈ r.1.dom) :
    (f4_atlas X h).IsAnalytic := by
  intro i j x hx
  change x ∈ j.1.dom ∩ i.1.dom at hx
  change ∃ W : Set (Fin i.1.n → ℂ), IsOpen W ∧ i.1.toFun x ∈ W ∧
    ∃ G : (Fin i.1.n → ℂ) → (Fin j.1.n → ℂ), AnalyticOnNhd ℂ G W ∧
      ∀ y ∈ j.1.dom ∩ i.1.dom, i.1.toFun y ∈ W → j.1.toFun y = G (i.1.toFun y)
  obtain ⟨f, hf, hxf⟩ := i.1.U.2.exists_basicOpen_le
    ⟨x.underlying, hx.1⟩ hx.2
  let t (a : Fin j.1.n) : Γ(X.left, X.left.basicOpen f) :=
    X.left.presheaf.map (homOfLE hf).op (j.1.coord a)
  choose k b hb using fun a ↦
    Point.exists_evaluate_basicOpen_eq_div i.1.U.2 f (t a)
  choose pf hpf using i.2.1 f
  choose pb hpb using fun a ↦ i.2.1 (b a)
  let W : Set (Fin i.1.n → ℂ) := {w | MvPolynomial.eval w pf ≠ 0}
  refine ⟨W, ?_, ?_, fun w a ↦ MvPolynomial.eval w (pb a) /
      MvPolynomial.eval w pf ^ k a, ?_, ?_⟩
  · exact isOpen_ne_fun (MvPolynomial.continuous_eval pf) continuous_const
  · change MvPolynomial.eval (i.1.toFun x) pf ≠ 0
    rw [← hpf x hx.2]
    exact (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero f x hx.2).mp hxf
  · intro w hw
    exact analyticAt_pi_iff.2 fun a ↦
      (AnalyticOnNhd.eval_mvPolynomial (pb a) w (mem_univ w)).div
        ((AnalyticOnNhd.eval_mvPolynomial pf w (mem_univ w)).pow (k a)) (pow_ne_zero _ hw)
  · intro y hy hyW
    have hyf : y ∈ Point.overOpen (X.left.basicOpen f) :=
      (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero f y hy.2).2 (by
        rw [hpf y hy.2]
        exact hyW)
    funext a
    rw [show j.1.toFun y a = Point.evaluate j.1.U.1 (j.1.coord a) y from rfl]
    rw [Point.evaluate_res hf (j.1.coord a) y hyf]
    rw [hb a y hyf]
    rw [hpb a y hy.2, hpf y hy.2]

theorem f4_secondCountable_aux (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] : SecondCountableTopology (ComplexPoint X) := by
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have hcover : univ ⊆ ⋃ U : X.left.affineOpens, (U : Set X.left) := by
    intro x _
    obtain ⟨V, hV, hxV, -⟩ :=
      X.left.isBasis_affineOpens.exists_subset_of_mem_open (mem_univ x) isOpen_univ
    obtain ⟨U, hU, rfl⟩ := hV
    exact mem_iUnion.mpr ⟨⟨U, hU⟩, hxV⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.left.affineOpens ↦ (U : Set X.left))
    (fun U ↦ U.1.2) hcover
  let r (i : s) : f4_RawChart X := Classical.choose (f4_exists_presentation_aux X i.1)
  have hr (i : s) : (r i).U = i.1 ∧ (r i).IsPresentation :=
    Classical.choose_spec (f4_exists_presentation_aux X i.1)
  have hemb (i : s) : IsEmbedding ((r i).dom.domRestrict (r i).toFun) :=
    f4_isEmbedding_of_generates_aux (r i) (hr i).2.1
  let U (i : s) : Set (ComplexPoint X) := (r i).dom
  let inst (i : s) : SecondCountableTopology (U i) := (hemb i).secondCountableTopology
  letI (i : s) : SecondCountableTopology (U i) := inst i
  refine TopologicalSpace.secondCountableTopology_of_countable_cover (U := U) ?_ ?_
  · intro i
    exact Point.isOpen_overOpen _
  · ext z
    simp only [mem_iUnion, mem_univ, iff_true]
    have hz : z.underlying ∈ ⋃ i ∈ s, (i : Set X.left) := hs (mem_univ _)
    simp only [mem_iUnion] at hz
    obtain ⟨i, hi, hzi⟩ := hz
    refine ⟨⟨i, hi⟩, ?_⟩
    change z.underlying ∈ (r ⟨i, hi⟩).U.1
    rw [(hr ⟨i, hi⟩).1]
    exact hzi

theorem f4_cuspChart_not_generates_aux :
    IsEmbedding (f4_cuspChart.dom.domRestrict f4_cuspChart.toFun) ∧
      f4_cuspChart.toFun '' f4_cuspChart.dom = an_zeroLocus univ f4_cuspChart.eqns ∧
      ¬ f4_cuspChart.Generates := by
  exact ⟨AnalytificationAn4_cuspChart_isEmbedding,
    AnalytificationAn5_cuspChart_range, AnalytificationAn5_cuspChart_not_generates⟩

/-! ### Functions and maps -/

theorem f4_isHolFun_evaluate_aux (X : Over (Spec ↧ℂ))
    (hcov : ∀ z : ComplexPoint X, ∃ r : f4_AdmChart X, z ∈ r.1.dom)
    (ht2 : T2Space (ComplexPoint X)) (hsc : SecondCountableTopology (ComplexPoint X))
    (han : (f4_atlas X hcov).IsAnalytic) (U : X.left.Opens) (s : Γ(X.left, U)) :
    (f4_an X hcov ht2 hsc han).IsHolFun
      (fun z : (Point.overOpen U : Set (ComplexPoint X)) ↦
        Point.evaluate U s (z : ComplexPoint X)) := by
  intro x r hxr
  obtain ⟨f, hfU, hxf⟩ := r.1.U.2.exists_basicOpen_le
    (V := U) ⟨x.1.underlying, x.2⟩ hxr
  let t : Γ(X.left, X.left.basicOpen f) :=
    X.left.presheaf.map (homOfLE hfU).op s
  obtain ⟨k, a, ha⟩ := Point.exists_evaluate_basicOpen_eq_div
    (X := X) r.1.U.2 f t
  obtain ⟨pa, hpa⟩ := r.2.1 a
  obtain ⟨pf, hpf⟩ := r.2.1 f
  let G : (Fin r.1.n → ℂ) → ℂ := fun w ↦
    MvPolynomial.eval w pa / MvPolynomial.eval w pf ^ k
  have hfx : MvPolynomial.eval (r.1.toFun x) pf ≠ 0 := by
    rw [← hpf x hxr]
    exact (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero f x hxr).mp hxf
  have hG : AnalyticAt ℂ G (r.1.toFun x) :=
    (AnalyticOnNhd.eval_mvPolynomial pa _ (mem_univ _)).div
      ((AnalyticOnNhd.eval_mvPolynomial pf _ (mem_univ _)).pow k) (pow_ne_zero k hfx)
  refine ⟨Point.overOpen (X.left.basicOpen f), Point.isOpen_overOpen _, hxf, G, hG, ?_⟩
  intro y hy
  change Point.evaluate U s y = G (r.1.toFun y)
  rw [Point.evaluate_res hfU s y hy.1]
  rw [ha y hy.1, hpa y hy.2, hpf y hy.2]

theorem f4_map_isHom_aux {X Y : Over (Spec ↧ℂ)}
    (hcov : ∀ z : ComplexPoint X, ∃ r : f4_AdmChart X, z ∈ r.1.dom)
    (ht2 : T2Space (ComplexPoint X)) (hsc : SecondCountableTopology (ComplexPoint X))
    (han : (f4_atlas X hcov).IsAnalytic)
    (hcov' : ∀ z : ComplexPoint Y, ∃ r : f4_AdmChart Y, z ∈ r.1.dom)
    (ht2' : T2Space (ComplexPoint Y)) (hsc' : SecondCountableTopology (ComplexPoint Y))
    (han' : (f4_atlas Y hcov').IsAnalytic) (f : X ⟶ Y) :
    an_IsHom (f4_an X hcov ht2 hsc han) (f4_an Y hcov' ht2' hsc' han') (Point.map f) := by
  rw [an_isHom_iff_chart]
  refine ⟨Point.continuous_map f, ?_⟩
  intro q r x hx
  obtain ⟨a, ha, hxa⟩ := r.1.U.2.exists_basicOpen_le
    (V := f.left ⁻¹ᵁ q.1.U.1)
    ⟨x.underlying, (Point.mem_overOpen_map_iff f x q.1.U.1).mp hx.1⟩ hx.2
  let t (i : Fin q.1.n) : Γ(X.left, X.left.basicOpen a) :=
    X.left.presheaf.map (homOfLE ha).op (f.left.app q.1.U.1 (q.1.coord i))
  choose k b hb using fun i ↦
    Point.exists_evaluate_basicOpen_eq_div (X := X) r.1.U.2 a (t i)
  choose pb hpb using fun i ↦ r.2.1 (b i)
  obtain ⟨pa, hpa⟩ := r.2.1 a
  let G : (Fin r.1.n → ℂ) → (Fin q.1.n → ℂ) := fun w i ↦
    MvPolynomial.eval w (pb i) / MvPolynomial.eval w pa ^ k i
  let W : Set (Fin r.1.n → ℂ) := {w | MvPolynomial.eval w pa ≠ 0}
  have hpa_cont : Continuous (fun w : Fin r.1.n → ℂ ↦ MvPolynomial.eval w pa) :=
    continuous_iff_continuousAt.2 fun w ↦
      (AnalyticOnNhd.eval_mvPolynomial pa w (mem_univ _)).continuousAt
  have hW : IsOpen W := isOpen_ne_fun hpa_cont continuous_const
  have hxW : r.1.toFun x ∈ W := by
    change MvPolynomial.eval (r.1.toFun x) pa ≠ 0
    rw [← hpa x hx.2]
    exact (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero a x hx.2).mp hxa
  have hG : AnalyticOnNhd ℂ G W := fun w hw ↦ AnalyticAt.pi fun i ↦
    (AnalyticOnNhd.eval_mvPolynomial (pb i) w (mem_univ _)).div
      ((AnalyticOnNhd.eval_mvPolynomial pa w (mem_univ _)).pow (k i))
      (pow_ne_zero _ hw)
  refine ⟨W, hW, hxW, G, hG, ?_⟩
  intro y hy hyW
  funext i
  have hya : y ∈ Point.overOpen (X.left.basicOpen a) :=
    (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero a y hy.2).mpr (by
      change MvPolynomial.eval (r.1.toFun y) pa ≠ 0 at hyW
      rw [hpa y hy.2]
      exact hyW)
  change Point.evaluate q.1.U.1 (q.1.coord i) (Point.map f y) = G (r.1.toFun y) i
  rw [Point.evaluate_map]
  rw [Point.evaluate_res ha (f.left.app q.1.U.1 (q.1.coord i)) y hya]
  rw [hb i y hya, hpb i y hy.2, hpa y hy.2]

/-! ### Fibre products -/

theorem f4_pullbackPair_range_aux {X Y Z : Over (Spec ↧ℂ)} (f : X ⟶ Y) (g : Z ⟶ Y) :
    range (f4_pullbackPair f g) = {p | Point.map f p.1 = Point.map g p.2} := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    simp only [f4_pullbackPair, mem_setOf_eq, Point.map, Category.assoc,
      pullback.condition]
  · intro hp
    let z : ComplexPoint (pullback f g) := pullback.lift p.1 p.2 hp
    refine ⟨z, Prod.ext ?_ ?_⟩
    · exact pullback.lift_fst p.1 p.2 hp
    · exact pullback.lift_snd p.1 p.2 hp

theorem f4_pullbackPair_isEmbedding_aux {X Y Z : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Z ⟶ Y) :
    IsEmbedding (f4_pullbackPair f g) := by
  let k : (pullback f g).left ⟶ (X ⊗ Z).left :=
    pullback.lift (pullback.fst f g).left (pullback.snd f g).left (by
      rw [Over.w (pullback.fst f g), Over.w (pullback.snd f g)])
  let j : pullback f g ⟶ X ⊗ Z := Over.homMk
    k (by
      change k ≫ (pullback.fst X.hom Z.hom ≫ X.hom) = _
      simp [k, Category.assoc, Over.w (pullback.fst f g)])
  letI : IsImmersion j.left := by
    have hk : k = pullbackComparison (Over.forget (Spec ↧ℂ)) f g ≫
        pullback.mapDesc f.left g.left Y.hom ≫
        (pullback.congrHom (Over.w f) (Over.w g)).hom := by
      apply pullback.hom_ext
      · simpa [k, pullback.congrHom, Category.assoc] using
          (pullbackComparison_comp_fst (Over.forget (Spec ↧ℂ)) f g).symm
      · simpa [k, pullback.congrHom, Category.assoc] using
          (pullbackComparison_comp_snd (Over.forget (Spec ↧ℂ)) f g).symm
    change IsImmersion k
    rw [hk]
    infer_instance
  have hj : IsEmbedding (Point.map j) :=
    AnalytificationAn5_isEmbedding_map_of_immersion j
  have he := (HodgeLean.Foundations.complexPointProdHomeomorph X Z).isEmbedding
  have hfun : f4_pullbackPair f g =
      HodgeLean.Foundations.complexPointProdHomeomorph X Z ∘ Point.map j := by
    funext z
    apply Prod.ext <;> apply Over.OverMorphism.ext
    · change z.left ≫ (pullback.fst f g).left =
        (z.left ≫ k) ≫
          pullback.fst X.hom Z.hom
      simp [k, Category.assoc]
    · change z.left ≫ (pullback.snd f g).left =
        (z.left ≫ k) ≫
          pullback.snd X.hom Z.hom
      simp [k, Category.assoc]
  rw [hfun]
  exact he.comp hj

theorem f4_t2Space_aux (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [IsSeparated X.hom] :
    T2Space (ComplexPoint X) := by
  rw [t2_iff_isClosed_diagonal]
  let f := f4_toPoint X
  let e := equalizer.ι (pullback.fst f f) (pullback.snd f f)
  have he : IsClosedEmbedding (Point.map e) := by
    exact ComplexPoint.isClosedEmbedding_map_of_closedImmersion (i := e)
  have hp : IsEmbedding (f4_pullbackPair f f) :=
    f4_pullbackPair_isEmbedding_aux f f
  have hsurj : Function.Surjective (f4_pullbackPair f f) := by
    intro p
    rw [← mem_range]
    rw [f4_pullbackPair_range_aux]
    exact Subsingleton.elim _ _
  have hh : IsClosedEmbedding (f4_pullbackPair f f) :=
    (hp.toHomeomorphOfSurjective hsurj).isClosedEmbedding
  have hc : IsClosed (range (f4_pullbackPair f f ∘ Point.map e)) :=
    (hh.comp he).isClosed_range
  have hrange : range (f4_pullbackPair f f ∘ Point.map e) =
      diagonal (ComplexPoint X) := by
    ext p
    rw [mem_range, mem_diagonal_iff]
    constructor
    · rintro ⟨z, rfl⟩
      have hz := congrArg Point.map
        (equalizer.condition (pullback.fst f f) (pullback.snd f f))
      exact congrFun hz z
    · intro hp'
      obtain ⟨q, hq⟩ := hsurj p
      have hq1 : Point.map (pullback.fst f f) q = p.1 := congrArg Prod.fst hq
      have hq2 : Point.map (pullback.snd f f) q = p.2 := congrArg Prod.snd hq
      have hqe : Point.map (pullback.fst f f) q = Point.map (pullback.snd f f) q := by
        rw [hq1, hq2, hp']
      let z : ComplexPoint (equalizer (pullback.fst f f) (pullback.snd f f)) :=
        equalizer.lift q hqe
      refine ⟨z, ?_⟩
      have hzq : Point.map e z = q := by
        have hz := congrArg Point.map (equalizer.lift_ι q hqe)
        exact congrFun hz (𝟙 f4_point)
      change f4_pullbackPair f f (Point.map e z) = p
      rw [hzq]
      exact hq
  rwa [hrange] at hc

theorem f4_exists_not_t2Space_aux :
    ∃ X : Over (Spec ↧ℂ), LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom ∧
      ¬ IsSeparated X.hom ∧ ¬ T2Space (ComplexPoint X) := by
  refine ⟨AnalytificationDbl, inferInstance, inferInstance, ?_,
    AnalytificationDbl_not_t2Space⟩
  intro h
  letI : IsSeparated AnalytificationDbl.hom := h
  exact AnalytificationDbl_not_t2Space (f4_t2Space_aux AnalytificationDbl)

/-! ### Closed subschemes -/

theorem f4_isClosedAnalytic_preimage_aux (X : Over (Spec ↧ℂ))
    (hcov : ∀ z : ComplexPoint X, ∃ r : f4_AdmChart X, z ∈ r.1.dom)
    (ht2 : T2Space (ComplexPoint X)) (hsc : SecondCountableTopology (ComplexPoint X))
    (han : (f4_atlas X hcov).IsAnalytic) [LocallyOfFiniteType X.hom] (Z : Set X.left)
    (hZ : IsClosed Z) :
    an_IsClosedAnalytic (f4_an X hcov ht2 hsc han) (Point.underlying ⁻¹' Z) := by
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  refine ⟨?_, fun x hx ↦ ?_⟩
  · rw [← isOpen_compl_iff]
    convert Point.isOpen_overOpen (X := X) ⟨Zᶜ, hZ.isOpen_compl⟩ using 1
    ext z
    rfl
  · obtain ⟨U, hU, hxU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X.left) (U := ⊤) (Set.mem_univ x.underlying)
    obtain ⟨s, hs⟩ :=
      AnalyticDivisorAlgebraic.exists_finset_basicOpen hZ hU
    let e : Fin s.card ≃ s := s.equivFin.symm
    refine ⟨Point.overOpen U, Point.isOpen_overOpen U, hxU, s.card,
      fun j z ↦ Point.evaluate U (e j).1 z, ?_, ?_⟩
    · intro j
      exact f4_isHolFun_evaluate_aux X hcov ht2 hsc han U (e j).1
    · intro y
      change y.1.underlying ∈ Z ↔ _
      rw [hs y.1.underlying y.2]
      constructor
      · intro hy j
        by_contra hne
        exact hy (e j).1 (e j).2
          ((Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero (e j).1 y y.2).2 hne)
      · intro hy f hf
        let j : Fin s.card := e.symm ⟨f, hf⟩
        intro hmem
        exact (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero f y y.2).1 hmem
          (by simpa [j] using hy j)

theorem f4_isClosedAnalytic_range_aux {Z X : Over (Spec ↧ℂ)}
    (hcov : ∀ z : ComplexPoint X, ∃ r : f4_AdmChart X, z ∈ r.1.dom)
    (ht2 : T2Space (ComplexPoint X)) (hsc : SecondCountableTopology (ComplexPoint X))
    (han : (f4_atlas X hcov).IsAnalytic) [LocallyOfFiniteType X.hom] (i : Z ⟶ X)
    [IsClosedImmersion i.left] :
    an_IsClosedAnalytic (f4_an X hcov ht2 hsc han) (range (Point.map i)) := by
  rw [ComplexPoint.range_map_of_closedImmersion i]
  exact f4_isClosedAnalytic_preimage_aux X hcov ht2 hsc han (range i.left)
    i.left.isClosedEmbedding.isClosed_range

theorem f4_closedImmersion_isHolFun_iff_aux {Z X : Over (Spec ↧ℂ)}
    (hcov : ∀ z : ComplexPoint Z, ∃ r : f4_AdmChart Z, z ∈ r.1.dom)
    (ht2 : T2Space (ComplexPoint Z)) (hsc : SecondCountableTopology (ComplexPoint Z))
    (han : (f4_atlas Z hcov).IsAnalytic)
    (hcov' : ∀ z : ComplexPoint X, ∃ r : f4_AdmChart X, z ∈ r.1.dom)
    (ht2' : T2Space (ComplexPoint X)) (hsc' : SecondCountableTopology (ComplexPoint X))
    (han' : (f4_atlas X hcov').IsAnalytic) [LocallyOfFiniteType X.hom] (i : Z ⟶ X)
    [IsClosedImmersion i.left] {W : Set (ComplexPoint Z)} (hW : IsOpen W) (g : W → ℂ) :
    (f4_an Z hcov ht2 hsc han).IsHolFun g ↔
      ∀ w : W, ∃ V : Set (ComplexPoint X), IsOpen V ∧ Point.map i w ∈ V ∧
        ∃ G : V → ℂ, (f4_an X hcov' ht2' hsc' han').IsHolFun G ∧
          ∀ w' : W, ∀ h : Point.map i w' ∈ V, g w' = G ⟨Point.map i w', h⟩ := by
  constructor
  · intro hg w
    obtain ⟨r, hwr⟩ := hcov w
    obtain ⟨N, hN, hwN, F, hF, hgF⟩ := hg w r hwr
    obtain ⟨U₀, hU₀, hwU₀, -⟩ := exists_isAffineOpen_mem_and_subset
      (X := X.left) (U := ⊤) (Set.mem_univ (Point.map i w).underlying)
    let A : Z.left.Opens := i.left ⁻¹ᵁ U₀
    have hA : IsAffineOpen A := hU₀.preimage i.left
    have hwA : w.1.underlying ∈ A := (Point.mem_overOpen_map_iff i w U₀).mp hwU₀
    obtain ⟨b, hb, hwb⟩ := hA.exists_basicOpen_le
      (V := r.1.U.1) ⟨w.1.underlying, hwr⟩ hwA
    obtain ⟨a, ha⟩ := i.left.app_surjective U₀ hU₀ b
    let U : X.left.Opens := X.left.basicOpen a
    have hU : IsAffineOpen U := hU₀.basicOpen a
    have hpre : i.left ⁻¹ᵁ U ≤ r.1.U.1 := by
      rw [show i.left ⁻¹ᵁ U = Z.left.basicOpen b by
        dsimp [U]
        rw [Scheme.Hom.preimage_basicOpen, ha]]
      exact hb
    have hwU : (Point.map i w).underlying ∈ U := by
      change Point.map i w ∈ Point.overOpen U
      rw [Point.mem_overOpen_map_iff i w U]
      rw [show i.left ⁻¹ᵁ U = Z.left.basicOpen b by
        dsimp [U]
        rw [Scheme.Hom.preimage_basicOpen, ha]]
      exact hwb
    obtain ⟨q₀, hqU, hqpres⟩ := f4_exists_presentation_aux X ⟨U, hU⟩
    let qraw : f4_RawChart X := q₀
    have hqadm : qraw.IsAdmissible := ⟨hqpres.1,
      f4_isEmbedding_of_generates_aux qraw hqpres.1,
      f4_image_eq_of_isPresentation_aux qraw hqpres⟩
    let q : f4_AdmChart X := ⟨qraw, hqadm⟩
    have hqU' : q.1.U.1 = U := congrArg Subtype.val hqU
    subst U
    have hpreq : i.left ⁻¹ᵁ q.1.U.1 ≤ r.1.U.1 := by simpa [hqU'] using hpre
    have hwq : Point.map i w ∈ q.1.dom := by
      change (Point.map i w).underlying ∈ q.1.U.1
      rwa [hqU']
    let t (j : Fin r.1.n) : Γ(Z.left, i.left ⁻¹ᵁ q.1.U.1) :=
      Z.left.presheaf.map (homOfLE hpreq).op (r.1.coord j)
    choose c hc using fun j ↦ i.left.app_surjective q.1.U.1 q.1.U.2 (t j)
    choose p hp using fun j ↦ q.2.1 (c j)
    let H : (Fin q.1.n → ℂ) → (Fin r.1.n → ℂ) :=
      fun z j ↦ MvPolynomial.eval z (p j)
    have hH : AnalyticOnNhd ℂ H univ := fun z _ ↦
      AnalyticAt.pi fun j ↦ AnalyticOnNhd.eval_mvPolynomial (p j) z (mem_univ _)
    let S : Set (Fin r.1.n → ℂ) := {z | AnalyticAt ℂ F z}
    have hS : IsOpen S := isOpen_analyticAt ℂ F
    have hcoord : H (q.1.toFun (Point.map i w)) = r.1.toFun w := by
      funext j
      change MvPolynomial.eval (q.1.toFun (Point.map i w)) (p j) = _
      rw [← hp j (Point.map i w) hwq, Point.evaluate_map, hc j]
      simpa [t, f4_RawChart.toFun] using
        (Point.evaluate_res hpreq (r.1.coord j) w
          ((Point.mem_overOpen_map_iff i w q.1.U.1).mp hwq)).symm
    obtain ⟨O, hO, hpreO⟩ :=
      (AnalytificationAn5_isEmbedding_map_of_immersion i).isInducing.isOpen_iff.mp hN
    let V : Set (ComplexPoint X) := q.1.dom ∩ (O ∩ (H ∘ q.1.toFun) ⁻¹' S)
    have hqcont : ContinuousOn q.1.toFun q.1.dom :=
      continuousOn_iff_continuous_domRestrict.mpr q.2.2.1.continuous
    have hcont : ContinuousOn (H ∘ q.1.toFun) q.1.dom :=
      hH.continuousOn.comp hqcont (fun _ _ ↦ mem_univ _)
    have hV : IsOpen V := by
      simpa [V, inter_assoc, inter_left_comm] using
        hO.inter (hcont.isOpen_inter_preimage (q.1.toChart q.2).isOpen_dom hS)
    have hwV : Point.map i w ∈ V := ⟨hwq, ⟨by
      have : (w : ComplexPoint Z) ∈ Point.map i ⁻¹' O := by rw [hpreO]; exact hwN
      exact this, by
      change H (q.1.toFun (Point.map i w)) ∈ S
      rw [hcoord]
      exact hF⟩⟩
    let G : V → ℂ := fun x ↦ F (H (q.1.toFun x))
    have hG : (f4_an X hcov' ht2' hsc' han').IsHolFun G := by
      rw [an_chart_restrict (f4_an X hcov' ht2' hsc' han') q]
      · let k : (q.1.toChart q.2).modelImage V → ℂ := fun x ↦ F (H x.1.1)
        refine ⟨k, ?_, fun x ↦ rfl⟩
        intro x
        let T : Set (Fin q.1.n → ℂ) := H ⁻¹' S
        have hxT : x.1.1 ∈ T := by
          obtain ⟨y, hy, hey⟩ := x.2
          change H x.1.1 ∈ S
          rw [← hey]
          exact hy.1.2.2
        refine ⟨T, hH.continuous.isOpen_preimage _ hS, hxT, F ∘ H, ?_, fun _ _ ↦ rfl⟩
        intro z hz
        exact (hz : AnalyticAt ℂ F (H z)).comp (hH z (mem_univ _))
      · intro x hx
        exact hx.1
    refine ⟨V, hV, hwV, G, hG, ?_⟩
    intro w' hw'V
    have hw'N : (w' : ComplexPoint Z) ∈ N := by
      rw [← hpreO]
      exact hw'V.2.1
    have hw'r : (w' : ComplexPoint Z) ∈ r.1.dom := by
      apply hpreq
      exact (Point.mem_overOpen_map_iff i w' q.1.U.1).mp hw'V.1
    have hcoord' : H (q.1.toFun (Point.map i w')) = r.1.toFun w' := by
      funext j
      change MvPolynomial.eval (q.1.toFun (Point.map i w')) (p j) = _
      rw [← hp j (Point.map i w') hw'V.1, Point.evaluate_map, hc j]
      simpa [t, f4_RawChart.toFun] using
        (Point.evaluate_res hpreq (r.1.coord j) w'
          ((Point.mem_overOpen_map_iff i w' q.1.U.1).mp hw'V.1)).symm
    exact (hgF w' ⟨hw'N, hw'r⟩).trans (by
      change F (r.1.toFun w') = _
      simp [G, hcoord'])
  · intro H
    intro w r hwr
    obtain ⟨V, hV, hwV, G, hG, hgG⟩ := H w
    have hi := f4_map_isHom_aux hcov ht2 hsc han hcov' ht2' hsc' han' i
    have hpull := hi.2 V hV G hG
    let wV : (Point.map i ⁻¹' V : Set (ComplexPoint Z)) := ⟨w, hwV⟩
    obtain ⟨N, hN, hwN, F, hF, hEq⟩ := hpull wV r hwr
    refine ⟨N ∩ Point.map i ⁻¹' V, hN.inter (hi.1.isOpen_preimage _ hV),
      ⟨hwN, hwV⟩, F, hF, ?_⟩
    intro y hy
    have hyV : Point.map i y ∈ V := hy.1.2
    exact (hgG y hyV).trans (hEq ⟨y, hyV⟩ ⟨hy.1.1, hy.2⟩)

/-! ### Properness -/

theorem f4_projOver_homeomorph_aux (Y : Over (Spec ↧ℂ)) (d : ℕ) :
    ∃ e : ComplexPoint (f4_projOver Y d) ≃ₜ ComplexPoint (f4_projectiveSpace d) × ComplexPoint Y,
      ∀ z, (e z).2 = Point.map (f4_projToBase Y d) z := by
  exact AnalytificationAn5_projOver_homeomorph Y d

theorem f4_isProperMap_projToBase_aux (Y : Over (Spec ↧ℂ)) (d : ℕ) :
    IsProperMap (Point.map (f4_projToBase Y d)) := by
  obtain ⟨e, he⟩ := f4_projOver_homeomorph_aux Y d
  have hfactor : Point.map (f4_projToBase Y d) = Prod.snd ∘ e := by
    funext z
    exact (he z).symm
  rw [hfactor]
  exact isProperMap_snd_of_compactSpace.comp e.isProperMap

theorem f4_isProperMap_of_isProjective_aux {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y)
    [IsProjective f.left] : IsProperMap (Point.map f) := by
  obtain ⟨P⟩ := IsProjective.nonempty_presentation (f := f.left)
  let i : X ⟶ f4_projOver Y P.ambientDimension :=
    Over.homMk P.immersion (by
      change ((P.immersion ≫
        ProjectiveSpace.toBase (Fin (P.ambientDimension + 1)) Y.left) ≫ Y.hom = X.hom)
      rw [P.immersion_toBase, Over.w f])
  letI : IsClosedImmersion i.left := P.isClosedImmersion
  have hi := ComplexPoint.isClosedEmbedding_map_of_closedImmersion i
  have hcomp : Point.map f =
      Point.map (f4_projToBase Y P.ambientDimension) ∘ Point.map i := by
    funext z
    apply Over.OverMorphism.ext
    change z.left ≫ f.left = (z.left ≫ P.immersion) ≫
      ProjectiveSpace.toBase (Fin (P.ambientDimension + 1)) Y.left
    rw [Category.assoc, P.immersion_toBase]
  rw [hcomp]
  exact (f4_isProperMap_projToBase_aux Y P.ambientDimension).comp hi.isProperMap

/-- Chow's lemma is pure scheme theory (Mathlib's scheme library and the upstream `IsProjective`),
with no analytic input: an upstream target for Mathlib. Its proof follows the stages F4g-C1 to
F4g-C4 of `docs/specs/Analytification.md` (`AnalytificationChow3_chow`), with the reducible case
handled by a cover of `X` by dense affine opens (`AnalytificationChow3_exists_dense_affine_cover`)
in place of a disjoint union over the irreducible components. -/
theorem f4_chow_aux {X Y : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsProper f.left] :
    ∃ (X' : Over (Spec ↧ℂ)) (π : X' ⟶ X), LocallyOfFiniteType X'.hom ∧
      IsProjective (π ≫ f).left ∧ Surjective π.left := by
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  obtain ⟨X', π, h₁, h₂, h₃⟩ := AnalytificationChow3_chow X.hom Y.hom f.left (Over.w f)
  exact ⟨Over.mk (π ≫ X.hom), Over.homMk π, h₁, h₂, h₃⟩

theorem f4_map_surjective_aux {X' X : Over (Spec ↧ℂ)} [LocallyOfFiniteType X'.hom]
    (π : X' ⟶ X) [Surjective π.left] : Function.Surjective (Point.map π) := by
  haveI : LocallyOfFiniteType (π.left ≫ X.hom) := by
    rw [Over.w π]
    infer_instance
  letI : LocallyOfFiniteType π.left := locallyOfFiniteType_of_comp π.left X.hom
  intro x
  let P : Over (Spec ↧ℂ) := Over.mk (pullback.snd π.left x.left)
  letI : MorphismProperty.IsStableUnderBaseChangeAlong
      (P := @LocallyOfFiniteType) x.left := {
    of_isPullback pb h :=
      locallyOfFiniteType_isStableUnderBaseChange.of_isPullback pb h }
  haveI : LocallyOfFiniteType (pullback.snd π.left x.left) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  haveI : LocallyOfFiniteType P.hom := by
    change LocallyOfFiniteType (pullback.snd π.left x.left)
    infer_instance
  obtain ⟨y, hy⟩ := Surjective.surj (f := π.left) x.underlying
  have hy' : π.left y = x.left (IsLocalRing.closedPoint ℂ) := hy
  obtain ⟨p, -, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := π.left) (g := x.left) y (IsLocalRing.closedPoint ℂ) hy'
  have hP : (Set.univ : Set P.left).Nonempty := ⟨p, Set.mem_univ _⟩
  haveI : JacobsonSpace P.left := LocallyOfFiniteType.jacobsonSpace P.hom
  obtain ⟨q, -, hq⟩ := (jacobsonSpace_iff_locallyClosed.mp inferInstance)
    Set.univ hP isOpen_univ.isLocallyClosed
  let z : ComplexPoint P := Over.homMk
    ((pointEquivClosedPoint P.hom).symm ⟨q, hq⟩).1
    ((pointEquivClosedPoint P.hom).symm ⟨q, hq⟩).2
  let j : P ⟶ X' := Over.homMk (pullback.fst π.left x.left) (by
    change pullback.fst π.left x.left ≫ X'.hom = pullback.snd π.left x.left
    rw [← Over.w π, ← Category.assoc, pullback.condition, Category.assoc, x.w]
    change pullback.snd π.left x.left ≫ 𝟙 _ = pullback.snd π.left x.left
    simp)
  refine ⟨Point.map j z, ?_⟩
  apply Over.OverMorphism.ext
  change z.left ≫ pullback.fst π.left x.left ≫ π.left = x.left
  rw [pullback.condition, ← Category.assoc]
  have hz := z.w
  change z.left ≫ pullback.snd π.left x.left = 𝟙 _ at hz
  rw [hz, Category.id_comp]

theorem f4_isProperMap_of_isProper_aux {X Y : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (f : X ⟶ Y) [IsProper f.left] : IsProperMap (Point.map f) := by
  obtain ⟨X', π, hX', hproj, hπ⟩ := f4_chow_aux f
  letI : LocallyOfFiniteType X'.hom := hX'
  letI : IsProjective (π ≫ f).left := hproj
  letI : Surjective π.left := hπ
  apply isProperMap_of_comp_of_surj (Point.continuous_map π) (Point.continuous_map f)
    (f_surj := f4_map_surjective_aux π)
  convert f4_isProperMap_of_isProjective_aux (π ≫ f) using 1
  funext x
  exact (Point.map_comp_apply π f x).symm

theorem f4_isProperHom_aux {X Y : Over (Spec ↧ℂ)}
    (hcov : ∀ z : ComplexPoint X, ∃ r : f4_AdmChart X, z ∈ r.1.dom)
    (ht2 : T2Space (ComplexPoint X)) (hsc : SecondCountableTopology (ComplexPoint X))
    (han : (f4_atlas X hcov).IsAnalytic)
    (hcov' : ∀ z : ComplexPoint Y, ∃ r : f4_AdmChart Y, z ∈ r.1.dom)
    (ht2' : T2Space (ComplexPoint Y)) (hsc' : SecondCountableTopology (ComplexPoint Y))
    (han' : (f4_atlas Y hcov').IsAnalytic) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsProper f.left] :
    an_IsProperHom (f4_an X hcov ht2 hsc han) (f4_an Y hcov' ht2' hsc' han') (Point.map f) := by
  exact ⟨f4_isProperMap_of_isProper_aux f,
    f4_map_isHom_aux hcov ht2 hsc han hcov' ht2' hsc' han' f⟩

/-! ### Comparison with the manifold structure of smooth schemes -/

theorem AnalytificationAn3.manifoldToF4_isHom (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (hcov : ∀ z : ComplexPoint X, ∃ r : f4_AdmChart X, z ∈ r.1.dom)
    (ht2 : T2Space (ComplexPoint X)) (hsc : SecondCountableTopology (ComplexPoint X))
    (han : (f4_atlas X hcov).IsAnalytic) :
    an_IsHom (an_manifoldSpace (Fin d → ℂ) (ComplexPoint X))
      (f4_an X hcov ht2 hsc han) id := by
  rw [an_isHom_iff_chart]
  refine ⟨continuous_id, ?_⟩
  intro q z x hx
  let c := localChart X d z
  let e := an_coord (Fin d → ℂ)
  let ψ : (Fin (Module.finrank ℂ (Fin d → ℂ)) → ℂ) → ComplexPoint X :=
    fun w ↦ c.symm (e.symm w)
  let W : Set (Fin (Module.finrank ℂ (Fin d → ℂ)) → ℂ) :=
    e '' c.target ∩ ψ ⁻¹' q.1.dom
  have hψ : ContinuousOn ψ (e '' c.target) := by
    apply c.continuousOn_symm.comp e.symm.continuous.continuousOn
    rintro _ ⟨v, hv, rfl⟩
    simpa [e]
  have hW : IsOpen W := hψ.isOpen_inter_preimage
    (e.toHomeomorph.isOpenMap _ c.open_target) (Point.isOpen_overOpen q.1.U.1)
  have hxq : x ∈ q.1.dom := hx.1
  have hxW : e (c x) ∈ W := ⟨⟨c x, c.map_source hx.2, rfl⟩, by
    simpa [ψ, e, c, c.left_inv hx.2] using hxq⟩
  let G : (Fin (Module.finrank ℂ (Fin d → ℂ)) → ℂ) → (Fin q.1.n → ℂ) := fun w i ↦
    Point.evaluate q.1.U.1 (q.1.coord i) (ψ w)
  have hG : AnalyticOnNhd ℂ G W := by
    rintro w ⟨⟨v, hv, rfl⟩, hw⟩
    change AnalyticAt ℂ
      (fun w i ↦ Point.evaluate q.1.U.1 (q.1.coord i) (c.symm (e.symm w))) (e v)
    apply AnalyticAt.pi
    intro i
    apply (analyticAt_localChart_symm_evaluate X d z hv q.1.U.1 (q.1.coord i) (by
      simpa [e, ψ] using hw)).comp_of_eq (e.symm.toContinuousLinearMap.analyticAt (e v))
    simp [e]
  refine ⟨W, hW, hxW, G, hG, ?_⟩
  intro y hy hyW
  change q.1.toFun y = G (e (c y))
  funext i
  change Point.evaluate q.1.U.1 (q.1.coord i) y =
    Point.evaluate q.1.U.1 (q.1.coord i) (ψ (e (c y)))
  simp [ψ, e, c, c.left_inv hy.2]

theorem AnalytificationAn3.f4ToManifold_isHom (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (hcov : ∀ z : ComplexPoint X, ∃ r : f4_AdmChart X, z ∈ r.1.dom)
    (ht2 : T2Space (ComplexPoint X)) (hsc : SecondCountableTopology (ComplexPoint X))
    (han : (f4_atlas X hcov).IsAnalytic) :
    an_IsHom (f4_an X hcov ht2 hsc han)
      (an_manifoldSpace (Fin d → ℂ) (ComplexPoint X)) id := by
  rw [an_isHom_iff_chart]
  refine ⟨continuous_id, ?_⟩
  intro z r x hx
  let D := localEtaleCoordinates X d z
  have hxD : x ∈ Point.overOpen D.ambientCoordinateOpen := by
    have hm := mem_coordinateNeighborhood_of_mem_localChart_source X d z x hx.1
    simpa only [D, LocalEtaleCoordinates.ambientCoordinateOpen,
      Scheme.Opens.ι_image_top] using hm
  obtain ⟨a, ha, hxa⟩ := r.1.U.2.exists_basicOpen_le
    (V := D.ambientCoordinateOpen) ⟨x.underlying, hxD⟩ hx.2
  let t (i : Fin d) : Γ(X.left, X.left.basicOpen a) :=
    X.left.presheaf.map (homOfLE ha).op (D.ambientCoordinateSection i)
  choose k b hb using fun i ↦
    Point.exists_evaluate_basicOpen_eq_div (X := X) r.1.U.2 a (t i)
  choose pb hpb using fun i ↦ r.2.1 (b i)
  obtain ⟨pa, hpa⟩ := r.2.1 a
  let H : (Fin r.1.n → ℂ) → (Fin d → ℂ) := fun w i ↦
    MvPolynomial.eval w (pb i) / MvPolynomial.eval w pa ^ k i
  let e := an_coord (Fin d → ℂ)
  let G := e ∘ H
  let W : Set (Fin r.1.n → ℂ) := {w | MvPolynomial.eval w pa ≠ 0}
  have hpa_cont : Continuous (fun w : Fin r.1.n → ℂ ↦ MvPolynomial.eval w pa) :=
    continuous_iff_continuousAt.2 fun w ↦
      (AnalyticOnNhd.eval_mvPolynomial pa w (mem_univ _)).continuousAt
  have hW : IsOpen W := isOpen_ne_fun hpa_cont continuous_const
  have hxW : r.1.toFun x ∈ W := by
    change MvPolynomial.eval (r.1.toFun x) pa ≠ 0
    rw [← hpa x hx.2]
    exact (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero a x hx.2).mp hxa
  have hH : AnalyticOnNhd ℂ H W := fun w hw ↦ AnalyticAt.pi fun i ↦
    (AnalyticOnNhd.eval_mvPolynomial (pb i) w (mem_univ _)).div
      ((AnalyticOnNhd.eval_mvPolynomial pa w (mem_univ _)).pow (k i)) (pow_ne_zero _ hw)
  have hG : AnalyticOnNhd ℂ G W := fun w hw ↦
    e.toContinuousLinearMap.analyticAt (H w) |>.comp (hH w hw)
  refine ⟨W, hW, hxW, G, hG, ?_⟩
  intro y hy hyW
  have hya : y ∈ Point.overOpen (X.left.basicOpen a) :=
    (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero a y hy.2).mpr (by
      change MvPolynomial.eval (r.1.toFun y) pa ≠ 0 at hyW
      rw [hpa y hy.2]
      exact hyW)
  change e (localChart X d z y) = e (H (r.1.toFun y))
  congr 1
  funext i
  rw [localChart_apply_component_eq_evaluate X d z y hy.1 i]
  rw [Point.evaluate_res ha (D.ambientCoordinateSection i) y hya]
  rw [hb i y hya, hpb i y hy.2, hpa y hy.2]

theorem AnalytificationAn3.isHom_comp {A B C : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (S : an_ReducedSpace A) (T : an_ReducedSpace B) (U : an_ReducedSpace C)
    {f : A → B} {g : B → C} (hf : an_IsHom S T f) (hg : an_IsHom T U g) :
    an_IsHom S U (g ∘ f) := by
  refine ⟨hg.1.comp hf.1, ?_⟩
  intro V hV q hq
  have hgq := hg.2 V hV q hq
  have hfq := hf.2 (g ⁻¹' V) (hV.preimage hg.1) _ hgq
  convert hfq using 1 <;> rfl

theorem f4_isHolFun_iff_contMDiffOn_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (hcov : ∀ z : ComplexPoint X, ∃ r : f4_AdmChart X, z ∈ r.1.dom)
    (ht2 : T2Space (ComplexPoint X)) (hsc : SecondCountableTopology (ComplexPoint X))
    (han : (f4_atlas X hcov).IsAnalytic) (g : ComplexPoint X → ℂ) {U : Set (ComplexPoint X)}
    (hU : IsOpen U) :
    (f4_an X hcov ht2 hsc han).IsHolFun (fun x : U ↦ g x) ↔
      ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω g U := by
  let S := f4_an X hcov ht2 hsc han
  let M := an_manifoldSpace (Fin d → ℂ) (ComplexPoint X)
  have hSM := AnalytificationAn3.f4ToManifold_isHom X d hcov ht2 hsc han
  have hMS := AnalytificationAn3.manifoldToF4_isHom X d hcov ht2 hsc han
  calc
    S.IsHolFun (fun x : U ↦ g x) ↔ M.IsHolFun (fun x : U ↦ g x) := by
      constructor
      · intro hg
        simpa [S, M] using hMS.2 U hU (fun x : U ↦ g x) hg
      · intro hg
        simpa [S, M] using hSM.2 U hU (fun x : U ↦ g x) hg
    _ ↔ ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω g U :=
      an_manifold_isHolFun_iff g hU

theorem f4_isHom_iff_contMDiff_aux {X Y : Over (Spec ↧ℂ)} {d e : ℕ}
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
   
    (hcov : ∀ z : ComplexPoint X, ∃ r : f4_AdmChart X, z ∈ r.1.dom)
    (ht2 : T2Space (ComplexPoint X)) (hsc : SecondCountableTopology (ComplexPoint X))
    (han : (f4_atlas X hcov).IsAnalytic)
    (hcov' : ∀ z : ComplexPoint Y, ∃ r : f4_AdmChart Y, z ∈ r.1.dom)
    (ht2' : T2Space (ComplexPoint Y)) (hsc' : SecondCountableTopology (ComplexPoint Y))
    (han' : (f4_atlas Y hcov').IsAnalytic) (F : ComplexPoint X → ComplexPoint Y) :
    an_IsHom (f4_an X hcov ht2 hsc han) (f4_an Y hcov' ht2' hsc' han') F ↔
      ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) ω F := by
  let SX := f4_an X hcov ht2 hsc han
  let SY := f4_an Y hcov' ht2' hsc' han'
  let MX := an_manifoldSpace (Fin d → ℂ) (ComplexPoint X)
  let MY := an_manifoldSpace (Fin e → ℂ) (ComplexPoint Y)
  have hXS := AnalytificationAn3.manifoldToF4_isHom X d hcov ht2 hsc han
  have hSX := AnalytificationAn3.f4ToManifold_isHom X d hcov ht2 hsc han
  have hYS := AnalytificationAn3.manifoldToF4_isHom Y e hcov' ht2' hsc' han'
  have hSY := AnalytificationAn3.f4ToManifold_isHom Y e hcov' ht2' hsc' han'
  rw [← an_manifold_isHom_iff]
  constructor
  · intro hF
    have h := AnalytificationAn3.isHom_comp MX SX SY hXS hF
    have h' := AnalytificationAn3.isHom_comp MX SY MY h hSY
    simpa [Function.comp_def] using h'
  · intro hF
    have h := AnalytificationAn3.isHom_comp SX MX MY hSX hF
    have h' := AnalytificationAn3.isHom_comp SX MY SY h hYS
    simpa [Function.comp_def] using h'

/-! ### Instances -/

theorem f4_affineSpace_isHom_aux (n : ℕ)
    (hcov : ∀ z : ComplexPoint (f4_affineSpace n),
      ∃ r : f4_AdmChart (f4_affineSpace n), z ∈ r.1.dom)
    (ht2 : T2Space (ComplexPoint (f4_affineSpace n)))
    (hsc : SecondCountableTopology (ComplexPoint (f4_affineSpace n)))
    (han : (f4_atlas (f4_affineSpace n) hcov).IsAnalytic) :
    an_IsHom (f4_an (f4_affineSpace n) hcov ht2 hsc han) (an_euclidSpace n)
        (affineSpaceEquiv (Fin n)) ∧
      an_IsHom (an_euclidSpace n) (f4_an (f4_affineSpace n) hcov ht2 hsc han)
        (affineSpaceEquiv (Fin n)).symm := by
  constructor
  · rw [an_isHom_iff_chart]
    refine ⟨(affineSpaceHomeomorph (Fin n)).continuous, ?_⟩
    intro _ r x hx
    let s (i : Fin n) : Γ((f4_affineSpace n).left, r.1.U.1) :=
      (f4_affineSpace n).left.presheaf.map (homOfLE le_top).op
        (AffineSpace.coord (Spec ↧ℂ) i)
    choose p hp using fun i ↦ r.2.1 (s i)
    let G : (Fin r.1.n → ℂ) → (Fin n → ℂ) := fun w i ↦ MvPolynomial.eval w (p i)
    refine ⟨univ, isOpen_univ, mem_univ _, G,
      fun w _ ↦ AnalyticAt.pi fun i ↦
        AnalyticOnNhd.eval_mvPolynomial (p i) w (mem_univ _), ?_⟩
    intro y hy _
    funext i
    change affineSpaceEquiv (Fin n) y i = G (r.1.toFun y) i
    rw [show affineSpaceEquiv (Fin n) y i =
      Point.evaluate ⊤ (AffineSpace.coord (Spec ↧ℂ) i) y from
        (evaluate_top_eq_appTop _ _).symm]
    rw [Point.evaluate_res le_top (AffineSpace.coord (Spec ↧ℂ) i) y hy.2]
    exact hp i y hy.2
  · rw [an_isHom_iff_chart]
    refine ⟨(affineSpaceHomeomorph (Fin n)).symm.continuous, ?_⟩
    intro q _ x hx
    let z : ComplexPoint (f4_affineSpace n) := (affineSpaceEquiv (Fin n)).symm x
    obtain ⟨a, ha, hza⟩ := (isAffineOpen_top (complexAffineSpace (Fin n))).exists_basicOpen_le
      (V := q.1.U.1) ⟨z.underlying, hx.1⟩ trivial
    let t (i : Fin q.1.n) : Γ((f4_affineSpace n).left,
        (f4_affineSpace n).left.basicOpen a) :=
      (f4_affineSpace n).left.presheaf.map (homOfLE ha).op (q.1.coord i)
    choose k b hb using fun i ↦ Point.exists_evaluate_basicOpen_eq_div
      (X := f4_affineSpace n) (isAffineOpen_top _) a (t i)
    let pb (i : Fin q.1.n) := affineGlobalPolynomial (b i)
    let pa := affineGlobalPolynomial a
    let G : (Fin n → ℂ) → (Fin q.1.n → ℂ) := fun w i ↦
      MvPolynomial.eval w (pb i) / MvPolynomial.eval w pa ^ k i
    let W : Set (Fin n → ℂ) := {w | MvPolynomial.eval w pa ≠ 0}
    have hW : IsOpen W := isOpen_ne_fun
      (continuous_iff_continuousAt.2 fun w ↦
        (AnalyticOnNhd.eval_mvPolynomial pa w (mem_univ _)).continuousAt) continuous_const
    have hxW : x ∈ W := by
      change MvPolynomial.eval x pa ≠ 0
      rw [← evaluate_affineSpaceEquiv_symm_top a x]
      have hzTop : z ∈ Point.overOpen (⊤ : (f4_affineSpace n).left.Opens) := trivial
      set_option maxHeartbeats 400000 in
        exact (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero (X := f4_affineSpace n)
          a z hzTop).mp hza
    have hG : AnalyticOnNhd ℂ G W := fun w hw ↦ AnalyticAt.pi fun i ↦
      (AnalyticOnNhd.eval_mvPolynomial (pb i) w (mem_univ _)).div
        ((AnalyticOnNhd.eval_mvPolynomial pa w (mem_univ _)).pow (k i)) (pow_ne_zero _ hw)
    refine ⟨W, hW, hxW, G, hG, ?_⟩
    intro y hy hyW
    let zy : ComplexPoint (f4_affineSpace n) := (affineSpaceEquiv (Fin n)).symm y
    have hzya : zy ∈ Point.overOpen ((f4_affineSpace n).left.basicOpen a) :=
      (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero a zy
        (show zy ∈ Point.overOpen (⊤ : (f4_affineSpace n).left.Opens) from trivial)).mpr (by
        change MvPolynomial.eval y pa ≠ 0 at hyW
        rw [evaluate_affineSpaceEquiv_symm_top a y]
        exact hyW)
    funext i
    change Point.evaluate q.1.U.1 (q.1.coord i) zy = G y i
    rw [Point.evaluate_res ha (q.1.coord i) zy hzya]
    rw [hb i zy hzya, evaluate_affineSpaceEquiv_symm_top (b i) y,
      evaluate_affineSpaceEquiv_symm_top a y]

theorem f4_node_isHom_aux
    (hcov : ∀ z : ComplexPoint f4_node, ∃ r : f4_AdmChart f4_node, z ∈ r.1.dom)
    (ht2 : T2Space (ComplexPoint f4_node))
    (hsc : SecondCountableTopology (ComplexPoint f4_node))
    (han : (f4_atlas f4_node hcov).IsAnalytic) :
    an_IsHom (f4_an f4_node hcov ht2 hsc han) an_nodeSpace f4_nodeEquiv ∧
      an_IsHom an_nodeSpace (f4_an f4_node hcov ht2 hsc han) f4_nodeEquiv.symm := by
  have hcoord (i : Fin 2) (z : ComplexPoint f4_node) :
      (f4_nodeEquiv z : Fin 2 → ℂ) i = Point.evaluate ⊤
        ((Scheme.ΓSpecIso ↧f4_nodeRing).inv
          (Ideal.Quotient.mk _ (MvPolynomial.X i))) z := by
    exact affineSpecEquiv_apply f4_nodeRing z _
  have hforward : Continuous f4_nodeEquiv := by
    rw [continuous_induced_rng]
    exact continuous_pi fun i ↦ by
      convert continuous_evaluate_top (X := f4_node)
        ((Scheme.ΓSpecIso ↧f4_nodeRing).inv
          (Ideal.Quotient.mk _ (MvPolynomial.X i))) using 1
      funext z
      exact hcoord i z
  have halg : Continuous f4_nodeAlgHom := by
    rw [continuous_induced_rng]
    apply continuous_pi
    intro r
    induction r using Quotient.inductionOn' with
    | _ p =>
      change Continuous fun w : an_node ↦ MvPolynomial.eval (w : Fin 2 → ℂ) p
      exact continuous_iff_continuousAt.2 fun w ↦
        (AnalyticOnNhd.eval_mvPolynomial p w (mem_univ _)).continuousAt.comp
          continuousAt_subtype_val
  have hinverse : Continuous f4_nodeEquiv.symm := by
    exact (affineSpecHomeomorph f4_nodeRing).symm.continuous.comp halg
  constructor
  · rw [an_isHom_iff_chart]
    refine ⟨hforward, ?_⟩
    intro _ r x hx
    let s (i : Fin 2) : Γ(f4_node.left, r.1.U.1) :=
      f4_node.left.presheaf.map (homOfLE le_top).op
        ((Scheme.ΓSpecIso ↧f4_nodeRing).inv
          (Ideal.Quotient.mk _ (MvPolynomial.X i)))
    choose p hp using fun i ↦ r.2.1 (s i)
    let G : (Fin r.1.n → ℂ) → (Fin 2 → ℂ) := fun w i ↦ MvPolynomial.eval w (p i)
    refine ⟨univ, isOpen_univ, mem_univ _, G,
      fun w _ ↦ AnalyticAt.pi fun i ↦
        AnalyticOnNhd.eval_mvPolynomial (p i) w (mem_univ _), ?_⟩
    intro y hy _
    funext i
    change (f4_nodeEquiv y : Fin 2 → ℂ) i = G (r.1.toFun y) i
    rw [hcoord i y]
    rw [Point.evaluate_res le_top _ y hy.2]
    exact hp i y hy.2
  · rw [an_isHom_iff_chart]
    refine ⟨hinverse, ?_⟩
    intro q _ x hx
    let z : ComplexPoint f4_node := f4_nodeEquiv.symm x
    letI : IsAffine f4_node.left := isAffine_Spec _
    obtain ⟨a, ha, hza⟩ := (isAffineOpen_top (Spec ↧f4_nodeRing)).exists_basicOpen_le
      (V := q.1.U.1) ⟨z.underlying, hx.1⟩ trivial
    let t (i : Fin q.1.n) : Γ(f4_node.left, f4_node.left.basicOpen a) :=
      f4_node.left.presheaf.map (homOfLE ha).op (q.1.coord i)
    choose k b hb using fun i ↦ Point.exists_evaluate_basicOpen_eq_div
      (X := f4_node) (isAffineOpen_top _) a (t i)
    choose pb hpb using fun i ↦ Ideal.Quotient.mk_surjective
      ((Scheme.ΓSpecIso ↧f4_nodeRing).hom (b i))
    obtain ⟨pa, hpa⟩ := Ideal.Quotient.mk_surjective
      ((Scheme.ΓSpecIso ↧f4_nodeRing).hom a)
    let G : (Fin 2 → ℂ) → (Fin q.1.n → ℂ) := fun w i ↦
      MvPolynomial.eval w (pb i) / MvPolynomial.eval w pa ^ k i
    let W : Set (Fin 2 → ℂ) := {w | MvPolynomial.eval w pa ≠ 0}
    have hW : IsOpen W := isOpen_ne_fun
      (continuous_iff_continuousAt.2 fun w ↦
        (AnalyticOnNhd.eval_mvPolynomial pa w (mem_univ _)).continuousAt) continuous_const
    have heval (s : Γ(f4_node.left, ⊤)) (p : MvPolynomial (Fin 2) ℂ)
        (hp : Ideal.Quotient.mk _ p = (Scheme.ΓSpecIso ↧f4_nodeRing).hom s)
        (w : an_node) : Point.evaluate ⊤ s (f4_nodeEquiv.symm w) = MvPolynomial.eval w p := by
      change Point.evaluate ⊤ s ((affineSpecEquiv f4_nodeRing).symm (f4_nodeAlgHom w)) = _
      rw [evaluate_affineSpecEquiv_symm_top]
      change f4_nodeAlgHom w ((Scheme.ΓSpecIso ↧f4_nodeRing).hom s) = _
      rw [← hp]
      simp [f4_nodeAlgHom]
    have hxW : (x : Fin 2 → ℂ) ∈ W := by
      change MvPolynomial.eval (x : Fin 2 → ℂ) pa ≠ 0
      rw [← heval a pa hpa x]
      have hzTop : z ∈ Point.overOpen (⊤ : f4_node.left.Opens) := trivial
      exact (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero (X := f4_node)
        a z hzTop).mp hza
    have hG : AnalyticOnNhd ℂ G W := fun w hw ↦ AnalyticAt.pi fun i ↦
      (AnalyticOnNhd.eval_mvPolynomial (pb i) w (mem_univ _)).div
        ((AnalyticOnNhd.eval_mvPolynomial pa w (mem_univ _)).pow (k i)) (pow_ne_zero _ hw)
    refine ⟨W, hW, hxW, G, hG, ?_⟩
    intro y hy hyW
    let zy : ComplexPoint f4_node := f4_nodeEquiv.symm y
    have hzya : zy ∈ Point.overOpen (f4_node.left.basicOpen a) :=
      (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero a zy
        (show zy ∈ Point.overOpen (⊤ : f4_node.left.Opens) from trivial)).mpr (by
        change MvPolynomial.eval (y : Fin 2 → ℂ) pa ≠ 0 at hyW
        rw [heval a pa hpa y]
        exact hyW)
    funext i
    change Point.evaluate q.1.U.1 (q.1.coord i) zy = G y i
    rw [Point.evaluate_res ha (q.1.coord i) zy hzya]
    rw [hb i zy hzya, heval (b i) (pb i) (hpb i) y, heval a pa hpa y]

end HodgeLean.Foundations.Analytic
