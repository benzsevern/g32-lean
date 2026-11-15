import HodgeLean.Adapters.NormalConeB4aGysinSectionEvaluation
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.PointwiseDimension
import HodgeLean.Foundations.Port.AlgebraicGeometry.Smooth.RegularLocal
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.RingTheory.Ideal.Cotangent

/-! # Reformulated bridge of A3-B4a: analytic and algebraic differentials

On a complex scheme smooth of relative dimension `d`, regular functions vanishing at a complex
point whose analytic Jacobian in a holomorphic chart is invertible generate the maximal ideal of
the local ring. Elements of the square of the maximal ideal have zero analytic derivative, and the
cotangent space of the regular local ring has dimension `d`. Source: Serre, *Géométrie algébrique
et géométrie analytique*, §2 (comparison of local rings); Matsumura, *Commutative Ring Theory*,
Theorem 14.2 and §14. -/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry IsLocalRing Point

/-- The underlying scheme point of a complex point of a complex scheme locally of finite type is
closed. -/
theorem a3b4g_isClosed_underlying (X : Over (Spec (CommRingCat.of ℂ)))
    [LocallyOfFiniteType X.hom] (x : ComplexPoint X) : IsClosed {x.underlying} :=
  ((pointEquivClosedPoint X.hom) ⟨x.left, Over.w x⟩).2

/-- At a closed point of a complex scheme smooth of relative dimension `d`, the local ring has
Krull dimension `d`. Source: Hartshorne, *Algebraic Geometry*, Theorem III.10.2. -/
theorem a3b4g_ringKrullDim_stalk_of_smooth (X : Over (Spec (CommRingCat.of ℂ))) {d : ℕ}
    [SmoothOfRelativeDimension d X.hom] (x : X.left) (hx : IsClosed {x}) :
    ringKrullDim (X.left.presheaf.stalk x) = d := by
  rw [ringKrullDim_stalk_eq_coheight]
  obtain ⟨U, hU, hxU, hsmooth⟩ :=
    SmoothOfRelativeDimension.exists_affine_isStandardSmoothOfRelativeDimension (d := d) X.hom x
  let y : U.toScheme := ⟨x, hxU⟩
  let P : Ideal Γ(X.left, U) := (hU.primeIdealOf y).asIdeal
  haveI : P.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed y hx
  have hP : P.height = d :=
    (algebraMap_isStandardSmoothOfRelativeDimension (d := d) (Over.mk X.hom) hsmooth
      ).height_eq_of_isMaximal P
  have hcoheight : Order.coheight x = d := by
    calc
      Order.coheight x = Order.coheight y := coheight_eq_of_isOpenImmersion (x := y) U.ι
      _ = P.height := (hU.primeIdealOf_height_eq_coheight y).symm
      _ = d := hP
  rw [hcoheight]
  rfl

section Evaluation

variable {X : Over (Spec (CommRingCat.of ℂ))}

theorem a3b4g_evaluate_add (U : X.left.Opens) (s t : Γ(X.left, U)) (z : ComplexPoint X) :
    evaluate U (s + t) z = evaluate U s z + evaluate U t z := by
  unfold evaluate
  split_ifs <;> simp

theorem a3b4g_evaluate_sub (U : X.left.Opens) (s t : Γ(X.left, U)) (z : ComplexPoint X) :
    evaluate U (s - t) z = evaluate U s z - evaluate U t z := by
  unfold evaluate
  split_ifs <;> simp

theorem a3b4g_evaluate_mul (U : X.left.Opens) (s t : Γ(X.left, U)) (z : ComplexPoint X) :
    evaluate U (s * t) z = evaluate U s z * evaluate U t z := by
  unfold evaluate
  split_ifs <;> simp

theorem a3b4g_evaluate_sum (U : X.left.Opens) {ι : Type*} (T : Finset ι) (s : ι → Γ(X.left, U))
    (z : ComplexPoint X) : evaluate U (∑ k ∈ T, s k) z = ∑ k ∈ T, evaluate U (s k) z := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    unfold evaluate
    split_ifs <;> simp
  | insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, a3b4g_evaluate_add, ih]

/-- The value at a point of the germ of a section is its evaluation. -/
theorem a3b4g_stalkHom_germ (U : X.left.Opens) (s : Γ(X.left, U)) (z : ComplexPoint X)
    (hz : z.underlying ∈ U) :
    z.stalkHom.hom (X.left.presheaf.germ U z.underlying hz s) = evaluate U s z := by
  rw [evaluate, dif_pos hz]

/-- Elements of the maximal ideal of the local ring at a complex point have value zero. -/
theorem a3b4g_stalkHom_eq_zero_of_mem (z : ComplexPoint X)
    (m : X.left.presheaf.stalk z.underlying)
    (hm : m ∈ maximalIdeal (X.left.presheaf.stalk z.underlying)) : z.stalkHom.hom m = 0 := by
  by_contra h
  exact hm ((isUnit_map_iff z.stalkHom.hom m).mp (Ne.isUnit h))

/-- Elements of value zero lie in the maximal ideal. -/
theorem a3b4g_mem_of_stalkHom_eq_zero (z : ComplexPoint X)
    (m : X.left.presheaf.stalk z.underlying) (hm : z.stalkHom.hom m = 0) :
    m ∈ maximalIdeal (X.left.presheaf.stalk z.underlying) := by
  intro hu
  have := hu.map z.stalkHom.hom
  rw [hm] at this
  exact not_isUnit_zero this

end Evaluation

section Chart

variable (X : Over (Spec (CommRingCat.of ℂ))) {d : ℕ} [SmoothOfRelativeDimension d X.hom]

open Topology Filter

/-- Sections with equal germs have evaluations agreeing near the point along an inverse chart. -/
theorem a3b4g_evaluate_eventuallyEq_of_germ_eq (j x : ComplexPoint X)
    (hx : x ∈ (chartAt (Fin d → ℂ) j).source) {W W' : X.left.Opens}
    (s : Γ(X.left, W)) (s' : Γ(X.left, W')) (hW : x.underlying ∈ W) (hW' : x.underlying ∈ W')
    (h : X.left.presheaf.germ W x.underlying hW s = X.left.presheaf.germ W' x.underlying hW' s') :
    (fun a => evaluate W s ((chartAt (Fin d → ℂ) j).symm a)) =ᶠ[𝓝 ((chartAt (Fin d → ℂ) j) x)]
      (fun a => evaluate W' s' ((chartAt (Fin d → ℂ) j).symm a)) := by
  obtain ⟨V, hxV, iU, iV, heq⟩ := TopCat.Presheaf.germ_eq X.left.presheaf x.underlying hW hW' s s' h
  let e := chartAt (Fin d → ℂ) j
  have hcont : ContinuousAt e.symm (e x) := e.continuousAt_symm (e.map_source hx)
  have hopen : IsOpen (overOpen (X := X) V) := isOpen_overOpen V
  have hxV' : e.symm (e x) ∈ overOpen (X := X) V := by
    rw [e.left_inv hx]
    exact hxV
  filter_upwards [hcont.preimage_mem_nhds (hopen.mem_nhds hxV')] with a ha
  rw [evaluate_res (X := X) iU.le s _ ha, evaluate_res (X := X) iV.le s' _ ha]
  have h1 : homOfLE iU.le = iU := Subsingleton.elim _ _
  have h2 : homOfLE iV.le = iV := Subsingleton.elim _ _
  rw [h1, h2, heq]

/-- A section whose germ lies in the square of the maximal ideal has zero analytic derivative
along an inverse chart. -/
theorem a3b4g_hasFDerivAt_zero_of_mem_sq (j x : ComplexPoint X)
    (hx : x ∈ (chartAt (Fin d → ℂ) j).source) (h : X.left.presheaf.stalk x.underlying)
    (hh : h ∈ maximalIdeal (X.left.presheaf.stalk x.underlying) ^ 2) :
    ∀ (W : X.left.Opens) (hW : x.underlying ∈ W) (s : Γ(X.left, W)),
      X.left.presheaf.germ W x.underlying hW s = h →
      HasFDerivAt (fun a => evaluate W s ((chartAt (Fin d → ℂ) j).symm a))
        (0 : (Fin d → ℂ) →L[ℂ] ℂ) ((chartAt (Fin d → ℂ) j) x) := by
  let e := chartAt (Fin d → ℂ) j
  have ha₀ : e x ∈ e.target := e.map_source hx
  have hsymm : e.symm (e x) = x := e.left_inv hx
  have hanalytic : ∀ (W : X.left.Opens) (hW : x.underlying ∈ W) (s : Γ(X.left, W)),
      AnalyticAt ℂ (fun a => evaluate W s (e.symm a)) (e x) := fun W hW s =>
    ComplexPoint.analyticAt_localChart_symm_evaluate X d j ha₀ W s (by
      change e.symm (e x) ∈ _
      rw [hsymm]
      exact hW)
  rw [pow_two] at hh
  refine Submodule.mul_induction_on (C := fun h => ∀ (W : X.left.Opens)
    (hW : x.underlying ∈ W) (s : Γ(X.left, W)),
      X.left.presheaf.germ W x.underlying hW s = h →
      HasFDerivAt (fun a => evaluate W s ((chartAt (Fin d → ℂ) j).symm a))
        (0 : (Fin d → ℂ) →L[ℂ] ℂ) ((chartAt (Fin d → ℂ) j) x)) hh ?_ ?_
  · intro m hm n hn W hW s hs
    obtain ⟨Wm, hxm, sm, hsm⟩ := X.left.presheaf.exists_germ_eq m
    obtain ⟨Wn, hxn, sn, hsn⟩ := X.left.presheaf.exists_germ_eq n
    let W₀ := Wm ⊓ Wn
    have hx₀ : x.underlying ∈ W₀ := ⟨hxm, hxn⟩
    let rm := X.left.presheaf.map (homOfLE (inf_le_left : W₀ ≤ Wm)).op sm
    let rn := X.left.presheaf.map (homOfLE (inf_le_right : W₀ ≤ Wn)).op sn
    have hgm : X.left.presheaf.germ W₀ x.underlying hx₀ rm = m := by
      rw [TopCat.Presheaf.germ_res_apply, hsm]
    have hgn : X.left.presheaf.germ W₀ x.underlying hx₀ rn = n := by
      rw [TopCat.Presheaf.germ_res_apply, hsn]
    have hgerm : X.left.presheaf.germ W₀ x.underlying hx₀ (rm * rn) =
        X.left.presheaf.germ W x.underlying hW s := by
      rw [map_mul, hgm, hgn, hs]
    have hev := a3b4g_evaluate_eventuallyEq_of_germ_eq X j x hx (rm * rn) s hx₀ hW hgerm
    refine HasFDerivAt.congr_of_eventuallyEq ?_ hev.symm
    have hm0 : evaluate W₀ rm (e.symm (e x)) = 0 := by
      rw [hsymm, ← a3b4g_stalkHom_germ W₀ rm x hx₀, hgm]
      exact a3b4g_stalkHom_eq_zero_of_mem x m hm
    have hn0 : evaluate W₀ rn (e.symm (e x)) = 0 := by
      rw [hsymm, ← a3b4g_stalkHom_germ W₀ rn x hx₀, hgn]
      exact a3b4g_stalkHom_eq_zero_of_mem x n hn
    have hd := ((hanalytic W₀ hx₀ rm).differentiableAt.hasFDerivAt).mul
      ((hanalytic W₀ hx₀ rn).differentiableAt.hasFDerivAt)
    simp only [hm0, hn0, zero_smul, add_zero] at hd
    have hfun : (fun a => evaluate W₀ (rm * rn) (e.symm a)) =
        (fun a => evaluate W₀ rm (e.symm a) * evaluate W₀ rn (e.symm a)) := by
      funext a
      exact a3b4g_evaluate_mul W₀ rm rn _
    rw [hfun]
    exact hd
  · intro h₁ h₂ ih₁ ih₂ W hW s hs
    obtain ⟨W₁, hx₁, s₁, hs₁⟩ := X.left.presheaf.exists_germ_eq h₁
    obtain ⟨W₂, hx₂, s₂, hs₂⟩ := X.left.presheaf.exists_germ_eq h₂
    let W₀ := W₁ ⊓ W₂
    have hx₀ : x.underlying ∈ W₀ := ⟨hx₁, hx₂⟩
    let r₁ := X.left.presheaf.map (homOfLE (inf_le_left : W₀ ≤ W₁)).op s₁
    let r₂ := X.left.presheaf.map (homOfLE (inf_le_right : W₀ ≤ W₂)).op s₂
    have hg₁ : X.left.presheaf.germ W₀ x.underlying hx₀ r₁ = h₁ := by
      rw [TopCat.Presheaf.germ_res_apply, hs₁]
    have hg₂ : X.left.presheaf.germ W₀ x.underlying hx₀ r₂ = h₂ := by
      rw [TopCat.Presheaf.germ_res_apply, hs₂]
    have hgerm : X.left.presheaf.germ W₀ x.underlying hx₀ (r₁ + r₂) =
        X.left.presheaf.germ W x.underlying hW s := by
      rw [map_add, hg₁, hg₂, hs]
    have hev := a3b4g_evaluate_eventuallyEq_of_germ_eq X j x hx (r₁ + r₂) s hx₀ hW hgerm
    refine HasFDerivAt.congr_of_eventuallyEq ?_ hev.symm
    have hd := (ih₁ W₀ hx₀ r₁ hg₁).add (ih₂ W₀ hx₀ r₂ hg₂)
    rw [add_zero] at hd
    have hfun : (fun a => evaluate W₀ (r₁ + r₂) (e.symm a)) =
        (fun a => evaluate W₀ r₁ (e.symm a) + evaluate W₀ r₂ (e.symm a)) := by
      funext a
      exact a3b4g_evaluate_add W₀ r₁ r₂ _
    rw [hfun]
    exact hd

end Chart

section Main

open Topology Filter

/-- Regular functions vanishing at a complex point of a complex scheme smooth of relative
dimension `d`, whose analytic Jacobian along an inverse holomorphic chart is invertible, generate
the maximal ideal of the local ring. Source: Serre, *Géométrie algébrique et géométrie analytique*,
§2; Matsumura, *Commutative Ring Theory*, Theorem 14.2. -/
theorem a3b4g_span_germ_eq_maximalIdeal_of_isUnit_fderiv
    (X : Over (Spec (CommRingCat.of ℂ))) {d : ℕ} [SmoothOfRelativeDimension d X.hom]
    [LocallyOfFiniteType X.hom] (x j : ComplexPoint X)
    (hxj : x ∈ (chartAt (Fin d → ℂ) j).source) (V : X.left.Opens) (hxV : x.underlying ∈ V)
    (f : Fin d → Γ(X.left, V)) (hf0 : ∀ k, evaluate V (f k) x = 0)
    (hunit : IsUnit (fderiv ℂ (fun a k => evaluate V (f k) ((chartAt (Fin d → ℂ) j).symm a))
      ((chartAt (Fin d → ℂ) j) x))) :
    Ideal.span (Set.range fun k => X.left.presheaf.germ V x.underlying hxV (f k)) =
      maximalIdeal (X.left.presheaf.stalk x.underlying) := by
  classical
  let A := X.left.presheaf.stalk x.underlying
  let e := chartAt (Fin d → ℂ) j
  haveI : Smooth X.hom := SmoothOfRelativeDimension.smooth d X.hom
  haveI : IsRegularLocalRing A := Smooth.isRegularLocalRing_stalk_complex (f := X.hom) x.underlying
  have hdim : ringKrullDim A = d :=
    a3b4g_ringKrullDim_stalk_of_smooth X x.underlying (a3b4g_isClosed_underlying X x)
  have hfin : Module.finrank (ResidueField A) (CotangentSpace A) = d := by
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace (R := A)).mp inferInstance
    rw [hdim] at h
    exact_mod_cast h
  have hm : ∀ k, X.left.presheaf.germ V x.underlying hxV (f k) ∈ maximalIdeal A := fun k =>
    a3b4g_mem_of_stalkHom_eq_zero x _ (by rw [a3b4g_stalkHom_germ V (f k) x hxV, hf0 k])
  let v : Fin d → CotangentSpace A := fun k =>
    (maximalIdeal A).toCotangent ⟨_, hm k⟩
  have ha₀ : e x ∈ e.target := e.map_source hxj
  have hsymm : e.symm (e x) = x := e.left_inv hxj
  have hnear : ∀ᶠ a in 𝓝 (e x), e.symm a ∈ overOpen (X := X) V := by
    have hcont : ContinuousAt e.symm (e x) := e.continuousAt_symm ha₀
    have hxV' : e.symm (e x) ∈ overOpen (X := X) V := by rw [hsymm]; exact hxV
    exact hcont.preimage_mem_nhds ((isOpen_overOpen V).mem_nhds hxV')
  have hanalytic : ∀ k, AnalyticAt ℂ (fun a => evaluate V (f k) (e.symm a)) (e x) := fun k =>
    ComplexPoint.analyticAt_localChart_symm_evaluate X d j ha₀ V (f k) (by
      change e.symm (e x) ∈ _
      rw [hsymm]
      exact hxV)
  let F : (Fin d → ℂ) → (Fin d → ℂ) := fun a k => evaluate V (f k) (e.symm a)
  have hFdiff : DifferentiableAt ℂ F (e x) :=
    differentiableAt_pi.mpr fun k => (hanalytic k).differentiableAt
  set D := fderiv ℂ F (e x) with hD
  have hFD : HasFDerivAt F D (e x) := hFdiff.hasFDerivAt
  have hcomp : ∀ k, HasFDerivAt (fun a => evaluate V (f k) (e.symm a))
      ((ContinuousLinearMap.proj k).comp D) (e x) := hasFDerivAt_pi'.mp hFD
  have hsurj : Function.Surjective D := by
    obtain ⟨u, hu⟩ := hunit
    intro z
    refine ⟨(↑u⁻¹ : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) z, ?_⟩
    have h := congrArg (fun T : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) => T z) u.mul_inv
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at h
    rw [← hu]
    exact h
  have hkey : ∀ c : Fin d → ℂ, (∑ k, X.left.presheaf.germ V x.underlying hxV
      (a3b4a_gysin_sectionConst X.hom V (c k) * f k)) ∈ maximalIdeal A ^ 2 → c = 0 := by
    intro c hc
    let S : Γ(X.left, V) := ∑ k, a3b4a_gysin_sectionConst X.hom V (c k) * f k
    have hcS : X.left.presheaf.germ V x.underlying hxV S ∈ maximalIdeal A ^ 2 := by
      simpa only [S, map_sum] using hc
    have hZ := a3b4g_hasFDerivAt_zero_of_mem_sq X j x hxj _ hcS V hxV S rfl
    have hH : HasFDerivAt (fun a => ∑ k, c k * evaluate V (f k) (e.symm a))
        (∑ k, c k • (ContinuousLinearMap.proj k).comp D) (e x) :=
      HasFDerivAt.fun_sum fun k _ => (hcomp k).const_mul (c k)
    have heq : (fun a => ∑ k, c k * evaluate V (f k) (e.symm a)) =ᶠ[𝓝 (e x)]
        (fun a => evaluate V S (e.symm a)) := by
      filter_upwards [hnear] with a ha
      rw [a3b4g_evaluate_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [a3b4g_evaluate_mul, a3b4a_gysin_evaluate_sectionConst X.hom V (e.symm a) ha (c k)]
    have h0 := hH.unique (hZ.congr_of_eventuallyEq heq)
    funext k₀
    obtain ⟨y, hy⟩ := hsurj (Pi.single k₀ 1)
    have hy' := congrArg (fun T : (Fin d → ℂ) →L[ℂ] ℂ => T y) h0
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.proj_apply, hy,
      ContinuousLinearMap.zero_apply, smul_eq_mul] at hy'
    simpa [Pi.single_apply] using hy'
  have hli : LinearIndependent (ResidueField A) v := by
    rw [Fintype.linearIndependent_iff]
    intro μ hμ k₀
    choose a ha using fun k => IsLocalRing.residue_surjective (R := A) (μ k)
    let c : Fin d → ℂ := fun k => x.stalkHom.hom (a k)
    have hconst : ∀ k, x.stalkHom.hom (X.left.presheaf.germ V x.underlying hxV
        (a3b4a_gysin_sectionConst X.hom V (c k))) = c k := fun k => by
      rw [a3b4g_stalkHom_germ V _ x hxV]
      exact a3b4a_gysin_evaluate_sectionConst X.hom V x hxV (c k)
    have hamem : ∀ k, a k - X.left.presheaf.germ V x.underlying hxV
        (a3b4a_gysin_sectionConst X.hom V (c k)) ∈ maximalIdeal A := fun k =>
      a3b4g_mem_of_stalkHom_eq_zero x _ (by rw [map_sub, hconst k, sub_self])
    have hsum : (∑ k, a k * X.left.presheaf.germ V x.underlying hxV (f k)) ∈
        maximalIdeal A ^ 2 := by
      have hmem : (∑ k, a k * X.left.presheaf.germ V x.underlying hxV (f k)) ∈
          maximalIdeal A := Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hm k)
      have htc : (maximalIdeal A).toCotangent ⟨_, hmem⟩ = ∑ k, μ k • v k := by
        have hsub : (⟨_, hmem⟩ : maximalIdeal A) = ∑ k, a k • (⟨_, hm k⟩ : maximalIdeal A) := by
          ext
          simp [smul_eq_mul]
        rw [hsub, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul, ← ha k]
        exact (algebraMap_smul (ResidueField A) (a k) (v k)).symm
      rw [hμ] at htc
      exact (Ideal.toCotangent_eq_zero _ _).mp htc
    have hsq : (∑ k, X.left.presheaf.germ V x.underlying hxV
        (a3b4a_gysin_sectionConst X.hom V (c k) * f k)) ∈ maximalIdeal A ^ 2 := by
      have hrest : (∑ k, (a k - X.left.presheaf.germ V x.underlying hxV
          (a3b4a_gysin_sectionConst X.hom V (c k))) *
            X.left.presheaf.germ V x.underlying hxV (f k)) ∈ maximalIdeal A ^ 2 :=
        Ideal.sum_mem _ fun k _ => by
          rw [pow_two]
          exact Ideal.mul_mem_mul (hamem k) (hm k)
      have h := Ideal.sub_mem _ hsum hrest
      have heq : (∑ k, a k * X.left.presheaf.germ V x.underlying hxV (f k)) -
          (∑ k, (a k - X.left.presheaf.germ V x.underlying hxV
            (a3b4a_gysin_sectionConst X.hom V (c k))) *
              X.left.presheaf.germ V x.underlying hxV (f k)) =
          ∑ k, X.left.presheaf.germ V x.underlying hxV
            (a3b4a_gysin_sectionConst X.hom V (c k) * f k) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_mul]
        ring
      rwa [heq] at h
    have hc0 := congrFun (hkey c hsq) k₀
    rw [← ha k₀]
    exact (IsLocalRing.residue_eq_zero_iff (a k₀)).mpr (a3b4g_mem_of_stalkHom_eq_zero x _ hc0)
  have hspan : Submodule.span (ResidueField A) (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hfin])
  have himage : (maximalIdeal A).toCotangent ''
      Set.range (fun k => (⟨_, hm k⟩ : maximalIdeal A)) = Set.range v := by
    rw [← Set.range_comp]
    rfl
  rw [← himage, CotangentSpace.span_image_eq_top_iff] at hspan
  have hmap := congrArg (Submodule.map (maximalIdeal A).subtype) hspan
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at hmap
  exact hmap

end Main

end HodgeLean.Adapters
