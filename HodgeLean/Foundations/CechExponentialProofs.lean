module
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Contractible
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.Cochain

public import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CoefficientSubdivisionCochain
public import HodgeLean.Foundations.CechExponentialDefs
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # Logarithmic lifting: proof obligations

Route A uses convex logarithms and a degree-two Čech--singular diagram chase over the integers.
All geometric premises are explicit. HC no distance; AV milestone no distance.
-/

public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Filter Set Topology
open scoped Simplicial BigOperators
namespace HodgeLean.Foundations

/-- A nonvanishing analytic germ has a local analytic logarithm.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, I.C,
the local logarithm theorem. -/
theorem cech_local_analytic_log (n : ℕ) (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℂ)
    (hf : AnalyticAt ℂ f x) (hne : f x ≠ 0) :
    ∃ g : (Fin n → ℂ) → ℂ, AnalyticAt ℂ g x ∧
      ∀ᶠ z in 𝓝 x, Complex.exp (g z) = f z := by
  let t : (Fin n → ℂ) → ℂ := fun z ↦ f z / f x
  let g : (Fin n → ℂ) → ℂ := fun z ↦ Complex.log (t z) + Complex.log (f x)
  have ht : AnalyticAt ℂ t x := hf.div_const
  have htx : t x = 1 := by simp [t, hne]
  have hlog : AnalyticAt ℂ Complex.log 1 := by
    apply DifferentiableOn.analyticAt (s := Complex.slitPlane)
    · intro z hz
      exact (Complex.differentiableAt_log hz).differentiableWithinAt
    · exact Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane
  have hg : AnalyticAt ℂ g x := (hlog.comp_of_eq ht htx).add analyticAt_const
  refine ⟨g, hg, ?_⟩
  have ht_ne : ∀ᶠ z in nhds x, t z ≠ 0 :=
    ht.continuousAt.eventually_ne (by rw [htx]; exact one_ne_zero)
  filter_upwards [ht_ne] with z hz
  rw [show Complex.exp (g z) = Complex.exp (Complex.log (t z)) *
      Complex.exp (Complex.log (f x)) by simp only [g, Complex.exp_add]]
  rw [Complex.exp_log hz, Complex.exp_log hne]
  exact div_mul_cancel₀ (f z) hne


/-- Pointed open covers have pointed convex refinements.
Source: metric balls form a basis; Mathlib `Metric.isOpen_iff` and `convex_ball`. -/
theorem cech_convex_refinement_aux (n : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hU : ∀ p, IsOpen (U p)) (hcover : ∀ p, p ∈ U p) :
    ∃ V : (Fin n → ℂ) → Set (Fin n → ℂ),
      (∀ p, IsOpen (V p)) ∧ (∀ p, p ∈ V p) ∧
      (∀ p, Convex ℝ (V p)) ∧ (∀ p, V p ⊆ U p) := by
  choose r hrpos hrsub using fun p ↦ (Metric.isOpen_iff.1 (hU p)) p (hcover p)
  refine ⟨fun p ↦ Metric.ball p (r p), fun p ↦ Metric.isOpen_ball, ?_, ?_, hrsub⟩
  · intro p
    exact Metric.mem_ball_self (hrpos p)
  · intro p
    exact convex_ball p (r p)

/-- A nonvanishing analytic function on a convex open has an analytic logarithm.
Source: Mathlib `Complex.isCoveringMapOn_exp` and
`IsCoveringMapOn.existsUnique_continuousMap_lifts`; local analytic logarithms. -/
theorem cech_convex_log_aux (n : ℕ) (S : Set (Fin n → ℂ))
    (hS : IsOpen S) (hc : Convex ℝ S)
    (f : (Fin n → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f S)
    (hn : ∀ z ∈ S, f z ≠ 0) :
    ∃ b : (Fin n → ℂ) → ℂ,
      AnalyticOnNhd ℂ b S ∧ ∀ z ∈ S, Complex.exp (b z) = f z := by
  by_cases hneS : S.Nonempty
  · have hsc : IsSimplyConnected S := by
      letI : ContractibleSpace S := Convex.contractibleSpace hc hneS
      exact (inferInstance : SimplyConnectedSpace S)
    have hzero : 0 ∉ f '' S := by
      rintro ⟨z, hz, hzf⟩
      exact hn z hz hzf
    obtain ⟨b, hbcont, hbexp⟩ :=
      Complex.exists_continuousOn_eqOn_exp_comp hsc hS hf.continuousOn hzero
    refine ⟨b, ?_, fun z hz ↦ hbexp hz⟩
    intro x hx
    obtain ⟨g, hg, hge⟩ := cech_local_analytic_log n f x (hf x hx) (hn x hx)
    let d : ℂ := b x - g x
    have hed : Complex.exp d = 1 := by
      rw [Complex.exp_sub, show Complex.exp (b x) = f x by simpa using hbexp hx,
        hge.self_of_nhds]
      exact div_self (hn x hx)
    have hg' : AnalyticAt ℂ (fun z ↦ g z + d) x := hg.add analyticAt_const
    have hevent : ∀ᶠ z in 𝓝 x,
        z ∈ S ∧ Complex.exp (g z + d) = f z ∧ ContinuousAt g z := by
      filter_upwards [hS.mem_nhds hx, hge, hg.eventually_continuousAt] with z hzS hzg hgc
      refine ⟨hzS, ?_, hgc⟩
      rw [Complex.exp_add, hed, mul_one, hzg]
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hevent
    have heq : Set.EqOn b (fun z ↦ g z + d) (Metric.ball x ε) := by
      apply IsCoveringMap.eqOn_of_comp_eqOn Complex.isCoveringMap_exp
        (convex_ball x ε).isPreconnected
      · exact hbcont.mono (fun z hz ↦ (hball hz).1)
      · intro z hz
        exact ((hball hz).2.2.add continuousAt_const).continuousWithinAt
      · intro z hz
        apply Subtype.ext
        exact (show Complex.exp (b z) = f z by simpa using hbexp (hball hz).1).trans
          (hball hz).2.1.symm
      · exact Metric.mem_ball_self hε
      · simp only [d]
        abel
    exact hg'.congr (heq.symm.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self hε)))
  · refine ⟨0, ?_, ?_⟩
    · intro z hz
      exact (hneS ⟨z, hz⟩).elim
    · intro z hz
      exact (hneS ⟨z, hz⟩).elim

/-- The exponential of the additive defect of overlap logarithms is one. -/
private theorem cech_defect_exp (n : ℕ) (V : (Fin n → ℂ) → Set (Fin n → ℂ))
    (u b : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (he : ∀ p q z, z ∈ V p ∩ V q → Complex.exp (b p q z) = u p q z)
    (hc : ∀ p q r z, z ∈ V p ∩ V q ∩ V r → u p q z * u q r z = u p r z)
    (p q r z : Fin n → ℂ) (hz : z ∈ V p ∩ V q ∩ V r) :
    Complex.exp (b q r z - b p r z + b p q z) = 1 := by
  rw [Complex.exp_add, Complex.exp_sub, he q r z ⟨hz.1.2, hz.2⟩,
    he p r z ⟨hz.1.1, hz.2⟩, he p q z hz.1, div_mul_eq_mul_div,
    mul_comm (u q r z) (u p q z), hc p q r z hz, div_self]
  rw [← he p r z ⟨hz.1.1, hz.2⟩]
  exact Complex.exp_ne_zero _

/-- The additive defect is constant on a convex triple intersection. -/
private theorem cech_defect_const (n : ℕ) (V : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hv : ∀ p, Convex ℝ (V p))
    (u b : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (hb : ∀ p q, AnalyticOnNhd ℂ (b p q) (V p ∩ V q))
    (he : ∀ p q z, z ∈ V p ∩ V q → Complex.exp (b p q z) = u p q z)
    (hc : ∀ p q r z, z ∈ V p ∩ V q ∩ V r → u p q z * u q r z = u p r z)
    (p q r : Fin n → ℂ) {z w : Fin n → ℂ}
    (hz : z ∈ V p ∩ V q ∩ V r) (hw : w ∈ V p ∩ V q ∩ V r) :
    b q r z - b p r z + b p q z = b q r w - b p r w + b p q w := by
  let T := V p ∩ V q ∩ V r
  let d := fun z ↦ b q r z - b p r z + b p q z
  have hd : ContinuousOn d T :=
    ((hb q r).continuousOn.mono fun _ h ↦ ⟨h.1.2, h.2⟩).sub
      ((hb p r).continuousOn.mono fun _ h ↦ ⟨h.1.1, h.2⟩) |>.add
      ((hb p q).continuousOn.mono fun _ h ↦ h.1)
  have hexd : ∀ x ∈ T, ∀ y ∈ T,
      (⟨Complex.exp (d x), Complex.exp_ne_zero _⟩ : {z : ℂ // z ≠ 0}) =
        ⟨Complex.exp (d y), Complex.exp_ne_zero _⟩ := by
    intro x hx y hy
    apply Subtype.ext
    exact (cech_defect_exp n V u b he hc p q r x hx).trans
      (cech_defect_exp n V u b he hc p q r y hy).symm
  exact IsCoveringMap.constOn_of_comp Complex.isCoveringMap_exp
    ((hv p).inter (hv q) |>.inter (hv r)).isPreconnected hd hexd hz hw

/-- Overlap logarithms determine a constant integral two-cocycle on a convex cover.
Source: Gunning--Rossi, VIII, exponential sequence; Mathlib `Complex.exp_eq_one_iff`. -/
theorem cech_integer_defect_aux (n : ℕ) (V : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hV : ∀ p, IsOpen (V p)) (hv : ∀ p, Convex ℝ (V p))
    (u b : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (hb : ∀ p q, AnalyticOnNhd ℂ (b p q) (V p ∩ V q))
    (he : ∀ p q z, z ∈ V p ∩ V q → Complex.exp (b p q z) = u p q z)
    (hc : ∀ p q r z, z ∈ V p ∩ V q ∩ V r → u p q z * u q r z = u p r z) :
    ∃ c : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℤ,
      (∀ p q r z, z ∈ V p ∩ V q ∩ V r →
        b q r z - b p r z + b p q z = (2 * Real.pi * Complex.I) * (c p q r : ℂ)) ∧
      (∀ p q r s z, z ∈ V p ∩ V q ∩ V r ∩ V s →
        c q r s - c p r s + c p q s - c p q r = 0) := by
  classical
  have hex : ∀ p q r, ∃ k : ℤ, ∀ z, z ∈ V p ∩ V q ∩ V r →
      b q r z - b p r z + b p q z = (2 * Real.pi * Complex.I) * (k : ℂ) := by
    intro p q r
    by_cases hn : (V p ∩ V q ∩ V r).Nonempty
    · obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp
        (cech_defect_exp n V u b he hc p q r hn.choose hn.choose_spec)
      refine ⟨k, fun z hz ↦ ?_⟩
      rw [cech_defect_const n V hv u b hb he hc p q r hz hn.choose_spec, hk]
      ring
    · exact ⟨0, fun z hz ↦ (hn ⟨z, hz⟩).elim⟩
  choose c hdef using hex
  refine ⟨c, hdef, ?_⟩
  intro p q r s z hz
  have hzqrs : z ∈ V q ∩ V r ∩ V s := ⟨⟨hz.1.1.2, hz.1.2⟩, hz.2⟩
  have hzprs : z ∈ V p ∩ V r ∩ V s := ⟨⟨hz.1.1.1, hz.1.2⟩, hz.2⟩
  have hzpqs : z ∈ V p ∩ V q ∩ V s := ⟨hz.1.1, hz.2⟩
  have hzpqr : z ∈ V p ∩ V q ∩ V r := hz.1
  have hsum : (2 * Real.pi * Complex.I : ℂ) *
      ((c q r s - c p r s + c p q s - c p q r : ℤ) : ℂ) = 0 := by
    rw [Int.cast_sub, Int.cast_add, Int.cast_sub]
    calc
      _ = (b r s z - b q s z + b q r z) -
          (b r s z - b p s z + b p r z) +
          (b q s z - b p s z + b p q z) -
          (b q r z - b p r z + b p q z) := by
            rw [hdef q r s z hzqrs, hdef p r s z hzprs,
              hdef p q s z hzpqs, hdef p q r z hzpqr]
            ring
      _ = 0 := by ring
  have hperiod : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hcast : ((c q r s - c p r s + c p q s - c p q r : ℤ) : ℂ) = 0 :=
    (mul_eq_zero.mp hsum).resolve_left hperiod
  exact_mod_cast hcast

/-- Positive Čech degrees of the singular cochain rows are exact on supported simplices.
Source: Bott--Tu, §8, contraction by an index containing the entire simplex. -/
theorem cech_horizontal_exact_aux (n p q : ℕ) (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (F : (Fin (p + 2) → (Fin n → ℂ)) → cech_simplex n q → ℤ)
    (hF : ∀ t σ, (∀ x i, σ x ∈ U (t i)) → cech_h n (p + 1) F t σ = 0) :
    ∃ G : (Fin (p + 1) → (Fin n → ℂ)) → cech_simplex n q → ℤ,
      ∀ t σ, (∀ x i, σ x ∈ U (t i)) → cech_h n p G t σ = F t σ := by
  classical
  let j : cech_simplex n q → (Fin n → ℂ) := fun σ ↦
    if h : ∃ a, ∀ x, σ x ∈ U a then Classical.choose h else 0
  have hj (σ : cech_simplex n q) (h : ∃ a, ∀ x, σ x ∈ U a) :
      ∀ x, σ x ∈ U (j σ) := by
    simp only [j, dite_eq_left h]
    exact Classical.choose_spec h
  let G : (Fin (p + 1) → (Fin n → ℂ)) → cech_simplex n q → ℤ := fun t σ ↦
    F (Fin.cases (j σ) t) σ
  refine ⟨G, ?_⟩
  intro t σ ht
  have hjσ := hj σ ⟨t 0, fun x ↦ ht x 0⟩
  have hsupport : ∀ x i, σ x ∈ U (Fin.cases (j σ) t i) := by
    intro x i
    refine Fin.cases (hjσ x) (fun k ↦ ht x k) i
  have hzero := hF (Fin.cases (j σ) t) σ hsupport
  have hzeroFace : (Fin.cases (j σ) t) ∘ Fin.succAbove 0 = t := by
    funext x
    simp
  have hsuccFace (i : Fin (p + 2)) :
      (Fin.cases (j σ) t) ∘ i.succ.succAbove =
        Fin.cases (j σ) (t ∘ i.succAbove) := by
    funext x
    refine Fin.cases ?_ (fun k ↦ ?_) x
    · simp
    · simp only [Function.comp_apply, Fin.cases_succ]
      by_cases hki : k.castSucc < i
      · simp [Fin.succAbove, hki, Fin.cases]
      · simp [Fin.succAbove, hki, Fin.cases]
  rw [cech_h, Fin.sum_univ_succ, hzeroFace] at hzero
  simp only [Fin.val_zero, pow_zero, one_mul] at hzero
  simp_rw [hsuccFace] at hzero
  have hsign (i : Fin (p + 2)) : (-1 : ℤ) ^ i.succ.val = -((-1 : ℤ) ^ i.val) := by
    rw [show i.succ.val = i.val + 1 by rfl, pow_succ]
    omega
  simp_rw [hsign, neg_mul, Finset.sum_neg_distrib] at hzero
  rw [cech_h]
  simp only [G]
  linarith

/-- Compatible degree-zero rows glue to a cochain on cover-small singular simplices.
Source: Bott--Tu, §8, augmentation of the Čech double complex. -/
theorem cech_horizontal_glue_aux (n q : ℕ) (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (F : (Fin 1 → (Fin n → ℂ)) → cech_simplex n q → ℤ)
    (hF : ∀ t σ, (∀ x i, σ x ∈ U (t i)) → cech_h n 0 F t σ = 0) :
    ∃ G : cech_simplex n q → ℤ,
      ∀ t σ, (∀ x i, σ x ∈ U (t i)) → G σ = F t σ := by
  classical
  let j : cech_simplex n q → (Fin n → ℂ) := fun σ ↦
    if h : ∃ a, ∀ x, σ x ∈ U a then Classical.choose h else 0
  have hj (σ : cech_simplex n q) (h : ∃ a, ∀ x, σ x ∈ U a) :
      ∀ x, σ x ∈ U (j σ) := by
    simp only [j, dite_eq_left h]
    exact Classical.choose_spec h
  let G : cech_simplex n q → ℤ := fun σ ↦ F (fun _ ↦ j σ) σ
  refine ⟨G, ?_⟩
  intro t σ ht
  have hjσ := hj σ ⟨t 0, fun x ↦ ht x 0⟩
  let T : Fin 2 → (Fin n → ℂ) := Fin.cases (j σ) t
  have hsupport : ∀ x i, σ x ∈ U (T i) := by
    intro x i
    refine Fin.cases (hjσ x) (fun k ↦ ht x k) i
  have hzero := hF T σ hsupport
  have ht_const : t = fun _ ↦ t 0 := by
    funext i
    exact Fin.eq_zero i ▸ rfl
  have hfirst : T ∘ Fin.succAbove 0 = t := by
    funext i
    simp [T]
  have hsecond : T ∘ (Fin.succ 0).succAbove = fun _ ↦ j σ := by
    funext i
    fin_cases i
    rfl
  rw [cech_h, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero,
    hfirst, hsecond] at hzero
  norm_num at hzero
  change F (fun _ ↦ j σ) σ = F t σ
  rw [ht_const] at hzero ⊢
  linarith

private theorem cech_contractible_one_exact (X : Type) [TopologicalSpace X]
    [ContractibleSpace X]
    (F : (TopCat.toSSet.obj (TopCat.of X)).obj (.op ⦋1⦌) → ℤ)
    (hF : ∀ σ, ∑ i : Fin 3, (-1 : ℤ) ^ i.val *
      F ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) = 0) :
    ∃ G : (TopCat.toSSet.obj (TopCat.of X)).obj (.op ⦋0⦌) → ℤ,
      ∀ σ, ∑ i : Fin 2, (-1 : ℤ) ^ i.val *
        G ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) = F σ := by
  let T := TopCat.toSSet.obj (TopCat.of X)
  let C := T.chainComplex (ModuleCat.of ℤ ℤ)
  let φ : Module.Dual ℤ (C.X 1) :=
    (CategoryTheory.Limits.Sigma.desc fun σ ↦ ModuleCat.ofHom <|
      (LinearMap.ringLmapEquivSelf ℤ ℤ ℤ).symm (F σ)).hom
  have hφ_basis (σ : T.obj (.op ⦋1⦌)) (r : ℤ) :
      φ ((T.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom r) = r * F σ := by
    dsimp only [φ, SSet.ιChainComplex]
    change (CategoryTheory.Limits.Sigma.ι
        (fun _ : T.obj (.op ⦋1⦌) ↦ ModuleCat.of ℤ ℤ) σ ≫
      CategoryTheory.Limits.Sigma.desc (fun τ ↦ ModuleCat.ofHom
        ((LinearMap.ringLmapEquivSelf ℤ ℤ ℤ).symm (F τ)))).hom r = r * F σ
    rw [CategoryTheory.Limits.Sigma.ι_desc]
    simp
  have hd : C.d 2 1 ≫ ModuleCat.ofHom φ = 0 := by
    apply T.chainComplex_hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change φ ((T.ιChainComplex σ ≫ C.d 2 1).hom r) = 0
    rw [SSet.ιChainComplex_d]
    change ((∑ i : Fin 3, (-1 : ℤ) ^ i.val • T.ιChainComplex (T.δ i σ)) ≫
      ModuleCat.ofHom φ).hom r = 0
    rw [CategoryTheory.Preadditive.sum_comp]
    simp only [CategoryTheory.Preadditive.zsmul_comp]
    simp [hφ_basis]
    norm_num [Fin.sum_univ_succ] at hF ⊢
    linear_combination r * hF σ
  have hφ : (C.d 2 1).hom.dualMap φ = 0 := by
    apply LinearMap.ext
    intro c
    exact congrArg (fun f ↦ f.hom c) hd
  have hrange : φ ∈ LinearMap.range (C.d 1 0).hom.dualMap := by
    have heq := AlgebraicTopology.singularChain_dual_range_eq_ker_of_contractible ℤ X 0
    change LinearMap.range (C.d 1 0).hom.dualMap =
      LinearMap.ker (C.d 2 1).hom.dualMap at heq
    rw [heq]
    exact hφ
  obtain ⟨ψ, hψ⟩ := hrange
  let G : T.obj (.op ⦋0⦌) → ℤ := fun σ ↦
    ψ ((T.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1)
  refine ⟨G, ?_⟩
  intro σ
  have hv := LinearMap.congr_fun hψ
    ((T.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1)
  change ψ ((C.d 1 0).hom
    ((T.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1)) =
      φ ((T.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1) at hv
  rw [hφ_basis, one_mul] at hv
  rw [← ModuleCat.comp_apply, SSet.ιChainComplex_d] at hv
  simpa [G] using hv

private theorem cech_contractible_zero_constant (X : Type) [TopologicalSpace X]
    [ContractibleSpace X]
    (F : (TopCat.toSSet.obj (TopCat.of X)).obj (.op ⦋0⦌) → ℤ)
    (hF : ∀ σ, ∑ i : Fin 2, (-1 : ℤ) ^ i.val *
      F ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) = 0) :
    ∃ k : ℤ, ∀ σ, F σ = k := by
  let T := TopCat.toSSet.obj (TopCat.of X)
  let C := T.chainComplex (ModuleCat.of ℤ ℤ)
  let φ : Module.Dual ℤ (C.X 0) :=
    (Sigma.desc fun σ ↦ ModuleCat.ofHom <|
      (LinearMap.ringLmapEquivSelf ℤ ℤ ℤ).symm (F σ)).hom
  have hφ_basis (σ : T.obj (.op ⦋0⦌)) (r : ℤ) :
      φ ((T.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom r) = r * F σ := by
    dsimp only [φ, SSet.ιChainComplex]
    change (Sigma.ι (fun _ : T.obj (.op ⦋0⦌) ↦ ModuleCat.of ℤ ℤ) σ ≫
      Sigma.desc (fun τ ↦ ModuleCat.ofHom
        ((LinearMap.ringLmapEquivSelf ℤ ℤ ℤ).symm (F τ)))).hom r = r * F σ
    rw [Sigma.ι_desc]
    simp
  have hφ : (C.d 1 0).hom.dualMap φ = 0 := by
    apply LinearMap.ext
    intro c
    have hd : C.d 1 0 ≫ ModuleCat.ofHom φ = 0 := by
      apply T.chainComplex_hom_ext
      intro σ
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      change φ ((T.ιChainComplex σ ≫ C.d 1 0).hom r) = 0
      rw [SSet.ιChainComplex_d]
      change ((∑ i : Fin 2, (-1 : ℤ) ^ i.val • T.ιChainComplex (T.δ i σ)) ≫
        ModuleCat.ofHom φ).hom r = 0
      rw [Preadditive.sum_comp]
      simp only [Preadditive.zsmul_comp]
      simp [hφ_basis]
      norm_num [Fin.sum_univ_succ] at hF ⊢
      linear_combination r * hF σ
    exact congrArg (fun f ↦ f.hom c) hd
  letI : T.IsConnected :=
    inferInstanceAs ((TopCat.toSSet.obj (TopCat.of X)).IsConnected)
  obtain ⟨k, hk⟩ :=
    AlgebraicTopology.Singular.exists_eq_smul_simplicialZeroAugmentation_of_connected
      ℤ T φ hφ
  refine ⟨k, ?_⟩
  intro σ
  have hv := congrArg (fun f ↦ f
    ((T.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1)) hk
  rw [hφ_basis, one_mul] at hv
  have haug :
      (AlgebraicTopology.Singular.simplicialZeroAugmentation ℤ T).hom
        ((T.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1) = 1 :=
    congrArg (fun f ↦ f.hom 1)
      (AlgebraicTopology.Singular.ιChainComplex_comp_simplicialZeroAugmentation ℤ T σ)
  change k * (AlgebraicTopology.Singular.simplicialZeroAugmentation ℤ T).hom
    ((T.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1) = F σ at hv
  rw [haug, mul_one] at hv
  exact hv.symm

/-- A closed integral singular one-cochain on a convex subset has a primitive.
Source: Hatcher, Theorem 2.10 and §3.1; upstream
`singularCochainComplex_exactAt_of_contractible` at `2ead713`. -/
theorem cech_vertical_one_aux (n : ℕ) (S : Set (Fin n → ℂ)) (hc : Convex ℝ S)
    (F : cech_simplex n 1 → ℤ)
    (hF : ∀ σ, (∀ x, σ x ∈ S) → cech_d n 1 F σ = 0) :
    ∃ G : cech_simplex n 0 → ℤ,
      ∀ σ, (∀ x, σ x ∈ S) → cech_d n 0 G σ = F σ := by
  classical
  by_cases hS : S.Nonempty
  · letI : ContractibleSpace S := hc.contractibleSpace hS
    let forget (q : ℕ) : (TopCat.toSSet.obj (TopCat.of S)).obj (.op ⦋q⦌) →
        cech_simplex n q := fun σ ↦
      ⟨fun x ↦ ((TopCat.of S).toSSetObjEquiv _ σ x).1,
        continuous_subtype_val.comp
          ((TopCat.of S).toSSetObjEquiv _ σ).continuous⟩
    have hclosed : ∀ σ, ∑ i : Fin 3, (-1 : ℤ) ^ i.val *
        (F ∘ forget 1) ((TopCat.toSSet.obj (TopCat.of S)).δ i σ) = 0 := by
      intro σ
      have h := hF (forget 2 σ)
        (fun x ↦ ((TopCat.of S).toSSetObjEquiv _ σ x).2)
      have hface (i : Fin 3) :
          forget 1 ((TopCat.toSSet.obj (TopCat.of S)).δ i σ) =
            cech_face n 1 i (forget 2 σ) := by
        ext x
        rfl
      simpa [cech_d, Function.comp_def, hface] using h
    obtain ⟨G, hG⟩ := cech_contractible_one_exact S (F ∘ forget 1) hclosed
    refine ⟨fun σ ↦ if hσ : ∀ x, σ x ∈ S then
      G (((TopCat.of S).toSSetObjEquiv (.op ⦋0⦌)).symm
        ⟨fun x ↦ ⟨σ x, hσ x⟩, σ.continuous.subtype_mk _⟩) else 0, ?_⟩
    intro σ hσ
    let τ : C(SimplexCategory.toTop₀.obj ⦋1⦌, S) :=
      ⟨fun x ↦ ⟨σ x, hσ x⟩, σ.continuous.subtype_mk _⟩
    let τs := ((TopCat.of S).toSSetObjEquiv (.op ⦋1⦌)).symm τ
    have h := hG τs
    simp only [cech_d]
    rw [Fin.sum_univ_two]
    simp only [Fin.isValue, Fin.val_zero, pow_zero, one_mul, Fin.val_one, pow_one,
      neg_one_mul]
    have hface (i : Fin 2) : ∀ x, cech_face n 0 i σ x ∈ S := fun x ↦ hσ _
    simp only [hface]
    have hnat (i : Fin 2) :
        ((TopCat.of S).toSSetObjEquiv (.op ⦋0⦌)).symm
          ⟨fun x ↦ ⟨cech_face n 0 i σ x, hface i x⟩,
            (cech_face n 0 i σ).continuous.subtype_mk _⟩ =
          (TopCat.toSSet.obj (TopCat.of S)).δ i τs := by
      rfl
    have hforget : forget 1 τs = σ := by
      ext x
      rfl
    convert h using 1
    · simp only [dif_pos (fun _ ↦ trivial), Fin.sum_univ_two, Fin.isValue,
        Fin.val_zero, pow_zero, one_mul, Fin.val_one, pow_one, neg_one_mul]
      rw [hnat 0, hnat 1]
    · simpa [Function.comp_def] using congrArg F hforget.symm
  · refine ⟨fun _ ↦ 0, ?_⟩
    intro σ hσ
    exact (hS ⟨σ (Classical.arbitrary _), hσ _⟩).elim

/-- Closed singular zero-cochains on a convex subset are constant.
Source: Hatcher, §3.1, degree-zero cohomology and paths. -/
theorem cech_vertical_zero_aux (n : ℕ) (S : Set (Fin n → ℂ)) (hc : Convex ℝ S)
    (F : cech_simplex n 0 → ℤ)
    (hF : ∀ σ, (∀ x, σ x ∈ S) → cech_d n 0 F σ = 0) :
    ∃ k : ℤ, ∀ σ, (∀ x, σ x ∈ S) → F σ = k := by
  classical
  by_cases hS : S.Nonempty
  · letI : ContractibleSpace S := hc.contractibleSpace hS
    let forget (q : ℕ) : (TopCat.toSSet.obj (TopCat.of S)).obj (.op ⦋q⦌) →
        cech_simplex n q := fun σ ↦
      ⟨fun x ↦ ((TopCat.of S).toSSetObjEquiv _ σ x).1,
        continuous_subtype_val.comp
          ((TopCat.of S).toSSetObjEquiv _ σ).continuous⟩
    have hclosed : ∀ σ, ∑ i : Fin 2, (-1 : ℤ) ^ i.val *
        (F ∘ forget 0) ((TopCat.toSSet.obj (TopCat.of S)).δ i σ) = 0 := by
      intro σ
      have h := hF (forget 1 σ)
        (fun x ↦ ((TopCat.of S).toSSetObjEquiv _ σ x).2)
      have hface (i : Fin 2) :
          forget 0 ((TopCat.toSSet.obj (TopCat.of S)).δ i σ) =
            cech_face n 0 i (forget 1 σ) := by
        ext x
        rfl
      simpa [cech_d, Function.comp_def, hface] using h
    obtain ⟨k, hk⟩ := cech_contractible_zero_constant S (F ∘ forget 0) hclosed
    refine ⟨k, ?_⟩
    intro σ hσ
    let τ : C(SimplexCategory.toTop₀.obj ⦋0⦌, S) :=
      ⟨fun x ↦ ⟨σ x, hσ x⟩, σ.continuous.subtype_mk _⟩
    let τs := ((TopCat.of S).toSSetObjEquiv (.op ⦋0⦌)).symm τ
    have h := hk τs
    have hforget : forget 0 τs = σ := by
      ext x
      rfl
    simpa [Function.comp_def, hforget] using h
  · refine ⟨0, ?_⟩
    intro σ hσ
    exact (hS ⟨σ (Classical.arbitrary _), hσ _⟩).elim

private noncomputable def cechSmallCochain (n q : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (F : cech_simplex n q → ℤ) :
    Module.Dual ℤ
      ((AlgebraicTopology.Singular.CoverSmallCoefficientSingularChainComplex ℤ
        (TopCat.of (Fin n → ℂ)) U).X q) :=
  let X : SSet := AlgebraicTopology.Singular.coverSmallSingularSubcomplex
    (TopCat.of (Fin n → ℂ)) U
  ModuleCat.Hom.hom <|
    (X.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) q).desc
      (CategoryTheory.Limits.Cofan.mk _ fun σ ↦ ModuleCat.ofHom <|
        LinearMap.mulLeft ℤ (F ((TopCat.of (Fin n → ℂ)).toSSetObjEquiv _ σ.1)))

private lemma cechSmallCochain_iota (n q : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (F : cech_simplex n q → ℤ)
    (σ : (AlgebraicTopology.Singular.coverSmallSingularSubcomplex
      (TopCat.of (Fin n → ℂ)) U).obj (.op ⟨q⟩)) :
    cechSmallCochain n q U F
        ((((AlgebraicTopology.Singular.coverSmallSingularSubcomplex
          (TopCat.of (Fin n → ℂ)) U : SSet).chainComplexXCofan
            (ModuleCat.of ℤ ℤ) q).inj σ).hom 1) =
      F ((TopCat.of (Fin n → ℂ)).toSSetObjEquiv _ σ.1) := by
  dsimp only [cechSmallCochain]
  change (((AlgebraicTopology.Singular.coverSmallSingularSubcomplex
      (TopCat.of (Fin n → ℂ)) U : SSet).isColimitChainComplexXCofan
        (ModuleCat.of ℤ ℤ) q).desc _).hom
      ((((AlgebraicTopology.Singular.coverSmallSingularSubcomplex
        (TopCat.of (Fin n → ℂ)) U : SSet).chainComplexXCofan
          (ModuleCat.of ℤ ℤ) q).inj σ).hom 1) = _
  have hfac :=
    ((AlgebraicTopology.Singular.coverSmallSingularSubcomplex
      (TopCat.of (Fin n → ℂ)) U : SSet).isColimitChainComplexXCofan
        (ModuleCat.of ℤ ℤ) q |>.fac
          (CategoryTheory.Limits.Cofan.mk _ fun τ ↦ ModuleCat.ofHom <|
            LinearMap.mulLeft ℤ
              (F ((TopCat.of (Fin n → ℂ)).toSSetObjEquiv _ τ.1)))
          (CategoryTheory.Discrete.mk σ))
  have hhom := congrArg ModuleCat.Hom.hom hfac
  have h := LinearMap.congr_fun hhom (1 : ℤ)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, mul_one, CategoryTheory.Limits.Cofan.inj,
    CategoryTheory.Limits.Cofan.mk_ι_app,
    CategoryTheory.Discrete.functor_obj, ModuleCat.hom_ofHom] using h

private lemma cechSmallCochain_d_iota (n q : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (F : cech_simplex n q → ℤ)
    (σ : (AlgebraicTopology.Singular.coverSmallSingularSubcomplex
      (TopCat.of (Fin n → ℂ)) U).obj (.op ⟨q + 1⟩)) :
    (show Module.Dual ℤ
        ((AlgebraicTopology.Singular.CoverSmallCoefficientSingularChainComplex ℤ
          (TopCat.of (Fin n → ℂ)) U).X (q + 1)) from
      ((AlgebraicTopology.Singular.CoverSmallCoefficientSingularChainComplex ℤ
        (TopCat.of (Fin n → ℂ)) U).linearDualCochainComplex.d q (q + 1)).hom
        (cechSmallCochain n q U F))
        ((((AlgebraicTopology.Singular.coverSmallSingularSubcomplex
          (TopCat.of (Fin n → ℂ)) U : SSet).chainComplexXCofan
            (ModuleCat.of ℤ ℤ) (q + 1)).inj σ).hom 1) =
      cech_d n q F ((TopCat.of (Fin n → ℂ)).toSSetObjEquiv _ σ.1) := by
  rw [show ((AlgebraicTopology.Singular.coverSmallSingularSubcomplex
      (TopCat.of (Fin n → ℂ)) U : SSet).chainComplexXCofan
        (ModuleCat.of ℤ ℤ) (q + 1)).inj σ =
      (AlgebraicTopology.Singular.coverSmallSingularSubcomplex
        (TopCat.of (Fin n → ℂ)) U : SSet).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) σ from rfl]
  change cechSmallCochain n q U F
      (((AlgebraicTopology.Singular.CoverSmallCoefficientSingularChainComplex ℤ
        (TopCat.of (Fin n → ℂ)) U).d (q + 1) q).hom
        (((AlgebraicTopology.Singular.coverSmallSingularSubcomplex
          (TopCat.of (Fin n → ℂ)) U : SSet).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) σ).hom 1)) = _
  have hd := CategoryTheory.ConcreteCategory.congr_hom
    (SSet.ιChainComplex_d
      (AlgebraicTopology.Singular.coverSmallSingularSubcomplex
        (TopCat.of (Fin n → ℂ)) U : SSet)
      (R := ModuleCat.of ℤ ℤ) σ) 1
  have hstep :
      ((AlgebraicTopology.Singular.CoverSmallCoefficientSingularChainComplex ℤ
        (TopCat.of (Fin n → ℂ)) U).d (q + 1) q).hom
        (((AlgebraicTopology.Singular.coverSmallSingularSubcomplex
          (TopCat.of (Fin n → ℂ)) U : SSet).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) σ).hom 1) =
      (∑ i : Fin (q + 2), (-1 : ℤ) ^ i.val •
        (AlgebraicTopology.Singular.coverSmallSingularSubcomplex
          (TopCat.of (Fin n → ℂ)) U : SSet).ιChainComplex
            (R := ModuleCat.of ℤ ℤ)
            ((AlgebraicTopology.Singular.coverSmallSingularSubcomplex
              (TopCat.of (Fin n → ℂ)) U : SSet).δ i σ)).hom 1 := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
    exact hd
  rw [hstep]
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.sum_apply, map_sum, cech_d]
  apply Finset.sum_congr rfl
  intro i _
  change cechSmallCochain n q U F
      (((-1 : ℤ) ^ i.val) •
        (((AlgebraicTopology.Singular.coverSmallSingularSubcomplex
          (TopCat.of (Fin n → ℂ)) U : SSet).ιChainComplex
            (R := ModuleCat.of ℤ ℤ)
            ((AlgebraicTopology.Singular.coverSmallSingularSubcomplex
              (TopCat.of (Fin n → ℂ)) U : SSet).δ i σ)).hom 1)) = _
  rw [map_zsmul]
  rw [show (AlgebraicTopology.Singular.coverSmallSingularSubcomplex
      (TopCat.of (Fin n → ℂ)) U : SSet).ιChainComplex
        (R := ModuleCat.of ℤ ℤ)
        ((AlgebraicTopology.Singular.coverSmallSingularSubcomplex
          (TopCat.of (Fin n → ℂ)) U : SSet).δ i σ) =
      ((AlgebraicTopology.Singular.coverSmallSingularSubcomplex
        (TopCat.of (Fin n → ℂ)) U : SSet).chainComplexXCofan
          (ModuleCat.of ℤ ℤ) q).inj
        ((AlgebraicTopology.Singular.coverSmallSingularSubcomplex
          (TopCat.of (Fin n → ℂ)) U : SSet).δ i σ) from rfl]
  congr 1
  exact cechSmallCochain_iota n q U F _

private lemma cech_mem_coverSmall_iff (n q : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (σ : (TopCat.toSSet.obj (TopCat.of (Fin n → ℂ))).obj (.op ⟨q⟩)) :
    (∃ p, ∀ x, ((TopCat.of (Fin n → ℂ)).toSSetObjEquiv _ σ) x ∈ U p) ↔
      σ ∈ (AlgebraicTopology.Singular.coverSmallSingularSubcomplex
        (TopCat.of (Fin n → ℂ)) U).obj (.op ⟨q⟩) := by
  rw [AlgebraicTopology.Singular.mem_coverSmallSingularSubcomplex_iff_exists_preimage]
  constructor
  · rintro ⟨p, hp⟩
    let f : C(SimplexCategory.toTop₀.obj ⦋q⦌, U p) :=
      ⟨fun x ↦ ⟨((TopCat.of (Fin n → ℂ)).toSSetObjEquiv _ σ) x, hp x⟩,
        ((TopCat.of (Fin n → ℂ)).toSSetObjEquiv _ σ).continuous.subtype_mk _⟩
    refine ⟨p, ((TopCat.of (U p)).toSSetObjEquiv _).symm f, ?_⟩
    apply ((TopCat.of (Fin n → ℂ)).toSSetObjEquiv _).injective
    ext x
    rfl
  · rintro ⟨p, y, rfl⟩
    refine ⟨p, fun x ↦ ?_⟩
    exact (((TopCat.of (U p)).toSSetObjEquiv _ y) x).property

/-- A closed integral cover-small two-cochain on affine space has a cover-small primitive.
Source: Hatcher, Proposition 2.21 and Theorem 2.10; upstream
`coverSmallChainApproximation_of_openCover` at `2ead713`. -/
theorem cech_small_two_aux (n : ℕ) (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hU : ∀ p, IsOpen (U p)) (hcover : ∀ p, p ∈ U p)
    (F : cech_simplex n 2 → ℤ)
    (hF : ∀ σ, (∃ p, ∀ x, σ x ∈ U p) → cech_d n 2 F σ = 0) :
    ∃ G : cech_simplex n 1 → ℤ,
      ∀ σ, (∃ p, ∀ x, σ x ∈ U p) → cech_d n 1 G σ = F σ := by
  let Y : TopCat := TopCat.of (Fin n → ℂ)
  let C := AlgebraicTopology.Singular.CoverSmallCoefficientSingularChainComplex ℤ Y U
  let B := C.linearDualCochainComplex
  let ρ := AlgebraicTopology.Singular.coefficientCochainRestrictionToCoverSmall ℤ Y U
  have hUcover : ⋃ p, U p = Set.univ := by
    ext z
    simp only [mem_iUnion, mem_univ, iff_true]
    exact ⟨z, hcover z⟩
  letI : QuasiIso ρ :=
    AlgebraicTopology.Singular.coefficientCochainRestrictionToCoverSmall_quasiIso
      ℤ Y U hU hUcover
  have hA := AlgebraicTopology.singularCochainComplex_exactAt_of_contractible
    ℤ (Fin n → ℂ) 1
  have hB : B.ExactAt 2 := by
    rw [← exactAt_iff_of_quasiIsoAt ρ 2]
    exact hA
  have hB' := hB
  rw [HomologicalComplex.exactAt_iff' B 1 2 3 (by simp) (by simp)] at hB'
  have hrange := hB'.moduleCat_range_eq_ker
  let φ : B.X 2 := cechSmallCochain n 2 U F
  have hφ' : (B.d 2 (2 + 1)).hom φ = 0 := by
    have hmorph : CategoryTheory.CategoryStruct.comp (C.d (2 + 1) 2) (ModuleCat.ofHom φ) = 0 := by
      apply SSet.chainComplex_hom_ext
      intro σ
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      have hsmall : ∃ p, ∀ x,
          (Y.toSSetObjEquiv _ σ.1) x ∈ U p :=
        (cech_mem_coverSmall_iff n 3 U σ.1).mpr σ.property
      have hz := hF (Y.toSSetObjEquiv _ σ.1) hsmall
      have heval := cechSmallCochain_d_iota n 2 U F σ
      have hgen : (show Module.Dual ℤ (C.X (2 + 1)) from (B.d 2 (2 + 1)).hom φ)
          (((AlgebraicTopology.Singular.coverSmallSingularSubcomplex Y U : SSet).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) σ).hom 1) = 0 := by
        rw [show (AlgebraicTopology.Singular.coverSmallSingularSubcomplex Y U : SSet).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) σ =
          ((AlgebraicTopology.Singular.coverSmallSingularSubcomplex Y U : SSet).chainComplexXCofan
            (ModuleCat.of ℤ ℤ) (2 + 1)).inj σ from rfl]
        convert heval.trans hz using 1
      change (show Module.Dual ℤ (C.X (2 + 1)) from (B.d 2 (2 + 1)).hom φ)
        (((AlgebraicTopology.Singular.coverSmallSingularSubcomplex Y U : SSet).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) σ).hom a) = 0
      have hiota :
          ((AlgebraicTopology.Singular.coverSmallSingularSubcomplex Y U : SSet).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) σ).hom a =
          a • ((AlgebraicTopology.Singular.coverSmallSingularSubcomplex Y U : SSet).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) σ).hom 1 := by
        calc
          _ = ((AlgebraicTopology.Singular.coverSmallSingularSubcomplex Y U : SSet).ιChainComplex
              (R := ModuleCat.of ℤ ℤ) σ).hom (a • (1 : ℤ)) := by
                rw [smul_eq_mul, mul_one]
          _ = _ := map_zsmul _ _ _
      rw [hiota, map_zsmul, hgen, smul_zero]
    apply LinearMap.ext
    intro c
    have hc := CategoryTheory.ConcreteCategory.congr_hom hmorph c
    change (show Module.Dual ℤ (C.X 2) from φ) ((C.d (2 + 1) 2).hom c) = 0
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      ModuleCat.hom_zero, LinearMap.zero_apply] using hc
  have hφ : (B.d 2 3).hom φ = 0 := by
    simpa only [Nat.reduceAdd] using hφ'
  have hmem : φ ∈ LinearMap.ker (B.d 2 3).hom := hφ
  change φ ∈ LinearMap.ker (B.sc' 1 2 3).g.hom at hmem
  rw [← hrange] at hmem
  obtain ⟨ψ, hψ⟩ := hmem
  classical
  let G : cech_simplex n 1 → ℤ := fun σ ↦
    if hs : ∃ p, ∀ x, σ x ∈ U p then
      (show Module.Dual ℤ (C.X 1) from ψ)
        ((((AlgebraicTopology.Singular.coverSmallSingularSubcomplex Y U : SSet).chainComplexXCofan
        (ModuleCat.of ℤ ℤ) 1).inj
          ⟨(Y.toSSetObjEquiv _).symm σ, by
            exact (cech_mem_coverSmall_iff n 1 U _).mp hs⟩).hom 1)
    else 0
  refine ⟨G, ?_⟩
  intro σ hs
  let τ : (AlgebraicTopology.Singular.coverSmallSingularSubcomplex Y U).obj (.op ⟨2⟩) :=
    ⟨(Y.toSSetObjEquiv _).symm σ, by
      exact (cech_mem_coverSmall_iff n 2 U _).mp hs⟩
  have hface (i : Fin 3) : ∃ p, ∀ x, cech_face n 1 i σ x ∈ U p := by
    obtain ⟨p, hp⟩ := hs
    exact ⟨p, fun x ↦ hp _⟩
  have hψeval := LinearMap.congr_fun hψ
    ((((AlgebraicTopology.Singular.coverSmallSingularSubcomplex Y U : SSet).chainComplexXCofan
      (ModuleCat.of ℤ ℤ) 2).inj τ).hom 1)
  rw [cechSmallCochain_iota] at hψeval
  change (show Module.Dual ℤ (C.X 2) from (B.d 1 2).hom ψ)
      ((((AlgebraicTopology.Singular.coverSmallSingularSubcomplex Y U : SSet).chainComplexXCofan
        (ModuleCat.of ℤ ℤ) 2).inj τ).hom 1) =
    F (Y.toSSetObjEquiv _ τ.1) at hψeval
  have hψeval' : (show Module.Dual ℤ (C.X 2) from (B.d 1 2).hom ψ)
      ((((AlgebraicTopology.Singular.coverSmallSingularSubcomplex Y U : SSet).chainComplexXCofan
        (ModuleCat.of ℤ ℤ) 2).inj τ).hom 1) = F σ := by
    simpa only [τ, Equiv.apply_symm_apply] using hψeval
  change ∑ i : Fin 3, (-1 : ℤ) ^ i.val * G (cech_face n 1 i σ) = F σ
  rw [← hψeval']
  rw [show ((AlgebraicTopology.Singular.coverSmallSingularSubcomplex Y U : SSet).chainComplexXCofan
      (ModuleCat.of ℤ ℤ) 2).inj τ =
    (AlgebraicTopology.Singular.coverSmallSingularSubcomplex Y U : SSet).ιChainComplex
      (R := ModuleCat.of ℤ ℤ) τ from rfl]
  change _ = (show Module.Dual ℤ (C.X 1) from ψ) ((C.d 2 1).hom
    (((AlgebraicTopology.Singular.coverSmallSingularSubcomplex Y U : SSet).ιChainComplex
      (R := ModuleCat.of ℤ ℤ) τ).hom 1))
  have hd := CategoryTheory.ConcreteCategory.congr_hom
    (SSet.ιChainComplex_d
      (AlgebraicTopology.Singular.coverSmallSingularSubcomplex Y U : SSet)
      (R := ModuleCat.of ℤ ℤ) τ) 1
  have hstep : (C.d 2 1).hom
      (((AlgebraicTopology.Singular.coverSmallSingularSubcomplex Y U : SSet).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) τ).hom 1) =
      (∑ i : Fin 3, (-1 : ℤ) ^ i.val •
        (AlgebraicTopology.Singular.coverSmallSingularSubcomplex Y U : SSet).ιChainComplex
          (R := ModuleCat.of ℤ ℤ)
          ((AlgebraicTopology.Singular.coverSmallSingularSubcomplex Y U : SSet).δ i τ)).hom 1 := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
    exact hd
  rw [hstep]
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (-1 : ℤ) ^ i.val * G (cech_face n 1 i σ) =
    (show Module.Dual ℤ (C.X 1) from ψ)
      (((-1 : ℤ) ^ i.val) •
        ((AlgebraicTopology.Singular.coverSmallSingularSubcomplex Y U : SSet).ιChainComplex
          (R := ModuleCat.of ℤ ℤ)
          ((AlgebraicTopology.Singular.coverSmallSingularSubcomplex Y U : SSet).δ i τ)).hom 1)
  rw [map_zsmul]
  simp only [smul_eq_mul]
  simp only [G, dif_pos (hface i)]
  congr 2

private theorem cech_face_face (n q : ℕ) (σ : cech_simplex n (q + 2))
    (i j : Fin (q + 2)) (H : i ≤ j) :
    cech_face n q i (cech_face n (q + 1) j.succ σ) =
      cech_face n q j (cech_face n (q + 1) i.castSucc σ) := by
  simp only [cech_face, ContinuousMap.comp_assoc]
  congr 1
  have hm := congrArg (fun f => SimplexCategory.toTop₀.map f)
    (SimplexCategory.δ_comp_δ H)
  change TopCat.Hom.hom (CategoryTheory.CategoryStruct.comp
      (SimplexCategory.toTop₀.map (SimplexCategory.δ i))
      (SimplexCategory.toTop₀.map (SimplexCategory.δ j.succ))) =
    TopCat.Hom.hom (CategoryTheory.CategoryStruct.comp
      (SimplexCategory.toTop₀.map (SimplexCategory.δ j))
      (SimplexCategory.toTop₀.map (SimplexCategory.δ i.castSucc)))
  rw [← SimplexCategory.toTop₀.map_comp, ← SimplexCategory.toTop₀.map_comp]
  exact congrArg TopCat.Hom.hom hm

private theorem cech_d_sq_zero_zero (n : ℕ) (F : cech_simplex n 0 → ℤ) :
    cech_d n 1 (cech_d n 0 F) = fun _ ↦ 0 := by
  funext σ
  have h₁ : cech_face n 0 0 (cech_face n 1 0 σ) =
      cech_face n 0 0 (cech_face n 1 1 σ) := by
    simp only [cech_face, ContinuousMap.comp_assoc]
    congr 1
    ext x
    change Convexity.StdSimplex.map _ (Convexity.StdSimplex.map _ x) =
      Convexity.StdSimplex.map _ (Convexity.StdSimplex.map _ x)
    rw [← Convexity.StdSimplex.map_comp, ← Convexity.StdSimplex.map_comp]
    congr 1
  have h₂ : cech_face n 0 1 (cech_face n 1 0 σ) =
      cech_face n 0 0 (cech_face n 1 2 σ) := by
    simp only [cech_face, ContinuousMap.comp_assoc]
    congr 1
    ext x
    change Convexity.StdSimplex.map _ (Convexity.StdSimplex.map _ x) =
      Convexity.StdSimplex.map _ (Convexity.StdSimplex.map _ x)
    rw [← Convexity.StdSimplex.map_comp, ← Convexity.StdSimplex.map_comp]
    congr 1
    funext j
    fin_cases j
    rfl
  have h₃ : cech_face n 0 1 (cech_face n 1 1 σ) =
      cech_face n 0 1 (cech_face n 1 2 σ) := by
    simp only [cech_face, ContinuousMap.comp_assoc]
    congr 1
    ext x
    change Convexity.StdSimplex.map _ (Convexity.StdSimplex.map _ x) =
      Convexity.StdSimplex.map _ (Convexity.StdSimplex.map _ x)
    rw [← Convexity.StdSimplex.map_comp, ← Convexity.StdSimplex.map_comp]
    congr 1
    funext j
    fin_cases j
    rfl
  simp [cech_d, Fin.sum_univ_three, Fin.sum_univ_two, h₁, h₂, h₃]
  ring

private theorem cech_d_sq_zero_one (n : ℕ) (F : cech_simplex n 1 → ℤ) :
    cech_d n 2 (cech_d n 1 F) = fun _ ↦ 0 := by
  funext σ
  have e00 := cech_face_face n 1 σ (0 : Fin 3) (0 : Fin 3) (by decide)
  have e01 := cech_face_face n 1 σ (0 : Fin 3) (1 : Fin 3) (by decide)
  have e02 := cech_face_face n 1 σ (0 : Fin 3) (2 : Fin 3) (by decide)
  have e11 := cech_face_face n 1 σ (1 : Fin 3) (1 : Fin 3) (by decide)
  have e12 := cech_face_face n 1 σ (1 : Fin 3) (2 : Fin 3) (by decide)
  have e22 := cech_face_face n 1 σ (2 : Fin 3) (2 : Fin 3) (by decide)
  norm_num [Fin.succ, Fin.castSucc] at e00 e01 e02 e11 e12 e22
  simp [cech_d, Fin.sum_univ_four, Fin.sum_univ_three, e00, e01, e02, e11, e12, e22]
  ring

private theorem cech_d_sub (n q : ℕ) (F G : cech_simplex n q → ℤ)
    (σ : cech_simplex n (q + 1)) :
    cech_d n q (fun τ ↦ F τ - G τ) σ = cech_d n q F σ - cech_d n q G σ := by
  simp only [cech_d, mul_sub, Finset.sum_sub_distrib]

/-- Integral two-cocycles on a convex open cover of affine space have integral primitives.
Source: Bott--Tu, §§8--9, the Čech double complex; the degree-two diagram chase
using `cech_horizontal_exact`, `cech_horizontal_glue`, `cech_vertical_one`,
`cech_vertical_zero`, and `cech_small_two`. -/
theorem cech_integral_primitive_aux (n : ℕ) (V : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hV : ∀ p, IsOpen (V p)) (hcover : ∀ p, p ∈ V p)
    (hv : ∀ p, Convex ℝ (V p))
    (c : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℤ)
    (hc : ∀ p q r s z, z ∈ V p ∩ V q ∩ V r ∩ V s →
      c q r s - c p r s + c p q s - c p q r = 0) :
    ∃ k : (Fin n → ℂ) → (Fin n → ℂ) → ℤ,
      ∀ p q r z, z ∈ V p ∩ V q ∩ V r →
        k q r - k p r + k p q = c p q r := by
  let C : (Fin 3 → (Fin n → ℂ)) → cech_simplex n 0 → ℤ :=
    fun t _ ↦ c (t 0) (t 1) (t 2)
  obtain ⟨b, hb⟩ := cech_horizontal_exact_aux n 1 0 V C (by
    intro t σ hσ
    have hz := hc (t 0) (t 1) (t 2) (t 3) (σ default) (by
      exact ⟨⟨⟨hσ default 0, hσ default 1⟩, hσ default 2⟩, hσ default 3⟩)
    simp [C, cech_h, Fin.sum_univ_four, Fin.succAbove]
    omega)
  let db : (Fin 2 → (Fin n → ℂ)) → cech_simplex n 1 → ℤ :=
    fun t σ ↦ cech_d n 0 (b t) σ
  obtain ⟨a, ha⟩ := cech_horizontal_exact_aux n 0 1 V db (by
    intro t σ hσ
    have hcomm : cech_h n 1 db t σ = cech_d n 0 (cech_h n 1 b t) σ := by
      simp only [db, cech_h, cech_d]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hcomm]
    have hface (i : Fin 2) : cech_h n 1 b t (cech_face n 0 i σ) = C t (cech_face n 0 i σ) := by
      apply hb
      intro x j
      exact hσ _ j
    simp only [cech_d]
    rw [Fin.sum_univ_two]
    rw [hface 0, hface 1]
    simp [C])
  let da : (Fin 1 → (Fin n → ℂ)) → cech_simplex n 2 → ℤ :=
    fun t σ ↦ cech_d n 1 (a t) σ
  obtain ⟨F, hF⟩ := cech_horizontal_glue_aux n 2 V da (by
    intro t σ hσ
    have hcomm : cech_h n 0 da t σ = cech_d n 1 (cech_h n 0 a t) σ := by
      simp only [da, cech_h, cech_d]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hcomm]
    calc
      cech_d n 1 (cech_h n 0 a t) σ = cech_d n 1 (db t) σ := by
        unfold cech_d
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        apply ha
        intro x j
        exact hσ _ j
      _ = 0 := congrFun (cech_d_sq_zero_zero n (b t)) σ)
  have hFclosed : ∀ σ, (∃ p, ∀ x, σ x ∈ V p) → cech_d n 2 F σ = 0 := by
    intro σ hσ
    obtain ⟨p, hp⟩ := hσ
    let t : Fin 1 → (Fin n → ℂ) := fun _ ↦ p
    calc
      cech_d n 2 F σ = cech_d n 2 (a t |> cech_d n 1) σ := by
        unfold cech_d
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        apply hF t
        intro x j
        exact hp _
      _ = 0 := congrFun (cech_d_sq_zero_one n (a t)) σ
  obtain ⟨B, hB⟩ := cech_small_two_aux n V hV hcover F hFclosed
  let A : (Fin n → ℂ) → cech_simplex n 1 → ℤ :=
    fun p σ ↦ a (fun _ ↦ p) σ - B σ
  have hAclosed : ∀ p σ, (∀ x, σ x ∈ V p) → cech_d n 1 (A p) σ = 0 := by
    intro p σ hσ
    let t : Fin 1 → (Fin n → ℂ) := fun _ ↦ p
    have haF : cech_d n 1 (a t) σ = F σ := by
      symm
      apply hF t σ
      intro x i
      exact hσ x
    have hBF : cech_d n 1 B σ = F σ := by
      apply hB σ
      exact ⟨p, hσ⟩
    change cech_d n 1 (fun τ ↦ a t τ - B τ) σ = 0
    rw [cech_d_sub]
    rw [haF, hBF]
    exact sub_self _
  choose f hf using fun p ↦ cech_vertical_one_aux n (V p) (hv p) (A p) (hAclosed p)
  let g : (Fin 2 → (Fin n → ℂ)) → cech_simplex n 0 → ℤ :=
    fun t σ ↦ b t σ - (f (t 1) σ - f (t 0) σ)
  have hgclosed : ∀ t σ, (∀ x i, σ x ∈ V (t i)) → cech_d n 0 (g t) σ = 0 := by
    intro t σ hσ
    have hfp : cech_d n 0 (f (t 0)) σ = A (t 0) σ :=
      hf (t 0) σ (fun x ↦ hσ x 0)
    have hfq : cech_d n 0 (f (t 1)) σ = A (t 1) σ :=
      hf (t 1) σ (fun x ↦ hσ x 1)
    have hab : a (fun _ ↦ t 1) σ - a (fun _ ↦ t 0) σ = db t σ := by
      have := ha t σ hσ
      have ht0 : t ∘ (0 : Fin 2).succAbove = fun _ ↦ t 1 := by
        funext i
        fin_cases i
        rfl
      have hts : t ∘ Fin.succ = fun _ ↦ t 1 := by
        funext i
        fin_cases i
        rfl
      have ht1 : t ∘ (1 : Fin 2).succAbove = fun _ ↦ t 0 := by
        funext i
        fin_cases i
        rfl
      simpa [cech_h, Fin.sum_univ_two, ht0, ht1, hts, sub_eq_add_neg] using this
    change cech_d n 0 (fun τ ↦ b t τ - (f (t 1) τ - f (t 0) τ)) σ = 0
    rw [cech_d_sub, cech_d_sub]
    rw [hfp, hfq]
    change db t σ - ((a (fun _ ↦ t 1) σ - B σ) -
      (a (fun _ ↦ t 0) σ - B σ)) = 0
    rw [← hab]
    ring
  choose K hK using fun t : Fin 2 → (Fin n → ℂ) ↦
    cech_vertical_zero_aux n (V (t 0) ∩ V (t 1)) ((hv (t 0)).inter (hv (t 1)))
      (g t) (by
        intro σ hσ
        apply hgclosed t σ
        intro x i
        fin_cases i
        · exact (hσ x).1
        · exact (hσ x).2)
  let k : (Fin n → ℂ) → (Fin n → ℂ) → ℤ :=
    fun p q ↦ K ![p, q]
  refine ⟨k, ?_⟩
  intro p q r z hz
  let σ : cech_simplex n 0 := ContinuousMap.const _ z
  let tpq : Fin 2 → (Fin n → ℂ) := ![p, q]
  let tpr : Fin 2 → (Fin n → ℂ) := ![p, r]
  let tqr : Fin 2 → (Fin n → ℂ) := ![q, r]
  have hpq : g tpq σ = K tpq := hK tpq σ (by
    intro x
    exact ⟨hz.1.1, hz.1.2⟩)
  have hpr : g tpr σ = K tpr := hK tpr σ (by
    intro x
    exact ⟨hz.1.1, hz.2⟩)
  have hqr : g tqr σ = K tqr := hK tqr σ (by
    intro x
    exact ⟨hz.1.2, hz.2⟩)
  have hbc : b ![p, q] σ - b ![p, r] σ + b ![q, r] σ = c p q r := by
    have h := hb ![p, q, r] σ (by
      intro x i
      fin_cases i
      · exact hz.1.1
      · exact hz.1.2
      · exact hz.2)
    have ht0 : ![p, q, r] ∘ (0 : Fin 3).succAbove = ![q, r] := by
      funext i
      fin_cases i <;> rfl
    have hts : ![p, q, r] ∘ Fin.succ = ![q, r] := by
      funext i
      fin_cases i <;> rfl
    have ht1 : ![p, q, r] ∘ (1 : Fin 3).succAbove = ![p, r] := by
      funext i
      fin_cases i <;> rfl
    have ht2 : ![p, q, r] ∘ (2 : Fin 3).succAbove = ![p, q] := by
      funext i
      fin_cases i <;> rfl
    have h' : b ![q, r] σ - b ![p, r] σ + b ![p, q] σ = c p q r := by
      simpa [C, cech_h, Fin.sum_univ_three, ht0, ht1, ht2, hts,
        sub_eq_add_neg] using h
    omega
  change K tqr - K tpr + K tpq = c p q r
  rw [← hqr, ← hpr, ← hpq]
  change (b ![q, r] σ - (f r σ - f q σ)) -
      (b ![p, r] σ - (f r σ - f p σ)) +
      (b ![p, q] σ - (f q σ - f p σ)) = c p q r
  rw [← hbc]
  ring

/-- Subtracting the integral primitive makes the logarithms additive without changing exponentials.
Source: Gunning--Rossi, VIII, the exponential sequence; direct cancellation of the defect. -/
theorem cech_correct_logarithms_aux (n : ℕ) (V : (Fin n → ℂ) → Set (Fin n → ℂ))
    (u b : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (k : (Fin n → ℂ) → (Fin n → ℂ) → ℤ)
    (hb : ∀ p q, AnalyticOnNhd ℂ (b p q) (V p ∩ V q))
    (he : ∀ p q z, z ∈ V p ∩ V q → Complex.exp (b p q z) = u p q z)
    (hd : ∀ p q r z, z ∈ V p ∩ V q ∩ V r →
      b q r z - b p r z + b p q z =
        (2 * Real.pi * Complex.I) * ((k q r - k p r + k p q : ℤ) : ℂ)) :
    (∀ p q, AnalyticOnNhd ℂ (cech_correct n b k p q) (V p ∩ V q)) ∧
      (∀ p z, z ∈ V p → cech_correct n b k p p z = 0) ∧
      (∀ p q r z, z ∈ V p ∩ V q ∩ V r →
        cech_correct n b k p q z + cech_correct n b k q r z = cech_correct n b k p r z) ∧
      (∀ p q z, z ∈ V p ∩ V q → Complex.exp (cech_correct n b k p q z) = u p q z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p q
    exact (hb p q).sub analyticOnNhd_const
  · intro p z hz
    have h := hd p p p z ⟨⟨hz, hz⟩, hz⟩
    simp only [cech_correct]
    simp only [sub_self, zero_add] at h
    exact sub_eq_zero.mpr h
  · intro p q r z hz
    have h := hd p q r z hz
    simp only [cech_correct]
    push_cast at h
    linear_combination h
  · intro p q z hz
    rw [cech_correct, Complex.exp_sub, he p q z hz]
    have hperiod :
        Complex.exp ((2 * Real.pi * Complex.I) * (k p q : ℂ)) = 1 := by
      rw [show (2 * Real.pi * Complex.I) * (k p q : ℂ) =
          (k p q : ℂ) * (2 * Real.pi * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I (k p q)
    rw [hperiod, div_one]

/-- A multiplicative cocycle has an additive logarithmic lift after refinement.
Source: Gunning--Rossi, VIII, exponential sequence and Cousin II.
This is the exact type of `bh7_exponential_trivialization_aux`. -/
theorem cech_exponential_trivialization_aux (n : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hU : ∀ p, IsOpen (U p)) (hcover : ∀ p, p ∈ U p)
    (u : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (hu : ∀ p q, AnalyticOnNhd ℂ (u p q) (U p ∩ U q))
    (hun : ∀ p q z, z ∈ U p ∩ U q → u p q z ≠ 0)
    (hdiag : ∀ p z, z ∈ U p → u p p z = 1)
    (hcocycle : ∀ p q r z, z ∈ U p ∩ U q ∩ U r → u p q z * u q r z = u p r z) :
    ∃ (V : (Fin n → ℂ) → Set (Fin n → ℂ)) (r : (Fin n → ℂ) → (Fin n → ℂ))
      (a : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ),
      (∀ p, IsOpen (V p)) ∧ (∀ p, p ∈ V p) ∧ (∀ p, V p ⊆ U (r p)) ∧
      (∀ p q, AnalyticOnNhd ℂ (a p q) (V p ∩ V q)) ∧
      (∀ p z, z ∈ V p → a p p z = 0) ∧
      (∀ p q t z, z ∈ V p ∩ V q ∩ V t → a p q z + a q t z = a p t z) ∧
      (∀ p q z, z ∈ V p ∩ V q → Complex.exp (a p q z) = u (r p) (r q) z) := by
  have hdiag_used := hdiag
  clear hdiag_used
  obtain ⟨V, hV, hp, hv, hVU⟩ := cech_convex_refinement_aux n U hU hcover
  have huV : ∀ p q, AnalyticOnNhd ℂ (u p q) (V p ∩ V q) := by
    intro p q
    exact (hu p q).mono (inter_subset_inter (hVU p) (hVU q))
  have hunV : ∀ p q z, z ∈ V p ∩ V q → u p q z ≠ 0 := by
    intro p q z hz
    exact hun p q z ⟨hVU p hz.1, hVU q hz.2⟩
  have hconv : ∀ p q, Convex ℝ (V p ∩ V q) := by
    intro p q
    exact (hv p).inter (hv q)
  choose b hb he using fun p q ↦
    cech_convex_log_aux n (V p ∩ V q) ((hV p).inter (hV q)) (hconv p q)
      (u p q) (huV p q) (hunV p q)
  have hcocycleV : ∀ p q r z, z ∈ V p ∩ V q ∩ V r →
      u p q z * u q r z = u p r z := by
    intro p q r z hz
    exact hcocycle p q r z ⟨⟨hVU p hz.1.1, hVU q hz.1.2⟩, hVU r hz.2⟩
  obtain ⟨c, hd, hc⟩ :=
    cech_integer_defect_aux n V hV hv u b hb he hcocycleV
  obtain ⟨k, hk⟩ := cech_integral_primitive_aux n V hV hp hv c hc
  have hdefect : ∀ p q r z, z ∈ V p ∩ V q ∩ V r →
      b q r z - b p r z + b p q z =
        (2 * Real.pi * Complex.I) * ((k q r - k p r + k p q : ℤ) : ℂ) := by
    intro p q r z hz
    rw [hd p q r z hz, hk p q r z hz]
  obtain ⟨ha, hzero, hadd, hexp⟩ :=
    cech_correct_logarithms_aux n V u b k hb he hdefect
  exact ⟨V, id, cech_correct n b k, hV, hp, hVU, ha, hzero, hadd, hexp⟩

end HodgeLean.Foundations
