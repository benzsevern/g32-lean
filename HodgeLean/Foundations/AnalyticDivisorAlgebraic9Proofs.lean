import HodgeLean.Foundations.AnalyticDivisorAlgebraic8

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic9

open Polynomial
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7

theorem spec_zero_mem_closure_ne_zero_aux {n : ℕ}
    (h : (Fin n → ℂ) → ℂ) (hh : AnalyticAt ℂ h 0)
    (hnz : (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) h, ⟨h, hh, rfl⟩⟩ :
      AnalyticGerm n) ≠ 0) :
    (0 : Fin n → ℂ) ∈ closure {x | h x ≠ 0} := by
  rw [mem_closure_iff]
  intro U hU h0
  by_contra hUhn
  apply hnz
  apply Subtype.ext
  apply Filter.EventuallyEq.germ_eq
  filter_upwards [hU.mem_nhds h0] with x hx
  apply Classical.byContradiction
  intro hne
  exact hUhn ⟨x, hx, hne⟩

theorem spec_zero_mem_closure_two_ne_zero_aux {n : ℕ}
    (h₁ h₂ : (Fin n → ℂ) → ℂ) (hh₁ : AnalyticAt ℂ h₁ 0)
    (hh₂ : AnalyticAt ℂ h₂ 0)
    (hnz₁ : (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) h₁, ⟨h₁, hh₁, rfl⟩⟩ :
      AnalyticGerm n) ≠ 0)
    (hnz₂ : (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) h₂, ⟨h₂, hh₂, rfl⟩⟩ :
      AnalyticGerm n) ≠ 0) :
    (0 : Fin n → ℂ) ∈ closure {x | h₁ x ≠ 0 ∧ h₂ x ≠ 0} := by
  have hprod := spec_zero_mem_closure_ne_zero_aux (fun x ↦ h₁ x * h₂ x) (hh₁.mul hh₂) (by
    change
      (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) h₁, ⟨h₁, hh₁, rfl⟩⟩ :
          AnalyticGerm n) *
        (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) h₂, ⟨h₂, hh₂, rfl⟩⟩ :
          AnalyticGerm n) ≠ 0
    exact mul_ne_zero hnz₁ hnz₂)
  simpa only [mul_ne_zero_iff] using hprod

open Lean Elab Term in
syntax "gaga6Private% " str : term

open Lean Elab Term in
elab_rules : term
  | `(gaga6Private% $s:str) =>
      let n := (s.getString.splitOn ".").foldl (fun n p =>
        match p.toNat? with | some k => Name.num n k | none => Name.str n p) Name.anonymous
      return mkConst n

private abbrev gaga9CanonicalEmbedding :=
  gaga6Private% "_private.HodgeLean.Foundations.AnalyticDivisorAlgebraic6Proofs.0.HodgeLean.Foundations.AnalyticDivisorAlgebraic6.canonicalEmbedding"

private abbrev gaga9CanonicalEmbeddingSpec :=
  gaga6Private% "_private.HodgeLean.Foundations.AnalyticDivisorAlgebraic6Proofs.0.HodgeLean.Foundations.AnalyticDivisorAlgebraic6.canonicalEmbedding_spec"

private abbrev gaga9CanonicalEmbeddingDvdIff :=
  gaga6Private% "_private.HodgeLean.Foundations.AnalyticDivisorAlgebraic6Proofs.0.HodgeLean.Foundations.AnalyticDivisorAlgebraic6.canonicalEmbedding_dvd_iff"

private abbrev gaga9SplitGermEquiv :=
  gaga6Private% "_private.HodgeLean.Foundations.AnalyticDivisorAlgebraic6Proofs.0.HodgeLean.Foundations.AnalyticDivisorAlgebraic6.splitGermEquiv"

private abbrev gaga9ProductPolynomial :=
  gaga6Private% "_private.HodgeLean.Foundations.AnalyticDivisorAlgebraic6Proofs.0.HodgeLean.Foundations.AnalyticDivisorAlgebraic6.productPolynomial"

private abbrev gaga9ProductPolynomialSum :=
  gaga6Private% "_private.HodgeLean.Foundations.AnalyticDivisorAlgebraic6Proofs.0.HodgeLean.Foundations.AnalyticDivisorAlgebraic6.productPolynomial_sum"

private abbrev gaga9WeierstrassRepresentative :=
  gaga6Private% "_private.HodgeLean.Foundations.AnalyticDivisorAlgebraic6Proofs.0.HodgeLean.Foundations.AnalyticDivisorAlgebraic6.weierstrass_representative"

private theorem gaga9_weierstrass_division {n : ℕ}
    (P : Polynomial (AnalyticGerm n)) (hP : IsWeierstrassPolynomial P)
    (g : AnalyticGerm (n + 1)) :
    ∃ (q : AnalyticGerm (n + 1)) (r : Polynomial (AnalyticGerm n)),
      g = q * gaga9CanonicalEmbedding n P + gaga9CanonicalEmbedding n r ∧
        r.natDegree < P.natDegree := by
  let e := gaga9SplitGermEquiv n
  obtain ⟨f, hf, hfg⟩ := (e g).2
  obtain ⟨a, ha, hPa⟩ := gaga9WeierstrassRepresentative hP
  obtain ⟨q, hq, b, hb, hdiv⟩ :=
    HodgeLean.Foundations.AnalyticDivisorAlgebraic4.spec_weierstrass_division
      hf (fun j ↦ (ha j).1) (fun j ↦ (ha j).2)
  let qb : ProductAnalyticGerm n := ⟨↑q, q, hq, rfl⟩
  let qg : AnalyticGerm (n + 1) := e.symm qb
  let bg : Fin P.natDegree → AnalyticGerm n := fun j ↦ ⟨↑(b j), b j, hb j, rfl⟩
  let r : Polynomial (AnalyticGerm n) := ∑ j, C (bg j) * X ^ (j : ℕ)
  refine ⟨qg, r, ?_, ?_⟩
  · apply e.injective
    simp only [qg, map_add, map_mul, RingEquiv.apply_symm_apply, gaga9CanonicalEmbedding]
    have hc : ∀ Q, e (gaga9CanonicalEmbedding n Q) = gaga9ProductPolynomial n Q :=
      fun Q ↦ by
        change e (e.symm (gaga9ProductPolynomial n Q)) = _
        exact e.apply_symm_apply _
    rw [hc, hc]
    change e g = qb * gaga9ProductPolynomial n P + gaga9ProductPolynomial n r
    apply Subtype.ext
    change (e g).1 = qb.1 * (gaga9ProductPolynomial n P).1 +
      (gaga9ProductPolynomial n r).1
    rw [← hfg, hPa]
    rw [gaga9ProductPolynomialSum bg b (fun _ ↦ rfl)]
    exact Filter.Germ.coe_eq.mpr hdiv
  · by_cases hr : r = 0
    · simp [hr, hP.2.1]
    apply (natDegree_lt_iff_degree_lt hr).2
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j _ ↦ ?_
    exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by exact_mod_cast j.2)

theorem spec_weierstrass_resultant_ne_zero_aux {n : ℕ}
    (ι : Polynomial (AnalyticGerm n) →+* AnalyticGerm (n + 1))
    (hι : IsWeierstrassEmbedding ι) (P : Polynomial (AnalyticGerm n))
    (hP : IsWeierstrassPolynomial P) (g : AnalyticGerm (n + 1))
    (hPg : IsCoprime (ι P) g) :
    ∃ (q : AnalyticGerm (n + 1)) (r : Polynomial (AnalyticGerm n)),
      g = q * ι P + ι r ∧ r.natDegree < P.natDegree ∧
        IsCoprime P r ∧ P.resultant r ≠ 0 := by
  have hi : ι = gaga9CanonicalEmbedding n :=
    weierstrassEmbedding_unique hι (gaga9CanonicalEmbeddingSpec n)
  subst ι
  obtain ⟨q, r, hgr, hrdeg⟩ := gaga9_weierstrass_division P hP g
  have hir : IsCoprime (gaga9CanonicalEmbedding n P) (gaga9CanonicalEmbedding n r) := by
    rcases hPg with ⟨a, b, hab⟩
    refine ⟨a + b * q, b, ?_⟩
    calc
      (a + b * q) * gaga9CanonicalEmbedding n P +
          b * gaga9CanonicalEmbedding n r =
          a * gaga9CanonicalEmbedding n P + b * g := by rw [hgr]; ring
      _ = 1 := hab
  have hPr : IsCoprime P r := by
    rcases hir with ⟨a, b, hab⟩
    obtain ⟨qa, ra, hara, -⟩ := gaga9_weierstrass_division P hP a
    obtain ⟨qb, rb, hbrb, -⟩ := gaga9_weierstrass_division P hP b
    have hd : gaga9CanonicalEmbedding n P ∣
        gaga9CanonicalEmbedding n (1 - (ra * P + rb * r)) := by
      refine ⟨qa * gaga9CanonicalEmbedding n P + qb * gaga9CanonicalEmbedding n r, ?_⟩
      simp only [map_sub, map_one, map_add, map_mul]
      rw [hara, hbrb] at hab
      linear_combination -hab
    obtain ⟨t, ht⟩ := (gaga9CanonicalEmbeddingDvdIff hP).mp hd
    refine ⟨ra + t, rb, ?_⟩
    linear_combination -ht
  refine ⟨q, r, hgr, hrdeg, hPr, ?_⟩
  letI := spec_analyticGerm_ufd n
  letI : IsDomain (AnalyticGerm n) := {}
  exact resultant_ne_zero P r hPr

theorem spec_resultant_specialization_avoids_common_root_aux {n : ℕ}
    (P g : Polynomial (AnalyticGerm n))
    (a b : ℕ → (Fin n → ℂ) → ℂ) (R : (Fin n → ℂ) → ℂ)
    (U : Set (Fin n → ℂ)) (hU : U ∈ nhds (0 : Fin n → ℂ))
    (ha : ∀ j, AnalyticOnNhd ℂ (a j) U)
    (hb : ∀ j, AnalyticOnNhd ℂ (b j) U) (hR : AnalyticOnNhd ℂ R U)
    (haP : ∀ j, (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j),
      ⟨a j, (ha j 0 (mem_of_mem_nhds hU)), rfl⟩⟩ : AnalyticGerm n) =
        P.coeff j)
    (hbg : ∀ j, (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (b j),
      ⟨b j, (hb j 0 (mem_of_mem_nhds hU)), rfl⟩⟩ : AnalyticGerm n) =
        g.coeff j)
    (hRR : (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) R,
      ⟨R, hR 0 (mem_of_mem_nhds hU), rfl⟩⟩ : AnalyticGerm n) =
        P.resultant g)
    (hfibre : ∀ x ∈ U, P.sum (fun j _ ↦ monomial j (a j x)) ≠ 0)
    (hcompat : ∀ x ∈ U, R x = (P.sum fun j _ ↦ monomial j (a j x)).resultant
      (g.sum fun j _ ↦ monomial j (b j x)))
    (x : Fin n → ℂ) (hxU : x ∈ U) (hx : R x ≠ 0) (w : ℂ) :
    (P.sum fun j _ ↦ monomial j (a j x)).eval w ≠ 0 ∨
      (g.sum fun j _ ↦ monomial j (b j x)).eval w ≠ 0 := by
  let f := P.sum fun j _ ↦ monomial j (a j x)
  let q := g.sum fun j _ ↦ monomial j (b j x)
  have hc : IsCoprime f q := by
    by_contra hc
    apply hx
    rw [hcompat x hxU]
    exact (resultant_eq_zero_iff (f := f) (g := q)).2
      ⟨Or.inl (hfibre x hxU), hc⟩
  rcases hc with ⟨u, v, huv⟩
  by_contra h
  push Not at h
  have h₁ := h.1
  have h₂ := h.2
  change f.eval w = 0 at h₁
  change q.eval w = 0 at h₂
  have he := congrArg (Polynomial.eval w) huv
  simp [h₁, h₂] at he

theorem spec_discriminant_specialization_simple_root_aux {n : ℕ}
    (P : Polynomial (AnalyticGerm n)) (a : ℕ → (Fin n → ℂ) → ℂ)
    (D : (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ))
    (hU : U ∈ nhds (0 : Fin n → ℂ)) (ha : ∀ j, AnalyticOnNhd ℂ (a j) U)
    (hD : AnalyticOnNhd ℂ D U)
    (haP : ∀ j, (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j),
      ⟨a j, ha j 0 (mem_of_mem_nhds hU), rfl⟩⟩ : AnalyticGerm n) =
        P.coeff j)
    (hDD : (⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) D,
      ⟨D, hD 0 (mem_of_mem_nhds hU), rfl⟩⟩ : AnalyticGerm n) = P.discr)
    (hfibre : ∀ x ∈ U, P.sum (fun j _ ↦ monomial j (a j x)) ≠ 0)
    (hcompat : ∀ x ∈ U, D x = (P.sum fun j _ ↦ monomial j (a j x)).discr)
    (x : Fin n → ℂ) (hxU : x ∈ U) (hx : D x ≠ 0)
    (w : ℂ) (hw : (P.sum fun j _ ↦ monomial j (a j x)).eval w = 0) :
    (P.sum fun j _ ↦ monomial j (a j x)).derivative.eval w ≠ 0 := by
  let f := P.sum fun j _ ↦ monomial j (a j x)
  have hf : f ≠ 0 := hfibre x hxU
  have hpos : 0 < f.natDegree := by
    apply Nat.pos_of_ne_zero
    intro hdeg
    have hw' := hw
    change f.eval w = 0 at hw'
    rw [eq_C_of_natDegree_eq_zero hdeg, eval_C] at hw'
    apply hf
    rw [eq_C_of_natDegree_eq_zero hdeg, hw', C_0]
  have hres : f.resultant f.derivative ≠ 0 := by
    change resultant f f.derivative f.natDegree f.derivative.natDegree ≠ 0
    rw [natDegree_derivative]
    rw [resultant_deriv (natDegree_pos_iff_degree_pos.mp hpos)]
    exact mul_ne_zero (mul_ne_zero (neg_one_pow_ne_zero _) (leadingCoeff_ne_zero.mpr hf))
      (by simpa [hcompat x hxU] using hx)
  have hc : IsCoprime f f.derivative := by
    by_contra hc
    apply hres
    exact (resultant_eq_zero_iff (f := f) (g := f.derivative)).2
      ⟨Or.inl hf, hc⟩
  rcases hc with ⟨u, v, huv⟩
  intro hd
  have hw' := hw
  have hd' := hd
  change f.eval w = 0 at hw'
  change f.derivative.eval w = 0 at hd'
  have he := congrArg (Polynomial.eval w) huv
  simp [hw', hd'] at he

open HodgeLean.Foundations.AnalyticDivisorAlgebraic8
open HodgeLean.Foundations.AnalyticDivisorAlgebraic4
open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
open Set Filter Topology

private theorem clean_germ_isUnit_iff {n : ℕ} (g : ProductAnalyticGerm n) :
    IsUnit g ↔ g.1.value ≠ 0 := by
  constructor
  · intro h
    exact (h.map ((Filter.Germ.valueRingHom (X := (Fin n → ℂ) × ℂ) (E := ℂ)).comp
      (productAnalyticGermSubring n).subtype)).ne_zero
  · obtain ⟨f, hf, hfg⟩ := g.2
    intro h
    have hf0 : f 0 ≠ 0 := by
      rw [← hfg, Filter.Germ.value_ofFun] at h
      exact h
    let q : ProductAnalyticGerm n := ⟨↑(fun z ↦ (f z)⁻¹), fun z ↦ (f z)⁻¹,
      hf.inv hf0, rfl⟩
    apply isUnit_iff_exists_inv.mpr
    refine ⟨q, Subtype.ext ?_⟩
    change g.1 * q.1 = 1
    rw [← hfg]
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hf.continuousAt.eventually_ne hf0] with z hz
    exact mul_inv_cancel₀ hz

private theorem clean_germ_irreducible {n : ℕ}
    {f : (Fin n → ℂ) × ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hi : IsIrreducibleAt f 0) :
    Irreducible (productAnalyticGermOf f hf) := by
  refine ⟨fun hu ↦ (clean_germ_isUnit_iff _).mp hu hi.1, ?_⟩
  intro a b hab
  obtain ⟨g, hg, hga⟩ := a.2
  obtain ⟨h, hh, hhb⟩ := b.2
  have hfac : f =ᶠ[nhds 0] fun x ↦ g x * h x := by
    apply Filter.Germ.coe_eq.mp
    calc
      ↑f = (a * b).1 := congrArg Subtype.val hab
      _ = a.1 * b.1 := rfl
      _ = ↑g * ↑h := congrArg₂ (· * ·) hga.symm hhb.symm
      _ = ↑(fun x ↦ g x * h x) := rfl
  rcases hi.2 g h hg hh hfac with hg0 | hh0
  · left
    apply (clean_germ_isUnit_iff a).mpr
    rw [← hga, Filter.Germ.value_ofFun]
    exact hg0
  · right
    apply (clean_germ_isUnit_iff b).mpr
    rw [← hhb, Filter.Germ.value_ofFun]
    exact hh0

private theorem clean_product_squarefree {n k : ℕ}
    {P : Fin k → (Fin n → ℂ) × ℂ → ℂ}
    (hP : ∀ i, AnalyticAt ℂ (P i) 0 ∧ IsIrreducibleAt (P i) 0)
    (hcP : Pairwise (fun i j ↦ IsCoprimeAt (P i) (P j) 0)) :
    IsSquareFreeAt (fun y ↦ ∏ i, P i y) 0 := by
  classical
  letI : UniqueFactorizationMonoid (ProductAnalyticGerm n) := productAnalyticGermUFD n
  let A : Fin k → ProductAnalyticGerm n := fun i ↦ productAnalyticGermOf (P i) (hP i).1
  have hi : ∀ i, Irreducible (A i) := fun i ↦ clean_germ_irreducible (hP i).1 (hP i).2
  have hc : Pairwise (fun i j ↦ IsRelPrime (A i) (A j)) := by
    intro i j hij
    apply (hi i).isRelPrime_iff_not_dvd.mpr
    rintro ⟨b, hb⟩
    obtain ⟨g, hg, hgb⟩ := b.2
    apply hcP hij
    refine ⟨P i, fun _ ↦ 1, g, (hP i).1, analyticAt_const, hg, (hP i).2.1,
      Eventually.of_forall (fun y ↦ (mul_one _).symm), ?_⟩
    apply Filter.Germ.coe_eq.mp
    have he := congrArg Subtype.val hb
    change ↑(P j) = ↑(P i) * b.1 at he
    rw [← hgb] at he
    exact he
  have hs : Squarefree (∏ i, A i) :=
    Finset.squarefree_prod_of_pairwise_isCoprime (fun i _ j _ hij ↦ hc hij)
      (fun i _ ↦ (hi i).squarefree)
  intro g h hg hh hg0 hfac
  let G := productAnalyticGermOf g hg
  let H := productAnalyticGermOf h hh
  have he : (∏ i, A i) = G * G * H := by
    apply Subtype.ext
    have hp : (∏ i, A i).1 = (↑(fun y ↦ ∏ i, P i y) :
        Filter.Germ (nhds (0 : (Fin n → ℂ) × ℂ)) ℂ) := by
      change (productAnalyticGermSubring n).subtype (∏ i, A i) = _
      rw [map_prod]
      have hfun : (∏ i, P i) = fun y ↦ ∏ i, P i y := by
        funext y
        simp only [Finset.prod_apply]
      change (∏ i, (Filter.Germ.coeRingHom (nhds (0 : (Fin n → ℂ) × ℂ))) (P i)) = _
      rw [← map_prod, hfun]
      rfl
    rw [hp]
    exact Filter.Germ.coe_eq.mpr (hfac.mono fun y hy ↦ by simpa only [pow_two] using hy)
  exact (clean_germ_isUnit_iff G).mp (hs G ⟨H, he⟩) hg0

private theorem clean_factor_of_regular_product
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k : ℕ}
    {P : Fin k → E → ℂ} {y : E} (hP : ∀ i, AnalyticAt ℂ (P i) y)
    (i : Fin k) (hi : P i y = 0)
    (hd : fderiv ℂ (fun z ↦ ∏ j, P j z) y ≠ 0) :
    (∀ j, j ≠ i → P j y ≠ 0) ∧ fderiv ℂ (P i) y ≠ 0 := by
  classical
  let g : E → ℂ := fun z ↦ ∏ j ∈ Finset.univ.erase i, P j z
  have hg : AnalyticAt ℂ g y := Finset.analyticAt_fun_prod _ (fun j _ ↦ hP j)
  have he : (fun z ↦ ∏ j, P j z) = fun z ↦ P i z * g z := by
    funext z
    exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hder : fderiv ℂ (fun z ↦ ∏ j, P j z) y = g y • fderiv ℂ (P i) y := by
    rw [he, fderiv_fun_mul (hP i).differentiableAt hg.differentiableAt, hi]
    simp only [zero_smul, zero_add]
  have hg0 : g y ≠ 0 := by
    intro hz
    apply hd
    rw [hder, hz, zero_smul]
  refine ⟨fun j hji ↦ ?_, fun hz ↦ hd (by rw [hder, hz, smul_zero])⟩
  exact (Finset.prod_ne_zero_iff.mp hg0) j (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)

private theorem clean_zero_avoiding_base {n d : ℕ}
    {f : (Fin n → ℂ) × ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hd : analyticOrderAt (fun w ↦ f (0, w)) 0 = d) (hd0 : d ≠ 0)
    {D : (Fin n → ℂ) → ℂ} (hD : ¬ ∀ᶠ z in nhds 0, D z = 0) :
    (0 : (Fin n → ℂ) × ℂ) ∈ closure {p | f p = 0 ∧ D p.1 ≠ 0} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨r, hr, hrε, δ, hδ, -, -, hcount⟩ := spec_exists_zeroCount_eq_order hf hd hε
  have hex : ∃ z ∈ Metric.ball (0 : Fin n → ℂ) (min δ ε), D z ≠ 0 := by
    by_contra hn
    apply hD
    filter_upwards [Metric.ball_mem_nhds (0 : Fin n → ℂ) (lt_min hδ hε)] with z hz
    by_contra hne
    exact hn ⟨z, hz, hne⟩
  obtain ⟨z, hz, hzD⟩ := hex
  have hc := hcount z (Metric.ball_subset_ball (min_le_left _ _) hz)
  obtain ⟨w, hw, hw0⟩ : ∃ w ∈ Metric.ball (0 : ℂ) r,
      analyticOrderNatAt (fun w ↦ f (z, w)) w ≠ 0 := by
    apply exists_ne_zero_of_finsum_mem_ne_zero
    rw [← zeroCount, hc]
    exact hd0
  refine ⟨(z, w), ⟨apply_eq_zero_of_analyticOrderNatAt_ne_zero (f := fun w ↦ f (z, w)) hw0, hzD⟩, ?_⟩
  rw [Prod.dist_eq, max_lt_iff]
  constructor
  · rw [dist_comm]
    exact lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right _ _)
  · rw [dist_comm]
    exact lt_trans (Metric.mem_ball.mp hw) hrε

private theorem clean_preparation_regular {n d : ℕ}
    {f u : (Fin n → ℂ) × ℂ → ℂ}
    {a : Fin d → (Fin n → ℂ) → ℂ}
    (L : ((Fin n → ℂ) × ℂ) ≃L[ℂ] ((Fin n → ℂ) × ℂ))
    {p : (Fin n → ℂ) × ℂ} (hf : AnalyticAt ℂ f (L p))
    (hu : AnalyticAt ℂ u p) (hu0 : u p ≠ 0)
    (ha : ∀ j, AnalyticAt ℂ (a j) p.1)
    (hfac : (fun q ↦ f (L q)) =ᶠ[nhds p] fun q ↦ u q * monicInLast a q)
    (hf0 : f (L p) = 0) (hD : weierstrassDiscr a p.1 ≠ 0) :
    fderiv ℂ f (L p) ≠ 0 := by
  have hP0 : monicInLast a p = 0 := by
    have he := hfac.self_of_nhds
    change f (L p) = u p * monicInLast a p at he
    rw [hf0] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hu0
  have hPa : AnalyticAt ℂ (monicInLast a) p := laneC_analyticAt_monicInLast ha p.2
  have hline : HasDerivAt (fun w : ℂ ↦ ((p.1, w) : (Fin n → ℂ) × ℂ)) (0, 1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have hPw : AnalyticAt ℂ (fun w ↦ monicInLast a (p.1, w)) p.2 :=
    hPa.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have hord : analyticOrderAt (fun w ↦ monicInLast a (p.1, w)) p.2 = 1 := by
    have hle := (spec_weierstrassDiscr_ne_zero_iff a p.1).mp hD p.2
    have hne := analyticOrderAt_ne_zero.mpr ⟨hPw, hP0⟩
    generalize analyticOrderAt (fun w ↦ monicInLast a (p.1, w)) p.2 = k at hle hne ⊢
    induction k using ENat.recTopCoe with
    | top => simp at hle
    | coe k => norm_cast at hle hne ⊢; omega
  have hpd := laneC_deriv_ne_zero_of_order_one hPw hord
  intro hfd
  have he := hfac.fderiv_eq (𝕜 := ℂ)
  have hc : fderiv ℂ (fun q ↦ f (L q)) p = 0 := by
    change fderiv ℂ (f ∘ L) p = 0
    rw [fderiv_comp p hf.differentiableAt L.differentiableAt, hfd]
    rfl
  rw [hc] at he
  have hG := hu.mul hPa
  have hGline := hG.differentiableAt.hasFDerivAt.comp_hasDerivAt p.2 hline
  have huline := (hu.differentiableAt.comp p.2 hline.differentiableAt).hasDerivAt
  have hPline := hPw.differentiableAt.hasDerivAt
  have huniq := hGline.unique (huline.mul hPline)
  have h01 : fderiv ℂ (fun q ↦ u q * monicInLast a q) p (0, 1) = 0 := by
    rw [← he]; rfl
  change fderiv ℂ (fun q ↦ u q * monicInLast a q) p (0, 1) =
    deriv (fun w ↦ u (p.1, w)) p.2 * monicInLast a p +
      u p * deriv (fun w ↦ monicInLast a (p.1, w)) p.2 at huniq
  rw [h01, hP0, mul_zero, zero_add] at huniq
  exact hpd ((mul_eq_zero.mp huniq.symm).resolve_left hu0)

theorem spec_zero_mem_closure_clean_regular_factor_aux {n k : ℕ}
    {P : Fin k → (Fin n → ℂ) × ℂ → ℂ}
    (hP : ∀ i, AnalyticAt ℂ (P i) 0 ∧ IsIrreducibleAt (P i) 0)
    (hcP : Pairwise (fun i j ↦ IsCoprimeAt (P i) (P j) 0)) (i : Fin k) :
    (0 : (Fin n → ℂ) × ℂ) ∈ closure
      {y | P i y = 0 ∧ (∀ j, j ≠ i → P j y ≠ 0) ∧ fderiv ℂ (P i) y ≠ 0} := by
  classical
  let F : (Fin n → ℂ) × ℂ → ℂ := fun y ↦ ∏ j, P j y
  have hF : AnalyticAt ℂ F 0 := Finset.analyticAt_fun_prod _ (fun j _ ↦ (hP j).1)
  have hs : IsSquareFreeAt F 0 := clean_product_squarefree hP hcP
  have hnz : ¬ ∀ᶠ y in nhds 0, F y = 0 := by
    intro hz
    exact hs 0 0 analyticAt_const analyticAt_const rfl
      (hz.mono fun y hy ↦ by simpa only [Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), zero_mul] using hy)
  obtain ⟨m, -, L, u, hu, hu0, a, ha, hfac⟩ := spec_exists_linearEquiv_preparation hF hnz
  have hLa : AnalyticAt ℂ L 0 := L.toContinuousLinearMap.analyticAt 0
  have hFi : AnalyticAt ℂ (fun y ↦ P i (L y)) 0 :=
    ((hP i).1).comp_of_eq hLa L.map_zero
  have horderF := spec_analyticOrderAt_of_preparation hu hu0 (fun j ↦ (ha j).2) hfac
  have horderi : analyticOrderAt (fun w ↦ P i (L (0, w))) 0 ≠ ⊤ := by
    intro ht
    have hz := analyticOrderAt_eq_top.mp ht
    have hzF : ∀ᶠ w in nhds (0 : ℂ), F (L (0, w)) = 0 := by
      filter_upwards [hz] with w hw
      exact Finset.prod_eq_zero (Finset.mem_univ i) hw
    have htF := analyticOrderAt_eq_top.mpr hzF
    rw [horderF] at htF
    exact ENat.natCast_ne_top _ htF
  obtain ⟨d, hd⟩ : ∃ d : ℕ, analyticOrderAt (fun w ↦ P i (L (0, w))) 0 = d := by
    obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp horderi
    exact ⟨d, hd.symm⟩
  have hd0 : d ≠ 0 := by
    intro hz
    have hne := analyticOrderAt_ne_zero.mpr
      ⟨hFi.comp₂ analyticAt_const analyticAt_id, by simpa only [id_eq, Prod.mk_zero_zero, L.map_zero] using (hP i).2.1⟩
    exact hne (hd.trans (by rw [hz]; rfl))
  have hsA : IsSquareFreeAt (monicInLast a) 0 :=
    laneC_isSquareFreeAt_of_comp L (by simpa only [L.map_zero] using hs) hu hfac
  have haa : AnalyticAt ℂ (monicInLast a) 0 :=
    laneC_analyticAt_monicInLast (fun j ↦ (ha j).1) 0
  have hD := spec_weierstrassDiscr_not_eventually_zero (fun j ↦ (ha j).1)
    (fun j ↦ (ha j).2) (spec_eventually_isSquareFreeAt haa hsA)
  have hcl := clean_zero_avoiding_base hFi hd hd0 hD
  have hL0 : Tendsto L (nhds 0) (nhds 0) := by simpa only [L.map_zero] using L.continuous.tendsto 0
  have hPan : ∀ᶠ p in nhds (0 : (Fin n → ℂ) × ℂ), ∀ j, AnalyticAt ℂ (P j) (L p) :=
    hL0 (eventually_all.mpr fun j ↦ (hP j).1.eventually_analyticAt)
  have haa' : ∀ᶠ p in nhds (0 : (Fin n → ℂ) × ℂ), ∀ j, AnalyticAt ℂ (a j) p.1 :=
    (continuous_fst.tendsto (0 : (Fin n → ℂ) × ℂ))
      (eventually_all.mpr fun j ↦ (ha j).1.eventually_analyticAt)
  obtain ⟨V, hV, hVo, h0V⟩ := eventually_nhds_iff.mp
    ((((hfac.eventually_nhds.and hu.eventually_analyticAt).and
      (hu.continuousAt.eventually_ne hu0)).and haa').and hPan)
  rw [mem_closure_iff] at hcl ⊢
  intro U hU h0U
  obtain ⟨p, hpU, hp⟩ := hcl (L ⁻¹' U ∩ V) ((hU.preimage L.continuous).inter hVo)
    ⟨by simpa only [Set.mem_preimage, L.map_zero] using h0U, h0V⟩
  obtain ⟨⟨⟨⟨hfacp, hup⟩, hup0⟩, hap⟩, hPp⟩ := hV p hpU.2
  have hFp : F (L p) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hp.1
  have hFpa : AnalyticAt ℂ F (L p) := Finset.analyticAt_fun_prod _ (fun j _ ↦ hPp j)
  have hreg := clean_preparation_regular L hFpa hup hup0 hap hfacp hFp hp.2
  exact ⟨L p, hpU.1, hp.1, clean_factor_of_regular_product hPp i hp.1 hreg⟩

theorem spec_resultant_ne_zero_of_isCoprime_aux {R : Type*} [CommRing R] [IsDomain R]
    (P g : R[X]) (hPg : IsCoprime P g) : P.resultant g ≠ 0 := by
  exact resultant_ne_zero P g hPg

theorem spec_resultant_avoids_common_root_aux {K : Type*} [Field K]
    (P g : K[X]) (hPg : IsCoprime P g) (w : K) : P.eval w ≠ 0 ∨ g.eval w ≠ 0 := by
  rcases hPg with ⟨a, b, hab⟩
  by_contra h
  push Not at h
  have he := congrArg (Polynomial.eval w) hab
  simp [h.1, h.2] at he

theorem spec_discr_ne_zero_of_isCoprime_derivative_aux {R : Type*}
    [CommRing R] [IsDomain R] [CharZero R] (P : R[X]) (hP : P.Monic)
    (hdeg : 0 < P.natDegree) (hsep : IsCoprime P P.derivative) : P.discr ≠ 0 := by
  have hres : P.resultant P.derivative ≠ 0 := resultant_ne_zero P P.derivative hsep
  change resultant P P.derivative P.natDegree P.derivative.natDegree ≠ 0 at hres
  rw [natDegree_derivative] at hres
  rw [resultant_deriv (natDegree_pos_iff_degree_pos.mp hdeg), hP.leadingCoeff, mul_one] at hres
  exact fun h ↦ hres (by rw [h, mul_zero])

theorem spec_resultant_X_eq_eval_zero_aux {R : Type*} [CommRing R] (g : R[X]) :
    resultant X g 1 g.natDegree = g.eval 0 := by
  nontriviality R
  have hx : (X - C (0 : R) : R[X]) = X := by simp
  rw [← hx]
  exact resultant_X_sub_C_left g g.natDegree 0 le_rfl

theorem spec_resultant_self_zero_excluded_aux {R : Type*} [Field R]
    (P h : R[X]) (hdeg : P.natDegree ≠ 0) : P.resultant (P * h) = 0 := by
  rw [resultant_eq_zero_iff]
  refine ⟨Or.inl (fun hP ↦ hdeg (by rw [hP, natDegree_zero])), ?_⟩
  intro hc
  exact (not_isUnit_of_natDegree_pos P (Nat.pos_of_ne_zero hdeg))
    (hc.isUnit_of_dvd ⟨h, rfl⟩)

theorem spec_associated_non_coprime_aux {R : Type*} [CommRing R] [IsDomain R]
    (P Q : R[X]) (hP : ¬ IsUnit P) (hPQ : Associated P Q) : ¬ IsCoprime P Q := by
  intro hc
  have hd : P ∣ Q := hPQ.dvd
  exact hP (hc.isUnit_of_dvd hd)

end HodgeLean.Foundations.AnalyticDivisorAlgebraic9
