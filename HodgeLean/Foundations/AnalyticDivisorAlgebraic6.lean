import HodgeLean.Foundations.AnalyticDivisorAlgebraic6Proofs

/-! # Factorial analytic germs and local multiplicities: frozen specification

This stage claims the honest UFD induction for the local ring `AnalyticGerm n`: the zero-variable
base; implication from preparation and division to association with a Weierstrass polynomial;
irreducibility transfer; the product-coordinate identification; invariance under invertible linear
coordinate changes; regularity after such a change; the successor theorem; and induction. It then
claims the resulting function-level square-free decomposition, nearby square-freeness, and
transverse multiplicity.

Coordinates use `Fin (n+1)`, with `Fin.last n` the distinguished `w` coordinate. The polynomial
embedding is characterized by adjoining that coordinate to the first `n` coordinate germs.
Not claimed are Noetherianity, uniqueness of displayed function representatives, analytic-set
components, a global divisor, Chow's theorem, GAGA, algebraicity, or a cycle class.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology Polynomial
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
variable {n : ℕ}

/-- **Base case.** The ring of analytic germs in zero variables is a UFD.
Source: Gunning--Rossi II.B, Theorems 3--6; de Jong--Pfister §3. -/
theorem spec_analyticGerm_ufd_zero : UniqueFactorizationMonoid (AnalyticGerm 0) :=
  spec_analyticGerm_ufd_zero_aux

example : UniqueFactorizationMonoid (Polynomial (AnalyticGerm 0)) := by
  letI := spec_analyticGerm_ufd_zero
  infer_instance

/-- **Preparation transfer.** A nonunit germ regular in the last variable is associated to the
image of a positive-degree Weierstrass polynomial over the `n`-variable analytic germ ring.
Source: Gunning--Rossi II.B, Theorem 2 and its uniqueness clause; de Jong--Pfister §3. -/
theorem spec_preparation_transfer {g : AnalyticGerm (n + 1)}
    (hg : IsRegularInLast g) (hnu : ¬ IsUnit g) :
    ∃ (ι : Polynomial (AnalyticGerm n) →+* AnalyticGerm (n + 1))
      (P : Polynomial (AnalyticGerm n)),
      IsWeierstrassEmbedding ι ∧ IsWeierstrassPolynomial P ∧ Associated g (ι P) :=
  spec_preparation_transfer_aux hg hnu

example {g : AnalyticGerm (n + 1)} (hg : IsRegularInLast g) (hnu : ¬ IsUnit g) :
    ∃ P : Polynomial (AnalyticGerm n), 0 < P.natDegree := by
  obtain ⟨ι, P, -, hP, -⟩ := spec_preparation_transfer hg hnu
  exact ⟨P, hP.2.1⟩

/-- **Irreducibility transfer.** A Weierstrass polynomial is irreducible over the coefficient
germ ring exactly when its image is irreducible in the next analytic germ ring.
Source: Gunning--Rossi II.B, Theorems 3--4 (division); de Jong--Pfister §3. -/
theorem spec_irreducible_transfer
    (ι : Polynomial (AnalyticGerm n) →+* AnalyticGerm (n + 1))
    (hι : IsWeierstrassEmbedding ι) {P : Polynomial (AnalyticGerm n)}
    (hP : IsWeierstrassPolynomial P) : Irreducible P ↔ Irreducible (ι P) :=
  spec_irreducible_transfer_aux ι hι hP

example (ι : Polynomial (AnalyticGerm n) →+* AnalyticGerm (n + 1))
    (hι : IsWeierstrassEmbedding ι) {P : Polynomial (AnalyticGerm n)}
    (hP : IsWeierstrassPolynomial P) (hirr : Irreducible P) : ¬ IsUnit (ι P) :=
  (spec_irreducible_transfer ι hι hP).1 hirr |>.not_isUnit

/-- **Product coordinates.** Germs on `Fin (n+1) → ℂ` are isomorphic as a ring to germs on
`(Fin n → ℂ) × ℂ`, and the `Fin.last n` coordinate is carried to the `w` coordinate.
Source: Gunning--Rossi II.B, Lemma 1; the standard equivalence `Fin (n+1) ≃ Fin n ⊕ Unit`. -/
theorem spec_finSucc_product_equiv :
    ∃ e : AnalyticGerm (n + 1) ≃+* ProductAnalyticGerm n,
      e ⟨@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds 0)
          (fun z ↦ z (Fin.last n)),
        ⟨fun z ↦ z (Fin.last n),
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ)
            (Fin.last n)).analyticAt 0, rfl⟩⟩ =
        ⟨@Filter.Germ.ofFun ((Fin n → ℂ) × ℂ) ℂ (nhds 0) (fun p ↦ p.2),
          ⟨fun p ↦ p.2, analyticAt_snd, rfl⟩⟩ :=
  spec_finSucc_product_equiv_aux

example : ∃ e : AnalyticGerm 1 ≃+* ProductAnalyticGerm 0,
    e ⟨@Filter.Germ.ofFun (Fin 1 → ℂ) ℂ (nhds 0) (fun z ↦ z (Fin.last 0)),
      ⟨fun z ↦ z (Fin.last 0),
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ)
          (Fin.last 0)).analyticAt 0, rfl⟩⟩ ≠ 1 := by
  obtain ⟨e, he⟩ := spec_finSucc_product_equiv (n := 0)
  refine ⟨e, ?_⟩
  rw [he]
  intro h
  have hv := congrArg (fun g : ProductAnalyticGerm 0 ↦ g.1.value) h
  change (0 : ℂ) = 1 at hv
  exact zero_ne_one hv

/-- **Linear-coordinate invariance.** Pullback by an invertible complex-linear coordinate change
induces a ring automorphism of analytic germs and preserves irreducibility and associatedness.
Consequently any UFD structure already present remains the UFD structure on the same ring.
Source: Gunning--Rossi II.B, Lemma 1; de Jong--Pfister §3. -/
theorem spec_linearChange_automorphism
    (L : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ)) :
    ∃ e : AnalyticGerm (n + 1) ≃+* AnalyticGerm (n + 1),
      (∀ (g : AnalyticGerm (n + 1)) (f : (Fin (n + 1) → ℂ) → ℂ),
        AnalyticAt ℂ f 0 →
        (@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds 0) f) = g.1 →
        (@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds 0) (fun z ↦ f (L z))) =
          (e g).1) ∧
      (∀ g, Irreducible (e g) ↔ Irreducible g) ∧
      (∀ g h, Associated (e g) (e h) ↔ Associated g h) :=
  spec_linearChange_automorphism_aux L

example (L : (Fin 1 → ℂ) ≃L[ℂ] (Fin 1 → ℂ)) :
    ∃ e : AnalyticGerm 1 ≃+* AnalyticGerm 1, ¬ Associated (e 0) (e 1) := by
  obtain ⟨e, -, -, hassoc⟩ := spec_linearChange_automorphism L
  refine ⟨e, ?_⟩
  rw [hassoc]
  rw [Associated.comm, associated_zero_iff_eq_zero]
  exact (one_ne_zero : (1 : AnalyticGerm 1) ≠ 0)

/-- **Regularity in generic coordinates.** Every nonzero nonunit analytic germ becomes regular in
the last coordinate after an invertible complex-linear change of variables.
Source: Gunning--Rossi II.B, Lemma 1; `AnalyticDivisorAlgebraic5.spec_exists_linearEquiv_preparation`. -/
theorem spec_exists_linearChange_regular {g : AnalyticGerm (n + 1)}
    (hg0 : g ≠ 0) (hgu : ¬ IsUnit g) :
    ∃ (L : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ))
      (e : AnalyticGerm (n + 1) ≃+* AnalyticGerm (n + 1)),
      (∀ (a : AnalyticGerm (n + 1)) (f : (Fin (n + 1) → ℂ) → ℂ),
        AnalyticAt ℂ f 0 →
        (@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds 0) f) = a.1 →
        (@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds 0) (fun z ↦ f (L z))) =
          (e a).1) ∧
      IsRegularInLast (e g) :=
  spec_exists_linearChange_regular_aux hg0 hgu

example : IsRegularInLast
    (⟨@Filter.Germ.ofFun (Fin 1 → ℂ) ℂ (nhds 0) (fun z ↦ z (Fin.last 0)),
      ⟨fun z ↦ z (Fin.last 0),
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ)
          (Fin.last 0)).analyticAt 0, rfl⟩⟩ : AnalyticGerm 1) := by
  refine ⟨fun z ↦ z (Fin.last 0), ?_, rfl, ?_⟩
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ)
      (Fin.last 0)).analyticAt 0
  · simp only [Pi.single_eq_same]
    change analyticOrderAt (id : ℂ → ℂ) 0 ≠ ⊤
    rw [analyticOrderAt_id]
    exact ENat.one_ne_top

/-- **Successor step.** UFD for `n`-variable analytic germs implies UFD for `n+1` variables.
Source: Gunning--Rossi II.B, Theorems 2--6; de Jong--Pfister §3; Mathlib
`Polynomial.uniqueFactorizationMonoid`. -/
theorem spec_analyticGerm_ufd_succ (hn : UniqueFactorizationMonoid (AnalyticGerm n)) :
    UniqueFactorizationMonoid (AnalyticGerm (n + 1)) :=
  spec_analyticGerm_ufd_succ_aux hn

example (hn : UniqueFactorizationMonoid (AnalyticGerm n)) :
    UniqueFactorizationMonoid (Polynomial (AnalyticGerm (n + 1))) := by
  letI := spec_analyticGerm_ufd_succ hn
  infer_instance

/-- **Induction.** Every finite-dimensional complex analytic germ ring is a UFD.
Source: Gunning--Rossi II.B, Theorems 3--6; de Jong--Pfister §3. -/
theorem spec_analyticGerm_ufd : ∀ n, UniqueFactorizationMonoid (AnalyticGerm n) :=
  spec_analyticGerm_ufd_aux

example : UniqueFactorizationMonoid (AnalyticGerm 6) := spec_analyticGerm_ufd 6

/-- **Square-free decomposition.** A nonzero analytic germ vanishing at the origin is a unit
times positive powers of reduced, pairwise coprime analytic germs.
Source: Gunning--Rossi II.B, Theorems 3--6; de Jong--Pfister §3. -/
theorem spec_exists_squarefree_decomposition {f : (Fin n → ℂ) × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0) (hnz : ¬ ∀ᶠ y in nhds 0, f y = 0) :
    ∃ k : ℕ, ∃ u : (Fin n → ℂ) × ℂ → ℂ,
      ∃ P : Fin k → (Fin n → ℂ) × ℂ → ℂ, ∃ m : Fin k → ℕ,
        AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
        (∀ i, AnalyticAt ℂ (P i) 0 ∧ P i 0 = 0 ∧ 0 < m i ∧ IsSquareFreeAt (P i) 0) ∧
        Pairwise (fun i j ↦ IsCoprimeAt (P i) (P j) 0) ∧
        f =ᶠ[nhds 0] fun y ↦ u y * ∏ i, (P i y) ^ (m i) :=
  spec_exists_squarefree_decomposition_aux hf hf0 hnz

example : ∀ y : (Fin 1 → ℂ) × ℂ,
    y.2 ^ 2 * (y.2 - y.1 0) =
      (1 : ℂ) * ∏ i, (![y.2, y.2 - y.1 0] i) ^ (![2, 1] i) := by
  intro y
  simp [Fin.prod_univ_two]

/-- **Nearby square-freeness.** An analytic function square-free at the origin remains
square-free throughout some neighbourhood. Source: Gunning--Rossi II.B, Theorems 3--6. -/
theorem spec_eventually_isSquareFreeAt {f : (Fin n → ℂ) × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hsq : IsSquareFreeAt f 0) :
    ∀ᶠ y in nhds 0, IsSquareFreeAt f y :=
  spec_eventually_isSquareFreeAt_aux hf hsq

example (w : ℂ) (hw : w ≠ 0) :
    IsSquareFreeAt (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2 * (y.2 - y.1 0))
      ((fun _ ↦ w), w) := by
  intro g h hg hh hg0 hfac
  have hfst : DifferentiableAt ℂ (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2) ((fun _ ↦ w), w) :=
    by fun_prop
  have hsnd : DifferentiableAt ℂ (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2 - y.1 0)
      ((fun _ ↦ w), w) := by fun_prop
  have hder := hfac.fderiv_eq (𝕜 := ℂ)
  rw [fderiv_fun_mul (𝕜 := ℂ) hfst hsnd,
    fderiv_fun_mul (𝕜 := ℂ) (c := fun p ↦ g p ^ 2) (d := h)
      (hg.pow 2).differentiableAt hh.differentiableAt] at hder
  simp only [pow_two] at hder
  rw [fderiv_fun_mul (𝕜 := ℂ) (c := g) (d := g)
    hg.differentiableAt hg.differentiableAt] at hder
  have happ := congrArg
    (fun L : ((Fin 1 → ℂ) × ℂ) →L[ℂ] ℂ ↦ L (0, 1)) hder
  have hsnd_eval :
      (fderiv ℂ (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2 - y.1 0) ((fun _ ↦ w), w))
        (0, 1) = 1 := by
    have happ0 : DifferentiableAt ℂ (fun y : (Fin 1 → ℂ) × ℂ ↦ y.1 0)
        ((fun _ ↦ w), w) := by fun_prop
    rw [fderiv_fun_sub (𝕜 := ℂ) differentiableAt_snd happ0, fderiv_snd,
      fderiv_apply (𝕜 := ℂ) differentiableAt_fst 0, fderiv_fst]
    simp
  simp [hg0] at happ
  rw [hsnd_eval] at happ
  exact hw (happ.resolve_right one_ne_zero)

/-- **Transverse order.** At a zero belonging only to `P i`, every direction transverse to that
factor has slice order `m i`. Source: Gunning--Rossi II.B, Theorems 3--6; Chirka §2.3. -/
theorem spec_transverseOrder_of_decomposition {k : ℕ}
    {f u : (Fin n → ℂ) × ℂ → ℂ}
    {P : Fin k → (Fin n → ℂ) × ℂ → ℂ} {m : Fin k → ℕ}
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) (hP : ∀ i, AnalyticAt ℂ (P i) 0)
    (hm : ∀ i, 0 < m i) (hfac : f =ᶠ[nhds 0] fun y ↦ u y * ∏ i, (P i y) ^ (m i)) :
    ∀ᶠ y in nhds 0, ∀ i, P i y = 0 → (∀ j, j ≠ i → P j y ≠ 0) →
      ∀ v : (Fin n → ℂ) × ℂ, fderiv ℂ (P i) y v ≠ 0 →
        analyticOrderAt (fun t : ℂ ↦ f (y + t • v)) 0 = m i :=
  spec_transverseOrder_of_decomposition_aux hu hu0 hP hm hfac

example : analyticOrderAt (fun t : ℂ ↦ t ^ 2 * (t - 1)) 0 = 2 := by
  have han : AnalyticAt ℂ (fun t : ℂ ↦ t ^ 2 * (t - 1)) 0 :=
    (analyticAt_id.pow 2).mul (analyticAt_id.sub analyticAt_const)
  apply (han.analyticOrderAt_eq_natCast (n := 2)).2
  exact ⟨fun t ↦ t - 1, analyticAt_id.sub analyticAt_const, by norm_num,
    Eventually.of_forall fun t ↦ by simp [smul_eq_mul]⟩

end HodgeLean.Foundations.AnalyticDivisorAlgebraic6
