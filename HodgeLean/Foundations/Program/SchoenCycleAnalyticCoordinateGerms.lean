import HodgeLean.Foundations.Program.SchoenCycleAnalyticGermPullback

/-! # Reduced products of distinct analytic coordinate germs -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
open scoped BigOperators
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Foundations.Program

/-- The actual analytic germ of a specified linear coordinate at the origin.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Gunning–Rossi, Analytic Functions of Several Complex Variables, II.B. -/
def s2e_analyticCoordinateGerm (n : ℕ) (i : Fin n) : AnalyticGermAt n 0 :=
  ⟨Filter.Germ.ofFun (fun z => z i), fun z => z i,
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt 0, rfl⟩

/-- Every analytic coordinate germ is irreducible in its actual analytic local ring.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Gunning–Rossi, Analytic Functions of Several Complex Variables, II.B. -/
theorem s2e_analyticCoordinateGerm_irreducible (n : ℕ) (i : Fin n) :
    Irreducible (s2e_analyticCoordinateGerm n i) := by
  have hdi : fderiv ℂ (fun z : Fin n → ℂ => z i) 0 ≠ 0 := by
    change fderiv ℂ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i) 0 ≠ 0
    rw [(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).hasFDerivAt.fderiv]
    intro he
    have h := congrArg (fun L : (Fin n → ℂ) →L[ℂ] ℂ => L (Pi.single i 1)) he
    simpa using h
  constructor
  · intro hu
    have hv := (s2e_analyticGermAt_isUnit_iff _).mp hu
    change (s2e_analyticCoordinateGerm n i).val.value ≠ 0 at hv
    have hne : (0 : ℂ) ≠ 0 := by
      simpa only [s2e_analyticCoordinateGerm, Filter.Germ.value_ofFun, Pi.zero_apply] using hv
    exact hne rfl
  · intro a b hab
    obtain ⟨f, hf, hfa⟩ := a.2
    obtain ⟨g, hg, hgb⟩ := b.2
    have he : (fun z : Fin n → ℂ => z i) =ᶠ[𝓝 0] fun z => f z * g z := by
      apply Filter.Germ.coe_eq.mp
      have h := congrArg Subtype.val hab
      change Filter.Germ.ofFun (fun z : Fin n → ℂ => z i) = a.val * b.val at h
      rwa [← hfa, ← hgb] at h
    by_cases hf0 : f 0 = 0
    · right
      apply (s2e_analyticGermAt_isUnit_iff b).mpr
      change b.val.value ≠ 0
      rw [← hgb, Filter.Germ.value_ofFun]
      intro hg0
      have hz : fderiv ℂ (fun z => f z * g z) 0 = 0 := by
        change fderiv ℂ (f * g) 0 = 0
        rw [fderiv_mul hf.differentiableAt hg.differentiableAt, hf0, hg0]
        ext z
        simp
      exact hdi ((he.fderiv_eq (𝕜 := ℂ)).trans hz)
    · left
      apply (s2e_analyticGermAt_isUnit_iff a).mpr
      change a.val.value ≠ 0
      rwa [← hfa, Filter.Germ.value_ofFun]

/-- Distinct analytic coordinate germs do not divide one another.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Gunning–Rossi, Analytic Functions of Several Complex Variables, II.B. -/
theorem s2e_analyticCoordinateGerm_not_dvd (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    ¬ s2e_analyticCoordinateGerm n i ∣ s2e_analyticCoordinateGerm n j := by
  rintro ⟨g, hg⟩
  obtain ⟨f, hf, hfg⟩ := g.2
  have he : (fun z : Fin n → ℂ => z j) =ᶠ[𝓝 0] fun z => z i * f z := by
    apply Filter.Germ.coe_eq.mp
    have h := congrArg Subtype.val hg
    change Filter.Germ.ofFun (fun z : Fin n → ℂ => z j) =
      Filter.Germ.ofFun (fun z : Fin n → ℂ => z i) * g.val at h
    rwa [← hfg] at h
  let Li := ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i
  let Lj := ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j
  have hd := he.fderiv_eq (𝕜 := ℂ)
  change fderiv ℂ Lj 0 = fderiv ℂ (⇑Li * f) 0 at hd
  rw [Lj.hasFDerivAt.fderiv, fderiv_mul Li.differentiableAt hf.differentiableAt,
    Li.hasFDerivAt.fderiv] at hd
  have hv := congrArg (fun L : (Fin n → ℂ) →L[ℂ] ℂ => L (Pi.single j 1)) hd
  simpa [Li, Lj, hij] using hv

/-- A product of distinct analytic coordinate germs is squarefree, including the empty product.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Gunning–Rossi, Analytic Functions of Several Complex Variables, II.B. -/
theorem s2e_analyticCoordinateGerm_product_squarefree (n : ℕ) (S : Finset (Fin n)) :
    Squarefree (∏ i ∈ S, s2e_analyticCoordinateGerm n i) := by
  obtain ⟨e, _, _⟩ :=
    HodgeLean.Foundations.AnalyticDivisorAlgebraic11.spec_germ_translation_equiv n 0
  letI : UniqueFactorizationMonoid (AnalyticGermAt n 0) :=
    e.symm.toMulEquiv.uniqueFactorizationMonoid
      (HodgeLean.Foundations.AnalyticDivisorAlgebraic6.spec_analyticGerm_ufd n)
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    exact (s2e_analyticCoordinateGerm_irreducible n i).isRelPrime_iff_not_dvd.mpr
      (s2e_analyticCoordinateGerm_not_dvd n i j hij)
  · intro i hi
    exact (s2e_analyticCoordinateGerm_irreducible n i).squarefree

end HodgeLean.Foundations.Program
