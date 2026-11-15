import HodgeLean.Foundations.AnalyticDivisorAlgebraic7Proofs

/-! # Local components of a hypersurface germ: frozen specification

This stage claims implication from analytic factoriality to an irreducible function-level
decomposition and its uniqueness up to permutation and analytic units.  It also claims the local
zero-set union, density of regular points on every displayed component, and constancy of the
transverse order on the regular part of one component away from all the others.

These are statements about finitely many local equations near the origin.  Not claimed are an
analytic-set component type, gluing between neighbourhoods, a global analytic divisor, Riemann
extension, proper finite projection, Chow's theorem, GAGA, algebraicity, or a cycle class.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic7

open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
variable {n : ℕ}

/-- A nonzero analytic germ vanishing at the origin is a unit times positive powers of distinct
irreducible analytic function germs.
Source: Gunning--Rossi II.B, Theorems 3--6; de Jong--Pfister §§3--4. -/
theorem spec_exists_irreducible_decomposition {f : (Fin n → ℂ) × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0) (hnz : ¬ ∀ᶠ y in nhds 0, f y = 0) :
    ∃ k : ℕ, ∃ u : (Fin n → ℂ) × ℂ → ℂ,
      ∃ P : Fin k → (Fin n → ℂ) × ℂ → ℂ, ∃ m : Fin k → ℕ,
        AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
        (∀ i, AnalyticAt ℂ (P i) 0 ∧ IsIrreducibleAt (P i) 0 ∧ 0 < m i) ∧
        Pairwise (fun i j ↦ IsCoprimeAt (P i) (P j) 0) ∧
        f =ᶠ[nhds 0] fun y ↦ u y * ∏ i, (P i y) ^ (m i) :=
  spec_exists_irreducible_decomposition_aux hf hf0 hnz

example
    (hnz : ¬ ∀ᶠ y in nhds (0 : (Fin 1 → ℂ) × ℂ),
      y.2 ^ 2 * (y.2 - y.1 0) = 0) :
    ∃ k : ℕ, ∃ u : (Fin 1 → ℂ) × ℂ → ℂ,
      ∃ P : Fin k → (Fin 1 → ℂ) × ℂ → ℂ, ∃ m : Fin k → ℕ,
        AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
        (∀ i, AnalyticAt ℂ (P i) 0 ∧ IsIrreducibleAt (P i) 0 ∧ 0 < m i) ∧
        Pairwise (fun i j ↦ IsCoprimeAt (P i) (P j) 0) ∧
        (fun y ↦ y.2 ^ 2 * (y.2 - y.1 0)) =ᶠ[nhds 0]
          fun y ↦ u y * ∏ i, (P i y) ^ (m i) := by
  apply spec_exists_irreducible_decomposition
  · have hz : AnalyticAt ℂ (fun y : (Fin 1 → ℂ) × ℂ ↦ y.1 0) 0 :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0).comp_of_eq
        analyticAt_fst rfl
    exact (analyticAt_snd.pow 2).mul (analyticAt_snd.sub hz)
  · norm_num
  · exact hnz

/-- Two irreducible decompositions of the same nonzero germ have the same factors, up to a
permutation and multiplication by analytic units, and the same exponents.
Source: Gunning--Rossi II.B, Theorems 3--6; de Jong--Pfister §§3--4. -/
theorem spec_irreducible_decomposition_unique {k l : ℕ}
    {f u v : (Fin n → ℂ) × ℂ → ℂ}
    {P : Fin k → (Fin n → ℂ) × ℂ → ℂ} {m : Fin k → ℕ}
    {Q : Fin l → (Fin n → ℂ) × ℂ → ℂ} {r : Fin l → ℕ}
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) (hv : AnalyticAt ℂ v 0) (hv0 : v 0 ≠ 0)
    (hP : ∀ i, AnalyticAt ℂ (P i) 0 ∧ IsIrreducibleAt (P i) 0 ∧ 0 < m i)
    (hQ : ∀ j, AnalyticAt ℂ (Q j) 0 ∧ IsIrreducibleAt (Q j) 0 ∧ 0 < r j)
    (hcP : Pairwise (fun i j ↦ IsCoprimeAt (P i) (P j) 0))
    (hcQ : Pairwise (fun i j ↦ IsCoprimeAt (Q i) (Q j) 0))
    (hfacP : f =ᶠ[nhds 0] fun y ↦ u y * ∏ i, (P i y) ^ (m i))
    (hfacQ : f =ᶠ[nhds 0] fun y ↦ v y * ∏ j, (Q j y) ^ (r j)) :
    ∃ e : Fin k ≃ Fin l, ∀ i, AreAssociatedAt (P i) (Q (e i)) 0 ∧ m i = r (e i) :=
  spec_irreducible_decomposition_unique_aux hu hu0 hv hv0 hP hQ hcP hcQ hfacP hfacQ

example
    (hP : ∀ i : Fin 2, IsIrreducibleAt
      (![fun y : (Fin 1 → ℂ) × ℂ ↦ y.2, fun y ↦ y.2 - y.1 0] i) 0)
    (hcP : Pairwise (fun i j ↦ IsCoprimeAt
      (![fun y : (Fin 1 → ℂ) × ℂ ↦ y.2, fun y ↦ y.2 - y.1 0] i)
      (![fun y : (Fin 1 → ℂ) × ℂ ↦ y.2, fun y ↦ y.2 - y.1 0] j) 0))
    (hcQ : Pairwise (fun i j ↦ IsCoprimeAt
      (![fun y : (Fin 1 → ℂ) × ℂ ↦ y.2 - y.1 0, fun y ↦ y.2] i)
      (![fun y : (Fin 1 → ℂ) × ℂ ↦ y.2 - y.1 0, fun y ↦ y.2] j) 0)) :
    ∃ e : Fin 2 ≃ Fin 2, ∀ i,
      AreAssociatedAt
        (![fun y : (Fin 1 → ℂ) × ℂ ↦ y.2, fun y ↦ y.2 - y.1 0] i)
        (![fun y : (Fin 1 → ℂ) × ℂ ↦ y.2 - y.1 0, fun y ↦ y.2] (e i)) 0 ∧
      (![2, 1] i) = (![1, 2] (e i)) := by
  apply spec_irreducible_decomposition_unique (f := fun y ↦ y.2 ^ 2 * (y.2 - y.1 0))
      (u := fun _ ↦ 1) (v := fun _ ↦ 1)
  · fun_prop
  · norm_num
  · fun_prop
  · norm_num
  · intro i
    refine ⟨?_, hP i, by fin_cases i <;> norm_num⟩
    · fin_cases i <;> simp
      · exact analyticAt_snd
      · exact analyticAt_snd.sub
          (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0).comp_of_eq
            analyticAt_fst rfl)
  · intro i
    refine ⟨?_, ?_, by fin_cases i <;> norm_num⟩
    · fin_cases i <;> simp
      · exact analyticAt_snd.sub
          (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0).comp_of_eq
            analyticAt_fst rfl)
      · exact analyticAt_snd
    · fin_cases i
      · simpa using hP 1
      · simpa using hP 0
  · exact hcP
  · exact hcQ
  · filter_upwards [] with y
    simp [Fin.prod_univ_two]
  · filter_upwards [] with y
    simp [Fin.prod_univ_two]
    ring

/-- Near the origin, the zero set of a finite factorization is exactly the union of the zero sets
of its positive-power factors.
Source: Chirka, *Complex Analytic Sets*, §§2--3; elementary local factorization. -/
theorem spec_eventually_zero_iff_factor_zero {k : ℕ}
    {f u : (Fin n → ℂ) × ℂ → ℂ}
    {P : Fin k → (Fin n → ℂ) × ℂ → ℂ} {m : Fin k → ℕ}
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) (hm : ∀ i, 0 < m i)
    (hfac : f =ᶠ[nhds 0] fun y ↦ u y * ∏ i, (P i y) ^ (m i)) :
    ∀ᶠ y in nhds 0, f y = 0 ↔ ∃ i, P i y = 0 :=
  spec_eventually_zero_iff_factor_zero_aux hu hu0 hm hfac

example : ∀ y : ℂ × ℂ, y.1 ^ 2 * y.2 = 0 ↔ y.1 = 0 ∨ y.2 = 0 := by
  intro y
  simp

/-- Regular points are dense near the origin on every displayed square-free factor.
Source: Gunning--Rossi III.A; Chirka §2.3. -/
theorem spec_eventually_mem_closure_regular_factor {k : ℕ}
    {P : Fin k → (Fin n → ℂ) × ℂ → ℂ}
    (hP : ∀ i, AnalyticAt ℂ (P i) 0 ∧ IsSquareFreeAt (P i) 0) :
    ∀ᶠ y in nhds 0, ∀ i, P i y = 0 →
      y ∈ closure {p | P i p = 0 ∧ fderiv ℂ (P i) p ≠ 0} :=
  spec_eventually_mem_closure_regular_factor_aux hP

example : (0 : ℂ × ℂ) ∈ closure {p : ℂ × ℂ | p.2 = 0 ∧
    fderiv ℂ (fun q : ℂ × ℂ ↦ q.2) p ≠ 0} := by
  apply subset_closure
  constructor
  · rfl
  · rw [fderiv_snd]
    intro h
    have := DFunLike.congr_fun h (0, 1)
    norm_num at this

/-- On the regular part of one component away from the other components, transverse slice order
is independent of the point and transverse direction.
Source: Gunning--Rossi II.B, Theorems 3--6; Chirka §2.3. -/
theorem spec_transverseOrder_constant {k : ℕ}
    {f u : (Fin n → ℂ) × ℂ → ℂ}
    {P : Fin k → (Fin n → ℂ) × ℂ → ℂ} {m : Fin k → ℕ}
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) (hP : ∀ i, AnalyticAt ℂ (P i) 0)
    (hcP : Pairwise (fun i j ↦ IsCoprimeAt (P i) (P j) 0))
    (hm : ∀ i, 0 < m i) (hfac : f =ᶠ[nhds 0] fun y ↦ u y * ∏ i, (P i y) ^ (m i)) :
    ∀ᶠ y in nhds 0, ∀ᶠ z in nhds 0, ∀ i,
      P i y = 0 → (∀ j, j ≠ i → P j y ≠ 0) →
      P i z = 0 → (∀ j, j ≠ i → P j z ≠ 0) →
      ∀ a b : (Fin n → ℂ) × ℂ, fderiv ℂ (P i) y a ≠ 0 → fderiv ℂ (P i) z b ≠ 0 →
        analyticOrderAt (fun t : ℂ ↦ f (y + t • a)) 0 =
          analyticOrderAt (fun t : ℂ ↦ f (z + t • b)) 0 :=
  spec_transverseOrder_constant_aux hu hu0 hP hcP hm hfac

example : analyticOrderAt (fun t : ℂ ↦ t ^ 3 * (t - 1)) 0 =
    analyticOrderAt (fun t : ℂ ↦ (-2 : ℂ) * t ^ 3) 0 := by
  have hleft : analyticOrderAt (fun t : ℂ ↦ t ^ 3 * (t - 1)) 0 = 3 :=
    ((analyticAt_id.pow 3).mul (analyticAt_id.sub analyticAt_const)).analyticOrderAt_eq_natCast.2
      ⟨fun t ↦ t - 1, analyticAt_id.sub analyticAt_const, by norm_num,
        Eventually.of_forall fun t ↦ by ring⟩
  have hright : analyticOrderAt (fun t : ℂ ↦ (-2 : ℂ) * t ^ 3) 0 = 3 :=
    (analyticAt_const.mul (analyticAt_id.pow 3)).analyticOrderAt_eq_natCast.2
      ⟨fun _ ↦ -2, analyticAt_const, by norm_num, Eventually.of_forall fun t ↦ by ring⟩
  exact hleft.trans hright.symm

end HodgeLean.Foundations.AnalyticDivisorAlgebraic7
