import HodgeLean.Foundations.AnalyticDivisorAlgebraic17Proofs

/-! # Nearby factor grouping and local-component compatibility

Implication from a stage-fourteen decomposition at `p`, represented on an open neighbourhood
`N` of `p` inside a divisor chart, to divisibility, decomposition, and factor matching at a zero
`q ∈ N` of a selected member. Matching compares that member's factors with a separate ambient
decomposition at `q` using analytic association. Component compatibility uses stage sixteen's
actual support intersections. Global local finiteness and algebraization are not claimed.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic17

open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic16

/-- The selected member of the decomposition at `p` divides the chart equation at `q`.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B,
Theorems 3--6 (factorization in the local analytic ring); Chirka, *Complex Analytic Sets*, §2.3. -/
theorem spec_nearby_selected_factor_divides {n r : ℕ} {ι : Type*}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (i : ι) {p q : (Fin n → ℂ) × ℂ} {N : Set ((Fin n → ℂ) × ℂ)}
    (hNo : IsOpen N) (hNp : N ∈ 𝓝 p) (hNV : N ⊆ V i) (hqN : q ∈ N)
    {v : (Fin n → ℂ) × ℂ → ℂ} {P : Fin r → (Fin n → ℂ) × ℂ → ℂ}
    {b : Fin r → ℕ} (hv : AnalyticOnNhd ℂ v N) (hv0 : v p ≠ 0)
    (hP : ∀ a, AnalyticOnNhd ℂ (P a) N)
    (hirr : ∀ a, IsIrreducibleAt (P a) p) (hb : ∀ a, 0 < b a)
    (hcop : Pairwise (fun a c ↦ IsCoprimeAt (P a) (P c) p))
    (hfacN : ∀ y ∈ N, f i y = v y * ∏ a, P a y ^ b a)
    (a : Fin r) (hzero : P a q = 0) :
    ∃ s : (Fin n → ℂ) × ℂ → ℂ, AnalyticAt ℂ s q ∧
      f i =ᶠ[𝓝 q] fun y ↦ P a y * s y :=
  spec_nearby_selected_factor_divides_aux hD i hNo hNp hNV hqN hv hv0 hP hirr hb hcop hfacN a hzero

/-- A selected member of the decomposition at `p` has a decomposition at its nearby zero `q`.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B,
Theorems 3--6 (factorization in the local analytic ring); Chirka, *Complex Analytic Sets*, §2.3. -/
theorem spec_nearby_factor_decomposition {n r : ℕ} {ι : Type*}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (i : ι) {p q : (Fin n → ℂ) × ℂ} {N : Set ((Fin n → ℂ) × ℂ)}
    (hNo : IsOpen N) (hNp : N ∈ 𝓝 p) (hNV : N ⊆ V i) (hqN : q ∈ N)
    {v : (Fin n → ℂ) × ℂ → ℂ} {P : Fin r → (Fin n → ℂ) × ℂ → ℂ}
    {b : Fin r → ℕ} (hv : AnalyticOnNhd ℂ v N) (hv0 : v p ≠ 0)
    (hP : ∀ a, AnalyticOnNhd ℂ (P a) N)
    (hirr : ∀ a, IsIrreducibleAt (P a) p) (hb : ∀ a, 0 < b a)
    (hcop : Pairwise (fun a c ↦ IsCoprimeAt (P a) (P c) p))
    (hfacN : ∀ y ∈ N, f i y = v y * ∏ a, P a y ^ b a)
    (a : Fin r) (hzero : P a q = 0) :
    ∃ k : ℕ, ∃ u : (Fin n → ℂ) × ℂ → ℂ,
      ∃ Q : Fin k → (Fin n → ℂ) × ℂ → ℂ, ∃ d : Fin k → ℕ,
        AnalyticAt ℂ u q ∧ u q ≠ 0 ∧
        (∀ j, AnalyticAt ℂ (Q j) q ∧ IsIrreducibleAt (Q j) q ∧ 0 < d j) ∧
        Pairwise (fun j l ↦ IsCoprimeAt (Q j) (Q l) q) ∧
        P a =ᶠ[𝓝 q] fun y ↦ u y * ∏ j, Q j y ^ d j :=
  spec_nearby_factor_decomposition_aux hD i hNo hNp hNV hqN hv hv0 hP hirr hb hcop hfacN a hzero

/-- Each irreducible factor of the selected member at `q` divides the ambient equation at `q`.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B,
Theorems 3--6 (factorization in the local analytic ring); Chirka, *Complex Analytic Sets*, §2.3. -/
theorem spec_nearby_factor_divides {n r : ℕ} {ι : Type*}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (i : ι) {p q : (Fin n → ℂ) × ℂ} {N : Set ((Fin n → ℂ) × ℂ)}
    (hNo : IsOpen N) (hNp : N ∈ 𝓝 p) (hNV : N ⊆ V i) (hqN : q ∈ N)
    {v : (Fin n → ℂ) × ℂ → ℂ} {P : Fin r → (Fin n → ℂ) × ℂ → ℂ}
    {b : Fin r → ℕ} (hv : AnalyticOnNhd ℂ v N) (hv0 : v p ≠ 0)
    (hP : ∀ a, AnalyticOnNhd ℂ (P a) N)
    (hirr : ∀ a, IsIrreducibleAt (P a) p) (hb : ∀ a, 0 < b a)
    (hcop : Pairwise (fun a c ↦ IsCoprimeAt (P a) (P c) p))
    (hfacN : ∀ y ∈ N, f i y = v y * ∏ a, P a y ^ b a)
    (a : Fin r) (hzero : P a q = 0)
    {k : ℕ} {u : (Fin n → ℂ) × ℂ → ℂ}
    {Q : Fin k → (Fin n → ℂ) × ℂ → ℂ} {d : Fin k → ℕ}
    (hu : AnalyticAt ℂ u q) (hu0 : u q ≠ 0)
    (hQ : ∀ j, AnalyticAt ℂ (Q j) q ∧ IsIrreducibleAt (Q j) q ∧ 0 < d j)
    (hcQ : Pairwise (fun j l ↦ IsCoprimeAt (Q j) (Q l) q))
    (hfacQ : P a =ᶠ[𝓝 q] fun y ↦ u y * ∏ j, Q j y ^ d j) (j : Fin k) :
    ∃ s : (Fin n → ℂ) × ℂ → ℂ, AnalyticAt ℂ s q ∧
      f i =ᶠ[𝓝 q] fun y ↦ Q j y * s y :=
  spec_nearby_factor_divides_aux hD i hNo hNp hNV hqN hv hv0 hP hirr hb hcop hfacN a hzero hu hu0 hQ hcQ hfacQ j

/-- An irreducible analytic divisor of a unit times a finite product divides one factor.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B,
Theorems 3--6 (factorization in the local analytic ring); Chirka, *Complex Analytic Sets*, §2.3. -/
theorem gaga17_prime_divides_factor {n t : ℕ}
    {F A w s : (Fin n → ℂ) × ℂ → ℂ} {q : (Fin n → ℂ) × ℂ}
    {R : Fin t → (Fin n → ℂ) × ℂ → ℂ} {e : Fin t → ℕ}
    (hA : AnalyticAt ℂ A q) (hiA : IsIrreducibleAt A q)
    (hs : AnalyticAt ℂ s q) (hdiv : F =ᶠ[𝓝 q] fun y ↦ A y * s y)
    (hw : AnalyticAt ℂ w q) (hw0 : w q ≠ 0)
    (hR : ∀ l, AnalyticAt ℂ (R l) q)
    (hfac : F =ᶠ[𝓝 q] fun y ↦ w y * ∏ l, R l y ^ e l) :
    ∃ l : Fin t, ∃ c : (Fin n → ℂ) × ℂ → ℂ, AnalyticAt ℂ c q ∧
      R l =ᶠ[𝓝 q] fun y ↦ A y * c y :=
  gaga17_prime_divides_factor_aux hA hiA hs hdiv hw hw0 hR hfac

/-- An irreducible analytic divisor of an irreducible germ is associated to it.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B,
Theorems 3--6 (factorization in the local analytic ring); Chirka, *Complex Analytic Sets*, §2.3. -/
theorem gaga17_associated_of_irreducible_divides {n : ℕ}
    {A B c : (Fin n → ℂ) × ℂ → ℂ} {q : (Fin n → ℂ) × ℂ}
    (hA : AnalyticAt ℂ A q) (hiA : IsIrreducibleAt A q)
    (hB : AnalyticAt ℂ B q) (hiB : IsIrreducibleAt B q)
    (hc : AnalyticAt ℂ c q) (hdiv : B =ᶠ[𝓝 q] fun y ↦ A y * c y) :
    AreAssociatedAt A B q :=
  gaga17_associated_of_irreducible_divides_aux hA hiA hB hiB hc hdiv

/-- Each factor of the selected member at `q` matches a factor of the ambient decomposition at `q`.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B,
Theorems 3--6 (factorization in the local analytic ring); Chirka, *Complex Analytic Sets*, §2.3. -/
theorem spec_nearby_factor_matching {n r : ℕ} {ι : Type*}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (i : ι) {p q : (Fin n → ℂ) × ℂ} {N : Set ((Fin n → ℂ) × ℂ)}
    (hNo : IsOpen N) (hNp : N ∈ 𝓝 p) (hNV : N ⊆ V i) (hqN : q ∈ N)
    {v : (Fin n → ℂ) × ℂ → ℂ} {P : Fin r → (Fin n → ℂ) × ℂ → ℂ}
    {b : Fin r → ℕ} (hv : AnalyticOnNhd ℂ v N) (hv0 : v p ≠ 0)
    (hP : ∀ a, AnalyticOnNhd ℂ (P a) N)
    (hirr : ∀ a, IsIrreducibleAt (P a) p) (hb : ∀ a, 0 < b a)
    (hcop : Pairwise (fun a c ↦ IsCoprimeAt (P a) (P c) p))
    (hfacN : ∀ y ∈ N, f i y = v y * ∏ a, P a y ^ b a)
    (a : Fin r) (hzero : P a q = 0)
    {k : ℕ} {u : (Fin n → ℂ) × ℂ → ℂ}
    {Q : Fin k → (Fin n → ℂ) × ℂ → ℂ} {d : Fin k → ℕ}
    (hu : AnalyticAt ℂ u q) (hu0 : u q ≠ 0)
    (hQ : ∀ j, AnalyticAt ℂ (Q j) q ∧ IsIrreducibleAt (Q j) q ∧ 0 < d j)
    (hcQ : Pairwise (fun j l ↦ IsCoprimeAt (Q j) (Q l) q))
    (hfacQ : P a =ᶠ[𝓝 q] fun y ↦ u y * ∏ j, Q j y ^ d j)
    {t : ℕ} {w : (Fin n → ℂ) × ℂ → ℂ}
    {R : Fin t → (Fin n → ℂ) × ℂ → ℂ} {e : Fin t → ℕ}
    (hw : AnalyticAt ℂ w q) (hw0 : w q ≠ 0)
    (hR : ∀ l, AnalyticAt ℂ (R l) q ∧ IsIrreducibleAt (R l) q ∧ 0 < e l)
    (hcR : Pairwise (fun l s ↦ IsCoprimeAt (R l) (R s) q))
    (hfacR : f i =ᶠ[𝓝 q] fun y ↦ w y * ∏ l, R l y ^ e l) :
    ∀ j, ∃ l, AreAssociatedAt (Q j) (R l) q :=
  spec_nearby_factor_matching_aux hD i hNo hNp hNV hqN hv hv0 hP hirr hb hcop hfacN a hzero hu hu0 hQ hcQ hfacQ hw hw0 hR hcR hfacR

/-- Near `q`, the fixed selected component is the union of the components of its factors at `q`.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B,
Theorems 3--6 (factorization in the local analytic ring); Chirka, *Complex Analytic Sets*, §2.3. -/
theorem spec_nearby_component_grouping {n r : ℕ} {ι : Type*}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (i : ι) {p q : (Fin n → ℂ) × ℂ} {N : Set ((Fin n → ℂ) × ℂ)}
    (hNo : IsOpen N) (hNp : N ∈ 𝓝 p) (hNV : N ⊆ V i) (hqN : q ∈ N)
    {v : (Fin n → ℂ) × ℂ → ℂ} {P : Fin r → (Fin n → ℂ) × ℂ → ℂ}
    {b : Fin r → ℕ} (hv : AnalyticOnNhd ℂ v N) (hv0 : v p ≠ 0)
    (hP : ∀ a, AnalyticOnNhd ℂ (P a) N)
    (hirr : ∀ a, IsIrreducibleAt (P a) p) (hb : ∀ a, 0 < b a)
    (hcop : Pairwise (fun a c ↦ IsCoprimeAt (P a) (P c) p))
    (hfacN : ∀ y ∈ N, f i y = v y * ∏ a, P a y ^ b a)
    (a : Fin r) (hzero : P a q = 0)
    {k : ℕ} {u : (Fin n → ℂ) × ℂ → ℂ}
    {Q : Fin k → (Fin n → ℂ) × ℂ → ℂ} {d : Fin k → ℕ}
    (hu : AnalyticAt ℂ u q) (hu0 : u q ≠ 0)
    (hQ : ∀ j, AnalyticAt ℂ (Q j) q ∧ IsIrreducibleAt (Q j) q ∧ 0 < d j)
    (hcQ : Pairwise (fun j l ↦ IsCoprimeAt (Q j) (Q l) q))
    (hfacQ : P a =ᶠ[𝓝 q] fun y ↦ u y * ∏ j, Q j y ^ d j) :
    ∃ W : Set ((Fin n → ℂ) × ℂ), IsOpen W ∧ q ∈ W ∧ W ⊆ N ∧
      W ∩ gaga16_localComponent V f i (P a) =
        W ∩ gaga17_groupedLocalComponent V f i Q :=
  spec_nearby_component_grouping_aux hD i hNo hNp hNV hqN hv hv0 hP hirr hb hcop hfacN a hzero hu hu0 hQ hcQ hfacQ

/-- The normal crossing equation has genuine local divisor data and two coprime factors at zero.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1
(coordinate divisors); Gunning--Rossi, II.B, Theorems 3--6. -/
theorem gaga17_crossing_data :
    IsLocalDivisorData (univ : Set ((Fin 1 → ℂ) × ℂ)) (fun _ : Unit ↦ univ)
        (fun _ y ↦ y.1 0 * y.2) ∧
      (∀ a, AnalyticOnNhd ℂ (gaga17_crossingFactors a) univ) ∧
      (∀ a, IsIrreducibleAt (gaga17_crossingFactors a) 0) ∧
      Pairwise (fun a b ↦ IsCoprimeAt (gaga17_crossingFactors a)
        (gaga17_crossingFactors b) 0) ∧
      ∀ c : ℂ, IsIrreducibleAt (gaga17_crossingFactors 0) (0, c) :=
  gaga17_crossing_data_aux 

/-- A coordinate hyperplane with positive multiplicity is local divisor data in every dimension.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1
(coordinate divisors); Gunning--Rossi, II.B, Theorems 3--6. -/
theorem gaga17_axis_power_data (n m : ℕ) (hm : 0 < m) :
    IsLocalDivisorData (univ : Set ((Fin n → ℂ) × ℂ)) (fun _ : Unit ↦ univ)
        (fun _ y ↦ y.2 ^ m) ∧
      ∀ q : (Fin n → ℂ) × ℂ, q.2 = 0 → IsIrreducibleAt (fun y ↦ y.2) q :=
  gaga17_axis_power_data_aux n m hm

/-! ## Concrete coordinate checks

The fixtures above specify actual local divisor data, with no assumed divisor or factorization
premises. These examples feed that data into the nearby statements.
-/

-- At the origin the equation has the displayed two coprime irreducible factors.
example : IsLocalDivisorData (univ : Set ((Fin 1 → ℂ) × ℂ))
    (fun _ : Unit ↦ univ) (fun _ y ↦ y.1 0 * y.2) ∧
    (∀ a, IsIrreducibleAt (gaga17_crossingFactors a) 0) ∧
    IsCoprimeAt (gaga17_crossingFactors 0) (gaga17_crossingFactors 1) 0 ∧
    (∀ y : (Fin 1 → ℂ) × ℂ,
      y.1 0 * y.2 = ∏ a : Fin 2, gaga17_crossingFactors a y ^ (1 : ℕ)) := by
  refine ⟨gaga17_crossing_data.1, gaga17_crossing_data.2.2.1,
    gaga17_crossing_data.2.2.2.1 (by decide), ?_⟩
  intro y
  simp [gaga17_crossingFactors, Fin.prod_univ_two]

-- Transport from the origin to every point of the first axis, including the crossing.
example (c : ℂ) : ∃ s : (Fin 1 → ℂ) × ℂ → ℂ, AnalyticAt ℂ s (0, c) ∧
    (fun y : (Fin 1 → ℂ) × ℂ ↦ y.1 0 * y.2) =ᶠ[𝓝 (0, c)] fun y ↦ y.1 0 * s y := by
  obtain ⟨hD, hP, hiP, hcP, haxis⟩ := gaga17_crossing_data
  have hfac : ∀ y ∈ (univ : Set ((Fin 1 → ℂ) × ℂ)),
      y.1 0 * y.2 = (1 : ℂ) * ∏ a, gaga17_crossingFactors a y ^ (1 : ℕ) := by
    intro y _
    simp [gaga17_crossingFactors, Fin.prod_univ_two]
  exact spec_nearby_selected_factor_divides hD () (p := 0) (q := (0, c)) isOpen_univ
    Filter.univ_mem subset_rfl (mem_univ _) analyticOnNhd_const one_ne_zero
    hP hiP (fun _ ↦ Nat.zero_lt_one) hcP hfac (0 : Fin 2) rfl

-- Decomposition is applied to the selected first factor, not to the whole crossing equation.
example (c : ℂ) :
    ∃ k : ℕ, ∃ u : (Fin 1 → ℂ) × ℂ → ℂ,
      ∃ Q : Fin k → (Fin 1 → ℂ) × ℂ → ℂ, ∃ d : Fin k → ℕ,
        AnalyticAt ℂ u (0, c) ∧ u (0, c) ≠ 0 ∧
        (∀ j, AnalyticAt ℂ (Q j) (0, c) ∧ IsIrreducibleAt (Q j) (0, c) ∧ 0 < d j) ∧
        Pairwise (fun j l ↦ IsCoprimeAt (Q j) (Q l) (0, c)) ∧
        gaga17_crossingFactors 0 =ᶠ[𝓝 (0, c)] fun y ↦ u y * ∏ j, Q j y ^ d j := by
  obtain ⟨hD, hP, hiP, hcP, haxis⟩ := gaga17_crossing_data
  have hfac : ∀ y ∈ (univ : Set ((Fin 1 → ℂ) × ℂ)),
      y.1 0 * y.2 = (1 : ℂ) * ∏ a, gaga17_crossingFactors a y ^ (1 : ℕ) := by
    intro y _
    simp [gaga17_crossingFactors, Fin.prod_univ_two]
  exact spec_nearby_factor_decomposition hD () (p := 0) (q := (0, c)) isOpen_univ
    Filter.univ_mem subset_rfl (mem_univ _) analyticOnNhd_const one_ne_zero
    hP hiP (fun _ ↦ Nat.zero_lt_one) hcP hfac (0 : Fin 2) rfl

-- The single factor of the selected coordinate still divides the whole equation at the crossing.
example : ∃ s : (Fin 1 → ℂ) × ℂ → ℂ, AnalyticAt ℂ s (0, 0) ∧
    (fun y : (Fin 1 → ℂ) × ℂ ↦ y.1 0 * y.2) =ᶠ[𝓝 (0, 0)] fun y ↦ y.1 0 * s y := by
  let c : ℂ := 0
  obtain ⟨hD, hP, hiP, hcP, haxis⟩ := gaga17_crossing_data
  have hfac : ∀ y ∈ (univ : Set ((Fin 1 → ℂ) × ℂ)),
      y.1 0 * y.2 = (1 : ℂ) * ∏ a, gaga17_crossingFactors a y ^ (1 : ℕ) := by
    intro y _
    simp [gaga17_crossingFactors, Fin.prod_univ_two]
  have hQ : ∀ j : Fin 1, AnalyticAt ℂ (gaga17_crossingFactors 0) (0, c) ∧
      IsIrreducibleAt (gaga17_crossingFactors 0) (0, c) ∧ 0 < (1 : ℕ) :=
    fun _ ↦ ⟨hP 0 _ (mem_univ _), haxis c, Nat.zero_lt_one⟩
  have hcQ : Pairwise (fun _ _ : Fin 1 ↦ IsCoprimeAt
      (gaga17_crossingFactors 0) (gaga17_crossingFactors 0) (0, c)) := by
    intro j l hne
    exact (hne (Subsingleton.elim j l)).elim
  have hfacQ : gaga17_crossingFactors 0 =ᶠ[𝓝 (0, c)]
      fun y ↦ (1 : ℂ) * ∏ _j : Fin 1, gaga17_crossingFactors 0 y ^ (1 : ℕ) := by
    filter_upwards [] with y
    simp
  exact spec_nearby_factor_divides hD () (p := 0) (q := (0, c)) isOpen_univ
    Filter.univ_mem subset_rfl (mem_univ _) analyticOnNhd_const one_ne_zero
    hP hiP (fun _ ↦ Nat.zero_lt_one) hcP hfac (0 : Fin 2) rfl
    analyticAt_const one_ne_zero hQ hcQ hfacQ (0 : Fin 1)

-- At a point on only the first axis, the ambient decomposition has one factor and unit z₂.
example (c : ℂ) (hc : c ≠ 0) :
    ∃ l : Fin 1, AreAssociatedAt (gaga17_crossingFactors 0)
      ((fun _ : Fin 1 ↦ gaga17_crossingFactors 0) l) (0, c) := by
  obtain ⟨hD, hP, hiP, hcP, haxis⟩ := gaga17_crossing_data
  have hfac : ∀ y ∈ (univ : Set ((Fin 1 → ℂ) × ℂ)),
      y.1 0 * y.2 = (1 : ℂ) * ∏ a, gaga17_crossingFactors a y ^ (1 : ℕ) := by
    intro y _
    simp [gaga17_crossingFactors, Fin.prod_univ_two]
  have hQ : ∀ j : Fin 1, AnalyticAt ℂ (gaga17_crossingFactors 0) (0, c) ∧
      IsIrreducibleAt (gaga17_crossingFactors 0) (0, c) ∧ 0 < (1 : ℕ) :=
    fun _ ↦ ⟨hP 0 _ (mem_univ _), haxis c, Nat.zero_lt_one⟩
  have hcQ : Pairwise (fun _ _ : Fin 1 ↦ IsCoprimeAt
      (gaga17_crossingFactors 0) (gaga17_crossingFactors 0) (0, c)) := by
    intro j l hne
    exact (hne (Subsingleton.elim j l)).elim
  have hfacQ : gaga17_crossingFactors 0 =ᶠ[𝓝 (0, c)]
      fun y ↦ (1 : ℂ) * ∏ _j : Fin 1, gaga17_crossingFactors 0 y ^ (1 : ℕ) := by
    filter_upwards [] with y
    simp
  have hfacR : (fun y : (Fin 1 → ℂ) × ℂ ↦ y.1 0 * y.2) =ᶠ[𝓝 (0, c)]
      fun y ↦ y.2 * ∏ _l : Fin 1, gaga17_crossingFactors 0 y ^ (1 : ℕ) := by
    filter_upwards [] with y
    simp [gaga17_crossingFactors, mul_comm]
  exact spec_nearby_factor_matching hD () (p := 0) (q := (0, c)) isOpen_univ
    Filter.univ_mem subset_rfl (mem_univ _) analyticOnNhd_const one_ne_zero
    hP hiP (fun _ ↦ Nat.zero_lt_one) hcP hfac (0 : Fin 2) rfl
    analyticAt_const one_ne_zero hQ hcQ hfacQ analyticAt_snd hc hQ hcQ hfacR (0 : Fin 1)

-- The same matching at the origin uses two ambient factors, not the one-factor chart above.
example : ∃ l : Fin 2,
    AreAssociatedAt (gaga17_crossingFactors 0) (gaga17_crossingFactors l) (0, 0) := by
  let c : ℂ := 0
  obtain ⟨hD, hP, hiP, hcP, haxis⟩ := gaga17_crossing_data
  have hfac : ∀ y ∈ (univ : Set ((Fin 1 → ℂ) × ℂ)),
      y.1 0 * y.2 = (1 : ℂ) * ∏ a, gaga17_crossingFactors a y ^ (1 : ℕ) := by
    intro y _
    simp [gaga17_crossingFactors, Fin.prod_univ_two]
  have hQ : ∀ j : Fin 1, AnalyticAt ℂ (gaga17_crossingFactors 0) (0, c) ∧
      IsIrreducibleAt (gaga17_crossingFactors 0) (0, c) ∧ 0 < (1 : ℕ) :=
    fun _ ↦ ⟨hP 0 _ (mem_univ _), haxis c, Nat.zero_lt_one⟩
  have hcQ : Pairwise (fun _ _ : Fin 1 ↦ IsCoprimeAt
      (gaga17_crossingFactors 0) (gaga17_crossingFactors 0) (0, c)) := by
    intro j l hne
    exact (hne (Subsingleton.elim j l)).elim
  have hfacQ : gaga17_crossingFactors 0 =ᶠ[𝓝 (0, c)]
      fun y ↦ (1 : ℂ) * ∏ _j : Fin 1, gaga17_crossingFactors 0 y ^ (1 : ℕ) := by
    filter_upwards [] with y
    simp
  exact spec_nearby_factor_matching hD () (p := 0) (q := (0, c)) isOpen_univ
    Filter.univ_mem subset_rfl (mem_univ _) analyticOnNhd_const one_ne_zero
    hP hiP (fun _ ↦ Nat.zero_lt_one) hcP hfac (0 : Fin 2) rfl
    analyticAt_const one_ne_zero hQ hcQ hfacQ analyticAt_const one_ne_zero
    (fun l ↦ ⟨hP l 0 (mem_univ _), hiP l, Nat.zero_lt_one⟩) hcP
    (Eventually.of_forall fun y ↦ hfac y (mem_univ _)) (0 : Fin 1)

-- Grouping to itself on the first axis; c ≠ 0 specializes this to a point on only that axis.
example (c : ℂ) : ∃ W : Set ((Fin 1 → ℂ) × ℂ), IsOpen W ∧ (0, c) ∈ W ∧
    W ⊆ univ ∧
    W ∩ gaga16_localComponent (fun _ : Unit ↦ univ)
      (fun _ y ↦ y.1 0 * y.2) () (gaga17_crossingFactors 0) =
    W ∩ gaga17_groupedLocalComponent (fun _ : Unit ↦ univ)
      (fun _ y ↦ y.1 0 * y.2) () (fun _ : Fin 1 ↦ gaga17_crossingFactors 0) := by
  obtain ⟨hD, hP, hiP, hcP, haxis⟩ := gaga17_crossing_data
  have hfac : ∀ y ∈ (univ : Set ((Fin 1 → ℂ) × ℂ)),
      y.1 0 * y.2 = (1 : ℂ) * ∏ a, gaga17_crossingFactors a y ^ (1 : ℕ) := by
    intro y _
    simp [gaga17_crossingFactors, Fin.prod_univ_two]
  have hQ : ∀ j : Fin 1, AnalyticAt ℂ (gaga17_crossingFactors 0) (0, c) ∧
      IsIrreducibleAt (gaga17_crossingFactors 0) (0, c) ∧ 0 < (1 : ℕ) :=
    fun _ ↦ ⟨hP 0 _ (mem_univ _), haxis c, Nat.zero_lt_one⟩
  have hcQ : Pairwise (fun _ _ : Fin 1 ↦ IsCoprimeAt
      (gaga17_crossingFactors 0) (gaga17_crossingFactors 0) (0, c)) := by
    intro j l hne
    exact (hne (Subsingleton.elim j l)).elim
  have hfacQ : gaga17_crossingFactors 0 =ᶠ[𝓝 (0, c)]
      fun y ↦ (1 : ℂ) * ∏ _j : Fin 1, gaga17_crossingFactors 0 y ^ (1 : ℕ) := by
    filter_upwards [] with y
    simp
  exact spec_nearby_component_grouping hD () (p := 0) (q := (0, c)) isOpen_univ
    Filter.univ_mem subset_rfl (mem_univ _) analyticOnNhd_const one_ne_zero
    hP hiP (fun _ ↦ Nat.zero_lt_one) hcP hfac (0 : Fin 2) rfl
    analyticAt_const one_ne_zero hQ hcQ hfacQ

-- Direct check of the prime-product step with the actual two coordinate factors.
example : ∃ l : Fin 2, ∃ s : (Fin 1 → ℂ) × ℂ → ℂ, AnalyticAt ℂ s 0 ∧
    gaga17_crossingFactors l =ᶠ[𝓝 0] fun y ↦ y.1 0 * s y := by
  obtain ⟨_, hP, hiP, _, _⟩ := gaga17_crossing_data
  exact gaga17_prime_divides_factor (e := fun _ ↦ 1) (hP 0 0 (mem_univ _)) (hiP 0)
    analyticAt_snd (Eventually.of_forall fun _ ↦ rfl)
    analyticAt_const one_ne_zero (fun l ↦ hP l 0 (mem_univ _))
    (Eventually.of_forall fun y ↦ by simp [gaga17_crossingFactors, Fin.prod_univ_two])

-- Association uses an analytic quotient, here the constant unit 1.
example (c : ℂ) : AreAssociatedAt (gaga17_crossingFactors 0)
    (gaga17_crossingFactors 0) (0, c) := by
  have hA := gaga17_crossing_data.2.1 0 (0, c) (mem_univ _)
  have hiA := gaga17_crossing_data.2.2.2.2 c
  exact gaga17_associated_of_irreducible_divides hA hiA hA hiA analyticAt_const
    (Eventually.of_forall fun _ ↦ (mul_one _).symm)

-- Positive multiplicity two and n = 0 are actual local data on the remaining complex coordinate.
example : IsLocalDivisorData (univ : Set ((Fin 0 → ℂ) × ℂ))
    (fun _ : Unit ↦ univ) (fun _ y ↦ y.2 ^ 2) :=
  (gaga17_axis_power_data 0 2 (by decide)).1

-- A hyperplane in every dimension, at any zero q, has one irreducible coordinate factor.
example (n : ℕ) (q : (Fin n → ℂ) × ℂ) (hq : q.2 = 0) :
    IsIrreducibleAt (fun y : (Fin n → ℂ) × ℂ ↦ y.2) q :=
  (gaga17_axis_power_data n 1 (by decide)).2 q hq

-- The square has the same one-factor support group, with exponent two retained at p.
example : ∃ W : Set ((Fin 0 → ℂ) × ℂ), IsOpen W ∧ (0 : (Fin 0 → ℂ) × ℂ) ∈ W ∧
    W ⊆ univ ∧
    W ∩ gaga16_localComponent (fun _ : Unit ↦ univ)
      (fun _ y ↦ y.2 ^ 2) () (fun y ↦ y.2) =
    W ∩ gaga17_groupedLocalComponent (fun _ : Unit ↦ univ)
      (fun _ y ↦ y.2 ^ 2) () (fun _ : Fin 1 ↦ fun y ↦ y.2) := by
  obtain ⟨hD, hi⟩ := gaga17_axis_power_data 0 2 (by decide)
  have hcop : Pairwise (fun _ _ : Fin 1 ↦ IsCoprimeAt
      (fun y : (Fin 0 → ℂ) × ℂ ↦ y.2) (fun y ↦ y.2) 0) := by
    intro j l hne
    exact (hne (Subsingleton.elim j l)).elim
  exact spec_nearby_component_grouping hD () (p := 0) (q := 0)
    isOpen_univ Filter.univ_mem subset_rfl (mem_univ _)
    analyticOnNhd_const one_ne_zero (fun _ : Fin 1 ↦ analyticOnNhd_snd)
    (fun _ ↦ hi 0 rfl) (b := fun _ ↦ 2) (fun _ ↦ by decide) hcop
    (by intro y _; simp) (0 : Fin 1) rfl analyticAt_const one_ne_zero
    (d := fun _ : Fin 1 ↦ 1) (fun _ ↦ ⟨analyticAt_snd, hi 0 rfl, Nat.zero_lt_one⟩)
    hcop (Eventually.of_forall fun y ↦ by simp)

end HodgeLean.Foundations.AnalyticDivisorAlgebraic17
