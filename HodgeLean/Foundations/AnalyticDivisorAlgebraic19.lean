import HodgeLean.Foundations.AnalyticDivisorAlgebraic19Proofs

/-! # Nearby factor groups and ambient matching

This stage connects stage seventeen's ambient matching to stage eighteen's propagation of
coprimality.  The result says that factors descended from distinct selected groups at the anchor
cannot be sent to the same irreducible member of an ambient decomposition nearby.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic19

open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic17

/-- Coprimality propagation in the product coordinates used by local divisor data.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B,
Theorems 3--6 and III.A, Theorem 1. -/
theorem gaga19_pair_propagation_product (n : ℕ) (p : (Fin n → ℂ) × ℂ)
    (F G : (Fin n → ℂ) × ℂ → ℂ)
    (hF : AnalyticAt ℂ F p) (hG : AnalyticAt ℂ G p)
    (hiF : IsIrreducibleAt F p) (hiG : IsIrreducibleAt G p)
    (hc : IsCoprimeAt F G p) :
    ∀ᶠ q in nhds p, IsCoprimeAt F G q ∧
      ∀ (k l : ℕ) (u v : (Fin n → ℂ) × ℂ → ℂ)
        (Q : Fin k → (Fin n → ℂ) × ℂ → ℂ)
        (R : Fin l → (Fin n → ℂ) × ℂ → ℂ)
        (d : Fin k → ℕ) (e : Fin l → ℕ),
        AnalyticAt ℂ u q → u q ≠ 0 → AnalyticAt ℂ v q → v q ≠ 0 →
        (∀ j, AnalyticAt ℂ (Q j) q ∧ IsIrreducibleAt (Q j) q ∧ 0 < d j) →
        (∀ j, AnalyticAt ℂ (R j) q ∧ IsIrreducibleAt (R j) q ∧ 0 < e j) →
        Pairwise (fun j j' ↦ IsCoprimeAt (Q j) (Q j') q) →
        Pairwise (fun j j' ↦ IsCoprimeAt (R j) (R j') q) →
        (F =ᶠ[nhds q] fun z ↦ u z * ∏ j, Q j z ^ d j) →
        (G =ᶠ[nhds q] fun z ↦ v z * ∏ j, R j z ^ e j) →
        ∀ j j', ¬ AreAssociatedAt (Q j) (R j') q :=
  gaga19_pair_propagation_product_aux n p F G hF hG hiF hiG hc

/-- Factors descended from distinct selected groups match distinct ambient factors nearby.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B,
Theorems 3--6 and III.A, Theorem 1; `spec_nearby_factor_matching` and
`gaga19_pair_propagation_product`. -/
theorem spec_nearby_distinct_group_matching {n r : ℕ} {ι : Type*}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (i : ι) {p : (Fin n → ℂ) × ℂ}
    {v : (Fin n → ℂ) × ℂ → ℂ} {P : Fin r → (Fin n → ℂ) × ℂ → ℂ}
    {b : Fin r → ℕ} (hvP : AnalyticAt ℂ v p) (hv0P : v p ≠ 0)
    (hPp : ∀ a, AnalyticAt ℂ (P a) p) (hirr : ∀ a, IsIrreducibleAt (P a) p)
    (hb : ∀ a, 0 < b a) (hcop : Pairwise (fun a c ↦ IsCoprimeAt (P a) (P c) p)) :
    ∀ᶠ q in nhds p, ∀ (N : Set ((Fin n → ℂ) × ℂ)), IsOpen N → N ∈ nhds p →
      N ⊆ V i → q ∈ N → AnalyticOnNhd ℂ v N →
      (∀ a, AnalyticOnNhd ℂ (P a) N) →
      (∀ y ∈ N, f i y = v y * ∏ a, P a y ^ b a) →
      ∀ (a c : Fin r), a ≠ c → P a q = 0 → P c q = 0 →
      ∀ (ka kc t : ℕ) (ua uc w : (Fin n → ℂ) × ℂ → ℂ)
        (Qa : Fin ka → (Fin n → ℂ) × ℂ → ℂ)
        (Qc : Fin kc → (Fin n → ℂ) × ℂ → ℂ)
        (R : Fin t → (Fin n → ℂ) × ℂ → ℂ)
        (da : Fin ka → ℕ) (dc : Fin kc → ℕ) (e : Fin t → ℕ),
        AnalyticAt ℂ ua q → ua q ≠ 0 →
        (∀ j, AnalyticAt ℂ (Qa j) q ∧ IsIrreducibleAt (Qa j) q ∧ 0 < da j) →
        Pairwise (fun j l ↦ IsCoprimeAt (Qa j) (Qa l) q) →
        (P a =ᶠ[nhds q] fun y ↦ ua y * ∏ j, Qa j y ^ da j) →
        AnalyticAt ℂ uc q → uc q ≠ 0 →
        (∀ j, AnalyticAt ℂ (Qc j) q ∧ IsIrreducibleAt (Qc j) q ∧ 0 < dc j) →
        Pairwise (fun j l ↦ IsCoprimeAt (Qc j) (Qc l) q) →
        (P c =ᶠ[nhds q] fun y ↦ uc y * ∏ j, Qc j y ^ dc j) →
        AnalyticAt ℂ w q → w q ≠ 0 →
        (∀ l, AnalyticAt ℂ (R l) q ∧ IsIrreducibleAt (R l) q ∧ 0 < e l) →
        Pairwise (fun l s ↦ IsCoprimeAt (R l) (R s) q) →
        (f i =ᶠ[nhds q] fun y ↦ w y * ∏ l, R l y ^ e l) →
        ∀ ja jc, ∃ la lc, AreAssociatedAt (Qa ja) (R la) q ∧
          AreAssociatedAt (Qc jc) (R lc) q ∧ la ≠ lc := by
  have hall : ∀ᶠ q in nhds p, ∀ a c, a ≠ c →
      IsCoprimeAt (P a) (P c) q ∧
        ∀ (ka kc : ℕ) (ua uc : (Fin n → ℂ) × ℂ → ℂ)
          (Qa : Fin ka → (Fin n → ℂ) × ℂ → ℂ)
          (Qc : Fin kc → (Fin n → ℂ) × ℂ → ℂ)
          (da : Fin ka → ℕ) (dc : Fin kc → ℕ),
          AnalyticAt ℂ ua q → ua q ≠ 0 → AnalyticAt ℂ uc q → uc q ≠ 0 →
          (∀ j, AnalyticAt ℂ (Qa j) q ∧ IsIrreducibleAt (Qa j) q ∧ 0 < da j) →
          (∀ j, AnalyticAt ℂ (Qc j) q ∧ IsIrreducibleAt (Qc j) q ∧ 0 < dc j) →
          Pairwise (fun j j' ↦ IsCoprimeAt (Qa j) (Qa j') q) →
          Pairwise (fun j j' ↦ IsCoprimeAt (Qc j) (Qc j') q) →
          (P a =ᶠ[nhds q] fun z ↦ ua z * ∏ j, Qa j z ^ da j) →
          (P c =ᶠ[nhds q] fun z ↦ uc z * ∏ j, Qc j z ^ dc j) →
          ∀ j j', ¬ AreAssociatedAt (Qa j) (Qc j') q := by
    apply eventually_all.mpr
    intro a
    apply eventually_all.mpr
    intro c
    by_cases hac : a = c
    · exact Eventually.of_forall fun _ hne ↦ False.elim (hne hac)
    · exact (gaga19_pair_propagation_product n p (P a) (P c)
        (hPp a) (hPp c) (hirr a) (hirr c) (hcop hac)).mono fun _ h _ ↦ h
  filter_upwards [hall] with q hq
  intro N hNo hNp hNV hqN hv hP hfac a c hac hza hzc ka kc t ua uc w Qa Qc R da dc e
    hua hua0 hQa hcQa hfa huc huc0 hQc hcQc hfc hw hw0 hR hcR hfR ja jc
  have hdis := (hq a c hac).2 ka kc ua uc Qa Qc da dc hua hua0 huc huc0
    hQa hQc hcQa hcQc hfa hfc
  obtain ⟨la, hla⟩ := spec_nearby_factor_matching hD i hNo hNp hNV hqN hv hv0P hP hirr hb
    hcop hfac a hza hua hua0 hQa hcQa hfa hw hw0 hR hcR hfR ja
  obtain ⟨lc, hlc⟩ := spec_nearby_factor_matching hD i hNo hNp hNV hqN hv hv0P hP hirr hb
    hcop hfac c hzc huc huc0 hQc hcQc hfc hw hw0 hR hcR hfR jc
  refine ⟨la, lc, hla, hlc, ?_⟩
  intro heq
  apply hdis ja jc
  exact gaga19_associated_of_common_right_aux hla (heq ▸ hlc)

-- The product-coordinate propagation input is inhabited by the two axes of the crossing.
example : ∀ᶠ q in nhds (0 : (Fin 1 → ℂ) × ℂ),
    IsCoprimeAt (gaga17_crossingFactors 0) (gaga17_crossingFactors 1) q ∧
      ∀ (k l : ℕ) (u v : (Fin 1 → ℂ) × ℂ → ℂ)
        (Q : Fin k → (Fin 1 → ℂ) × ℂ → ℂ)
        (R : Fin l → (Fin 1 → ℂ) × ℂ → ℂ)
        (d : Fin k → ℕ) (e : Fin l → ℕ),
        AnalyticAt ℂ u q → u q ≠ 0 → AnalyticAt ℂ v q → v q ≠ 0 →
        (∀ j, AnalyticAt ℂ (Q j) q ∧ IsIrreducibleAt (Q j) q ∧ 0 < d j) →
        (∀ j, AnalyticAt ℂ (R j) q ∧ IsIrreducibleAt (R j) q ∧ 0 < e j) →
        Pairwise (fun j j' ↦ IsCoprimeAt (Q j) (Q j') q) →
        Pairwise (fun j j' ↦ IsCoprimeAt (R j) (R j') q) →
        (gaga17_crossingFactors 0 =ᶠ[nhds q] fun z ↦ u z * ∏ j, Q j z ^ d j) →
        (gaga17_crossingFactors 1 =ᶠ[nhds q] fun z ↦ v z * ∏ j, R j z ^ e j) →
        ∀ j j', ¬ AreAssociatedAt (Q j) (R j') q := by
  obtain ⟨_, hP, hiP, hcP, _⟩ := gaga17_crossing_data
  exact gaga19_pair_propagation_product 1 0 _ _
    (hP 0 0 (mem_univ _)) (hP 1 0 (mem_univ _)) (hiP 0) (hiP 1)
    (hcP (by decide))

-- Both singleton groups at the crossing match distinct members of the same ambient pair.
example : ∃ la lc : Fin 2,
    AreAssociatedAt (gaga17_crossingFactors 0) (gaga17_crossingFactors la) 0 ∧
    AreAssociatedAt (gaga17_crossingFactors 1) (gaga17_crossingFactors lc) 0 ∧ la ≠ lc := by
  obtain ⟨hD, hP, hiP, hcP, _⟩ := gaga17_crossing_data
  have hfac : ∀ y ∈ (univ : Set ((Fin 1 → ℂ) × ℂ)),
      y.1 0 * y.2 = (1 : ℂ) * ∏ a, gaga17_crossingFactors a y ^ (1 : ℕ) := by
    intro y _
    simp [gaga17_crossingFactors, Fin.prod_univ_two]
  have hQ : ∀ a : Fin 2, ∀ _j : Fin 1,
      AnalyticAt ℂ (gaga17_crossingFactors a) 0 ∧
      IsIrreducibleAt (gaga17_crossingFactors a) 0 ∧ 0 < (1 : ℕ) :=
    fun a _ ↦ ⟨hP a 0 (mem_univ _), hiP a, Nat.zero_lt_one⟩
  have hcQ : ∀ a : Fin 2, Pairwise (fun _ _ : Fin 1 ↦ IsCoprimeAt
      (gaga17_crossingFactors a) (gaga17_crossingFactors a) 0) := by
    intro _ j l hne
    exact (hne (Subsingleton.elim j l)).elim
  have hfacQ : ∀ a : Fin 2, gaga17_crossingFactors a =ᶠ[𝓝 0]
      fun y ↦ (1 : ℂ) * ∏ _j : Fin 1, gaga17_crossingFactors a y ^ (1 : ℕ) := by
    intro a
    exact Eventually.of_forall fun _ ↦ by simp
  have hm := (spec_nearby_distinct_group_matching hD () (p := 0)
    (v := fun _ ↦ 1) analyticAt_const one_ne_zero
    (fun a ↦ hP a 0 (mem_univ _)) hiP (fun _ ↦ Nat.zero_lt_one) hcP).self_of_nhds
  exact hm univ isOpen_univ Filter.univ_mem subset_rfl (mem_univ _)
    analyticOnNhd_const hP hfac 0 1 (by decide)
    (AnalyticDivisorAlgebraic18.gaga18_coordinate_data.1 0).2.1
    (AnalyticDivisorAlgebraic18.gaga18_coordinate_data.1 1).2.1
    1 1 2 (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ 1)
    (fun _ ↦ gaga17_crossingFactors 0) (fun _ ↦ gaga17_crossingFactors 1)
    gaga17_crossingFactors (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ 1)
    analyticAt_const one_ne_zero (hQ 0) (hcQ 0) (hfacQ 0)
    analyticAt_const one_ne_zero (hQ 1) (hcQ 1) (hfacQ 1)
    analyticAt_const one_ne_zero
    (fun l ↦ ⟨hP l 0 (mem_univ _), hiP l, Nat.zero_lt_one⟩) hcP
    (Eventually.of_forall fun y ↦ hfac y (mem_univ _)) 0 0

end HodgeLean.Foundations.AnalyticDivisorAlgebraic19
