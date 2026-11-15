import HodgeLean.Foundations.Program.G32PropFourSixPacked0207
import HodgeLean.Foundations.Program.G32PropFourSixPacked0450
import HodgeLean.Foundations.Program.G32PropFourSixPacked0444
import HodgeLean.Foundations.Program.G32PropFourSixPacked0449
import HodgeLean.Foundations.Program.G32PropFourSixPacked0448
import HodgeLean.Foundations.Program.G32PropFourSixPacked0442
import HodgeLean.Foundations.Program.G32PropFourSixRowComparison
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0003

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000

def g32p_integrationLabel : g32p_G → Fin 102 :=
  Classical.choose g32p_literal_class_fibres

theorem g32p_integrationLabel_conj (g : g32p_G) :
    IsConj g (g32p_literalRepresentative (g32p_integrationLabel g)) :=
  (Classical.choose_spec g32p_literal_class_fibres).1 g

theorem g32p_integrationLabel_of_isConj {g : g32p_G} {c : Fin 102}
    (h : IsConj g (g32p_literalRepresentative c)) : g32p_integrationLabel g = c :=
  g32p_literalRepresentative_classes_injective
    (ConjClasses.mk_eq_mk_iff_isConj.mpr ((g32p_integrationLabel_conj g).symm.trans h))

theorem g32p_integrationLabel_rep (c : Fin 102) :
    g32p_integrationLabel (g32p_literalRepresentative c) = c :=
  g32p_integrationLabel_of_isConj (IsConj.refl _)

def g32p_integrationClassData : g32p_familiesClassData where
  label := g32p_integrationLabel
  identity := by
    apply g32p_integrationLabel_of_isConj
    have h : g32p_literalRepresentative 0 = 1 := rfl
    rw [h]
  card c := by
    rw [← Nat.card_eq_fintype_card]
    exact (Classical.choose_spec g32p_literal_class_fibres).2 c
  inverse g := by
    apply g32p_integrationLabel_of_isConj
    have hi : IsConj g⁻¹ (g32p_literalRepresentative (g32p_integrationLabel g))⁻¹ := by
      obtain ⟨a, ha⟩ := isConj_iff.mp (g32p_integrationLabel_conj g)
      apply isConj_iff.mpr
      exact ⟨a, by rw [← ha, conj_inv]⟩
    exact hi.trans (g32p_literalRepresentative_inverse _)

theorem g32p_integrationLabel_square (g : g32p_G) :
    g32p_integrationLabel (g * g) = g32p_familiesSquare (g32p_integrationLabel g) := by
  apply g32p_integrationLabel_of_isConj
  obtain ⟨a, ha⟩ := isConj_iff.mp (g32p_integrationLabel_conj g)
  have h : IsConj (g * g)
      (g32p_literalRepresentative (g32p_integrationLabel g) *
       g32p_literalRepresentative (g32p_integrationLabel g)) := by
    apply isConj_iff.mpr
    refine ⟨a, ?_⟩
    rw [← ha]
    group
  exact h.trans (g32p_integration_square_representative _)

theorem g32p_integrationLabel_branch (j : Fin 13) :
    g32p_integrationLabel (g32p_classDatum j) = g32p_familyCWBranchClass j := by
  fin_cases j <;> first
  | exact g32p_integrationLabel_of_isConj g32p_integrationBranch0_actual
  | exact g32p_integrationLabel_of_isConj g32p_integrationBranch1_actual
  | exact g32p_integrationLabel_of_isConj g32p_integrationBranch2_actual

#print axioms g32p_integrationClassData
#print axioms g32p_integrationLabel_square
#print axioms g32p_integrationLabel_branch
end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000

/-- Coordinate selection from the recorded character table.
Source: G32 v0.16, Proposition 4.6 and Appendix A. -/
def g32p_restrictionFamilyPair : Fin 44 → Fin 102 :=
  ![1, 3, 7, 5, 10, 13, 11, 16, 19, 22, 20, 28, 26, 34, 33, 36, 42, 44, 38, 40, 46, 49, 53, 54, 56, 58, 60, 64, 62, 67, 70, 68, 73, 74, 76, 80, 84, 82, 86, 88, 92, 94, 97, 100]

/-- Conjugate coordinate selection from the recorded character table.
Source: G32 v0.16, Proposition 4.6 and Appendix A. -/
def g32p_restrictionFamilyBar : Fin 44 → Fin 102 :=
  ![2, 4, 8, 6, 9, 14, 12, 17, 18, 23, 21, 29, 27, 35, 32, 37, 43, 45, 39, 41, 47, 50, 52, 55, 57, 59, 61, 65, 63, 66, 71, 69, 72, 75, 77, 81, 85, 83, 87, 89, 93, 95, 98, 101]

/-- Quaternionic coordinate selection from the recorded character table.
Source: G32 v0.16, Proposition 4.6 and Appendix A. -/
def g32p_restrictionFamilyQuat : Fin 4 → Fin 102 := ![30, 78, 91, 96]

def g32p_restrictionFamilyCoefficient (j : Fin 48) (c : Fin 102) : HurwitzPrymRex_Zw :=
  if h : j.val < 44 then
    let x := g32p_literalCharacterValue (g32p_restrictionFamilyPair ⟨j.val,h⟩) (g32p_literalColumn c)
    let y := g32p_literalCharacterValue (g32p_restrictionFamilyBar ⟨j.val,h⟩) (g32p_literalColumn c)
    ⟨x.re - y.re, x.om - y.om⟩
  else g32p_literalCharacterValue
    (g32p_restrictionFamilyQuat ⟨j.val-44, by omega⟩) (g32p_literalColumn c)

theorem g32p_restriction_family_trace
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (g : g32p_G) (c : Fin 102)
    (hτ : ∀ j, (τ j).character g = g32p_literalComplexValue (g32p_restrictionFamilyPair j) c)
    (hbar : ∀ j, (τbar j).character g = g32p_literalComplexValue (g32p_restrictionFamilyBar j) c)
    (hθ : ∀ j, (θ j).character g = g32p_literalComplexValue (g32p_restrictionFamilyQuat j) c)
    (j : Fin 48) :
    g32p_restrictionTrace τ τbar θ j g =
      HurwitzPrymRex_ev g32h_omega (g32p_restrictionFamilyCoefficient j c) := by
  unfold g32p_restrictionTrace g32p_restrictionFamilyCoefficient
  split_ifs with h
  · rw [hτ, hbar]
    simp only [g32p_literalComplexValue, HurwitzPrymRex_ev, Int.cast_sub]
    ring
  · exact hθ _

example : g32p_restrictionFamilyPair 0 = 1 ∧ g32p_restrictionFamilyBar 0 = 2 ∧
    g32p_restrictionFamilyQuat 0 = 30 := by decide

end HodgeLean.Foundations.Program

end
end

section

namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000

theorem g32p_comparisonAssembly_ordering :
    g32p_familiesPair = g32p_restrictionFamilyPair ∧
    g32p_familiesBar = g32p_restrictionFamilyBar ∧
    g32p_familiesQuat = g32p_restrictionFamilyQuat :=
  ⟨rfl, rfl, rfl⟩

theorem g32p_comparisonAssembly_coefficient (c : Fin 102) (j : Fin 48) :
    g32p_comparisonAssemblyValue c j =
      HurwitzPrymRex_ev g32h_omega (g32p_restrictionFamilyCoefficient j c) := by
  unfold g32p_comparisonAssemblyValue g32p_restrictionFamilyCoefficient
  split_ifs
  · simp only [g32p_literalComplexValue, HurwitzPrymRex_ev, Int.cast_sub]
    rw [g32p_comparisonAssembly_ordering.1, g32p_comparisonAssembly_ordering.2.1]
    ring
  · rfl

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program
open HodgeLean.Papers

theorem g32p_integration_value_coefficient (c : Fin 102) (j : Fin 48) :
    g32p_comparisonAssemblyValue c j =
      HurwitzPrymRex_ev g32h_omega (g32p_restrictionFamilyCoefficient j c) :=
  g32p_comparisonAssembly_coefficient c j

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row02_pairingTerms : Fin 48 → List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  ![g32p_row02_terms_0, g32p_row02_terms_1, g32p_row02_terms_2, g32p_row02_terms_3, g32p_row02_terms_4, g32p_row02_terms_5, g32p_row02_terms_6, g32p_row02_terms_7, g32p_row02_terms_8, g32p_row02_terms_9, g32p_row02_terms_10, g32p_row02_terms_11, g32p_row02_terms_12, g32p_row02_terms_13, g32p_row02_terms_14, g32p_row02_terms_15, g32p_row02_terms_16, g32p_row02_terms_17, g32p_row02_terms_18, g32p_row02_terms_19, g32p_row02_terms_20, g32p_row02_terms_21, g32p_row02_terms_22, g32p_row02_terms_23, g32p_row02_terms_24, g32p_row02_terms_25, g32p_row02_terms_26, g32p_row02_terms_27, g32p_row02_terms_28, g32p_row02_terms_29, g32p_row02_terms_30, g32p_row02_terms_31, g32p_row02_terms_32, g32p_row02_terms_33, g32p_row02_terms_34, g32p_row02_terms_35, g32p_row02_terms_36, g32p_row02_terms_37, g32p_row02_terms_38, g32p_row02_terms_39, g32p_row02_terms_40, g32p_row02_terms_41, g32p_row02_terms_42, g32p_row02_terms_43, g32p_row02_terms_44, g32p_row02_terms_45, g32p_row02_terms_46, g32p_row02_terms_47]

def g32p_row02_pairingQuotients : Fin 48 → List ℤ :=
  ![[], [], [], [], [], [-3456, -4032, -1152, 1728, 2304, 1152], [], [], [], [], [], [0, 576, 0, 576, 0, -1152], [], [], [], [], [], [], [], [], [], [], [], [], [0, 576, 0, 576, 0, -1152], [], [], [], [], [], [-3456, -4032, -1152, 1728, 2304, 1152], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def g32p_row02_freeCoordinates : Fin 44 → ℤ :=
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def g32p_row02_quaternionicMultiplicities : Fin 4 → ℤ :=
  ![0, 0, 0, 0]

theorem g32p_row02_pairingFree (j : Fin 44) :
    g32p_cyclotomicPairingCheck 3456 (g32p_row02_freeCoordinates j)
      (g32p_pairingCoefficients 6 (g32p_row02_pairingTerms ⟨j.val, by omega⟩))
      [1, -1, 1] (g32p_row02_pairingQuotients ⟨j.val, by omega⟩) = true := by
  fin_cases j
  · exact g32p_row02_pairing_0
  · exact g32p_row02_pairing_1
  · exact g32p_row02_pairing_2
  · exact g32p_row02_pairing_3
  · exact g32p_row02_pairing_4
  · exact g32p_row02_pairing_5
  · exact g32p_row02_pairing_6
  · exact g32p_row02_pairing_7
  · exact g32p_row02_pairing_8
  · exact g32p_row02_pairing_9
  · exact g32p_row02_pairing_10
  · exact g32p_row02_pairing_11
  · exact g32p_row02_pairing_12
  · exact g32p_row02_pairing_13
  · exact g32p_row02_pairing_14
  · exact g32p_row02_pairing_15
  · exact g32p_row02_pairing_16
  · exact g32p_row02_pairing_17
  · exact g32p_row02_pairing_18
  · exact g32p_row02_pairing_19
  · exact g32p_row02_pairing_20
  · exact g32p_row02_pairing_21
  · exact g32p_row02_pairing_22
  · exact g32p_row02_pairing_23
  · exact g32p_row02_pairing_24
  · exact g32p_row02_pairing_25
  · exact g32p_row02_pairing_26
  · exact g32p_row02_pairing_27
  · exact g32p_row02_pairing_28
  · exact g32p_row02_pairing_29
  · exact g32p_row02_pairing_30
  · exact g32p_row02_pairing_31
  · exact g32p_row02_pairing_32
  · exact g32p_row02_pairing_33
  · exact g32p_row02_pairing_34
  · exact g32p_row02_pairing_35
  · exact g32p_row02_pairing_36
  · exact g32p_row02_pairing_37
  · exact g32p_row02_pairing_38
  · exact g32p_row02_pairing_39
  · exact g32p_row02_pairing_40
  · exact g32p_row02_pairing_41
  · exact g32p_row02_pairing_42
  · exact g32p_row02_pairing_43

theorem g32p_row02_pairingQuat (j : Fin 4) :
    g32p_cyclotomicPairingCheck 3456 (g32p_row02_quaternionicMultiplicities j)
      (g32p_pairingCoefficients 6 (g32p_row02_pairingTerms ⟨44 + j.val, by omega⟩))
      [1, -1, 1] (g32p_row02_pairingQuotients ⟨44 + j.val, by omega⟩) = true := by
  fin_cases j
  · exact g32p_row02_pairing_44
  · exact g32p_row02_pairing_45
  · exact g32p_row02_pairing_46
  · exact g32p_row02_pairing_47

theorem g32p_row02_restriction_of_sums {G : Type*} [Group G]
    (H : Subgroup G) [Fintype H]
    (τ τbar : Fin 44 → FDRep ℂ G) (θ : Fin 4 → FDRep ℂ G) (χ : H →* ℂˣ)
    (z : ℂ) (hz : IsPrimitiveRoot z 6) (horder : Fintype.card H = 3456)
    (hfree : ∀ j : Fin 44,
      (∑ h : H, ((τ j).character h - (τbar j).character h) * (χ h⁻¹ : ℂ)) =
        ((g32p_row02_pairingTerms ⟨j.val, by omega⟩).map (fun x => (x.1 : ℂ) *
          HurwitzPrymRex_ev (z ^ (6 / 3)) x.2.1 * z ^ x.2.2)).sum)
    (hquat : ∀ j : Fin 4,
      (∑ h : H, (θ j).character h * (χ h⁻¹ : ℂ)) =
        ((g32p_row02_pairingTerms ⟨44 + j.val, by omega⟩).map (fun x => (x.1 : ℂ) *
          HurwitzPrymRex_ev (z ^ (6 / 3)) x.2.1 * z ^ x.2.2)).sum) :
    ∃ v ∈ g32VectorTable,
      v.i = 2 ∧ papersA τ τbar θ H χ = g32SparseVec v.coords := by
  obtain ⟨v, hv, hi, hc⟩ := g32p_row02_coordinates
  refine ⟨v, hv, hi, ?_⟩
  rw [hc]
  refine (g32p_polynomialPairing_row H τ τbar θ χ 6
    g32p_row02_freeCoordinates g32p_row02_quaternionicMultiplicities
    g32p_row02_pairingTerms [1, -1, 1] g32p_row02_pairingQuotients z
    (g32p_pairing_modulus_six hz) hfree hquat
    (by rw [horder]; exact g32p_row02_pairingFree)
    (by rw [horder]; exact g32p_row02_pairingQuat)).trans ?_
  apply Prod.ext
  · rfl
  · funext j
    fin_cases j <;> rfl

end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 200000

theorem g32p_restriction_supplier_sums (S : g32p_Supplier) [Fintype S.H]
    {n : ℕ} (e : Fin n ≃ S.H) (values : Fin n → Multiplicative (ZMod S.m))
    (hvalues : ∀ i, S.χ (e i) = values i)
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (terms : Fin 48 → List (ℕ × HurwitzPrymRex_Zw × ℕ))
    (coeff : Fin 48 → Fin n → HurwitzPrymRex_Zw)
    (label : ∀ j, Fin n → Option (Fin (terms j).length))
    (hroot : g32p_root S.m ^ (S.m / 3) = g32h_omega)
    (htrace : ∀ j i, g32p_restrictionTrace τ τbar θ j (e i) =
      HurwitzPrymRex_ev g32h_omega (coeff j i))
    (hdecode : ∀ j i,
      (label j i = none → coeff j i = ⟨0, 0⟩) ∧
      ∀ t, label j i = some t → coeff j i = (terms j)[t].2.1 ∧
        (Multiplicative.toAdd (values i)⁻¹).val = (terms j)[t].2.2)
    (hcount : ∀ j t, (Finset.univ.filter (fun i => label j i = some t)).card =
      (terms j)[t].1) (j : Fin 48) :
    (∑ h : S.H, g32p_restrictionTrace τ τbar θ j h *
      (g32p_complexCharacter S h⁻¹ : ℂ)) =
    ((terms j).map (fun x => (x.1 : ℂ) *
      HurwitzPrymRex_ev (g32p_root S.m ^ (S.m / 3)) x.2.1 *
        g32p_root S.m ^ x.2.2)).sum := by
  apply g32p_restriction_histogram_sum S.H e _ _ (label j) (g32p_root S.m) S.m
  · intro i
    rw [htrace, ← hroot, g32p_complexCharacter_apply, map_inv, hvalues]
    have hd := hdecode j i
    cases hl : label j i with
    | none =>
      rw [hd.1 hl]
      simp only [HurwitzPrymRex_ev, Int.cast_zero, zero_mul, zero_add, Option.elim_none]
    | some t =>
      have ht := hd.2 t hl
      rw [ht.1, ht.2]
      rfl
  · exact hcount j

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

theorem g32p_restriction_bucket_counts {n k t : ℕ}
    (bucket : Fin n → Fin k) (sizes : Fin k → ℕ)
    (label : Fin k → Option (Fin t))
    (hcount : ∀ a, (Finset.univ.filter (fun i => bucket i = a)).card = sizes a)
    (a : Fin t) :
    (Finset.univ.filter (fun i => label (bucket i) = some a)).card =
      ∑ b ∈ Finset.univ.filter (fun b => label b = some a), sizes b := by
  have h := Finset.sum_card_fiberwise_eq_card_filter Finset.univ
    (Finset.univ.filter (fun b => label b = some a)) bucket
  simpa only [hcount, Finset.mem_filter, Finset.mem_univ, true_and] using h.symm

theorem g32p_restriction_bucket_sums (S : g32p_Supplier) [Fintype S.H]
    {n k : ℕ} (e : Fin n ≃ S.H) (values : Fin n → Multiplicative (ZMod S.m))
    (hvalues : ∀ i, S.χ (e i) = values i)
    (bucket : Fin n → Fin k) (sizes : Fin k → ℕ) (exps : Fin k → ℕ)
    (hcount : ∀ a, (Finset.univ.filter (fun i => bucket i = a)).card = sizes a)
    (hexp : ∀ i, (Multiplicative.toAdd (values i)⁻¹).val = exps (bucket i))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (terms : Fin 48 → List (ℕ × HurwitzPrymRex_Zw × ℕ))
    (coeff : Fin 48 → Fin k → HurwitzPrymRex_Zw)
    (label : ∀ j, Fin k → Option (Fin (terms j).length))
    (hroot : g32p_root S.m ^ (S.m / 3) = g32h_omega)
    (htrace : ∀ j i, g32p_restrictionTrace τ τbar θ j (e i) =
      HurwitzPrymRex_ev g32h_omega (coeff j (bucket i)))
    (hdecode : ∀ j a,
      (label j a = none → coeff j a = ⟨0, 0⟩) ∧
      ∀ t, label j a = some t → coeff j a = (terms j)[t].2.1 ∧
        exps a = (terms j)[t].2.2)
    (hterms : ∀ j t,
      (∑ a ∈ Finset.univ.filter (fun a => label j a = some t), sizes a) =
        (terms j)[t].1) (j : Fin 48) :
    (∑ h : S.H, g32p_restrictionTrace τ τbar θ j h *
      (g32p_complexCharacter S h⁻¹ : ℂ)) =
    ((terms j).map (fun x => (x.1 : ℂ) *
      HurwitzPrymRex_ev (g32p_root S.m ^ (S.m / 3)) x.2.1 *
        g32p_root S.m ^ x.2.2)).sum := by
  apply g32p_restriction_supplier_sums S e values hvalues τ τbar θ terms
    (fun j i => coeff j (bucket i)) (fun j i => label j (bucket i)) hroot htrace
  · intro j i
    refine ⟨(hdecode j (bucket i)).1, ?_⟩
    intro t ht
    exact ⟨((hdecode j (bucket i)).2 t ht).1,
      (hexp i).trans ((hdecode j (bucket i)).2 t ht).2⟩
  · intro j t
    rw [g32p_restriction_bucket_counts bucket sizes (label j) hcount, hterms]

end HodgeLean.Foundations.Program

end
end
