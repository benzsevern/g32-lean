import HodgeLean.Foundations.Program.G32PropFourSixDefs
import HodgeLean.Foundations.Program.RiemannSurfaceQuotientDefs
import HodgeLean.Foundations.Program.SchoenSelectedGeometryLabelEnumeration
import HodgeLean.Papers.PapersSupplyProofs

/-! Index pairs for the retained supplier exponent list. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Papers
open scoped BigOperators Manifold ContDiff
namespace HodgeLean.Foundations.Program

private theorem pairList_length (L : List (ℕ × ℕ)) :
    (L.flatMap fun p => [p.1, p.2]).length = 2 * L.length := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
    omega

private theorem pairList_get (L : List (ℕ × ℕ)) (i : Fin L.length) :
    (L.flatMap fun p => [p.1, p.2])[2 * i.val]'(by rw [pairList_length]; omega) = L[i].1 ∧
    (L.flatMap fun p => [p.1, p.2])[2 * i.val + 1]'(by rw [pairList_length]; omega) = L[i].2 := by
  induction L with
  | nil => exact Fin.elim0 i
  | cons p L ih =>
    rcases i with ⟨n, hn⟩
    cases n with
    | zero => simp only [Fin.getElem_fin, List.flatMap_cons, List.cons_append, List.nil_append,
        Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero, List.getElem_cons_succ,
        and_self]
    | succ n =>
      have hn' : n < L.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hn
      have hh := ih ⟨n, hn'⟩
      simpa only [Fin.getElem_fin, Nat.mul_succ, Nat.add_assoc, List.flatMap_cons, List.cons_append,
        List.nil_append, List.getElem_cons_succ] using hh

/-- A simple list in the positive residue range has an occurrence-preserving pairing. -/
theorem selectedPairIndices_of_simple {m : ℕ} {α : List ℕ}
    (hs : IsSimpleExps m α) (hb : ∀ a ∈ α, 0 < a ∧ a < m) :
    ∃ (r : ℕ) (σ : Fin (2 * r) ≃ Fin α.length),
      ∀ i : Fin r, α[σ ⟨2 * i.val, by omega⟩] +
        α[σ ⟨2 * i.val + 1, by omega⟩] = m := by
  classical
  obtain ⟨L, hp, hmod⟩ := hs
  let l := L.flatMap fun p => [p.1, p.2]
  have hl : ∀ b ∈ l, b ≠ 0 := fun b h => ne_of_gt (hb b (hp.mem_iff.mp h)).1
  obtain ⟨e, he⟩ := s0_label_enumeration (fun i : Fin α.length => α[i]) l
    (fun i => ne_of_gt (hb _ (List.getElem_mem i.isLt)).1) hl (by
      intro w hw
      rw [← List.sum_ofFn]
      change (List.ofFn fun i : Fin α.length => w α[i.val]).sum = _
      rw [List.ofFn_getElem_eq_map]
      exact (hp.map w).sum_eq.symm)
  let d : Fin (2 * L.length) ≃ Fin l.length := finCongr (pairList_length L).symm
  refine ⟨L.length, d.trans e, fun i => ?_⟩
  have he0 := he (d ⟨2 * i.val, by omega⟩)
  have he1 := he (d ⟨2 * i.val + 1, by omega⟩)
  have hg := pairList_get L i
  change α[e (d ⟨2 * i.val, by omega⟩)] + α[e (d ⟨2 * i.val + 1, by omega⟩)] = m
  rw [he0, he1]
  change (L.flatMap fun p => [p.1, p.2])[2 * i.val]'
    (by rw [pairList_length]; omega) +
    (L.flatMap fun p => [p.1, p.2])[2 * i.val + 1]'
    (by rw [pairList_length]; omega) = m
  rw [hg.1, hg.2]
  have hm := hmod L[i] (List.getElem_mem i.isLt)
  have h0 := hb L[i].1 (hp.mem_iff.mp (by
    apply List.mem_flatMap.mpr
    exact ⟨L[i], List.getElem_mem i.isLt, by simp⟩))
  have h1 := hb L[i].2 (hp.mem_iff.mp (by
    apply List.mem_flatMap.mpr
    exact ⟨L[i], List.getElem_mem i.isLt, by simp⟩))
  have hsum : L[i].1 + L[i].2 < 2 * m := by omega
  have hdiv : m ∣ L[i].1 + L[i].2 := Nat.dvd_of_mod_eq_zero hm
  obtain ⟨q, hq⟩ := hdiv
  have hqpos : 0 < q := by nlinarith [h0.1]
  have hqlt : q < 2 := by nlinarith [h0.1, h0.2]
  have : q = 1 := by omega
  simpa only [this, Nat.mul_one] using hq

/-- The native exponent bounds hold for every supplier. -/
theorem selectedPairIndices_exponent_bounds (S : g32p_Supplier) :
    ∀ i : Fin (g32p_exponents S).length,
      0 < (g32p_exponents S)[i] ∧ (g32p_exponents S)[i] < S.m := by
  intro i
  have ha := List.getElem_mem (l := g32p_exponents S) i.isLt
  change (g32p_exponents S)[i] ∈ papersExpsList S.H S.χ g32p_classList at ha
  rw [papersExpsList, Multiset.mem_toList, Multiset.mem_map] at ha
  obtain ⟨b, hb, he⟩ := ha
  rw [← he]
  exact ⟨ZMod.val_pos.mpr (papersExpsTuple_ne_zero S.H S.χ g32p_classList b hb),
    ZMod.val_lt b⟩

/-- Pair indices and a power degree for the supplied primitive part. -/
theorem selectedPairIndices {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} (S : g32p_Supplier)
    (hS : g32p_Admissible aut S) (P : g32p_Part J aut S) :
    ∃ (r : ℕ) (σ : Fin (2 * r) ≃ Fin (g32p_exponents S).length),
      (∀ i : Fin (g32p_exponents S).length,
        0 < (g32p_exponents S)[i] ∧ (g32p_exponents S)[i] < S.m) ∧
      (∀ i : Fin r,
        (g32p_exponents S)[σ ⟨2 * i.val, by omega⟩] +
        (g32p_exponents S)[σ ⟨2 * i.val + 1, by omega⟩] = S.m) ∧
      ∃ h : ℕ, 0 < h + 1 ∧ h + 1 = 2 * P.k ∧ h = 2 * P.k - 1 := by
  have hb := selectedPairIndices_exponent_bounds S
  obtain ⟨r, σ, hpair⟩ := selectedPairIndices_of_simple hS.1 (by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    exact hb ⟨i, hi⟩)
  have hk : 0 < 2 * P.k := Nat.mul_pos (by omega) P.act.cyc_positive
  exact ⟨r, σ, hb, hpair, 2 * P.k - 1, by omega, by omega, rfl⟩

/-- Retain the supplied branch representatives and rotations while inserting pair indices. -/
theorem selectedPairIndices_retained {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} (S : g32p_Supplier)
    (hS : g32p_Admissible aut S) (P : g32p_Part J aut S)
    (C : Type) [TopologicalSpace C] [MulAction g32p_G C]
    [ChartedSpace ℂ (rsq_Quot S.χ.ker C)]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.χ.ker C)]
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (y : Fin (g32p_exponents S).length → rsq_Quot S.χ.ker C)
    (rot : Fin (g32p_exponents S).length → S.H ⧸ S.χ.ker)
    (hrot : ∀ i, b4_IsRotGen ℂ (y i) (rot i) ∧
      e (rot i) = Multiplicative.ofAdd ((g32p_exponents S)[i] : ZMod S.m)) :
    ∃ (r : ℕ) (σ : Fin (2 * r) ≃ Fin (g32p_exponents S).length),
    ∃ (y' : Fin (g32p_exponents S).length → rsq_Quot S.χ.ker C)
      (rot' : Fin (g32p_exponents S).length → S.H ⧸ S.χ.ker),
      y' = y ∧ rot' = rot ∧
      (∀ i, b4_IsRotGen ℂ (y' i) (rot' i) ∧
        e (rot' i) = Multiplicative.ofAdd ((g32p_exponents S)[i] : ZMod S.m)) ∧
      (∀ i : Fin (g32p_exponents S).length,
        0 < (g32p_exponents S)[i] ∧ (g32p_exponents S)[i] < S.m) ∧
      (∀ i : Fin r,
        (g32p_exponents S)[σ ⟨2 * i.val, by omega⟩] +
        (g32p_exponents S)[σ ⟨2 * i.val + 1, by omega⟩] = S.m) ∧
      ∃ h : ℕ, 0 < h + 1 ∧ h + 1 = 2 * P.k ∧ h = 2 * P.k - 1 := by
  obtain ⟨r, σ, hb, hp, hd⟩ := selectedPairIndices S hS P
  exact ⟨r, σ, y, rot, rfl, rfl, hrot, hb, hp, hd⟩

#print axioms pairList_length
#print axioms pairList_get
#print axioms selectedPairIndices_of_simple
#print axioms selectedPairIndices_exponent_bounds
#print axioms selectedPairIndices
#print axioms selectedPairIndices_retained

end HodgeLean.Foundations.Program
