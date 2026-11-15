import HodgeLean.Foundations.AnalyticDivisorAlgebraic7Defs
import HodgeLean.Foundations.AnalyticDivisorAlgebraic6

noncomputable section
open Set Filter Topology
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic7

open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
variable {n : ℕ}

private theorem productGerm_isUnit_iff (g : ProductAnalyticGerm n) :
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
    refine ⟨q, ?_⟩
    apply Subtype.ext
    change g.1 * q.1 = 1
    rw [← hfg]
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hf.continuousAt.eventually_ne hf0] with z hz
    exact mul_inv_cancel₀ hz

private theorem irreducibleAt_of_irreducible_productGerm
    {f : (Fin n → ℂ) × ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0)
    (hi : Irreducible (⟨↑f, f, hf, rfl⟩ : ProductAnalyticGerm n)) :
    IsIrreducibleAt f 0 := by
  refine ⟨hf0, ?_⟩
  intro g h hg hh hfac
  let G : ProductAnalyticGerm n := ⟨↑g, g, hg, rfl⟩
  let H : ProductAnalyticGerm n := ⟨↑h, h, hh, rfl⟩
  have he : (⟨↑f, f, hf, rfl⟩ : ProductAnalyticGerm n) = G * H := by
    apply Subtype.ext
    exact Filter.Germ.coe_eq.mpr hfac
  rcases hi.isUnit_or_isUnit he with hG | hH
  · left
    exact (productGerm_isUnit_iff G).mp hG
  · right
    exact (productGerm_isUnit_iff H).mp hH

private theorem irreducible_productGerm_of_irreducibleAt
    {f : (Fin n → ℂ) × ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hi : IsIrreducibleAt f 0) :
    Irreducible (⟨↑f, f, hf, rfl⟩ : ProductAnalyticGerm n) := by
  refine ⟨fun hu ↦ (productGerm_isUnit_iff _).mp hu hi.1, ?_⟩
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
    apply (productGerm_isUnit_iff a).mpr
    rw [← hga, Filter.Germ.value_ofFun]
    exact hg0
  · right
    apply (productGerm_isUnit_iff b).mpr
    rw [← hhb, Filter.Germ.value_ofFun]
    exact hh0

private theorem associatedAt_of_associated_productGerm
    {f g : (Fin n → ℂ) × ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0)
    (h : Associated (⟨↑f, f, hf, rfl⟩ : ProductAnalyticGerm n)
      ⟨↑g, g, hg, rfl⟩) : AreAssociatedAt f g 0 := by
  obtain ⟨w, hw⟩ := h.symm
  obtain ⟨u, hu, huw⟩ := (w : ProductAnalyticGerm n).2
  refine ⟨u, hu, ?_, ?_⟩
  · have hwu : IsUnit (w : ProductAnalyticGerm n) := w.isUnit
    have := (productGerm_isUnit_iff (w : ProductAnalyticGerm n)).mp hwu
    rw [← huw, Filter.Germ.value_ofFun] at this
    exact this
  · apply Filter.Germ.coe_eq.mp
    calc
      ↑f = (⟨↑f, f, hf, rfl⟩ : ProductAnalyticGerm n).1 := rfl
      _ = (⟨↑g, g, hg, rfl⟩ * (w : ProductAnalyticGerm n)).1 :=
        (congrArg Subtype.val hw).symm
      _ = (⟨↑g, g, hg, rfl⟩ : ProductAnalyticGerm n).1 *
          (w : ProductAnalyticGerm n).1 := rfl
      _ = ↑g * ↑u := congrArg₂ (· * ·) rfl huw.symm
      _ = ↑(fun x ↦ u x * g x) := by rw [mul_comm]; rfl

theorem spec_exists_irreducible_decomposition_aux {f : (Fin n → ℂ) × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0) (hnz : ¬ ∀ᶠ y in nhds 0, f y = 0) :
    ∃ k : ℕ, ∃ u : (Fin n → ℂ) × ℂ → ℂ,
      ∃ P : Fin k → (Fin n → ℂ) × ℂ → ℂ, ∃ m : Fin k → ℕ,
        AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
        (∀ i, AnalyticAt ℂ (P i) 0 ∧ IsIrreducibleAt (P i) 0 ∧ 0 < m i) ∧
        Pairwise (fun i j ↦ IsCoprimeAt (P i) (P j) 0) ∧
        f =ᶠ[nhds 0] fun y ↦ u y * ∏ i, (P i y) ^ (m i) := by
  classical
  obtain ⟨germEquiv, -⟩ := spec_finSucc_product_equiv (n := n)
  letI : UniqueFactorizationMonoid (ProductAnalyticGerm n) :=
    germEquiv.toMulEquiv.uniqueFactorizationMonoid
      (spec_analyticGerm_ufd_aux (n + 1))
  letI : StrongNormalizationMonoid (ProductAnalyticGerm n) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let G : ProductAnalyticGerm n := ⟨↑f, f, hf, rfl⟩
  have hG : G ≠ 0 := fun h ↦ hnz (Filter.Germ.coe_eq.mp (congrArg Subtype.val h))
  let F := UniqueFactorizationMonoid.normalizedFactors G
  let S := F.toFinset
  let k := Fintype.card S
  let e : Fin k ≃ S := (Fintype.equivFin S).symm
  let p : Fin k → ProductAnalyticGerm n := fun i ↦ (e i).1
  have hmem : ∀ i, p i ∈ F := fun i ↦ Multiset.mem_toFinset.mp (e i).2
  have hp : ∀ i, Prime (p i) := fun i ↦
    UniqueFactorizationMonoid.prime_of_normalized_factor _ (hmem i)
  let m : Fin k → ℕ := fun i ↦ F.count (p i)
  have hm : ∀ i, 0 < m i := fun i ↦ Multiset.count_pos.mpr (hmem i)
  have hprod : (∏ i, p i ^ m i) = F.prod := by
    rw [Finset.prod_multiset_count]
    exact (Fintype.prod_equiv e _ (fun q ↦ q.1 ^ F.count q.1) (fun _ ↦ rfl)).trans
      (Finset.prod_coe_sort S (fun q ↦ q ^ F.count q))
  obtain ⟨v, hv⟩ := UniqueFactorizationMonoid.prod_normalizedFactors hG
  obtain ⟨u, hu, huv⟩ := (v : ProductAnalyticGerm n).2
  choose P hPa hPg using fun i ↦ (p i).2
  have hu0 : u 0 ≠ 0 := by
    have h := (productGerm_isUnit_iff (v : ProductAnalyticGerm n)).mp v.isUnit
    rw [← huv, Filter.Germ.value_ofFun] at h
    exact h
  have hP0 : ∀ i, P i 0 = 0 := by
    intro i
    by_contra hi
    apply (hp i).not_isUnit
    apply (productGerm_isUnit_iff _).mpr
    rw [← hPg i, Filter.Germ.value_ofFun]
    exact hi
  have hPi : ∀ i, Irreducible (⟨↑(P i), P i, hPa i, rfl⟩ : ProductAnalyticGerm n) := by
    intro i
    have heq : (⟨↑(P i), P i, hPa i, rfl⟩ : ProductAnalyticGerm n) = p i :=
      Subtype.ext (hPg i)
    rw [heq]
    exact (hp i).irreducible
  refine ⟨k, u, P, m, hu, hu0, (fun i ↦ ⟨hPa i,
    irreducibleAt_of_irreducible_productGerm (hPa i) (hP0 i) (hPi i), hm i⟩), ?_, ?_⟩
  · intro i j hij
    rintro ⟨q, r, s, hq, hr, hs, hq0, hqr, hqs⟩
    let Q : ProductAnalyticGerm n := ⟨↑q, q, hq, rfl⟩
    have hQu : ¬ IsUnit Q := fun h ↦ (productGerm_isUnit_iff Q).mp h hq0
    have hQi : Q ∣ p i := by
      refine ⟨⟨↑r, r, hr, rfl⟩, ?_⟩
      apply Subtype.ext
      rw [← hPg i]
      exact Filter.Germ.coe_eq.mpr hqr
    have hQj : Q ∣ p j := by
      refine ⟨⟨↑s, s, hs, rfl⟩, ?_⟩
      apply Subtype.ext
      rw [← hPg j]
      exact Filter.Germ.coe_eq.mpr hqs
    have hiQ := ((hp i).irreducible.dvd_iff.mp hQi).resolve_left hQu
    have hjQ := ((hp j).irreducible.dvd_iff.mp hQj).resolve_left hQu
    have heq : p i = p j := UniqueFactorizationMonoid.mem_normalizedFactors_eq_of_associated
      (hmem i) (hmem j) (hiQ.trans hjQ.symm)
    exact hij (e.injective (Subtype.ext heq))
  · have hfun : (fun y ↦ u y * ∏ i, P i y ^ m i) = u * ∏ i, (P i) ^ m i := by
      ext y
      simp only [Pi.mul_apply, Finset.prod_apply, Pi.pow_apply]
    rw [hfun]
    apply Filter.Germ.coe_eq.mp
    change G.1 = _
    rw [← hv, ← hprod]
    change (productAnalyticGermSubring n).subtype (∏ i, p i ^ m i) *
      (v : ProductAnalyticGerm n).1 = _
    rw [map_prod]
    simp only [map_pow, ← huv]
    change (∏ i, (p i).1 ^ m i) * ↑u =
      (Filter.Germ.coeRingHom (nhds (0 : (Fin n → ℂ) × ℂ)))
        (u * ∏ i, (P i) ^ m i)
    rw [map_mul, map_prod]
    simp only [map_pow, Filter.Germ.coe_coeRingHom, ← hPg]
    exact mul_comm _ _

theorem spec_irreducible_decomposition_unique_aux {k l : ℕ}
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
    ∃ e : Fin k ≃ Fin l, ∀ i, AreAssociatedAt (P i) (Q (e i)) 0 ∧ m i = r (e i) := by
  classical
  obtain ⟨germEquiv, -⟩ := spec_finSucc_product_equiv (n := n)
  letI : UniqueFactorizationMonoid (ProductAnalyticGerm n) :=
    germEquiv.toMulEquiv.uniqueFactorizationMonoid
      (spec_analyticGerm_ufd_aux (n + 1))
  letI : StrongNormalizationMonoid (ProductAnalyticGerm n) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let A : Fin k → ProductAnalyticGerm n := fun i ↦ ⟨↑(P i), P i, (hP i).1, rfl⟩
  let B : Fin l → ProductAnalyticGerm n := fun j ↦ ⟨↑(Q j), Q j, (hQ j).1, rfl⟩
  have hAi : ∀ i, Irreducible (A i) := fun i ↦
    irreducible_productGerm_of_irreducibleAt (hP i).1 (hP i).2.1
  have hBi : ∀ j, Irreducible (B j) := fun j ↦
    irreducible_productGerm_of_irreducibleAt (hQ j).1 (hQ j).2.1
  let sA : Multiset (ProductAnalyticGerm n) :=
    (Finset.univ : Finset (Fin k)).1.bind fun i ↦ Multiset.replicate (m i) (A i)
  let sB : Multiset (ProductAnalyticGerm n) :=
    (Finset.univ : Finset (Fin l)).1.bind fun j ↦ Multiset.replicate (r j) (B j)
  have hsAi : ∀ a ∈ sA, Irreducible a := by
    intro a ha
    simp only [sA, Multiset.mem_bind, Finset.mem_val, Finset.mem_univ, true_and,
      Multiset.mem_replicate] at ha
    obtain ⟨i, -, rfl⟩ := ha
    exact hAi i
  have hsBi : ∀ b ∈ sB, Irreducible b := by
    intro b hb
    simp only [sB, Multiset.mem_bind, Finset.mem_val, Finset.mem_univ, true_and,
      Multiset.mem_replicate] at hb
    obtain ⟨j, -, rfl⟩ := hb
    exact hBi j
  have hsAprod : sA.prod = ∏ i, A i ^ m i := by
    simp only [sA, Multiset.prod_bind, Multiset.map_coe, Multiset.prod_replicate,
      Finset.prod_map, Function.Embedding.coeFn_mk]
    rfl
  have hsBprod : sB.prod = ∏ j, B j ^ r j := by
    simp only [sB, Multiset.prod_bind, Multiset.map_coe, Multiset.prod_replicate,
      Finset.prod_map, Function.Embedding.coeFn_mk]
    rfl
  have hprodAssoc : Associated sA.prod sB.prod := by
    let U : ProductAnalyticGerm n := ⟨↑u, u, hu, rfl⟩
    let V : ProductAnalyticGerm n := ⟨↑v, v, hv, rfl⟩
    have hUV : U * sA.prod = V * sB.prod := by
      apply Subtype.ext
      rw [hsAprod, hsBprod]
      change ((⟨↑u, u, hu, rfl⟩ : ProductAnalyticGerm n).1 *
        (productAnalyticGermSubring n).subtype (∏ i, A i ^ m i)) =
        ((⟨↑v, v, hv, rfl⟩ : ProductAnalyticGerm n).1 *
        (productAnalyticGermSubring n).subtype (∏ j, B j ^ r j))
      rw [map_prod, map_prod]
      simp only [map_pow]
      have hfun :
          (@Filter.Germ.ofFun ((Fin n → ℂ) × ℂ) ℂ
            (nhds (0 : (Fin n → ℂ) × ℂ))
            (fun y ↦ u y * ∏ i, P i y ^ m i)) =
          @Filter.Germ.ofFun ((Fin n → ℂ) × ℂ) ℂ
            (nhds (0 : (Fin n → ℂ) × ℂ))
            (fun y ↦ v y * ∏ j, Q j y ^ r j) := by
        apply Filter.Germ.coe_eq.mpr
        filter_upwards [hfacP, hfacQ] with y hyP hyQ
        exact hyP.symm.trans hyQ
      calc
        ↑u * ∏ i, ↑(P i) ^ m i =
            @Filter.Germ.ofFun ((Fin n → ℂ) × ℂ) ℂ
              (nhds (0 : (Fin n → ℂ) × ℂ))
              (fun y ↦ u y * ∏ i, P i y ^ m i) := by
          have hpoint : u * ∏ i, (P i) ^ m i =
              fun y ↦ u y * ∏ i, P i y ^ m i := by
            ext y
            simp only [Pi.mul_apply, Finset.prod_apply, Pi.pow_apply]
          calc
            ↑u * ∏ i, ↑(P i) ^ m i =
                (Filter.Germ.coeRingHom (nhds (0 : (Fin n → ℂ) × ℂ)))
                  (u * ∏ i, (P i) ^ m i) := by
                    rw [map_mul, map_prod]
                    simp only [map_pow, Filter.Germ.coe_coeRingHom]
            _ = _ := congrArg (Filter.Germ.coeRingHom
              (nhds (0 : (Fin n → ℂ) × ℂ))) hpoint
        _ = @Filter.Germ.ofFun ((Fin n → ℂ) × ℂ) ℂ
              (nhds (0 : (Fin n → ℂ) × ℂ))
              (fun y ↦ v y * ∏ j, Q j y ^ r j) := hfun
        _ = ↑v * ∏ j, ↑(Q j) ^ r j := by
          have hpoint : v * ∏ j, (Q j) ^ r j =
              fun y ↦ v y * ∏ j, Q j y ^ r j := by
            ext y
            simp only [Pi.mul_apply, Finset.prod_apply, Pi.pow_apply]
          calc
            _ = (Filter.Germ.coeRingHom (nhds (0 : (Fin n → ℂ) × ℂ)))
                (v * ∏ j, (Q j) ^ r j) :=
              (congrArg (Filter.Germ.coeRingHom
                (nhds (0 : (Fin n → ℂ) × ℂ))) hpoint).symm
            _ = ↑v * ∏ j, ↑(Q j) ^ r j := by
              rw [map_mul, map_prod]
              simp only [map_pow, Filter.Germ.coe_coeRingHom]
    have hassoc : Associated (sA.prod * U) (sB.prod * V) := by
      rw [mul_comm sA.prod U, mul_comm sB.prod V]
      exact Associated.of_eq hUV
    exact (associated_mul_isUnit_right_iff ((productGerm_isUnit_iff V).mpr hv0)).mp
      ((associated_mul_isUnit_left_iff ((productGerm_isUnit_iff U).mpr hu0)).mp hassoc)
  have hnf : sA.map normalize = sB.map normalize := by
    rw [← UniqueFactorizationMonoid.normalizedFactors_prod_eq sA hsAi,
      ← UniqueFactorizationMonoid.normalizedFactors_prod_eq sB hsBi]
    exact hprodAssoc.normalizedFactors_eq
  have hnormA : Function.Injective (fun i ↦ normalize (A i)) := by
    intro i j hij
    by_contra hne
    apply hcP hne
    have hassoc : Associated (A i) (A j) :=
      (normalize_associated (A i)).symm.trans
        ((Associated.of_eq hij).trans (normalize_associated (A j)))
    obtain ⟨w, hw⟩ := hassoc
    obtain ⟨q, hq, hqw⟩ := (w : ProductAnalyticGerm n).2
    refine ⟨P i, fun _ ↦ 1, q, (hP i).1, analyticAt_const, hq,
      (hP i).2.1.1, Eventually.of_forall (fun y ↦ by simp), ?_⟩
    apply Filter.Germ.coe_eq.mp
    calc
      ↑(P j) = (A j).1 := rfl
      _ = (A i * (w : ProductAnalyticGerm n)).1 := (congrArg Subtype.val hw).symm
      _ = (A i).1 * (w : ProductAnalyticGerm n).1 := rfl
      _ = ↑(P i) * ↑q := congrArg₂ (· * ·) rfl hqw.symm
      _ = ↑(fun y ↦ P i y * q y) := rfl
  have hnormB : Function.Injective (fun j ↦ normalize (B j)) := by
    intro i j hij
    by_contra hne
    apply hcQ hne
    have hassoc : Associated (B i) (B j) :=
      (normalize_associated (B i)).symm.trans
        ((Associated.of_eq hij).trans (normalize_associated (B j)))
    obtain ⟨w, hw⟩ := hassoc
    obtain ⟨q, hq, hqw⟩ := (w : ProductAnalyticGerm n).2
    refine ⟨Q i, fun _ ↦ 1, q, (hQ i).1, analyticAt_const, hq,
      (hQ i).2.1.1, Eventually.of_forall (fun y ↦ by simp), ?_⟩
    apply Filter.Germ.coe_eq.mp
    calc
      ↑(Q j) = (B j).1 := rfl
      _ = (B i * (w : ProductAnalyticGerm n)).1 := (congrArg Subtype.val hw).symm
      _ = (B i).1 * (w : ProductAnalyticGerm n).1 := rfl
      _ = ↑(Q i) * ↑q := congrArg₂ (· * ·) rfl hqw.symm
      _ = ↑(fun y ↦ Q i y * q y) := rfl
  have himage : Set.range (fun i ↦ normalize (A i)) =
      Set.range (fun j ↦ normalize (B j)) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      have hmpos := (hP i).2.2
      have hmem : normalize (A i) ∈ sA.map normalize := by
        simp only [sA, Multiset.mem_map, Multiset.mem_bind, Finset.mem_val, Finset.mem_univ,
          true_and, Multiset.mem_replicate]
        exact ⟨A i, ⟨i, Nat.ne_of_gt hmpos, rfl⟩, rfl⟩
      rw [hnf] at hmem
      simp only [sB, Multiset.mem_map, Multiset.mem_bind, Finset.mem_val, Finset.mem_univ,
        true_and, Multiset.mem_replicate] at hmem
      obtain ⟨b, ⟨j, -, rfl⟩, hb⟩ := hmem
      exact ⟨j, hb⟩
    · rintro ⟨j, rfl⟩
      have hrpos := (hQ j).2.2
      have hmem : normalize (B j) ∈ sB.map normalize := by
        simp only [sB, Multiset.mem_map, Multiset.mem_bind, Finset.mem_val, Finset.mem_univ,
          true_and, Multiset.mem_replicate]
        exact ⟨B j, ⟨j, Nat.ne_of_gt hrpos, rfl⟩, rfl⟩
      rw [← hnf] at hmem
      simp only [sA, Multiset.mem_map, Multiset.mem_bind, Finset.mem_val, Finset.mem_univ,
        true_and, Multiset.mem_replicate] at hmem
      obtain ⟨a, ⟨i, -, rfl⟩, ha⟩ := hmem
      exact ⟨i, ha⟩
  let e : Fin k ≃ Fin l :=
    (Equiv.ofInjective (fun i ↦ normalize (A i)) hnormA).trans
      ((Set.equivOfEq himage).trans
        (Equiv.ofInjective (fun j ↦ normalize (B j)) hnormB).symm)
  have heNorm (i : Fin k) : normalize (A i) = normalize (B (e i)) := by
    let x := (Set.equivOfEq himage)
      ((Equiv.ofInjective (fun i ↦ normalize (A i)) hnormA) i)
    change normalize (A i) = normalize (B
      ((Equiv.ofInjective (fun j ↦ normalize (B j)) hnormB).symm x))
    calc
      normalize (A i) = x.1 := rfl
      _ = normalize (B ((Equiv.ofInjective (fun j ↦ normalize (B j)) hnormB).symm x)) :=
        (congrArg Subtype.val
          ((Equiv.ofInjective (fun j ↦ normalize (B j)) hnormB).apply_symm_apply x)).symm
  refine ⟨e, fun i ↦ ⟨?_, ?_⟩⟩
  · apply associatedAt_of_associated_productGerm (hP i).1 (hQ (e i)).1
    exact (normalize_associated (A i)).symm.trans
      ((Associated.of_eq (heNorm i)).trans
        (normalize_associated (B (e i))))
  · have hc := congrArg (Multiset.count (normalize (A i))) hnf
    simp only [sA, sB, Multiset.map_bind, Multiset.map_replicate,
      Multiset.count_bind, Multiset.count_replicate] at hc
    rw [← Finset.sum_eq_multiset_sum, ← Finset.sum_eq_multiset_sum] at hc
    rw [Finset.sum_eq_single i] at hc
    · rw [Finset.sum_eq_single (e i)] at hc
      · simpa [heNorm i] using hc
      · intro j _ hj
        have hne' : normalize (B j) ≠ normalize (A i) := fun heq ↦
          hj (hnormB (heq.trans (heNorm i)))
        simp [hne']
      · simp
    · intro j _ hj
      simp [hnormA.ne hj]
    · simp

theorem spec_eventually_zero_iff_factor_zero_aux {k : ℕ}
    {f u : (Fin n → ℂ) × ℂ → ℂ}
    {P : Fin k → (Fin n → ℂ) × ℂ → ℂ} {m : Fin k → ℕ}
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) (hm : ∀ i, 0 < m i)
    (hfac : f =ᶠ[nhds 0] fun y ↦ u y * ∏ i, (P i y) ^ (m i)) :
    ∀ᶠ y in nhds 0, f y = 0 ↔ ∃ i, P i y = 0 := by
  filter_upwards [hfac, hu.continuousAt.eventually_ne hu0] with y hy huy
  rw [hy, mul_eq_zero, or_iff_right huy, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and]
  exact exists_congr fun i ↦ pow_eq_zero_iff (Nat.ne_of_gt (hm i))

theorem spec_eventually_mem_closure_regular_factor_aux {k : ℕ}
    {P : Fin k → (Fin n → ℂ) × ℂ → ℂ}
    (hP : ∀ i, AnalyticAt ℂ (P i) 0 ∧ IsSquareFreeAt (P i) 0) :
    ∀ᶠ y in nhds 0, ∀ i, P i y = 0 →
      y ∈ closure {p | P i p = 0 ∧ fderiv ℂ (P i) p ≠ 0} := by
  apply eventually_all.mpr
  intro i
  exact spec_eventually_mem_closure_regular (hP i).1
    (spec_eventually_isSquareFreeAt (hP i).1 (hP i).2)

theorem spec_transverseOrder_constant_aux {k : ℕ}
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
          analyticOrderAt (fun t : ℂ ↦ f (z + t • b)) 0 := by
  have horder := spec_transverseOrder_of_decomposition hu hu0 hP hm hfac
  filter_upwards [horder] with y hy
  filter_upwards [horder] with z hz
  intro i hPiy hother_y hPiz hother_z a b hdera hderb
  exact (hy i hPiy hother_y a hdera).trans (hz i hPiz hother_z b hderb).symm

end HodgeLean.Foundations.AnalyticDivisorAlgebraic7
