import HodgeLean.Foundations.AnalyticDivisorAlgebraic17Defs

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic17

open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic16

theorem spec_nearby_selected_factor_divides_aux {n r : ℕ} {ι : Type*}
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
      f i =ᶠ[𝓝 q] fun y ↦ P a y * s y := by
  classical
  let s : (Fin n → ℂ) × ℂ → ℂ := fun y ↦
    v y * P a y ^ (b a - 1) * ∏ c ∈ Finset.univ.erase a, P c y ^ b c
  refine ⟨s, ?_, ?_⟩
  · exact ((hv q hqN).mul ((hP a q hqN).pow _)).mul
      (Finset.analyticAt_fun_prod _ fun c _ ↦ (hP c q hqN).pow _)
  · filter_upwards [hNo.mem_nhds hqN] with y hy
    rw [hfacN y hy]
    change v y * ∏ c, P c y ^ b c =
      P a y * (v y * P a y ^ (b a - 1) * ∏ c ∈ Finset.univ.erase a, P c y ^ b c)
    have hba : b a = (b a - 1) + 1 := by
      have := hb a
      omega
    have hpowa : P a y ^ b a = P a y * P a y ^ (b a - 1) := by
      calc
        P a y ^ b a = P a y ^ ((b a - 1) + 1) := congrArg (P a y ^ ·) hba
        _ = P a y ^ (b a - 1) * P a y := pow_succ _ _
        _ = P a y * P a y ^ (b a - 1) := mul_comm _ _
    have hprod : (∏ c, P c y ^ b c) =
        P a y ^ b a * ∏ c ∈ Finset.univ.erase a, P c y ^ b c :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ a)).symm
    rw [hprod, hpowa]
    ring

theorem spec_nearby_factor_decomposition_aux {n r : ℕ} {ι : Type*}
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
        P a =ᶠ[𝓝 q] fun y ↦ u y * ∏ j, Q j y ^ d j := by
  have hnz : ¬ ∀ᶠ y in 𝓝 q, P a y = 0 := by
    intro hPa
    apply hD.2.2.2.1 i q (hNV hqN)
    obtain ⟨s, hs, hdiv⟩ := spec_nearby_selected_factor_divides_aux hD i hNo hNp hNV
      hqN hv hv0 hP hirr hb hcop hfacN a hzero
    filter_upwards [hdiv, hPa] with y hfy hPy
    rw [hfy, hPy, zero_mul]
  exact spec_exists_irreducible_decomposition_at (hP a q hqN) hzero hnz

theorem spec_nearby_factor_divides_aux {n r : ℕ} {ι : Type*}
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
      f i =ᶠ[𝓝 q] fun y ↦ Q j y * s y := by
  classical
  obtain ⟨s₀, hs₀, hdiv⟩ := spec_nearby_selected_factor_divides_aux hD i hNo hNp hNV
    hqN hv hv0 hP hirr hb hcop hfacN a hzero
  let t : (Fin n → ℂ) × ℂ → ℂ := fun y ↦
    u y * Q j y ^ (d j - 1) * ∏ l ∈ Finset.univ.erase j, Q l y ^ d l
  have ht : AnalyticAt ℂ t q :=
    (hu.mul ((hQ j).1.pow _)).mul
      (Finset.analyticAt_fun_prod _ fun l _ ↦ (hQ l).1.pow _)
  have hQa : P a =ᶠ[𝓝 q] fun y ↦ Q j y * t y := by
    filter_upwards [hfacQ] with y hy
    rw [hy]
    change u y * ∏ l, Q l y ^ d l =
      Q j y * (u y * Q j y ^ (d j - 1) * ∏ l ∈ Finset.univ.erase j, Q l y ^ d l)
    have hdj : d j = (d j - 1) + 1 := by
      have := (hQ j).2.2
      omega
    have hpow : Q j y ^ d j = Q j y * Q j y ^ (d j - 1) := by
      calc
        Q j y ^ d j = Q j y ^ ((d j - 1) + 1) := congrArg (Q j y ^ ·) hdj
        _ = Q j y ^ (d j - 1) * Q j y := pow_succ _ _
        _ = Q j y * Q j y ^ (d j - 1) := mul_comm _ _
    have hprod : (∏ l, Q l y ^ d l) =
        Q j y ^ d j * ∏ l ∈ Finset.univ.erase j, Q l y ^ d l :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
    rw [hprod, hpow]
    ring
  refine ⟨fun y ↦ t y * s₀ y, ht.mul hs₀, ?_⟩
  filter_upwards [hdiv, hQa] with y hfy hPy
  rw [hfy, hPy]
  ring

private theorem gaga17_analyticAt_translate {n : ℕ}
    {f : (Fin n → ℂ) × ℂ → ℂ} {q : (Fin n → ℂ) × ℂ} (hf : AnalyticAt ℂ f q) :
    AnalyticAt ℂ (fun z ↦ f (q + z)) 0 :=
  hf.comp_of_eq (analyticAt_const.add analyticAt_id) (by simp)

private theorem gaga17_productGerm_irreducible {n : ℕ}
    {f : (Fin n → ℂ) × ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hi : IsIrreducibleAt f 0) :
    Irreducible (AnalyticDivisorAlgebraic8.productAnalyticGermOf f hf) := by
  let G := AnalyticDivisorAlgebraic8.productAnalyticGermOf f hf
  refine ⟨?_, ?_⟩
  · intro hG
    have hz := (hG.map ((Filter.Germ.valueRingHom
      (X := (Fin n → ℂ) × ℂ) (E := ℂ)).comp
        (productAnalyticGermSubring n).subtype)).ne_zero
    exact hz hi.1
  · intro a b hab
    obtain ⟨g, hg, hga⟩ := a.2
    obtain ⟨h, hh, hhb⟩ := b.2
    have hfac : f =ᶠ[𝓝 0] fun x ↦ g x * h x := by
      apply Filter.Germ.coe_eq.mp
      calc
        ↑f = G.1 := rfl
        _ = (a * b).1 := congrArg Subtype.val hab
        _ = a.1 * b.1 := rfl
        _ = ↑g * ↑h := congrArg₂ (· * ·) hga.symm hhb.symm
        _ = ↑(fun x ↦ g x * h x) := rfl
    rcases hi.2 g h hg hh hfac with hg0 | hh0
    · left
      let gInv := AnalyticDivisorAlgebraic8.productAnalyticGermOf
        (fun z ↦ (g z)⁻¹) (hg.inv hg0)
      apply isUnit_iff_exists_inv.mpr
      refine ⟨gInv, Subtype.ext ?_⟩
      change a.1 * gInv.1 = 1
      rw [← hga]
      apply Filter.Germ.coe_eq.mpr
      filter_upwards [hg.continuousAt.eventually_ne hg0] with z hz
      exact mul_inv_cancel₀ hz
    · right
      let hInv := AnalyticDivisorAlgebraic8.productAnalyticGermOf
        (fun z ↦ (h z)⁻¹) (hh.inv hh0)
      apply isUnit_iff_exists_inv.mpr
      refine ⟨hInv, Subtype.ext ?_⟩
      change b.1 * hInv.1 = 1
      rw [← hhb]
      apply Filter.Germ.coe_eq.mpr
      filter_upwards [hh.continuousAt.eventually_ne hh0] with z hz
      exact mul_inv_cancel₀ hz

private theorem gaga17_productGerm_unit {n : ℕ}
    {f : (Fin n → ℂ) × ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hf0 : f 0 ≠ 0) :
    IsUnit (AnalyticDivisorAlgebraic8.productAnalyticGermOf f hf) := by
  let fInv := AnalyticDivisorAlgebraic8.productAnalyticGermOf
    (fun z ↦ (f z)⁻¹) (hf.inv hf0)
  apply isUnit_iff_exists_inv.mpr
  refine ⟨fInv, Subtype.ext ?_⟩
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [hf.continuousAt.eventually_ne hf0] with z hz
  exact mul_inv_cancel₀ hz

theorem gaga17_prime_divides_factor_aux {n t : ℕ}
    {F A w s : (Fin n → ℂ) × ℂ → ℂ} {q : (Fin n → ℂ) × ℂ}
    {R : Fin t → (Fin n → ℂ) × ℂ → ℂ} {e : Fin t → ℕ}
    (hA : AnalyticAt ℂ A q) (hiA : IsIrreducibleAt A q)
    (hs : AnalyticAt ℂ s q) (hdiv : F =ᶠ[𝓝 q] fun y ↦ A y * s y)
    (hw : AnalyticAt ℂ w q) (hw0 : w q ≠ 0)
    (hR : ∀ l, AnalyticAt ℂ (R l) q)
    (hfac : F =ᶠ[𝓝 q] fun y ↦ w y * ∏ l, R l y ^ e l) :
    ∃ l : Fin t, ∃ c : (Fin n → ℂ) × ℂ → ℂ, AnalyticAt ℂ c q ∧
      R l =ᶠ[𝓝 q] fun y ↦ A y * c y := by
  classical
  letI := AnalyticDivisorAlgebraic8.productAnalyticGermUFD n
  have hAt := gaga17_analyticAt_translate hA
  have hst := gaga17_analyticAt_translate hs
  have hwt := gaga17_analyticAt_translate hw
  have hRt : ∀ l, AnalyticAt ℂ (fun z ↦ R l (q + z)) 0 :=
    fun l ↦ gaga17_analyticAt_translate (hR l)
  let AG := AnalyticDivisorAlgebraic8.productAnalyticGermOf (fun z ↦ A (q + z)) hAt
  let SG := AnalyticDivisorAlgebraic8.productAnalyticGermOf (fun z ↦ s (q + z)) hst
  let WG := AnalyticDivisorAlgebraic8.productAnalyticGermOf (fun z ↦ w (q + z)) hwt
  let RG : Fin t → ProductAnalyticGerm n := fun l ↦
    AnalyticDivisorAlgebraic8.productAnalyticGermOf (fun z ↦ R l (q + z)) (hRt l)
  have hiAt : IsIrreducibleAt (fun z ↦ A (q + z)) 0 := by
    refine ⟨by simpa using hiA.1, ?_⟩
    intro g h hg hh hgh
    have hsubA : AnalyticAt ℂ (fun y : (Fin n → ℂ) × ℂ ↦ y - q) q :=
      analyticAt_id.sub analyticAt_const
    have hsub : Tendsto (fun y : (Fin n → ℂ) × ℂ ↦ y - q) (𝓝 q) (𝓝 0) := by
      have hc := hsubA.continuousAt
      change Tendsto (fun y : (Fin n → ℂ) × ℂ ↦ y - q) (𝓝 q) (𝓝 (q - q)) at hc
      simpa using hc
    have hg' := hg.comp_of_eq hsubA (by simp)
    have hh' := hh.comp_of_eq hsubA (by simp)
    have hgh' := hgh.comp_tendsto hsub
    have hfac' : A =ᶠ[𝓝 q] fun y ↦ g (y - q) * h (y - q) := by
      simpa [Function.comp_def, add_comm] using hgh'
    rcases hiA.2 _ _ hg' hh' hfac' with hg0 | hh0
    · left; simpa using hg0
    · right; simpa using hh0
  have hAGirr : Irreducible AG := gaga17_productGerm_irreducible hAt hiAt
  have hAGprime : Prime AG := UniqueFactorizationMonoid.irreducible_iff_prime.mp hAGirr
  have htrans : Tendsto (fun z : (Fin n → ℂ) × ℂ ↦ q + z) (𝓝 0) (𝓝 q) := by
    have hc := (analyticAt_const.add analyticAt_id :
      AnalyticAt ℂ (fun z : (Fin n → ℂ) × ℂ ↦ q + z) 0).continuousAt
    change Tendsto (fun z : (Fin n → ℂ) × ℂ ↦ q + z) (𝓝 0) (𝓝 (q + 0)) at hc
    simpa using hc
  have hdivG : AG ∣ WG * ∏ l, RG l ^ e l := by
    refine ⟨SG, ?_⟩
    apply Subtype.ext
    have hd := hdiv.comp_tendsto htrans
    have hf := hfac.comp_tendsto htrans
    have hf' : ((fun z ↦ w (q + z)) * ∏ l, (fun z ↦ R l (q + z)) ^ e l) =ᶠ[𝓝 0]
        fun z ↦ F (q + z) := by
      filter_upwards [hf.symm] with z hz
      simpa only [Pi.mul_apply, Finset.prod_apply, Pi.pow_apply, Function.comp_apply] using hz
    change WG.1 * (productAnalyticGermSubring n).subtype (∏ l, RG l ^ e l) =
      AG.1 * SG.1
    calc
      _ = (Filter.Germ.coeRingHom (𝓝 (0 : (Fin n → ℂ) × ℂ)))
          ((fun z ↦ w (q + z)) * ∏ l, (fun z ↦ R l (q + z)) ^ e l) := by
        rw [map_mul, map_prod, map_prod]
        simp only [map_pow, Filter.Germ.coe_coeRingHom]
        rfl
      _ = ↑(fun z ↦ F (q + z)) := Filter.Germ.coe_eq.mpr hf'
      _ = ↑(fun z ↦ A (q + z) * s (q + z)) := Filter.Germ.coe_eq.mpr (by
        simpa [Function.comp_def] using hd)
      _ = AG.1 * SG.1 := rfl
  have hprod : AG ∣ ∏ l, RG l ^ e l :=
    (gaga17_productGerm_unit hwt (by simpa using hw0)).dvd_mul_left.mp hdivG
  obtain ⟨l, -, hlpow⟩ := (hAGprime.dvd_finset_prod_iff (fun l ↦ RG l ^ e l)).mp hprod
  have hl : AG ∣ RG l := hAGprime.dvd_of_dvd_pow hlpow
  obtain ⟨C, hC⟩ := hl
  obtain ⟨c0, hc0, hcG⟩ := C.2
  refine ⟨l, fun y ↦ c0 (y - q), hc0.comp_of_eq
    (analyticAt_id.sub analyticAt_const) (by simp), ?_⟩
  have hzero : Tendsto (fun y : (Fin n → ℂ) × ℂ ↦ y - q) (𝓝 q) (𝓝 0) := by
    have hc := (analyticAt_id.sub analyticAt_const :
      AnalyticAt ℂ (fun y : (Fin n → ℂ) × ℂ ↦ y - q) q).continuousAt
    change Tendsto (fun y : (Fin n → ℂ) × ℂ ↦ y - q) (𝓝 q) (𝓝 (q - q)) at hc
    simpa using hc
  have hEq : (fun z ↦ R l (q + z)) =ᶠ[𝓝 0]
      fun z ↦ A (q + z) * c0 z := by
    apply Filter.Germ.coe_eq.mp
    calc
      ↑(fun z ↦ R l (q + z)) = (RG l).1 := rfl
      _ = (AG * C).1 := congrArg Subtype.val hC
      _ = AG.1 * C.1 := rfl
      _ = ↑(fun z ↦ A (q + z)) * ↑c0 := congrArg₂ (· * ·) rfl hcG.symm
      _ = ↑(fun z ↦ A (q + z) * c0 z) := rfl
  have := hEq.comp_tendsto hzero
  simpa [Function.comp_def, add_comm] using this

theorem gaga17_associated_of_irreducible_divides_aux {n : ℕ}
    {A B c : (Fin n → ℂ) × ℂ → ℂ} {q : (Fin n → ℂ) × ℂ}
    (hA : AnalyticAt ℂ A q) (hiA : IsIrreducibleAt A q)
    (hB : AnalyticAt ℂ B q) (hiB : IsIrreducibleAt B q)
    (hc : AnalyticAt ℂ c q) (hdiv : B =ᶠ[𝓝 q] fun y ↦ A y * c y) :
    AreAssociatedAt A B q := by
  have hc0 : c q ≠ 0 := by
    rcases hiB.2 A c hA hc hdiv with hA0 | hc0
    · exact False.elim (hA0 hiA.1)
    · exact hc0
  refine ⟨fun y ↦ (c y)⁻¹, hc.inv hc0, inv_ne_zero hc0, ?_⟩
  filter_upwards [hdiv, hc.continuousAt.eventually_ne hc0] with y hy hcy
  rw [hy, mul_comm (A y) (c y), ← mul_assoc, inv_mul_cancel₀ hcy, one_mul]

theorem spec_nearby_factor_matching_aux {n r : ℕ} {ι : Type*}
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
    ∀ j, ∃ l, AreAssociatedAt (Q j) (R l) q := by
  intro j
  obtain ⟨s, hs, hdiv⟩ := spec_nearby_factor_divides_aux hD i hNo hNp hNV hqN
    hv hv0 hP hirr hb hcop hfacN a hzero hu hu0 hQ hcQ hfacQ j
  obtain ⟨l, c, hc, hRl⟩ := gaga17_prime_divides_factor_aux
    (hQ j).1 (hQ j).2.1 hs hdiv hw hw0 (fun l ↦ (hR l).1) hfacR
  exact ⟨l, gaga17_associated_of_irreducible_divides_aux
    (hQ j).1 (hQ j).2.1 (hR l).1 (hR l).2.1 hc hRl⟩

theorem spec_nearby_component_grouping_aux {n r : ℕ} {ι : Type*}
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
        W ∩ gaga17_groupedLocalComponent V f i Q := by
  have hu_ne : ∀ᶠ y in nhds q, u y ≠ 0 := hu.continuousAt.eventually_ne hu0
  have hzero_eq : ∀ᶠ y in nhds q, P a y = 0 ↔ ∃ j, Q j y = 0 := by
    filter_upwards [hfacQ, hu_ne] with y hfac hyu
    rw [hfac]
    simp only [mul_eq_zero, hyu, false_or, Finset.prod_eq_zero_iff,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, eq_zero_of_pow_eq_zero hj⟩
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_⟩
      rw [hj]
      exact zero_pow (hQ j).2.2.ne'
  have hN : N ∩ {y | P a y = 0 ↔ ∃ j, Q j y = 0} ∈ nhds q :=
    inter_mem (hNo.mem_nhds hqN) hzero_eq
  obtain ⟨W, hWsub, hWo, hqW⟩ := mem_nhds_iff.mp hN
  refine ⟨W, hWo, hqW, fun y hy ↦ (hWsub hy).1, ?_⟩
  ext y
  constructor
  · intro hy
    obtain ⟨j, hQj⟩ := (hWsub hy.1).2.mp hy.2.2
    exact ⟨hy.1, mem_iUnion.mpr ⟨j, hy.2.1, hQj⟩⟩
  · intro hy
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy.2
    exact ⟨hy.1, hj.1, (hWsub hy.1).2.mpr ⟨j, hj.2⟩⟩

private theorem gaga17_irreducibleAt_of_fderiv_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {y : E} (hf : AnalyticAt ℂ f y) (hf0 : f y = 0)
    (hd : fderiv ℂ f y ≠ 0) : IsIrreducibleAt f y := by
  refine ⟨hf0, ?_⟩
  intro g h hg hh hfac
  by_contra hn
  push Not at hn
  have he := hfac.fderiv_eq (𝕜 := ℂ)
  have he0 : fderiv ℂ (fun x ↦ g x * h x) y = 0 := by
    change fderiv ℂ (g * h) y = 0
    rw [fderiv_mul hg.differentiableAt hh.differentiableAt, hn.1, hn.2]
    ext z
    simp
  exact hd (he.trans he0)

private theorem gaga17_fderiv_snd_ne_zero {n : ℕ} (q : (Fin n → ℂ) × ℂ) :
    fderiv ℂ (fun y : (Fin n → ℂ) × ℂ ↦ y.2) q ≠ 0 := by
  have hd : HasFDerivAt (fun y : (Fin n → ℂ) × ℂ ↦ y.2)
      (ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ) q := by fun_prop
  intro h
  have he := congrArg (fun L ↦ L (0, 1)) h
  rw [hd.fderiv] at he
  norm_num at he

private theorem gaga17_fderiv_fst_zero_ne_zero (q : (Fin 1 → ℂ) × ℂ) :
    fderiv ℂ (fun y : (Fin 1 → ℂ) × ℂ ↦ y.1 0) q ≠ 0 := by
  have hd : HasFDerivAt (fun y : (Fin 1 → ℂ) × ℂ ↦ y.1 0)
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).comp
        (ContinuousLinearMap.fst ℂ (Fin 1 → ℂ) ℂ)) q := by fun_prop
  intro h
  have he := congrArg (fun L ↦ L (fun _ ↦ 1, 0)) h
  rw [hd.fderiv] at he
  norm_num at he

private theorem gaga17_coordinate_coprime :
    IsCoprimeAt (fun y : (Fin 1 → ℂ) × ℂ ↦ y.1 0) (fun y ↦ y.2) 0 := by
  rintro ⟨q, r, s, hq, hr, hs, hq0, hfr, hfs⟩
  have hdq := hq.differentiableAt
  have hdr := hr.differentiableAt
  have hds := hs.differentiableAt
  have hfr' := hfr.fderiv_eq (𝕜 := ℂ)
  have hfs' := hfs.fderiv_eq (𝕜 := ℂ)
  have hmulr := fderiv_mul hdq hdr
  have hmuls := fderiv_mul hdq hds
  change fderiv ℂ (fun x ↦ q x * r x) 0 = _ at hmulr
  change fderiv ℂ (fun x ↦ q x * s x) 0 = _ at hmuls
  have hdf : HasFDerivAt (fun y : (Fin 1 → ℂ) × ℂ ↦ y.1 0)
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).comp
        (ContinuousLinearMap.fst ℂ (Fin 1 → ℂ) ℂ)) 0 := by fun_prop
  have hdg : HasFDerivAt (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2)
      (ContinuousLinearMap.snd ℂ (Fin 1 → ℂ) ℂ) 0 := by fun_prop
  have er1 := congrArg (fun L ↦ L (fun _ ↦ 1, 0)) hfr'
  have er2 := congrArg (fun L ↦ L (0, 1)) hfr'
  have es1 := congrArg (fun L ↦ L (fun _ ↦ 1, 0)) hfs'
  have es2 := congrArg (fun L ↦ L (0, 1)) hfs'
  rw [hdf.fderiv, hmulr, hq0] at er1 er2
  rw [hdg.fderiv, hmuls, hq0] at es1 es2
  norm_num [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at er1 er2 es1 es2
  have hr0 : r 0 ≠ 0 := by
    intro hrz
    rw [hrz, zero_mul] at er1
    exact one_ne_zero er1
  have hdq2 : fderiv ℂ q 0 (0, 1) = 0 := by
    exact er2.resolve_left hr0
  rw [hdq2, mul_zero] at es2
  exact one_ne_zero es2

theorem gaga17_crossing_data_aux :
    IsLocalDivisorData (univ : Set ((Fin 1 → ℂ) × ℂ)) (fun _ : Unit ↦ univ)
        (fun _ y ↦ y.1 0 * y.2) ∧
      (∀ a, AnalyticOnNhd ℂ (gaga17_crossingFactors a) univ) ∧
      (∀ a, IsIrreducibleAt (gaga17_crossingFactors a) 0) ∧
      Pairwise (fun a b ↦ IsCoprimeAt (gaga17_crossingFactors a)
        (gaga17_crossingFactors b) 0) ∧
      ∀ c : ℂ, IsIrreducibleAt (gaga17_crossingFactors 0) (0, c) := by
  have hfst : ∀ q : (Fin 1 → ℂ) × ℂ, AnalyticAt ℂ (fun y ↦ y.1 0) q := fun q ↦
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt q.1).comp
      analyticAt_fst
  have hsnd : ∀ q : (Fin 1 → ℂ) × ℂ, AnalyticAt ℂ (fun y ↦ y.2) q := fun _ ↦
    analyticAt_snd
  have hprod : AnalyticOnNhd ℂ (fun y : (Fin 1 → ℂ) × ℂ ↦ y.1 0 * y.2) univ :=
    fun q _ ↦ (hfst q).mul (hsnd q)
  have hnonzero : ∀ x : (Fin 1 → ℂ) × ℂ,
      ¬ ∀ᶠ y in 𝓝 x, y.1 0 * y.2 = 0 := by
    intro x hx
    have hall := hprod.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ x) hx
    have hone := hall (mem_univ ((fun _ ↦ 1), 1))
    norm_num at hone
  have hD : IsLocalDivisorData (univ : Set ((Fin 1 → ℂ) × ℂ))
      (fun _ : Unit ↦ univ) (fun _ y ↦ y.1 0 * y.2) := by
    refine ⟨fun _ ↦ isOpen_univ, iUnion_const _, fun _ ↦ hprod, ?_, ?_⟩
    · intro _ x _
      exact hnonzero x
    · intro _ _ x _
      exact ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero,
        Eventually.of_forall fun _ ↦ by simp⟩
  refine ⟨hD, ?_, ?_, ?_, ?_⟩
  · intro a x _
    fin_cases a
    · exact hfst x
    · exact hsnd x
  · intro a
    fin_cases a
    · exact gaga17_irreducibleAt_of_fderiv_ne_zero (hfst 0) rfl
        (gaga17_fderiv_fst_zero_ne_zero 0)
    · exact gaga17_irreducibleAt_of_fderiv_ne_zero (hsnd 0) rfl
        (gaga17_fderiv_snd_ne_zero 0)
  · intro a b hab
    fin_cases a <;> fin_cases b
    · exact (hab rfl).elim
    · exact gaga17_coordinate_coprime
    · intro hcommon
      apply gaga17_coordinate_coprime
      rcases hcommon with ⟨q, r, s, hq, hr, hs, hq0, hsnd, hfst⟩
      exact ⟨q, s, r, hq, hs, hr, hq0, hfst, hsnd⟩
    · exact (hab rfl).elim
  · intro c
    exact gaga17_irreducibleAt_of_fderiv_ne_zero (hfst (0, c)) rfl
      (gaga17_fderiv_fst_zero_ne_zero (0, c))

theorem gaga17_axis_power_data_aux (n m : ℕ) (hm : 0 < m) :
    IsLocalDivisorData (univ : Set ((Fin n → ℂ) × ℂ)) (fun _ : Unit ↦ univ)
        (fun _ y ↦ y.2 ^ m) ∧
      ∀ q : (Fin n → ℂ) × ℂ, q.2 = 0 → IsIrreducibleAt (fun y ↦ y.2) q := by
  have hsnd : ∀ q : (Fin n → ℂ) × ℂ, AnalyticAt ℂ (fun y ↦ y.2) q := fun _ ↦
    analyticAt_snd
  have hpow : AnalyticOnNhd ℂ (fun y : (Fin n → ℂ) × ℂ ↦ y.2 ^ m) univ :=
    fun q _ ↦ (hsnd q).pow m
  have hnonzero : ∀ x : (Fin n → ℂ) × ℂ, ¬ ∀ᶠ y in 𝓝 x, y.2 ^ m = 0 := by
    intro x hx
    have hall := hpow.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ x) hx
    have hone := hall (mem_univ (0, 1))
    norm_num at hone
  refine ⟨?_, ?_⟩
  · refine ⟨fun _ ↦ isOpen_univ, iUnion_const _, fun _ ↦ hpow, ?_, ?_⟩
    · intro _ x _
      exact hnonzero x
    · intro _ _ x _
      exact ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero,
        Eventually.of_forall fun _ ↦ by simp⟩
  · intro q hq
    exact gaga17_irreducibleAt_of_fderiv_ne_zero (hsnd q) hq
      (gaga17_fderiv_snd_ne_zero q)

end HodgeLean.Foundations.AnalyticDivisorAlgebraic17
