import HodgeLean.Adapters.IntersectionProductDefs
import HodgeLean.Adapters.IntersectionProductCMTor
import HodgeLean.Adapters.IntersectionProductCMRegular

/-! # Cohen–Macaulay quotients of a regular local ring

For a regular local ring `A`:
* `A` has a regular system of parameters that is a weakly regular sequence
  (`a3c_exists_regular_sop`);
* a quotient `A ⧸ 𝔭` that is itself a regular local ring satisfies `a3i_IsCMQuotient 𝔭`
  (`a3c_isCMQuotient_of_isRegularLocalRing`);
* the embedding-dimension argument: if `𝔭 + 𝔮 = 𝔪` and `dim A ≤ dim A/𝔭 + dim A/𝔮`, both quotients
  are regular local rings, hence Cohen–Macaulay (`a3c_isCMQuotient_pair`);
* Serre's vanishing `Tor_{i+1}(A/𝔭, A/𝔮) = 0` when both quotients are Cohen–Macaulay,
  `A/(𝔭 + 𝔮)` has finite length and `dim A ≤ dim A/𝔭 + dim A/𝔮`
  (`a3c_isZero_tor_succ_of_isCMQuotient`).

Source: Serre, *Algèbre locale, multiplicités*, Chapitre IV, D and Chapitre V, B.6;
Fulton, *Intersection Theory*, second edition, Proposition 8.2 and §20.4;
Matsumura, *Commutative Ring Theory*, §14 and §17. HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace HodgeLean.Adapters
universe u

section
variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

lemma a3c_exists_list_ofList_eq_maximalIdeal :
    ∃ ys : List R, ys.length = (maximalIdeal R).spanFinrank ∧
      Ideal.ofList ys = maximalIdeal R := by
  classical
  obtain ⟨s, hcard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank (maximalIdeal R).fg_of_isNoetherianRing
  refine ⟨s.toList, by simp [hcard], ?_⟩
  rw [← hspan, Ideal.ofList]
  congr 1
  ext
  simp

end

/-- A regular local ring has a regular system of parameters that is a weakly regular
sequence; in particular it is a domain.
Source: Matsumura, *Commutative Ring Theory*, Theorems 14.3 and 17.8. -/
theorem a3c_exists_regular_sop (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    ∃ ys : List R, (ys.length : WithBot ℕ∞) = ringKrullDim R ∧
      Ideal.ofList ys = maximalIdeal R ∧ IsDomain R ∧
        RingTheory.Sequence.IsWeaklyRegular R ys := by
  obtain ⟨ys, hlen, hys⟩ := a3c_exists_list_ofList_eq_maximalIdeal R
  have hdim : ringKrullDim R = ys.length := by
    rw [hlen, ← IsRegularLocalRing.spanFinrank_maximalIdeal]
  obtain ⟨h1, h2⟩ := a3c_isDomain_isWeaklyRegular ys.length R hdim ys rfl hys
  exact ⟨ys, hdim.symm, hys, h1, h2⟩

section quot
variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- A quotient that is a regular local ring is a Cohen–Macaulay quotient: a regular system of
parameters of `A ⧸ 𝔭`, lifted to `A`, is weakly regular on `A ⧸ 𝔭`.
Source: Matsumura, *Commutative Ring Theory*, Theorem 17.8. -/
theorem a3c_isCMQuotient_of_isRegularLocalRing (𝔭 : Ideal A) [IsRegularLocalRing (A ⧸ 𝔭)] :
    a3i_IsCMQuotient 𝔭 := by
  obtain ⟨ys, hlen, hys, -, hreg⟩ := a3c_exists_regular_sop (A ⧸ 𝔭)
  let s : A ⧸ 𝔭 → A := Function.surjInv Ideal.Quotient.mk_surjective
  have hs : ∀ y, Ideal.Quotient.mk 𝔭 (s y) = y := Function.surjInv_eq Ideal.Quotient.mk_surjective
  have hmap : (ys.map s).map (algebraMap A (A ⧸ 𝔭)) = ys := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id ys]
    exact List.map_congr_left fun y _ => hs y
  refine ⟨ys.map s, ?_, ?_, by simpa using hlen⟩
  · intro r hr
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
    have hy' : y ∈ maximalIdeal (A ⧸ 𝔭) := hys ▸ Ideal.subset_span hy
    have : IsLocalHom (Ideal.Quotient.mk 𝔭) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    rw [← IsLocalRing.maximalIdeal_comap (Ideal.Quotient.mk 𝔭), Ideal.mem_comap, hs]
    exact hy'
  · rw [← RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (S := A ⧸ 𝔭), hmap]
    exact hreg

variable [IsNoetherianRing A]

/-- Embedding dimension of a quotient: `edim A/I + dim P ≤ dim 𝔪/𝔪²`, where `P` is the span of
the classes of `I` in the cotangent space. -/
theorem a3c_spanFinrank_quotient_add_le (I : Ideal A) (hI : I ≤ maximalIdeal A)
    [IsLocalRing (A ⧸ I)] :
    (maximalIdeal (A ⧸ I)).spanFinrank +
        Module.finrank (ResidueField A) (a3c_cotSub I) ≤
      Module.finrank (ResidueField A) (CotangentSpace A) := by
  obtain ⟨zs, hlen, -, hzs⟩ := a3c_exists_list_sup_eq I hI
  have hsum := Submodule.finrank_quotient_add_finrank (a3c_cotSub I)
  have hgen : Ideal.ofList (zs.map (Ideal.Quotient.mk I)) = maximalIdeal (A ⧸ I) := by
    rw [← Ideal.map_ofList, ← IsLocalRing.map_maximalIdeal_of_surjective _
      Ideal.Quotient.mk_surjective, ← hzs, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq]
  have hle : (maximalIdeal (A ⧸ I)).spanFinrank ≤ zs.length := by
    rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    simpa using a3c_finrank_cotangentSpace_le _ hgen
  omega

/-- If `I + J = 𝔪`, the classes of `I` and `J` span the cotangent space. -/
theorem a3c_finrank_le_cotSub_add (I J : Ideal A) (hI : I ≤ maximalIdeal A)
    (hJ : J ≤ maximalIdeal A) (hIJ : I ⊔ J = maximalIdeal A) :
    Module.finrank (ResidueField A) (CotangentSpace A) ≤
      Module.finrank (ResidueField A) (a3c_cotSub I) +
        Module.finrank (ResidueField A) (a3c_cotSub J) := by
  have htop : a3c_cotSub I ⊔ a3c_cotSub J = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨m, rfl⟩ := (maximalIdeal A).toCotangent_surjective v
    have hm : (m : A) ∈ I ⊔ J := by rw [hIJ]; exact m.2
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hm
    have : m = ⟨a, hI ha⟩ + ⟨b, hJ hb⟩ := Subtype.ext hab.symm
    rw [this, map_add]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨_, ha, rfl⟩)
      (Submodule.subset_span ⟨_, hb, rfl⟩)
  have h := Submodule.finrank_sup_add_finrank_inf_eq (a3c_cotSub I) (a3c_cotSub J)
  rw [htop, finrank_top] at h
  omega

omit [IsNoetherianRing A] in
lemma a3c_ne_top_of_isCMQuotient {𝔭 : Ideal A} (h : a3i_IsCMQuotient 𝔭) : 𝔭 ≠ ⊤ := by
  rintro rfl
  obtain ⟨rs, -, -, hrs⟩ := h
  have : ringKrullDim (A ⧸ (⊤ : Ideal A)) = ⊥ := by
    rw [ringKrullDim_eq_bot_iff_subsingleton]
    infer_instance
  rw [this] at hrs
  exact WithBot.coe_ne_bot hrs

omit [IsLocalRing A] [IsNoetherianRing A] in
lemma a3c_finite_iterQuot : ∀ (rs : List A) (M : ModuleCat.{u} A) [Module.Finite A M],
    Module.Finite A (a3c_iterQuot rs M)
  | [], M, _ => ‹_›
  | r :: rs, M, _ => by
    have : Module.Finite A (ModuleCat.of A (QuotSMulTop r M)) :=
      inferInstanceAs (Module.Finite A (QuotSMulTop r M))
    exact a3c_finite_iterQuot rs (ModuleCat.of A (QuotSMulTop r M))

omit [IsLocalRing A] in
/-- A finite module of support dimension at most `0` over a Noetherian local ring has finite
length. -/
theorem a3c_isFiniteLength_of_supportDim_le_zero (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] (h : Module.supportDim A M ≤ 0) : IsFiniteLength A M := by
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator] at h
  have : Ring.KrullDimLE 0 (A ⧸ Module.annihilator A M) := by
    rw [Ring.krullDimLE_iff]
    exact_mod_cast h
  have : IsArtinianRing (A ⧸ Module.annihilator A M) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  let := Module.quotientAnnihilator (R := A) (M := M)
  have : IsScalarTower A (A ⧸ Module.annihilator A M) M :=
    (Module.isTorsionBySet_annihilator A M).isScalarTower
  have : Module.Finite (A ⧸ Module.annihilator A M) M :=
    Module.Finite.of_restrictScalars_finite A _ M
  have : IsArtinian (A ⧸ Module.annihilator A M) M := inferInstance
  have : IsArtinian A M := isArtinian_of_surjective_algebraMap
    (R := A ⧸ Module.annihilator A M) Ideal.Quotient.mk_surjective
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

/-- A Cohen–Macaulay quotient divided by its regular sequence has finite length. -/
theorem a3c_isFiniteLength_iterQuot (𝔭 : Ideal A) (rs : List A)
    (hrs : ∀ r ∈ rs, r ∈ maximalIdeal A)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (A ⧸ 𝔭) rs)
    (hlen : (rs.length : WithBot ℕ∞) = ringKrullDim (A ⧸ 𝔭)) (h𝔭 : 𝔭 ≠ ⊤) :
    IsFiniteLength A (a3c_iterQuot rs (ModuleCat.of A (A ⧸ 𝔭))) := by
  have : Nontrivial (A ⧸ 𝔭) := Ideal.Quotient.nontrivial_iff.mpr h𝔭
  have hreg' : RingTheory.Sequence.IsRegular (A ⧸ 𝔭) rs :=
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hrs).mpr hreg
  have hdim := Module.supportDim_add_length_eq_supportDim_of_isRegular rs hreg'
  rw [Module.supportDim_quotient_eq_ringKrullDim, ← hlen] at hdim
  let e := a3c_iterQuotEquiv rs (ModuleCat.of A (A ⧸ 𝔭))
  have : Module.Finite A (a3c_iterQuot rs (ModuleCat.of A (A ⧸ 𝔭))) :=
    a3c_finite_iterQuot rs (ModuleCat.of A (A ⧸ 𝔭))
  refine a3c_isFiniteLength_of_supportDim_le_zero _ ?_
  rw [Module.supportDim_eq_of_equiv e]
  generalize Module.supportDim A ((A ⧸ 𝔭) ⧸ (Ideal.ofList rs • ⊤ : Submodule A (A ⧸ 𝔭))) = x
    at hdim ⊢
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe x =>
    have h1 : x + (rs.length : ℕ∞) = rs.length := by exact_mod_cast hdim
    have h2 : x = 0 := by
      induction x using ENat.recTopCoe with
      | top => simp at h1
      | coe k =>
        have : k + rs.length = rs.length := by exact_mod_cast h1
        have : k = 0 := by omega
        rw [this]; rfl
    rw [h2]
    rfl

end quot

section reg
variable {A : Type u} [CommRing A] [IsRegularLocalRing A]

/-- The embedding-dimension argument: over a regular local ring `A`, if `𝔭 + 𝔮 = 𝔪` and
`dim A ≤ dim A/𝔭 + dim A/𝔮`, then `A/𝔭` and `A/𝔮` are regular local rings, hence
Cohen–Macaulay quotients.
Source: Fulton, *Intersection Theory*, second edition, Proposition 8.2 (proof);
Matsumura, *Commutative Ring Theory*, §14 and Theorem 17.8. -/
theorem a3c_isCMQuotient_pair (𝔭 𝔮 : Ideal A)
    (h𝔭 : 𝔭 ≤ maximalIdeal A) (h𝔮 : 𝔮 ≤ maximalIdeal A) (hsup : 𝔭 ⊔ 𝔮 = maximalIdeal A)
    (a b d : ℕ) (hd : ringKrullDim A = d) (ha : ringKrullDim (A ⧸ 𝔭) = a)
    (hb : ringKrullDim (A ⧸ 𝔮) = b) (hab : d ≤ a + b) :
    a3i_IsCMQuotient 𝔭 ∧ a3i_IsCMQuotient 𝔮 := by
  have hV : Module.finrank (ResidueField A) (CotangentSpace A) = d := by
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace A).mp inferInstance
    rw [hd] at h
    exact_mod_cast h
  have : Nontrivial (A ⧸ 𝔭) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top h𝔭)
  have : Nontrivial (A ⧸ 𝔮) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top h𝔮)
  have : IsLocalRing (A ⧸ 𝔭) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsLocalRing (A ⧸ 𝔮) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have e1 := a3c_spanFinrank_quotient_add_le 𝔭 h𝔭
  have e2 := a3c_spanFinrank_quotient_add_le 𝔮 h𝔮
  have e3 := a3c_finrank_le_cotSub_add 𝔭 𝔮 h𝔭 h𝔮 hsup
  have f1 : a ≤ (maximalIdeal (A ⧸ 𝔭)).spanFinrank := by
    have h := ringKrullDim_le_spanFinrank_maximalIdeal (A ⧸ 𝔭)
    rw [ha] at h
    exact_mod_cast h
  have f2 : b ≤ (maximalIdeal (A ⧸ 𝔮)).spanFinrank := by
    have h := ringKrullDim_le_spanFinrank_maximalIdeal (A ⧸ 𝔮)
    rw [hb] at h
    exact_mod_cast h
  have : IsRegularLocalRing (A ⧸ 𝔭) := IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (by
    rw [ha]; exact_mod_cast (show (maximalIdeal (A ⧸ 𝔭)).spanFinrank ≤ a by omega))
  have : IsRegularLocalRing (A ⧸ 𝔮) := IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (by
    rw [hb]; exact_mod_cast (show (maximalIdeal (A ⧸ 𝔮)).spanFinrank ≤ b by omega))
  exact ⟨a3c_isCMQuotient_of_isRegularLocalRing 𝔭, a3c_isCMQuotient_of_isRegularLocalRing 𝔮⟩

/-- Serre's vanishing of higher `Tor` for Cohen–Macaulay quotients of a regular local ring:
if `A ⧸ 𝔭` and `A ⧸ 𝔮` are Cohen–Macaulay, a power of `𝔪` lies in `𝔭 + 𝔮` and
`dim A ≤ dim A/𝔭 + dim A/𝔮`, then `Tor_{i+1}(A/𝔭, A/𝔮) = 0`.
Source: Serre, *Algèbre locale, multiplicités*, Chapitre V, B.6, Corollaire; Fulton,
*Intersection Theory*, second edition, §20.4. -/
theorem a3c_isZero_tor_succ_of_isCMQuotient (𝔭 𝔮 : Ideal A)
    (hu : a3i_IsCMQuotient 𝔭) (hv : a3i_IsCMQuotient 𝔮) (K : ℕ)
    (hK : maximalIdeal A ^ K ≤ 𝔭 ⊔ 𝔮)
    (hdim : ringKrullDim A ≤ ringKrullDim (A ⧸ 𝔭) + ringKrullDim (A ⧸ 𝔮)) (i : ℕ) :
    IsZero (((Tor (ModuleCat.{u} A) (i + 1)).obj (ModuleCat.of A (A ⧸ 𝔭))).obj
      (ModuleCat.of A (A ⧸ 𝔮))) := by
  obtain ⟨xs, hxlen, hxs, -, hxreg⟩ := a3c_exists_regular_sop A
  obtain ⟨rs, hrs, hrreg, hrlen⟩ := hu
  obtain ⟨ss, hss, hsreg, hslen⟩ := hv
  have h𝔭 : 𝔭 ≠ ⊤ := a3c_ne_top_of_isCMQuotient ⟨rs, hrs, hrreg, hrlen⟩
  have hlen : xs.length ≤ rs.length + ss.length := by
    rw [← hxlen, ← hrlen, ← hslen] at hdim
    exact_mod_cast hdim
  have hann : maximalIdeal A ^ K ≤ Module.annihilator A (ModuleCat.of A (A ⧸ 𝔭)) ⊔
      Module.annihilator A (ModuleCat.of A (A ⧸ 𝔮)) := by
    change maximalIdeal A ^ K ≤ Module.annihilator A (A ⧸ 𝔭) ⊔ Module.annihilator A (A ⧸ 𝔮)
    rw [Ideal.annihilator_quotient, Ideal.annihilator_quotient]
    exact hK
  exact a3c_isZero_tor_cm xs hxreg hxs (ModuleCat.of A (A ⧸ 𝔮)) ss hsreg hss K rs
    (ModuleCat.of A (A ⧸ 𝔭)) hrreg hrs hann
    (a3c_isFiniteLength_iterQuot 𝔭 rs hrs hrreg hrlen h𝔭) (i + 1) (by omega)

end reg

end HodgeLean.Adapters
