import HodgeLean.Adapters.IntersectionProductMovingFamily
import HodgeLean.Foundations.Mathlib.GenericFreeness
import Mathlib.Algebra.MvPolynomial.Funext

/-! # Generic parameters and the dimension of generic fibres

Roberts' construction chooses a linear projection and a linear translation "in general position".
A set of complex parameter values is generic (`a3r_Generic`) when it contains the non-vanishing
locus of a nonzero polynomial; generic sets are nonempty and closed under finite intersections,
and the non-vanishing locus of a nonzero polynomial with coefficients in any field extension of
`ℂ` is generic (`a3r_generic_of_ne_zero`).

The dimension tool is the generic fibre dimension (`a3r_generic_fibre_dim`): for a finite-type
algebra `E` over the polynomial ring `ℂ[a_ι]`, at generic points `a` every prime of `E` over `a`
has `dim E/𝔓 + card ι ≤ dim E` (generic flatness and going-down). Its main instance is the linear
incidence bound `a3r_generic_linear`: for a finite-type `ℂ`-algebra `D`, at a generic complex
matrix `a` every prime containing the equations `Σ_k a_{ik} δ_k = c_i` and not containing `δ_j`
has `dim D/𝔓 + card ρ ≤ dim D`.

Source: EGA IV, Théorème 6.9.1 (generic flatness); Matsumura, *Commutative Ring Theory*,
Theorem 15.1 (dimension and going-down for flat extensions); Hartshorne, *Algebraic Geometry*,
II, Exercise 3.22 (dimension of fibres); Kleiman, *The transversality of a general translate*,
Compositio Math. 28 (1974), proof of Theorem 2. HC no distance; AV milestone no distance.
-/

noncomputable section

open MvPolynomial

namespace HodgeLean.Adapters

/-! ## Generic sets of parameters -/

/-- A set of complex parameter values is generic if it contains the locus where some nonzero
polynomial does not vanish. -/
def a3r_Generic {ι : Type} (U : Set (ι → ℂ)) : Prop :=
  ∃ F : MvPolynomial ι ℂ, F ≠ 0 ∧ ∀ a, eval a F ≠ 0 → a ∈ U

theorem a3r_generic_univ {ι : Type} : a3r_Generic (Set.univ : Set (ι → ℂ)) :=
  ⟨1, one_ne_zero, fun _ _ => trivial⟩

theorem a3r_Generic.mono {ι : Type} {U V : Set (ι → ℂ)} (h : a3r_Generic U) (hUV : U ⊆ V) :
    a3r_Generic V :=
  let ⟨F, hF, hU⟩ := h
  ⟨F, hF, fun a ha => hUV (hU a ha)⟩

theorem a3r_Generic.inter {ι : Type} {U V : Set (ι → ℂ)} (hU : a3r_Generic U)
    (hV : a3r_Generic V) : a3r_Generic (U ∩ V) := by
  obtain ⟨F, hF, hFU⟩ := hU
  obtain ⟨G, hG, hGV⟩ := hV
  refine ⟨F * G, mul_ne_zero hF hG, fun a ha => ?_⟩
  rw [map_mul] at ha
  exact ⟨hFU a (left_ne_zero_of_mul ha), hGV a (right_ne_zero_of_mul ha)⟩

theorem a3r_generic_iInter {ι κ : Type} (s : Finset κ) (U : κ → Set (ι → ℂ))
    (hU : ∀ i ∈ s, a3r_Generic (U i)) : a3r_Generic {a | ∀ i ∈ s, a ∈ U i} := by
  classical
  induction s using Finset.induction_on with
  | empty => exact a3r_generic_univ.mono fun _ _ i hi => absurd hi (Finset.notMem_empty i)
  | insert j s hj ih =>
    refine ((hU j (Finset.mem_insert_self j s)).inter
      (ih fun i hi => hU i (Finset.mem_insert_of_mem hi))).mono ?_
    rintro a ⟨h1, h2⟩ i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact h1
    · exact h2 i hi

theorem a3r_generic_iInter_fintype {ι κ : Type} [Finite κ] (U : κ → Set (ι → ℂ))
    (hU : ∀ i, a3r_Generic (U i)) : a3r_Generic {a | ∀ i, a ∈ U i} := by
  have := Fintype.ofFinite κ
  exact (a3r_generic_iInter Finset.univ U fun i _ => hU i).mono fun a ha i =>
    ha i (Finset.mem_univ i)

theorem a3r_generic_biInter {ι κ : Type} (s : Set κ) (hs : s.Finite) (U : κ → Set (ι → ℂ))
    (hU : ∀ i ∈ s, a3r_Generic (U i)) : a3r_Generic {a | ∀ i ∈ s, a ∈ U i} :=
  (a3r_generic_iInter hs.toFinset U fun i hi => hU i (hs.mem_toFinset.1 hi)).mono
    fun _ ha i hi => ha i (hs.mem_toFinset.2 hi)

theorem a3r_Generic.nonempty {ι : Type} {U : Set (ι → ℂ)} (h : a3r_Generic U) : U.Nonempty := by
  obtain ⟨F, hF, hU⟩ := h
  by_contra hne
  apply hF
  refine MvPolynomial.funext fun b => ?_
  rw [map_zero]
  by_contra hb
  exact hne ⟨b, hU b hb⟩

/-- Genericity pulls back along an injective change of the parameter index. -/
theorem a3r_Generic.comap {ι κ : Type} (f : ι → κ) (hf : Function.Injective f)
    {U : Set (ι → ℂ)} (h : a3r_Generic U) : a3r_Generic {b : κ → ℂ | b ∘ f ∈ U} := by
  obtain ⟨F, hF, hU⟩ := h
  refine ⟨rename f F, fun h0 => hF (rename_injective f hf (by rw [h0, map_zero])), fun b hb => ?_⟩
  rw [eval_rename] at hb
  exact hU _ hb

/-- The coefficientwise image of a polynomial under a linear map. -/
def a3r_mapLin {ι K : Type} [Field K] [Algebra ℂ K] (φ : K →ₗ[ℂ] ℂ) (G : MvPolynomial ι K) :
    MvPolynomial ι ℂ :=
  ∑ u ∈ G.support, monomial u (φ (G.coeff u))

theorem a3r_eval_mapLin {ι K : Type} [Field K] [Algebra ℂ K] (φ : K →ₗ[ℂ] ℂ)
    (G : MvPolynomial ι K) (a : ι → ℂ) :
    eval a (a3r_mapLin φ G) = φ (eval (fun i => algebraMap ℂ K (a i)) G) := by
  conv_rhs => rw [G.as_sum]
  rw [a3r_mapLin, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [eval_monomial, eval_monomial]
  have : (u.prod fun i e => algebraMap ℂ K (a i) ^ e) =
      algebraMap ℂ K (u.prod fun i e => a i ^ e) := by
    rw [map_finsuppProd]
    simp [map_pow]
  rw [this, mul_comm (G.coeff u), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

theorem a3r_coeff_mapLin {ι K : Type} [Field K] [Algebra ℂ K] (φ : K →ₗ[ℂ] ℂ)
    (G : MvPolynomial ι K) (u : ι →₀ ℕ) : (a3r_mapLin φ G).coeff u = φ (G.coeff u) := by
  classical
  rw [a3r_mapLin, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, map_zero]

/-- A nonzero polynomial with coefficients in a field extension of `ℂ` does not vanish at generic
complex points. -/
theorem a3r_generic_of_ne_zero {ι K : Type} [Field K] [Algebra ℂ K] (G : MvPolynomial ι K)
    (hG : G ≠ 0) : a3r_Generic {a : ι → ℂ | eval (fun i => algebraMap ℂ K (a i)) G ≠ 0} := by
  obtain ⟨u, hu⟩ := MvPolynomial.ne_zero_iff.1 hG
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ K, φ (G.coeff u) ≠ 0 := by
    by_contra h
    push Not at h
    exact hu ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h)
  refine ⟨a3r_mapLin φ G, fun h0 => hφ ?_, fun a ha h0 => ha ?_⟩
  · rw [← a3r_coeff_mapLin, h0]
    rfl
  · rw [a3r_eval_mapLin, h0, map_zero]

/-! ## Dimension of generic fibres -/

section GenericFibre

variable {ι : Type} [Fintype ι]

/-- The maximal ideal of the complex point `a`. -/
abbrev a3r_pt (a : ι → ℂ) : Ideal (MvPolynomial ι ℂ) := RingHom.ker (eval a)

instance a3r_pt_isMaximal (a : ι → ℂ) : (a3r_pt a).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun c => ⟨C c, eval_C c⟩

theorem a3r_height_pt (a : ι → ℂ) : ((a3r_pt a).height : WithBot ℕ∞) = Fintype.card ι := by
  have h := hc9k8_height_add_ringKrullDim_quotient (k := ℂ) (a3r_pt a)
  have hq : ringKrullDim (MvPolynomial ι ℂ ⧸ a3r_pt a) = 0 := by
    have : IsField (MvPolynomial ι ℂ ⧸ a3r_pt a) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 inferInstance
    exact @ringKrullDim_eq_zero_of_isField _ _ this
  rw [hq, add_zero, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    ENat.card_eq_coe_fintype_card, zero_add] at h
  exact h

omit [Fintype ι] in
/-- A polynomial not vanishing at `a` lies outside every prime over the point `a`. -/
theorem a3r_notMem_of_eval_ne_zero {E : Type} [CommRing E] [Algebra (MvPolynomial ι ℂ) E]
    (a : ι → ℂ) (F : MvPolynomial ι ℂ) (hF : eval a F ≠ 0) (𝔓 : Ideal E) [𝔓.IsPrime]
    (h𝔓 : a3r_pt a ≤ 𝔓.comap (algebraMap (MvPolynomial ι ℂ) E)) : algebraMap (MvPolynomial ι ℂ) E F ∉ 𝔓 := by
  intro hmem
  have h1 : F - C (eval a F) ∈ a3r_pt a := by
    rw [RingHom.mem_ker, map_sub, eval_C, sub_self]
  have h2 : C (eval a F) ∈ 𝔓.comap (algebraMap (MvPolynomial ι ℂ) E) := by
    have := h𝔓 h1
    rw [Ideal.mem_comap, map_sub] at this
    rw [Ideal.mem_comap]
    simpa using sub_mem hmem this
  have hu : IsUnit (C (eval a F) : MvPolynomial ι ℂ) := (isUnit_iff_ne_zero.2 hF).map C
  exact (Ideal.IsPrime.ne_top inferInstance) (Ideal.eq_top_of_isUnit_mem _ h2 hu)

/-- The generic fibre dimension for a domain of finite type over a polynomial ring. -/
theorem a3r_generic_fibre_dim_domain (D : Type) [CommRing D] [IsDomain D]
    [Algebra (MvPolynomial ι ℂ) D] [Algebra ℂ D] [IsScalarTower ℂ (MvPolynomial ι ℂ) D]
    [Algebra.FiniteType ℂ D] :
    a3r_Generic {a | ∀ 𝔓 : Ideal D, 𝔓.IsPrime → a3r_pt a ≤ 𝔓.comap (algebraMap (MvPolynomial ι ℂ) D) →
      ringKrullDim (D ⧸ 𝔓) + Fintype.card ι ≤ ringKrullDim D} := by
  classical
  set Rp := MvPolynomial ι ℂ
  by_cases hinj : Function.Injective (algebraMap Rp D)
  · have : Algebra.FiniteType Rp D := Algebra.FiniteType.of_restrictScalars_finiteType ℂ Rp D
    obtain ⟨F, hF0, hflat⟩ := HodgeLean.GenericFreeness.genFlat_of_finiteType (A := Rp) (B := D)
    refine ⟨F, hF0, fun a ha 𝔓 h𝔓 hle => ?_⟩
    set f := algebraMap Rp D F
    let Df := Localization.Away f
    have hloc : IsLocalizedModule (Submonoid.powers F)
        (IsScalarTower.toAlgHom Rp D Df).toLinearMap := by
      rw [isLocalizedModule_iff_isLocalization, Algebra.algebraMapSubmonoid_powers]
      infer_instance
    have : Module.Flat Rp (LocalizedModule (Submonoid.powers F) D) := hflat F dvd_rfl
    have : Module.Flat Rp Df :=
      Module.Flat.of_linearEquiv (IsLocalizedModule.iso (Submonoid.powers F)
        (IsScalarTower.toAlgHom Rp D Df).toLinearMap).symm
    have : Algebra.HasGoingDown Rp Df := Algebra.HasGoingDown.of_flat
    have hf : f ∉ 𝔓 := a3r_notMem_of_eval_ne_zero a F ha 𝔓 hle
    have hdisj : Disjoint (Submonoid.powers f : Set D) (𝔓 : Set D) := by
      rw [Set.disjoint_left]
      rintro _ ⟨m, rfl⟩ hm
      exact hf (h𝔓.mem_of_pow_mem m hm)
    set 𝔓' := 𝔓.map (algebraMap D Df)
    have h𝔓' : 𝔓'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ Df 𝔓 h𝔓 hdisj
    have hunder : 𝔓'.under D = 𝔓 := IsLocalization.under_map_of_isPrime_disjoint _ Df h𝔓 hdisj
    have hlies : 𝔓'.LiesOver (a3r_pt a) := by
      constructor
      rw [Ideal.under, IsScalarTower.algebraMap_eq Rp D Df, ← Ideal.comap_comap]
      change a3r_pt a = Ideal.comap (algebraMap Rp D) (𝔓'.under D)
      rw [hunder]
      exact (Ideal.IsMaximal.eq_of_le inferInstance (Ideal.IsPrime.ne_top inferInstance) hle)
    have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing ℂ D
    have : IsNoetherianRing Df := IsLocalization.isNoetherianRing (Submonoid.powers f) Df inferInstance
    have hht := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (a3r_pt a) 𝔓'
    have hht' : 𝔓.height = 𝔓'.height := by
      rw [← hunder]
      exact IsLocalization.height_under (Submonoid.powers f) 𝔓'
    have hdim := hc9k8_height_add_ringKrullDim_quotient (k := ℂ) 𝔓
    rw [← hdim, hht', hht, add_comm]
    have hpt := a3r_height_pt a
    gcongr
    rw [← hpt]
    exact_mod_cast le_self_add
  · obtain ⟨F, hF⟩ : ∃ F : Rp, F ≠ 0 ∧ algebraMap Rp D F = 0 := by
      by_contra h
      push Not at h
      exact hinj ((injective_iff_map_eq_zero _).2 fun F hF => by
        by_contra hne; exact h F hne hF)
    refine ⟨F, hF.1, fun a ha 𝔓 h𝔓 hle => ?_⟩
    exact absurd (hF.2 ▸ zero_mem 𝔓) (a3r_notMem_of_eval_ne_zero a F ha 𝔓 hle)

/-- The generic fibre dimension: for a finite-type algebra `E` over `ℂ[a_ι]`, at generic complex
points `a`, every prime of `E` over `a` has codimension at least `card ι` in dimension. -/
theorem a3r_generic_fibre_dim (E : Type) [CommRing E] [Algebra (MvPolynomial ι ℂ) E] [Algebra ℂ E]
    [IsScalarTower ℂ (MvPolynomial ι ℂ) E] [Algebra.FiniteType ℂ E] :
    a3r_Generic {a | ∀ 𝔓 : Ideal E, 𝔓.IsPrime → a3r_pt a ≤ 𝔓.comap (algebraMap (MvPolynomial ι ℂ) E) →
      ringKrullDim (E ⧸ 𝔓) + Fintype.card ι ≤ ringKrullDim E} := by
  classical
  have : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing ℂ E
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing E ⊥
  refine (a3r_generic_biInter _ hfin (fun Q => {a | ∀ 𝔓 : Ideal (E ⧸ Q), 𝔓.IsPrime →
      a3r_pt a ≤ 𝔓.comap (algebraMap (MvPolynomial ι ℂ) (E ⧸ Q)) →
      ringKrullDim ((E ⧸ Q) ⧸ 𝔓) + Fintype.card ι ≤ ringKrullDim (E ⧸ Q)}) ?_).mono ?_
  · intro Q hQ
    have : Q.IsPrime := hQ.1.1
    exact a3r_generic_fibre_dim_domain (E ⧸ Q)
  · intro a ha 𝔓 h𝔓 hle
    obtain ⟨Q, hQ, hQ𝔓⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ 𝔓)
    have : Q.IsPrime := hQ.1.1
    have hker : RingHom.ker (Ideal.Quotient.mk Q) ≤ 𝔓 := by rwa [Ideal.mk_ker]
    have h𝔓' : (𝔓.map (Ideal.Quotient.mk Q)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
    have hcomap : (𝔓.map (Ideal.Quotient.mk Q)).comap (algebraMap (MvPolynomial ι ℂ) (E ⧸ Q)) =
        𝔓.comap (algebraMap (MvPolynomial ι ℂ) E) := by
      rw [IsScalarTower.algebraMap_eq (MvPolynomial ι ℂ) E (E ⧸ Q), ← Ideal.comap_comap,
        Ideal.Quotient.algebraMap_eq, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
        sup_eq_left.2 hker]
    have := ha Q hQ _ h𝔓' (hcomap ▸ hle)
    rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hQ𝔓)] at this
    exact this.trans (ringKrullDim_quotient_le Q)

end GenericFibre

/-! ## Linear incidence conditions -/

theorem a3r_withBot_le_of_add_le_add {x y : WithBot ℕ∞} (n : ℕ) (h : x + n ≤ y + n) : x ≤ y := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe x =>
    induction y using WithBot.recBotCoe with
    | bot => exact absurd h (by simp)
    | coe y =>
      have h' : x + n ≤ y + n := by exact_mod_cast h
      exact_mod_cast (ENat.add_le_add_iff_right (ENat.natCast_ne_top n)).1 h'

/-- Localization does not increase the Krull dimension. -/
theorem a3r_ringKrullDim_localization_le {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] : ringKrullDim S ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    (Monotone.strictMono_of_injective (fun _ _ h => Ideal.comap_mono h)
      (PrimeSpectrum.localization_comap_injective S M))


/-- Linear incidence conditions: for a finite-type `ℂ`-algebra `D` with elements `δ_k` and
`c_i`, at generic complex matrices `a`, every prime of `D` containing the equations
`Σ_k a_{ik} δ_k = c_i` and not containing `δ_j` has dimension at most `dim D - card ρ`. The
equations solve for the column `a_{·j}` where `δ_j` is a unit, so the incidence algebra is a
polynomial ring over `D[1/δ_j]`.
Source: Hartshorne, *Algebraic Geometry*, II, Exercise 3.22 (dimension of fibres);
Kleiman, *The transversality of a general translate* (1974), proof of Theorem 2. -/
theorem a3r_generic_linear {ρ κ : Type} [Fintype ρ] [Fintype κ] [DecidableEq κ] (D : Type)
    [CommRing D] [Algebra ℂ D] [Algebra.FiniteType ℂ D] (δ : κ → D) (c : ρ → D) (j : κ) :
    a3r_Generic {a : ρ × κ → ℂ | ∀ 𝔓 : Ideal D, 𝔓.IsPrime → δ j ∉ 𝔓 →
      (∀ i, ∑ k, algebraMap ℂ D (a (i, k)) * δ k - c i ∈ 𝔓) →
      ringKrullDim (D ⧸ 𝔓) + Fintype.card ρ ≤ ringKrullDim D} := by
  classical
  set Dδ := Localization.Away (δ j)
  set E := MvPolynomial (ρ × {k // k ≠ j}) Dδ
  set u : Dδ := IsLocalization.Away.invSelf (δ j)
  -- the parametrization of the incidence algebra
  let val : ρ × κ → E := fun ik =>
    if h : ik.2 = j then
      C u * (C (algebraMap D Dδ (c ik.1)) -
        ∑ k : {k // k ≠ j}, C (algebraMap D Dδ (δ k)) * X (ik.1, k))
    else X (ik.1, ⟨ik.2, h⟩)
  let φ : MvPolynomial (ρ × κ) ℂ →ₐ[ℂ] E := aeval val
  let : Algebra (MvPolynomial (ρ × κ) ℂ) E := φ.toRingHom.toAlgebra
  have : IsScalarTower ℂ (MvPolynomial (ρ × κ) ℂ) E :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  have : Algebra.FiniteType ℂ Dδ := Algebra.FiniteType.trans (S := D) inferInstance
    (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (δ j)) Dδ)
  have : Algebra.FiniteType ℂ E := Algebra.FiniteType.trans (S := Dδ) inferInstance inferInstance
  have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing ℂ D
  have : IsNoetherianRing Dδ := Algebra.FiniteType.isNoetherianRing ℂ Dδ
  have hdimE : ringKrullDim E + Fintype.card ρ ≤ ringKrullDim D + Fintype.card (ρ × κ) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ENat.card_eq_coe_fintype_card]
    have hcard : Fintype.card (ρ × {k // k ≠ j}) + Fintype.card ρ = Fintype.card (ρ × κ) := by
      have h1 : Fintype.card {k // k ≠ j} + 1 = Fintype.card κ := by
        have := Fintype.card_pos_iff.2 ⟨j⟩
        rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
        omega
      rw [Fintype.card_prod, Fintype.card_prod, ← h1]
      ring
    rw [← hcard, add_assoc]
    push_cast
    gcongr
    exact a3r_ringKrullDim_localization_le (Submonoid.powers (δ j))
  refine (a3r_generic_fibre_dim (ι := ρ × κ) E).mono fun a ha 𝔓 h𝔓 hδ hEq => ?_
  -- the point of the incidence algebra over `a` and `𝔓`
  set T := Localization.Away (Ideal.Quotient.mk 𝔓 (δ j))
  have hδ' : Ideal.Quotient.mk 𝔓 (δ j) ≠ 0 := fun h => hδ (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have : IsDomain T := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors hδ')
  let ε : Dδ →+* T := IsLocalization.Away.map Dδ T (Ideal.Quotient.mk 𝔓) (δ j)
  let Ψ : E →+* T := eval₂Hom ε fun ik => algebraMap ℂ T (a (ik.1, ik.2))
  have hεD : ∀ d : D, ε (algebraMap D Dδ d) = algebraMap (D ⧸ 𝔓) T (Ideal.Quotient.mk 𝔓 d) :=
    fun d => IsLocalization.map_eq _ d
  have hεu : ε u * algebraMap (D ⧸ 𝔓) T (Ideal.Quotient.mk 𝔓 (δ j)) = 1 := by
    rw [← hεD, ← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]
  have hεC : ∀ z : ℂ, ε (algebraMap ℂ Dδ z) = algebraMap ℂ T z := by
    intro z
    rw [IsScalarTower.algebraMap_apply ℂ D Dδ, hεD, Ideal.Quotient.mk_algebraMap,
      ← IsScalarTower.algebraMap_apply]
  have hΨC : ∀ x, Ψ (C x) = ε x := fun x => eval₂_C _ _ _
  have hΨX : ∀ ik, Ψ (X ik) = algebraMap ℂ T (a (ik.1, ik.2)) := fun ik => eval₂_X _ _ _
  -- `Ψ` sends the parameters to `a`
  have hΨ : Ψ.comp (algebraMap (MvPolynomial (ρ × κ) ℂ) E) = (algebraMap ℂ T).comp (eval a) := by
    refine MvPolynomial.ringHom_ext (fun z => ?_) (fun ik => ?_)
    · change Ψ (φ (C z)) = _
      rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_apply, hΨC, hεC, RingHom.comp_apply,
        eval_C]
    · change Ψ (φ (X ik)) = _
      rw [MvPolynomial.aeval_X, RingHom.comp_apply, eval_X]
      obtain ⟨i, k⟩ := ik
      by_cases hk : k = j
      · subst hk
        simp only [val, dite_true]
        rw [map_mul, map_sub, map_sum, hΨC, hΨC, hεD]
        simp only [map_mul, hΨC, hΨX, hεD]
        have hrel := hEq i
        rw [Fintype.sum_eq_add_sum_subtype_ne _ k] at hrel
        have hrel' : algebraMap (D ⧸ 𝔓) T (Ideal.Quotient.mk 𝔓 (c i)) -
            ∑ x : {x // x ≠ k}, algebraMap (D ⧸ 𝔓) T (Ideal.Quotient.mk 𝔓 (δ x)) *
              algebraMap ℂ T (a (i, x)) =
            algebraMap ℂ T (a (i, k)) * algebraMap (D ⧸ 𝔓) T (Ideal.Quotient.mk 𝔓 (δ k)) := by
          have h0 := congrArg (algebraMap (D ⧸ 𝔓) T) (Ideal.Quotient.eq_zero_iff_mem.2 hrel)
          simp only [map_sub, map_add, map_mul, map_sum, map_zero, Ideal.Quotient.mk_algebraMap,
            ← IsScalarTower.algebraMap_apply] at h0
          have hs : ∑ x : {x // x ≠ k}, algebraMap (D ⧸ 𝔓) T (Ideal.Quotient.mk 𝔓 (δ x)) *
              algebraMap ℂ T (a (i, x)) = ∑ x : {x // x ≠ k}, algebraMap ℂ T (a (i, x)) *
              algebraMap (D ⧸ 𝔓) T (Ideal.Quotient.mk 𝔓 (δ x)) :=
            Finset.sum_congr rfl fun _ _ => mul_comm _ _
          rw [hs, ← sub_eq_zero, ← neg_eq_zero, ← h0]
          ring
        rw [hrel', mul_comm (algebraMap ℂ T _), ← mul_assoc, hεu, one_mul]
      · simp only [val, hk, dite_false, hΨX]
  set 𝔓t := RingHom.ker Ψ
  have h𝔓t : 𝔓t.IsPrime := RingHom.ker_isPrime Ψ
  have hle : a3r_pt a ≤ 𝔓t.comap (algebraMap (MvPolynomial (ρ × κ) ℂ) E) := by
    intro F hF
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hΨ, RingHom.comp_apply,
      RingHom.mem_ker.1 hF, map_zero]
  have hfib := ha 𝔓t h𝔓t hle
  -- `D/𝔓` embeds in `E/𝔓t`
  let f : D →ₐ[ℂ] E := (IsScalarTower.toAlgHom ℂ Dδ E).comp (IsScalarTower.toAlgHom ℂ D Dδ)
  have hcomap : Ideal.comap f 𝔓t = 𝔓 := by
    ext d
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change Ψ (algebraMap Dδ E (algebraMap D Dδ d)) = 0 ↔ d ∈ 𝔓
    rw [MvPolynomial.algebraMap_eq, hΨC, hεD, ← Ideal.Quotient.eq_zero_iff_mem]
    exact (IsLocalization.injective T (powers_le_nonZeroDivisors_of_noZeroDivisors hδ')).eq_iff'
      (map_zero _)
  let ι := Ideal.quotientMapₐ 𝔓t f hcomap.ge
  have hι : Function.Injective ι :=
    Ideal.quotientMap_injective' (H := (show 𝔓 ≤ Ideal.comap (f : D →+* E) 𝔓t from hcomap.ge))
      hcomap.le
  have : Algebra.FiniteType ℂ (E ⧸ 𝔓t) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  have : Algebra.FiniteType ℂ (D ⧸ 𝔓) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  have hdim := a3m_ringKrullDim_le_of_injective ι hι
  apply a3r_withBot_le_of_add_le_add (Fintype.card (ρ × κ))
  calc ringKrullDim (D ⧸ 𝔓) + Fintype.card ρ + Fintype.card (ρ × κ)
      ≤ ringKrullDim (E ⧸ 𝔓t) + Fintype.card (ρ × κ) + Fintype.card ρ := by
        rw [add_right_comm]; gcongr
    _ ≤ ringKrullDim E + Fintype.card ρ := by gcongr
    _ ≤ _ := hdimE

end HodgeLean.Adapters
