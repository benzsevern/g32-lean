import HodgeLean.Foundations.Mathlib.CyclePushforwardCore
import HodgeLean.Foundations.Curves.CurveValuation

/-! # Orders of vanishing as sums over valuations

Helpers for lane A2 (rational equivalence), pure commutative algebra. For a local domain `O` with
an algebra map to a field `F`, `a2r_Dom O F` is the set of proper valuation subrings of `F`
dominating `O`, `a2r_resDeg O v` the residue degree of `v` over `O` and `a2r_vord v x` the
integer order of `x` at a discrete valuation subring `v`. A prime `P` of a domain `R` whose
localization is a DVR gives the valuation subring `a2r_locVal P`; every proper valuation subring
containing `R` and centred at `P` equals it.
HC no distance; AV milestone no distance.
-/

noncomputable section
open IsLocalRing HodgeLean.Foundations.Curves

namespace HodgeLean.Adapters

/-! ## Integer orders, dominating valuation subrings and residue degrees -/

/-- The integer-valued order of vanishing `Ring.ordFrac` on the fraction field of a
one-dimensional Noetherian domain, with the junk value `0` at `0`. On a stalk of a scheme it is
Mathlib's `Scheme.ord`.
Source: Fulton, *Intersection Theory*, second edition, §1.2; Stacks Project, Tag 02MD. -/
def a2r_ordZ (R K : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [Field K] [Algebra R K] [IsFractionRing R K] (x : K) : ℤ :=
  Multiplicative.toAdd ((Ring.ordFrac R x).unzeroD 1)

open Classical in
/-- The order of `x` at a discrete valuation subring `v` of `F` (junk value `0` when `v` is not a
DVR).
Source: Fulton, *Intersection Theory*, second edition, §1.2. -/
def a2r_vord {F : Type*} [Field F] (v : ValuationSubring F) (x : F) : ℤ :=
  if h : IsDiscreteValuationRing v then haveI := h; a2r_ordZ v F x else 0

/-- The condition that `v` contains the image of `O` and that the maximal ideal of `O` maps into
the maximal ideal of `v`. -/
def a2r_Dominates (O : Type*) [CommRing O] [IsLocalRing O] {F : Type*} [Field F] [Algebra O F]
    (v : ValuationSubring F) : Prop :=
  ∀ a : O, algebraMap O F a ∈ v ∧ (a ∈ maximalIdeal O → v.valuation (algebraMap O F a) < 1)

/-- The proper valuation subrings of `F` dominating the local ring `O`.
Source: Zariski–Samuel, *Commutative Algebra* II, Chapter VI, §2 (centres of valuations). -/
def a2r_Dom (O F : Type*) [CommRing O] [IsLocalRing O] [Field F] [Algebra O F] :
    Set (ValuationSubring F) :=
  {v | v ≠ ⊤ ∧ a2r_Dominates O v}

/-- The ring map from `O` to a valuation subring containing its image. -/
def a2r_domHom {O F : Type*} [CommRing O] [Field F] [Algebra O F] (v : ValuationSubring F)
    (h : ∀ a : O, algebraMap O F a ∈ v) : O →+* v :=
  (algebraMap O F).codRestrict v h

theorem a2r_domHom_isLocalHom {O F : Type*} [CommRing O] [IsLocalRing O] [Field F] [Algebra O F]
    (v : ValuationSubring F) (h : a2r_Dominates O v) :
    IsLocalHom (a2r_domHom v fun a => (h a).1) := by
  constructor
  intro a ha
  by_contra hna
  have h1 := (h a).2 hna
  rw [ValuationSubring.valuation_eq_one_iff] at ha
  exact absurd ha (ne_of_lt h1)

open Classical in
/-- The residue degree `[κ(v) : κ(O)]` of a valuation subring `v` dominating `O` (junk value `0`
otherwise, and `0` when the extension is infinite).
Source: Zariski–Samuel, *Commutative Algebra* II, Chapter VI, §11. -/
def a2r_resDeg (O : Type*) [CommRing O] [IsLocalRing O] {F : Type*} [Field F] [Algebra O F]
    (v : ValuationSubring F) : ℕ :=
  if h : a2r_Dominates O v then
    haveI := a2r_domHom_isLocalHom v h
    letI := (ResidueField.map (a2r_domHom v fun a => (h a).1)).toAlgebra
    Module.finrank (ResidueField O) (ResidueField v)
  else 0

theorem a2r_resDeg_of {O : Type*} [CommRing O] [IsLocalRing O] {F : Type*} [Field F]
    [Algebra O F] (v : ValuationSubring F) (h : a2r_Dominates O v) :
    a2r_resDeg O v = (haveI := a2r_domHom_isLocalHom v h
      letI := (ResidueField.map (a2r_domHom v fun a => (h a).1)).toAlgebra
      Module.finrank (ResidueField O) (ResidueField v)) :=
  dite_eq_left h

/-! ## Elementary facts on valuation subrings -/

/-- For `y ≠ 0`, `v(y) < 1` exactly when `y ∈ v` and `y⁻¹ ∉ v`. -/
theorem a2r_valuation_lt_one_iff {F : Type*} [Field F] (v : ValuationSubring F) {y : F}
    (hy : y ≠ 0) : v.valuation y < 1 ↔ y ∈ v ∧ y⁻¹ ∉ v := by
  rw [← ValuationSubring.valuation_le_one_iff, ← ValuationSubring.valuation_le_one_iff,
    map_inv₀]
  have h0 : v.valuation y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  constructor
  · intro h
    refine ⟨h.le, fun h' => ?_⟩
    exact absurd h (not_lt.mpr ((inv_le_one₀ (pos_iff_ne_zero.mpr h0)).mp h'))
  · rintro ⟨h1, h2⟩
    refine lt_of_le_of_ne h1 fun h => h2 ?_
    rw [h, inv_one]

/-- A valuation subring containing all of `F` is `⊤`. -/
theorem a2r_eq_top_of_forall_mem {F : Type*} [Field F] (v : ValuationSubring F)
    (h : ∀ x : F, x ∈ v) : v = ⊤ :=
  eq_top_iff.mpr fun x _ => h x

/-- Two valuation subrings `u ≤ w` of `F` such that every element of the maximal ideal of `u`
is a non-unit of `w` are equal. -/
theorem a2r_eq_of_le_of_dominates {F : Type*} [Field F] (u w : ValuationSubring F) (hle : u ≤ w)
    (hdom : ∀ x : F, x ≠ 0 → u.valuation x < 1 → w.valuation x < 1) : u = w := by
  refine le_antisymm hle fun x hx => ?_
  by_contra hxu
  have hx0 : x ≠ 0 := by rintro rfl; exact hxu u.zero_mem
  have hinv : x⁻¹ ∈ u := (u.mem_or_inv_mem x).resolve_left hxu
  have hlt : u.valuation x⁻¹ < 1 := by
    rw [a2r_valuation_lt_one_iff u (inv_ne_zero hx0), inv_inv]
    exact ⟨hinv, hxu⟩
  have := hdom x⁻¹ (inv_ne_zero hx0) hlt
  rw [a2r_valuation_lt_one_iff w (inv_ne_zero hx0), inv_inv] at this
  exact this.2 hx

/-! ## Localizations at primes as valuation subrings -/

section loc

variable {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

/-- The localization of `R` at a prime, as a subalgebra of the fraction field `F`. -/
def a2r_locSub (P : Ideal R) [P.IsPrime] : Subalgebra R F :=
  Localization.subalgebra.ofField F P.primeCompl P.primeCompl_le_nonZeroDivisors

instance a2r_locSub_algebra (P : Ideal R) [P.IsPrime] : Algebra R (a2r_locSub (F := F) P) :=
  Subalgebra.algebra _

instance a2r_locSub_isLocalization (P : Ideal R) [P.IsPrime] :
    IsLocalization.AtPrime (a2r_locSub (F := F) P) P :=
  Localization.subalgebra.isLocalization_ofField F P.primeCompl P.primeCompl_le_nonZeroDivisors

instance a2r_locSub_isLocalRing (P : Ideal R) [P.IsPrime] :
    IsLocalRing (a2r_locSub (F := F) P) :=
  IsLocalization.AtPrime.isLocalRing _ P

theorem a2r_mem_locSub (P : Ideal R) [P.IsPrime] {x : F} :
    x ∈ a2r_locSub P ↔ ∃ (a s : R) (_ : s ∈ P.primeCompl),
      x = algebraMap R F a * (algebraMap R F s)⁻¹ := Iff.rfl

/-- The localization at a prime whose localization is a valuation ring, as a valuation subring
of `F`. -/
def a2r_locVal (P : Ideal R) [P.IsPrime] (hP : IsDiscreteValuationRing (a2r_locSub (F := F) P)) :
    ValuationSubring F :=
  have := hP
  valuationSubringOfFractionRing (a2r_locSub (F := F) P) F

theorem a2r_mem_locVal (P : Ideal R) [P.IsPrime]
    (hP : IsDiscreteValuationRing (a2r_locSub (F := F) P)) {x : F} :
    x ∈ a2r_locVal P hP ↔ x ∈ a2r_locSub P := by
  have := hP
  rw [a2r_locVal, mem_valuationSubringOfFractionRing]
  exact ⟨fun ⟨r, hr⟩ => hr ▸ r.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem a2r_algebraMap_mem_locSub (P : Ideal R) [P.IsPrime] (a : R) :
    algebraMap R F a ∈ a2r_locSub P :=
  (a2r_mem_locSub P).mpr ⟨a, 1, P.primeCompl.one_mem, by simp⟩

/-- For `a ≠ 0` in `R`: `a ∈ P` exactly when `a⁻¹` is not in the localization at `P`. -/
theorem a2r_mem_prime_iff (P : Ideal R) [P.IsPrime] {a : R} (ha : a ≠ 0) :
    a ∈ P ↔ (algebraMap R F a)⁻¹ ∉ a2r_locSub P := by
  have ha' : algebraMap R F a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr ha
  constructor
  · intro haP h
    have hu : IsUnit (algebraMap R (a2r_locSub (F := F) P) a) := by
      refine IsUnit.of_mul_eq_one (⟨_, h⟩ : a2r_locSub (F := F) P) (Subtype.ext ?_)
      change algebraMap R F a * (algebraMap R F a)⁻¹ = 1
      rw [mul_inv_cancel₀ ha']
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (a2r_locSub (F := F) P) P a).mp hu haP
  · intro h
    by_contra haP
    have hu := (IsLocalization.AtPrime.isUnit_to_map_iff (a2r_locSub (F := F) P) P a).mpr haP
    apply h
    have h1 : algebraMap _ F (algebraMap R (a2r_locSub (F := F) P) a) *
        algebraMap _ F (↑hu.unit⁻¹ : a2r_locSub (F := F) P) = 1 := by
      rw [← map_mul, IsUnit.mul_val_inv, map_one]
    have h2 := (eq_inv_of_mul_eq_one_right h1).symm
    change (algebraMap R F a)⁻¹ = _ at h2
    rw [h2]
    exact (↑hu.unit⁻¹ : a2r_locSub (F := F) P).2

/-- The prime is recovered from its valuation subring. -/
theorem a2r_locVal_injective {P Q : Ideal R} [P.IsPrime] [Q.IsPrime]
    (hP : IsDiscreteValuationRing (a2r_locSub (F := F) P))
    (hQ : IsDiscreteValuationRing (a2r_locSub (F := F) Q))
    (h : a2r_locVal P hP = a2r_locVal Q hQ) : P = Q := by
  ext a
  by_cases ha : a = 0
  · simp [ha]
  rw [a2r_mem_prime_iff (F := F) P ha, a2r_mem_prime_iff (F := F) Q ha, ← a2r_mem_locVal P hP,
    ← a2r_mem_locVal Q hQ, h]

/-- **Central lemma.** A proper valuation subring of `F` containing `R`, in which every element
outside `P` is a unit, is the localization of `R` at `P`, provided this localization is a DVR.
Source: Atiyah–Macdonald, Proposition 5.18 and Theorem 9.2. -/
theorem a2r_eq_locVal (P : Ideal R) [P.IsPrime]
    (hP : IsDiscreteValuationRing (a2r_locSub (F := F) P)) (v : ValuationSubring F) (hv : v ≠ ⊤)
    (hR : ∀ a, algebraMap R F a ∈ v) (hunit : ∀ s, s ∉ P → (algebraMap R F s)⁻¹ ∈ v) :
    v = a2r_locVal P hP := by
  have := hP
  have hsub : ∀ r : a2r_locSub (F := F) P, algebraMap (a2r_locSub (F := F) P) F r ∈ v := by
    intro r
    obtain ⟨a, s, hs, hr⟩ := (a2r_mem_locSub P).mp r.2
    change r.1 ∈ v
    rw [hr]
    exact mul_mem (hR a) (hunit s hs)
  ext x
  rw [a2r_mem_locVal]
  constructor
  · intro hx
    obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_mem_valuationSubring v hsub hv hx
    rw [← hr]
    exact r.2
  · intro hx
    exact hsub ⟨x, hx⟩

theorem a2r_locVal_ne_top (P : Ideal R) [P.IsPrime] (hP0 : P ≠ ⊥)
    (hP : IsDiscreteValuationRing (a2r_locSub (F := F) P)) : a2r_locVal P hP ≠ ⊤ := by
  intro h
  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have := (a2r_mem_prime_iff (F := F) P ha0).mp haP
  apply this
  rw [← a2r_mem_locVal P hP, h]
  trivial

end loc

/-! ## The integer order -/

section ordZ

variable {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  [Field K] [Algebra R K] [IsFractionRing R K]

theorem a2r_ordFrac_ne_zero {x : K} (hx : x ≠ 0) : Ring.ordFrac R x ≠ 0 := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have ha : a ≠ 0 := by rintro rfl; simp at hx
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  rw [map_div₀, Ring.ordFrac_eq_ord R ha, Ring.ordFrac_eq_ord R hb0]
  exact div_ne_zero (Ring.ordMonoidWithZeroHom_ne_zero (mem_nonZeroDivisors_of_ne_zero ha))
    (Ring.ordMonoidWithZeroHom_ne_zero hb)

theorem a2r_ordFrac_eq (x : K) (hx : x ≠ 0) :
    Ring.ordFrac R x = ((Multiplicative.ofAdd (a2r_ordZ R K x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rw [a2r_ordZ, ofAdd_toAdd, WithZero.unzeroD_eq_unzero (a2r_ordFrac_ne_zero hx),
    WithZero.coe_unzero]

theorem a2r_ordZ_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    a2r_ordZ R K (x * y) = a2r_ordZ R K x + a2r_ordZ R K y := by
  have h := map_mul (Ring.ordFrac R) x y
  rw [a2r_ordFrac_eq x hx, a2r_ordFrac_eq y hy, a2r_ordFrac_eq _ (mul_ne_zero hx hy),
    ← WithZero.coe_mul, ← ofAdd_add] at h
  exact Multiplicative.ofAdd.injective (WithZero.coe_injective h)

theorem a2r_ordZ_one : a2r_ordZ R K 1 = 0 := by
  have h := a2r_ordFrac_eq (R := R) (1 : K) one_ne_zero
  rw [map_one, ← WithZero.coe_one, ← ofAdd_zero] at h
  exact (Multiplicative.ofAdd.injective (WithZero.coe_injective h)).symm

theorem a2r_ordZ_inv {x : K} (hx : x ≠ 0) : a2r_ordZ R K x⁻¹ = - a2r_ordZ R K x := by
  have h := a2r_ordZ_mul (R := R) hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, a2r_ordZ_one] at h
  omega

theorem a2r_ordZ_div {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    a2r_ordZ R K (x / y) = a2r_ordZ R K x - a2r_ordZ R K y := by
  rw [div_eq_mul_inv, a2r_ordZ_mul hx (inv_ne_zero hy), a2r_ordZ_inv hy, sub_eq_add_neg]

theorem a2r_ordZ_zero : a2r_ordZ R K 0 = 0 := by
  simp [a2r_ordZ, WithZero.unzeroD]

theorem a2r_ordZ_algebraMap {a : R} (ha : a ≠ 0) :
    a2r_ordZ R K (algebraMap R K a) = ((Ring.ord R a).toNat : ℤ) := by
  have hnzd : a ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero ha
  have h := a2r_ordFrac_eq (R := R) (algebraMap R K a)
    ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha)
  rw [Ring.ordFrac_eq_ord R ha,
    Ring.ordMonoidWithZeroHom_eq_coe R hnzd (ENat.natCast_toNat (Ring.ord_ne_top hnzd)).symm] at h
  exact (Multiplicative.ofAdd.injective (WithZero.coe_injective h)).symm

end ordZ

/-- The integer order depends only on the image of the ring in its fraction field.
Source: Stacks Project, Tag 02MD. -/
theorem a2r_ordZ_eq_of_range_eq {R S K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [CommRing S] [IsDomain S] [IsNoetherianRing S] [Ring.KrullDimLE 1 S]
    [Field K] [Algebra R K] [IsFractionRing R K] [Algebra S K] [IsFractionRing S K]
    (h : ∀ x, (∃ r, algebraMap R K r = x) ↔ ∃ s, algebraMap S K s = x) (x : K) :
    a2r_ordZ R K x = a2r_ordZ S K x := by
  by_cases hx : x = 0
  · rw [hx, a2r_ordZ_zero, a2r_ordZ_zero]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have ha : a ≠ 0 := by rintro rfl; simp at hx
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨a', ha'⟩ := (h (algebraMap R K a)).mp ⟨a, rfl⟩
  obtain ⟨b', hb'⟩ := (h (algebraMap R K b)).mp ⟨b, rfl⟩
  have hinjR := IsFractionRing.injective R K
  have hinjS := IsFractionRing.injective S K
  have ha'0 : a' ≠ 0 := by
    rintro rfl; rw [map_zero] at ha'; exact ha (hinjR (by rw [← ha', map_zero]))
  have hb'0 : b' ≠ 0 := by
    rintro rfl; rw [map_zero] at hb'; exact hb0 (hinjR (by rw [← hb', map_zero]))
  have hA := (map_ne_zero_iff _ hinjR).mpr ha
  have hB := (map_ne_zero_iff _ hinjR).mpr hb0
  rw [a2r_ordZ_div hA hB, a2r_ordZ_div hA hB, a2r_ordZ_algebraMap ha, a2r_ordZ_algebraMap hb0,
    ← ha', ← hb', a2r_ordZ_algebraMap ha'0, a2r_ordZ_algebraMap hb'0,
    ord_eq_of_range_eq (algebraMap R K) (algebraMap S K) hinjR hinjS h ha'.symm,
    ord_eq_of_range_eq (algebraMap R K) (algebraMap S K) hinjR hinjS h hb'.symm]

/-- A ring isomorphic to a DVR is a DVR. -/
theorem a2r_isDVR_of_ringEquiv {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing R] (e : R ≃+* S) : IsDiscreteValuationRing S := by
  have : IsLocalRing S := IsLocalRing.of_surjective' e.toRingHom e.surjective
  have : IsPrincipalIdealRing S := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  refine { not_a_field' := ?_ }
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (IsDiscreteValuationRing.not_a_field R)
  intro h
  have : e r ∈ maximalIdeal S := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply (mem_maximalIdeal r).mp hr
    simpa using hu.map e.symm.toRingHom
  rw [h, Submodule.mem_bot, map_eq_zero_iff e e.injective] at this
  exact hr0 this

/-- **Image transport.** If an injective ring map `j : A → F` from a DVR `A` with fraction field
`F` has image `v`, the order at `v` is the order on `A`. -/
theorem a2r_vord_eq_of_range {F A : Type*} [Field F] [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Algebra A F] [IsFractionRing A F] (v : ValuationSubring F)
    (hv : ∀ x, x ∈ v ↔ ∃ a, algebraMap A F a = x) (x : F) :
    a2r_vord v x = a2r_ordZ A F x := by
  let j : A →+* v := (algebraMap A F).codRestrict v fun a => (hv _).mpr ⟨a, rfl⟩
  have hj : Function.Bijective j := by
    refine ⟨fun a b hab => IsFractionRing.injective A F (congrArg Subtype.val hab), fun y => ?_⟩
    obtain ⟨a, ha⟩ := (hv y).mp y.2
    exact ⟨a, Subtype.ext ha⟩
  have hdvr : IsDiscreteValuationRing v := a2r_isDVR_of_ringEquiv (RingEquiv.ofBijective j hj)
  rw [a2r_vord, dite_eq_left hdvr]
  refine (a2r_ordZ_eq_of_range_eq (fun y => ?_) x).symm
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨j a, rfl⟩
  · rintro ⟨w, rfl⟩
    exact (hv _).mp w.2

/-! ## Lengths -/

/-- Length along a chain of submodules `A ≤ B ≤ M`. -/
theorem a2r_length_quotient_chain {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (A B : Submodule R M) (h : A ≤ B) :
    Module.length R (M ⧸ A) =
      Module.length R (B ⧸ A.comap B.subtype) + Module.length R (M ⧸ B) := by
  let f : (B ⧸ A.comap B.subtype) →ₗ[R] M ⧸ A :=
    (A.comap B.subtype).mapQ A B.subtype le_rfl
  let g : (M ⧸ A) →ₗ[R] M ⧸ B := A.mapQ B LinearMap.id h
  refine Module.length_eq_add_of_exact f g ?_ ?_ ?_
  · rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ]
    ext x
    simp
  · intro y
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective B y
    exact ⟨Submodule.mkQ A m, rfl⟩
  · intro y
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective A y
    constructor
    · intro hm
      have hmB : m ∈ B := by
        simpa [g, Submodule.Quotient.mk_eq_zero] using hm
      exact ⟨Submodule.mkQ _ ⟨m, hmB⟩, rfl⟩
    · rintro ⟨z, hz⟩
      obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ z
      rw [← hz]
      simp [f, g, Submodule.Quotient.mk_eq_zero]

/-- A finitely generated module annihilated by a non-zero-divisor of a one-dimensional Noetherian
ring has finite length. -/
theorem a2r_isFiniteLength_of_smul_eq_zero {R Q : Type*} [CommRing R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [AddCommGroup Q] [Module R Q] [Module.Finite R Q] {c : R}
    (hc : c ∈ nonZeroDivisors R) (hQ : ∀ q : Q, c • q = 0) : IsFiniteLength R Q := by
  have hM : Module.IsTorsionBySet R Q (Ideal.span {c} : Set R) := by
    intro q ⟨r, hr⟩
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    change (d * c) • q = 0
    rw [mul_smul, hQ, smul_zero]
  let := hM.module
  have : IsScalarTower R (R ⧸ Ideal.span {c}) Q := hM.isScalarTower
  have hfl := isFiniteLength_quotient_span_singleton R hc
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl
  have : IsArtinian R (R ⧸ Ideal.span {c}) := hfl.2
  have : IsArtinianRing (R ⧸ Ideal.span {c}) := isArtinian_of_tower R hfl.2
  have : Module.Finite (R ⧸ Ideal.span {c}) Q := Module.Finite.of_restrictScalars_finite R _ _
  have : IsArtinian (R ⧸ Ideal.span {c}) Q := inferInstance
  have : IsArtinian R Q :=
    isArtinian_of_surjective_algebraMap (R := R ⧸ Ideal.span {c}) (S := R)
      Ideal.Quotient.mk_surjective
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨inferInstance, this⟩

/-- **Step A of the normalization formula.** If `B ⊇ O` is a finite extension of domains whose
conductor contains a non-zero-divisor `c`, then `ℓ_O(O/a) = ℓ_O(B/aB)` for every `a ≠ 0`.
Source: Fulton, *Intersection Theory*, second edition, Lemma A.2. -/
theorem a2r_length_quot_eq {O B : Type*} [CommRing O] [IsDomain O] [IsNoetherianRing O]
    [Ring.KrullDimLE 1 O] [CommRing B] [IsDomain B] [Algebra O B] [Module.Finite O B]
    (hinj : Function.Injective (algebraMap O B)) {c : O} (hc : c ≠ 0)
    (hcB : ∀ x : B, ∃ r : O, c • x = algebraMap O B r) {a : O} (ha : a ≠ 0) :
    Module.length O (O ⧸ Ideal.span {a}) =
      Module.length O (B ⧸ (Ideal.span {algebraMap O B a}).restrictScalars O) := by
  set a' := algebraMap O B a with ha'def
  have ha' : a' ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha
  let N : Submodule O B := LinearMap.range (Algebra.linearMap O B)
  let μ : B →ₗ[O] B := LinearMap.mulLeft O a'
  let A1 : Submodule O B := N.map μ
  let Bs : Submodule O B := LinearMap.range μ
  have hA1N : A1 ≤ N := by
    rintro _ ⟨_, ⟨r, rfl⟩, rfl⟩
    refine ⟨a * r, ?_⟩
    simp [μ, a', map_mul]
  have hA1B : A1 ≤ Bs := LinearMap.map_le_range
  have h1 := a2r_length_quotient_chain A1 N hA1N
  have h2 := a2r_length_quotient_chain A1 Bs hA1B
  -- `N / A1 ≅ O / aO`
  let eN : O ≃ₗ[O] N := LinearEquiv.ofInjective (Algebra.linearMap O B) hinj
  have hmap1 : (A1.comap N.subtype).map eN.symm.toLinearMap = Ideal.span {a} := by
    ext r
    constructor
    · rintro ⟨n, hn, rfl⟩
      obtain ⟨_, ⟨s, rfl⟩, hs⟩ := hn
      have : eN.symm n = a * s := by
        apply eN.injective
        rw [LinearEquiv.apply_symm_apply]
        apply Subtype.ext
        have hs' : (n : B) = μ (Algebra.linearMap O B s) := hs.symm
        rw [hs']
        change _ = algebraMap O B (a * s)
        simp [μ, a', map_mul]
      rw [LinearEquiv.coe_coe, this]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)
    · intro hr
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      refine ⟨eN (s * a), ?_, by simp⟩
      refine ⟨algebraMap O B s, ⟨s, rfl⟩, ?_⟩
      change _ = algebraMap O B (s * a)
      simp [μ, a', map_mul, mul_comm]
  let e1 : (N ⧸ A1.comap N.subtype) ≃ₗ[O] O ⧸ Ideal.span {a} :=
    Submodule.Quotient.equiv _ _ eN.symm hmap1
  -- `B / N ≅ Bs / A1`
  have hμinj : Function.Injective μ := fun x y hxy => mul_left_cancel₀ ha' hxy
  let eμ : B ≃ₗ[O] Bs := LinearEquiv.ofInjective μ hμinj
  have hmap2 : N.map eμ.toLinearMap = A1.comap Bs.subtype := by
    ext ⟨x, hx⟩
    constructor
    · rintro ⟨n, hn, hnx⟩
      have : μ n = x := congrArg Subtype.val hnx
      change x ∈ A1
      rw [← this]
      exact ⟨n, hn, rfl⟩
    · intro hxA
      obtain ⟨n, hn, hnx⟩ := hxA
      exact ⟨n, hn, Subtype.ext hnx⟩
  let e2 : (B ⧸ N) ≃ₗ[O] Bs ⧸ A1.comap Bs.subtype := Submodule.Quotient.equiv _ _ eμ hmap2
  -- finiteness of `B / N`
  have hfin : Module.length O (B ⧸ N) ≠ ⊤ := by
    rw [Module.length_ne_top_iff]
    refine a2r_isFiniteLength_of_smul_eq_zero (mem_nonZeroDivisors_of_ne_zero hc) fun q => ?_
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N q
    obtain ⟨r, hr⟩ := hcB x
    rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hr]
    exact ⟨r, rfl⟩
  have hBs : Bs = (Ideal.span {a'}).restrictScalars O := by
    ext x
    simp only [Bs, LinearMap.mem_range, Submodule.restrictScalars_mem,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨y, mul_comm _ _⟩
    · rintro ⟨y, rfl⟩; exact ⟨y, mul_comm _ _⟩
  have key : Module.length O (O ⧸ Ideal.span {a}) + Module.length O (B ⧸ N) =
      Module.length O (B ⧸ Bs) + Module.length O (B ⧸ N) := by
    rw [← e1.length_eq, ← h1, h2, ← e2.length_eq, add_comm]
  rw [← hBs]
  exact WithTop.add_right_cancel hfin key

open UniqueFactorizationMonoid in
/-- In a Dedekind domain, the multiplicity of a maximal ideal `P` in `(s)` is the length-based
order of `s` in the localization at `P`.
Source: Neukirch, *Algebraic Number Theory*, I, Proposition 11.5; Stacks Project, Tag 02MD. -/
theorem a2r_ord_localization_eq_count {S : Type*} [CommRing S] [IsDedekindDomain S] (P : Ideal S)
    [P.IsMaximal] (hP : P ≠ ⊥) (Sₚ : Type*) [CommRing Sₚ] [IsDomain Sₚ] [Algebra S Sₚ]
    [IsLocalization.AtPrime Sₚ P] [IsLocalRing Sₚ] {s : S} (hs : s ≠ 0) :
    Ring.ord Sₚ (algebraMap S Sₚ s) =
      (Multiset.count P (normalizedFactors (Ideal.span {s})) : ℕ∞) := by
  have hI : Ideal.span {s} ≠ ⊥ := by simpa using hs
  obtain ⟨I, hPI, h⟩ := Ideal.eq_prime_pow_mul_coprime hI P
  have hIP : ¬ I ≤ P := by
    intro hle
    rw [sup_of_le_left hle] at hPI
    exact (Ideal.IsMaximal.ne_top inferInstance) hPI
  have hSₚ := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hP Sₚ
  apply_fun Ideal.map (algebraMap S Sₚ) at h
  rw [Ideal.map_mul, Ideal.map_pow, IsLocalization.AtPrime.map_eq_top_of_not_le Sₚ hIP,
    Ideal.mul_top, IsLocalization.AtPrime.map_eq_maximalIdeal P Sₚ, Ideal.map_span,
    Set.image_singleton] at h
  rw [Ring.ord, h, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

/-- If every maximal ideal of `S` contains the image of the maximal ideal of `O`, the structure
map to a localization of `S` at a maximal ideal is local. -/
theorem a2r_isLocalHom_localization {O S : Type*} [CommRing O] [IsLocalRing O] [CommRing S]
    [Algebra O S] (P : Ideal S) [P.IsMaximal] (hmax : ∀ a ∈ maximalIdeal O, algebraMap O S a ∈ P) :
    IsLocalHom (algebraMap O (Localization.AtPrime P)) := by
  constructor
  intro a ha
  by_contra hna
  rw [IsScalarTower.algebraMap_apply O S (Localization.AtPrime P)] at ha
  exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P _).mp ha
    (hmax a hna)

/-- `ℓ_O(S / P^n) = n · [κ(P) : κ(O)]` for a maximal ideal `P ≠ 0` of a Dedekind domain. -/
theorem a2r_length_quot_pow {O S : Type*} [CommRing O] [IsLocalRing O] [CommRing S]
    [IsDedekindDomain S] [Algebra O S] (P : Ideal S) [P.IsMaximal] (hP : P ≠ ⊥)
    [IsLocalHom (algebraMap O (Localization.AtPrime P))] (n : ℕ) :
    Module.length O (S ⧸ P ^ n) =
      n * Module.length (ResidueField O) (ResidueField (Localization.AtPrime P)) := by
  have hdvr := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hP
    (Localization.AtPrime P)
  let e := IsLocalization.AtPrime.equivQuotMaximalIdealPow P (Localization.AtPrime P) n
  rw [(e.toLinearEquiv.restrictScalars O).length_eq,
    IsLocalRing.length_restrictScalars O (Localization.AtPrime P),
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

open Classical in
/-- The length `ℓ_{κ(O)}(κ(S_P))` of the residue field of `S_P` over that of `O`, for a prime `P`
of an `O`-algebra `S` with local structure map (junk value `0` otherwise). -/
def a2r_locLen (O : Type*) [CommRing O] [IsLocalRing O] {S : Type*} [CommRing S] [Algebra O S]
    (P : Ideal S) : ℕ∞ :=
  if h : P.IsPrime then
    haveI := h
    if h2 : IsLocalHom (algebraMap O (Localization.AtPrime P)) then
      haveI := h2
      Module.length (ResidueField O) (ResidueField (Localization.AtPrime P))
    else 0
  else 0

theorem a2r_locLen_of {O : Type*} [CommRing O] [IsLocalRing O] {S : Type*} [CommRing S]
    [Algebra O S] (P : Ideal S) [P.IsPrime] [IsLocalHom (algebraMap O (Localization.AtPrime P))] :
    a2r_locLen O P = Module.length (ResidueField O) (ResidueField (Localization.AtPrime P)) := by
  rw [a2r_locLen, dite_eq_left ‹_›, dite_eq_left ‹_›]

open UniqueFactorizationMonoid in
/-- **Step B of the normalization formula.** For a nonzero ideal `I` of a Dedekind domain `S`
over a local ring `O`, all of whose maximal ideals lie over the maximal ideal of `O`:
`ℓ_O(S/I) = ∑_P v_P(I) [κ(P) : κ(O)]`.
Source: Fulton, *Intersection Theory*, second edition, Lemma A.3 and Example A.3.1. -/
theorem a2r_length_quot_dedekind {O S : Type*} [CommRing O] [IsLocalRing O] [CommRing S]
    [IsDedekindDomain S] [Algebra O S]
    (hmax : ∀ P : Ideal S, P.IsMaximal → ∀ a ∈ maximalIdeal O, algebraMap O S a ∈ P)
    {I : Ideal S} (hI : I ≠ ⊥) :
    Module.length O (S ⧸ I) = ∑ P ∈ (normalizedFactors I).toFinset,
      (Multiset.count P (normalizedFactors I) : ℕ∞) * a2r_locLen O P := by
  rw [← factors_eq_normalizedFactors]
  let e₀ := IsDedekindDomain.quotientEquivPiFactors hI
  let e : (S ⧸ I) ≃ₗ[O] ((P : (factors I).toFinset) →
      S ⧸ (P : Ideal S) ^ Multiset.count (P : Ideal S) (factors I)) :=
    { e₀ with
      map_smul' := by
        intro r y
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
        rw [RingHom.id_apply]
        change e₀ (r • Ideal.Quotient.mk I x) = r • e₀ (Ideal.Quotient.mk I x)
        rw [show (r • Ideal.Quotient.mk I x : S ⧸ I) = Ideal.Quotient.mk I (algebraMap O S r * x)
          by rw [Algebra.smul_def, map_mul]; rfl]
        rw [IsDedekindDomain.quotientEquivPiFactors_mk,
          IsDedekindDomain.quotientEquivPiFactors_mk]
        ext P
        simp [Algebra.smul_def] }
  rw [e.length_eq, Module.length_pi_of_fintype]
  rw [← Finset.sum_coe_sort (factors I).toFinset]
  refine Finset.sum_congr rfl fun P _ => ?_
  have hPprime : Prime (P : Ideal S) := prime_of_factor _ (Multiset.mem_toFinset.mp P.2)
  have hP0 : (P : Ideal S) ≠ ⊥ := hPprime.ne_zero
  have : (P : Ideal S).IsPrime := Ideal.isPrime_of_prime hPprime
  have : (P : Ideal S).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  have := a2r_isLocalHom_localization (P : Ideal S) (hmax _ inferInstance)
  rw [a2r_length_quot_pow (P : Ideal S) hP0, a2r_locLen_of]

/-! ## Valuations dominating a local ring and the maximal ideals of its integral closure -/

section correspondence

variable {O S F : Type*} [CommRing O] [IsLocalRing O] [Field F] [Algebra O F]
  [CommRing S] [Algebra O S] [Algebra S F] [IsScalarTower O S F]
  [IsFractionRing S F]

/-- The localization of `S` at a maximal ideal lying over the maximal ideal of `O` dominates
`O`. -/
theorem a2r_locVal_mem_Dom [IsDomain S] (P : Ideal S) [P.IsPrime] (hP0 : P ≠ ⊥)
    (hP : IsDiscreteValuationRing (a2r_locSub (F := F) P))
    (hmax : ∀ a ∈ maximalIdeal O, algebraMap O S a ∈ P) :
    a2r_locVal P hP ∈ a2r_Dom O F := by
  refine ⟨a2r_locVal_ne_top P hP0 hP, fun a => ⟨?_, fun ha => ?_⟩⟩
  · rw [IsScalarTower.algebraMap_apply O S F, a2r_mem_locVal]
    exact a2r_algebraMap_mem_locSub P _
  · rw [IsScalarTower.algebraMap_apply O S F]
    by_cases h0 : algebraMap O S a = 0
    · rw [h0, map_zero, map_zero]; exact zero_lt_one
    have h0' : algebraMap S F (algebraMap O S a) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective S F)).mpr h0
    rw [a2r_valuation_lt_one_iff _ h0', a2r_mem_locVal, a2r_mem_locVal]
    exact ⟨a2r_algebraMap_mem_locSub P _, (a2r_mem_prime_iff P h0).mp (hmax a ha)⟩

/-- Every proper valuation subring of `F` dominating `O` is the localization of the integral
closure `S` at a maximal ideal.
Source: Atiyah–Macdonald, Proposition 5.18, Corollary 5.22 and Theorem 9.2. -/
theorem a2r_exists_locVal_of_mem_Dom [IsDedekindDomain S] [Algebra.IsIntegral O S]
    (hO : maximalIdeal O ≠ ⊥) (hinj : Function.Injective (algebraMap O S))
    (v : ValuationSubring F) (hv : v ∈ a2r_Dom O F) :
    ∃ (P : Ideal S) (_ : P.IsMaximal) (_ : P ≠ ⊥)
      (hP : IsDiscreteValuationRing (a2r_locSub (F := F) P)), v = a2r_locVal P hP := by
  obtain ⟨hvtop, hdom⟩ := hv
  have hS : ∀ s : S, algebraMap S F s ∈ v := by
    intro s
    have hint : IsIntegral O (algebraMap S F s) :=
      (Algebra.IsIntegral.isIntegral (R := O) s).map (IsScalarTower.toAlgHom O S F)
    let j : O →+* v := a2r_domHom v fun a => (hdom a).1
    let := j.toAlgebra
    have : IsScalarTower O v F := .of_algebraMap_eq fun a => rfl
    obtain ⟨w, hw⟩ := (IsIntegrallyClosed.isIntegral_iff (R := v) (K := F)).mp
      (hint.tower_top (A := v))
    rw [← hw]
    exact w.2
  let ι : S →+* v := (algebraMap S F).codRestrict v hS
  let P : Ideal S := (maximalIdeal v).comap ι
  have hPprime : P.IsPrime := Ideal.comap_isPrime ι (maximalIdeal v)
  have hmO : ∀ a ∈ maximalIdeal O, algebraMap O S a ∈ P := by
    intro a ha
    change ι (algebraMap O S a) ∈ maximalIdeal v
    rw [ValuationSubring.valuation_lt_one_iff]
    change v.valuation (algebraMap S F (algebraMap O S a)) < 1
    rw [← IsScalarTower.algebraMap_apply]
    exact (hdom a).2 ha
  have hPmax : P.IsMaximal := by
    have hunder : maximalIdeal O = P.under O :=
      (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (Ideal.IsPrime.ne_top
        (Ideal.IsPrime.under O P)) (fun a ha => hmO a ha)
    exact Ideal.IsIntegral.isMaximal_of_isMaximal_under (R := O) P
      (hunder ▸ IsLocalRing.maximalIdeal.isMaximal O)
  obtain ⟨a, haO, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hO
  have hP0 : P ≠ ⊥ := by
    intro h
    have := hmO a haO
    rw [h, Ideal.mem_bot, map_eq_zero_iff _ hinj] at this
    exact ha0 this
  have hP := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hP0
    (a2r_locSub (F := F) P)
  refine ⟨P, hPmax, hP0, hP, a2r_eq_locVal P hP v hvtop hS fun s hs => ?_⟩
  have hu : IsUnit (ι s) := by
    by_contra hn
    exact hs ((IsLocalRing.mem_maximalIdeal _).mpr hn)
  have h1 : (ι s : F) * ((hu.unit⁻¹ : vˣ) : v) = 1 := by
    rw [← v.coe_mul, IsUnit.mul_val_inv, v.coe_one]
  rw [show (algebraMap S F s)⁻¹ = ((hu.unit⁻¹ : vˣ) : v) from
    (eq_inv_of_mul_eq_one_right h1).symm]
  exact (hu.unit⁻¹ : vˣ).1.2

end correspondence

/-! ## Transport of orders and residue degrees -/

/-- A ring isomorphism compatible with the maps from `O` identifies the residue lengths. -/
theorem a2r_length_residue_eq {O A B : Type*} [CommRing O] [IsLocalRing O] [CommRing A]
    [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra O A] [IsLocalHom (algebraMap O A)]
    (f : O →+* B) [IsLocalHom f] (e : A ≃+* B) (he : ∀ a, e (algebraMap O A a) = f a) :
    Module.length (ResidueField O) (ResidueField A) =
      (letI := (ResidueField.map f).toAlgebra
       Module.length (ResidueField O) (ResidueField B)) := by
  let := (ResidueField.map f).toAlgebra
  let E := ResidueField.mapEquiv e
  let L : ResidueField A ≃ₗ[ResidueField O] ResidueField B :=
    { E with
      map_smul' := by
        intro c y
        obtain ⟨c0, rfl⟩ := IsLocalRing.residue_surjective c
        rw [Algebra.smul_def, Algebra.smul_def, RingHom.id_apply]
        change E (algebraMap (ResidueField O) (ResidueField A) (residue O c0) * y) =
          ResidueField.map f (residue O c0) * E y
        rw [map_mul, IsLocalRing.ResidueField.algebraMap_residue]
        congr 1
        simp only [E, ResidueField.mapEquiv_apply, ResidueField.map_residue]
        congr 1
        exact he c0 }
  exact L.length_eq

theorem a2r_toNat_length_eq_finrank (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
    (Module.length K V).toNat = Module.finrank K V := by
  rw [Module.length_eq_rank, Cardinal.toNat_toENat]
  rfl

section transport

variable {O S F : Type*} [CommRing O] [IsLocalRing O] [Field F] [Algebra O F]
  [CommRing S] [IsDedekindDomain S] [Algebra O S] [Algebra S F] [IsScalarTower O S F]
  [IsFractionRing S F]

open UniqueFactorizationMonoid in
/-- The order at `a2r_locVal P` of an element of `S` is its multiplicity at `P`. -/
theorem a2r_vord_locVal_algebraMap (P : Ideal S) [P.IsMaximal] (hP0 : P ≠ ⊥)
    (hP : IsDiscreteValuationRing (a2r_locSub (F := F) P)) {s : S} (hs : s ≠ 0) :
    a2r_vord (a2r_locVal P hP) (algebraMap S F s) =
      (Multiset.count P (normalizedFactors (Ideal.span {s})) : ℤ) := by
  have := hP
  rw [a2r_vord_eq_of_range (A := a2r_locSub (F := F) P) _ (fun x => by
    rw [a2r_mem_locVal]
    exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, fun ⟨r, hr⟩ => hr ▸ r.2⟩)]
  have hs' : algebraMap S (a2r_locSub (F := F) P) s ≠ 0 := by
    intro h
    apply hs
    apply IsFractionRing.injective S F
    rw [map_zero]
    exact congrArg Subtype.val h
  rw [show algebraMap S F s = algebraMap (a2r_locSub (F := F) P) F
      (algebraMap S (a2r_locSub (F := F) P) s) from rfl, a2r_ordZ_algebraMap hs',
    a2r_ord_localization_eq_count P hP0 (a2r_locSub (F := F) P) hs, ENat.toNat_natCast]

/-- The residue degree of `a2r_locVal P` over `O` is the residue length at `P`. -/
theorem a2r_resDeg_locVal (P : Ideal S) [P.IsMaximal] (hP0 : P ≠ ⊥)
    (hP : IsDiscreteValuationRing (a2r_locSub (F := F) P))
    (hmax : ∀ a ∈ maximalIdeal O, algebraMap O S a ∈ P) :
    a2r_resDeg O (a2r_locVal P hP) = (a2r_locLen O P).toNat := by
  have hdom := (a2r_locVal_mem_Dom P hP0 hP hmax).2
  have := a2r_isLocalHom_localization P hmax
  have := a2r_domHom_isLocalHom _ hdom
  rw [a2r_resDeg_of _ hdom, a2r_locLen_of, ← a2r_toNat_length_eq_finrank]
  let e1 : Localization.AtPrime P ≃+* a2r_locSub (F := F) P :=
    (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P)
      (a2r_locSub (F := F) P)).toRingEquiv
  let j : a2r_locSub (F := F) P →+* a2r_locVal P hP :=
    (algebraMap (a2r_locSub (F := F) P) F).codRestrict _ fun r => by
      rw [a2r_mem_locVal]; exact r.2
  have hj : Function.Bijective j := by
    refine ⟨fun a b hab => ?_, fun y => ?_⟩
    · have h := congrArg Subtype.val hab
      exact Subtype.ext h
    · exact ⟨⟨y, (a2r_mem_locVal P hP).mp y.2⟩, rfl⟩
  have hE : ∀ a, (e1.trans (RingEquiv.ofBijective j hj)) (algebraMap O (Localization.AtPrime P) a)
      = a2r_domHom (a2r_locVal P hP) (fun a => (hdom a).1) a := by
    intro a
    apply Subtype.ext
    have h1 : algebraMap O (Localization.AtPrime P) a =
        algebraMap S (Localization.AtPrime P) (algebraMap O S a) :=
      IsScalarTower.algebraMap_apply O S _ a
    have h2 : e1 (algebraMap S (Localization.AtPrime P) (algebraMap O S a)) =
        algebraMap S (a2r_locSub (F := F) P) (algebraMap O S a) :=
      AlgEquiv.commutes _ _
    change ((e1 (algebraMap O (Localization.AtPrime P) a) : a2r_locSub (F := F) P) : F) =
      algebraMap O F a
    rw [h1, h2, IsScalarTower.algebraMap_apply O S F]
    rfl
  exact congrArg ENat.toNat (a2r_length_residue_eq _ _ hE).symm

/-- A ring isomorphism of algebras over a field compatible with the structure maps preserves
`finrank`. -/
theorem a2r_finrank_eq_of_ringEquiv' {k A B : Type*} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (e : A ≃+* B) (he : ∀ c, e (algebraMap k A c) = algebraMap k B c) :
    Module.finrank k A = Module.finrank k B :=
  (AlgEquiv.ofRingEquiv (f := e) he).toLinearEquiv.finrank_eq

/-- The residue length at a maximal ideal `P` lying over the maximal ideal of `O` is the inertia
degree. -/
theorem a2r_locLen_toNat_eq_inertiaDeg {O S : Type*} [CommRing O] [IsLocalRing O] [CommRing S]
    [Algebra O S] (P : Ideal S) [P.IsMaximal] [P.LiesOver (maximalIdeal O)]
    [IsLocalHom (algebraMap O (Localization.AtPrime P))] :
    (a2r_locLen O P).toNat = P.inertiaDeg O := by
  rw [a2r_locLen_of, a2r_toNat_length_eq_finrank,
    Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal O) P]
  let e : (S ⧸ P) ≃+* ResidueField (Localization.AtPrime P) :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P)).toRingEquiv
  have he : ∀ c : O ⧸ maximalIdeal O, e (algebraMap (O ⧸ maximalIdeal O) (S ⧸ P) c) =
      algebraMap (ResidueField O) (ResidueField (Localization.AtPrime P)) c := by
    intro c
    obtain ⟨c0, rfl⟩ := Ideal.Quotient.mk_surjective c
    change e (Ideal.Quotient.mk P (algebraMap O S c0)) =
      algebraMap (ResidueField O) (ResidueField (Localization.AtPrime P)) (residue O c0)
    rw [ResidueField.algebraMap_residue,
      IsScalarTower.algebraMap_apply O S (Localization.AtPrime P)]
    exact (IsLocalization.AtPrime.equivQuotMaximalIdeal P
      (Localization.AtPrime P)).commutes (algebraMap O S c0)
  have h1 := @a2r_finrank_eq_of_ringEquiv' (O ⧸ maximalIdeal O) (S ⧸ P)
    (ResidueField (Localization.AtPrime P)) (inferInstance : Field (ResidueField O)) _ _
    (inferInstance : Algebra (O ⧸ maximalIdeal O) (S ⧸ P))
    (inferInstance : Algebra (ResidueField O) (ResidueField (Localization.AtPrime P))) e he
  exact h1.symm

end transport

/-! ## The normalization formula -/

section normalization

open Classical in
/-- `a2r_locVal` as a total function of the ideal (junk value `⊤`). -/
def a2r_locV {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
    (P : Ideal R) : ValuationSubring F :=
  if h : P.IsPrime then
    haveI := h
    if h2 : IsDiscreteValuationRing (a2r_locSub (F := F) P) then a2r_locVal P h2 else ⊤
  else ⊤

theorem a2r_locV_eq {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] (P : Ideal R) [P.IsPrime]
    (hP : IsDiscreteValuationRing (a2r_locSub (F := F) P)) : a2r_locV P = a2r_locVal P hP := by
  rw [a2r_locV, dite_eq_left ‹_›, dite_eq_left hP]

/-- A finite extension of a domain inside its fraction field has a nonzero conductor element. -/
theorem a2r_exists_conductor {O S F : Type*} [CommRing O] [IsDomain O] [Field F] [Algebra O F]
    [IsFractionRing O F] [CommRing S] [Algebra O S] [Algebra S F] [IsScalarTower O S F]
    [Module.Finite O S] (hSF : Function.Injective (algebraMap S F)) :
    ∃ c : O, c ≠ 0 ∧ ∀ x : S, ∃ r : O, c • x = algebraMap O S r := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := S)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O)
    (s.image (algebraMap S F))
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, fun x => ?_⟩
  have hx : x ∈ Submodule.span O (s : Set S) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, hr⟩ := hb (algebraMap S F y) (Finset.mem_image_of_mem _ hy)
    refine ⟨r, hSF ?_⟩
    rw [← IsScalarTower.algebraMap_apply, hr, Algebra.smul_def, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply]
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨r, hr⟩ := hy
    obtain ⟨t, ht⟩ := hz
    exact ⟨r + t, by rw [smul_add, hr, ht, map_add]⟩
  | smul a y _ hy =>
    obtain ⟨r, hr⟩ := hy
    exact ⟨a * r, by rw [smul_comm, hr, Algebra.smul_def, map_mul]⟩

variable (O F : Type*) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O]
  [Ring.KrullDimLE 1 O] [Field F] [Algebra O F] [IsFractionRing O F]

omit [IsLocalRing O] [IsNoetherianRing O] [Ring.KrullDimLE 1 O] in
theorem a2r_isFractionRing_integralClosure : IsFractionRing (integralClosure O F) F :=
  integralClosure.isFractionRing_of_finite_extension F F

omit [IsLocalRing O] in
theorem a2r_isDedekindDomain_integralClosure [Module.Finite O (integralClosure O F)] :
    IsDedekindDomain (integralClosure O F) := by
  have : IsFractionRing (integralClosure O F) F := a2r_isFractionRing_integralClosure O F
  have : IsIntegrallyClosed (integralClosure O F) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension F (L := F)
  have : IsNoetherianRing (integralClosure O F) := isNoetherian_of_tower O inferInstance
  have : Ring.DimensionLEOne O := ⟨fun hne hp => hp.isMaximal_of_ne_bot hne⟩
  have : Ring.DimensionLEOne (integralClosure O F) := inferInstance
  exact { }

open UniqueFactorizationMonoid in
/-- **The normalization formula.** For a one-dimensional Noetherian local domain `O` with fraction
field `F` and finite normalization, the proper valuation subrings of `F` dominating `O` form a
finite set of DVRs, and `ord_O(x) = ∑_v v(x) [κ(v) : κ(O)]`.
Source: Fulton, *Intersection Theory*, second edition, Example A.3.1 and Lemma A.3. -/
theorem a2r_ordZ_eq_finsum [Module.Finite O (integralClosure O F)] (hO : maximalIdeal O ≠ ⊥) :
    (a2r_Dom O F).Finite ∧ ∀ x : F, x ≠ 0 →
      a2r_ordZ O F x = ∑ᶠ v ∈ a2r_Dom O F, a2r_vord v x * a2r_resDeg O v := by
  classical
  let S := integralClosure O F
  have : IsFractionRing S F := a2r_isFractionRing_integralClosure O F
  have : IsDedekindDomain S := a2r_isDedekindDomain_integralClosure O F
  have hOF : Function.Injective (algebraMap O F) := IsFractionRing.injective O F
  have hinj : Function.Injective (algebraMap O S) := by
    intro a b hab
    apply hOF
    rw [IsScalarTower.algebraMap_apply O S F, hab, ← IsScalarTower.algebraMap_apply]
  have hmax : ∀ P : Ideal S, P.IsMaximal → ∀ a ∈ maximalIdeal O, algebraMap O S a ∈ P := by
    intro P hP a ha
    have h1 : (P.under O).IsMaximal := Ideal.IsMaximal.under O P
    have h2 : P.under O = maximalIdeal O := IsLocalRing.eq_maximalIdeal h1
    change a ∈ P.under O
    rw [h2]; exact ha
  obtain ⟨a₀, ha₀O, ha₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hO
  have hne : ∀ P : Ideal S, P.IsMaximal → P ≠ ⊥ := by
    intro P hP h
    have := hmax P hP a₀ ha₀O
    rw [h, Ideal.mem_bot, map_eq_zero_iff _ hinj] at this
    exact ha₀ this
  have hdvr : ∀ P : Ideal S, ∀ _ : P.IsMaximal, IsDiscreteValuationRing (a2r_locSub (F := F) P) :=
    fun P hP => IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S
      (hne P hP) _
  let Max : Set (Ideal S) := {P | P.IsMaximal}
  have hMaxfin : Max.Finite := by
    refine (Algebra.QuasiFinite.finite_primesOver (maximalIdeal O)).subset fun P hP => ?_
    have : P.IsMaximal := hP
    refine ⟨inferInstance, ⟨?_⟩⟩
    exact (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under O P)).symm
  have hDom : a2r_Dom O F = (a2r_locV (F := F)) '' Max := by
    ext v
    constructor
    · intro hv
      obtain ⟨P, hPmax, -, hP, rfl⟩ := a2r_exists_locVal_of_mem_Dom hO hinj v hv
      exact ⟨P, hPmax, a2r_locV_eq P hP⟩
    · rintro ⟨P, hP, rfl⟩
      have : P.IsMaximal := hP
      rw [a2r_locV_eq P (hdvr P hP)]
      exact a2r_locVal_mem_Dom P (hne P hP) (hdvr P hP) (hmax P hP)
  have hinjOn : Set.InjOn (a2r_locV (F := F)) Max := by
    intro P hP Q hQ h
    have : P.IsMaximal := hP
    have : Q.IsMaximal := hQ
    rw [a2r_locV_eq P (hdvr P hP), a2r_locV_eq Q (hdvr Q hQ)] at h
    exact a2r_locVal_injective _ _ h
  refine ⟨hDom ▸ hMaxfin.image _, ?_⟩
  -- the case of an element of `O`
  have key : ∀ a : O, a ≠ 0 → a2r_ordZ O F (algebraMap O F a) =
      ∑ᶠ v ∈ a2r_Dom O F, a2r_vord v (algebraMap O F a) * a2r_resDeg O v := by
    intro a ha
    set a' := algebraMap O S a
    have ha' : a' ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha
    obtain ⟨c, hc, hcS⟩ := a2r_exists_conductor (O := O) (S := S) (F := F)
      (IsFractionRing.injective S F)
    have hA := a2r_length_quot_eq hinj hc hcS ha
    rw [(Submodule.Quotient.restrictScalarsEquiv O (Ideal.span {a'})).length_eq] at hA
    have hI : Ideal.span {a'} ≠ ⊥ := by simpa using ha'
    have hB := a2r_length_quot_dedekind (O := O) hmax hI
    have hord : Ring.ord O a = ∑ P ∈ (normalizedFactors (Ideal.span {a'})).toFinset,
        (Multiset.count P (normalizedFactors (Ideal.span {a'})) : ℕ∞) * a2r_locLen O P :=
      hA.trans hB
    set T := (normalizedFactors (Ideal.span {a'})).toFinset
    have hTmax : ∀ P ∈ T, P.IsMaximal := by
      intro P hP
      have hPp := prime_of_normalized_factor _ (Multiset.mem_toFinset.mp hP)
      exact Ideal.IsPrime.isMaximal (Ideal.isPrime_of_prime hPp) hPp.ne_zero
    rw [a2r_ordZ_algebraMap ha, hord, ENat.toNat_sum (fun P hP => ?_)]
    swap
    · intro htop
      have : Ring.ord O a = ⊤ := by
        rw [hord]; exact WithTop.sum_eq_top.mpr ⟨P, hP, htop⟩
      exact Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero ha) this
    rw [hDom, finsum_mem_image hinjOn, finsum_mem_eq_finite_toFinset_sum _ hMaxfin]
    push_cast
    have hsub : T ⊆ hMaxfin.toFinset := fun P hP => (Set.Finite.mem_toFinset _).mpr (hTmax P hP)
    rw [← Finset.sum_subset hsub ?_]
    · refine Finset.sum_congr rfl fun P hP => ?_
      have : P.IsMaximal := hTmax P hP
      rw [a2r_locV_eq P (hdvr P this), IsScalarTower.algebraMap_apply O S F,
        a2r_vord_locVal_algebraMap P (hne P this) (hdvr P this) ha',
        a2r_resDeg_locVal P (hne P this) (hdvr P this) (hmax P this), ENat.toNat_mul,
        ENat.toNat_natCast]
      push_cast
      ring
    · intro P hP hPT
      have : P.IsMaximal := (Set.Finite.mem_toFinset _).mp hP
      rw [a2r_locV_eq P (hdvr P this), IsScalarTower.algebraMap_apply O S F,
        a2r_vord_locVal_algebraMap P (hne P this) (hdvr P this) ha',
        Multiset.count_eq_zero.mpr fun h => hPT (Multiset.mem_toFinset.mpr h)]
      simp
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
  have ha : a ≠ 0 := by rintro rfl; simp at hx
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hA := (map_ne_zero_iff _ hOF).mpr ha
  have hB := (map_ne_zero_iff _ hOF).mpr hb0
  have hvdiv : ∀ v ∈ a2r_Dom O F, a2r_vord v (algebraMap O F a / algebraMap O F b) =
      a2r_vord v (algebraMap O F a) - a2r_vord v (algebraMap O F b) := by
    intro v hv
    rw [hDom] at hv
    obtain ⟨P, hP, rfl⟩ := hv
    have : P.IsMaximal := hP
    have := hdvr P hP
    rw [a2r_locV_eq P (hdvr P hP)]
    have hrange : ∀ y, y ∈ a2r_locVal P (hdvr P hP) ↔
        ∃ r : a2r_locSub (F := F) P, algebraMap _ F r = y := fun y => by
      rw [a2r_mem_locVal]
      exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨r, hr⟩ => hr ▸ r.2⟩
    rw [a2r_vord_eq_of_range _ hrange, a2r_vord_eq_of_range _ hrange,
      a2r_vord_eq_of_range _ hrange, a2r_ordZ_div hA hB]
  have hDomfin : (a2r_Dom O F).Finite := hDom ▸ hMaxfin.image _
  rw [a2r_ordZ_div hA hB, key a ha, key b hb0, ← finsum_mem_sub_distrib _ _ hDomfin]
  refine finsum_mem_congr rfl fun v hv => ?_
  rw [hvdiv v hv, sub_mul]

end normalization

/-! ## The norm formula -/

section norm

/-- The order at a DVR valuation subring is its own integer order. -/
theorem a2r_vord_self {K : Type*} [Field K] (u : ValuationSubring K) [IsDiscreteValuationRing u]
    (x : K) : a2r_vord u x = a2r_ordZ u K x :=
  a2r_vord_eq_of_range u (fun y => ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨r, hr⟩ => hr ▸ r.2⟩) x

/-- The order at a DVR valuation subring is additive. -/
theorem a2r_vord_mul_of_dvr {K : Type*} [Field K] (u : ValuationSubring K)
    [IsDiscreteValuationRing u] {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    a2r_vord u (x * y) = a2r_vord u x + a2r_vord u y := by
  rw [a2r_vord_self, a2r_vord_self, a2r_vord_self, a2r_ordZ_mul hx hy]

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [CharZero K]

open UniqueFactorizationMonoid in
/-- **The norm formula.** For a DVR `u` of `K` and a finite extension `L / K` of characteristic
zero, the valuation subrings of `L` dominating `u` form a finite set, and
`u(N_{L/K} x) = ∑_v v(x) [κ(v) : κ(u)]`.
Source: Fulton, *Intersection Theory*, second edition, Example A.3.1 and Proposition 1.4;
Serre, *Local Fields*, I, §4 and II, §2. -/
theorem a2r_vord_norm_eq_finsum (u : ValuationSubring K) [IsDiscreteValuationRing u] :
    (a2r_Dom u L).Finite ∧ ∀ x : L, x ≠ 0 →
      a2r_vord u (Algebra.norm K x) = ∑ᶠ v ∈ a2r_Dom u L, a2r_vord v x * a2r_resDeg u v := by
  classical
  let S := integralClosure u L
  have : IsFractionRing S L := integralClosure.isFractionRing_of_finite_extension K L
  have : IsDedekindDomain S := integralClosure.isDedekindDomain u K L
  have : Module.Finite u S := IsIntegralClosure.finite u K L S
  have huL : Function.Injective (algebraMap u L) := by
    rw [IsScalarTower.algebraMap_eq u K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective u K)
  have : Module.IsTorsionFree u L := Module.isTorsionFree_iff_algebraMap_injective.mpr huL
  have : Module.Free u S := IsIntegralClosure.module_free u K L S
  have hinj : Function.Injective (algebraMap u S) := by
    intro a b hab
    apply huL
    rw [IsScalarTower.algebraMap_apply u S L, hab, ← IsScalarTower.algebraMap_apply]
  have hO : maximalIdeal u ≠ ⊥ := IsDiscreteValuationRing.not_a_field u
  have hmax : ∀ P : Ideal S, P.IsMaximal → ∀ a ∈ maximalIdeal u, algebraMap u S a ∈ P := by
    intro P hP a ha
    have h2 : P.under u = maximalIdeal u :=
      IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under u P)
    change a ∈ P.under u
    rw [h2]; exact ha
  obtain ⟨a₀, ha₀O, ha₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hO
  have hne : ∀ P : Ideal S, P.IsMaximal → P ≠ ⊥ := by
    intro P hP h
    have := hmax P hP a₀ ha₀O
    rw [h, Ideal.mem_bot, map_eq_zero_iff _ hinj] at this
    exact ha₀ this
  have hdvr : ∀ P : Ideal S, ∀ _ : P.IsMaximal, IsDiscreteValuationRing (a2r_locSub (F := L) P) :=
    fun P hP => IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S
      (hne P hP) _
  let Max : Set (Ideal S) := {P | P.IsMaximal}
  have hMaxfin : Max.Finite := by
    refine (Algebra.QuasiFinite.finite_primesOver (maximalIdeal u)).subset fun P hP => ?_
    have : P.IsMaximal := hP
    refine ⟨inferInstance, ⟨?_⟩⟩
    exact (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under u P)).symm
  have hDom : a2r_Dom u L = (a2r_locV (F := L)) '' Max := by
    ext v
    constructor
    · intro hv
      obtain ⟨P, hPmax, -, hP, rfl⟩ := a2r_exists_locVal_of_mem_Dom hO hinj v hv
      exact ⟨P, hPmax, a2r_locV_eq P hP⟩
    · rintro ⟨P, hP, rfl⟩
      have : P.IsMaximal := hP
      rw [a2r_locV_eq P (hdvr P hP)]
      exact a2r_locVal_mem_Dom P (hne P hP) (hdvr P hP) (hmax P hP)
  have hinjOn : Set.InjOn (a2r_locV (F := L)) Max := by
    intro P hP Q hQ h
    have : P.IsMaximal := hP
    have : Q.IsMaximal := hQ
    rw [a2r_locV_eq P (hdvr P hP), a2r_locV_eq Q (hdvr Q hQ)] at h
    exact a2r_locVal_injective _ _ h
  have hDomfin : (a2r_Dom u L).Finite := hDom ▸ hMaxfin.image _
  refine ⟨hDomfin, ?_⟩
  have key : ∀ s : S, s ≠ 0 → a2r_vord u (Algebra.norm K (algebraMap S L s)) =
      ∑ᶠ v ∈ a2r_Dom u L, a2r_vord v (algebraMap S L s) * a2r_resDeg u v := by
    intro s hs
    have hsL : algebraMap S L s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective S L)).mpr hs
    have hn := Algebra.algebraMap_intNorm (A := u) (K := K) (L := L) s
    rw [← hn]
    have hn0 : Algebra.intNorm u S s ≠ 0 := by
      intro h0
      rw [h0, map_zero, eq_comm, Algebra.norm_eq_zero_iff] at hn
      exact hsL hn
    rw [a2r_vord_self, a2r_ordZ_algebraMap hn0]
    set T := (normalizedFactors (Ideal.span {s})).toFinset
    have hTmax : ∀ P ∈ T, P.IsMaximal := by
      intro P hP
      have hPp := prime_of_normalized_factor _ (Multiset.mem_toFinset.mp hP)
      exact Ideal.IsPrime.isMaximal (Ideal.isPrime_of_prime hPp) hPp.ne_zero
    have hspan : Ideal.span {Algebra.intNorm u S s} =
        maximalIdeal u ^ ∑ P ∈ T, P.inertiaDeg u *
          Multiset.count P (normalizedFactors (Ideal.span {s})) := by
      have hI : Ideal.span {s} ≠ ⊥ := by simpa using hs
      rw [← Ideal.relNorm_singleton]
      conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI]
      rw [map_multiset_prod]
      have hmap : (normalizedFactors (Ideal.span {s})).map (Ideal.relNorm u) =
          (normalizedFactors (Ideal.span {s})).map
            (fun P => maximalIdeal u ^ P.inertiaDeg u) := by
        refine Multiset.map_congr rfl fun P hP => ?_
        have : P.IsMaximal := hTmax P (Multiset.mem_toFinset.mpr hP)
        have : P.LiesOver (maximalIdeal u) :=
          ⟨(IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under u P)).symm⟩
        exact Ideal.relNorm_eq_pow_of_isMaximal P (maximalIdeal u)
      rw [hmap, Finset.prod_multiset_map_count, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun P _ => ?_
      rw [pow_mul]
    have hord : Ring.ord u (Algebra.intNorm u S s) = ((∑ P ∈ T, P.inertiaDeg u *
        Multiset.count P (normalizedFactors (Ideal.span {s})) : ℕ) : ℕ∞) := by
      rw [Ring.ord, hspan, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
    rw [hord, ENat.toNat_natCast, hDom, finsum_mem_image hinjOn,
      finsum_mem_eq_finite_toFinset_sum _ hMaxfin]
    have hsub : T ⊆ hMaxfin.toFinset := fun P hP => (Set.Finite.mem_toFinset _).mpr (hTmax P hP)
    rw [← Finset.sum_subset hsub ?_]
    · push_cast
      refine Finset.sum_congr rfl fun P hP => ?_
      have hPm : P.IsMaximal := hTmax P hP
      have : P.LiesOver (maximalIdeal u) :=
        ⟨(IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under u P)).symm⟩
      have := a2r_isLocalHom_localization P (hmax P hPm)
      rw [a2r_locV_eq P (hdvr P hPm),
        a2r_vord_locVal_algebraMap P (hne P hPm) (hdvr P hPm) hs,
        a2r_resDeg_locVal P (hne P hPm) (hdvr P hPm) (hmax P hPm),
        a2r_locLen_toNat_eq_inertiaDeg]
      ring
    · intro P hP hPT
      have : P.IsMaximal := (Set.Finite.mem_toFinset _).mp hP
      rw [a2r_locV_eq P (hdvr P this),
        a2r_vord_locVal_algebraMap P (hne P this) (hdvr P this) hs,
        Multiset.count_eq_zero.mpr fun h => hPT (Multiset.mem_toFinset.mpr h)]
      simp
  intro x hx
  have hloc := IsIntegralClosure.isLocalization u K L S
  obtain ⟨⟨s, ⟨t, a, ha, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid S (nonZeroDivisors u)) x
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have ht0 : algebraMap u S a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha0
  have hspec := IsLocalization.mk'_spec (M := Algebra.algebraMapSubmonoid S (nonZeroDivisors u))
    L s ⟨algebraMap u S a, a, ha, rfl⟩
  set y := IsLocalization.mk' L s
    (⟨algebraMap u S a, a, ha, rfl⟩ : Algebra.algebraMapSubmonoid S (nonZeroDivisors u))
  have htL : algebraMap S L (algebraMap u S a) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective S L)).mpr ht0
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_eq_zero] at hspec
    exact hspec.elim hx htL
  have hsL : algebraMap S L s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective S L)).mpr hs0
  have hNy : Algebra.norm K y ≠ 0 := (Algebra.norm_ne_zero_iff).mpr hx
  have hNt : Algebra.norm K (algebraMap S L (algebraMap u S a)) ≠ 0 :=
    (Algebra.norm_ne_zero_iff).mpr htL
  have hN : Algebra.norm K y = Algebra.norm K (algebraMap S L s) /
      Algebra.norm K (algebraMap S L (algebraMap u S a)) := by
    rw [eq_div_iff hNt, ← map_mul, hspec]
  have hvdiv : ∀ v ∈ a2r_Dom u L, a2r_vord v y =
      a2r_vord v (algebraMap S L s) - a2r_vord v (algebraMap S L (algebraMap u S a)) := by
    intro v hv
    rw [hDom] at hv
    obtain ⟨P, hP, rfl⟩ := hv
    have : P.IsMaximal := hP
    have := hdvr P hP
    rw [a2r_locV_eq P (hdvr P hP)]
    have hrange : ∀ z, z ∈ a2r_locVal P (hdvr P hP) ↔
        ∃ r : a2r_locSub (F := L) P, algebraMap _ L r = z := fun z => by
      rw [a2r_mem_locVal]
      exact ⟨fun h => ⟨⟨z, h⟩, rfl⟩, fun ⟨r, hr⟩ => hr ▸ r.2⟩
    rw [a2r_vord_eq_of_range _ hrange, a2r_vord_eq_of_range _ hrange,
      a2r_vord_eq_of_range _ hrange, eq_sub_iff_add_eq, ← a2r_ordZ_mul hx htL, hspec]
  rw [hN, a2r_vord_self, a2r_ordZ_div ((Algebra.norm_ne_zero_iff).mpr hsL) hNt,
    ← a2r_vord_self, ← a2r_vord_self, key s hs0, key _ ht0,
    ← finsum_mem_sub_distrib _ _ hDomfin]
  refine finsum_mem_congr rfl fun v hv => ?_
  rw [hvdiv v hv, sub_mul]

end norm

/-! ## Towers -/

section tower

/-- The tower law for `finrank` along two ring maps of fields, the infinite case included. -/
theorem a2r_finrank_comp {K L M : Type*} [Field K] [Field L] [Field M] (i : K →+* L)
    (j : L →+* M) :
    (letI := (j.comp i).toAlgebra; Module.finrank K M) =
      (letI := i.toAlgebra; Module.finrank K L) * (letI := j.toAlgebra; Module.finrank L M) := by
  let _ := i.toAlgebra
  let _ := j.toAlgebra
  let _ := (j.comp i).toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (Module.finrank_mul_finrank K L M).symm

/-- `v(f y) < 1` in `v` exactly when `v(y) < 1` in the pulled-back valuation subring. -/
theorem a2r_comap_valuation_lt_one_iff {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (v : ValuationSubring L) (y : K) :
    (v.comap f).valuation y < 1 ↔ v.valuation (f y) < 1 := by
  by_cases hy : y = 0
  · simp [hy]
  have hfy : f y ≠ 0 := (map_ne_zero_iff f f.injective).mpr hy
  rw [a2r_valuation_lt_one_iff _ hy, a2r_valuation_lt_one_iff _ hfy,
    ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀]

variable {O K L : Type*} [CommRing O] [IsLocalRing O] [Field K] [Field L] [Algebra O K]
  [Algebra K L] [Algebra O L] [IsScalarTower O K L] [Algebra.IsAlgebraic K L]

/-- A proper valuation subring of `L` restricts to a proper valuation subring of `K`. -/
theorem a2r_comap_ne_top (v : ValuationSubring L) (hv : v ≠ ⊤) :
    v.comap (algebraMap K L) ≠ ⊤ := by
  intro h
  apply hv
  refine a2r_eq_top_of_forall_mem v fun x => ?_
  have hK : ∀ k : K, algebraMap K L k ∈ v := fun k => by
    have : k ∈ v.comap (algebraMap K L) := h ▸ trivial
    exact this
  let j : K →+* v := (algebraMap K L).codRestrict v hK
  let := j.toAlgebra
  have : IsScalarTower K v L := .of_algebraMap_eq fun _ => rfl
  obtain ⟨w, hw⟩ := (IsIntegrallyClosed.isIntegral_iff (R := v) (K := L)).mp
    ((Algebra.IsIntegral.isIntegral (R := K) x).tower_top (A := v))
  rw [← hw]
  exact w.2

theorem a2r_comap_mem_Dom (v : ValuationSubring L) (hv : v ∈ a2r_Dom O L) :
    v.comap (algebraMap K L) ∈ a2r_Dom O K := by
  refine ⟨a2r_comap_ne_top v hv.1, fun a => ⟨?_, fun ha => ?_⟩⟩
  · rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact (hv.2 a).1
  · rw [a2r_comap_valuation_lt_one_iff, ← IsScalarTower.algebraMap_apply]
    exact (hv.2 a).2 ha

omit [Algebra.IsAlgebraic K L] in
/-- The valuation subrings of `L` dominating `u ∈ Dom(O, K)` are those dominating `O` and
restricting to `u`. -/
theorem a2r_mem_Dom_tower_iff (u : ValuationSubring K) (hu : u ∈ a2r_Dom O K)
    (v : ValuationSubring L) :
    v ∈ a2r_Dom u L ↔ v ∈ a2r_Dom O L ∧ v.comap (algebraMap K L) = u := by
  constructor
  · rintro ⟨hvtop, hvdom⟩
    have hO : v ∈ a2r_Dom O L := by
      refine ⟨hvtop, fun a => ⟨?_, fun ha => ?_⟩⟩
      · rw [IsScalarTower.algebraMap_apply O K L]
        exact (hvdom ⟨_, (hu.2 a).1⟩).1
      · rw [IsScalarTower.algebraMap_apply O K L]
        refine (hvdom ⟨_, (hu.2 a).1⟩).2 ?_
        rw [ValuationSubring.valuation_lt_one_iff]
        exact (hu.2 a).2 ha
    refine ⟨hO, (a2r_eq_of_le_of_dominates u _ (fun x hx => ?_) fun x hx0 hx => ?_).symm⟩
    · exact (hvdom ⟨x, hx⟩).1
    · have hxu : x ∈ u := (ValuationSubring.valuation_le_one_iff u x).mp hx.le
      rw [a2r_comap_valuation_lt_one_iff]
      refine (hvdom ⟨x, hxu⟩).2 ?_
      rw [ValuationSubring.valuation_lt_one_iff]
      exact hx
  · rintro ⟨⟨hvtop, -⟩, hcomap⟩
    refine ⟨hvtop, fun a => ⟨?_, fun ha => ?_⟩⟩
    · have : (a : K) ∈ v.comap (algebraMap K L) := hcomap ▸ a.2
      exact this
    · rw [ValuationSubring.valuation_lt_one_iff] at ha
      set y : K := (a : K)
      have ha' : (v.comap (algebraMap K L)).valuation y < 1 := hcomap ▸ ha
      exact (a2r_comap_valuation_lt_one_iff (algebraMap K L) v y).mp ha'

omit [Algebra.IsAlgebraic K L] in
/-- Residue degrees are multiplicative in towers. -/
theorem a2r_resDeg_tower (u : ValuationSubring K) (hu : u ∈ a2r_Dom O K)
    (v : ValuationSubring L) (hv : v ∈ a2r_Dom u L) :
    a2r_resDeg O v = a2r_resDeg O u * a2r_resDeg u v := by
  have hvO := ((a2r_mem_Dom_tower_iff u hu v).mp hv).1
  have := a2r_domHom_isLocalHom v hvO.2
  have := a2r_domHom_isLocalHom u hu.2
  have := a2r_domHom_isLocalHom v hv.2
  rw [a2r_resDeg_of v hvO.2, a2r_resDeg_of u hu.2, a2r_resDeg_of v hv.2]
  have hcomp : a2r_domHom v (fun a => (hvO.2 a).1) =
      (a2r_domHom v (fun a => (hv.2 a).1)).comp (a2r_domHom u (fun a => (hu.2 a).1)) := by
    ext a
    change algebraMap O L a = algebraMap K L (algebraMap O K a)
    exact IsScalarTower.algebraMap_apply O K L a
  have h := a2r_finrank_comp (ResidueField.map (a2r_domHom u (fun a => (hu.2 a).1)))
    (ResidueField.map (a2r_domHom v (fun a => (hv.2 a).1)))
  have hmap : ResidueField.map (a2r_domHom v (fun a => (hvO.2 a).1)) =
      (ResidueField.map (a2r_domHom v (fun a => (hv.2 a).1))).comp
        (ResidueField.map (a2r_domHom u (fun a => (hu.2 a).1))) := by
    refine RingHom.ext fun x => ?_
    obtain ⟨x0, rfl⟩ := IsLocalRing.residue_surjective x
    simp only [RingHom.comp_apply, ResidueField.map_residue]
    rw [hcomp]
    rfl
  rw [hmap]
  exact h

/-- Sums over the valuations of `L` dominating `O` split along their restrictions to `K`. -/
theorem a2r_finsum_tower (g : ValuationSubring L → ℤ) (hfin : (a2r_Dom O K).Finite)
    (hfin2 : ∀ u ∈ a2r_Dom O K, (a2r_Dom u L).Finite) :
    ∑ᶠ v ∈ a2r_Dom O L, g v = ∑ᶠ u ∈ a2r_Dom O K, ∑ᶠ v ∈ a2r_Dom u L, g v := by
  have hset : a2r_Dom O L = ⋃ u ∈ a2r_Dom O K, a2r_Dom u L := by
    ext v
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro hv
      exact ⟨_, a2r_comap_mem_Dom v hv,
        (a2r_mem_Dom_tower_iff _ (a2r_comap_mem_Dom v hv) v).mpr ⟨hv, rfl⟩⟩
    · rintro ⟨u, hu, hv⟩
      exact ((a2r_mem_Dom_tower_iff u hu v).mp hv).1
  rw [hset, finsum_mem_biUnion _ hfin hfin2]
  intro u hu u' hu' hne
  refine Set.disjoint_left.mpr fun v hv hv' => hne ?_
  rw [← ((a2r_mem_Dom_tower_iff u hu v).mp hv).2, ((a2r_mem_Dom_tower_iff u' hu' v).mp hv').2]

end tower

/-! ## Arithmetic of `a2r_vord` -/

theorem a2r_vord_mul {F : Type*} [Field F] (v : ValuationSubring F) {x y : F} (hx : x ≠ 0)
    (hy : y ≠ 0) : a2r_vord v (x * y) = a2r_vord v x + a2r_vord v y := by
  by_cases h : IsDiscreteValuationRing v
  · exact a2r_vord_mul_of_dvr v hx hy
  · simp [a2r_vord, h]

theorem a2r_vord_inv {F : Type*} [Field F] (v : ValuationSubring F) {x : F} (hx : x ≠ 0) :
    a2r_vord v x⁻¹ = - a2r_vord v x := by
  by_cases h : IsDiscreteValuationRing v
  · rw [a2r_vord_self, a2r_vord_self, a2r_ordZ_inv hx]
  · simp [a2r_vord, h]

theorem a2r_vord_pow {F : Type*} [Field F] (v : ValuationSubring F) {x : F} (hx : x ≠ 0)
    (n : ℕ) : a2r_vord v (x ^ n) = n * a2r_vord v x := by
  induction n with
  | zero =>
    by_cases h : IsDiscreteValuationRing v
    · rw [pow_zero, a2r_vord_self, a2r_ordZ_one]; simp
    · simp [a2r_vord, h]
  | succ n ih =>
    rw [pow_succ, a2r_vord_mul v (pow_ne_zero n hx) hx, ih]
    push_cast; ring

/-- Units of a valuation subring have order zero. -/
theorem a2r_vord_eq_zero_of_unit {F : Type*} [Field F] (v : ValuationSubring F) {x : F}
    (hx : x ∈ v) (hx' : x⁻¹ ∈ v) : a2r_vord v x = 0 := by
  by_cases h : IsDiscreteValuationRing v
  · rw [a2r_vord_self]
    by_cases hx0 : x = 0
    · rw [hx0, a2r_ordZ_zero]
    have hu : IsUnit (⟨x, hx⟩ : v) := by
      refine IsUnit.of_mul_eq_one (⟨x⁻¹, hx'⟩ : v) (Subtype.ext ?_)
      change x * x⁻¹ = 1
      exact mul_inv_cancel₀ hx0
    have hx0' : (⟨x, hx⟩ : v) ≠ 0 := fun h0 => hx0 (congrArg Subtype.val h0)
    rw [show x = algebraMap v F ⟨x, hx⟩ from rfl, a2r_ordZ_algebraMap hx0', Ring.ord_of_isUnit hu]
    rfl
  · simp [a2r_vord, h]

/-! ## The polynomial ring `K[t]` and its localization at `(t)` -/

section rational

open Polynomial
open scoped IntermediateField IntermediateField.algebraAdjoinAdjoin

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] (t : L)

/-- The element `t` of `K[t]`. -/
def a2r_tGen : Algebra.adjoin K {t} := ⟨t, Algebra.self_mem_adjoin_singleton K t⟩

/-- The prime `(t)` of `K[t]`. -/
def a2r_tIdeal : Ideal (Algebra.adjoin K {t}) := Ideal.span {a2r_tGen K t}

variable {K t}

theorem a2r_polyEquiv_X (ht : Transcendental K t) :
    Polynomial.algEquivOfTranscendental K t ht X = a2r_tGen K t := by
  ext; simp [a2r_tGen]

theorem a2r_isPrincipalIdealRing_adjoin (ht : Transcendental K t) :
    IsPrincipalIdealRing (Algebra.adjoin K {t}) :=
  IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental K t ht).toRingHom
    (Polynomial.algEquivOfTranscendental K t ht).surjective

theorem a2r_tIdeal_eq_map (ht : Transcendental K t) : a2r_tIdeal K t =
    (Ideal.span {X - C (0 : K)}).map (Polynomial.algEquivOfTranscendental K t ht) := by
  rw [Ideal.map_span, Set.image_singleton, map_sub, C_0, map_zero, sub_zero, a2r_polyEquiv_X]
  rfl

theorem a2r_tIdeal_ne_bot (ht : Transcendental K t) : a2r_tIdeal K t ≠ ⊥ := by
  rw [a2r_tIdeal, Ne, Ideal.span_singleton_eq_bot]
  intro h
  have : t = 0 := congrArg Subtype.val h
  exact ht (this ▸ isAlgebraic_zero)

/-- `K[t]/(t) ≅ K` as `K`-algebras. -/
def a2r_quotientTIdealEquiv (ht : Transcendental K t) :
    K ≃ₐ[K] Algebra.adjoin K {t} ⧸ a2r_tIdeal K t :=
  (Polynomial.quotientSpanXSubCAlgEquiv (0 : K)).symm.trans
    (Ideal.quotientEquivAlg _ _ (Polynomial.algEquivOfTranscendental K t ht)
      (a2r_tIdeal_eq_map ht))

theorem a2r_tIdeal_isMaximal (ht : Transcendental K t) : (a2r_tIdeal K t).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _
    (MulEquiv.isField (Field.toIsField K) (a2r_quotientTIdealEquiv ht).symm.toMulEquiv)

theorem a2r_algebraMap_quotient_bijective (ht : Transcendental K t) :
    Function.Bijective (algebraMap K (Algebra.adjoin K {t} ⧸ a2r_tIdeal K t)) := by
  have h : ⇑(algebraMap K (Algebra.adjoin K {t} ⧸ a2r_tIdeal K t)) =
      ⇑(a2r_quotientTIdealEquiv ht) := by
    ext c
    rw [← (a2r_quotientTIdealEquiv ht).commutes c]
    rfl
  rw [h]
  exact (a2r_quotientTIdealEquiv ht).bijective

end rational

/-- `a2r_locVal P` is a DVR. -/
theorem a2r_locVal_isDVR {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] (P : Ideal R) [P.IsPrime]
    (hP : IsDiscreteValuationRing (a2r_locSub (F := F) P)) :
    IsDiscreteValuationRing (a2r_locVal P hP) := by
  have := hP
  let j : a2r_locSub (F := F) P →+* a2r_locVal P hP :=
    (algebraMap (a2r_locSub (F := F) P) F).codRestrict _ fun r => by
      rw [a2r_mem_locVal]; exact r.2
  have hj : Function.Bijective j := by
    refine ⟨fun a b hab => ?_, fun y => ?_⟩
    · have h := congrArg Subtype.val hab
      exact Subtype.ext h
    · exact ⟨⟨y, (a2r_mem_locVal P hP).mp y.2⟩, rfl⟩
  exact a2r_isDVR_of_ringEquiv (RingEquiv.ofBijective j hj)

/-- An algebra whose structure map is bijective has rank one. -/
theorem a2r_finrank_eq_one_of_bijective {R S : Type*} [CommRing R] [Nontrivial R] [CommRing S]
    [Algebra R S] (h : Function.Bijective (algebraMap R S)) : Module.finrank R S = 1 := by
  rw [← (AlgEquiv.ofBijective (Algebra.ofId R S) h).toLinearEquiv.finrank_eq,
    Module.finrank_self]

section zeroHalf

open Polynomial
open scoped IntermediateField IntermediateField.algebraAdjoinAdjoin

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [CharZero K] {t : L}

open UniqueFactorizationMonoid in
/-- **Zeros of a transcendental element.** For `t` transcendental over `K` with `L` finite over
`K(t)`, the proper valuation subrings of `L` containing `K` in which `t` has positive valuation
form a finite set, and the sum over them of `v(t) [κ(v) : K]` is `[L : K(t)]`.
Source: Fulton, *Intersection Theory*, second edition, proof of Proposition 1.4; Hartshorne,
*Algebraic Geometry*, II, Proposition 6.9. -/
theorem a2r_finsum_zeros (ht : Transcendental K t) [FiniteDimensional K⟮t⟯ L] :
    {v | v ∈ a2r_Dom K L ∧ v.valuation t < 1}.Finite ∧
      ∑ᶠ v ∈ {v | v ∈ a2r_Dom K L ∧ v.valuation t < 1}, a2r_vord v t * a2r_resDeg K v =
        Module.finrank K⟮t⟯ L := by
  classical
  set R := Algebra.adjoin K {t}
  set E := K⟮t⟯
  have : IsPrincipalIdealRing R := a2r_isPrincipalIdealRing_adjoin ht
  have : IsDedekindDomain R := IsPrincipalIdealRing.isDedekindDomain R
  set P := a2r_tIdeal K t
  have hPmax : P.IsMaximal := a2r_tIdeal_isMaximal ht
  have hP0 : P ≠ ⊥ := a2r_tIdeal_ne_bot ht
  have hP : IsDiscreteValuationRing (a2r_locSub (F := E) P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hP0 _
  set u0 := a2r_locVal (F := E) P hP
  have : IsDiscreteValuationRing u0 := a2r_locVal_isDVR P hP
  have hmaxK : ∀ a ∈ maximalIdeal K, algebraMap K R a ∈ P := by
    intro a ha
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at ha
    rw [ha, map_zero]
    exact P.zero_mem
  have hu0 : u0 ∈ a2r_Dom K E := a2r_locVal_mem_Dom P hP0 hP hmaxK
  set tE : E := IntermediateField.AdjoinSimple.gen K t
  have htE : algebraMap E L tE = t := rfl
  have htE0 : tE ≠ 0 := by
    intro h
    apply ht
    rw [← htE, h, map_zero]
    exact isAlgebraic_zero
  have htER : tE = algebraMap R E (a2r_tGen K t) := rfl
  -- `t` has positive valuation at `u0`
  have hu0t : u0.valuation tE < 1 := by
    rw [a2r_valuation_lt_one_iff _ htE0, a2r_mem_locVal, a2r_mem_locVal, htER]
    refine ⟨a2r_algebraMap_mem_locSub P _, (a2r_mem_prime_iff P ?_).mp
      (Ideal.subset_span rfl)⟩
    intro h
    exact htE0 (by rw [htER, h, map_zero])
  -- the set of the statement is `Dom(u0, L)`
  have hset : {v | v ∈ a2r_Dom K L ∧ v.valuation t < 1} = a2r_Dom u0 L := by
    ext v
    rw [a2r_mem_Dom_tower_iff u0 hu0 v]
    constructor
    · rintro ⟨hv, hvt⟩
      have hR' : ∀ x ∈ Algebra.adjoin K {t}, x ∈ v := by
        intro x hx
        induction hx using Algebra.adjoin_induction with
        | mem x hx =>
          obtain rfl := Set.mem_singleton_iff.mp hx
          exact (ValuationSubring.valuation_le_one_iff v _).mp hvt.le
        | algebraMap c => exact (hv.2 c).1
        | add x y _ _ hx hy => exact add_mem hx hy
        | mul x y _ _ hx hy => exact mul_mem hx hy
      have hR : ∀ r : R, (r : L) ∈ v := fun r => hR' r r.2
      refine ⟨hv, (a2r_eq_locVal P hP _ (a2r_comap_ne_top v hv.1) (fun a => ?_)
        (fun s hs => ?_))⟩
      · rw [ValuationSubring.mem_comap]
        exact hR a
      · rw [ValuationSubring.mem_comap, map_inv₀]
        change ((s : L))⁻¹ ∈ v
        have hs0 : (s : L) ≠ 0 := by
          intro h
          apply hs
          rw [show s = 0 from Subtype.ext h]
          exact P.zero_mem
        have hv1 : v.valuation (s : L) = 1 := by
          refine le_antisymm ((ValuationSubring.valuation_le_one_iff v _).mpr (hR s)) ?_
          by_contra hlt
          push Not at hlt
          obtain ⟨y, i, hi, hyi⟩ := hPmax.exists_inv hs
          obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hi
          have h1 : v.valuation (((y * s + q * a2r_tGen K t : R)) : L) < 1 := by
            have e : (((y * s + q * a2r_tGen K t : R)) : L) =
                (y : L) * (s : L) + (q : L) * t := rfl
            rw [e]
            refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
            · rw [map_mul]
              exact lt_of_le_of_lt (mul_le_of_le_one_left' ((ValuationSubring.valuation_le_one_iff
                v _).mpr (hR y))) hlt
            · rw [map_mul]
              exact lt_of_le_of_lt (mul_le_of_le_one_left' ((ValuationSubring.valuation_le_one_iff
                v _).mpr (hR q))) hvt
          rw [hyi] at h1
          simp at h1
        rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, hv1, inv_one]
    · rintro ⟨hv, hcomap⟩
      refine ⟨hv, ?_⟩
      rw [← htE, ← a2r_comap_valuation_lt_one_iff, hcomap]
      exact hu0t
  obtain ⟨hfin, hD⟩ := a2r_vord_norm_eq_finsum E L u0
  refine ⟨hset ▸ hfin, ?_⟩
  have ht0 : t ≠ 0 := fun h => ht (h ▸ isAlgebraic_zero)
  -- residue degree of `u0` over `K` is one
  have hres0 : a2r_resDeg K u0 = 1 := by
    have : P.LiesOver (maximalIdeal K) := by
      constructor
      rw [IsLocalRing.maximalIdeal_eq_bot]
      exact ((Ideal.eq_bot_or_top _).resolve_right
        (Ideal.IsPrime.ne_top (Ideal.IsPrime.under K P))).symm
    have := a2r_isLocalHom_localization P hmaxK
    rw [a2r_resDeg_locVal P hP0 hP hmaxK, a2r_locLen_toNat_eq_inertiaDeg,
      Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal K) P]
    apply a2r_finrank_eq_one_of_bijective
    have hb := a2r_algebraMap_quotient_bijective ht
    have hcomp : ∀ c : K, algebraMap (K ⧸ maximalIdeal K) (R ⧸ P) (Ideal.Quotient.mk _ c) =
        algebraMap K (R ⧸ P) c := fun c => rfl
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [hcomp, hcomp] at hxy
      rw [hb.1 hxy]
    · obtain ⟨c, hc⟩ := hb.2 z
      exact ⟨Ideal.Quotient.mk _ c, by rw [hcomp, hc]⟩
  -- the order of `t` at `u0` is one
  have hvt0 : a2r_vord u0 tE = 1 := by
    have hrange : ∀ z, z ∈ u0 ↔ ∃ r : a2r_locSub (F := E) P, algebraMap _ E r = z := fun z => by
      rw [a2r_mem_locVal]
      exact ⟨fun h => ⟨⟨z, h⟩, rfl⟩, fun ⟨r, hr⟩ => hr ▸ r.2⟩
    have hg0 : a2r_tGen K t ≠ 0 := fun h => htE0 (by rw [htER, h, map_zero])
    have hg0' : algebraMap R (a2r_locSub (F := E) P) (a2r_tGen K t) ≠ 0 := by
      intro h
      apply htE0
      rw [htER]
      exact congrArg Subtype.val h
    rw [a2r_vord_eq_of_range _ hrange,
      show tE = algebraMap (a2r_locSub (F := E) P) E
        (algebraMap R (a2r_locSub (F := E) P) (a2r_tGen K t)) from rfl,
      a2r_ordZ_algebraMap hg0', a2r_ord_localization_eq_count P hP0 _ hg0]
    have hirr : Irreducible P := (Ideal.prime_of_isPrime hP0 inferInstance).irreducible
    have hspan : Ideal.span {a2r_tGen K t} = P := rfl
    rw [hspan, UniqueFactorizationMonoid.normalizedFactors_irreducible hirr, normalize_eq,
      Multiset.count_singleton_self]
    rfl
  rw [hset]
  calc ∑ᶠ v ∈ a2r_Dom u0 L, a2r_vord v t * a2r_resDeg K v
      = ∑ᶠ v ∈ a2r_Dom u0 L, a2r_vord v t * a2r_resDeg u0 v := by
        refine finsum_mem_congr rfl fun v hv => ?_
        rw [a2r_resDeg_tower u0 hu0 v hv, hres0, one_mul]
    _ = a2r_vord u0 (Algebra.norm E t) := (hD t ht0).symm
    _ = Module.finrank E L := by
        rw [← htE, Algebra.norm_algebraMap, a2r_vord_pow u0 htE0, hvt0, mul_one]

/-- An element integral over a field contained in a valuation subring lies in it. -/
theorem a2r_mem_of_isIntegral {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : ValuationSubring L) (hK : ∀ c : K, algebraMap K L c ∈ v) {x : L}
    (hx : IsIntegral K x) : x ∈ v := by
  let j : K →+* v := (algebraMap K L).codRestrict v hK
  let := j.toAlgebra
  have : IsScalarTower K v L := .of_algebraMap_eq fun _ => rfl
  obtain ⟨w, hw⟩ := (IsIntegrallyClosed.isIntegral_iff (R := v) (K := L)).mp
    (hx.tower_top (A := v))
  rw [← hw]
  exact w.2

open UniqueFactorizationMonoid in
/-- **Degree of a principal divisor.** On a field `L` over `K` of characteristic zero in which
every transcendental element `t` has `L` finite over `K(t)` (a function field of one variable),
the orders of a nonzero element at the proper valuation subrings containing `K`, weighted by the
residue degrees, have finite support and sum to zero.
Source: Fulton, *Intersection Theory*, second edition, proof of Proposition 1.4; Hartshorne,
*Algebraic Geometry*, II, Corollary 6.10. -/
theorem a2r_finsum_vord_eq_zero {φ : L} (hφ : φ ≠ 0)
    (hfd : ∀ t : L, Transcendental K t → FiniteDimensional K⟮t⟯ L) :
    (a2r_Dom K L ∩ Function.support fun v => a2r_vord v φ * a2r_resDeg K v).Finite ∧
      ∑ᶠ v ∈ a2r_Dom K L, a2r_vord v φ * a2r_resDeg K v = 0 := by
  classical
  by_cases halg : IsAlgebraic K φ
  · have hzero : ∀ v ∈ a2r_Dom K L, a2r_vord v φ * a2r_resDeg K v = 0 := by
      intro v hv
      have hK : ∀ c : K, algebraMap K L c ∈ v := fun c => (hv.2 c).1
      rw [a2r_vord_eq_zero_of_unit v (a2r_mem_of_isIntegral v hK halg.isIntegral)
        (a2r_mem_of_isIntegral v hK halg.inv.isIntegral), zero_mul]
    refine ⟨Set.Finite.subset Set.finite_empty fun v ⟨hv, hs⟩ => hs (hzero v hv), ?_⟩
    exact finsum_mem_eq_zero_of_forall_eq_zero hzero
  have ht : Transcendental K φ := halg
  have ht' : Transcendental K φ⁻¹ := fun h => halg (by simpa using h.inv)
  have := hfd φ ht
  have := hfd φ⁻¹ ht'
  obtain ⟨hZ, hsumZ⟩ := a2r_finsum_zeros (K := K) (L := L) ht
  obtain ⟨hZ', hsumZ'⟩ := a2r_finsum_zeros (K := K) (L := L) ht'
  set Z := {v | v ∈ a2r_Dom K L ∧ v.valuation φ < 1}
  set Z' := {v | v ∈ a2r_Dom K L ∧ v.valuation φ⁻¹ < 1}
  set f := fun v : ValuationSubring L => a2r_vord v φ * a2r_resDeg K v
  have hsupp : ∀ v ∈ a2r_Dom K L, f v ≠ 0 → v ∈ Z ∪ Z' := by
    intro v hv hfv
    by_cases h1 : φ ∈ v
    · by_cases h2 : φ⁻¹ ∈ v
      · exact absurd (by simp [f, a2r_vord_eq_zero_of_unit v h1 h2]) hfv
      · exact Or.inl ⟨hv, (a2r_valuation_lt_one_iff v hφ).mpr ⟨h1, h2⟩⟩
    · have h2 : φ⁻¹ ∈ v := (v.mem_or_inv_mem φ).resolve_left h1
      refine Or.inr ⟨hv, (a2r_valuation_lt_one_iff v (inv_ne_zero hφ)).mpr ⟨h2, ?_⟩⟩
      rwa [inv_inv]
  have hdisj : Disjoint Z Z' := by
    refine Set.disjoint_left.mpr fun v hv hv' => ?_
    have h1 := hv.2
    have h2 := hv'.2
    have h0 : v.valuation φ ≠ 0 := (Valuation.ne_zero_iff _).mpr hφ
    rw [map_inv₀, inv_lt_one₀ (pos_iff_ne_zero.mpr h0)] at h2
    exact lt_asymm h1 h2
  have hsub : Z ∪ Z' ⊆ a2r_Dom K L := Set.union_subset (fun v hv => hv.1) (fun v hv => hv.1)
  refine ⟨(hZ.union hZ').subset fun v ⟨hv, hs⟩ => hsupp v hv hs, ?_⟩
  rw [finsum_mem_inter_support_eq' f (a2r_Dom K L) (Z ∪ Z') fun v hv =>
    ⟨fun h => hsupp v h hv, fun h => hsub h⟩, finsum_mem_union hdisj hZ hZ']
  have hZ'val : ∑ᶠ v ∈ Z', f v = - (Module.finrank K⟮φ⁻¹⟯ L : ℤ) := by
    rw [← hsumZ', ← finsum_mem_neg_distrib _ hZ']
    refine finsum_mem_congr rfl fun v _ => ?_
    simp only [f]
    rw [a2r_vord_inv v hφ]
    ring
  have hE : K⟮φ⁻¹⟯ = K⟮φ⟯ := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self K φ)
    · rw [IntermediateField.adjoin_simple_le_iff]
      simpa using inv_mem (IntermediateField.mem_adjoin_simple_self K φ⁻¹)
  rw [hZ'val, hsumZ, hE, add_neg_cancel]

end zeroHalf

/-! ## Finiteness of the normalization -/

/-- The integral closure of a finitely generated domain over a field of characteristic zero in
its fraction field is a finite module.
Source: Atiyah–Macdonald, Proposition 5.17 and Exercise 5.16 (Noether normalization);
Eisenbud, *Commutative Algebra*, Corollary 13.13. -/
theorem a2r_finite_integralClosure {k A F : Type*} [Field k] [CharZero k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [Field F] [Algebra A F]
    [IsFractionRing A F] : Module.Finite A (integralClosure A F) := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin s) k
  let := g.toRingHom.toAlgebra
  have : Module.Finite P A := hfin
  let := ((algebraMap A F).comp (algebraMap P A)).toAlgebra
  have : IsScalarTower P A F := .of_algebraMap_eq fun _ => rfl
  have : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hinj
  have hPF : Function.Injective (algebraMap P F) :=
    (IsFractionRing.injective A F).comp hinj
  have : FaithfulSMul P F := (faithfulSMul_iff_algebraMap_injective P F).mpr hPF
  let FP := FractionRing P
  let := FractionRing.liftAlgebra P F
  have : IsScalarTower P FP F := inferInstance
  have : Algebra.IsIntegral P A := Algebra.IsIntegral.of_finite P A
  have : Module.Finite FP F := Module.Finite.of_isLocalization P A (Rₚ := FP) (Sₚ := F)
    (nonZeroDivisors P)
  have hfinP : Module.Finite P (integralClosure P F) :=
    IsIntegralClosure.finite P FP F (integralClosure P F)
  have hmem : ∀ x : F, x ∈ integralClosure P F ↔ x ∈ integralClosure A F := by
    intro x
    rw [mem_integralClosure_iff, mem_integralClosure_iff]
    constructor
    · intro hx
      exact hx.tower_top
    · intro hx
      exact isIntegral_trans (R := P) (A := A) x hx
  let e : integralClosure P F ≃ₗ[P] (integralClosure A F).restrictScalars P :=
    LinearEquiv.ofEq (integralClosure P F).toSubmodule
      ((integralClosure A F).restrictScalars P).toSubmodule (by ext x; exact hmem x)
  have : Module.Finite P ((integralClosure A F).restrictScalars P) := Module.Finite.equiv e
  let e2 : (integralClosure A F).restrictScalars P ≃ₗ[P] integralClosure A F :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have : Module.Finite P (integralClosure A F) := Module.Finite.equiv e2
  exact Module.Finite.of_restrictScalars_finite P A (integralClosure A F)

/-- Finiteness of the normalization passes to localizations.
Source: Atiyah–Macdonald, Proposition 5.12. -/
theorem a2r_finite_integralClosure_localization {A F Aₚ : Type*} [CommRing A] [IsDomain A]
    [Field F] [Algebra A F] [IsFractionRing A F] [hfin : Module.Finite A (integralClosure A F)]
    (M : Submonoid A) [CommRing Aₚ] [Algebra A Aₚ]
    [IsLocalization M Aₚ] [Algebra Aₚ F] [IsScalarTower A Aₚ F] :
    Module.Finite Aₚ (integralClosure Aₚ F) := by
  classical
  obtain ⟨T, hT⟩ := hfin
  let ι : integralClosure A F → integralClosure Aₚ F := fun t =>
    ⟨(t : F), (t.2 : IsIntegral A (t : F)).tower_top⟩
  refine ⟨⟨T.image ι, ?_⟩⟩
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  obtain ⟨⟨m, hm⟩, hmx⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M x hx
  have hmx' : (⟨m • x, hmx⟩ : integralClosure A F) ∈ Submodule.span A (T : Set _) := by
    rw [hT]; trivial
  have hmu : IsUnit (algebraMap A Aₚ m) := IsLocalization.map_units Aₚ ⟨m, hm⟩
  have key : ∀ y : integralClosure A F, y ∈ Submodule.span A (T : Set _) →
      ι y ∈ Submodule.span Aₚ ((T.image ι : Finset _) : Set (integralClosure Aₚ F)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (Finset.mem_image_of_mem _ hy)
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul a b _ hb =>
      have : ι (a • b) = algebraMap A Aₚ a • ι b := by
        apply Subtype.ext
        change a • (b : F) = algebraMap A Aₚ a • (b : F)
        rw [algebraMap_smul]
      rw [this]
      exact Submodule.smul_mem _ _ hb
  have h1 := key _ hmx'
  have : (⟨x, hx⟩ : integralClosure Aₚ F) = (hmu.unit⁻¹ : Aₚˣ) • ι ⟨m • x, hmx⟩ := by
    apply Subtype.ext
    change x = ((hmu.unit⁻¹ : Aₚˣ) : Aₚ) • (m • x)
    rw [← algebraMap_smul Aₚ m x, smul_smul, hmu.val_inv_mul, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ h1

/-- The valuations dominating a one-dimensional Noetherian local domain with finite normalization
are DVRs. -/
theorem a2r_isDVR_of_mem_Dom (O F : Type*) [CommRing O] [IsDomain O] [IsLocalRing O]
    [IsNoetherianRing O] [Ring.KrullDimLE 1 O] [Field F] [Algebra O F] [IsFractionRing O F]
    [Module.Finite O (integralClosure O F)] (hO : maximalIdeal O ≠ ⊥)
    (v : ValuationSubring F) (hv : v ∈ a2r_Dom O F) : IsDiscreteValuationRing v := by
  have : IsFractionRing (integralClosure O F) F := a2r_isFractionRing_integralClosure O F
  have : IsDedekindDomain (integralClosure O F) := a2r_isDedekindDomain_integralClosure O F
  have hinj : Function.Injective (algebraMap O (integralClosure O F)) := by
    intro a b hab
    apply IsFractionRing.injective O F
    rw [IsScalarTower.algebraMap_apply O (integralClosure O F) F, hab,
      ← IsScalarTower.algebraMap_apply]
  obtain ⟨P, _, _, hP, rfl⟩ := a2r_exists_locVal_of_mem_Dom hO hinj v hv
  exact a2r_locVal_isDVR P hP

end HodgeLean.Adapters
