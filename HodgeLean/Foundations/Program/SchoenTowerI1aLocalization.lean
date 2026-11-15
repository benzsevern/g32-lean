import HodgeLean.Foundations.Program.SchoenTowerI1aPre2Helpers
import Mathlib.Data.Fintype.Order

/-! # Fixed elements after principal localization
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A fixed unit has its inverse in the fixed subring.
Source: SGA 1, Exposé V, §1, invariant rings. -/
theorem s2v_i1alo_fixed_unit
    (S G : Type) [CommRing S] [Group G] [MulSemiringAction G S]
    (T : Subring S) (hT : ∀ x, x ∈ T ↔ ∀ g : G, g • x = x)
    (u : T) (hu : IsUnit u.val) : IsUnit u := by
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hu
  have hvT : v ∈ T := by
    apply (hT v).mpr
    intro g
    apply hu.mul_left_cancel
    calc
      u.val * (g • v) = g • (u.val * v) := by rw [smul_mul', (hT u.val).mp u.property g]
      _ = 1 := by rw [hv, smul_one]
      _ = u.val * v := hv.symm
  exact isUnit_iff_exists_inv.mpr ⟨⟨v, hvT⟩, Subtype.ext hv⟩

/-- One denominator power makes a numerator with fixed image fixed before localization.
Source: SGA 1, Exposé V, §1, localization of finite invariant rings. -/
theorem s2v_i1alo_fixed_numerator
    (R L G : Type) [CommRing R] [CommRing L] [Group G] [Finite G]
    [Algebra R L] [MulSemiringAction G R] [MulSemiringAction G L]
    (heq : ∀ (g : G) (x : R), algebraMap R L (g • x) = g • algebraMap R L x)
    (r : R) [IsLocalization.Away r L] (hr : ∀ g : G, g • r = r)
    (b : R) (hb : ∀ g : G, g • algebraMap R L b = algebraMap R L b) :
    ∃ n : ℕ, ∀ g : G, g • (r ^ n * b) = r ^ n * b := by
  have hn (g : G) : ∃ n : ℕ, r ^ n * (g • b) = r ^ n * b := by
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers r)
      ((heq g b).trans (hb g))
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff c.val r).mp c.property
    exact ⟨n, hn ▸ hc⟩
  choose n hn using hn
  obtain ⟨N, hN⟩ := Finite.exists_le n
  refine ⟨N, fun g => ?_⟩
  rw [smul_mul', smul_pow', hr g]
  calc
    r ^ N * (g • b) = r ^ (N - n g) * (r ^ n g * (g • b)) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hN g)]
    _ = r ^ (N - n g) * (r ^ n g * b) := by rw [hn g]
    _ = r ^ N * b := by rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hN g)]

/-- Localizing at a fixed element commutes with the fixed subrings of a finite action.
Source: SGA 1, Exposé V, §1, localization of invariant rings. -/
theorem s2v_i1alo_fixed_localization
    (R L G : Type) [CommRing R] [CommRing L] [Group G] [Finite G]
    [Algebra R L] [MulSemiringAction G R] [MulSemiringAction G L]
    (heq : ∀ (g : G) (x : R), algebraMap R L (g • x) = g • algebraMap R L x)
    (A : Subring R) (B : Subring L)
    (hA : ∀ x, x ∈ A ↔ ∀ g : G, g • x = x)
    (hB : ∀ x, x ∈ B ↔ ∀ g : G, g • x = x)
    (f : A →+* B) (hf : ∀ x : A, (f x).val = algebraMap R L x.val)
    (r : A) [IsLocalization.Away r.val L] :
    letI := f.toAlgebra
    IsLocalization.Away r B := by
  letI := f.toAlgebra
  have hr : ∀ g : G, g • r.val = r.val := (hA r.val).mp r.property
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · intro c
    change IsUnit (f c.val)
    apply s2v_i1alo_fixed_unit L G B hB
    rw [hf]
    apply IsLocalization.map_units (M := Submonoid.powers r.val) (S := L)
      ⟨c.val.val, ?_⟩
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff c.val r).mp c.property
    exact ⟨n, congrArg Subtype.val hn⟩
  · intro z
    obtain ⟨⟨b, c⟩, hc⟩ := IsLocalization.surj (Submonoid.powers r.val) z.val
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff c.val r.val).mp c.property
    change z.val * algebraMap R L c.val = algebraMap R L b at hc
    rw [← hn] at hc
    have hb : ∀ g : G, g • algebraMap R L b = algebraMap R L b := by
      intro g
      rw [← hc, smul_mul', (hB z.val).mp z.property g, ← heq, smul_pow', hr g]
    obtain ⟨k, hk⟩ := s2v_i1alo_fixed_numerator R L G heq r.val hr b hb
    let a : A := ⟨r.val ^ k * b, (hA _).mpr hk⟩
    refine ⟨⟨a, ⟨r ^ (n + k), ⟨n + k, rfl⟩⟩⟩, ?_⟩
    apply Subtype.ext
    change z.val * (f (r ^ (n + k))).val = (f a).val
    rw [hf, hf]
    change z.val * algebraMap R L (r.val ^ (n + k)) = algebraMap R L (r.val ^ k * b)
    calc
      _ = (z.val * algebraMap R L (r.val ^ n)) * algebraMap R L (r.val ^ k) := by
        rw [pow_add, map_mul, mul_assoc]
      _ = algebraMap R L b * algebraMap R L (r.val ^ k) := by rw [hc]
      _ = algebraMap R L (r.val ^ k * b) := by rw [map_mul, mul_comm]
  · intro x y hxy
    have he : algebraMap R L x.val = algebraMap R L y.val := by
      rw [← hf x, ← hf y]
      exact congrArg Subtype.val hxy
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers r.val) he
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff c.val r.val).mp c.property
    refine ⟨⟨r ^ n, ⟨n, rfl⟩⟩, Subtype.ext ?_⟩
    change r.val ^ n * x.val = r.val ^ n * y.val
    exact hn ▸ hc

/-- The section fixed subring is the existing chart invariant subring.
Source: SGA 1, Exposé V, §1, inverse pullback on sections. -/
theorem s2v_i1alo_section_fixed_iff
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] (a : G → (X ⟶ X))
    (U : X.left.Opens) (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (ρ : MulSemiringAction G Γ(X.left, U))
    (hρ : ∀ g x, @SMul.smul G Γ(X.left, U) ρ.toSMul g x =
      ((a g⁻¹).left.appLE U U (hiU g⁻¹)).hom x) :
    ∀ x, x ∈ s2v_i1a_chartInvariants X G a U hiU ↔
      ∀ g, @SMul.smul G Γ(X.left, U) ρ.toSMul g x = x := by
  intro x
  constructor
  · intro hx g
    exact (hρ g x).trans (hx g⁻¹)
  · intro hx g
    have hh := (hρ g⁻¹ x).symm.trans (hx g⁻¹)
    simpa only [inv_inv] using hh

/-- Restriction commutes with inverse pullback on two preserved opens.
Source: SGA 1, Exposé V, §1, naturality of section pullback. -/
theorem s2v_i1alo_section_restriction_equivariant
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] (a : G → (X ⟶ X))
    (U V : X.left.Opens) (hVU : V ≤ U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (hiV : ∀ g, V ≤ (a g).left ⁻¹ᵁ V)
    (ρU : MulSemiringAction G Γ(X.left, U))
    (ρV : MulSemiringAction G Γ(X.left, V))
    (hρU : ∀ g x, @SMul.smul G Γ(X.left, U) ρU.toSMul g x =
      ((a g⁻¹).left.appLE U U (hiU g⁻¹)).hom x)
    (hρV : ∀ g x, @SMul.smul G Γ(X.left, V) ρV.toSMul g x =
      ((a g⁻¹).left.appLE V V (hiV g⁻¹)).hom x) :
    ∀ g x, (X.left.presheaf.map (homOfLE hVU).op).hom
        (@SMul.smul G Γ(X.left, U) ρU.toSMul g x) =
      @SMul.smul G Γ(X.left, V) ρV.toSMul g
        ((X.left.presheaf.map (homOfLE hVU).op).hom x) := by
  intro g x
  let t := X.left.presheaf.map (homOfLE hVU).op
  have ht : (a g⁻¹).left.appLE U U (hiU g⁻¹) ≫ t =
      t ≫ (a g⁻¹).left.appLE V V (hiV g⁻¹) := by
    dsimp [t]
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  calc
    _ = t.hom (((a g⁻¹).left.appLE U U (hiU g⁻¹)).hom x) :=
      congrArg t.hom (hρU g x)
    _ = ((a g⁻¹).left.appLE V V (hiV g⁻¹)).hom (t.hom x) :=
      congrArg (fun k : Γ(X.left, U) ⟶ Γ(X.left, V) => k.hom x) ht
    _ = _ := (hρV g (t.hom x)).symm

end HodgeLean.Foundations.Program
