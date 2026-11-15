import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! The original field as the fraction field of its integral closure.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- An integral field generator makes the original field the fraction field of the integral closure.
Source: subfield generation and the description of a subfield closure by ring fractions. -/
theorem s2v_i2b_integralClosure_fractionField
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (v : K) (hv : IsIntegral R v)
    (hgen : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤) :
    IsFractionRing (integralClosure R K) K := by
  have hclosure : Subfield.closure (Set.range (algebraMap (integralClosure R K) K)) = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply Subfield.closure_le.mpr
    intro x hx
    apply Subfield.subset_closure
    rcases hx with ⟨r, rfl⟩ | hx
    · exact ⟨algebraMap R (integralClosure R K) r, rfl⟩
    · have hxv : x = v := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨⟨v, hv⟩, rfl⟩
  apply IsFractionRing.of_field
  intro x
  have hx : x ∈ Subfield.closure (Set.range (algebraMap (integralClosure R K) K)) := by
    rw [hclosure]
    trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Subfield.mem_closure_iff.mp hx
  have hring : Subring.closure (Set.range (algebraMap (integralClosure R K) K)) =
      (algebraMap (integralClosure R K) K).range := by
    rw [← RingHom.coe_range, Subring.closure_eq]
  rw [hring] at ha hb
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  exact ⟨a', b', hab.symm⟩

/-- Base-linear field homomorphisms agree if they agree on the specified generator.
Source: the universal property of subfield generation. -/
theorem s2v_i2b_field_hom_ext
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (v : K) (hgen : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤)
    (f g : K →ₐ[R] K) (hv : f v = g v) : f = g := by
  have he : f.toRingHom = g.toRingHom :=
    RingHom.eq_of_eqOn_of_field_closure_eq_top hgen (by
      intro x hx
      rcases hx with ⟨r, rfl⟩ | hx
      · exact (f.commutes r).trans (g.commutes r).symm
      · have hxv : x = v := Set.mem_singleton_iff.mp hx
        subst x
        exact hv)
  ext x
  exact DFunLike.congr_fun he x

/-- Every base-linear field endomorphism commutes with the retained binomial eigen-action.
Source: all roots of the binomial differ by roots of unity in the base field. -/
theorem s2v_i2b_binomial_hom_commutes
    {F R K : Type*} [Field F] [CommRing R] [Field K]
    [Algebra F R] [Algebra R K] [Algebra F K] [IsScalarTower F R K]
    (m : ℕ) (hm : 0 < m) (ζ₀ : F) (hζ₀ : IsPrimitiveRoot ζ₀ m)
    (v : K) (hv0 : v ≠ 0) (r : R) (hv : v ^ m = algebraMap R K r)
    (hgen : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤)
    (δ : K ≃ₐ[R] K) (a : R) (hδ : δ v = algebraMap R K a * v)
    (σ : K →ₐ[R] K) : δ.toAlgHom.comp σ = σ.comp δ.toAlgHom := by
  haveI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hroot : IsPrimitiveRoot (algebraMap F K ζ₀) m :=
    hζ₀.map_of_injective (algebraMap F K).injective
  have hfixed : σ (v ^ m) = v ^ m := by rw [hv]; exact σ.commutes r
  have hratio : (σ v / v) ^ m = 1 := by
    rw [div_pow, ← map_pow, hfixed, div_self (pow_ne_zero m hv0)]
  obtain ⟨k, hk, he⟩ := hroot.eq_pow_of_pow_eq_one hratio
  have hσ : σ v = algebraMap F K (ζ₀ ^ k) * v := by
    apply (div_eq_iff hv0).mp
    rw [map_pow]
    exact he.symm
  have hδF : ∀ a : F, δ (algebraMap F K a) = algebraMap F K a := by
    intro a
    rw [IsScalarTower.algebraMap_apply F R K]
    exact δ.commutes _
  apply s2v_i2b_field_hom_ext v hgen
  change δ (σ v) = σ (δ v)
  simp only [hσ, hδ, map_mul, hδF, σ.commutes]
  ring

/-- Every injective base-linear evaluation of the integral closure intertwines the binomial action.
Source: extension to the fraction field and commutation of base-linear Kummer field homomorphisms. -/
theorem s2v_i2b_integral_embedding_commutes
    {F R K : Type*} [Field F] [CommRing R] [Field K]
    [Algebra F R] [Algebra R K] [Algebra F K] [IsScalarTower F R K]
    (m : ℕ) (hm : 0 < m) (ζ₀ : F) (hζ₀ : IsPrimitiveRoot ζ₀ m)
    (v : K) (hv0 : v ≠ 0) (hvint : IsIntegral R v)
    (r : R) (hv : v ^ m = algebraMap R K r)
    (hgen : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤)
    (δ : K ≃ₐ[R] K) (a : R) (hδ : δ v = algebraMap R K a * v)
    (e : integralClosure R K →ₐ[R] K) (he : Function.Injective e) :
    ∀ b, e (δ.mapIntegralClosure b) = δ (e b) := by
  haveI : IsFractionRing (integralClosure R K) K :=
    s2v_i2b_integralClosure_fractionField v hvint hgen
  let σ : K →ₐ[R] K := IsFractionRing.liftAlgHom he
  have hσ : ∀ b : integralClosure R K, σ (b : K) = e b := by
    intro b
    exact IsFractionRing.lift_algebraMap he b
  have hcomm := s2v_i2b_binomial_hom_commutes m hm ζ₀ hζ₀ v hv0 r hv hgen δ a hδ σ
  intro b
  have h := DFunLike.congr_fun hcomm (b : K)
  change δ (σ (b : K)) = σ (δ (b : K)) at h
  rw [hσ b] at h
  have hb : σ (δ (b : K)) = e (δ.mapIntegralClosure b) := hσ (δ.mapIntegralClosure b)
  exact (h.trans hb).symm

end HodgeLean.Foundations.Program
