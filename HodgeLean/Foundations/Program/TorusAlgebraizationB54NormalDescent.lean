import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

noncomputable section
namespace HodgeLean.Foundations.Program

variable {R T : Type*} [CommRing R] [IsDomain R] [CommRing T] [IsDomain T]

set_option backward.isDefEq.respectTransparency false in
theorem b54_normal_of_division_closed_range (f : R →+* T) (hf : Function.Injective f)
    [IsIntegrallyClosed T]
    (hdiv : ∀ (a b : R) (y : T), b ≠ 0 → f a = f b * y → ∃ r, f r = y) :
    IsIntegrallyClosed R := by
  apply (isIntegrallyClosed_iff (FractionRing R)).mpr
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R x
  have hb : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  let φ : FractionRing R →+* FractionRing T := IsFractionRing.map hf
  have hc : (algebraMap T (FractionRing T)).comp f =
      φ.comp (algebraMap R (FractionRing R)) := by
    ext r
    simp [φ, IsFractionRing.map]
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff (FractionRing T)).mp inferInstance
    (IsIntegral.map_of_comp_eq f φ hc hx)
  have hfmap (r : R) : φ (algebraMap R (FractionRing R) r) =
      algebraMap T (FractionRing T) (f r) := (RingHom.congr_fun hc r).symm
  simp only [map_div₀, hfmap] at hy
  have hfb : algebraMap T (FractionRing T) (f b) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective T (FractionRing T))).mpr
      ((map_ne_zero_iff _ hf).mpr hb)
  rw [eq_div_iff hfb] at hy
  have hab : f a = f b * y := by
    apply IsFractionRing.injective T (FractionRing T)
    rw [map_mul, mul_comm]
    exact hy.symm
  obtain ⟨r, hr⟩ := hdiv a b y hb hab
  have ha : a = b * r := hf (by rw [map_mul, hr, hab])
  refine ⟨r, ?_⟩
  rw [ha, map_mul, mul_div_cancel_left₀]
  exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hb

theorem b54_normal_of_equalizer_range {ι D : Type*} [CommRing D] [IsDomain D]
    (f : R →+* T) (hf : Function.Injective f) [IsIntegrallyClosed T]
    (α β : ι → T →+* D) (hα : ∀ i, Function.Injective (α i))
    (hrange : ∀ y, y ∈ f.range ↔ ∀ i, α i y = β i y) : IsIntegrallyClosed R := by
  apply b54_normal_of_division_closed_range f hf
  intro a b y hb he
  change y ∈ f.range
  apply (hrange y).mpr
  intro i
  have ha := (hrange (f a)).mp ⟨a, rfl⟩ i
  have hb' := (hrange (f b)).mp ⟨b, rfl⟩ i
  rw [he, map_mul, map_mul, ← hb'] at ha
  exact mul_left_cancel₀
    ((map_ne_zero_iff _ (hα i)).mpr ((map_ne_zero_iff _ hf).mpr hb)) ha

theorem b54_normal_of_ring_retraction (i : R →+* T) (ρ : T →+* R)
    (hρ : Function.LeftInverse ρ i) [IsIntegrallyClosed T] : IsIntegrallyClosed R := by
  apply b54_normal_of_division_closed_range i hρ.injective
  intro a b y hb he
  refine ⟨ρ y, ?_⟩
  have h : a = b * ρ y := by
    have hh := congrArg ρ he
    simpa only [map_mul, hρ a, hρ b] using hh
  apply mul_left_cancel₀ ((map_ne_zero_iff _ hρ.injective).mpr hb)
  rw [← map_mul, ← h, he]

end HodgeLean.Foundations.Program
