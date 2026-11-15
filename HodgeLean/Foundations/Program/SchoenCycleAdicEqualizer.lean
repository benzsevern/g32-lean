import Mathlib.RingTheory.AdicCompletion.Exactness

/-! # Finite equalizers and adic limits -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
universe u
namespace HodgeLean.Foundations.Program

/-- Adic completion preserves an exact pair with injective first map between finite
modules over a Noetherian ring, without surjectivity of the second map.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10,
Proposition 10.12; Mathlib, AdicCompletion.map_exact and AdicCompletion.map_injective. -/
theorem s2e_adic_map_exact_of_injective
    {R M N P : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    [Module.Finite R N] [Module.Finite R P]
    (I : Ideal R) (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (hfg : Function.Exact f g) :
    Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) := by
  have he : Function.Exact f g.rangeRestrict :=
    (Submodule.injective_subtype g.range).comp_exact_iff_exact.mp
      (by simpa only [LinearMap.subtype_comp_rangeRestrict] using hfg)
  have hc := AdicCompletion.map_exact (I := I) hf he g.surjective_rangeRestrict
  have hi := AdicCompletion.map_injective I (Submodule.injective_subtype g.range)
  have h := hi.comp_exact_iff_exact.mpr hc
  simpa only [AdicCompletion.map_comp, LinearMap.subtype_comp_rangeRestrict] using h

#print axioms s2e_adic_map_exact_of_injective

/-- Finite simultaneous fixed points commute with adic completion for finite modules
when the original fixed points are the image of an injective linear map.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10,
Proposition 10.12; the equalizer is the kernel of the finite family of differences. -/
theorem s2e_adic_finite_fixed_points
    {R M N ι : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Finite R N] [Fintype ι]
    (I : Ideal R) (f : M →ₗ[R] N) (a : ι → N →ₗ[R] N)
    (hf : Function.Injective f) (hfix : ∀ i y, a i (f y) = f y)
    (hdesc : ∀ x, (∀ i, a i x = x) → ∃ y, f y = x)
    (x : AdicCompletion I N) :
    (∀ i, AdicCompletion.map I (a i) x = x) ↔
      ∃! y, AdicCompletion.map I f y = x := by
  classical
  let g : N →ₗ[R] (ι → N) := LinearMap.pi (fun i => a i - LinearMap.id)
  have hg (z : N) : g z = 0 ↔ ∀ i, a i z = z := by
    constructor
    · intro h i
      exact sub_eq_zero.mp (congrFun h i)
    · intro h
      funext i
      exact sub_eq_zero.mpr (h i)
  have hfg : Function.Exact f g := by
    intro z
    rw [hg]
    constructor
    · exact hdesc z
    · rintro ⟨y, rfl⟩ i
      exact hfix i y
  have he := s2e_adic_map_exact_of_injective I f g hf hfg
  have hproj (i : ι) : (LinearMap.proj i).comp g = a i - LinearMap.id := by
    ext z
    rfl
  have hker : AdicCompletion.map I g x = 0 ↔
      ∀ i, AdicCompletion.map I (a i) x = x := by
    constructor
    · intro h i
      have h0 : AdicCompletion.map I (a i - LinearMap.id) x = 0 := by
        rw [← hproj i, ← AdicCompletion.map_comp_apply, h, map_zero]
      have h1 : AdicCompletion.map I (a i) x - x = 0 := by
        simpa only [map_sub, LinearMap.sub_apply, AdicCompletion.map_id,
          LinearMap.id_apply] using h0
      exact sub_eq_zero.mp h1
    · intro h
      apply (AdicCompletion.piEquivOfFintype I (fun _ : ι => N)).injective
      rw [map_zero, AdicCompletion.piEquivOfFintype_apply]
      apply funext
      intro i
      change AdicCompletion.map I (LinearMap.proj i) (AdicCompletion.map I g x) = 0
      rw [AdicCompletion.map_comp_apply, hproj, map_sub, AdicCompletion.map_id]
      change AdicCompletion.map I (a i) x - x = 0
      exact sub_eq_zero.mpr (h i)
  constructor
  · intro h
    obtain ⟨y, hy⟩ := (he x).mp (hker.mpr h)
    refine ⟨y, hy, ?_⟩
    intro z hz
    exact AdicCompletion.map_injective I hf (hz.trans hy.symm)
  · rintro ⟨y, hy, _⟩
    exact hker.mp ((he x).mpr ⟨y, hy⟩)

#print axioms s2e_adic_finite_fixed_points
end HodgeLean.Foundations.Program
