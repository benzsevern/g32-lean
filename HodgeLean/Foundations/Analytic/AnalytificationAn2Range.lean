import HodgeLean.Foundations.Analytic.AnalytificationAn2Embedding

noncomputable section

open Set

namespace HodgeLean.Foundations.Analytic

set_option maxHeartbeats 400000 in
theorem AnalytificationAn2_range_coordinates
    {A : Type} [CommRing A] [Algebra ℂ A] {ι κ : Type}
    (c : ι → A) (q : κ → MvPolynomial ι ℂ)
    (hgen : ∀ a : A, ∃ p : MvPolynomial ι ℂ,
      ∀ φ : A →ₐ[ℂ] ℂ, φ a = MvPolynomial.eval (fun i ↦ φ (c i)) p)
    (hrel : ∀ p : MvPolynomial ι ℂ,
      (∀ φ : A →ₐ[ℂ] ℂ, MvPolynomial.eval (fun i ↦ φ (c i)) p = 0) ↔
        p ∈ Ideal.span (range q)) :
    range (fun φ : A →ₐ[ℂ] ℂ ↦ fun i ↦ φ (c i)) =
      {w : ι → ℂ | ∀ j, MvPolynomial.eval w (q j) = 0} := by
  ext w
  constructor
  · rintro ⟨φ, rfl⟩ j
    exact (hrel (q j)).2 (Ideal.subset_span (mem_range_self j)) φ
  · intro hw
    let ev : MvPolynomial ι ℂ →+* ℂ := MvPolynomial.eval₂Hom (RingHom.id ℂ) w
    have hev (p : MvPolynomial ι ℂ) : ev p = MvPolynomial.eval w p := by simp [ev]
    have hspan : Ideal.span (range q) ≤ RingHom.ker ev := by
      apply Ideal.span_le.2
      rintro p ⟨j, rfl⟩
      change ev (q j) = 0
      rw [hev]
      exact hw j
    choose rep hrep using hgen
    have hrep_eq (a : A) (p : MvPolynomial ι ℂ)
        (hp : ∀ φ : A →ₐ[ℂ] ℂ,
          φ a = MvPolynomial.eval (fun i ↦ φ (c i)) p) :
        MvPolynomial.eval w (rep a) = MvPolynomial.eval w p := by
      have hd : rep a - p ∈ Ideal.span (range q) := (hrel (rep a - p)).1 fun φ ↦ by
        rw [map_sub, ← hrep a φ, ← hp φ, sub_self]
      have hk := hspan hd
      change ev (rep a - p) = 0 at hk
      rw [map_sub, hev, hev, sub_eq_zero] at hk
      exact hk
    let ψ : A →ₐ[ℂ] ℂ :=
      { toFun := fun a ↦ MvPolynomial.eval w (rep a)
        map_one' := (hrep_eq 1 1 (fun φ ↦ by simp)).trans (by simp)
        map_mul' := fun a b ↦ by
          rw [hrep_eq (a * b) (rep a * rep b)]
          · simp
          · intro φ
            rw [map_mul, hrep a φ, hrep b φ, map_mul]
        map_zero' := (hrep_eq 0 0 (fun φ ↦ by simp)).trans (by simp)
        map_add' := fun a b ↦ by
          rw [hrep_eq (a + b) (rep a + rep b)]
          · simp
          · intro φ
            rw [map_add, hrep a φ, hrep b φ, map_add]
        commutes' := fun z ↦ by
          rw [hrep_eq (algebraMap ℂ A z) (MvPolynomial.C z)]
          · simp
          · intro φ
            simp }
    refine ⟨ψ, ?_⟩
    funext i
    change MvPolynomial.eval w (rep (c i)) = w i
    rw [hrep_eq (c i) (MvPolynomial.X i)]
    · simp
    · intro φ
      simp

end HodgeLean.Foundations.Analytic
