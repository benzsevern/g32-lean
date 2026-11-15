import HodgeLean.Foundations.Program.MilneTensorSubstitution

noncomputable section
namespace HodgeLean.Foundations.Program

theorem m1b_polynomial_uniform_denominator {A R S σ X : Type*}
    [CommRing A] [CommRing R] [CommRing S] (f : A →+* R) (e : X → R →+* S)
    (a : R) (v : σ → X → S)
    (hv : ∀ i, ∃ k : ℕ, ∃ b : R, ∀ x, e x a ^ k * v i x = e x b)
    (p : MvPolynomial σ A) :
    ∃ k : ℕ, ∃ b : R, ∀ x,
      e x a ^ k * MvPolynomial.eval₂Hom ((e x).comp f) (fun i => v i x) p = e x b := by
  let g : R →+* (X → S) := RingHom.pi e
  have hv' : ∀ i, ∃ k : ℕ, ∃ b : R, g a ^ k * v i = g b := by
    intro i
    obtain ⟨k, b, h⟩ := hv i
    exact ⟨k, b, funext h⟩
  obtain ⟨k, b, h⟩ := m1b_polynomial_pivot_denominator f g a v hv' p
  refine ⟨k, b, ?_⟩
  intro x
  have heval : (MvPolynomial.eval₂Hom (g.comp f) v p) x =
      MvPolynomial.eval₂Hom ((e x).comp f) (fun i => v i x) p := by
    exact MvPolynomial.map_eval₂Hom (g.comp f) v (Pi.evalRingHom (fun _ : X => S) x) p
  have hx := congrFun h x
  change e x a ^ k * (MvPolynomial.eval₂Hom (g.comp f) v p) x = e x b at hx
  rwa [heval] at hx

theorem m1b_polynomial_chart_denominator {σ τ : Type*}
    (a : MvPolynomial τ ℂ) (v : σ → (τ → ℂ) → ℂ)
    (hv : ∀ i, ∃ k : ℕ, ∃ b : MvPolynomial τ ℂ, ∀ x,
      MvPolynomial.eval x a ≠ 0 →
        MvPolynomial.eval x a ^ k * v i x = MvPolynomial.eval x b)
    (p : MvPolynomial σ ℂ) :
    ∃ k : ℕ, ∃ b : MvPolynomial τ ℂ, ∀ x,
      MvPolynomial.eval x a ≠ 0 →
        MvPolynomial.eval x a ^ k * MvPolynomial.eval (fun i => v i x) p =
          MvPolynomial.eval x b := by
  let X := {x : τ → ℂ // MvPolynomial.eval x a ≠ 0}
  obtain ⟨k, b, hb⟩ := m1b_polynomial_uniform_denominator MvPolynomial.C
    (fun x : X => MvPolynomial.eval x.val) a (fun i x => v i x.val)
    (by
      intro i
      obtain ⟨k, b, h⟩ := hv i
      exact ⟨k, b, fun x => h x.val x.property⟩) p
  refine ⟨k, b, ?_⟩
  intro x hx
  have h := hb ⟨x, hx⟩
  have he : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℂ := by
    ext c
    exact MvPolynomial.eval_C c
  change MvPolynomial.eval x a ^ k *
    MvPolynomial.eval₂Hom ((MvPolynomial.eval x).comp MvPolynomial.C)
      (fun i => v i x) p = MvPolynomial.eval x b at h
  rw [he] at h
  exact h

theorem m1b_polynomial_affine_pivot_chart {σ τ : Type*}
    (a : MvPolynomial τ ℂ) (u v : σ → MvPolynomial τ ℂ)
    (p : MvPolynomial σ ℂ) :
    ∃ k : ℕ, ∃ b : MvPolynomial τ ℂ, ∀ x,
      MvPolynomial.eval x a ≠ 0 →
        MvPolynomial.eval x a ^ k * MvPolynomial.eval
          (fun i => MvPolynomial.eval x (u i) +
            MvPolynomial.eval x (v i) / MvPolynomial.eval x a) p =
          MvPolynomial.eval x b := by
  apply m1b_polynomial_chart_denominator
  intro i
  refine ⟨1, a * u i + v i, ?_⟩
  intro x hx
  simp only [pow_one, map_add, map_mul]
  field_simp

end HodgeLean.Foundations.Program
