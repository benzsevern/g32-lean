import HodgeLean.Foundations.Program.SchoenCycleCoordinateErasureIdeals

/-! # Ideal control from polynomial coordinates and marked erasure -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Polynomial coordinates transfer marked-erasure kernel control to ideals
in arbitrary coefficient algebras.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 1 and 10. -/
theorem s2e_polynomial_erasure_ideal_control
    (C R S : Type*) [CommRing C] [CommRing R] [CommRing S] [Algebra C R] [Algebra C S]
    (n N : ℕ) (f : R →ₐ[C] S) (t : Fin (n + 1) → R) (u : Fin n → S)
    (I : Ideal R) (J : Ideal S)
    (hf : ∀ r ∈ I, f r ∈ J)
    (ht : ∀ i, f (t i) = Fin.cases 0 u i)
    (hrep : ∀ r : R, ∃ p : MvPolynomial (Fin (n + 1)) C, r - aeval t p ∈ I)
    (hR : ∀ p : MvPolynomial (Fin (n + 1)) C,
      p ∈ idealOfVars (Fin (n + 1)) C ^ N → aeval t p ∈ I)
    (hS : ∀ p : MvPolynomial (Fin n) C,
      aeval u p ∈ J → p ∈ idealOfVars (Fin n) C ^ N)
    (r : R) (hr : f r ∈ J) : r ∈ Ideal.span {t 0} ⊔ I := by
  obtain ⟨p, hp⟩ := hrep r
  have he : f.comp (aeval t) = aeval (Fin.cases 0 u) := by
    apply MvPolynomial.algHom_ext
    intro i
    change f (aeval t (X i : MvPolynomial (Fin (n + 1)) C)) =
      aeval (Fin.cases 0 u) (X i : MvPolynomial (Fin (n + 1)) C)
    rw [aeval_X, aeval_X]
    exact ht i
  have hep : f (aeval t p) = aeval u (s2e_eraseFirstCoordinate C n p) := by
    have h := congrArg (fun g : MvPolynomial (Fin (n + 1)) C →ₐ[C] S => g p) he
    exact h.trans (s2e_eraseFirstCoordinate_aeval C S n u p).symm
  have hj : f (aeval t p) ∈ J := by
    have hm := J.sub_mem hr (hf _ hp)
    simpa only [map_sub, sub_sub_cancel] using hm
  have hP : p ∈ idealOfVars (Fin (n + 1)) C ^ N ⊔ Ideal.span {(X 0 : MvPolynomial (Fin (n + 1)) C)} := by
    rw [← s2e_eraseFirstCoordinate_power_comap]
    exact hS _ (hep ▸ hj)
  obtain ⟨p₁, hp₁, p₂, hp₂, hsum⟩ := Submodule.mem_sup.mp hP
  have h₁ : aeval t p₁ ∈ Ideal.span {t 0} ⊔ I :=
    (show I ≤ Ideal.span {t 0} ⊔ I from le_sup_right) (hR p₁ hp₁)
  have h₂ : aeval t p₂ ∈ Ideal.span {t 0} ⊔ I := by
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hp₂
    apply (show Ideal.span {t 0} ≤ Ideal.span {t 0} ⊔ I from le_sup_left)
    rw [hq, map_mul, aeval_X]
    exact (Ideal.span {t 0}).mul_mem_right _ (Ideal.subset_span rfl)
  have hval : aeval t p ∈ Ideal.span {t 0} ⊔ I := by
    rw [← hsum, map_add]
    exact (Ideal.span {t 0} ⊔ I).add_mem h₁ h₂
  have hm := (Ideal.span {t 0} ⊔ I).add_mem
    ((show I ≤ Ideal.span {t 0} ⊔ I from le_sup_right) hp) hval
  simpa only [sub_add_cancel] using hm

end HodgeLean.Foundations.Program
