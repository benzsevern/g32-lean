import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFaceRootFamily

/-! Exact normalized root enumeration passes to every actual intrinsic open base face. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_face_root_enumeration {n q : ℕ}
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (C : Fin q → Set (EuclideanSpace ℝ (Fin n)))
    (r : Fin q → ℕ) (ψ : (j : Fin q) → Fin (r j) → C j → ℝ)
    (Q : Polynomial (MvPolynomial (Fin n) ℝ))
    (hcover : ∀ j (x : C j) z,
      Q.eval₂ (MvPolynomial.eval (fun i => x.val i)) z = 0 ↔ ∃ a, z = ψ j a x)
    (parent : L.faces → Fin q)
    (hp : ∀ (s : L.faces) (x : EuclideanSpace ℝ (Fin n)),
      x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) → β x ∈ C (parent s))
    (f : (s : L.faces) → Fin (r (parent s)) → EuclideanSpace ℝ (Fin n) → ℝ)
    (hagree : ∀ (s : L.faces) (a : Fin (r (parent s))) (x : EuclideanSpace ℝ (Fin n))
      (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))))),
      f s a x = ψ (parent s) a ⟨β x, hp s x hx⟩) :
    ∀ (s : L.faces) (x : EuclideanSpace ℝ (Fin n)),
      x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) →
      ∀ z, Q.eval₂ (MvPolynomial.eval (fun i => β x i)) z = 0 ↔ ∃ a, z = f s a x := by
  intro s x hx z
  rw [hcover (parent s) ⟨β x, hp s x hx⟩ z]
  apply exists_congr
  intro a
  rw [hagree s a x hx]

end HodgeLean.Foundations.Program
