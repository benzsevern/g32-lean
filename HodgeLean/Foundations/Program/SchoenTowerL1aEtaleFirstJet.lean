import HodgeLean.Foundations.Program.SchoenTowerL1aSquareZeroJets
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.Algebra.MvPolynomial.Eval

/-! # Nonzero first-order classes of etale curve coordinates

Formal smoothness lifts the coordinate tangent direction to dual numbers.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
/-- An etale one-variable coordinate has a nonzero first-order class at every rational point.
Source: Hartshorne, Algebraic Geometry, II.8 and III.10, dual numbers and the infinitesimal lifting property. -/
theorem s2v_l1a_etale_coordinate_first_jet
    {K A : Type} [Field K] [CommRing A] [Algebra K A]
    (g : MvPolynomial (Fin 1) K →ₐ[K] A) (hg : g.toRingHom.Etale)
    (ev : A →ₐ[K] K) :
    let r := g (MvPolynomial.X 0) - algebraMap K A (ev (g (MvPolynomial.X 0)))
    r ∈ RingHom.ker ev.toRingHom ∧ r ∉ RingHom.ker ev.toRingHom ^ 2 := by
  let P := MvPolynomial (Fin 1) K
  let B := TrivSqZeroExt K K
  let c := ev (g (MvPolynomial.X 0))
  let b : P →+* B := MvPolynomial.eval₂Hom (TrivSqZeroExt.inlHom K K)
    (fun _ : Fin 1 => ⟨c, 1⟩)
  letI : Algebra P A := g.toRingHom.toAlgebra
  letI : Algebra P K := (ev.toRingHom.comp g.toRingHom).toAlgebra
  letI : Algebra P B := b.toAlgebra
  have : Algebra.Etale P A := hg
  have hbase : (TrivSqZeroExt.fstHom K K K).toRingHom.comp b =
      ev.toRingHom.comp g.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro k
      simp [b, P, B, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp [b, P, B, c, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
  let e : A →ₐ[P] K := { ev.toRingHom with commutes' := fun _ => rfl }
  let π : B →ₐ[P] K :=
    { (TrivSqZeroExt.fstHom K K K).toRingHom with
      commutes' := fun p => DFunLike.congr_fun hbase p }
  have hπ : Function.Surjective π := fun k => ⟨TrivSqZeroExt.inl k, rfl⟩
  have hnπ : IsNilpotent (RingHom.ker π.toRingHom) :=
    ⟨2, TrivSqZeroExt.kerIdeal_sq K K⟩
  let l := Algebra.FormallySmooth.liftOfSurjective e π hπ hnπ
  have hl : (TrivSqZeroExt.fstHom K K K).toRingHom.comp l.toRingHom = ev.toRingHom := by
    apply RingHom.ext
    exact Algebra.FormallySmooth.liftOfSurjective_apply e π hπ hnπ
  have ht : l (g (MvPolynomial.X 0)) = b (MvPolynomial.X 0) := l.commutes _
  have hc : l (algebraMap K A c) = TrivSqZeroExt.inl c := by
    have H := l.commutes (MvPolynomial.C c)
    change l (g (MvPolynomial.C c)) = b (MvPolynomial.C c) at H
    simpa [b, P, B, MvPolynomial.eval₂Hom_C] using H
  apply s2v_l1a_square_zero_detects_first_jet ev.toRingHom l.toRingHom hl
  · simp [c]
  · change (l (g (MvPolynomial.X 0) - algebraMap K A c)).snd ≠ 0
    rw [map_sub, ht, hc]
    simp [b, P, B, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']

end HodgeLean.Foundations.Program
