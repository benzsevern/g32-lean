import HodgeLean.Foundations.Program.SchoenTowerFoundB3
import HodgeLean.Foundations.Program.SchoenTowerI2aReesFields

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program

/-- A specified pair of polynomial coordinates gives the actual transverse
Rees fraction chart, retaining every other coordinate and its actual ratio.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13; Stacks Project, Tag 052Q. -/
theorem s2v_i2a_transverse_coordinate_rees_chart
    (A : Type) [CommRing A] (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    let P := MvPolynomial (Fin n) A
    let x : P := MvPolynomial.X i
    let y : P := MvPolynomial.X j
    let I : Ideal P := Ideal.span {x, y}
    ∃ e : s2t_reesChart I x ≃+* P,
      (∀ a : A, e (algebraMap P _ (MvPolynomial.C a)) = MvPolynomial.C a) ∧
      (∀ k, k ≠ j → e (algebraMap P _ (MvPolynomial.X k)) = MvPolynomial.X k) ∧
      e (algebraMap P _ y) = x * y ∧
      e (s2v_i2a_reesFraction I x ⟨y, Ideal.subset_span (by simp)⟩) = y := by
  classical
  let P := MvPolynomial (Fin n) A
  let x : P := MvPolynomial.X i
  let y : P := MvPolynomial.X j
  let I : Ideal P := Ideal.span {x, y}
  let L := Localization.Away x
  let C := s2t_reesChart I x
  let incl : P →+* L := algebraMap P L
  obtain ⟨t, ht, hyt, hsur⟩ := s2t_pairChart_coordinate P x y
  let g : P →+* C := MvPolynomial.eval₂Hom
    ((algebraMap P C).comp MvPolynomial.C)
    (fun k => if k = j then t else algebraMap P C (MvPolynomial.X k))
  have gk (k : Fin n) (hk : k ≠ j) :
      g (MvPolynomial.X k) = algebraMap P C (MvPolynomial.X k) := by
    simp [MvPolynomial.eval₂Hom, g, hk]
  have gx : g x = algebraMap P C x := gk i hij
  have gy : g y = t := by simp [MvPolynomial.eval₂Hom, g, y]
  have gc (a : A) : g (MvPolynomial.C a) = algebraMap P C (MvPolynomial.C a) := by
    simp [MvPolynomial.eval₂Hom, g]
    rfl
  let b : P →+* P := MvPolynomial.eval₂Hom MvPolynomial.C
    (fun k => if k = j then x * y else MvPolynomial.X k)
  have bk (k : Fin n) (hk : k ≠ j) : b (MvPolynomial.X k) = MvPolynomial.X k := by
    simp [MvPolynomial.eval₂Hom, b, hk]
  have bx : b x = x := bk i hij
  have byy : b y = x * y := by simp [MvPolynomial.eval₂Hom, b, y]
  have gb : g.comp b = algebraMap P C := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [MvPolynomial.eval₂Hom, b]
      exact gc a
    · intro k
      change g (b (MvPolynomial.X k)) = _
      by_cases hk : k = j
      · subst k
        rw [byy, map_mul, gx, gy]
        exact hyt.symm
      · rw [bk k hk, gk k hk]
  have hg_sur : Function.Surjective g := by
    intro z
    obtain ⟨p, rfl⟩ := hsur z
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨p', hp'⟩ := hp
      obtain ⟨q', hq'⟩ := hq
      exact ⟨p' + q', by simp [hp', hq']⟩
    | monomial m a =>
      refine ⟨b a * y ^ m, ?_⟩
      rw [map_mul, map_pow, gy]
      have hba : g (b a) = algebraMap P C a := RingHom.congr_fun gb a
      rw [hba, Polynomial.aeval_monomial]
  have hu : IsUnit ((incl.comp b) x) := by
    change IsUnit (incl (b x))
    rw [bx]
    exact IsLocalization.Away.algebraMap_isUnit x
  let F : L →+* L := IsLocalization.Away.lift x hu
  have Fi (p : P) : F (incl p) = incl (b p) := IsLocalization.Away.lift_eq x hu p
  have Ft : F t.val = incl y := by
    have H := congrArg (fun z : C => F z.val) hyt
    change F (incl y) = F (incl x * t.val) at H
    rw [map_mul, Fi, Fi, bx, byy, map_mul] at H
    exact (IsLocalization.Away.algebraMap_isUnit x).mul_left_cancel H.symm
  have Fg : F.comp (C.val.toRingHom.comp g) = incl := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change F ((g (MvPolynomial.C a)).val) = incl (MvPolynomial.C a)
      rw [gc]
      change F (incl (MvPolynomial.C a)) = _
      rw [Fi]
      simp [MvPolynomial.eval₂Hom, b]
      rfl
    · intro k
      change F ((g (MvPolynomial.X k)).val) = incl (MvPolynomial.X k)
      by_cases hk : k = j
      · subst k
        rw [gy]
        exact Ft
      · rw [gk k hk]
        exact (Fi _).trans (congrArg incl (bk k hk))
  have hi : Function.Injective incl := by
    apply IsLocalization.injective L (M := Submonoid.powers x)
    rintro z ⟨m, rfl⟩
    exact (MvPolynomial.isRegular_X_pow m).mem_nonZeroDivisors
  have hg_inj : Function.Injective g := by
    intro p q hpq
    apply hi
    rw [← RingHom.congr_fun Fg p, ← RingHom.congr_fun Fg q]
    change F (g p).val = F (g q).val
    rw [hpq]
  let e := (RingEquiv.ofBijective g ⟨hg_inj, hg_sur⟩).symm
  have eg (p : P) : e (g p) = p := (RingEquiv.ofBijective g ⟨hg_inj, hg_sur⟩).symm_apply_apply p
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [← gc]
    exact eg _
  · intro k hk
    rw [← gk k hk]
    exact eg _
  · rw [hyt, map_mul, ← gx, ← gy, eg, eg]
  · have heq : s2v_i2a_reesFraction I x ⟨y, Ideal.subset_span (by simp)⟩ = t :=
      Subtype.ext ht.symm
    rw [heq, ← gy, eg]

end HodgeLean.Foundations.Program
