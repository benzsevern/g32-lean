import HodgeLean.Foundations.Program.G32Native.PairedC3BlowupAffineReesCharts
import HodgeLean.Foundations.Program.G32Native.PairedC3SuppliedAffineRegularChart
import HodgeLean.Foundations.Program.G32Native.PairedC3DenominatorChartSequence

/-! # Regular total-transform charts for a coordinate centre and slice -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry RingTheory.Sequence
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- A slice cut by distinct étale coordinates has regular total-transform
equations on both actual charts of the blow-up of the first two coordinates.
Source: Hartshorne, Algebraic Geometry, II.5, II.7.13–II.7.14 and II.8. -/
theorem paired_c3_coordinate_blowup_regular_charts
    (B X : Over (Spec ↧ℂ)) (p : X ⟶ B) (K I : B.left.IdealSheafData)
    (hcartier : ∀ z : X.left, ∃ V : X.left.affineOpens, z ∈ V.1 ∧
      Nonempty (((K.comap p.left).ideal V) ≃ₗ[Γ(X.left, V)] Γ(X.left, V)))
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ z : T.left, ∃ V : T.left.affineOpens, z ∈ V.1 ∧
        Nonempty (((K.comap f.left).ideal V) ≃ₗ[Γ(T.left, V)] Γ(T.left, V))) →
      ∃! j : T ⟶ X, j ≫ p = f)
    (U : B.left.affineOpens) {σ : Type} [DecidableEq σ]
    (F : MvPolynomial σ ℂ →+* Γ(B.left, U.1)) (hF : F.Etale)
    (k : ℕ) (hk : 0 < k) (e : Fin (k + 1) ↪ σ)
    (hK : K.ideal U = Ideal.span
      {F (MvPolynomial.X (e ⟨1, by omega⟩)), F (MvPolynomial.X (e 0))})
    (hI : I.ideal U = Ideal.span
      (Set.range (fun j : Fin k => F (MvPolynomial.X (e j.succ))))) :
    ∀ y : X.left, p.left y ∈ U.1 →
      ∃ (A : CommRingCat.{0}) (j : Spec A ⟶ X.left) (_ : IsOpenImmersion j),
        y ∈ j.opensRange ∧
        ∃ f : Fin k → A, IsWeaklyRegular A (List.ofFn f) ∧
          Ideal.map (Scheme.ΓSpecIso A).hom.hom
            (((I.comap p.left).comap j).ideal ⟨⊤, isAffineOpen_top _⟩) =
            Ideal.span (Set.range f) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  let a := e (0 : Fin (n + 1)).succ
  let b := e 0
  let w := F (MvPolynomial.X a)
  let v := F (MvPolynomial.X b)
  have hab : a ≠ b := by
    intro h
    have h' := congrArg (fun j : Fin (n + 1 + 1) => j.val) (e.injective h)
    simp only [Fin.val_succ, Fin.val_zero] at h'
    omega
  letI : Algebra (MvPolynomial σ ℂ) Γ(B.left, U.1) := F.toAlgebra
  letI : Algebra.Etale (MvPolynomial σ ℂ) Γ(B.left, U.1) := hF
  obtain ⟨hb, ha⟩ := s2v_l1b_polynomial_coordinate_pair (k := ℂ) a b hab
  have hpair := s2v_l1b_regular_pair_flat (A := Γ(B.left, U.1))
    (MvPolynomial.X a) (MvPolynomial.X b) hb ha
  change IsRegular v ∧ IsRegular (Ideal.Quotient.mk (Ideal.span {v}) w) at hpair
  obtain ⟨ha', hb'⟩ := s2v_l1b_polynomial_coordinate_pair (k := ℂ) b a hab.symm
  have hpair' := s2v_l1b_regular_pair_flat (A := Γ(B.left, U.1))
    (MvPolynomial.X b) (MvPolynomial.X a) ha' hb'
  change IsRegular w ∧ IsRegular (Ideal.Quotient.mk (Ideal.span {w}) v) at hpair'
  obtain ⟨V₁, V₂, h₁, h₂, s, t, hcover, hrel₁, hrel₂, hs₁, hk₁, hs₂, hk₂⟩ :=
    paired_c3_blowup_affine_rees_charts B X p K hcartier hblowup U w v hK
      hpair.1 hpair.2 hpair'.1 hpair'.2
  intro y hy
  have hy' : y ∈ V₁.1 ⊔ V₂.1 := by rw [hcover]; exact hy
  rcases TopologicalSpace.Opens.mem_sup.mp hy' with hy₁ | hy₂
  · have hw : w - 0 * v = algebraMap (MvPolynomial σ ℂ) Γ(B.left, U.1)
        (MvPolynomial.X (e (0 : Fin (n + 1)).succ)) := by
      rw [zero_mul, sub_zero]
      rfl
    have hvcoord : v = algebraMap (MvPolynomial σ ℂ) Γ(B.left, U.1)
        (MvPolynomial.X (e 0)) := rfl
    exact paired_c3_supplied_affine_regular_chart (K := ℂ) (σ := σ) (n := n)
      p.left I U V₁ h₁ y hy₁ w v 0 s hs₁ hk₁ e hw hvcoord hI
  · let f₂ := (p.left.appLE U.1 V₂.1 h₂).hom
    let q : Fin (n + 1) ↪ σ := ⟨fun j => e j.succ,
      fun _ _ h => Fin.succ_injective _ (e.injective h)⟩
    have hbq : b ∉ Set.range q := by
      rintro ⟨j, hj⟩
      have h := congrArg (fun j : Fin (n + 1 + 1) => j.val) (e.injective hj)
      simp only [Fin.val_succ, Fin.val_zero] at h
      omega
    have hr := paired_c3_supplied_unchanged_sequence (K := ℂ) (σ := σ) (n := n + 1) f₂ b a hab.symm t hs₂ hk₂ q hbq
    apply paired_c3_affine_regular_chart (I.comap p.left) V₂ y hy₂
      (fun j : Fin (n + 1) => f₂ (F (MvPolynomial.X (e j.succ)))) hr
    rw [s2e_c1_affine_comap_appLE p.left I U V₂ h₂, hI, Ideal.map_span, ← Set.range_comp]
    rfl

#print axioms paired_c3_coordinate_blowup_regular_charts
end HodgeLean.Foundations.Program.G32Native
