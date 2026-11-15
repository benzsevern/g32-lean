import HodgeLean.Foundations.Program.G32Native.PairedC3SuppliedChartFrame

/-! # Actual ideal generators in an adapted supplied chart -/
noncomputable section
set_option maxHeartbeats 200000
open Polynomial RingTheory.Sequence
namespace HodgeLean.Foundations.Program.G32Native

/-- Labelled adapted coordinates give a finite regular generating family
for the image of the slice ideal in the supplied Rees chart.
Source: Hartshorne, Algebraic Geometry, II.7.13 and II.8. -/
theorem paired_c3_adapted_chart_generators
    {K A B σ : Type} [CommRing K] [CommRing A] [CommRing B] [DecidableEq σ]
    [Algebra (MvPolynomial σ K) A] [Algebra.Etale (MvPolynomial σ K) A]
    (f : A →+* B) (u v c : A) (s : B)
    (hsurj : Function.Surjective (eval₂RingHom f s))
    (hker : RingHom.ker (eval₂RingHom f s) = Ideal.span {C u - X * C v})
    {n : ℕ} (e : Fin (n + 2) ↪ σ)
    (hu : u - c * v = algebraMap (MvPolynomial σ K) A
      (MvPolynomial.X (e (0 : Fin (n + 1)).succ)))
    (hv : v = algebraMap (MvPolynomial σ K) A (MvPolynomial.X (e 0)))
    (I : Ideal A)
    (hI : I = Ideal.span (Set.range (fun j : Fin (n + 1) =>
      algebraMap (MvPolynomial σ K) A (MvPolynomial.X (e j.succ))))) :
    ∃ z : Fin (n + 1) → B,
      IsWeaklyRegular B (List.ofFn z) ∧ Ideal.map f I = Ideal.span (Set.range z) := by
  let t : Fin n ↪ σ :=
    ⟨fun j => e j.succ.succ, fun i j hij => Fin.succ_injective _
      (Fin.succ_injective _ (e.injective hij))⟩
  have ha : e (0 : Fin (n + 1)).succ ∉ Set.range t := by
    rintro ⟨j, hj⟩
    have h := e.injective hj
    have hv := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_zero] at hv
    omega
  have hb : e 0 ∉ Set.range t := by
    rintro ⟨j, hj⟩
    have h := e.injective hj
    have hv := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_zero] at hv
    omega
  have hab : e (0 : Fin (n + 1)).succ ≠ e 0 := by
    intro h
    have h' := congrArg Fin.val (e.injective h)
    simp only [Fin.val_succ, Fin.val_zero] at h'
    omega
  let z : Fin (n + 1) → B := Fin.append
    (fun j => f (algebraMap (MvPolynomial σ K) A (MvPolynomial.X (t j))))
    (fun _ : Fin 1 => f (u - c * v))
  refine ⟨z, paired_c3_supplied_chart_finite_sequence f u v c s hsurj hker
    _ _ hab hu hv t ha hb, ?_⟩
  rw [hI, Ideal.map_span, ← Set.range_comp]
  congr 1
  ext b
  simp only [Set.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨j, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · exact ⟨Fin.natAdd n 0, by simp only [z, Fin.append_right, hu]⟩
    · exact ⟨Fin.castAdd 1 j, by simp only [z, Fin.append_left]; rfl⟩
  · rintro ⟨j, rfl⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · exact ⟨j.succ, by simp only [z, Fin.append_left]; rfl⟩
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact ⟨0, by simp only [z, Fin.append_right, hu]⟩

#print axioms paired_c3_adapted_chart_generators
end HodgeLean.Foundations.Program.G32Native
