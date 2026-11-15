import HodgeLean.Foundations.Program.SchoenTowerL1bAdicLifting

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A formally smooth coefficient algebra lifts from the residue quotient
into the adic ring, retaining its specified residue map. -/
theorem s2v_l1b_adic_coefficient_lift
    {k B R : Type*} [CommRing k] [CommRing B] [CommRing R]
    [Algebra k B] [Algebra k R] [Algebra.FormallySmooth k B]
    (I : Ideal R) (f : B →ₐ[k] R ⧸ I) :
    ∃ g : B →ₐ[k] AdicCompletion I R,
      ((AdicCompletion.evalOneₐ I).restrictScalars k).comp g = f := by
  classical
  let b : ∀ n : ℕ, B →ₐ[k] R ⧸ I ^ (n + 1) :=
    Nat.rec (((Ideal.quotientEquivAlgOfEq k (pow_one I).symm).toAlgHom).comp f)
      (fun n v => (s2v_l1b_adic_lift_successor I (n + 1) (by omega) v).choose)
  have hb (n : ℕ) :
      (Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (n + 1).le_succ)).comp
        (b (n + 1)) = b n := by
    exact (s2v_l1b_adic_lift_successor I (n + 1) (by omega) (b n)).choose_spec
  letI : Subsingleton (R ⧸ I ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
  let ff : ∀ n : ℕ, B →ₐ[k] R ⧸ I ^ n
    | 0 => default
    | n + 1 => b n
  have hs (n : ℕ) (x : B) :
      ff n x = Ideal.Quotient.factorPow I n.le_succ (ff (n + 1) x) := by
    cases n with
    | zero => exact Subsingleton.elim _ _
    | succ n => exact (congrArg (fun h => h x) (hb n)).symm
  have hf {m n : ℕ} (h : m ≤ n) :
      (Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right h)).comp (ff n) = ff m := by
    ext x
    exact (Ideal.Quotient.eq_factor_of_eq_factor_succ
      (fun a b h => Ideal.pow_le_pow_right h) (fun n => ff n x) (fun n => hs n x) h).symm
  refine ⟨AdicCompletion.liftAlgHom I ff (fun h => hf h), ?_⟩
  ext x
  rw [AlgHom.comp_apply]
  change AdicCompletion.evalOneₐ I (AdicCompletion.liftAlgHom I ff (fun h => hf h) x) = f x
  rw [AdicCompletion.evalOneₐ_liftAlgHom]
  change Ideal.Quotient.factorₐ k (by simp) (b 0 x) = f x
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (f x)
  change Ideal.Quotient.factorₐ k (by simp)
    ((Ideal.quotientEquivAlgOfEq k (pow_one I).symm) (f x)) = f x
  rw [← hr]
  rfl

end HodgeLean.Foundations.Program
