import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Adic scalar change from a base ideal to its actual extension -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Relative adic modules and adic rings for the extended ideal have the same finite coordinates.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
def s2e_adic_scalar_change_equiv
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] (I : Ideal R) :
    AdicCompletion I B ≃ₗ[R] AdicCompletion (I.map (algebraMap R B)) B := by
  let J := I.map (algebraMap R B)
  have hfiltration (n : ℕ) : (I ^ n • ⊤ : Submodule R B) =
      (J ^ n • ⊤ : Submodule B B).restrictScalars R := by
    simp [J, Ideal.smul_top_eq_map, Ideal.map_pow]
  let e (n : ℕ) : (B ⧸ (I ^ n • ⊤ : Submodule R B)) ≃ₗ[R]
      (B ⧸ (J ^ n • ⊤ : Submodule B B)) :=
    (Submodule.quotEquivOfEq _ _ (hfiltration n)).trans
      (Submodule.Quotient.restrictScalarsEquiv R (J ^ n • ⊤ : Submodule B B))
  have heval (n : ℕ) (b : B) :
      e n (Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R B)) b) =
        Submodule.Quotient.mk (p := (J ^ n • ⊤ : Submodule B B)) b := by
    simp only [e, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
      Submodule.Quotient.restrictScalarsEquiv_mk]
  have hcompat {m n : ℕ} (hmn : m ≤ n) (z : B ⧸ (I ^ n • ⊤ : Submodule R B)) :
      AdicCompletion.transitionMap J B hmn (e n z) =
        e m (AdicCompletion.transitionMap I B hmn z) := by
    refine Quotient.inductionOn' z (fun b => ?_)
    change AdicCompletion.transitionMap J B hmn
      (e n (Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R B)) b)) = _
    rw [heval]
    change Submodule.Quotient.mk (p := (J ^ m • ⊤ : Submodule B B)) b =
      e m (Submodule.Quotient.mk (p := (I ^ m • ⊤ : Submodule R B)) b)
    exact (heval m b).symm
  exact
    { toFun := fun x => ⟨fun n => e n (x.val n), fun hmn =>
        (hcompat hmn (x.val _)).trans (congrArg (e _) (x.property hmn))⟩
      invFun := fun y => ⟨fun n => (e n).symm (y.val n), fun hmn => by
        apply (e _).injective
        rw [← hcompat, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, y.property hmn]⟩
      left_inv := fun x => AdicCompletion.ext (fun n => (e n).symm_apply_apply (x.val n))
      right_inv := fun y => AdicCompletion.ext (fun n => (e n).apply_symm_apply (y.val n))
      map_add' := fun x y => AdicCompletion.ext (fun n => (e n).map_add (x.val n) (y.val n))
      map_smul' := fun c x => AdicCompletion.ext (fun n => (e n).map_smul c (x.val n)) }

#print axioms s2e_adic_scalar_change_equiv
end HodgeLean.Foundations.Program
