import HodgeLean.Foundations.Program.RigidStartingSystemPathUnits

noncomputable section
open Set
namespace HodgeLean.Foundations.Program

theorem b65r_regular_monodromy (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (U : Set ℂ) (hU : IsOpen U)
    (A : ℂ → E →L[ℂ] E) (hA : AnalyticOnNhd ℂ A U) (x : U) :
    ∃ M : FundamentalGroup U x →* (E →L[ℂ] E)ˣ,
      ∀ p : Path x x, (M (FundamentalGroup.fromPath ⟦p⟧)).val =
        b65f_transport E A (fun t ↦ (p.extend t).val) := by
  let t := fun p : Path x x ↦ b65r_pathUnit E U hU A hA p
  have ht (p : Path x x) : (t p).val =
      b65f_transport E A (fun s ↦ (p.extend s).val) := b65r_pathUnit_val E U hU A hA p
  let q : Path.Homotopic.Quotient x x → (E →L[ℂ] E)ˣ := Quotient.lift t (by
    intro p p' h
    apply Units.ext
    rw [ht,ht]
    exact b65f_homotopy_invariance E U hU A hA x x p p' h)
  have hq (p : Path x x) : q ⟦p⟧ = t p := rfl
  let M : FundamentalGroup U x →* (E →L[ℂ] E)ˣ := {
    toFun := fun p ↦ q p.toPath
    map_one' := by
      change q ⟦Path.refl x⟧ = 1
      rw [hq]
      apply Units.ext
      rw [ht]
      simpa only [Path.refl_extend,ContinuousMap.const_apply,Units.val_one] using
        b65r_transport_constant E A x.val
    map_mul' := by
      intro p p'
      change q (p'.toPath.trans p.toPath) = q p.toPath*q p'.toPath
      induction p.toPath using Path.Homotopic.Quotient.ind with
      | mk γ =>
        induction p'.toPath using Path.Homotopic.Quotient.ind with
        | mk δ =>
          change t (δ.trans γ) = t γ*t δ
          exact b65r_pathUnit_trans E U hU A hA δ γ }
  exact ⟨M,ht⟩

end HodgeLean.Foundations.Program
