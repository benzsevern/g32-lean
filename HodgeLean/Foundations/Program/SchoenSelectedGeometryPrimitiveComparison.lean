import HodgeLean.Foundations.Program.SchoenSelectedGeometryRanks

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s0_equivariant_primitive_lift
    {P J Y A : Type*} [AddCommGroup P] [Module ℚ P]
    [AddCommGroup J] [Module ℚ J] [AddCommGroup Y] [Module ℚ Y]
    (V : Submodule ℚ Y) (p : P →ₗ[ℚ] J) (q : Y →ₗ[ℚ] J)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hr : LinearMap.range (q.comp V.subtype) = LinearMap.range p)
    (ρP : A → Module.End ℚ P) (ρJ : A → Module.End ℚ J) (ρY : A → Module.End ℚ Y)
    (heP : ∀ a, p ∘ₗ ρP a = ρJ a ∘ₗ p)
    (heY : ∀ a, q ∘ₗ ρY a = ρJ a ∘ₗ q) :
    ∃ E : P ≃ₗ[ℚ] V,
      (∀ v, q (E v) = p v) ∧
      ∀ a v, ρY a (E v) = (E (ρP a v) : Y) := by
  let qV := q.comp V.subtype
  let qP : V →ₗ[ℚ] LinearMap.range p := qV.codRestrict _ (fun v ↦ by
    rw [← hr]
    exact LinearMap.mem_range_self qV v)
  have hqP : Function.Bijective qP := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply hq
      exact congrArg Subtype.val h
    · intro y
      have hy : y.val ∈ LinearMap.range qV := by rw [hr]; exact y.property
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩
  let Q := LinearEquiv.ofBijective qP hqP
  let R := LinearEquiv.ofInjective p hp
  let E := R.trans Q.symm
  have hE (v : P) : q (E v) = p v := by
    exact congrArg Subtype.val (Q.apply_symm_apply (R v))
  refine ⟨E, hE, ?_⟩
  intro a v
  apply hq
  calc
    q (ρY a (E v)) = ρJ a (q (E v)) := LinearMap.congr_fun (heY a) (E v)
    _ = ρJ a (p v) := by rw [hE]
    _ = p (ρP a v) := (LinearMap.congr_fun (heP a) v).symm
    _ = q (E (ρP a v)) := (hE _).symm

#print axioms s0_equivariant_primitive_lift

end HodgeLean.Foundations.Program
