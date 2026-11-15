import HodgeLean.Foundations.WeilPowerHodge

/-! # The Hodge decomposition on an exterior power of a power

The pieces are spans of wedges of Hodge vectors with the prescribed total
bidegree. They span the exterior power, and the induced grading has precisely
their diagonal sum as kernel. This supplies the exterior-power Hodge-class
criterion needed in F-1575's transport. It is at the level of `⋀ H¹`, without C7
or algebraicity. HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.WeilPower
open InvariantsExterior
variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)

/-- The exterior Hodge piece of total bidegree `pq` for `V ⊗ ℚᵐ`.
Source: constructed here by the usual tensor and exterior Hodge grading;
van Geemen, An introduction to the Hodge conjecture for abelian varieties, §5–6. -/
def exteriorHodge (m k : ℕ) (pq : ℤ × ℤ) :
    Submodule ℂ (⋀[ℂ]^k (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin m → ℚ)))) :=
  Submodule.span ℂ {v | ∃ (ps : Fin k → ℤ × ℤ) (x : Fin k → ℂ ⊗[ℚ] V)
    (u : Fin k → (Fin m → ℂ)), (∀ i, x i ∈ H (ps i)) ∧ (∑ i, ps i) = pq ∧
      v = exteriorPower.ιMulti ℂ k (fun i => (powerBaseChange m).symm (x i ⊗ₜ[ℂ] u i))}

example (m k : ℕ) (ps : Fin k → ℤ × ℤ) (x : Fin k → ℂ ⊗[ℚ] V)
    (u : Fin k → (Fin m → ℂ)) (hx : ∀ i, x i ∈ H (ps i)) :
    exteriorPower.ιMulti ℂ k (fun i => (powerBaseChange m).symm (x i ⊗ₜ[ℂ] u i)) ∈
      exteriorHodge H m k (∑ i, ps i) :=
  Submodule.subset_span ⟨ps, x, u, hx, rfl, rfl⟩

include hH in
private theorem hodge_vectors_span (m : ℕ) :
    Submodule.span ℂ {z | ∃ (pq : ℤ × ℤ) (x : ℂ ⊗[ℚ] V) (u : Fin m → ℂ),
      x ∈ H pq ∧ z = (powerBaseChange m).symm (x ⊗ₜ[ℂ] u)} = ⊤ := by
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨z, rfl⟩ := (powerBaseChange (V := V) m).symm.surjective z
  induction z using TensorProduct.inductionOn with
  | tmul x u =>
    have hx : x ∈ ⨆ pq, H pq := by rw [hH.submodule_iSup_eq_top]; trivial
    induction hx using Submodule.iSup_induction' with
    | mem pq x hx => exact Submodule.subset_span ⟨pq, x, u, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      simpa only [TensorProduct.add_tmul, map_add] using Submodule.add_mem _ hx hy
  | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

include hH in
theorem iSup_exteriorHodge (m k : ℕ) : ⨆ pq, exteriorHodge H m k pq = ⊤ := by
  apply top_unique
  rw [← exteriorPower.ιMulti_span_of_span ℂ k _ (hodge_vectors_span H hH m)]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  have hv' : ∀ i, ∃ (pq : ℤ × ℤ) (x : ℂ ⊗[ℚ] V) (u : Fin m → ℂ),
      x ∈ H pq ∧ v i = (powerBaseChange m).symm (x ⊗ₜ[ℂ] u) :=
    fun i => hv ⟨i, rfl⟩
  choose ps x u hx he using hv'
  have he' : v = fun i => (powerBaseChange m).symm (x i ⊗ₜ[ℂ] u i) := funext he
  apply (le_iSup (fun pq => exteriorHodge H m k pq) (∑ i, ps i))
  exact Submodule.subset_span ⟨ps, x, u, hx, rfl, congrArg (exteriorPower.ιMulti ℂ k) he'⟩

omit hH in
theorem exterior_hodge_action_pure (m k : ℕ) (Y : Module.End ℂ (ℂ ⊗[ℚ] V))
    (f : ℤ × ℤ → ℂ) (hY : ∀ pq x, x ∈ H pq → Y x = f pq • x)
    (ps : Fin k → ℤ × ℤ) (x : Fin k → ℂ ⊗[ℚ] V)
    (u : Fin k → (Fin m → ℂ)) (hx : ∀ i, x i ∈ H (ps i)) :
    exteriorDer k (powerAction m Y)
      (exteriorPower.ιMulti ℂ k (fun i => (powerBaseChange m).symm (x i ⊗ₜ[ℂ] u i))) =
      (∑ i, f (ps i)) •
        exteriorPower.ιMulti ℂ k (fun i => (powerBaseChange m).symm (x i ⊗ₜ[ℂ] u i)) := by
  rw [exteriorDer_ιMulti, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  have hi : powerAction m Y ((powerBaseChange m).symm (x i ⊗ₜ[ℂ] u i)) =
      f (ps i) • (powerBaseChange m).symm (x i ⊗ₜ[ℂ] u i) := by
    simp [powerAction, hY _ _ (hx i), TensorProduct.smul_tmul]
  rw [hi]
  rw [AlternatingMap.map_update_smul, Function.update_eq_self]

omit hH in
theorem exteriorHodge_le_eigenspace_of (m k : ℕ) (Y : Module.End ℂ (ℂ ⊗[ℚ] V))
    (f : (ℤ × ℤ) →+ ℂ) (hY : ∀ pq x, x ∈ H pq → Y x = f pq • x) (pq : ℤ × ℤ) :
    exteriorHodge H m k pq ≤ Module.End.eigenspace (exteriorDer k (powerAction m Y)) (f pq) := by
  apply Submodule.span_le.mpr
  rintro v ⟨ps, x, u, hx, hps, rfl⟩
  apply Module.End.mem_eigenspace_iff.mpr
  rw [exterior_hodge_action_pure H m k Y f hY ps x u hx,
    ← map_sum, hps]

theorem exteriorHodge_le_eigenspace (m k : ℕ) (pq : ℤ × ℤ) :
    exteriorHodge H m k pq ≤
      Module.End.eigenspace (exteriorDer k (powerAction m (gradingOperator H hH)))
        (Complex.I * ((pq.1 : ℂ) - pq.2)) := by
  let f : (ℤ × ℤ) →+ ℂ :=
    { toFun := fun pq => Complex.I * ((pq.1 : ℂ) - pq.2)
      map_zero' := by simp
      map_add' := by intros; simp only [Prod.fst_add, Prod.snd_add]; push_cast; ring }
  exact exteriorHodge_le_eigenspace_of H m k _ f
    (fun pq x hx => gradingOperator_apply_of_mem H hH hx) pq

include hH in
/-- The exterior pieces form the induced Hodge decomposition. -/
theorem isInternal_exteriorHodge (m k : ℕ) :
    DirectSum.IsInternal (exteriorHodge H m k) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, iSup_exteriorHodge H hH m k⟩
  have hind := (Module.End.eigenspaces_iSupIndep
    (exteriorDer k (powerAction m (separatingOperator H hH)))).comp separating_injective
  apply hind.mono
  intro pq
  let f : (ℤ × ℤ) →+ ℂ :=
    { toFun := fun pq => (((pq.1 + pq.2 : ℤ) : ℂ) + Complex.I * ((pq.1 : ℂ) - pq.2))
      map_zero' := by simp
      map_add' := by intros; simp only [Prod.fst_add, Prod.snd_add]; push_cast; ring }
  exact exteriorHodge_le_eigenspace_of H m k _ f
    (fun pq x hx => separatingOperator_apply_of_mem H hH hx) pq

/-- The induced grading kernel is exactly the sum of the exterior `(p,p)` pieces. -/
theorem ker_exterior_hodge_grading (m k : ℕ) :
    LinearMap.ker (exteriorDer k (powerAction m (gradingOperator H hH))) =
      ⨆ p : ℤ, exteriorHodge H m k (p, p) :=
  ker_eq_iSup_diag _ (iSup_exteriorHodge H hH m k) _
    (fun p q _x hx => Module.End.mem_eigenspace_iff.mp
      (exteriorHodge_le_eigenspace H hH m k (p, q) hx))

end HodgeLean.Foundations.WeilPower
