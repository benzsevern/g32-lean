import HodgeLean.Foundations.Program.G32Native.CanonicalCoefficientForms
import HodgeLean.Foundations.Program.SchoenCycleBlockMultiplicity

/-! # Canonical divisor orders in a positive collision partition -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native

/-- Natural lower bounds agree with their mapped integer-order lower bounds. -/
theorem nat_le_mapped_analytic_order (n : ℕ) (s : ℕ∞) :
    (n : WithTop ℤ) ≤ s.map (fun k : ℕ => (k : ℤ)) ↔ (n : ℕ∞) ≤ s := by
  cases s using ENat.recTopCoe <;> simp [ENat.map_top, ENat.map_natCast]

/-- Orders along every point of an exact canonical tuple reduce to its positive blocks. -/
theorem canonical_divisor_block_orders (G : CanonicalAbelGeometry)
    (θ δ : b3_HolForm (Fin 1 → ℂ) (ComplexPoint G.Z)) (hθ : θ ≠ 0)
    (z : Fin (2 * G.k) → ComplexPoint G.Z)
    (hz : b4c_divForm (hE := Module.finrank_fin_fun (n := 1) ℂ) θ.val =
      ∑ i, Finsupp.single (z i) (1 : ℤ))
    (b : ℕ) (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin (2 * G.k))
    (q : Fin b → ComplexPoint G.Z) (hq : Function.Injective q)
    (hzq : ∀ a j, z (ι ⟨a, j⟩) = q a) :
    (∀ p : ComplexPoint G.Z,
      meromorphicOrderAt (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) θ p) 0 ≤
      meromorphicOrderAt (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) δ p) 0) ↔
    ∀ a, (m a : ℕ∞) ≤ analyticOrderAt
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) δ (q a)) 0 := by
  classical
  let h := Module.finrank_fin_fun (n := 1) ℂ
  let w : b4c_MeroForm (Fin 1 → ℂ) (ComplexPoint G.Z) h :=
    ⟨θ, RiemannRochAna_hol_isMeroForm h θ⟩
  have horder (p : ComplexPoint G.Z) :
      meromorphicOrderAt (HurwitzPrymRR_loc h θ p) 0 =
        ((∑ i, Finsupp.single (z i) (1 : ℤ)) p : WithTop ℤ) := by
    exact (RiemannRochAna_coe_divForm_apply h w
      (b4c_meroForm_orderSupport_finite_aux h w) p
      (RiemannRochAna_hol_order_ne_top h θ hθ p)).symm.trans
        (congrArg (fun D : ComplexPoint G.Z →₀ ℤ => (D p : WithTop ℤ)) hz)
  have hblock (a : Fin b) :
      meromorphicOrderAt (HurwitzPrymRR_loc h θ (q a)) 0 = (m a : WithTop ℤ) := by
    rw [horder, s2e_block_tuple_divisor_multiplicity m ι q hq z hzq a]
    simp
  constructor
  · intro ho a
    have hh := ho (q a)
    rw [hblock, (RiemannRochAna_hol_loc_analytic h δ (q a)).meromorphicOrderAt_eq] at hh
    exact (nat_le_mapped_analytic_order (m a) _).mp hh
  · intro ho p
    by_cases hp : ∃ a, q a = p
    · obtain ⟨a, rfl⟩ := hp
      rw [hblock, (RiemannRochAna_hol_loc_analytic h δ (q a)).meromorphicOrderAt_eq]
      exact (nat_le_mapped_analytic_order (m a) _).mpr (ho a)
    · have hzoff (i : Fin (2 * G.k)) : z i ≠ p := by
        obtain ⟨⟨a, j⟩, rfl⟩ := ι.surjective i
        rw [hzq]
        exact fun he => hp ⟨a, he⟩
      rw [horder]
      have hzero : (∑ i, Finsupp.single (z i) (1 : ℤ)) p = 0 := by
        simp only [Finsupp.finsetSum_apply, Finsupp.single_apply]
        simp [hzoff]
      rw [hzero]
      exact (RiemannRochAna_hol_loc_analytic h δ p).meromorphicOrderAt_nonneg

#print axioms nat_le_mapped_analytic_order
#print axioms canonical_divisor_block_orders
end HodgeLean.Foundations.Program.G32Native
