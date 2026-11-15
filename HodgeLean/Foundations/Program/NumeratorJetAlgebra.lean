import HodgeLean.Foundations.Program.NumeratorJetDefs

noncomputable section
open Polynomial
namespace HodgeLean.Foundations.Program

theorem b65e_divByMonic_mul_cancel (A B C : ℂ[X]) (hB : B.Monic) (hC : C.Monic) :
    (A * C) /ₘ (B * C) = A /ₘ B := by
  apply (Polynomial.div_modByMonic_unique (A /ₘ B) ((A %ₘ B) * C) (hB.mul hC) ?_).1
  constructor
  · calc
      A %ₘ B * C + B * C * (A /ₘ B) = (A %ₘ B + B * (A /ₘ B)) * C := by ring
      _ = A * C := by rw [Polynomial.modByMonic_add_div]
  · rw [Polynomial.degree_mul, Polynomial.degree_mul]
    exact WithBot.add_lt_add_of_lt_of_le (by simpa using hC.ne_zero)
      (Polynomial.degree_modByMonic_lt A hB) le_rfl

theorem b65e_polyPart_div (A B : ℂ[X]) (hB : B.Monic) :
    b65e_polyPart (algebraMap ℂ[X] (RatFunc ℂ) A /
      algebraMap ℂ[X] (RatFunc ℂ) B) = A /ₘ B := by
  let f : RatFunc ℂ := algebraMap ℂ[X] (RatFunc ℂ) A / algebraMap ℂ[X] (RatFunc ℂ) B
  have hprod : f.num * B = A * f.denom :=
    (RatFunc.num_mul_eq_mul_denom_iff hB.ne_zero).mpr rfl
  obtain ⟨C, hC⟩ := RatFunc.denom_div_dvd A B
  have hmC : C.Monic := (RatFunc.monic_denom f).of_mul_monic_left (hC ▸ hB)
  have hA : A = f.num * C := by
    apply mul_right_cancel₀ (RatFunc.denom_ne_zero f)
    rw [← hprod, hC]
    ring
  change f.num /ₘ f.denom = A /ₘ B
  rw [hA, hC, b65e_divByMonic_mul_cancel _ _ _ (RatFunc.monic_denom f) hmC]

theorem b65e_polyPart_add (f g : RatFunc ℂ) :
    b65e_polyPart (f + g) = b65e_polyPart f + b65e_polyPart g := by
  have hrep : f + g =
      algebraMap ℂ[X] (RatFunc ℂ) (f.num * g.denom + g.num * f.denom) /
        algebraMap ℂ[X] (RatFunc ℂ) (f.denom * g.denom) := by
    rw [map_add, map_mul, map_mul, map_mul]
    conv_lhs => rw [← RatFunc.num_div_denom f, ← RatFunc.num_div_denom g]
    rw [div_add_div _ _ (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero f))
      (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero g))]
    ring

  rw [hrep, b65e_polyPart_div _ _ ((RatFunc.monic_denom f).mul (RatFunc.monic_denom g)),
    Polynomial.add_divByMonic,
    b65e_divByMonic_mul_cancel _ _ _ (RatFunc.monic_denom f) (RatFunc.monic_denom g)]
  rw [mul_comm f.denom g.denom,
    b65e_divByMonic_mul_cancel _ _ _ (RatFunc.monic_denom g) (RatFunc.monic_denom f)]
  rfl

theorem b65e_polyPart_C_mul (c : ℂ) (f : RatFunc ℂ) :
    b65e_polyPart (RatFunc.C c * f) = c • b65e_polyPart f := by
  have hrep : RatFunc.C c * f =
      algebraMap ℂ[X] (RatFunc ℂ) (c • f.num) /
        algebraMap ℂ[X] (RatFunc ℂ) f.denom := by
    rw [Algebra.smul_def, Polynomial.algebraMap_eq, map_mul, RatFunc.algebraMap_C, mul_div_assoc,
      RatFunc.num_div_denom]
  rw [hrep, b65e_polyPart_div _ _ (RatFunc.monic_denom f), Polynomial.smul_divByMonic]
  rfl

theorem b65e_coeff_divByMonic (F B : ℂ[X]) (d j : ℕ) (hF : F.natDegree < d) :
    (F /ₘ B).coeff j = ∑ k ∈ Finset.range d, F.coeff k * (X ^ k /ₘ B).coeff j := by
  conv_lhs => rw [F.as_sum_range' d hF]
  change ((Polynomial.divByMonicHom B) _).coeff j = _
  rw [map_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Polynomial.smul_X_eq_monomial, map_smul]
  simp only [Polynomial.coeff_smul, smul_eq_mul, Polynomial.divByMonicHom_apply]


theorem b65e_analytic_div_coeff {s : Set ℂ} (F : ℂ → ℂ[X]) (B : ℂ[X])
    (d : ℕ) (hdeg : ∀ θ, (F θ).natDegree < d)
    (hF : ∀ k, AnalyticOnNhd ℂ (fun θ ↦ (F θ).coeff k) s) (j : ℕ) :
    AnalyticOnNhd ℂ (fun θ ↦ (F θ /ₘ B).coeff j) s := by
  have heq : (fun θ ↦ (F θ /ₘ B).coeff j) =
      fun θ ↦ ∑ k ∈ Finset.range d, (F θ).coeff k * (X ^ k /ₘ B).coeff j := by
    funext θ
    exact b65e_coeff_divByMonic _ _ _ _ (hdeg θ)
  rw [heq]
  have h := Finset.analyticOnNhd_sum (Finset.range d)
    (fun k _ ↦ (hF k).mul (analyticOnNhd_const (v := (X ^ k /ₘ B).coeff j)))
  simpa only [Finset.sum_fn] using h

theorem b65e_analytic_mul_coeff {s : Set ℂ} (F G : ℂ → ℂ[X])
    (hF : ∀ k, AnalyticOnNhd ℂ (fun θ ↦ (F θ).coeff k) s)
    (hG : ∀ k, AnalyticOnNhd ℂ (fun θ ↦ (G θ).coeff k) s) (j : ℕ) :
    AnalyticOnNhd ℂ (fun θ ↦ (F θ * G θ).coeff j) s := by
  simp only [Polynomial.coeff_mul]
  have h := Finset.analyticOnNhd_sum (Finset.HasAntidiagonal.antidiagonal j)
    (fun k _ ↦ (hF k.1).mul (hG k.2))
  simpa only [Finset.sum_fn] using h

theorem b65e_analytic_prod_coeff {ι : Type*} {s : Set ℂ} (S : Finset ι)
    (t : ℂ → ι → ℂ) (ht : ∀ x, AnalyticOnNhd ℂ (fun θ ↦ t θ x) s) (j : ℕ) :
    AnalyticOnNhd ℂ (fun θ ↦ (∏ x ∈ S, (X - C (t θ x))).coeff j) s := by
  classical
  induction S using Finset.induction_on generalizing j with
  | empty => simpa only [Finset.prod_empty] using
      (analyticOnNhd_const (v := (1 : ℂ[X]).coeff j) (s := s))
  | @insert x S hx ih =>
    simp only [Finset.prod_insert hx]
    apply b65e_analytic_mul_coeff _ _ _ ih j
    intro k
    by_cases hk : k = 0
    · subst k
      simpa only [Polynomial.coeff_sub, Polynomial.coeff_X_zero,
        Polynomial.coeff_C_zero, zero_sub, Pi.neg_def] using (ht x).neg
    · simpa only [Polynomial.coeff_sub, Polynomial.coeff_C, hk, ite_false, sub_zero]
        using (analyticOnNhd_const (v := (X : ℂ[X]).coeff k) (s := s))


end HodgeLean.Foundations.Program
