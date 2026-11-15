import HodgeLean.Foundations.Program.G32PropFourSixDefs
import HodgeLean.Foundations.Program.G32PropFourSixFiniteCheck
import HodgeLean.Foundations.Program.G32PropFourSixFiniteCharacter

section

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_coinduced {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (χ : H →* ℂˣ) : FDRep ℂ G :=
  FDRep.of (Representation.coind H.subtype (papersLinRep χ).ρ)

def g32p_coinducedFunction {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (χ : H →* ℂˣ) (f : g32p_coinduced H χ) : G → ℂ :=
  (show Representation.coindV H.subtype (papersLinRep χ).ρ from f).val

theorem g32p_coinduced_apply {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (χ : H →* ℂˣ) (g : G) (f : g32p_coinduced H χ) (x : G) :
    g32p_coinducedFunction H χ ((g32p_coinduced H χ).ρ g f) x =
      g32p_coinducedFunction H χ f (x * g) := rfl

def g32p_coinduced_delta {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (χ : H →* ℂˣ) : g32p_coinduced H χ := by
  classical
  refine ⟨(fun g => if hg : g ∈ H then (χ ⟨g, hg⟩ : ℂ) else 0), ?_⟩
  intro h g
  change (if hx : (h : G) * g ∈ H then (χ ⟨(h : G) * g, hx⟩ : ℂ) else 0) =
    (χ h : ℂ) * (if hg : g ∈ H then (χ ⟨g, hg⟩ : ℂ) else 0)
  by_cases hg : g ∈ H
  · have hh : (h : G) * g ∈ H := H.mul_mem h.property hg
    simp only [dite_eq_left hh, dite_eq_left hg]
    change (χ (h * ⟨g, hg⟩) : ℂ) = (χ h : ℂ) * (χ ⟨g, hg⟩ : ℂ)
    simp only [map_mul, Units.val_mul]
  · have hh : (h : G) * g ∉ H := fun hx => hg ((H.mul_mem_cancel_left h.property).mp hx)
    simp only [dite_eq_right hh, dite_eq_right hg, mul_zero]

theorem g32p_coinduced_delta_one {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (χ : H →* ℂˣ) : g32p_coinducedFunction H χ (g32p_coinduced_delta H χ) 1 = 1 := by
  classical
  change (if h : (1 : G) ∈ H then (χ ⟨1, h⟩ : ℂ) else 0) = 1
  rw [dite_eq_left H.one_mem]
  change (χ 1 : ℂ) = 1
  simp only [map_one, Units.val_one]

theorem g32p_coinduced_delta_ne_zero {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (χ : H →* ℂˣ) : g32p_coinduced_delta H χ ≠ 0 := by
  intro hz
  have hh := congrArg (fun f : g32p_coinduced H χ => g32p_coinducedFunction H χ f 1) hz
  change g32p_coinducedFunction H χ (g32p_coinduced_delta H χ) 1 = 0 at hh
  rw [g32p_coinduced_delta_one] at hh
  exact one_ne_zero hh

def g32p_coinducedHomEquiv {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (χ : H →* ℂˣ) (V : FDRep ℂ G) :
    (papersResRep H V ⟶ papersLinRep χ) ≃ₗ[ℂ] (V ⟶ g32p_coinduced H χ) := by
  let F := forget₂ (FDRep ℂ G) (Rep ℂ G)
  let K := forget₂ (FDRep ℂ H) (Rep ℂ H)
  exact (FDRep.forget₂HomLinearEquiv (papersResRep H V) (papersLinRep χ)).symm.trans
    ((Rep.resCoindHomEquiv.{0, 0, 0, 0} H.subtype (F.obj V)
      (K.obj (papersLinRep χ))).trans
        (FDRep.forget₂HomLinearEquiv V (g32p_coinduced H χ)))

theorem g32p_hom_finrank_symm {G : Type} [Group G] [Fintype G]
    (V W : FDRep ℂ G) : Module.finrank ℂ (V ⟶ W) = Module.finrank ℂ (W ⟶ V) := by
  let := invertibleOfNonzero (NeZero.ne (Nat.card G : ℂ))
  apply Nat.cast_injective (R := ℂ)
  rw [← FDRep.scalar_product_char_eq_finrank_equivariant,
    ← FDRep.scalar_product_char_eq_finrank_equivariant]
  congr 1
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => by simp [mul_comm])

theorem g32p_coinduced_mult {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (χ : H →* ℂˣ) (V : FDRep ℂ G) :
    Module.finrank ℂ (V ⟶ g32p_coinduced H χ) = papersMult H V χ := by
  classical
  let := Fintype.ofFinite H
  rw [← (g32p_coinducedHomEquiv H χ V).finrank_eq]
  exact g32p_hom_finrank_symm _ _

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory HodgeLean.Papers
open scoped Classical

set_option maxHeartbeats 400000

def g32p_coinducedAverage {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (χ : H →* ℂˣ) : (G → ℂ) →ₗ[ℂ] g32p_coinduced H χ := by
  classical
  let A : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
    (Nat.card H : ℂ)⁻¹ • ∑ h : H, (χ h : ℂ)⁻¹ • LinearMap.funLeft ℂ ℂ
      (fun x : G => (h : G) * x)
  refine A.codRestrict _ fun f => ?_
  intro k x
  change A f ((k : G) * x) = (χ k : ℂ) * A f x
  simp only [A, LinearMap.smul_apply, LinearMap.sum_apply, Finset.sum_apply,
    LinearMap.funLeft_apply, Pi.smul_apply, smul_eq_mul]
  change (Nat.card H : ℂ)⁻¹ * (∑ h : H, (χ h : ℂ)⁻¹ * f ((h : G) * ((k : G) * x))) =
    (χ k : ℂ) * ((Nat.card H : ℂ)⁻¹ * ∑ h : H, (χ h : ℂ)⁻¹ * f ((h : G) * x))
  have hs : (∑ h : H, (χ h : ℂ)⁻¹ * f ((h : G) * ((k : G) * x))) =
      ∑ h : H, (χ k : ℂ) * ((χ h : ℂ)⁻¹ * f ((h : G) * x)) := by
    refine Fintype.sum_equiv (Equiv.mulRight k) _ _ fun h => ?_
    change (χ h : ℂ)⁻¹ * f ((h : G) * ((k : G) * x)) =
      (χ k : ℂ) * ((χ (h * k) : ℂ)⁻¹ * f (((h * k : H) : G) * x))
    simp only [map_mul, Units.val_mul, Subgroup.coe_mul, mul_inv_rev, mul_assoc]
    field_simp
  rw [hs, ← Finset.mul_sum]
  ring

theorem g32p_coinducedAverage_apply {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (χ : H →* ℂˣ) (f : G → ℂ) (x : G) :
    g32p_coinducedFunction H χ (g32p_coinducedAverage H χ f) x =
      (Nat.card H : ℂ)⁻¹ * ∑ h : H, (χ h : ℂ)⁻¹ * f ((h : G) * x) := by
  classical
  change (((Nat.card H : ℂ)⁻¹ • ∑ h : H, (χ h : ℂ)⁻¹ •
    LinearMap.funLeft ℂ ℂ (fun x : G => (h : G) * x)) f) x = _
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, Finset.sum_apply,
    LinearMap.funLeft_apply, Pi.smul_apply, smul_eq_mul]

theorem g32p_coinducedAverage_retract {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (χ : H →* ℂˣ) (f : g32p_coinduced H χ) :
    g32p_coinducedAverage H χ (g32p_coinducedFunction H χ f) = f := by
  classical
  apply Subtype.ext
  funext x
  rw [← g32p_coinducedFunction, g32p_coinducedAverage_apply]
  have he (h : H) : g32p_coinducedFunction H χ f ((h : G) * x) =
      (χ h : ℂ) * g32p_coinducedFunction H χ f x := f.property h x
  simp only [he, ← mul_assoc, inv_mul_cancel₀ (χ _).ne_zero, one_mul,
    Finset.sum_const, nsmul_eq_mul]
  change (Nat.card H : ℂ)⁻¹ * (Fintype.card H : ℂ) *
    g32p_coinducedFunction H χ f x = g32p_coinducedFunction H χ f x
  rw [Fintype.card_eq_nat_card, inv_mul_cancel₀ (by exact_mod_cast (Nat.card_pos (α := H)).ne'), one_mul]

theorem g32p_coinduced_character_sum {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (χ : H →* ℂˣ) (g : G) :
    (g32p_coinduced H χ).character g =
      (Nat.card H : ℂ)⁻¹ * ∑ x : G, ∑ h : H,
        if (h : G) * (x * g) = x then (χ h : ℂ)⁻¹ else 0 := by
  classical
  let S := g32p_coinduced H χ
  let inc : S →ₗ[ℂ] (G → ℂ) := (Representation.coindV H.subtype (papersLinRep χ).ρ).subtype
  let avg := g32p_coinducedAverage H χ
  have he : avg.comp inc = LinearMap.id := by
    ext f
    exact g32p_coinducedAverage_retract H χ f
  have ht : (S.ρ g).comp (avg.comp inc) = S.ρ g := by rw [he, LinearMap.comp_id]
  change LinearMap.trace ℂ S (S.ρ g) = _
  rw [← ht, ← LinearMap.comp_assoc, LinearMap.trace_comp_comm']
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ G)]
  change (∑ x : G, (inc.comp ((S.ρ g).comp avg)) (Pi.single x 1) x) = _
  change (∑ x : G, g32p_coinducedFunction H χ
    (S.ρ g (avg (Pi.single x 1))) x) = _
  dsimp only [S, avg]
  simp_rw [g32p_coinduced_apply, g32p_coinducedAverage_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  by_cases hh : (h : G) * (x * g) = x
  · simp only [hh, Pi.single_eq_same, mul_one, ite_true]
  · simp only [Pi.single_eq_of_ne hh, mul_zero, ite_eq_right hh]

theorem g32p_coinduced_character {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (χ : H →* ℂˣ) (g : G) :
    (g32p_coinduced H χ).character g =
      (Nat.card H : ℂ)⁻¹ * ∑ x : G,
        if hx : x * g⁻¹ * x⁻¹ ∈ H then (χ ⟨x * g⁻¹ * x⁻¹, hx⟩ : ℂ)⁻¹ else 0 := by
  classical
  rw [g32p_coinduced_character_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  have he (h : H) : (h : G) * (x * g) = x ↔ (h : G) = x * g⁻¹ * x⁻¹ := by
    rw [← eq_mul_inv_iff_mul_eq]
    simp only [mul_inv_rev, mul_assoc]
  by_cases hx : x * g⁻¹ * x⁻¹ ∈ H
  · rw [dite_eq_left hx]
    let h₀ : H := ⟨x * g⁻¹ * x⁻¹, hx⟩
    rw [Finset.sum_eq_single h₀]
    · rw [ite_eq_left ((he h₀).mpr rfl)]
    · intro h _ hne
      rw [ite_eq_right]
      exact fun hh => hne (Subtype.ext ((he h).mp hh))
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
  · rw [dite_eq_right hx]
    apply Finset.sum_eq_zero
    intro h _
    rw [ite_eq_right]
    exact fun hh => hx ((he h).mp hh ▸ h.property)

theorem g32p_coinduced_finrank {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (χ : H →* ℂˣ) :
    (Module.finrank ℂ (g32p_coinduced H χ) : ℂ) =
      (Nat.card H : ℂ)⁻¹ * (Nat.card G : ℂ) := by
  classical
  rw [← FDRep.char_one, g32p_coinduced_character]
  simp only [inv_one, mul_one, mul_inv_cancel, dite_eq_left H.one_mem]
  have he : (⟨1, H.one_mem⟩ : H) = 1 := rfl
  simp only [he, map_one, Units.val_one, inv_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Fintype.card_eq_nat_card]

end HodgeLean.Foundations.Program

end
end

section

namespace HodgeLean.Foundations.Program

def g32p_finBlockIndex (n : ℕ) [NeZero n] (q : ℕ) (r : Fin 16) : Fin n :=
  Fin.ofNat n (q * 16 + r.val)

theorem g32p_forall_fin_blocks {n : ℕ} [NeZero n] (P : Fin n → Prop)
    (h : ∀ q : Fin ((n + 15) / 16), ∀ r : Fin 16,
      P (g32p_finBlockIndex n q.val r)) : ∀ i, P i := by
  intro i
  have hq : i.val / 16 < (n + 15) / 16 := by omega
  have he : g32p_finBlockIndex n (i.val / 16) ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩ = i := by
    apply Fin.ext
    change (i.val / 16 * 16 + i.val % 16) % n = i.val
    rw [Nat.mul_comm (i.val / 16) 16, Nat.div_add_mod, Nat.mod_eq_of_lt i.isLt]
  exact he ▸ h ⟨i.val / 16, hq⟩ ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩

def g32p_matrixFingerprint (M : HurwitzPrymRex_Mat) : ℤ :=
  (List.ofFn fun i : Fin 4 => List.ofFn fun j : Fin 4 =>
    [(M i j).re, (M i j).om]).flatten.flatten.foldr (fun a b => a + 64 * b) 0

theorem g32p_matrix_injective_of_decoder {n : ℕ} (nodes : Fin n → HurwitzPrymRex_Mat)
    (decode : ℤ → Fin n) (h : ∀ i, decode (g32p_matrixFingerprint (nodes i)) = i) :
    Function.Injective nodes := by
  intro i j hij
  rw [← h i, ← h j, hij]

end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

def g32p_supplierOfFiniteTransitions {n k m : ℕ} (hm : 3 ≤ m)
    (gens : Fin k → g32p_G)
    (e : Fin n ≃ Subgroup.closure (Set.range gens)) (origin : Fin n)
    (h1 : e origin = 1) (next : Fin n → Fin k → Fin n)
    (hstep : ∀ i s, e (next i s) = e i *
      ⟨gens s, Subgroup.subset_closure (Set.mem_range_self s)⟩)
    (values : Fin n → Multiplicative (ZMod m))
    (hzero : values origin = 1)
    (hvalues : ∀ i s, values (next i s) = values i * values (next origin s))
    (hsurj : Function.Surjective values) : g32p_Supplier := by
  let lifted : Fin k → Subgroup.closure (Set.range gens) :=
    fun s => ⟨gens s, Subgroup.subset_closure (Set.mem_range_self s)⟩
  have hgen : Subgroup.closure (Set.range lifted) = ⊤ :=
    g32p_lifted_generators_top gens _ rfl lifted (fun _ => rfl)
  have hind (s : Fin k) : e.symm (lifted s) = next origin s := by
    have hh : e (next origin s) = lifted s := by
      rw [hstep, h1, one_mul]
    exact (congrArg e.symm hh).symm.trans (e.symm_apply_apply _)
  let χ := g32p_homOfFiniteTransitions lifted hgen e origin h1 next hstep values hzero
    (fun i s => by rw [hind]; exact hvalues i s)
  exact ⟨_, m, hm, χ, fun x => by
    obtain ⟨i, hi⟩ := hsurj x
    exact ⟨e i, by change values (e.symm (e i)) = x; rw [e.symm_apply_apply, hi]⟩⟩

theorem g32p_supplierOfFiniteTransitions_value {n k m : ℕ} (hm : 3 ≤ m)
    (gens : Fin k → g32p_G)
    (e : Fin n ≃ Subgroup.closure (Set.range gens)) (origin : Fin n)
    (h1 : e origin = 1) (next : Fin n → Fin k → Fin n)
    (hstep : ∀ i s, e (next i s) = e i *
      ⟨gens s, Subgroup.subset_closure (Set.mem_range_self s)⟩)
    (values : Fin n → Multiplicative (ZMod m))
    (hzero : values origin = 1)
    (hvalues : ∀ i s, values (next i s) = values i * values (next origin s))
    (hsurj : Function.Surjective values) (i : Fin n) :
    (g32p_supplierOfFiniteTransitions hm gens e origin h1 next hstep values
      hzero hvalues hsurj).χ (e i) = values i := by
  change values (e.symm (e i)) = values i
  rw [e.symm_apply_apply]

end HodgeLean.Foundations.Program

end
end

section

namespace HodgeLean.Foundations.Program

theorem g32p_transition_integral_sound {n k : ℕ}
    (nodes : Fin n → HurwitzPrymRex_Mat) (gens : Fin k → HurwitzPrymRex_Mat)
    (next : Fin n → Fin k → Fin n)
    (h : g32p_transitionCheck nodes gens next = true) (i : Fin n) (s : Fin k) :
    HurwitzPrymRex_mmul (nodes i) (gens s) = nodes (next i s) :=
  (of_decide_eq_true h) i s

end HodgeLean.Foundations.Program

end
