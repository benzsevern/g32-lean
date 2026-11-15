import HodgeLean.Adapters.NormalConeB4aGysinGenericOpen

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- A closed boundary avoiding every component generic point has strictly
smaller dimension than a finite ambient dimension bound. -/
theorem a3b4a_gysin_boundary_dimension_lt_of_generic_avoidance
    {Z : Scheme.{0}} (B : Closeds Z) (n : ℕ)
    (hdim : topologicalKrullDim Z ≤ (n : ℕ))
    (hgeneric : ∀ ξ ∈ genericPoints Z, ξ ∉ B) :
    topologicalKrullDim (reducedClosedSubscheme B) < (n : ℕ) := by
  classical
  rw [Scheme.topologicalKrullDim_eq_orderKrullDim] at hdim
  let f := reducedClosedSubschemeι B
  have hiff (a b : reducedClosedSubscheme B) : f a ≤ f b ↔ a ≤ b := by
    rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
    exact f.isClosedEmbedding.isInducing.specializes_iff
  have hstrict : StrictMono f := fun a b hab =>
    lt_iff_le_not_ge.mpr ⟨(hiff a b).mpr hab.le, fun h => hab.not_ge ((hiff b a).mp h)⟩
  have hplus : ∀ b : reducedClosedSubscheme B, Order.height b + 1 ≤ n := by
    intro b
    let K : irreducibleComponents Z :=
      ⟨irreducibleComponent (f b), irreducibleComponent_mem_irreducibleComponents (f b)⟩
    let ξ := (genericPoints.ofComponent K).val
    have hξ : ξ ∈ genericPoints Z := (genericPoints.ofComponent K).property
    have hbξ : f b ∈ closure ({ξ} : Set Z) := by
      change f b ∈ closure ({(genericPoints.ofComponent K).val} : Set Z)
      rw [(genericPoints.isGenericPoint_ofComponent K).def]
      exact mem_irreducibleComponent
    have hle : f b ≤ ξ := Scheme.le_iff_specializes.mpr
      (specializes_iff_mem_closure.mpr hbξ)
    have hne : f b ≠ ξ := by
      intro heq
      have hbB : f b ∈ B := (range_reducedClosedSubschemeι B).le ⟨b, rfl⟩
      exact hgeneric ξ hξ (heq ▸ hbB)
    have hlt : f b < ξ := lt_iff_le_not_ge.mpr ⟨hle, fun hge =>
      hne (((Scheme.le_iff_specializes.mp hge).antisymm
        (Scheme.le_iff_specializes.mp hle)).eq)⟩
    have hξdim : Order.height ξ ≤ n :=
      WithBot.coe_le_coe.mp ((Order.height_le_krullDim ξ).trans hdim)
    calc
      Order.height b + 1 ≤ Order.height (f b) + 1 :=
        add_le_add (Order.height_le_height_apply_of_strictMono f hstrict b) le_rfl
      _ ≤ Order.height ξ := Order.height_add_one_le hlt
      _ ≤ n := hξdim
  cases n with
  | zero =>
    haveI : IsEmpty (reducedClosedSubscheme B) := ⟨fun b => by
      have hp := hplus b
      simpa using hp⟩
    rw [Scheme.topologicalKrullDim_eq_orderKrullDim, Order.krullDim_eq_bot]
    simp
  | succ k =>
    have hb : ∀ b : reducedClosedSubscheme B, Order.height b ≤ k := by
      intro b
      apply (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp
      simpa only [Nat.cast_add, Nat.cast_one] using hplus b
    have hdB : topologicalKrullDim (reducedClosedSubscheme B) ≤ (k : ℕ) := by
      rw [Scheme.topologicalKrullDim_eq_orderKrullDim, Order.krullDim_eq_iSup_height]
      exact iSup_le fun b => WithBot.coe_le_coe.mpr (hb b)
    exact hdB.trans_lt (by exact_mod_cast Nat.lt_succ_self k)

end HodgeLean.Adapters
