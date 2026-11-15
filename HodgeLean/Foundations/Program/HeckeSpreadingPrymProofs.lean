import HodgeLean.Foundations.Program.HeckeSpreadingPrymDefs
import HodgeLean.Papers.QuasiInverse

/-! # Proofs for the Hecke spreading specification S7

Each `_aux` theorem is restated in `HeckeSpreadingPrym.lean`. The arguments follow the stages below.

* S7a: S6 (`hk_weilAlg_of_open`) on the open set of dominance, with the forward binder at each
  dominance pair and `g32s_fiber_alg`.
* S7b: `g32r_dominant`, S7a and `C = {univ}`.
* S7c: `g32tr_weilAlg_pullback` along the reverse isogeny, with `b60b_member` and
  `g32h_fiber_polarized`.
* S7d: `qinv_KIsog_reverse_of_witness` on the dominance isogeny.
* S7e: the reverse field on two members; the Prym fibre is a member by `g32h_fiber_polarized`
  and `g32a_fiber_disc`.
* S7f, S7g: S7b with S7c and S7d, respectively S7c and S7e.

HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.Adapters HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem hk7_algLocus_eq_univ_aux (P : g32h_PrymFamily) (h46 : g32s_Prop46 P)
    {U : Set g32m_Domain} (hU : IsOpen U) (hne : U.Nonempty)
    (hdom : ∀ m ∈ U, ∃ s, (m, s) ∈ hk7_pairs P)
    (hfwd : ∀ p ∈ hk7_pairs P, g32t_WeilAlg (P.fiber p.2) → g32t_WeilAlg (b60b_univ p.1)) :
    hk7_algLocus = Set.univ := by
  apply Set.eq_univ_of_forall
  intro τ
  exact hk_weilAlg_of_open hU hne (fun m hm => by
    obtain ⟨s, hs⟩ := hdom m hm
    exact hfwd (m, s) hs (g32s_fiber_alg P h46 s)) τ

theorem hk7_spread_aux (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (P : g32h_PrymFamily) (h46 : g32s_Prop46 P) (R : g32r_PeriodMap F P)
    (hfwd : ∀ p ∈ hk7_pairs P, g32t_WeilAlg (P.fiber p.2) → g32t_WeilAlg (b60b_univ p.1)) :
    ∃ C : Set (Set g32m_Domain), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧ {m | g32t_WeilAlg (F.univ m)} = ⋃₀ C := by
  obtain ⟨U, hU, hne, hdom⟩ := g32r_dominant F P R
  have hloc := hk7_algLocus_eq_univ_aux P h46 hU hne (fun m hm => by
    obtain ⟨s, hs⟩ := hdom m hm
    exact ⟨s, by simpa only [hk7_pairs, Set.mem_ofPred_eq, hF] using hs⟩) hfwd
  refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
  · rintro Z rfl
    exact isClosedAnalytic_univ
  · rw [Set.sUnion_singleton, hF]
    exact hloc

theorem hk7_forward_of_reverse_aux (P : g32h_PrymFamily)
    (hrev : ∀ p ∈ hk7_pairs P, g32t_KIsog (b60b_univ p.1) (P.fiber p.2)) :
    ∀ p ∈ hk7_pairs P, g32t_WeilAlg (P.fiber p.2) → g32t_WeilAlg (b60b_univ p.1) := by
  intro p hp hAlg
  exact g32tr_weilAlg_pullback _ _
    ((g32t_isMember_iff _).1 (b60b_member p.1)).1
    (g32h_fiber_polarized P p.2) (hrev p hp) hAlg

set_option maxRecDepth 2000 in
theorem hk7_reverse_of_witness_aux (P : g32h_PrymFamily)
    (hw : ∀ (m : g32m_Domain) (s : P.S) (f : (P.fiber s).X ⟶ (b60b_univ m).X),
      IsMonHom f → ccm2_IsogenyOnPoints f →
        Nonempty (qinv_Witness (P.fiber s) (b60b_univ m) f)) :
    ∀ p ∈ hk7_pairs P, g32t_KIsog (b60b_univ p.1) (P.fiber p.2) := by
  intro p hp
  obtain ⟨f, hf, hi, hK, c, hc, hpol⟩ := hp
  obtain ⟨w⟩ := hw p.1 p.2 f hf hi
  exact qinv_KIsog_reverse_of_witness (P.fiber p.2) (b60b_univ p.1)
    f hf hi hK c hc hpol w

theorem hk7_reverse_of_members_aux (P : g32h_PrymFamily)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s))
    (hrev : ∀ A B, g32t_IsMember A → g32t_IsMember B → g32t_KIsog A B → g32t_KIsog B A) :
    ∀ p ∈ hk7_pairs P, g32t_KIsog (b60b_univ p.1) (P.fiber p.2) := by
  intro p hp
  exact hrev _ _
    ((g32t_isMember_iff _).2
      ⟨g32h_fiber_polarized P p.2, g32a_fiber_disc P hpol p.2 _⟩)
    (b60b_member p.1) hp

theorem hk7_spread_of_witness_aux (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (P : g32h_PrymFamily) (h46 : g32s_Prop46 P) (R : g32r_PeriodMap F P)
    (hw : ∀ (m : g32m_Domain) (s : P.S) (f : (P.fiber s).X ⟶ (b60b_univ m).X),
      IsMonHom f → ccm2_IsogenyOnPoints f →
        Nonempty (qinv_Witness (P.fiber s) (b60b_univ m) f)) :
    ∃ C : Set (Set g32m_Domain), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧ {m | g32t_WeilAlg (F.univ m)} = ⋃₀ C := by
  exact hk7_spread_aux F hF P h46 R
    (hk7_forward_of_reverse_aux P (hk7_reverse_of_witness_aux P hw))

theorem hk7_spread_of_members_aux (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (P : g32h_PrymFamily) (h46 : g32s_Prop46 P) (R : g32r_PeriodMap F P)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s))
    (hrev : ∀ A B, g32t_IsMember A → g32t_IsMember B → g32t_KIsog A B → g32t_KIsog B A) :
    ∃ C : Set (Set g32m_Domain), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧ {m | g32t_WeilAlg (F.univ m)} = ⋃₀ C := by
  exact hk7_spread_aux F hF P h46 R
    (hk7_forward_of_reverse_aux P (hk7_reverse_of_members_aux P hpol hrev))

end HodgeLean.Foundations.Program
