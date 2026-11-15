import HodgeLean.Foundations.MatrixAlgGroupLieCartier
import HodgeLean.Foundations.MatrixAlgGroupLieSmooth
import HodgeLean.Foundations.MatrixAlgGroupLieDefs
import HodgeLean.Foundations.MatrixAlgGroupLieBracket
import HodgeLean.Foundations.MatrixAlgGroupLieElem
import HodgeLean.Foundations.MatrixAlgGroupLieIdentityComponent
import HodgeLean.Foundations.MatrixAlgGroupLieRecovery

/-! # Open proof obligations for matrix algebraic groups and their Lie algebras -/

noncomputable section

namespace HodgeLean.Foundations

open MvPolynomial HodgeLean.Foundations.Program
open scoped TensorProduct

variable {k : Type*} [Field k] {n : ℕ}

theorem g1_lie_mono_aux (G H : MatrixAlgGroup k n) (h : G.carrier ≤ H.carrier) :
    g1_lieAlgebra G ≤ g1_lieAlgebra H :=
  g1_lieOfSet_mono h

theorem g1_lieAlgebra_eq_bot_of_finite_aux (G : MatrixAlgGroup k n) [Finite G.carrier] :
    g1_lieAlgebra G = ⊥ :=
  g1_lieOfSet_eq_bot_of_finite _ (Set.toFinite _)

theorem g1_isConnected_iff_of_finite_aux (G : MatrixAlgGroup k n) [Finite G.carrier] :
    g1_IsConnected G ↔ G.carrier = ⊥ := by
  let _ := g1_zariski k n
  have := g1_t1Space (k := k) (n := n)
  unfold g1_IsConnected
  constructor
  · intro h
    have hsub : (G.carrier : Set (Matrix.GeneralLinearGroup (Fin n) k)).Subsingleton := by
      have : PreconnectedSpace G.carrier :=
        Subtype.preconnectedSpace h.isPreconnected
      intro a ha b hb
      have := (isPreconnected_univ (α := G.carrier)).subsingleton (Set.mem_univ ⟨a, ha⟩)
        (Set.mem_univ ⟨b, hb⟩)
      exact congrArg Subtype.val this
    rw [eq_bot_iff]
    intro g hg
    exact hsub hg G.carrier.one_mem
  · intro h
    rw [h]
    change IsConnected ({1} : Set _)
    exact isConnected_singleton

theorem g1_lieAlgebra_GL_aux [Infinite k] : g1_lieAlgebra (g1_GL k n) = ⊤ := by
  rw [eq_top_iff]
  intro X _
  change X ∈ g1_lieOfSet _
  simp only [g1_lieOfSet, Submodule.mem_iInf, LinearMap.mem_ker]
  intro f hf
  have : f = 0 := by
    have h := g1_vanishingIdeal_GL (k := k) (n := n)
    rw [g1_vanishingIdeal] at h
    rw [h] at hf
    exact (Ideal.mem_bot).mp hf
  subst this
  simp [g1_differential]

theorem g1_lie_mem_aux [IsAlgClosed k] (G : MatrixAlgGroup k n)
    (X Y : Matrix (Fin n) (Fin n) k) (hX : X ∈ g1_lieAlgebra G) (hY : Y ∈ g1_lieAlgebra G) :
    X * Y - Y * X ∈ g1_lieAlgebra G :=
  g1_lieOfSet_bracket_mem _ (fun _ hg _ hh ↦ G.carrier.mul_mem hg hh) X Y hX hY

theorem g1_exists_identityComponent_aux [IsAlgClosed k] (G : MatrixAlgGroup k n) :
    ∃ I : MatrixAlgGroup k n, (I.carrier : Set (Matrix.GeneralLinearGroup (Fin n) k)) =
      g1_identityComponent G :=
  g1_exists_identityComponent_of_closed G

theorem g1_lie_identityComponent_aux [IsAlgClosed k] (G : MatrixAlgGroup k n) :
    g1_lieOfSet (g1_identityComponent G) = g1_lieAlgebra G :=
  g1_lieOfSet_identityComponent G

theorem g1_exists_centralizer_aux (G : MatrixAlgGroup k n)
    (S : Set (Matrix.GeneralLinearGroup (Fin n) k)) :
    ∃ C : MatrixAlgGroup k n, C.carrier = G.carrier ⊓ Subgroup.centralizer S := by
  refine ⟨g1_ofEquations ((G.equations : Set (MvPolynomial (Fin n × Fin n) k)) ∪
    {f | ∃ s ∈ S, ∃ i j : Fin n,
      f = (g1_varMatrix k n * (s : Matrix (Fin n) (Fin n) k).map C -
      (s : Matrix (Fin n) (Fin n) k).map C * g1_varMatrix k n :
        Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) k)) i j})
    (G.carrier ⊓ Subgroup.centralizer S) ?_, rfl⟩
  intro g
  rw [Subgroup.mem_inf, G.equations_iff, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hG, hS⟩ f (hf | ⟨s, hs, i, j, rfl⟩)
    · exact hG f hf
    · rw [g1_eval_commEq, ← Units.val_mul, ← hS s hs, Units.val_mul, sub_self]; rfl
  · intro h
    refine ⟨fun f hf ↦ h f (Or.inl hf), fun s hs ↦ ?_⟩
    have : (g : Matrix (Fin n) (Fin n) k) * s - s * g = 0 := by
      ext i j
      rw [← g1_eval_commEq]
      exact h _ (Or.inr ⟨s, hs, i, j, rfl⟩)
    exact Units.ext (sub_eq_zero.mp this).symm

theorem g1_lie_inf_aux [IsAlgClosed k] [CharZero k] (G H I : MatrixAlgGroup k n)
    (hI : I.carrier = G.carrier ⊓ H.carrier) :
    g1_lieAlgebra I = g1_lieAlgebra G ⊓ g1_lieAlgebra H := by
  have hmem : ∀ g, g ∈ I.carrier → g ∈ G.carrier ∧ g ∈ H.carrier := fun g hg ↦ by
    rwa [hI, Subgroup.mem_inf] at hg
  exact le_antisymm
    (le_inf (g1_lieOfSet_mono fun g hg ↦ (hmem g hg).1)
      (g1_lieOfSet_mono fun g hg ↦ (hmem g hg).2))
    (g1_lieAlgebra_inf_le G H I hI)

theorem g1_lie_centralizer_aux [IsAlgClosed k] [CharZero k] (G C : MatrixAlgGroup k n)
    (S : Set (Matrix.GeneralLinearGroup (Fin n) k))
    (hC : C.carrier = G.carrier ⊓ Subgroup.centralizer S) :
    g1_lieAlgebra C = g1_lieAlgebra G ⊓ g1_lieCentralizer S := by
  rw [g1_lie_inf_aux G (g1_centralizerGroup S) C hC, g1_lieAlgebra_centralizerGroup]

/-- In characteristic zero the Lie algebra of a matrix algebraic group has the
Krull dimension of its coordinate ring `k[x_ij] ⧸ g1_vanishingIdeal G` (the group is smooth).
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §3.6 and AG.16.2 (`dim 𝔤 = dim G`);
Humphreys, *Linear Algebraic Groups*, §5.5 and §9.1; Cartier's smoothness theorem
(Demazure–Gabriel, *Groupes algébriques*, II.6.1.1). -/
private lemma g1_dim_lie_eq_dim [IsAlgClosed k] [CharZero k] (G : MatrixAlgGroup k n) :
    (Module.finrank k (g1_lieAlgebra G) : WithBot ℕ∞) =
      ringKrullDim (MvPolynomial (Fin n × Fin n) k ⧸ g1_vanishingIdeal G) :=
  g1_finrank_lie_eq_krullDim G

/-- One inclusion of the recovery statement: `G ∩ H` has Lie algebra `𝔤 ∩ 𝔥 = 𝔤`, hence the
dimension of `G`, so it is all of the connected group `G`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §7.1. -/
private lemma g1_le_of_lie_eq [IsAlgClosed k] [CharZero k] (G H : MatrixAlgGroup k n)
    (hG : g1_IsConnected G) (hlie : g1_lieAlgebra G = g1_lieAlgebra H) :
    G.carrier ≤ H.carrier := by
  have hI : g1_lieAlgebra (g1_inter G H) = g1_lieAlgebra G := by
    rw [g1_lie_inf_aux G H (g1_inter G H) rfl, ← hlie, inf_idem]
  exact (g1_le_of_lie_eq_of_dim G (g1_inter G H) hG inf_le_left hI (g1_dim_lie_eq_dim G)
    (g1_dim_lie_eq_dim _)).trans inf_le_right

theorem g1_eq_of_lie_eq_aux [IsAlgClosed k] [CharZero k] (G H : MatrixAlgGroup k n)
    (hG : g1_IsConnected G) (hH : g1_IsConnected H)
    (hlie : g1_lieAlgebra G = g1_lieAlgebra H) : G.carrier = H.carrier :=
  le_antisymm (g1_le_of_lie_eq G H hG hlie) (g1_le_of_lie_eq H G hH hlie.symm)

theorem g1_hodgeGroup_eq_gkGroup_aux {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] {H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)}
    (hH : DirectSum.IsInternal H) (E : LinearMap.BilinForm ℚ V)
    (R : Subalgebra ℚ (Module.End ℚ V)) (J : Module.End ℚ V) {m : ℕ}
    (b : Module.Basis (Fin m) ℂ (ℂ ⊗[ℚ] V)) (Hg Gk : MatrixAlgGroup ℂ m)
    (hHg : g1_IsConnected Hg) (hGk : g1_IsConnected Gk)
    (hHgLie : g1_lieAlgebra Hg =
      (complexSpan (hodgeLieAlgebra H hH).toSubmodule).map (LinearMap.toMatrix b b).toLinearMap)
    (hGkLie : g1_lieAlgebra Gk =
      (complexSpan (gkLie E R J).toSubmodule).map (LinearMap.toMatrix b b).toLinearMap)
    (hIs : HodgeLieIsGk H hH E R J) : Hg.carrier = Gk.carrier := by
  refine g1_eq_of_lie_eq_aux Hg Gk hHg hGk ?_
  rw [hHgLie, hGkLie]
  exact congrArg _ hIs

end HodgeLean.Foundations
