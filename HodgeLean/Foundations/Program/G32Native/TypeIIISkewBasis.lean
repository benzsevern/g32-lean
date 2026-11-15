import HodgeLean.Foundations.Program.G32Native.TypeIIISkewKernel
import HodgeLean.Foundations.Program.G32Native.TypeIIIQuaternionDivision
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section
set_option maxHeartbeats 400000
open scoped Quaternion
open Module
namespace HodgeLean.Foundations.Program.G32Native

/-- Finite dimensional nondegenerate skew-Hermitian quaternion forms have
an orthogonal basis with nonzero diagonal entries. -/
theorem typeIII_skew_orthogonal_basis (b : ℚ) (hb : b < 0) :
    letI := typeIIIQuaternionDivisionRing b hb
    ∀ (n : ℕ) {V : Type*} [AddCommGroup V] [Module ℍ[ℚ, -3, 0, b] V]
      [Module.Finite ℍ[ℚ, -3, 0, b] V]
      (H : V → V → ℍ[ℚ, -3, 0, b])
      (haddL : ∀ v w x, H (v + w) x = H v x + H w x)
      (haddR : ∀ v w x, H v (w + x) = H v w + H v x)
      (hsmulL : ∀ (q : ℍ[ℚ, -3, 0, b]) v x, H (q • v) x = q * H v x)
      (hsmulR : ∀ (q : ℍ[ℚ, -3, 0, b]) v x, H v (q • x) = H v x * star q)
      (hskew : ∀ v w, H w v = -star (H v w))
      (hnd : ∀ v, (∀ w, H v w = 0) → v = 0)
      (hdim : finrank ℍ[ℚ, -3, 0, b] V = n),
      ∃ e : Basis (Fin n) ℍ[ℚ, -3, 0, b] V,
        (∀ i j, i ≠ j → H (e i) (e j) = 0) ∧ (∀ i, H (e i) (e i) ≠ 0) := by
  letI := typeIIIQuaternionDivisionRing b hb
  intro n
  induction n with
  | zero =>
    intro V _ _ _ H haddL haddR hsmulL hsmulR hskew hnd hdim
    refine ⟨(Module.finBasis ℍ[ℚ, -3, 0, b] V).reindex (finCongr hdim), ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
  | succ n ih =>
    intro V _ _ _ H haddL haddR hsmulL hsmulR hskew hnd hdim
    letI : Nontrivial V := Module.nontrivial_of_finrank_pos
      (show 0 < finrank ℍ[ℚ, -3, 0, b] V by omega)
    obtain ⟨x, hx⟩ := typeIII_skew_exists_diagonal b H haddL haddR hsmulL hskew hnd
    let p := typeIIISkewCoefficient H haddL hsmulL x
    let K := LinearMap.ker p
    let f := typeIIISkewSplit H haddL hsmulL x hx
    have hdimK : finrank ℍ[ℚ, -3, 0, b] K = n := by
      have h := f.finrank_eq
      change finrank ℍ[ℚ, -3, 0, b] (ℍ[ℚ, -3, 0, b] × K) =
        finrank ℍ[ℚ, -3, 0, b] V at h
      rw [Module.finrank_prod, Module.finrank_self, hdim] at h
      omega
    let HK : K → K → ℍ[ℚ, -3, 0, b] := fun u v => H u v
    have hndK : ∀ u, (∀ v, HK u v = 0) → u = 0 :=
      typeIIISkewKernel_nondegenerate H haddL haddR hsmulL hsmulR hnd x hx
    obtain ⟨eK, horthK, hdiagK⟩ := ih HK
      (fun u v w => haddL u v w) (fun u v w => haddR u v w)
      (fun q u v => hsmulL q u v) (fun q u v => hsmulR q u v)
      (fun u v => hskew u v) hndK hdimK
    let e : Basis (Unit ⊕ Fin n) ℍ[ℚ, -3, 0, b] V :=
      ((Basis.singleton Unit ℍ[ℚ, -3, 0, b]).prod eK).map f
    have eleft : e (Sum.inl ()) = x := by
      simp only [e, Basis.map_apply, Basis.prod_apply, Sum.elim_inl, Function.comp_apply,
        LinearMap.inl_apply, Basis.singleton_apply]
      change (1 : ℍ[ℚ, -3, 0, b]) • x + 0 = x
      simp
    have eright (i : Fin n) : e (Sum.inr i) = (eK i : V) := by
      simp only [e, Basis.map_apply, Basis.prod_apply, Sum.elim_inr, Function.comp_apply,
        LinearMap.inr_apply]
      change (0 : ℍ[ℚ, -3, 0, b]) • x + (eK i : V) = _
      simp
    have hker (i : Fin n) : H (eK i : V) x = 0 :=
      (typeIIISkewCoefficient_ker H haddL hsmulL x (eK i) hx).1 (eK i).property
    have horth : ∀ i j, i ≠ j → H (e i) (e j) = 0 := by
      intro i j hij
      rcases i with u | i <;> rcases j with v | j
      · exact (hij (congrArg Sum.inl (Subsingleton.elim _ _))).elim
      · cases u
        rw [eleft, eright, hskew, hker, star_zero, neg_zero]
      · cases v
        rw [eright, eleft, hker]
      · rw [eright, eright]
        exact horthK i j (fun h => hij (congrArg Sum.inr h))
    have hdiag : ∀ i, H (e i) (e i) ≠ 0 := by
      intro i
      rcases i with u | i
      · cases u; simpa only [eleft] using hx
      · simpa only [eright] using hdiagK i
    let σ : (Unit ⊕ Fin n) ≃ Fin (n + 1) :=
      Fintype.equivOfCardEq (by simp [Nat.add_comm])
    refine ⟨e.reindex σ, ?_, ?_⟩
    · intro i j hij
      simp only [Basis.reindex_apply]
      exact horth _ _ (fun h => hij (σ.symm.injective h))
    · intro i
      simp only [Basis.reindex_apply]
      exact hdiag _

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_skew_orthogonal_basis
