import HodgeLean.Foundations.Library.Lie.SpecialOrthogonalCoordinates

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Library.Lie
open LieAlgebra.Orthogonal
attribute [local instance 100] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma pelSkew_reverse (a b : n) : pelSkew (K := K) b a = -pelSkew (K := K) a b := by
  simp [pelSkew, neg_sub]

lemma pelSkew_bracket_chain (a b c : n) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ⁅pelSkew (K := K) a b, pelSkew (K := K) b c⁆ = pelSkew (K := K) a c := by
  ext p q
  rw [pelSkew_bracket_entry]
  simp only [pelSkew, Matrix.sub_apply, Matrix.single_apply]
  by_cases hp : p = a <;> by_cases hp' : p = b <;> by_cases hp'' : p = c <;>
    by_cases hq : q = a <;> by_cases hq' : q = b <;> by_cases hq'' : q = c <;>
    simp_all [Ne.symm hab, Ne.symm hbc, Ne.symm hac, eq_comm]

/-- Two specified distinct indices extend to five distinct positions. -/
lemma pel_five_positions {m : ℕ} (hm : 5 ≤ m) (a b : Fin m) (hab : a ≠ b) :
    ∃ f : Fin 5 → Fin m, Function.Injective f ∧ f 0 = a ∧ f 1 = b := by
  let z : Fin m := ⟨0, by omega⟩
  let o : Fin m := ⟨1, by omega⟩
  let e := Equiv.swap z a
  have he : e z = a := Equiv.swap_apply_left z a
  let d := e.symm b
  have hd : d ≠ z := by
    intro h
    have : b = a := by simpa [d, he] using congrArg e h
    exact hab this.symm
  let σ := (Equiv.swap o d).trans e
  refine ⟨fun i => σ (Fin.castLE hm i), σ.injective.comp (Fin.castLE_injective hm), ?_, ?_⟩
  · change e (Equiv.swap o d z) = a
    rw [Equiv.swap_apply_of_ne_of_ne (by simp [z, o]) hd.symm, he]
  · change e (Equiv.swap o d o) = b
    rw [Equiv.swap_apply_left]
    exact e.apply_symm_apply b

/-- An ideal containing one elementary skew matrix contains all of them. -/
lemma pelSkew_generate (S : Submodule K (Matrix n n K))
    (hS : ∀ (a b : n) (X : Matrix n n K), X ∈ S → ⁅pelSkew (K := K) a b, X⁆ ∈ S)
    (a b : n) (hab : a ≠ b) (hseed : pelSkew (K := K) a b ∈ S) :
    ∀ i j, pelSkew (K := K) i j ∈ S := by
  have first (i : n) : pelSkew (K := K) a i ∈ S := by
    by_cases hi : i = a
    · subst i
      simpa [pelSkew] using S.zero_mem
    by_cases hib : i = b
    · simpa [hib] using hseed
    have h := hS b i _ hseed
    rw [← lie_skew, pelSkew_bracket_chain a b i hab (Ne.symm hib) (Ne.symm hi)] at h
    simpa using S.neg_mem h
  intro i j
  by_cases hi : i = a
  · simpa [hi] using first j
  by_cases hj : j = a
  · rw [hj, pelSkew_reverse]
    exact S.neg_mem (first i)
  by_cases hij : i = j
  · subst j
    simpa [pelSkew] using S.zero_mem
  have h := hS i a _ (first j)
  rwa [pelSkew_bracket_chain i a j hi (Ne.symm hj) hij] at h

lemma pelSkew_sum (X : Matrix n n K) (hX : X ∈ so n K) :
    (2 : K)⁻¹ • ∑ i, ∑ j, X i j • pelSkew (K := K) i j = X := by
  ext p q
  have hs : X q p = -X p q := congrFun (congrFun ((mem_so n K X).mp hX) p) q
  simp only [Matrix.smul_apply, Matrix.sum_apply, pelSkew, Matrix.sub_apply,
    Matrix.single_apply, smul_eq_mul]
  simp [ite_and, mul_sub, mul_ite, Finset.sum_sub_distrib, hs]
  ring

/-- Orthogonal Lie algebras in at least five coordinates are simple in
characteristic zero.
Source: Humphreys, Introduction to Lie Algebras and Representation Theory,
§§1.2, 19 (the orthogonal series and elementary root generators). -/
theorem pel_orthogonal_isSimple_aux {m : ℕ} (hm : 5 ≤ m) :
    LieAlgebra.IsSimple K (so (Fin m) K) := by
  refine ⟨fun I => ?_, ?_⟩
  · by_cases hI : I = ⊥
    · exact Or.inl hI
    right
    obtain ⟨y, hyI, hy0⟩ := (Submodule.ne_bot_iff (LieSubmodule.toSubmodule I)).mp
      (by rwa [ne_eq, LieSubmodule.toSubmodule_eq_bot])
    let S : Submodule K (Matrix (Fin m) (Fin m) K) :=
      (LieSubmodule.toSubmodule I).map (so (Fin m) K).incl.toLinearMap
    have hbr (a b : Fin m) (X : Matrix (Fin m) (Fin m) K) (hX : X ∈ S) :
        ⁅pelSkew (K := K) a b, X⁆ ∈ S := by
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hX
      exact Submodule.mem_map.mpr
        ⟨⁅(⟨pelSkew (K := K) a b, pelSkew_mem a b⟩ : so (Fin m) K), v⁆,
          I.lie_mem hv, rfl⟩
    have hyS : (y : Matrix (Fin m) (Fin m) K) ∈ S := Submodule.mem_map.mpr ⟨y, hyI, rfl⟩
    have hyM : (y : Matrix (Fin m) (Fin m) K) ≠ 0 := fun h => hy0 (Subtype.ext h)
    obtain ⟨a, b, hab0⟩ : ∃ a b, (y : Matrix (Fin m) (Fin m) K) a b ≠ 0 := by
      by_contra! h
      exact hyM (by ext i j; exact h i j)
    have hab : a ≠ b := by
      intro h
      subst b
      have hs := congrFun (congrFun ((mem_so (Fin m) K y.val).mp y.property) a) a
      change y.val a a = -y.val a a at hs
      apply hab0
      linear_combination (1 / 2 : K) * hs
    obtain ⟨f, hf, hfa, hfb⟩ := pel_five_positions hm a b hab
    have hfilter (i j : Fin m) (X : Matrix (Fin m) (Fin m) K) (hX : X ∈ S) :
        ⁅pelSkew (K := K) i j, ⁅pelSkew (K := K) i j, X⁆⁆ ∈ S := hbr _ _ _ (hbr _ _ _ hX)
    have hext := pelSkew_extract f hf y.val y.property
    have hcoef : y.val a b • pelSkew (K := K) a b ∈ S := by
      rw [← hfa, ← hfb]
      rw [← hext]
      exact hfilter _ _ _ (hfilter _ _ _ (hfilter _ _ _ (hfilter _ _ _ hyS)))
    have hseed : pelSkew (K := K) a b ∈ S := by
      have h := S.smul_mem (y.val a b)⁻¹ hcoef
      simpa only [smul_smul, inv_mul_cancel₀ hab0, one_smul] using h
    have hall := pelSkew_generate S hbr a b hab hseed
    rw [eq_top_iff]
    intro z _
    have hzS : z.val ∈ S := by
      rw [← pelSkew_sum z.val z.property]
      exact S.smul_mem _ (S.sum_mem fun i _ => S.sum_mem fun j _ => S.smul_mem _ (hall i j))
    obtain ⟨v, hv, hvz⟩ := Submodule.mem_map.mp hzS
    exact (Subtype.ext hvz : v = z) ▸ hv
  · intro h
    let a : Fin m := ⟨0, by omega⟩
    let b : Fin m := ⟨1, by omega⟩
    let c : Fin m := ⟨2, by omega⟩
    have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
    have hbc : b ≠ c := by simp [b, c, Fin.ext_iff]
    have hac : a ≠ c := by simp [a, c, Fin.ext_iff]
    have hz := congrArg Subtype.val (trivial_lie_zero (so (Fin m) K) (so (Fin m) K)
      ⟨pelSkew (K := K) a b, pelSkew_mem a b⟩ ⟨pelSkew (K := K) b c, pelSkew_mem b c⟩)
    change ⁅pelSkew (K := K) a b, pelSkew (K := K) b c⁆ = 0 at hz
    rw [pelSkew_bracket_chain a b c hab hbc hac] at hz
    have := congrFun (congrFun hz a) c
    simpa [pelSkew, Matrix.single_apply, hac, hac.symm] using this

/-- The six-coordinate complex orthogonal Lie algebra is simple. -/
theorem pel_so6_isSimple_aux : LieAlgebra.IsSimple ℂ (so (Fin 6) ℂ) :=
  pel_orthogonal_isSimple_aux (by omega)

end HodgeLean.Foundations.Library.Lie
