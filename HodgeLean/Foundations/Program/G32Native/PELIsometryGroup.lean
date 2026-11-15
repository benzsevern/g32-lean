import HodgeLean.Foundations.MatrixAlgGroupLie

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations MvPolynomial
variable {k : Type*} [Field k] {n : ℕ}

/-- Isometries commuting with a retained family of operators, including
noninvertible operators. In particular the scalar and quaternion generators
can all be retained without choosing units.
Source: Birkenhake–Lange, Complex Abelian Varieties, §§5.5, 9.6;
Abdulali, International Journal of Mathematics 10 (1999), §2.5. -/
def pelIsometrySubgroup (Ω : Matrix (Fin n) (Fin n) k)
    (S : Set (Matrix (Fin n) (Fin n) k)) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) k) :=
  (g1_isometrySubgroup Ω) ⊓
    { carrier := {g | ∀ T ∈ S, Commute (g : Matrix (Fin n) (Fin n) k) T}
      one_mem' := by intro T hT; exact Commute.one_left T
      mul_mem' := by intro a b ha hb T hT; exact (ha T hT).mul_left (hb T hT)
      inv_mem' := by intro a ha T hT; exact (ha T hT).units_inv_left }

private theorem eval_isometry (Ω : Matrix (Fin n) (Fin n) k)
    (g : Matrix.GeneralLinearGroup (Fin n) k) (i j : Fin n) :
    eval (g1_coords g) (g1_isometryEquations Ω i j) =
      ((g : Matrix (Fin n) (Fin n) k).transpose * Ω * g - Ω) i j := by
  have h := (g1_isometryGroup Ω).equations_iff g
  have hΩ : (eval (g1_coords g)).mapMatrix (Ω.map C) = Ω := by ext a b; simp
  have hx := g1_mapMatrix_eval_varMatrix g
  have ht : (eval (g1_coords g)).mapMatrix (g1_varMatrix k n).transpose =
      (g : Matrix (Fin n) (Fin n) k).transpose := by
    ext a b
    simp [g1_varMatrix, g1_coords]
  have hm : (eval (g1_coords g)).mapMatrix (g1_isometryEquations Ω) =
      (g : Matrix (Fin n) (Fin n) k).transpose * Ω * g - Ω := by
    rw [g1_isometryEquations, map_sub, map_mul, map_mul, hΩ, ht, hx]
  exact congrArg (fun M : Matrix (Fin n) (Fin n) k => M i j) hm

/-- The D-linear polarization isometries as a matrix algebraic group,
constructed from their isometry and commutator equations.
Source: Borel, Linear Algebraic Groups, second edition, §§1.6–1.7;
Abdulali, Annals 155 (2002), §§3.1–3.3. -/
def pelIsometryGroup (Ω : Matrix (Fin n) (Fin n) k)
    (S : Set (Matrix (Fin n) (Fin n) k)) : MatrixAlgGroup k n :=
  g1_ofEquations
    ({f | ∃ i j, f = g1_isometryEquations Ω i j} ∪
      {f | ∃ T ∈ S, ∃ i j, f = g1_commEquation T i j})
    (pelIsometrySubgroup Ω S) (by
      intro g
      constructor
      · rintro ⟨hg, hc⟩ f (⟨i, j, rfl⟩ | ⟨T, hT, i, j, rfl⟩)
        · rw [eval_isometry, hg, sub_self]; rfl
        · rw [g1_eval_commEquation]
          change ((g : Matrix (Fin n) (Fin n) k) * T - T * g) i j = 0
          rw [(hc T hT).eq, sub_self]; rfl
      · intro hg
        constructor
        · change (g : Matrix (Fin n) (Fin n) k).transpose * Ω * g = Ω
          apply sub_eq_zero.mp
          ext i j
          exact (eval_isometry Ω g i j) ▸ hg _ (Or.inl ⟨i, j, rfl⟩)
        · intro T hT
          apply sub_eq_zero.mp
          ext i j
          have h := hg _ (Or.inr ⟨T, hT, i, j, rfl⟩)
          rw [g1_eval_commEquation] at h
          exact h)

/-- Membership retains both the polarization and every specified operator.
Source: Borel, Linear Algebraic Groups, second edition, §§1.6–1.7. -/
theorem mem_pelIsometryGroup (Ω : Matrix (Fin n) (Fin n) k)
    (S : Set (Matrix (Fin n) (Fin n) k)) (g : Matrix.GeneralLinearGroup (Fin n) k) :
    g ∈ (pelIsometryGroup Ω S).carrier ↔
      (g : Matrix (Fin n) (Fin n) k).transpose * Ω * g = Ω ∧
      ∀ T ∈ S, (g : Matrix (Fin n) (Fin n) k) * T = T * g := Iff.rfl

/-- The connected PEL group, using the Zariski identity component of the
D-linear polarization isometries.
Source: Abdulali, International Journal of Mathematics 10 (1999), §2.5;
Borel, Linear Algebraic Groups, second edition, §1.2. -/
def pelGenericGroup (Ω : Matrix (Fin n) (Fin n) k)
    (S : Set (Matrix (Fin n) (Fin n) k)) : Set (Matrix.GeneralLinearGroup (Fin n) k) :=
  g1_identityComponent (pelIsometryGroup Ω S)

#print axioms pelIsometrySubgroup
#print axioms pelIsometryGroup
#print axioms mem_pelIsometryGroup
#print axioms pelGenericGroup
end HodgeLean.Foundations.Program.GeneralTypeIII
