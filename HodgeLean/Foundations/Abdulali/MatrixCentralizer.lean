import HodgeLean.Foundations.Abdulali.PolarizedMultiplicity

noncomputable section
namespace HodgeLean.Foundations.Abdulali

/-- The standard matrix action on two copies of a multiplicity module.
Source: Abdulali, Annals of Mathematics 155 (2002), §4, p. 923. -/
def twoCopyAction {U : Type*} [AddCommGroup U] [Module ℂ U]
    (m : Matrix (Fin 2) (Fin 2) ℂ) (z : Fin 2 → U) : Fin 2 → U :=
  fun i => ∑ j, m i j • z j

example {U : Type*} [AddCommGroup U] [Module ℂ U] (z : Fin 2 → U) :
    twoCopyAction (1 : Matrix (Fin 2) (Fin 2) ℂ) z = z := by
  ext i
  fin_cases i <;> simp [twoCopyAction, Fin.sum_univ_two, Matrix.one_apply]

/-- The centralizer of the standard matrix action acts only on the multiplicity
space. The multiplicity operator is unique, including for the zero module.
Source: the matrix-unit centralizer calculation underlying Abdulali,
Annals of Mathematics 155 (2002), §4, p. 923. -/
theorem matrix_centralizer_multiplicity {U : Type*} [AddCommGroup U] [Module ℂ U]
    (X : Module.End ℂ (Fin 2 → U)) :
    (∀ (m : Matrix (Fin 2) (Fin 2) ℂ) z,
      X (twoCopyAction m z) = twoCopyAction m (X z)) ↔
    ∃! T : Module.End ℂ U, ∀ z i, X z i = T (z i) := by
  classical
  constructor
  · intro h
    let T : Module.End ℂ U := (LinearMap.proj (0 : Fin 2)).comp
      (X.comp (LinearMap.single ℂ (fun _ : Fin 2 => U) 0))
    have h0 (z : Fin 2 → U) : X z 0 = T (z 0) := by
      have hz : twoCopyAction (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) z =
          Pi.single 0 (z 0) := by
        ext i; fin_cases i <;> simp [twoCopyAction, Fin.sum_univ_two, Matrix.one_apply]
      have hh := congrFun (h !![1, 0; 0, 0] z) 0
      simpa [hz, twoCopyAction, Fin.sum_univ_two, T] using hh.symm
    have h1 (z : Fin 2 → U) : X z 1 = T (z 1) := by
      have hz : twoCopyAction (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) z =
          Pi.single 0 (z 1) := by
        ext i; fin_cases i <;> simp [twoCopyAction, Fin.sum_univ_two, Matrix.one_apply]
      have hh := congrFun (h !![0, 1; 0, 0] z) 0
      simpa [hz, twoCopyAction, Fin.sum_univ_two, T] using hh.symm
    refine ⟨T, ?_, ?_⟩
    · intro z i; fin_cases i
      · exact h0 z
      · exact h1 z
    · intro S hS
      ext u
      simpa [T] using (hS (Pi.single 0 u) 0).symm
  · rintro ⟨T, hT, _⟩ m z
    ext i
    simp only [hT, twoCopyAction, map_sum, map_smul]

end HodgeLean.Foundations.Abdulali
