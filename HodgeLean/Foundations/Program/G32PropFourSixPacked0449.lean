import HodgeLean.Foundations.Program.G32PropFourSixPacked0187
import HodgeLean.Foundations.Program.G32PropFourSixPacked0448
import HodgeLean.Foundations.Program.G32PropFourSixPacked0442

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_integrationSquare024Word : List (Fin 4) := []

def g32p_integrationSquare024Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare024Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare024_certificate : g32p_archiveWordCertificate g32p_integrationSquare024Word g32p_integrationSquare024Stages = true := by
  decide +kernel

theorem g32p_integrationSquare024_integral : g32p_archiveIntegralWord g32p_integrationSquare024Word = g32p_integrationSquare024Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare024_certificate
  have hx : x = g32p_integrationSquare024Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare024_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_024 g32p_literalMatrix_024) g32p_integrationSquare024Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare024Matrix g32p_literalMatrix_078 := by
  decide +kernel

theorem g32p_integrationSquare024_actual : IsConj (g32p_literalRepresentative 24 * g32p_literalRepresentative 24)
    (g32p_literalRepresentative (g32p_familiesSquare 24)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare024Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_024 g32p_literalMatrix_024) g32p_literalMatrix_078 g32p_integrationSquare024Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_024) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_024) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 78) = _
    exact g32p_literalRepresentative_matrix 78
  · exact g32p_integrationSquare024_integral
  · exact g32p_integrationSquare024_equation

def g32p_integrationSquare025Word : List (Fin 4) := [1, 2, 2, 1]

def g32p_integrationSquare025Matrix : HurwitzPrymRex_Mat := ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

def g32p_integrationSquare025Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare025_certificate : g32p_archiveWordCertificate g32p_integrationSquare025Word g32p_integrationSquare025Stages = true := by
  decide +kernel

theorem g32p_integrationSquare025_integral : g32p_archiveIntegralWord g32p_integrationSquare025Word = g32p_integrationSquare025Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare025_certificate
  have hx : x = g32p_integrationSquare025Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare025_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_025 g32p_literalMatrix_025) g32p_integrationSquare025Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare025Matrix g32p_literalMatrix_004 := by
  decide +kernel

theorem g32p_integrationSquare025_actual : IsConj (g32p_literalRepresentative 25 * g32p_literalRepresentative 25)
    (g32p_literalRepresentative (g32p_familiesSquare 25)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare025Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_025 g32p_literalMatrix_025) g32p_literalMatrix_004 g32p_integrationSquare025Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_025) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_025) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 4) = _
    exact g32p_literalRepresentative_matrix 4
  · exact g32p_integrationSquare025_integral
  · exact g32p_integrationSquare025_equation

def g32p_integrationSquare026Word : List (Fin 4) := [2, 2, 3, 3, 0, 0, 1, 0]

def g32p_integrationSquare026Matrix : HurwitzPrymRex_Mat := ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

def g32p_integrationSquare026Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare026_certificate : g32p_archiveWordCertificate g32p_integrationSquare026Word g32p_integrationSquare026Stages = true := by
  decide +kernel

theorem g32p_integrationSquare026_integral : g32p_archiveIntegralWord g32p_integrationSquare026Word = g32p_integrationSquare026Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare026_certificate
  have hx : x = g32p_integrationSquare026Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare026_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_026 g32p_literalMatrix_026) g32p_integrationSquare026Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare026Matrix g32p_literalMatrix_016 := by
  decide +kernel

theorem g32p_integrationSquare026_actual : IsConj (g32p_literalRepresentative 26 * g32p_literalRepresentative 26)
    (g32p_literalRepresentative (g32p_familiesSquare 26)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare026Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_026 g32p_literalMatrix_026) g32p_literalMatrix_016 g32p_integrationSquare026Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_026) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_026) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 16) = _
    exact g32p_literalRepresentative_matrix 16
  · exact g32p_integrationSquare026_integral
  · exact g32p_integrationSquare026_equation

def g32p_integrationSquare027Word : List (Fin 4) := [0, 3, 0, 0, 1, 0]

def g32p_integrationSquare027Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

def g32p_integrationSquare027Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare027_certificate : g32p_archiveWordCertificate g32p_integrationSquare027Word g32p_integrationSquare027Stages = true := by
  decide +kernel

theorem g32p_integrationSquare027_integral : g32p_archiveIntegralWord g32p_integrationSquare027Word = g32p_integrationSquare027Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare027_certificate
  have hx : x = g32p_integrationSquare027Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare027_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_027 g32p_literalMatrix_027) g32p_integrationSquare027Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare027Matrix g32p_literalMatrix_091 := by
  decide +kernel

theorem g32p_integrationSquare027_actual : IsConj (g32p_literalRepresentative 27 * g32p_literalRepresentative 27)
    (g32p_literalRepresentative (g32p_familiesSquare 27)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare027Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_027 g32p_literalMatrix_027) g32p_literalMatrix_091 g32p_integrationSquare027Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_027) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_027) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 91) = _
    exact g32p_literalRepresentative_matrix 91
  · exact g32p_integrationSquare027_integral
  · exact g32p_integrationSquare027_equation

def g32p_integrationSquare028Word : List (Fin 4) := [0, 1, 2]

def g32p_integrationSquare028Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

def g32p_integrationSquare028Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare028_certificate : g32p_archiveWordCertificate g32p_integrationSquare028Word g32p_integrationSquare028Stages = true := by
  decide +kernel

theorem g32p_integrationSquare028_integral : g32p_archiveIntegralWord g32p_integrationSquare028Word = g32p_integrationSquare028Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare028_certificate
  have hx : x = g32p_integrationSquare028Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare028_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_028 g32p_literalMatrix_028) g32p_integrationSquare028Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare028Matrix g32p_literalMatrix_087 := by
  decide +kernel

theorem g32p_integrationSquare028_actual : IsConj (g32p_literalRepresentative 28 * g32p_literalRepresentative 28)
    (g32p_literalRepresentative (g32p_familiesSquare 28)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare028Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_028 g32p_literalMatrix_028) g32p_literalMatrix_087 g32p_integrationSquare028Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_028) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_028) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 87) = _
    exact g32p_literalRepresentative_matrix 87
  · exact g32p_integrationSquare028_integral
  · exact g32p_integrationSquare028_equation

def g32p_integrationSquare029Word : List (Fin 4) := [1, 2, 2, 1]

def g32p_integrationSquare029Matrix : HurwitzPrymRex_Mat := ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

def g32p_integrationSquare029Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare029_certificate : g32p_archiveWordCertificate g32p_integrationSquare029Word g32p_integrationSquare029Stages = true := by
  decide +kernel

theorem g32p_integrationSquare029_integral : g32p_archiveIntegralWord g32p_integrationSquare029Word = g32p_integrationSquare029Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare029_certificate
  have hx : x = g32p_integrationSquare029Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare029_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_029 g32p_literalMatrix_029) g32p_integrationSquare029Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare029Matrix g32p_literalMatrix_011 := by
  decide +kernel

theorem g32p_integrationSquare029_actual : IsConj (g32p_literalRepresentative 29 * g32p_literalRepresentative 29)
    (g32p_literalRepresentative (g32p_familiesSquare 29)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare029Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_029 g32p_literalMatrix_029) g32p_literalMatrix_011 g32p_integrationSquare029Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_029) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_029) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 11) = _
    exact g32p_literalRepresentative_matrix 11
  · exact g32p_integrationSquare029_integral
  · exact g32p_integrationSquare029_equation

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_integrationSquare030Word : List (Fin 4) := [0, 3, 3, 0, 1]

def g32p_integrationSquare030Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

def g32p_integrationSquare030Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare030_certificate : g32p_archiveWordCertificate g32p_integrationSquare030Word g32p_integrationSquare030Stages = true := by
  decide +kernel

theorem g32p_integrationSquare030_integral : g32p_archiveIntegralWord g32p_integrationSquare030Word = g32p_integrationSquare030Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare030_certificate
  have hx : x = g32p_integrationSquare030Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare030_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_030 g32p_literalMatrix_030) g32p_integrationSquare030Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare030Matrix g32p_literalMatrix_056 := by
  decide +kernel

theorem g32p_integrationSquare030_actual : IsConj (g32p_literalRepresentative 30 * g32p_literalRepresentative 30)
    (g32p_literalRepresentative (g32p_familiesSquare 30)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare030Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_030 g32p_literalMatrix_030) g32p_literalMatrix_056 g32p_integrationSquare030Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_030) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_030) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 56) = _
    exact g32p_literalRepresentative_matrix 56
  · exact g32p_integrationSquare030_integral
  · exact g32p_integrationSquare030_equation

def g32p_integrationSquare031Word : List (Fin 4) := [2, 1, 1, 0, 0]

def g32p_integrationSquare031Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

def g32p_integrationSquare031Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare031_certificate : g32p_archiveWordCertificate g32p_integrationSquare031Word g32p_integrationSquare031Stages = true := by
  decide +kernel

theorem g32p_integrationSquare031_integral : g32p_archiveIntegralWord g32p_integrationSquare031Word = g32p_integrationSquare031Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare031_certificate
  have hx : x = g32p_integrationSquare031Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare031_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_031 g32p_literalMatrix_031) g32p_integrationSquare031Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare031Matrix g32p_literalMatrix_082 := by
  decide +kernel

theorem g32p_integrationSquare031_actual : IsConj (g32p_literalRepresentative 31 * g32p_literalRepresentative 31)
    (g32p_literalRepresentative (g32p_familiesSquare 31)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare031Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_031 g32p_literalMatrix_031) g32p_literalMatrix_082 g32p_integrationSquare031Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_031) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_031) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 82) = _
    exact g32p_literalRepresentative_matrix 82
  · exact g32p_integrationSquare031_integral
  · exact g32p_integrationSquare031_equation

def g32p_integrationSquare032Word : List (Fin 4) := [3, 3, 2, 2, 0, 3]

def g32p_integrationSquare032Matrix : HurwitzPrymRex_Mat := ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

def g32p_integrationSquare032Stages : List HurwitzPrymRex_Mat :=
  [![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]],
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare032_certificate : g32p_archiveWordCertificate g32p_integrationSquare032Word g32p_integrationSquare032Stages = true := by
  decide +kernel

theorem g32p_integrationSquare032_integral : g32p_archiveIntegralWord g32p_integrationSquare032Word = g32p_integrationSquare032Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare032_certificate
  have hx : x = g32p_integrationSquare032Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare032_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_032 g32p_literalMatrix_032) g32p_integrationSquare032Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare032Matrix g32p_literalMatrix_045 := by
  decide +kernel

theorem g32p_integrationSquare032_actual : IsConj (g32p_literalRepresentative 32 * g32p_literalRepresentative 32)
    (g32p_literalRepresentative (g32p_familiesSquare 32)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare032Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_032 g32p_literalMatrix_032) g32p_literalMatrix_045 g32p_integrationSquare032Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_032) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_032) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 45) = _
    exact g32p_literalRepresentative_matrix 45
  · exact g32p_integrationSquare032_integral
  · exact g32p_integrationSquare032_equation

def g32p_integrationSquare033Word : List (Fin 4) := [2, 1, 0, 3, 2, 2, 1, 0]

def g32p_integrationSquare033Matrix : HurwitzPrymRex_Mat := ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

def g32p_integrationSquare033Stages : List HurwitzPrymRex_Mat :=
  [![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]],
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare033_certificate : g32p_archiveWordCertificate g32p_integrationSquare033Word g32p_integrationSquare033Stages = true := by
  decide +kernel

theorem g32p_integrationSquare033_integral : g32p_archiveIntegralWord g32p_integrationSquare033Word = g32p_integrationSquare033Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare033_certificate
  have hx : x = g32p_integrationSquare033Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare033_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_033 g32p_literalMatrix_033) g32p_integrationSquare033Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare033Matrix g32p_literalMatrix_054 := by
  decide +kernel

theorem g32p_integrationSquare033_actual : IsConj (g32p_literalRepresentative 33 * g32p_literalRepresentative 33)
    (g32p_literalRepresentative (g32p_familiesSquare 33)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare033Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_033 g32p_literalMatrix_033) g32p_literalMatrix_054 g32p_integrationSquare033Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_033) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_033) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 54) = _
    exact g32p_literalRepresentative_matrix 54
  · exact g32p_integrationSquare033_integral
  · exact g32p_integrationSquare033_equation

def g32p_integrationSquare034Word : List (Fin 4) := []

def g32p_integrationSquare034Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare034Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare034_certificate : g32p_archiveWordCertificate g32p_integrationSquare034Word g32p_integrationSquare034Stages = true := by
  decide +kernel

theorem g32p_integrationSquare034_integral : g32p_archiveIntegralWord g32p_integrationSquare034Word = g32p_integrationSquare034Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare034_certificate
  have hx : x = g32p_integrationSquare034Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare034_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_034 g32p_literalMatrix_034) g32p_integrationSquare034Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare034Matrix g32p_literalMatrix_097 := by
  decide +kernel

theorem g32p_integrationSquare034_actual : IsConj (g32p_literalRepresentative 34 * g32p_literalRepresentative 34)
    (g32p_literalRepresentative (g32p_familiesSquare 34)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare034Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_034 g32p_literalMatrix_034) g32p_literalMatrix_097 g32p_integrationSquare034Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_034) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_034) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 97) = _
    exact g32p_literalRepresentative_matrix 97
  · exact g32p_integrationSquare034_integral
  · exact g32p_integrationSquare034_equation

def g32p_integrationSquare035Word : List (Fin 4) := [2, 3, 0, 1, 2, 3, 0]

def g32p_integrationSquare035Matrix : HurwitzPrymRex_Mat := ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

def g32p_integrationSquare035Stages : List HurwitzPrymRex_Mat :=
  [![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]],
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]],
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]],
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare035_certificate : g32p_archiveWordCertificate g32p_integrationSquare035Word g32p_integrationSquare035Stages = true := by
  decide +kernel

theorem g32p_integrationSquare035_integral : g32p_archiveIntegralWord g32p_integrationSquare035Word = g32p_integrationSquare035Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare035_certificate
  have hx : x = g32p_integrationSquare035Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare035_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_035 g32p_literalMatrix_035) g32p_integrationSquare035Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare035Matrix g32p_literalMatrix_045 := by
  decide +kernel

theorem g32p_integrationSquare035_actual : IsConj (g32p_literalRepresentative 35 * g32p_literalRepresentative 35)
    (g32p_literalRepresentative (g32p_familiesSquare 35)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare035Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_035 g32p_literalMatrix_035) g32p_literalMatrix_045 g32p_integrationSquare035Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_035) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_035) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 45) = _
    exact g32p_literalRepresentative_matrix 45
  · exact g32p_integrationSquare035_integral
  · exact g32p_integrationSquare035_equation

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_integrationSquare036Word : List (Fin 4) := [2, 3, 0, 1, 0, 0]

def g32p_integrationSquare036Matrix : HurwitzPrymRex_Mat := ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

def g32p_integrationSquare036Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare036_certificate : g32p_archiveWordCertificate g32p_integrationSquare036Word g32p_integrationSquare036Stages = true := by
  decide +kernel

theorem g32p_integrationSquare036_integral : g32p_archiveIntegralWord g32p_integrationSquare036Word = g32p_integrationSquare036Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare036_certificate
  have hx : x = g32p_integrationSquare036Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare036_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_036 g32p_literalMatrix_036) g32p_integrationSquare036Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare036Matrix g32p_literalMatrix_054 := by
  decide +kernel

theorem g32p_integrationSquare036_actual : IsConj (g32p_literalRepresentative 36 * g32p_literalRepresentative 36)
    (g32p_literalRepresentative (g32p_familiesSquare 36)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare036Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_036 g32p_literalMatrix_036) g32p_literalMatrix_054 g32p_integrationSquare036Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_036) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_036) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 54) = _
    exact g32p_literalRepresentative_matrix 54
  · exact g32p_integrationSquare036_integral
  · exact g32p_integrationSquare036_equation

def g32p_integrationSquare037Word : List (Fin 4) := []

def g32p_integrationSquare037Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare037Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare037_certificate : g32p_archiveWordCertificate g32p_integrationSquare037Word g32p_integrationSquare037Stages = true := by
  decide +kernel

theorem g32p_integrationSquare037_integral : g32p_archiveIntegralWord g32p_integrationSquare037Word = g32p_integrationSquare037Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare037_certificate
  have hx : x = g32p_integrationSquare037Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare037_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_037 g32p_literalMatrix_037) g32p_integrationSquare037Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare037Matrix g32p_literalMatrix_096 := by
  decide +kernel

theorem g32p_integrationSquare037_actual : IsConj (g32p_literalRepresentative 37 * g32p_literalRepresentative 37)
    (g32p_literalRepresentative (g32p_familiesSquare 37)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare037Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_037 g32p_literalMatrix_037) g32p_literalMatrix_096 g32p_integrationSquare037Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_037) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_037) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 96) = _
    exact g32p_literalRepresentative_matrix 96
  · exact g32p_integrationSquare037_integral
  · exact g32p_integrationSquare037_equation

def g32p_integrationSquare038Word : List (Fin 4) := [3, 2, 2, 1, 0, 0]

def g32p_integrationSquare038Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

def g32p_integrationSquare038Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]],
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare038_certificate : g32p_archiveWordCertificate g32p_integrationSquare038Word g32p_integrationSquare038Stages = true := by
  decide +kernel

theorem g32p_integrationSquare038_integral : g32p_archiveIntegralWord g32p_integrationSquare038Word = g32p_integrationSquare038Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare038_certificate
  have hx : x = g32p_integrationSquare038Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare038_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_038 g32p_literalMatrix_038) g32p_integrationSquare038Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare038Matrix g32p_literalMatrix_069 := by
  decide +kernel

theorem g32p_integrationSquare038_actual : IsConj (g32p_literalRepresentative 38 * g32p_literalRepresentative 38)
    (g32p_literalRepresentative (g32p_familiesSquare 38)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare038Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_038 g32p_literalMatrix_038) g32p_literalMatrix_069 g32p_integrationSquare038Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_038) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_038) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 69) = _
    exact g32p_literalRepresentative_matrix 69
  · exact g32p_integrationSquare038_integral
  · exact g32p_integrationSquare038_equation

def g32p_integrationSquare039Word : List (Fin 4) := [3, 1, 2, 1, 1, 0]

def g32p_integrationSquare039Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

def g32p_integrationSquare039Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare039_certificate : g32p_archiveWordCertificate g32p_integrationSquare039Word g32p_integrationSquare039Stages = true := by
  decide +kernel

theorem g32p_integrationSquare039_integral : g32p_archiveIntegralWord g32p_integrationSquare039Word = g32p_integrationSquare039Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare039_certificate
  have hx : x = g32p_integrationSquare039Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare039_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_039 g32p_literalMatrix_039) g32p_integrationSquare039Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare039Matrix g32p_literalMatrix_068 := by
  decide +kernel

theorem g32p_integrationSquare039_actual : IsConj (g32p_literalRepresentative 39 * g32p_literalRepresentative 39)
    (g32p_literalRepresentative (g32p_familiesSquare 39)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare039Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_039 g32p_literalMatrix_039) g32p_literalMatrix_068 g32p_integrationSquare039Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_039) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_039) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 68) = _
    exact g32p_literalRepresentative_matrix 68
  · exact g32p_integrationSquare039_integral
  · exact g32p_integrationSquare039_equation

def g32p_integrationSquare040Word : List (Fin 4) := [3, 1, 0, 0, 3]

def g32p_integrationSquare040Matrix : HurwitzPrymRex_Mat := ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 2⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

def g32p_integrationSquare040Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 2⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare040_certificate : g32p_archiveWordCertificate g32p_integrationSquare040Word g32p_integrationSquare040Stages = true := by
  decide +kernel

theorem g32p_integrationSquare040_integral : g32p_archiveIntegralWord g32p_integrationSquare040Word = g32p_integrationSquare040Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare040_certificate
  have hx : x = g32p_integrationSquare040Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare040_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_040 g32p_literalMatrix_040) g32p_integrationSquare040Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare040Matrix g32p_literalMatrix_006 := by
  decide +kernel

theorem g32p_integrationSquare040_actual : IsConj (g32p_literalRepresentative 40 * g32p_literalRepresentative 40)
    (g32p_literalRepresentative (g32p_familiesSquare 40)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare040Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_040 g32p_literalMatrix_040) g32p_literalMatrix_006 g32p_integrationSquare040Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_040) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_040) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 6) = _
    exact g32p_literalRepresentative_matrix 6
  · exact g32p_integrationSquare040_integral
  · exact g32p_integrationSquare040_equation

def g32p_integrationSquare041Word : List (Fin 4) := [3, 2, 2, 3, 0, 0]

def g32p_integrationSquare041Matrix : HurwitzPrymRex_Mat := ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

def g32p_integrationSquare041Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare041_certificate : g32p_archiveWordCertificate g32p_integrationSquare041Word g32p_integrationSquare041Stages = true := by
  decide +kernel

theorem g32p_integrationSquare041_integral : g32p_archiveIntegralWord g32p_integrationSquare041Word = g32p_integrationSquare041Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare041_certificate
  have hx : x = g32p_integrationSquare041Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare041_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_041 g32p_literalMatrix_041) g32p_integrationSquare041Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare041Matrix g32p_literalMatrix_023 := by
  decide +kernel

theorem g32p_integrationSquare041_actual : IsConj (g32p_literalRepresentative 41 * g32p_literalRepresentative 41)
    (g32p_literalRepresentative (g32p_familiesSquare 41)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare041Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_041 g32p_literalMatrix_041) g32p_literalMatrix_023 g32p_integrationSquare041Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_041) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_041) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 23) = _
    exact g32p_literalRepresentative_matrix 23
  · exact g32p_integrationSquare041_integral
  · exact g32p_integrationSquare041_equation

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_integrationSquare042Word : List (Fin 4) := [2, 3, 0, 1, 2, 0, 3, 0]

def g32p_integrationSquare042Matrix : HurwitzPrymRex_Mat := ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

def g32p_integrationSquare042Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]],
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]],
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare042_certificate : g32p_archiveWordCertificate g32p_integrationSquare042Word g32p_integrationSquare042Stages = true := by
  decide +kernel

theorem g32p_integrationSquare042_integral : g32p_archiveIntegralWord g32p_integrationSquare042Word = g32p_integrationSquare042Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare042_certificate
  have hx : x = g32p_integrationSquare042Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare042_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_042 g32p_literalMatrix_042) g32p_integrationSquare042Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare042Matrix g32p_literalMatrix_068 := by
  decide +kernel

theorem g32p_integrationSquare042_actual : IsConj (g32p_literalRepresentative 42 * g32p_literalRepresentative 42)
    (g32p_literalRepresentative (g32p_familiesSquare 42)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare042Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_042 g32p_literalMatrix_042) g32p_literalMatrix_068 g32p_integrationSquare042Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_042) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_042) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 68) = _
    exact g32p_literalRepresentative_matrix 68
  · exact g32p_integrationSquare042_integral
  · exact g32p_integrationSquare042_equation

def g32p_integrationSquare043Word : List (Fin 4) := [2, 2, 3, 2, 0, 1]

def g32p_integrationSquare043Matrix : HurwitzPrymRex_Mat := ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

def g32p_integrationSquare043Stages : List HurwitzPrymRex_Mat :=
  [![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]],
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare043_certificate : g32p_archiveWordCertificate g32p_integrationSquare043Word g32p_integrationSquare043Stages = true := by
  decide +kernel

theorem g32p_integrationSquare043_integral : g32p_archiveIntegralWord g32p_integrationSquare043Word = g32p_integrationSquare043Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare043_certificate
  have hx : x = g32p_integrationSquare043Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare043_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_043 g32p_literalMatrix_043) g32p_integrationSquare043Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare043Matrix g32p_literalMatrix_078 := by
  decide +kernel

theorem g32p_integrationSquare043_actual : IsConj (g32p_literalRepresentative 43 * g32p_literalRepresentative 43)
    (g32p_literalRepresentative (g32p_familiesSquare 43)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare043Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_043 g32p_literalMatrix_043) g32p_literalMatrix_078 g32p_integrationSquare043Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_043) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_043) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 78) = _
    exact g32p_literalRepresentative_matrix 78
  · exact g32p_integrationSquare043_integral
  · exact g32p_integrationSquare043_equation

def g32p_integrationSquare044Word : List (Fin 4) := [3, 2, 2, 3]

def g32p_integrationSquare044Matrix : HurwitzPrymRex_Mat := ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

def g32p_integrationSquare044Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]],
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare044_certificate : g32p_archiveWordCertificate g32p_integrationSquare044Word g32p_integrationSquare044Stages = true := by
  decide +kernel

theorem g32p_integrationSquare044_integral : g32p_archiveIntegralWord g32p_integrationSquare044Word = g32p_integrationSquare044Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare044_certificate
  have hx : x = g32p_integrationSquare044Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare044_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_044 g32p_literalMatrix_044) g32p_integrationSquare044Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare044Matrix g32p_literalMatrix_067 := by
  decide +kernel

theorem g32p_integrationSquare044_actual : IsConj (g32p_literalRepresentative 44 * g32p_literalRepresentative 44)
    (g32p_literalRepresentative (g32p_familiesSquare 44)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare044Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_044 g32p_literalMatrix_044) g32p_literalMatrix_067 g32p_integrationSquare044Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_044) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_044) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 67) = _
    exact g32p_literalRepresentative_matrix 67
  · exact g32p_integrationSquare044_integral
  · exact g32p_integrationSquare044_equation

def g32p_integrationSquare045Word : List (Fin 4) := [3, 0, 0, 1, 1, 2, 1]

def g32p_integrationSquare045Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

def g32p_integrationSquare045Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare045_certificate : g32p_archiveWordCertificate g32p_integrationSquare045Word g32p_integrationSquare045Stages = true := by
  decide +kernel

theorem g32p_integrationSquare045_integral : g32p_archiveIntegralWord g32p_integrationSquare045Word = g32p_integrationSquare045Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare045_certificate
  have hx : x = g32p_integrationSquare045Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare045_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_045 g32p_literalMatrix_045) g32p_integrationSquare045Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare045Matrix g32p_literalMatrix_035 := by
  decide +kernel

theorem g32p_integrationSquare045_actual : IsConj (g32p_literalRepresentative 45 * g32p_literalRepresentative 45)
    (g32p_literalRepresentative (g32p_familiesSquare 45)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare045Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_045 g32p_literalMatrix_045) g32p_literalMatrix_035 g32p_integrationSquare045Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_045) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_045) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 35) = _
    exact g32p_literalRepresentative_matrix 35
  · exact g32p_integrationSquare045_integral
  · exact g32p_integrationSquare045_equation

def g32p_integrationSquare046Word : List (Fin 4) := [3, 1, 0, 0]

def g32p_integrationSquare046Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

def g32p_integrationSquare046Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare046_certificate : g32p_archiveWordCertificate g32p_integrationSquare046Word g32p_integrationSquare046Stages = true := by
  decide +kernel

theorem g32p_integrationSquare046_integral : g32p_archiveIntegralWord g32p_integrationSquare046Word = g32p_integrationSquare046Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare046_certificate
  have hx : x = g32p_integrationSquare046Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare046_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_046 g32p_literalMatrix_046) g32p_integrationSquare046Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare046Matrix g32p_literalMatrix_092 := by
  decide +kernel

theorem g32p_integrationSquare046_actual : IsConj (g32p_literalRepresentative 46 * g32p_literalRepresentative 46)
    (g32p_literalRepresentative (g32p_familiesSquare 46)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare046Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_046 g32p_literalMatrix_046) g32p_literalMatrix_092 g32p_integrationSquare046Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_046) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_046) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 92) = _
    exact g32p_literalRepresentative_matrix 92
  · exact g32p_integrationSquare046_integral
  · exact g32p_integrationSquare046_equation

def g32p_integrationSquare047Word : List (Fin 4) := [0, 3, 1, 0, 0, 1]

def g32p_integrationSquare047Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

def g32p_integrationSquare047Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare047_certificate : g32p_archiveWordCertificate g32p_integrationSquare047Word g32p_integrationSquare047Stages = true := by
  decide +kernel

theorem g32p_integrationSquare047_integral : g32p_archiveIntegralWord g32p_integrationSquare047Word = g32p_integrationSquare047Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare047_certificate
  have hx : x = g32p_integrationSquare047Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare047_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_047 g32p_literalMatrix_047) g32p_integrationSquare047Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare047Matrix g32p_literalMatrix_016 := by
  decide +kernel

theorem g32p_integrationSquare047_actual : IsConj (g32p_literalRepresentative 47 * g32p_literalRepresentative 47)
    (g32p_literalRepresentative (g32p_familiesSquare 47)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare047Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_047 g32p_literalMatrix_047) g32p_literalMatrix_016 g32p_integrationSquare047Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_047) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_047) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 16) = _
    exact g32p_literalRepresentative_matrix 16
  · exact g32p_integrationSquare047_integral
  · exact g32p_integrationSquare047_equation

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_integrationSquare048Word : List (Fin 4) := [2, 1, 1, 0]

def g32p_integrationSquare048Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

def g32p_integrationSquare048Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare048_certificate : g32p_archiveWordCertificate g32p_integrationSquare048Word g32p_integrationSquare048Stages = true := by
  decide +kernel

theorem g32p_integrationSquare048_integral : g32p_archiveIntegralWord g32p_integrationSquare048Word = g32p_integrationSquare048Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare048_certificate
  have hx : x = g32p_integrationSquare048Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare048_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_048 g32p_literalMatrix_048) g32p_integrationSquare048Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare048Matrix g32p_literalMatrix_089 := by
  decide +kernel

theorem g32p_integrationSquare048_actual : IsConj (g32p_literalRepresentative 48 * g32p_literalRepresentative 48)
    (g32p_literalRepresentative (g32p_familiesSquare 48)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare048Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_048 g32p_literalMatrix_048) g32p_literalMatrix_089 g32p_integrationSquare048Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_048) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_048) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 89) = _
    exact g32p_literalRepresentative_matrix 89
  · exact g32p_integrationSquare048_integral
  · exact g32p_integrationSquare048_equation

def g32p_integrationSquare049Word : List (Fin 4) := [2, 1, 1, 0, 3, 0]

def g32p_integrationSquare049Matrix : HurwitzPrymRex_Mat := ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

def g32p_integrationSquare049Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare049_certificate : g32p_archiveWordCertificate g32p_integrationSquare049Word g32p_integrationSquare049Stages = true := by
  decide +kernel

theorem g32p_integrationSquare049_integral : g32p_archiveIntegralWord g32p_integrationSquare049Word = g32p_integrationSquare049Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare049_certificate
  have hx : x = g32p_integrationSquare049Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare049_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_049 g32p_literalMatrix_049) g32p_integrationSquare049Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare049Matrix g32p_literalMatrix_034 := by
  decide +kernel

theorem g32p_integrationSquare049_actual : IsConj (g32p_literalRepresentative 49 * g32p_literalRepresentative 49)
    (g32p_literalRepresentative (g32p_familiesSquare 49)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare049Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_049 g32p_literalMatrix_049) g32p_literalMatrix_034 g32p_integrationSquare049Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_049) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_049) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 34) = _
    exact g32p_literalRepresentative_matrix 34
  · exact g32p_integrationSquare049_integral
  · exact g32p_integrationSquare049_equation

def g32p_integrationSquare050Word : List (Fin 4) := [0, 3, 1, 0, 0, 1]

def g32p_integrationSquare050Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

def g32p_integrationSquare050Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare050_certificate : g32p_archiveWordCertificate g32p_integrationSquare050Word g32p_integrationSquare050Stages = true := by
  decide +kernel

theorem g32p_integrationSquare050_integral : g32p_archiveIntegralWord g32p_integrationSquare050Word = g32p_integrationSquare050Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare050_certificate
  have hx : x = g32p_integrationSquare050Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare050_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_literalMatrix_050) g32p_integrationSquare050Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare050Matrix g32p_literalMatrix_004 := by
  decide +kernel

theorem g32p_integrationSquare050_actual : IsConj (g32p_literalRepresentative 50 * g32p_literalRepresentative 50)
    (g32p_literalRepresentative (g32p_familiesSquare 50)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare050Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_literalMatrix_050) g32p_literalMatrix_004 g32p_integrationSquare050Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_050) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_050) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 4) = _
    exact g32p_literalRepresentative_matrix 4
  · exact g32p_integrationSquare050_integral
  · exact g32p_integrationSquare050_equation

def g32p_integrationSquare051Word : List (Fin 4) := [2, 2, 3, 0, 1]

def g32p_integrationSquare051Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

def g32p_integrationSquare051Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare051_certificate : g32p_archiveWordCertificate g32p_integrationSquare051Word g32p_integrationSquare051Stages = true := by
  decide +kernel

theorem g32p_integrationSquare051_integral : g32p_archiveIntegralWord g32p_integrationSquare051Word = g32p_integrationSquare051Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare051_certificate
  have hx : x = g32p_integrationSquare051Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare051_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_051 g32p_literalMatrix_051) g32p_integrationSquare051Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare051Matrix g32p_literalMatrix_087 := by
  decide +kernel

theorem g32p_integrationSquare051_actual : IsConj (g32p_literalRepresentative 51 * g32p_literalRepresentative 51)
    (g32p_literalRepresentative (g32p_familiesSquare 51)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare051Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_051 g32p_literalMatrix_051) g32p_literalMatrix_087 g32p_integrationSquare051Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_051) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_051) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 87) = _
    exact g32p_literalRepresentative_matrix 87
  · exact g32p_integrationSquare051_integral
  · exact g32p_integrationSquare051_equation

def g32p_integrationSquare052Word : List (Fin 4) := [2, 3, 3, 1, 2]

def g32p_integrationSquare052Matrix : HurwitzPrymRex_Mat := ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

def g32p_integrationSquare052Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare052_certificate : g32p_archiveWordCertificate g32p_integrationSquare052Word g32p_integrationSquare052Stages = true := by
  decide +kernel

theorem g32p_integrationSquare052_integral : g32p_archiveIntegralWord g32p_integrationSquare052Word = g32p_integrationSquare052Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare052_certificate
  have hx : x = g32p_integrationSquare052Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare052_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_052 g32p_literalMatrix_052) g32p_integrationSquare052Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare052Matrix g32p_literalMatrix_065 := by
  decide +kernel

theorem g32p_integrationSquare052_actual : IsConj (g32p_literalRepresentative 52 * g32p_literalRepresentative 52)
    (g32p_literalRepresentative (g32p_familiesSquare 52)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare052Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_052 g32p_literalMatrix_052) g32p_literalMatrix_065 g32p_integrationSquare052Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_052) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_052) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 65) = _
    exact g32p_literalRepresentative_matrix 65
  · exact g32p_integrationSquare052_integral
  · exact g32p_integrationSquare052_equation

def g32p_integrationSquare053Word : List (Fin 4) := [3, 2, 2, 3, 2, 0, 0, 1]

def g32p_integrationSquare053Matrix : HurwitzPrymRex_Mat := ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

def g32p_integrationSquare053Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]],
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare053_certificate : g32p_archiveWordCertificate g32p_integrationSquare053Word g32p_integrationSquare053Stages = true := by
  decide +kernel

theorem g32p_integrationSquare053_integral : g32p_archiveIntegralWord g32p_integrationSquare053Word = g32p_integrationSquare053Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare053_certificate
  have hx : x = g32p_integrationSquare053Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare053_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_053 g32p_literalMatrix_053) g32p_integrationSquare053Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare053Matrix g32p_literalMatrix_014 := by
  decide +kernel

theorem g32p_integrationSquare053_actual : IsConj (g32p_literalRepresentative 53 * g32p_literalRepresentative 53)
    (g32p_literalRepresentative (g32p_familiesSquare 53)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare053Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_053 g32p_literalMatrix_053) g32p_literalMatrix_014 g32p_integrationSquare053Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_053) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_053) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 14) = _
    exact g32p_literalRepresentative_matrix 14
  · exact g32p_integrationSquare053_integral
  · exact g32p_integrationSquare053_equation

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_integrationSquare054Word : List (Fin 4) := [3, 1, 1, 2, 0, 0, 3, 0, 0]

def g32p_integrationSquare054Matrix : HurwitzPrymRex_Mat := ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

def g32p_integrationSquare054Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare054_certificate : g32p_archiveWordCertificate g32p_integrationSquare054Word g32p_integrationSquare054Stages = true := by
  decide +kernel

theorem g32p_integrationSquare054_integral : g32p_archiveIntegralWord g32p_integrationSquare054Word = g32p_integrationSquare054Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare054_certificate
  have hx : x = g32p_integrationSquare054Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare054_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_054 g32p_literalMatrix_054) g32p_integrationSquare054Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare054Matrix g32p_literalMatrix_036 := by
  decide +kernel

theorem g32p_integrationSquare054_actual : IsConj (g32p_literalRepresentative 54 * g32p_literalRepresentative 54)
    (g32p_literalRepresentative (g32p_familiesSquare 54)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare054Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_054 g32p_literalMatrix_054) g32p_literalMatrix_036 g32p_integrationSquare054Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_054) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_054) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 36) = _
    exact g32p_literalRepresentative_matrix 36
  · exact g32p_integrationSquare054_integral
  · exact g32p_integrationSquare054_equation

def g32p_integrationSquare055Word : List (Fin 4) := [3, 2, 1, 0, 0, 1]

def g32p_integrationSquare055Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

def g32p_integrationSquare055Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare055_certificate : g32p_archiveWordCertificate g32p_integrationSquare055Word g32p_integrationSquare055Stages = true := by
  decide +kernel

theorem g32p_integrationSquare055_integral : g32p_archiveIntegralWord g32p_integrationSquare055Word = g32p_integrationSquare055Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare055_certificate
  have hx : x = g32p_integrationSquare055Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare055_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_055 g32p_literalMatrix_055) g32p_integrationSquare055Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare055Matrix g32p_literalMatrix_091 := by
  decide +kernel

theorem g32p_integrationSquare055_actual : IsConj (g32p_literalRepresentative 55 * g32p_literalRepresentative 55)
    (g32p_literalRepresentative (g32p_familiesSquare 55)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare055Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_055 g32p_literalMatrix_055) g32p_literalMatrix_091 g32p_integrationSquare055Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_055) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_055) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 91) = _
    exact g32p_literalRepresentative_matrix 91
  · exact g32p_integrationSquare055_integral
  · exact g32p_integrationSquare055_equation

def g32p_integrationSquare056Word : List (Fin 4) := [3, 2, 2, 3, 1, 0, 0, 1]

def g32p_integrationSquare056Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

def g32p_integrationSquare056Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare056_certificate : g32p_archiveWordCertificate g32p_integrationSquare056Word g32p_integrationSquare056Stages = true := by
  decide +kernel

theorem g32p_integrationSquare056_integral : g32p_archiveIntegralWord g32p_integrationSquare056Word = g32p_integrationSquare056Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare056_certificate
  have hx : x = g32p_integrationSquare056Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare056_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_056 g32p_literalMatrix_056) g32p_integrationSquare056Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare056Matrix g32p_literalMatrix_004 := by
  decide +kernel

theorem g32p_integrationSquare056_actual : IsConj (g32p_literalRepresentative 56 * g32p_literalRepresentative 56)
    (g32p_literalRepresentative (g32p_familiesSquare 56)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare056Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_056 g32p_literalMatrix_056) g32p_literalMatrix_004 g32p_integrationSquare056Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_056) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_056) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 4) = _
    exact g32p_literalRepresentative_matrix 4
  · exact g32p_integrationSquare056_integral
  · exact g32p_integrationSquare056_equation

def g32p_integrationSquare057Word : List (Fin 4) := [0, 0, 3, 3, 1, 0]

def g32p_integrationSquare057Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

def g32p_integrationSquare057Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare057_certificate : g32p_archiveWordCertificate g32p_integrationSquare057Word g32p_integrationSquare057Stages = true := by
  decide +kernel

theorem g32p_integrationSquare057_integral : g32p_archiveIntegralWord g32p_integrationSquare057Word = g32p_integrationSquare057Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare057_certificate
  have hx : x = g32p_integrationSquare057Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare057_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_057 g32p_literalMatrix_057) g32p_integrationSquare057Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare057Matrix g32p_literalMatrix_013 := by
  decide +kernel

theorem g32p_integrationSquare057_actual : IsConj (g32p_literalRepresentative 57 * g32p_literalRepresentative 57)
    (g32p_literalRepresentative (g32p_familiesSquare 57)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare057Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_057 g32p_literalMatrix_057) g32p_literalMatrix_013 g32p_integrationSquare057Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_057) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_057) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 13) = _
    exact g32p_literalRepresentative_matrix 13
  · exact g32p_integrationSquare057_integral
  · exact g32p_integrationSquare057_equation

def g32p_integrationSquare058Word : List (Fin 4) := [3, 0, 0, 1, 0]

def g32p_integrationSquare058Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

def g32p_integrationSquare058Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare058_certificate : g32p_archiveWordCertificate g32p_integrationSquare058Word g32p_integrationSquare058Stages = true := by
  decide +kernel

theorem g32p_integrationSquare058_integral : g32p_archiveIntegralWord g32p_integrationSquare058Word = g32p_integrationSquare058Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare058_certificate
  have hx : x = g32p_integrationSquare058Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare058_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_058 g32p_literalMatrix_058) g32p_integrationSquare058Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare058Matrix g32p_literalMatrix_081 := by
  decide +kernel

theorem g32p_integrationSquare058_actual : IsConj (g32p_literalRepresentative 58 * g32p_literalRepresentative 58)
    (g32p_literalRepresentative (g32p_familiesSquare 58)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare058Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_058 g32p_literalMatrix_058) g32p_literalMatrix_081 g32p_integrationSquare058Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_058) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_058) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 81) = _
    exact g32p_literalRepresentative_matrix 81
  · exact g32p_integrationSquare058_integral
  · exact g32p_integrationSquare058_equation

def g32p_integrationSquare059Word : List (Fin 4) := [3, 3, 0, 0, 1]

def g32p_integrationSquare059Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

def g32p_integrationSquare059Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare059_certificate : g32p_archiveWordCertificate g32p_integrationSquare059Word g32p_integrationSquare059Stages = true := by
  decide +kernel

theorem g32p_integrationSquare059_integral : g32p_archiveIntegralWord g32p_integrationSquare059Word = g32p_integrationSquare059Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare059_certificate
  have hx : x = g32p_integrationSquare059Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare059_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_literalMatrix_059) g32p_integrationSquare059Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare059Matrix g32p_literalMatrix_011 := by
  decide +kernel

theorem g32p_integrationSquare059_actual : IsConj (g32p_literalRepresentative 59 * g32p_literalRepresentative 59)
    (g32p_literalRepresentative (g32p_familiesSquare 59)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare059Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_literalMatrix_059) g32p_literalMatrix_011 g32p_integrationSquare059Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_059) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_059) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 11) = _
    exact g32p_literalRepresentative_matrix 11
  · exact g32p_integrationSquare059_integral
  · exact g32p_integrationSquare059_equation

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_integrationSquare060Word : List (Fin 4) := [3, 2, 1, 0, 0, 3, 2, 1]

def g32p_integrationSquare060Matrix : HurwitzPrymRex_Mat := ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

def g32p_integrationSquare060Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare060_certificate : g32p_archiveWordCertificate g32p_integrationSquare060Word g32p_integrationSquare060Stages = true := by
  decide +kernel

theorem g32p_integrationSquare060_integral : g32p_archiveIntegralWord g32p_integrationSquare060Word = g32p_integrationSquare060Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare060_certificate
  have hx : x = g32p_integrationSquare060Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare060_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_060 g32p_literalMatrix_060) g32p_integrationSquare060Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare060Matrix g32p_literalMatrix_026 := by
  decide +kernel

theorem g32p_integrationSquare060_actual : IsConj (g32p_literalRepresentative 60 * g32p_literalRepresentative 60)
    (g32p_literalRepresentative (g32p_familiesSquare 60)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare060Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_060 g32p_literalMatrix_060) g32p_literalMatrix_026 g32p_integrationSquare060Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_060) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_060) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 26) = _
    exact g32p_literalRepresentative_matrix 26
  · exact g32p_integrationSquare060_integral
  · exact g32p_integrationSquare060_equation

def g32p_integrationSquare061Word : List (Fin 4) := [1, 2, 2, 1]

def g32p_integrationSquare061Matrix : HurwitzPrymRex_Mat := ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

def g32p_integrationSquare061Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare061_certificate : g32p_archiveWordCertificate g32p_integrationSquare061Word g32p_integrationSquare061Stages = true := by
  decide +kernel

theorem g32p_integrationSquare061_integral : g32p_archiveIntegralWord g32p_integrationSquare061Word = g32p_integrationSquare061Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare061_certificate
  have hx : x = g32p_integrationSquare061Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare061_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_061 g32p_literalMatrix_061) g32p_integrationSquare061Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare061Matrix g32p_literalMatrix_051 := by
  decide +kernel

theorem g32p_integrationSquare061_actual : IsConj (g32p_literalRepresentative 61 * g32p_literalRepresentative 61)
    (g32p_literalRepresentative (g32p_familiesSquare 61)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare061Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_061 g32p_literalMatrix_061) g32p_literalMatrix_051 g32p_integrationSquare061Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_061) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_061) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 51) = _
    exact g32p_literalRepresentative_matrix 51
  · exact g32p_integrationSquare061_integral
  · exact g32p_integrationSquare061_equation

def g32p_integrationSquare062Word : List (Fin 4) := [3, 1, 2, 2, 3, 1, 2, 1, 0]

def g32p_integrationSquare062Matrix : HurwitzPrymRex_Mat := ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

def g32p_integrationSquare062Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]],
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare062_certificate : g32p_archiveWordCertificate g32p_integrationSquare062Word g32p_integrationSquare062Stages = true := by
  decide +kernel

theorem g32p_integrationSquare062_integral : g32p_archiveIntegralWord g32p_integrationSquare062Word = g32p_integrationSquare062Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare062_certificate
  have hx : x = g32p_integrationSquare062Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare062_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_062 g32p_literalMatrix_062) g32p_integrationSquare062Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare062Matrix g32p_literalMatrix_009 := by
  decide +kernel

theorem g32p_integrationSquare062_actual : IsConj (g32p_literalRepresentative 62 * g32p_literalRepresentative 62)
    (g32p_literalRepresentative (g32p_familiesSquare 62)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare062Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_062 g32p_literalMatrix_062) g32p_literalMatrix_009 g32p_integrationSquare062Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_062) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_062) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 9) = _
    exact g32p_literalRepresentative_matrix 9
  · exact g32p_integrationSquare062_integral
  · exact g32p_integrationSquare062_equation

def g32p_integrationSquare063Word : List (Fin 4) := [3, 1, 0, 0, 3, 1, 0]

def g32p_integrationSquare063Matrix : HurwitzPrymRex_Mat := ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

def g32p_integrationSquare063Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare063_certificate : g32p_archiveWordCertificate g32p_integrationSquare063Word g32p_integrationSquare063Stages = true := by
  decide +kernel

theorem g32p_integrationSquare063_integral : g32p_archiveIntegralWord g32p_integrationSquare063Word = g32p_integrationSquare063Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare063_certificate
  have hx : x = g32p_integrationSquare063Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare063_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_063 g32p_literalMatrix_063) g32p_integrationSquare063Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare063Matrix g32p_literalMatrix_081 := by
  decide +kernel

theorem g32p_integrationSquare063_actual : IsConj (g32p_literalRepresentative 63 * g32p_literalRepresentative 63)
    (g32p_literalRepresentative (g32p_familiesSquare 63)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare063Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_063 g32p_literalMatrix_063) g32p_literalMatrix_081 g32p_integrationSquare063Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_063) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_063) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 81) = _
    exact g32p_literalRepresentative_matrix 81
  · exact g32p_integrationSquare063_integral
  · exact g32p_integrationSquare063_equation

def g32p_integrationSquare064Word : List (Fin 4) := [2]

def g32p_integrationSquare064Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

def g32p_integrationSquare064Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare064_certificate : g32p_archiveWordCertificate g32p_integrationSquare064Word g32p_integrationSquare064Stages = true := by
  decide +kernel

theorem g32p_integrationSquare064_integral : g32p_archiveIntegralWord g32p_integrationSquare064Word = g32p_integrationSquare064Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare064_certificate
  have hx : x = g32p_integrationSquare064Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare064_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_064 g32p_literalMatrix_064) g32p_integrationSquare064Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare064Matrix g32p_literalMatrix_100 := by
  decide +kernel

theorem g32p_integrationSquare064_actual : IsConj (g32p_literalRepresentative 64 * g32p_literalRepresentative 64)
    (g32p_literalRepresentative (g32p_familiesSquare 64)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare064Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_064 g32p_literalMatrix_064) g32p_literalMatrix_100 g32p_integrationSquare064Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_064) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_064) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 100) = _
    exact g32p_literalRepresentative_matrix 100
  · exact g32p_integrationSquare064_integral
  · exact g32p_integrationSquare064_equation

def g32p_integrationSquare065Word : List (Fin 4) := []

def g32p_integrationSquare065Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare065Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare065_certificate : g32p_archiveWordCertificate g32p_integrationSquare065Word g32p_integrationSquare065Stages = true := by
  decide +kernel

theorem g32p_integrationSquare065_integral : g32p_archiveIntegralWord g32p_integrationSquare065Word = g32p_integrationSquare065Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare065_certificate
  have hx : x = g32p_integrationSquare065Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare065_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_065 g32p_literalMatrix_065) g32p_integrationSquare065Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare065Matrix g32p_literalMatrix_096 := by
  decide +kernel

theorem g32p_integrationSquare065_actual : IsConj (g32p_literalRepresentative 65 * g32p_literalRepresentative 65)
    (g32p_literalRepresentative (g32p_familiesSquare 65)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare065Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_065 g32p_literalMatrix_065) g32p_literalMatrix_096 g32p_integrationSquare065Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_065) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_065) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 96) = _
    exact g32p_literalRepresentative_matrix 96
  · exact g32p_integrationSquare065_integral
  · exact g32p_integrationSquare065_equation

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_integrationSquare066Word : List (Fin 4) := [3, 0, 0, 3, 2, 0, 0]

def g32p_integrationSquare066Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

def g32p_integrationSquare066Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]],
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare066_certificate : g32p_archiveWordCertificate g32p_integrationSquare066Word g32p_integrationSquare066Stages = true := by
  decide +kernel

theorem g32p_integrationSquare066_integral : g32p_archiveIntegralWord g32p_integrationSquare066Word = g32p_integrationSquare066Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare066_certificate
  have hx : x = g32p_integrationSquare066Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare066_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_066 g32p_literalMatrix_066) g32p_integrationSquare066Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare066Matrix g32p_literalMatrix_045 := by
  decide +kernel

theorem g32p_integrationSquare066_actual : IsConj (g32p_literalRepresentative 66 * g32p_literalRepresentative 66)
    (g32p_literalRepresentative (g32p_familiesSquare 66)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare066Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_066 g32p_literalMatrix_066) g32p_literalMatrix_045 g32p_integrationSquare066Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_066) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_066) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 45) = _
    exact g32p_literalRepresentative_matrix 45
  · exact g32p_integrationSquare066_integral
  · exact g32p_integrationSquare066_equation

def g32p_integrationSquare067Word : List (Fin 4) := []

def g32p_integrationSquare067Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare067Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare067_certificate : g32p_archiveWordCertificate g32p_integrationSquare067Word g32p_integrationSquare067Stages = true := by
  decide +kernel

theorem g32p_integrationSquare067_integral : g32p_archiveIntegralWord g32p_integrationSquare067Word = g32p_integrationSquare067Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare067_certificate
  have hx : x = g32p_integrationSquare067Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare067_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_067 g32p_literalMatrix_067) g32p_integrationSquare067Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare067Matrix g32p_literalMatrix_076 := by
  decide +kernel

theorem g32p_integrationSquare067_actual : IsConj (g32p_literalRepresentative 67 * g32p_literalRepresentative 67)
    (g32p_literalRepresentative (g32p_familiesSquare 67)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare067Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_067 g32p_literalMatrix_067) g32p_literalMatrix_076 g32p_integrationSquare067Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_067) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_067) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 76) = _
    exact g32p_literalRepresentative_matrix 76
  · exact g32p_integrationSquare067_integral
  · exact g32p_integrationSquare067_equation

def g32p_integrationSquare068Word : List (Fin 4) := [2, 2, 0, 0, 3, 2]

def g32p_integrationSquare068Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

def g32p_integrationSquare068Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]],
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare068_certificate : g32p_archiveWordCertificate g32p_integrationSquare068Word g32p_integrationSquare068Stages = true := by
  decide +kernel

theorem g32p_integrationSquare068_integral : g32p_archiveIntegralWord g32p_integrationSquare068Word = g32p_integrationSquare068Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare068_certificate
  have hx : x = g32p_integrationSquare068Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare068_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_068 g32p_literalMatrix_068) g32p_integrationSquare068Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare068Matrix g32p_literalMatrix_042 := by
  decide +kernel

theorem g32p_integrationSquare068_actual : IsConj (g32p_literalRepresentative 68 * g32p_literalRepresentative 68)
    (g32p_literalRepresentative (g32p_familiesSquare 68)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare068Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_068 g32p_literalMatrix_068) g32p_literalMatrix_042 g32p_integrationSquare068Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_068) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_068) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 42) = _
    exact g32p_literalRepresentative_matrix 42
  · exact g32p_integrationSquare068_integral
  · exact g32p_integrationSquare068_equation

def g32p_integrationSquare069Word : List (Fin 4) := []

def g32p_integrationSquare069Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare069Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare069_certificate : g32p_archiveWordCertificate g32p_integrationSquare069Word g32p_integrationSquare069Stages = true := by
  decide +kernel

theorem g32p_integrationSquare069_integral : g32p_archiveIntegralWord g32p_integrationSquare069Word = g32p_integrationSquare069Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare069_certificate
  have hx : x = g32p_integrationSquare069Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare069_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_069 g32p_literalMatrix_069) g32p_integrationSquare069Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare069Matrix g32p_literalMatrix_099 := by
  decide +kernel

theorem g32p_integrationSquare069_actual : IsConj (g32p_literalRepresentative 69 * g32p_literalRepresentative 69)
    (g32p_literalRepresentative (g32p_familiesSquare 69)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare069Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_069 g32p_literalMatrix_069) g32p_literalMatrix_099 g32p_integrationSquare069Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_069) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_069) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 99) = _
    exact g32p_literalRepresentative_matrix 99
  · exact g32p_integrationSquare069_integral
  · exact g32p_integrationSquare069_equation

def g32p_integrationSquare070Word : List (Fin 4) := [0, 3, 1, 1]

def g32p_integrationSquare070Matrix : HurwitzPrymRex_Mat := ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

def g32p_integrationSquare070Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare070_certificate : g32p_archiveWordCertificate g32p_integrationSquare070Word g32p_integrationSquare070Stages = true := by
  decide +kernel

theorem g32p_integrationSquare070_integral : g32p_archiveIntegralWord g32p_integrationSquare070Word = g32p_integrationSquare070Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare070_certificate
  have hx : x = g32p_integrationSquare070Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare070_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_070 g32p_literalMatrix_070) g32p_integrationSquare070Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare070Matrix g32p_literalMatrix_042 := by
  decide +kernel

theorem g32p_integrationSquare070_actual : IsConj (g32p_literalRepresentative 70 * g32p_literalRepresentative 70)
    (g32p_literalRepresentative (g32p_familiesSquare 70)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare070Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_070 g32p_literalMatrix_070) g32p_literalMatrix_042 g32p_integrationSquare070Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_070) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_070) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 42) = _
    exact g32p_literalRepresentative_matrix 42
  · exact g32p_integrationSquare070_integral
  · exact g32p_integrationSquare070_equation

def g32p_integrationSquare071Word : List (Fin 4) := [3, 3, 0, 0, 1]

def g32p_integrationSquare071Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

def g32p_integrationSquare071Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare071_certificate : g32p_archiveWordCertificate g32p_integrationSquare071Word g32p_integrationSquare071Stages = true := by
  decide +kernel

theorem g32p_integrationSquare071_integral : g32p_archiveIntegralWord g32p_integrationSquare071Word = g32p_integrationSquare071Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare071_certificate
  have hx : x = g32p_integrationSquare071Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare071_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_071 g32p_literalMatrix_071) g32p_integrationSquare071Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare071Matrix g32p_literalMatrix_006 := by
  decide +kernel

theorem g32p_integrationSquare071_actual : IsConj (g32p_literalRepresentative 71 * g32p_literalRepresentative 71)
    (g32p_literalRepresentative (g32p_familiesSquare 71)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare071Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_071 g32p_literalMatrix_071) g32p_literalMatrix_006 g32p_integrationSquare071Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_071) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_071) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 6) = _
    exact g32p_literalRepresentative_matrix 6
  · exact g32p_integrationSquare071_integral
  · exact g32p_integrationSquare071_equation

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_integrationSquare072Word : List (Fin 4) := [2, 2, 3, 0, 1, 2, 3]

def g32p_integrationSquare072Matrix : HurwitzPrymRex_Mat := ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

def g32p_integrationSquare072Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]],
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare072_certificate : g32p_archiveWordCertificate g32p_integrationSquare072Word g32p_integrationSquare072Stages = true := by
  decide +kernel

theorem g32p_integrationSquare072_integral : g32p_archiveIntegralWord g32p_integrationSquare072Word = g32p_integrationSquare072Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare072_certificate
  have hx : x = g32p_integrationSquare072Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare072_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_072 g32p_literalMatrix_072) g32p_integrationSquare072Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare072Matrix g32p_literalMatrix_019 := by
  decide +kernel

theorem g32p_integrationSquare072_actual : IsConj (g32p_literalRepresentative 72 * g32p_literalRepresentative 72)
    (g32p_literalRepresentative (g32p_familiesSquare 72)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare072Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_072 g32p_literalMatrix_072) g32p_literalMatrix_019 g32p_integrationSquare072Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_072) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_072) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 19) = _
    exact g32p_literalRepresentative_matrix 19
  · exact g32p_integrationSquare072_integral
  · exact g32p_integrationSquare072_equation

def g32p_integrationSquare073Word : List (Fin 4) := [3, 3, 2, 0, 0, 3, 2, 0, 0, 1, 0]

def g32p_integrationSquare073Matrix : HurwitzPrymRex_Mat := ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare073Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare073_certificate : g32p_archiveWordCertificate g32p_integrationSquare073Word g32p_integrationSquare073Stages = true := by
  decide +kernel

theorem g32p_integrationSquare073_integral : g32p_archiveIntegralWord g32p_integrationSquare073Word = g32p_integrationSquare073Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare073_certificate
  have hx : x = g32p_integrationSquare073Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare073_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_073 g32p_literalMatrix_073) g32p_integrationSquare073Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare073Matrix g32p_literalMatrix_073 := by
  decide +kernel

theorem g32p_integrationSquare073_actual : IsConj (g32p_literalRepresentative 73 * g32p_literalRepresentative 73)
    (g32p_literalRepresentative (g32p_familiesSquare 73)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare073Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_073 g32p_literalMatrix_073) g32p_literalMatrix_073 g32p_integrationSquare073Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_073) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_073) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 73) = _
    exact g32p_literalRepresentative_matrix 73
  · exact g32p_integrationSquare073_integral
  · exact g32p_integrationSquare073_equation

def g32p_integrationSquare074Word : List (Fin 4) := [0, 3, 1, 1]

def g32p_integrationSquare074Matrix : HurwitzPrymRex_Mat := ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

def g32p_integrationSquare074Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare074_certificate : g32p_archiveWordCertificate g32p_integrationSquare074Word g32p_integrationSquare074Stages = true := by
  decide +kernel

theorem g32p_integrationSquare074_integral : g32p_archiveIntegralWord g32p_integrationSquare074Word = g32p_integrationSquare074Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare074_certificate
  have hx : x = g32p_integrationSquare074Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare074_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_literalMatrix_074) g32p_integrationSquare074Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare074Matrix g32p_literalMatrix_078 := by
  decide +kernel

theorem g32p_integrationSquare074_actual : IsConj (g32p_literalRepresentative 74 * g32p_literalRepresentative 74)
    (g32p_literalRepresentative (g32p_familiesSquare 74)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare074Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_literalMatrix_074) g32p_literalMatrix_078 g32p_integrationSquare074Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_074) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_074) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 78) = _
    exact g32p_literalRepresentative_matrix 78
  · exact g32p_integrationSquare074_integral
  · exact g32p_integrationSquare074_equation

def g32p_integrationSquare075Word : List (Fin 4) := [3, 0, 0, 1, 2, 3, 1, 1]

def g32p_integrationSquare075Matrix : HurwitzPrymRex_Mat := ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

def g32p_integrationSquare075Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare075_certificate : g32p_archiveWordCertificate g32p_integrationSquare075Word g32p_integrationSquare075Stages = true := by
  decide +kernel

theorem g32p_integrationSquare075_integral : g32p_archiveIntegralWord g32p_integrationSquare075Word = g32p_integrationSquare075Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare075_certificate
  have hx : x = g32p_integrationSquare075Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare075_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_075 g32p_literalMatrix_075) g32p_integrationSquare075Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare075Matrix g32p_literalMatrix_006 := by
  decide +kernel

theorem g32p_integrationSquare075_actual : IsConj (g32p_literalRepresentative 75 * g32p_literalRepresentative 75)
    (g32p_literalRepresentative (g32p_familiesSquare 75)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare075Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_075 g32p_literalMatrix_075) g32p_literalMatrix_006 g32p_integrationSquare075Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_075) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_075) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 6) = _
    exact g32p_literalRepresentative_matrix 6
  · exact g32p_integrationSquare075_integral
  · exact g32p_integrationSquare075_equation

def g32p_integrationSquare076Word : List (Fin 4) := []

def g32p_integrationSquare076Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare076Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare076_certificate : g32p_archiveWordCertificate g32p_integrationSquare076Word g32p_integrationSquare076Stages = true := by
  decide +kernel

theorem g32p_integrationSquare076_integral : g32p_archiveIntegralWord g32p_integrationSquare076Word = g32p_integrationSquare076Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare076_certificate
  have hx : x = g32p_integrationSquare076Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare076_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_076 g32p_literalMatrix_076) g32p_integrationSquare076Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare076Matrix g32p_literalMatrix_067 := by
  decide +kernel

theorem g32p_integrationSquare076_actual : IsConj (g32p_literalRepresentative 76 * g32p_literalRepresentative 76)
    (g32p_literalRepresentative (g32p_familiesSquare 76)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare076Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_076 g32p_literalMatrix_076) g32p_literalMatrix_067 g32p_integrationSquare076Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_076) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_076) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 67) = _
    exact g32p_literalRepresentative_matrix 67
  · exact g32p_integrationSquare076_integral
  · exact g32p_integrationSquare076_equation

def g32p_integrationSquare077Word : List (Fin 4) := [1, 2, 3, 3]

def g32p_integrationSquare077Matrix : HurwitzPrymRex_Mat := ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

def g32p_integrationSquare077Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare077_certificate : g32p_archiveWordCertificate g32p_integrationSquare077Word g32p_integrationSquare077Stages = true := by
  decide +kernel

theorem g32p_integrationSquare077_integral : g32p_archiveIntegralWord g32p_integrationSquare077Word = g32p_integrationSquare077Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare077_certificate
  have hx : x = g32p_integrationSquare077Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare077_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_077 g32p_literalMatrix_077) g32p_integrationSquare077Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare077Matrix g32p_literalMatrix_067 := by
  decide +kernel

theorem g32p_integrationSquare077_actual : IsConj (g32p_literalRepresentative 77 * g32p_literalRepresentative 77)
    (g32p_literalRepresentative (g32p_familiesSquare 77)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare077Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_077 g32p_literalMatrix_077) g32p_literalMatrix_067 g32p_integrationSquare077Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_077) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_077) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 67) = _
    exact g32p_literalRepresentative_matrix 67
  · exact g32p_integrationSquare077_integral
  · exact g32p_integrationSquare077_equation

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_integrationSquare078Word : List (Fin 4) := [3, 2, 0, 1]

def g32p_integrationSquare078Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

def g32p_integrationSquare078Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]],
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare078_certificate : g32p_archiveWordCertificate g32p_integrationSquare078Word g32p_integrationSquare078Stages = true := by
  decide +kernel

theorem g32p_integrationSquare078_integral : g32p_archiveIntegralWord g32p_integrationSquare078Word = g32p_integrationSquare078Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare078_certificate
  have hx : x = g32p_integrationSquare078Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare078_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_078 g32p_literalMatrix_078) g32p_integrationSquare078Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare078Matrix g32p_literalMatrix_078 := by
  decide +kernel

theorem g32p_integrationSquare078_actual : IsConj (g32p_literalRepresentative 78 * g32p_literalRepresentative 78)
    (g32p_literalRepresentative (g32p_familiesSquare 78)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare078Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_078 g32p_literalMatrix_078) g32p_literalMatrix_078 g32p_integrationSquare078Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_078) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_078) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 78) = _
    exact g32p_literalRepresentative_matrix 78
  · exact g32p_integrationSquare078_integral
  · exact g32p_integrationSquare078_equation

def g32p_integrationSquare079Word : List (Fin 4) := [2, 2, 3]

def g32p_integrationSquare079Matrix : HurwitzPrymRex_Mat := ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

def g32p_integrationSquare079Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]],
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare079_certificate : g32p_archiveWordCertificate g32p_integrationSquare079Word g32p_integrationSquare079Stages = true := by
  decide +kernel

theorem g32p_integrationSquare079_integral : g32p_archiveIntegralWord g32p_integrationSquare079Word = g32p_integrationSquare079Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare079_certificate
  have hx : x = g32p_integrationSquare079Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare079_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_079 g32p_literalMatrix_079) g32p_integrationSquare079Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare079Matrix g32p_literalMatrix_076 := by
  decide +kernel

theorem g32p_integrationSquare079_actual : IsConj (g32p_literalRepresentative 79 * g32p_literalRepresentative 79)
    (g32p_literalRepresentative (g32p_familiesSquare 79)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare079Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_079 g32p_literalMatrix_079) g32p_literalMatrix_076 g32p_integrationSquare079Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_079) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_079) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 76) = _
    exact g32p_literalRepresentative_matrix 76
  · exact g32p_integrationSquare079_integral
  · exact g32p_integrationSquare079_equation

def g32p_integrationSquare080Word : List (Fin 4) := [2, 0, 1, 1, 0, 3, 3, 0]

def g32p_integrationSquare080Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

def g32p_integrationSquare080Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]],
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]],
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]],
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]],
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare080_certificate : g32p_archiveWordCertificate g32p_integrationSquare080Word g32p_integrationSquare080Stages = true := by
  decide +kernel

theorem g32p_integrationSquare080_integral : g32p_archiveIntegralWord g32p_integrationSquare080Word = g32p_integrationSquare080Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare080_certificate
  have hx : x = g32p_integrationSquare080Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare080_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_080 g32p_literalMatrix_080) g32p_integrationSquare080Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare080Matrix g32p_literalMatrix_089 := by
  decide +kernel

theorem g32p_integrationSquare080_actual : IsConj (g32p_literalRepresentative 80 * g32p_literalRepresentative 80)
    (g32p_literalRepresentative (g32p_familiesSquare 80)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare080Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_080 g32p_literalMatrix_080) g32p_literalMatrix_089 g32p_integrationSquare080Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_080) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_080) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 89) = _
    exact g32p_literalRepresentative_matrix 89
  · exact g32p_integrationSquare080_integral
  · exact g32p_integrationSquare080_equation

def g32p_integrationSquare081Word : List (Fin 4) := [2, 1]

def g32p_integrationSquare081Matrix : HurwitzPrymRex_Mat := ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

def g32p_integrationSquare081Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare081_certificate : g32p_archiveWordCertificate g32p_integrationSquare081Word g32p_integrationSquare081Stages = true := by
  decide +kernel

theorem g32p_integrationSquare081_integral : g32p_archiveIntegralWord g32p_integrationSquare081Word = g32p_integrationSquare081Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare081_certificate
  have hx : x = g32p_integrationSquare081Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare081_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_081 g32p_literalMatrix_081) g32p_integrationSquare081Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare081Matrix g32p_literalMatrix_002 := by
  decide +kernel

theorem g32p_integrationSquare081_actual : IsConj (g32p_literalRepresentative 81 * g32p_literalRepresentative 81)
    (g32p_literalRepresentative (g32p_familiesSquare 81)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare081Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_081 g32p_literalMatrix_081) g32p_literalMatrix_002 g32p_integrationSquare081Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_081) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_081) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 2) = _
    exact g32p_literalRepresentative_matrix 2
  · exact g32p_integrationSquare081_integral
  · exact g32p_integrationSquare081_equation

def g32p_integrationSquare082Word : List (Fin 4) := []

def g32p_integrationSquare082Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare082Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare082_certificate : g32p_archiveWordCertificate g32p_integrationSquare082Word g32p_integrationSquare082Stages = true := by
  decide +kernel

theorem g32p_integrationSquare082_integral : g32p_archiveIntegralWord g32p_integrationSquare082Word = g32p_integrationSquare082Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare082_certificate
  have hx : x = g32p_integrationSquare082Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare082_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_082 g32p_literalMatrix_082) g32p_integrationSquare082Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare082Matrix g32p_literalMatrix_101 := by
  decide +kernel

theorem g32p_integrationSquare082_actual : IsConj (g32p_literalRepresentative 82 * g32p_literalRepresentative 82)
    (g32p_literalRepresentative (g32p_familiesSquare 82)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare082Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_082 g32p_literalMatrix_082) g32p_literalMatrix_101 g32p_integrationSquare082Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_082) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_082) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 101) = _
    exact g32p_literalRepresentative_matrix 101
  · exact g32p_integrationSquare082_integral
  · exact g32p_integrationSquare082_equation

def g32p_integrationSquare083Word : List (Fin 4) := [2, 0, 3]

def g32p_integrationSquare083Matrix : HurwitzPrymRex_Mat := ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

def g32p_integrationSquare083Stages : List HurwitzPrymRex_Mat :=
  [![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare083_certificate : g32p_archiveWordCertificate g32p_integrationSquare083Word g32p_integrationSquare083Stages = true := by
  decide +kernel

theorem g32p_integrationSquare083_integral : g32p_archiveIntegralWord g32p_integrationSquare083Word = g32p_integrationSquare083Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare083_certificate
  have hx : x = g32p_integrationSquare083Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare083_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_083 g32p_literalMatrix_083) g32p_integrationSquare083Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare083Matrix g32p_literalMatrix_065 := by
  decide +kernel

theorem g32p_integrationSquare083_actual : IsConj (g32p_literalRepresentative 83 * g32p_literalRepresentative 83)
    (g32p_literalRepresentative (g32p_familiesSquare 83)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare083Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_083 g32p_literalMatrix_083) g32p_literalMatrix_065 g32p_integrationSquare083Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_083) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_083) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 65) = _
    exact g32p_literalRepresentative_matrix 65
  · exact g32p_integrationSquare083_integral
  · exact g32p_integrationSquare083_equation

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_integrationSquare084Word : List (Fin 4) := [2, 2, 3, 0, 1, 2, 1, 0]

def g32p_integrationSquare084Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

def g32p_integrationSquare084Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]],
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare084_certificate : g32p_archiveWordCertificate g32p_integrationSquare084Word g32p_integrationSquare084Stages = true := by
  decide +kernel

theorem g32p_integrationSquare084_integral : g32p_archiveIntegralWord g32p_integrationSquare084Word = g32p_integrationSquare084Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare084_certificate
  have hx : x = g32p_integrationSquare084Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare084_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_084 g32p_literalMatrix_084) g32p_integrationSquare084Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare084Matrix g32p_literalMatrix_035 := by
  decide +kernel

theorem g32p_integrationSquare084_actual : IsConj (g32p_literalRepresentative 84 * g32p_literalRepresentative 84)
    (g32p_literalRepresentative (g32p_familiesSquare 84)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare084Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_084 g32p_literalMatrix_084) g32p_literalMatrix_035 g32p_integrationSquare084Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_084) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_084) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 35) = _
    exact g32p_literalRepresentative_matrix 35
  · exact g32p_integrationSquare084_integral
  · exact g32p_integrationSquare084_equation

def g32p_integrationSquare085Word : List (Fin 4) := [2, 0, 1, 1]

def g32p_integrationSquare085Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

def g32p_integrationSquare085Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare085_certificate : g32p_archiveWordCertificate g32p_integrationSquare085Word g32p_integrationSquare085Stages = true := by
  decide +kernel

theorem g32p_integrationSquare085_integral : g32p_archiveIntegralWord g32p_integrationSquare085Word = g32p_integrationSquare085Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare085_certificate
  have hx : x = g32p_integrationSquare085Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare085_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_085 g32p_literalMatrix_085) g32p_integrationSquare085Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare085Matrix g32p_literalMatrix_087 := by
  decide +kernel

theorem g32p_integrationSquare085_actual : IsConj (g32p_literalRepresentative 85 * g32p_literalRepresentative 85)
    (g32p_literalRepresentative (g32p_familiesSquare 85)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare085Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_085 g32p_literalMatrix_085) g32p_literalMatrix_087 g32p_integrationSquare085Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_085) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_085) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 87) = _
    exact g32p_literalRepresentative_matrix 87
  · exact g32p_integrationSquare085_integral
  · exact g32p_integrationSquare085_equation

def g32p_integrationSquare086Word : List (Fin 4) := [3, 2, 2, 1, 0]

def g32p_integrationSquare086Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

def g32p_integrationSquare086Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare086_certificate : g32p_archiveWordCertificate g32p_integrationSquare086Word g32p_integrationSquare086Stages = true := by
  decide +kernel

theorem g32p_integrationSquare086_integral : g32p_archiveIntegralWord g32p_integrationSquare086Word = g32p_integrationSquare086Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare086_certificate
  have hx : x = g32p_integrationSquare086Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare086_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_086 g32p_literalMatrix_086) g32p_integrationSquare086Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare086Matrix g32p_literalMatrix_035 := by
  decide +kernel

theorem g32p_integrationSquare086_actual : IsConj (g32p_literalRepresentative 86 * g32p_literalRepresentative 86)
    (g32p_literalRepresentative (g32p_familiesSquare 86)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare086Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_086 g32p_literalMatrix_086) g32p_literalMatrix_035 g32p_integrationSquare086Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_086) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_086) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 35) = _
    exact g32p_literalRepresentative_matrix 35
  · exact g32p_integrationSquare086_integral
  · exact g32p_integrationSquare086_equation

def g32p_integrationSquare087Word : List (Fin 4) := [2, 2]

def g32p_integrationSquare087Matrix : HurwitzPrymRex_Mat := ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

def g32p_integrationSquare087Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare087_certificate : g32p_archiveWordCertificate g32p_integrationSquare087Word g32p_integrationSquare087Stages = true := by
  decide +kernel

theorem g32p_integrationSquare087_integral : g32p_archiveIntegralWord g32p_integrationSquare087Word = g32p_integrationSquare087Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare087_certificate
  have hx : x = g32p_integrationSquare087Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare087_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_087 g32p_literalMatrix_087) g32p_integrationSquare087Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare087Matrix g32p_literalMatrix_100 := by
  decide +kernel

theorem g32p_integrationSquare087_actual : IsConj (g32p_literalRepresentative 87 * g32p_literalRepresentative 87)
    (g32p_literalRepresentative (g32p_familiesSquare 87)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare087Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_087 g32p_literalMatrix_087) g32p_literalMatrix_100 g32p_integrationSquare087Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_087) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_087) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 100) = _
    exact g32p_literalRepresentative_matrix 100
  · exact g32p_integrationSquare087_integral
  · exact g32p_integrationSquare087_equation

def g32p_integrationSquare088Word : List (Fin 4) := [3, 0, 1]

def g32p_integrationSquare088Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

def g32p_integrationSquare088Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare088_certificate : g32p_archiveWordCertificate g32p_integrationSquare088Word g32p_integrationSquare088Stages = true := by
  decide +kernel

theorem g32p_integrationSquare088_integral : g32p_archiveIntegralWord g32p_integrationSquare088Word = g32p_integrationSquare088Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare088_certificate
  have hx : x = g32p_integrationSquare088Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare088_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_088 g32p_literalMatrix_088) g32p_integrationSquare088Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare088Matrix g32p_literalMatrix_100 := by
  decide +kernel

theorem g32p_integrationSquare088_actual : IsConj (g32p_literalRepresentative 88 * g32p_literalRepresentative 88)
    (g32p_literalRepresentative (g32p_familiesSquare 88)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare088Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_088 g32p_literalMatrix_088) g32p_literalMatrix_100 g32p_integrationSquare088Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_088) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_088) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 100) = _
    exact g32p_literalRepresentative_matrix 100
  · exact g32p_integrationSquare088_integral
  · exact g32p_integrationSquare088_equation

def g32p_integrationSquare089Word : List (Fin 4) := [3, 2, 2, 1, 1]

def g32p_integrationSquare089Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

def g32p_integrationSquare089Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare089_certificate : g32p_archiveWordCertificate g32p_integrationSquare089Word g32p_integrationSquare089Stages = true := by
  decide +kernel

theorem g32p_integrationSquare089_integral : g32p_archiveIntegralWord g32p_integrationSquare089Word = g32p_integrationSquare089Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare089_certificate
  have hx : x = g32p_integrationSquare089Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare089_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_089 g32p_literalMatrix_089) g32p_integrationSquare089Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare089Matrix g32p_literalMatrix_001 := by
  decide +kernel

theorem g32p_integrationSquare089_actual : IsConj (g32p_literalRepresentative 89 * g32p_literalRepresentative 89)
    (g32p_literalRepresentative (g32p_familiesSquare 89)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare089Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_089 g32p_literalMatrix_089) g32p_literalMatrix_001 g32p_integrationSquare089Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_089) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_089) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 1) = _
    exact g32p_literalRepresentative_matrix 1
  · exact g32p_integrationSquare089_integral
  · exact g32p_integrationSquare089_equation

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_integrationSquare090Word : List (Fin 4) := [2, 0]

def g32p_integrationSquare090Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

def g32p_integrationSquare090Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare090_certificate : g32p_archiveWordCertificate g32p_integrationSquare090Word g32p_integrationSquare090Stages = true := by
  decide +kernel

theorem g32p_integrationSquare090_integral : g32p_archiveIntegralWord g32p_integrationSquare090Word = g32p_integrationSquare090Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare090_certificate
  have hx : x = g32p_integrationSquare090Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare090_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_090 g32p_literalMatrix_090) g32p_integrationSquare090Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare090Matrix g32p_literalMatrix_082 := by
  decide +kernel

theorem g32p_integrationSquare090_actual : IsConj (g32p_literalRepresentative 90 * g32p_literalRepresentative 90)
    (g32p_literalRepresentative (g32p_familiesSquare 90)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare090Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_090 g32p_literalMatrix_090) g32p_literalMatrix_082 g32p_integrationSquare090Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_090) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_090) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 82) = _
    exact g32p_literalRepresentative_matrix 82
  · exact g32p_integrationSquare090_integral
  · exact g32p_integrationSquare090_equation

def g32p_integrationSquare091Word : List (Fin 4) := [0, 0, 3]

def g32p_integrationSquare091Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

def g32p_integrationSquare091Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare091_certificate : g32p_archiveWordCertificate g32p_integrationSquare091Word g32p_integrationSquare091Stages = true := by
  decide +kernel

theorem g32p_integrationSquare091_integral : g32p_archiveIntegralWord g32p_integrationSquare091Word = g32p_integrationSquare091Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare091_certificate
  have hx : x = g32p_integrationSquare091Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare091_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_091 g32p_literalMatrix_091) g32p_integrationSquare091Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare091Matrix g32p_literalMatrix_100 := by
  decide +kernel

theorem g32p_integrationSquare091_actual : IsConj (g32p_literalRepresentative 91 * g32p_literalRepresentative 91)
    (g32p_literalRepresentative (g32p_familiesSquare 91)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare091Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_091 g32p_literalMatrix_091) g32p_literalMatrix_100 g32p_integrationSquare091Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_091) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_091) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 100) = _
    exact g32p_literalRepresentative_matrix 100
  · exact g32p_integrationSquare091_integral
  · exact g32p_integrationSquare091_equation

def g32p_integrationSquare092Word : List (Fin 4) := [2, 2, 0, 3, 1, 1]

def g32p_integrationSquare092Matrix : HurwitzPrymRex_Mat := ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

def g32p_integrationSquare092Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]],
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare092_certificate : g32p_archiveWordCertificate g32p_integrationSquare092Word g32p_integrationSquare092Stages = true := by
  decide +kernel

theorem g32p_integrationSquare092_integral : g32p_archiveIntegralWord g32p_integrationSquare092Word = g32p_integrationSquare092Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare092_certificate
  have hx : x = g32p_integrationSquare092Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare092_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_092 g32p_literalMatrix_092) g32p_integrationSquare092Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare092Matrix g32p_literalMatrix_011 := by
  decide +kernel

theorem g32p_integrationSquare092_actual : IsConj (g32p_literalRepresentative 92 * g32p_literalRepresentative 92)
    (g32p_literalRepresentative (g32p_familiesSquare 92)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare092Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_092 g32p_literalMatrix_092) g32p_literalMatrix_011 g32p_integrationSquare092Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_092) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_092) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 11) = _
    exact g32p_literalRepresentative_matrix 11
  · exact g32p_integrationSquare092_integral
  · exact g32p_integrationSquare092_equation

def g32p_integrationSquare093Word : List (Fin 4) := [3, 2, 1]

def g32p_integrationSquare093Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

def g32p_integrationSquare093Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare093_certificate : g32p_archiveWordCertificate g32p_integrationSquare093Word g32p_integrationSquare093Stages = true := by
  decide +kernel

theorem g32p_integrationSquare093_integral : g32p_archiveIntegralWord g32p_integrationSquare093Word = g32p_integrationSquare093Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare093_certificate
  have hx : x = g32p_integrationSquare093Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare093_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_093 g32p_literalMatrix_093) g32p_integrationSquare093Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare093Matrix g32p_literalMatrix_001 := by
  decide +kernel

theorem g32p_integrationSquare093_actual : IsConj (g32p_literalRepresentative 93 * g32p_literalRepresentative 93)
    (g32p_literalRepresentative (g32p_familiesSquare 93)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare093Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_093 g32p_literalMatrix_093) g32p_literalMatrix_001 g32p_integrationSquare093Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_093) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_093) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 1) = _
    exact g32p_literalRepresentative_matrix 1
  · exact g32p_integrationSquare093_integral
  · exact g32p_integrationSquare093_equation

def g32p_integrationSquare094Word : List (Fin 4) := [2, 3, 3]

def g32p_integrationSquare094Matrix : HurwitzPrymRex_Mat := ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

def g32p_integrationSquare094Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare094_certificate : g32p_archiveWordCertificate g32p_integrationSquare094Word g32p_integrationSquare094Stages = true := by
  decide +kernel

theorem g32p_integrationSquare094_integral : g32p_archiveIntegralWord g32p_integrationSquare094Word = g32p_integrationSquare094Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare094_certificate
  have hx : x = g32p_integrationSquare094Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare094_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_094 g32p_literalMatrix_094) g32p_integrationSquare094Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare094Matrix g32p_literalMatrix_018 := by
  decide +kernel

theorem g32p_integrationSquare094_actual : IsConj (g32p_literalRepresentative 94 * g32p_literalRepresentative 94)
    (g32p_literalRepresentative (g32p_familiesSquare 94)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare094Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_094 g32p_literalMatrix_094) g32p_literalMatrix_018 g32p_integrationSquare094Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_094) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_094) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 18) = _
    exact g32p_literalRepresentative_matrix 18
  · exact g32p_integrationSquare094_integral
  · exact g32p_integrationSquare094_equation

def g32p_integrationSquare095Word : List (Fin 4) := [2, 3, 3]

def g32p_integrationSquare095Matrix : HurwitzPrymRex_Mat := ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

def g32p_integrationSquare095Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare095_certificate : g32p_archiveWordCertificate g32p_integrationSquare095Word g32p_integrationSquare095Stages = true := by
  decide +kernel

theorem g32p_integrationSquare095_integral : g32p_archiveIntegralWord g32p_integrationSquare095Word = g32p_integrationSquare095Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare095_certificate
  have hx : x = g32p_integrationSquare095Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare095_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_095 g32p_literalMatrix_095) g32p_integrationSquare095Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare095Matrix g32p_literalMatrix_076 := by
  decide +kernel

theorem g32p_integrationSquare095_actual : IsConj (g32p_literalRepresentative 95 * g32p_literalRepresentative 95)
    (g32p_literalRepresentative (g32p_familiesSquare 95)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare095Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_095 g32p_literalMatrix_095) g32p_literalMatrix_076 g32p_integrationSquare095Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_095) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_095) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 76) = _
    exact g32p_literalRepresentative_matrix 76
  · exact g32p_integrationSquare095_integral
  · exact g32p_integrationSquare095_equation

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_integrationSquare096Word : List (Fin 4) := []

def g32p_integrationSquare096Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare096Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare096_certificate : g32p_archiveWordCertificate g32p_integrationSquare096Word g32p_integrationSquare096Stages = true := by
  decide +kernel

theorem g32p_integrationSquare096_integral : g32p_archiveIntegralWord g32p_integrationSquare096Word = g32p_integrationSquare096Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare096_certificate
  have hx : x = g32p_integrationSquare096Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare096_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_096 g32p_literalMatrix_096) g32p_integrationSquare096Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare096Matrix g32p_literalMatrix_101 := by
  decide +kernel

theorem g32p_integrationSquare096_actual : IsConj (g32p_literalRepresentative 96 * g32p_literalRepresentative 96)
    (g32p_literalRepresentative (g32p_familiesSquare 96)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare096Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_096 g32p_literalMatrix_096) g32p_literalMatrix_101 g32p_integrationSquare096Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_096) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_096) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 101) = _
    exact g32p_literalRepresentative_matrix 101
  · exact g32p_integrationSquare096_integral
  · exact g32p_integrationSquare096_equation

def g32p_integrationSquare097Word : List (Fin 4) := []

def g32p_integrationSquare097Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare097Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare097_certificate : g32p_archiveWordCertificate g32p_integrationSquare097Word g32p_integrationSquare097Stages = true := by
  decide +kernel

theorem g32p_integrationSquare097_integral : g32p_archiveIntegralWord g32p_integrationSquare097Word = g32p_integrationSquare097Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare097_certificate
  have hx : x = g32p_integrationSquare097Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare097_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_097 g32p_literalMatrix_097) g32p_integrationSquare097Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare097Matrix g32p_literalMatrix_101 := by
  decide +kernel

theorem g32p_integrationSquare097_actual : IsConj (g32p_literalRepresentative 97 * g32p_literalRepresentative 97)
    (g32p_literalRepresentative (g32p_familiesSquare 97)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare097Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_097 g32p_literalMatrix_097) g32p_literalMatrix_101 g32p_integrationSquare097Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_097) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_097) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 101) = _
    exact g32p_literalRepresentative_matrix 101
  · exact g32p_integrationSquare097_integral
  · exact g32p_integrationSquare097_equation

def g32p_integrationSquare098Word : List (Fin 4) := [3, 3]

def g32p_integrationSquare098Matrix : HurwitzPrymRex_Mat := ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

def g32p_integrationSquare098Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare098_certificate : g32p_archiveWordCertificate g32p_integrationSquare098Word g32p_integrationSquare098Stages = true := by
  decide +kernel

theorem g32p_integrationSquare098_integral : g32p_archiveIntegralWord g32p_integrationSquare098Word = g32p_integrationSquare098Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare098_certificate
  have hx : x = g32p_integrationSquare098Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare098_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_098 g32p_literalMatrix_098) g32p_integrationSquare098Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare098Matrix g32p_literalMatrix_002 := by
  decide +kernel

theorem g32p_integrationSquare098_actual : IsConj (g32p_literalRepresentative 98 * g32p_literalRepresentative 98)
    (g32p_literalRepresentative (g32p_familiesSquare 98)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare098Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_098 g32p_literalMatrix_098) g32p_literalMatrix_002 g32p_integrationSquare098Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_098) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_098) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 2) = _
    exact g32p_literalRepresentative_matrix 2
  · exact g32p_integrationSquare098_integral
  · exact g32p_integrationSquare098_equation

def g32p_integrationSquare099Word : List (Fin 4) := []

def g32p_integrationSquare099Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare099Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare099_certificate : g32p_archiveWordCertificate g32p_integrationSquare099Word g32p_integrationSquare099Stages = true := by
  decide +kernel

theorem g32p_integrationSquare099_integral : g32p_archiveIntegralWord g32p_integrationSquare099Word = g32p_integrationSquare099Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare099_certificate
  have hx : x = g32p_integrationSquare099Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare099_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_099 g32p_literalMatrix_099) g32p_integrationSquare099Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare099Matrix g32p_literalMatrix_000 := by
  decide +kernel

theorem g32p_integrationSquare099_actual : IsConj (g32p_literalRepresentative 99 * g32p_literalRepresentative 99)
    (g32p_literalRepresentative (g32p_familiesSquare 99)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare099Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_099 g32p_literalMatrix_099) g32p_literalMatrix_000 g32p_integrationSquare099Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_099) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_099) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 0) = _
    exact g32p_literalRepresentative_matrix 0
  · exact g32p_integrationSquare099_integral
  · exact g32p_integrationSquare099_equation

def g32p_integrationSquare100Word : List (Fin 4) := [2]

def g32p_integrationSquare100Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

def g32p_integrationSquare100Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare100_certificate : g32p_archiveWordCertificate g32p_integrationSquare100Word g32p_integrationSquare100Stages = true := by
  decide +kernel

theorem g32p_integrationSquare100_integral : g32p_archiveIntegralWord g32p_integrationSquare100Word = g32p_integrationSquare100Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare100_certificate
  have hx : x = g32p_integrationSquare100Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare100_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_100 g32p_literalMatrix_100) g32p_integrationSquare100Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare100Matrix g32p_literalMatrix_087 := by
  decide +kernel

theorem g32p_integrationSquare100_actual : IsConj (g32p_literalRepresentative 100 * g32p_literalRepresentative 100)
    (g32p_literalRepresentative (g32p_familiesSquare 100)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare100Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_100 g32p_literalMatrix_100) g32p_literalMatrix_087 g32p_integrationSquare100Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_100) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_100) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 87) = _
    exact g32p_literalRepresentative_matrix 87
  · exact g32p_integrationSquare100_integral
  · exact g32p_integrationSquare100_equation

def g32p_integrationSquare101Word : List (Fin 4) := []

def g32p_integrationSquare101Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare101Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare101_certificate : g32p_archiveWordCertificate g32p_integrationSquare101Word g32p_integrationSquare101Stages = true := by
  decide +kernel

theorem g32p_integrationSquare101_integral : g32p_archiveIntegralWord g32p_integrationSquare101Word = g32p_integrationSquare101Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare101_certificate
  have hx : x = g32p_integrationSquare101Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare101_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_101 g32p_literalMatrix_101) g32p_integrationSquare101Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare101Matrix g32p_literalMatrix_096 := by
  decide +kernel

theorem g32p_integrationSquare101_actual : IsConj (g32p_literalRepresentative 101 * g32p_literalRepresentative 101)
    (g32p_literalRepresentative (g32p_familiesSquare 101)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare101Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_101 g32p_literalMatrix_101) g32p_literalMatrix_096 g32p_integrationSquare101Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_101) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_101) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 96) = _
    exact g32p_literalRepresentative_matrix 96
  · exact g32p_integrationSquare101_integral
  · exact g32p_integrationSquare101_equation

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_integration_square_representative (c : Fin 102) :
    IsConj (g32p_literalRepresentative c * g32p_literalRepresentative c)
      (g32p_literalRepresentative (g32p_familiesSquare c)) := by
  fin_cases c
  · exact g32p_integrationSquare000_actual
  · exact g32p_integrationSquare001_actual
  · exact g32p_integrationSquare002_actual
  · exact g32p_integrationSquare003_actual
  · exact g32p_integrationSquare004_actual
  · exact g32p_integrationSquare005_actual
  · exact g32p_integrationSquare006_actual
  · exact g32p_integrationSquare007_actual
  · exact g32p_integrationSquare008_actual
  · exact g32p_integrationSquare009_actual
  · exact g32p_integrationSquare010_actual
  · exact g32p_integrationSquare011_actual
  · exact g32p_integrationSquare012_actual
  · exact g32p_integrationSquare013_actual
  · exact g32p_integrationSquare014_actual
  · exact g32p_integrationSquare015_actual
  · exact g32p_integrationSquare016_actual
  · exact g32p_integrationSquare017_actual
  · exact g32p_integrationSquare018_actual
  · exact g32p_integrationSquare019_actual
  · exact g32p_integrationSquare020_actual
  · exact g32p_integrationSquare021_actual
  · exact g32p_integrationSquare022_actual
  · exact g32p_integrationSquare023_actual
  · exact g32p_integrationSquare024_actual
  · exact g32p_integrationSquare025_actual
  · exact g32p_integrationSquare026_actual
  · exact g32p_integrationSquare027_actual
  · exact g32p_integrationSquare028_actual
  · exact g32p_integrationSquare029_actual
  · exact g32p_integrationSquare030_actual
  · exact g32p_integrationSquare031_actual
  · exact g32p_integrationSquare032_actual
  · exact g32p_integrationSquare033_actual
  · exact g32p_integrationSquare034_actual
  · exact g32p_integrationSquare035_actual
  · exact g32p_integrationSquare036_actual
  · exact g32p_integrationSquare037_actual
  · exact g32p_integrationSquare038_actual
  · exact g32p_integrationSquare039_actual
  · exact g32p_integrationSquare040_actual
  · exact g32p_integrationSquare041_actual
  · exact g32p_integrationSquare042_actual
  · exact g32p_integrationSquare043_actual
  · exact g32p_integrationSquare044_actual
  · exact g32p_integrationSquare045_actual
  · exact g32p_integrationSquare046_actual
  · exact g32p_integrationSquare047_actual
  · exact g32p_integrationSquare048_actual
  · exact g32p_integrationSquare049_actual
  · exact g32p_integrationSquare050_actual
  · exact g32p_integrationSquare051_actual
  · exact g32p_integrationSquare052_actual
  · exact g32p_integrationSquare053_actual
  · exact g32p_integrationSquare054_actual
  · exact g32p_integrationSquare055_actual
  · exact g32p_integrationSquare056_actual
  · exact g32p_integrationSquare057_actual
  · exact g32p_integrationSquare058_actual
  · exact g32p_integrationSquare059_actual
  · exact g32p_integrationSquare060_actual
  · exact g32p_integrationSquare061_actual
  · exact g32p_integrationSquare062_actual
  · exact g32p_integrationSquare063_actual
  · exact g32p_integrationSquare064_actual
  · exact g32p_integrationSquare065_actual
  · exact g32p_integrationSquare066_actual
  · exact g32p_integrationSquare067_actual
  · exact g32p_integrationSquare068_actual
  · exact g32p_integrationSquare069_actual
  · exact g32p_integrationSquare070_actual
  · exact g32p_integrationSquare071_actual
  · exact g32p_integrationSquare072_actual
  · exact g32p_integrationSquare073_actual
  · exact g32p_integrationSquare074_actual
  · exact g32p_integrationSquare075_actual
  · exact g32p_integrationSquare076_actual
  · exact g32p_integrationSquare077_actual
  · exact g32p_integrationSquare078_actual
  · exact g32p_integrationSquare079_actual
  · exact g32p_integrationSquare080_actual
  · exact g32p_integrationSquare081_actual
  · exact g32p_integrationSquare082_actual
  · exact g32p_integrationSquare083_actual
  · exact g32p_integrationSquare084_actual
  · exact g32p_integrationSquare085_actual
  · exact g32p_integrationSquare086_actual
  · exact g32p_integrationSquare087_actual
  · exact g32p_integrationSquare088_actual
  · exact g32p_integrationSquare089_actual
  · exact g32p_integrationSquare090_actual
  · exact g32p_integrationSquare091_actual
  · exact g32p_integrationSquare092_actual
  · exact g32p_integrationSquare093_actual
  · exact g32p_integrationSquare094_actual
  · exact g32p_integrationSquare095_actual
  · exact g32p_integrationSquare096_actual
  · exact g32p_integrationSquare097_actual
  · exact g32p_integrationSquare098_actual
  · exact g32p_integrationSquare099_actual
  · exact g32p_integrationSquare100_actual
  · exact g32p_integrationSquare101_actual

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_literalInverseWord_000 : List (Fin 4) := []

def g32p_literalInverseMatrix_000 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_literalInverseStages_000 : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_literalInverseCertificate_000 :
    g32p_archiveWordCertificate g32p_literalInverseWord_000
      g32p_literalInverseStages_000 = true := by
  decide +kernel

theorem g32p_literalInverseIntegral_000 :
    g32p_archiveIntegralWord g32p_literalInverseWord_000 =
      g32p_literalInverseMatrix_000 := by
  obtain ⟨a, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_literalInverseCertificate_000
  have ha : a = g32p_literalInverseStages_000.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, ha]
  rfl

theorem g32p_literalInverseEquation_000 :
    HurwitzPrymRex_mmul g32p_literalMatrix_000
      (HurwitzPrymRex_mmul g32p_literalInverseMatrix_000 g32p_literalMatrix_000) =
        g32p_literalInverseMatrix_000 := by
  decide +kernel

theorem g32p_literalInverseConjugacy_000 :
    IsConj (g32p_literalRepresentative 0)⁻¹ (g32p_literalRepresentative 0) :=
  g32p_archiveWord_inverse_isConj _ _ _ _ _ _
    g32p_literalIntegral_000 g32p_literalIntegral_000
    g32p_literalInverseIntegral_000 g32p_literalInverseEquation_000

def g32p_literalInverseWord_001 : List (Fin 4) := []

def g32p_literalInverseMatrix_001 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_literalInverseStages_001 : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_literalInverseCertificate_001 :
    g32p_archiveWordCertificate g32p_literalInverseWord_001
      g32p_literalInverseStages_001 = true := by
  decide +kernel

theorem g32p_literalInverseIntegral_001 :
    g32p_archiveIntegralWord g32p_literalInverseWord_001 =
      g32p_literalInverseMatrix_001 := by
  obtain ⟨a, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_literalInverseCertificate_001
  have ha : a = g32p_literalInverseStages_001.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, ha]
  rfl

theorem g32p_literalInverseEquation_001 :
    HurwitzPrymRex_mmul g32p_literalMatrix_001
      (HurwitzPrymRex_mmul g32p_literalInverseMatrix_001 g32p_literalMatrix_002) =
        g32p_literalInverseMatrix_001 := by
  decide +kernel

theorem g32p_literalInverseConjugacy_001 :
    IsConj (g32p_literalRepresentative 1)⁻¹ (g32p_literalRepresentative 2) :=
  g32p_archiveWord_inverse_isConj _ _ _ _ _ _
    g32p_literalIntegral_001 g32p_literalIntegral_002
    g32p_literalInverseIntegral_001 g32p_literalInverseEquation_001

def g32p_literalInverseWord_002 : List (Fin 4) := []

def g32p_literalInverseMatrix_002 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_literalInverseStages_002 : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_literalInverseCertificate_002 :
    g32p_archiveWordCertificate g32p_literalInverseWord_002
      g32p_literalInverseStages_002 = true := by
  decide +kernel

theorem g32p_literalInverseIntegral_002 :
    g32p_archiveIntegralWord g32p_literalInverseWord_002 =
      g32p_literalInverseMatrix_002 := by
  obtain ⟨a, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_literalInverseCertificate_002
  have ha : a = g32p_literalInverseStages_002.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, ha]
  rfl

theorem g32p_literalInverseEquation_002 :
    HurwitzPrymRex_mmul g32p_literalMatrix_002
      (HurwitzPrymRex_mmul g32p_literalInverseMatrix_002 g32p_literalMatrix_001) =
        g32p_literalInverseMatrix_002 := by
  decide +kernel

theorem g32p_literalInverseConjugacy_002 :
    IsConj (g32p_literalRepresentative 2)⁻¹ (g32p_literalRepresentative 1) :=
  g32p_archiveWord_inverse_isConj _ _ _ _ _ _
    g32p_literalIntegral_002 g32p_literalIntegral_001
    g32p_literalInverseIntegral_002 g32p_literalInverseEquation_002

def g32p_literalInverseWord_003 : List (Fin 4) := [0]

def g32p_literalInverseMatrix_003 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

def g32p_literalInverseStages_003 : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_literalInverseCertificate_003 :
    g32p_archiveWordCertificate g32p_literalInverseWord_003
      g32p_literalInverseStages_003 = true := by
  decide +kernel

theorem g32p_literalInverseIntegral_003 :
    g32p_archiveIntegralWord g32p_literalInverseWord_003 =
      g32p_literalInverseMatrix_003 := by
  obtain ⟨a, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_literalInverseCertificate_003
  have ha : a = g32p_literalInverseStages_003.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, ha]
  rfl

theorem g32p_literalInverseEquation_003 :
    HurwitzPrymRex_mmul g32p_literalMatrix_003
      (HurwitzPrymRex_mmul g32p_literalInverseMatrix_003 g32p_literalMatrix_008) =
        g32p_literalInverseMatrix_003 := by
  decide +kernel

theorem g32p_literalInverseConjugacy_003 :
    IsConj (g32p_literalRepresentative 3)⁻¹ (g32p_literalRepresentative 8) :=
  g32p_archiveWord_inverse_isConj _ _ _ _ _ _
    g32p_literalIntegral_003 g32p_literalIntegral_008
    g32p_literalInverseIntegral_003 g32p_literalInverseEquation_003

def g32p_literalInverseWord_004 : List (Fin 4) := []

def g32p_literalInverseMatrix_004 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_literalInverseStages_004 : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_literalInverseCertificate_004 :
    g32p_archiveWordCertificate g32p_literalInverseWord_004
      g32p_literalInverseStages_004 = true := by
  decide +kernel

theorem g32p_literalInverseIntegral_004 :
    g32p_archiveIntegralWord g32p_literalInverseWord_004 =
      g32p_literalInverseMatrix_004 := by
  obtain ⟨a, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_literalInverseCertificate_004
  have ha : a = g32p_literalInverseStages_004.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, ha]
  rfl

theorem g32p_literalInverseEquation_004 :
    HurwitzPrymRex_mmul g32p_literalMatrix_004
      (HurwitzPrymRex_mmul g32p_literalInverseMatrix_004 g32p_literalMatrix_011) =
        g32p_literalInverseMatrix_004 := by
  decide +kernel

theorem g32p_literalInverseConjugacy_004 :
    IsConj (g32p_literalRepresentative 4)⁻¹ (g32p_literalRepresentative 11) :=
  g32p_archiveWord_inverse_isConj _ _ _ _ _ _
    g32p_literalIntegral_004 g32p_literalIntegral_011
    g32p_literalInverseIntegral_004 g32p_literalInverseEquation_004

def g32p_literalInverseWord_005 : List (Fin 4) := [1, 0, 0]

def g32p_literalInverseMatrix_005 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

def g32p_literalInverseStages_005 : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_literalInverseCertificate_005 :
    g32p_archiveWordCertificate g32p_literalInverseWord_005
      g32p_literalInverseStages_005 = true := by
  decide +kernel

theorem g32p_literalInverseIntegral_005 :
    g32p_archiveIntegralWord g32p_literalInverseWord_005 =
      g32p_literalInverseMatrix_005 := by
  obtain ⟨a, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_literalInverseCertificate_005
  have ha : a = g32p_literalInverseStages_005.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, ha]
  rfl

theorem g32p_literalInverseEquation_005 :
    HurwitzPrymRex_mmul g32p_literalMatrix_005
      (HurwitzPrymRex_mmul g32p_literalInverseMatrix_005 g32p_literalMatrix_005) =
        g32p_literalInverseMatrix_005 := by
  decide +kernel

theorem g32p_literalInverseConjugacy_005 :
    IsConj (g32p_literalRepresentative 5)⁻¹ (g32p_literalRepresentative 5) :=
  g32p_archiveWord_inverse_isConj _ _ _ _ _ _
    g32p_literalIntegral_005 g32p_literalIntegral_005
    g32p_literalInverseIntegral_005 g32p_literalInverseEquation_005


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_literalInverseWord_006 : List (Fin 4) := [1, 2, 0, 1]

def g32p_literalInverseMatrix_006 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

def g32p_literalInverseStages_006 : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]],
   ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_literalInverseCertificate_006 :
    g32p_archiveWordCertificate g32p_literalInverseWord_006
      g32p_literalInverseStages_006 = true := by
  decide +kernel

theorem g32p_literalInverseIntegral_006 :
    g32p_archiveIntegralWord g32p_literalInverseWord_006 =
      g32p_literalInverseMatrix_006 := by
  obtain ⟨a, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_literalInverseCertificate_006
  have ha : a = g32p_literalInverseStages_006.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, ha]
  rfl

theorem g32p_literalInverseEquation_006 :
    HurwitzPrymRex_mmul g32p_literalMatrix_006
      (HurwitzPrymRex_mmul g32p_literalInverseMatrix_006 g32p_literalMatrix_006) =
        g32p_literalInverseMatrix_006 := by
  decide +kernel

theorem g32p_literalInverseConjugacy_006 :
    IsConj (g32p_literalRepresentative 6)⁻¹ (g32p_literalRepresentative 6) :=
  g32p_archiveWord_inverse_isConj _ _ _ _ _ _
    g32p_literalIntegral_006 g32p_literalIntegral_006
    g32p_literalInverseIntegral_006 g32p_literalInverseEquation_006

def g32p_literalInverseWord_007 : List (Fin 4) := [0, 1, 0]

def g32p_literalInverseMatrix_007 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

def g32p_literalInverseStages_007 : List HurwitzPrymRex_Mat :=
  [![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_literalInverseCertificate_007 :
    g32p_archiveWordCertificate g32p_literalInverseWord_007
      g32p_literalInverseStages_007 = true := by
  decide +kernel

theorem g32p_literalInverseIntegral_007 :
    g32p_archiveIntegralWord g32p_literalInverseWord_007 =
      g32p_literalInverseMatrix_007 := by
  obtain ⟨a, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_literalInverseCertificate_007
  have ha : a = g32p_literalInverseStages_007.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, ha]
  rfl

theorem g32p_literalInverseEquation_007 :
    HurwitzPrymRex_mmul g32p_literalMatrix_007
      (HurwitzPrymRex_mmul g32p_literalInverseMatrix_007 g32p_literalMatrix_020) =
        g32p_literalInverseMatrix_007 := by
  decide +kernel

theorem g32p_literalInverseConjugacy_007 :
    IsConj (g32p_literalRepresentative 7)⁻¹ (g32p_literalRepresentative 20) :=
  g32p_archiveWord_inverse_isConj _ _ _ _ _ _
    g32p_literalIntegral_007 g32p_literalIntegral_020
    g32p_literalInverseIntegral_007 g32p_literalInverseEquation_007

def g32p_literalInverseWord_008 : List (Fin 4) := [1]

def g32p_literalInverseMatrix_008 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_literalInverseStages_008 : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_literalInverseCertificate_008 :
    g32p_archiveWordCertificate g32p_literalInverseWord_008
      g32p_literalInverseStages_008 = true := by
  decide +kernel

theorem g32p_literalInverseIntegral_008 :
    g32p_archiveIntegralWord g32p_literalInverseWord_008 =
      g32p_literalInverseMatrix_008 := by
  obtain ⟨a, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_literalInverseCertificate_008
  have ha : a = g32p_literalInverseStages_008.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, ha]
  rfl

theorem g32p_literalInverseEquation_008 :
    HurwitzPrymRex_mmul g32p_literalMatrix_008
      (HurwitzPrymRex_mmul g32p_literalInverseMatrix_008 g32p_literalMatrix_003) =
        g32p_literalInverseMatrix_008 := by
  decide +kernel

theorem g32p_literalInverseConjugacy_008 :
    IsConj (g32p_literalRepresentative 8)⁻¹ (g32p_literalRepresentative 3) :=
  g32p_archiveWord_inverse_isConj _ _ _ _ _ _
    g32p_literalIntegral_008 g32p_literalIntegral_003
    g32p_literalInverseIntegral_008 g32p_literalInverseEquation_008

def g32p_literalInverseWord_009 : List (Fin 4) := [0, 1, 2, 2, 0]

def g32p_literalInverseMatrix_009 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

def g32p_literalInverseStages_009 : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_literalInverseCertificate_009 :
    g32p_archiveWordCertificate g32p_literalInverseWord_009
      g32p_literalInverseStages_009 = true := by
  decide +kernel

theorem g32p_literalInverseIntegral_009 :
    g32p_archiveIntegralWord g32p_literalInverseWord_009 =
      g32p_literalInverseMatrix_009 := by
  obtain ⟨a, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_literalInverseCertificate_009
  have ha : a = g32p_literalInverseStages_009.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, ha]
  rfl

theorem g32p_literalInverseEquation_009 :
    HurwitzPrymRex_mmul g32p_literalMatrix_009
      (HurwitzPrymRex_mmul g32p_literalInverseMatrix_009 g32p_literalMatrix_014) =
        g32p_literalInverseMatrix_009 := by
  decide +kernel

theorem g32p_literalInverseConjugacy_009 :
    IsConj (g32p_literalRepresentative 9)⁻¹ (g32p_literalRepresentative 14) :=
  g32p_archiveWord_inverse_isConj _ _ _ _ _ _
    g32p_literalIntegral_009 g32p_literalIntegral_014
    g32p_literalInverseIntegral_009 g32p_literalInverseEquation_009

def g32p_literalInverseWord_010 : List (Fin 4) := [0, 1, 2, 2, 1, 0, 3, 3]

def g32p_literalInverseMatrix_010 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

def g32p_literalInverseStages_010 : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]],
   ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]],
   ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]],
   ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]],
   ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_literalInverseCertificate_010 :
    g32p_archiveWordCertificate g32p_literalInverseWord_010
      g32p_literalInverseStages_010 = true := by
  decide +kernel

theorem g32p_literalInverseIntegral_010 :
    g32p_archiveIntegralWord g32p_literalInverseWord_010 =
      g32p_literalInverseMatrix_010 := by
  obtain ⟨a, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_literalInverseCertificate_010
  have ha : a = g32p_literalInverseStages_010.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, ha]
  rfl

theorem g32p_literalInverseEquation_010 :
    HurwitzPrymRex_mmul g32p_literalMatrix_010
      (HurwitzPrymRex_mmul g32p_literalInverseMatrix_010 g32p_literalMatrix_015) =
        g32p_literalInverseMatrix_010 := by
  decide +kernel

theorem g32p_literalInverseConjugacy_010 :
    IsConj (g32p_literalRepresentative 10)⁻¹ (g32p_literalRepresentative 15) :=
  g32p_archiveWord_inverse_isConj _ _ _ _ _ _
    g32p_literalIntegral_010 g32p_literalIntegral_015
    g32p_literalInverseIntegral_010 g32p_literalInverseEquation_010

def g32p_literalInverseWord_011 : List (Fin 4) := []

def g32p_literalInverseMatrix_011 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_literalInverseStages_011 : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_literalInverseCertificate_011 :
    g32p_archiveWordCertificate g32p_literalInverseWord_011
      g32p_literalInverseStages_011 = true := by
  decide +kernel

theorem g32p_literalInverseIntegral_011 :
    g32p_archiveIntegralWord g32p_literalInverseWord_011 =
      g32p_literalInverseMatrix_011 := by
  obtain ⟨a, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_literalInverseCertificate_011
  have ha : a = g32p_literalInverseStages_011.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, ha]
  rfl

theorem g32p_literalInverseEquation_011 :
    HurwitzPrymRex_mmul g32p_literalMatrix_011
      (HurwitzPrymRex_mmul g32p_literalInverseMatrix_011 g32p_literalMatrix_004) =
        g32p_literalInverseMatrix_011 := by
  decide +kernel

theorem g32p_literalInverseConjugacy_011 :
    IsConj (g32p_literalRepresentative 11)⁻¹ (g32p_literalRepresentative 4) :=
  g32p_archiveWord_inverse_isConj _ _ _ _ _ _
    g32p_literalIntegral_011 g32p_literalIntegral_004
    g32p_literalInverseIntegral_011 g32p_literalInverseEquation_011


end HodgeLean.Foundations.Program

end
end
