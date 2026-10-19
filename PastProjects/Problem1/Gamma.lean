import Riesz.PastProjects.Problem1.Sphere

noncomputable section

namespace Problem1

-- lem:gamma-negative-strip: Problem1.gamma_negative_strip
theorem gamma_negative_strip (a : ℝ) (haLower : -1 < a) (haUpper : a < 0) :
  Real.Gamma a < 0 := by
  nlinarith [Real.Gamma_add_one haUpper.ne,
    Real.Gamma_pos_of_pos (show 0 < a + 1 by linarith)]


end Problem1
