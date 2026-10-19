import Showcase_WithProofs

/-! The build fails if the public theorem's axiom report changes.
This module imports the proved showcase, which does not import Showcase. -/

/-- info: 'RieszShowcase.main_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RieszShowcase.main_theorem
