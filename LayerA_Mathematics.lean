import «Feffermann-Classification»
import Fefferman.MovingFrame

set_option autoImplicit false

namespace Fefferman

/- Layer A is the mathematical core.  It contains the R3/T3 NSE/Fefferman
   reconstruction, MasterAC, intrinsic-force identification, and the finite
   moving Parseval-frame theorem.  It has no dependency on the physics
   example layer. -/

theorem LAYER_A_MASTER_AC_TO_FEFFERMAN_AC {a : Analysis} (o : LedgerArithmetic a)
    (m : R3DerivationModel a) (h : MasterAC m) (p : MasterACProjection m) :
    A a ∧ C a :=
  MASTER_AC_IMPLIES_FEFFERMAN_A_AND_C o m h p

end Fefferman
