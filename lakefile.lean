import Lake
open Lake DSL

package nseFeffermanABCD where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

@[default_target]
lean_lib NSEFefferman where
  roots := #[`All]
  globs := #[
    .one `All,
    .one `Audit,
    .one `ConcreteABCDUnifiedClosure,
    .one `Fefferman.Analysis,
    .one `Fefferman.CanonicalSource,
    .one `Fefferman.Continuation,
    .one `Fefferman.DerivationSupport,
    .one `Fefferman.FiniteSpectral,
    .one `Fefferman.ForceRegimes,
    .one `Fefferman.IntrinsicIdentification,
    .one `Fefferman.KernelAlgebra,
    .one `Fefferman.KernelBirth,
    .one `Fefferman.KernelCalculus,
    .one `Fefferman.KernelCapacity,
    .one `Fefferman.KernelCovariance,
    .one `Fefferman.KernelCritical,
    .one `Fefferman.KernelGeometry,
    .one `Fefferman.KernelPackets,
    .one `Fefferman.KernelRenewal,
    .one `Fefferman.KernelStorage,
    .one `Fefferman.Logic,
    .one `Fefferman.MasterAC,
    .one `Fefferman.MasterCore,
    .one `Fefferman.MovingFrame,
    .one `Fefferman.Obstructions,
    .one `Fefferman.PhysicsClassical,
    .one `Fefferman.PhysicsGravity,
    .one `Fefferman.PhysicsQuantum,
    .one `Fefferman.PhysicsUnification,
    .one `Fefferman.PhysicsVariationalTransport,
    .one `Fefferman.ProjectRoutes,
    .one `Fefferman.R3SourceBranch,
    .one `Fefferman.ReconstructedRoutes,
    .one `Fefferman.ReducedCapacity,
    .one `Fefferman.ScalarLedger,
    .one `Fefferman.SourceGeometry,
    .one `Fefferman.Statements,
    .one `Fefferman.T3IntegralBranch,
    .one `«Feffermann-Classification»,
    .one `LayerA_Mathematics,
    .one `LayerB_Physics,
    .one `Master_R3_derivation,
    .one `Master_R3_details,
    .one `Master_T3,
    .one `Master_T3_derivation,
    .one `Master_T3_details,
    .one `Master_r3,
    .one `NSE.Audit,
    .one `NSE.Completion,
    .one `NSE.Continuation,
    .one `NSE.CriticalBalance,
    .one `NSE.HilbertEntrance,
    .one `NSE.Injection,
    .one `NSE.LHLedger,
    .one `NSE.NSEAnchor,
    .one `NSE.PrefixPayment,
    .one `NSE.Representation,
    .one `NSE.Serrin,
    .one `NSEForcingRegularityClasses,
    .one `Types
  ]
