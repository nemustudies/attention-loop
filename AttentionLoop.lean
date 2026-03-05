-- Root import file for AttentionLoop
-- Formal verification companion to "Self-Referring Attention"

-- Layer 1: Definitions (11 files)
import AttentionLoop.Defs.SimplexMap
import AttentionLoop.Defs.BlendRate
import AttentionLoop.Defs.Embedding
import AttentionLoop.Defs.LoopState
import AttentionLoop.Defs.Scoring
import AttentionLoop.Defs.Observation
import AttentionLoop.Defs.Accumulation
import AttentionLoop.Defs.Retrieval
import AttentionLoop.Defs.Consolidation
import AttentionLoop.Defs.Capture
import AttentionLoop.Defs.DerivedQuantities

-- Layer 2: Rigidity (10 files)
import AttentionLoop.Rigidity.CaptureScaleInvariant
import AttentionLoop.Rigidity.IdempotentCapture
import AttentionLoop.Rigidity.CaptureRigidity
import AttentionLoop.Rigidity.AccumulationRigidity
import AttentionLoop.Rigidity.ConsolidationRigidity
import AttentionLoop.Rigidity.PipelineRigidity
import AttentionLoop.Rigidity.TargetAxioms
import AttentionLoop.Rigidity.ScoringAdditivity
import AttentionLoop.Rigidity.StepAblation
import AttentionLoop.Rigidity.RigiditySummary

-- Layer 3: Core Dynamics (20 files)
import AttentionLoop.Core.HistoryIndependence
import AttentionLoop.Core.SelectivePersistence
import AttentionLoop.Core.RetrievalGatedStability
import AttentionLoop.Core.MonotoneAcquisition
import AttentionLoop.Core.ConvexHullInvariance
import AttentionLoop.Core.FiniteMemory
import AttentionLoop.Core.BoundedBias
import AttentionLoop.Core.NonDegeneracy
import AttentionLoop.Core.RetrievalInHull
import AttentionLoop.Core.QueryNormBound
import AttentionLoop.Core.BlendRateBounds
import AttentionLoop.Core.AttentionBudget
import AttentionLoop.Core.Lyapunov
import AttentionLoop.Core.ContractionRate
import AttentionLoop.Core.FanEffect
import AttentionLoop.Core.RetrievalWeightBounds
import AttentionLoop.Core.Convergence
import AttentionLoop.Core.SelfLimiting
import AttentionLoop.Core.PrototypeFormation
import AttentionLoop.Core.ContextVariation

-- Layer 4: Capture Inertness (7 files)
import AttentionLoop.CaptureInertness.CaptureArgmax
import AttentionLoop.CaptureInertness.SoftmaxLipschitz
import AttentionLoop.CaptureInertness.SigmaIncrement
import AttentionLoop.CaptureInertness.FiniteArgmax
import AttentionLoop.CaptureInertness.PerturbativeInertness
import AttentionLoop.CaptureInertness.KZeroInertness
import AttentionLoop.CaptureInertness.ForcedCycleGeneralK

-- Layer 5: Carrying Capacity (3 files)
import AttentionLoop.CarryingCapacity.CarryingCapacity
import AttentionLoop.CarryingCapacity.ExternalController
import AttentionLoop.CarryingCapacity.CapacityOverrun

-- Main theorem (Mathlib-only statement + proof + axiom audit)
import AttentionLoop.MainTheorem
import AttentionLoop.ProofOfMainTheorem
import AttentionLoop.Verification
