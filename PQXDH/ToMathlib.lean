/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import ToMathlib.Control.WriterT

instance instLawfulMonadLiftWriterTAppend {ω : Type} {m : Type → Type}
    [Monad m] [EmptyCollection ω] [Append ω] [LawfulAppend ω] [LawfulMonad m] :
    LawfulMonadLift m (WriterT ω m) where
  monadLift_pure x := map_pure (·, ∅) x
  monadLift_bind {α β} x y := by
    change WriterT.mk _ = WriterT.mk _
    simp [WriterT.monadLift_def', WriterT.mk, WriterT.run]
