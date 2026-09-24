/-
Copyright (c) 2026 Marco Devillers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco Devillers
-/

import Mathlib.Data.Set.Defs

/-! prefix series -/
structure Series (α : Type) where
  carrier : Set (List α)
  closed :
    (∀ ⦃xs ys : List α⦄,
      ys ∈ carrier →
      xs <:+ ys →
      xs ∈ carrier)
  shared :
    (∀ ⦃xs ys : List α⦄,
      xs ∈ carrier →
      ys ∈ carrier →
      xs <:+ ys ∨ ys <:+ xs)

noncomputable def Series.get {α : Type} (s : Series α) (n : Nat) : Option α := by
  classical
  if h : ∃ x, x ∈ s.carrier ∧ n < x.length then
    let x := Classical.choose h
    exact x[n]?
  else
    exact none
