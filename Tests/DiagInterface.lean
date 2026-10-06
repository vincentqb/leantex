module

import LeanTex.Core.Diag

/-! The diagnostic record and its accounting API are public. Registry
construction and accumulation details stay private to their implementation. -/

open LeanTex.Core

example : DiagCode → Loss := DiagCode.loss
example : DiagCode → String := DiagCode.meaning
example : Array Diag → Array Diag := Diag.tallySites
example (ds : Array Diag) : (Diag.tallySites ds).size = ds.size :=
  Diag.tallySites_length ds

example : True := by
  fail_if_success have := DiagCode.spec
  fail_if_success have := DiagCode.ctorCeiling
  fail_if_success have := Diag.carrier
  fail_if_success have := Resolution.record
  trivial
