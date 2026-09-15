/-
Copyright (c) 2026 abobreshov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: abobreshov
-/

import LeanPool.StampFolding.Basic

/-!
# Stamp folding, the first five counts

Source: arxiv:1302.2025, url:https://oeis.org/A000136
Authors: abobreshov
Status: verified
Main declarations: `StampFolding.card_foldings_five`
Tags: combinatorics, stamp-folding, finite-enumeration
MSC: 05A15
-/

/-!
## Mathematical overview

The number of ways to fold a strip of `n` labelled stamps into a pile, OEIS A000136 (Lucas 1891,
Touchard 1950, Lunnon 1968, Koehler 1968; survey by Legendre, arXiv:1302.2025), has no known
closed form. `Basic` states the standard combinatorial model: a folding is a permutation of
`Fin n` giving the order of the stamps in the pile, hinges between consecutive stamps lie on one
of two sides according to parity, and two hinges on the same side must not cross. The predicate
is decidable, and `decide` proves the counts 1, 2, 6, 16, 50 for `n = 1, …, 5`, matching the
sequence.

## What is not formalized

That the permutation model is the physical folding problem, any `n ≥ 6`, and the blank-stamp
sequence A001011.
-/
