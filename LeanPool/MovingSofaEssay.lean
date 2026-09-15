/-
Copyright (c) 2026 abobreshov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: abobreshov
-/

import LeanPool.MovingSofaEssay.Basic
import LeanPool.MovingSofaEssay.Hammersley
import LeanPool.MovingSofaEssay.Problem

/-!
# The moving sofa problem

Source: arxiv:1606.08111, url:https://arxiv.org/abs/2411.19826
Authors: abobreshov
Status: verified
Main declarations: `MovingSofaEssay.hammersleySofa_movable`, `MovingSofaEssay.halfDisc_movable`, `MovingSofaEssay.hammersley_area_bounds`
Tags: moving-sofa, convex-geometry, rigid-motions
MSC: 52A40
-/

/-!
## Mathematical overview

Leo Moser posed the moving sofa problem in 1966 (SIAM Review, Problem 66-11): what is the
largest area of a planar region that can be moved around a right-angled corner in a hallway of
unit width? Hammersley (1968) gave a region of area `π/2 + 2/π ≈ 2.2074`; Gerver (1992) gave a
region of area `2.2195…`; Romik (arXiv:1606.08111) reduced Gerver's construction to a system of
differential equations and published the parameters used here; Baek (arXiv:2411.19826) claims
Gerver's region is optimal.

`Problem` states the problem: the L-shaped hallway of unit width, rigid motions as a rotation
angle and a translation, movability as a continuous path of motions on `[0, 1]` that keeps the
region inside the hallway and carries it from one arm to the other, the set of achievable areas
and the sofa constant as its supremum. It proves the unit square and the closed unit half-disc
movable.

`Hammersley` defines Hammersley's region (a rectangle `4/π` wide with two unit quarter discs and
a half-disc notch of radius `2/π`) and proves `hammersleySofa_movable`: the region passes the
corner by sliding in, turning a quarter turn while its notch centre travels a quarter circle
about the inner corner, and sliding out. It also records that the naive motion which keeps the
notch centre fixed at the corner does not fit (`proposedHammersleyMotion_fails`).

`Basic` proves the arithmetic a popular essay on the problem needs: Hammersley's area identity
`4/π + π/2 - 2/π = π/2 + 2/π`, six-decimal bounds on that number from Mathlib's bounds on `π`,
the excess of a 0.1 percent enlargement over the hallway, and that any area at least `2.2195315`
exceeds Hammersley's.

## What is not formalized

The area of `hammersleySofa`, anything about Gerver's region, any upper bound on the sofa
constant, and Baek's optimality theorem. The numerical certificates for those live outside Lean.
-/
