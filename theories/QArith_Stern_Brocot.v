(************************************************************************)
(* Copyright 2006 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/lgpl-2.1.html>         *)
(************************************************************************)

(* Importing this file will provide a theory of rational numbers as a
denumerable Archimedean ordered field with decidable equality. *)

(* NB: This file will also import Q_to_R.v for dealing with the image
of Q in R. This in turn will import the real numbers form the standard
library. If you do not want to use these (classical) real numbers you
should not import this file. Instead you can use all the other modules
that are imported here, except Q_to_R.  *)

From QArithSternBrocot Require Export Qsyntax.
From QArithSternBrocot Require Export Field_Theory_Q.
From QArithSternBrocot Require Export Q_ordered_field_properties.
From QArithSternBrocot Require Export Qabs.
From QArithSternBrocot Require Export Qmax_min.
From QArithSternBrocot Require Export Q_Archimedean.
From QArithSternBrocot Require Export Q_denumerable.
From QArithSternBrocot Require Export Q_to_R.
