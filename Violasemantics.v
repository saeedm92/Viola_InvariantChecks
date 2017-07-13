(*
 * Viola semantics
 * File: Viola.v
 *
 * Copyright (c) 2017 University of California, Irvine, CA, USA
 * All rights reserved.
 *
 * Authors: Saeed Mirzamohammadi <saeed@uci.edu>
 *	    Ardalan Amiri Sani   <arrdalan@gmail.com>
 *
 * Originally from "Jitk: A Trustworthy In-Kernel Interpreter Infrastructure" 
 * from http://css.csail.mit.edu/jitk/
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 as published by
 * the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 * more details.
 *
 * You should have received a copy of the GNU General Public License along with
 * this program.  If not, see <http://www.gnu.org/licenses/>.
 *)

Require Import compcert.common.Globalenvs.
Require Import compcert.common.Smallstep.
Require Import compcert.lib.Coqlib.
Require Import Violaspec.
Require Import CpdtTactics.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

Lemma trace_E0:
  forall p s t s', Step (semantics p) s t s' -> t = nil.
Proof.
  intros.
  destruct H; auto.
Qed.

Lemma semantics_receptive:
  forall (p: program), receptive (semantics p).
Proof.
  intro.
  constructor; simpl; intros.

  exists s1.
  assert (t1 = t2).
  assert (t1 = nil).
  apply (trace_E0 p s t1 s1). auto.
  destruct H0; crush.
  crush.

  constructor.
  destruct H; auto.
Qed.
