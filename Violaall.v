(*
 * Viola to asm
 * File: Violaall.v
 *
 * Copyright (c) 2017 University of California, Irvine, CA, USA
 * All rights reserved.
 *
 * Authors: Saeed Mirzamohammadi <saeed@uci.edu>
 *	    Ardalan Amiri Sani   <arrdalan@gmail.com>
 *
 * Inspired by "Jitk: A Trustworthy In-Kernel Interpreter Infrastructure" 
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

Require Import Violaspec.
Require Import Violatrans.
Require Import compcert.driver.Compiler.
Require Import compcert.common.Errors.
Require Import compcert.common.AST.
Require Import List.
Require Import ZArith.

Open Local Scope error_monad_scope.

Definition viola_to_asm (p: Violaspec.program) : res Asm.program :=
  do cmp <- Violatrans.transl_program p;
  do asp <- Compiler.transf_cminor_program cmp;
  OK asp.
