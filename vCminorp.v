(*
 * Viola Cminor
 * File: vCminorp.v
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

Require Export compcert.backend.Cminor.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Export Violaconf.
Import ListNotations.

Inductive initial_state (p: Cminor.program): Cminor.state -> Prop :=
  | initial_state_intro: forall b fd m0 m1 m2 m3 m4 m5 m6 m_iomem s_iomem reg,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m0 ->
    Genv.find_symbol ge p.(prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some fd ->
    funsig fd = signature_main ->
    Mem.alloc m0 0 sizeof_master_iomem_space = (m1, m_iomem) ->
    Mem.alloc m1 sizeof_master_iomem_space sizeof_slave_iomem_space = (m2, s_iomem) ->
    Mem.alloc m2 (sizeof_master_iomem_space + sizeof_slave_iomem_space) sizeof_regaccess_data = (m3, reg) ->
    Mem.storebytes m3 m_iomem 0 (Memdata.inj_bytes master_iomem_space_data) = Some m4 ->
    Mem.storebytes m4 s_iomem 0 (Memdata.inj_bytes slave_iomem_space_data) = Some m5 ->
    Mem.storebytes m5 reg 0 (Memdata.inj_bytes regaccess_data) = Some m6 ->
    initial_state p (Callstate fd [ Vptr m_iomem Int.zero; Vptr s_iomem Int.zero; Vptr reg Int.zero ] Kstop m6).

Definition semantics (p: Cminor.program) :=
  Semantics Cminor.step (initial_state p) Cminor.final_state (Genv.globalenv p).
