(*
 * Viola Configs
 * File: Violaconf.v
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

Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Import ListNotations.

Parameter sizeof_master_iomem_space : Z. (**r sizeof master mmio space *)
Axiom sizeof_master_iomem_space_pos: 0 < sizeof_master_iomem_space.

Parameter master_iomem_space_data : list byte.
Axiom length_master_iomem_space : list_length_z master_iomem_space_data = sizeof_master_iomem_space.

Parameter sizeof_slave_iomem_space : Z. (**r sizeof slave mmio space *)
Axiom sizeof_slave_iomem_space_pos: 0 < sizeof_slave_iomem_space.

Parameter slave_iomem_space_data : list byte.
Axiom length_slave_iomem_space : list_length_z slave_iomem_space_data = sizeof_slave_iomem_space.

Parameter sizeof_regaccess_data : Z. (**r sizeof data of a register access *)
Axiom sizeof_regaccess_data_pos: 0 < sizeof_regaccess_data.

Parameter regaccess_data : list byte.
Axiom length_regaccess_data : list_length_z regaccess_data = sizeof_regaccess_data.

Parameter viola_memwords : Z.
Axiom viola_memwords_pos: 0 < viola_memwords.
Axiom viola_memwords_noovfl: 4 * viola_memwords < Int.modulus.

Parameter ident_of_string : String.string -> ident.

Definition Tpointer := Tint. (* assume 32-bit pointers *)

Definition signature_main := mksignature [ Tpointer; Tpointer; Tpointer ] (Some Tint) cc_default.

Local Open Scope string_scope.

Definition main_id := ident_of_string "viola_main".
