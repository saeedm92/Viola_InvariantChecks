(*
 * Viola Code Extraction
 * File: extraction.v
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

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import Violaconf.
Require Import Violaspec.
Require Import Violatrans.
Require Import Violaall.
Require Import Violadevspecs.
Require Import compcert.common.Errors.

Extraction Blacklist List String Int.

Extraction Inline Errors.bind Errors.bind2.

Extract Constant ident_of_string =>
  "fun s -> Camlcoq.intern_string (Camlcoq.camlstring_of_coqstring s)".

Extract Constant Violaconf.sizeof_master_iomem_space =>
  "Violaaux.sizeof_master_iomem_space".

Extract Constant Violaconf.master_iomem_space_data =>
  "[]".

Extract Constant Violaconf.sizeof_slave_iomem_space =>
  "Violaaux.sizeof_slave_iomem_space".

Extract Constant Violaconf.slave_iomem_space_data =>
  "[]".

Extract Constant Violaconf.sizeof_regaccess_data =>
  "Violaaux.sizeof_regaccess_data".

Extract Constant Violaconf.regaccess_data =>
  "[]".

Extract Constant Violaconf.viola_memwords =>
  "Violaaux.viola_memwords".

Extract Constant Violaspec.RET_REJECT  => "Violaaux.ret_reject".
Extract Constant Violaspec.RET_ALLOW  => "Violaaux.ret_allow".

Cd "vcodegen".
Extraction Library Violaconf.
Extraction Library Violaspec.
Extraction Library Violatrans.
Extraction Library Violaall.
Extraction Library Violadevspecs.
