(*
 * Viola aux
 * File: Violaaux.ml
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

open BinPos
open Camlcoq

let sizeof_master_iomem_space = coqint_of_camlint (Int32.of_int 2)
let sizeof_slave_iomem_space = coqint_of_camlint (Int32.of_int 2)
let sizeof_regaccess_data = coqint_of_camlint (Int32.of_int 2)

let viola_memwords = Camlcoq.Z.of_uint 0

let ret_allow  = coqint_of_camlint 0l;;
let ret_reject  = coqint_of_camlint 0x00030000l;;
