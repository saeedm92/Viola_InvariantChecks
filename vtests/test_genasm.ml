(*
 * File: test_genasm.ml
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

open Violaspec
open Violaconf
open Violaall
open Violadevspecs
open AST
open PrintCminor
open Errors
open Printf
open Camlcoq
open Buffer

let print_error oc msg =
  let print_one_error = function
  | Errors.MSG s -> output_string oc (Camlcoq.camlstring_of_coqstring s)
  | Errors.CTX i -> output_string oc (Camlcoq.extern_atom i)
  | Errors.POS i -> fprintf oc "%ld" (Camlcoq.P.to_int32 i)
  in
    List.iter print_one_error msg;
    output_char oc '\n';;

let gen_file f =
  let main = Violaconf.main_id in
  let p = { prog_defs = [(main, Gfun (Internal f))]; prog_main = main } in
  match Violaall.viola_to_asm p with
  | Errors.OK asm -> ( PrintAsm.print_program stdout asm; exit 0 )
  | Errors.Error msg -> ( print_error stdout msg; exit 1 )
;;

(* Galaxy Nexus mic->led invariant *)
List.map gen_file [ [gnexus_mic_led_invariant1; gnexus_mic_led_invariant2; gnexus_mic_led_invariant3; gnexus_mic_led_invariant4; gnexus_mic_led_invariant5; gnexus_mic_led_invariant6] ];;

(* Nexus 5 cam->vib invariant *)
(* List.map gen_file [ [n5_cam_vib_invariant] ];; *)

