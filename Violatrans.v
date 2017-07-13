(*
 * Viola Cminor Implementation
 * File: Violatrans.v
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
Require Import compcert.common.Errors.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.backend.Cminor.
Require Import Violaconf.
Require Import Violaspec.
Import ListNotations.

Section TRANSL.

Open Local Scope error_monad_scope.

Definition regaccess_p : ident := 1%positive.
Definition regaccess_dev_id : ident := 2%positive.
Definition regaccess_reg_off : ident := 3%positive.
Definition regaccess_val : ident := 4%positive.
Definition m_iomem_p : ident := 5%positive.
Definition s_iomem_p : ident := 6%positive.

Definition C_return_allow : Cminor.stmt :=
  Sskip.

Definition C_return_reject : Cminor.stmt :=
  Sreturn (Some ((Econst (Ointconst (Int.repr RET_REJECT))))).

Definition C_sstate_already_in_target (ss : sstate) (iomem_p : ident) : Cminor.expr :=
  let ss_reg_off := ((ss.(ss_regvar)).(rv_reg)).(reg_off) in
  let ss_regvar_mask := Econst (Ointconst (Int.repr ((ss.(ss_regvar)).(rv_mask)))) in
  let ss_regvar_off := Econst (Ointconst (Int.repr ((ss.(ss_regvar)).(rv_off)))) in
  let ss_reg_val := Econst (Ointconst (Int.repr (ss.(ss_val)))) in
  let addr := Ebinop Oadd (Evar iomem_p) (Econst (Ointconst (Int.repr ss_reg_off))) in
  Ebinop (Ocmp Ceq) ss_reg_val (Ebinop Oshru (Ebinop Oand (Eload Mint8unsigned addr) ss_regvar_mask)
                                             ss_regvar_off).

Definition C_is_tran_dst_inv_ss (tran : state_trans) (inv_ss : sstate) : Cminor.expr :=
  let inv_ss_reg_off := Econst (Ointconst (Int.repr ((inv_ss.(ss_regvar)).(rv_reg)).(reg_off))) in
  let inv_ss_val := Econst (Ointconst (Int.repr (inv_ss.(ss_val)))) in
  let inv_ss_regvar_off := Econst (Ointconst (Int.repr ((inv_ss.(ss_regvar)).(rv_off)))) in
  let inv_ss_regvar_mask := Econst (Ointconst (Int.repr ((inv_ss.(ss_regvar)).(rv_mask)))) in
  let tran_dst_reg_off := Econst (Ointconst (Int.repr (((tran.(dst)).(ss_regvar)).(rv_reg)).(reg_off))) in
  let tran_dst_val := Econst (Ointconst (Int.repr ((tran.(dst)).(ss_val)))) in
  let tran_dst_regvar_off := Econst (Ointconst (Int.repr (((tran.(dst)).(ss_regvar)).(rv_off)))) in
  let tran_dst_regvar_mask := Econst (Ointconst (Int.repr (((tran.(dst)).(ss_regvar)).(rv_mask)))) in
  Ebinop Oand (Ebinop Oand (Ebinop (Ocmp Ceq) tran_dst_reg_off inv_ss_reg_off)
                           (Ebinop (Ocmp Ceq) tran_dst_val inv_ss_val))
              (Ebinop Oand (Ebinop (Ocmp Ceq) tran_dst_regvar_off inv_ss_regvar_off)
                           (Ebinop (Ocmp Ceq) tran_dst_regvar_mask inv_ss_regvar_mask)).

Definition C_is_tran_dst_not_inv_ss (tran : state_trans) (inv_ss : sstate) : Cminor.expr :=
  let inv_ss_reg_off := Econst (Ointconst (Int.repr ((inv_ss.(ss_regvar)).(rv_reg)).(reg_off))) in
  let inv_ss_val := Econst (Ointconst (Int.repr (inv_ss.(ss_val)))) in
  let inv_ss_regvar_off := Econst (Ointconst (Int.repr ((inv_ss.(ss_regvar)).(rv_off)))) in
  let inv_ss_regvar_mask := Econst (Ointconst (Int.repr ((inv_ss.(ss_regvar)).(rv_mask)))) in
  let tran_dst_reg_off := Econst (Ointconst (Int.repr (((tran.(dst)).(ss_regvar)).(rv_reg)).(reg_off))) in
  let tran_dst_val := Econst (Ointconst (Int.repr ((tran.(dst)).(ss_val)))) in
  let tran_dst_regvar_off := Econst (Ointconst (Int.repr (((tran.(dst)).(ss_regvar)).(rv_off)))) in
  let tran_dst_regvar_mask := Econst (Ointconst (Int.repr (((tran.(dst)).(ss_regvar)).(rv_mask)))) in
  Ebinop Oand (Ebinop Oand (Ebinop (Ocmp Ceq) tran_dst_reg_off inv_ss_reg_off)
                           (Ebinop (Ocmp Cne) tran_dst_val inv_ss_val))
              (Ebinop Oand (Ebinop (Ocmp Ceq) tran_dst_regvar_off inv_ss_regvar_off)
                           (Ebinop (Ocmp Ceq) tran_dst_regvar_mask inv_ss_regvar_mask)).

Definition C_is_tran_event_triggered (tran : state_trans) : Cminor.expr :=
  let tran_event_reg_off := Econst (Ointconst (Int.repr ((((tran.(evnt)).(ev_regvar)).(rv_reg)).(reg_off)))) in
  let tran_event_regvar_off := Econst (Ointconst (Int.repr (((tran.(evnt)).(ev_regvar)).(rv_off)))) in
  let tran_event_regvar_mask := Econst (Ointconst (Int.repr (((tran.(evnt)).(ev_regvar)).(rv_mask)))) in
  let tran_event_val := Econst (Ointconst (Int.repr ((tran.(evnt)).(ev_val)))) in
  match (tran.(evnt)).(ev_type) with
  | ev_eq => Ebinop Oand (Ebinop (Ocmp Ceq) tran_event_reg_off (Evar regaccess_reg_off))
              (Ebinop (Ocmp Ceq) tran_event_val (Ebinop Oshru (Ebinop Oand (Evar regaccess_val)
                                                                           tran_event_regvar_mask)
                                                              tran_event_regvar_off))
  | ev_ne => Ebinop Oand (Ebinop (Ocmp Ceq) tran_event_reg_off (Evar regaccess_reg_off))
              (Ebinop (Ocmp Cne) tran_event_val (Ebinop Oshru (Ebinop Oand (Evar regaccess_val)
                                                                           tran_event_regvar_mask)
                                                              tran_event_regvar_off))
  end.

Definition C_is_tran_src_satisfied (tran : state_trans) (iomem_p : ident) : Cminor.expr :=
  let any_srcss := Econst (Ointconst (Int.repr (tran.(src)).(any_srcss))) in
  let tran_src_reg_off := Econst (Ointconst (Int.repr ((((((tran.(src).(exact_srcss))).(ss_regvar)).(rv_reg)).(reg_off))))) in
  let tran_src_regvar_off := Econst (Ointconst (Int.repr ((((tran.(src).(exact_srcss)).(ss_regvar)).(rv_off))))) in
  let tran_src_regvar_mask := Econst (Ointconst (Int.repr ((((tran.(src).(exact_srcss))).(ss_regvar)).(rv_mask)))) in
  let tran_src_val := Econst (Ointconst (Int.repr (((tran.(src).(exact_srcss))).(ss_val)))) in
  let addr := Ebinop Oadd (Evar iomem_p) tran_src_reg_off in
  Ebinop Oor (Ebinop (Ocmp Cne) any_srcss (Econst (Ointconst Int.zero)))
             (C_sstate_already_in_target (tran.(src)).(exact_srcss) iomem_p).

Fixpoint C_will_sstate_go_to_target (inv_ss : sstate) (trans: list state_trans) (iomem_p : ident) : Cminor.expr :=
  match trans with
  | nil => Econst (Ointconst Int.zero)
  | hd :: tl => Ebinop Oor (Ebinop Oand (Ebinop Oand (C_is_tran_dst_inv_ss hd inv_ss)
                                                     (C_is_tran_event_triggered hd))
                                        (C_is_tran_src_satisfied hd iomem_p))
                           (C_will_sstate_go_to_target inv_ss tl iomem_p)
  end.

Fixpoint C_will_sstate_go_out_of_target (inv_ss : sstate) (trans: list state_trans) (iomem_p : ident) : Cminor.expr :=
  match trans with
  | nil => Econst (Ointconst Int.zero)
  | hd :: tl => Ebinop Oor (Ebinop Oand (Ebinop Oand (C_is_tran_dst_not_inv_ss hd inv_ss)
                                                     (C_is_tran_event_triggered hd))
                                        (C_is_tran_src_satisfied hd iomem_p))
                           (C_will_sstate_go_out_of_target inv_ss tl iomem_p)
  end.

Fixpoint __C_will_dev_go_target_state (trans : list state_trans) (inv_ss : list sstate)
                                      (iomem_p : ident): Cminor.expr :=
  match inv_ss with
  | nil => Econst (Ointconst Int.one)
  | hd :: tl => let now_ss := C_sstate_already_in_target hd iomem_p in
                let will_ss := C_will_sstate_go_to_target hd trans iomem_p in
                Ebinop Oand (Ebinop Oor will_ss now_ss)
                           (__C_will_dev_go_target_state trans tl iomem_p)
  end.

Fixpoint __C_will_dev_go_out_of_target_state (trans : list state_trans) (inv_ss : list sstate)
                                      (iomem_p : ident) : Cminor.expr :=
  match inv_ss with
  | nil => Econst (Ointconst Int.zero)
  | hd :: tl => let now_ss := C_sstate_already_in_target hd iomem_p in 
                let will_ss_go_out := C_will_sstate_go_out_of_target hd trans iomem_p in
                Ebinop Oor (Ebinop Oand will_ss_go_out now_ss)
                           (__C_will_dev_go_out_of_target_state trans tl iomem_p)
  end.

Definition C_will_dev_go_target_state (trans : list state_trans) (inv_ss : list sstate)
                                      (iomem_p : ident) : Cminor.expr :=
  match inv_ss with
  | nil => Econst (Ointconst Int.zero)
  | _ => __C_will_dev_go_target_state trans inv_ss iomem_p
  end.

Definition C_will_dev_go_out_of_target_state (trans : list state_trans) (inv_ss : list sstate)
                                          (iomem_p : ident) : Cminor.expr :=
  match inv_ss with
  | nil => Econst (Ointconst Int.one)
  | _ => __C_will_dev_go_out_of_target_state trans inv_ss iomem_p
  end.

Fixpoint __C_is_dev_in_target_state (iomem_p : ident) (inv_ss : list sstate) : Cminor.expr :=
  match inv_ss with
  | nil => Econst (Ointconst Int.one)
  | hd :: tl => Ebinop Oand (C_sstate_already_in_target hd iomem_p)
                            (__C_is_dev_in_target_state iomem_p tl)
  end.

Definition C_is_dev_in_target_state (iomem_p : ident) (inv_ss : list sstate) : Cminor.expr :=
  match inv_ss with
  | nil => Econst (Ointconst Int.zero)
  | _ => __C_is_dev_in_target_state iomem_p inv_ss
  end.

Definition NOT_C_is_dev_in_target_state (iomem_p : ident) (inv_ss : list sstate) : Cminor.expr :=
  Ebinop Oxor (C_is_dev_in_target_state iomem_p inv_ss) (Econst (Ointconst Int.one)).

Fixpoint C_is_valid_dev_access (regs : list register): Cminor.expr :=
  match regs with
  | nil => Econst (Ointconst Int.zero)
  | hd :: tl => let reg_off := hd.(reg_off) in
                Ebinop Oor (Ebinop (Ocmp Ceq) (Evar regaccess_reg_off) (Econst (Ointconst (Int.repr reg_off)))) 
                           (C_is_valid_dev_access tl)
  end.

Definition C_eval_master_access (i : invariant) : Cminor.stmt :=
  Sifthenelse (C_is_valid_dev_access (i.(master_dev)).(regs))
    (Sifthenelse (Ebinop Oand (C_will_dev_go_target_state (i.(master_dev)).(trans)
                                                          (i.(inv_master)).(inv_ss) m_iomem_p)
                              (NOT_C_is_dev_in_target_state s_iomem_p (i.(inv_slave)).(inv_ss)))
                 C_return_reject C_return_allow)
    C_return_allow.

Definition C_eval_slave_access (i : invariant) : Cminor.stmt :=
  Sifthenelse (C_is_valid_dev_access (i.(slave_dev)).(regs))
    (Sifthenelse (Ebinop Oand (C_will_dev_go_out_of_target_state (i.(slave_dev)).(trans)
                                                              (i.(inv_slave)).(inv_ss) s_iomem_p)
                              (C_is_dev_in_target_state m_iomem_p (i.(inv_master)).(inv_ss)))
                 C_return_reject C_return_allow)
    C_return_allow.

Definition C_is_dev_access (dev_id : Z): Cminor.expr :=
  Ebinop (Ocmp Ceq) (Evar regaccess_dev_id) (Econst (Ointconst (Int.repr dev_id))).

Definition transl_uni_r_binder (i : invariant) : Cminor.stmt :=
  Sifthenelse (C_is_dev_access (i.(master_dev)).(dev_id)) (C_eval_master_access i)
  (Sifthenelse (C_is_dev_access (i.(slave_dev)).(dev_id)) (C_eval_slave_access i) C_return_allow).

Definition transl_invariant (i: invariant) : res Cminor.stmt :=
  match (i.(inv_binder)) with
  | uni_r => OK (transl_uni_r_binder i) (* Unidirectional invariant *)
  | bidir => OK Sskip 			(* Two-directional invariant. Not implemented: the invariant is ignored *)
  end.

Fixpoint transl_code (c: Violaspec.code) : res Cminor.stmt :=
  match c with
  | nil => OK (Sreturn (Some ((Econst (Ointconst (Int.repr RET_ALLOW))))))
  | hd::tl =>
    let n := length tl in
    do t <- transl_code tl;
    do h <- transl_invariant hd;
    OK (Sseq h t)
  end.

Definition transl_funbody (f: Violaspec.function) : res Cminor.stmt :=
  do b <- transl_code f;
  let regaccess_dev_id_offset := Econst (Ointconst (Int.repr REGACCESS_DEV_ID_OFFSET)) in
  let regaccess_dev_id_p := Ebinop Oadd (Evar regaccess_p) regaccess_dev_id_offset in
  let init_a := (Sassign regaccess_dev_id (Eload Mint8unsigned regaccess_dev_id_p)) in
  let regaccess_reg_off_offset := Econst (Ointconst (Int.repr REGACCESS_REG_OFF_OFFSET)) in
  let regaccess_reg_off_p := Ebinop Oadd (Evar regaccess_p) regaccess_reg_off_offset in
  let init_b := (Sassign regaccess_reg_off (Eload Mint8unsigned regaccess_reg_off_p)) in
  let regaccess_val_offset := Econst (Ointconst (Int.repr REGACCESS_VAL_OFFSET)) in
  let regaccess_val_p := Ebinop Oadd (Evar regaccess_p) regaccess_val_offset in
  let init_c := (Sassign regaccess_val (Eload Mint8unsigned regaccess_val_p)) in
  OK (Sseq init_a (Sseq init_b (Sseq init_c b))).

Definition transl_function (f: Violaspec.function) : res Cminor.function :=
  do body <- transl_funbody f;
  let params := [ m_iomem_p; s_iomem_p; regaccess_p ] in
  let vars := [ regaccess_dev_id; regaccess_reg_off; regaccess_val ] in
  let stackspace := 4 * viola_memwords in
  OK (Cminor.mkfunction signature_main params vars stackspace body).

Definition transl_fundef (fd: Violaspec.fundef) :=
  match fd with
  | Internal f => do f' <- transl_function f; OK (Internal f')
  | External ef => Error (msg "no external function allowed")
  end.

Definition transl_program (p: Violaspec.program) : res Cminor.program :=
  transform_partial_program transl_fundef p.

End TRANSL.
