(*
 * Viola Specifications
 * File: Violaspec.v
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
Require Import compcert.lib.Maps.
Require Import Violaconf.
Require Import CpdtTactics.
Require Import MiscLemmas.
Require Import Coq.ZArith.Int.

Import ListNotations.

Record register : Type := mkreg {
  reg_off: Z;
  init_val: Z
}.

Record reg_var : Type := mkregvar {
  rv_reg: register;
  rv_off: Z;
  rv_mask: Z
}.

Record sstate : Type := mksstate {
  ss_regvar: reg_var;
  ss_val: Z
}.

Inductive event_type : Type :=
  | ev_eq : event_type
  | ev_ne : event_type.

Record vevent : Type := mkvevent {
  ev_type: event_type; 
  ev_regvar: reg_var;
  ev_val: Z
}.

Record src_sstate : Type := mksrcsstate {
  any_srcss : Z;
  exact_srcss : sstate
}.

Record state_trans : Type := mkstrans {
  src: src_sstate;
  evnt: vevent;
  dst: sstate
}.

Record device_spec : Type := mkdevspec {
  dev_id: Z;
  regs: list register;           (**r device registers: each register is represented
                                      as an offset from iomem base *)
  regvars: list reg_var;         (**r device register variables *)
  sstates: list sstate;          (**r device sub-states *)
  evnts: list vevent;            (**r device events (read/write to registers) *)
  trans: list state_trans        (**r state transitions *)
}.

Record inv_dev_state : Type := mkinvdstate {
  inv_ss: list sstate
}.


Inductive binder : Type :=
  | uni_r : binder
  | bidir : binder.

Inductive action : Type :=
  | A_reject : action
  | A_allow  : action.

Parameter RET_REJECT  : Z.
Parameter RET_ALLOW   : Z.

Notation REGACCESS_DEV_ID_OFFSET := 0%Z.
Notation REGACCESS_REG_OFF_OFFSET := 1%Z.
Notation REGACCESS_VAL_OFFSET := 2%Z.

Definition action_enc (a: action) :=
  match a with
  | A_reject    => Int.repr RET_REJECT
  | A_allow     => Int.repr RET_ALLOW
  end.

Record invariant : Type := mkinv {
  inv_binder: binder;
  inv_master: inv_dev_state;
  inv_slave: inv_dev_state;
  master_dev: device_spec;
  slave_dev: device_spec
}.

Definition code := list invariant.

Section PROGRAM.

Definition function := code.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

End PROGRAM.

Section SEMANTICS.

Definition genv := Genv.t fundef unit.

Inductive state : Type :=
  | State:
    forall (f: function)         (**r function *)
           (c: code)             (**r current invariant *)
           (om: block)           (**r master iomem space *)
           (os: block)           (**r slave iomem space *)
           (rid: int)            (**r register access: device id *)
           (roff: int)           (**r register access: register off *)
           (rval: int)           (**r register access: register val (to be written) *)
           (m: mem),             (**r memory state *)
    state
  | Callstate:
    forall (fd: fundef)          (**r calling function *)
           (om: block)           (**r master iomem space *)
           (os: block)           (**r slave iomem space *)
           (r: block)            (**r register access arguments *) 
           (m: mem),             (**r memory state *)
    state
  | Returnstate:
    forall (a: action),          (**r action *)
    state
  .

Local Notation "a # b" := (PMap.get b a) (at level 1).

Definition reg_to_int (reg : register) :=
  Int.repr reg.(reg_off).

Definition bsel (vl: list memval) :=
  match proj_bytes vl with
  | Some bl => bl
  | None    => []
  end.

Definition decode_val_Mint8unsigned_int (vl: list memval) : int :=
  Int.zero_ext 8 (Int.repr (decode_int (bsel vl))).

Definition my_load_Mint8unsigned_int (m : mem) (b : block) (ofs : Z) : int :=
  decode_val_Mint8unsigned_int (Mem.getN (size_chunk_nat Mint8unsigned) ofs (m.(Mem.mem_contents)#b)).

Definition decode_val_Mint8unsigned (vl: list memval) : val :=
  Vint (Int.zero_ext 8 (Int.repr (decode_int (bsel vl)))).

Definition my_load_Mint8unsigned (m : mem) (b : block) (ofs : Z) : val :=
  decode_val_Mint8unsigned (Mem.getN (size_chunk_nat Mint8unsigned) ofs (m.(Mem.mem_contents)#b)).

Definition NOT_ss_in_target (ss: sstate) (o: block) (rid roff rval: int) (m: mem) :=
  Vint (Int.repr ss.(ss_val)) <> Val.shru (Val.and (my_load_Mint8unsigned m o (Int.unsigned (Int.repr (((ss.(ss_regvar)).(rv_reg)).(reg_off)))))
                                                  (Vint (Int.repr ((ss.(ss_regvar)).(rv_mask)))))
                                         (Vint (Int.repr ((ss.(ss_regvar)).(rv_off)))).

Definition ss_in_target (ss: sstate) (o: block) (rid roff rval: int) (m: mem) :=
  Vint (Int.repr ss.(ss_val)) = Val.shru (Val.and (my_load_Mint8unsigned m o (Int.unsigned (Int.repr (((ss.(ss_regvar)).(rv_reg)).(reg_off)))))
                                                  (Vint (Int.repr ((ss.(ss_regvar)).(rv_mask)))))
                                         (Vint (Int.repr ((ss.(ss_regvar)).(rv_off)))).

Definition is_tran_dst_inv_ss (tran: state_trans) (ss: sstate) (o: block) (rid roff rval: int) (m: mem) :=
  Int.repr ((((tran.(dst)).(ss_regvar)).(rv_reg)).(reg_off)) = Int.repr (((ss.(ss_regvar)).(rv_reg)).(reg_off)) /\
  Int.repr ((tran.(dst)).(ss_val)) = Int.repr (ss.(ss_val)) /\
  Int.repr (((tran.(dst)).(ss_regvar)).(rv_off)) = Int.repr ((ss.(ss_regvar)).(rv_off)) /\
  Int.repr (((tran.(dst)).(ss_regvar)).(rv_mask)) = Int.repr ((ss.(ss_regvar)).(rv_mask)).

Definition is_tran_dst_not_inv_ss (tran: state_trans) (ss: sstate) (o: block) (rid roff rval: int) (m: mem) :=
  Int.repr ((((tran.(dst)).(ss_regvar)).(rv_reg)).(reg_off)) = Int.repr (((ss.(ss_regvar)).(rv_reg)).(reg_off)) /\
  Int.repr ((tran.(dst)).(ss_val)) <> Int.repr (ss.(ss_val)) /\
  Int.repr (((tran.(dst)).(ss_regvar)).(rv_off)) = Int.repr ((ss.(ss_regvar)).(rv_off)) /\
  Int.repr (((tran.(dst)).(ss_regvar)).(rv_mask)) = Int.repr ((ss.(ss_regvar)).(rv_mask)).

Definition is_tran_triggered (tran: state_trans) (ss: sstate) (o: block) (rid roff rval: int) (m: mem) :=
  match (tran.(evnt)).(ev_type) with
  | ev_eq => (Int.repr ((((tran.(evnt)).(ev_regvar)).(rv_reg)).(reg_off))) = roff /\
             Val.shru (Val.and (Vint rval) (Vint (Int.repr ((((tran.(evnt)).(ev_regvar)).(rv_mask))))))
                      (Vint (Int.repr ((((tran.(evnt)).(ev_regvar)).(rv_off))))) = (Vint (Int.repr ((((tran.(evnt)).(ev_val))))))
  | ev_ne => (Int.repr ((((tran.(evnt)).(ev_regvar)).(rv_reg)).(reg_off))) = roff /\
             Val.shru (Val.and (Vint rval) (Vint (Int.repr ((((tran.(evnt)).(ev_regvar)).(rv_mask))))))
                      (Vint (Int.repr ((((tran.(evnt)).(ev_regvar)).(rv_off))))) <> (Vint (Int.repr ((((tran.(evnt)).(ev_val))))))
  end.

Definition is_tran_src_satisfied (tran: state_trans) (ss: sstate) (o: block) (rid roff rval: int) (m: mem) :=
  Int.repr (tran.(src)).(any_srcss) <> Int.zero \/ ss_in_target (tran.(src)).(exact_srcss) o rid roff rval m.

Definition will_ss_go_to_target (s: device_spec) (ss: sstate) (o: block) (rid roff rval: int) (m: mem) :=
  s.(trans) <> [] /\ exists tran, In tran s.(trans) /\ is_tran_dst_inv_ss tran ss o rid roff rval m /\ is_tran_triggered tran ss o rid roff rval m
                                 /\ is_tran_src_satisfied tran ss o rid roff rval m.

Definition NOT_will_ss_go_to_target (s: device_spec) (ss: sstate) (o: block) (rid roff rval: int) (m: mem) :=
  s.(trans) = [] \/ forall tran, In tran s.(trans) -> ~ (is_tran_dst_inv_ss tran ss o rid roff rval m /\ is_tran_triggered tran ss o rid roff rval m
                                 /\ is_tran_src_satisfied tran ss o rid roff rval m).

Definition will_ss_go_out_of_target (s: device_spec) (ss: sstate) (o: block) (rid roff rval: int) (m: mem) :=
  s.(trans) <> [] /\ exists tran, In tran s.(trans) /\ is_tran_dst_not_inv_ss tran ss o rid roff rval m /\ is_tran_triggered tran ss o rid roff rval m
                                 /\ is_tran_src_satisfied tran ss o rid roff rval m.

Definition NOT_will_ss_go_out_of_target (s: device_spec) (ss: sstate) (o: block) (rid roff rval: int) (m: mem) :=
  s.(trans) = [] \/ forall tran, In tran s.(trans) -> ~ (is_tran_dst_not_inv_ss tran ss o rid roff rval m /\ is_tran_triggered tran ss o rid roff rval m
                                 /\ is_tran_src_satisfied tran ss o rid roff rval m).

Definition will_go_to_target_state (s: device_spec) (is : inv_dev_state) (o: block) (rid roff rval: int) (m: mem) :=
  is.(inv_ss) <> [] /\ forall ss, In ss is.(inv_ss) -> (ss_in_target ss o rid roff rval m \/ will_ss_go_to_target s ss o rid roff rval m).

Definition NOT_will_go_to_target_state (s: device_spec) (is : inv_dev_state) (o: block) (rid roff rval: int) (m: mem) :=
  is.(inv_ss) = [] \/ exists ss, In ss is.(inv_ss) /\ ~(ss_in_target ss o rid roff rval m \/ will_ss_go_to_target s ss o rid roff rval m).

Definition will_go_out_of_target_state (s: device_spec) (is : inv_dev_state) (o: block) (rid roff rval: int) (m: mem) :=
  is.(inv_ss) = [] \/ exists ss, In ss is.(inv_ss) /\ (ss_in_target ss o rid roff rval m /\ will_ss_go_out_of_target s ss o rid roff rval m).

Definition NOT_will_go_out_of_target_state (s: device_spec) (is : inv_dev_state) (o: block) (rid roff rval: int) (m: mem) :=
  is.(inv_ss) <> [] /\ forall ss, In ss is.(inv_ss) -> ~ (ss_in_target ss o rid roff rval m /\ will_ss_go_out_of_target s ss o rid roff rval m).

Definition is_in_target_state (s: device_spec) (is : inv_dev_state) (o: block) (rid roff rval: int) (m: mem) :=
  is.(inv_ss) <> [] /\ forall ss, In ss is.(inv_ss) -> ss_in_target ss o rid roff rval m.

Definition master_eval_reject (i: invariant) (om os: block) (rid roff rval: int) (m: mem) :=
  (In roff (map reg_to_int (i.(master_dev)).(regs)) /\
   will_go_to_target_state i.(master_dev) i.(inv_master) om rid roff rval m /\
   ~ is_in_target_state i.(slave_dev) i.(inv_slave) os rid roff rval m).

Definition slave_eval_reject (i: invariant) (om os: block) (rid roff rval: int) (m: mem) :=
  (In roff (map reg_to_int (i.(slave_dev)).(regs)) /\
   will_go_out_of_target_state i.(slave_dev) i.(inv_slave) os rid roff rval m /\
   is_in_target_state i.(master_dev) i.(inv_master) om rid roff rval m).

Definition trans_uni_r_reject (i: invariant) (om os: block) (rid roff rval: int) (m: mem) :=
  (rid = Int.repr (i.(master_dev)).(dev_id) /\ master_eval_reject i om os rid roff rval m) \/ 
  (~(rid = Int.repr (i.(master_dev)).(dev_id)) /\ (rid = Int.repr (i.(slave_dev)).(dev_id) /\ 
                                                   slave_eval_reject i om os rid roff rval m)).

Definition eval_inv_reject (i: invariant) (om os: block) (rid roff rval: int) (m: mem) :=
  i.(inv_binder) = uni_r /\
  trans_uni_r_reject i om os rid roff rval m.

Inductive step (ge: genv) : state -> trace -> state -> Prop :=
  | exec_reject:
    forall f c i om os rid roff rval m,
    eval_inv_reject i om os rid roff rval m ->
    step ge (State f (i :: c) om os rid roff rval m)
         E0 (Returnstate A_reject)

  | exec_skip:
    forall f c i om os rid roff rval m,
    ~ eval_inv_reject i om os rid roff rval m ->
    step ge (State f (i :: c) om os rid roff rval m)
         E0 (State f c om os rid roff rval m)

  | exec_allow:
    forall f om os rid roff rval m,
    step ge (State f [] om os rid roff rval m)
         E0 (Returnstate A_allow)
  | exec_call:
    forall  f om os r rid roff rval m,
    Mem.load Mint8unsigned m r REGACCESS_DEV_ID_OFFSET = Some (Vint rid) ->
    Mem.load Mint8unsigned m r REGACCESS_REG_OFF_OFFSET = Some (Vint roff) ->
    Mem.load Mint8unsigned m r REGACCESS_VAL_OFFSET = Some (Vint rval) ->
    step ge (Callstate (Internal f) om os r m)
         E0 (State f f om os rid roff rval m).

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b fd m0 m1 m2 m3 m4 m5 m6 m_iomem s_iomem reg rid roff rval,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m0 ->
    Genv.find_symbol ge p.(prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some fd -> 
    Mem.alloc m0 0 sizeof_master_iomem_space = (m1, m_iomem) ->
    Mem.alloc m1 sizeof_master_iomem_space sizeof_slave_iomem_space = (m2, s_iomem) ->
    Mem.alloc m2 (sizeof_master_iomem_space + sizeof_slave_iomem_space) sizeof_regaccess_data = (m3, reg) ->
    Mem.storebytes m3 m_iomem 0 (Memdata.inj_bytes master_iomem_space_data) = Some m4 ->
    Mem.storebytes m4 s_iomem 0 (Memdata.inj_bytes slave_iomem_space_data) = Some m5 ->
    Mem.storebytes m5 reg 0 (Memdata.inj_bytes regaccess_data) = Some m6 ->
    Mem.load Mint8unsigned (fst (Mem.alloc m6 0
        match viola_memwords with
        | 0 => 0
        | Z.pos y' => Z.pos y'~0~0
        | Z.neg y' => Z.neg y'~0~0
        end)) reg (Int.unsigned Int.zero) = Some (Vint rid) ->
    Mem.load Mint8unsigned (fst (Mem.alloc m6 0
        match viola_memwords with
        | 0 => 0
        | Z.pos y' => Z.pos y'~0~0
        | Z.neg y' => Z.neg y'~0~0
        end)) reg (Int.unsigned (Int.repr 1)) = Some (Vint roff) ->
    Mem.load Mint8unsigned (fst (Mem.alloc m6 0
        match viola_memwords with
        | 0 => 0
        | Z.pos y' => Z.pos y'~0~0
        | Z.neg y' => Z.neg y'~0~0
        end)) reg (Int.unsigned (Int.repr 2)) = Some (Vint rval) ->

    Mem.free m6 reg 0
        match viola_memwords with
        | 0 => 0
        | Z.pos y' => Z.pos y'~0~0
        | Z.neg y' => Z.neg y'~0~0
        end = Some m6 ->

    Mem.alloc m6 0
        match viola_memwords with
        | 0 => 0
        | Z.pos y' => Z.pos y'~0~0
        | Z.neg y' => Z.neg y'~0~0
        end = (m6, reg) ->
    initial_state p (Callstate fd m_iomem s_iomem reg m6).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall a,
      final_state (Returnstate a) (action_enc a).

End SEMANTICS.
