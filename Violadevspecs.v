(*
 * Viola Device Specifications
 * File: Violadevspecs.v
 *
 * Copyright (c) 2017 University of California, Irvine, CA, USA
 * All rights reserved.
 *
 * Authors: Saeed Mirzamohammadi <saeed@uci.edu>
 *	    Ardalan Amiri Sani   <arrdalan@gmail.com>
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

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import Violaconf.
Require Import Violaspec.
Import ListNotations.

Inductive bin_digit : Type :=
  | bO : bin_digit
  | bI : bin_digit.

Fixpoint _rvmask (digits : list bin_digit) : positive :=
  match digits with
  | nil => xH
  | hd :: tl => match hd with
                | bO => xO (_rvmask tl)
                | bI => xI (_rvmask tl)
                end
  end.

Fixpoint rvmask (digits : list bin_digit) : Z := 
  match digits with
  | nil => 0%Z
  | hd :: tl => match hd with
                | bO => rvmask tl
                | bI => Zpos (_rvmask (rev tl))
                end
  end.

(** output ports **)
Definition AMICBCTL := mkreg 10%Z 0%Z.
Definition DMICBCTL := mkreg 11%Z 0%Z.
Definition MICLCTL := mkreg 12%Z 0%Z.
Definition MICRCTL := mkreg 13%Z 0%Z.

(*** reg vars ***)

Definition headset_mic_bias := mkregvar AMICBCTL 0%Z (rvmask [bO;bO;bO;bO;bO;bO;bO;bI]). (* 0b00000001 *)
Definition main_mic_bias := mkregvar AMICBCTL 4%Z (rvmask [bO;bO;bO;bI;bO;bO;bO;bO]). (* 0b00010000 *)
Definition digital_mic1_bias := mkregvar DMICBCTL 0%Z (rvmask [bO;bO;bO;bO;bO;bO;bO;bI]). (* 0b00000001 *)
Definition digital_mic2_bias := mkregvar DMICBCTL 4%Z (rvmask [bO;bO;bO;bI;bO;bO;bO;bO]). (* 0b00010000 *)
Definition left_adc := mkregvar MICLCTL 2%Z (rvmask [bO;bO;bO;bO;bO;bI;bO;bO]). (* 0b00000100 *)
Definition right_adc := mkregvar MICRCTL 2%Z (rvmask [bO;bO;bO;bO;bO;bI;bO;bO]). (* 0b00000100 *)

(*** sstates ***)
Definition ss_headset_mic_bias_on := mksstate headset_mic_bias 1%Z.
Definition ss_headset_mic_bias_off := mksstate headset_mic_bias 0%Z.
Definition ss_main_mic_bias_on := mksstate main_mic_bias 1%Z.
Definition ss_main_mic_bias_off := mksstate main_mic_bias 0%Z.
Definition ss_digital_mic1_bias_on := mksstate digital_mic1_bias 1%Z.
Definition ss_digital_mic1_bias_off := mksstate digital_mic1_bias 0%Z.
Definition ss_digital_mic2_bias_on := mksstate digital_mic2_bias 1%Z.
Definition ss_digital_mic2_bias_off := mksstate digital_mic2_bias 0%Z.
Definition ss_left_adc_on := mksstate left_adc 1%Z.
Definition ss_left_adc_off := mksstate left_adc 0%Z.
Definition ss_right_adc_on := mksstate right_adc 1%Z.
Definition ss_right_adc_off := mksstate right_adc 0%Z.

(*** events ***)

Definition ev_headset_mic_bias_1 := mkvevent ev_eq headset_mic_bias 1%Z.
Definition ev_headset_mic_bias_0 := mkvevent ev_eq headset_mic_bias 0%Z.
Definition ev_main_mic_bias_1 := mkvevent ev_eq main_mic_bias 1%Z.
Definition ev_main_mic_bias_0 := mkvevent ev_eq main_mic_bias 0%Z.
Definition ev_digital_mic1_bias_1 := mkvevent ev_eq digital_mic1_bias 1%Z.
Definition ev_digital_mic1_bias_0 := mkvevent ev_eq digital_mic1_bias 0%Z.
Definition ev_digital_mic2_bias_1 := mkvevent ev_eq digital_mic2_bias 1%Z.
Definition ev_digital_mic2_bias_0 := mkvevent ev_eq digital_mic2_bias 0%Z.
Definition ev_left_adc_1 := mkvevent ev_eq left_adc 1%Z.
Definition ev_left_adc_0 := mkvevent ev_eq left_adc 0%Z.
Definition ev_right_adc_1 := mkvevent ev_eq right_adc 1%Z.
Definition ev_right_adc_0 := mkvevent ev_eq right_adc 0%Z.

(*** transitions ***)

Definition tran_headset_mic_bias_1 := mkstrans (mksrcsstate 0%Z ss_headset_mic_bias_off) ev_headset_mic_bias_1 ss_headset_mic_bias_on.
Definition tran_headset_mic_bias_0 := mkstrans (mksrcsstate 0%Z ss_headset_mic_bias_on) ev_headset_mic_bias_0 ss_headset_mic_bias_off.
Definition tran_main_mic_bias_1 := mkstrans (mksrcsstate 0%Z ss_main_mic_bias_off) ev_main_mic_bias_1 ss_main_mic_bias_on.
Definition tran_main_mic_bias_0 := mkstrans (mksrcsstate 0%Z ss_main_mic_bias_on) ev_main_mic_bias_0 ss_main_mic_bias_off.
Definition tran_digital_mic1_bias_1 := mkstrans (mksrcsstate 0%Z ss_digital_mic1_bias_off) ev_digital_mic1_bias_1 ss_digital_mic1_bias_on.
Definition tran_digital_mic1_bias_0 := mkstrans (mksrcsstate 0%Z ss_digital_mic1_bias_on) ev_digital_mic1_bias_0 ss_digital_mic1_bias_off.
Definition tran_digital_mic2_bias_1 := mkstrans (mksrcsstate 0%Z ss_digital_mic2_bias_off) ev_digital_mic2_bias_1 ss_digital_mic2_bias_on.
Definition tran_digital_mic2_bias_0 := mkstrans (mksrcsstate 0%Z ss_digital_mic2_bias_on) ev_digital_mic2_bias_0 ss_digital_mic2_bias_off.
Definition tran_left_adc_1 := mkstrans (mksrcsstate 0%Z ss_left_adc_off) ev_left_adc_1 ss_left_adc_on.
Definition tran_left_adc_0 := mkstrans (mksrcsstate 0%Z ss_left_adc_on) ev_left_adc_0 ss_left_adc_off.
Definition tran_right_adc_1 := mkstrans (mksrcsstate 0%Z ss_right_adc_off) ev_right_adc_1 ss_right_adc_on.
Definition tran_right_adc_0 := mkstrans (mksrcsstate 0%Z ss_right_adc_on) ev_right_adc_0 ss_right_adc_off.

Definition twl6040_regs := [AMICBCTL; DMICBCTL; MICLCTL; MICRCTL].

Definition twl6040_regvars := [headset_mic_bias; main_mic_bias; digital_mic1_bias; digital_mic2_bias; left_adc; right_adc].

Definition twl6040_trans := [tran_headset_mic_bias_1; tran_headset_mic_bias_0; tran_main_mic_bias_1; tran_main_mic_bias_0;
                             tran_digital_mic1_bias_1; tran_digital_mic1_bias_0; tran_digital_mic2_bias_1; tran_digital_mic2_bias_0;
                             tran_left_adc_1; tran_left_adc_0; tran_right_adc_1; tran_right_adc_0].

Definition twl6040_spec := mkdevspec 75%Z twl6040_regs twl6040_regvars [] [] twl6040_trans. (* I2C ID: 0x4b *)

Definition mic_master1 := mkinvdstate [ss_headset_mic_bias_on].
Definition mic_master2 := mkinvdstate [ss_main_mic_bias_on].
Definition mic_master3 := mkinvdstate [ss_digital_mic1_bias_on].
Definition mic_master4 := mkinvdstate [ss_digital_mic2_bias_on].
Definition mic_master5 := mkinvdstate [ss_left_adc_on].
Definition mic_master6 := mkinvdstate [ss_right_adc_on].

(************** AN30259A LED on Galaxy Nexus ******************)

(*** registers ***)

Definition r_sreset   := mkreg 0%Z 0%Z.
Definition r_ledon    := mkreg 1%Z 0%Z.
Definition r_sel      := mkreg 2%Z 64%Z. (* init/default val = 40h *)
Definition r_led1cc   := mkreg 3%Z 0%Z.
Definition r_led2cc   := mkreg 4%Z 0%Z.
Definition r_led3cc   := mkreg 5%Z 0%Z.
Definition r_led1slp  := mkreg 6%Z 136%Z. (* init/default val = 88h *)
Definition r_led1cnt1 := mkreg 9%Z 248%Z. (* init/default val = f8h *)
Definition r_led1cnt2 := mkreg 10%Z 0%Z.
Definition r_led1cnt3 := mkreg 11%Z 136%Z. (* init/default val = 88h *)
Definition r_led1cnt4 := mkreg 12%Z 136%Z. (* init/default val = 88h *)

(*** regvars ***)

Definition rv_sreset   := mkregvar r_sreset   0%Z (rvmask [bO;bO;bO;bO;bO;bO;bO;bI]). (* 0b00000001 *)
Definition rv_sel      := mkregvar r_sel      0%Z (rvmask [bI;bI;bI;bI;bI;bI;bI;bI]). (* 0b11111111 *)

Definition rv_led1on := mkregvar r_ledon 0%Z (rvmask [bO;bO;bO;bO;bO;bO;bO;bI]). (* 0b00000001 *)
Definition rv_led1md := mkregvar r_ledon 4%Z (rvmask [bO;bO;bO;bI;bO;bO;bO;bO]). (* 0b00010000 *)
Definition rv_led1cc   := mkregvar r_led1cc   0%Z (rvmask [bI;bI;bI;bI;bI;bI;bI;bI]). (* 0b11111111 *)

Definition rv_led2on := mkregvar r_ledon 1%Z (rvmask [bO;bO;bO;bO;bO;bO;bI;bO]). (* 0b00000010 *)

Definition rv_led3on := mkregvar r_ledon 2%Z (rvmask [bO;bO;bO;bO;bO;bI;bO;bO]). (* 0b00000100 *)

Definition rv_led1slp  := mkregvar r_led1slp  0%Z (rvmask [bI;bI;bI;bI;bI;bI;bI;bI]). (* 0b11111111 *)
Definition rv_led1cnt1 := mkregvar r_led1cnt1 0%Z (rvmask [bI;bI;bI;bI;bI;bI;bI;bI]). (* 0b11111111 *)
Definition rv_led1cnt2 := mkregvar r_led1cnt2 0%Z (rvmask [bI;bI;bI;bI;bI;bI;bI;bI]). (* 0b11111111 *)
Definition rv_led1cnt3 := mkregvar r_led1cnt3 0%Z (rvmask [bI;bI;bI;bI;bI;bI;bI;bI]). (* 0b11111111 *)
Definition rv_led1cnt4 := mkregvar r_led1cnt4 0%Z (rvmask [bI;bI;bI;bI;bI;bI;bI;bI]). (* 0b11111111 *)

(*** sstates ***)

Definition ss_sel_t := mksstate rv_sel 192%Z. (* 0xc0 *)
Definition ss_sel_nt := mksstate rv_sel 64%Z.

Definition ss_led1_on := mksstate rv_led1on 1%Z.
Definition ss_led1_off := mksstate rv_led1on 0%Z.
Definition ss_led1_slope := mksstate rv_led1md 1%Z.
Definition ss_led1_const := mksstate rv_led1md 0%Z.
Definition ss_led1_cc_t := mksstate rv_led1cc 255%Z.
Definition ss_led1_cc_nt := mksstate rv_led1cc 0%Z.

Definition ss_led2_on := mksstate rv_led2on 1%Z.
Definition ss_led2_off := mksstate rv_led2on 0%Z.

Definition ss_led3_on := mksstate rv_led3on 1%Z.
Definition ss_led3_off := mksstate rv_led3on 0%Z.

Definition ss_led1slp_t := mksstate rv_led1slp 17%Z. (* 0x11 *)
Definition ss_led1slp_nt := mksstate rv_led1slp 0%Z. (* default: 0x88 *)
Definition ss_led1cnt1_t := mksstate rv_led1cnt1 243%Z. (* 0xf3 *)
Definition ss_led1cnt1_nt := mksstate rv_led1cnt1 248%Z. (* default: 0xf8 *)
Definition ss_led1cnt2_t := mksstate rv_led1cnt2 0%Z. (* 0x0 *)
Definition ss_led1cnt2_nt := mksstate rv_led1cnt2 1%Z.
Definition ss_led1cnt3_t := mksstate rv_led1cnt3 0%Z. (* 0x0 *)
Definition ss_led1cnt3_nt := mksstate rv_led1cnt3 136%Z. (* default: 0x88 *)
Definition ss_led1cnt4_t := mksstate rv_led1cnt4 0%Z. (* 0x0 *)
Definition ss_led1cnt4_nt := mksstate rv_led1cnt4 136%Z. (* default: 0x88 *)

(*** events ***)

Definition ev_reset := mkvevent ev_eq rv_sreset 1%Z.

Definition ev_sel_t := mkvevent ev_eq rv_sel 12%Z.
Definition ev_sel_nt := mkvevent ev_ne rv_sel 12%Z.

Definition ev_led1_on := mkvevent ev_eq rv_led1on 1%Z.
Definition ev_led1_off := mkvevent ev_eq rv_led1on 0%Z.
Definition ev_led1_slope := mkvevent ev_eq rv_led1md 1%Z.
Definition ev_led1_const := mkvevent ev_eq rv_led1md 0%Z.
Definition ev_led1_cc_t := mkvevent ev_eq rv_led1cc 255%Z.
Definition ev_led1_cc_nt := mkvevent ev_ne rv_led1cc 255%Z.

Definition ev_led2_on := mkvevent ev_eq rv_led2on 1%Z.
Definition ev_led2_off := mkvevent ev_eq rv_led2on 0%Z.

Definition ev_led3_on := mkvevent ev_eq rv_led3on 1%Z.
Definition ev_led3_off := mkvevent ev_eq rv_led3on 0%Z.

Definition ev_led1slp_t := mkvevent ev_eq rv_led1slp 17%Z.
Definition ev_led1slp_nt := mkvevent ev_ne rv_led1slp 17%Z.
Definition ev_led1cnt1_t := mkvevent ev_eq rv_led1cnt1 243%Z.
Definition ev_led1cnt1_nt := mkvevent ev_ne rv_led1cnt1 243%Z.
Definition ev_led1cnt2_t := mkvevent ev_eq rv_led1cnt2 0%Z.
Definition ev_led1cnt2_nt := mkvevent ev_ne rv_led1cnt2 0%Z.
Definition ev_led1cnt3_t := mkvevent ev_eq rv_led1cnt3 0%Z.
Definition ev_led1cnt3_nt := mkvevent ev_ne rv_led1cnt3 0%Z.
Definition ev_led1cnt4_t := mkvevent ev_eq rv_led1cnt4 0%Z.
Definition ev_led1cnt4_nt := mkvevent ev_ne rv_led1cnt4 0%Z.

(*** transitions ***)

Definition any_srcss := mksrcsstate 1%Z (mksstate rv_sel 0%Z).

Definition tran_sel_t := mkstrans any_srcss ev_sel_t ss_sel_t.
Definition tran_sel_nt := mkstrans (mksrcsstate 0%Z ss_sel_t) ev_sel_nt ss_sel_nt.

Definition tran_led1_on := mkstrans (mksrcsstate 0%Z ss_led1_off) ev_led1_on ss_led1_on.
Definition tran_led1_off := mkstrans (mksrcsstate 0%Z ss_led1_on) ev_led1_off ss_led1_off. 
Definition tran_led1_slope := mkstrans (mksrcsstate 0%Z ss_led1_const) ev_led1_slope ss_led1_slope.
Definition tran_led1_const := mkstrans (mksrcsstate 0%Z ss_led1_slope) ev_led1_const ss_led1_const.
Definition tran_led1_cc_t := mkstrans any_srcss ev_led1_cc_t ss_led1_cc_t.
Definition tran_led1_cc_nt := mkstrans (mksrcsstate 0%Z ss_led1_cc_t) ev_led1_cc_nt ss_led1_cc_nt.

Definition tran_led2_on := mkstrans (mksrcsstate 0%Z ss_led2_off) ev_led2_on ss_led2_on.
Definition tran_led2_off := mkstrans (mksrcsstate 0%Z ss_led2_on) ev_led2_off ss_led2_off.

Definition tran_led3_on := mkstrans (mksrcsstate 0%Z ss_led3_off) ev_led3_on ss_led3_on.
Definition tran_led3_off := mkstrans (mksrcsstate 0%Z ss_led3_on) ev_led3_off ss_led3_off. 

Definition tran_led1slp_t := mkstrans any_srcss ev_led1slp_t ss_led1slp_t.
Definition tran_led1slp_nt := mkstrans (mksrcsstate 0%Z ss_led1slp_t) ev_led1slp_nt ss_led1slp_nt.
Definition tran_led1cnt1_t := mkstrans any_srcss ev_led1cnt1_t ss_led1cnt1_t.
Definition tran_led1cnt1_nt := mkstrans (mksrcsstate 0%Z ss_led1cnt1_t) ev_led1cnt1_nt ss_led1cnt1_nt.
Definition tran_led1cnt2_t := mkstrans any_srcss ev_led1cnt2_t ss_led1cnt2_t.
Definition tran_led1cnt2_nt := mkstrans (mksrcsstate 0%Z ss_led1cnt2_t) ev_led1cnt2_nt ss_led1cnt2_nt.
Definition tran_led1cnt3_t := mkstrans any_srcss ev_led1cnt3_t ss_led1cnt3_t.
Definition tran_led1cnt3_nt := mkstrans (mksrcsstate 0%Z ss_led1cnt3_t) ev_led1cnt3_nt ss_led1cnt3_nt.
Definition tran_led1cnt4_t := mkstrans any_srcss ev_led1cnt4_t ss_led1cnt4_t.
Definition tran_led1cnt4_nt := mkstrans (mksrcsstate 0%Z ss_led1cnt4_t) ev_led1cnt4_nt ss_led1cnt4_nt.

Definition tran_reset_sel := mkstrans any_srcss ev_reset ss_sel_nt.

Definition tran_reset_led1on := mkstrans any_srcss ev_reset ss_led1_off.
Definition tran_reset_led1md := mkstrans any_srcss ev_reset ss_led1_const.
Definition tran_reset_led1cc := mkstrans any_srcss ev_reset ss_led1_cc_nt.

Definition tran_reset_led2on := mkstrans any_srcss ev_reset ss_led2_off.

Definition tran_reset_led3on := mkstrans any_srcss ev_reset ss_led3_off.

Definition tran_reset_led1slp_t := mkstrans any_srcss ev_reset ss_led1slp_nt.
Definition tran_reset_led1cnt1_t := mkstrans any_srcss ev_reset ss_led1cnt1_nt.
Definition tran_reset_led1cnt2_t := mkstrans any_srcss ev_reset ss_led1cnt2_t. (* this is not an error, its default val is the target val *)
Definition tran_reset_led1cnt3_t := mkstrans any_srcss ev_reset ss_led1cnt3_nt.
Definition tran_reset_led1cnt4_t := mkstrans any_srcss ev_reset ss_led1cnt4_nt.

(*** lists ***)

Definition an_regs := [r_sreset; r_ledon; r_sel; r_led1cc; r_led1slp; r_led1cnt1; r_led1cnt2; r_led1cnt3; r_led1cnt4].

Definition an_regvars := [rv_sreset; rv_sel; rv_led1on; rv_led1md; rv_led1cc; rv_led2on; rv_led3on; rv_led1slp; rv_led1cnt1; rv_led1cnt2; rv_led1cnt3; rv_led1cnt4].

Definition an_trans := [tran_sel_t; tran_sel_nt; tran_led1_on; tran_led1_off; tran_led1_slope; tran_led1_const; tran_led1_cc_t; tran_led1_cc_nt; tran_led2_on; tran_led2_off; tran_led3_on; tran_led3_off; tran_led1slp_t; tran_led1slp_nt; tran_led1cnt1_t; tran_led1cnt1_nt; tran_led1cnt2_t; tran_led1cnt2_nt; tran_led1cnt3_t; tran_led1cnt3_nt; tran_led1cnt4_t; tran_led1cnt4_nt; tran_reset_sel; tran_reset_led1on; tran_reset_led1md; tran_reset_led1cc; tran_reset_led2on; tran_reset_led3on; tran_reset_led1slp_t; tran_reset_led1cnt1_t; tran_reset_led1cnt2_t; tran_reset_led1cnt3_t; tran_reset_led1cnt4_t].

Definition an_spec := mkdevspec 48%Z an_regs an_regvars [] [] an_trans. (* ID = 0x30 *)

Definition an_target_state_red := mkinvdstate [ss_led1_on; ss_led1_slope; ss_sel_t; ss_led1_cc_t; ss_led2_off; ss_led3_off; ss_led1slp_t; ss_led1cnt1_t; ss_led1cnt2_t; ss_led1cnt3_t; ss_led1cnt4_t].

(************** Nexus 5 MSM camera ******************)

(*** regs ****)

Definition MSM_CPP_MICRO_CLKEN_CTL := mkreg 48%Z 0%Z.

(*** reg vars ***)

Definition rv_cpp_clk_en := mkregvar MSM_CPP_MICRO_CLKEN_CTL 0%Z (rvmask [bI;bI;bI;bI;bI;bI;bI;bI]). (* 0b11111111 *)

(*** sstates ***)
Definition ss_cpp_clk_on := mksstate rv_cpp_clk_en 1%Z.
Definition ss_cpp_clk_off := mksstate rv_cpp_clk_en 0%Z.

(*** events ***)

Definition ev_cpp_clk_enable := mkvevent ev_eq rv_cpp_clk_en 1%Z.
Definition ev_cpp_clk_disable := mkvevent ev_eq rv_cpp_clk_en 0%Z.

(*** transitions ***)

Definition tran_cpp_clk_enable := mkstrans (mksrcsstate 0%Z ss_cpp_clk_off) ev_cpp_clk_enable ss_cpp_clk_on.
Definition tran_cpp_clk_disable := mkstrans (mksrcsstate 0%Z ss_cpp_clk_on) ev_cpp_clk_disable ss_cpp_clk_off.

Definition msm_cam_regs := [MSM_CPP_MICRO_CLKEN_CTL].

Definition msm_cam_regvars := [rv_cpp_clk_en].

Definition msm_cam_trans := [tran_cpp_clk_enable; tran_cpp_clk_disable].

Definition msm_cam_spec := mkdevspec 4%Z msm_cam_regs msm_cam_regvars [] [] msm_cam_trans.

Definition msm_cam_on := mkinvdstate [ss_cpp_clk_on].

(************** Nexus 5 MSM 8974 vibrator ******************)

(*** regs ****)

Definition reg_1 := mkreg 84%Z 0%Z.
Definition reg_2 := mkreg 85%Z 0%Z.
Definition reg_3 := mkreg 88%Z 0%Z.
Definition reg_4 := mkreg 92%Z 0%Z.
Definition reg_5 := mkreg 96%Z 0%Z.
Definition reg_6 := mkreg 80%Z 0%Z.
Definition reg_7 := mkreg 116%Z 0%Z.

(*** reg vars ***)

Definition rv_1 := mkregvar reg_1 0%Z (rvmask [bI;bI;bI;bI;bI;bI;bI;bI]). (* 0b11111111 *)
Definition rv_2 := mkregvar reg_2 0%Z (rvmask [bI;bI;bI;bI;bI;bI;bI;bI]). (* 0b11111111 *)
Definition rv_3 := mkregvar reg_3 0%Z (rvmask [bI;bI;bI;bI;bI;bI;bI;bI]). (* 0b11111111 *)
Definition rv_4 := mkregvar reg_4 0%Z (rvmask [bI;bI;bI;bI;bI;bI;bI;bI]). (* 0b11111111 *)
Definition rv_5 := mkregvar reg_5 0%Z (rvmask [bI;bI;bI;bI;bI;bI;bI;bI]). (* 0b11111111 *)
Definition rv_6 := mkregvar reg_6 0%Z (rvmask [bI;bI;bI;bI;bI;bI;bI;bI]). (* 0b11111111 *)
Definition rv_7 := mkregvar reg_7 0%Z (rvmask [bI;bI;bI;bI;bI;bI;bI;bI]). (* 0b11111111 *)

(*** sstates ***)
Definition ss_rv_1_target := mksstate rv_1 7%Z. (* 0x07 *)
Definition ss_rv_1_notarget := mksstate rv_1 0%Z.
Definition ss_rv_2_target := mksstate rv_2 32%Z. (* 0x20 *)
Definition ss_rv_2_notarget := mksstate rv_2 0%Z.
Definition ss_rv_3_target := mksstate rv_3 1%Z. (* 0x1 *)
Definition ss_rv_3_notarget := mksstate rv_3 0%Z.
Definition ss_rv_4_target := mksstate rv_4 129%Z. (* 0x81 *)
Definition ss_rv_4_notarget := mksstate rv_4 0%Z.
Definition ss_rv_5_target := mksstate rv_5 49%Z. (* 0x31 *)
Definition ss_rv_5_notarget := mksstate rv_5 0%Z.
Definition ss_rv_6_target := mksstate rv_6 1%Z. (* 0x1 *)
Definition ss_rv_6_notarget := mksstate rv_6 0%Z.
Definition ss_rv_7_target := mksstate rv_7 1%Z. (* 0x1 *)
Definition ss_rv_7_notarget := mksstate rv_7 0%Z.

(*** events ***)

Definition ev_rv_1_target := mkvevent ev_eq rv_1 7%Z.
Definition ev_rv_1_notarget := mkvevent ev_ne rv_1 7%Z.
Definition ev_rv_2_target := mkvevent ev_eq rv_2 32%Z.
Definition ev_rv_2_notarget := mkvevent ev_ne rv_2 32%Z.
Definition ev_rv_3_target := mkvevent ev_eq rv_3 1%Z.
Definition ev_rv_3_notarget := mkvevent ev_ne rv_3 1%Z.
Definition ev_rv_4_target := mkvevent ev_eq rv_4 129%Z.
Definition ev_rv_4_notarget := mkvevent ev_ne rv_4 129%Z.
Definition ev_rv_5_target := mkvevent ev_eq rv_5 49%Z.
Definition ev_rv_5_notarget := mkvevent ev_ne rv_5 49%Z.
Definition ev_rv_6_target := mkvevent ev_eq rv_6 1%Z.
Definition ev_rv_6_notarget := mkvevent ev_ne rv_6 1%Z.
Definition ev_rv_7_target := mkvevent ev_eq rv_7 1%Z.
Definition ev_rv_7_notarget := mkvevent ev_ne rv_7 1%Z.

(*** transitions ***)

Definition tran_rv_1_target := mkstrans any_srcss ev_rv_1_target ss_rv_1_target.
Definition tran_rv_1_notarget := mkstrans (mksrcsstate 0%Z ss_rv_1_target) ev_rv_1_notarget ss_rv_1_notarget.
Definition tran_rv_2_target := mkstrans any_srcss ev_rv_2_target ss_rv_2_target.
Definition tran_rv_2_notarget := mkstrans (mksrcsstate 0%Z ss_rv_2_target) ev_rv_2_notarget ss_rv_2_notarget.
Definition tran_rv_3_target := mkstrans any_srcss ev_rv_3_target ss_rv_3_target.
Definition tran_rv_3_notarget := mkstrans (mksrcsstate 0%Z ss_rv_3_target) ev_rv_3_notarget ss_rv_3_notarget.
Definition tran_rv_4_target := mkstrans any_srcss ev_rv_4_target ss_rv_4_target.
Definition tran_rv_4_notarget := mkstrans (mksrcsstate 0%Z ss_rv_4_target) ev_rv_4_notarget ss_rv_4_notarget.
Definition tran_rv_5_target := mkstrans any_srcss ev_rv_5_target ss_rv_5_target.
Definition tran_rv_5_notarget := mkstrans (mksrcsstate 0%Z ss_rv_5_target) ev_rv_5_notarget ss_rv_5_notarget.
Definition tran_rv_6_target := mkstrans any_srcss ev_rv_6_target ss_rv_6_target.
Definition tran_rv_6_notarget := mkstrans (mksrcsstate 0%Z ss_rv_6_target) ev_rv_6_notarget ss_rv_6_notarget.
Definition tran_rv_7_target := mkstrans any_srcss ev_rv_7_target ss_rv_7_target.
Definition tran_rv_7_notarget := mkstrans (mksrcsstate 0%Z ss_rv_7_target) ev_rv_7_notarget ss_rv_7_notarget.

Definition msm_vib_regs := [reg_1; reg_2; reg_3; reg_4; reg_5; reg_6; reg_7].

Definition msm_vib_regvars := [rv_1; rv_2; rv_3; rv_4; rv_5; rv_6; rv_7].

Definition msm_vib_trans := [tran_rv_1_target; tran_rv_1_notarget;
                             tran_rv_2_target; tran_rv_2_notarget;
                             tran_rv_3_target; tran_rv_3_notarget;
                             tran_rv_4_target; tran_rv_4_notarget;
                             tran_rv_5_target; tran_rv_5_notarget;
                             tran_rv_6_target; tran_rv_6_notarget;
                             tran_rv_7_target; tran_rv_7_notarget].

Definition msm_vib_spec := mkdevspec 5%Z msm_vib_regs msm_vib_regvars [] [] msm_vib_trans.

Definition msm_vib_on := mkinvdstate [ss_rv_1_target; ss_rv_2_target; ss_rv_3_target; ss_rv_4_target;
                                      ss_rv_5_target; ss_rv_6_target; ss_rv_7_target].

(************** Nexus 5 MSM 8974 vibrator IC ******************)

(*** regs ****)

Definition ic_reg_1 := mkreg 193%Z 0%Z. (* 0x3c1 -> 0xc1 *)
Definition ic_reg_2 := mkreg 196%Z 0%Z. (* 0x3c4 -> 0xc4 *)

(*** reg vars ***)

Definition ic_rv_1 := mkregvar ic_reg_1 1%Z (rvmask [bO;bO;bO;bO;bO;bO;bI;bO]). (* 0b00000010 *)
Definition ic_rv_2 := mkregvar ic_reg_2 0%Z (rvmask [bI;bI;bI;bI;bI;bI;bI;bI]). (* 0b11111111 *)

(*** sstates ***)
Definition ic_ss_rv_1_target := mksstate ic_rv_1 1%Z.
Definition ic_ss_rv_1_notarget := mksstate ic_rv_1 0%Z.
Definition ic_ss_rv_2_target := mksstate ic_rv_2 2%Z. (* 0x20 *)
Definition ic_ss_rv_2_notarget := mksstate ic_rv_2 0%Z.

(*** events ***)

Definition ic_ev_rv_1_target := mkvevent ev_eq ic_rv_1 1%Z.
Definition ic_ev_rv_1_notarget := mkvevent ev_ne ic_rv_1 1%Z.
Definition ic_ev_rv_2_target := mkvevent ev_eq ic_rv_2 2%Z.
Definition ic_ev_rv_2_notarget := mkvevent ev_ne ic_rv_2 2%Z.

(*** transitions ***)

Definition ic_tran_rv_1_target := mkstrans any_srcss ic_ev_rv_1_target ic_ss_rv_1_target.
Definition ic_tran_rv_1_notarget := mkstrans (mksrcsstate 0%Z ic_ss_rv_1_target) ic_ev_rv_1_notarget ic_ss_rv_1_notarget.
Definition ic_tran_rv_2_target := mkstrans any_srcss ic_ev_rv_2_target ic_ss_rv_2_target.
Definition ic_tran_rv_2_notarget := mkstrans (mksrcsstate 0%Z ic_ss_rv_2_target) ic_ev_rv_2_notarget ic_ss_rv_2_notarget.

Definition msm_ic_vib_regs := [ic_reg_1; ic_reg_2].

Definition msm_ic_vib_regvars := [ic_rv_1; ic_rv_2].

Definition msm_ic_vib_trans := [ic_tran_rv_1_target; ic_tran_rv_1_notarget;
                             ic_tran_rv_2_target; ic_tran_rv_2_notarget].

Definition msm_ic_vib_spec := mkdevspec 6%Z msm_ic_vib_regs msm_ic_vib_regvars [] [] msm_ic_vib_trans.

Definition msm_ic_vib_on := mkinvdstate [ic_ss_rv_1_target; ic_ss_rv_2_target].

(************** Nexus 5 MSM 8974 vibrator clock domain ******************)

(*** regs ****)

Definition clk_reg_1 := mkreg 88%Z 0%Z. (* 0x458 -> 0x58 *)
Definition clk_reg_2 := mkreg 92%Z 0%Z. (* 0x45c -> 0x5c *)
Definition clk_reg_3 := mkreg 96%Z 0%Z. (* 0x460 -> 0x60 *)
Definition clk_reg_4 := mkreg 84%Z 0%Z. (* 0x454 -> 0x54 *)
Definition clk_reg_5 := mkreg 85%Z 0%Z. (* 0x455 -> 0x55 *)

(*** reg vars ***)

Definition clk_rv_1 := mkregvar clk_reg_1 0%Z (rvmask [bI;bI;bI;bI;bI;bI;bI;bI]). (* 0b11111111 *)
Definition clk_rv_2 := mkregvar clk_reg_2 0%Z (rvmask [bI;bI;bI;bI;bI;bI;bI;bI]). (* 0b11111111 *)
Definition clk_rv_3 := mkregvar clk_reg_3 0%Z (rvmask [bI;bI;bI;bI;bI;bI;bI;bI]). (* 0b11111111 *)
Definition clk_rv_4 := mkregvar clk_reg_4 0%Z (rvmask [bI;bI;bI;bI;bI;bI;bI;bI]). (* 0b11111111 *)
Definition clk_rv_5 := mkregvar clk_reg_5 0%Z (rvmask [bI;bI;bI;bI;bI;bI;bI;bI]). (* 0b11111111 *)

(*** sstates ***)
Definition clk_ss_rv_1_target := mksstate clk_rv_1 1%Z. (* 0x01 *)
Definition clk_ss_rv_1_notarget := mksstate clk_rv_1 0%Z.
Definition clk_ss_rv_2_target := mksstate clk_rv_2 215%Z. (* 0xd7 *)
Definition clk_ss_rv_2_notarget := mksstate clk_rv_2 0%Z.
Definition clk_ss_rv_3_target := mksstate clk_rv_3 214%Z. (* 0xd6 *)
Definition clk_ss_rv_3_notarget := mksstate clk_rv_3 0%Z.
Definition clk_ss_rv_4_target := mksstate clk_rv_4 31%Z. (* 0x1f *)
Definition clk_ss_rv_4_notarget := mksstate clk_rv_4 0%Z.
Definition clk_ss_rv_5_target := mksstate clk_rv_5 32%Z. (* 0x20 *)
Definition clk_ss_rv_5_notarget := mksstate clk_rv_5 0%Z.

(*** events ***)

Definition clk_ev_rv_1_target := mkvevent ev_eq clk_rv_1 1%Z.
Definition clk_ev_rv_1_notarget := mkvevent ev_ne clk_rv_1 1%Z.
Definition clk_ev_rv_2_target := mkvevent ev_eq clk_rv_2 215%Z.
Definition clk_ev_rv_2_notarget := mkvevent ev_ne clk_rv_2 215%Z.
Definition clk_ev_rv_3_target := mkvevent ev_eq clk_rv_3 214%Z.
Definition clk_ev_rv_3_notarget := mkvevent ev_ne clk_rv_3 214%Z.
Definition clk_ev_rv_4_target := mkvevent ev_eq clk_rv_4 31%Z.
Definition clk_ev_rv_4_notarget := mkvevent ev_ne clk_rv_4 31%Z.
Definition clk_ev_rv_5_target := mkvevent ev_eq clk_rv_5 32%Z.
Definition clk_ev_rv_5_notarget := mkvevent ev_ne clk_rv_5 32%Z.

(*** transitions ***)

Definition clk_tran_rv_1_target := mkstrans any_srcss clk_ev_rv_1_target clk_ss_rv_1_target.
Definition clk_tran_rv_1_notarget := mkstrans (mksrcsstate 0%Z clk_ss_rv_1_target) clk_ev_rv_1_notarget clk_ss_rv_1_notarget.
Definition clk_tran_rv_2_target := mkstrans any_srcss clk_ev_rv_2_target clk_ss_rv_2_target.
Definition clk_tran_rv_2_notarget := mkstrans (mksrcsstate 0%Z clk_ss_rv_2_target) clk_ev_rv_2_notarget clk_ss_rv_2_notarget.
Definition clk_tran_rv_3_target := mkstrans any_srcss clk_ev_rv_3_target clk_ss_rv_3_target.
Definition clk_tran_rv_3_notarget := mkstrans (mksrcsstate 0%Z clk_ss_rv_3_target) clk_ev_rv_3_notarget clk_ss_rv_3_notarget.
Definition clk_tran_rv_4_target := mkstrans any_srcss clk_ev_rv_4_target clk_ss_rv_4_target.
Definition clk_tran_rv_4_notarget := mkstrans (mksrcsstate 0%Z clk_ss_rv_4_target) clk_ev_rv_4_notarget clk_ss_rv_4_notarget.
Definition clk_tran_rv_5_target := mkstrans any_srcss clk_ev_rv_5_target clk_ss_rv_5_target.
Definition clk_tran_rv_5_notarget := mkstrans (mksrcsstate 0%Z clk_ss_rv_5_target) clk_ev_rv_5_notarget clk_ss_rv_5_notarget.

Definition msm_clk_vib_regs := [clk_reg_1; clk_reg_2; clk_reg_3; clk_reg_4; clk_reg_5].

Definition msm_clk_vib_regvars := [clk_rv_1; clk_rv_2; clk_rv_3; clk_rv_4; clk_rv_5].

Definition msm_clk_vib_trans := [clk_tran_rv_1_target; clk_tran_rv_1_notarget;
                             clk_tran_rv_2_target; clk_tran_rv_2_notarget;
                             clk_tran_rv_3_target; clk_tran_rv_3_notarget;
                             clk_tran_rv_4_target; clk_tran_rv_4_notarget;
                             clk_tran_rv_5_target; clk_tran_rv_5_notarget].

Definition msm_clk_vib_spec := mkdevspec 7%Z msm_clk_vib_regs msm_clk_vib_regvars [] [] msm_clk_vib_trans.

Definition msm_clk_vib_on := mkinvdstate [clk_ss_rv_1_target; clk_ss_rv_2_target; clk_ss_rv_3_target; clk_ss_rv_4_target;
                                      clk_ss_rv_5_target].


(***** Galaxy Nexus mic_led invariant ******)
Definition gnexus_mic_led_invariant1 := mkinv uni_r mic_master1 an_target_state_red twl6040_spec an_spec.
Definition gnexus_mic_led_invariant2 := mkinv uni_r mic_master2 an_target_state_red twl6040_spec an_spec.
Definition gnexus_mic_led_invariant3 := mkinv uni_r mic_master3 an_target_state_red twl6040_spec an_spec.
Definition gnexus_mic_led_invariant4 := mkinv uni_r mic_master4 an_target_state_red twl6040_spec an_spec.
Definition gnexus_mic_led_invariant5 := mkinv uni_r mic_master5 an_target_state_red twl6040_spec an_spec.
Definition gnexus_mic_led_invariant6 := mkinv uni_r mic_master6 an_target_state_red twl6040_spec an_spec.

(***** Nexus 5 cam_vib invariant ******)
Definition n5_ic_clk_invariant := mkinv uni_r msm_ic_vib_on msm_clk_vib_on msm_ic_vib_spec msm_clk_vib_spec.
Definition n5_vib_ic_invariant := mkinv uni_r msm_vib_on msm_ic_vib_on msm_vib_spec msm_ic_vib_spec.
Definition n5_cam_vib_invariant := mkinv uni_r msm_cam_on msm_vib_on msm_cam_spec msm_vib_spec.
