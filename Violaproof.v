(*
 * Viola Proof
 * File: Violaproof.v
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
Require Import compcert.common.Smallstep.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import CpdtTactics.
Require Import Violaspec.
Require Import Violaconf.
Require Import Violatrans.
Require Import vCminorp.
Require Import Violasemantics.
Require Import MiscLemmas.
Require Import Classical_Prop.
Import ListNotations.

Section TRANSLATION.

Variable prog: Violaspec.program.
Variable tprog: Cminor.program.
Hypothesis TRANSL: Violatrans.transl_program prog = OK tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Variable dummy_ss: sstate.

(****Dev spec axioms****)
Axiom dev_spec_ss_size: forall regvar, (Int.ltu (Int.repr ((regvar)).(rv_off)) Int.iwordsize) = true.
(** We assume rv_off (register variable offset) is less than word size **)

Axiom dev_spec_mem_perm: forall m b ofs, { r | Mem.range_perm_dec m b ofs (ofs + size_chunk Mint8unsigned) Cur Readable = left r}.
(** & We have readable permission for reading a chunk size of Mint8unsigned from location (m, b, ofs) to (m, b, ofs + chunk_size)
* which m is the mem state, b is the block identifier, and ofs being the byte offset withing the block  **)

Axiom dev_spec_mem_aligned: forall ofs, { r | (Zdivide_dec (align_chunk Mint8unsigned) ofs (align_chunk_pos Mint8unsigned) = left r)}.
(** & the offset (ofs) respects the bounds and alignment constraint in which a valid offset range is between low_bound m b and
* high_bound m b **)

Axiom dev_spec_mem_defined : forall (vl: list memval) , { v | proj_bytes vl = Some v }.
(** & the memory being read is allocated before. **)
(************************)

Local Notation "a # b" := (PMap.get b a) (at level 1).

Lemma mem_load_equal: forall (m : mem) (b : block) (ofs : Z),
           Some (my_load_Mint8unsigned m b ofs) = (Mem.load Mint8unsigned m b ofs).
Proof.
        intros.
        Transparent Mem.load.
        unfold Mem.load.
        unfold Mem.valid_access_dec.
        destruct dev_spec_mem_perm with (m:=m) (b:=b) (ofs:=ofs) as [ss H].
        rewrite H.
                  
        destruct dev_spec_mem_aligned with (ofs:=ofs) as [sss H2].
        rewrite H2.

        unfold my_load_Mint8unsigned.
        unfold decode_val_Mint8unsigned.
        unfold decode_val.
        clear H H2.

        destruct (dev_spec_mem_defined (Mem.getN (size_chunk_nat Mint8unsigned) ofs (Mem.mem_contents m) # b)) as [s H].
        rewrite H.
        unfold bsel.
        rewrite H.
        auto.
Qed.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  exact (Genv.find_symbol_transf_partial _ _ TRANSL).
Qed.

Lemma function_ptr_translated:
  forall (b: block) (fd: Violaspec.fundef),
  Genv.find_funct_ptr ge b = Some fd ->
  exists tfd, Genv.find_funct_ptr tge b = Some tfd /\ transl_fundef fd = OK tfd.
Proof.
  exact (Genv.find_funct_ptr_transf_partial _ _ TRANSL).
Qed.

Lemma sig_transl_function:
  forall fd tfd,
  transl_fundef fd = OK tfd ->
  Cminor.funsig tfd = signature_main.
Proof.
  intros.
  destruct fd; monadInv H; auto.
  monadInv EQ.
  auto.
Qed.

Inductive match_states: Violaspec.state -> Cminor.state -> Prop :=
  | match_state:
    forall f c om os rid roff rval m tf ts tk tsp te tm tb tm'
      (MPOM: Some (Vptr om Int.zero) = te!m_iomem_p)
      (MPOS: Some (Vptr os Int.zero) = te!s_iomem_p)
      (MRID: Some (Vint rid) = te!regaccess_dev_id)
      (MROFF: Some (Vint roff) = te!regaccess_reg_off)
      (MRVAL: Some (Vint rval) = te!regaccess_val)
      (TF: Violatrans.transl_function f = OK tf)
      (TC: Violatrans.transl_code c = OK ts)

      (MK: call_cont tk = Kstop)
      (MSP: tsp = Vptr tb Int.zero)
      (MFREE: Mem.free tm tb 0 tf.(fn_stackspace) = Some tm')

      (MINJ: mem_inj m tm'),
      match_states (Violaspec.State f c om os rid roff rval m)
                   (Cminor.State tf ts tk tsp te tm)
  | match_callstate:
    forall fd om os r m tfd targs tk tm
      (TFD: transl_fundef fd = OK tfd)

      (MINJ: mem_inj m tm)     
      (MARGS: targs = [ Vptr om Int.zero; Vptr os Int.zero; Vptr r Int.zero ])
        (MFREE2: Mem.free m r 0
        match viola_memwords with
        | 0 => 0
        | Z.pos y' => Z.pos y'~0~0
        | Z.neg y' => Z.neg y'~0~0
        end = Some tm)

        (MALLOC: Mem.alloc tm 0
        match viola_memwords with
        | 0 => 0
        | Z.pos y' => Z.pos y'~0~0
        | Z.neg y' => Z.neg y'~0~0
        end = (m, r))

      (MK: call_cont tk = Kstop),
      match_states (Violaspec.Callstate fd om os r m)
                   (Cminor.Callstate tfd targs tk tm)
  | match_returnstate:
    forall a tv tk tm m
      (MV: Vint (Violaspec.action_enc a) = tv)
      (MINJ: mem_inj m tm)
      (MK: tk = Kstop),
      match_states (Violaspec.Returnstate a)
                   (Cminor.Returnstate tv tk tm)
  .

Lemma transl_initial_states:
  forall S, Violaspec.initial_state prog S ->
  exists R, vCminorp.initial_state tprog R /\ match_states S R.
Proof.
  induction 1.
  exploit function_ptr_translated; eauto.
  intros (tf, (A, B)).

  econstructor; split.

  (* initial_state tprog R *)
  - econstructor.
    + apply (Genv.init_mem_transf_partial _ _ TRANSL); eauto.
    + rewrite (transform_partial_program_main _ _ TRANSL).
      fold tge.
      rewrite symbols_preserved.
      eauto.
    + eexact A.
    + eapply sig_transl_function.
      eexact B.
    + eexact H2.
    + eapply H3.
    + eexact H4.
    + eexact H5.
    + eexact H6.
    + eexact H7.

  (* match states S R *)
  - econstructor.
    + eauto.
    + apply inj_refl.
    + eauto.
    + eauto.
    + eauto.
    + eauto.
Qed.

Lemma transl_final_states:
  forall S R r,
  match_states S R -> Violaspec.final_state S r -> Cminor.final_state R r.
Proof.
  intros.
  inv H0.
  inv H.
  constructor.
Qed.

Lemma remove_OK: forall (a b : Cminor.stmt), OK a = OK b -> a = b.
Proof.
  crush.
Qed.

Lemma or_over_and: forall a b c, (a \/ b) /\ (a \/ c) -> a \/ (b /\ c).
Proof.
  intros.
  crush.
Qed.

Lemma or_switch: forall a b, a \/ b -> b \/ a.
Proof.
  intros.
  crush.
Qed.

Lemma my_and_or: forall a b, ~ (a /\ b) -> ~ a \/ (a /\ ~b).
Proof.
  intros.
  apply Classical_Prop.not_and_or in H.
  destruct H.
  + apply or_introl. assumption.
  + apply or_over_and.
    apply conj.
    apply or_switch.
    apply Classical_Prop.classic.
    apply or_intror.
    assumption.  
Qed.

Lemma my_or_or: forall a b, a \/ b -> a \/ (~a /\ b).
Proof.
  intros.
  destruct H.
  + apply or_introl. assumption.
  + apply or_over_and.
    apply conj.
    apply Classical_Prop.classic.
    apply or_intror.
    assumption.  
Qed.

Lemma my_or_in_assumption: forall a b, a \/ b -> a \/ (~a /\ b).
Proof.
  intros.
  destruct H.
  + apply or_introl. assumption.
  + apply or_over_and.
    apply conj.
    apply Classical_Prop.classic.
    apply or_intror.
    assumption.
Qed.

Lemma my_or_in_goal: forall a b, a \/ (~a /\ b) -> a \/ b.
Proof.
  intros.
  crush.
Qed.

Fixpoint test_fix (a : list Z) : Z :=
  match a with
  | [] => 0
  | hd :: tl => 1 + test_fix tl
  end.

Lemma test_lemma2_2: forall a, a >= 0 -> 1 + a >= 0.
Proof.
  intros.
  destruct a.
  crush.
  crush.
  crush.
Qed.

Lemma test_lemma2_1: forall l, test_fix l >= 0.
Proof.
  intros.
  induction l.
  unfold test_fix.
  crush.
  assert (test_fix (a :: l) = 1 + test_fix l) as EQ1.
  crush.
  rewrite EQ1.
  apply test_lemma2_2 with (a:=test_fix l).
  assumption.
Qed.

Lemma test_lemma2_3: forall a, a >= 0 -> 1 + a > 0.
Proof.
  intros.
  destruct a.
  crush.
  crush.
  crush.
Qed.

Lemma test_lemma2: forall l, In 1 l -> test_fix l > 0.
Proof.
  intros.
  destruct l.
  inversion H.
  assert (test_fix (z :: l) = 1 + test_fix l) as EQ1.
  crush.
  rewrite -> EQ1.
  assert (test_fix l >= 0) as EQ2.
    apply test_lemma2_1.
  apply test_lemma2_3 with (a:=test_fix l).
  assumption.
Qed.

Lemma test_lemma: forall (l : list Z), In 1 l -> ((Z.of_nat (length l)) > 0).
Proof.
  intros.
  induction l.
  inversion H.
  crush.
Qed.

Lemma forall_exists1:
        forall (U:Type) (P Q:U -> Prop), ~ (exists n : U, P n -> Q n) -> forall n:U, (P n -> ~ Q n).
Proof.
        intros.
        apply Classical_Pred_Type.not_ex_all_not with (n:=n) in H.
        apply imply_to_and in H.
        inversion H.
        auto.
Qed.

Lemma remove_not: forall (P Q: Prop), ( Q -> P ) -> (~P -> ~Q).
Proof.
        intros.
        apply imply_to_or in H.
        destruct H.
        assumption.
        crush.
Qed.

Lemma remove_not2: forall (P Q: Prop), ( ~Q -> ~P ) -> (P -> Q).
Proof.
        intros.
        apply imply_to_or in H.
        destruct H.
        apply NNPP in H.
        assumption.
        crush.
Qed.

Lemma PNNP: forall p:Prop, p -> ~ ~ p.
Proof.
       crush.
Qed. 

Lemma forall_exists2:
        forall (U:Type) (P Q:U -> Prop), ~ (forall n:U, (P n -> Q n)) -> exists n : U, (P n -> ~ Q n).
Proof.
       intros U P Q.
       apply remove_not2.
       intros H.

       apply PNNP.
       intros.
       
       apply Classical_Pred_Type.not_ex_all_not with (n:=n) in H.
       apply imply_to_and in H.
       inversion H.
       apply NNPP in H2.
       auto.
Qed.

Lemma in1 (x y : Type) : In x [y] <-> x = y.
Proof.
        split; intros H.
        + crush.
        + constructor. auto.
Qed.


Lemma by_empty: forall (X: Type) (a : X) (P: X -> Prop) l, (a :: l = []) -> (l = []) /\ ([a] = []).
Proof.
        intros.
        induction l as [|hd l'].
        auto.
        crush.     
Qed.

Lemma and_over_or3: forall P1 P2 Q R, (P1 /\ P2) /\ (Q \/ R) -> ( (P1 /\ P2) /\ Q) \/ ( (P1 /\ P2) /\ R).
Proof.
  crush.
Qed.

Lemma helper2: forall (X: Type) (a : X) (P: X -> Prop) (l:list X), 
        ~ (exists b : X, In b l /\ P b) ->
        (forall b : X, In b l -> ~ P b).
Proof.
        intros.
        apply Classical_Pred_Type.not_ex_all_not with (n:=b) in H.
        apply not_and_or in H.
        destruct H.
        auto.
        auto.        
Qed.

Lemma helper3: forall ( P Q R: Prop ), (P /\ Q) -> (P /\ Q /\ R \/ P /\ Q /\ ~R).
Proof.
        intros.
        destruct (classic R) as [r | rn].
        - left. constructor. inversion H. assumption. constructor. inversion H. assumption. assumption.
        - right. constructor. inversion H. assumption. constructor. inversion H. assumption. assumption.
Qed.

Lemma helper4: forall (X: Type) (P: X -> Prop) (l:list X), 
        ~ (forall b : X, In b l -> P b) ->
          (exists b : X, In b l /\ ~ P b).
Proof.
        intros.
        apply Classical_Pred_Type.not_all_not_ex.
        revert H.
        apply remove_not.
        intros H.
        crush.
        specialize H with b.
        tauto.
Qed.

Lemma helper5: forall (X: Type) (a : X) (P: X -> Prop) (l:list X), 
        ~ (exists b : X, In b l /\ ~ P b) ->
        (forall b : X, In b l -> P b).
Proof.
        intros.
        apply Classical_Pred_Type.not_ex_all_not with (n:=b) in H.
        apply not_and_or in H.
        destruct H. crush.
        apply NNPP in H.
        auto.
Qed.

Lemma exists_in_list: forall (X : Type) (a : X) l (P : X -> Prop),
            (a :: l <> [] /\ exists b : X, In b (a :: l) /\ P b) ->
            (P a /\ l = []) \/
            (P a /\ l <> [] /\ exists b : X, In b l /\ P b) \/
            (P a /\ l <> [] /\ forall b : X, In b l -> ~ P b) \/
            (~ P a /\ l <> [] /\ exists b : X, In b l /\ P b).
Proof.
        intros.

        assert( (P a /\ l = [] \/
        P a /\ l <> [] /\ (exists b : X, In b l /\ P b) \/
        P a /\ l <> [] /\ (~ (exists b : X, In b l /\ P b)) \/
        ~ P a /\ l <> [] /\ (exists b : X, In b l /\ P b)) ->
        (P a /\ l = [] \/ P a /\ l <> [] /\ (exists b : X, In b l /\ P b) \/
        P a /\ l <> [] /\ (forall b : X, In b l -> ~ P b) \/ ~ P a /\ l <> [] /\ (exists b : X, In b l /\ P b))) as EQ1.
        intros.
        (** 1st **)
        destruct H0.
        left. assumption.
        (** 2nd **)        
        destruct H0.
        right. left. assumption.
        (** 3rd **)        
        destruct H0.
        right. right. left.
        inversion H0. constructor. assumption. constructor.
        inversion H2. assumption. apply helper2. assumption.
        inversion H2. assumption.
        (** 4th **)        
        right. right. right. assumption.
        
        apply EQ1.
        clear EQ1.
         
         assert ( (P a /\ l = [] \/ P a /\ l <> [] \/
         ~ P a /\ l <> [] /\ (exists b : X, In b l /\ P b))->
         (P a /\ l = [] \/
         P a /\ l <> [] /\ (exists b : X, In b l /\ P b) \/
         P a /\ l <> [] /\ ~ (exists b : X, In b l /\ P b) \/
         ~ P a /\ l <> [] /\ (exists b : X, In b l /\ P b))) as EQ1.
         intros.
         
         destruct H0.
         - left. assumption.
         - right.
             destruct H0.
             apply helper3 with (R:=(exists b : X, In b l /\ P b)) in H0.
             destruct H0. left. assumption. right. left. assumption.
             right. right. assumption.
         - apply EQ1. clear EQ1.

         inversion H.

         destruct l.
         inversion H1.
         inversion H2.
         
         assert ( (In x [a]) -> (x = a) ) as EQ1.
            intros Ht.
            crush. 

         apply EQ1 in H3.
         rewrite H3 in H4.
         left. constructor. assumption. auto. 
         
         destruct (classic (P a)) as [ Pa_T | Pa_F ].
         right. left. constructor.  assumption. crush.
         right. right.  constructor. assumption.
         constructor. crush.
         inversion H1.
         exists x0.
         inversion H2.
         constructor.
         crush. assumption.
Qed.

Lemma exists_in_list_not_prop: forall (X : Type) (a : X) l (P : X -> Prop),
            (a :: l <> [] /\ exists b : X, In b (a :: l) /\ ~ P b) ->
            (~ P a /\ l = []) \/
            (~ P a /\ l <> [] /\ exists b : X, In b l /\ ~ P b) \/
            (~ P a /\ l <> [] /\ forall b : X, In b l -> P b) \/
            (P a /\ l <> [] /\ exists b : X, In b l /\ ~ P b).
Proof.
        intros.

        assert( (~ P a /\ l = [] \/
        ~P a /\ l <> [] /\ (exists b : X, In b l /\ ~ P b) \/
        ~P a /\ l <> [] /\ (~ (exists b : X, In b l /\ ~ P b)) \/
        P a /\ l <> [] /\ (exists b : X, In b l /\ ~ P b)) ->
        (~ P a /\ l = [] \/ ~ P a /\ l <> [] /\ (exists b : X, In b l /\ ~ P b) \/
        ~ P a /\ l <> [] /\ (forall b : X, In b l -> P b) \/ P a /\ l <> [] /\ (exists b : X, In b l /\ ~ P b))) as EQ1.
        intros.
        (** 1st **)
        destruct H0.
        left. assumption.
        (** 2nd **)        
        destruct H0.
        right. left. assumption.
        (** 3rd **)        
        destruct H0.
        right. right. left.
        inversion H0. constructor. assumption. constructor.
        inversion H2. assumption.
        inversion H2. apply helper5. auto. auto.
        (** 4th **)        
        right. right. right. auto.
        
        apply EQ1.
        clear EQ1.

        assert ( (~ P a /\ l = [] \/ ~ P a /\ l <> [] \/
        P a /\ l <> [] /\ (exists b : X, In b l /\ ~ P b))->
        (~ P a /\ l = [] \/
        ~ P a /\ l <> [] /\ (exists b : X, In b l /\ ~ P b) \/
        ~ P a /\ l <> [] /\ ~ (exists b : X, In b l /\ ~ P b) \/
        P a /\ l <> [] /\ (exists b : X, In b l /\ ~ P b))) as EQ1.
        intros.
         
        destruct H0.
        - left. assumption.
        - right.
           destruct H0.
             apply helper3 with (R:=(exists b : X, In b l /\ ~ P b)) in H0.
             destruct H0. left. assumption. right. left. assumption.
             right. right. assumption.
         - apply EQ1. clear EQ1.

         inversion H.

         destruct l.
         inversion H1.
         inversion H2.
         
         assert ( (In x [a]) -> (x = a) ) as EQ1.
            intros Ht.
            crush. 

         apply EQ1 in H3.
         rewrite H3 in H4.
         left. constructor. assumption. auto. 
         
         destruct (classic (~ P a)) as [ Pa_T | Pa_F ].
         right. left. constructor.  assumption. crush. 
         right. right.  constructor. apply NNPP in Pa_F. assumption.
         apply NNPP in Pa_F.
         constructor. crush.
         inversion H1.
         exists x0.
         inversion H2.
         constructor.
         crush. assumption.
Qed.

Lemma val_remains_int_axiom: forall (a b c d: int), Int.ltu c Int.iwordsize = true -> (Val.shru (Val.and (Vint a) (Vint b)) (Vint c)) <> (Vint d) ->
                           (exists (e : int), (Val.shru (Val.and (Vint a) (Vint b)) (Vint c)) = (Vint e) /\ e <> d).
Proof.
        intros.
        unfold Val.shru in H0.
        unfold Val.shru.
        simpl.
        simpl in H0.
        rewrite H.
        rewrite H in H0.
        eexists. split.
        - reflexivity.
        - intro Heq. subst. auto.
Qed.

Lemma ss_not_target_axiom : forall ss o rid roff rval m, ~ ss_in_target ss o rid roff rval m -> NOT_ss_in_target ss o rid roff rval m.
Proof.
        intros.
        unfold ss_in_target in H.
        unfold NOT_ss_in_target.
        crush.
Qed.

Lemma eq_noteq : forall s, trans s = [] -> ~ trans s <> [].
Proof.
        crush.
Qed.

Lemma noteq_eq : forall s, ~ trans s <> [] -> trans s = [].
Proof.
        intros.
        crush.
        apply imply_to_or in H.
        destruct H.
        apply imply_to_and in H.
        inversion H.
        assumption.
        crush.
Qed.

Lemma noteq_eq2 : forall ss, ~ inv_ss ss <> [] -> inv_ss ss = [].
Proof.
        intros.
        crush.
        apply imply_to_or in H.
        destruct H.
        apply imply_to_and in H.
        inversion H.
        assumption.
        crush.  
Qed.

Variable (my_tran : state_trans).
Lemma will_not_go_to_target_axiom: forall s ss o rid roff rval m, ~ will_ss_go_to_target s ss o rid roff rval m -> NOT_will_ss_go_to_target s ss o rid roff rval m.
Proof.  
        intros.
        unfold will_ss_go_to_target in H.
        unfold NOT_will_ss_go_to_target.
        apply Classical_Prop.not_and_or in H.
        destruct H.
        left.
        apply noteq_eq in H.
        assumption.
        right.
        apply helper2. auto. assumption. 
Qed.

(* Definition lnat := []:list Z. *)
Definition lnat := [1; 2; 3].

Definition BB (aa : Z) : Prop :=
  match aa with
  | 4 => False
  | _ => True
  end.

SearchAbout In.

Lemma will_not_go_out_of_target_axiom: forall s ss o rid roff rval m, ~ will_ss_go_out_of_target s ss o rid roff rval m -> NOT_will_ss_go_out_of_target s ss o rid roff rval m.
Proof.
        intros.
        unfold will_ss_go_out_of_target in H.
        unfold NOT_will_ss_go_out_of_target.
        apply Classical_Prop.not_and_or in H.
        destruct H.
        left.
        apply noteq_eq in H.
        assumption.
        right.
        apply helper2. auto. assumption.
Qed.

Lemma will_dev_not_go_to_target_axiom: forall s ss o rid roff rval m, ~ will_go_to_target_state s ss o rid roff rval m -> NOT_will_go_to_target_state s ss o rid roff rval m.
Proof.
        intros.
        unfold will_go_to_target_state in H.
        unfold NOT_will_go_to_target_state.
        apply Classical_Prop.not_and_or in H.
        destruct H.
        left.
        apply noteq_eq2.
        assumption.
        right.
        apply helper4. auto.
Qed.

Lemma will_dev_not_go_out_of_target_axiom: forall s ss o rid roff rval m, ~ will_go_out_of_target_state s ss o rid roff rval m -> NOT_will_go_out_of_target_state s ss o rid roff rval m.
Proof.
        intros.
        unfold will_go_out_of_target_state in H.
        unfold NOT_will_go_out_of_target_state.
        apply not_or_and in H.
        inversion H.
        clear H.
        constructor. 
        assumption. 
        apply helper2; auto.    
Qed.

Lemma invalid_access: forall ige isp ie im regs' roff,
                      Some (Vint roff) = ie ! regaccess_reg_off ->
                      ~ In roff (map reg_to_int regs') ->
                      eval_expr ige isp ie im (C_is_valid_dev_access regs') Vfalse.
         intros.

         induction regs' as [|reg' regs''].
         unfold C_is_valid_dev_access.
         apply eval_Econst.
         auto.

         unfold C_is_valid_dev_access.
         fold C_is_valid_dev_access.
         apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
         apply eval_Ebinop with (v1:=Vint roff) (v2:=Vint (Int.repr (reg_off reg'))). constructor. auto. constructor. constructor.
         unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto.
         unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
         assert (Int.cmp Ceq roff (Int.repr (reg_off reg')) = false) as EQ3.
         simpl.
         apply Int.eq_false.
         crush.
         unfold In in H0.
         rewrite EQ3.
         auto.

         apply IHregs''.
         crush.
         auto.
Qed.

Lemma and_over_or: forall P Q R, P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
Proof.
  crush.
Qed.

Lemma and_over_or2: forall P Q R, P /\ (Q \/ R) -> (Q /\ P) \/ (R /\ P).
Proof.
  crush.
Qed.

Lemma and_or_neg: forall (P Q : Prop), P -> (P /\ (Q \/ ~ Q)).
Proof.
  intros.
  apply conj.
  assumption.
  apply Classical_Prop.classic.
Qed.

Lemma and_or_neg2: forall (P Q : Prop), P -> (P /\ (~ Q \/ Q)).
Proof.
  intros.
  apply conj.
  assumption.
    assert (Q \/ ~ Q -> ~ Q \/ Q) as EQ.
    intros.
    crush.
  apply EQ.
  apply Classical_Prop.classic.
Qed.

Lemma exists_in_list_map: forall reg regs' roff,
              In roff (map reg_to_int (reg :: regs')) ->
              (((roff = reg_to_int reg) /\ (In roff (map reg_to_int (regs')))) \/
               ((roff = reg_to_int reg) /\ (~ In roff (map reg_to_int (regs')))) \/
               ((roff <> reg_to_int reg) /\ In roff (map reg_to_int (regs')))).
        intros.        
        destruct H.
        assert ((roff = reg_to_int reg /\ In roff (map reg_to_int regs') \/
                roff = reg_to_int reg /\ ~ In roff (map reg_to_int regs')) ->
                (roff = reg_to_int reg /\ In roff (map reg_to_int regs') \/
                roff = reg_to_int reg /\ ~ In roff (map reg_to_int regs') \/
                roff <> reg_to_int reg /\ In roff (map reg_to_int regs'))) as EQ.
        intros.
        destruct H0.
        left.
        assumption.
        right.
        left.
        assumption.
        apply EQ.
        apply and_over_or.
        apply and_or_neg.
        crush.

        assert ((roff = reg_to_int reg /\ In roff (map reg_to_int regs') \/
                roff <> reg_to_int reg /\ In roff (map reg_to_int regs')) ->
                (roff = reg_to_int reg /\ In roff (map reg_to_int regs') \/
                roff = reg_to_int reg /\ ~ In roff (map reg_to_int regs') \/
                roff <> reg_to_int reg /\ In roff (map reg_to_int regs'))) as EQ.
        intros.
        destruct H0.
        left.
        assumption.
        right.
        right.
        assumption.
        apply EQ.
        apply and_over_or2.
        apply and_or_neg.
        crush.
Qed.

Lemma not_nil: forall (X : Type) (a : X) l, a :: l <> [].
Proof.
  intros.
  induction l as [|a' l'].
  crush.
  crush.
Qed.

Lemma in_subset: forall (X : Type) (ss ss' ss'' : X) inv_ss'',
                   In ss (ss'' :: inv_ss'') -> In ss (ss' :: ss'' :: inv_ss'').
Proof.
  intros.
  destruct H.
  simpl.
  crush.
  simpl.
  crush.
Qed.

(* From SF book *)
Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.
Qed.

Theorem does_not_exist : forall (X:Type) (P : X -> Prop), ~ (exists x : X, P x) -> (forall x : X, ~ P x).
Proof.
  apply Classical_Pred_Type.not_ex_all_not.
Qed.

Lemma not_in_ex: forall (X:Type) (P Q : X -> Prop), (exists x : X, ~ (P x -> Q x)) -> (exists x : X, P x /\ ~ Q x).
Proof.
  intros.
  inversion H.
  exists x.
  apply Classical_Prop.imply_to_and.
  assumption.
Qed.

Lemma and_in_ex: forall (X:Type) (P Q : X -> Prop), (exists x : X, P x /\ Q x) -> ((exists x : X, P x -> Q x)).
Proof.
  intros.
  inversion H.
  exists x.
  intros.
  inversion H0.
  assumption.
Qed.

Lemma forall_just_one: forall (X : Type) (a' : X) (P : X -> Prop),
      (forall a, In a [a'] -> P a) -> P a'.
Proof.
  intros.
  apply H.
  crush.
Qed.

Lemma forall_in_list: forall (X : Type) (a' : X) l (P : X -> Prop),
      (forall a, In a (a'::l) -> P a) -> P a'.
Proof.
  intros.
  apply H.
  crush.
Qed.

Lemma forall_in_list2: forall (X : Type) (a' : X) l (P : X -> Prop),
      (forall a, In a (a'::l) -> P a) -> P a' /\ (forall a, In a (l) -> P a).
Proof.
  intros.
  apply conj.
  apply H.
  crush.
  intros.
  apply H.
  crush.
Qed.

Lemma expand_or: forall P Q, P \/ Q -> (P /\ Q) \/ (P /\ ~ Q) \/ (~ P /\ Q).
Proof.
  intros.
  destruct H.
  assert (P /\ Q \/ P /\ ~ Q -> P /\ Q \/ P /\ ~ Q \/ ~ P /\ Q) as EQ.
    intros.
    destruct H0.
    left.
    assumption.
    right.
    left.
    assumption.
  apply EQ.
  apply and_over_or.
  apply and_or_neg.
  assumption.
  assert (P /\ Q \/ ~ P /\ Q -> P /\ Q \/ P /\ ~ Q \/ ~ P /\ Q) as EQ.
    intros.
    destruct H0.
    left.
    assumption.
    right.
    right.
    assumption.
  apply EQ.
  apply and_over_or2.
  apply and_or_neg.
  assumption.
Qed.

Lemma expand_and_over_two_or: forall (P Q R S : Prop), (P /\ (Q \/ R \/ S)) -> ((P /\ Q) \/ (P /\ R) \/ (P /\ S)).
Proof.
  intros.
  crush.
Qed.

Lemma not_two_and: forall (Q R : Prop), ~ (Q /\ R) -> ((~ Q /\ R) \/ (Q /\ ~ R) \/ (~ Q /\ ~ R)).
Proof.
  intros.
  apply Classical_Prop.not_and_or in H.
  destruct H.
  assert (~ Q /\ ~ R \/ ~ Q /\ R -> ~ Q /\ R \/ Q /\ ~ R \/ ~ Q /\ ~ R) as EQ.
    intros.
    destruct H0.
    right.
    right.
    assumption.
    left.
    assumption.
  apply EQ.
  apply and_over_or.
  apply and_or_neg2.
  assumption.
  assert (~ Q /\ ~ R \/ Q /\ ~ R -> ~ Q /\ R \/ Q /\ ~ R \/ ~ Q /\ ~ R) as EQ.
    intros.
    destruct H0.
    right.
    right.
    assumption.
    right.
    left.
    assumption.
  apply EQ.
  apply and_over_or2.
  apply and_or_neg2.
  assumption.  
Qed.

Lemma expand_neg_and_in_three: forall (P Q R : Prop),
                               ((~ P /\ Q /\ R) \/
                                (~ P /\ ~ (Q /\ R))) ->
                               ((~ P /\ Q /\ R) \/
                                (~ P /\ ~ Q /\ R) \/
                                (~ P /\ Q /\ ~ R) \/
                                (~ P /\ ~ Q /\ ~ R)).
Proof.
  intros.
  destruct H.
  left.
  assumption.
  right.
  apply expand_and_over_two_or.
  inversion H.
  apply conj.
  assumption.
  apply not_two_and.
  assumption.
Qed.

Lemma not_three_and: forall P Q R, ~ (P /\ Q /\ R) -> (~ P /\ Q /\ R) \/
                                                      (P /\ ~ Q /\ R) \/
                                                      (P /\ Q /\ ~ R) \/
                                                      (~ P /\ ~ Q /\ R) \/
                                                      (P /\ ~ Q /\ ~ R) \/
                                                      (~ P /\ Q /\ ~ R) \/
                                                      (~ P /\ ~ Q /\ ~ R).
Proof.
  intros.
  apply Classical_Prop.not_and_or in H.
  destruct H.
  assert (((~ P /\ Q /\ R) \/
           (~ P /\ ~ Q /\ R) \/
           (~ P /\ Q /\ ~ R) \/
           (~ P /\ ~ Q /\ ~ R)) ->
          ((~ P /\ Q /\ R) \/
           (P /\ ~ Q /\ R) \/
           (P /\ Q /\ ~ R) \/
           (~ P /\ ~ Q /\ R) \/
           (P /\ ~ Q /\ ~ R) \/
           (~ P /\ Q /\ ~ R) \/
           (~ P /\ ~ Q /\ ~ R))) as EQ.
    intros.
    destruct H0.
    left.
    assumption.
    destruct H0.
    right; right; right; left.
    assumption.
    destruct H0.
    right; right; right; right; right; left.
    assumption.
    right; right; right; right; right; right.
    assumption.
  apply EQ.
  clear EQ.
  apply expand_neg_and_in_three.
  apply and_over_or.
  apply conj.
  assumption.
  apply Classical_Prop.classic.

  apply Classical_Prop.not_and_or in H.
  destruct H.
  assert (((~ Q /\ P /\ R) \/
           (~ Q /\ ~ P /\ R) \/
           (~ Q /\ P /\ ~ R) \/
           (~ Q /\ ~ P /\ ~ R)) ->
          ((~ P /\ Q /\ R) \/
           (P /\ ~ Q /\ R) \/
           (P /\ Q /\ ~ R) \/
           (~ P /\ ~ Q /\ R) \/
           (P /\ ~ Q /\ ~ R) \/
           (~ P /\ Q /\ ~ R) \/
           (~ P /\ ~ Q /\ ~ R))) as EQ.
    intros.
    destruct H0.
    right; left.
    crush.
    destruct H0.
    right; right; right; left.
    crush.
    destruct H0.
    right; right; right; right; left.
    crush.
    right; right; right; right; right; right.
    crush.
  apply EQ.
  clear EQ.
  apply expand_neg_and_in_three.
  apply and_over_or.
  apply conj.
  assumption.
  apply Classical_Prop.classic.
  
  assert (((~ R /\ P /\ Q) \/
           (~ R /\ ~ P /\ Q) \/
           (~ R /\ P /\ ~ Q) \/
           (~ R /\ ~ P /\ ~ Q)) ->
          ((~ P /\ Q /\ R) \/
           (P /\ ~ Q /\ R) \/
           (P /\ Q /\ ~ R) \/
           (~ P /\ ~ Q /\ R) \/
           (P /\ ~ Q /\ ~ R) \/
           (~ P /\ Q /\ ~ R) \/
           (~ P /\ ~ Q /\ ~ R))) as EQ.
    intros.
    destruct H0.
    right; right; left.
    crush.
    destruct H0.
    right; right; right; right; right; left.
    crush.
    destruct H0.
    right; right; right; right; left.
    crush.
    right; right; right; right; right; right.
    crush.
  apply EQ.
  clear EQ.
  apply expand_neg_and_in_three.
  apply and_over_or.
  apply conj.
  assumption.
  apply Classical_Prop.classic.
Qed.

Lemma expand_and_over_six_or: forall (P Q R S T U V W: Prop), (P /\ (Q \/ R \/ S \/ T \/ U \/ V \/ W)) ->
                                                       ((P /\ Q) \/ (P /\ R) \/ (P /\ S) \/ (P /\ T) \/
                                                        (P /\ U) \/ (P /\ V) \/ (P /\ W)).
Proof.
  intros.
  crush.
Qed.

Lemma expand_neg_and_in_four: forall (P Q R S: Prop),
                              (~ P /\ Q /\ R /\ S \/
                               ~ P /\ ~ (Q /\ R /\ S)) ->
                              (~ P /\ Q /\ R /\ S \/
                               ~ P /\ ~ Q /\ R /\ S \/
                               ~ P /\ Q /\ ~ R /\ S \/
                               ~ P /\ Q /\ R /\ ~ S \/
                               ~ P /\ ~ Q /\ ~ R /\ S \/
                               ~ P /\ Q /\ ~ R /\ ~ S \/
                               ~ P /\ ~ Q /\ R /\ ~ S \/
                               ~ P /\ ~ Q /\ ~ R /\ ~ S).
Proof.
  intros.
  destruct H.
  left.
  assumption.
  right.
  apply expand_and_over_six_or.
  inversion H.
  apply conj.
  assumption.
  apply not_three_and.
  assumption.
Qed.

Lemma not_four_and: forall P Q R S, ~ (P /\ Q /\ R /\ S) -> (~ P /\ Q /\ R /\ S) \/
                                                            (P /\ ~ Q /\ R /\ S) \/
                                                            (P /\ Q /\ ~ R /\ S) \/
                                                            (P /\ Q /\ R /\ ~ S) \/

                                                            (~ P /\ ~ Q /\ R /\ S) \/
                                                            (~ P /\ Q /\ ~ R /\ S) \/
                                                            (~ P /\ Q /\ R /\ ~ S) \/
                                                            (P /\ ~ Q /\ ~ R /\ S) \/
                                                            (P /\ ~ Q /\ R /\ ~ S) \/
                                                            (P /\ Q /\ ~ R /\ ~ S) \/

                                                            (P /\ ~ Q /\ ~ R /\ ~ S) \/
                                                            (~ P /\ Q /\ ~ R /\ ~ S) \/
                                                            (~ P /\ ~ Q /\ R /\ ~ S) \/
                                                            (~ P /\ ~ Q /\ ~ R /\ S) \/
                                                            (~ P /\ ~ Q /\ ~ R /\ ~ S).
Proof.
  intros.
  apply Classical_Prop.not_and_or in H.
  destruct H.
  assert (((~ P /\ Q /\ R /\ S) \/
           (~ P /\ ~ Q /\ R /\ S) \/
           (~ P /\ Q /\ ~ R /\ S) \/
           (~ P /\ Q /\ R /\ ~ S) \/
           (~ P /\ ~ Q /\ ~ R /\ S) \/
           (~ P /\ Q /\ ~ R /\ ~ S) \/
           (~ P /\ ~ Q /\ R /\ ~ S) \/
           (~ P /\ ~ Q /\ ~ R /\ ~ S)) ->
          ((~ P /\ Q /\ R /\ S) \/
           (P /\ ~ Q /\ R /\ S) \/
           (P /\ Q /\ ~ R /\ S) \/
           (P /\ Q /\ R /\ ~ S) \/
           (~ P /\ ~ Q /\ R /\ S) \/
           (~ P /\ Q /\ ~ R /\ S) \/
           (~ P /\ Q /\ R /\ ~ S) \/
           (P /\ ~ Q /\ ~ R /\ S) \/
           (P /\ ~ Q /\ R /\ ~ S) \/
           (P /\ Q /\ ~ R /\ ~ S) \/
           (P /\ ~ Q /\ ~ R /\ ~ S) \/
           (~ P /\ Q /\ ~ R /\ ~ S) \/
           (~ P /\ ~ Q /\ R /\ ~ S) \/
           (~ P /\ ~ Q /\ ~ R /\ S) \/
           (~ P /\ ~ Q /\ ~ R /\ ~ S))) as EQ.
    intros.
    destruct H0.
    left.
    assumption.
    destruct H0.
    right; right; right; right; left.
    assumption.
    destruct H0.
    right; right; right; right; right; left.
    assumption.
    destruct H0.
    right; right; right; right; right; right; left.
    assumption.
    destruct H0.
    right; right; right; right; right; right; right; right; right; right; right; right; right; left.
    assumption.
    destruct H0.
    right; right; right; right; right; right; right; right; right; right; right; left.
    assumption.
    destruct H0.
    right; right; right; right; right; right; right; right; right; right; right; right; left.
    assumption.
    right; right; right; right; right; right; right; right; right; right; right; right; right; right.
    assumption.
  apply EQ.
  apply expand_neg_and_in_four.
  apply and_over_or.
  apply conj.
  assumption.
  apply Classical_Prop.classic.

  apply Classical_Prop.not_and_or in H.
  destruct H.
  assert (((~ Q /\ P /\ R /\ S) \/
           (~ Q /\ ~ P /\ R /\ S) \/
           (~ Q /\ P /\ ~ R /\ S) \/
           (~ Q /\ P /\ R /\ ~ S) \/
           (~ Q /\ ~ P /\ ~ R /\ S) \/
           (~ Q /\ P /\ ~ R /\ ~ S) \/
           (~ Q /\ ~ P /\ R /\ ~ S) \/
           (~ Q /\ ~ P /\ ~ R /\ ~ S)) ->
          ((~ P /\ Q /\ R /\ S) \/
           (P /\ ~ Q /\ R /\ S) \/
           (P /\ Q /\ ~ R /\ S) \/
           (P /\ Q /\ R /\ ~ S) \/
           (~ P /\ ~ Q /\ R /\ S) \/
           (~ P /\ Q /\ ~ R /\ S) \/
           (~ P /\ Q /\ R /\ ~ S) \/
           (P /\ ~ Q /\ ~ R /\ S) \/
           (P /\ ~ Q /\ R /\ ~ S) \/
           (P /\ Q /\ ~ R /\ ~ S) \/
           (P /\ ~ Q /\ ~ R /\ ~ S) \/
           (~ P /\ Q /\ ~ R /\ ~ S) \/
           (~ P /\ ~ Q /\ R /\ ~ S) \/
           (~ P /\ ~ Q /\ ~ R /\ S) \/
           (~ P /\ ~ Q /\ ~ R /\ ~ S))) as EQ.
    intros.
    destruct H0.
    right; left.
    crush.
    destruct H0.
    right; right; right; right; left.
    crush.
    destruct H0.
    right; right; right; right; right; right; right; left.
    crush.
    destruct H0.
    right; right; right; right; right; right; right; right; left.
    crush.
    destruct H0.
    right; right; right; right; right; right; right; right; right; right; right; right; right; left.
    crush.
    destruct H0.
    right; right; right; right; right; right; right; right; right; right; left.
    crush.
    destruct H0.
    right; right; right; right; right; right; right; right; right; right; right; right; left.
    crush.
    right; right; right; right; right; right; right; right; right; right; right; right; right; right.
    crush.
  apply EQ.
  apply expand_neg_and_in_four.
  apply and_over_or.
  apply conj.
  assumption.
  apply Classical_Prop.classic.

  apply Classical_Prop.not_and_or in H.
  destruct H.
  assert (((~ R /\ P /\ Q /\ S) \/
           (~ R /\ ~ P /\ Q /\ S) \/
           (~ R /\ P /\ ~ Q /\ S) \/
           (~ R /\ P /\ Q /\ ~ S) \/
           (~ R /\ ~ P /\ ~ Q /\ S) \/
           (~ R /\ P /\ ~ Q /\ ~ S) \/
           (~ R /\ ~ P /\ Q /\ ~ S) \/
           (~ R /\ ~ P /\ ~ Q /\ ~ S)) ->
          ((~ P /\ Q /\ R /\ S) \/
           (P /\ ~ Q /\ R /\ S) \/
           (P /\ Q /\ ~ R /\ S) \/
           (P /\ Q /\ R /\ ~ S) \/
           (~ P /\ ~ Q /\ R /\ S) \/
           (~ P /\ Q /\ ~ R /\ S) \/
           (~ P /\ Q /\ R /\ ~ S) \/
           (P /\ ~ Q /\ ~ R /\ S) \/
           (P /\ ~ Q /\ R /\ ~ S) \/
           (P /\ Q /\ ~ R /\ ~ S) \/
           (P /\ ~ Q /\ ~ R /\ ~ S) \/
           (~ P /\ Q /\ ~ R /\ ~ S) \/
           (~ P /\ ~ Q /\ R /\ ~ S) \/
           (~ P /\ ~ Q /\ ~ R /\ S) \/
           (~ P /\ ~ Q /\ ~ R /\ ~ S))) as EQ.
    intros.
    destruct H0.
    right; right; left.
    crush.
    destruct H0.
    right; right; right; right; right; left.
    crush.
    destruct H0.
    right; right; right; right; right; right; right; left.
    crush.
    destruct H0.
    right; right; right; right; right; right; right; right; right; left.
    crush.
    destruct H0.
    right; right; right; right; right; right; right; right; right; right; right; right; right; left.
    crush.
    destruct H0.
    right; right; right; right; right; right; right; right; right; right; left.
    crush.
    destruct H0.
    right; right; right; right; right; right; right; right; right; right; right; left.
    crush.
    right; right; right; right; right; right; right; right; right; right; right; right; right; right.
    crush.
  apply EQ.
  apply expand_neg_and_in_four.
  apply and_over_or.
  apply conj.
  assumption.
  apply Classical_Prop.classic.

  assert (((~ S /\ P /\ Q /\ R) \/
           (~ S /\ ~ P /\ Q /\ R) \/
           (~ S /\ P /\ ~ Q /\ R) \/
           (~ S /\ P /\ Q /\ ~ R) \/
           (~ S /\ ~ P /\ ~ Q /\ R) \/
           (~ S /\ P /\ ~ Q /\ ~ R) \/
           (~ S /\ ~ P /\ Q /\ ~ R) \/
           (~ S /\ ~ P /\ ~ Q /\ ~ R)) ->
          ((~ P /\ Q /\ R /\ S) \/
           (P /\ ~ Q /\ R /\ S) \/
           (P /\ Q /\ ~ R /\ S) \/
           (P /\ Q /\ R /\ ~ S) \/
           (~ P /\ ~ Q /\ R /\ S) \/
           (~ P /\ Q /\ ~ R /\ S) \/
           (~ P /\ Q /\ R /\ ~ S) \/
           (P /\ ~ Q /\ ~ R /\ S) \/
           (P /\ ~ Q /\ R /\ ~ S) \/
           (P /\ Q /\ ~ R /\ ~ S) \/
           (P /\ ~ Q /\ ~ R /\ ~ S) \/
           (~ P /\ Q /\ ~ R /\ ~ S) \/
           (~ P /\ ~ Q /\ R /\ ~ S) \/
           (~ P /\ ~ Q /\ ~ R /\ S) \/
           (~ P /\ ~ Q /\ ~ R /\ ~ S))) as EQ.
    intros.
    destruct H0.
    right; right; right; left.
    crush.
    destruct H0.
    right; right; right; right; right; right; left.
    crush.
    destruct H0.
    right; right; right; right; right; right; right; right; left.
    crush.
    destruct H0.
    right; right; right; right; right; right; right; right; right; left.
    crush.
    destruct H0.
    right; right; right; right; right; right; right; right; right; right; right; right; left.
    crush.
    destruct H0.
    right; right; right; right; right; right; right; right; right; right; left.
    crush.
    destruct H0.
    right; right; right; right; right; right; right; right; right; right; right; left.
    crush.
    right; right; right; right; right; right; right; right; right; right; right; right; right; right.
    crush.
  apply EQ.
  apply expand_neg_and_in_four.
  apply and_over_or.
  apply conj.
  assumption.
  apply Classical_Prop.classic.
Qed.

Lemma __L_Eload: forall tge0 tb te tm tm' tf m o x x0 iomem_p,
      Some (Vptr o Int.zero) = te ! iomem_p ->
      Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
      mem_inj m tm' ->
      Some (Vint x0) = Mem.load Mint8unsigned m o
        (Int.unsigned (Int.repr (reg_off (rv_reg (ss_regvar x))))) ->
      eval_expr tge0 (Vptr tb Int.zero) te tm
        (Eload Mint8unsigned
            (Ebinop Oadd (Evar iomem_p)
               (Econst (Ointconst (Int.repr (reg_off (rv_reg (ss_regvar x)))))))) (Vint x0).
Proof.
      (* Mem load start *)
      intros tge0 tb te tm tm' tf m o x x0 iomem_p MPOM MFREE MINJ H.

      apply eval_Eload with (vaddr:=Vptr o (Int.repr (reg_off (rv_reg (ss_regvar x))))).
      apply eval_Ebinop with (v1:=Vptr o Int.zero) (v2:=Vint ((Int.repr (reg_off (rv_reg (ss_regvar x)))))).
      constructor.
      auto.
      apply eval_Econst.
      auto.
      unfold eval_binop.
      unfold Val.add.
      rewrite Int.add_zero_l.
      reflexivity.
      unfold Mem.loadv.
      Print Mem.load_inj.
      destruct (Mem.load_inj inject_id m tm' Mint8unsigned o (Int.unsigned (Int.repr (reg_off (rv_reg (ss_regvar x))))) o 0 (Vint x0)); eauto.
      rewrite Z.add_0_r in *.
      inversion H0.
      (* inversion H27. *)
      rewrite Mem.load_free_2 with (m2:=tm') (bf:=tb) (lo:=0) (hi:=(fn_stackspace tf)) (v:=x1).
      inversion H2; eauto.
      eauto.
      eauto.
Qed.

Lemma reg_off_equal: forall ss' tge0 tb te tm tran',
      Int.repr (reg_off (rv_reg (ss_regvar (dst tran')))) = Int.repr (reg_off (rv_reg (ss_regvar ss'))) ->
      eval_expr tge0 (Vptr tb Int.zero) te tm
        (Ebinop (Ocmp Ceq)
           (Econst
              (Ointconst (Int.repr (reg_off (rv_reg (ss_regvar (dst tran')))))))
           (Econst (Ointconst (Int.repr (reg_off (rv_reg (ss_regvar ss')))))))
      Vtrue.
Proof.
      intros ss' tge0 tb te tm tran' H.
      apply eval_Ebinop with (v1:=Vint (Int.repr (reg_off (rv_reg (ss_regvar (dst tran'))))))
                     (v2:=Vint (Int.repr (reg_off (rv_reg (ss_regvar ss'))))). constructor. constructor. constructor. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Ceq (Int.repr (reg_off (rv_reg (ss_regvar (dst tran'))))) 
                          (Int.repr (reg_off (rv_reg (ss_regvar ss')))) = true) as EQ3.
        simpl.
        rewrite H.
        apply Int.eq_true.
      rewrite EQ3.
      constructor.
Qed.

Lemma NOT_reg_off_equal: forall ss' tge0 tb te tm tran',
      Int.repr (reg_off (rv_reg (ss_regvar (dst tran')))) <> Int.repr (reg_off (rv_reg (ss_regvar ss'))) ->
      eval_expr tge0 (Vptr tb Int.zero) te tm
        (Ebinop (Ocmp Ceq)
           (Econst
              (Ointconst (Int.repr (reg_off (rv_reg (ss_regvar (dst tran')))))))
           (Econst (Ointconst (Int.repr (reg_off (rv_reg (ss_regvar ss')))))))
      Vfalse.
Proof.
      intros ss' tge0 tb te tm tran' H.
      apply eval_Ebinop with (v1:=Vint (Int.repr (reg_off (rv_reg (ss_regvar (dst tran'))))))
                     (v2:=Vint (Int.repr (reg_off (rv_reg (ss_regvar ss'))))). constructor. constructor. constructor. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Ceq (Int.repr (reg_off (rv_reg (ss_regvar (dst tran'))))) 
                          (Int.repr (reg_off (rv_reg (ss_regvar ss')))) = false) as EQ3.
        apply Int.eq_false.
        assumption.
      rewrite EQ3.
      constructor.
Qed.

Lemma val_equal: forall ss' tge0 tb te tm tran',
      Int.repr (ss_val (dst tran')) = Int.repr (ss_val ss') ->
      eval_expr tge0 (Vptr tb Int.zero) te tm
        (Ebinop (Ocmp Ceq) (Econst (Ointconst (Int.repr (ss_val (dst tran')))))
           (Econst (Ointconst (Int.repr (ss_val ss'))))) Vtrue.
Proof.
      intros ss' tge0 tb te tm tran' H.
      apply eval_Ebinop with (v1:=Vint (Int.repr (ss_val (dst tran'))))
                     (v2:=Vint (Int.repr (ss_val ss'))). constructor. constructor. constructor. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Ceq (Int.repr (ss_val (dst tran')))
                          (Int.repr (ss_val ss')) = true) as EQ3.
        simpl.
        rewrite H.
        apply Int.eq_true.
      rewrite EQ3.
      constructor.
Qed.

Lemma NOT_val_equal: forall ss' tge0 tb te tm tran',
      Int.repr (ss_val (dst tran')) <> Int.repr (ss_val ss') ->
      eval_expr tge0 (Vptr tb Int.zero) te tm
        (Ebinop (Ocmp Ceq) (Econst (Ointconst (Int.repr (ss_val (dst tran')))))
           (Econst (Ointconst (Int.repr (ss_val ss'))))) Vfalse.
Proof.
      intros ss' tge0 tb te tm tran' H.
      apply eval_Ebinop with (v1:=Vint (Int.repr (ss_val (dst tran'))))
                     (v2:=Vint (Int.repr (ss_val ss'))). constructor. constructor. constructor. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Ceq (Int.repr (ss_val (dst tran')))
                          (Int.repr (ss_val ss')) = false) as EQ3.
        apply Int.eq_false.
        assumption.
      rewrite EQ3.
      constructor.
Qed.

Lemma true_negb: forall b, b = false -> negb b = true.
  intros.
  crush.
Qed.

Lemma val_not_equal: forall ss' tge0 tb te tm tran',
      Int.repr (ss_val (dst tran')) <> Int.repr (ss_val ss') ->
      eval_expr tge0 (Vptr tb Int.zero) te tm
        (Ebinop (Ocmp Cne) (Econst (Ointconst (Int.repr (ss_val (dst tran')))))
           (Econst (Ointconst (Int.repr (ss_val ss'))))) Vtrue.
Proof.
      intros ss' tge0 tb te tm tran' H.

      apply eval_Ebinop with (v1:=Vint (Int.repr (ss_val (dst tran'))))
                     (v2:=Vint (Int.repr (ss_val ss'))). constructor. constructor. constructor. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Cne (Int.repr (ss_val (dst tran')))
                          (Int.repr (ss_val ss')) = true) as EQ3.
        simpl.
        apply true_negb.
        apply Int.eq_false.
        assumption.
      rewrite EQ3.
      constructor.
Qed.

Lemma false_negb: forall b, b = true -> negb b = false.
  intros.
  crush.
Qed.

(*
 * Inspired by proof of Theorem not_exists_dist in 
 * from https://github.com/haklabbeograd/software-foundations-coq-workshop/blob/master/Logic.v
 *)
Lemma not_not_equal: forall (X:Type) (a b: X), ~ (a <> b) -> a = b.
Proof.
  intros.
  assert ((a = b) \/ ~ (a = b)).
  apply Classical_Prop.classic.
  inversion H0.
  apply H1.
  apply ex_falso_quodlibet.
  unfold not in H.
  apply H.
  unfold not in H1.
  apply H1.
Qed.

Lemma NOT_val_not_equal: forall ss' tge0 tb te tm tran',
      ~ Int.repr (ss_val (dst tran')) <> Int.repr (ss_val ss') ->
      eval_expr tge0 (Vptr tb Int.zero) te tm
        (Ebinop (Ocmp Cne) (Econst (Ointconst (Int.repr (ss_val (dst tran')))))
           (Econst (Ointconst (Int.repr (ss_val ss'))))) Vfalse.
Proof.
      intros ss' tge0 tb te tm tran' H.

      apply eval_Ebinop with (v1:=Vint (Int.repr (ss_val (dst tran'))))
                     (v2:=Vint (Int.repr (ss_val ss'))). constructor. constructor. constructor. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Cne (Int.repr (ss_val (dst tran')))
                          (Int.repr (ss_val ss')) = false) as EQ3.
        simpl.
        apply false_negb.
        apply not_not_equal in H.
        rewrite H.
        apply Int.eq_true.
      rewrite EQ3.
      constructor.
Qed.

Lemma regvar_off_equal: forall ss' tge0 tb te tm tran',
      Int.repr (rv_off (ss_regvar (dst tran'))) = Int.repr (rv_off (ss_regvar ss')) ->
      eval_expr tge0 (Vptr tb Int.zero) te tm
        (Ebinop (Ocmp Ceq)
           (Econst (Ointconst (Int.repr (rv_off (ss_regvar (dst tran'))))))
           (Econst (Ointconst (Int.repr (rv_off (ss_regvar ss')))))) Vtrue.
Proof.
      intros ss' tge0 tb te tm tran' H.

      apply eval_Ebinop with (v1:=Vint (Int.repr (rv_off (ss_regvar (dst tran')))))
                     (v2:=Vint (Int.repr (rv_off (ss_regvar ss')))). constructor. constructor. constructor. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Ceq (Int.repr (rv_off (ss_regvar (dst tran')))) 
                          (Int.repr (rv_off (ss_regvar ss'))) = true) as EQ3.
        simpl.
        rewrite H.
        apply Int.eq_true.
      rewrite EQ3.
      constructor.
Qed.

Lemma NOT_regvar_off_equal: forall ss' tge0 tb te tm tran',
      Int.repr (rv_off (ss_regvar (dst tran'))) <> Int.repr (rv_off (ss_regvar ss')) ->
      eval_expr tge0 (Vptr tb Int.zero) te tm
        (Ebinop (Ocmp Ceq)
           (Econst (Ointconst (Int.repr (rv_off (ss_regvar (dst tran'))))))
           (Econst (Ointconst (Int.repr (rv_off (ss_regvar ss')))))) Vfalse.
Proof.
      intros ss' tge0 tb te tm tran' H.

      apply eval_Ebinop with (v1:=Vint (Int.repr (rv_off (ss_regvar (dst tran')))))
                     (v2:=Vint (Int.repr (rv_off (ss_regvar ss')))). constructor. constructor. constructor. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Ceq (Int.repr (rv_off (ss_regvar (dst tran')))) 
                          (Int.repr (rv_off (ss_regvar ss'))) = false) as EQ3.
        apply Int.eq_false.
        assumption.
      rewrite EQ3.
      constructor.
Qed.

Lemma regvar_mask_equal: forall ss' tge0 tb te tm tran',
      Int.repr (rv_mask (ss_regvar (dst tran'))) = Int.repr (rv_mask (ss_regvar ss')) ->
      eval_expr tge0 (Vptr tb Int.zero) te tm
        (Ebinop (Ocmp Ceq)
           (Econst (Ointconst (Int.repr (rv_mask (ss_regvar (dst tran'))))))
           (Econst (Ointconst (Int.repr (rv_mask (ss_regvar ss')))))) Vtrue.
Proof.
      intros ss' tge0 tb te tm tran' H.

      apply eval_Ebinop with (v1:=Vint (Int.repr (rv_mask (ss_regvar (dst tran')))))
                     (v2:=Vint (Int.repr (rv_mask (ss_regvar ss')))). constructor. constructor. constructor. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Ceq (Int.repr (rv_mask (ss_regvar (dst tran'))))
                          (Int.repr (rv_mask (ss_regvar ss'))) = true) as EQ3.
        simpl.
        rewrite H.
        apply Int.eq_true.
      rewrite EQ3.
      constructor.
Qed.

Lemma NOT_regvar_mask_equal: forall ss' tge0 tb te tm tran',
      Int.repr (rv_mask (ss_regvar (dst tran'))) <> Int.repr (rv_mask (ss_regvar ss')) ->
      eval_expr tge0 (Vptr tb Int.zero) te tm
        (Ebinop (Ocmp Ceq)
           (Econst (Ointconst (Int.repr (rv_mask (ss_regvar (dst tran'))))))
           (Econst (Ointconst (Int.repr (rv_mask (ss_regvar ss')))))) Vfalse.
Proof.
      intros ss' tge0 tb te tm tran' H.

      apply eval_Ebinop with (v1:=Vint (Int.repr (rv_mask (ss_regvar (dst tran')))))
                     (v2:=Vint (Int.repr (rv_mask (ss_regvar ss')))). constructor. constructor. constructor. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Ceq (Int.repr (rv_mask (ss_regvar (dst tran'))))
                          (Int.repr (rv_mask (ss_regvar ss'))) = false) as EQ3.
        apply Int.eq_false.
        assumption.
      rewrite EQ3.
      constructor.
Qed.

Lemma __L_is_tran_dst_inv_ss: forall ss' o rid roff rval m tge0 tb te tm tran',
      is_tran_dst_inv_ss tran' ss' o rid roff rval m ->
      eval_expr tge0 (Vptr tb Int.zero) te tm (C_is_tran_dst_inv_ss tran' ss')
        Vtrue.
Proof.
      intros ss' o rid roff rval m tge0 tb te tm tran' H.
      (* C_is_tran_dst_inv_ss start *)
      unfold C_is_tran_dst_inv_ss.
      unfold is_tran_dst_inv_ss in H.
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply reg_off_equal.
      assumption.
      apply val_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply regvar_off_equal.
      assumption.
      apply regvar_mask_equal.
      assumption.
      auto.
      auto.
      (* C_is_tran_dst_inv_ss end *)
Qed.

Lemma __L_NOT_is_tran_dst_inv_ss: forall ss' o rid roff rval m tge0 tb te tm tran',
      ~ is_tran_dst_inv_ss tran' ss' o rid roff rval m ->
      eval_expr tge0 (Vptr tb Int.zero) te tm (C_is_tran_dst_inv_ss tran' ss')
        Vfalse.
Proof.
      intros ss' o rid roff rval m tge0 tb te tm tran' H.

      unfold C_is_tran_dst_inv_ss.
      
      unfold is_tran_dst_inv_ss in H.
      apply not_four_and in H.

      destruct H.

      (** case 1 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply NOT_reg_off_equal.
      assumption.
      apply val_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply regvar_off_equal.
      assumption.
      apply regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 1 - end **)

      destruct H.

      (** case 2 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply reg_off_equal.
      assumption.
      apply NOT_val_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply regvar_off_equal.
      assumption.
      apply regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 2 - end **)

      destruct H.

      (** case 3 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply reg_off_equal.
      assumption.
      apply val_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply NOT_regvar_off_equal.
      assumption.
      apply regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 3 - end **)
      destruct H.

      (** case 4 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply reg_off_equal.
      assumption.
      apply val_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply regvar_off_equal.
      assumption.
      apply NOT_regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 4 - end **)
      destruct H.

      (** case 5 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply NOT_reg_off_equal.
      assumption.
      apply NOT_val_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply regvar_off_equal.
      assumption.
      apply regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 5 - end **)
      destruct H.

      (** case 6 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply NOT_reg_off_equal.
      assumption.
      apply val_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply NOT_regvar_off_equal.
      assumption.
      apply regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 6 - end **)
      destruct H.

      (** case 7 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply NOT_reg_off_equal.
      assumption.
      apply val_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply regvar_off_equal.
      assumption.
      apply NOT_regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 7 - end **)
      destruct H.

      (** case 8 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply reg_off_equal.
      assumption.
      apply NOT_val_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply NOT_regvar_off_equal.
      assumption.
      apply regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 8 - end **)
      destruct H.

      (** case 9 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply reg_off_equal.
      assumption.
      apply NOT_val_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply regvar_off_equal.
      assumption.
      apply NOT_regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 9 - end **)
      destruct H.

      (** case 10 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply reg_off_equal.
      assumption.
      apply val_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply NOT_regvar_off_equal.
      assumption.
      apply NOT_regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 10 - end **)
      destruct H.

      (** case 11 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply reg_off_equal.
      assumption.
      apply NOT_val_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply NOT_regvar_off_equal.
      assumption.
      apply NOT_regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 11 - end **)
      destruct H.

      (** case 12 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply NOT_reg_off_equal.
      assumption.
      apply val_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply NOT_regvar_off_equal.
      assumption.
      apply NOT_regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 12 - end **)
      destruct H.

      (** case 13 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply NOT_reg_off_equal.
      assumption.
      apply NOT_val_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply regvar_off_equal.
      assumption.
      apply NOT_regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 13 - end **)
      destruct H.

      (** case 14 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply NOT_reg_off_equal.
      assumption.
      apply NOT_val_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply NOT_regvar_off_equal.
      assumption.
      apply regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 14 - end **)

      (** case 15 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply NOT_reg_off_equal.
      assumption.
      apply NOT_val_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply NOT_regvar_off_equal.
      assumption.
      apply NOT_regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 15 - end **)
Qed.

Lemma __L_is_tran_dst_not_inv_ss: forall ss' o rid roff rval m tge0 tb te tm tran',
      is_tran_dst_not_inv_ss tran' ss' o rid roff rval m ->
      eval_expr tge0 (Vptr tb Int.zero) te tm (C_is_tran_dst_not_inv_ss tran' ss')
        Vtrue.
Proof.
      intros ss' o rid roff rval m tge0 tb te tm tran' H.
      (* C_is_tran_dst_inv_ss start *)
      unfold C_is_tran_dst_inv_ss.
      unfold is_tran_dst_inv_ss in H.
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply reg_off_equal.
      assumption.
      apply val_not_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply regvar_off_equal.
      assumption.
      apply regvar_mask_equal.
      assumption.
      auto.
      auto.
Qed.

Lemma __L_NOT_is_tran_dst_not_inv_ss: forall ss' o rid roff rval m tge0 tb te tm tran',
      ~ is_tran_dst_not_inv_ss tran' ss' o rid roff rval m ->
      eval_expr tge0 (Vptr tb Int.zero) te tm (C_is_tran_dst_not_inv_ss tran' ss')
        Vfalse.
Proof.
      intros ss' o rid roff rval m tge0 tb te tm tran' H.

      unfold C_is_tran_dst_inv_ss.
      
      unfold is_tran_dst_inv_ss in H.
      apply not_four_and in H.

      destruct H.

      (** case 1 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply NOT_reg_off_equal.
      assumption.
      apply val_not_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply regvar_off_equal.
      assumption.
      apply regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 1 - end **)
      destruct H.

      (** case 2 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply reg_off_equal.
      assumption.
      apply NOT_val_not_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply regvar_off_equal.
      assumption.
      apply regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 2 - end **)
      destruct H.

      (** case 3 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply reg_off_equal.
      assumption.
      apply val_not_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply NOT_regvar_off_equal.
      assumption.
      apply regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 3 - end **)
      destruct H.

      (** case 4 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply reg_off_equal.
      assumption.
      apply val_not_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply regvar_off_equal.
      assumption.
      apply NOT_regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 4 - end **)
      destruct H.

      (** case 5 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply NOT_reg_off_equal.
      assumption.
      apply NOT_val_not_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply regvar_off_equal.
      assumption.
      apply regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 5 - end **)
      destruct H.

      (** case 6 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply NOT_reg_off_equal.
      assumption.
      apply val_not_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply NOT_regvar_off_equal.
      assumption.
      apply regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 6 - end **)
      destruct H.

      (** case 7 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply NOT_reg_off_equal.
      assumption.
      apply val_not_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply regvar_off_equal.
      assumption.
      apply NOT_regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 7 - end **)
      destruct H.

      (** case 8 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply reg_off_equal.
      assumption.
      apply NOT_val_not_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply NOT_regvar_off_equal.
      assumption.
      apply regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 8 - end **)
      destruct H.

      (** case 9 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply reg_off_equal.
      assumption.
      apply NOT_val_not_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply regvar_off_equal.
      assumption.
      apply NOT_regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 9 - end **)
      destruct H.

      (** case 10 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply reg_off_equal.
      assumption.
      apply val_not_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply NOT_regvar_off_equal.
      assumption.
      apply NOT_regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 10 - end **)
      destruct H.

      (** case 11 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply reg_off_equal.
      assumption.
      apply NOT_val_not_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply NOT_regvar_off_equal.
      assumption.
      apply NOT_regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 11 - end **)
      destruct H.

      (** case 12 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply NOT_reg_off_equal.
      assumption.
      apply val_not_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply NOT_regvar_off_equal.
      assumption.
      apply NOT_regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 12 - end **)
      destruct H.

      (** case 13 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply NOT_reg_off_equal.
      assumption.
      apply NOT_val_not_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply regvar_off_equal.
      assumption.
      apply NOT_regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 13 - end **)
      destruct H.

      (** case 14 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply NOT_reg_off_equal.
      assumption.
      apply NOT_val_not_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply NOT_regvar_off_equal.
      assumption.
      apply regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 14 - end **)

      (** case 15 - start **)
      inversion H.
      inversion H1.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply NOT_reg_off_equal.
      assumption.
      apply NOT_val_not_equal.
      assumption.
      auto.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply NOT_regvar_off_equal.
      assumption.
      apply NOT_regvar_mask_equal.
      assumption.
      auto.
      auto.
      (** case 15 - end **)
Qed.

Lemma __L_is_tran_triggered: forall ss' o rid roff rval m tge0 tb te tm tran',
      Some (Vint rval) = te ! regaccess_val ->
      Some (Vint roff) = te ! regaccess_reg_off ->
      is_tran_triggered tran' ss' o rid roff rval m ->
      eval_expr tge0 (Vptr tb Int.zero) te tm (C_is_tran_event_triggered tran')
        Vtrue.
Proof.
      intros ss' o rid roff rval m tge0 tb te tm tran' MRVAL MROFF H.

      (* event_triggered start *)
      unfold C_is_tran_event_triggered.
            
      unfold is_tran_triggered in H.

      destruct (ev_type (evnt tran')).

      (* Case: ev_eq *)
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      inversion H.
      apply eval_Ebinop with (v1:=Vint (Int.repr (reg_off (rv_reg (ev_regvar (evnt tran')))))) (v2:=Vint roff). constructor. constructor. constructor. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Ceq (Int.repr (reg_off (rv_reg (ev_regvar (evnt tran'))))) roff = true) as EQ3.
        simpl.
        rewrite H0.
        apply Int.eq_true.
      rewrite EQ3.
      constructor.
      (* *)
      apply eval_Ebinop with (v1:=Vint (Int.repr (ev_val (evnt tran')))) (v2:=Val.shru (Val.and (Vint rval)
                                                      (Vint (Int.repr (rv_mask (ev_regvar (evnt tran'))))))
                                                      (Vint (Int.repr (rv_off (ev_regvar (evnt tran')))))).
      constructor. auto. 
      apply eval_Ebinop with (v1:=(Val.and (Vint rval) (Vint (Int.repr (rv_mask (ev_regvar (evnt tran')))))))
                             (v2:=(Vint (Int.repr (rv_off (ev_regvar (evnt tran')))))).
      apply eval_Ebinop with (v1:=Vint rval) (v2:=Vint (Int.repr (rv_mask (ev_regvar (evnt tran'))))).
      constructor. auto.
      constructor. constructor.
      unfold Val.and. unfold eval_binop. unfold Val.and.
      reflexivity.
      apply eval_Econst.
      auto.
      unfold eval_binop.
      reflexivity.
      inversion H.
      rewrite H1.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Ceq (Int.repr (ev_val (evnt tran'))) (Int.repr (ev_val (evnt tran'))) = true) as EQ3.
        simpl.
        apply Int.eq_true.
      rewrite EQ3.
      constructor.
      auto.

      (* Case: ev_ne *)
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      inversion H.
      apply eval_Ebinop with (v1:=Vint (Int.repr (reg_off (rv_reg (ev_regvar (evnt tran')))))) (v2:=Vint roff). constructor. constructor. constructor. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Ceq (Int.repr (reg_off (rv_reg (ev_regvar (evnt tran'))))) roff = true) as EQ3.
        simpl.
        rewrite H0.
        apply Int.eq_true.
      rewrite EQ3.
      constructor.
      (* *)
      apply eval_Ebinop with (v1:=Vint (Int.repr (ev_val (evnt tran')))) (v2:=Val.shru (Val.and (Vint rval)
                                                      (Vint (Int.repr (rv_mask (ev_regvar (evnt tran'))))))
                                                      (Vint (Int.repr (rv_off (ev_regvar (evnt tran')))))).
      constructor. auto. 
      apply eval_Ebinop with (v1:=(Val.and (Vint rval) (Vint (Int.repr (rv_mask (ev_regvar (evnt tran')))))))
                             (v2:=(Vint (Int.repr (rv_off (ev_regvar (evnt tran')))))).
      apply eval_Ebinop with (v1:=Vint rval) (v2:=Vint (Int.repr (rv_mask (ev_regvar (evnt tran'))))).
      constructor. auto.
      constructor. constructor.
      unfold Val.and. unfold eval_binop. unfold Val.and.
      reflexivity.
      apply eval_Econst.
      auto.
      unfold eval_binop.
      reflexivity.
      inversion H.
      apply val_remains_int_axiom in H1.
      inversion H1.
      inversion H2.
      rewrite H3.
      unfold eval_binop.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Cne (Int.repr (ev_val (evnt tran'))) x = true) as EQ3.
        simpl.
        apply true_negb.
        apply Int.eq_false.
        crush.
      rewrite EQ3.
      auto.
      apply dev_spec_ss_size.
      auto.
      (* event_triggered end *)
Qed.

Lemma __L_NOT_is_tran_triggered: forall ss' o rid roff rval m tge0 tb te tm tran',
      Some (Vint rval) = te ! regaccess_val ->
      Some (Vint roff) = te ! regaccess_reg_off ->
      ~ is_tran_triggered tran' ss' o rid roff rval m ->
      eval_expr tge0 (Vptr tb Int.zero) te tm (C_is_tran_event_triggered tran')
        Vfalse.
Proof.
      intros ss' o rid roff rval m tge0 tb te tm tran' MRVAL MROFF H.

      unfold C_is_tran_event_triggered.
            
      unfold is_tran_triggered in H.

      destruct (ev_type (evnt tran')).

      (* Case: ev_eq *)

      apply not_two_and in H.

      destruct H.

      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      inversion H.
      apply eval_Ebinop with (v1:=Vint (Int.repr (reg_off (rv_reg (ev_regvar (evnt tran')))))) (v2:=Vint roff). constructor. constructor. constructor. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Ceq (Int.repr (reg_off (rv_reg (ev_regvar (evnt tran'))))) roff = false) as EQ3.
        simpl.
        apply Int.eq_false.
        assumption.
      rewrite EQ3.
      constructor.
      (* *)
      apply eval_Ebinop with (v1:=Vint (Int.repr (ev_val (evnt tran')))) (v2:=Val.shru (Val.and (Vint rval)
                                                      (Vint (Int.repr (rv_mask (ev_regvar (evnt tran'))))))
                                                      (Vint (Int.repr (rv_off (ev_regvar (evnt tran')))))).
      constructor. auto. 
      apply eval_Ebinop with (v1:=(Val.and (Vint rval) (Vint (Int.repr (rv_mask (ev_regvar (evnt tran')))))))
                             (v2:=(Vint (Int.repr (rv_off (ev_regvar (evnt tran')))))).
      apply eval_Ebinop with (v1:=Vint rval) (v2:=Vint (Int.repr (rv_mask (ev_regvar (evnt tran'))))).
      constructor. auto.
      constructor. constructor.
      unfold Val.and. unfold eval_binop. unfold Val.and.
      reflexivity.
      apply eval_Econst.
      auto.
      unfold eval_binop.
      reflexivity.
      inversion H.
      rewrite H1.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Ceq (Int.repr (ev_val (evnt tran'))) (Int.repr (ev_val (evnt tran'))) = true) as EQ3.
        simpl.
        apply Int.eq_true.
      rewrite EQ3.
      constructor.
      auto.

      destruct H.

      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      inversion H.
      apply eval_Ebinop with (v1:=Vint (Int.repr (reg_off (rv_reg (ev_regvar (evnt tran')))))) (v2:=Vint roff). constructor. constructor. constructor. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Ceq (Int.repr (reg_off (rv_reg (ev_regvar (evnt tran'))))) roff = true) as EQ3.
        simpl.
        rewrite H0.
        apply Int.eq_true.
      rewrite EQ3.
      constructor.
      (* *)
      apply eval_Ebinop with (v1:=Vint (Int.repr (ev_val (evnt tran')))) (v2:=Val.shru (Val.and (Vint rval)
                                                      (Vint (Int.repr (rv_mask (ev_regvar (evnt tran'))))))
                                                      (Vint (Int.repr (rv_off (ev_regvar (evnt tran')))))).
      constructor. auto. 
      apply eval_Ebinop with (v1:=(Val.and (Vint rval) (Vint (Int.repr (rv_mask (ev_regvar (evnt tran')))))))
                             (v2:=(Vint (Int.repr (rv_off (ev_regvar (evnt tran')))))).
      apply eval_Ebinop with (v1:=Vint rval) (v2:=Vint (Int.repr (rv_mask (ev_regvar (evnt tran'))))).
      constructor. auto.
      constructor. constructor.
      unfold Val.and. unfold eval_binop. unfold Val.and.
      reflexivity.
      apply eval_Econst.
      auto.
      unfold eval_binop.
      reflexivity.
      inversion H.
      apply val_remains_int_axiom in H1.
      inversion H1.
      inversion H2.
      rewrite H3.
      unfold eval_binop.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Ceq (Int.repr (ev_val (evnt tran'))) x = false) as EQ3.
        simpl.
        apply Int.eq_false.
        crush.
      rewrite EQ3.

      constructor.

      apply dev_spec_ss_size.

      auto.

      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      inversion H.
      apply eval_Ebinop with (v1:=Vint (Int.repr (reg_off (rv_reg (ev_regvar (evnt tran')))))) (v2:=Vint roff). constructor. constructor. constructor. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Ceq (Int.repr (reg_off (rv_reg (ev_regvar (evnt tran'))))) roff = false) as EQ3.
        simpl.
        apply Int.eq_false.
        assumption.
      rewrite EQ3.
      constructor.
      (* *)
      apply eval_Ebinop with (v1:=Vint (Int.repr (ev_val (evnt tran')))) (v2:=Val.shru (Val.and (Vint rval)
                                                      (Vint (Int.repr (rv_mask (ev_regvar (evnt tran'))))))
                                                      (Vint (Int.repr (rv_off (ev_regvar (evnt tran')))))).
      constructor. auto. 
      apply eval_Ebinop with (v1:=(Val.and (Vint rval) (Vint (Int.repr (rv_mask (ev_regvar (evnt tran')))))))
                             (v2:=(Vint (Int.repr (rv_off (ev_regvar (evnt tran')))))).
      apply eval_Ebinop with (v1:=Vint rval) (v2:=Vint (Int.repr (rv_mask (ev_regvar (evnt tran'))))).
      constructor. auto.
      constructor. constructor.
      unfold Val.and. unfold eval_binop. unfold Val.and.
      reflexivity.
      apply eval_Econst.
      auto.
      unfold eval_binop.
      reflexivity.
      inversion H.
      apply val_remains_int_axiom in H1.
      inversion H1.
      inversion H2.
      rewrite H3.
      unfold eval_binop.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Ceq (Int.repr (ev_val (evnt tran'))) x = false) as EQ3.
        simpl.
        apply Int.eq_false.
        crush.
      rewrite EQ3.

      constructor.

      apply dev_spec_ss_size.

      auto.

      (* Case: ev_ne *)

      apply not_two_and in H.

      destruct H.

      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      inversion H.
      apply eval_Ebinop with (v1:=Vint (Int.repr (reg_off (rv_reg (ev_regvar (evnt tran')))))) (v2:=Vint roff). constructor. constructor. constructor. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto. (* rewrite H; constructor. *)
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Ceq (Int.repr (reg_off (rv_reg (ev_regvar (evnt tran'))))) roff = false) as EQ3.
        simpl.
        apply Int.eq_false.
        assumption.
      rewrite EQ3.
      constructor.
      (* *)
      apply eval_Ebinop with (v1:=Vint (Int.repr (ev_val (evnt tran')))) (v2:=Val.shru (Val.and (Vint rval)
                                                      (Vint (Int.repr (rv_mask (ev_regvar (evnt tran'))))))
                                                      (Vint (Int.repr (rv_off (ev_regvar (evnt tran')))))).
      constructor. auto. 
      apply eval_Ebinop with (v1:=(Val.and (Vint rval) (Vint (Int.repr (rv_mask (ev_regvar (evnt tran')))))))
                             (v2:=(Vint (Int.repr (rv_off (ev_regvar (evnt tran')))))).
      apply eval_Ebinop with (v1:=Vint rval) (v2:=Vint (Int.repr (rv_mask (ev_regvar (evnt tran'))))).
      constructor. auto.
      constructor. constructor.
      unfold Val.and. unfold eval_binop. unfold Val.and.
      reflexivity.
      apply eval_Econst.
      auto.
      unfold eval_binop.
      reflexivity.
      inversion H.
      apply val_remains_int_axiom in H1.
      inversion H1.
      inversion H2.
      rewrite H3.
      unfold eval_binop.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Cne (Int.repr (ev_val (evnt tran'))) x = true) as EQ3.
        simpl.
        apply true_negb.
        apply Int.eq_false.
        crush.
      rewrite EQ3.
      constructor.

      apply dev_spec_ss_size.

      auto.

      destruct H.

      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      inversion H.
      apply eval_Ebinop with (v1:=Vint (Int.repr (reg_off (rv_reg (ev_regvar (evnt tran')))))) (v2:=Vint roff). constructor. constructor. constructor. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Ceq (Int.repr (reg_off (rv_reg (ev_regvar (evnt tran'))))) roff = true) as EQ3.
        simpl.
        rewrite H0.
        apply Int.eq_true.
      rewrite EQ3.
      constructor.
      (* *)
      apply eval_Ebinop with (v1:=Vint (Int.repr (ev_val (evnt tran')))) (v2:=Val.shru (Val.and (Vint rval)
                                                      (Vint (Int.repr (rv_mask (ev_regvar (evnt tran'))))))
                                                      (Vint (Int.repr (rv_off (ev_regvar (evnt tran')))))).
      constructor. auto. 
      apply eval_Ebinop with (v1:=(Val.and (Vint rval) (Vint (Int.repr (rv_mask (ev_regvar (evnt tran')))))))
                             (v2:=(Vint (Int.repr (rv_off (ev_regvar (evnt tran')))))).
      apply eval_Ebinop with (v1:=Vint rval) (v2:=Vint (Int.repr (rv_mask (ev_regvar (evnt tran'))))).
      constructor. auto.
      constructor. constructor.
      unfold Val.and. unfold eval_binop. unfold Val.and.
      reflexivity.
      apply eval_Econst.
      auto.
      unfold eval_binop.
      reflexivity.
      inversion H.
      apply not_not_equal in H1.
      rewrite H1.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Cne (Int.repr (ev_val (evnt tran'))) (Int.repr (ev_val (evnt tran'))) = false) as EQ3.
        simpl.
        apply false_negb.
        apply Int.eq_true.
      rewrite EQ3.
      constructor.
      auto.


      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      inversion H.
      apply eval_Ebinop with (v1:=Vint (Int.repr (reg_off (rv_reg (ev_regvar (evnt tran')))))) (v2:=Vint roff). constructor. constructor. constructor. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Ceq (Int.repr (reg_off (rv_reg (ev_regvar (evnt tran'))))) roff = false) as EQ3.
        simpl.
        apply Int.eq_false.
        assumption.
      rewrite EQ3.
      constructor.
      (* *)
      apply eval_Ebinop with (v1:=Vint (Int.repr (ev_val (evnt tran')))) (v2:=Val.shru (Val.and (Vint rval)
                                                      (Vint (Int.repr (rv_mask (ev_regvar (evnt tran'))))))
                                                      (Vint (Int.repr (rv_off (ev_regvar (evnt tran')))))).
      constructor. auto. 
      apply eval_Ebinop with (v1:=(Val.and (Vint rval) (Vint (Int.repr (rv_mask (ev_regvar (evnt tran')))))))
                             (v2:=(Vint (Int.repr (rv_off (ev_regvar (evnt tran')))))).
      apply eval_Ebinop with (v1:=Vint rval) (v2:=Vint (Int.repr (rv_mask (ev_regvar (evnt tran'))))).
      constructor. auto.
      constructor. constructor.
      unfold Val.and. unfold eval_binop. unfold Val.and.
      reflexivity.
      apply eval_Econst.
      auto.
      unfold eval_binop.
      reflexivity.
      inversion H.
      apply not_not_equal in H1.
      rewrite H1.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Cne (Int.repr (ev_val (evnt tran'))) (Int.repr (ev_val (evnt tran'))) = false) as EQ3.
        simpl.
        apply false_negb.
        apply Int.eq_true.
      rewrite EQ3.
      constructor.
      auto.
Qed.

Lemma __L_sstate_already_in_target: forall ss' o rid roff rval m tge0 tb te tm tm' tf iomem_p,
      Some (Vptr o Int.zero) = te ! iomem_p ->
      Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
      mem_inj m tm' ->
      ss_in_target ss' o rid roff rval m ->
      eval_expr tge0 (Vptr tb Int.zero) te tm
        (C_sstate_already_in_target ss' iomem_p) Vtrue.
Proof.
      intros ss' o rid roff rval m tge0 tb te tm tm' tf iomem_p MPOM MFREE MINJ H.
           
      unfold ss_in_target in H.
      
      unfold C_sstate_already_in_target.

      apply eval_Ebinop with (v1:=Vint (Int.repr (ss_val ss')))
                             (v2:=Val.shru (Val.and (my_load_Mint8unsigned m o
                             (Int.unsigned (Int.repr (reg_off (rv_reg (ss_regvar ss'))))))
                             (Vint (Int.repr (rv_mask (ss_regvar ss')))))
                             (Vint (Int.repr (rv_off (ss_regvar ss'))))).

      apply eval_Econst.
      crush.

      apply eval_Ebinop with (v1:=(Val.and (my_load_Mint8unsigned m o (Int.unsigned (Int.repr (reg_off (rv_reg (ss_regvar ss'))))))
                                           (Vint (Int.repr (rv_mask (ss_regvar ss'))))))
                             (v2:=(Vint (Int.repr (rv_off (ss_regvar ss'))))).

      apply eval_Ebinop with (v1:=(my_load_Mint8unsigned m o
        (Int.unsigned (Int.repr (reg_off (rv_reg (ss_regvar ss'))))))) (v2:=Vint (Int.repr (rv_mask (ss_regvar ss')))).

      apply __L_Eload with (tm':=tm') (tf:=tf) (m:=m) (o:=o); repeat( assumption ).
      apply mem_load_equal.
      apply eval_Econst.
      crush.
      crush.
      apply eval_Econst.
      crush.
      unfold eval_binop; reflexivity.
      
      unfold eval_binop.

      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      rewrite <- H. simpl. 
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      simpl. auto. 
      assert (Int.eq (Int.repr (ss_val ss')) (Int.repr (ss_val ss')) = true) as EQ3.
        simpl.
        apply Int.eq_true.
      rewrite EQ3.
      constructor.
Qed.

Lemma remove_Some: forall (val1 val2: val), (val1 = val2) -> (Some val1 = Some val2).
Proof.
       intros.
       crush.
Qed.

Lemma remove_Vint: forall (val1 val2: int), (Vint val1 <> Vint val2) -> (val1 <> val2).
Proof.
       intros.
       crush.
Qed.

Lemma helper6: forall (val1 val2: int), ((Vint val1) <> (Vint val2)) ->  (Val.cmp Ceq (Vint val1) (Vint val2) = Vfalse).
Proof.
      intros.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      apply remove_Vint in H.
      apply Int.eq_false in H.
      unfold Int.cmp.
      rewrite H.
      auto.
Qed.

Lemma __L_NOT_sstate_already_in_target: forall ss' o rid roff rval m tge0 tb te tm tm' tf iomem_p,
      Some (Vptr o Int.zero) = te ! iomem_p ->
      Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
      mem_inj m tm' ->
      ~ ss_in_target ss' o rid roff rval m ->
      eval_expr tge0 (Vptr tb Int.zero) te tm
        (C_sstate_already_in_target ss' iomem_p) Vfalse.
Proof.
      intros ss' o rid roff rval m tge0 tb te tm tm' tf iomem_p MPOM MFREE MINJ H.
           
      apply ss_not_target_axiom in H.

      unfold NOT_ss_in_target in H.
      unfold C_sstate_already_in_target.

      apply eval_Ebinop with (v1:=Vint (Int.repr (ss_val ss')))
                             (v2:=Val.shru (Val.and (my_load_Mint8unsigned m o (Int.unsigned (Int.repr (reg_off (rv_reg (ss_regvar ss'))))))
                                 (Vint (Int.repr (rv_mask (ss_regvar ss')))))
                                 (Vint (Int.repr (rv_off (ss_regvar ss'))))).

      apply eval_Econst.
      crush.

      apply eval_Ebinop with (v1:=Val.and (my_load_Mint8unsigned m o (Int.unsigned (Int.repr (reg_off (rv_reg (ss_regvar ss'))))))
                                 (Vint (Int.repr (rv_mask (ss_regvar ss')))))
                             (v2:=Vint (Int.repr (rv_off (ss_regvar ss')))).
      apply eval_Ebinop with (v1:=(my_load_Mint8unsigned m o (Int.unsigned (Int.repr (reg_off (rv_reg (ss_regvar ss')))))))
                             (v2:=Vint (Int.repr (rv_mask (ss_regvar ss')))).

      apply __L_Eload with (tm':=tm') (tf:=tf) (m:=m) (o:=o); repeat( assumption ).
      apply mem_load_equal.
      
      eapply eval_Econst.
      crush.
      unfold eval_binop.
      reflexivity.
      apply eval_Econst.
      crush.
      unfold eval_binop.
      reflexivity.
      
      unfold eval_binop.
      apply remove_Some.
      unfold my_load_Mint8unsigned.
      unfold decode_val_Mint8unsigned.
      unfold my_load_Mint8unsigned in H.
      unfold decode_val_Mint8unsigned in H.
      unfold Val.and. unfold Val.shru.
      rewrite dev_spec_ss_size.
      apply helper6.

      unfold Val.and in H. unfold Val.shru in H.
      rewrite dev_spec_ss_size in H.
      assumption. 
Qed.

Lemma __L_is_tran_src_satisfied: forall ss' o rid roff rval m tge0 tb te tm tm' tf tran' iomem_p,
      Some (Vptr o Int.zero) = te ! iomem_p ->
      Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
      mem_inj m tm' ->
      is_tran_src_satisfied tran' ss' o rid roff rval m ->
      eval_expr tge0 (Vptr tb Int.zero) te tm
        (C_is_tran_src_satisfied tran' iomem_p) Vtrue.
Proof.
      (* src_satisfied start *)
      intros ss' o rid roff rval m tge0 tb te tm tm' tf tran' iomem_p MPOM MFREE MINJ H.

      unfold C_is_tran_src_satisfied.

      unfold is_tran_src_satisfied in H.
      apply expand_or in H.

      (** case 1 **)
      destruct H.

      inversion H.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vint (Int.repr (any_srcss (src tran')))) (v2:=Vint Int.zero).
                                                   constructor. constructor. constructor. auto.
      simpl. unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Cne (Int.repr (any_srcss (src tran'))) Int.zero = true) as EQ3.
        simpl.
        apply true_negb.
        apply Int.eq_false.
        assumption.
      rewrite EQ3.
      auto.

      apply __L_sstate_already_in_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat(assumption).

      auto.

      (** case 2 **)
      destruct H.

      inversion H.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vint (Int.repr (any_srcss (src tran')))) (v2:=Vint Int.zero).
                                                   constructor. constructor. constructor. auto.
      simpl. unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Cne (Int.repr (any_srcss (src tran'))) Int.zero = true) as EQ3.
        simpl.
        apply true_negb.
        apply Int.eq_false.
        assumption.
      rewrite EQ3.
      auto.

      apply __L_NOT_sstate_already_in_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat(assumption).
      auto.
      

      (** case 3 **)
      inversion H.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vint (Int.repr (any_srcss (src tran')))) (v2:=Vint Int.zero).
                                                   constructor. constructor. constructor. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Cne (Int.repr (any_srcss (src tran'))) Int.zero = false) as EQ3.
        simpl.
        apply false_negb.
        apply not_not_equal in H0.
        rewrite H0.
        apply Int.eq_true.
      rewrite EQ3.
      auto.

      apply __L_sstate_already_in_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); assumption.

      auto.

Qed.

Lemma __L_NOT_is_tran_src_satisfied: forall ss' o rid roff rval m tge0 tb te tm tm' tf tran' iomem_p,
      Some (Vptr o Int.zero) = te ! iomem_p ->
      Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
      mem_inj m tm' ->
      ~ is_tran_src_satisfied tran' ss' o rid roff rval m ->
      eval_expr tge0 (Vptr tb Int.zero) te tm
        (C_is_tran_src_satisfied tran' iomem_p) Vfalse.
Proof.
      intros ss' o rid roff rval m tge0 tb te tm tm' tf tran' iomem_p MPOM MFREE MINJ H.

      unfold C_is_tran_src_satisfied.

      unfold is_tran_src_satisfied in H.
      apply Classical_Prop.not_or_and in H.

      inversion H.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vint (Int.repr (any_srcss (src tran')))) (v2:=Vint Int.zero).
                                                   constructor. constructor. constructor. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl. auto.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Cne (Int.repr (any_srcss (src tran'))) Int.zero = false) as EQ3.
        simpl.
        apply false_negb.
        apply not_not_equal in H0.
        rewrite H0.
        apply Int.eq_true.
      rewrite EQ3.
      auto.

      apply __L_NOT_sstate_already_in_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat(assumption).
      auto.
Qed.

Lemma __NOT_will_sstate_tran_go_to_target: forall ss' o rid roff rval m tge0 tb te tm tm' tf tran' iomem_p,
      Some (Vptr o Int.zero) = te ! iomem_p ->
      Some (Vint rval) = te ! regaccess_val ->
      Some (Vint roff) = te ! regaccess_reg_off ->
      Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
      mem_inj m tm' ->
      ~
      (is_tran_dst_inv_ss tran' ss' o rid roff rval m /\
       is_tran_triggered tran' ss' o rid roff rval m /\
       is_tran_src_satisfied tran' ss' o rid roff rval m) ->
      eval_expr tge0 (Vptr tb Int.zero) te tm
        (Ebinop Oand
           (Ebinop Oand (C_is_tran_dst_inv_ss tran' ss')
              (C_is_tran_event_triggered tran'))
        (C_is_tran_src_satisfied tran' iomem_p)) Vfalse.
Proof.
      intros ss' o rid roff rval m tge0 tb te tm tm' tf tran' iomem_p MPOM MRVAL MROFF MFREE MINJ H.

      apply not_three_and in H.
      destruct H.
      (** case 1 - start **)
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).      
      inversion H.
      apply __L_NOT_is_tran_dst_inv_ss with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m).
      assumption.
      inversion H.
      inversion H1.
      apply __L_is_tran_triggered with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m); repeat( assumption ).
      auto.      
      inversion H.
      inversion H1.
      apply __L_is_tran_src_satisfied with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      auto.
      (** case 1 - end **)
      destruct H.
      (** case 2 - start **)
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).      
      inversion H.
      apply __L_is_tran_dst_inv_ss with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m).
      assumption.
      inversion H.
      inversion H1.
      apply __L_NOT_is_tran_triggered with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m); repeat( assumption ).
      auto.      
      inversion H.
      inversion H1.
      apply __L_is_tran_src_satisfied with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      auto.
      (** case 2 - end **)
      destruct H.
      (** case 3 - start **)
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).      
      inversion H.
      apply __L_is_tran_dst_inv_ss with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m).
      assumption.
      inversion H.
      inversion H1.
      apply __L_is_tran_triggered with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m); repeat( assumption ).
      auto.      
      inversion H.
      inversion H1.
      apply __L_NOT_is_tran_src_satisfied with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      auto.
      (** case 3 - end **)
      destruct H.
      (** case 4 - start **)
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).      
      inversion H.
      apply __L_NOT_is_tran_dst_inv_ss with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m); repeat( assumption ).
      inversion H.
      inversion H1.
      apply __L_NOT_is_tran_triggered with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m); repeat( assumption ).
      auto.      
      inversion H.
      inversion H1.
      apply __L_is_tran_src_satisfied with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      auto.
      (** case 4 - end **)
      destruct H.
      (** case 5 - start **)
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).      
      inversion H.
      apply __L_is_tran_dst_inv_ss with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m).
      assumption.
      inversion H.
      inversion H1.
      apply __L_NOT_is_tran_triggered with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m); repeat( assumption ).
      auto.      
      inversion H.
      inversion H1.
      apply __L_NOT_is_tran_src_satisfied with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      auto.
      (** case 5 - end **)
      destruct H.
      (** case 6 - start **)
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).      
      inversion H.
      apply __L_NOT_is_tran_dst_inv_ss with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m); repeat( assumption ).
      inversion H.
      inversion H1.
      apply __L_is_tran_triggered with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m); repeat( assumption ).
      auto.      
      inversion H.
      inversion H1.
      apply __L_NOT_is_tran_src_satisfied with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      auto.
      (** case 6 - end **)
      (** case 7 - start **)
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).      
      inversion H.
      apply __L_NOT_is_tran_dst_inv_ss with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m); repeat( assumption ).
      inversion H.
      inversion H1.
      apply __L_NOT_is_tran_triggered with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m); repeat( assumption ).
      auto.      
      inversion H.
      inversion H1.
      apply __L_NOT_is_tran_src_satisfied with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      auto.
      (** case 7 - end **)
Qed.

Lemma __NOT_will_sstate_tran_go_out_of_target: forall ss' o rid roff rval m tge0 tb te tm tm' tf tran' iomem_p,
      Some (Vptr o Int.zero) = te ! iomem_p ->
      Some (Vint rval) = te ! regaccess_val ->
      Some (Vint roff) = te ! regaccess_reg_off ->
      Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
      mem_inj m tm' ->
      ~
      (is_tran_dst_not_inv_ss tran' ss' o rid roff rval m /\
       is_tran_triggered tran' ss' o rid roff rval m /\
       is_tran_src_satisfied tran' ss' o rid roff rval m) ->
      eval_expr tge0 (Vptr tb Int.zero) te tm
        (Ebinop Oand
           (Ebinop Oand (C_is_tran_dst_not_inv_ss tran' ss')
              (C_is_tran_event_triggered tran'))
        (C_is_tran_src_satisfied tran' iomem_p)) Vfalse.
Proof.
      intros ss' o rid roff rval m tge0 tb te tm tm' tf tran' iomem_p MPOM MRVAL MROFF MFREE MINJ H.

      apply not_three_and in H.
      destruct H.
      (** case 1 - start **)
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).      
      inversion H.
      apply __L_NOT_is_tran_dst_not_inv_ss with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m).
      assumption.
      inversion H.
      inversion H1.
      apply __L_is_tran_triggered with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m); repeat( assumption ).
      auto.      
      inversion H.
      inversion H1.
      apply __L_is_tran_src_satisfied with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      auto.
      (** case 1 - end **)
      destruct H.
      (** case 2 - start **)
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).      
      inversion H.
      apply __L_is_tran_dst_not_inv_ss with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m).
      assumption.
      inversion H.
      inversion H1.
      apply __L_NOT_is_tran_triggered with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m); repeat( assumption ).
      auto.      
      inversion H.
      inversion H1.
      apply __L_is_tran_src_satisfied with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      auto.
      (** case 2 - end **)
      destruct H.
      (** case 3 - start **)
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).      
      inversion H.
      apply __L_is_tran_dst_not_inv_ss with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m).
      assumption.
      inversion H.
      inversion H1.
      apply __L_is_tran_triggered with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m); repeat( assumption ).
      auto.      
      inversion H.
      inversion H1.
      apply __L_NOT_is_tran_src_satisfied with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      auto.
      (** case 3 - end **)
      destruct H.
      (** case 4 - start **)
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).      
      inversion H.
      apply __L_NOT_is_tran_dst_not_inv_ss with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m).
      assumption.
      inversion H.
      inversion H1.
      apply __L_NOT_is_tran_triggered with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m); repeat( assumption ).
      auto.      
      inversion H.
      inversion H1.
      apply __L_is_tran_src_satisfied with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      auto.
      (** case 4 - end **)
      destruct H.
      (** case 5 - start **)
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).      
      inversion H.
      apply __L_is_tran_dst_not_inv_ss with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m).
      assumption.
      inversion H.
      inversion H1.
      apply __L_NOT_is_tran_triggered with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m); repeat( assumption ).
      auto.      
      inversion H.
      inversion H1.
      apply __L_NOT_is_tran_src_satisfied with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      auto.
      (** case 5 - end **)
      destruct H.
      (** case 6 - start **)
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).      
      inversion H.
      apply __L_NOT_is_tran_dst_not_inv_ss with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m).
      assumption.
      inversion H.
      inversion H1.
      apply __L_is_tran_triggered with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m); repeat( assumption ).
      auto.      
      inversion H.
      inversion H1.
      apply __L_NOT_is_tran_src_satisfied with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      auto.
      (** case 6 - end **)
      (** case 7 - start **)
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).      
      inversion H.
      apply __L_NOT_is_tran_dst_not_inv_ss with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m).
      assumption.
      inversion H.
      inversion H1.
      apply __L_NOT_is_tran_triggered with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m); repeat( assumption ).
      auto.      
      inversion H.
      inversion H1.
      apply __L_NOT_is_tran_src_satisfied with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      auto.
      (** case 7 - end **)
Qed.

Lemma __L_will_sstate_go_to_target: forall ss' o rid roff rval m i tge0 tb te tm tm' tf iomem_p,
      Some (Vptr o Int.zero) = te ! iomem_p ->
      Some (Vint rval) = te ! regaccess_val ->
      Some (Vint roff) = te ! regaccess_reg_off ->
      Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
      mem_inj m tm' ->
      will_ss_go_to_target (master_dev i) ss' o rid roff rval m ->
      eval_expr tge0 (Vptr tb Int.zero) te tm
        (C_will_sstate_go_to_target ss' (trans (master_dev i)) iomem_p) Vtrue.
Proof.
      intros ss' o rid roff rval m i tge0 tb te tm tm' tf iomem_p MPOM MRVAL MROFF MFREE  MINJ H.

      unfold will_ss_go_to_target in H.
      
      induction trans as [|tran' trans'].
      crush.
      apply exists_in_list in H.

      destruct H.

      (** first case - start **)
      inversion H.
      unfold C_will_sstate_go_to_target.
      fold C_will_sstate_go_to_target.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).      
      inversion H0.
      apply __L_is_tran_dst_inv_ss with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m).
      assumption.
      inversion H0.
      inversion H3.
      apply __L_is_tran_triggered with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m); repeat( assumption ).
      auto.      
      inversion H0.
      inversion H3.
      apply __L_is_tran_src_satisfied with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      auto.  
      inversion H.
      unfold C_will_sstate_go_to_target.
      rewrite H3.
      unfold C_will_sstate_go_to_target.
      apply eval_Econst.
      auto.
      auto.
      (** first case - end **)

      destruct H.

      (** second case - start **)
      inversion H.
      inversion H1.
      unfold C_will_sstate_go_to_target.
      fold C_will_sstate_go_to_target.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).      
      inversion H0.
      apply __L_is_tran_dst_inv_ss with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m).
      assumption.
      inversion H0.
      inversion H5.
      apply __L_is_tran_triggered with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m); repeat( assumption ).
      auto.      
      inversion H0.
      inversion H5.
      apply __L_is_tran_src_satisfied with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      auto.         
      apply IHtrans'.
      assumption.
      auto.
      (** second case - end **)

      destruct H.

      (** third case - start **)
      inversion H.
      inversion H1.
      unfold C_will_sstate_go_to_target.
      fold C_will_sstate_go_to_target.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).      
      inversion H0.
      apply __L_is_tran_dst_inv_ss with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m).
      assumption.
      inversion H0.
      inversion H5.
      apply __L_is_tran_triggered with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m); repeat( assumption ).
      auto.      
      inversion H0.
      inversion H5.
      apply __L_is_tran_src_satisfied with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      auto.
      clear IHtrans'.
      clear H.
      clear H0.
      clear H1.
      clear H2.
      induction trans' as [|tran'' trans''].
      unfold C_will_sstate_go_to_target.
      apply eval_Econst.
      auto.
      unfold C_will_sstate_go_to_target.
      fold C_will_sstate_go_to_target.
      apply forall_in_list2 in H3.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply __NOT_will_sstate_tran_go_to_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      apply IHtrans''.
      assumption.
      auto.
      auto.
      (** third case - end **)

      (** fourth case - start **)
      inversion H.
      inversion H1.
      unfold C_will_sstate_go_to_target.
      fold C_will_sstate_go_to_target.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply __NOT_will_sstate_tran_go_to_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      apply IHtrans'.
      assumption.
      auto.
      (** fourth case - end **)
Qed.

Lemma __L_NOT_will_sstate_go_to_target: forall ss' o rid roff rval m i tge0 tb te tm tm' tf iomem_p,
      Some (Vptr o Int.zero) = te ! iomem_p ->
      Some (Vint rval) = te ! regaccess_val ->
      Some (Vint roff) = te ! regaccess_reg_off ->
      Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
      mem_inj m tm' ->
      ~ will_ss_go_to_target (master_dev i) ss' o rid roff rval m ->
      eval_expr tge0 (Vptr tb Int.zero) te tm
        (C_will_sstate_go_to_target ss' (trans (master_dev i)) iomem_p) Vfalse.
Proof.
      intros ss' o rid roff rval m i tge0 tb te tm tm' tf iomem_p MPOM MRVAL MROFF MFREE MINJ H.

      apply will_not_go_to_target_axiom in H.

      unfold NOT_will_ss_go_to_target in H.

      induction trans as [|tran' trans'].

      unfold C_will_sstate_go_out_of_target.
      apply eval_Econst.
      auto.

      destruct H.
      crush.

      unfold C_will_sstate_go_to_target.
      fold C_will_sstate_go_to_target.

      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply forall_in_list2 in H.
      inversion H.
      apply __NOT_will_sstate_tran_go_to_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).

      apply IHtrans'.
      right.
      apply forall_in_list2 in H.
      inversion H.
      assumption.
      auto.
Qed.

Lemma __L_will_sstate_go_out_of_target: forall ss' o rid roff rval m i tge0 tb te tm tm' tf iomem_p,
      Some (Vptr o Int.zero) = te ! iomem_p ->
      Some (Vint rval) = te ! regaccess_val ->
      Some (Vint roff) = te ! regaccess_reg_off ->
      Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
      mem_inj m tm' ->
      will_ss_go_out_of_target (slave_dev i) ss' o rid roff rval m ->
      eval_expr tge0 (Vptr tb Int.zero) te tm
        (C_will_sstate_go_out_of_target ss' (trans (slave_dev i)) iomem_p) Vtrue.
Proof.
      intros ss' o rid roff rval m i tge0 tb te tm tm' tf iomem_p MPOM MRVAL MROFF MFREE MINJ H.

      unfold will_ss_go_out_of_target in H.
      
      induction trans as [|tran' trans'].
      crush.

      apply exists_in_list in H.

      destruct H.

      (** first case - start **)
      inversion H.
      unfold C_will_sstate_go_to_target.
      fold C_will_sstate_go_to_target.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).      
      inversion H0.
      apply __L_is_tran_dst_not_inv_ss with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m).
      assumption.
      inversion H0.
      inversion H3.
      apply __L_is_tran_triggered with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m); repeat( assumption ).
      auto.      
      inversion H0.
      inversion H3.
      apply __L_is_tran_src_satisfied with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      auto.            
      inversion H.
      unfold C_will_sstate_go_to_target.
      rewrite H3.
      unfold C_will_sstate_go_to_target.
      apply eval_Econst.
      auto.
      auto.
      (** first case - end **)

      destruct H.

      (** second case - start **)
      inversion H.
      inversion H1.
      unfold C_will_sstate_go_to_target.
      fold C_will_sstate_go_to_target.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      inversion H0.
      apply __L_is_tran_dst_not_inv_ss with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m).
      assumption.
      inversion H0.
      inversion H5.
      apply __L_is_tran_triggered with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m); repeat( assumption ).
      auto.      
      inversion H0.
      inversion H5.
      apply __L_is_tran_src_satisfied with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      auto.         
      apply IHtrans'.
      assumption.
      auto.
      (** second case - end **)

      destruct H.

      (** third case - start **)
      inversion H.
      inversion H1.
      unfold C_will_sstate_go_to_target.
      fold C_will_sstate_go_to_target.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).      
      inversion H0.
      apply __L_is_tran_dst_not_inv_ss with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m).
      assumption.
      inversion H0.
      inversion H5.
      apply __L_is_tran_triggered with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m); repeat( assumption ).
      auto.      
      inversion H0.
      inversion H5.
      apply __L_is_tran_src_satisfied with (ss':=ss') (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      auto.
      clear IHtrans'.
      clear H H0 H1 H2.
      induction trans' as [|tran'' trans''].
      unfold C_will_sstate_go_to_target.
      apply eval_Econst.
      auto.
      unfold C_will_sstate_go_to_target.
      fold C_will_sstate_go_to_target.
      apply forall_in_list2 in H3.
      inversion H3.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply __NOT_will_sstate_tran_go_out_of_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      apply IHtrans''.
      assumption.
      auto.
      auto.
      (** third case - end **)

      (** fourth case - start **)
      inversion H.
      inversion H1.
      unfold C_will_sstate_go_to_target.
      fold C_will_sstate_go_to_target.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply __NOT_will_sstate_tran_go_out_of_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      apply IHtrans'.
      assumption.
      auto.
      (** fourth case - end **)
Qed.

Lemma __L_NOT_will_sstate_go_out_of_target: forall ss' o rid roff rval m i tge0 tb te tm tm' tf iomem_p,
      Some (Vptr o Int.zero) = te ! iomem_p ->
      Some (Vint rval) = te ! regaccess_val ->
      Some (Vint roff) = te ! regaccess_reg_off ->
      Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
      mem_inj m tm' ->
      ~ will_ss_go_out_of_target (slave_dev i) ss' o rid roff rval m ->
      eval_expr tge0 (Vptr tb Int.zero) te tm
        (C_will_sstate_go_out_of_target ss' (trans (slave_dev i)) iomem_p) Vfalse.
Proof.
      intros ss' o rid roff rval m i tge0 tb te tm tm' tf iomem_p MPOM MRVAL MROFF MFREE MINJ H.

      apply will_not_go_out_of_target_axiom in H.

      unfold NOT_will_ss_go_out_of_target in H.

      induction trans as [|tran' trans'].

      unfold C_will_sstate_go_out_of_target.
      apply eval_Econst.
      auto.

      destruct H.
      crush.

      unfold C_will_sstate_go_out_of_target.
      fold C_will_sstate_go_out_of_target.

      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
            apply forall_in_list2 in H.
      inversion H.
      apply __NOT_will_sstate_tran_go_out_of_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).

      apply IHtrans'.
      right.
      apply forall_in_list2 in H.
      inversion H.
      assumption.
      auto.
Qed.

Lemma __L_will_dev_go_target_state: forall ss' o rid roff rval m i tge tb te tm tm' tf iomem_p,
      Some (Vptr o Int.zero) = te ! iomem_p ->
      Some (Vint rval) = te ! regaccess_val ->
      Some (Vint roff) = te ! regaccess_reg_off ->
      Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
      mem_inj m tm' ->
      ss_in_target ss' o rid roff rval m /\ will_ss_go_to_target (master_dev i) ss' o rid roff rval m ->
      eval_expr tge (Vptr tb Int.zero) te tm
        (Ebinop Oor
           (C_will_sstate_go_to_target ss' (trans (master_dev i)) iomem_p)
           (C_sstate_already_in_target ss' iomem_p)) Vtrue.
Proof.
      intros ss' o rid roff rval m i tge0 tb te tm tm' tf iomem_p MPOM MRVAL MROFF MFREE MINJ H.

      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      inversion H.

      apply __L_will_sstate_go_to_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).

      inversion H.

      apply __L_sstate_already_in_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).

      auto.
Qed.

Lemma __L_will_dev_go_target_state2: forall ss' o rid roff rval m i tge tb te tm tm' tf iomem_p,
      Some (Vptr o Int.zero) = te ! iomem_p ->
      Some (Vint rval) = te ! regaccess_val ->
      Some (Vint roff) = te ! regaccess_reg_off ->
      Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
      mem_inj m tm' ->
      ss_in_target ss' o rid roff rval m /\ ~ will_ss_go_to_target (master_dev i) ss' o rid roff rval m ->
      eval_expr tge (Vptr tb Int.zero) te tm
        (Ebinop Oor
           (C_will_sstate_go_to_target ss' (trans (master_dev i)) iomem_p)
           (C_sstate_already_in_target ss' iomem_p)) Vtrue.
Proof.
      intros ss' o rid roff rval m i tge0 tb te tm tm' tf iomem_p MPOM MRVAL MROFF MFREE MINJ H.

      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      inversion H.

      apply __L_NOT_will_sstate_go_to_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).

      inversion H.

      apply __L_sstate_already_in_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).

      auto.
Qed.

Lemma __L_will_dev_go_target_state3: forall ss' o rid roff rval m i tge tb te tm tm' tf iomem_p,
      Some (Vptr o Int.zero) = te ! iomem_p ->
      Some (Vint rval) = te ! regaccess_val ->
      Some (Vint roff) = te ! regaccess_reg_off ->
      Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
      mem_inj m tm' ->
      ~ ss_in_target ss' o rid roff rval m /\ will_ss_go_to_target (master_dev i) ss' o rid roff rval m ->
      eval_expr tge (Vptr tb Int.zero) te tm
        (Ebinop Oor
           (C_will_sstate_go_to_target ss' (trans (master_dev i)) iomem_p)
           (C_sstate_already_in_target ss' iomem_p)) Vtrue.
Proof.
      intros ss' o rid roff rval m i tge0 tb te tm tm' tf iomem_p MPOM MRVAL MROFF MFREE MINJ H.

      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      inversion H.

      apply __L_will_sstate_go_to_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).

      inversion H.

      apply __L_NOT_sstate_already_in_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      auto.
Qed.

Lemma __L_will_dev_go_target_state4: forall ss' o rid roff rval m i tge tb te tm tm' tf iomem_p,
      Some (Vptr o Int.zero) = te ! iomem_p ->
      Some (Vint rval) = te ! regaccess_val ->
      Some (Vint roff) = te ! regaccess_reg_off ->
      Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
      mem_inj m tm' ->
      ss_in_target ss' o rid roff rval m \/ will_ss_go_to_target (master_dev i) ss' o rid roff rval m ->
      eval_expr tge (Vptr tb Int.zero) te tm
        (Ebinop Oor
           (C_will_sstate_go_to_target ss' (trans (master_dev i)) iomem_p)
           (C_sstate_already_in_target ss' iomem_p)) Vtrue.
Proof.
      intros ss' o rid roff rval m i tge0 tb te tm tm' tf iomem_p MPOM MRVAL MROFF MFREE MINJ H.

      apply expand_or in H.
      destruct H.

      apply __L_will_dev_go_target_state with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).

      destruct H.

      apply __L_will_dev_go_target_state2 with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).

      apply __L_will_dev_go_target_state3 with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
Qed.

Lemma __L_NOT_will_dev_go_target_state: forall ss' o rid roff rval m i tge tb te tm tm' tf iomem_p,
      Some (Vptr o Int.zero) = te ! iomem_p ->
      Some (Vint rval) = te ! regaccess_val ->
      Some (Vint roff) = te ! regaccess_reg_off ->
      Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
      mem_inj m tm' ->
      ~ ss_in_target ss' o rid roff rval m /\ ~ will_ss_go_to_target (master_dev i) ss' o rid roff rval m ->
      eval_expr tge (Vptr tb Int.zero) te tm
        (Ebinop Oor
           (C_will_sstate_go_to_target ss' (trans (master_dev i)) iomem_p)
           (C_sstate_already_in_target ss' iomem_p)) Vfalse.
Proof.
      intros ss' o rid roff rval m i tge0 tb te tm tm' tf iomem_p MPOM MRVAL MROFF MFREE MINJ H.

      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      inversion H.

      apply __L_NOT_will_sstate_go_to_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).

      inversion H.

      apply __L_NOT_sstate_already_in_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).

      auto.
Qed.

Lemma __L_will_dev_go_out_of_target_state: forall ss' o rid roff rval m i tge tb te tm tm' tf iomem_p,
      Some (Vptr o Int.zero) = te ! iomem_p ->
      Some (Vint rval) = te ! regaccess_val ->
      Some (Vint roff) = te ! regaccess_reg_off ->
      Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
      mem_inj m tm' ->
      ss_in_target ss' o rid roff rval m /\ will_ss_go_out_of_target (slave_dev i) ss' o rid roff rval m ->
      eval_expr tge (Vptr tb Int.zero) te tm
        (Ebinop Oand
           (C_will_sstate_go_out_of_target ss' (trans (slave_dev i)) iomem_p)
           (C_sstate_already_in_target ss' iomem_p)) Vtrue.
Proof.
      intros ss' o rid roff rval m i tge0 tb te tm tm' tf iomem_p MPOM MRVAL MROFF MFREE MINJ H.

      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      inversion H.

      apply __L_will_sstate_go_out_of_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).

      inversion H.

      apply __L_sstate_already_in_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).

      auto.
Qed.

Lemma __L_NOT_will_dev_go_out_of_target_state: forall ss' o rid roff rval m i tge tb te tm tm' tf iomem_p,
      Some (Vptr o Int.zero) = te ! iomem_p ->
      Some (Vint rval) = te ! regaccess_val ->
      Some (Vint roff) = te ! regaccess_reg_off ->
      Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
      mem_inj m tm' ->
      ~ (ss_in_target ss' o rid roff rval m /\ will_ss_go_out_of_target (slave_dev i) ss' o rid roff rval m) ->
      eval_expr tge (Vptr tb Int.zero) te tm
        (Ebinop Oand
           (C_will_sstate_go_out_of_target ss' (trans (slave_dev i)) iomem_p)
           (C_sstate_already_in_target ss' iomem_p)) Vfalse.
Proof.
      intros ss' o rid roff rval m i tge0 tb te tm tm' tf iomem_p MPOM MRVAL MROFF MFREE MINJ H.

      apply not_two_and in H.

      destruct H.

      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      inversion H.

      apply __L_will_sstate_go_out_of_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).

      inversion H.

      apply __L_NOT_sstate_already_in_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).

      auto.

      destruct H.

      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      inversion H.

      apply __L_NOT_will_sstate_go_out_of_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).

      inversion H.

      apply __L_sstate_already_in_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).

      auto.

      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      inversion H.

      apply __L_NOT_will_sstate_go_out_of_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).

      inversion H.

      apply __L_NOT_sstate_already_in_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval) (m:=m) (tm':=tm') (tf:=tf); repeat( assumption ).
      auto.
Qed.

Lemma L_is_valid_dev_access: forall roff regs tge tb te tm,
             Some (Vint roff) = te ! regaccess_reg_off ->
             In roff (map reg_to_int regs) ->
             eval_expr tge (Vptr tb Int.zero) te tm
               (C_is_valid_dev_access regs) Vtrue.
Proof.
      intros roff regs tge0 tb te tm MROFF H.

      induction regs as [|reg regs'].
      inversion H.

      (* destruct H. *)
      apply exists_in_list_map in H.
      
      destruct H.
      inversion H.

      unfold C_is_valid_dev_access.
      unfold reg_to_int in H0.
      rewrite <- H0.

      fold C_is_valid_dev_access.

      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vint roff) (v2:=Vint roff). constructor. auto. constructor. constructor.
      simpl. unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Ceq roff roff = true) as EQ3.
        simpl.
        apply Int.eq_true.
      rewrite EQ3.
      auto.

      apply IHregs'.
      assumption.

      auto.
      destruct H.
      inversion H.
      unfold C_is_valid_dev_access.
      unfold reg_to_int in H0.
      rewrite <- H0.

      fold C_is_valid_dev_access.

      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      apply eval_Ebinop with (v1:=Vint roff) (v2:=Vint roff). constructor. auto. constructor. constructor.
      simpl. unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Ceq roff roff = true) as EQ3.
        simpl.
        apply Int.eq_true.
      rewrite EQ3.
      auto.

      (* Proof for: ~ In roff (map reg_to_int regs') -> eval_expr tge (Vptr tb Int.zero) te tm (C_is_valid_dev_access regs') Vfalse *)
      (* start *)

      apply invalid_access with (roff:=roff); repeat( assumption ).
      auto.

      (* end *)
      
      unfold C_is_valid_dev_access.
      inversion H.
      unfold reg_to_int in H0.      

      fold C_is_valid_dev_access.

      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply eval_Ebinop with (v1:=Vint roff) (v2:=Vint (Int.repr (reg_off reg))). constructor. auto. constructor. constructor.
      simpl. unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Ceq roff (Int.repr (reg_off reg)) = false) as EQ3.
        simpl.
        apply Int.eq_false.
        assumption.
      rewrite EQ3.
      auto.

      apply IHregs'.
      assumption.
 
      auto.
Qed.

Lemma not_in_list_map: forall roff reg regs', ~ In roff (map reg_to_int (reg :: regs')) ->
                             roff <> reg_to_int reg /\ ~ In roff (map reg_to_int regs').
Proof.
  intros.
  apply conj; crush.
Qed.

Lemma L_NOT_is_valid_dev_access: forall roff regs tge tb te tm,
             Some (Vint roff) = te ! regaccess_reg_off ->
             ~ In roff (map reg_to_int regs) ->
             eval_expr tge (Vptr tb Int.zero) te tm
               (C_is_valid_dev_access regs) Vfalse.
Proof.
      intros roff regs tge0 tb te tm MROFF H.

      induction regs as [|reg regs'].
      unfold C_is_valid_dev_access.
      apply eval_Econst.
      auto.

      apply not_in_list_map in H.
      inversion H.

      unfold C_is_valid_dev_access.
      fold C_is_valid_dev_access.

      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).

      apply eval_Ebinop with (v1:=Vint roff) (v2:=Vint (reg_to_int reg)). constructor. auto. constructor. constructor.
      simpl. unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool.
      assert (Int.cmp Ceq roff (reg_to_int reg) = false) as EQ3.
      simpl.
      apply Int.eq_false; assumption.
      rewrite EQ3.
      auto.

      apply IHregs'; assumption.
      auto.
Qed.

Lemma L_will_dev_go_target_state: forall i inv o rid roff rval m tge tb te tf tm tm' iomem_p,
             Some (Vptr o Int.zero) = te ! iomem_p ->
             Some (Vint rid) = te ! regaccess_dev_id ->
             Some (Vint roff) = te ! regaccess_reg_off ->
             Some (Vint rval) = te ! regaccess_val ->
             Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
             mem_inj m tm' ->
             will_go_to_target_state (master_dev i) inv o rid roff rval m ->
             eval_expr tge (Vptr tb Int.zero) te tm
               (C_will_dev_go_target_state (trans (master_dev i)) (inv_ss inv)
                  iomem_p) Vtrue.
Proof.
      intros i inv o rid roff rval m tge0 tb te tf tm tm' iomem_p MPOM MRID MROFF MRVAL MFREE MINJ H.

      (********** C_will_dev_go_target_state: start ************)

      unfold C_will_dev_go_target_state.
      
      unfold will_go_to_target_state in H.
      inversion H.

      induction inv_ss as [|ss' inv_ss'].

      unfold __C_will_dev_go_target_state.
      crush.

      (***************** start **********)
      unfold __C_will_dev_go_target_state.

      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).

      apply forall_in_list in H1.
      apply expand_or in H1.
      
      destruct H1.

      (* * * ss_in_target /\ will_ss_go_to_target - start * * *)
      apply __L_will_dev_go_target_state with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval)
                                              (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=iomem_p); repeat( assumption ).
      (* * * ss_in_target /\ will_ss_go_to_target - end * * *)
      
      destruct H1.

      (* * * ss_in_target /\ ~ will_ss_go_to_target - start * * *)
      apply __L_will_dev_go_target_state2 with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval)
                                               (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=iomem_p); repeat( assumption ).
      (* * * ss_in_target /\ ~ will_ss_go_to_target - end * * *)

      (* * * ~ ss_in_target /\ will_ss_go_to_target - start * * *)
      apply __L_will_dev_go_target_state3 with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval)
                                               (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=iomem_p); repeat( assumption ).
      (* * * ~ ss_in_target /\ will_ss_go_to_target - end * * *)

      (***************** end **********)

      destruct inv_ss' as [|ss'' inv_ss''].
      apply eval_Econst.
      auto.

      fold __C_will_dev_go_target_state.
    
      apply IHinv_ss'.
      apply conj.
      apply not_nil.
      intros.
      apply H.
      apply in_subset.
      assumption.
      apply not_nil.
      intros.
      apply H.
      apply in_subset.
      assumption.
      auto.
      (********** C_will_dev_go_target_state: end ************)
Qed.

Lemma L_NOT_will_dev_go_target_state: forall i inv o rid roff rval m tge tb te tf tm tm' iomem_p,
             Some (Vptr o Int.zero) = te ! iomem_p ->
             Some (Vint rid) = te ! regaccess_dev_id ->
             Some (Vint roff) = te ! regaccess_reg_off ->
             Some (Vint rval) = te ! regaccess_val ->
             Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
             mem_inj m tm' ->
             ~ will_go_to_target_state (master_dev i) inv o rid roff rval m ->
             eval_expr tge (Vptr tb Int.zero) te tm
               (C_will_dev_go_target_state (trans (master_dev i)) (inv_ss inv)
                  iomem_p) Vfalse.
Proof.
      intros i inv o rid roff rval m tge0 tb te tf tm tm' iomem_p MPOM MRID MROFF MRVAL MFREE MINJ H.

      apply will_dev_not_go_to_target_axiom in H.

      unfold NOT_will_go_to_target_state in H.

      apply my_or_or in H.
      destruct H.

      rewrite H.

      apply eval_Econst.
      auto.

      inversion H.
      
      inversion H.
      clear H H0 H1.

      assert (inv_ss inv <> [] /\
              exists ss: sstate, In ss (inv_ss inv) /\ ~ (ss_in_target ss o rid roff rval m \/
                                                will_ss_go_to_target (master_dev i) ss o rid roff rval m)) as H8.
      apply conj; repeat( assumption ).

      induction inv_ss as [|ss' inv_ss'].
      apply eval_Econst.
      auto.

      apply exists_in_list in H8.

      destruct H8.

      (**** first case start ****)

      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      inversion H.

      apply Classical_Prop.not_or_and in H0.
      inversion H0.
      
      apply __L_NOT_will_dev_go_target_state with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval)
                                                     (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=iomem_p); repeat( assumption ).

      inversion H.
      rewrite H1.
      apply eval_Econst.
      auto.
      auto.

      (**** first case end ****)
      destruct H.
      (**** second case start ****)

      inversion H.
      inversion H1.

      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      apply Classical_Prop.not_or_and in H0.
      inversion H0.

      apply __L_NOT_will_dev_go_target_state with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval)
                                                     (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=iomem_p); repeat( assumption ).

      fold __C_will_dev_go_target_state.
Lemma fold_C_will_dev_go_target_state: forall inv_ss' i iomem_p tb te tm tge0,
             inv_ss' <> [] /\ (eval_expr tge0 (Vptr tb Int.zero) te tm
                                 (C_will_dev_go_target_state (trans (master_dev i)) inv_ss'
                                    iomem_p) Vfalse) ->
             (eval_expr tge0 (Vptr tb Int.zero) te tm
                (__C_will_dev_go_target_state (trans (master_dev i)) inv_ss'
                   iomem_p) Vfalse).
Proof.
      intros inv_ss' i iomem_p tb te tm tge0 H.
      unfold C_will_dev_go_target_state in H.
      inversion H.
      destruct inv_ss' as [|ss'' inv_ss''].
      unfold __C_will_dev_go_target_state.
      crush.
      assumption.
Qed.
      apply fold_C_will_dev_go_target_state.
      apply conj.
      assumption.
      apply IHinv_ss'; repeat( assumption ).
      auto.
      (**** second case end ****)
      destruct H.
      (**** third case start ****)
      inversion H.
      inversion H1.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      apply Classical_Prop.not_or_and in H0.
      inversion H0.

      apply __L_NOT_will_dev_go_target_state with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval)
                                                     (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=iomem_p); repeat( assumption ).

      clear H1 H IHinv_ss' H2 H3 H4.
      induction inv_ss' as [|ss'' inv_ss''].
      apply eval_Econst.
      auto.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).
      
      apply __L_will_dev_go_target_state4 with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval)
                                                         (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=iomem_p); repeat( assumption ).
      assert (~ ~ (ss_in_target ss'' o rid roff rval m \/
                  will_ss_go_to_target (master_dev i) ss'' o rid roff rval m) ->
                  (ss_in_target ss'' o rid roff rval m \/
                  will_ss_go_to_target (master_dev i) ss'' o rid roff rval m)) as EQ3.
        intros.
        apply Classical_Prop.NNPP in H.
        assumption.
      apply EQ3.
      apply H5.
      crush.

      apply IHinv_ss''.
      apply forall_in_list2 in H5.
      inversion H5.
      assumption.
      auto.
      auto.
      (**** third case end ****)
      (**** fourth case start ****)
      inversion H.
      inversion H1.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      
      apply __L_will_dev_go_target_state4 with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval)
                                                     (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=iomem_p); repeat( assumption ).
      assert (~ ~ (ss_in_target ss' o rid roff rval m \/
                  will_ss_go_to_target (master_dev i) ss' o rid roff rval m) ->
                  (ss_in_target ss' o rid roff rval m \/
                  will_ss_go_to_target (master_dev i) ss' o rid roff rval m)) as EQ3.
        intros.
        apply Classical_Prop.NNPP in H6.
        assumption.
      apply EQ3.
      assumption.

      fold __C_will_dev_go_out_of_target_state.
      apply fold_C_will_dev_go_target_state.
      apply conj.
      assumption.
      apply IHinv_ss'; repeat( assumption ).
      auto.
      (**** fourth case end ****)
Qed.

Lemma L_will_dev_go_out_of_target_state: forall i inv o rid roff rval m tge tb te tf tm tm' iomem_p,
             Some (Vptr o Int.zero) = te ! iomem_p ->
             Some (Vint rid) = te ! regaccess_dev_id ->
             Some (Vint roff) = te ! regaccess_reg_off ->
             Some (Vint rval) = te ! regaccess_val ->
             Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
             mem_inj m tm' ->
             will_go_out_of_target_state (slave_dev i) inv o rid roff rval m ->
             eval_expr tge (Vptr tb Int.zero) te tm
               (C_will_dev_go_out_of_target_state (trans (slave_dev i))
                  (inv_ss inv) iomem_p) Vtrue.
Proof.
      intros i inv o rid roff rval m tge0 tb te tf tm tm' iomem_p MPOM MRID MROFF MRVAL MFREE MINJ H.

      (********** C_will_dev_go_out_of_target_state: start ************)
      unfold will_go_out_of_target_state in H.

      apply my_or_or in H.
      destruct H.

      rewrite H.

      apply eval_Econst.
      auto.

      inversion H.
      
      inversion H.
      clear H H0 H1.

      assert (inv_ss inv <> [] /\
              exists ss: sstate, In ss (inv_ss inv) /\ ss_in_target ss o rid roff rval m /\
                                                will_ss_go_out_of_target (slave_dev i) ss o rid roff rval m) as H8.
        apply conj; repeat( assumption ).

      induction inv_ss as [|ss' inv_ss'].
      apply eval_Econst.
      auto.

      apply exists_in_list in H8.

      destruct H8.

      (**** first case start ****)

      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).
      inversion H.
      
      apply __L_will_dev_go_out_of_target_state with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval)
                                                     (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=iomem_p); repeat( assumption ).

      inversion H.
      rewrite H1.
      apply eval_Econst.
      auto.
      auto.

      (**** first case end ****)
      destruct H.
      (**** second case start ****)

      inversion H.
      inversion H1.

      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).

      apply __L_will_dev_go_out_of_target_state with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval)
                                                     (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=iomem_p); repeat( assumption ).

      fold __C_will_dev_go_out_of_target_state.
Lemma fold_C_will_dev_go_out_of_target_state: forall inv_ss' i iomem_p tb te tm tge0,
             inv_ss' <> [] /\ (eval_expr tge0 (Vptr tb Int.zero) te tm
                                 (C_will_dev_go_out_of_target_state (trans (slave_dev i)) inv_ss'
                                    iomem_p) Vtrue) ->
             (eval_expr tge0 (Vptr tb Int.zero) te tm
                (__C_will_dev_go_out_of_target_state (trans (slave_dev i)) inv_ss'
                   iomem_p) Vtrue).
Proof.
      intros inv_ss' i iomem_p tb te tm tge0 H.
      unfold C_will_dev_go_out_of_target_state in H.
      inversion H.
      destruct inv_ss' as [|ss'' inv_ss''].
      unfold __C_will_dev_go_out_of_target_state.
      crush.
      assumption.
Qed.
      apply fold_C_will_dev_go_out_of_target_state.
      apply conj.
      assumption.
      apply IHinv_ss'.
      assumption.
      assumption.
      assumption.
      auto.
      (**** second case end ****)
      destruct H.
      (**** third case start ****)
      inversion H.
      inversion H1.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).

      apply __L_will_dev_go_out_of_target_state with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval)
                                                     (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=iomem_p); repeat( assumption ).

      clear H1 H IHinv_ss' H2 H3 H4.
      induction inv_ss' as [|ss'' inv_ss''].
      apply eval_Econst.
      auto.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).
      
      apply __L_NOT_will_dev_go_out_of_target_state with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval)
                                                         (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=iomem_p); repeat( assumption ).
      apply H5.
      crush.

      apply IHinv_ss''.
      apply forall_in_list2 in H5.
      inversion H5.
      assumption.
      auto.
      auto.
      (**** third case end ****)
      (**** fourth case start ****)
      inversion H.
      inversion H1.
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).
      
      apply __L_NOT_will_dev_go_out_of_target_state with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval)
                                                     (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=iomem_p); repeat( assumption ).

      fold __C_will_dev_go_out_of_target_state.
      apply fold_C_will_dev_go_out_of_target_state.
      apply conj.
      assumption.
      apply IHinv_ss'; repeat( assumption ).
      auto.
      (**** fourth case end ****)
Qed.

Lemma L_NOT_will_dev_go_out_of_target_state: forall i inv o rid roff rval m tge tb te tf tm tm' iomem_p,
             Some (Vptr o Int.zero) = te ! iomem_p ->
             Some (Vint rid) = te ! regaccess_dev_id ->
             Some (Vint roff) = te ! regaccess_reg_off ->
             Some (Vint rval) = te ! regaccess_val ->
             Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
             mem_inj m tm' ->
             ~ will_go_out_of_target_state (slave_dev i) inv o rid roff rval m ->
             eval_expr tge (Vptr tb Int.zero) te tm
               (C_will_dev_go_out_of_target_state (trans (slave_dev i))
                  (inv_ss inv) iomem_p) Vfalse.
Proof.
      intros i inv o rid roff rval m tge0 tb te tf tm tm' iomem_p MPOM MRID MROFF MRVAL MFREE MINJ H.

      apply will_dev_not_go_out_of_target_axiom in H.

      unfold NOT_will_go_out_of_target_state in H.
      inversion H.
      clear H.

      induction inv_ss as [|ss' inv_ss'].

      unfold C_will_dev_go_out_of_target_state.
      crush.

      (***************** start **********)
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).

      apply forall_in_list in H1.
      apply not_two_and in H1.
      
      destruct H1.

      (* * * ~ ss_in_target /\ will_ss_go_to_target - start * * *)
      inversion H.
      apply __L_NOT_will_dev_go_out_of_target_state with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval)
                                              (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=iomem_p); repeat( assumption ).
      apply Classical_Prop.or_not_and.
      left.
      assumption.

      (* * * ss_in_target /\ ~ will_ss_go_to_target - end * * *)
      
      destruct H.

      (* * * ~ ss_in_target /\ ~ will_ss_go_to_target - start * * *)
      inversion H.
      apply __L_NOT_will_dev_go_out_of_target_state with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval)
                                               (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=iomem_p); repeat( assumption ).
      apply  Classical_Prop.or_not_and.
      right.
      assumption.
      (* * * ss_in_target /\ ~ will_ss_go_to_target - end * * *)

      (* * * ~ ss_in_target /\ will_ss_go_to_target - start * * *)
      inversion H.
      apply __L_NOT_will_dev_go_out_of_target_state with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval)
                                              (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=iomem_p); repeat( assumption ).
      apply Classical_Prop.or_not_and.
      left.
      assumption.
      (* * * ~ ss_in_target /\ will_ss_go_to_target - end * * *)

      (***************** end **********)

      destruct inv_ss' as [|ss'' inv_ss''].
      apply eval_Econst.
      auto.

      fold __C_will_dev_go_out_of_target_state.
    
      apply IHinv_ss'.
      (* apply conj. *)
      apply not_nil.
      intros.
      apply H1.
      apply in_subset.
      assumption.
      auto.
Qed.

Lemma L_is_dev_in_target_state: forall i inv o rid roff rval m tge tb te tf tm tm' iomem_p,
             Some (Vptr o Int.zero) = te ! iomem_p ->
             Some (Vint rid) = te ! regaccess_dev_id ->
             Some (Vint roff) = te ! regaccess_reg_off ->
             Some (Vint rval) = te ! regaccess_val ->
             Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
             mem_inj m tm' ->
             is_in_target_state (master_dev i) inv o rid roff rval m ->
             eval_expr tge (Vptr tb Int.zero) te tm
               (C_is_dev_in_target_state iomem_p (inv_ss inv)) Vtrue.
Proof.
      intros i inv o rid roff rval m tge0 tb te tf tm tm' iomem_p MPOM MRID MROFF MRVAL MFREE MINJ H.

      unfold is_in_target_state in H.

      inversion H.

Lemma fold_C_is_dev_in_target_state2: forall inv_ss' iomem_p tb te tm tge0,
             inv_ss' <> [] /\ (eval_expr tge0 (Vptr tb Int.zero) te tm
                                 (__C_is_dev_in_target_state iomem_p inv_ss') Vtrue) ->
             (eval_expr tge0 (Vptr tb Int.zero) te tm
                (C_is_dev_in_target_state iomem_p inv_ss') Vtrue).
Proof.
      intros inv_ss' iomem_p tb te tm tge0 H.
      unfold C_is_dev_in_target_state in H.
      inversion H.
      destruct inv_ss' as [|ss'' inv_ss''].
      unfold __C_is_dev_in_target_state.
      crush.
      assumption.
Qed.
      apply fold_C_is_dev_in_target_state2.
      apply conj.
      assumption.
      clear H H0.

      induction inv_ss as [|ss inv_ss'].

      apply eval_Econst.
      auto.

      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).

      assert (ss_in_target ss o rid roff rval m) as EQ2.
        apply H1.
        crush.

      (*****************)
      unfold ss_in_target in EQ2.

      inversion EQ2.

      apply __L_sstate_already_in_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval)
                                              (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=iomem_p); repeat( assumption ).

      fold __C_is_dev_in_target_state.

      apply IHinv_ss'.

      intros.
      assert (In ss0 inv_ss' -> In ss0 (ss :: inv_ss')) as EQ2.
        crush.
      assert (In ss0 (ss :: inv_ss')) as EQ3.     
      apply EQ2.
      assumption.
      apply H1.
      assumption.

      auto.
Qed.

Lemma L_NOT_is_dev_in_target_state: forall i inv o rid roff rval m tge tb te tf tm tm' iomem_p,
             Some (Vptr o Int.zero) = te ! iomem_p ->
             Some (Vint rid) = te ! regaccess_dev_id ->
             Some (Vint roff) = te ! regaccess_reg_off ->
             Some (Vint rval) = te ! regaccess_val ->
             Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
             mem_inj m tm' ->
             ~ is_in_target_state (master_dev i) inv o rid roff rval m ->
             eval_expr tge (Vptr tb Int.zero) te tm
               (C_is_dev_in_target_state iomem_p (inv_ss inv)) Vfalse.
Proof.
      intros i inv o rid roff rval m tge0 tb te tf tm tm' iomem_p MPOM MRID MROFF MRVAL MFREE MINJ H.

      unfold is_in_target_state in H.

      apply Classical_Prop.not_and_or in H.
      apply my_or_or in H.
      destruct H.
      apply not_not_equal in H.
      rewrite H.

      apply eval_Econst.
      auto.
      inversion H.
      apply Classical_Prop.NNPP in H0.

      assert ((~ (forall ss : sstate, In ss (inv_ss inv) -> ss_in_target ss o rid roff rval m)) ->
              (exists ss,  In ss (inv_ss inv) /\  ~ ss_in_target ss o rid roff rval m)) as EQ3.
        intros.
        apply Classical_Pred_Type.not_all_ex_not in H2.
        inversion H2.
        exists x.
        apply imply_to_and in H3. assumption.

      apply EQ3 in H1.
      clear EQ3.

      assert (inv_ss inv <> [] /\
              exists ss : sstate, In ss (inv_ss inv) /\ ~ ss_in_target ss o rid roff rval m) as H8.
        apply conj; repeat (assumption).

      induction inv_ss as [|ss' inv_ss'].
      crush.
      
      apply exists_in_list_not_prop in H8.
      destruct H8.
      inversion H.

      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).

      fold C_sstate_already_in_target.
      unfold ss_in_target in H1.

      apply __L_NOT_sstate_already_in_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval)
                   (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=iomem_p); repeat( assumption ).
     
      inversion H2. assumption.
      inversion H2.
      rewrite H6.
      unfold C_is_dev_in_target_state.
      apply eval_Econst.
      auto.
      auto.

      destruct H2.

      inversion H2.
      inversion H4.

      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).

      apply __L_NOT_sstate_already_in_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval)
                                                  (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=iomem_p); repeat( assumption ).

      fold __C_is_dev_in_target_state.

Lemma fold_C_is_dev_in_target_state: forall inv_ss' iomem_p tb te tm tge0,
             inv_ss' <> [] /\ (eval_expr tge0 (Vptr tb Int.zero) te tm
                                 (C_is_dev_in_target_state iomem_p inv_ss') Vfalse) ->
             (eval_expr tge0 (Vptr tb Int.zero) te tm
                (__C_is_dev_in_target_state iomem_p inv_ss') Vfalse).
Proof.
      intros inv_ss' s_iomem_p tb te tm tge0 H.
      unfold C_is_dev_in_target_state in H.
      inversion H.
      destruct inv_ss' as [|ss'' inv_ss''].
      unfold __C_is_dev_in_target_state.
      crush.
      assumption.
Qed.
      apply fold_C_is_dev_in_target_state.
      apply conj.
      assumption.

      apply IHinv_ss'.
      constructor. 
      apply PNNP. assumption.
      apply Classical_Pred_Type.ex_not_not_all.
      inversion H6. exists x.
      revert H7. apply remove_not2. intros H7.
      apply NNPP in H7.
      apply or_not_and. apply imply_to_or in H7.
      destruct H7. left. assumption. right. apply PNNP.  assumption. assumption. auto. auto. auto. 

      destruct H2.

      inversion H2.
      inversion H4.

      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).

      apply __L_NOT_sstate_already_in_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval)
                                                  (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=iomem_p); repeat( assumption ).

      clear IHinv_ss'.
      clear H H0 H1 H2 H3 H4 H5.
      induction inv_ss' as [|ss'' inv_ss''].
      unfold C_is_dev_in_target_state.
      apply eval_Econst.
      auto.
      unfold C_is_dev_in_target_state.
      fold C_is_dev_in_target_state.
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).

      assert (ss_in_target ss'' o rid roff rval m) as EQ2.
         apply H6.
         crush.

      apply __L_sstate_already_in_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval)
                                              (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=iomem_p); repeat( assumption ).

      apply IHinv_ss''.
      crush.
      auto.
      auto.

      inversion H2.
      inversion H4.

      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).

      (*****************)
      unfold ss_in_target in H3.


      apply __L_sstate_already_in_target with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval)
                                              (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=iomem_p); repeat( assumption ).

      fold __C_is_dev_in_target_state.
      apply fold_C_is_dev_in_target_state.
      apply conj.
      assumption.
      apply IHinv_ss'; repeat( assumption ).
      constructor. 
      apply PNNP. assumption.
      apply Classical_Pred_Type.ex_not_not_all.
      inversion H6. exists x.
      revert H7. apply remove_not2. intros H7.
      apply NNPP in H7.
      apply or_not_and. apply imply_to_or in H7.
      destruct H7. left. assumption. right. apply PNNP.  assumption. 
      auto.
Qed.


Lemma NOT_L_is_dev_in_target_state: forall i inv o rid roff rval m tge tb te tf tm tm' iomem_p,
             Some (Vptr o Int.zero) = te ! iomem_p ->
             Some (Vint rid) = te ! regaccess_dev_id ->
             Some (Vint roff) = te ! regaccess_reg_off ->
             Some (Vint rval) = te ! regaccess_val ->
             Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
             mem_inj m tm' ->
             ~ is_in_target_state (slave_dev i) inv o rid roff rval m ->
             eval_expr tge (Vptr tb Int.zero) te tm
               (NOT_C_is_dev_in_target_state iomem_p (inv_ss inv)) Vtrue.
Proof.
      intros i inv o rid roff rval m tge0 tb te tf tm tm' iomem_p MPOM MRID MROFF MRVAL MFREE MINJ H.

      unfold NOT_C_is_dev_in_target_state.

      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vint Int.one).

      apply L_NOT_is_dev_in_target_state with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval)
                                              (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=iomem_p) (i:=i); repeat( assumption ).

      apply eval_Econst.
      auto.
      auto.
Qed.

Lemma NOT_L_NOT_is_dev_in_target_state: forall i inv o rid roff rval m tge tb te tf tm tm' iomem_p,
             Some (Vptr o Int.zero) = te ! iomem_p ->
             Some (Vint rid) = te ! regaccess_dev_id ->
             Some (Vint roff) = te ! regaccess_reg_off ->
             Some (Vint rval) = te ! regaccess_val ->
             Mem.free tm tb 0 (fn_stackspace tf) = Some tm' ->
             mem_inj m tm' ->
             is_in_target_state (slave_dev i) inv o rid roff rval m ->
             eval_expr tge (Vptr tb Int.zero) te tm
               (NOT_C_is_dev_in_target_state iomem_p (inv_ss inv)) Vfalse.
Proof.
      intros i inv o rid roff rval m tge0 tb te tf tm tm' iomem_p MPOM MRID MROFF MRVAL MFREE MINJ H.

      unfold NOT_C_is_dev_in_target_state.

      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).

      apply L_is_dev_in_target_state with (o:=o) (rid:=rid) (roff:=roff) (rval:=rval)
                                          (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=iomem_p) (i:=i); repeat( assumption ).

      apply eval_Econst.
      auto.
      auto.
Qed.

Lemma transl_step:
  forall S1 t S2, Violaspec.step ge S1 t S2 ->
  forall R1, match_states S1 R1 ->
  exists R2, plus Cminor.step tge R1 t R2 /\ match_states S2 R2.
Proof.
    induction 1; intros R1 MST; inversion MST.

(** 1- exec_reject step **)

  - monadInv TC.
    unfold eval_inv_reject in H.
    inversion H.
    unfold transl_invariant in EQ1.
    rewrite -> H0 in EQ1.
    unfold transl_uni_r_binder in EQ1.
    unfold C_is_dev_access in EQ1.
    unfold trans_uni_r_reject in H1.
    destruct H1.
    + unfold master_eval_reject in H1.
      inversion H1.
      rewrite <- H2 in EQ1.
      apply remove_OK in EQ1.
      inversion EQ1.
      econstructor; split.
      eapply plus_left with (t1:=E0) (t2:=E0); [ constructor | idtac | auto ].
      unfold C_return_reject.
      unfold C_return_allow.
      eapply star_step; [ idtac | idtac | erewrite E0_left; auto ].
      eapply step_ifthenelse with (v:=Val.of_optbool (Val.cmpu_bool (Mem.valid_pointer tm) Ceq (Vint rid) (Vint rid))).
      apply eval_Ebinop with (v1:=Vint rid) (v2:=Vint rid). constructor. auto. repeat( constructor ).
      unfold Val.cmpu. unfold Val.of_optbool. unfold Val.cmpu_bool. simpl. auto.
      unfold Val.cmpu. unfold Val.of_optbool. unfold Val.cmpu_bool.
 
      assert (Int.cmpu Ceq rid rid = true) as EQ3.
        simpl.
        apply Int.eq_true.
      rewrite EQ3.
      constructor.
      eapply star_step; [ idtac | idtac | auto ].
      unfold C_eval_master_access.

      inversion H3.
      inversion H6.
  
      eapply step_ifthenelse with (v:=Vtrue).

      apply L_is_valid_dev_access with (roff:=roff) (regs:=(regs (master_dev i))); assumption.

      constructor.

      eapply star_step; [ idtac | idtac | auto ].

      eapply step_ifthenelse with (v:=Vtrue).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).

      inversion H3.
      inversion H6.

      apply L_will_dev_go_target_state with (o:=om) (rid:=rid) (roff:=roff) (rval:=rval)
                                            (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=m_iomem_p); assumption.

      inversion H3.
      inversion H6.


      apply NOT_L_is_dev_in_target_state with (o:=os) (rid:=rid) (roff:=roff) (rval:=rval)
                                              (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=s_iomem_p) (i:=i); assumption. 

      auto.
      constructor.

      eapply star_step; [ constructor | idtac | apply E0_left; auto ].
      eapply eval_Econst.
      constructor.
      eapply MFREE.

      apply star_refl.
      econstructor.

      econstructor.
      auto.
      eapply MINJ.
      apply MK.

    + inversion H1.
      unfold slave_eval_reject in H3.
      apply remove_OK in EQ1.
      inversion EQ1.
      econstructor; split.
      eapply plus_left with (t1:=E0) (t2:=E0); [ constructor | idtac | auto ].
      unfold C_return_reject.
      unfold C_return_allow.
      eapply star_step; [ idtac | idtac | erewrite E0_left; auto ].

      eapply step_ifthenelse with (v:=Val.of_optbool (Val.cmpu_bool (Mem.valid_pointer tm) Ceq (Vint rid) (Vint (Int.repr (dev_id (master_dev i)))))).
      apply eval_Ebinop with (v1:=Vint rid) (v2:=Vint (Int.repr (dev_id (master_dev i)))). constructor. auto. repeat( constructor ).
      unfold Val.cmpu. unfold Val.of_optbool. unfold Val.cmpu_bool. simpl. auto.
      unfold Val.cmpu. unfold Val.of_optbool. unfold Val.cmpu_bool.
      assert (Int.cmpu Ceq rid (Int.repr (dev_id (master_dev i))) = false) as EQ3.
        simpl.
        apply Int.eq_false.
        inversion H3.
        assumption.
      rewrite EQ3.
      constructor.

      eapply star_step; [ econstructor | idtac | apply E0_left; auto ].
      inversion H3.
      rewrite <- H5.
      apply eval_Ebinop with (v1:=Vint rid) (v2:=Vint rid). constructor. auto. constructor. constructor. constructor.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl.
      rewrite -> Int.eq_true.
      constructor.

      eapply star_step; [ idtac | idtac | auto ].
      unfold C_eval_slave_access.

      inversion H3.
      inversion H6.

      eapply step_ifthenelse with (v:=Vtrue).

      apply L_is_valid_dev_access with (roff:=roff) (regs:=(regs (slave_dev i))).
      assumption.
      assumption.

      auto.
      constructor.

      eapply star_step; [ idtac | idtac | auto ].

      eapply step_ifthenelse with (v:=Vtrue).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vtrue).

      inversion H3.
      inversion H6.
      inversion H8.

      apply L_will_dev_go_out_of_target_state with (o:=os) (rid:=rid) (roff:=roff) (rval:=rval)
                                            (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=s_iomem_p); assumption.

      inversion H3.
      inversion H6.
      inversion H8.

      apply L_is_dev_in_target_state with (o:=om) (rid:=rid) (roff:=roff) (rval:=rval)
                                          (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=m_iomem_p) (i:=i); assumption.

      auto.
      constructor.

      eapply star_step; [ constructor | idtac | apply E0_left; auto ].
  
      eapply eval_Econst.
      constructor.
      eapply MFREE.

      apply star_refl.
      econstructor.
      econstructor.

      auto.
      eapply MINJ.
      apply MK.

(** 2- exec_skip step **)

  - monadInv TC.
    unfold eval_inv_reject in H.
    apply my_and_or in H.
    destruct H.

    (* Case: inv_binder <> uni_r *)
    unfold transl_invariant in EQ1.
    assert (OK Sskip = OK x0) as EQ2.
      destruct (inv_binder i).
      crush.
      assumption.

    apply remove_OK in EQ2.
    rewrite <- EQ2.
    econstructor; split.

    eapply plus_left with (t1:=E0) (t2:=E0); [ constructor | idtac | auto ].
    eapply star_step; [ constructor | idtac | apply E0_left; auto ].
    apply star_refl.

    econstructor; eauto. 

    (* Case: inv_binder i = uni_r /\ ~ trans_uni_r_reject i om os rid roff rval m *)
    unfold eval_inv_reject in H.
    inversion H.
    unfold transl_invariant in EQ1.
    rewrite -> H0 in EQ1.
    unfold transl_uni_r_binder in EQ1.
    unfold C_is_dev_access in EQ1.
    unfold trans_uni_r_reject in H1.

    apply Classical_Prop.not_or_and in H1.
    inversion H1.

    apply my_and_or in H2.
    destruct H2.

    (* SCase: rid <> Int.repr (dev_id (master_dev i)) *)
    apply my_and_or in H3.
    destruct H3.

    (* SSCase: ~ rid <> Int.repr (dev_id (master_dev i)) *)
    crush.

    (* SSCase: rid <> Int.repr (dev_id (master_dev i)) /\ ... *)
    inversion H3.
    clear H4. (* the same as H2 *)
    apply my_and_or in H5.
    destruct H5.
    (* SSSCase: rid <> Int.repr (dev_id (slave_dev i)) *)
      clear H3 H1.
      apply remove_OK in EQ1.
      inversion EQ1.
      econstructor; split.
      eapply plus_left with (t1:=E0) (t2:=E0); [ constructor | idtac | auto ].
      unfold C_return_reject.
      unfold C_return_allow.
      eapply star_step; [ idtac | idtac | erewrite E0_left; auto ].

      eapply step_ifthenelse with (v:=Val.of_optbool (Val.cmpu_bool (Mem.valid_pointer tm) Ceq (Vint rid) (Vint (Int.repr (dev_id (master_dev i)))))).
      apply eval_Ebinop with (v1:=Vint rid) (v2:=Vint (Int.repr (dev_id (master_dev i)))). constructor. auto. repeat( constructor ).
      unfold Val.cmpu. unfold Val.of_optbool. unfold Val.cmpu_bool. simpl. auto.
      unfold Val.cmpu. unfold Val.of_optbool. unfold Val.cmpu_bool.
      assert (Int.cmpu Ceq rid (Int.repr (dev_id (master_dev i))) = false) as EQ3.
        simpl.
        apply Int.eq_false.
        assumption.
      rewrite EQ3.
      constructor.
      (**)
      
      eapply star_step; [ idtac | idtac | erewrite E0_left; auto ].

      eapply step_ifthenelse with (v:=Val.of_optbool (Val.cmpu_bool (Mem.valid_pointer tm) Ceq (Vint rid) (Vint (Int.repr (dev_id (slave_dev i)))))).
      apply eval_Ebinop with (v1:=Vint rid) (v2:=Vint (Int.repr (dev_id (slave_dev i)))). constructor. auto. repeat( constructor ).
      unfold Val.cmpu. unfold Val.of_optbool. unfold Val.cmpu_bool. simpl. auto.
      unfold Val.cmpu. unfold Val.of_optbool. unfold Val.cmpu_bool.
      assert (Int.cmpu Ceq rid (Int.repr (dev_id (slave_dev i))) = false) as EQ3.
        simpl.
        apply Int.eq_false.
        assumption.
      rewrite EQ3.
      constructor.

      eapply star_step; [ constructor | idtac | apply E0_left; auto ].
      apply star_refl.

      econstructor; eauto. 

    (* SSSCase: rid = Int.repr (dev_id (slave_dev i)) /\ ~ slave_eval_reject i om os rid roff rval m *)
      inversion H4.
      clear H4 H3 H1.
      
      unfold slave_eval_reject in H6.
      apply my_and_or in H6.

      destruct H6.
      (* SSSSCase: ~ In roff (map reg_to_int (regs (slave_dev i))) *)

      apply remove_OK in EQ1.
      inversion EQ1.
      unfold C_return_allow.
      unfold C_return_allow in H3.
      econstructor; split.
      eapply plus_left with (t1:=E0) (t2:=E0); [ constructor | idtac | auto ].
      unfold C_return_reject.
      eapply star_step; [ idtac | idtac | erewrite E0_left; auto ].

      eapply step_ifthenelse with (v:=Val.of_optbool (Val.cmpu_bool (Mem.valid_pointer tm) Ceq (Vint rid) (Vint (Int.repr (dev_id (master_dev i)))))).
      apply eval_Ebinop with (v1:=Vint rid) (v2:=Vint (Int.repr (dev_id (master_dev i)))). constructor. auto. repeat( constructor ).
      unfold Val.cmpu. unfold Val.of_optbool. unfold Val.cmpu_bool. simpl. auto.
      unfold Val.cmpu. unfold Val.of_optbool. unfold Val.cmpu_bool.
      assert (Int.cmpu Ceq rid (Int.repr (dev_id (master_dev i))) = false) as EQ3.
        simpl.
        apply Int.eq_false.
        assumption.
      rewrite EQ3.
      constructor.
      (**)
      eapply star_step; [ econstructor | idtac | apply E0_left; auto ].
      rewrite <- H5.
      apply eval_Ebinop with (v1:=Vint rid) (v2:=Vint rid). constructor. auto. constructor. constructor. constructor.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl.
      rewrite -> Int.eq_true.
      constructor.

      eapply star_step; [ idtac | idtac | auto ].
      unfold C_eval_slave_access.
      unfold C_return_allow.

      eapply step_ifthenelse with (v:=Vfalse).

      apply L_NOT_is_valid_dev_access with (roff:=roff) (regs:=(regs (slave_dev i))); repeat( assumption ).

      auto.
      constructor.


      eapply star_step; [ constructor | idtac | apply E0_left; auto ].
      apply star_refl.
      constructor.

      econstructor; eauto. 

      (* SSSSCase: In roff (map reg_to_int (regs (slave_dev i))) /\ ... *)
      inversion H1.
      apply not_two_and in H4.
      destruct H4.

      (* SSSSSCase: ~ will ... /\ is_in ... *)
      inversion H4.
      clear H4.
      apply remove_OK in EQ1.
      inversion EQ1.
      unfold C_return_allow.
      unfold C_return_allow in H3.
      econstructor; split.
      eapply plus_left with (t1:=E0) (t2:=E0); [ constructor | idtac | auto ].
      unfold C_return_reject.
      eapply star_step; [ idtac | idtac | erewrite E0_left; auto ].

      eapply step_ifthenelse with (v:=Val.of_optbool (Val.cmpu_bool (Mem.valid_pointer tm) Ceq (Vint rid) (Vint (Int.repr (dev_id (master_dev i)))))).
      apply eval_Ebinop with (v1:=Vint rid) (v2:=Vint (Int.repr (dev_id (master_dev i)))). constructor. auto. repeat( constructor ).
      unfold Val.cmpu. unfold Val.of_optbool. unfold Val.cmpu_bool. simpl. auto.
      unfold Val.cmpu. unfold Val.of_optbool. unfold Val.cmpu_bool.
      assert (Int.cmpu Ceq rid (Int.repr (dev_id (master_dev i))) = false) as EQ3.
        simpl.
        apply Int.eq_false.
        assumption.
      rewrite EQ3.
      constructor.
      (**)
      eapply star_step; [ econstructor | idtac | apply E0_left; auto ].
      rewrite <- H5.
      apply eval_Ebinop with (v1:=Vint rid) (v2:=Vint rid). constructor. auto. constructor. constructor. constructor.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl.
      rewrite -> Int.eq_true.
      constructor.

      eapply star_step; [ idtac | idtac | auto ].
      unfold C_eval_slave_access.
      unfold C_return_allow.

      eapply step_ifthenelse with (v:=Vtrue).

      apply L_is_valid_dev_access with (roff:=roff) (regs:=(regs (slave_dev i))); repeat( assumption ).

      auto.
      constructor.

      eapply star_step; [ idtac | idtac | auto ].

      eapply step_ifthenelse with (v:=Vfalse).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).

      apply L_NOT_will_dev_go_out_of_target_state with (o:=os) (rid:=rid) (roff:=roff) (rval:=rval)
                                            (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=s_iomem_p); assumption.

      apply L_is_dev_in_target_state with (o:=om) (rid:=rid) (roff:=roff) (rval:=rval)
                                          (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=m_iomem_p) (i:=i); assumption.

      auto.
      constructor.

      eapply star_step; [ constructor | idtac | apply E0_left; auto ].
      apply star_refl.
      constructor.

      econstructor; eauto. 

      destruct H4.
      (* SSSSSCase: will ... /\ ~ is_in ... *)
      inversion H4.
      clear H4.
      apply remove_OK in EQ1.
      inversion EQ1.
      unfold C_return_allow.
      unfold C_return_allow in H3.
      econstructor; split.
      eapply plus_left with (t1:=E0) (t2:=E0); [ constructor | idtac | auto ].
      unfold C_return_reject.
      eapply star_step; [ idtac | idtac | erewrite E0_left; auto ].

      eapply step_ifthenelse with (v:=Val.of_optbool (Val.cmpu_bool (Mem.valid_pointer tm) Ceq (Vint rid) (Vint (Int.repr (dev_id (master_dev i)))))).
      apply eval_Ebinop with (v1:=Vint rid) (v2:=Vint (Int.repr (dev_id (master_dev i)))). constructor. auto. repeat( constructor ).
      unfold Val.cmpu. unfold Val.of_optbool. unfold Val.cmpu_bool. simpl. auto.
      unfold Val.cmpu. unfold Val.of_optbool. unfold Val.cmpu_bool.
      assert (Int.cmpu Ceq rid (Int.repr (dev_id (master_dev i))) = false) as EQ3.
        simpl.
        apply Int.eq_false.
        assumption.
      rewrite EQ3.
      constructor.
      (**)
      eapply star_step; [ econstructor | idtac | apply E0_left; auto ].
      rewrite <- H5.
      apply eval_Ebinop with (v1:=Vint rid) (v2:=Vint rid). constructor. auto. constructor. constructor. constructor.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl.
      rewrite -> Int.eq_true.
      constructor.

      eapply star_step; [ idtac | idtac | auto ].
      unfold C_eval_slave_access.
      unfold C_return_allow.

      eapply step_ifthenelse with (v:=Vtrue).

      apply L_is_valid_dev_access with (roff:=roff) (regs:=(regs (slave_dev i))).
      assumption.
      assumption.

      auto.
      constructor.

      eapply star_step; [ idtac | idtac | auto ].

      eapply step_ifthenelse with (v:=Vfalse).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).

      apply L_will_dev_go_out_of_target_state with (o:=os) (rid:=rid) (roff:=roff) (rval:=rval)
                                            (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=s_iomem_p); assumption.

      apply L_NOT_is_dev_in_target_state with (o:=om) (rid:=rid) (roff:=roff) (rval:=rval)
                                          (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=m_iomem_p) (i:=i); assumption.

      auto.
      constructor.

      eapply star_step; [ constructor | idtac | apply E0_left; auto ].
      apply star_refl.
      constructor.

      econstructor; eauto.

      (* SSSSSCase: ~ will ... /\ is_in ... *)
      inversion H4.
      clear H4.
      apply remove_OK in EQ1.
      inversion EQ1.
      unfold C_return_allow.
      unfold C_return_allow in H3.
      econstructor; split.
      eapply plus_left with (t1:=E0) (t2:=E0); [ constructor | idtac | auto ].
      unfold C_return_reject.
      eapply star_step; [ idtac | idtac | erewrite E0_left; auto ].

      eapply step_ifthenelse with (v:=Val.of_optbool (Val.cmpu_bool (Mem.valid_pointer tm) Ceq (Vint rid) (Vint (Int.repr (dev_id (master_dev i)))))).
      apply eval_Ebinop with (v1:=Vint rid) (v2:=Vint (Int.repr (dev_id (master_dev i)))). constructor. auto. repeat( constructor ).
      unfold Val.cmpu. unfold Val.of_optbool. unfold Val.cmpu_bool. simpl. auto.
      unfold Val.cmpu. unfold Val.of_optbool. unfold Val.cmpu_bool.
      assert (Int.cmpu Ceq rid (Int.repr (dev_id (master_dev i))) = false) as EQ3.
        simpl.
        apply Int.eq_false.
        assumption.
      rewrite EQ3.
      constructor.
      (**)
      eapply star_step; [ econstructor | idtac | apply E0_left; auto ].
      rewrite <- H5.
      apply eval_Ebinop with (v1:=Vint rid) (v2:=Vint rid). constructor. auto. constructor. constructor. constructor.
      unfold Val.cmp. unfold Val.of_optbool. unfold Val.cmp_bool. simpl.
      rewrite -> Int.eq_true.
      constructor.

      eapply star_step; [ idtac | idtac | auto ].
      unfold C_eval_slave_access.
      unfold C_return_allow.

      eapply step_ifthenelse with (v:=Vtrue).

      apply L_is_valid_dev_access with (roff:=roff) (regs:=(regs (slave_dev i))); repeat( assumption ).

      auto.
      constructor.

      eapply star_step; [ idtac | idtac | auto ].

      eapply step_ifthenelse with (v:=Vfalse).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).

      apply L_NOT_will_dev_go_out_of_target_state with (o:=os) (rid:=rid) (roff:=roff) (rval:=rval)
                                            (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=s_iomem_p); repeat( assumption ).

      apply L_NOT_is_dev_in_target_state with (o:=om) (rid:=rid) (roff:=roff) (rval:=rval)
                                          (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=m_iomem_p) (i:=i); assumption.

      auto.
      constructor.

      eapply star_step; [ constructor | idtac | apply E0_left; auto ].
      apply star_refl.
      constructor.

      econstructor; eauto.

    (* SCase: rid = Int.repr (dev_id (master_dev i)) /\ ~ master_eval_reject i om os rid roff rval m *)
    inversion H2.
    apply my_and_or in H3.
    destruct H3.
    (* SSCase: ~ rid <> Int.repr (dev_id (master_dev i)) *)
    clear H3. (* the same as H4 *)
    clear H1 H2.
    unfold master_eval_reject in H5.
    apply my_and_or in H5.
    destruct H5.
    (* SSSCase: ~ In roff (map reg_to_int (regs (master_dev i))) *)      
      rewrite <- H4 in EQ1.
      apply remove_OK in EQ1.
      inversion EQ1.
      econstructor; split.
      eapply plus_left with (t1:=E0) (t2:=E0); [ constructor | idtac | auto ].
      unfold C_return_reject.
      unfold C_return_allow.
      eapply star_step; [ idtac | idtac | erewrite E0_left; auto ].
      eapply step_ifthenelse with (v:=Val.of_optbool (Val.cmpu_bool (Mem.valid_pointer tm) Ceq (Vint rid) (Vint rid))).
      apply eval_Ebinop with (v1:=Vint rid) (v2:=Vint rid). constructor. auto. constructor. constructor.
      unfold Val.cmpu. unfold Val.of_optbool. unfold Val.cmpu_bool. simpl. auto.
      unfold Val.cmpu. unfold Val.of_optbool. unfold Val.cmpu_bool.
 
      assert (Int.cmpu Ceq rid rid = true) as EQ3.
        simpl.
        apply Int.eq_true.
      rewrite EQ3.
      constructor.
      eapply star_step; [ idtac | idtac | auto ].
      unfold C_eval_master_access.

      eapply step_ifthenelse with (v:=Vfalse).

      apply L_NOT_is_valid_dev_access with (roff:=roff) (regs:=(regs (master_dev i))).
      assumption.
      assumption.

      constructor.

      eapply star_step; [ constructor | idtac | apply E0_left; auto ].

      constructor.
      constructor.

      econstructor; eauto. 

    (* SSSCase: In roff (map reg_to_int (regs (master_dev i))) /\ ... *)
    inversion H1.
    apply not_two_and in H3.
    destruct H3.

    (* SSSSCase: ~ will ... /\ ~ is_in ... *)
      inversion H3.
      clear H1 H3.
      rewrite <- H4 in EQ1.
      apply remove_OK in EQ1.
      inversion EQ1.
      econstructor; split.
      eapply plus_left with (t1:=E0) (t2:=E0); [ constructor | idtac | auto ].
      unfold C_return_reject.
      unfold C_return_allow.
      eapply star_step; [ idtac | idtac | erewrite E0_left; auto ].
      eapply step_ifthenelse with (v:=Val.of_optbool (Val.cmpu_bool (Mem.valid_pointer tm) Ceq (Vint rid) (Vint rid))).
      apply eval_Ebinop with (v1:=Vint rid) (v2:=Vint rid). constructor. auto. constructor. constructor.
      unfold Val.cmpu. unfold Val.of_optbool. unfold Val.cmpu_bool. simpl. auto.
      unfold Val.cmpu. unfold Val.of_optbool. unfold Val.cmpu_bool.
 
      assert (Int.cmpu Ceq rid rid = true) as EQ3.
        simpl.
        apply Int.eq_true.
      rewrite EQ3.
      constructor.
      eapply star_step; [ idtac | idtac | auto ].
      unfold C_eval_master_access.

      eapply step_ifthenelse with (v:=Vtrue).

      apply L_is_valid_dev_access with (roff:=roff) (regs:=(regs (master_dev i))).
      assumption.
      assumption.

      constructor.

      eapply star_step; [ idtac | idtac | auto ].

      eapply step_ifthenelse with (v:=Vfalse).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vtrue).

      apply L_NOT_will_dev_go_target_state with (o:=om) (rid:=rid) (roff:=roff) (rval:=rval)
                                            (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=m_iomem_p); assumption.

      apply NOT_L_is_dev_in_target_state with (o:=os) (rid:=rid) (roff:=roff) (rval:=rval)
                                              (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=s_iomem_p) (i:=i); assumption.

      auto.
      constructor.

      eapply star_step; [ constructor | idtac | apply E0_left; auto ].

      constructor.
      constructor.

      econstructor; eauto. 

    destruct H3.
    (* SSSSCase: will ... /\ ~ ~ is_in ... *)
      inversion H3.
      clear H1 H3.
      rewrite <- H4 in EQ1.
      apply remove_OK in EQ1.
      inversion EQ1.
      econstructor; split.
      eapply plus_left with (t1:=E0) (t2:=E0); [ constructor | idtac | auto ].
      unfold C_return_reject.
      unfold C_return_allow.
      eapply star_step; [ idtac | idtac | erewrite E0_left; auto ].
      eapply step_ifthenelse with (v:=Val.of_optbool (Val.cmpu_bool (Mem.valid_pointer tm) Ceq (Vint rid) (Vint rid))).
      apply eval_Ebinop with (v1:=Vint rid) (v2:=Vint rid). constructor. auto. constructor. constructor.
      unfold Val.cmpu. unfold Val.of_optbool. unfold Val.cmpu_bool. simpl. auto.
      unfold Val.cmpu. unfold Val.of_optbool. unfold Val.cmpu_bool.
 
      assert (Int.cmpu Ceq rid rid = true) as EQ3.
        simpl.
        apply Int.eq_true.
      rewrite EQ3.
      constructor.
      eapply star_step; [ idtac | idtac | auto ].
      unfold C_eval_master_access.

      eapply step_ifthenelse with (v:=Vtrue).

      apply L_is_valid_dev_access with (roff:=roff) (regs:=(regs (master_dev i))); repeat(assumption).
      constructor.

      eapply star_step; [ idtac | idtac | auto ].

      eapply step_ifthenelse with (v:=Vfalse).
      apply eval_Ebinop with (v1:=Vtrue) (v2:=Vfalse).

      apply L_will_dev_go_target_state with (o:=om) (rid:=rid) (roff:=roff) (rval:=rval)
                                            (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=m_iomem_p); assumption.

      apply NOT_L_NOT_is_dev_in_target_state with (o:=os) (rid:=rid) (roff:=roff) (rval:=rval)
                                              (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=s_iomem_p) (i:=i); repeat(assumption).
      apply Classical_Prop.NNPP in H6; repeat( assumption ).

      auto.
      constructor.

      eapply star_step; [ constructor | idtac | apply E0_left; auto ].

      constructor.
      constructor.

      econstructor; eauto.

    (* SSSSCase: ~ will ... /\ ~ ~ is_in ... *)
      inversion H3.
      clear H1 H3.
      rewrite <- H4 in EQ1.
      apply remove_OK in EQ1.
      inversion EQ1.
      econstructor; split.
      eapply plus_left with (t1:=E0) (t2:=E0); [ constructor | idtac | auto ].
      unfold C_return_reject.
      unfold C_return_allow.
      eapply star_step; [ idtac | idtac | erewrite E0_left; auto ].
      eapply step_ifthenelse with (v:=Val.of_optbool (Val.cmpu_bool (Mem.valid_pointer tm) Ceq (Vint rid) (Vint rid))).
      apply eval_Ebinop with (v1:=Vint rid) (v2:=Vint rid). constructor. auto. repeat( constructor ).
      unfold Val.cmpu. unfold Val.of_optbool. unfold Val.cmpu_bool. simpl. auto.
      unfold Val.cmpu. unfold Val.of_optbool. unfold Val.cmpu_bool.
 
      assert (Int.cmpu Ceq rid rid = true) as EQ3.
        simpl.
        apply Int.eq_true.
      rewrite EQ3.
      constructor.
      eapply star_step; [ idtac | idtac | auto ].
      unfold C_eval_master_access.

      eapply step_ifthenelse with (v:=Vtrue).

      apply L_is_valid_dev_access with (roff:=roff) (regs:=(regs (master_dev i))).
      assumption.
      assumption.

      constructor.

      eapply star_step; [ idtac | idtac | auto ].

      eapply step_ifthenelse with (v:=Vfalse).
      apply eval_Ebinop with (v1:=Vfalse) (v2:=Vfalse).

      apply L_NOT_will_dev_go_target_state with (o:=om) (rid:=rid) (roff:=roff) (rval:=rval)
                                            (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=m_iomem_p); assumption.

      apply NOT_L_NOT_is_dev_in_target_state with (o:=os) (rid:=rid) (roff:=roff) (rval:=rval)
                                              (m:=m) (tm':=tm') (tf:=tf) (iomem_p:=s_iomem_p) (i:=i); repeat(assumption).
      apply Classical_Prop.NNPP in H6.
      assumption.

      auto.
      constructor.

      eapply star_step; [ constructor | idtac | apply E0_left; auto ].

      constructor.
      constructor.

      econstructor; eauto.
      inversion H3.
      crush.

(** 3- exec_allow step **)
  
  - monadInv TC.

    econstructor; split.
    eapply plus_left with (t1:=E0) (t2:=E0); [ constructor | idtac | auto ].

    apply eval_Econst.
    constructor.
    eapply MFREE.
    apply star_refl.

    econstructor.
    auto.
    eapply MINJ.
    apply MK.

(** 4- exec_call step **)

  - monadInv TFD.
    monadInv EQ.
    monadInv EQ0.
    econstructor; split.
    eapply plus_left with (t1:=E0) (t2:=E0); [ idtac | idtac | auto ].

    apply step_internal_function with (m' := m)
                                  (sp := r). eauto. eauto.

(* 1st *)
    eapply star_step with (t1:=E0) (t2:=E0); [ constructor | idtac | auto ].

    eapply star_step with (t1:=E0) (t2:=E0). constructor.
    intros; apply eval_Eload with (vaddr:=Vptr (r) Int.zero).
    
    apply eval_Ebinop with (v1:=Vptr r Int.zero) (v2:=Vint Int.zero).
           constructor. simpl. eauto. 

    apply eval_Econst. unfold eval_constant. auto.
    auto. 
    unfold Mem.loadv.
    eauto.

(* 2nd *)
    eapply star_step with (t1:=E0) (t2:=E0); [ constructor; constructor; constructor | idtac | auto ].
    eapply star_step with (t1:=E0) (t2:=E0); [ constructor; constructor; constructor | idtac | auto ].
    eapply star_step with (t1:=E0) (t2:=E0). constructor.
    intros; apply eval_Eload with (vaddr:=Vptr (r) (Int.repr 1)).

    apply eval_Ebinop with (v1:=Vptr r Int.zero) (v2:=Vint (Int.repr 1)).
           constructor. simpl. eauto. 

      apply eval_Econst. unfold eval_constant. auto.
      auto.
      unfold Mem.loadv.
      eauto.

(* 3rd *)
    eapply star_step with (t1:=E0) (t2:=E0); [ constructor; constructor; constructor | idtac | auto ].
    eapply star_step with (t1:=E0) (t2:=E0); [ constructor; constructor; constructor | idtac | auto ].
    eapply star_step with (t1:=E0) (t2:=E0). constructor.
    intros; apply eval_Eload with (vaddr:=Vptr (r) (Int.repr 2)).

    apply eval_Ebinop with (v1:=Vptr r Int.zero) (v2:=Vint (Int.repr 2)).
           constructor. simpl. eauto. 
    apply eval_Econst. unfold eval_constant. auto. auto.
    unfold Mem.loadv.
    eauto.

    eapply star_step with (t1:=E0) (t2:=E0); [ constructor; constructor; constructor | idtac | auto ].
    constructor. constructor. constructor. constructor. econstructor; eauto.

    unfold transl_function. unfold transl_funbody. rewrite EQ; auto.

Qed.

Definition semantics (p: program) :=
    Semantics step (initial_state p) final_state (Genv.globalenv p).


Theorem transl_program_correct:
    forward_simulation (Violasemantics.semantics prog) (vCminorp.semantics tprog).
Proof.
    eapply forward_simulation_plus.
    eexact symbols_preserved.
    eexact transl_initial_states.
    eexact transl_final_states.
    eexact transl_step.
Qed.

End TRANSLATION.
