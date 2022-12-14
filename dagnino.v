Require Export List.
Require Export Wf.

Export ListNotations.

Parameter config: Type.
Parameter result: Type.
Parameter is_rule: list (config * result) -> config -> result -> Prop.

(* Based on Francesco Dagnino, A Meta-theory for Big-step Semantics, ACM Transactions on Computational Logic 23(3), April 2022. *)

(* Significant ergonomics can probably be gained by specializing these rules for particular numbers of premises (e.g. 0, 1, 2, and more than 2) *)

Inductive terminates: config -> result -> Prop :=
| terminates_intro ps c r:
  is_rule ps c r ->
  (forall pc pr, In (pc, pr) ps -> terminates pc pr) ->
  terminates c r.

CoInductive diverges: config -> Prop :=
| diverges_intro ps0 pc pr ps1 c r:
  is_rule (ps0 ++ ((pc, pr) :: ps1)) c r ->
  Forall (fun pc_pr => terminates (fst pc_pr) (snd pc_pr)) ps0 ->
  diverges pc ->
  diverges c.

Inductive diverges_rule: config -> config -> Prop :=
| diverges_rule_intro ps0 pc pr ps1 c r:
  is_rule (ps0 ++ ((pc, pr) :: ps1)) c r ->
  Forall (fun pc_pr => terminates (fst pc_pr) (snd pc_pr)) ps0 ->
  diverges_rule pc c.

Lemma diverges_lemma(P: config -> Prop):
  (forall c, P c -> exists pc, P pc /\ diverges_rule pc c) ->
  (forall c, P c -> diverges c).
Proof.
  intro H.
  cofix Hcofix.
  intros.
  apply H in H0.
  destruct H0 as [pc [? ?]].
  inversion H1; clear H1; subst.
  apply (diverges_intro ps0 pc pr ps1 c r); try assumption.
  apply Hcofix.
  assumption.
Qed.

Definition rule_prefix: Type := list (config * result) * config.

Definition state: Type := config * option result * list rule_prefix.

Inductive step: state -> state -> Prop :=
| step_ax c r k:
  is_rule [] c r ->
  step (c, None, k) (c, Some r, k)
| step_enter pc pr ps c r k:
  is_rule ((pc, pr) :: ps) c r ->
  step (c, None, k) (pc, None, ([], c)::k)
| step_next ps1 pc1 pr1 pc2 pr2 ps2 c r k:
  is_rule (ps1 ++ ((pc1, pr1) :: (pc2, pr2) :: ps2)) c r ->
  step (pc1, Some pr1, (ps1, c)::k) (pc2, None, (ps1 ++ [(pc1, pr1)], c)::k)
| step_exit ps1 pc pr c r k:
  is_rule (ps1 ++ [(pc, pr)]) c r ->
  step (pc, Some pr, (ps1, c)::k) (c, Some r, k)
.

Inductive rtc{A}(R: A -> A -> Prop): A -> A -> Prop :=
| rtc_refl x: rtc R x x
| rtc_step x y z:
  R x y ->
  rtc R y z ->
  rtc R x z.

Lemma destruct_list_snoc {A} (xs: list A):
  xs = [] \/ exists xs0 x, xs = xs0 ++ [x].
Proof.
  induction xs.
  - tauto.
  - right.
    destruct IHxs as [Hxs|[xs0 [x Hxs0]]].
    + exists [].
      exists a.
      rewrite Hxs.
      reflexivity.
    + exists (a::xs0).
      exists x.
      rewrite Hxs0.
      reflexivity.
Qed.

Lemma step_toplevel_config_lemma c1 or1 k1 c2 or2 k2:
  step (c1, or1, k1) (c2, or2, k2) ->
  last (c1::map snd k1) c1 = last (c2::map snd k2) c2.
Proof.
  intro H; inversion H; clear H; subst.
  - reflexivity.
  - destruct (destruct_list_snoc k1) as [Hk1|[k11 [klast Hk1]]].
    + subst.
      reflexivity.
    + rewrite Hk1.
      rewrite map_app.
      simpl.
      rewrite map_app.
      simpl.
      rewrite ! last_last.
      reflexivity.
  - destruct (destruct_list_snoc k) as [Hk|[k1 [klast Hk1]]].
    + subst.
      reflexivity.
    + rewrite Hk1.
      simpl.
      rewrite ! map_app.
      simpl.
      rewrite ! last_last.
      reflexivity.
  - destruct (destruct_list_snoc k2) as [Hk2|[k21 [klast Hk21]]].
    + subst.
      reflexivity.
    + rewrite Hk21.
      simpl.
      rewrite ! map_app.
      simpl.
      rewrite ! last_last.
      reflexivity.
Qed.

Lemma rtc_step_toplevel_config_lemma s1 s2:
  rtc step s1 s2 ->
  forall c1 or1 k1 c2 or2 k2,
  s1 = (c1, or1, k1) ->
  s2 = (c2, or2, k2) ->
  last (c1::map snd k1) c1 = last (c2::map snd k2) c2.
Proof.
  induction 1.
  - intros; subst.
    injection H0; clear H0; intros; subst.
    reflexivity.
  - intros.
    destruct y as [[cy ory] ky].
    subst.
    rewrite <- (IHrtc cy ory ky c2 or2 k2); try reflexivity.
    apply step_toplevel_config_lemma with (1:=H).
Qed.

Inductive state_inv: state -> Prop :=
| state_inv_intro c or k:
  (match or with None => True | Some r => terminates c r end) ->
  Forall (fun ps_c => Forall (fun pc_pr => terminates (fst pc_pr) (snd pc_pr)) (fst ps_c)) k ->
  state_inv (c, or, k)
.

Lemma step_inv s1 s2:
  step s1 s2 ->
  state_inv s1 ->
  state_inv s2.
Proof.
  intros Hstep Hs1.
  inversion Hs1; clear Hs1; subst.
  inversion Hstep; clear Hstep; subst.
  - (* step_ax *) 
    constructor.
    + econstructor. eassumption.
      intros.
      inversion H1.
    + apply H0.
  - (* step_enter *)
    constructor; try tauto.
    constructor.
    + constructor.
    + apply H0.
  - (* step_next *)
    inversion H0; clear H0; subst.
    constructor; try tauto.
    constructor.
    + apply Forall_app.
      split.
      * apply H3.
      * constructor; [|constructor].
        apply H.
    + apply H4.
  - (* step_exit *)
    inversion H0; clear H0; subst.
    constructor; try tauto.
    econstructor.
    eassumption.
    intros.
    apply in_app_or in H0.
    destruct H0.
    + apply (proj1 (Forall_forall _ _) H3 (pc, pr0)).
      apply H0.
    + inversion H0; clear H0; subst.
      * injection H1; clear H1; intros; subst.
        assumption.
      * inversion H1.
Qed.

Lemma rtc_inv{A}(R: A -> A -> Prop)(P: A -> Prop):
  (forall x y, R x y -> P x -> P y) ->
  (forall x y, rtc R x y -> P x -> P y).
Proof.
  intros.
  revert H1.
  induction H0.
  - tauto.
  - intros.
    apply IHrtc.
    apply H with (1:=H0).
    assumption.
Qed.

Theorem step_terminates c1 c2 r:
  rtc step (c1, None, []) (c2, Some r, []) ->
  c2 = c1 /\ terminates c1 r.
Proof.
  intros.
  assert (c2 = c1). {
    eapply rtc_step_toplevel_config_lemma in H.
    2:{ reflexivity. }
    2:{ reflexivity. }
    simpl in H.
    congruence.
  }
  subst.
  split.
  - reflexivity.
  - assert (state_inv (c1, Some r, [])). {
      apply rtc_inv with (1:=step_inv) (2:=H).
      constructor; try tauto.
      constructor.
    }
    inversion H0; subst.
    assumption.
Qed.

Lemma rtc_trans{A}(R: A -> A -> Prop) x y z:
  rtc R x y ->
  rtc R y z ->
  rtc R x z.
Proof.
  induction 1.
  - tauto.
  - intros.
    eapply rtc_step.
    + eassumption.
    + apply IHrtc.
      apply H1.
Qed.

Lemma terminates_step_premises_lemma ps1 pc pr ps2 c r k:
  is_rule (ps1 ++ ((pc, pr) :: ps2)) c r ->
  (forall pc1 pr1,
   In (pc1, pr1) ((pc, pr) :: ps2) ->
   forall k, rtc step (pc1, None, k) (pc1, Some pr1, k)) ->
  rtc step (pc, None, (ps1, c)::k) (c, Some r, k).
Proof.
  revert ps1 pc pr.
  induction ps2; intros.
  - eapply rtc_trans.
    apply H0.
    + constructor.
      reflexivity.
    + eapply rtc_step; [|apply rtc_refl].
      apply step_exit.
      assumption.
  - destruct a as [pc1 pr1].
    eapply rtc_trans.
    + apply H0.
      left.
      * reflexivity.
    + eapply rtc_step.
      * eapply step_next.
        apply H.
      * eapply IHps2.
        -- rewrite <- app_assoc.
           apply H.
        -- intros.
           apply H0.
           right.
           assumption.
Qed.

Lemma terminates_step_lemma c r k:
  terminates c r ->
  rtc step (c, None, k) (c, Some r, k).
Proof.
  intro H.
  revert k.
  induction H.
  intro.
  destruct ps as [|[pc pr] ps1].
  - eapply rtc_step; [|apply rtc_refl].
    apply step_ax.
    assumption.
  - eapply rtc_step.
    + eapply step_enter.
      eassumption.
    + apply terminates_step_premises_lemma with (ps1:=[]) (pr:=pr) (ps2:=ps1).
      * apply H.
      * apply H1.
Qed.

Theorem terminates_step c r:
  terminates c r ->
  rtc step (c, None, []) (c, Some r, []).
Proof.
  intros.
  apply terminates_step_lemma.
  assumption.
Qed.

Require Import Lia.

Lemma firstn_app_all_l{A}(l1 l2: list A):
  firstn (length (l1 ++ l2) - length l2) (l1 ++ l2) = l1.
Proof.
  rewrite app_length.
  assert (length l1 + length l2 - length l2 = length l1). lia. rewrite H.
  rewrite firstn_app.
  rewrite firstn_all.
  assert (length l1 - length l1 = 0). lia. rewrite H0.
  rewrite firstn_O.
  apply app_nil_r.
Qed.

Lemma step_remove_context_suffix {c0 or0 c k0 k c1 or1 k1_}:
  step (c0, or0, k0 ++ k) (c1, or1, k1_) ->
  last (c0::map snd k0) c = c ->
  (~ exists r, (c0, or0, k0) = (c, Some r, [])) ->
  exists k1,
  k1_ = k1 ++ k /\
  step (c0, or0, k0) (c1, or1, k1) /\
  last (c1::map snd k1) c = c.
Proof.
  intros.
  inversion H; clear H; subst.
  - exists k0.
    split. {
      reflexivity.
    }
    split. {
      apply step_ax; assumption.
    }
    assumption.
  - exists (([], c0) :: k0).
    split. {
      reflexivity.
    }
    split. {
      eapply step_enter; eassumption.
    }
    simpl.
    apply H0.
  - destruct k0.
    + elim H1.
      exists pr1.
      simpl in H0.
      subst.
      reflexivity.
    + simpl in H5.
      injection H5; clear H5; intros; subst.
      exists ((ps1 ++ [(c0, pr1)], c2)::k0).
      split. {
        reflexivity.
      }
      split. {
        eapply step_next; eassumption.
      }
      simpl.
      apply H0.
  - destruct k0.
    + simpl in H0.
      subst.
      elim H1.
      exists pr.
      reflexivity.
    + simpl in H5.
      injection H5; clear H5; intros; subst.
      exists k0.
      split. {
        reflexivity.
      }
      split. {
        apply step_exit.
        assumption.
      }
      apply H0.
Qed.

Lemma trace_remove_context_suffix {trace c0 or0 c k0 k}:
  (forall i, step (trace i) (trace (S i))) ->
  trace 0 = (c0, or0, k0 ++ k) ->
  last (c0::map snd k0) c = c ->
  ~ (exists i r, trace i = (c, Some r, k)) ->
  exists trace',
  trace' 0 = (c0, or0, k0) /\
  (forall i, step (trace' i) (trace' (S i))).
Proof.
  intros.
  exists (fun i => match trace i with (ci, ori, ki) => (ci, ori, firstn (length ki - length k) ki) end).
  split.
  - rewrite H0.
    rewrite firstn_app_all_l.
    reflexivity.
  - assert (forall i, match trace i with (ci, ori, ki) => exists ki0, ki = ki0 ++ k /\ last (ci::map snd ki0) c = c end). {
      induction i.
      - rewrite H0.
        exists k0.
        split. { reflexivity. }
        apply H1.
      - pose proof (H i).
        assert (~ exists r, trace i = (c, Some r, k)). {
          intro.
          elim H2.
          exists i.
          apply H4.
        }
        destruct (trace i) as [[ci ori] ki].
        destruct (trace (S i)) as [[cSi orSi] kSi].
        destruct IHi as [ki0 [? ?]].
        subst.
        assert (~ exists r, (ci, ori, ki0) = (c, Some r, [])). {
          intro.
          elim H4.
          destruct H5 as [r ?].
          exists r.
          injection H5; clear H5; intros; subst.
          reflexivity.
        }
        destruct (step_remove_context_suffix H3 H6 H5) as [kSi0 [? [? ?]]].
        exists kSi0. tauto.
    }
    intro i.
    pose proof (H3 i).
    pose proof (H i).
    assert (~ exists r, trace i = (c, Some r, k)). {
      intro.
      elim H2.
      exists i.
      apply H6.
    }
    destruct (trace i) as [[ci ori] ki].
    destruct (trace (S i)) as [[cSi orSi] kSi].
    destruct H4 as [ki0 [? ?]].
    subst.
    assert (~ exists r, (ci, ori, ki0) = (c, Some r, [])). {
      intro.
      elim H6.
      destruct H4 as [r ?].
      exists r.
      injection H4; clear H4; intros; subst.
      reflexivity.
    }
    destruct (step_remove_context_suffix H5 H7 H4) as [kSi0 [? [? ?]]].
    subst.
    rewrite ! firstn_app_all_l.
    assumption.
Qed.

Inductive is_rule_prefix: rule_prefix -> Prop :=
| is_rule_prefix_intro c r ps1 ps2:
  is_rule (ps1 ++ ps2) c r ->
  Forall (fun pc_pr => terminates (fst pc_pr) (snd pc_pr)) ps1 ->
  is_rule_prefix (ps1, c).

Inductive rule_prefix_lt: rule_prefix -> rule_prefix -> Prop :=
| rule_prefix_lt_intro ps1 p ps2 c:
  is_rule_prefix (ps1, c) ->
  is_rule_prefix (ps1 ++ (p::ps2), c) ->
  rule_prefix_lt (ps1 ++ (p::ps2), c) (ps1, c)
.

Parameter rule_prefix_lt_wf: well_founded rule_prefix_lt.

Require Export Classical.

Theorem step_diverges c:
  (exists trace,
  (forall i, step (trace i) (trace (S i))) /\
  trace 0 = (c, None, [])) ->
  diverges c.
Proof.
  revert c.
  apply diverges_lemma.
  intros.
  destruct H as [trace [? ?]].
  pose proof (H 0).
  rewrite H0 in H1.
  inversion H1; clear H1; subst. {
    pose proof (H 1).
    rewrite <- H5 in H1.
    inversion H1; clear H1; subst.
  }
  apply (well_founded_ind rule_prefix_lt_wf (fun prefix =>
    forall ps1 pc pr ps2 c r,
    prefix = (ps1, c) ->
    is_rule (ps1 ++ ((pc, pr) :: ps2)) c r ->
    Forall (fun pc_pr => terminates (fst pc_pr) (snd pc_pr)) ps1 ->
    forall trace,
    (forall i, step (trace i) (trace (S i))) ->
    trace O = (pc, None, [(ps1, c)]) ->
    exists pc0,
      (exists trace',
       (forall i, step (trace' i) (trace' (S i))) /\
       trace' 0 = (pc0, None, [])) /\
      diverges_rule pc0 c)) with (trace:=fun i => trace (S i)) (ps1:=[]) (pc:=pc) (pr:=pr) (r:=r) (ps2:=ps) (a:=([], c)); try tauto.
  2:{ constructor. }
  2:{ intros; apply H. }
  2:{ rewrite <- H5. reflexivity. }
  clear c trace H H0 pc pr ps r H3 H5.
  intros prefix1 Hind.
  intros.
  subst.
  destruct (classic (exists i pr, trace i = (pc, Some pr, [(ps1, c)]))).
  - destruct H as [i [pri Hi]].
    assert (Hstate_inv0: state_inv (trace 0)). {
      rewrite H3.
      constructor; try tauto.
      constructor; [|constructor].
      apply H1.
    }
    assert (Hstate_inv: state_inv (trace i)). {
      clear H3 Hi.
      revert trace H2 Hstate_inv0.
      revert i.
      induction i.
      - tauto.
      - intros.
        apply IHi in Hstate_inv0.
        pose proof (H2 i).
        apply step_inv with (1:=H) (2:=Hstate_inv0).
        apply H2.
    }
    pose proof (H2 i).
    inversion H; clear H; subst; try congruence.
    2:{
      rewrite Hi in H4.
      injection H4; clear H4; intros; subst.
      pose proof (H2 (S i)).
      rewrite <- H5 in H.
      inversion H.
    }
    rewrite Hi in H4.
    injection H4; clear H4; intros; subst.
    eapply (Hind (ps1 ++ [(pc, pri)], c)) with (trace:=fun j => trace (j + S i)).
    + constructor.
      * econstructor.
        -- apply H0.
        -- apply H1.
      * econstructor.
        -- rewrite <- app_assoc.
           apply H6.
        -- apply Forall_app.
           split.
           ++ apply H1.
           ++ constructor; [|constructor].
              rewrite Hi in Hstate_inv.
              inversion Hstate_inv; clear Hstate_inv; subst.
              apply H7.
    + reflexivity.
    + rewrite <- app_assoc.
      apply H6.
    + apply Forall_app.
      split.
      * apply H1.
      * constructor; [|constructor].
        rewrite Hi in Hstate_inv.
        inversion Hstate_inv; clear Hstate_inv; subst.
        apply H7.
    + intros.
      apply H2.
    + simpl.
      congruence.
  - exists pc.
    destruct (trace_remove_context_suffix (c0:=pc) (or0:=None) (k:=[(ps1, c)]) (c:=pc) (k0:=[]) H2) as [trace' [? ?]]. {
      assumption.
    } {
      reflexivity.
    } { assumption. }
    split. {
      exists trace'.
      tauto.
    }
    econstructor; eassumption.
Qed.

Require Import ClassicalChoice.

Lemma rtc_f s0 sn:
  rtc step s0 sn ->
  exists n f,
  f 0 = s0 /\
  f n = sn /\
  forall i,
  i < n ->
  step (f i) (f (S i)).
Proof.
  induction 1.
  - exists 0.
    exists (fun _ => x).
    split. reflexivity.
    split. reflexivity.
    intros.
    lia.
  - destruct IHrtc as [n [f [? [? ?]]]].
    exists (S n).
    exists (fun n => match n with O => x | S i => f i end).
    split. reflexivity.
    split. assumption.
    intros.
    destruct i.
    + rewrite H1.
      assumption.
    + apply H3.
      lia.
Qed.

Fixpoint concat_seqs(f: state -> nat * (nat -> state))(s0: state)(k: nat) {struct k}: nat * (nat -> state) :=
  match k with
    O => let (n, seq) := f s0 in (S n, seq)
  | S k0 =>
    let (m, trace) := concat_seqs f s0 k0 in
    let (n, seq) := f (trace m) in
    (m + S n, fun i => if Nat.ltb i m then trace i else seq (i - m))
  end.

Lemma trace_intro (P: state -> Prop):
  (forall s0, P s0 -> exists s1 sN, step s0 s1 /\ rtc step s1 sN /\ P sN) ->
  forall s0,
  P s0 ->
  exists trace,
  (forall i, step (trace i) (trace (S i))) /\
  trace 0 = s0.
Proof.
  intros H.
  assert (forall s0, exists n_f, P s0 -> match n_f with (n, f) => f 0 = s0 /\ P (f (S n)) /\ forall i, i <= n -> step (f i) (f (S i)) end). {
    intros.
    destruct (classic (P s0)).
    - destruct (H s0 H0) as [s1 [sN [? [? ?]]]].
      apply rtc_f in H2.
      destruct H2 as [n [f [? [? ?]]]].
      exists (n, fun i => match i with O => s0 | S i => f i end).
      intros.
      split. reflexivity.
      split. rewrite H4. assumption.
      intros.
      destruct i.
      + rewrite H2.
        assumption.
      + apply H5.
        lia.
    - exists (O, fun _ => s0).
      intros.
      elim (H0 H1).
  }
  clear H.
  apply choice in H0.
  destruct H0 as [f Hf].
  intros s0 Hs0.
  assert (Hfst: forall k0, forall k1, k1 + fst (concat_seqs f s0 k0) <= fst (concat_seqs f s0 (k1 + k0))). {
    intros k0.
    induction k1.
    - simpl.
      lia.
    - simpl.
      case_eq (concat_seqs f s0 (k1 + k0)); intros.
      case_eq (f (s n)); intros.
      simpl.
      rewrite H in IHk1.
      simpl in IHk1.
      lia.
  }
  assert (HP: forall k, let (m, trace) := concat_seqs f s0 k in P (trace m)). {
    induction k.
    - simpl.
      case_eq (f s0); intros n seq Hfs0.
      pose proof (Hf s0 Hs0).
      rewrite Hfs0 in H.
      destruct H as [? [? ?]].
      assumption.
    - simpl.
      case_eq (concat_seqs f s0 k); intros m trace Hmtrace.
      case_eq (f (trace m)); intros n seq Hnseq.
      case_eq (Nat.ltb (m + S n) m); intros.
      + rewrite PeanoNat.Nat.ltb_lt in H.
        lia.
      + assert (m + S n - m = S n). lia. rewrite H0.
        rewrite Hmtrace in IHk.
        pose proof (Hf (trace m) IHk).
        rewrite Hnseq in H1.
        tauto.
  }
  assert (Hsnd: forall k0, forall k1, forall i, i <= fst (concat_seqs f s0 k0) -> snd (concat_seqs f s0 (k1 + k0)) i = snd (concat_seqs f s0 k0) i). {
    intro k0.
    induction k1.
    - intros.
      reflexivity.
    - intros.
      simpl.
      rewrite <- IHk1 with (1:=H).
      case_eq (concat_seqs f s0 (k1 + k0)); intros.
      case_eq (f (s n)); intros.
      simpl.
      case_eq (Nat.ltb i n); intros.
      + reflexivity.
      + apply PeanoNat.Nat.ltb_ge in H2.
        pose proof (Hfst k0 k1).
        rewrite H0 in H3.
        simpl in H3.
        assert (i = n). lia.
        subst.
        assert (n - n = 0). lia. rewrite H4.
        pose proof (HP (k1 + k0)).
        rewrite H0 in H5.
        pose proof (Hf (s n) H5).
        rewrite H1 in H6.
        tauto.
  }
  assert (Hf_step: forall k, let (m, trace) := concat_seqs f s0 k in forall i, i < m -> step (trace i) (trace (S i))). {
    induction k.
    - simpl.
      case_eq (f s0); intros n seq Hnseq.
      intros.
      pose proof (Hf s0 Hs0).
      rewrite Hnseq in H0.
      destruct H0 as [? [? ?]].
      apply H2.
      lia.
    - simpl.
      case_eq (concat_seqs f s0 k); intros m trace Hmtrace.
      rewrite Hmtrace in IHk.
      case_eq (f (trace m)); intros n seq Hnseq.
      intros.
      case_eq (Nat.ltb i m); intros.
      + rewrite PeanoNat.Nat.ltb_lt in H0.
        case_eq (Nat.ltb (S i) m); intros.
        * rewrite PeanoNat.Nat.ltb_lt in H1.
          apply IHk.
          lia.
        * rewrite PeanoNat.Nat.ltb_ge in H1.
          assert (m = S i). lia. rewrite H2.
          assert (S i - S i = 0). lia. rewrite H3.
          pose proof (HP k).
          rewrite Hmtrace in H4.
          pose proof (Hf (trace m) H4).
          rewrite Hnseq in H5.
          destruct H5 as [? [? ?]].
          rewrite H5.
          subst.
          apply IHk.
          assumption.
      + rewrite PeanoNat.Nat.ltb_ge in H0.
        case_eq (Nat.ltb (S i) m); intros.
        * rewrite PeanoNat.Nat.ltb_lt in H1.
          lia.
        * rewrite PeanoNat.Nat.ltb_ge in H1.
          pose proof (HP k).
          rewrite Hmtrace in H2.
          pose proof (Hf (trace m) H2).
          rewrite Hnseq in H3.
          destruct H3 as [? [? ?]].
          assert (S i - m = S (i - m)). lia. rewrite H6.
          apply H5.
          lia.
  }
  exists (fun i => snd (concat_seqs f s0 i) i).
  split.
  - intros.
    pose proof (Hsnd i 1 (S i)).
    assert (1 + i = S i). reflexivity. rewrite H0 in H.
    rewrite H. 2:{
      pose proof (Hfst 0 i).
      case_eq (concat_seqs f s0 0); intros m trace Hmtrace.
      rewrite Hmtrace in H1.
      assert (i + 0 = i). lia. rewrite H2 in H1.
      case_eq (concat_seqs f s0 i); intros mi tracei Hmtracei.
      rewrite Hmtracei in H1.
      simpl in H1.
      simpl.
      simpl in Hmtrace.
      case_eq (f s0); intros n seq Hnseq.
      rewrite Hnseq in Hmtrace.
      injection Hmtrace; clear Hmtrace; intros; subst.
      lia.
    }
    case_eq (concat_seqs f s0 i); intros m trace Hmtrace.
    pose proof (Hf_step i).
    rewrite Hmtrace in H1.
    apply H1.
    pose proof (Hfst 0 i).
    assert (i + 0 = i). lia. rewrite H3 in H2.
    rewrite Hmtrace in H2.
    simpl in H2.
    case_eq (f s0); intros n seq Hnseq.
    rewrite Hnseq in H2.
    simpl in H2.
    lia.
  - simpl.
    case_eq (f s0); intros n seq Hnseq.
    simpl.
    pose proof (Hf s0 Hs0).
    rewrite Hnseq in H.
    tauto.
Qed.

Lemma diverges_step_lemma c:
  diverges c ->
  exists trace,
  (forall i, step (trace i) (trace (S i))) /\
  trace 0 = (c, None, []).
Proof.
  intro Hc.
  apply trace_intro with (P:=fun state => exists c k, state = (c, None, k) /\ diverges c).
  2:{
    exists c.
    exists [].
    tauto.
  }
  intros.
  clear c Hc.
  destruct H as [c [k [Hs0 H]]].
  inversion H; clear H; subst.
  destruct ps0 as [|[pc0 pr0] ps0'].
  - simpl in H0.
    eexists.
    eexists.
    split. {
      eapply step_enter. eassumption.
    }
    split. apply rtc_refl.
    eexists; eexists.
    split. reflexivity.
    assumption.
  - simpl in H0.
    exists (pc0, None, ([], pc0)::k).
    
    eapply step_enter. eassumption.
    