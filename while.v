Require Import BinInt.
Require Import Arith.

(* Needed to define cpo_lub *)
Require Import Classical.
Require Import ClassicalDescription.

Definition mem := nat -> Z.
Definition expr := mem -> Z.

Inductive stat :=
| Skip : stat
| Stop : stat
| Assign : nat -> expr -> stat
| Seq : stat -> stat -> stat
| If : expr -> stat -> stat -> stat
| While : expr -> stat -> stat.

Definition update (m : mem) x z y := if x =? y then z else m y.

Inductive cpo (A : Type) :=
| Bottom : cpo A
| Some : A -> cpo A.

Arguments Bottom [A].
Arguments Some [A].

Definition cpo_leq {A : Type} (u v : cpo A) := (u = Bottom) \/ (u = v).

Lemma cpo_leq_trans {A : Type} :
  forall u v w : cpo A, cpo_leq u v -> cpo_leq v w -> cpo_leq u w.
Proof.
  intros u v w H1 H2; unfold cpo_leq in *; destruct u; destruct v; destruct w; destruct H1 as [H1|H1]; destruct H2 as [H2|H2]; inversion H1; inversion H2; auto.
Qed.

Definition cpo_chain {A : Type} (f : nat -> cpo A) := forall n, cpo_leq (f n) (f (S n)).

Lemma cpo_chain_leq {A : Type} : forall (f : nat -> cpo A), cpo_chain f -> forall x y, f x <> Bottom -> x <= y -> f y = f x.
Proof.
  intros f H1 x y H2 H3. induction H3. auto. specialize (H1 m). unfold cpo_leq in *. destruct H1; congruence.
Qed.

Lemma cpo_chain_add {A : Type} (f : nat -> cpo A) (H : cpo_chain f) :
  forall n p : nat, cpo_leq (f n) (f (n + p)).
Proof.
  induction p as [|p Hp].
  - simpl; unfold cpo_leq; auto.
  - simpl. apply cpo_leq_trans with (v := f (n + p)).
    + auto.
    + rewrite <- plus_n_Sm. apply H.
Qed.

Lemma cpo_lub_lemma {A : Type} : forall (f : nat -> cpo A), cpo_chain f -> exists!x, forall y, cpo_leq x y <-> (forall n, cpo_leq (f n) y).
Proof.
  intros f H. destruct (classic (exists n, f n <> Bottom)) as [[x H1] | H1].
  - exists (f x).
    assert (H2 : forall n, f n = Bottom \/ f n = f x).
    + intros n. destruct (le_lt_dec n x) as [H2 | H2].
      * classical_right. symmetry. apply cpo_chain_leq; auto.
      * right. apply cpo_chain_leq; auto. auto using Nat.lt_le_incl.
    + split. intro y. split.
      * intros H3 n. destruct (H2 n) as [H4 | H4]; rewrite H4; [unfold cpo_leq|]; auto.
      * intros H3; auto.
      * intros x' H3.
        assert (H4 : cpo_leq (f x) x'). apply H3. unfold cpo_leq; auto.
        unfold cpo_leq in H4; destruct H4; congruence.
  - exists Bottom.
    assert (H1' : forall n, f n = Bottom) by (intro; apply NNPP; eauto).
    split.
    + intro y. split.
      * intros. rewrite H1'. auto.
      * intros. unfold cpo_leq; auto.
    + intros x H2. destruct (H2 Bottom) as [H3 H4]. destruct H4.
      intro. rewrite H1'. unfold cpo_leq; auto. auto. auto.
Qed.

Definition cpo_lub {A : Type} (f : nat -> cpo A) (H : cpo_chain f) := proj1_sig (constructive_definite_description _ (cpo_lub_lemma f H)).

Lemma cpo_lub_def : forall {A : Type} (f : nat -> cpo A) (H : cpo_chain f) (x : cpo A),
    cpo_lub f H = x <-> (forall y, cpo_leq x y <-> (forall n, cpo_leq (f n) y)).
Proof.
  intros A f Hc x.
  unfold cpo_lub.
  remember (constructive_definite_description _ (cpo_lub_lemma f Hc)) as y.
  simpl. destruct y as [y Hy].
  split.
  - intros H; subst; auto.
  - intros H. destruct (cpo_lub_lemma f Hc) as [z [Hex Hun]].
    simpl. transitivity z; [symmetry|]; apply Hun; auto.
Qed.

Lemma cpo_lub_def_eq :
  forall {A : Type} (f : nat -> cpo A) (H : cpo_chain f) (x : cpo A),
    cpo_leq (cpo_lub f H) x <-> forall n, cpo_leq (f n) x.
Proof.
  intros A f H. rewrite <- cpo_lub_def. auto.
Qed.

Lemma cpo_lub_eq_some :
  forall {A : Type} (f : nat -> cpo A) (H : cpo_chain f) (n : nat), f n <> Bottom -> cpo_lub f H = f n.
Proof.
  intros A f H1 n H2.
  apply cpo_lub_def.
  intros y. split.
  - intros H3 n1. unfold cpo_leq in H3.
    destruct H3 as [H3 | H3]; try congruence. rewrite <- H3.
    destruct (le_lt_dec n1 n) as [H4 | H4].
    + rewrite <- le_plus_minus_r with (n := n1) (m := n); auto.
      apply cpo_chain_add; auto.
    + unfold cpo_leq; classical_right. apply cpo_chain_leq; auto using Nat.lt_le_incl.
  - intros; auto.
Qed.

Lemma cpo_lub_eq :
  forall {A : Type} (f : nat -> cpo A) (H : cpo_chain f),
  exists (n : nat), cpo_lub f H = f n.
Proof.
  intros A f H.
  destruct (classic (exists n, f n <> Bottom)) as [[x H1] | H1].
  - exists x. apply cpo_lub_eq_some; auto.
  - exists 0. apply cpo_lub_def.
    assert (forall n, f n = Bottom).
    + intros n. destruct (classic (f n = Bottom)); auto.
      exfalso; apply H1; exists n; auto.
    + rewrite H0. intros y; split; intros H2.
      * intros n; rewrite H0; unfold cpo_leq; auto.
      * unfold cpo_leq; auto.
Qed.

Lemma cpo_lub_ext :
  forall {A : Type} (f1 f2 : nat -> cpo A) (H1 : cpo_chain f1) (H2 : cpo_chain f2),
    (forall n : nat, f1 n = f2 n) -> cpo_lub f1 H1 = cpo_lub f2 H2.
Proof.
  intros A f1 f2 H1 H2 Heq.
  apply cpo_lub_def. intros y. split.
  - intros H3. rewrite cpo_lub_def_eq in H3. intros; rewrite Heq; auto.
  - intros H3. rewrite cpo_lub_def_eq. intros; rewrite <- Heq; auto.
Qed.

Lemma subchain_chain :
  forall {A : Type} (f : nat -> cpo A) (H : cpo_chain f) (p : nat), cpo_chain (fun n => f (n + p)).
Proof.
  intros A f H p n. apply H.
Qed.

Lemma cpo_lub_subchain :
  forall {A : Type} (f : nat -> cpo A) (H : cpo_chain f) (p : nat),
    cpo_lub f H = cpo_lub _ (subchain_chain f H p).
Proof.
  intros A f H p. apply cpo_lub_def.
  intros y.
  split.
  - intros H2. rewrite cpo_lub_def_eq in H2.
    intros n. apply cpo_leq_trans with (v := f (n + p)).
    + apply cpo_chain_add; auto.
    + auto.
  - intros H2. apply cpo_lub_def_eq. intros; auto.
Qed.

Definition ifapply e (f1 f2 : cpo mem -> cpo mem) m :=
  match m with
  | Bottom => Bottom
  | Some m => if (e m =? 0)%Z then f2 (Some m) else f1 (Some m)
  end.

Lemma ifapply_monotone :
  forall e f1 f2 m1 m2,
    cpo_leq m1 m2 -> cpo_leq (ifapply e f1 f2 m1) (ifapply e f1 f2 m2).
Proof.
  intros e f1 f2 m1 m2 H.
  destruct m1; destruct m2; destruct H; unfold cpo_leq in *; simpl; inversion H; auto.
Qed.

Fixpoint while_n n e f :=
  match n with
  | 0 => ifapply e (fun _ => Bottom) id
  | S n => (fun m => while_n n e f (ifapply e f id m))
  end.

Lemma while_n_bottom :
  forall n e f, while_n n e f Bottom = Bottom.
Proof.
  induction n as [|n H].
  - intros; simpl; auto.
  - intros; simpl; rewrite H; auto.
Qed.

Lemma while_n_monotone :
  forall n e f m1 m2, cpo_leq m1 m2 -> cpo_leq (while_n n e f m1) (while_n n e f m2).
Proof.
  induction n as [|n H1].
  - intros e f m1 m2 H2. simpl. apply ifapply_monotone; auto.
  - intros e f m1 m2 H2. simpl. apply H1. apply ifapply_monotone; auto.
Qed.

Lemma while_n_leq :
  forall n e f m, cpo_leq (while_n n e f m) (while_n (S n) e f m).
Proof.
  induction n as [|n H].
  - intros e f m; simpl; unfold ifapply. destruct m as [|m].
    + unfold cpo_leq; auto.
    + destruct ((e m =? 0)%Z) eqn:He; repeat (simpl; rewrite He).
      * unfold cpo_leq; auto.
      * unfold cpo_leq; auto.
  - intros e f m. simpl. apply H.
Qed.

Lemma while_n_chain :
  forall e f m, cpo_chain (fun n => while_n n e f m).
Proof.
  intros e f m n. apply while_n_leq.
Qed.

Fixpoint sem s m :=
  match s, m with
  | _, Bottom | Stop, _ => Bottom
  | Skip, Some m => Some m
  | Assign x e, Some m => Some (update m x (e m))
  | Seq s1 s2, m => sem s2 (sem s1 m)
  | If e s1 s2, m => ifapply e (sem s1) (sem s2) m
  | While e s, Some m => cpo_lub (fun n => while_n n e (sem s) (Some m)) (while_n_chain e (sem s) (Some m))
  end.

Notation "[[ s ]]" := (sem s) (at level 30).

Lemma sem_bottom :
  forall s, [[s]] Bottom = Bottom.
Proof.
  intros s. destruct s; auto.
Qed.

(* Not used, but here it is anyway. *)
Lemma while_fixpoint :
  forall e s m, [[While e s]] m = [[Seq (If e s Skip) (While e s)]] m.
Proof.
  intros e s m. simpl.
  destruct m as [|m].
  - auto.
  - simpl.
    destruct (e m =? 0)%Z eqn:H.
    + auto.
    + destruct ([[s]](Some m)) eqn:H2.
      * apply cpo_lub_def. intros x; split.
        -- intros H3 n. destruct n; simpl.
           ++ rewrite H; auto.
           ++ rewrite H; simpl. rewrite H2. rewrite while_n_bottom; auto.
        -- intros; unfold cpo_leq; auto.
      * rewrite cpo_lub_subchain with (p := 1).
        apply cpo_lub_ext. intros n.
        rewrite <- plus_n_Sm. simpl. rewrite <- plus_n_O.
        rewrite H. rewrite <- H2. auto.
Qed.

Inductive HoareTripleP : (mem -> Prop) -> stat -> (mem -> Prop) -> Prop :=
| HSkip : forall phi, HoareTripleP phi Skip phi
| HStop : forall phi psi, HoareTripleP phi Stop psi
| HAssign : forall phi x e, HoareTripleP (fun m => phi (update m x (e m))) (Assign x e) phi
| HSeq : forall phi pi psi s1 s2, HoareTripleP phi s1 pi -> HoareTripleP pi s2 psi -> HoareTripleP phi (Seq s1 s2) psi
| HConseq : forall (phi1 phi2 psi1 psi2 : mem -> Prop) s, (forall m, phi1 m -> phi2 m) -> (forall m, psi2 m -> psi1 m) -> HoareTripleP phi2 s psi2 -> HoareTripleP phi1 s psi1
| HIf : forall phi psi e s1 s2, HoareTripleP (fun m => phi m /\ (e m <> 0)%Z) s1 psi -> HoareTripleP (fun m => phi m /\ (e m = 0)%Z) s2 psi -> HoareTripleP phi (If e s1 s2) psi
| HWhile : forall I e s, HoareTripleP (fun m => I m /\ (e m <> 0)%Z) s I -> HoareTripleP I (While e s) (fun m => I m /\ (e m = 0)%Z).

Notation "|- {{ phi }} s {{ psi }}" := (HoareTripleP phi s psi) (at level 90, s at next level).

Notation "m |= phi" := (phi m) (at level 80, only parsing).
Notation "m |== phi" := (match m with Bottom => True | Some m1 => m1 |= phi end) (at level 80).

Definition HoareTriple phi s psi :=
  forall m, m |= phi -> [[s]] (Some m) |== psi.

Notation "|= {{ phi }} s {{ psi }}" := (HoareTriple phi s psi) (at level 90, s at next level).

Lemma while_n_preserve :
  forall s I e n m, (|= {{ fun m => I m /\ (e m <> 0)%Z }} s {{ I }}) -> I m ->
               (while_n n e ([[s]]) (Some m) |== (fun m => I m /\ (e m = 0)%Z)).
Proof.
  intros s I e n. induction n as [|n H].
  - intros m Hinv HI. simpl.
    destruct (e m =? 0)%Z eqn:Heq; simpl.
    + split; auto. apply Z.eqb_eq; auto.
    + auto.
  - intros m Hinv HI. simpl.
    remember (if (e m =? 0)%Z then id (Some m) else ([[s]]) (Some m)) as m1.
    destruct m1 as [|m1].
    + rewrite while_n_bottom; auto.
    + apply H; auto.
      destruct (e m =? 0)%Z eqn:Heq; simpl in Heqm1.
      * unfold id in Heqm1; congruence.
      * specialize (Hinv m); simpl in *. rewrite <- Heqm1 in Hinv.
        apply Hinv; split; auto. apply Z.eqb_neq; auto.
Qed.

(* This proof was done without the termination lemma, which has not been
   formally proved.
 *)
Lemma HoareTriple_correct :
  forall s phi psi, (|- {{ phi }} s {{ psi }}) -> (|= {{ phi }} s {{ psi }}).
Proof.
  intros s phi psi H. induction H.
  - intros m; simpl; auto.
  - intros m; simpl; auto.
  - intros m; simpl; auto.
  - intros m H1; simpl.
    destruct ([[s1]] (Some m)) eqn:H2.
    + rewrite sem_bottom; auto.
    + apply IHHoareTripleP2. specialize (IHHoareTripleP1 m); rewrite H2 in *; auto.
  - intros m; simpl.
    destruct ([[s]] (Some m)) eqn:H2.
    + auto.
    + intros H3; apply H0; specialize (IHHoareTripleP m); rewrite H2 in *; auto.
  - intros m H1; simpl.
    destruct ((e m =? 0)%Z) eqn:H2.
    + apply IHHoareTripleP2; split; auto. apply Z.eqb_eq; auto.
    + apply IHHoareTripleP1; split; auto. apply Z.eqb_neq; auto.
  - intros m H1. destruct ([[While e s]] (Some m)) as [|m1] eqn:Heq; simpl.
    + auto.
    + simpl in Heq.
      destruct (cpo_lub_eq _ (while_n_chain e ([[s]]) (Some m))) as [n H2].
      rewrite H2 in Heq.
      assert (while_n n e ([[s]]) (Some m) |== (fun m => I m /\ (e m = 0)%Z)) by (apply while_n_preserve; auto).
      rewrite Heq in *; auto.
Qed.

Inductive annot (A : Type) : stat -> Type :=
| Nskip : annot A Skip
| Nstop : annot A Stop
| Nassign : forall x e, annot A (Assign x e)
| Nseq : forall s1 s2, annot A s1 -> annot A s2 -> annot A (Seq s1 s2)
| Nif : forall e s1 s2, annot A s1 -> annot A s2 -> annot A (If e s1 s2)
| Nwhile : forall e s, A -> annot A s -> annot A (While e s).

Arguments Nskip [A].
Arguments Nstop [A].
Arguments Nassign [A].
Arguments Nseq [A].
Arguments Nif [A].
Arguments Nwhile [A].

(* It would be nicer to do match s, a with | Skip, Nskip => ...,
   but Coq dependant typing faculties are not enough to handle this,
   unfortunately. *)
Fixpoint wp (s : stat) (a : annot (mem -> Prop) s) (phi : mem -> Prop) : (mem -> Prop) :=
  match a with
  | Nskip => phi
  | Nstop => fun m => True
  | Nassign x e => fun m => phi (update m x (e m))
  | Nseq s1 s2 a1 a2 => wp s1 a1 (wp s2 a2 phi)
  | Nif e s1 s2 a1 a2 => fun m => ((e m <> 0)%Z -> wp s1 a1 phi m) /\ ((e m = 0)%Z -> wp s2 a2 phi m)
  | Nwhile e s P a => fun m => P m /\ (forall m1, (e m1 <> 0)%Z -> P m1 -> wp s a P m1) /\
                           (forall m1, (e m1 = 0)%Z -> P m1 -> phi m1)
  end.

Lemma wp_imp : forall s a (phi psi : mem -> Prop), (forall m, phi m -> psi m) -> (forall m, wp s a phi m -> wp s a psi m).
Proof.
  intros s. induction a; simpl; intros phi psi H m; auto.
  - intros H1; eapply IHa1; [|apply H1]. eapply IHa2. auto.
  - intros [H1 H2]; split; intros H3.
    + eapply IHa1; eauto.
    + eapply IHa2; eauto.
  - intros [H1 [H2 H3] ]; split; auto.
Qed.

Lemma wp_and : forall s a phi psi m, psi /\ (wp s a phi) m -> wp s a (fun m => phi m /\ psi) m.
Proof.
  intros s. induction a; simpl; intros phi psi m; try tauto.
  - intros [Hpsi H]. eapply wp_imp; [|apply H].
    intros m0 H0. apply IHa2; auto.
  - intros [Hpsi [H1 H2] ]. split; intros H3.
    + apply IHa1; auto.
    + apply IHa2; auto.
  - intros [Hpsi [H1 [H2 H3] ] ]. split; auto.
Qed.

Theorem wp_correct : forall s a phi, |- {{wp s a phi}} s {{phi}}.
Proof.
  intros s. induction a.
  - simpl. intros phi. apply HSkip.
  - simpl. intros phi. apply HStop.
  - simpl. intros phi. apply HAssign.
  - simpl. intros phi. eapply HSeq; auto.
  - simpl. intros phi. apply HIf.
    + eapply HConseq with (psi2 := phi); [|auto|apply IHa1]. intros; tauto.
    + eapply HConseq with (psi2 := phi); [|auto|apply IHa2]. intros; tauto.
  - simpl. intros phi.
    eapply HConseq; [intros m H; exact H| |eapply HWhile].
    + intros m H. simpl in H. destruct H as [ [H1 [H2 H3] ] H4].
      apply H3; auto.
    + eapply HConseq; [|intros m H; exact H|apply IHa].
      intros m [ [H1 [H2 H3] ] H4]. apply wp_and. split; auto.
Qed.

Inductive assertion :=
| Top : assertion
| Bot : assertion
| Not : assertion -> assertion
| And : assertion -> assertion -> assertion
| Or : assertion -> assertion -> assertion
| Implies : assertion -> assertion -> assertion
| Zexpr : expr -> assertion
| VForall : nat -> assertion -> assertion
| VExists : nat -> assertion -> assertion
| MForall : assertion -> assertion
| MExists : assertion -> assertion
| Subst : nat -> expr -> assertion -> assertion.

Fixpoint asem (a : assertion) (m : mem) :=
  match a with
  | Top => True
  | Bot => False
  | Not a => ~(asem a m)
  | And a1 a2 => (asem a1 m) /\ (asem a2 m)
  | Or a1 a2 => (asem a1 m) \/ (asem a2 m)
  | Implies a1 a2 => (asem a1 m) -> (asem a2 m)
  | Zexpr e => (e m = 0)%Z
  | VForall n a => forall x, asem a (update m n x)
  | VExists n a => exists x, asem a (update m n x)
  | MForall a => forall m1, asem a m1
  | MExists a => exists m1, asem a m1
  | Subst n e a => asem a (update m n (e m))
  end.

Fixpoint wps (s : stat) (a : annot assertion s) (phi : assertion) :=
  match a with
  | Nskip => phi
  | Nstop => Top
  | Nassign x e => Subst x e phi
  | Nseq s1 s2 a1 a2 => wps s1 a1 (wps s2 a2 phi)
  | Nif e s1 s2 a1 a2 => And (Implies (Not (Zexpr e)) (wps s1 a1 phi)) (Implies (Zexpr e) (wps s2 a2 phi))
  | Nwhile e s P a => And P (And
       (MForall (Implies (Not (Zexpr e)) (Implies P (wps s a P))))
       (MForall (Implies (Zexpr e) (Implies P phi))))
  end.

Fixpoint amap {A B : Type} (s : stat) (a : annot A s) (f : A -> B) :=
  match a with
  | Nskip => Nskip
  | Nstop => Nstop
  | Nassign x e => Nassign x e
  | Nseq s1 s2 a1 a2 => Nseq s1 s2 (amap s1 a1 f) (amap s2 a2 f)
  | Nif e s1 s2 a1 a2 => Nif e s1 s2 (amap s1 a1 f) (amap s2 a2 f)
  | Nwhile e s P a => Nwhile e s (f P) (amap s a f)
  end.

Lemma wps_wp : forall s a phi, asem (wps s a phi) = wp s (amap s a asem) (asem phi).
Proof.
  induction a; intros; simpl; auto.
  - rewrite IHa1; rewrite IHa2; auto.
  - rewrite IHa1; rewrite IHa2; auto.
  - rewrite IHa; auto.
Qed.

Theorem wps_correct : forall s a phi, |- {{asem (wps s a phi)}} s {{asem phi}}.
Proof.
  intros. rewrite wps_wp. apply wp_correct.
Qed.

Theorem wps_correct2: forall s a phi, |= {{asem (wps s a phi)}} s {{asem phi}}.
Proof.
  intros. apply HoareTriple_correct. apply wps_correct.
Qed.

Require Extraction.
Extraction wps.

(* Note how the extracted function doesn't depend on s itself but on the
   annotation only. This is because the annotation contains all the
   information needed to reconstruct s, and we didn't use match s, a with ...
   but match a with ... only.
   Besides, it is interesting to note how the computation of precondition
   can grow to very large sizes, even for simple programs, due to the
   duplication for cases like If.
 *)