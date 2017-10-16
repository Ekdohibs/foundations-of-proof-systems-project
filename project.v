(* -------------------------------------------------------------------- *)
Require Import Arith List.
From Autosubst Require Import Autosubst.
Require Import Coq.Logic.FunctionalExtensionality.

Inductive expr : Type :=
| Var (_ : var)
| Zero
| Succ (_ : expr)
| Plus (_ : expr) (_ : expr)
| Mult (_ : expr) (_ : expr).

Infix "@+" := Plus (at level 50, left associativity).
Infix "@*" := Mult (at level 40, left associativity).

Inductive formula : Type :=
| Bottom
| DummyVar (_ : var)
| Implies (_ : formula) (_ : formula)
| And (_ : formula) (_ : formula)
| Or (_ : formula) (_ : formula)
| Eq (_ : expr) (_ : expr)
| Forall (_ : {bind expr in formula})
| Exists (_ : {bind expr in formula}).

Notation "x @-> y" := (Implies x y) (at level 99, right associativity, y at level 200).
Infix "@/\" := And (at level 80, right associativity).
Infix "@\/" := Or (at level 85, right associativity).
Infix "@=" := Eq (at level 70).

Instance Ids_expr : Ids expr. derive. Defined.
Instance Rename_expr : Rename expr. derive. Defined.
Instance Subst_expr : Subst expr. derive. Defined.
Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.
Instance HSubst_formula : HSubst expr formula. derive. Defined.
Instance Ids_formula : Ids formula. derive. Defined.
Instance Rename_formula : Rename formula. derive. Defined.
Instance Subst_formula : Subst formula. derive. Defined.
Instance HSubstLemmas_formula : HSubstLemmas expr formula. derive. Qed.
Instance SubstHSubstComp_expr_formula : SubstHSubstComp expr formula. derive. Qed.
Instance SubstLemmas_formula : SubstLemmas formula. derive. Qed.

Lemma subst_cons :
  forall A Gamma sigma, (A :: Gamma)..|[sigma] = A.|[sigma] :: Gamma..|[sigma].
Proof.
  auto.
Qed.

Lemma subst_app :
  forall Gamma Delta sigma, (Gamma ++ Delta)..|[sigma] = Gamma..|[sigma] ++ Delta..|[sigma].
Proof.
  intros Gamma Delta sigma; induction Gamma.
  - simpl; auto.
  - simpl. f_equal. auto.
Qed.

Definition env := list formula.
Inductive nd (ax : formula -> Type) : env -> formula -> Type :=
| Nd_axiom : forall A Gamma, ax A -> nd ax Gamma A
| Nd_assume : forall A Gamma, nd ax (A :: Gamma) A
| Nd_weak : forall A B Gamma, nd ax Gamma A -> nd ax (B :: Gamma) A
| Nd_impI : forall A B Gamma, nd ax (A :: Gamma) B -> nd ax Gamma (Implies A B)
| Nd_impE : forall A B Gamma, nd ax Gamma (Implies A B) -> nd ax Gamma A -> nd ax Gamma B
| Nd_andI : forall A B Gamma, nd ax Gamma A -> nd ax Gamma B -> nd ax Gamma (And A B)
| Nd_andEL : forall A B Gamma, nd ax Gamma (And A B) -> nd ax Gamma A
| Nd_andER : forall A B Gamma, nd ax Gamma (And A B) -> nd ax Gamma B
| Nd_orIL : forall A B Gamma, nd ax Gamma A -> nd ax Gamma (Or A B)
| Nd_orIR : forall A B Gamma, nd ax Gamma B -> nd ax Gamma (Or A B)
| Nd_orE : forall A B C Gamma, nd ax Gamma (Or A B) -> nd ax (A :: Gamma) C -> nd ax (B :: Gamma) C -> nd ax Gamma C
| Nd_botE : forall A Gamma, nd ax Gamma Bottom -> nd ax Gamma A
| Nd_forallI : forall A Gamma, nd ax Gamma..|[ren (+1)] A -> nd ax Gamma (Forall A)
| Nd_forallE : forall A Gamma t, nd ax Gamma (Forall A) -> nd ax Gamma A.|[t/]
| Nd_existI : forall A Gamma t, nd ax Gamma A.|[t/] -> nd ax Gamma (Exists A)
| Nd_existE : forall A B Gamma, nd ax Gamma (Exists A) -> nd ax (A :: Gamma..|[ren (+1)]) B.|[ren (+1)] -> nd ax Gamma B
| Nd_eq_refl : forall Gamma t, nd ax Gamma (t @= t)
| Nd_eq_elim : forall Gamma A t1 t2, nd ax Gamma (t1 @= t2) -> nd ax Gamma A.|[t1/] -> nd ax Gamma A.|[t2/].

Ltac nd_clear n :=
  match n with
  | 0 => idtac
  | S ?n => apply Nd_weak; nd_clear n
  end.

Ltac nd_assumption_n n :=
  nd_clear n; apply Nd_assume.

Ltac nd_assumption' :=
  solve [apply Nd_assume | apply Nd_weak; nd_assumption'].

Tactic Notation "nd_assumption" := nd_assumption'.
Tactic Notation "nd_assumption" constr(n) := nd_assumption_n n.

Fixpoint tr_expr sigma e :=
  match e with
  | Var n => sigma n
  | Zero => 0
  | Succ e => S (tr_expr sigma e)
  | e1 @+ e2 => (tr_expr sigma e1) + (tr_expr sigma e2)
  | e1 @* e2 => (tr_expr sigma e1) * (tr_expr sigma e2)
  end.

Fixpoint tr_formula sigma A : Type :=
  match A with
  | Bottom => False
  | DummyVar _ => True
  | A @-> B => (tr_formula sigma A) -> (tr_formula sigma B)
  | A @/\ B => (tr_formula sigma A) * (tr_formula sigma B)
  | A @\/ B => (tr_formula sigma A) + (tr_formula sigma B)
  | e1 @= e2 => (tr_expr sigma e1) = (tr_expr sigma e2)
  | Forall A => forall x, tr_formula (x .: sigma) A
  | Exists A => sigT (fun x => tr_formula (x .: sigma) A)
  end.

Definition tr_env sigma Gamma := fold_right prod True (map (tr_formula sigma) Gamma).
Hint Unfold tr_env.

Lemma tr_env_rw : forall sigma A Gamma, tr_env sigma (A :: Gamma) = (tr_formula sigma A * tr_env sigma Gamma)%type.
Proof.
  intros; unfold tr_env; auto.
Qed.

Lemma tr_expr_subst : forall e sigma xi, tr_expr xi e.[sigma] = tr_expr (fun x => tr_expr xi (sigma x)) e.
Proof.
  intros e; induction e; intros; simpl; auto.
Qed.

Lemma tr_expr_extensionality : forall e sigma1 sigma2,
    (forall x, sigma1 x = sigma2 x) -> tr_expr sigma1 e = tr_expr sigma2 e.
Proof.
  intros e; induction e; intros; simpl; auto.
Qed.

Ltac sigT_extensionality x :=
  f_equal; [intros H1 H2; rewrite H2; reflexivity | extensionality x].

Lemma sigT_extensionality : forall A (P1 P2 : A -> Type),
    (forall x, P1 x = P2 x) -> {x : A & P1 x} = {x : A & P2 x}.
Proof.
  intros A P1 P2 H. f_equal; auto. extensionality x; auto.
Qed.

Lemma tr_formula_extensionality : forall A sigma1 sigma2,
    (forall x, sigma1 x = sigma2 x) -> tr_formula sigma1 A = tr_formula sigma2 A.
Proof.
  intros A; induction A; intros; simpl; try auto.
  - rewrite (IHA1 sigma1 sigma2 H); rewrite (IHA2 sigma1 sigma2 H); auto.
  - rewrite (IHA1 sigma1 sigma2 H); rewrite (IHA2 sigma1 sigma2 H); auto.
  - rewrite (IHA1 sigma1 sigma2 H); rewrite (IHA2 sigma1 sigma2 H); auto.
  - repeat (rewrite (tr_expr_extensionality _ sigma1 sigma2); auto).
  - extensionality x. apply IHA. intros [|n]; autosubst.
  - sigT_extensionality x. apply IHA. intros [|n]; autosubst.
Qed.

Lemma tr_env_extensionality : forall Gamma sigma1 sigma2,
    (forall x, sigma1 x = sigma2 x) -> tr_env sigma1 Gamma = tr_env sigma2 Gamma.
Proof.
  intros Gamma; induction Gamma.
  - intros; unfold tr_env; simpl; auto.
  - intros; unfold tr_env; simpl.
    erewrite tr_formula_extensionality; auto.
    f_equal. apply IHGamma; auto.
Qed.

Lemma tr_formula_subst : forall A sigma xi, tr_formula xi A.|[sigma] = tr_formula (fun x => tr_expr xi (sigma x)) A.
Proof.
  intros A; induction A; intros; simpl; auto.
  - rewrite IHA1; rewrite IHA2; auto.
  - rewrite IHA1; rewrite IHA2; auto.
  - rewrite IHA1; rewrite IHA2; auto.
  - repeat (rewrite tr_expr_subst); auto.
  - extensionality x. rewrite IHA. apply tr_formula_extensionality.
    intros [|n]; simpl; asimpl; auto.
    rewrite tr_expr_subst. apply tr_expr_extensionality. intros; simpl; auto.
  - sigT_extensionality x. rewrite IHA. apply tr_formula_extensionality.
    intros [|n]; simpl; asimpl; auto.
    rewrite tr_expr_subst. apply tr_expr_extensionality. intros; simpl; auto.
Qed.

Lemma tr_formula_subst1 : forall A sigma e, tr_formula sigma A.|[e/] = tr_formula ((tr_expr sigma e) .: sigma) A.
Proof.
  intros A sigma e; rewrite tr_formula_subst; apply tr_formula_extensionality.
  intros [|n]; simpl; auto.
Qed.

Lemma tr_env_subst : forall Gamma sigma xi, tr_env xi Gamma..|[sigma] = tr_env (fun x => tr_expr xi (sigma x)) Gamma.
Proof.
  intros Gamma; induction Gamma.
  - intros; unfold tr_env; simpl; auto.
  - intros sigma xi; unfold tr_env; simpl; asimpl.
    rewrite tr_formula_subst. f_equal.
    unfold tr_env in IHGamma. rewrite <- IHGamma. auto.
Qed.

(*
Definition test := Forall (Exists (Or (Eq (Var 1) (Succ (Var 0))) (Eq (Var 1) Zero))).
Parameter f : var -> nat.
Compute tr_formula f test.
 *)

Notation Not := (fun P => P @-> Bottom).
Notation "@~ x" := (Not x) (at level 75, right associativity).

Inductive PeanoAxioms : formula -> Type :=
| Peano_0_ne_Sn : PeanoAxioms (Forall (@~ (Succ (Var 0) @= Zero)))
| Peano_ne_0_Sn : PeanoAxioms (Forall (Exists ((@~ (Var 1 @= Zero)) @-> (Succ (Var 0) @= Var 1))))
| Peano_S_inj : PeanoAxioms (Forall (Forall ((Succ (Var 1) @= Succ (Var 0)) @-> (Var 1 @= Var 0))))
| Peano_plus_0 : PeanoAxioms (Forall (Var 0 @+ Zero @= Var 0))
| Peano_plus_S : PeanoAxioms (Forall (Forall (Succ (Var 1) @+ Var 0 @= Succ (Var 1 @+ Var 0))))
| Peano_mult_0 : PeanoAxioms (Forall (Zero @* Var 0 @= Zero))
| Peano_mult_S : PeanoAxioms (Forall (Forall (Succ (Var 1) @* Var 0 @= Var 1 @* Var 0 @+ Var 0)))
| Peano_rec : forall P, PeanoAxioms (P.|[Zero/] @-> ((Forall (Implies P P.|[Succ (Var 0) .: ren (+1)])) @-> (Forall P))).

Notation Heyting := (nd PeanoAxioms).

Theorem reflect : forall Gamma A, Heyting Gamma A -> forall sigma, tr_env sigma Gamma -> tr_formula sigma A.
Proof.
  intros Gamma A dn; elim dn.
  - intros A0 Gamma0 H sigma Henv.
    destruct H; simpl; try (intros; auto; congruence).
    + intros [|n].
      * exists 0; intros; exfalso; auto.
      * exists n; auto.
    + intros; apply plus_comm.
    + intros H0 HI x; induction x as [|x IHx]; simpl in *.
      * rewrite tr_formula_subst1 in H0. auto.
      * specialize (HI x IHx). rewrite tr_formula_subst in HI.
        erewrite tr_formula_extensionality; [apply HI|].
        intros [|n]; simpl; auto.
  - simpl. intros A0 Gamma0 sigma [H1 H2]; auto.
  - simpl. intros A0 B0 Gamma0 H1 H2 sigma [H3 H4]. auto.
  - simpl. intros A0 B0 Gamma0 H1 H2 sigma H3 H4.
    apply H2. unfold tr_env; simpl. auto.
  - simpl. intros A0 B0 Gamma0 H1 H2 H3 H4 sigma H5.
    apply H2; auto.
  - simpl. intros A0 B0 Gamma0 H1 H2 H3 H4 sigma H5. auto.
  - simpl. intros A0 B0 Gamma0 H1 H2 sigma H3. apply H2; auto.
  - simpl. intros A0 B0 Gamma0 H1 H2 sigma H3. apply H2; auto.
  - simpl. intros A0 B0 Gamma0 H1 H2 sigma H3. auto.
  - simpl. intros A0 B0 Gamma0 H1 H2 sigma H3. auto.
  - simpl. intros A0 B0 C0 Gamma0 H1 H2 H3 H4 H5 H6 sigma H7.
    destruct (H2 sigma H7); [apply H4 | apply H6]; unfold tr_env; simpl; auto.
  - simpl. intros A0 Gamma0 H1 H2 sigma H3. exfalso; eapply H2; eauto.
  - simpl. intros A0 Gamma0 H1 H2 sigma H3 x. apply H2.
    rewrite tr_env_subst.
    erewrite tr_env_extensionality; eauto.
  - simpl. intros A0 Gamma0 t H1 H2 sigma H3.
    rewrite tr_formula_subst1. apply H2; auto.
  - simpl. intros A0 Gamma0 t H1 H2 sigma H3.
    specialize (H2 sigma H3). rewrite tr_formula_subst1 in H2.
    eauto.
  - simpl. intros A0 B0 Gamma0 H1 H2 H3 H4 sigma H5.
    destruct (H2 sigma H5) as [x H6].
    specialize (H4 (x .: sigma)). rewrite tr_env_rw in H4.
    rewrite tr_formula_subst in H4.
    apply H4. rewrite tr_env_subst; auto.
  - simpl. intros Gamma0 t sigma H. reflexivity.
  - simpl. intros Gamma0 A0 t1 t2 H1 H2 H3 H4 sigma H5.
    specialize (H2 sigma H5).
    specialize (H4 sigma H5).
    rewrite tr_formula_subst1 in *. congruence.
Defined.

Corollary Heyting_consistent : Heyting nil Bottom -> False.
Proof.
  intros H. apply reflect with (sigma := fun _ => 0) in H; auto.
  unfold tr_env; simpl; auto.
Defined.

Definition dnegA A B := (B @-> A) @-> A.

Fixpoint friedman A B :=
  match B with
  | Bottom | DummyVar _ | _ @= _ => B @\/ A
  | B @/\ C => (dnegA A (friedman A B)) @/\ (dnegA A (friedman A C))
  | B @\/ C => (dnegA A (friedman A B)) @\/ (dnegA A (friedman A C))
  | B @-> C => (dnegA A (friedman A B)) @-> (dnegA A (friedman A C))
  | Forall B => (Forall (dnegA A.|[ren (+1)] (friedman (A.|[ren (+1)]) B)))
  | Exists B => (dnegA A (Exists (friedman (A.|[ren (+1)]) B)))
  end.

Inductive ClassicalPeano : formula -> Type :=
| PeanoAxiom : forall A, PeanoAxioms A -> ClassicalPeano A
| DoubleNegation : forall A, ClassicalPeano (@~ @~ A @-> A).

Notation Peano := (nd ClassicalPeano).

Lemma nd_cut : forall ax Gamma A B, nd ax Gamma A -> nd ax (A :: Gamma) B -> nd ax Gamma B.
Proof.
  intros ax Gamma A B H0 H1.
  apply Nd_impE with (A := A).
  - apply Nd_impI; auto.
  - auto.
Defined.

Lemma nd_weak_r : forall ax Gamma A, nd ax Gamma A -> forall Delta Pi B, Gamma = Delta ++ Pi -> nd ax (Delta ++ (B :: Pi)) A.
Proof.
  intros ax Gamma A dn; elim dn.
  - intros; apply Nd_axiom; auto.
  - intros A0 Gamma0 [|A1 Delta] Pi B H.
    + simpl in *. apply Nd_weak. rewrite <- H. apply Nd_assume.
    + simpl in *. replace A1 with A0 by congruence. apply Nd_assume.
  - intros A0 B Gamma0 H1 H2 [|B1 Delta] Pi B0 H3.
    + simpl in *. rewrite <- H3. apply Nd_weak. apply Nd_weak. auto.
    + simpl in *. apply Nd_weak. apply H2. congruence.
  - intros A0 B Gamma0 H1 H2 Delta Pi B0 H3. apply Nd_impI.
    apply H2 with (Delta := A0 :: Delta). simpl; congruence.
  - intros A0 B Gamma0 H1 H2 H3 H4 Delta Pi B0 H5. apply Nd_impE with (A := A0).
    + apply H2; auto.
    + apply H4; auto.
  - intros A0 B Gamma0 H1 H2 H3 H4 Delta Pi B0 H5. apply Nd_andI.
    + apply H2; auto.
    + apply H4; auto.
  - intros A0 B Gamma0 H1 H2 Delta Pi B0 H3. eapply Nd_andEL. apply H2; auto.
  - intros A0 B Gamma0 H1 H2 Delta Pi B0 H3. eapply Nd_andER. apply H2; auto.
  - intros A0 B Gamma0 H1 H2 Delta Pi B0 H3. eapply Nd_orIL. apply H2; auto.
  - intros A0 B Gamma0 H1 H2 Delta Pi B0 H3. eapply Nd_orIR. apply H2; auto.
  - intros A0 B0 C Gamma0 H1 H2 H3 H4 H5 H6 Delta Pi B1 H7. eapply Nd_orE.
    + apply H2; auto.
    + apply H4 with (Delta := A0 :: Delta). simpl; congruence.
    + apply H6 with (Delta := B0 :: Delta). simpl; congruence.
  - intros A0 Gamma0 H1 H2 Delta Pi B H3. apply Nd_botE. auto.
  - intros A0 Gamma0 H1 H2 Delta Pi B H3. apply Nd_forallI.
    rewrite H3 in *. rewrite subst_app in *. rewrite subst_cons.
    apply H2; auto.
  - intros A0 Gamma0 t H1 H2 Delta Pi B H3. apply Nd_forallE. apply H2; auto.
  - intros A0 Gamma0 t H1 H2 Delta Pi B H3. apply Nd_existI with (t := t).
    apply H2; auto.
  - intros A0 B Gamma0 H1 H2 H3 H4 Delta Pi B0 H5. eapply Nd_existE.
    + apply H2; auto.
    + rewrite H5 in *. rewrite subst_app in *. rewrite subst_cons.
      apply H4 with (Delta0 := (A0 :: Delta..|[ren (+1)])); auto.
  - intros Gamma0 t Delta Pi B H. apply Nd_eq_refl.
  - intros Gamma0 A0 t1 t2 H1 H2 H3 H4 Delta Pi B H5.
    eapply Nd_eq_elim; [apply H2 | apply H4]; auto.
Defined.

Lemma nd_weak : forall ax Gamma Delta A B, nd ax (Gamma ++ Delta) A -> nd ax (Gamma ++ (B :: Delta)) A.
Proof.
  intros ax Gamma Delta A B H. apply nd_weak_r with (Gamma := Gamma ++ Delta) (Delta := Gamma) (Pi := Delta); auto.
Defined.

Ltac nd_weak n :=
  match n with
  | 0 => apply Nd_weak
  | 1 => apply (nd_weak _ (_ :: nil)); simpl
  | 2 => apply (nd_weak _ (_ :: _ :: nil)); simpl
  | 3 => apply (nd_weak _ (_ :: _ :: _ :: nil)); simpl
  | 4 => apply (nd_weak _ (_ :: _ :: _ :: _ :: nil)); simpl
  | 5 => apply (nd_weak _ (_ :: _ :: _ :: _ :: _ :: nil)); simpl
  | 6 => apply (nd_weak _ (_ :: _ :: _ :: _ :: _ :: _ :: nil)); simpl
  end.

Ltac nd_apply n :=
  eapply Nd_impE; [nd_assumption n|].

Ltac nd_intro := apply Nd_impI.

Ltac nd_destruct_or n :=
  eapply Nd_orE; [nd_assumption n|nd_weak (S n)|nd_weak (S n)].
Ltac nd_left := apply Nd_orIL.
Ltac nd_right := apply Nd_orIR.

Ltac nd_assert H :=
  apply Nd_impE with (A := H); [nd_intro|].

Ltac nd_destruct_and n :=
  eapply Nd_impE;
  [
    nd_intro; eapply Nd_impE;
    [nd_intro; nd_weak (S (S n))
    |eapply Nd_andEL; nd_assumption (S n)
    ]
   |eapply Nd_andER; nd_assumption n
  ].
Ltac nd_split := apply Nd_andI.

Lemma double_neg_simpl :
  forall ax Gamma A B, nd ax Gamma A -> nd ax Gamma (dnegA B A).
Proof.
  intros ax Gamma A B H.
  nd_intro. nd_apply 0. nd_weak 0; auto.
Defined.

Lemma double_neg_imp :
  forall ax Gamma A B C, nd ax (B :: Gamma) C -> nd ax (dnegA A B :: Gamma) (dnegA A C).
Proof.
  intros ax Gamma A B C H.
  nd_intro. nd_apply 1. nd_intro. nd_apply 1.
  nd_weak 1; nd_weak 1; auto.
Defined.

Lemma or_imp :
  forall Gamma A B C, Heyting (B :: Gamma) C -> Heyting ((A @\/ B) :: Gamma) (A @\/ C).
Proof.
  intros Gamma A B C H.
  nd_destruct_or 0.
  - nd_left; nd_assumption.
  - nd_right; auto.
Defined.

Lemma or_double_neg :
  forall ax Gamma A B, nd ax Gamma (A @\/ B) -> nd ax Gamma (dnegA A B).
Proof.
  intros ax Gamma A B H.
  nd_intro.
  eapply Nd_orE; [nd_weak 0; eauto| |].
  - nd_assumption.
  - nd_apply 1; nd_assumption.
Defined.

Lemma or_double_neg_rev :
  forall ax Gamma A B, nd ax Gamma (B @\/ A) -> nd ax Gamma (dnegA A B).
Proof.
  intros ax Gamma A B H.
  nd_intro.
  eapply Nd_orE; [nd_weak 0; eauto| |].
  - nd_apply 1; nd_assumption.
  - nd_assumption.
Defined.

Lemma double_neg_4 : forall ax Gamma A B, nd ax Gamma (dnegA B (dnegA B A)) -> nd ax Gamma (dnegA B A).
Proof.
  intros ax Gamma A B H.
  nd_intro.
  eapply Nd_impE; [nd_weak 0; eauto|].
  nd_intro; nd_apply 0; nd_assumption.
Defined.

Lemma double_neg_weak :
  forall ax Gamma A B C, nd ax (B :: Gamma) (dnegA A C) -> nd ax (dnegA A B :: Gamma) (dnegA A C).
Proof.
  intros ax Gamma A B C H.
  apply double_neg_4. apply double_neg_imp; auto.
Defined.

Lemma double_neg_weakH :
  forall ax Gamma A B C, nd ax (B :: Gamma) (dnegA A C) -> nd ax Gamma (dnegA A B) -> nd ax Gamma (dnegA A C).
Proof.
  intros ax Gamma A B C H1 H2.
  eapply Nd_impE; [|apply H2].
  nd_intro; apply double_neg_weak; auto.
Defined.

Lemma friedman_subst :
  forall B A sigma, (friedman A B).|[sigma] = friedman A.|[sigma] B.|[sigma].
Proof.
  intros B. induction B; intros; simpl; auto.
  - rewrite IHB1; rewrite IHB2; auto.
  - rewrite IHB1; rewrite IHB2; auto.
  - rewrite IHB1; rewrite IHB2; auto.
  - rewrite IHB. asimpl. auto.
  - rewrite IHB. asimpl. auto.
Qed.

Lemma friedman_subst_map :
  forall Gamma A sigma, (map (friedman A) Gamma)..|[sigma] = map (friedman A.|[sigma]) Gamma..|[sigma].
Proof.
  intros. induction Gamma.
  - simpl; auto.
  - rewrite subst_cons. unfold map in *. rewrite subst_cons.
    rewrite IHGamma. rewrite friedman_subst. auto.
Qed.

Lemma double_neg_bottom :
  forall Gamma A, Heyting Gamma (dnegA A (Bottom @\/ A)) -> Heyting Gamma A.
Proof.
  intros Gamma A H.
  eapply Nd_impE; [apply H|].
  apply Nd_impI. eapply Nd_orE.
  - apply Nd_assume.
  - apply Nd_botE; apply Nd_assume.
  - apply Nd_assume.
Qed.

Lemma friedman_imp_t :
  forall ax A B Gamma, nd ax Gamma B -> nd ax Gamma (friedman B A).
Proof.
Admitted.

Lemma friedman_imp :
  forall ax A B C Gamma, nd ax Gamma (friedman C A) -> nd ax Gamma (A @-> friedman C B) ->
                nd ax Gamma (friedman C B).
Proof.
  intros ax A. induction A.
  - intros B C Gamma H1 H2; simpl in *.
    apply friedman_imp_t. give_up.
  - intros B C Gamma H1 H2; simpl in *.
    eapply Nd_orE.
    + apply H1.
    + eapply Nd_impE; [apply Nd_weak; apply H2|apply Nd_assume].
    + apply friedman_imp_t; apply Nd_assume.
  - intros B C Gamma H1 H2; simpl in *.
    eapply Nd_impE; [apply H2|].
Abort.

Lemma imp_friedman :
  forall ax A B Gamma, (nd ax Gamma A -> nd ax Gamma (friedman B A)) *
              (nd ax Gamma (dnegA B (friedman B A)) -> nd ax Gamma (dnegA B A)).
Proof.
  intros ax A. induction A.
  - intros B Gamma; simpl in *. split.
    + intros H. apply Nd_botE. auto.
    + intros H. give_up.
  - intros B Gamma. simpl in *. split.
    + intros H. apply Nd_orIL. auto.
    + intros H. apply or_double_neg_rev; auto. give_up.
  - intros B Gamma. simpl in *.
    split.
    + intros H.
      apply Nd_impI.
      apply Nd_impE with (A := dnegA B A1); [|apply IHA1; apply Nd_assume].
      apply Nd_weak; apply Nd_impI. apply double_neg_imp.
      apply IHA2. eapply Nd_impE; [apply Nd_weak; apply H|apply Nd_assume].
    + intros H.
      apply Nd_impE with (A := dnegA B (dnegA B (friedman B A1) @-> dnegA B (friedman B A2))); [|apply H].
      apply Nd_impI. apply double_neg_weak.
(*  - intros B Gamma H. simpl in *. apply Nd_impI. apply double_neg_imp.
    apply IHA2. eapply Nd_impE; [apply Nd_weak; apply H|]. *)
Abort.

Lemma friedman_Peano_Heyting :
  forall Gamma A, Peano Gamma A -> forall P, Heyting (map (friedman P) Gamma) (dnegA P (friedman P A)).
Proof.
  intros Gamma A dn; elim dn; clear Gamma A dn.
  - intros A Gamma H P. destruct H as [A HA | A].
    + give_up.
    + simpl. remember (friedman P A) as C.
      apply double_neg_simpl.
      apply Nd_impI. apply double_neg_weak.
      apply Nd_impI. apply double_neg_bottom.
      eapply Nd_impE; [apply Nd_weak; apply Nd_assume|].
      apply double_neg_simpl. apply Nd_impI.
      apply double_neg_weak. apply Nd_impI; apply Nd_weak.
      eapply Nd_impE; [apply Nd_weak|]; apply Nd_assume.
  - intros A Gamma P; simpl; apply double_neg_simpl; apply Nd_assume.
  - intros A B Gamma H1 H2 P; simpl; apply Nd_weak; apply H2.
  - intros A B Gamma H1 H2 P; simpl; apply double_neg_simpl.
    apply Nd_impI; simpl in H2. apply double_neg_weak; auto.
  - intros A B Gamma H1 H2 H3 H4 P. simpl in *.
    apply Nd_impI. eapply Nd_impE.
    + apply Nd_weak; apply H2.
    + apply Nd_impI. eapply Nd_impE; [|apply Nd_weak; apply Nd_assume].
      eapply Nd_impE. apply Nd_assume.
      apply Nd_weak; apply Nd_weak; apply H4.
  - intros A B Gamma H1 H2 H3 H4 P. simpl in *.
    apply double_neg_simpl. apply Nd_andI; auto.
  - intros A B Gamma H1 H2 P. simpl in *.
    eapply double_neg_weakH; [|apply H2].
    eauto using Nd_andEL, Nd_assume.
  - intros A B Gamma H1 H2 P. simpl in *.
    eapply double_neg_weakH; [|apply H2].
    eauto using Nd_andER, Nd_assume.
  - intros A B Gamma H1 H2 P. simpl in *.
    apply double_neg_simpl; eauto using Nd_orIL.
  - intros A B Gamma H1 H2 P. simpl in *.
    apply double_neg_simpl; eauto using Nd_orIR.
  - intros A B C Gamma H1 H2 H3 H4 H5 H6 P. simpl in *.
    eapply double_neg_weakH; [|apply H2].
    eapply Nd_orE.
    + apply Nd_assume.
    + apply nd_weak with (Gamma := (dnegA P (friedman P A)) :: nil); simpl.
      apply double_neg_weak; apply H4.
    + apply nd_weak with (Gamma := (dnegA P (friedman P B)) :: nil); simpl.
      apply double_neg_weak; apply H6.
  - intros A Gamma H1 H2 P; simpl in *. apply Nd_impI; apply Nd_weak.
    eapply Nd_impE; [apply H2|]. apply Nd_impI.
    eapply Nd_orE.
    + apply Nd_assume.
    + apply Nd_botE; apply Nd_assume.
    + apply Nd_assume.
  - intros A Gamma H1 H2 P; simpl in *. apply double_neg_simpl.
    specialize (H2 P.|[ren (+1)]).
    apply Nd_forallI. rewrite friedman_subst_map. auto.
  - intros A Gamma t H1 H2 P; simpl in *.
    specialize (H2 P).
    eapply double_neg_weakH; [|apply H2].
    replace (dnegA P (friedman P A.|[t/]))
      with (dnegA P.|[ren (+1)] (friedman P.|[ren (+1)] A)).|[t/]
      by (asimpl; rewrite friedman_subst; autosubst).
    apply Nd_forallE; apply Nd_assume.
  - intros A Gamma t H1 H2 P; simpl in *.
    apply double_neg_simpl.
    specialize (H2 P).
    apply Nd_impI. eapply Nd_impE; [apply Nd_weak; apply H2|].
    apply Nd_impI. eapply Nd_impE; [apply Nd_weak; apply Nd_assume|].
    eapply Nd_existI. asimpl; rewrite friedman_subst; asimpl; apply Nd_assume.
  - intros A B Gamma H1 H2 H3 H4 P; simpl in *.
    specialize (H4 P.|[ren (+1)]).
    specialize (H2 P).
    apply double_neg_4 in H2.
    eapply double_neg_weakH; [|apply H2].
    eapply Nd_existE; [apply Nd_assume|].
    rewrite subst_cons.
    apply nd_weak with (Gamma := friedman P.|[ren (+1)] A :: nil); simpl.
    rewrite friedman_subst_map; simpl. rewrite friedman_subst. auto.
    (* Defined. *)
Admitted.

Fixpoint QF P : Type :=
  match P with
  | Bottom | _ @= _ => True
  | (A @-> B) | A @\/ B | A @/\ B => QF A * QF B
  | Forall _ | Exists _ | DummyVar _ => False
  end.

Definition equiv (A B : Type) : Type := (A -> B) * (B -> A).

Lemma equiv_refl :
  forall A, equiv A A.
Proof.
  split; auto.
Defined.

Lemma nd_eq_sym : forall ax Gamma t1 t2, nd ax Gamma (t1 @= t2) -> nd ax Gamma (t2 @= t1).
Proof.
  intros ax Gamma t1 t2 H.
  apply Nd_eq_elim with (A := Var 0 @= t1.[ren (+1)]) in H; asimpl in *; auto.
  apply Nd_eq_refl.
Qed.

Lemma Peano_S_inj_i : forall Gamma t1 t2,
    Heyting ((Succ t1 @= Succ t2) :: Gamma) (t1 @= t2).
Proof.
  intros Gamma t1 t2.
  evar (Delta : env).
  set (H := Nd_axiom PeanoAxioms _ ?Delta Peano_S_inj).
  apply Nd_forallE with (t := t1) in H.
  apply Nd_forallE with (t := t2) in H.
  asimpl in H.
  eapply Nd_impE; [apply H|apply Nd_assume].
Defined.

Lemma eq_decidable_forall : forall Gamma,
    Heyting Gamma (Forall (Forall ((Var 1 @= Var 0) @\/ @~ (Var 1 @= Var 0)))).
Proof.
  intros Gamma.
  eapply Nd_impE.
  - eapply Nd_impE.
    + apply Nd_axiom. apply Peano_rec.
    + asimpl.
      eapply Nd_impE.
      * eapply Nd_impE.
        -- apply Nd_axiom. apply Peano_rec.
        -- asimpl. apply Nd_orIL; apply Nd_eq_refl.
      * asimpl. apply Nd_forallI; apply Nd_impI; apply Nd_weak; apply Nd_orIR.
        apply Nd_impI.
        evar (Delta : env).
        set (H := (Nd_axiom _ _ ?Delta Peano_0_ne_Sn)).
        apply Nd_forallE with (t := Var 0) in H.
        asimpl in H.
        eapply Nd_impE; [apply H|].
        apply nd_eq_sym; apply Nd_assume.
  - asimpl. apply Nd_forallI. apply Nd_impI.
    eapply Nd_impE.
    + eapply Nd_impE.
      * apply Nd_axiom. apply Peano_rec.
      * asimpl.
        apply Nd_orIR.
        evar (Delta : env).
        set (H := (Nd_axiom _ _ ?Delta Peano_0_ne_Sn)).
        apply Nd_forallE with (t := Var 0) in H.
        asimpl in H; apply H.
    + asimpl. apply Nd_forallI; asimpl.
      apply Nd_impI. apply Nd_weak.
      eapply Nd_impE; [|apply Nd_forallE with (t := Var 0); apply Nd_assume].
      asimpl. apply Nd_impI.
      eapply Nd_orE; [apply Nd_assume| |].
      * apply Nd_orIL.
        evar (Delta : env).
        set (H := (Nd_eq_elim PeanoAxioms ?Delta (Succ (Var 2) @= Succ (Var 0)) (Var 1) (Var 0))).
        asimpl in H. apply H; [apply Nd_assume|apply Nd_eq_refl].
      * apply Nd_orIR. apply Nd_impI.
        eapply Nd_impE; [apply Nd_weak; apply Nd_assume|].
        apply Peano_S_inj_i.
Defined.

Lemma eq_decidable : forall Gamma e1 e2,
    Heyting Gamma ((e1 @= e2) @\/ @~ (e1 @= e2)).
Proof.
  intros Gamma e1 e2.
  set (H := eq_decidable_forall Gamma).
  apply Nd_forallE with (t := e1) in H.
  apply Nd_forallE with (t := e2) in H.
  asimpl in H; auto.
Defined.

Lemma qf_decidable : forall Gamma A, QF A -> Heyting Gamma (A @\/ (@~ A)).
Proof.
  intros Gamma A. induction A; intros H; simpl in H; try (exfalso; assumption).
  - apply Nd_orIR. apply Nd_impI. apply Nd_assume.
  - destruct H as [H1 H2].
    eapply Nd_orE; [apply IHA2; auto| |].
    + apply Nd_orIL; apply Nd_impI; apply Nd_weak; apply Nd_assume.
    + eapply Nd_orE; [apply Nd_weak; apply IHA1; auto| |].
      * apply Nd_orIR; apply Nd_impI.
        eapply Nd_impE; [apply Nd_weak; apply Nd_weak; apply Nd_assume|].
        eapply Nd_impE; [|apply Nd_weak]; apply Nd_assume.
      * apply Nd_orIL; apply Nd_impI. apply Nd_botE.
        eapply Nd_impE; [apply Nd_weak|]; apply Nd_assume.
  - destruct H as [H1 H2].
    eapply Nd_orE; [apply IHA1; auto| |].
    + eapply Nd_orE; [apply Nd_weak; apply IHA2; auto| |].
      * apply Nd_orIL; apply Nd_andI; [apply Nd_weak|]; apply Nd_assume.
      * apply Nd_orIR; apply Nd_impI.
        eapply Nd_impE; [apply Nd_weak; apply Nd_assume|].
        eapply Nd_andER; apply Nd_assume.
    + apply Nd_orIR; apply Nd_impI.
      eapply Nd_impE; [apply Nd_weak; apply Nd_assume|].
      eapply Nd_andEL; apply Nd_assume.
  - destruct H as [H1 H2].
    eapply Nd_orE; [apply IHA1; auto| |].
    + apply Nd_orIL; apply Nd_orIL; apply Nd_assume.
    + eapply Nd_orE; [apply Nd_weak; apply IHA2; auto| |].
      * apply Nd_orIL; apply Nd_orIR; apply Nd_assume.
      * apply Nd_orIR; apply Nd_impI.
        eapply Nd_orE; [apply Nd_assume| |].
        -- eapply Nd_impE; [apply Nd_weak; apply Nd_weak; apply Nd_weak|]; apply Nd_assume.
        -- eapply Nd_impE; [apply Nd_weak; apply Nd_weak|]; apply Nd_assume.
  - apply eq_decidable.
Defined.

Lemma friedman_or_equiv :
  forall P Gamma A, QF P -> (Heyting Gamma ((friedman A P) @-> (P @\/ A)) *
                 Heyting Gamma ((P @\/ A) @-> (friedman A P))).
Proof.
  intros P. induction P.
  - intros Gamma A H. simpl in *.
    split; apply Nd_impI; apply Nd_assume.
  - intros Gamma A H. simpl in *.
    split; apply Nd_impI; apply Nd_assume.
  - intros Gamma A [HQF1 HQF2]. simpl in *.
    split.
    + apply Nd_impI.
      eapply Nd_impE; [|apply (qf_decidable _ P1 HQF1)].
      apply Nd_impI.
      eapply Nd_orE; [apply Nd_assume| |].
      * eapply Nd_impE; [|apply (qf_decidable _ P2 HQF2)].
        apply Nd_impI.
        eapply Nd_orE; [apply Nd_assume| |].
        -- apply Nd_orIL; apply Nd_impI; apply Nd_weak; apply Nd_assume.
        -- apply Nd_orIR.
           apply Nd_impE with (A := (friedman A P2) @-> A).
           ++ eapply Nd_impE; [apply Nd_weak; apply Nd_weak; apply Nd_weak; apply Nd_weak; apply Nd_assume|].
              apply double_neg_simpl.
              eapply Nd_impE; [apply IHP1; auto|].
              apply Nd_orIL; apply Nd_weak; apply Nd_weak; apply Nd_assume.
           ++ apply Nd_impI.
              eapply Nd_orE; [|apply Nd_botE; eapply Nd_impE; [apply Nd_weak; apply Nd_weak|]; apply Nd_assume |apply Nd_assume].
              eapply Nd_impE; [|apply Nd_assume].
              apply IHP2; auto.
      * apply Nd_orIL; apply Nd_impI. apply Nd_botE.
        eapply Nd_impE; [apply Nd_weak|]; apply Nd_assume.
    + apply Nd_impI; apply Nd_impI; apply Nd_impI.
      eapply Nd_orE; [apply Nd_weak; apply Nd_weak; apply Nd_assume| |apply Nd_assume].
      apply Nd_impE with (A := P1 @-> A).
      * apply Nd_impI. eapply Nd_impE; [apply Nd_weak; apply Nd_weak; apply Nd_weak; apply Nd_assume|].
        apply Nd_impI.
        eapply Nd_orE; [eapply Nd_impE; [apply IHP1; auto|apply Nd_assume]| |apply Nd_assume].
        eapply Nd_impE; [apply Nd_weak; apply Nd_weak|]; apply Nd_assume.
      * apply Nd_impI. eapply Nd_impE; [apply Nd_weak; apply Nd_weak; apply Nd_assume|].
        eapply Nd_impE; [apply IHP2; auto|].
        apply Nd_orIL; eapply Nd_impE; [apply Nd_weak|]; apply Nd_assume.
  - intros Gamma A [HQF1 HQF2]. simpl in *.
    split.
    + apply Nd_impI.
      eapply Nd_impE; [|apply (qf_decidable _ P1 HQF1)].
      apply Nd_impI.
      eapply Nd_orE; [apply Nd_assume| |].
      * eapply Nd_impE; [|apply (qf_decidable _ P2 HQF2)].
        apply Nd_impI.
        eapply Nd_orE; [apply Nd_assume| |].
        -- apply Nd_orIL. apply Nd_andI; [apply Nd_weak; apply Nd_weak|]; apply Nd_assume.
        -- apply Nd_orIR. 

Lemma tr_friedman_equiv :
  forall P A sigma, QF P ->
    equiv (tr_formula sigma (friedman A P)) (tr_formula sigma (P @\/ A)).
Proof.
  intros P. induction P.
  - intros A sigma HQF.
    simpl. apply equiv_refl.
  - intros A sigma HQF. simpl. apply equiv_refl.
  - intros A sigma [HQF1 HQF2]. simpl in *.
    split.
    + intros H. give_up.
    + specialize (IHP1 A sigma HQF1).
      specialize (IHP2 A sigma HQF2).
      intros H1 H2 H3. destruct H1 as [H1 | H1]; [|assumption].
      assert (H4 : tr_formula sigma P1 -> tr_formula sigma A).
      * intros H. apply H3. apply IHP2. left; apply H1; assumption.
      * apply H2. intros H. apply IHP1 in H. destruct H; auto.
