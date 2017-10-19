(* -------------------------------------------------------------------- *)
Require Import Arith List.
From Autosubst Require Import Autosubst.
(* These are already required by Autosubst. However, having them        *
 * available is useful to prove equality lemmas about the translation   *
 * to Coq formulas.                                                     *)
Require Import Coq.Logic.FunctionalExtensionality.

(* -------------------------------------------------------------------- *)
Inductive expr : Type :=
| Var (_ : var)
| Zero
| Succ (_ : expr)
| Plus (_ : expr) (_ : expr)
| Mult (_ : expr) (_ : expr).

Inductive formula : Type :=
| Bottom
(* Autosubst complains if this line is not present.
 * See https://github.com/uds-psl/autosubst/issues/4 *)
| DummyVar (_ : var)
| Implies (_ : formula) (_ : formula)
| And (_ : formula) (_ : formula)
| Or (_ : formula) (_ : formula)
| Eq (_ : expr) (_ : expr)
| Forall (_ : {bind expr in formula})
| Exists (_ : {bind expr in formula}).


Infix "@+" := Plus (at level 50, left associativity).
Infix "@*" := Mult (at level 40, left associativity).
Notation "x @-> y" := (Implies x y) (at level 99, right associativity, y at level 200).
Infix "@/\" := And (at level 80, right associativity).
Infix "@\/" := Or (at level 85, right associativity).
Infix "@=" := Eq (at level 70).
Notation Not := (fun P => P @-> Bottom).
Notation "@~ x" := (Not x) (at level 75, right associativity).

Instance Ids_expr : Ids expr. derive. Defined.
Instance Rename_expr : Rename expr. derive. Defined.
Instance Subst_expr : Subst expr. derive. Defined.
Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.
Instance HSubst_formula : HSubst expr formula. derive. Defined.
Instance Ids_formula : Ids formula. derive. Defined.
Instance Rename_formula : Rename formula. derive. Defined.
Instance Subst_formula : Subst formula. derive. Defined.
Instance HSubstLemmas_formula : HSubstLemmas expr formula. derive. Qed.
Instance SubstHSubstComp_expr_formula : SubstHSubstComp expr formula. derive. Defined.
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

Ltac nd_exfalso := apply Nd_botE.

Ltac nd_unapply n := eapply Nd_impE; [|nd_assumption n].
Ltac nd_revert n := nd_unapply n; nd_weak n.

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

Lemma double_neg_or :
  forall ax Gamma A B, nd ax Gamma (dnegA A B) -> nd ax Gamma (dnegA A (B @\/ A)).
Proof.
  intros ax Gamma A B H.
  nd_intro. eapply Nd_impE; [nd_weak 0; apply H|].
  nd_intro. nd_apply 1. nd_left; nd_assumption.
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
Defined.

Lemma friedman_subst_map :
  forall Gamma A sigma, (map (friedman A) Gamma)..|[sigma] = map (friedman A.|[sigma]) Gamma..|[sigma].
Proof.
  intros. induction Gamma.
  - simpl; auto.
  - rewrite subst_cons. unfold map in *. rewrite subst_cons.
    rewrite IHGamma. rewrite friedman_subst. auto.
Defined.

Lemma double_neg_bottom :
  forall Gamma A, Heyting Gamma (dnegA A (Bottom @\/ A)) -> Heyting Gamma A.
Proof.
  intros Gamma A H.
  eapply Nd_impE; [apply H|].
  nd_intro. nd_destruct_or 0.
  - nd_exfalso; nd_assumption.
  - nd_assumption.
Defined.

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
Defined.

Lemma Peano_0_ne_Sn_i : forall Gamma t,
    Heyting Gamma (@~ (Succ t @= Zero)).
Proof.
  intros Gamma t.
  evar (Delta : env).
  set (H := Nd_axiom PeanoAxioms _ ?Delta Peano_0_ne_Sn).
  apply Nd_forallE with (t := t) in H.
  asimpl in H.
  apply H.
Defined.

Lemma Peano_ne_0_Sn_i : forall Gamma t,
    Heyting Gamma (Exists ((@~ (t.[ren (+1)] @= Zero)) @-> (Succ (Var 0) @= t.[ren (+1)]))).
Proof.
  intros Gamma t.
  evar (Delta : env).
  set (H := Nd_axiom PeanoAxioms _ ?Delta Peano_ne_0_Sn).
  apply Nd_forallE with (t := t) in H.
  asimpl in H. apply H.
Defined.

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

Lemma Peano_plus_0_i : forall Gamma t,
    Heyting Gamma ((t @+ Zero) @= t).
Proof.
  intros Gamma t.
  evar (Delta : env).
  set (H := Nd_axiom PeanoAxioms _ ?Delta Peano_plus_0).
  apply Nd_forallE with (t := t) in H.
  asimpl in H.
  apply H.
Defined.

Lemma Peano_plus_S_i : forall Gamma t1 t2,
    Heyting Gamma ((Succ t1 @+ t2) @= Succ (t1 @+ t2)).
Proof.
  intros Gamma t1 t2.
  evar (Delta : env).
  set (H := Nd_axiom PeanoAxioms _ ?Delta Peano_plus_S).
  apply Nd_forallE with (t := t1) in H.
  apply Nd_forallE with (t := t2) in H.
  asimpl in H.
  apply H.
Defined.

Lemma Peano_mult_0_i : forall Gamma t,
    Heyting Gamma ((Zero @* t) @= Zero).
Proof.
  intros Gamma t.
  evar (Delta : env).
  set (H := Nd_axiom PeanoAxioms _ ?Delta Peano_mult_0).
  apply Nd_forallE with (t := t) in H.
  asimpl in H.
  apply H.
Defined.

Lemma Peano_mult_S_i : forall Gamma t1 t2,
    Heyting Gamma ((Succ t1 @* t2) @= t1 @* t2 @+ t2).
Proof.
  intros Gamma t1 t2.
  evar (Delta : env).
  set (H := Nd_axiom PeanoAxioms _ ?Delta Peano_mult_S).
  apply Nd_forallE with (t := t1) in H.
  apply Nd_forallE with (t := t2) in H.
  asimpl in H.
  apply H.
Defined.

Ltac HA_rec :=
  eapply Nd_impE; [
    eapply Nd_impE; [
      apply Nd_axiom; apply Peano_rec
     |asimpl]
   |asimpl; apply Nd_forallI; asimpl; nd_intro].

Lemma eq_decidable_forall : forall Gamma,
    Heyting Gamma (Forall (Forall ((Var 1 @= Var 0) @\/ @~ (Var 1 @= Var 0)))).
Proof.
  intros Gamma.
  HA_rec.
  - HA_rec.
    + nd_left; apply Nd_eq_refl.
    + nd_weak 0; nd_right.
      nd_intro.
      eapply Nd_impE; [|apply nd_eq_sym; nd_assumption].
      apply Peano_0_ne_Sn_i.
  - HA_rec.
    + nd_right.
      apply Peano_0_ne_Sn_i.
    + nd_weak 0.
      eapply Nd_impE; [|apply Nd_forallE with (t := Var 0); apply Nd_assume].
      asimpl. nd_intro.
      nd_destruct_or 0.
      * nd_left.
        evar (Delta : env).
        set (H := (Nd_eq_elim PeanoAxioms ?Delta (Succ (Var 2) @= Succ (Var 0)) (Var 1) (Var 0))).
        asimpl in H. apply H; [nd_assumption|apply Nd_eq_refl].
      * nd_right; nd_intro; nd_apply 1.
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
  - nd_right; nd_intro; nd_assumption.
  - destruct H as [H1 H2].
    eapply Nd_orE; [apply IHA2; auto| |].
    + apply Nd_orIL; nd_intro; nd_assumption.
    + eapply Nd_orE; [nd_weak 0; apply IHA1; auto| |].
      * nd_right; nd_intro.
        nd_apply 2. nd_apply 0. nd_assumption.
      * nd_left; nd_intro; nd_exfalso.
        nd_apply 1; nd_assumption.
  - destruct H as [H1 H2].
    eapply Nd_orE; [apply IHA1; auto| |].
    + eapply Nd_orE; [nd_weak 0; apply IHA2; auto| |].
      * nd_left; nd_split; nd_assumption.
      * nd_right; nd_intro.
        nd_destruct_and 0; nd_apply 2; nd_assumption.
    + nd_right; nd_intro.
      nd_apply 1; nd_destruct_and 0; nd_assumption.
  - destruct H as [H1 H2].
    eapply Nd_orE; [apply IHA1; auto| |].
    + nd_left; nd_left; nd_assumption.
    + eapply Nd_orE; [apply Nd_weak; apply IHA2; auto| |].
      * nd_left; nd_right; nd_assumption.
      * nd_right; nd_intro; nd_destruct_or 0; [nd_apply 2 | nd_apply 1]; nd_assumption.
  - apply eq_decidable.
Defined.

Lemma friedman_Peano_Heyting :
  forall Gamma A, Peano Gamma A -> forall P, Heyting (map (friedman P) Gamma) (dnegA P (friedman P A)).
Proof.
  intros Gamma A dn; elim dn; clear Gamma A dn.
  - intros A Gamma H P. destruct H as [A HA | A].
    + apply double_neg_simpl.
      destruct HA; simpl.
      * apply Nd_forallI. apply double_neg_simpl.
        nd_intro; apply double_neg_imp.
        nd_destruct_or 0; [|nd_right; nd_assumption].
        nd_left; nd_revert 0.
        apply Peano_0_ne_Sn_i.
      * apply Nd_forallI. apply double_neg_simpl; apply double_neg_simpl.
        eapply Nd_impE; [|apply Nd_forallE with (t := Var 0); apply Nd_axiom; apply Peano_ne_0_Sn].
        asimpl. nd_intro.
        eapply Nd_existE; [nd_assumption|].
        rewrite subst_cons; nd_weak 1. asimpl.
        apply Nd_existI with (t := Var 0). asimpl.
        nd_intro. apply double_neg_weak. apply double_neg_or.
        apply Nd_impE with (A := dnegA P.|[ren (+2)] (Var 1 @= Zero @-> Bottom)).
        -- nd_intro. apply double_neg_imp. nd_apply 2. nd_assumption.
        -- nd_weak 1. nd_intro. eapply Nd_impE; [nd_apply 1|].
           ++ nd_weak 1. nd_intro.
              eapply Nd_impE; [|apply eq_decidable].
              nd_intro; nd_destruct_or 0.
              ** nd_apply 1; nd_left; nd_assumption.
              ** nd_apply 2; nd_assumption.
           ++ nd_intro. nd_destruct_or 0; [nd_exfalso|]; nd_assumption.
      * apply Nd_forallI. apply double_neg_simpl.
        apply Nd_forallI. apply double_neg_simpl.
        nd_intro. apply double_neg_imp.
        nd_destruct_or 0; [|nd_right; nd_assumption].
        nd_left. apply Peano_S_inj_i.
      * apply Nd_forallI. apply double_neg_simpl.
        nd_left. apply Peano_plus_0_i.
      * apply Nd_forallI. apply double_neg_simpl.
        apply Nd_forallI. apply double_neg_simpl.
        nd_left. apply Peano_plus_S_i.
      * apply Nd_forallI. apply double_neg_simpl.
        nd_left. apply Peano_mult_0_i.
      * apply Nd_forallI. apply double_neg_simpl.
        apply Nd_forallI. apply double_neg_simpl.
        nd_left. apply Peano_mult_S_i.
      * eapply Nd_impE; [|apply Nd_axiom; apply Peano_rec with
          (P := dnegA P.|[ren (+1)] (friedman P.|[ren (+1)] P0))].
        nd_intro. nd_intro. apply double_neg_simpl.
        nd_intro. apply double_neg_imp.
        eapply Nd_impE; [nd_apply 2|]; asimpl.
        -- rewrite friedman_subst. asimpl. nd_assumption.
        -- nd_weak 1. nd_weak 1. apply Nd_forallI.
           eapply Nd_impE; [|apply Nd_forallE with (t := Var 0); nd_assumption].
           rewrite subst_cons. nd_weak 0. asimpl.
           nd_intro. nd_intro. rewrite friedman_subst.
           eapply Nd_impE; [|nd_assumption 1]; nd_intro.
           apply double_neg_weak.
           asimpl. nd_apply 0. nd_assumption.
    + simpl. remember (friedman P A) as C.
      apply double_neg_simpl.
      nd_intro. apply double_neg_weak.
      nd_intro. apply double_neg_bottom.
      nd_apply 1. apply double_neg_simpl.
      nd_intro. apply double_neg_weak.
      nd_intro; nd_apply 2; nd_assumption.
  - intros A Gamma P; simpl; apply double_neg_simpl; nd_assumption.
  - intros A B Gamma H1 H2 P; simpl; nd_weak 0; apply H2.
  - intros A B Gamma H1 H2 P; simpl in *; apply double_neg_simpl.
    nd_intro. apply double_neg_weak; auto.
  - intros A B Gamma H1 H2 H3 H4 P. simpl in *.
    nd_intro. eapply Nd_impE; [nd_weak 0; apply H2|].
    nd_intro. nd_revert 1. nd_apply 0. nd_weak 0; apply H4.
  - intros A B Gamma H1 H2 H3 H4 P. simpl in *.
    apply double_neg_simpl. nd_split; auto.
  - intros A B Gamma H1 H2 P. simpl in *.
    eapply double_neg_weakH; [|apply H2].
    nd_destruct_and 0; nd_assumption.
  - intros A B Gamma H1 H2 P. simpl in *.
    eapply double_neg_weakH; [|apply H2].
    nd_destruct_and 0; nd_assumption.
  - intros A B Gamma H1 H2 P. simpl in *.
    apply double_neg_simpl; nd_left; auto.
  - intros A B Gamma H1 H2 P. simpl in *.
    apply double_neg_simpl; nd_right; auto.
  - intros A B C Gamma H1 H2 H3 H4 H5 H6 P. simpl in *.
    eapply double_neg_weakH; [|apply H2].
    nd_destruct_or 0; apply double_neg_weak; [apply H4 | apply H6].
  - intros A Gamma H1 H2 P; simpl in *.
    nd_intro. nd_weak 0.
    eapply Nd_impE; [apply H2|].
    nd_intro. nd_destruct_or 0; [nd_exfalso|]; nd_assumption.
  - intros A Gamma H1 H2 P; simpl in *.
    apply double_neg_simpl.
    specialize (H2 P.|[ren (+1)]).
    apply Nd_forallI. rewrite friedman_subst_map. auto.
  - intros A Gamma t H1 H2 P; simpl in *.
    specialize (H2 P).
    eapply double_neg_weakH; [|apply H2].
    replace (dnegA P (friedman P A.|[t/]))
      with (dnegA P.|[ren (+1)] (friedman P.|[ren (+1)] A)).|[t/]
      by (asimpl; rewrite friedman_subst; autosubst).
    apply Nd_forallE; nd_assumption.
  - intros A Gamma t H1 H2 P; simpl in *.
    apply double_neg_simpl.
    specialize (H2 P).
    nd_intro. eapply Nd_impE; [nd_weak 0; apply H2|].
    nd_intro. nd_apply 1.
    eapply Nd_existI. asimpl; rewrite friedman_subst; asimpl; nd_assumption.
  - intros A B Gamma H1 H2 H3 H4 P; simpl in *.
    specialize (H4 P.|[ren (+1)]); specialize (H2 P).
    apply double_neg_4 in H2.
    eapply double_neg_weakH; [|apply H2].
    eapply Nd_existE; [nd_assumption|].
    rewrite subst_cons.
    nd_weak 1.
    rewrite friedman_subst_map; simpl. rewrite friedman_subst. auto.
  - intros Gamma t P; simpl in *.
    apply double_neg_simpl. nd_left. apply Nd_eq_refl.
  - intros Gamma A t1 t2 H1 H2 H3 H4 P.
    nd_assert (dnegA P ((t1 @= t2) @\/ P)); [|apply H2].
    apply double_neg_weak. nd_destruct_or 0.
    + replace (dnegA P (friedman P A.|[t2/]))
        with (dnegA P.|[ren (+1)] (friedman P.|[ren (+1)] A)).|[t2/]
        by (asimpl; rewrite friedman_subst; autosubst).
      eapply Nd_eq_elim; [nd_assumption|].
      asimpl; rewrite friedman_subst; asimpl. nd_weak 0; apply H4.
    + nd_intro; nd_assumption.
Defined.

Lemma friedman_or_equiv :
  forall P Gamma A, QF P -> (Heyting Gamma ((friedman A P) @-> (P @\/ A)) *
                 Heyting Gamma ((P @\/ A) @-> (friedman A P))).
Proof.
  intros P. induction P.
  - intros Gamma A H. simpl in *.
    split; nd_intro; nd_assumption.
  - intros Gamma A H. simpl in *.
    split; nd_intro; nd_assumption.
  - intros Gamma A [HQF1 HQF2]. simpl in *.
    split.
    + nd_intro.
      eapply Nd_impE; [|apply (qf_decidable _ P1 HQF1)]; nd_intro.
      nd_destruct_or 0.
      * eapply Nd_impE; [|apply (qf_decidable _ P2 HQF2)]; nd_intro.
        nd_destruct_or 0.
        -- nd_left; nd_intro; nd_assumption.
        -- nd_right.
           apply Nd_impE with (A := friedman A P2 @-> A).
           ++ nd_apply 2. apply double_neg_simpl.
              eapply Nd_impE; [apply IHP1; auto|].
              nd_left. nd_assumption.
           ++ nd_intro.
              eapply Nd_orE; [|nd_exfalso; nd_apply 2; nd_assumption|nd_assumption].
              nd_revert 0; apply IHP2; auto.
      * nd_left; nd_intro; nd_exfalso.
        nd_apply 1; nd_assumption.
    + nd_intro; nd_intro; nd_intro.
      nd_destruct_or 2; [|nd_assumption].
      nd_assert (P1 @-> A).
      * nd_apply 3. nd_intro.
        eapply Nd_orE; [eapply Nd_impE; [apply IHP1; auto|nd_assumption]| |nd_assumption].
        nd_apply 2; nd_assumption.
      * nd_intro. nd_apply 2.
        eapply Nd_impE; [apply IHP2; auto|].
        nd_left; nd_apply 1; nd_assumption.
  - intros Gamma A [HQF1 HQF2]. simpl in *.
    split.
    + nd_intro.
      eapply Nd_impE; [|apply (qf_decidable _ P1 HQF1)]; nd_intro.
      nd_destruct_or 0.
      * eapply Nd_impE; [|apply (qf_decidable _ P2 HQF2)]; nd_intro.
        nd_destruct_or 0.
        -- nd_left. nd_split; nd_assumption.
        -- nd_right. nd_destruct_and 2.
           nd_apply 1; nd_intro.
           nd_assert (P2 @\/ A); [|nd_revert 0; apply IHP2; auto].
           nd_destruct_or 0; [nd_exfalso; nd_apply 4|]; nd_assumption.
      * nd_right. nd_destruct_and 1.
        nd_apply 0; nd_intro.
        nd_assert (P1 @\/ A); [|nd_revert 0; apply IHP1; auto].
        nd_destruct_or 0; [nd_exfalso; nd_apply 4|]; nd_assumption.
    + nd_intro.
      nd_destruct_or 0.
      * nd_destruct_and 0. nd_split; apply double_neg_simpl.
        -- eapply Nd_impE; [apply IHP1; auto|]. nd_left; nd_assumption.
        -- eapply Nd_impE; [apply IHP2; auto|]. nd_left; nd_assumption.
      * nd_split; nd_intro; nd_assumption.
  - intros Gamma A [HQF1 HQF2]. simpl in *.
    split.
    + nd_intro.
      eapply Nd_impE; [|apply (qf_decidable _ P1 HQF1)]; nd_intro.
      nd_destruct_or 0.
      * nd_left; nd_left; nd_assumption.
      * eapply Nd_impE; [|apply (qf_decidable _ P2 HQF2)]; nd_intro.
        nd_destruct_or 0.
        -- nd_left; nd_right; nd_assumption.
        -- nd_right. nd_destruct_or 2; nd_apply 0; nd_intro.
           ++ nd_assert (P1 @\/ A); [|nd_revert 0; apply IHP1; auto].
              nd_destruct_or 0; [nd_exfalso; nd_apply 4|]; nd_assumption.
           ++ nd_assert (P2 @\/ A); [|nd_revert 0; apply IHP2; auto].
              nd_destruct_or 0; [nd_exfalso; nd_apply 3|]; nd_assumption.
    + nd_intro. nd_destruct_or 0.
      * nd_destruct_or 0; [nd_left | nd_right]; apply double_neg_simpl.
        -- eapply Nd_impE; [apply IHP1; auto|]. nd_left; nd_assumption.
        -- eapply Nd_impE; [apply IHP2; auto|]. nd_left; nd_assumption.
      * nd_left; nd_intro; nd_assumption.
  - intros Gamma A H. simpl in *.
    split; nd_intro; nd_assumption.
  - intros; simpl in *; exfalso; auto.
  - intros; simpl in *; exfalso; auto.
Defined.

Lemma friedman_or_equiv_l :
  forall P Gamma A, QF P -> Heyting Gamma ((friedman A P) @-> (P @\/ A)).
Proof.
  intros. apply friedman_or_equiv; auto.
Defined.

Lemma friedman_or_equiv_r :
  forall P Gamma A, QF P -> Heyting Gamma ((P @\/ A) @-> (friedman A P)).
Proof.
  intros. apply friedman_or_equiv; auto.
Defined.


Lemma tr_friedman_equiv :
  forall P A sigma, QF P ->
    equiv (tr_formula sigma (friedman A P)) (tr_formula sigma (P @\/ A)).
Proof.
  intros P A sigma H.
  destruct (friedman_or_equiv P nil A) as [E1 E2]; auto.
  split.
  - apply reflect with (sigma := sigma) in E1; simpl in *; auto.
    unfold tr_env; simpl; auto.
  - apply reflect with (sigma := sigma) in E2; simpl in *; auto.
    unfold tr_env; simpl; auto.
Defined.

Inductive Sigma_0 : nat -> formula -> Type :=
| QF_Sigma : forall n A, QF A -> Sigma_0 n A
| Exists_Sigma : forall n A, Sigma_0 (S n) A -> Sigma_0 (S n) (Exists A)
| Pi_Sigma : forall n A, Pi_0 n A -> Sigma_0 (S n) A

with Pi_0 : nat -> formula -> Type :=
| QF_Pi : forall n A, QF A -> Pi_0 n A
| Sigma_Pi : forall n A, Sigma_0 n A -> Pi_0 (S n) A
| Forall_Pi : forall n A, Pi_0 (S n) A -> Pi_0 (S n) (Forall A).

Fixpoint leading_exists A :=
  match A with
  | Exists A => S (leading_exists A)
  | _ => 0
  end.

Fixpoint after_exists A :=
  match A with
  | Exists A => after_exists A
  | _ => A
  end.

Fixpoint add_n_exists n A :=
  match n with
  | 0 => A
  | S n => Exists (add_n_exists n A)
  end.

Theorem add_n_exists_inverse :
  forall A, add_n_exists (leading_exists A) (after_exists A) = A.
Proof.
  intros A. induction A; simpl; congruence.
Defined.

Lemma double_neg_exists :
  forall Gamma P A, Heyting (A :: Gamma..|[ren (+1)]) P.|[ren (+1)] -> Heyting ((dnegA P (Exists A)) :: Gamma) P.
Proof.
  intros Gamma P A H.
  nd_apply 0. nd_intro. eapply Nd_existE; [nd_assumption|].
  rewrite subst_cons; rewrite subst_cons. nd_weak 1; nd_weak 1. apply H.
Defined.

Lemma exists_imply :
  forall n Gamma A, Heyting Gamma (A @-> (add_n_exists n A).|[ren (+n)]).
Proof.
  intros n. induction n as [|n IHn].
  - intros Gamma A. asimpl. nd_intro; nd_assumption.
  - intros Gamma A. simpl; nd_intro.
    apply Nd_existI with (t := Var n). asimpl.
    nd_revert 0. apply IHn.
Defined.

Lemma friedman_n_exists :
  forall n Gamma P A, Heyting ((friedman P.|[ren (+n)] A) :: Gamma..|[ren (+n)]) P.|[ren (+n)] -> Heyting (friedman P (add_n_exists n A) :: Gamma) P.
Proof.
  intros n. induction n as [|n IHn].
  - intros Gamma P A H. asimpl in *. apply H.
  - intros Gamma P A H. asimpl in *.
    apply double_neg_exists. apply IHn. asimpl. apply H.
Defined.

Lemma n_exists_friedman_imply :
  forall n Gamma A, QF A -> Heyting Gamma (dnegA (add_n_exists n A) (friedman (add_n_exists n A) (add_n_exists n A))) -> Heyting Gamma (add_n_exists n A).
Proof.
  intros n Gamma A H1 H2.
  eapply Nd_impE; [apply H2|].
  nd_intro. apply friedman_n_exists.
  eapply Nd_impE; [|apply friedman_or_equiv_l; apply H1].
  nd_intro. eapply Nd_impE; [|nd_apply 0; nd_assumption].
  nd_intro. nd_destruct_or 0; [|nd_assumption].
  nd_revert 0; nd_clear 2. apply exists_imply.
Defined.

Lemma after_exists_QF :
  forall A, QF A -> QF (after_exists A).
Proof.
  intros A H; destruct A; simpl in *; auto.
  exfalso; auto.
Defined.

Lemma Sigma_0_1_after_exists_QF :
  forall A, Sigma_0 1 A -> QF (after_exists A).
Proof.
  intros A H. remember 1 as n. induction H.
  - apply after_exists_QF; auto.
  - simpl; auto.
  - injection Heqn; intro; subst. inversion p. apply after_exists_QF; auto.
Defined.

Lemma Sigma_0_1_equiv :
  forall Gamma A, Sigma_0 1 A -> Heyting Gamma (dnegA A (friedman A A)) -> Heyting Gamma A.
Proof.
  intros Gamma A H1 H2.
  rewrite <- add_n_exists_inverse.
  apply n_exists_friedman_imply.
  - apply Sigma_0_1_after_exists_QF; auto.
  - rewrite add_n_exists_inverse; apply H2.
Defined.

Lemma Peano_Sigma_0_1_conservative :
  forall A, Sigma_0 1 A -> Peano nil A -> Heyting nil A.
Proof.
  intros A H1 H2.
  apply Sigma_0_1_equiv; auto.
  apply friedman_Peano_Heyting with (Gamma := nil); auto.
Defined.

Fixpoint leading_foralls A :=
  match A with
  | Forall A => S (leading_foralls A)
  | _ => 0
  end.

Fixpoint after_foralls A :=
  match A with
  | Forall A => after_foralls A
  | _ => A
  end.

Fixpoint add_n_foralls n A :=
  match n with
  | 0 => A
  | S n => Forall (add_n_foralls n A)
  end.

Theorem add_n_foralls_inverse :
  forall A, add_n_foralls (leading_foralls A) (after_foralls A) = A.
Proof.
  intros A. induction A; simpl; congruence.
Defined.

Lemma after_foralls_QF :
  forall A, QF A -> QF (after_foralls A).
Proof.
  intros A H; destruct A; simpl in *; auto.
  exfalso; auto.
Defined.

Lemma Sigma_0_n_Pi_0_n_after_foralls :
  forall n A, (Pi_0 n A -> Pi_0 n (after_foralls A)) * (Sigma_0 n A -> Sigma_0 n (after_foralls A)).
Proof.
  intros n. induction n as [|n IHn].
  - intros A. split; intros H; inversion H; constructor; apply after_foralls_QF; auto.
  - intros A. remember (S n) as m. split.
    + intros H. induction H.
      * apply QF_Pi; apply after_foralls_QF; auto.
      * injection Heqm; intros; subst. apply Sigma_Pi; apply IHn; auto.
      * simpl; auto.
    + intros H. induction H.
      * apply QF_Sigma; apply after_foralls_QF; auto.
      * simpl; apply Exists_Sigma; auto.
      * injection Heqm; intros; subst. apply Pi_Sigma; apply IHn; auto.
Defined.

Lemma Pi_0_Sn_after_foralls_Sigma_0_n :
  forall n A, Pi_0 (S n) A -> Sigma_0 n (after_foralls A).
Proof.
  intros n A H. remember (S n) as m. induction H.
  - apply QF_Sigma; apply after_foralls_QF; auto.
  - apply Sigma_0_n_Pi_0_n_after_foralls; congruence.
  - simpl; auto.
Defined.

Lemma add_foralls :
  forall ax n A Gamma, nd ax Gamma..|[ren (+n)] A -> nd ax Gamma (add_n_foralls n A).
Proof.
  intros ax n. induction n as [|n IHn].
  - intros. simpl. asimpl in *. auto.
  - intros A Gamma H. simpl in *. apply Nd_forallI. apply IHn.
    asimpl; auto.
Defined.

Lemma fold_env :
  forall ax Gamma A, nd ax Gamma A -> nd ax nil (fold_left (fun B C => C @-> B) Gamma A).
Proof.
  intros ax Gamma. induction Gamma as [|B Gamma IH].
  - simpl. auto.
  - intros A H. simpl. apply IH.
    nd_intro; auto.
Defined.

Lemma unfold_env :
  forall ax Gamma A, nd ax nil (fold_left (fun B C => C @-> B) Gamma A) -> nd ax Gamma A.
Proof.
  intros ax Gamma. induction Gamma as [|B Gamma IH].
  - simpl. auto.
  - intros A H. simpl. nd_revert 0. apply IH. simpl in H. auto.
Defined.

Definition closed_formula A := forall sigma, A.|[sigma] = A.

Lemma add_n_foralls_r :
  forall A n, add_n_foralls n (Forall A) = add_n_foralls (S n) A.
Proof.
  intros A n; induction n; simpl in *; congruence.
Defined.

Lemma add_n_foralls_closed :
  forall n A, closed_formula A -> closed_formula (add_n_foralls n A).
Proof.
  intros n. induction n as [|n IHn].
  - intros A H; simpl in *; auto.
  - intros A H sigma. simpl in *.
    rewrite IHn; auto.
Defined.

Lemma add_n_foralls_compose :
  forall n m A, add_n_foralls n (add_n_foralls m A) = add_n_foralls (n + m) A.
Proof.
  intros n m A. induction n; simpl in *; congruence.
Defined.

Lemma add_more_foralls_closed :
  forall n m A, m >= n -> closed_formula (add_n_foralls n A) -> closed_formula (add_n_foralls m A).
Proof.
  intros n m A H1 H2.
  replace m with ((m - n) + n) by (auto using Nat.sub_add).
  rewrite <- add_n_foralls_compose. apply add_n_foralls_closed; auto.
Defined.

Lemma iterate_sum :
  forall (X : Type) (f : X -> X) x n1 n2, iterate f n1 (iterate f n2 x) = iterate f (n1 + n2) x.
Proof.
  intros; induction n1 as [|n1 IH].
  - asimpl; auto.
  - simpl. unfold iterate in *. congruence.
Defined.
Hint Rewrite iterate_sum : autosubst.

Lemma upn_max :
  forall (P1 P2 : ((var -> expr) -> Prop)),
    {n | forall sigma, P1 (upn n sigma)} -> {n | forall sigma, P2 (upn n sigma)} ->
           {n | forall sigma, P1 (upn n sigma) /\ P2 (upn n sigma)}.
Proof.
  intros P1 P2 [n1 H1] [n2 H2].
  set (m := max n1 n2). exists m. intros sigma. asimpl.
  specialize (H1 (upn (m - n1) sigma)). specialize (H2 (upn (m - n2) sigma)).
  asimpl in *.
  rewrite Nat.add_comm in H1; rewrite Nat.sub_add in H1 by apply Nat.le_max_l.
  rewrite Nat.add_comm in H2; rewrite Nat.sub_add in H2 by apply Nat.le_max_r.
  auto.
Defined.

Lemma upn_succ :
  forall n sigma, upn (S n) sigma n = Var n.
Proof.
  intros n. induction n as [|n IH].
  - intros sigma. asimpl. auto.
  - intros sigma. asimpl. rewrite IH. auto.
Defined.
Hint Rewrite upn_succ : autosubst.

Lemma can_close_expr :
  forall (t : expr), {n | forall sigma, t.[upn n sigma] = t}.
Proof.
  intros t. induction t.
  - exists (S v). intros sigma. asimpl. rewrite upn_succ; auto.
  - exists 0. intros sigma. simpl. auto.
  - destruct IHt as [n H]. exists n. intros sigma. specialize (H sigma). simpl. congruence.
  - destruct (upn_max (fun sigma => t1.[sigma] = t1) (fun sigma => t2.[sigma] = t2) IHt1 IHt2)
      as [m H].
    exists m. intros sigma. specialize (H sigma). asimpl. destruct H; f_equal; auto.
  - destruct (upn_max (fun sigma => t1.[sigma] = t1) (fun sigma => t2.[sigma] = t2) IHt1 IHt2)
      as [m H].
    exists m. intros sigma. specialize (H sigma). asimpl. destruct H; f_equal; auto.
Defined.

Lemma can_close_formula :
  forall A, {n | forall sigma, A.|[upn n sigma] = A}.
Proof.
  intros A. induction A; try (exists 0; intro sigma; simpl in *; autosubst).
  - destruct (upn_max (fun sigma => A1.|[sigma] = A1) (fun sigma => A2.|[sigma] = A2) IHA1 IHA2)
      as [m H].
    exists m. asimpl. intros sigma; specialize (H sigma). destruct H.
    f_equal; auto.
  - destruct (upn_max (fun sigma => A1.|[sigma] = A1) (fun sigma => A2.|[sigma] = A2) IHA1 IHA2)
      as [m H].
    exists m. asimpl. intros sigma; specialize (H sigma). destruct H.
    f_equal; auto.
  - destruct (upn_max (fun sigma => A1.|[sigma] = A1) (fun sigma => A2.|[sigma] = A2) IHA1 IHA2)
      as [m H].
    exists m. asimpl. intros sigma; specialize (H sigma). destruct H.
    f_equal; auto.
  - asimpl.
    destruct (upn_max (fun sigma => e.[sigma] = e) (fun sigma => e0.[sigma] = e0) (can_close_expr e) (can_close_expr e0))
      as [m H].
    exists m. intros sigma; specialize (H sigma). destruct H.
    f_equal; auto.
  - destruct IHA as [n IHA].
    exists n. intros sigma. asimpl. specialize (IHA (up sigma)).
    asimpl in *. congruence.
  - destruct IHA as [n IHA].
    exists n. intros sigma. asimpl. specialize (IHA (up sigma)).
    asimpl in *. congruence.
Defined.

Lemma n_foralls_closed :
  forall n A, (forall sigma, A.|[upn n sigma] = A) -> closed_formula (add_n_foralls n A).
Proof.
  intros n. induction n as [|n IHn].
  - intros. simpl. auto.
  - intros. rewrite <- add_n_foralls_r.
    apply IHn. intros sigma. asimpl. rewrite H; auto.
Defined.

Lemma elim_foralls_closed :
  forall ax n A, closed_formula (add_n_foralls n A) -> nd ax nil (add_n_foralls n A) -> forall sigma, nd ax nil A.|[sigma].
Proof.
  intros ax n. induction n as [|n IHn].
  - intros A H1 H2 sigma. simpl in *. rewrite H1. auto.
  - intros A H1 H2 sigma. simpl in *.
    replace A.|[sigma] with A.|[Var 0 .: ((ren (+1)) >> sigma >> ren (+1))].|[sigma 0/] by autosubst.
    apply Nd_forallE.
    replace (Forall A.|[Var 0 .: ren (+1) >> sigma >> ren (+1)])
      with (Forall A).|[ren (+1) >> sigma] by autosubst.
    apply IHn; rewrite add_n_foralls_r; auto.
Defined.

Lemma fold_env_subst :
  forall Gamma A sigma,
    (fold_left (fun B C : formula => C @-> B) Gamma A).|[sigma] =
    fold_left (fun B C : formula => C @-> B) Gamma..|[sigma] A.|[sigma].
Proof.
  intros Gamma. induction Gamma as [|B Gamma IH].
  - intros. simpl. auto.
  - intros. rewrite subst_cons. simpl. rewrite IH. auto.
Defined.

Lemma prove_subst :
  forall ax Gamma A sigma, nd ax Gamma A -> nd ax Gamma..|[sigma] A.|[sigma].
Proof.
  intros ax Gamma A sigma H.
  apply unfold_env.
  replace (fold_left (fun B C : formula => C @-> B) Gamma..|[sigma] A.|[sigma])
    with (fold_left (fun B C : formula => C @-> B) Gamma A).|[sigma] by apply fold_env_subst.
  set (B := fold_left (fun B C : formula => C @-> B) Gamma A).
  destruct (can_close_formula B) as [n H1].
  eapply elim_foralls_closed.
  - apply n_foralls_closed. apply H1.
  - apply add_foralls. simpl. apply fold_env; auto.
Defined.

Lemma elim_foralls :
  forall ax n Gamma A, nd ax Gamma (add_n_foralls n A) -> forall sigma, nd ax Gamma..|[ren (+n) >> sigma] A.|[sigma].
Proof.
  intros ax n. induction n as [|n IHn].
  - intros Gamma A H sigma. simpl in *. asimpl. apply prove_subst. auto.
  - intros Gamma A H sigma. rewrite <- add_n_foralls_r in H.
    specialize (IHn Gamma (Forall A) H (ren (+1) >> sigma)).
    apply Nd_forallE with (t := sigma 0) in IHn.
    asimpl in *. auto.
Defined.

Lemma Peano_Pi_0_2_conservative :
  forall A, Pi_0 2 A -> Peano nil A -> Heyting nil A.
Proof.
  intros A H1 H2.
  rewrite <- add_n_foralls_inverse in H2.
  apply elim_foralls with (sigma := ids) in H2. asimpl in H2.
  apply Peano_Sigma_0_1_conservative in H2; [|apply Pi_0_Sn_after_foralls_Sigma_0_n; auto].
  rewrite <- add_n_foralls_inverse.
  apply add_foralls. asimpl. auto.
Defined.
