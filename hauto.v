Theorem hoare_if_wp : forall P1 P2 Q (b:bexp) c1 c2,
    {{ P1 }} c1 {{ Q }} ->
    {{ P2 }} c2 {{ Q }} ->
    {{ (b -> P1) /\ (~ b -> P2) }} if b then c1 else c2 end {{ Q }}.
Proof.
  intros P1 P2 Q b c1 c2 HTrue HFalse st st' HE [HP1 HP2].
  inversion HE; subst; eauto.
Qed.

Ltac hauto_vc :=
  eauto;
  unfold "->>", assn_sub, t_update, bassn;
  intros; simpl in *;
  repeat match goal with [H: _ /\ _ |- _] => destruct H end;
  repeat (
      try rewrite -> eqb_eq in *;
      try rewrite -> leb_le in *;
      try rewrite leb_iff in *;
      try rewrite leb_iff_conv in *;
      try match goal with [H: negb _ <> true |- _] => eapply not_true_is_false in H end;
      try match goal with [H: negb _ <> false |- _] => eapply not_false_is_true in H end;
      try match goal with [H: negb _ = true |- _] => eapply negb_true_iff in H end;
      try match goal with [H: negb _ = false |- _] => eapply negb_false_iff in H end;
      try match goal with [H: (_ =? _) = true |- _] => eapply beq_nat_true in H end;
      try match goal with [H: (_ =? _) = false |- _] => eapply beq_nat_false in H end
    );
  try contradiction; eauto; try nia.

Ltac hauto_split1 :=
  try match goal with
      | [|- {{_}} skip {{_}}] =>
        first [eapply hoare_skip;[] |eapply hoare_consequence_pre; [eapply hoare_skip|]]
      | [|- {{_}} _ := _ {{_}}] =>
        first [eapply hoare_asgn;[] |eapply hoare_consequence_pre; [eapply hoare_asgn|]]
      | [|- {{_}} _; _ {{_}}] =>
        eapply hoare_seq
      | [|- {{_}} if _ then _ else _ end {{_}}] =>
        first [eapply hoare_if_wp;[|] |eapply hoare_consequence_pre; [eapply hoare_if_wp|]]
      end.

Ltac hauto :=
  match goal with
  | [|- {{_}} _ {{_}}] => repeat hauto_split1
  | _ => idtac
  end;
  try (hauto_vc; fail).

Ltac hauto_while P :=
  first[
      eapply (hoare_while P) |
      eapply hoare_consequence_post; [eapply (hoare_while P)|] |
      eapply hoare_consequence_post; [eapply hoare_consequence_pre; [eapply (hoare_while P)|]|]
    ];
  hauto.
