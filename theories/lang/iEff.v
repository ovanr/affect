
From iris.proofmode  Require Import tactics.
From iris.base_logic Require Export lib.iprop.

From hazel.language Require Export eff_lang.
From hazel.program_logic Require Export protocols.

Lemma iEff_tele_eq' {Σ} (TT1 TT2 : tele) v m
  (v' : TT1 -t>         val) (P : TT1 -t>         iProp Σ)
  (w' : TT1 -t> TT2 -t> val) (Q : TT1 -t> TT2 -t> iProp Σ) Φ :
  iEff_car
    (>>.. x >> !           (tele_app v' x)
               {{          (tele_app P  x)   }};
     <<.. y << ? (tele_app (tele_app w' x) y)
               {{ tele_app (tele_app Q  x) y }} @m) v Φ ≡
  (∃.. x, ⌜ tele_app v' x = v ⌝ ∗ tele_app P x ∗
    □? m (∀.. y, tele_app (tele_app Q  x) y -∗
          Φ (tele_app (tele_app w' x) y)))%I.
Proof. 
  by rewrite (iEff_tele_eq (tele_app v') (tele_app P)
                  (λ x y, tele_app (tele_app w' x) y)
                  (λ x y, tele_app (tele_app Q  x) y)).
Qed.

Lemma iEff_le_upcl_intro {Σ} m (Ψ : iEff Σ) :
  ⊢ iEff_le Ψ (upcl m Ψ). 
Proof.
  iIntros (v Φ) "!# HΨ". iExists Φ. iFrame.
  destruct m; simpl; [iIntros "% $"|iIntros "!# % $"].
Qed.

Lemma iEff_le_upcl_ms_os {Σ} (Ψ : iEff Σ) :
  ⊢ iEff_le (upcl MS Ψ) (upcl OS Ψ).
Proof.
  iIntros (v Φ) "!# HMSΨ". rewrite /upcl /=.
  iDestruct "HMSΨ" as "(%Φ' & HΨΦ' & #HPost)".
  iExists Φ'. iFrame "#∗".
Qed.
