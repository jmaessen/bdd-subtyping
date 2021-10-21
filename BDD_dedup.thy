theory BDD_dedup
  imports BDD_select
begin

fun elim_dup :: "BDD \<Rightarrow> BDD" where
  "elim_dup (Select v t e) = (select v (elim_dup t) (elim_dup e))" |
  "elim_dup b = b"

theorem elim_dup_dedups [simp]: "ordered n a \<Longrightarrow> norm n (elim_dup a)"
  apply (induction a rule: ordered.induct)
  apply auto
  done

theorem elim_dup_noop [simp]: "norm n a \<Longrightarrow> elim_dup a = a"
  apply (induction n a rule: norm.induct)
  by auto

theorem elim_dup_idem [simp]: "elim_dup (elim_dup a) = elim_dup a"
  apply (induction a)
  by (auto simp add: select_def)

lemma elim_dup_correctl: "contains a f \<Longrightarrow> contains (elim_dup a) f"
  apply (induction a f rule: contains.induct)
  by (auto simp add: select_def contains_sel_t contains_sel_e)

lemma elim_dup_correctr: "contains (elim_dup a) f \<Longrightarrow> contains a f"
  apply (induction a rule: elim_dup.induct)
  apply (auto simp add: select_def)
  apply (case_tac "elim_dup t = elim_dup e")
  apply (metis (full_types) contains_sel_e contains_sel_t)
  by (simp add: contains_p_correct)

theorem elim_dup_correct [simp]: "contains (elim_dup a) f = contains a f"
  by (metis elim_dup_correctl elim_dup_correctr)

end