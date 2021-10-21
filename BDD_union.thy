theory BDD_union
  imports Main BDD_basic BDD_dedup BDD_select
begin

fun union :: "BDD \<Rightarrow> BDD \<Rightarrow> BDD" where
  "union Nothing b = b" |
  "union Top _ = Top" |
  "union a Nothing = a" |
  "union a Top = Top" |
  "union (Select a at ae) (Select b bt be) =
    (if a > b then select a (union at (Select b bt be)) (union ae (Select b bt be))
     else if a = b then  select a (union at bt) (union ae be)
     else select b (union (Select a at ae) bt) (union (Select a at ae) be))"

lemma union_simp_nothing [simp]: "union a Nothing = a"
  apply (induction a)
  by auto

lemma union_simp_top [simp]: "union a Top = Top"
  apply (induction a)
  by auto

theorem ordered_union [simp]: "ordered n a \<Longrightarrow> ordered n b \<Longrightarrow> ordered n (union a b)"
  apply (induction a b arbitrary: n rule: union.induct)
  apply simp_all
  apply auto
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) ordered.simps ordered_select)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) ordered.simps ordered_select)
  by (metis BDD.inject BDD.simps(5) BDD.simps(7) linorder_cases ordered.simps ordered_select)

lemma dup_free_union [simp]: "norm n a \<Longrightarrow> norm n b \<Longrightarrow> norm n (union a b)"
  apply (induction a b rule: union.induct)
  apply simp_all
  apply auto
  apply (metis BDD.distinct(3) BDD.distinct(6) BDD.inject elim_dup_dedups elim_dup_noop norm.simps norm_ord norm_select norm_widen ordered.simps ordered_union)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) elim_dup_dedups elim_dup_noop norm.cases norm_ord norm_select norm_widen ordered.simps ordered_union)
  by (smt (verit, best) BDD.distinct(6) BDD.inject select_def BDD.simps(5) antisym_conv3 elim_dup_dedups elim_dup_noop norm.simps norm_ord norm_widen ordered_union)

theorem union_correct [simp]: "contains (union a b) p = (contains a p \<or> contains b p)"
  apply (induction a b rule: union.induct)
  apply (simp add: contains_p_correct)
  apply fastforce
  apply fastforce
  apply fastforce
  apply (metis contains_p.simps(3) contains_p_correct select_correct union.simps(5))
  done

end