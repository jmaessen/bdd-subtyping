theory BDD_not
  imports Main BDD_basic BDD_select BDD_dedup
begin

fun not :: "BDD \<Rightarrow> BDD" where
  "not Nothing = Top" |
  "not Top = Nothing" |
  "not (Select a t e) = Select a (not t) (not e)"

theorem not_inj [simp]: "(not a = not b) = (a = b)"
  apply (induction a arbitrary: b)
  apply auto
  apply (metis BDD.distinct(5) not.elims)
  apply (metis BDD.distinct(3) not.elims)
  by (smt (z3) BDD.distinct(5) BDD.inject not.cases not.simps(1) not.simps(2) not.simps(3))

theorem not_ordered [simp]: "ordered n (not a) = ordered n a"
  apply (rule iffI)
  apply (induction a arbitrary: n)
  apply simp_all
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) ordered.simps)
  apply (induction a rule: ordered.induct)
  by auto

theorem not_norm [simp]: "norm n (not a) = norm n a"
  apply (rule iffI)
  apply (induction a)
  apply (auto)
  using norm.cases apply auto[1]
  apply (rule norm_sel)
  apply auto
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject elim_dup_dedups elim_dup_noop norm_ord norm_widen not_ordered)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject elim_dup_dedups elim_dup_noop norm_ord norm_widen not_ordered)
  apply (induction n a rule: norm.induct)
  by simp_all

theorem not_correct [simp]: "contains (not a) f \<noteq> contains a f"
  apply auto
  apply (induction a)
  apply simp_all
  using contains.cases apply blast
  apply (induction a)
  apply simp_all
  by (metis contains_sel_e contains_sel_t)

theorem not_inv [simp]: "not (not a) = a" 
  apply (induction a)
  apply auto
  done


lemma all_not [simp]: "(\<forall>f. \<not>contains a f) = (\<forall>f. contains (not a) f)"
  using not_correct by blast

lemma norm_nothing: "norm n b \<Longrightarrow> (\<forall>f. ~contains b f) \<Longrightarrow> b = Nothing"
  apply (induction rule: norm.induct)
  using contains.simps apply blast
  apply (rule refl)
  by (metis BDD.distinct(5) BDD_basic.norm_top all_not norm_sel not.simps(3) not_norm)

end