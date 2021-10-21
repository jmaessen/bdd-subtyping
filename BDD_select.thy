theory BDD_select
  imports Main BDD_basic
begin

definition select :: "nat \<Rightarrow> BDD \<Rightarrow> BDD \<Rightarrow> BDD" where
  "select a t e = (if t = e then t else Select a t e)"

lemma select_noop [simp]: "norm n t \<Longrightarrow> norm n e \<Longrightarrow> t \<noteq> e \<Longrightarrow> select v t e = Select v t e"
  by (auto simp: select_def)

theorem norm_select [simp]: "n > a \<Longrightarrow> norm a t \<Longrightarrow> norm a e \<Longrightarrow> norm n (select a t e)"
  by (simp add: select_def)

theorem ordered_select [simp]: "n > a \<Longrightarrow> ordered a t \<Longrightarrow> ordered a e \<Longrightarrow> ordered n (select a t e)"
  by (simp add: select_def)

theorem select_correct [simp]: "contains (select a t e) f = contains (Select a t e) f"
  apply (rule iffI)
  apply (auto simp add: select_def)
  apply (metis (full_types) contains_sel_e contains_sel_t)
  using contains.cases by auto

end