theory BDD_basic
  imports Main
begin

datatype BDD = Nothing | Top | Select nat BDD BDD

inductive contains :: "BDD \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool" where
  contains_top [simp, intro]: "contains Top f" |
  contains_sel_t: "f v \<Longrightarrow> contains t f \<Longrightarrow> contains (Select v t e) f" |
  contains_sel_e: "\<not>f v \<Longrightarrow> contains e f \<Longrightarrow> contains (Select v t e) f"

fun contains_p :: "BDD \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "contains_p Top _ = True" |
  "contains_p Nothing _ = False" |
  "contains_p (Select v t e) f = (if f v then contains_p t f else contains_p e f)"

theorem contains_p_correct: "contains a f = contains_p a f"
  apply (rule iffI)
  apply (induction rule: contains.induct)
  apply auto
  apply (induction a f rule: contains_p.induct)
  apply auto
  by (metis contains.simps)

lemma not_contains_nothing [simp]: "contains Nothing f = False"
  by (simp add: contains_p_correct)

lemma contains_sel: "(if f v then contains t f else contains e f) \<Longrightarrow> contains (Select v t e) f"
  by (metis contains.simps)

inductive ordered :: "nat \<Rightarrow> BDD \<Rightarrow> bool" where
  ordered_top [simp, intro]: "ordered n Top" |
  ordered_nothing [simp, intro]: "ordered n Nothing" |
  ordered_sel [simp, intro]: "n > v \<Longrightarrow> ordered v t \<Longrightarrow> ordered v e \<Longrightarrow> ordered n (Select v t e)"

inductive norm :: "nat \<Rightarrow> BDD \<Rightarrow> bool" where
  norm_top [simp, intro]: "norm n Top" |
  norm_nothing [simp, intro]: "norm n Nothing" |
  norm_sel [simp, intro]: "n > v \<Longrightarrow> t \<noteq> e \<Longrightarrow> norm v t \<Longrightarrow> norm v e \<Longrightarrow> norm n (Select v t e)"

lemma norm_ord: "norm n a \<Longrightarrow> ordered n a"
  apply (induction rule: norm.induct)
  by auto

theorem ordered_widen [simp]: "ordered m a \<Longrightarrow> m < n \<Longrightarrow> ordered n a"
  apply (induction a rule: ordered.induct)
  by auto

theorem norm_widen [simp]: "norm m a \<Longrightarrow> m < n \<Longrightarrow> norm n a"
  apply (induction a rule: norm.induct)
  by auto

abbreviation replace :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b" where
  "replace f i v \<equiv> (\<lambda>x. (if i = x then v else f x))"

lemma ordered_contains_ignore_pre_l: "contains t f' \<Longrightarrow> ordered a t \<Longrightarrow> f' = replace f a x \<Longrightarrow> contains t f"
  apply (induction rule: contains.induct)
  apply simp
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject contains_sel_t nat_less_le ordered.cases ordered_widen)
  apply (metis BDD.distinct(4) BDD.distinct(6) BDD.inject contains_sel_e nat_less_le ordered.cases ordered_widen)
  done

lemma ordered_contains_ignore_l: "ordered a t \<Longrightarrow> contains t (replace f a x) \<Longrightarrow> contains t f"
  by (simp add: ordered_contains_ignore_pre_l)

lemma ordered_contains_ignore_r: "contains t f \<Longrightarrow> ordered a t \<Longrightarrow> contains t (replace f a x)"
  apply (induction rule: contains.induct)
  apply simp
  apply (metis (mono_tags, lifting) BDD.distinct(3) BDD.distinct(5) BDD.inject contains_sel nat_neq_iff ordered.cases ordered_widen)
  apply (metis (mono_tags, lifting) BDD.distinct(3) BDD.distinct(5) BDD.inject contains_sel nat_neq_iff ordered.cases ordered_widen)
  done

lemma ordered_contains_ignore: "ordered a t \<Longrightarrow> contains t (replace f a x) = contains t f"
  using ordered_contains_ignore_l ordered_contains_ignore_r by blast

lemma ordered_contains_ignore_t [simp]: "ordered a t \<Longrightarrow> contains t (\<lambda>x. a \<noteq> x \<longrightarrow> f x) = contains t f"
  apply (insert ordered_contains_ignore[of a t True f])
  apply simp
  by presburger

lemma contains_all_select_t0: "contains s f \<Longrightarrow> s = Select a t e \<Longrightarrow> ordered a t \<Longrightarrow> (\<forall>f. contains s f) \<Longrightarrow> contains t f"
  apply (induction rule: contains.induct)
  apply auto
  apply (rule ordered_contains_ignore_l[where ?x = True and ?a = a])
  apply blast
  apply (metis (mono_tags) contains_p.simps(3) contains_p_correct)
  done

lemma contains_all_select_t: "ordered a t \<Longrightarrow> (\<forall>f. contains (Select a t e) f) \<Longrightarrow> contains t f"
  using contains_all_select_t0 by blast

lemma contains_all_select_e0: "contains s f \<Longrightarrow> s = Select a t e \<Longrightarrow> ordered a e \<Longrightarrow> (\<forall>f. contains s f) \<Longrightarrow> contains e f"
  apply (induction rule: contains.induct)
  apply auto
  apply (rule ordered_contains_ignore_l[where ?x = False and ?a = a])
  apply auto
  by (smt (verit, del_insts) BDD.distinct(5) BDD.inject contains.cases)

lemma contains_all_select_e: "ordered a e \<Longrightarrow> (\<forall>f. contains (Select a t e) f) \<Longrightarrow> contains e f"
  using contains_all_select_e0 by blast

lemma contains_all_select: "ordered a t \<Longrightarrow> ordered a e \<Longrightarrow> (\<forall>f. contains (Select a t e) f) \<Longrightarrow> contains t f \<and> contains e f"
  by (auto simp add: contains_all_select_e contains_all_select_t)

lemma norm_top: "norm n b \<Longrightarrow> (\<forall>f. contains b f) \<Longrightarrow> b = Top"
  apply (induction rule: norm.induct)
  apply (rule refl)
  using contains.simps apply blast
  by (metis contains_all_select norm_ord)


lemma select_var_eq0:
  "ordered va t \<Longrightarrow> ordered va e \<Longrightarrow>
   ordered vb t \<Longrightarrow> ordered vb e \<Longrightarrow>
   a = Select va t e \<Longrightarrow> b = Select vb t e \<Longrightarrow>
   f' = replace (replace f va True) vb False \<Longrightarrow>
   contains t f' \<noteq> contains e f' \<Longrightarrow>
   contains a f' = contains b f' \<Longrightarrow>
   va = vb"
  by (metis contains_p.simps(3) contains_p_correct)

lemma select_var_eq:
  "ordered va t \<Longrightarrow> ordered va e \<Longrightarrow>
   ordered vb t \<Longrightarrow> ordered vb e \<Longrightarrow>
   contains t (replace (replace f va True) vb False) \<noteq> contains e (replace (replace f va True) vb False) \<Longrightarrow>
   contains (Select va t e) (replace (replace f va True) vb False) = contains (Select vb t e) (replace (replace f va True) vb False) \<Longrightarrow>
   va = vb"
  apply (rule select_var_eq0[
        where ?a = "Select va t e" and ?b = "Select vb t e"])
  by auto

lemma double_replace_exclusion:
   "ordered va t \<Longrightarrow>
    ordered va e \<Longrightarrow>
    ordered vb t \<Longrightarrow>
    ordered vb e \<Longrightarrow>
    contains t f \<noteq> contains e f \<Longrightarrow>
    contains t (replace (replace f va x) vb y) \<noteq>
    contains e (replace (replace f va x) vb y)"
  apply (subst ordered_contains_ignore[where ?a = vb])
  apply assumption
  apply (subst ordered_contains_ignore[where ?a = vb])
  apply assumption
  apply (subst ordered_contains_ignore[where ?a = va])
  apply assumption
  apply (subst ordered_contains_ignore[where ?a = va])
  by assumption

lemma select_var_eq_gen:
  "ordered va t \<Longrightarrow> ordered va e \<Longrightarrow>
   ordered vb t \<Longrightarrow> ordered vb e \<Longrightarrow>
   contains t f \<noteq> contains e f \<Longrightarrow>
   contains (Select va t e) (replace (replace f va True) vb False) = contains (Select vb t e) (replace (replace f va True) vb False) \<Longrightarrow>
   va = vb"
  apply (rule select_var_eq[where ?f = f and ?e = e])
  apply assumption
  apply assumption
  apply assumption
  apply assumption
  defer
  apply assumption
  apply (rule double_replace_exclusion)
  by auto

lemma select_var_match0:
  "a = Select va ta ea \<Longrightarrow> b = Select vb tb eb \<Longrightarrow>
   ordered n a \<Longrightarrow> ordered m b \<Longrightarrow>
   ta = tb \<Longrightarrow>
   ea = eb \<Longrightarrow>
   contains ta f \<noteq> contains ea f \<Longrightarrow>
   (\<forall>f. contains a f = contains b f) \<Longrightarrow>
   Select va ta ea = Select vb tb eb"
  apply simp
  apply (rule select_var_eq[where ?t = tb and ?e = eb and ?f = f])
  prefer 5
  apply (rule double_replace_exclusion)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.cases)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.cases)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.cases)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.cases)
  defer
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.cases)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.cases)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.cases)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.cases)
  apply auto
  done

lemma select_var_match:
  "ordered n (Select va ta ea) \<Longrightarrow> ordered m (Select vb tb eb) \<Longrightarrow>
   contains ta f \<noteq> contains ea f \<Longrightarrow>
   (\<forall>f. contains (Select va ta ea) f = contains (Select vb tb eb) f) \<Longrightarrow>
   ta = tb \<Longrightarrow>
   ea = eb \<Longrightarrow>
   Select va ta ea = Select vb tb eb"
  apply (rule select_var_match0)
  apply (rule refl)
  apply (rule refl)
  by simp_all


end