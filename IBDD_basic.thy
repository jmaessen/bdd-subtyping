theory IBDD_basic
  imports Main
begin

datatype 'b PreBDD = Nothing | Top | Select nat 'b 'b

datatype BDD = BDD "BDD PreBDD"

inductive contains :: "BDD \<Rightarrow> nat set \<Rightarrow> bool" where
  contains_top [simp, intro]: "contains Top f" |
  contains_sel_t: "v \<in> f \<Longrightarrow> contains t f \<Longrightarrow> contains (Select v t e) f" |
  contains_sel_e: "v \<notin> f \<Longrightarrow> contains e f \<Longrightarrow> contains (Select v t e) f"

fun contains_p :: "BDD \<Rightarrow> nat set \<Rightarrow> bool" where
  "contains_p Top _ = True" |
  "contains_p Nothing _ = False" |
  "contains_p (Select v t e) f = (if v \<in> f then contains_p t f else contains_p e f)"

theorem contains_p_correct: "contains a f = contains_p a f"
  apply (rule iffI)
  apply (induction rule: contains.induct)
  apply auto
  apply (induction a f rule: contains_p.induct)
  apply auto
  by (metis contains.simps)

lemma not_contains_nothing [simp]: "contains Nothing f = False"
  by (simp add: contains_p_correct)

lemma contains_sel: "(if v \<in> f then contains t f else contains e f) \<Longrightarrow> contains (Select v t e) f"
  by (metis contains.simps)

inductive ordered :: "nat \<Rightarrow> BDD \<Rightarrow> bool" where
  ordered_top [simp, intro]: "ordered n Top" |
  ordered_nothing [simp, intro]: "ordered n Nothing" |
  ordered_sel [simp, intro]: "n > v \<Longrightarrow> ordered v t \<Longrightarrow> ordered v e \<Longrightarrow> ordered n (Select v t e)"

theorem ordered_widen [simp]: "ordered m a \<Longrightarrow> m < n \<Longrightarrow> ordered n a"
  apply (induction a rule: ordered.induct)
  by auto

inductive rooted :: "nat \<Rightarrow> BDD \<Rightarrow> bool" where
  rooted_top [simp, intro]: "rooted 0 Top" |
  rooted_nothing [simp, intro]: "rooted 0 Nothing" |
  rooted_sel [simp, intro]: "n \<ge> tn \<Longrightarrow> n \<ge> en \<Longrightarrow> rooted tn t \<Longrightarrow> rooted en e \<Longrightarrow> rooted (Suc n) (Select n t e)"

lemma rooted_is_ordered: "rooted n b \<Longrightarrow> ordered n b"
  apply (induction rule: rooted.induct)
  apply auto
  apply (rule ordered_sel)
  apply auto
  apply (metis le_less ordered_widen)
  apply (metis le_less ordered_widen)
  done

lemma ordered_is_rooted: "ordered n b \<Longrightarrow> \<exists>m. rooted m b"
  apply (induction rule: ordered.induct)
  apply auto
  apply (rule exI)
  apply (rule rooted_sel)
  apply auto
  apply (smt (verit, best) BDD.distinct(3) BDD.distinct(5) BDD.inject Suc_leI leI not_less0 ordered.cases rooted.cases)
  apply (smt (verit, best) BDD.distinct(3) BDD.distinct(5) BDD.inject Suc_leI leI not_less0 ordered.cases rooted.cases)
  done

inductive norm :: "nat \<Rightarrow> BDD \<Rightarrow> bool" where
  norm_top [simp, intro]: "norm n Top" |
  norm_nothing [simp, intro]: "norm n Nothing" |
  norm_sel [simp, intro]: "n > v \<Longrightarrow> t \<noteq> e \<Longrightarrow> norm v t \<Longrightarrow> norm v e \<Longrightarrow> norm n (Select v t e)"

lemma norm_ord: "norm n a \<Longrightarrow> ordered n a"
  apply (induction rule: norm.induct)
  by auto

inductive rnorm :: "nat \<Rightarrow> BDD \<Rightarrow> bool" where
  rnorm_top [simp, intro]: "rnorm 0 Top" |
  rnorm_nothing [simp, intro]: "rnorm 0 Nothing" |
  rnorm_sel [simp, intro]: "n \<ge> tn \<Longrightarrow> n \<ge> en \<Longrightarrow> t \<noteq> e \<Longrightarrow> rnorm tn t \<Longrightarrow> rnorm en e \<Longrightarrow> rnorm (Suc n) (Select n t e)"

lemma rnorm_rooted: "rnorm n a \<Longrightarrow> rooted n a"
  apply (induction rule: rnorm.induct)
  by auto

typedef IBDD = "{b | b n. rnorm n b }"
  by auto

theorem norm_widen [simp]: "norm m a \<Longrightarrow> m < n \<Longrightarrow> norm n a"
  apply (induction a rule: norm.induct)
  by auto

abbreviation replace :: "'a set \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'a set" where
  "replace f i v \<equiv> (if v then {i} \<union> f else f - {i})"

lemma ordered_contains_ignore_pre_l: "contains t f' \<Longrightarrow> ordered a t \<Longrightarrow> f' = replace f a x \<Longrightarrow> contains t f"
  apply (induction rule: contains.induct)
  apply simp
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject Diff_iff UnE contains_sel dual_order.strict_implies_not_eq ordered.cases ordered_widen singleton_iff)
  apply (metis BDD.distinct(4) BDD.inject DiffI UnI2 contains.simps less_irrefl ordered.simps ordered_widen singletonD)
  done

lemma ordered_contains_ignore_l: "ordered a t \<Longrightarrow> contains t (replace f a x) \<Longrightarrow> contains t f"
  by (simp add: ordered_contains_ignore_pre_l)

lemma ordered_contains_ignore_r: "contains t f \<Longrightarrow> ordered a t \<Longrightarrow> contains t (replace f a x)"
  apply (induction rule: contains.induct)
  apply simp
  apply (smt (z3) Diff_empty Diff_insert0 contains_sel_t insertI1 insert_Diff insert_Diff1 insert_is_Un ordered_contains_ignore_l)
  apply (smt (z3) Diff_empty Diff_insert0 contains_sel_e insertI1 insert_Diff insert_Diff1 insert_is_Un ordered_contains_ignore_l)
  done

lemma ordered_contains_ignore: "ordered a t \<Longrightarrow> contains t (replace f a x) = contains t f"
  using ordered_contains_ignore_l ordered_contains_ignore_r by blast

lemma ordered_contains_ignore_t [simp]: "ordered a t \<Longrightarrow> contains t ({a} \<union> f) = contains t f"
  apply (insert ordered_contains_ignore[of a t True f])
  apply simp
  done

lemma contains_all_select_t0: "contains s f \<Longrightarrow> s = Select a t e \<Longrightarrow> ordered a t \<Longrightarrow> (\<forall>f. contains s f) \<Longrightarrow> contains t f"
  apply (induction rule: contains.induct)
  apply auto
  apply (rule ordered_contains_ignore_l[where ?x = True and ?a = a])
  apply blast
  by (metis contains_p.simps(3) contains_p_correct insertI1 insert_is_Un)

lemma contains_all_select_t: "ordered a t \<Longrightarrow> (\<forall>f. contains (Select a t e) f) \<Longrightarrow> contains t f"
  using contains_all_select_t0 by blast

lemma contains_all_select_e0: "contains s f \<Longrightarrow> s = Select a t e \<Longrightarrow> ordered a e \<Longrightarrow> (\<forall>f. contains s f) \<Longrightarrow> contains e f"
  apply (induction rule: contains.induct)
  apply auto
  apply (rule ordered_contains_ignore_l[where ?x = False and ?a = a])
  apply auto
  by (metis Diff_iff contains_p.simps(3) contains_p_correct insertI1)

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
  by (metis Un_insert_left contains_p.simps(3) contains_p_correct insert_iff member_remove remove_def)

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