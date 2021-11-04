theory BDD_subtype_correctness
  imports Main BDD_basic BDD_select BDD_subtype_defs
begin

lemma common_sf_preserve: "sub_free n tr t \<Longrightarrow> sub_free n tr e \<Longrightarrow> sub_free_opt n tr (common m i tr t e)"
  apply (induction m i tr t e rule: common.induct)
  apply (simp_all split: bool.split Relatedness.split)
  defer
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.cases sub_free_some)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.cases sub_free_some)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.cases sub_free_some)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.cases sub_free_some)
  apply (case_tac "ie < it")
  apply (case_tac "tr it c")
  apply (case_tac "tr ie c")
  apply simp_all
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.simps sub_free_some)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.cases sub_free_some)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.cases sub_free_some)
  apply (case_tac "tr ie it")
  apply (case_tac "tr ie c")
  apply simp_all
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (case_tac "tr ie c")
  apply simp_all
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.cases)
  apply (case_tac "tr ie it")
  apply (case_tac "tr ie c")
  apply simp_all
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.cases)
  apply (case_tac "tr ie c")
  apply simp_all
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.cases)
  apply (case_tac "it = ie")
  apply simp_all
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.simps)
  apply (case_tac "tr ie c")
  apply (case_tac "tr it c")
  apply (case_tac "tr it ie")
  apply simp_all
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.cases)
  apply (case_tac "tr it ie")
  apply simp_all
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.cases)
  apply (case_tac "tr it ie")
  apply simp_all
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.cases)
  apply (case_tac "tr it c")
  apply simp_all
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.simps sub_free_some)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.simps sub_free_some)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.simps sub_free_some)
  apply (case_tac "tr it ie")
  apply simp_all
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.cases)
  done

lemma common_sf: "sub_free n tr t \<Longrightarrow> sub_free n tr e \<Longrightarrow> common m i tr t e = Some s \<Longrightarrow> sub_free n tr s"
  by (metis common_sf_preserve option.distinct(1) option.sel sub_free_opt.cases)


lemma common_df_preserve: "disj_free n tr t \<Longrightarrow> disj_free n tr e \<Longrightarrow> disj_free_opt n tr (common m i tr t e)"
  apply (induction m i tr t e rule: common.induct)
  apply (simp_all split: Relatedness.split)
  defer
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases disj_free_some select'_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases disj_free_some select'_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases disj_free_some select'_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases disj_free_some select'_df_preserve)
  apply (case_tac "tr ie c")
  apply (case_tac "ie < it")
  apply (case_tac "tr it c")
  apply simp_all
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases disj_free_some select'_df_preserve)
  apply (case_tac "tr ie it")
  apply simp_all
  apply (metis BDD.distinct(3) BDD.inject BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.distinct(3) BDD.inject BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.distinct(3) BDD.inject BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (case_tac "tr ie it")
  apply simp_all
  apply (metis BDD.distinct(3) BDD.inject BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.distinct(3) BDD.inject BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.distinct(3) BDD.inject BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (case_tac "tr it ie")
  apply simp_all
  apply (metis BDD.distinct(3) BDD.inject BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.distinct(3) BDD.inject BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.distinct(3) BDD.inject BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (case_tac "ie < it")
  apply (case_tac "tr it c")
  apply simp_all
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases disj_free_some select'_df_preserve)
  apply (case_tac "tr ie it")
  apply simp_all
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (case_tac "tr ie it")
  apply simp_all
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases disj_free_some select'_df_preserve)
  apply (case_tac "ie < it")
  apply (case_tac "tr it c")
  apply simp_all
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases disj_free_some select'_df_preserve)
  apply (case_tac "tr ie it")
  apply simp_all
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (case_tac "tr ie it")
  apply simp_all
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (case_tac "it = ie")
  apply simp_all
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases select'_df_preserve)
  apply (case_tac "tr it ie")
  apply simp_all
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  done

lemma common_df: "disj_free n tr t \<Longrightarrow> disj_free n tr e \<Longrightarrow> common m i tr t e = Some s \<Longrightarrow> disj_free n tr s"
  by (metis common_df_preserve option.distinct(1) option.sel disj_free_opt.cases)


lemma subtype_erases_subtype:
  "sub_free n tr t \<Longrightarrow> well_formed_tr n tr \<Longrightarrow> pwfbdd i tr t \<Longrightarrow>
   i \<le> n \<Longrightarrow> tr i n = Subtype \<Longrightarrow> sub_free i tr t"
  apply (induction n tr t rule: sub_free.induct)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject less_imp_le_nat pwf_weaken pwfbdd.cases sub_free_sel wftr3_trans wftr_wftr3)
  apply blast
  apply blast
  done

lemma disjoint_erases_disjoint_lt:
  "disj_free n tr t \<Longrightarrow> well_formed_tr n tr \<Longrightarrow> pwfbdd i tr t \<Longrightarrow>
   i \<le> n \<Longrightarrow> tr i n = Disjoint \<Longrightarrow> sub_free i tr t"
  apply (induction n tr t rule: disj_free.induct; blast?)
  apply (smt (verit, ccfv_threshold) BDD.inject BDD.simps(5) BDD.simps(7) leD linear pwf_weaken pwfbdd.cases sub_free_sel wftr_refl0 wftr_sub_disj)
  done
  
lemma disjoint_erases_disjoint_gt:
  "disj_free i tr t \<Longrightarrow> well_formed_tr n tr \<Longrightarrow> pwfbdd i tr t \<Longrightarrow>
   i \<le> n \<Longrightarrow> tr i n = Disjoint \<Longrightarrow> sub_free n tr t"
  apply (induction i tr t rule: disj_free.induct; blast?)
  apply (smt (verit) BDD.inject dual_order.trans le_cases3 order.strict_iff_order pwf_weaken pwfbdd.simps sub_free.simps wftr_refl0 wftr_sub_disj wftr_weaken)
  done
  

lemma common_pwfbdd_preserve:
  "well_formed_tr i tr \<Longrightarrow> n \<le> i \<Longrightarrow> pwfbdd n tr t \<Longrightarrow> pwfbdd n tr e \<Longrightarrow> 
   disj_free i tr t \<Longrightarrow> sub_free i tr e \<Longrightarrow> common n i tr t e = Some r \<Longrightarrow> pwfbdd n tr r"
  apply (induction n i tr t e arbitrary: r rule: common.induct)
  apply auto[4]
  apply (simp_all only: common.simps if_False)
  (* 5/5 *)
  apply (subgoal_tac "~(n \<le> it \<or> n \<le> ie)")
  prefer 2
  apply (metis option.distinct(1))
  using [[simp_depth_limit=1]] apply (simp only: not_le common.simps if_False if_True not_False_eq_True not_True_eq_False)
  apply simp_all
  apply auto
  apply (case_tac "ie < it")
  (* 5: 6 *)
  apply (case_tac "tr it c")
  (* 5: 8 *)
  apply auto[1]
  apply (case_tac "common it c tr et (Select ie te ee)")
  apply auto[2]
  apply (smt (verit) BDD.distinct(5) BDD.inject BDD.simps(5) common_sf disj_free.simps le_trans nat_le_linear pwfbdd.simps select_pwf subtype_erases_subtype)
  apply (metis BDD.distinct(5) BDD.inject BDD.simps(5) disj_free.cases)
  (* 5: 8 *)
  apply auto[1]
  apply (case_tac "tr ie it")
  apply (auto simp add: select'_def split: option.splits)[3]
  apply (smt (verit) BDD.distinct(5) BDD.inject BDD.simps(5) Relatedness.distinct(1) common_df common_sf disj_free.cases erase_disj_df_preserve erase_disj_disj_free erase_disj_sf_preserve erase_disjoints_pwf erase_subtypes_pwf erase_subtypes_sf_preserve erase_subtypes_sub_free le_cases3 order.strict_iff_order pwf_weaken pwfbdd.simps select_df_preserve select_pwf select_sf_preserve sub_free.simps)
  apply (smt (verit) BDD.distinct(3) BDD.distinct(5) BDD.inject Relatedness.distinct(1) common_df common_sf disj_free.cases erase_disj_disj_free erase_disj_sf_preserve erase_disjoints_pwf erase_subtypes_df_preserve erase_subtypes_pwf erase_subtypes_sf_preserve erase_subtypes_sub_free le_cases3 less_imp_le_nat pwf_weaken pwfbdd.cases select_pwf select_sf_preserve sub_free.simps)
  apply (smt (verit) BDD.distinct(5) BDD.inject BDD.simps(5) Relatedness.distinct(3) common_df common_sf disj_free.simps erase_disj_df_preserve erase_disj_disj_free erase_disj_sf_preserve erase_disjoints_pwf erase_subtypes_df_preserve erase_subtypes_pwf erase_subtypes_sf_preserve erase_subtypes_sub_free nat_less_le pwfbdd.simps select_df_preserve select_pwf select_sf_preserve sub_free.simps)
  (* 5: 5 *)
  apply auto[1]
  apply (case_tac "it = ie")
  apply (auto simp add: split: Relatedness.splits bool.splits)[2]
  (* 5: 8 *)
  apply (smt (verit) BDD.distinct(5) BDD.inject BDD.simps(5) common_df common_sf disj_free.cases pwfbdd.cases select'_some select_pwf sub_free.simps)
  apply (metis BDD.distinct(5) BDD.inject BDD.simps(5) sub_free.simps)
  apply (smt (verit) BDD.distinct(5) BDD.inject BDD.simps(5) common_sf disjoint_erases_disjoint_lt less_le linear option.inject order.trans pwfbdd.simps pwfbdd_sel select'_some select_pwf sub_free.simps)
  (* 5: 5 *)
  apply (auto simp add: select'_def split: option.splits bool.splits)
  apply (smt (verit) BDD.distinct(5) BDD.inject BDD.simps(5) common_df common_sf disj_free.simps erase_disj_df_preserve erase_disj_disj_free erase_disj_sf_preserve erase_disjoints_pwf erase_subtypes_df_preserve erase_subtypes_pwf erase_subtypes_sf_preserve erase_subtypes_sub_free not_le_imp_less not_less_iff_gr_or_eq pwf_weaken pwfbdd.simps select_df_preserve select_pwf select_sf_preserve sub_free.simps)
  (* 4/5 *)
  apply (case_tac "n \<le> it")
  apply (auto simp add: select'_def split: Relatedness.splits bool.splits option.splits)[2]
  apply (metis BDD.distinct(5) BDD.inject BDD.simps(5) common_sf disj_free.cases pwfbdd.simps select_pwf sub_free_nothing)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases)
  apply (smt (verit) BDD.distinct(5) BDD.inject BDD.simps(5) common_df common_sf disj_free.simps pwfbdd.simps select_pwf sub_free.simps)
  (* 3/5 *)
  apply (case_tac "n \<le> it")
  apply (auto simp add: select'_def split: Relatedness.splits bool.splits option.splits)[2]
  apply (smt (verit) BDD.distinct(5) BDD.inject BDD.simps(5) common_df common_sf disj_free.simps pwfbdd.simps select_pwf sub_free.simps)
  apply (smt (verit) BDD.distinct(5) BDD.inject BDD.simps(5) common_df common_sf disj_free.simps pwfbdd.simps select_pwf sub_free.simps)
  apply (smt (verit) BDD.distinct(5) BDD.inject BDD.simps(5) common_df common_sf disj_free.simps pwfbdd.simps select_pwf sub_free.simps)
  (* 2/5 *)
  apply (case_tac "n \<le> ie")
  apply (auto simp add: select'_def split: Relatedness.splits bool.splits option.splits)[2]
  apply (smt (verit) BDD.distinct(5) BDD.inject BDD.simps(5) common_df common_sf disj_free.simps pwfbdd.simps select_pwf sub_free.simps)
  apply (smt (verit) BDD.distinct(5) BDD.inject BDD.simps(5) common_df common_sf disj_free.simps pwfbdd.simps select_pwf sub_free.simps)
  apply (smt (verit) BDD.distinct(5) BDD.inject BDD.simps(5) common_df common_sf disj_free.simps pwfbdd.simps select_pwf sub_free.simps)
  (* 1/5 *)
  apply (case_tac "n \<le> ie")
  apply (auto simp add: select'_def split: Relatedness.splits bool.splits option.splits)[2]
  apply (smt (verit) BDD.distinct(5) BDD.inject BDD.simps(5) common_df common_sf disj_free.simps pwfbdd.simps select_pwf sub_free.simps)
  apply (smt (verit) BDD.distinct(5) BDD.inject BDD.simps(5) common_df common_sf disj_free.simps pwfbdd.simps select_pwf sub_free.simps)
  apply (smt (verit) BDD.distinct(5) BDD.inject BDD.simps(5) common_df common_sf disj_free.simps pwfbdd.simps select_pwf sub_free.simps)
  done

lemma common_nothing [simp]:
  "pwfbdd n tr e \<Longrightarrow> n \<le> c \<Longrightarrow> common n c tr Nothing e = Some s \<Longrightarrow> erase_disjoints c tr s = Nothing"
  apply (induction n tr e arbitrary: s rule: pwfbdd.induct)
  apply (auto simp add: select'_def split: Relatedness.splits option.splits)
  apply (simp add: BDD_select.select_def)
  apply (simp add: BDD_select.select_def)
  apply (simp add: BDD_select.select_def)
  done

lemma pwfbdd_1:
  "well_formed_tr 1 tr \<Longrightarrow> pwfbdd 1 tr t \<Longrightarrow>
   (t = Nothing \<or> t = Top \<or> t = Select 0 Top Nothing \<or> t = Select 0 Nothing Top)"
  apply (case_tac t)
  apply force
  apply force
  using pwfbdd.cases apply auto
  apply (metis BDD.distinct(5) BDD.inject BDD.simps(5) less_Suc0 less_zeroE)
  apply (metis BDD.distinct(5) BDD.inject BDD.simps(5) less_Suc0 less_zeroE)
  apply (metis BDD.distinct(5) BDD.inject BDD.simps(5) less_Suc0 less_zeroE)
  apply (metis BDD.distinct(5) BDD.inject BDD.simps(5) less_Suc0 less_zeroE)
  apply (metis BDD.distinct(5) BDD.inject BDD.simps(5) less_Suc0 less_zeroE)
  apply (metis BDD.distinct(5) BDD.inject BDD.simps(5) less_Suc0 less_zeroE)
  apply (metis BDD.distinct(5) BDD.inject BDD.simps(5) less_Suc0 less_zeroE)
  apply (metis BDD.distinct(5) BDD.inject BDD.simps(5) less_Suc0 less_zeroE)
  done

lemma select'_some: "tt = Some t \<Longrightarrow> ee = Some e \<Longrightarrow> z = select i t e \<Longrightarrow> select' i tt ee = Some z"
  by auto

lemma common_refl:
  "well_formed_tr c tr \<Longrightarrow> n \<le> c \<Longrightarrow>
   pwfbdd c tr a \<Longrightarrow> pwfbdd n tr a \<Longrightarrow>
   common n c tr a a = Some a"
  apply (induction a arbitrary: n c)
  apply auto
  apply (case_tac n)
  apply auto
  apply (metis BDD.distinct(5) BDD.simps(5) less_zeroE pwfbdd.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) leD pwfbdd.simps)
  apply (metis BDD.distinct(5) BDD.inject BDD.simps(5) BDD_select.select_def dual_order.strict_implies_order pwf_weaken pwfbdd.cases select'_some_some_some)
  done

theorem select_is_top: "select i t e = Top \<Longrightarrow> t = Top \<and> e = Top"
  by (metis BDD.distinct(5) BDD_select.select_def)

lemma sub_free_erase_subty:
  "well_formed_tr c tr \<Longrightarrow> pwfbdd c tr t \<Longrightarrow>
   disj_free c tr t \<Longrightarrow> erase_disjoints c tr t = t"
  by (meson erase_disj_df_noop pwf_is_norm)

lemma erase_disjoints_idem[simp]:
  "erase_disjoints c tr (erase_disjoints c tr t) = erase_disjoints c tr t"
  apply (induction t)
  apply (auto simp add: select_def)
  done

lemma erase_subtypes_idem[simp]:
  "erase_subtypes c tr (erase_subtypes c tr t) = erase_subtypes c tr t"
  apply (induction t)
  apply (auto simp add: select_def)
  done

lemma erase_exchange:
  "erase_subtypes c tr (erase_disjoints d tr t) = erase_disjoints d tr (erase_subtypes c tr t)"
  apply (induction t)
  apply (auto simp add: select_def)
  done

lemma common_dom_e:
  "n > ie \<Longrightarrow> pwfbdd ie tr t \<Longrightarrow>
   common n c tr t (Select ie te ee) =
     (case tr ie c of
        Disjoint \<Rightarrow> select' ie (Some te) (common ie c tr t ee) |
        _ \<Rightarrow> select' ie (common ie c tr (erase_disjoints ie tr t) te)
                        (common ie c tr (erase_subtypes ie tr t) ee))"
  apply (case_tac t)
  using pwfbdd.cases apply auto
  using pwfbdd.cases apply fastforce
  using pwfbdd.cases apply fastforce
  done

theorem common_correct_a:
  "erasures c tr s t e \<Longrightarrow>
   well_formed_tr c tr \<Longrightarrow> n \<le> c \<Longrightarrow>
   disj_free c tr t \<Longrightarrow> sub_free c tr e \<Longrightarrow>
   pwfbdd n tr t \<Longrightarrow> pwfbdd n tr e \<Longrightarrow> pwfbdd n tr s \<Longrightarrow>
   common n c tr t e \<noteq> None"
  apply (induction s t e arbitrary: n rule: erasures.induct)
  apply simp_all
  apply auto
  (* 9/9 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) leD pwfbdd.simps)
  (* 8/9 *)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject dual_order.trans erase_disj_disj_free erase_subtypes_sub_free erasures_erase le_cases not_None_eq option.distinct(1) pwfbdd.cases select'_some_some_some)
  (* 7/9 *)
  apply (rename_tac et ee t t0 e n)
  apply (case_tac t0)
  (* 7: 9 *)
  apply auto[1]
  apply (metis (no_types, hide_lams) BDD.distinct(3) BDD.distinct(5) BDD.inject leD pwfbdd.cases)
  apply (smt (verit) BDD.distinct(5) BDD.inject BDD.simps(5) dual_order.strict_iff_order pwf_weaken pwfbdd.cases select'_some_some_some sub_free.simps)
  apply auto[1]
  apply (metis (no_types, hide_lams) BDD.distinct(3) BDD.distinct(5) BDD.inject leD pwfbdd.cases)
  apply (smt (verit) BDD.distinct(5) BDD.inject BDD.simps(5) dual_order.strict_iff_order pwf_weaken pwfbdd.cases select'_some_some_some sub_free.simps)
  (* 7: 7 *)
  apply (rename_tac v tt te)
  apply simp_all
  apply auto[1]
  (* 7: 30 *)
  apply (metis (no_types, hide_lams) BDD.distinct(3) BDD.distinct(5) BDD.inject leD pwfbdd.cases)
  apply (metis (no_types, hide_lams) BDD.distinct(3) BDD.distinct(5) BDD.inject common.simps(5) common_refl erase_disjoints_pwf erasures_erase leD le_cases option.distinct(1) pwf_weaken pwfbdd.cases)
  apply (metis (no_types, hide_lams) BDD.distinct(3) BDD.distinct(5) BDD.inject leD pwfbdd.cases)
  apply (metis (no_types, hide_lams) BDD.distinct(3) BDD.distinct(5) BDD.inject leD pwfbdd.cases)
  apply (metis (no_types, hide_lams) BDD.distinct(3) BDD.distinct(5) BDD.inject common.simps(5) common_refl erase_disjoints_pwf erasures_erase leD le_cases option.distinct(1) pwf_weaken pwfbdd.cases)
  apply (metis (no_types, hide_lams) BDD.distinct(3) BDD.distinct(5) BDD.inject leD pwfbdd.cases)
  apply (metis (no_types, hide_lams) BDD.distinct(3) BDD.distinct(5) BDD.inject leD pwfbdd.cases)
  (* 7: 23 *)
  apply (subgoal_tac "sub_free i tr tt")
  prefer 2
  apply (metis BDD.distinct(3) BDD.inject BDD.simps(7) disjoint_erases_disjoint_gt leI le_cases pwfbdd.cases wftr_weaken)
  apply (subgoal_tac "erase_subtypes i tr tt = tt")
  prefer 2
  apply (metis BDD.distinct(3) BDD.inject BDD.simps(7) erase_subtypes_sf_noop leI pwf_is_norm pwf_weaken pwfbdd.cases)
  apply (subgoal_tac "\<exists>y. common i c tr (Select v tt te) et = Some y")
  prefer 2
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject dual_order.trans erase_disjoints_pwf erase_subtypes_sub_free erasures_erase le_cases pwfbdd.cases)
  apply simp
  apply (auto simp add: select'_def split: option.split)
  (* 7: 28 *)
  apply (smt (verit) BDD.distinct(5) BDD.inject BDD.simps(5) erase_disj_df_noop erase_disj_df_preserve erase_disjoints.simps(1) erasures_erase linorder_cases pwf_is_norm pwfbdd.cases pwfbdd.simps)
  (* 7: 27 *)
  apply (smt (verit) BDD.distinct(5) BDD.inject BDD.simps(5) dual_order.trans erase_disj_df_noop erase_disj_df_preserve erase_disj_sf_preserve erase_disjoints.simps(1) erase_disjoints_pwf erasures_erase leI le_cases3 pwf_is_norm pwfbdd.simps sub_free.cases wftr_symm wftr_weaken)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) leD pwfbdd.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject common.simps(5) common_refl dual_order.order_iff_strict erase_disjoints_pwf erasures_erase option.distinct(1) pwf_weaken pwfbdd.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject common.simps(5) common_refl dual_order.order_iff_strict erase_disjoints_pwf erasures_erase option.distinct(1) pwf_weaken pwfbdd.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject common.simps(5) common_refl dual_order.order_iff_strict erase_disjoints_pwf erasures_erase option.distinct(1) pwf_weaken pwfbdd.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject common.simps(5) common_refl dual_order.order_iff_strict erase_disjoints_pwf erasures_erase option.distinct(1) pwf_weaken pwfbdd.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject common.simps(5) common_refl dual_order.order_iff_strict erase_disjoints_pwf erasures_erase option.distinct(1) pwf_weaken pwfbdd.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject common.simps(5) common_refl dual_order.order_iff_strict erase_disjoints_pwf erasures_erase option.distinct(1) pwf_weaken pwfbdd.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject common.simps(5) common_refl dual_order.order_iff_strict erase_disjoints_pwf erasures_erase option.distinct(1) pwf_weaken pwfbdd.cases)
  (* 7: 18 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) Relatedness.distinct(1) dual_order.trans erase_disj_df_preserve erase_disjoints.simps(1) erase_disjoints_pwf erase_subtypes_sub_free erasures_erase le_cases pwfbdd.cases sub_free_erase_subty wftr_weaken)
  (* 7: 17 *)
  apply (smt (verit) BDD.distinct(5) BDD.inject BDD.simps(5) dual_order.trans erase_disj_df_noop erase_disj_df_preserve erase_disj_sf_preserve erase_disjoints.simps(1) erase_disjoints_pwf erasures_erase leI le_cases3 pwf_is_norm pwfbdd.simps sub_free.cases wftr_symm wftr_weaken)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject common.simps(5) common_refl dual_order.order_iff_strict erase_disjoints_pwf erasures_erase option.distinct(1) pwf_weaken pwfbdd.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject common.simps(5) common_refl dual_order.order_iff_strict erase_disjoints_pwf erasures_erase option.distinct(1) pwf_weaken pwfbdd.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject common.simps(5) common_refl dual_order.order_iff_strict erase_disjoints_pwf erasures_erase option.distinct(1) pwf_weaken pwfbdd.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject common.simps(5) common_refl dual_order.order_iff_strict erase_disjoints_pwf erasures_erase option.distinct(1) pwf_weaken pwfbdd.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject common.simps(5) common_refl dual_order.order_iff_strict erase_disjoints_pwf erasures_erase option.distinct(1) pwf_weaken pwfbdd.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject common.simps(5) common_refl dual_order.order_iff_strict erase_disjoints_pwf erasures_erase option.distinct(1) pwf_weaken pwfbdd.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject common.simps(5) common_refl dual_order.order_iff_strict erase_disjoints_pwf erasures_erase option.distinct(1) pwf_weaken pwfbdd.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject common.simps(5) common_refl dual_order.order_iff_strict erase_disjoints_pwf erasures_erase option.distinct(1) pwf_weaken pwfbdd.cases)
  (* 7: 8 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) Relatedness.distinct(1) dual_order.trans erase_disj_df_preserve erase_disjoints.simps(1) erase_disjoints_pwf erase_subtypes_sub_free erasures_erase le_cases pwfbdd.cases sub_free_erase_subty wftr_weaken)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.exhaust BDD.inject dual_order.trans erase_disj_sf_preserve erase_disjoints_pwf erase_subtypes.simps(1) erase_subtypes_sf_noop erase_subtypes_sub_free erasures_erase le_cases option.distinct(1) pwf_is_norm pwfbdd.cases)
  (* 6/9 *)
  apply (rename_tac tt et t te e n)
  apply (subgoal_tac "\<exists>x. common i c tr tt te = Some x")
  prefer 2
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases erase_subtypes_pwf erasures_erase le_trans less_imp_le_nat pwfbdd.simps)
  apply (subgoal_tac " \<exists>z. common i c tr et te = Some z")
  prefer 2
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases erase_subtypes_pwf erasures_erase le_trans less_imp_le_nat pwfbdd.simps)
  apply auto[1]
  sledgehammer[timeout=180]
  apply (case_tac "te")
  (* 6: 8 *)
  apply auto[2]
  apply (metis BDD.distinct(3) BDD.inject BDD.simps(7) leD pwfbdd.cases)
  apply (metis BDD.distinct(3) BDD.inject BDD.simps(7) leD pwfbdd.cases)
  (* 6: 6 *)
  apply (rename_tac j tet tee)
  apply simp_all
  apply (case_tac "tr j i")
  apply simp_all
  apply (case_tac "i = j")
  apply simp_all
  (* 6: 9 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) common.simps(5) common.simps(8) disj_free.cases less_irrefl_nat not_le_imp_less option.distinct(1))
  apply (case_tac "j < i")
  apply simp_all
  apply auto[1]
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) leD pwfbdd.cases)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) leD pwfbdd.cases)  
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_subtypes_sf_preserve erasures_erase pwfbdd.simps sub_free.simps)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_subtypes_sf_preserve erasures_erase pwfbdd.simps sub_free.simps)
  (* 6: 7 *)
  apply (metis (no_types, lifting) BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases erase_subtypes_df_preserve erasures_erase pwfbdd.simps)
  apply auto[1]
  (* 6: 13 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) leD pwfbdd.cases)
  apply (metis Relatedness.distinct(3) nat_le_linear wftr_symm wftr_weaken)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) leD pwfbdd.cases)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) leD pwfbdd.cases)
  apply (simp add: select'_def split: option.splits)
  apply auto[1]
  (* 6: 10 *)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject Relatedness.distinct(5) erase_disj_df_noop erase_disjoints.simps(1) erase_exchange erasures_erase pwf_is_norm pwfbdd.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject BDD_select.select_def Relatedness.distinct(3) erase_subtypes.simps(1) erase_subtypes_sf_noop erase_subtypes_sf_preserve erasures_erase norm_select option.distinct(1) pwf_is_norm pwfbdd.cases)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) leD pwfbdd.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) leD pwfbdd.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) common.simps(5) disj_free.cases erase_exchange erase_subtypes.simps(2) erase_subtypes.simps(3) erasures_erase not_le_imp_less option.simps(3))
  (* 5 / 9 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) less_or_eq_imp_le pwf_weaken pwfbdd.cases)
  (* 4 / 9 *)
  apply (rename_tac et ee t tt e te n)
  apply (case_tac te)
  apply simp_all
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_subtypes_sub_free erasures_erase leD le_cases option.distinct(1) option.exhaust pwf_weaken pwfbdd.cases select'_some_none_none)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_subtypes_sub_free erasures_erase leD le_cases option.distinct(1) option.exhaust pwf_weaken pwfbdd.cases select'_some_none_none)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject common.simps(5) common_refl dual_order.order_iff_strict dual_order.trans erase_disjoints_pwf erase_subtypes_sub_free erasures_erase leD le_cases option.distinct(1) pwf_weaken pwfbdd.cases pwfbdd.simps select'_some_some_some wftr_weaken)
  (* 3 / 9 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) less_or_eq_imp_le pwf_weaken pwfbdd.cases)
  (* 2 / 9 *)
  apply (rename_tac tt te t et e ee n)
  apply (case_tac ee)
  apply simp_all
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) common.simps(5) common_refl erase_disj_disj_free erase_disjoints_pwf erasures_erase le_refl linear option.exhaust option.simps(3) pwf_weaken pwfbdd.cases select'_some_none_none)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) common.simps(5) common_refl erase_disj_disj_free erase_disjoints_pwf erasures_erase le_refl linear option.exhaust option.simps(3) pwf_weaken pwfbdd.cases select'_some_none_none)
  apply (rename_tac j eet eee)
  apply (case_tac "i = j")
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) sub_free.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject erase_disj_disj_free erase_subtypes_pwf erasures_erase leD le_trans nat_le_linear not_Some_eq pwfbdd.simps select'_some_none_none)
  (* 1 / 9 *)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject order.strict_implies_order pwf_weaken pwfbdd.simps)
  done

theorem common_correct_t0:
  "well_formed_tr c tr \<Longrightarrow> n \<le> c \<Longrightarrow> t \<noteq> e \<Longrightarrow>
   disj_free c tr t \<Longrightarrow> sub_free c tr e \<Longrightarrow>
   pwfbdd c tr t \<Longrightarrow> pwfbdd c tr e \<Longrightarrow>
   pwfbdd (Suc n) tr t \<Longrightarrow> pwfbdd (Suc n) tr e \<Longrightarrow>
   common n c tr t e = Some s \<Longrightarrow>
   (erase_disjoints c tr s = t \<and> erase_subtypes c tr s = e)"
  apply (induction n c tr t e rule: common.induct)
  apply (simp_all del: erase_disjoints.simps erase_subtypes.simps split: option.split)
  apply simp_all
  defer
  (* Case 5 / 5 *)
  apply (case_tac "tr it c")
  apply (auto simp add: select'_def split: option.split)[3]
  sledgehammer
  apply (subgoal_tac "erase_disjoints c tr x2 = et")
  prefer 2
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases less_Suc_eq_le pwf_weaken pwfbdd.simps)
  apply (smt (verit, ccfv_SIG) BDD.distinct(3) BDD.distinct(5) BDD.inject BDD_select.select_def erase_disj_df_noop erase_disj_disj_free erase_disjoints.simps(1) leI less_trans nat_neq_iff pwf_is_norm pwf_weaken pwfbdd.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.simps)
  apply (subgoal_tac "erase_disjoints c tr x2 = tt")
  prefer 2
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases less_Suc_eq_le pwf_weaken pwfbdd.simps)
  apply (subgoal_tac "erase_disjoints c tr x2a = et")
  prefer 2
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases less_Suc_eq_le pwf_weaken pwfbdd.simps)
  apply (smt (verit, ccfv_SIG) BDD.distinct(3) BDD.distinct(5) BDD.inject BDD_select.select_def erase_disj_df_noop erase_disj_disj_free erase_disjoints.simps(1) leI less_trans nat_neq_iff pwf_is_norm pwf_weaken pwfbdd.cases)
  (* Case 4 / 5 *)
  apply (case_tac "tr it c")
  apply (auto simp add: select'_def split: option.split)[3]
  apply (subgoal_tac "erase_disjoints c tr x2 = et")
  prefer 2
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases less_Suc_eq_le pwf_weaken pwfbdd.simps)
  apply (smt (verit, ccfv_SIG) BDD.distinct(3) BDD.distinct(5) BDD.inject BDD_select.select_def erase_disj_df_noop erase_disj_disj_free erase_disjoints.simps(1) leI less_trans nat_neq_iff pwf_is_norm pwf_weaken pwfbdd.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.simps)
  apply (subgoal_tac "erase_disjoints c tr x2 = tt")
  prefer 2
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases less_Suc_eq_le pwf_weaken pwfbdd.simps)
  apply (subgoal_tac "erase_disjoints c tr x2a = et")
  prefer 2
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases less_Suc_eq_le pwf_weaken pwfbdd.simps)
  apply (smt (verit, ccfv_SIG) BDD.distinct(3) BDD.distinct(5) BDD.inject BDD_select.select_def erase_disj_df_noop erase_disj_disj_free erase_disjoints.simps(1) leI less_trans nat_neq_iff pwf_is_norm pwf_weaken pwfbdd.cases)
  (* Case 3 / 5 *)
  apply (case_tac "tr ie c")
  apply (auto simp add: select'_def split: option.split)[3]
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) BDD_select.select_def erase_disjoints.simps(1) less_Suc_eq_le pwf_weaken pwfbdd.cases sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) BDD_select.select_def erase_disjoints.simps(1) less_Suc_eq_le pwf_weaken pwfbdd.cases sub_free.simps)
  (* Case 2 / 5 *)
  apply (case_tac "tr ie c")
  apply (auto simp add: select'_def split: option.split)[3]
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) BDD_select.select_def erase_disjoints.simps(1) less_Suc_eq_le pwf_weaken pwfbdd.cases sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) BDD_select.select_def erase_disjoints.simps(1) less_Suc_eq_le pwf_weaken pwfbdd.cases sub_free.simps)
  (* Case 1 / 5 *)
  apply auto
  (* Case 12/12 *)
  apply (case_tac "common n c tr tt te")
  apply simp_all
  apply (subgoal_tac "erase_disjoints c tr a = tt")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases less_Suc_eq_le pwf_weaken pwfbdd.cases sub_free.cases)
  apply (case_tac "common n c tr et ee")
  apply simp_all
  apply (subgoal_tac "erase_disjoints c tr aa = et")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases less_Suc_eq_le pwf_weaken pwfbdd.cases sub_free.cases)
  apply simp_all
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject BDD_select.select_def disj_free.cases erase_disjoints.simps(1) pwfbdd.cases)
  (* Case 11/12 *)
  apply (case_tac "tr it ie")
  apply simp_all
  apply (case_tac "tr ie c")
  apply simp_all
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) sub_free.simps)
  apply (smt (verit) BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases leI order.asym pwfbdd.cases wftr_refl0 wftr_sub_disj)
  apply (case_tac "common n c tr
              (select it (erase_disjoints ie tr tt)
                (erase_disjoints ie tr et))
              te")
  apply simp_all
  apply (case_tac "common n c tr (erase_subtypes ie tr et) ee")
  apply simp_all
  apply (subgoal_tac "erase_disjoints c tr a =
        select it (erase_disjoints ie tr tt)
         (erase_disjoints ie tr et)")
  prefer 2
  apply (smt (verit) BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.simps erase_disj_df_preserve erase_disj_sf_preserve erase_disjoints_pwf less_SucE less_Suc_eq_le not_le pwf_weaken pwfbdd.simps select_df_preserve select_pwf sub_free.cases)
  apply (subgoal_tac "erase_disjoints c tr aa =
        erase_subtypes ie tr et")
  prefer 2
  apply (smt (verit) BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.simps erase_disj_df_preserve erase_disj_sf_preserve erase_disjoints_pwf less_SucE less_Suc_eq_le not_le pwf_weaken pwfbdd.simps select_df_preserve select_pwf sub_free.cases)
  apply (case_tac "tr it c")
  apply simp_all
  sledgehammer
  apply (smt (verit) BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases leI order.asym pwfbdd.cases wftr_refl0 wftr_sub_disj)
  (* Subcase 3 / 3 *)
  apply (case_tac "ie < it")
  apply (simp add: select'_def split: option.split)
  apply auto
  apply (case_tac "common n c tr et (Select ie te ee)")
  apply simp_all
  apply (case_tac "erase_disjoints c tr a = et")
  prefer 2
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases less_Suc_eq_le pwf_weaken pwfbdd.simps)
  apply (case_tac "common n c tr (Select it tt et) ee")
  apply simp_all
  apply (case_tac "common n c tr tt te")
  apply simp_all
  apply (case_tac "tr ie c")
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) sub_free.simps)
  apply simp_all
  apply (smt (verit) BDD.distinct(3) BDD.distinct(5) BDD.inject BDD_select.select_def disj_free.simps erase_disj_df_noop erase_disjoints.elims le_eq_less_or_eq less_Suc_eq_le less_le_not_le pwf_is_norm pwf_weaken pwfbdd.simps)
  apply (case_tac "tr it ie")
  apply (simp add: select'_def split: option.split)
  apply (case_tac "common n c tr
         (select it (erase_disjoints ie tr tt)
           (erase_disjoints ie tr et))
         te")
  apply (simp add: select_def)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases erase_disj_df_noop less_le pwf_is_norm pwf_weaken pwfbdd.cases)
  apply simp_all
  apply (case_tac "common n c tr (erase_subtypes ie tr et) ee")
  apply (simp add: select_def)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases erase_disj_df_noop leD le_cases pwf_is_norm pwf_weaken pwfbdd.simps)
  apply (simp add: select_def)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases erase_disj_df_noop leD le_cases pwf_is_norm pwf_weaken pwfbdd.simps)
  apply (case_tac "select' ie
         (common n c tr (erase_disjoints ie tr et) te)
         (common n c tr
           (select it (erase_subtypes ie tr tt)
             (erase_subtypes ie tr et))
           ee)")
  apply (simp add: select_def)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases erase_disj_df_noop leD le_cases pwf_is_norm pwf_weaken pwfbdd.simps)
  apply (simp add: select_def)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases erase_disj_df_noop leD le_cases pwf_is_norm pwf_weaken pwfbdd.simps)
  apply (case_tac "select' ie
         (common n c tr
           (select it (erase_disjoints ie tr tt)
             (erase_disjoints ie tr et))
           te)
         (common n c tr
           (select it (erase_subtypes ie tr tt)
             (erase_subtypes ie tr et))
           ee)")
  apply (simp add: select_def)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases erase_disj_df_noop leD le_cases pwf_is_norm pwf_weaken pwfbdd.simps)
  apply (simp add: select_def)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases erase_disj_df_noop leD le_cases pwf_is_norm pwf_weaken pwfbdd.simps)
  apply (case_tac "common n c tr et ee")
  apply simp_all
  apply (case_tac "tr ie c")
  apply simp_all
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject sub_free.cases)
  apply (simp add: select_def)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases erase_disj_df_noop leD le_cases pwf_is_norm pwf_weaken pwfbdd.simps)
  apply (case_tac "tr it ie")
  apply simp_all
  apply (case_tac "select' ie
         (common n c tr
           (select it (erase_disjoints ie tr tt)
             (erase_disjoints ie tr et))
           te)
         (common n c tr (erase_subtypes ie tr et) ee)")
  apply simp_all
  apply (simp add: select_def)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases erase_disj_df_noop leD le_cases pwf_is_norm pwf_weaken pwfbdd.simps)
  apply (simp add: select_def)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases erase_disj_df_noop leD le_cases pwf_is_norm pwf_weaken pwfbdd.simps)
  apply (case_tac "select' ie
         (common n c tr (erase_disjoints ie tr et) te)
         (common n c tr
           (select it (erase_subtypes ie tr tt)
             (erase_subtypes ie tr et))
           ee)")
  apply simp_all
  apply (simp add: select_def)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases erase_disj_df_noop leD le_cases pwf_is_norm pwf_weaken pwfbdd.simps)
  apply (simp add: select_def)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases erase_disj_df_noop leD le_cases pwf_is_norm pwf_weaken pwfbdd.simps)
  apply (case_tac "select' ie
         (common n c tr
           (select it (erase_disjoints ie tr tt)
             (erase_disjoints ie tr et))
           te)
         (common n c tr
           (select it (erase_subtypes ie tr tt)
             (erase_subtypes ie tr et))
           ee)")
  apply simp_all
  apply (simp add: select_def)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases erase_disj_df_noop leD le_cases pwf_is_norm pwf_weaken pwfbdd.simps)
  apply (simp add: select_def)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases erase_disj_df_noop leD le_cases pwf_is_norm pwf_weaken pwfbdd.simps)

(* IMPOSSIBLE *)
  sledgehammer
  oops


(* FIXME: \<not>(\<exists>b. wfbdd i tr b \<and> erase_disjoints i tr b = t \<and> erase_subtypes i tr b = e) \<Longrightarrow>
*)
inductive wfbdd :: "nat \<Rightarrow> TR \<Rightarrow> BDD \<Rightarrow> bool" where
  wfbdd_sel: "n > i \<Longrightarrow> sub_free i tr e \<Longrightarrow> disj_free i tr t \<Longrightarrow> 
              wfbdd i tr t \<Longrightarrow> wfbdd i tr e \<Longrightarrow> 
              wfbdd n tr (Select i t e)" |
  wfbdd_top: "wfbdd n tr Top" | wfbdd_nothing: "wfbdd n tr Nothing"



end