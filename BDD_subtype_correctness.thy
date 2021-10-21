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

lemma common_nothing [simp]:
  "well_formed_tr c tr \<Longrightarrow> n \<le> c \<Longrightarrow> sub_free c tr e \<Longrightarrow> pwfbdd n tr e \<Longrightarrow> (case common n c tr Nothing e of Some s \<Rightarrow> erase_disjoints c tr s = Nothing | None \<Rightarrow> True)"
  apply (induction e arbitrary: n)
  apply auto
  (* e \<Longrightarrow> Select i t e *)
  apply (rename_tac "i" "t" "e" "n")
  apply (case_tac n)
  apply auto
  apply (rename_tac "n")
  apply (subgoal_tac "sub_free c tr t")
  prefer 2
  apply (metis BDD.distinct(5) BDD.inject BDD.simps(5) sub_free.cases)
  apply (subgoal_tac "sub_free c tr e")
  prefer 2
  apply (metis BDD.distinct(5) BDD.inject BDD.simps(5) sub_free.cases)
  apply (subgoal_tac "pwfbdd n tr t")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) less_Suc_eq_le pwf_weaken pwfbdd.simps)
  apply (subgoal_tac "pwfbdd n tr e")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) less_Suc_eq_le pwf_weaken pwfbdd.simps)
  apply (simp split: Relatedness.splits option.splits)
  apply (auto simp add: select'_def)
  (* 6 cases *)
  (* 1/6 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) sub_free.simps)
  (* 2/6 *)
  apply (metis (no_types, lifting) option.case_eq_if option.distinct(1))
  (* 3/6 *)
  apply (case_tac "common n c tr Nothing t")
  apply auto
  apply (case_tac "common n c tr Nothing e")
  (* 3: 1/4 *)
  apply auto
  (* 3: 2/4 *)
  apply (smt (verit) BDD.inject BDD.simps(5) BDD.simps(7) BDD_select.select_def Suc_leD dual_order.trans erase_disjoints.simps(1) less_Suc_eq_le option.simps(5) pwfbdd.simps wftr_refl0)
  (* 3: 3/4 *)
  apply (metis option.case_eq_if option.distinct(1))
  (* 3: 4/4 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) sub_free.simps)
  (* 4/5 *)
  apply (smt (verit, ccfv_threshold) BDD.inject BDD.simps(5) BDD.simps(7) BDD_select.select_def Suc_leD dual_order.trans erase_disjoints.simps(1) option.case_eq_if option.distinct(1) option.sel order.strict_implies_order pwfbdd.simps wftr_refl0)
  (* 5/5 *)
  apply (smt (verit, ccfv_threshold) BDD.inject BDD.simps(5) BDD.simps(7) BDD_select.select_def Suc_leD dual_order.trans erase_disjoints.simps(1) option.case_eq_if option.distinct(1) option.sel order.strict_implies_order pwfbdd.simps wftr_refl0)
  done

lemma common_t_nothing [simp]:
  "well_formed_tr c tr \<Longrightarrow> n \<le> c \<Longrightarrow> sub_free c tr t \<Longrightarrow> pwfbdd n tr t \<Longrightarrow> common n c tr t Nothing = Some s \<Longrightarrow> erase_disjoints c tr s = Nothing"
  apply (induction t arbitrary: n s)
  apply auto
  (* t \<Longrightarrow> Select i t e *)
  apply (rename_tac "i" "t" "e" "n" "s")
  apply (case_tac n)
  apply auto
  apply (rename_tac "n")
  apply (subgoal_tac "sub_free c tr t")
  prefer 2
  apply (metis BDD.distinct(5) BDD.inject BDD.simps(5) sub_free.cases)
  apply (subgoal_tac "sub_free c tr e")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) sub_free.simps)
  apply (subgoal_tac "pwfbdd n tr t")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) less_Suc_eq_le pwf_weaken pwfbdd.simps)
  apply (subgoal_tac "pwfbdd n tr e")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) less_Suc_eq_le pwf_weaken pwfbdd.simps)
  apply (simp split: Relatedness.splits option.splits)
  apply (auto simp add: select'_def)
  (* 3 cases *)
  (* 3/3 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) sub_free.simps)
  (* 2/3 *)
  apply (case_tac "common n c tr t Nothing")
  apply auto
  apply (rename_tac "tt")
  apply (case_tac "common n c tr e Nothing")
  apply auto
  apply (rename_tac "ee")
  apply (metis BDD_select.select_def Suc_leD erase_disjoints.simps(1))
  (* 1/3 *)
  apply (case_tac "common n c tr t Nothing")
  apply auto
  apply (rename_tac "tt")
  apply (case_tac "common n c tr e Nothing")
  apply auto
  apply (rename_tac "ee")
  apply (smt (z3) BDD_select.select_def Suc_leD erase_disjoints.simps(1))
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

lemma common_idem:
  "well_formed_tr c tr \<Longrightarrow> n \<le> c \<Longrightarrow>
   pwfbdd c tr a \<Longrightarrow> pwfbdd n tr a \<Longrightarrow>
   common n c tr a a = Some a"
  apply (induction a arbitrary: n c)
  apply auto
  apply (case_tac n)
  apply auto
  apply (metis BDD.distinct(5) BDD.simps(5) less_zeroE pwfbdd.simps)
  by (metis BDD.distinct(3) BDD.inject BDD.simps(7) Suc_leD less_Suc_eq_le pwf_is_norm pwf_weaken pwfbdd.cases select'_some_some_some select_noop)

theorem select_is_top: "select i t e = Top \<Longrightarrow> t = Top \<and> e = Top"
  by (metis BDD.distinct(5) BDD_select.select_def)

nitpick_params [timeout=30]

sledgehammer_params [timeout=30]

lemma disj_free_subty:
  "well_formed_tr c tr \<Longrightarrow> pwfbdd c tr t \<Longrightarrow> i < c \<Longrightarrow>
   disj_free i tr t \<Longrightarrow> tr i c = Subtype \<Longrightarrow> disj_free c tr t"
  apply (induction t arbitrary: c)
  apply auto
  by (smt (verit, best) BDD.distinct(3) BDD.inject BDD.simps(7) disj_free.cases disj_free_sel less_or_eq_imp_le pwf_weaken pwfbdd.cases wftr_sub_disj)

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

theorem common_correct_a:
  "erasures c tr s t e \<Longrightarrow>
   well_formed_tr c tr \<Longrightarrow> n \<le> c \<Longrightarrow>
   disj_free c tr t \<Longrightarrow> sub_free c tr e \<Longrightarrow>
   pwfbdd c tr t \<Longrightarrow> pwfbdd c tr e \<Longrightarrow> pwfbdd c tr s \<Longrightarrow>
   pwfbdd n tr t \<Longrightarrow> pwfbdd n tr e \<Longrightarrow> pwfbdd n tr s \<Longrightarrow>
   common n c tr t e \<noteq> None"
  apply (induction s t e arbitrary: n rule: erasures.induct)
  apply simp_all
  (* 8/8 *)
  apply (case_tac n)
  apply auto
  apply (metis common.simps(8) common_idem le0 option.distinct(1))
  apply (rename_tac n)
  apply (case_tac "\<exists>y. common n c tr td ts = Some y")
  prefer 2  
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject Suc_leD erase_disj_disj_free erase_subtypes_sub_free erasures_erase less_Suc_eq_le pwf_weaken pwfbdd.cases)
  apply (case_tac "\<exists>y. common n c tr ed es = Some y")
  prefer 2  
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject Suc_leD erase_disj_disj_free erase_subtypes_sub_free erasures_erase less_Suc_eq_le pwf_weaken pwfbdd.cases)
  apply auto[1]
  (* 7/8 *)
  apply (case_tac n)
  apply auto
  apply (metis common.simps(8) common_idem le0 option.distinct(1))
  apply (rename_tac n)
  apply (case_tac "\<exists>y. common n c tr d ts = Some y")
  prefer 2
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject Suc_leD erase_disjoints_pwf erase_subtypes_sub_free erasures_erase leD not_None_eq not_less_eq_eq pwf_weaken pwfbdd.cases)
  apply (case_tac "\<exists>y. common n c tr d es = Some y")
  prefer 2  
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject Suc_leD erase_disjoints_pwf erase_subtypes_sub_free erasures_erase leD not_None_eq not_less_eq_eq pwf_weaken pwfbdd.cases)
  apply auto[1]
  apply (rename_tac ty ey)
  apply (case_tac d)
  apply auto[2]
  apply (rename_tac j tt ee)
  apply simp
  apply (subgoal_tac "j \<le> i")
  prefer 2
  apply (metis BDD.distinct(5) BDD.inject BDD.simps(5) erase_disjoints_pwf erasures_erase le_eq_less_or_eq pwfbdd.simps)
  apply (subgoal_tac "tr i i = Subtype")
  prefer 2
  apply (metis BDD.distinct(3) BDD.inject BDD.simps(7) dual_order.strict_iff_order pwfbdd.cases wftr_symm wftr_weaken)
  apply simp
  apply auto[1]
  sledgehammer
  (* 6/8 *)
  (* 5/8 *)
  oops

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