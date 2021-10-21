theory BDD_subtype_defs
  imports Main BDD_basic BDD_select
begin

datatype Relatedness = Subtype | Disjoint | MayIntersect

type_synonym TR = "nat \<Rightarrow> nat \<Rightarrow> Relatedness"

fun well_formed_tr3 :: "TR \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "well_formed_tr3 tr i j 0 =
    ((tr j i = Subtype \<longrightarrow> tr 0 j = Subtype \<longrightarrow> tr 0 i = Subtype) \<and>
     (tr j i = Subtype \<longrightarrow> tr 0 j = MayIntersect \<longrightarrow> tr 0 i \<noteq> Disjoint) \<and>
     (tr j i = Disjoint \<longrightarrow> tr 0 j = Subtype \<longrightarrow> tr 0 i = Disjoint) \<and>
     (tr j i = Disjoint \<longrightarrow> tr 0 j = MayIntersect \<longrightarrow> tr 0 i \<noteq> Subtype))" |
  "well_formed_tr3 tr i j k =
    ((tr j i = Subtype \<longrightarrow> tr k j = Subtype \<longrightarrow> tr k i = Subtype) \<and>
     (tr j i = Subtype \<longrightarrow> tr k j = MayIntersect \<longrightarrow> tr k i \<noteq> Disjoint) \<and>
     (tr j i = Disjoint \<longrightarrow> tr k j = Subtype \<longrightarrow> tr k i = Disjoint) \<and>
     (tr j i = Disjoint \<longrightarrow> tr k j = MayIntersect \<longrightarrow> tr k i \<noteq> Subtype) \<and>
     well_formed_tr3 tr i j (k-1))"

fun well_formed_tr2 :: "TR \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "well_formed_tr2 tr i 0 = ((tr i 0 = tr 0 i) \<and> well_formed_tr3 tr i 0 0)" |
  "well_formed_tr2 tr i j = ((tr i j = tr j i) \<and> well_formed_tr3 tr i j j \<and> well_formed_tr2 tr i (j-1))"

fun well_formed_tr :: "nat \<Rightarrow> TR \<Rightarrow> bool" where
  "well_formed_tr 0 tr = (tr 0 0 = Subtype)" |
  "well_formed_tr i tr = (tr i i = Subtype \<and> well_formed_tr2 tr i i \<and> well_formed_tr (i-1) tr)"

fun test_tr :: TR where
  "test_tr a b = (
     if a = b then Subtype
     else
       let aa = max a b in
       let bb = min a b in
       if bb = 0 then MayIntersect
       else let g = gcd aa bb in
            if g = 1 then Disjoint
            else if g = bb then Subtype
            else MayIntersect)"

lemma wftr_weaken: "well_formed_tr n tr \<Longrightarrow> m \<le> n \<Longrightarrow> well_formed_tr m tr"
  apply (induction n arbitrary: m)
  apply clarsimp
  apply (case_tac "m = Suc n")
  by auto

lemma wftr2_weaken: "well_formed_tr2 tr i j \<Longrightarrow> jj \<le> j \<Longrightarrow> well_formed_tr2 tr i jj"
  apply (induction j arbitrary: i jj)
  apply clarsimp
  apply (case_tac "jj = Suc j")
  by auto

lemma wftr3_weaken: "well_formed_tr3 tr i j k \<Longrightarrow> kk \<le> k \<Longrightarrow> well_formed_tr3 tr i j kk"
  apply (induction k arbitrary: i j kk)
  apply clarsimp
  apply (case_tac "kk = Suc k")
  by auto

lemma wftr_wftr2: "well_formed_tr i tr \<Longrightarrow> j \<le> i \<Longrightarrow> well_formed_tr2 tr i j"
  apply (case_tac i)
  apply clarsimp
  by (meson Suc_le_eq well_formed_tr.simps(2) wftr2_weaken wftr_weaken)

lemma wftr2_wftr3: "well_formed_tr2 tr i j \<Longrightarrow> j \<le> i \<Longrightarrow> k \<le> j \<Longrightarrow> well_formed_tr3 tr i j k"
  apply (case_tac j)
  apply clarsimp
  by (meson well_formed_tr2.simps(2) wftr3_weaken)

lemma wftr_wftr3: "well_formed_tr i tr \<Longrightarrow> j \<le> i \<Longrightarrow> k \<le> j \<Longrightarrow> well_formed_tr3 tr i j k"
  by (meson wftr2_wftr3 wftr_wftr2)

lemma wftr_symm: "well_formed_tr n tr \<Longrightarrow> tr n n = Subtype"
  apply (induction n)
  by auto

lemma wftr_refl0: "well_formed_tr a tr \<Longrightarrow> b \<le> a \<Longrightarrow> tr a b = tr b a"
  apply (induction a)
  apply clarsimp
  apply clarsimp
  by (metis (no_types, lifting) le_0_eq le_SucE well_formed_tr2.simps(1) well_formed_tr2.simps(2) wftr2_weaken zero_induct)

lemma wftr3_trans: "well_formed_tr3 tr i j k \<Longrightarrow> j \<le> i \<Longrightarrow> k \<le> j \<Longrightarrow> tr j i = Subtype \<Longrightarrow> tr k j = Subtype \<Longrightarrow> tr k i = Subtype"
  apply (induction k)
  by auto

lemma wftr_trans: "well_formed_tr (Suc i) tr \<Longrightarrow> j \<le> i \<Longrightarrow> k \<le> j \<Longrightarrow> tr j i = Subtype \<Longrightarrow> tr k j = Subtype \<Longrightarrow> tr k i = Subtype"
  by (metis diff_Suc_1 well_formed_tr.simps(2) wftr3_trans wftr_wftr3)

lemma wftr3_sub_disj:
    "well_formed_tr3 tr i j k \<Longrightarrow> j \<le> i \<Longrightarrow> k \<le> i \<Longrightarrow>
     tr j i = Subtype \<Longrightarrow> tr k i = Disjoint \<Longrightarrow> tr k j = Disjoint"
  apply (induction k)
  using Relatedness.exhaust by auto

lemma wftr_sub_disj: "well_formed_tr n tr \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> i \<Longrightarrow> k \<le> n \<Longrightarrow> tr j i = Subtype \<Longrightarrow> tr k i = Disjoint \<Longrightarrow> tr k j = Disjoint"
  apply (case_tac "k \<le> i")
  apply (smt (verit, ccfv_SIG) Relatedness.exhaust bot_nat_0.extremum_uniqueI le_SucE linear well_formed_tr3.simps(1) well_formed_tr3.simps(2) wftr_refl0 wftr_weaken wftr_wftr3 zero_induct)
  by (smt (verit, best) linear well_formed_tr.elims(1) well_formed_tr3.simps(1) well_formed_tr3.simps(2) wftr_refl0 wftr_weaken wftr_wftr3)

inductive sub_free :: "nat \<Rightarrow> TR \<Rightarrow> BDD \<Rightarrow> bool" where
  sub_free_sel: "tr i n \<noteq> Subtype \<Longrightarrow> sub_free n tr t \<Longrightarrow> sub_free n tr e \<Longrightarrow> sub_free n tr (Select i t e)" |
  sub_free_top: "sub_free n tr Top" | sub_free_nothing: "sub_free n tr Nothing"

declare sub_free.intros[simp, intro]

inductive disj_free :: "nat \<Rightarrow> TR \<Rightarrow> BDD \<Rightarrow> bool" where
  disj_free_sel: "tr i n \<noteq> Disjoint \<Longrightarrow> disj_free n tr t \<Longrightarrow> disj_free n tr e \<Longrightarrow> disj_free n tr (Select i t e)" |
  disj_free_top: "disj_free n tr Top" | disj_free_nothing: "disj_free n tr Nothing"

declare disj_free.intros[simp, intro]

lemma select_sf_preserve[simp]: "sub_free n tr t \<Longrightarrow> sub_free n tr e \<Longrightarrow> tr i n \<noteq> Subtype \<Longrightarrow> sub_free n tr (select i t e)"
  using select_def by simp

lemma select_df_preserve[simp]: "disj_free n tr t \<Longrightarrow> disj_free n tr e \<Longrightarrow> tr i n \<noteq> Disjoint \<Longrightarrow> disj_free n tr (select i t e)"
  using select_def by simp

fun erase_subtypes :: "nat \<Rightarrow> TR \<Rightarrow> BDD \<Rightarrow> BDD" where
  "erase_subtypes n tr (Select i t e) =
     (if tr i n = Subtype then
        erase_subtypes n tr e
      else
        select i (erase_subtypes n tr t) (erase_subtypes n tr e))" |
  "erase_subtypes n tr leaf = leaf"

fun erase_disjoints :: "nat \<Rightarrow> TR \<Rightarrow> BDD \<Rightarrow> BDD" where
  "erase_disjoints n tr (Select i t e) =
     (if tr i n = Disjoint then
        erase_disjoints n tr e
      else
        select i (erase_disjoints n tr t) (erase_disjoints n tr e))" |
  "erase_disjoints n tr leaf = leaf"

lemma erase_subtypes_sub_free: "sub_free n tr (erase_subtypes n tr a)"
  apply (induction a)
  by (simp_all add: select_def)

lemma erase_subtypes_sf_preserve: "sub_free n tr a \<Longrightarrow> sub_free n tr (erase_subtypes m tr a)"
  apply (induction a)
  apply (auto simp add: select_def)
  using sub_free.cases apply auto[1]
  using sub_free.cases apply auto[1]
  apply (rule sub_free_sel)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) sub_free.cases)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) sub_free.cases)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) sub_free.cases)
  done

lemma erase_subtypes_sf_noop: "norm n a \<Longrightarrow> sub_free n tr a \<Longrightarrow> erase_subtypes n tr a = a"
  apply (induction a)
  apply (auto simp add: select_def)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) norm.cases norm_widen sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) norm.cases norm_widen sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) norm.cases norm_widen sub_free.simps)
  done

lemma erase_subtypes_df_preserve: "disj_free n tr a \<Longrightarrow> disj_free n tr (erase_subtypes m tr a)"
  apply (induction a)
  apply (auto simp add: select_def)
  using disj_free.cases apply auto[1]
  using disj_free.cases apply auto[1]
  apply (rule disj_free_sel)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases)
  done

lemma erase_disj_disj_free: "disj_free n tr (erase_disjoints n tr a)"
  apply (induction a)
  by (simp_all add: select_def)

lemma erase_disj_sf_preserve: "sub_free n tr a \<Longrightarrow> sub_free n tr (erase_disjoints m tr a)"
  apply (induction a)
  apply (auto simp add: select_def)
  using sub_free.cases apply auto[1]
  using sub_free.cases apply auto[1]
  apply (rule sub_free_sel)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) sub_free.cases)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) sub_free.cases)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) sub_free.cases)
  done

lemma erase_disj_df_preserve: "disj_free n tr a \<Longrightarrow> disj_free n tr (erase_disjoints m tr a)"
  apply (induction a)
  apply (auto simp add: select_def)
  using disj_free.cases apply auto[1]
  using disj_free.cases apply auto[1]
  apply (rule disj_free_sel)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases)
  done

lemma erase_disj_df_noop: "norm n a \<Longrightarrow> disj_free n tr a \<Longrightarrow> erase_disjoints n tr a = a"
  apply (induction a)
  apply (auto simp add: select_def)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps norm.cases norm_widen)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps norm.cases norm_widen)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps norm.cases norm_widen)
  done

definition select' :: "nat \<Rightarrow> BDD option \<Rightarrow> BDD option \<Rightarrow> BDD option" where
  "select' i t e = (case (t, e) of (Some t, Some e) \<Rightarrow> Some (select i t e) | _ \<Rightarrow> None)"

inductive sub_free_opt:: "nat \<Rightarrow> TR \<Rightarrow> BDD option \<Rightarrow> bool" where
  sub_free_none[simp, intro]: "sub_free_opt n tr None" |
  sub_free_some[simp, intro]: "sub_free n tr s \<Longrightarrow> sub_free_opt n tr (Some s)"

lemma select'_sf_preserve: "sub_free_opt n tr t \<Longrightarrow> sub_free_opt n tr e \<Longrightarrow> tr i n \<noteq> Subtype \<Longrightarrow> sub_free_opt n tr (select' i t e)"
  apply (auto simp add: select'_def split: option.splits)
  by (metis option.discI option.inject select_sf_preserve sub_free_opt.simps)

inductive disj_free_opt:: "nat \<Rightarrow> TR \<Rightarrow> BDD option \<Rightarrow> bool" where
  disj_free_none[simp, intro]: "disj_free_opt n tr None" |
  disj_free_some[simp, intro]: "disj_free n tr s \<Longrightarrow> disj_free_opt n tr (Some s)"

lemma select'_df_preserve: "disj_free_opt n tr t \<Longrightarrow> disj_free_opt n tr e \<Longrightarrow> tr i n \<noteq> Disjoint \<Longrightarrow> disj_free_opt n tr (select' i t e)"
  apply (auto simp add: select'_def split: option.splits)
  by (metis option.discI option.inject select_df_preserve disj_free_opt.simps)


fun common:: "nat \<Rightarrow> nat \<Rightarrow> TR \<Rightarrow> BDD \<Rightarrow> BDD \<Rightarrow> BDD option" where
  "common _ c tr Top Nothing = None" |
  "common _ c tr Nothing Top = None" |
  "common _ c tr Top Top = Some Top" |
  "common _ c tr Nothing Nothing = Some Nothing" |
  "common 0 c tr _ _ = None" |
  "common (Suc n) c tr (Select it tt et) (Select ie te ee) =
     (if it > ie then
        (case tr it c of
           Subtype \<Rightarrow> select' it (Some tt) (common n c tr et (Select ie te ee)) |
           _ \<Rightarrow> select' it (common n c tr tt (erase_disjoints it tr (Select ie te ee)))
                           (common n c tr et (erase_subtypes it tr (Select ie te ee))))
      else if it = ie then
        select' it (common n c tr tt te) (common n c tr et ee)
      else
        (case tr ie c of
           Disjoint \<Rightarrow> select' ie (Some te) (common n c tr (Select it tt et) ee) |
           _ \<Rightarrow> select' ie (common n c tr (erase_disjoints ie tr (Select it tt et)) te)
                           (common n c tr (erase_subtypes ie tr (Select it tt et)) ee)))" |
  "common (Suc n) c tr (Select it tt et) e =
     (case tr it c of
        Subtype \<Rightarrow> select' it (Some tt) (common n c tr et e) |
        _ \<Rightarrow> select' it (common n c tr tt (erase_disjoints it tr e))
                        (common n c tr et (erase_subtypes it tr e)))" |
  "common (Suc n) c tr t (Select ie te ee) =
     (case tr ie c of
        Disjoint \<Rightarrow> select' ie (Some te) (common n c tr t ee) |
        _ \<Rightarrow> select' ie (common n c tr (erase_disjoints ie tr t) te)
                        (common n c tr (erase_subtypes ie tr t) ee))"

inductive pwfbdd :: "nat \<Rightarrow> TR \<Rightarrow> BDD \<Rightarrow> bool" where
  pwfbdd_sel[simp]: "n > i \<Longrightarrow> t \<noteq> e \<Longrightarrow>
               sub_free i tr e \<Longrightarrow> disj_free i tr t \<Longrightarrow>
               pwfbdd i tr t \<Longrightarrow> pwfbdd i tr e \<Longrightarrow>
               pwfbdd n tr (Select i t e)" |
  pwfbdd_top[simp]: "pwfbdd n tr Top" | pwfbdd_nothing[simp]: "pwfbdd n tr Nothing"

lemma pwf_is_norm: "pwfbdd n tr b \<Longrightarrow> norm n b"
  by (induction n tr b rule: pwfbdd.induct) auto

lemma pwf_weaken: "pwfbdd n tr b \<Longrightarrow> m \<ge> n \<Longrightarrow> pwfbdd m tr b"
  by (induction n tr b arbitrary: m rule: pwfbdd.induct) auto

theorem erase_subtypes_pwf[simp]: "pwfbdd n tr b \<Longrightarrow> i \<ge> n \<Longrightarrow> pwfbdd n tr (erase_subtypes i tr b)"
  apply (induction n tr b rule: pwfbdd.induct)
  apply (auto simp add: select_def)
  apply (meson less_le_not_le pwf_weaken)
  apply (meson less_le_not_le pwf_weaken)
  apply (rule pwfbdd_sel)
  apply simp_all
  using erase_subtypes_sf_preserve apply blast
  by (meson erase_subtypes_df_preserve)

theorem erase_disjoints_pwf[simp]: "pwfbdd n tr b \<Longrightarrow> i \<ge> n \<Longrightarrow> pwfbdd n tr (erase_disjoints i tr b)"
  apply (induction n tr b rule: pwfbdd.induct)
  apply (auto simp add: select_def)
  apply (meson less_le_not_le pwf_weaken)
  apply (meson less_le_not_le pwf_weaken)
  apply (rule pwfbdd_sel)
  apply simp_all
  using erase_disj_sf_preserve apply blast
  by (meson erase_disj_df_preserve)

lemma select_pwf[simp]: "pwfbdd i tr t \<Longrightarrow> pwfbdd i tr e \<Longrightarrow> i < n \<Longrightarrow> sub_free i tr e \<Longrightarrow> disj_free i tr t \<Longrightarrow> pwfbdd n tr (select i t e)"
  apply (simp add: select_def)
  apply auto
  by (meson le_eq_less_or_eq pwf_weaken)

inductive pwf_opt :: "nat \<Rightarrow> TR \<Rightarrow> BDD option \<Rightarrow> bool" where
  pwf_opt_none[simp, intro]: "pwf_opt n tr None" |
  pwf_opt_some[simp, intro]: "pwfbdd n tr s \<Longrightarrow> pwf_opt n tr (Some s)"

lemma select'_pwf[simp]: "pwf_opt i tr t \<Longrightarrow> pwf_opt i tr e \<Longrightarrow> i < n \<Longrightarrow> sub_free_opt i tr e \<Longrightarrow> disj_free_opt i tr t \<Longrightarrow> pwf_opt n tr (select' i t e)"
  apply (auto simp add: select'_def split: option.split)
  apply (rule pwf_opt_some)
  apply (rule select_pwf)
  apply (simp_all add: pwf_opt.simps sub_free_opt.simps disj_free_opt.simps)
  done

lemma select'_none_u[simp]: "select' i None e = None"
  by (auto simp add: select'_def)

lemma select'_u_none[simp]: "select' i t None = None"
  by (metis option.case_eq_if prod.simps(2) select'_def)

lemma select'_some_some_some[simp]: "select' i (Some t) (Some e) = Some (select i t e)"  
  by (auto simp add: select'_def)

lemma select'_some_none_none: "select' i (Some t) e = None \<Longrightarrow> e = None"
  apply (case_tac "e")
  apply (auto simp add: select'_def)
  done

lemma select'_none_some_none: "select' i t (Some e) = None \<Longrightarrow> t = None"
  apply (case_tac "t")
  apply (auto simp add: select'_def)
  done

lemma select'_some: "select' i t e = Some r \<Longrightarrow> \<exists>tt ee. t = Some tt \<and> e = Some ee \<and> r = select i tt ee"
  by (metis (no_types, lifting) is_none_code(1) is_none_code(2) option.inject option.split_sel prod.simps(2) select'_def select'_some_some_some)

inductive erasures :: "nat \<Rightarrow> TR \<Rightarrow> BDD \<Rightarrow> BDD \<Rightarrow> BDD \<Rightarrow> bool" for c tr where
  erase_nothing[simp, intro]: "erasures c tr Nothing Nothing Nothing" |
  erase_top[simp, intro]: "erasures c tr Top Top Top" |
  erase_sel_mi_nn[simp]: "tr i c = MayIntersect \<Longrightarrow> td \<noteq> ed \<Longrightarrow> ts \<noteq> es \<Longrightarrow>
      erasures c tr t td ts \<Longrightarrow> erasures c tr e ed es \<Longrightarrow>
      erasures c tr (Select i t e) (Select i td ed) (Select i ts es)" |
  erase_sel_mi_en[simp]: "tr i c = MayIntersect \<Longrightarrow> ts \<noteq> es \<Longrightarrow>
      erasures c tr t d ts \<Longrightarrow> erasures c tr e d es \<Longrightarrow>
      erasures c tr (Select i t e) d (Select i ts es)" |
  erase_sel_mi_ne[simp]: "tr i c = MayIntersect \<Longrightarrow> td \<noteq> ed \<Longrightarrow>
      erasures c tr t td s \<Longrightarrow> erasures c tr e ed s \<Longrightarrow>
      erasures c tr (Select i t e) (Select i td ed) s" |
  erase_sel_mi_ee[simp]: "tr i c = MayIntersect \<Longrightarrow>
      erasures c tr t d s \<Longrightarrow> erasures c tr e d s \<Longrightarrow>
      erasures c tr (Select i t e) d s" |
  erase_sel_disj_n[simp]: "tr i c = Disjoint \<Longrightarrow> ts \<noteq> es \<Longrightarrow>
      erasures c tr t td ts \<Longrightarrow> erasures c tr e ed es \<Longrightarrow>
      erasures c tr (Select i t e) ed (Select i ts es)" |
  erase_sel_disj_e[simp]: "tr i c = Disjoint \<Longrightarrow>
      erasures c tr t td s \<Longrightarrow> erasures c tr e ed s \<Longrightarrow>
      erasures c tr (Select i t e) ed s" |
  erase_sel_sub_n[simp]: "tr i c = Subtype \<Longrightarrow> td \<noteq> ed \<Longrightarrow>
      erasures c tr t td ts \<Longrightarrow> erasures c tr e ed es \<Longrightarrow>
      erasures c tr (Select i t e) (Select i td ed) es" |
  erase_sel_sub_e[simp]: "tr i c = Subtype \<Longrightarrow>
      erasures c tr t d ts \<Longrightarrow> erasures c tr e d es \<Longrightarrow>
      erasures c tr (Select i t e) d es"

lemma erasures_erase:
  "erasures c tr t d s \<Longrightarrow> (d = erase_disjoints c tr t \<and> s = erase_subtypes c tr t)"
  apply (induction rule: erasures.induct)
  by (auto simp add: select_def)

lemma erase_erasures:
  "d = erase_disjoints c tr t \<Longrightarrow> s = erase_subtypes c tr t \<Longrightarrow> erasures c tr t d s"
  apply (induction t arbitrary: s d)
  apply (auto simp add: select_def)
  apply (meson Relatedness.exhaust erase_sel_mi_ee erase_sel_sub_e)
  apply (meson Relatedness.exhaust erase_sel_mi_en)
  apply (meson Relatedness.exhaust erase_sel_mi_ne erase_sel_sub_n)
  by (meson Relatedness.exhaust erase_sel_mi_nn)

end