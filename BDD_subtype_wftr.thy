theory BDD_subtype_wftr
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
     (case (it > ie, it = ie) of
        (True, _) \<Rightarrow>
          (case tr it c of
             Subtype \<Rightarrow> select' it (Some tt) (common n c tr et (Select ie te ee)) |
             _ \<Rightarrow> select' it (common n c tr tt (erase_disjoints it tr (Select ie te ee)))
                             (common n c tr et (erase_subtypes it tr (Select ie te ee)))) |
        (False, True) \<Rightarrow> select' it (common n c tr tt te) (common n c tr et ee) |
        (False, False) \<Rightarrow>
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

lemma common_sf_preserve: "sub_free n tr t \<Longrightarrow> sub_free n tr e \<Longrightarrow> sub_free_opt n tr (common m i tr t e)"
  apply (induction m i tr t e rule: common.induct)
  apply (simp_all split: Relatedness.split)
  defer
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.cases sub_free_some)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.cases sub_free_some)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.cases sub_free_some)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.cases sub_free_some)
  apply auto
  apply (simp split: bool.split)
  apply auto
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.cases)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.cases sub_free_some)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.cases)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.cases sub_free_some)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.cases)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.cases sub_free_some)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (simp split: bool.split)
  apply auto
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (simp split: bool.split)
  apply auto
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (simp split: bool.split)
  apply auto
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.simps sub_free_some)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.simps sub_free_some)
  apply (simp split: bool.split)
  apply auto
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.simps sub_free_some)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.simps sub_free_some)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.simps sub_free_some)
  apply (simp split: bool.split)
  apply auto
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.simps sub_free_some)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.simps sub_free_some)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.simps sub_free_some)
  apply (simp split: bool.split)
  apply auto
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.simps sub_free_some)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.simps sub_free_some)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.simps sub_free_some)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (simp split: bool.split)
  apply auto
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (simp split: bool.split)
  apply auto
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) select'_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_subtypes_sf_preserve select'_sf_preserve select_sf_preserve sub_free.simps)
  done

lemma common_df_preserve: "disj_free n tr t \<Longrightarrow> disj_free n tr e \<Longrightarrow> disj_free_opt n tr (common m i tr t e)"
  apply (induction m i tr t e rule: common.induct)
  apply (simp_all split: Relatedness.split)
  defer
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases disj_free_some select'_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases disj_free_some select'_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases disj_free_some select'_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases disj_free_some select'_df_preserve)
  apply auto
  apply (simp split: bool.split)
  apply auto
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases select'_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps disj_free_some select'_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases select'_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps disj_free_some select'_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases select'_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps disj_free_some select'_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (simp split: bool.split)
  apply auto
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (simp split: bool.split)
  apply auto
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (simp split: bool.split)
  apply auto
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps disj_free_some select'_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps disj_free_some select'_df_preserve)
  apply (simp split: bool.split)
  apply auto
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps select'_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps disj_free_some select'_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps disj_free_some select'_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps disj_free_some select'_df_preserve)
  apply (simp split: bool.split)
  apply auto
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps disj_free_some select'_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps disj_free_some select'_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps disj_free_some select'_df_preserve)
  apply (simp split: bool.split)
  apply auto
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps disj_free_some select'_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps disj_free_some select'_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps disj_free_some select'_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (simp split: bool.split)
  apply auto
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (simp split: bool.split)
  apply auto
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps select'_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps select'_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps select'_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve erase_subtypes_df_preserve select'_df_preserve select_df_preserve)
  done

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
  "well_formed_tr c tr \<Longrightarrow> n \<le> c \<Longrightarrow> sub_free c tr t \<Longrightarrow> pwfbdd n tr t \<Longrightarrow> (case common n c tr t Nothing of Some s \<Rightarrow> erase_disjoints c tr s = Nothing | None \<Rightarrow> True)"
  apply (induction t arbitrary: n)
  apply auto
  (* t \<Longrightarrow> Select i t e *)
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
  apply (metis option.case_eq_if option.distinct(1))
  (* 4/6 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) sub_free.cases)
  (* 5/6 *)
  apply (smt (verit) BDD_select.select_def Suc_leD erase_disjoints.simps(1) not_Some_eq option.case_eq_if option.sel)
  (* 6/6 *)
  apply (smt (z3) BDD_select.select_def Suc_leD erase_disjoints.simps(1) option.case_eq_if option.distinct(1) option.inject)
  done

theorem common_correct_t0:
  "well_formed_tr c tr \<Longrightarrow> n \<le> c \<Longrightarrow>
   disj_free c tr t \<Longrightarrow> sub_free c tr e \<Longrightarrow>
   pwfbdd c tr t \<Longrightarrow> pwfbdd c tr e \<Longrightarrow>
   (case common n c tr t e of Some s \<Rightarrow> erase_disjoints c tr s = t | None \<Rightarrow> True)"
  apply (induction n c tr t e rule: common.induct)
  apply (simp_all del: erase_disjoints.simps erase_subtypes.simps split: option.split)
  apply simp
  apply simp
  defer
  (* Case 1 / 5 *)
  apply (case_tac "tr it c")
  apply (auto simp add: select'_def)[3]
  apply (case_tac "common n c tr et Nothing")
  apply auto[2]
  apply (simp add: select_def)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases erase_disj_df_noop less_le pwf_is_norm pwf_weaken pwfbdd.cases)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps)
  apply (case_tac "common n c tr tt Nothing")
  apply auto[2]
  apply (case_tac "common n c tr et Nothing")
  apply auto[2]
  apply (simp add: select_def)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases less_le pwf_weaken pwfbdd.cases)
  (* case 2 / 5 *)
  apply (case_tac "tr it c")
  apply (auto simp add: select'_def)[3]
  apply (case_tac "common n c tr et Top")
  apply auto[2]
  apply (simp add: select_def)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases erase_disj_df_noop less_le pwf_is_norm pwf_weaken pwfbdd.cases)
  apply (case_tac "common n c tr tt Top")
  apply auto[2]
  apply (case_tac "common n c tr et Top")
  apply auto[2]
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps)
  apply (case_tac "common n c tr tt Top")
  apply auto[2]
  apply (case_tac "common n c tr et Top")
  apply auto[2]
  apply (simp add: select_def)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases less_le pwf_weaken pwfbdd.cases)
  (* case 3 / 5 *)
  apply (case_tac "tr ie c")
  apply (auto simp add: select'_def)[3]
  apply (case_tac "common n c tr Nothing te")
  apply auto[2]
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject sub_free.cases)
  apply (case_tac "common n c tr Nothing ee")
  apply auto[2]
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) BDD_select.select_def erase_disjoints.simps(1) less_imp_le_nat pwf_weaken pwfbdd.simps sub_free.simps)
  apply (case_tac "common n c tr Nothing te")
  apply auto[2]
  apply (case_tac "common n c tr Nothing ee")
  apply auto[2]
  apply (simp add: select_def)
  apply auto
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) le_less pwf_weaken pwfbdd.simps sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) le_less pwf_weaken pwfbdd.simps sub_free.simps)
  (* case 4 / 5 *)
  apply (case_tac "tr ie c")
  apply (auto simp add: select'_def)[3]
  apply (case_tac "common n c tr Top te")
  apply auto[2]
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject sub_free.cases)
  apply (case_tac "common n c tr Top ee")
  apply auto[2]
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) BDD_select.select_def erase_disjoints.simps(1) less_imp_le_nat pwf_weaken pwfbdd.simps sub_free.simps)
  apply (case_tac "common n c tr Top ee")
  apply auto[2]
  apply (metis not_Some_eq option.case_eq_if)
  apply (case_tac "common n c tr Top te")
  apply auto[2]
  apply (metis BDD.distinct(5) BDD.inject BDD.simps(5) BDD_select.select_def erase_disjoints.simps(1) less_or_eq_imp_le pwf_weaken pwfbdd.simps sub_free.simps)
  (* case 5 / 5 *)
  apply (subgoal_tac "disj_free c tr et")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases)
  apply (subgoal_tac "pwfbdd c tr et")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) less_imp_not_less not_le pwf_weaken pwfbdd.cases)
  apply (simp split: bool.splits Relatedness.splits option.splits)
  apply (auto simp add: select'_def)
  apply (simp_all split: bool.splits Relatedness.splits option.splits)
  (* 5: 1/7 *)
  apply (auto simp add: select_def)[1]
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases erase_disj_df_noop norm_widen pwf_is_norm pwfbdd.cases)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases erase_disj_df_noop norm_widen pwf_is_norm pwfbdd.cases)
  apply metis
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases erase_disj_df_noop norm_widen pwf_is_norm pwfbdd.cases)
  (* 5: 2/7 *)
  apply (case_tac "tr ie it")
  apply auto[3]
  (* 5: 2: 1/3 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps)
  (* 5: 2: 2/3 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps)
  (* 5: 2: 3/3 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps)
  (* 5: 3/7 *)
  apply (subgoal_tac "sub_free c tr (erase_subtypes it tr ee)")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_subtypes_sf_preserve sub_free.simps)
  apply (subgoal_tac "pwfbdd c tr ee")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) less_imp_le_nat pwf_weaken pwfbdd.simps)
  apply (subgoal_tac "pwfbdd c tr (erase_subtypes it tr ee)")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_subtypes_pwf less_le_not_le pwf_weaken pwfbdd.cases)
  apply auto
  apply (subgoal_tac "disj_free c tr tt")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases)
  apply (subgoal_tac "sub_free c tr
                        (select ie (erase_disjoints it tr te)
                                   (erase_disjoints it tr ee))")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve select_sf_preserve sub_free.simps)
  apply (subgoal_tac "pwfbdd c tr tt")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) not_le order.asym pwf_weaken pwfbdd.simps)
  apply (subgoal_tac "pwfbdd c tr (erase_disjoints it tr te)")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disjoints_pwf less_le_not_le pwf_weaken pwfbdd.simps)
  apply (subgoal_tac "pwfbdd c tr
                (select ie (erase_disjoints it tr te)
                  (erase_disjoints it tr ee))")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_df_preserve erase_disj_sf_preserve erase_disjoints_pwf order.strict_implies_order pwfbdd.cases select_pwf)
  apply (case_tac "tr ie it")
  apply auto[3]
  (* 5: 3: 1/3 *)
  apply (simp add: select_def)
  apply auto[1]
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) pwfbdd.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) pwfbdd.cases)
  apply blast
  (* 5: 3: 2/3 *)
  apply (subst select_def)
  apply auto[1]
  apply (smt (verit) BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_disjoints_pwf erase_subtypes_df_preserve erase_subtypes_pwf erase_subtypes_sf_preserve less_imp_le pwf_weaken pwfbdd.cases pwfbdd.simps select_pwf select_sf_preserve sub_free.simps)
  apply (smt (verit) BDD.inject BDD.simps(5) BDD.simps(7) BDD_select.select_def erase_subtypes_df_preserve erase_subtypes_pwf erase_subtypes_sf_preserve order.strict_implies_order pwf_weaken pwfbdd.cases pwfbdd.simps select_pwf sub_free.simps)
  (* 5: 3: 3/3 *)
  apply (subst select_def)
  apply auto[1]
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_subtypes_df_preserve erase_subtypes_pwf erase_subtypes_sf_preserve less_imp_le pwfbdd.simps select_pwf select_sf_preserve sub_free.cases)
  apply (subst select_def)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_subtypes_df_preserve erase_subtypes_pwf erase_subtypes_sf_preserve less_le_not_le pwfbdd.simps select_pwf select_sf_preserve sub_free.cases)
  (* 5: 4/7 *)
  apply (subst select_def)
  apply auto[1]
  (* 5: 4: 1/3 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps)
  (* 5: 4: 2/3 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases le_less pwf_weaken pwfbdd.simps sub_free.simps)
  (* 5: 4: 3/3 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) BDD_select.select_def disj_free.cases less_imp_le pwf_weaken pwfbdd.cases sub_free.cases)
  (* 5: 5/7 *)
  apply (subst select_def)
  apply auto[1]
  (* 5: 5: 1/2 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) sub_free.cases)
  (* 5: 5: 2/2 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) sub_free.cases)
  (* 5: 5: 3/3 *)
  (* 5: 6/7 *)
  apply (subst select_def)
  apply auto[1]
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject less_or_eq_imp_le pwf_weaken pwfbdd.cases sub_free.cases)
  (* 5: 7/7 *)
  apply (subgoal_tac "sub_free c tr ee")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) sub_free.cases)
  apply (subgoal_tac "sub_free c tr te")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) sub_free.cases)
  apply (subgoal_tac "pwfbdd c tr ee")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) leD le_cases pwf_weaken pwfbdd.simps)
  apply (subgoal_tac "pwfbdd c tr te")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) leD le_cases pwf_weaken pwfbdd.simps)
  apply (subgoal_tac "disj_free c tr (erase_subtypes ie tr et)")
  prefer 2
  using erase_subtypes_df_preserve apply presburger
  apply (subgoal_tac "pwfbdd c tr (erase_subtypes ie tr et)")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_subtypes_pwf leI le_cases pwf_weaken pwfbdd.cases)
  apply (subgoal_tac "disj_free c tr
                        (select it (erase_disjoints ie tr tt)
                                   (erase_disjoints ie tr et))")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve select_df_preserve)
  apply (subgoal_tac "pwfbdd c tr
                        (select it (erase_disjoints ie tr tt)
                                   (erase_disjoints ie tr et))")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_df_preserve erase_disj_sf_preserve erase_disjoints_pwf leI pwfbdd.simps select_pwf)
  apply (case_tac "tr it ie")
  apply auto
  (* 5: 7: 1/3 *)
  apply (subst select_def)
  apply auto[1]
  (* IMPOSSIBLE *)
  sledgehammer
  oops


theorem common_correct_t0_test:
  "well_formed_tr c test_tr \<Longrightarrow> n \<le> c \<Longrightarrow>
   disj_free c test_tr t \<Longrightarrow> sub_free c test_tr e \<Longrightarrow>
   pwfbdd c test_tr t \<Longrightarrow> pwfbdd c test_tr e \<Longrightarrow>
   (case common n c test_tr t e of Some s \<Rightarrow> erase_disjoints c test_tr s = t | None \<Rightarrow> True)"
  apply (induction n c test_tr t e rule: common.induct)
  apply (simp_all del: erase_disjoints.simps erase_subtypes.simps add: select'_def split: option.split bool.split)
  apply simp_all
  apply (simp_all del: erase_disjoints.simps erase_subtypes.simps split: Relatedness.split)
  defer
  (* Case 1 / 5 *)
  apply (case_tac "test_tr it c")
  apply (auto simp add: select'_def)[3]
  apply (case_tac "common n c test_tr et Nothing")
  apply auto[2]
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) less_le pwfbdd.cases)
  apply (case_tac "common n c test_tr tt Nothing")
  apply (case_tac "common n c test_tr et Nothing")
  apply auto[2]
  apply (simp add: select_def)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases erase_disj_df_noop less_le pwf_is_norm pwf_weaken pwfbdd.cases)
  (* case 2 / 5 *)
  apply (case_tac "test_tr it c")
  apply (auto simp add: select'_def)[3]
  apply (case_tac "common n c test_tr et Top")
  apply auto[2]
  apply (simp add: select_def)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases erase_disj_df_noop less_le pwf_is_norm pwf_weaken pwfbdd.cases)
  apply (case_tac "common n c test_tr tt Top")
  apply auto[2]
  apply (case_tac "common n c test_tr et Top")
  apply auto[2]
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps)
  apply (case_tac "common n c test_tr tt Top")
  apply auto[2]
  apply (case_tac "common n c test_tr et Top")
  apply auto[2]
  apply (simp add: select_def)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject disj_free.cases less_le pwf_weaken pwfbdd.cases)
  (* case 3 / 5 *)
  apply (case_tac "test_tr c ie")
  apply (auto simp add: select'_def)[3]
  apply (case_tac "common n c test_tr Nothing te")
  apply auto[2]
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject less_le pwfbdd.cases sub_free.cases wftr_refl0)
  apply (case_tac "common n c test_tr Nothing ee")
  apply auto[2]
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) BDD_select.select_def erase_disjoints.simps(1) less_imp_le_nat pwf_weaken pwfbdd.simps sub_free.simps wftr_refl0)
  apply (case_tac "common n c test_tr Nothing te")
  apply auto[2]
  apply (case_tac "common n c test_tr Nothing ee")
  apply auto[2]
  apply (simp add: select_def)
  apply auto
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) le_less pwf_weaken pwfbdd.simps sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) le_less pwf_weaken pwfbdd.simps sub_free.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) le_less pwf_weaken pwfbdd.simps sub_free.simps)
  (* case 4 / 5 *)
  apply (case_tac "test_tr c ie")
  apply (auto simp add: select'_def)[3]
  apply (case_tac "common n c test_tr Top te")
  apply auto[2]
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject less_le pwfbdd.cases sub_free.cases wftr_refl0)
  apply (case_tac "common n c test_tr Top ee")
  apply auto[2]
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) BDD_select.select_def erase_disjoints.simps(1) less_imp_le_nat pwf_weaken pwfbdd.simps sub_free.simps wftr_refl0)
  apply (case_tac "common n c test_tr Top ee")
  apply auto[2]
  apply (metis not_Some_eq option.case_eq_if)
  apply (case_tac "common n c test_tr Top te")
  apply auto[2]
  apply (metis BDD.distinct(5) BDD.inject BDD.simps(5) BDD_select.select_def erase_disjoints.simps(1) less_or_eq_imp_le pwf_weaken pwfbdd.simps sub_free.simps)
  (* case 5 / 5 *)
  apply (subgoal_tac "disj_free c test_tr et")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases)
  apply (subgoal_tac "pwfbdd c test_tr et")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) less_imp_not_less not_le pwf_weaken pwfbdd.cases)
  apply (simp split: bool.splits Relatedness.splits option.splits)
  apply (auto simp add: select'_def)
  apply (simp_all split: bool.splits Relatedness.splits option.splits)
  (* 5: 1/7 *)
  apply (auto simp add: select_def)[1]
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases erase_disj_df_noop norm_widen pwf_is_norm pwfbdd.cases)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases erase_disj_df_noop norm_widen pwf_is_norm pwfbdd.cases)
  apply metis
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases erase_disj_df_noop norm_widen pwf_is_norm pwfbdd.cases)
  (* 5: 2/7 *)
  apply (case_tac "test_tr ie it")
  apply auto[3]
  (* 5: 2: 1/3 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps)
  (* 5: 2: 2/3 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps)
  (* 5: 2: 3/3 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps)
  (* 5: 3/7 *)
  apply (subgoal_tac "sub_free c test_tr (erase_subtypes it test_tr ee)")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_subtypes_sf_preserve sub_free.simps)
  apply (subgoal_tac "pwfbdd c test_tr ee")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) less_imp_le_nat pwf_weaken pwfbdd.simps)
  apply (subgoal_tac "pwfbdd c test_tr (erase_subtypes it test_tr ee)")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_subtypes_pwf less_le_not_le pwf_weaken pwfbdd.cases)
  apply auto
  apply (subgoal_tac "disj_free c test_tr tt")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases)
  apply (subgoal_tac "sub_free c tr
                        (select ie (erase_disjoints it test_tr te)
                                   (erase_disjoints it test_tr ee))")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve select_sf_preserve sub_free.simps)
  apply (subgoal_tac "pwfbdd c test_tr tt")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) not_le order.asym pwf_weaken pwfbdd.simps)
  apply (subgoal_tac "pwfbdd c test_tr (erase_disjoints it test_tr te)")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disjoints_pwf less_le_not_le pwf_weaken pwfbdd.simps)
  apply (subgoal_tac "pwfbdd c tr
                (select ie (erase_disjoints it test_tr te)
                  (erase_disjoints it test_tr ee))")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_df_preserve erase_disj_sf_preserve erase_disjoints_pwf order.strict_implies_order pwfbdd.cases select_pwf)
  apply (case_tac "test_tr ie it")
  apply auto[3]
  (* 5: 3: 1/3 *)
  apply (simp add: select_def)
  apply auto[1]
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) pwfbdd.simps)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) pwfbdd.cases)
  apply blast
  (* 5: 3: 2/3 *)
  apply (subst select_def)
  apply auto[1]
  apply (smt (verit) BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_sf_preserve erase_disjoints_pwf erase_subtypes_df_preserve erase_subtypes_pwf erase_subtypes_sf_preserve less_imp_le pwf_weaken pwfbdd.cases pwfbdd.simps select_pwf select_sf_preserve sub_free.simps)
  apply (smt (verit) BDD.inject BDD.simps(5) BDD.simps(7) BDD_select.select_def erase_subtypes_df_preserve erase_subtypes_pwf erase_subtypes_sf_preserve order.strict_implies_order pwf_weaken pwfbdd.cases pwfbdd.simps select_pwf sub_free.simps)
  (* 5: 3: 3/3 *)
  apply (subst select_def)
  apply auto[1]
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_subtypes_df_preserve erase_subtypes_pwf erase_subtypes_sf_preserve less_imp_le pwfbdd.simps select_pwf select_sf_preserve sub_free.cases)
  apply (subst select_def)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_subtypes_df_preserve erase_subtypes_pwf erase_subtypes_sf_preserve less_le_not_le pwfbdd.simps select_pwf select_sf_preserve sub_free.cases)
  (* 5: 4/7 *)
  apply (subst select_def)
  apply auto[1]
  (* 5: 4: 1/3 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps)
  (* 5: 4: 2/3 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.cases le_less pwf_weaken pwfbdd.simps sub_free.simps)
  (* 5: 4: 3/3 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) BDD_select.select_def disj_free.cases less_imp_le pwf_weaken pwfbdd.cases sub_free.cases)
  (* 5: 5/7 *)
  apply (subst select_def)
  apply auto[1]
  (* 5: 5: 1/3 *)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject Relatedness.distinct(1) not_le order.asym pwfbdd.cases wftr_refl0)
  (* 5: 5: 2/3 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) leD le_cases pwfbdd.simps sub_free.simps wftr_refl0)
  (* 5: 5: 3/3 *)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject less_or_eq_imp_le pwfbdd.cases sub_free.cases wftr_refl0)
  (* 5: 6/7 *)
  apply (subst select_def)
  apply auto[1]
  (* 5: 6: 1/3 *)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject less_or_eq_imp_le pwf_weaken pwfbdd.cases sub_free.cases)
  (* 5: 6: 2/3 *)
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) leD le_cases pwfbdd.simps wftr_refl0)
  (* 5: 6: 3/3 *)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject less_or_eq_imp_le pwfbdd.cases wftr_refl0)
  (* 5: 7/7 *)
  apply (subgoal_tac "sub_free c test_tr ee")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) sub_free.cases)
  apply (subgoal_tac "sub_free c test_tr te")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) sub_free.cases)
  apply (subgoal_tac "pwfbdd c test_tr ee")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) leD le_cases pwf_weaken pwfbdd.simps)
  apply (subgoal_tac "pwfbdd c test_tr te")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) leD le_cases pwf_weaken pwfbdd.simps)
  apply (subgoal_tac "disj_free c test_tr (erase_subtypes ie test_tr et)")
  prefer 2
  using erase_subtypes_df_preserve apply presburger
  apply (subgoal_tac "pwfbdd c test_tr (erase_subtypes ie test_tr et)")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_subtypes_pwf leI le_cases pwf_weaken pwfbdd.cases)
  apply (subgoal_tac "disj_free c tr
                        (select it (erase_disjoints ie test_tr tt)
                                   (erase_disjoints ie test_tr et))")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) disj_free.simps erase_disj_df_preserve select_df_preserve)
  apply (subgoal_tac "pwfbdd c tr
                        (select it (erase_disjoints ie test_tr tt)
                                   (erase_disjoints ie test_tr et))")
  prefer 2
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) erase_disj_df_preserve erase_disj_sf_preserve erase_disjoints_pwf leI pwfbdd.simps select_pwf)
  apply (case_tac "test_tr it ie")
  apply auto
  (* 5: 7: 1/3 *)
  apply (subst select_def)
  apply auto[1]
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) Relatedness.distinct(5) leI less_asym' pwfbdd.simps wftr_refl0)
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