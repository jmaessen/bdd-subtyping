theory BDD_intersect
  imports Main BDD_basic BDD_select
begin

fun intersect :: "BDD \<Rightarrow> BDD \<Rightarrow> BDD" where
  "intersect Nothing _ = Nothing" |
  "intersect Top b = b" |
  "intersect (Select _ _ _) Nothing = Nothing" |
  "intersect (Select va ta ea) Top = (Select va ta ea)" |
  "intersect (Select va ta ea) (Select vb tb eb) = 
     (if va > vb then
        select va (intersect ta (Select vb tb eb)) (intersect ea (Select vb tb eb))
      else if va = vb then
        select va (intersect ta tb) (intersect ea eb)
      else
        select vb (intersect (Select va ta ea) tb) (intersect (Select va ta ea) eb))"

lemma intersect_simp_Nothing: "intersect a Nothing = Nothing"
  apply (induction a)
  by auto

lemma intersect_simp_Top: "intersect a Top = a"
  apply (induction a)
  by auto

theorem ordered_intersect: "ordered n a \<Longrightarrow> ordered n b \<Longrightarrow> ordered n (intersect a b)"
  apply (induction a b arbitrary: n rule: intersect.induct)
  apply simp_all
  apply auto
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.simps ordered_select)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject ordered.simps ordered_select)
  by (metis BDD.distinct(6) BDD.inject BDD.simps(5) antisym_conv3 ordered.simps ordered_select)

theorem dup_free_intersect: "norm n a \<Longrightarrow> norm n b \<Longrightarrow> norm n (intersect a b)"
  apply (induction a b arbitrary: n rule: intersect.induct)
  apply simp
  apply simp
  apply simp
  apply simp
  (* Even a simp here really gets stuck for a long time. *)
  apply (case_tac "vb < va")
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) intersect.simps(5) norm.simps norm_select)
  apply (case_tac "vb = va")
  apply (metis BDD.inject BDD.simps(5) BDD.simps(7) intersect.simps(5) norm.simps norm_select)
  by (metis BDD.inject BDD.simps(5) BDD.simps(7) antisym_conv3 intersect.simps(5) norm.simps norm_select)

theorem intersect_correct: "contains (intersect a b) f = (contains a f \<and> contains b f)"
  apply (induction a b arbitrary: f rule: intersect.induct)  
  apply fastforce
  apply fastforce
  apply fastforce
  apply fastforce
  by (smt (z3) BDD_select.select_def contains_p.simps(3) contains_p_correct intersect.simps(5))

end