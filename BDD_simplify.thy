theory BDD_simplify
  imports Main BDD_basic BDD_union BDD_intersect BDD_uniqueness
begin

fun simplify_n :: "nat \<Rightarrow> BDD \<Rightarrow> BDD \<Rightarrow> BDD" where
  "simplify_n _ Nothing _ = Nothing" |
  "simplify_n _ Top b = b" |
  "simplify_n _ (Select va ta ea) Nothing = Nothing" |
  "simplify_n _ (Select va ta ea) Top = Top" |
  "simplify_n 0 (Select _ _ _) (Select _ _ _) = Top" |
  "simplify_n (Suc n) (Select va ta ea) (Select vb tb eb) =
     (if va > vb then
        simplify_n n (union ta ea) (Select vb tb eb)
      else if va = vb then
        if ta = Nothing then
          simplify_n n ea eb
        else if ea = Nothing then
          simplify_n n ta tb
        else
          select va (simplify_n n ta tb) (simplify_n n ea eb)
      else
        select vb (simplify_n n (Select va ta ea) tb)
                  (simplify_n n (Select va ta ea) eb))"


fun simplify :: "BDD \<Rightarrow> BDD \<Rightarrow> BDD" where
  "simplify Nothing _ = Nothing" |
  "simplify Top b = b" |
  "simplify (Select va ta ea) Nothing = Nothing" |
  "simplify (Select va ta ea) Top = Top" |
  "simplify (Select va ta ea) (Select vb tb eb) =
     (if va > vb then
        simplify_n (Suc va) (Select va ta ea) (Select vb tb eb)
      else
        simplify_n (Suc vb) (Select va ta ea) (Select vb tb eb))"

lemma simplify_n_top[simp]: "simplify_n n ta Top = (if ta = Nothing then Nothing else Top)"
  by (metis BDD.exhaust simplify_n.simps(1) simplify_n.simps(2) simplify_n.simps(4))

lemma not_norm_0_select[simp]: "~norm 0 (Select v t e)"
  using norm.cases by blast

lemma simplify_n_nothing [simp]: "simplify_n n a Nothing = Nothing"
  apply (induction a arbitrary: n)
  by auto

lemma simplify_nothing [simp]: "simplify a Nothing = Nothing"
  apply (case_tac a)
  by auto

lemma simplify_top: "a \<noteq> Nothing \<Longrightarrow> simplify a Top = Top"
  apply (case_tac a)
  by auto

lemma union_select_contains: "contains (Select v t e) f \<Longrightarrow> contains (union t e) f"
  apply simp
  apply (case_tac "f v")
  apply (simp add: contains_p_correct)
  apply (simp add: contains_p_correct)
  done

lemma simplify_n_idem: "norm n a \<Longrightarrow> norm n b \<Longrightarrow> s = simplify_n n a b \<Longrightarrow> simplify_n n a s = s"
  apply (induction n arbitrary: s a b)
  apply simp
  oops

end