theory BDD_uniqueness
  imports Main BDD_basic
begin


inductive distinguisher:: "BDD \<Rightarrow> BDD \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool" where
  dist_n_t [simp, intro]: "distinguisher Nothing Top f" |
  dist_n_st [simp, intro]: "f v \<Longrightarrow> distinguisher Nothing t f \<Longrightarrow> distinguisher Nothing (Select v t e) f" |
  dist_n_se [simp, intro]: "~f v \<Longrightarrow> distinguisher Nothing e f \<Longrightarrow> distinguisher Nothing (Select v t e) f" |
  dist_t_n [simp, intro]: "distinguisher Top Nothing f" | 
  dist_t_st [simp, intro]: "f v \<Longrightarrow> distinguisher Top t f \<Longrightarrow> distinguisher Top (Select v t e) f" |
  dist_t_se [simp, intro]: "~f v \<Longrightarrow> distinguisher Top e f \<Longrightarrow> distinguisher Top (Select v t e) f" |
  dist_s_nt [simp, intro]: "f v \<Longrightarrow> distinguisher t Nothing f \<Longrightarrow> distinguisher (Select v t e) Nothing f" |
  dist_s_ne [simp, intro]: "~f v \<Longrightarrow> distinguisher e Nothing f \<Longrightarrow> distinguisher (Select v t e) Nothing f" |
  dist_s_tt [simp, intro]: "f v \<Longrightarrow> distinguisher t Top f \<Longrightarrow> distinguisher (Select v t e) Top f" |
  dist_s_te [simp, intro]: "~f v \<Longrightarrow> distinguisher e Top f \<Longrightarrow> distinguisher (Select v t e) Top f" |
  dist_s_sgt: "va > vb \<Longrightarrow> f va \<Longrightarrow> distinguisher ta (Select vb tb eb) f \<Longrightarrow> distinguisher (Select va ta ea) (Select vb tb eb) f" |
  dist_s_sge: "va > vb \<Longrightarrow> ~f va \<Longrightarrow> distinguisher ea (Select vb tb eb) f \<Longrightarrow> distinguisher (Select va ta ea) (Select vb tb eb) f" |
  dist_s_slt: "vb > va \<Longrightarrow> f vb \<Longrightarrow> distinguisher (Select va ta ea) tb f \<Longrightarrow> distinguisher (Select va ta ea) (Select vb tb eb) f" |
  dist_s_sle: "vb > va \<Longrightarrow> ~f vb \<Longrightarrow> distinguisher (Select va ta ea) eb f \<Longrightarrow> distinguisher (Select va ta ea) (Select vb tb eb) f" |
  dist_s_set: "f v \<Longrightarrow> distinguisher ta tb f \<Longrightarrow> distinguisher (Select v ta ea) (Select v tb eb) f" |
  dist_s_see: "~f v \<Longrightarrow> distinguisher ea eb f \<Longrightarrow> distinguisher (Select v ta ea) (Select v tb eb) f"

(* TODO: dist_s_s, dist t_s, dist n_s, dist s_t, dist n_t proof fixtures *)

definition join_dist :: "nat \<Rightarrow> (nat \<Rightarrow> bool) option \<Rightarrow> (nat \<Rightarrow> bool) option \<Rightarrow> (nat \<Rightarrow> bool) option" where
  "join_dist v t e = (case t of
     Some(f) \<Rightarrow> Some(replace f v True) |
     None \<Rightarrow> e)"

fun distinguish :: "BDD \<Rightarrow> BDD \<Rightarrow> (nat \<Rightarrow> bool) option" where
  "distinguish (Select va ta ea) (Select vb tb eb) =
     (if va > vb
      then join_dist va (distinguish ta (Select vb tb eb)) (distinguish ea (Select vb tb eb))
      else if va = vb
      then join_dist va (distinguish ta tb) (distinguish ea eb)
      else join_dist vb (distinguish (Select va ta ea) tb) (distinguish (Select va ta ea) eb))" |
  "distinguish Nothing Top = Some (\<lambda>x. False)" |
  "distinguish Top Nothing = Some (\<lambda>x. False)" |
  "distinguish Nothing Nothing = None" |
  "distinguish Top Top = None" |
  "distinguish Nothing (Select vb tb eb) = join_dist vb (distinguish Nothing tb) (distinguish Nothing eb)" |
  "distinguish Top (Select vb tb eb) = join_dist vb (distinguish Top tb) (distinguish Top eb)" |
  "distinguish (Select va ta ea) Nothing = join_dist va (distinguish ta Nothing) (distinguish ea Nothing)" |
  "distinguish (Select va ta ea) Top = join_dist va (distinguish ta Top) (distinguish ea Top)"

(* TODO: Similar fixtures here, probably one for join_dist. *)
lemma join_dist_none [simp]: "(join_dist v mt me = None) = (mt = None \<and> me = None)"
  by (simp add: join_dist_def option.case_eq_if)

lemma join_dist_some [simp]:
  "(join_dist v mt me = Some f) =
   ((\<exists>g. mt = Some g \<and> f = replace g v True) \<or> (mt = None \<and> me = Some f))"
  by (auto simp add: join_dist_def option.case_eq_if)

theorem dist_contains: "distinguisher a b f \<Longrightarrow> contains a f \<noteq> contains b f"
  apply (induction a b f rule: distinguisher.induct)
  by (simp_all add: contains_p_correct)

lemma dist_symm: "distinguisher a b f \<Longrightarrow> distinguisher b a f"
  apply (induction a b f rule: distinguisher.induct)
  using distinguisher.intros by simp_all

lemma noncontains_dist_top [simp]: "\<not>contains b f \<Longrightarrow> distinguisher Top b f"
  apply (induction b)
  apply auto
  apply (case_tac "f x1")
  apply (meson contains_sel_t dist_t_st)
  apply (metis contains_sel_e dist_t_se)
  done

lemma contains_dist_nothing [simp]: "contains b f \<Longrightarrow> distinguisher Nothing b f"
  apply (induction b f rule: contains.induct)
  by auto

lemma contains_dist0: "contains a f \<Longrightarrow> \<not>contains b f \<Longrightarrow> distinguisher a b f"
  apply (induction a b rule: distinguish.induct)
  apply simp_all
  apply (case_tac "vb < va")
  apply auto[1]
  apply (case_tac "f va")
  apply (simp add: contains_p_correct dist_s_sgt)
  apply (simp add: contains_p_correct dist_s_sge)
  apply auto[1]
  apply (case_tac "vb = va")
  apply auto[1]
  apply (case_tac "f va")
  apply (simp add: contains_p_correct dist_s_set)
  apply (simp add: contains_p_correct dist_s_see)
  apply (subgoal_tac "va < vb")
  apply auto[2]
  apply (case_tac "f vb")
  apply (simp add: contains_p_correct dist_s_slt)
  apply (simp add: contains_p_correct dist_s_sle)
  using contains_dist_nothing dist_symm apply blast
  done

theorem contains_dist: "contains a f \<noteq> contains b f \<Longrightarrow> distinguisher a b f"
  by (meson contains_dist0 dist_symm)

theorem dister_correct: "distinguisher a b f = (contains a f \<noteq> contains b f)"
  using contains_dist dist_contains by blast

theorem norm_dist: "(\<forall>f. ~distinguisher a b f) = (\<forall>f. contains a f = contains b f)"
  using dister_correct by blast

theorem dist_comm0: "distinguish a b = r \<Longrightarrow> distinguish b a = r"
  apply (induction arbitrary: r rule: distinguish.induct)
  apply (auto simp add: split: option.split)
  done

lemma dist_comm: "distinguish a b = distinguish b a"
  using dist_comm0 by blast

theorem dist_none_equiv0: "distinguish a b = None \<Longrightarrow> contains a f \<Longrightarrow> contains b f"
  apply (induction arbitrary: f rule: distinguish.induct)
  apply (auto simp add: split: option.split)
  apply (metis contains_p.simps(3) contains_p_correct join_dist_none)
  apply (auto simp add: contains_p_correct)
  by presburger

theorem dist_none_dister: "distinguish a b = None \<Longrightarrow> ~distinguisher a b f"
  by (metis dist_comm0 dist_none_equiv0 norm_dist)

lemma dist_ord_false: "ordered n a \<Longrightarrow> ordered n b \<Longrightarrow> (distinguish a b = Some(f)) \<Longrightarrow> ~f n"
  apply (induction arbitrary: n f rule: distinguish.induct)
  apply (auto simp add: split: option.split)
  apply (case_tac "vb < va")
  apply auto[2]
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject nat_neq_iff ordered.cases ordered_widen)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject ordered.cases ordered_widen)
  apply (case_tac "vb = va")
  apply simp
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject less_not_refl ordered.cases ordered_widen)
  apply simp
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject leD order_refl ordered.cases ordered_widen)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) nat_neq_iff ordered.simps ordered_widen)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.simps ordered_widen)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) nat_neq_iff ordered.simps ordered_widen)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.simps ordered_widen)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) nat_neq_iff ordered.simps ordered_widen)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.simps ordered_widen)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) nat_neq_iff ordered.simps ordered_widen)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.simps ordered_widen)
  done  

lemma dist_nothing_correct: "ordered n a \<Longrightarrow> (distinguish Nothing a = Some(f)) \<Longrightarrow> contains a f"
  apply (induction a arbitrary: n f)
  apply auto
  apply (rule contains_sel_t)
  apply simp
  apply (subst ordered_contains_ignore_t)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.cases)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.cases)
  apply (rule contains_sel_e)
  apply (rule dist_ord_false[of _ Nothing])
  apply (rule ordered_nothing)
  prefer 2
  apply assumption
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.cases)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.cases)
  done

lemma dist_top_correct: "\<lbrakk>ordered n a; distinguish Top a = Some(f)\<rbrakk> \<Longrightarrow> \<not>contains a f"
  apply (induction a arbitrary: n f)
  apply simp_all
  apply (subst contains_p_correct)
  apply simp
  apply (subgoal_tac "\<forall>a. contains_p a f = contains a f")
  defer
  using contains_p_correct apply presburger
  apply auto
  apply (subgoal_tac "contains a1 g")
  apply (subgoal_tac "ordered n a1")
  apply auto[1]
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.simps)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject ordered.cases ordered_contains_ignore_t)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) dist_ord_false ordered.simps)
  by (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.simps)

theorem dist_correct: "ordered n a \<Longrightarrow> ordered n b \<Longrightarrow> (distinguish a b = Some(f)) \<Longrightarrow> (contains a f \<noteq> contains b f)"  
  apply (induction arbitrary: n f rule: distinguish.induct)
  apply simp_all
  defer
  apply (rule dist_nothing_correct)
  apply auto[2]
  apply (rule dist_top_correct)
  apply assumption
  apply simp
  apply (rule dist_nothing_correct)
  apply assumption
  apply (subst dist_comm)
  apply auto[1]
  apply (rule dist_top_correct)
  apply assumption
  apply (subst dist_comm)
  apply auto[1]
  apply (case_tac "vb < va")
  apply auto[1]
  defer
  apply (rule contains_sel_t)
  apply simp
  apply (subst ordered_contains_ignore_t)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject ordered.cases)
  apply (subgoal_tac "\<not>contains (Select vb tb eb) g")
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.simps)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject ordered.cases ordered_contains_ignore_t ordered_sel)
  defer
  apply (rule contains_sel_e)
  apply (rule dist_ord_false)
  prefer 3
  apply assumption
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.simps)
  apply (metis BDD.inject ordered.simps)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.simps)
  apply (case_tac "va = vb")
  apply auto[1]
  defer
  apply (rule contains_sel_t)
  apply simp
  apply (subst ordered_contains_ignore_t)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject ordered.cases)
  apply (subgoal_tac "\<not>contains tb g")
  apply (subgoal_tac "ordered n ta")
  apply (subgoal_tac "ordered n tb")
  apply auto[1]
  apply simp_all
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject ordered.cases ordered_widen)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject ordered.cases ordered_widen)
  apply (subgoal_tac "contains tb g = contains tb (replace g vb True)")
  using contains_sel_t apply auto[1]
  apply metis
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject ordered.cases ordered_contains_ignore_t)
  defer
  apply (rule contains_sel_e)
  apply (rule dist_ord_false)
  prefer 3
  apply assumption
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject ordered.cases)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject ordered.cases)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) contains.simps dist_ord_false ordered.simps)
  apply (subgoal_tac "va < vb")
  apply simp_all
  apply auto[1]
  defer
  apply (subst ordered_contains_ignore_t)
  apply (metis BDD.inject ordered.simps)
  apply (subgoal_tac "\<not>contains tb g")
  apply (subgoal_tac "ordered n ta")
  apply (subgoal_tac "ordered n tb")
  apply auto[1]
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject ordered.cases ordered_widen)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject ordered.cases ordered_widen)
  apply (subgoal_tac "contains tb g = contains tb (replace g vb True)")
  using contains_sel_t apply auto[1]
  apply metis
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject ordered.cases ordered_contains_ignore_t)
  defer
  apply (metis BDD.inject BDD.simps(5) contains.simps dist_ord_false ordered.simps)
  (* contains \<Longrightarrow> contains \<Longrightarrow> False va then *)
  apply (subgoal_tac "contains ta g")
  apply (subgoal_tac "ordered n ta")
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject ordered.cases ordered_contains_ignore_t ordered_sel)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.simps ordered_widen)
  apply (subgoal_tac "contains ta g = contains ta (replace g va True)")
  apply (erule ssubst)
  apply (erule ssubst)
  apply (metis (mono_tags, lifting) contains_p.simps(3) contains_p_correct)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject ordered.cases ordered_contains_ignore_t)
  (* va else *)
  apply (subgoal_tac "contains ea f")
  apply (subgoal_tac "ordered n ea")
  apply (metis)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.simps ordered_widen)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) contains_p.simps(3) contains_p_correct dist_ord_false ordered.simps)
  (* = then *)
  apply (subgoal_tac "contains tb g")
  apply (subgoal_tac "ordered n ta")
  apply (subgoal_tac "ordered n tb")
  apply (metis (mono_tags) BDD.distinct(3) BDD.distinct(5) BDD.inject contains_p.simps(3) contains_p_correct ordered.cases ordered_contains_ignore_t)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.simps ordered_widen)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject ordered.cases ordered_widen)
  apply (subgoal_tac "contains tb g = contains tb (replace g vb True)")
  apply (erule ssubst)
  apply (erule ssubst)
  apply (simp add: contains_p_correct)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject ordered.cases ordered_contains_ignore_t)
  (* = else *)
  apply (subgoal_tac "contains eb f")
  apply (subgoal_tac "ordered n eb")
  apply (subgoal_tac "ordered n ea")
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject contains.simps dist_ord_false ordered.cases)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.simps ordered_widen)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject ordered.cases ordered_widen)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject contains.simps dist_ord_false ordered.cases)
  (* vb then *)
  apply (subgoal_tac "contains (Select va ta ea) g")
  apply (subgoal_tac "ordered vb (Select va ta ea)")
  apply (subgoal_tac "ordered vb tb")
  apply (metis (mono_tags) contains_top dist_t_st dister_correct ordered_contains_ignore_t)
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject ordered.cases)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.simps)
  apply (subgoal_tac "contains (Select va ta ea) g = contains (Select va ta ea) (replace g vb True)")
  apply (erule ssubst)
  apply (erule ssubst)
  apply assumption
  apply (metis BDD.distinct(3) BDD.distinct(5) BDD.inject ordered.cases ordered_contains_ignore_t ordered_sel)
  (* vb else *)
  apply (subgoal_tac "contains (Select va ta ea) f")
  apply (subgoal_tac "ordered vb (Select va ta ea)")
  apply (subgoal_tac "ordered vb eb")
  apply (metis contains_p.simps(3) contains_p_correct dist_ord_false)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) ordered.simps)
  apply (metis BDD.inject ordered.simps)
  apply (metis)
  done

lemma dist_some_nothing_complete: "contains b f \<Longrightarrow> \<exists>g. distinguish Nothing b = Some g"
  apply (induction b arbitrary: f)
  apply simp_all
  apply (case_tac "f x1")
  apply (subgoal_tac "\<exists>g. distinguish Nothing b1 = Some g")
  apply auto[1]
  apply (simp add: contains_p_correct)
  apply (case_tac "distinguish Nothing b1")
  apply (subgoal_tac "\<exists>g. distinguish Nothing b2 = Some g")
  apply auto[1]
  apply (simp add: contains_p_correct)
  apply auto[1]
  done

lemma dist_some_top_complete: "~contains b f \<Longrightarrow> \<exists>g. distinguish Top b = Some g"
  apply (induction b arbitrary: f)
  apply simp_all
  apply (case_tac "f x1")
  apply (subgoal_tac "\<exists>g. distinguish Top b1 = Some g")
  apply auto[1]
  apply (simp add: contains_p_correct)
  apply (case_tac "distinguish Top b1")
  apply (subgoal_tac "\<exists>g. distinguish Top b2 = Some g")
  apply auto[1]
  apply (simp add: contains_p_correct)
  apply auto[1]
  done

theorem dist_some_complete0: "contains a f \<Longrightarrow> ~contains b f \<Longrightarrow> \<exists>g. distinguish a b = Some(g)"
  apply (induction a b arbitrary: f rule: distinguish.induct)
  prefer 7
  apply (rule dist_some_top_complete)
  apply assumption
  prefer 7
  apply (subst dist_comm)
  apply (rule dist_some_nothing_complete)
  apply assumption
  apply simp_all
  (* Select / Select *)
  (* = *)
  apply (case_tac "va = vb")
  apply simp_all
  apply (case_tac "f vb")
  (* f vb *)
  apply (subgoal_tac "\<exists>g. distinguish ta tb = Some g")
  apply auto[1]
  apply (simp add: contains_p_correct)
  (* ~f vb *)
  apply (case_tac "distinguish ta tb")
  (* ta tb indistinguishable *)
  apply (subgoal_tac "contains ea f")
  apply (subgoal_tac "\<not>contains eb f")
  apply auto[1]
  apply (meson contains_sel)
  apply (simp add: contains_p_correct)
  (* ta tb distinguishable *)
  apply auto[1]
  (* < *)
  apply (case_tac "vb < va")
  apply simp_all
  apply (case_tac "f va")
  (* f va *)
  apply (subgoal_tac "\<exists>g. distinguish ta (Select vb tb eb) = Some g")
  apply auto[1]
  apply (simp add: contains_p_correct)
  (* ~f va *)
  apply (case_tac "distinguish ta (Select vb tb eb)")
  (* indist *)
  apply (subgoal_tac "contains ea f")
  apply auto[1]
  apply (simp add: contains_p_correct)
  (* dist *)
  apply auto[1]
  (* > *)
  apply (case_tac "f vb")
  (* f vb *)
  apply (subgoal_tac "\<exists>g. distinguish (Select va ta ea) tb = Some g")
  apply auto[1]
  apply (simp add: contains_p_correct)
  (* ~f vb *)
  apply (case_tac "distinguish (Select va ta ea) tb")
  (* indist *)
  apply (subgoal_tac "\<not>contains eb f")
  apply auto[1]
  apply (meson contains_sel)
  (* dist *)
  apply auto[1]
  done


theorem dist_some_complete: "(contains a f \<noteq> contains b f) \<Longrightarrow> \<exists>g. distinguish a b = Some(g)"
  by (metis dist_comm dist_some_complete0)

lemma equiv_dist_none: "ordered n a \<Longrightarrow> ordered n b \<Longrightarrow> (\<forall>f. contains a f = contains b f) = (distinguish a b = None)"
  by (meson contains_dist dist_correct dist_none_dister option.exhaust)

lemma dist_none_nothing: "\<lbrakk>norm n b; distinguish Nothing b = None\<rbrakk> \<Longrightarrow> b = Nothing"
  apply (induction b arbitrary: n)
  apply auto
  by (metis BDD.inject BDD.simps(5) BDD.simps(7) norm.cases)

lemma dist_none_top: "\<lbrakk>norm n b; distinguish Top b = None\<rbrakk> \<Longrightarrow> b = Top"
  using norm_top contains_top dist_none_equiv0 by presburger

lemma dist_none_unique: "\<lbrakk>norm n a; norm n b; distinguish a b = None\<rbrakk> \<Longrightarrow> a = b"
  apply (induction a b arbitrary: n rule: distinguish.induct)
  defer
  apply simp
  apply simp
  apply simp
  apply simp
  apply simp
  apply (metis BDD.simps(5) dist_none_nothing distinguish.simps(6) join_dist_none)
  apply (metis dist_none_top)
  apply (metis dist_comm dist_none_nothing)
  apply (metis dist_comm dist_none_top)
  apply (insert norm_ord)
  (* vb < va *)
  apply (case_tac "vb < va")
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) distinguish.simps(1) join_dist_none norm.simps)
  (* vb = va *)
  apply (case_tac "vb = va")
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) distinguish.simps(1) join_dist_none norm.simps)
  (* vb > va *)
  apply (metis BDD.distinct(6) BDD.inject BDD.simps(5) distinguish.simps(1) join_dist_none norm.cases norm_widen)
  done

theorem dup_free_unique: "\<lbrakk>norm n a; norm n b\<rbrakk> \<Longrightarrow> (\<forall>f. contains a f = contains b f) = (a = b)"
  by (meson dist_none_unique equiv_dist_none norm_ord)

end