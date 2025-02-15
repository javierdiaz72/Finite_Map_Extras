section \<open> Extra Features for Finite Maps \<close>

theory Finite_Map_Extras
  imports "HOL-Library.Finite_Map"
begin

text \<open> Extra lemmas and syntactic sugar for \<open>fmap\<close> \<close>

notation fmlookup (infixl \<open>$$\<close> 900)

notation fmempty (\<open>{$$}\<close>)

nonterminal fmaplets and fmaplet

syntax
  "_fmaplet"  :: "['a, 'a] \<Rightarrow> fmaplet"                        ("_ /$$:=/ _")
  "_fmaplets" :: "['a, 'a] \<Rightarrow> fmaplet"                        ("_ /[$$:=]/ _")
  ""          :: "fmaplet \<Rightarrow> fmaplets"                        ("_")
  "_Fmaplets" :: "[fmaplet, fmaplets] \<Rightarrow> fmaplets"            ("_,/ _")
  "_FmapUpd"  :: "[('a, 'b) fmap, fmaplets] \<Rightarrow> ('a, 'b) fmap" ("_/'(_')" [900, 0] 900)
  "_Fmap"     :: "fmaplets \<Rightarrow> ('a, 'b) fmap"                  ("(1{_})")

translations
  "_FmapUpd m (_Fmaplets xy ms)"  \<rightleftharpoons> "_FmapUpd (_FmapUpd m xy) ms"
  "_FmapUpd m (_fmaplet  x y)"    \<rightleftharpoons> "CONST fmupd x y m"
  "_Fmap ms"                     \<rightleftharpoons> "_FmapUpd (CONST fmempty) ms"
  "_Fmap (_Fmaplets ms1 ms2)"     \<leftharpoondown> "_FmapUpd (_Fmap ms1) ms2"
  "_Fmaplets ms1 (_Fmaplets ms2 ms3)" \<leftharpoondown> "_Fmaplets (_Fmaplets ms1 ms2) ms3"

abbreviation fmap_lookup_the (infixl \<open>$$!\<close> 900) where
  "m $$! k \<equiv> the (m $$ k)"

lemma fmadd_singletons_comm:
  assumes "k\<^sub>1 \<noteq> k\<^sub>2"
  shows "{k\<^sub>1 $$:= v\<^sub>1} ++\<^sub>f {k\<^sub>2 $$:= v\<^sub>2} = {k\<^sub>2 $$:= v\<^sub>2} ++\<^sub>f {k\<^sub>1 $$:= v\<^sub>1}"
proof (intro fmap_ext)
  fix k
  consider
    (a) "k = k\<^sub>1" |
    (b) "k = k\<^sub>2" |
    (c) "k \<noteq> k\<^sub>1 \<and> k \<noteq> k\<^sub>2"
    by auto
  with assms show "({k\<^sub>1 $$:= v\<^sub>1} ++\<^sub>f {k\<^sub>2 $$:= v\<^sub>2}) $$ k = ({k\<^sub>2 $$:= v\<^sub>2} ++\<^sub>f {k\<^sub>1 $$:= v\<^sub>1}) $$ k"
    by auto
qed

lemma fmap_singleton_comm:
  assumes "m $$ k = None"
  shows "m ++\<^sub>f {k $$:= v} = {k $$:= v} ++\<^sub>f m"
  using assms
proof (induction m arbitrary: k v)
  case fmempty
  then show ?case
    by simp
next
  case (fmupd x y m)
  have "m(x $$:= y) ++\<^sub>f {k $$:= v} = m ++\<^sub>f {x $$:= y} ++\<^sub>f {k $$:= v}"
    by simp
  also from fmupd.hyps and fmupd.IH have "\<dots> = {x $$:= y} ++\<^sub>f m ++\<^sub>f {k $$:= v}"
    by simp
  also from fmupd.prems and fmupd.hyps and fmupd.IH have "\<dots> = {x $$:= y} ++\<^sub>f {k $$:= v} ++\<^sub>f m"
    by (metis fmadd_assoc fmupd_lookup)
  also have "\<dots> = {k $$:= v} ++\<^sub>f m(x $$:= y)"
  proof (cases "x \<noteq> k")
    case True
    then have "{x $$:= y} ++\<^sub>f {k $$:= v} ++\<^sub>f m = {k $$:= v} ++\<^sub>f {x $$:= y} ++\<^sub>f m"
      using fmadd_singletons_comm by metis
    also from fmupd.prems and fmupd.hyps and fmupd.IH have "\<dots> = {k $$:= v} ++\<^sub>f m ++\<^sub>f {x $$:= y}"
      by (metis fmadd_assoc)
    finally show ?thesis
      by simp
  next
    case False
    with fmupd.prems show ?thesis
      by auto
  qed
  finally show ?case .
qed

lemma fmap_disj_comm:
  assumes "fmdom' m\<^sub>1 \<inter> fmdom' m\<^sub>2 = {}"
  shows "m\<^sub>1 ++\<^sub>f m\<^sub>2 = m\<^sub>2 ++\<^sub>f m\<^sub>1"
  using assms
proof (induction m\<^sub>2 arbitrary: m\<^sub>1)
  case fmempty
  then show ?case
    by simp
next
  case (fmupd k v m\<^sub>2)
  then show ?case
  proof (cases "m\<^sub>1 $$ k = None")
    case True
    from fmupd.hyps have "m\<^sub>1 ++\<^sub>f m\<^sub>2(k $$:= v) = m\<^sub>1 ++\<^sub>f m\<^sub>2 ++\<^sub>f {k $$:= v}"
      by simp
    also from fmupd.prems and fmupd.hyps and fmupd.IH have "\<dots> = m\<^sub>2 ++\<^sub>f m\<^sub>1 ++\<^sub>f {k $$:= v}"
      by simp
    also from True have "\<dots> = m\<^sub>2 ++\<^sub>f {k $$:= v} ++\<^sub>f m\<^sub>1"
      using fmap_singleton_comm by (metis fmadd_assoc)
    finally show ?thesis
      by simp
  next
    case False
    with fmupd.prems show ?thesis
      by auto
  qed
qed

lemma fmran_singleton: "fmran {k $$:= v} = {|v|}"
proof -
  have "v' |\<in>| fmran {k $$:= v} \<Longrightarrow> v' = v" for v'
  proof -
    assume "v' |\<in>| fmran {k $$:= v}"
    fix k'
    have "fmdom' {k $$:= v} = {k}"
      by simp
    then show "v' = v"
    proof (cases "k' = k")
      case True
      with \<open>v' |\<in>| fmran {k $$:= v}\<close> show ?thesis
        using fmdom'I by fastforce
    next
      case False
      with \<open>fmdom' {k $$:= v} = {k}\<close> and \<open>v' |\<in>| fmran {k $$:= v}\<close> show ?thesis
        using fmdom'I by fastforce
    qed
  qed
  moreover have "v |\<in>| fmran {k $$:= v}"
    by (simp add: fmranI)
  ultimately show ?thesis
    by (simp add: fsubsetI fsubset_antisym)
qed

lemma fmmap_keys_hom:
  assumes "fmdom' m\<^sub>1 \<inter> fmdom' m\<^sub>2 = {}"
  shows "fmmap_keys f (m\<^sub>1 ++\<^sub>f m\<^sub>2) = fmmap_keys f m\<^sub>1 ++\<^sub>f fmmap_keys f m\<^sub>2"
  using assms
  by (simp add: fmap_ext)

lemma map_insort_is_insort_key:
  assumes "m $$ k = None"
  shows "map (\<lambda>k'. (k', m(k $$:= v) $$! k')) (insort k xs) =
    insort_key fst (k, v) (map (\<lambda>k'. (k', m(k $$:= v) $$! k')) xs)"
  using assms by (induction xs) auto

lemma sorted_list_of_fmap_is_insort_key_fst:
  assumes "m $$ k = None"
  shows "sorted_list_of_fmap (m(k $$:= v)) = insort_key fst (k, v) (sorted_list_of_fmap m)"
proof -
  have "sorted_list_of_fmap (m(k $$:= v)) =
    map (\<lambda>k'. (k', m(k $$:= v) $$! k')) (sorted_list_of_fset (fmdom (m(k $$:= v))))"
    unfolding sorted_list_of_fmap_def ..
  also have "\<dots> = 	map (\<lambda>k'. (k', m(k $$:= v) $$! k')) (sorted_list_of_fset (finsert k (fmdom m)))"
    by simp
  also from \<open>m $$ k = None\<close> have "\<dots> =
    map (\<lambda>k'. (k', m(k $$:= v) $$! k')) (insort k (sorted_list_of_fset (fmdom m - {|k|})))"
    by (simp add: sorted_list_of_fset.rep_eq)
  also from \<open>m $$ k = None\<close> have "\<dots> =
    map (\<lambda>k'. (k', m(k $$:= v) $$! k')) (insort k (sorted_list_of_fset (fmdom m)))"
    by (simp add: fmdom_notI)
  also from \<open>m $$ k = None\<close> have "\<dots> =
    insort_key fst (k, v) (map (\<lambda>k'. (k', m(k $$:= v) $$! k')) (sorted_list_of_fset (fmdom m)))"
    using map_insort_is_insort_key by fastforce
  also have "\<dots> = insort_key fst (k, v) (map (\<lambda>k'. (k', m $$! k')) (sorted_list_of_fset (fmdom m)))"
  proof -
    from \<open>m $$ k = None\<close> have "\<And>k'. k' \<in> fmdom' m \<Longrightarrow> m(k $$:= v) $$! k' = m $$! k'"
      using fmdom'_notI by force
    moreover from \<open>m $$ k = None\<close> have "k \<notin> set (sorted_list_of_fset (fmdom m))"
      using fmdom'_alt_def and fmdom'_notI and in_set_member by force
    ultimately show ?thesis
      by (metis (mono_tags, lifting) fmdom'_alt_def map_eq_conv sorted_list_of_fset_simps(1))
  qed
  finally show ?thesis
    unfolding sorted_list_of_fmap_def by simp
qed

lemma distinct_fst_inj:
  assumes "distinct (map fst ps)"
  and "inj f"
  shows "distinct (map fst (map (\<lambda>(k, v). (f k, v)) ps))"
proof -
  have "map fst (map (\<lambda>(k, v). (f k, v)) ps) = map f (map fst ps)"
    by (induction ps) auto
  moreover from assms have "distinct (map f (map fst ps))"
    by (simp add: distinct_map inj_on_def)
  ultimately show ?thesis
    by presburger
qed

lemma distinct_sorted_list_of_fmap:
  shows "distinct (map fst (sorted_list_of_fmap m))"
  unfolding sorted_list_of_fmap_def and sorted_list_of_fset_def
  by (simp add: distinct_map inj_on_def)

lemma map_inj_pair_non_membership:
  assumes "k \<notin> set (map fst ps)"
  and "inj f"
  shows "f k \<notin> set (map fst (map (\<lambda>(k, v). (f k, v)) ps))"
  using assms by (induction ps) (simp add: member_rec(2), fastforce simp add: injD)

lemma map_insort_key_fst:
  assumes "distinct (map fst ps)"
  and "k \<notin> set (map fst ps)"
  and "inj f"
  and "mono f"
  shows "map (\<lambda>(k, v). (f k, v)) (insort_key fst (k, v) ps) =
    insort_key fst (f k, v) (map (\<lambda>(k, v). (f k, v)) ps)"
  using assms
proof (induction ps)
  case Nil
  then show ?case
    by simp
next
  let ?g = "(\<lambda>(k, v). (f k, v))"
  case (Cons p ps)
  then show ?case
  proof (cases "k \<le> fst p")
    case True
    let ?f_p = "(f (fst p), snd p)"
    have "insort_key fst (f k, v) (map ?g (p # ps)) = insort_key fst (f k, v) (?f_p # map ?g ps)"
      by (simp add: prod.case_eq_if)
    moreover from Cons.prems(4) and True have "f k \<le> f (fst p)"
      by (auto dest: monoE)
    then have "insort_key fst (f k, v) (?f_p # map ?g ps) = (f k, v) # ?f_p # map ?g ps"
      by simp
    ultimately have "insort_key fst (f k, v) (map ?g (p # ps)) = (f k, v) # ?f_p # map ?g ps"
      by simp
    moreover from True have "map ?g (insort_key fst (k, v) (p # ps)) = (f k, v) # ?f_p # map ?g ps"
      by (simp add: case_prod_beta')
    ultimately show ?thesis
      by simp
  next
    case False
    let ?f_p = "(f (fst p), snd p)"
    have "insort_key fst (f k, v) (map ?g (p # ps)) = insort_key fst (f k, v) (?f_p # map ?g ps)"
      by (simp add: prod.case_eq_if)
    moreover from \<open>mono f\<close> and False have "f (fst p) \<le> f k"
      using not_le by (blast dest: mono_invE)
    ultimately have "insort_key fst (f k, v) (map ?g (p # ps)) =
      ?f_p # insort_key fst (f k, v) (map ?g ps)"
      using False and \<open>inj f\<close> by (fastforce dest: injD)
    also from Cons.IH and Cons.prems(1,2) and assms(3,4) have "\<dots> =
      ?f_p # (map ?g (insort_key fst (k, v) ps))"
      by (fastforce simp add: member_rec(1))
    also have "\<dots> = map ?g (p # insort_key fst (k, v) ps)"
      by (simp add: case_prod_beta)
    finally show ?thesis
      using False by simp
  qed
qed

lemma map_sorted_list_of_fmap:
  assumes "inj f"
  and "mono f"
  and "m $$ k = None"
  shows "map (\<lambda>(k, v). (f k, v)) (sorted_list_of_fmap (m(k $$:= v))) =
    insort_key fst (f k, v) (map (\<lambda>(k, v). (f k, v)) (sorted_list_of_fmap m))"
proof -
  let ?g = "(\<lambda>(k, v). (f k, v))"
  from \<open>m $$ k = None\<close> have "map ?g (sorted_list_of_fmap (m(k $$:= v))) =
  	map ?g (insort_key fst (k, v) (sorted_list_of_fmap m))"
  	using sorted_list_of_fmap_is_insort_key_fst by fastforce
  also have "\<dots> = insort_key fst (f k, v) (map ?g (sorted_list_of_fmap m))"
  proof -
    have "distinct (map fst (sorted_list_of_fmap m))"
      by (simp add: distinct_sorted_list_of_fmap)
    moreover from \<open>m $$ k = None\<close> have "k \<notin> set (map fst (sorted_list_of_fmap m))"
      by (metis image_set map_of_eq_None_iff map_of_sorted_list)
    ultimately show ?thesis
      by (simp add: map_insort_key_fst assms(1,2))
  qed
  finally show ?thesis .
qed

lemma fmap_of_list_insort_key_fst:
  assumes "distinct (map fst ps)"
  and "k \<notin> set (map fst ps)"
  shows "fmap_of_list (insort_key fst (k, v) ps) = (fmap_of_list ps)(k $$:= v)"
  using assms
proof (induction ps)
  case Nil
  then show ?case
    by simp
next
  case (Cons p ps)
  then show ?case
  proof (cases "k \<le> fst p")
    case True
    then show ?thesis
      by simp
  next
    case False
    then have "fmap_of_list (insort_key fst (k, v) (p # ps)) =
      fmap_of_list (p # insort_key fst (k, v) ps)"
      by simp
    also have "\<dots> = (fmap_of_list (insort_key fst (k, v) ps))(fst p $$:= snd p)"
      by (metis fmap_of_list_simps(2) prod.collapse)
    also from Cons.prems(1,2) and Cons.IH have "\<dots> = (fmap_of_list ps)(k $$:= v)(fst p $$:= snd p)"
      by (fastforce simp add: member_rec(1))
    finally show ?thesis
    proof -
      assume *: "fmap_of_list (insort_key fst (k, v) (p # ps)) =
        (fmap_of_list ps)(k $$:= v)(fst p $$:= snd p)"
      from Cons.prems(2) have "k \<notin> set (fst p # map fst ps)"
        by simp
      then have **: "{k $$:= v} $$ (fst p) = None"
        by (fastforce simp add: member_rec(1))
      have "fmap_of_list (p # ps) = (fmap_of_list ps)(fst p $$:= snd p)"
        by (metis fmap_of_list_simps(2) prod.collapse)
      with * and ** show ?thesis
        using fmap_singleton_comm by (metis fmadd_fmupd fmap_of_list_simps(1,2) fmupd_alt_def)
    qed
  qed
qed

lemma fmap_of_list_insort_key_fst_map:
  assumes "inj f"
  and "m $$ k = None"
  shows "fmap_of_list (insort_key fst (f k, v) (map (\<lambda>(k, v). (f k, v)) (sorted_list_of_fmap m))) =
    (fmap_of_list (map (\<lambda>(k, v). (f k, v)) (sorted_list_of_fmap m)))(f k $$:= v)"
proof -
  let ?g = "\<lambda>(k, v). (f k, v)"
  let ?ps = "map ?g (sorted_list_of_fmap m)"
  from \<open>inj f\<close> have "distinct (map fst ?ps)"
    using distinct_fst_inj and distinct_sorted_list_of_fmap by fastforce
  moreover have "f k \<notin> set (map fst ?ps)"
  proof -
    from \<open>m $$ k = None\<close> have "k \<notin> set (map fst (sorted_list_of_fmap m))"
      by (metis map_of_eq_None_iff map_of_sorted_list set_map)
    with \<open>inj f\<close> show ?thesis
      using map_inj_pair_non_membership by force
  qed
  ultimately show ?thesis
    using fmap_of_list_insort_key_fst by fast
qed

lemma fmap_of_list_sorted_list_of_fmap:
  fixes m :: "('a::linorder, 'b) fmap"
  and f :: "'a \<Rightarrow> 'c::linorder"
  assumes "inj f"
  and "mono f"
  and "m $$ k = None"
  shows "fmap_of_list (map (\<lambda>(k, v). (f k, v)) (sorted_list_of_fmap (m(k $$:= v)))) =
    (fmap_of_list (map (\<lambda>(k, v). (f k, v)) (sorted_list_of_fmap m)))(f k $$:= v)"
proof -
  let ?g = "\<lambda>(k, v). (f k, v)"
  from assms(3) have "fmap_of_list (map ?g (sorted_list_of_fmap (m(k $$:= v)))) =
    fmap_of_list (map ?g (insort_key fst (k, v) (sorted_list_of_fmap m)))"
    by (simp add: sorted_list_of_fmap_is_insort_key_fst)
  also from assms have "\<dots> = fmap_of_list (insort_key fst (f k, v) (map ?g (sorted_list_of_fmap m)))"
    using calculation and map_sorted_list_of_fmap by fastforce
  also from assms(1,3) have "\<dots> = (fmap_of_list (map ?g (sorted_list_of_fmap m)))(f k $$:= v)"
    by (simp add: fmap_of_list_insort_key_fst_map)
  finally show ?thesis .
qed

text \<open> Map difference \<close>

lemma fsubset_antisym:
  assumes "m \<subseteq>\<^sub>f n"
  and "n \<subseteq>\<^sub>f m"
  shows "m = n"
proof -
  from \<open>m \<subseteq>\<^sub>f n\<close> have "\<forall>k \<in> dom (($$) m). (($$) m) k = (($$) n) k"
    by (simp add: fmsubset.rep_eq map_le_def)
  moreover from \<open>n \<subseteq>\<^sub>f m\<close> have "\<forall>k \<in> dom (($$) n). (($$) n) k = (($$) m) k"
    by (simp add: fmsubset.rep_eq map_le_def)
  ultimately show ?thesis
  proof (intro fmap_ext)
    fix k
    consider
      (a) "k \<in> dom (($$) m)" |
      (b) "k \<in> dom (($$) n)" |
      (c) "k \<notin> dom (($$) m) \<and> k \<notin> dom (($$) n)"
      by auto
    then show "m $$ k = n $$ k"
    proof cases
      case a
      with \<open>\<forall>k \<in> dom (($$) m). m $$ k = n $$ k\<close> show ?thesis
        by simp
    next
      case b
      with \<open>\<forall>k \<in> dom (($$) n). n $$ k = m $$ k\<close> show ?thesis
        by simp
    next
      case c
      then show ?thesis
        by (simp add: fmdom'_notD)
    qed
  qed
qed

abbreviation
  fmdiff :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" (infixl \<open>--\<^sub>f\<close> 100) where
  "m\<^sub>1 --\<^sub>f m\<^sub>2 \<equiv> fmfilter (\<lambda>x. x \<notin> fmdom' m\<^sub>2) m\<^sub>1"

lemma fmdiff_partition:
  assumes "m\<^sub>2 \<subseteq>\<^sub>f m\<^sub>1"
  shows "m\<^sub>2 ++\<^sub>f (m\<^sub>1 --\<^sub>f m\<^sub>2) = m\<^sub>1"
proof -
  have *: "m\<^sub>2 ++\<^sub>f (m\<^sub>1 --\<^sub>f m\<^sub>2) \<subseteq>\<^sub>f m\<^sub>1"
  proof -
    have "\<forall>k v. (m\<^sub>2 ++\<^sub>f (m\<^sub>1 --\<^sub>f m\<^sub>2)) $$ k = Some v \<longrightarrow> m\<^sub>1 $$ k = Some v"
    proof (intro allI impI)
      fix k v
      assume "(m\<^sub>2 ++\<^sub>f (m\<^sub>1 --\<^sub>f m\<^sub>2)) $$ k = Some v"
      then have **: "(if k |\<in>| fmdom (m\<^sub>1 --\<^sub>f m\<^sub>2) then (m\<^sub>1 --\<^sub>f m\<^sub>2) $$ k else m\<^sub>2 $$ k) = Some v"
        by simp
      then show "m\<^sub>1 $$ k = Some v"
      proof (cases "k |\<in>| fmdom (m\<^sub>1 --\<^sub>f m\<^sub>2)")
        case True
        with ** show ?thesis
          by simp
      next
        case False
        with ** and \<open>m\<^sub>2 \<subseteq>\<^sub>f m\<^sub>1\<close> show ?thesis
          by (metis (mono_tags, lifting) fmpredD fmsubset_alt_def)
      qed
    qed
    then have "fmpred (\<lambda>k v. m\<^sub>1 $$ k = Some v) (m\<^sub>2 ++\<^sub>f (m\<^sub>1 --\<^sub>f m\<^sub>2))"
      by (blast intro: fmpred_iff)
    then show ?thesis
      by (auto simp add: fmsubset_alt_def)
  qed
  then have "m\<^sub>1 \<subseteq>\<^sub>f m\<^sub>2 ++\<^sub>f (m\<^sub>1 --\<^sub>f m\<^sub>2)"
    by (simp add: fmsubset.rep_eq map_le_def)
  with * show ?thesis
    by (simp add: fsubset_antisym)
qed

lemma fmdiff_fmupd:
  assumes "m $$ k = None"
  shows "m(k $$:= v) --\<^sub>f {k $$:= v} = m"
proof -
  let ?P = "(\<lambda>k'. k' \<notin> {k})"
  have "m(k $$:= v) --\<^sub>f {k $$:= v} = fmfilter (\<lambda>x. x \<notin> fmdom' {k $$:= v}) (m(k $$:= v))" ..
  also have "\<dots> = fmfilter ?P (m(k $$:= v))"
    by simp
  also have "\<dots> = (if ?P k then (fmfilter ?P m)(k $$:= v) else fmfilter ?P m)"
    by simp
  also have "\<dots> = fmfilter ?P m"
    by simp
  finally show ?thesis
  proof -
    from \<open>m $$ k = None\<close> have "\<And>k' v'. m $$ k' = Some v' \<Longrightarrow> ?P k'"
      by fastforce
    then show ?thesis
      by simp
  qed
qed

text \<open> Map symmetric difference \<close>

abbreviation fmsym_diff :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" (infixl \<open>\<Delta>\<^sub>f\<close> 100) where
  "m\<^sub>1 \<Delta>\<^sub>f m\<^sub>2 \<equiv> (m\<^sub>1 --\<^sub>f m\<^sub>2) ++\<^sub>f (m\<^sub>2 --\<^sub>f m\<^sub>1)"

text \<open> Domain restriction \<close>

abbreviation dom_res :: "'a set \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" (infixl \<open>\<lhd>\<close> 150) where
  "s \<lhd> m \<equiv> fmfilter (\<lambda>x. x \<in> s) m"

text \<open> Domain exclusion \<close>

abbreviation dom_exc :: "'a set \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" (infixl \<open>\<lhd>'/\<close> 150) where
  "s \<lhd>/ m \<equiv> fmfilter (\<lambda>x. x \<notin> s) m"

text \<open> Intersection plus \<close>

abbreviation intersection_plus :: "('a, 'b::monoid_add) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  (infixl \<open>\<inter>\<^sub>+\<close> 100)
where
  "m\<^sub>1 \<inter>\<^sub>+ m\<^sub>2 \<equiv> fmmap_keys (\<lambda>k v. v + m\<^sub>1 $$! k) (fmdom' m\<^sub>1 \<lhd> m\<^sub>2)"

text \<open> Union override right \<close>

abbreviation union_override_right :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  (infixl \<open>\<union>\<^sub>\<rightarrow>\<close> 100)
where
  "m\<^sub>1 \<union>\<^sub>\<rightarrow> m\<^sub>2 \<equiv> (fmdom' m\<^sub>2 \<lhd>/ m\<^sub>1) ++\<^sub>f m\<^sub>2"

text \<open> Union override left \<close>

abbreviation union_override_left :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  (infixl \<open>\<union>\<^sub>\<leftarrow>\<close> 100)
where
  "m\<^sub>1 \<union>\<^sub>\<leftarrow> m\<^sub>2 \<equiv> m\<^sub>1 ++\<^sub>f (fmdom' m\<^sub>1 \<lhd>/ m\<^sub>2)"

text \<open> Union override plus \<close>

abbreviation union_override_plus :: "('a, 'b::monoid_add) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  (infixl \<open>\<union>\<^sub>+\<close> 100)
where
  "m\<^sub>1 \<union>\<^sub>+ m\<^sub>2 \<equiv> (m\<^sub>1 \<Delta>\<^sub>f m\<^sub>2) ++\<^sub>f (m\<^sub>1 \<inter>\<^sub>+ m\<^sub>2)"

text \<open> Extra lemmas for the non-standard map operators \<close>

lemma dom_res_singleton:
  assumes "m $$ k = Some v"
  shows "{k} \<lhd> m = {k $$:= v}"
  using assms
proof (induction m)
  case fmempty
  then show ?case
    by simp
next
  case (fmupd k' v' m)
  then show ?case
  proof (cases "k = k'")
    case True
    with \<open>m(k' $$:= v') $$ k = Some v\<close> have "v = v'"
      by simp
    with True have "{k} \<lhd> m(k' $$:= v') = ({k} \<lhd> m)(k $$:= v)"
      by simp
    also from True and \<open>m $$ k' = None\<close> have "\<dots> = {$$}(k $$:= v)"
      by (simp add: fmap_ext)
    finally show ?thesis
      by simp
  next
    case False
    with \<open>m(k' $$:= v') $$ k = Some v\<close> have *: "m $$ k = Some v"
      by simp
    with False have "{k} \<lhd> m(k' $$:= v') = {k} \<lhd> m"
      by simp
    with * and fmupd.IH show ?thesis
      by simp
  qed
qed

lemma dom_res_union_distr:
  shows "(A \<union> B) \<lhd> m = A \<lhd> m ++\<^sub>f B \<lhd> m"
proof -
  have "($$) ((A \<union> B) \<lhd> m) \<subseteq>\<^sub>m ($$) (A \<lhd> m ++\<^sub>f B \<lhd> m)"
  proof (unfold map_le_def, intro ballI)
    fix k
    assume "k \<in> dom (($$) ((A \<union> B) \<lhd> m))"
    then show "((A \<union> B) \<lhd> m) $$ k = (A \<lhd> m ++\<^sub>f B \<lhd> m) $$ k"
      by auto
  qed
  moreover have "($$) (A \<lhd> m ++\<^sub>f B \<lhd> m) \<subseteq>\<^sub>m ($$) ((A \<union> B) \<lhd> m)"
  proof (unfold map_le_def, intro ballI)
    fix k
    assume "k \<in> dom (($$) (A \<lhd> m ++\<^sub>f B \<lhd> m))"
    then show "(A \<lhd> m ++\<^sub>f B \<lhd> m) $$ k = ((A \<union> B) \<lhd> m) $$ k"
      by auto
  qed
  ultimately show ?thesis
    using fmlookup_inject and map_le_antisym by blast
qed

lemma dom_exc_add_distr:
  shows "s \<lhd>/ (m\<^sub>1 ++\<^sub>f m\<^sub>2) = (s \<lhd>/ m\<^sub>1) ++\<^sub>f (s \<lhd>/ m\<^sub>2)"
  by (blast intro: fmfilter_add_distrib)

lemma fmap_partition:
  shows "m = s \<lhd>/ m ++\<^sub>f s \<lhd> m"
proof (induction m)
  case fmempty
  then show ?case
    by simp
next
  case (fmupd k v m)
  from fmupd.hyps have "s \<lhd>/ m(k $$:= v) ++\<^sub>f s \<lhd> m(k $$:= v) =
    s \<lhd>/ (m ++\<^sub>f {k $$:= v}) ++\<^sub>f s \<lhd> (m ++\<^sub>f {k $$:= v})"
    by simp
  also have "\<dots> = s \<lhd>/ m ++\<^sub>f s \<lhd>/ {k $$:= v} ++\<^sub>f s \<lhd> m ++\<^sub>f s \<lhd> {k $$:= v}"
    using dom_exc_add_distr by simp
  finally show ?case
  proof (cases "k \<in> s")
    case True
    then have "s \<lhd>/ m ++\<^sub>f s \<lhd>/ {k $$:= v} ++\<^sub>f s \<lhd> m ++\<^sub>f s \<lhd> {k $$:= v} =
      s \<lhd>/ m ++\<^sub>f {$$} ++\<^sub>f s \<lhd> m ++\<^sub>f {k $$:= v}"
      by simp
    also have "\<dots> = s \<lhd>/ m ++\<^sub>f s \<lhd> m ++\<^sub>f {k $$:= v}"
      by simp
    also from fmupd.IH have "\<dots> = m ++\<^sub>f {k $$:= v}"
      by simp
    finally show ?thesis using fmupd.hyps
      by auto
  next
    case False
    then have "s \<lhd>/ m ++\<^sub>f s \<lhd>/ {k $$:= v} ++\<^sub>f s \<lhd> m ++\<^sub>f s \<lhd> {k $$:= v} =
      s \<lhd>/ m ++\<^sub>f {k $$:= v} ++\<^sub>f s \<lhd> m ++\<^sub>f {$$}"
      by simp
    also have "\<dots> = s \<lhd>/ m ++\<^sub>f {k $$:= v} ++\<^sub>f s \<lhd> m"
      by simp
    also from fmupd.hyps have "\<dots> = s \<lhd>/ m ++\<^sub>f s \<lhd> m ++\<^sub>f {k $$:= v}"
      using fmap_singleton_comm by (metis (full_types) fmadd_assoc fmlookup_filter)
    also from fmupd.IH have "\<dots> = m ++\<^sub>f {k $$:= v}"
      by simp
    finally show ?thesis
      by auto
  qed
qed

lemma dom_res_addition_in:
  assumes "m\<^sub>1 $$ k = None"
  and "m\<^sub>2 $$ k = Some v'"
  shows "fmdom' (m\<^sub>1(k $$:= v)) \<lhd> m\<^sub>2 = fmdom' m\<^sub>1 \<lhd> m\<^sub>2 ++\<^sub>f {k $$:= v'}"
proof -
  from \<open>m\<^sub>1 $$ k = None\<close> have "fmdom' (m\<^sub>1(k $$:= v)) \<lhd> m\<^sub>2 = (fmdom' m\<^sub>1 \<union> {k}) \<lhd> m\<^sub>2"
    by simp
  also have "\<dots> = fmdom' m\<^sub>1 \<lhd> m\<^sub>2 ++\<^sub>f {k} \<lhd> m\<^sub>2"
    using dom_res_union_distr .
  finally show ?thesis
    using \<open>m\<^sub>2 $$ k = Some v'\<close> and dom_res_singleton by fastforce
qed

lemma dom_res_addition_not_in:
  assumes "m\<^sub>2 $$ k = None"
  shows "fmdom' (m\<^sub>1(k $$:= v)) \<lhd> m\<^sub>2 = fmdom' m\<^sub>1 \<lhd> m\<^sub>2"
proof -
  have "fmdom' (m\<^sub>1(k $$:= v)) \<lhd> m\<^sub>2 = fmfilter (\<lambda>k'. k' = k \<or> k' \<in> fmdom' m\<^sub>1) m\<^sub>2"
    by simp
  also have "\<dots> = fmdom' m\<^sub>1 \<lhd> m\<^sub>2"
  proof (intro fmfilter_cong')
    show "m\<^sub>2 = m\<^sub>2" ..
  next
    from assms show "k' \<in> fmdom' m\<^sub>2 \<Longrightarrow> (k' = k \<or> k' \<in> fmdom' m\<^sub>1) = (k' \<in> fmdom' m\<^sub>1)" for k'
    by (cases "k' = k") (simp_all add: fmdom'_notI)
  qed
  finally show ?thesis .
qed

lemma inter_plus_addition_in:
  assumes "m\<^sub>1 $$ k = None"
  and "m\<^sub>2 $$ k = Some v'"
  shows "m\<^sub>1(k $$:= v) \<inter>\<^sub>+ m\<^sub>2 = (m\<^sub>1 \<inter>\<^sub>+ m\<^sub>2) ++\<^sub>f {k $$:= v' + v}"
proof -
  let ?f = "\<lambda>k' v'. v' + m\<^sub>1(k $$:= v) $$! k'"
  from assms have "m\<^sub>1(k $$:= v) \<inter>\<^sub>+ m\<^sub>2 = fmmap_keys ?f ((fmdom' m\<^sub>1 \<lhd> m\<^sub>2) ++\<^sub>f {k $$:= v'})"
    using dom_res_addition_in by fastforce
  also have "\<dots> = fmmap_keys ?f (fmdom' m\<^sub>1 \<lhd> m\<^sub>2) ++\<^sub>f fmmap_keys ?f {k $$:= v'}"
  proof -
    from \<open>m\<^sub>1 $$ k = None\<close> have "fmdom' (fmdom' m\<^sub>1 \<lhd> m\<^sub>2) \<inter> fmdom' {k $$:= v'} = {}"
      by (simp add: fmdom'_notI)
    then show ?thesis
      using fmmap_keys_hom by blast
  qed
  also from assms
  have "\<dots> = fmmap_keys ?f (fmdom' m\<^sub>1 \<lhd> m\<^sub>2) ++\<^sub>f {k $$:= v' + v}"
  proof -
    have "fmmap_keys ?f {k $$:= v'} = {k $$:= v' + v}"
    proof (intro fmap_ext)
      fix k'
      have "fmmap_keys ?f {k $$:= v'} $$ k' = map_option (?f k') ({k $$:= v'} $$ k')"
        using fmlookup_fmmap_keys .
      also have "\<dots> = map_option (?f k') (if k = k' then Some v' else {$$} $$ k')"
        by simp
      also have "\<dots> = {k $$:= v' + v} $$ k'"
        by (cases "k' = k") simp_all
      finally show "fmmap_keys ?f {k $$:= v'} $$ k' = {k $$:= v' + v} $$ k'" .
    qed
    then show ?thesis
      by simp
  qed
  also have "\<dots> = fmmap_keys (\<lambda>k' v'. v' + m\<^sub>1 $$! k') (fmdom' m\<^sub>1 \<lhd> m\<^sub>2) ++\<^sub>f {k $$:= v' + v}"
    by (simp add: fmap_ext)
  finally show ?thesis .
qed

lemma inter_plus_addition_notin:
  assumes "m\<^sub>1 $$ k = None"
  and "m\<^sub>2 $$ k = None"
  shows "m\<^sub>1(k $$:= v) \<inter>\<^sub>+ m\<^sub>2 = (m\<^sub>1 \<inter>\<^sub>+ m\<^sub>2)"
proof -
  let ?f = "\<lambda>k' v'. v' + m\<^sub>1(k $$:= v) $$! k'"
  from \<open>m\<^sub>2 $$ k = None\<close>
  have "m\<^sub>1(k $$:= v) \<inter>\<^sub>+ m\<^sub>2 = fmmap_keys ?f (fmdom' m\<^sub>1 \<lhd> m\<^sub>2)"
    using dom_res_addition_not_in by metis
  also have "\<dots> = fmmap_keys (\<lambda>k' v'. v' + m\<^sub>1 $$! k') (fmdom' m\<^sub>1 \<lhd> m\<^sub>2)"
  proof (intro fmap_ext)
    fix k'
    have "fmmap_keys ?f (fmdom' m\<^sub>1 \<lhd> m\<^sub>2) $$ k' = map_option (?f k') ((fmdom' m\<^sub>1 \<lhd> m\<^sub>2) $$ k')"
      using fmlookup_fmmap_keys .
    also from \<open>m\<^sub>1 $$ k = None\<close> have "\<dots> = fmmap_keys (\<lambda>k' v'. v' + m\<^sub>1 $$! k') (fmdom' m\<^sub>1 \<lhd> m\<^sub>2) $$ k'"
      by (cases "k' = k") (simp_all add: fmdom'_notI)
    finally show "fmmap_keys ?f (fmdom' m\<^sub>1 \<lhd> m\<^sub>2) $$ k' =
      fmmap_keys (\<lambda>k' v'. v' + m\<^sub>1 $$! k') (fmdom' m\<^sub>1 \<lhd> m\<^sub>2) $$ k'" .
  qed
  finally show ?thesis .
qed

lemma union_plus_addition_notin: (* TODO: Find nicer proofs for SMT calls. *)
  assumes "m\<^sub>1 $$ k = None"
  and "m\<^sub>2 $$ k = None"
  shows "m\<^sub>1(k $$:= v) \<union>\<^sub>+ m\<^sub>2 = (m\<^sub>1 \<union>\<^sub>+ m\<^sub>2) ++\<^sub>f {k $$:= v}"
proof -
  from \<open>m\<^sub>2 $$ k = None\<close> have "(m\<^sub>1(k $$:= v)) \<union>\<^sub>+ m\<^sub>2 =
    fmdom' m\<^sub>2 \<lhd>/ m\<^sub>1 ++\<^sub>f {k $$:= v} ++\<^sub>f fmdom' (m\<^sub>1(k $$:= v)) \<lhd>/ m\<^sub>2 ++\<^sub>f (m\<^sub>1(k $$:= v) \<inter>\<^sub>+ m\<^sub>2)"
    by (simp add: fmdom'_notI)
  also from assms have "\<dots> =
    fmdom' m\<^sub>2 \<lhd>/ m\<^sub>1 ++\<^sub>f {k $$:= v} ++\<^sub>f fmdom' m\<^sub>1 \<lhd>/ m\<^sub>2 ++\<^sub>f (m\<^sub>1(k $$:= v) \<inter>\<^sub>+ m\<^sub>2)"
    by (smt fmdom'_fmupd fmfilter_cong insert_iff option.distinct(1))
  also from assms have "\<dots> = fmdom' m\<^sub>2 \<lhd>/ m\<^sub>1 ++\<^sub>f {k $$:= v} ++\<^sub>f fmdom' m\<^sub>1 \<lhd>/ m\<^sub>2 ++\<^sub>f (m\<^sub>1 \<inter>\<^sub>+ m\<^sub>2)"
    using inter_plus_addition_notin by metis
  also from assms have "\<dots> = fmdom' m\<^sub>2 \<lhd>/ m\<^sub>1 ++\<^sub>f fmdom' m\<^sub>1 \<lhd>/ m\<^sub>2 ++\<^sub>f (m\<^sub>1 \<inter>\<^sub>+ m\<^sub>2) ++\<^sub>f {k $$:= v}"
    using fmap_singleton_comm
    by (smt fmadd_assoc fmfilter_fmmap_keys fmlookup_filter fmlookup_fmmap_keys)
  finally show ?thesis .
qed


definition map_id :: "'a set \<Rightarrow> ('a, 'a) map" where 
  "map_id D = (\<lambda>x. if x \<in> D then Some x else None)"

lemma map_id_simps[simp] : 
  "(map_id D x = None) = (x \<notin> D)"
  "(map_id D x = Some y) = (x = y \<and> y \<in> D)"
  "dom(map_id D) = D"
  "ran(map_id D) = D"
  unfolding map_id_def ran_def
  by auto (meson option.distinct(1))

context
  includes fmap.lifting
           fset.lifting
begin

lift_definition fmap_id :: "'a fset \<Rightarrow> ('a,'a) fmap"
is "map_id" by simp

lemma fmap_id_fmlookup : 
  "fmlookup (fmap_id d) x = (if x |\<in>| d then Some x else None)"
  by transfer' (simp add: map_id_def)

lemma fmap_id_fmlookup_simps[simp] :
  "x |\<in>| d \<Longrightarrow> fmlookup (fmap_id d) x = Some x"
  "x |\<notin>| d \<Longrightarrow> fmlookup (fmap_id d) x = None"
  by (simp_all add: fmap_id_fmlookup)

lemma fmap_id_simps[simp] : 
  "(fmlookup (fmap_id d) x = None) = (x |\<notin>| d)"
  "(fmlookup (fmap_id d) x = Some y) = (x = y \<and> y |\<in>| d)"
  "fmdom (fmap_id d) = d"
  "fmran (fmap_id d) = d"
  apply transfer apply simp
  apply transfer apply simp
  apply transfer apply simp
  apply transfer apply simp
done

lift_definition fminvimage :: "('a, 'b) fmap \<Rightarrow> 'b fset \<Rightarrow> 'a fset" is "\<lambda>m S. {a | a b. m a = Some b \<and> b \<in> S}"
subgoal for m S
  apply (rule finite_subset[where B = "dom m"])
  apply (auto simp: ran_def)
  done
  done

lemma fminvimage_empty[simp]: "fminvimage m fempty = fempty"
by transfer' auto

lemma fminvimage_subset_ran[simp]: "fminvimage m S |\<subseteq>| fmdom m"
by transfer' (auto simp: dom_def)

lemma fmimage_dom_subset: "fmdom m |\<subseteq>| S \<Longrightarrow> fmimage m S = fmran m"
by transfer' (auto simp: ran_def)

lemma fminvimage_ran_subset: "fmran m |\<subseteq>| S \<Longrightarrow> fminvimage m S = fmdom m"
  by transfer' (auto simp: ran_def)

lemma fminvimage_ran[simp]: "fminvimage m (fmran m) = fmdom m"
  by transfer' (auto simp: ran_def)

lemma fmlookup_invimage_iff : "\<And>y. (y |\<in>| fminvimage m S) = (\<exists>x. fmlookup m y = Some x \<and> x |\<in>| S)"
by transfer' simp

lemma fmran_fmcomp : "fmran (g \<circ>\<^sub>f f) = fmimage g (fmran f)"
  by transfer' (auto simp add: ran_def map_comp_Some_iff)

lemma fmdom_fmcomp : "fmdom (g \<circ>\<^sub>f f) = fminvimage f (fmdom g)"
  apply transfer' 
  apply (auto simp add: dom_def map_comp_Some_iff)
  done


lemma fmimage_image: "fmimage g (fmimage f S) = fmimage (g \<circ>\<^sub>f f) S"
  by (auto simp add: fset_eq_iff fmlookup_image_iff Option.bind_eq_Some_conv)

end

lemma fmcomp_ran_subset:
  assumes "fmran g |\<subseteq>| K"
  shows "fmran (g \<circ>\<^sub>f f) |\<subseteq>| K"
  using assms
  by (metis dual_order.trans fmimage_subset_ran fmran_fmcomp)

lemma fmcomp_ran_superset:
  assumes "fmran f = fmdom g"
  assumes "fmran g = K"
  shows "K |\<subseteq>| fmran (g \<circ>\<^sub>f f)"
  using assms
  by (simp add: fmran_fmcomp)

lemma fmcomp_ran_equiv:
  assumes \<open>fmran f = fmdom g\<close>
  shows \<open>fmran (g \<circ>\<^sub>f f) = fmran g\<close>
  by (simp add: assms fmran_fmcomp)


lemma comp_fmdom_preserve[simp]:
  assumes "fmran f = fmdom g" 
  shows "fmdom (g \<circ>\<^sub>f f) = fmdom f"
by (simp add: assms[symmetric] fmdom_fmcomp) 


context
  includes fmap.lifting
begin
lemma map_comp_assoc: "m1 \<circ>\<^sub>m (m2 \<circ>\<^sub>m m3) = m1 \<circ>\<^sub>m m2 \<circ>\<^sub>m m3" 
  by (auto simp: map_comp_def split: option.splits)

lemma fmap_comp_assoc: "m1 \<circ>\<^sub>f (m2 \<circ>\<^sub>f m3) = m1 \<circ>\<^sub>f m2 \<circ>\<^sub>f m3"
  using map_comp_assoc[transferred] .

end

lemma fmdom_comp_fmdom[simp]:
  \<open>fmdom f = V \<Longrightarrow> fmdom (g \<circ>\<^sub>f f) |\<subseteq>| V\<close>
  by fastforce

lemma fmdom_comp_fmdom2[simp]:
  \<open>fmran f |\<subseteq>| fmdom g \<Longrightarrow> fmdom (g \<circ>\<^sub>f f) = fmdom f\<close>
  using fin_mono fmdom_notD fmranI by fastforce

definition map_inj :: "('a, 'b) map \<Rightarrow> bool" where
 "map_inj m \<equiv> inj_on m (dom m)"

lemma map_inj_expand: 
  "map_inj m = (\<forall>x1 x2 y. m x1 = Some y \<and> m x2 = Some y \<longrightarrow> (x1 = x2))" 
  unfolding map_inj_def dom_def inj_on_def
  by auto

lemma map_injD[dest]:
  assumes \<open>map_inj m\<close>
  assumes \<open>x \<in> dom m\<close>
  assumes \<open>y \<in> dom m\<close>
  assumes \<open>m x = m y\<close>
  shows \<open>x = y\<close>
  using assms
  by (auto simp add: map_inj_def dest: inj_onD)

lemma map_injI[intro]:
  "(\<And>x y. x \<in> dom m \<Longrightarrow> y \<in> dom m \<Longrightarrow> m x = m y \<Longrightarrow> x = y) \<Longrightarrow> map_inj m"
  by (simp add: domI map_inj_expand)

lemma map_inj_compI[intro]:
  assumes \<open>map_inj f\<close>
  assumes \<open>map_inj g\<close>
  shows \<open>map_inj (g \<circ>\<^sub>m f)\<close>
  using assms
  by (auto simp add: map_inj_def inj_on_def map_comp_def domI split: option.splits)

lemma map_inj_comp_f_inj:
  assumes \<open>map_inj (g \<circ>\<^sub>m f)\<close>
  assumes \<open>ran f \<subseteq> dom g\<close>
  shows \<open>map_inj f\<close>
  using assms
  unfolding map_inj_expand
  unfolding ran_def dom_def subset_iff
  by auto

lemma map_eq_induct[consumes 0, case_names NotInDom InDom]:
  "\<lbrakk>(\<And>x. m1 x = None \<Longrightarrow> m2 x = None); (\<And>x y. m1 x = Some y \<Longrightarrow> m2 x = Some y)\<rbrakk> \<Longrightarrow> (m1 = m2)"
  by (metis option.exhaust fun_eq_iff)

lemma fmap_eq_induct[consumes 0, case_names NotInDom InDom]:
  "\<And>fm1 fm2. (\<And>x. fmlookup fm1 x = None \<Longrightarrow> fmlookup fm2 x = None) \<Longrightarrow> (\<And>x y. fmlookup fm1 x = Some y \<Longrightarrow> fmlookup fm2 x = Some y) \<Longrightarrow> (fm1 = fm2)"
  by (metis option.exhaust fmap_ext)


context
  includes fmap.lifting fset.lifting
begin

lift_definition fmap_inj :: "('a,'b) fmap \<Rightarrow> bool"
is "map_inj" .

lemma fmap_injE[elim]:
  fixes x y g
  assumes \<open>fmap_inj g\<close>
  assumes \<open>x |\<in>| fmdom g\<close>
  assumes \<open>y |\<in>| fmdom g\<close>
  assumes \<open>fmlookup g x = fmlookup g y\<close>
  shows \<open>x = y\<close>
  using assms
  by transfer' (simp add: assms map_inj_def inj_onD)
 
lemma fmap_injI[intro]:
  assumes \<open>\<And>x y. x |\<in>| fmdom g \<Longrightarrow> y |\<in>| fmdom g \<Longrightarrow> fmlookup g x = fmlookup g y \<Longrightarrow> x = y\<close>
  shows \<open>fmap_inj g\<close>
  using assms
  by transfer' auto

lemma fmap_inj_spec : 
  "fmap_inj f = (\<forall>x y. x |\<in>| fmdom f \<longrightarrow> y |\<in>| fmdom f \<longrightarrow> fmlookup f x = fmlookup f y \<longrightarrow> (x = y))"
  by (metis fmap_injE fmap_injI)

lemma fmap_inj_eq_some_simp [simp] : 
  "fmap_inj f \<Longrightarrow> fmlookup f x = Some v \<Longrightarrow> ((fmlookup f y = Some v) = (y = x))"
  by (auto simp add: fmap_inj_spec iff: fmlookup_dom_iff)


lemma fmap_inj_compI[intro]:
  assumes \<open>fmap_inj f\<close>
  assumes \<open>fmap_inj g\<close>
  shows \<open>fmap_inj (g \<circ>\<^sub>f f)\<close>
  using assms
  by transfer' (intro map_inj_compI)

lemma fmap_inj_comp_f_inj:
  assumes \<open>fmap_inj (g \<circ>\<^sub>f f)\<close>
  assumes \<open>fmran f |\<subseteq>| fmdom g\<close>
  shows \<open>fmap_inj f\<close>
  using assms
  by transfer' (fact map_inj_comp_f_inj)

lemma fmap_inj_id : "fmap_inj (fmap_id d)"
  by (intro fmap_injI) simp

lemma map_comp_eq_None_iff : "((f \<circ>\<^sub>m g) x = None) = (g x = None \<or> (\<forall>y. g x = Some y \<longrightarrow> f y = None))"
proof (cases "g x")
  case None
  then show ?thesis 
    unfolding map_comp_def
    by simp
next
  case (Some y)
  then show ?thesis
    unfolding map_comp_def
    by simp
qed
  
lemma map_comp_eq_Some_iff : "((f \<circ>\<^sub>m g) x = Some z) = (\<exists>y. g x = Some y \<and> f y = Some z)"
proof (cases "g x")
  case None
  then show ?thesis 
    unfolding map_comp_def
    by simp
next
  case (Some y)
  then show ?thesis
    unfolding map_comp_def
    by simp
qed

lemma fmap_comp_eq_Some_iff : "(fmlookup (f \<circ>\<^sub>f g) x = Some z) = (\<exists>y. fmlookup g x = Some y \<and> fmlookup f y = Some z)"
  by transfer (rule map_comp_eq_Some_iff)

lemma fmap_comp_eq_None_iff : "(fmlookup (f \<circ>\<^sub>f g) x = None) = (fmlookup g x = None \<or> (\<forall>y. fmlookup g x = Some y \<longrightarrow> fmlookup f y = None))"
  by transfer (rule map_comp_eq_None_iff)

  

lemma map_id_comp_right_cancel:
  assumes dom_f: "dom f \<subseteq> d"
    shows "f \<circ>\<^sub>m map_id d = f"
proof (induction rule: map_eq_induct)
  case (NotInDom x)
  with dom_f show ?case     
    by (auto simp add: map_comp_eq_None_iff dom_def)    
next
  case (InDom x y)
  then show ?case 
    by (simp add: map_comp_eq_Some_iff dom_def)    
qed

lemma map_id_comp_right:
    shows "f \<circ>\<^sub>m map_id d = map_restrict_set d f"
proof (induction rule: map_eq_induct)
  case (NotInDom x)
  thus ?case     
    by (simp add: map_comp_eq_None_iff map_restrict_set_def map_filter_def)    
next
  case (InDom x y)
  then show ?case 
    by (simp add: map_comp_eq_Some_iff map_restrict_set_def map_filter_def)    
qed

lemma map_id_comp_left_cancel:
  assumes dom_f: "ran f \<subseteq> d"
    shows "map_id d \<circ>\<^sub>m f = f"
proof (induction rule: map_eq_induct)
  case (NotInDom x)
  with dom_f show ?case     
    by (auto simp add: map_comp_eq_None_iff ran_def subset_iff)    
       (meson option.exhaust)
    
next
  case (InDom x y)
  then show ?case 
    by (simp add: map_comp_eq_Some_iff dom_def)    
qed

lemma map_id_comp_left:
    shows "map_id d \<circ>\<^sub>m f = map_restrict_set {x. \<exists>y. f x = Some y \<and> y \<in> d} f"
proof (induction rule: map_eq_induct)
  case (NotInDom x)
  thus ?case     
    by (auto simp add: map_comp_eq_None_iff map_restrict_set_def map_filter_def)    
next
  case (InDom x y)
  then show ?case 
    by (simp add: map_comp_eq_Some_iff map_restrict_set_def map_filter_def)    
qed


lemma fmap_id_comp_right_cancel:
  "fmdom f |\<subseteq>| d \<Longrightarrow> f \<circ>\<^sub>f fmap_id d = f"
  by transfer (rule map_id_comp_right_cancel)

lemma fmap_id_comp_right:
  "f \<circ>\<^sub>f fmap_id d = fmrestrict_fset d f"
  by transfer (rule map_id_comp_right)

lemma fmap_id_comp_left_cancel:
  "fmran f |\<subseteq>| d \<Longrightarrow> fmap_id d \<circ>\<^sub>f f = f"
  by transfer (rule map_id_comp_left_cancel)


lift_definition fmap_bij_betw :: "('a, 'b) fmap \<Rightarrow> 'a fset \<Rightarrow> 'b fset \<Rightarrow> bool" 
is "\<lambda>f A B. bij_betw (the \<circ> f) A B" .

lemma fmap_bij_implies_inj:
  assumes \<open>fmap_bij_betw f (fmdom f) (fmran f)\<close>
  shows \<open>fmap_inj f\<close>
  using assms
  apply transfer
  apply(intro map_injI)
  by (metis bij_betw_inv_into_left comp_apply)

lemma fmap_inj_implies_bij:
  assumes \<open>fmap_inj f\<close>
  shows  \<open>fmap_bij_betw f (fmdom f) (fmran f)\<close>
  using assms
  by transfer (auto simp  add: inj_on_def bij_betw_def ran_alt_def domIff ranI)

lemma fmap_bijection_iff_injection:
  \<open>fmap_bij_betw f (fmdom f) (fmran f) \<longleftrightarrow> fmap_inj f\<close>
proof
  show \<open>fmap_inj f\<close> if \<open>fmap_bij_betw f (fmdom f) (fmran f)\<close>
    by (simp add: fmap_bij_implies_inj that)
next
  show \<open>fmap_bij_betw f (fmdom f) (fmran f) \<close> if \<open>fmap_inj f \<close>
    by (simp add: fmap_inj_implies_bij that)
qed
end


definition inverse_map :: "('a,'b) map \<Rightarrow> ('b,'a) map" where
"inverse_map m = (\<lambda>b. if b \<in> ran m then Some (SOME k. m k = Some b) else None)"

lemma dom_inverse_ran[simp]:
  shows "dom (inverse_map m) = ran m"
  by (simp add: inverse_map_def ran_def dom_def)

lemma inverse_range_subset_of_dom[simp]:
  \<open>ran (inverse_map m) \<subseteq> dom m\<close>
  apply (auto simp: inverse_map_def ran_def split: if_splits)
  by (meson someI_ex)

lemma inj_on_dom_subset_of_inverse_range[simp]:
  assumes "inj_on m (dom m)"
  shows \<open>dom m \<subseteq> ran (inverse_map m)\<close>
  using assms
  apply (auto simp: inverse_map_def ran_def inj_on_def dom_def)
  by (metis (mono_tags, lifting) someI_ex)

lemma ran_inj_inverse_dom[simp]:
  assumes "inj_on m (dom m)"
  shows "ran (inverse_map m) = dom m"
  using assms inverse_range_subset_of_dom inj_on_dom_subset_of_inverse_range
  by fast

lemma inverse_map_retrieves_original:
  assumes \<open>inverse_map m b = Some k\<close>
  shows \<open>m k = Some b\<close>
    using assms some_eq_imp[of "\<lambda>x. m x = Some b" k]
    by (auto simp: ran_def inverse_map_def split: if_splits)

lemma inj_on_map_implies_correct_inverse:
  assumes \<open>inj_on m (dom m)\<close>
  assumes \<open>m k = Some b\<close> 
  shows \<open>inverse_map m b = Some k\<close>
  using assms
  by (auto simp add: inverse_map_def ran_def domI inj_onD some_equality)

lemma inj_map_inverse_correct:
  assumes \<open>inj_on m (dom m)\<close>
  shows "(inverse_map m) b = Some k \<longleftrightarrow> m k = Some b"
proof
  show \<open>m k = Some b\<close> if \<open>inverse_map m b = Some k\<close>
    using inverse_map_retrieves_original[OF that]
    by assumption
next
  show \<open>inverse_map m b = Some k\<close> if \<open>m k = Some b\<close>
    using inj_on_map_implies_correct_inverse[OF assms that]
    by assumption
qed

lemma inj_m_inverse_inj:
  assumes \<open>inj_on m (dom m)\<close>
  shows \<open>inj_on (inverse_map m) (ran m)\<close>
proof -
  have \<open>x = y\<close> if \<open>(inverse_map m) x = (inverse_map m) y\<close> \<open>x \<in> ran m\<close>  \<open>y \<in> ran m\<close> for x y
    using that assms
    by (metis inverse_map_def inverse_map_retrieves_original option.inject)

  thus ?thesis
    by (simp add: inj_on_def)
qed

lemma inj_map_double_inverse_identity:
  assumes \<open>inj_on m (dom m)\<close>
  shows \<open>inverse_map (inverse_map m) = m\<close>
proof -
  have \<open>inverse_map (inverse_map m) x = m x\<close> for x
  proof (cases \<open>x \<in> dom m\<close>)
    case True
    then obtain y where y_def: \<open>m x = Some y\<close>
      by blast
    then have a:\<open>(inverse_map m) y = Some x\<close>
      using assms
      by (simp add: assms inj_map_inverse_correct)
    then have \<open>(inverse_map (inverse_map m)) x = Some y\<close>
      by (simp add: assms inj_m_inverse_inj inj_map_inverse_correct)
    thus ?thesis
      by (simp add: y_def)
  next
    case False
    then show ?thesis 
      using assms
      by (auto simp add: inverse_map_def dest: ran_inj_inverse_dom)
  qed

  thus ?thesis ..
qed

lemma map_inverse_correct:
  shows "\<And>(m :: ('a, 'b) map) b k. (inverse_map m) b = Some k \<Longrightarrow> m k = Some b" 
        "\<And>(m :: ('a, 'b) map) b. (inverse_map m) b = None \<equiv> (b \<notin> ran m)"
        "\<And>(m :: ('a, 'b) map) b k. m k = Some b \<Longrightarrow> b \<in> dom (inverse_map m)"
        "\<And>(m :: ('a, 'b) map) k. m k = None \<Longrightarrow> (k \<notin> ran (inverse_map m))"
proof -
  show main: "\<And>(m :: ('a, 'b) map) b k. (inverse_map m) b = Some k \<Longrightarrow> m k = Some b" 
    by (simp add: inverse_map_def ran_def)
       (metis (mono_tags, lifting) option.distinct(1) option.inject some_eq_ex)

  show main2: "\<And>(m :: ('a, 'b) map) b. (inverse_map m) b = None \<equiv> (b \<notin> ran m)"
    by (simp add: inverse_map_def ran_def)
       (smt (verit) option.distinct(1))

  show "\<And>(m :: ('a, 'b) map) b k. m k = Some b \<Longrightarrow> b \<in> dom (inverse_map m)"
    using main2 unfolding dom_def by (auto simp add: ran_def) 

  show "\<And>(m :: ('a, 'b) map) k. m k = None \<Longrightarrow> (k \<notin> ran (inverse_map m))"
    using main unfolding ran_def by fastforce
qed

context
  includes fmap.lifting fset.lifting
begin

lift_definition inverse_fmap :: "('a,'b) fmap \<Rightarrow> ('b,'a) fmap" 
  is inverse_map 
  by (simp add: finite_ran)

lemma fmap_inj_double_inverse[simp]:
  assumes \<open>fmap_inj m\<close>
  shows \<open>inverse_fmap (inverse_fmap m) = m\<close>
  using assms
  by transfer' (simp add:inj_map_double_inverse_identity map_inj_def)
  
lemma fmdom_inverse_fmran[simp]:
  shows "fmdom (inverse_fmap m) = fmran m"
  by transfer simp

lemma inverse_range_subset_of_fdom[simp]:
  \<open>fmran (inverse_fmap m) |\<subseteq>| fmdom m\<close>
  by transfer simp

lemma inj_fdom_subset_of_inverse_range[simp]:
  assumes "fmap_inj m"
  shows \<open>fmdom m |\<subseteq>| fmran (inverse_fmap m)\<close>
  using assms
  by transfer' (simp add: map_inj_def)

lemma fran_inj_inverse_fdom[simp]:
  assumes "fmap_inj m"
  shows "fmran (inverse_fmap m) = fmdom m"
  using assms
  by transfer (simp add: map_inj_def)

lemma inverse_fmap_retrieves_original:
  assumes \<open>fmlookup (inverse_fmap m) b = Some k\<close>
  shows \<open>fmlookup m k = Some b\<close>
  using assms
  by transfer' (auto dest: inverse_map_retrieves_original)

lemma inj_fmap_implies_correct_inverse:
  assumes \<open>fmap_inj m\<close>
  assumes \<open>fmlookup m k = Some b\<close> 
  shows \<open>fmlookup (inverse_fmap m) b = Some k\<close>
  using assms
  by transfer' (simp add: map_inj_def inj_map_inverse_correct)

lemma inj_fmap_inverse_correct:
  assumes "fmap_inj m"
  shows "fmlookup (inverse_fmap m) b = Some k \<longleftrightarrow> fmlookup m k = Some b"
  using assms
  by transfer' (simp add: map_inj_def inj_map_inverse_correct)

lemma inj_m_inverse_inj_fmap:
  assumes \<open>fmap_inj m\<close>
  shows \<open>fmap_inj (inverse_fmap m)\<close>
  using assms
  by transfer' (simp add: map_inj_def inj_m_inverse_inj)

end



lemma inverse_fmap_left_cancel_inj [simp]: 
  assumes "fmap_inj f"
  shows "inverse_fmap f \<circ>\<^sub>f f = fmap_id (fmdom f)"
  apply (rule fmap_ext)
  apply (auto simp add: fmlookup_dom_iff fmap_id_fmlookup)  
  by (meson assms inj_fmap_inverse_correct)

lemma inverse_fmap_left_cancel_inj_assoc [simp]: 
  assumes "fmap_inj f"
  shows "g \<circ>\<^sub>f inverse_fmap f \<circ>\<^sub>f f = g \<circ>\<^sub>f fmap_id (fmdom f)"
  by (metis assms fmap_comp_assoc inverse_fmap_left_cancel_inj)


lemma inverse_fmap_left_right [simp]: 
  shows "f \<circ>\<^sub>f inverse_fmap f = fmap_id (fmran f)"
  apply (rule fmap_ext)
  apply (simp add: fmlookup_dom_iff fmlookup_ran_iff fmap_id_fmlookup bind_eq_Some_conv bind_eq_None_conv)  
  by (metis fmdom_inverse_fmran fmdom_notI fmranI inverse_fmap_retrieves_original option.collapse)

lemma inverse_fmap_left_right_assoc [simp]: 
  shows "g \<circ>\<^sub>f f \<circ>\<^sub>f inverse_fmap f = g \<circ>\<^sub>f fmap_id (fmran f)"
  by (metis fmap_comp_assoc inverse_fmap_left_right)

lemma fmap_ext_iff:
  "(m = n) = (\<forall>x. fmlookup m x = fmlookup n x)"
  using fmap_ext by auto

lemma fmap_ext_iff_cases:
  "(m = n) = ((\<forall>x y. fmlookup m x = Some y \<longrightarrow> fmlookup n x = Some y) \<and> (\<forall>x. fmlookup m x = None \<longrightarrow> fmlookup n x = None))"
  unfolding fmap_ext_iff
  by (metis not_Some_eq)


lemma fminvimage_inverse_fmap_subset: "fminvimage (inverse_fmap f) S |\<subseteq>| fmimage f S"
  by (simp add: fsubset_iff fmlookup_invimage_iff fmlookup_image_iff)
     (meson inverse_fmap_retrieves_original)

lemma fminvimage_inverse_fmap_eq: "fmap_inj f \<Longrightarrow>fminvimage (inverse_fmap f) S = fmimage f S"
  by (simp add: fset_eq_iff fmlookup_invimage_iff fmlookup_image_iff inj_fmap_inverse_correct)


lemma fmadd_injI :
  assumes inj_f1: "fmap_inj f1"
      and inj_f2: "fmap_inj f2"
      and ran_disjoint: "fmran f1 |\<inter>| fmran f2 = {||}"
    shows "fmap_inj (fmadd f1 f2)"
  using assms
  unfolding fmap_inj_spec fmlookup_dom_iff fmlookup_ran_iff fset_eq_iff finter_iff
  by (simp add: fmlookup_dom_iff) metis

lemma fmadd_injE_disjoint :
  assumes inj_f12: "fmap_inj (fmadd f1 f2)"
      and disjoint: "fmdom f1 |\<inter>| fmdom f2 = {||}"
    shows "fmap_inj f1"
      and "fmap_inj f2"
      and "fmran f1 |\<inter>| fmran f2 = {||}"
proof -
  from disjoint have f12_simp: "\<And>x. x |\<in>| fmdom f1 \<Longrightarrow> x |\<notin>| fmdom f2" 
                 and f21_simp: "\<And>x. x |\<in>| fmdom f2 \<Longrightarrow> x |\<notin>| fmdom f1" 
    by (simp_all add: fset_eq_iff) blast

  from inj_f12 disjoint
  show "fmap_inj f1" "fmap_inj f2" by (simp_all add: fmap_inj_spec f12_simp)

  have "\<And>x. \<lbrakk>x |\<in>| fmran f1; x |\<in>| fmran f2\<rbrakk> \<Longrightarrow> False" 
  proof -
    fix x
    assume "x |\<in>| fmran f1" then obtain y1 where y1: "fmlookup f1 y1 = Some x"
      unfolding fmlookup_ran_iff 
      by blast
    assume "x |\<in>| fmran f2" then obtain y2 where y2: "fmlookup f2 y2 = Some x"
      unfolding fmlookup_ran_iff 
      by blast

    
    from y1 have y1_dom: "y1 |\<in>| fmdom f1"
      unfolding fmlookup_dom_iff by blast

    hence y1_nin_dom: "y1 |\<notin>| fmdom f2"
      by (rule f12_simp)

    from y2 have y2_dom: "y2 |\<in>| fmdom f2"
      unfolding fmlookup_dom_iff by blast
    hence y2_nin_dom: "y2 |\<notin>| fmdom f1"
      by (rule f21_simp)

    have "y1 = y2" 
      apply (rule fmap_injE[OF inj_f12])
      apply (simp_all add: y1_dom y2_dom y1_nin_dom y1 y2)
      done
    with y1_dom y2_nin_dom show False by blast
  qed
    
  thus "fmran f1 |\<inter>| fmran f2 = {||}"    
    by (auto simp add: fset_eq_iff)
qed


lemma fmran_add: "fmran (fmadd m1 m2) = fmran m2 |\<union>| fmran (fmdrop_fset (fmdom m2) m1)"
  apply (simp add: fset_eq_iff fmlookup_ran_iff fmlookup_dom_iff fmlookup_image_iff)
  apply (metis option.distinct(1) option.exhaust_sel)
  done

lemma fmimage_fmadd :
  "fmimage (m1 ++\<^sub>f m2) s = fmimage m2 s |\<union>| fmimage m1 (s |-| fmdom m2)"
  by (simp add: fset_eq_iff fmlookup_image_iff fmlookup_dom_iff) force

lemma fmadd_comm:
  assumes "fmdom f1 |\<inter>| fmdom f2 = {||}"
  shows "fmadd f1 f2 = fmadd f2 f1"
  using assms
  by (simp add: fmap_ext_iff fset_eq_iff fmlookup_dom_iff)
     (metis option.distinct(1))

lemma fmcomp_add_left: "fmcomp (fmadd f1 f2) f3 = fmadd (fmcomp f1 f3) (fmcomp f2 f3)"
  by (auto simp add: fmap_ext_iff_cases fmdom_fmcomp Option.bind_eq_Some_conv Option.bind_eq_None_conv fmlookup_invimage_iff fmlookup_dom_iff)

lemma fmcomp_add_right: "fmdom f1 |\<inter>| fmdom f2 = {||} \<Longrightarrow> fmcomp f3 (fmadd f1 f2) = fmadd (fmcomp f3 f1) (fmcomp f3 f2)"
  by (auto simp add: fset_eq_iff fmap_ext_iff_cases fmdom_fmcomp Option.bind_eq_Some_conv Option.bind_eq_None_conv fmlookup_invimage_iff fmlookup_dom_iff)
  

lemma inverse_fmap_comp:
  assumes inj: "fmap_inj (f1 ++\<^sub>f f2)"
      and disj: "fmdom f1 |\<inter>| fmdom f2 = {||}"
  shows "inverse_fmap (f1 ++\<^sub>f f2) = inverse_fmap f1 ++\<^sub>f inverse_fmap f2"
  using assms
  apply (simp add: fset_eq_iff fmap_ext_iff fmlookup_dom_iff fmlookup_ran_iff)
  by (smt (verit) fmap_inj_double_inverse fmap_inj_spec fmdom_notD fmdom_notI fmlookup_add fmlookup_dom_iff inj inj_fmap_inverse_correct inverse_fmap_retrieves_original option.distinct(1))


lemma fmcomp_non_fitting_dom_ran_empty:
  assumes "fmdom f1 |\<inter>| fmran f2 = {||}"
  shows "fmcomp f1 f2 = fmempty"
  using assms
  apply (simp add: fmap_ext_iff Option.bind_eq_None_conv fset_eq_iff fmlookup_dom_iff fmlookup_ran_iff)
  by (metis option.collapse)

lemma fmcomp_empty_left[simp]: "fmcomp fmempty f = fmempty"
  by (simp add: fmap_ext_iff Option.bind_eq_None_conv)

lemma fmcomp_empty_right[simp]: "fmcomp f fmempty = fmempty"
  by (simp add: fmap_ext_iff Option.bind_eq_None_conv)


end
