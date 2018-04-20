theory Union_Find
  imports
    Refine_Imperative_HOL.IICF
begin

section \<open>General definitions\<close>
record 'v node =
  (* node_value :: "'v" *)
  parent :: "'v"
  rank :: "nat"

type_synonym 'v "union_find" = "('v, 'v node) map"

inductive in_component :: "'v union_find \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool" where
  in_component_root[simp, intro]: "\<lbrakk>m v = Some node; parent node = v\<rbrakk> \<Longrightarrow> in_component m v v" |
  in_component_suc: "\<lbrakk>m v = Some node; parent node = p; v \<noteq> p; in_component m p c\<rbrakk> \<Longrightarrow> in_component m v c"

definition same_component :: "'v union_find \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool"
  where "same_component m a b \<equiv> \<exists>c. in_component m a c \<and> in_component m b c"

definition valid_union_find :: "'v union_find \<Rightarrow> bool"
  where "valid_union_find m \<equiv> \<forall>v\<in>dom m. \<exists>c. in_component m v c"

definition preserve_component :: "'v union_find \<Rightarrow> 'v union_find \<Rightarrow> bool"
  where "preserve_component m m' \<equiv> (\<forall>v\<in>dom m. (\<forall>c. in_component m v c \<longleftrightarrow> in_component m' v c))"

definition preserve_component_union :: "'v union_find \<Rightarrow> 'v union_find \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool"
  where "preserve_component_union m m' a b \<equiv> (\<forall>x\<in>dom m. \<forall>y\<in>dom m.
    (same_component m' x y \<longleftrightarrow> (same_component m x y \<or>
                                same_component m x a \<and> same_component m b y \<or>
                                same_component m b x \<and> same_component m y a)))"

section \<open>Helping lemmas\<close>
lemma same_component_simps[simp]:
  assumes "in_component m a c"
  assumes "in_component m b c"
  shows "same_component m a b"
  using assms unfolding same_component_def
  by auto

lemma in_component_unique:
  assumes "in_component m a c"
  assumes "in_component m a c'"
  shows "c = c'"
  using assms
proof (induction m a c rule: in_component.induct)
  case (in_component_root m a)
  with in_component.simps[of m a c']
    show ?case by auto
next
  case (in_component_suc m a p c)
  with in_component.simps[of m a c'] 
    show ?case by auto
qed

lemma not_same_component:
  assumes "in_component m a c"
  assumes "in_component m b d"
  assumes "c \<noteq> d"
  shows "\<not> same_component m a b"
proof
  assume "same_component m a b"
  then obtain c' where "in_component m a c' \<and> in_component m b c'"
    unfolding same_component_def by auto
  with assms in_component_unique[of m a c c'] in_component_unique[of m b d c']
  show False
    by simp
qed

lemma same_component_refl[simp]:
  assumes "valid_union_find m"
  assumes "v \<in> dom m"
  shows "same_component m v v"
  using assms unfolding same_component_def valid_union_find_def
  by auto

lemma same_component_sym:
  assumes "same_component m a b"
  shows "same_component m b a"
  using assms unfolding same_component_def
  by auto

lemma in_component_dom[simp]:
  assumes "in_component m v c"
  shows "v \<in> dom m" "c \<in> dom m"
  using assms
  by (induction m v c rule: in_component.induct) auto

lemma same_component_dom[simp]:
  assumes "same_component m x y"
  shows "x \<in> dom m" "y \<in> dom m"
  using assms unfolding same_component_def
  by (auto elim: in_component.cases)

lemma preserve_component_refl[simp]: "preserve_component l l"
  unfolding preserve_component_def by auto

lemma same_component_parent:
  assumes "valid_union_find m"
  assumes "m v = Some node"
  shows "same_component m v (parent node)"
proof -
  from assms obtain c where c: "in_component m v c"
    unfolding valid_union_find_def by blast
  with assms(2) have "in_component m (parent node) c"
    by (auto intro:in_component.cases[OF c])
  with c show ?thesis
    unfolding same_component_def by auto
qed

lemma same_component_trans:
  assumes "same_component m a b"
  assumes "same_component m b d"
  shows "same_component m a d"
proof -
  from assms(1) obtain c where c: "in_component m a c \<and> in_component m b c"
    unfolding same_component_def by blast
  from assms(2) obtain c' where c': "in_component m b c' \<and> in_component m d c'"
    unfolding same_component_def by blast
  from c c' have "c = c'"
    by (auto simp: in_component_unique)
  with c c' show ?thesis unfolding same_component_def
    by auto
qed


lemma in_component_same:
  assumes "in_component m v c"
  shows "same_component m v c"
proof -
  from assms have "in_component m c c"
    by (induction m v c rule: in_component.induct) auto
  with assms show ?thesis
    by simp
qed

lemma in_component_parent_root:
  assumes "in_component m v c"
  shows "parent (the (m c)) = c"
  using assms
  by (induction m v c rule: in_component.induct) auto

lemma preserve_component_impl:
  assumes "preserve_component m m'"
  assumes "in_component m v c"
  shows "in_component m' v c"
  using assms
  unfolding preserve_component_def
  by (meson domI in_component.cases)

lemma preserve_component_impl_same:
  assumes "preserve_component m m'"
  shows "\<forall>a \<in> dom m. \<forall>b \<in> dom m. same_component m a b \<longleftrightarrow> same_component m' a b"
  using assms
  unfolding preserve_component_def same_component_def
  by blast

lemma preserve_component_union_impl:
  assumes "preserve_component_union m m' a b"
  assumes "same_component m x y"
  shows "same_component m' x y"
  using assms
  unfolding preserve_component_union_def
  by auto

lemma preserve_component_union_impl_rev:
  assumes "preserve_component_union m m' a b"
  assumes "same_component m' x y"
  assumes "\<not> same_component m x y"
  assumes "dom m = dom m'"
  shows "same_component m x a \<and> same_component m b y \<or>
         same_component m b x \<and> same_component m y a"
  using assms same_component_dom[OF assms(2)]
  unfolding preserve_component_union_def
  by fast

lemma preserve_component_union_same:
  assumes "preserve_component_union m m' root_a root_b"
  assumes "in_component m a root_a"
  assumes "in_component m b root_b"
  shows "same_component m' a b"
  using assms in_component_same[OF assms(2)] in_component_same[OF assms(3)]
  unfolding preserve_component_union_def same_component_def
  by auto

lemma preserve_exists:
  assumes "valid_union_find m"
  assumes "preserve_component m m'"
  shows "dom m \<subseteq> dom m'"
proof
  fix x
  assume asm: "x \<in> dom m"
  with assms(1) obtain c where c: "in_component m x c"
    unfolding valid_union_find_def by auto
  with assms(2) asm in_component_dom(1)[of m' x c] show "x \<in> dom m'"
    unfolding preserve_component_def by blast
qed

lemma preserve_component_trans:
  assumes "valid_union_find m"
  assumes "preserve_component m m'"
  assumes "preserve_component m' m''"
  shows "preserve_component m m''"
  using assms preserve_exists[OF assms(1,2)]
  unfolding preserve_component_def
  by blast

lemma preserve_component_union_trans:
  assumes "preserve_component m m'"
  assumes "a \<in> dom m"
  assumes "b \<in> dom m"
  assumes "dom m = dom m'"
  assumes "preserve_component_union m' m'' a b"
  shows "preserve_component_union m m'' a b"
proof -
  have "same_component m'' x y \<longleftrightarrow>
          (same_component m x y \<or>
           same_component m x a \<and> same_component m b y \<or>
           same_component m b x \<and> same_component m y a)" (is "?lhs \<longleftrightarrow> ?rhs")
    if x: "x\<in>dom m" and y: "y\<in>dom m" for x y
  proof
    assume ?lhs
    with assms(4,5) x y have "same_component m' x y \<or>
           same_component m' x a \<and> same_component m' b y \<or>
           same_component m' b x \<and> same_component m' y a"
      unfolding preserve_component_union_def by simp
    with preserve_component_impl_same[OF assms(1)] x y assms(2,3) show ?rhs
      by blast
  next
    assume ?rhs
    with preserve_component_impl_same[OF assms(1)] x y assms(2,3)
    have "same_component m' x y \<or>
           same_component m' x a \<and> same_component m' b y \<or>
           same_component m' b x \<and> same_component m' y a"
      unfolding preserve_component_union_def by blast
    with assms(4,5) x y show ?lhs
      unfolding preserve_component_union_def by simp
  qed
  then show ?thesis
    unfolding preserve_component_union_def by simp
qed

lemma preserve_component_union_trans':
  assumes "preserve_component_union m m' a b"
  assumes "preserve_component m' m''"
  assumes "dom m = dom m'"
  shows "preserve_component_union m m'' a b"
proof -
  have "same_component m'' x y \<longleftrightarrow>
          (same_component m x y \<or>
           same_component m x a \<and> same_component m b y \<or>
           same_component m b x \<and> same_component m y a)" (is "?lhs \<longleftrightarrow> ?rhs")
    if x: "x\<in>dom m" and y: "y\<in>dom m" for x y
  proof
    assume ?lhs
    with preserve_component_impl_same[OF assms(2)] x y assms(3)
    have "same_component m' x y"
      unfolding preserve_component_union_def by blast
    with assms(1) x y show ?rhs
      unfolding preserve_component_union_def by simp
  next
    assume ?rhs
    with assms(1) x y
    have "same_component m' x y"
      unfolding preserve_component_union_def by simp
    with preserve_component_impl_same[OF assms(2)] x y assms(3) show ?lhs
      unfolding preserve_component_union_def by blast
  qed
  then show ?thesis
    unfolding preserve_component_union_def by simp
qed

lemma preserve_component_union_trans_roots:
  assumes "preserve_component m m'"
  assumes "dom m = dom m'"
  assumes "in_component m' a root_a"
  assumes "in_component m' b root_b"
  assumes "preserve_component_union m' m'' root_a root_b"
  shows "preserve_component_union m m'' a b"
proof -
  from assms(3,4) have a: "a\<in>dom m'" and b: "b\<in>dom m'"
    by auto
  have "same_component m'' x y \<longleftrightarrow>
          (same_component m x y \<or>
           same_component m x a \<and> same_component m b y \<or>
           same_component m b x \<and> same_component m y a)" (is "?lhs \<longleftrightarrow> ?rhs")
    if x: "x\<in>dom m" and y: "y\<in>dom m" for x y
  proof
    assume ?lhs
    with x y assms(2,5) have "same_component m' x y \<or>
           same_component m' x root_a \<and> same_component m' root_b y \<or>
           same_component m' root_b x \<and> same_component m' y root_a"
      unfolding preserve_component_union_def by simp
    with same_component_trans[OF _ same_component_sym[OF in_component_same[OF assms(3)]]]
         same_component_trans[OF in_component_same[OF assms(4)]]
    have "same_component m' x y \<or>
           same_component m' x a \<and> same_component m' b y \<or>
           same_component m' b x \<and> same_component m' y a"
      by auto
    with preserve_component_impl_same[OF assms(1)] x y assms(2) a b show ?rhs
      by blast
  next
    assume ?rhs
    with preserve_component_impl_same[OF assms(1)] x y assms(2) a b
    have "same_component m' x y \<or>
           same_component m' x a \<and> same_component m' b y \<or>
           same_component m' b x \<and> same_component m' y a"
      unfolding preserve_component_union_def by blast
    with same_component_trans[OF same_component_sym[OF in_component_same[OF assms(4)]]]
         same_component_trans[OF _ in_component_same[OF assms(3)]]
    have "same_component m' x y \<or>
           same_component m' x root_a \<and> same_component m' root_b y \<or>
           same_component m' root_b x \<and> same_component m' y root_a"
      by blast
    with assms(2,5) x y show ?lhs
      unfolding preserve_component_union_def by simp
  qed
  then show ?thesis
    unfolding preserve_component_union_def by simp
qed

lemma weaker_preserve_component:
  assumes "preserve_component m m'"
  assumes "same_component m' a b"
  assumes "a \<in> dom m"
  assumes "b \<in> dom m"
  shows "preserve_component_union m m' a b"
proof -
  have "same_component m' x y \<longleftrightarrow>
          (same_component m x y \<or>
           same_component m x a \<and> same_component m b y \<or>
           same_component m b x \<and> same_component m y a)" (is "?lhs \<longleftrightarrow> ?rhs")
    if xy: "x\<in>dom m" "y\<in>dom m" for x y
  proof
    assume ?lhs
    with preserve_component_impl_same[OF assms(1)] xy show ?rhs by blast
  next
    assume ?rhs
    from preserve_component_impl_same[OF assms(1)] assms(2,3,4)
    have "same_component m a b"
      by blast
    with `?rhs` same_component_trans[OF same_component_trans, of m x a b y]
         same_component_sym[OF same_component_trans[OF same_component_trans, of m y a b x]]
    have "same_component m x y"
      by auto
    with preserve_component_impl_same[OF assms(1)] xy show ?lhs
      by blast
  qed
  then show ?thesis
    unfolding preserve_component_union_def by simp
qed

lemma preserve_component_union_sym:
  assumes "preserve_component_union m m' a b"
  shows "preserve_component_union m m' b a"
  using assms same_component_sym[of m]
  unfolding preserve_component_union_def
  by blast


section \<open>Helping functions\<close>
subsection \<open>Update parent\<close>
definition update_parent_spec :: "'v union_find \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('v union_find) nres"
  where "update_parent_spec m v p \<equiv> do {
    ASSERT (v \<in> dom m \<and> p \<in> dom m  \<and> parent (the (m v)) = v \<and> parent (the (m p)) = p \<and> valid_union_find m);
    SPEC (\<lambda>m'. valid_union_find m' \<and> preserve_component_union m m' v p \<and> dom m = dom m' \<and> in_component m' v p)
  }"

definition update_parent :: "'v union_find \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('v union_find) nres"
  where "update_parent m v p = mop_map_update v \<lparr>
    parent = p,
    rank = rank (the (m v))
  \<rparr> m"

lemma update_parent_new_component:
  assumes "m p = Some node_p"
  assumes "parent node_p = p"
  shows "in_component (m(v \<mapsto> \<lparr>parent = p, rank = rank (the (m v))\<rparr>)) v p"
proof -
  from assms in_component_root[of "m(v \<mapsto> \<lparr>parent = p, rank = rank (the (m v))\<rparr>)" p node_p]
  have "in_component (m(v \<mapsto> \<lparr>parent = p, rank = rank (the (m v))\<rparr>)) p p"
    by fastforce
  with in_component_suc[of "m(v \<mapsto> \<lparr>parent = p, rank = rank (the (m v))\<rparr>)" v _ p p]
  show ?thesis
    by fastforce
qed


lemma update_parent_in_component_changed:
  assumes "m p = Some node_p"
  assumes "parent node_p = p"
  assumes "in_component m v' v"
  shows "in_component (m(v \<mapsto> \<lparr>parent = p, rank = rank (the (m v))\<rparr>)) v' p"
proof -
  from assms(1,2) update_parent_new_component have
    "in_component (m(v \<mapsto> \<lparr>parent = p, rank = rank (the (m v))\<rparr>)) v p"
    by fast
  with assms(3) show ?thesis 
  proof (induction m v' v rule: in_component.induct)
    case (in_component_root m v' node)
    then show ?case
      by auto
  next
    case (in_component_suc m v' node p' v)
    with in_component.in_component_suc[OF _ in_component_suc.hyps(2,3), of "m(v \<mapsto> \<lparr>parent = p, rank = rank (the (m v))\<rparr>)" p]
    show ?case
      by (cases "v = v'") fastforce+
  qed
qed

lemma update_parent_in_component_unchanged:
  assumes "m p = Some node_p"
  assumes "parent node_p = p"
  assumes "in_component m v' c"
  assumes "c \<noteq> v"
  assumes "in_component m v v"
  shows "in_component (m(v \<mapsto> \<lparr>parent = p, rank = rank (the (m v))\<rparr>)) v' c"
proof -
  from assms(1,2) update_parent_new_component have
    asm: "in_component (m(v \<mapsto> \<lparr>parent = p, rank = rank (the (m v))\<rparr>)) v p"
    by fast
  with assms(3,4,5) show ?thesis
  proof (induction m v' c rule: in_component.induct)
    case (in_component_root m v' node)
    then show ?case
      by auto
  next
    case (in_component_suc m v' node p' c)
    show ?case
    proof (cases "v = v'")
      case True
      with in_component_unique[OF in_component.in_component_suc[OF in_component_suc.hyps]]
           in_component_suc.prems(1,2) 
      show ?thesis by simp
    next
      case False
      with in_component_suc in_component.in_component_suc[OF _ in_component_suc.hyps(2,3), of "m(v \<mapsto> \<lparr>parent = p, rank = rank (the (m v))\<rparr>)" c]
      show ?thesis
        by fastforce
    qed
  qed
qed

lemma update_parent_in_component:
  assumes "m p = Some node_p"
  assumes "parent node_p = p"
  assumes "m v = Some node_v"
  assumes "parent node_v = v"
  assumes "in_component m v' c"
  shows "in_component (m(v \<mapsto> \<lparr>parent = p, rank = rank (the (m v))\<rparr>)) v' c \<or>
         in_component (m(v \<mapsto> \<lparr>parent = p, rank = rank (the (m v))\<rparr>)) v' p"
  using update_parent_in_component_changed[OF assms(1,2,5)]
        update_parent_in_component_unchanged[OF assms(1,2,5) _ in_component_root[of m, OF assms(3,4)]]
  by auto

lemma update_parent_same_component:
  assumes "m p = Some node_p"
  assumes "parent node_p = p"
  assumes "m v = Some node_v"
  assumes "parent node_v = v"
  assumes "same_component m a b"
  shows "same_component (m(v \<mapsto> \<lparr>parent = p, rank = rank (the (m v))\<rparr>)) a b"
proof -
  let ?m = "m(v \<mapsto> \<lparr>parent = p, rank = rank (the (m v))\<rparr>)"
  from assms(5) obtain c where "in_component m a c \<and> in_component m b c"
    unfolding same_component_def by auto
  with update_parent_in_component_changed[of m p node_p _ v, OF assms(1,2)]
       update_parent_in_component_unchanged[of m p node_p _ c, OF assms(1,2) _ _ in_component_root[of m, OF assms(3,4)]]
  have "(in_component ?m a c \<and> in_component ?m b c) \<or>
        (in_component ?m a p \<and> in_component ?m b p)"
    by fast
  then show ?thesis
    unfolding same_component_def by auto
qed

lemma update_parent_valid:
  assumes "m p = Some node_p"
  assumes "parent node_p = p"
  assumes "m v = Some node_v"
  assumes "parent node_v = v"
  assumes "valid_union_find m"
  shows "valid_union_find (m(v \<mapsto> \<lparr>parent = p, rank = rank (the (m v))\<rparr>))"
  unfolding valid_union_find_def
proof
  fix v'
  let ?m = "m(v \<mapsto> \<lparr>parent = p, rank = rank (the (m v))\<rparr>)"
  assume "v' \<in> dom ?m"
  with assms(3) have "v' \<in> dom m"
    by auto
  with assms(5) obtain c where "in_component m v' c"
    unfolding valid_union_find_def by auto
  from update_parent_in_component[OF assms(1,2,3,4) this]
  show "\<exists>c. in_component (m(v \<mapsto> \<lparr>parent = p, rank = rank (the (m v))\<rparr>)) v' c"
    by auto
qed

lemma update_parent_preserve_component_union:
  assumes "m p = Some node_p"
  assumes "parent node_p = p"
  assumes "m v = Some node_v"
  assumes "parent node_v = v"
  assumes "valid_union_find m"
  shows "preserve_component_union m (m(v \<mapsto> \<lparr>parent = p, rank = rank (the (m v))\<rparr>)) v p"
proof -
  let ?m = "m(v \<mapsto> \<lparr>parent = p, rank = rank (the (m v))\<rparr>)"
  have "same_component ?m x y \<longleftrightarrow>
          (same_component m x y \<or>
           same_component m x v \<and> same_component m p y \<or>
           same_component m p x \<and> same_component m y v)" (is "?lhs \<longleftrightarrow> ?rhs")
    if xy: "x\<in>dom m" "y\<in>dom m" for x y
  proof
    assume ?lhs
    then obtain c where c: "in_component ?m x c" "in_component ?m y c"
      unfolding same_component_def by blast
    from assms(5) xy obtain cx cy where cxy: "in_component m x cx" "in_component m y cy"
      unfolding valid_union_find_def by blast
    show ?rhs
    proof (cases "cx = v")
      case True
      with cxy update_parent_in_component_changed[of m, OF assms(1,2), of x v]
      have cx': "in_component ?m x p"
        by simp
      show ?thesis
      proof (cases "cy = v")
        case True
        with `cx = v` have "cx = cy" by simp
        with cxy show ?thesis
          by simp
      next
        case False
        from update_parent_in_component_unchanged[OF assms(1,2) cxy(2) False in_component_root[of m, OF assms(3,4)]]
        have cy': "in_component ?m y cy" .
        from in_component_unique[OF c(1) cx'] in_component_unique[OF c(2) cy']
        have "p = cy"
          by simp
        with cxy `cx = v` in_component_same same_component_sym
        show ?thesis
          by fast
      qed
    next
      case False
      from update_parent_in_component_unchanged[OF assms(1,2) cxy(1) False in_component_root[of m, OF assms(3,4)]]
      have cx': "in_component ?m x cx" .
      show ?thesis
      proof (cases "cy = v")
        case True
        with cxy update_parent_in_component_changed[of m, OF assms(1,2), of y v]
        have cy': "in_component ?m y p"
          by simp
        from in_component_unique[OF c(1) cx'] in_component_unique[OF c(2) cy']
        have "p = cx"
          by simp
        with cxy `cy = v` in_component_same same_component_sym
        show ?thesis
          by fast
      next
        case False
        from update_parent_in_component_unchanged[OF assms(1,2) cxy(2) False in_component_root[of m, OF assms(3,4)]]
        have cy': "in_component ?m y cy" .
        from in_component_unique[OF c(1) cx'] in_component_unique[OF c(2) cy']
        have "cx = cy"
          by simp
        with cxy show ?thesis
          by simp 
      qed
    qed
  next
    assume ?rhs
    with update_parent_same_component[OF assms(1,2,3,4)]
    have "same_component ?m x y \<or>
           same_component ?m x v \<and> same_component ?m p y \<or>
           same_component ?m p x \<and> same_component ?m y v"
      by auto
    with in_component_same[OF update_parent_new_component[of m, OF assms(1,2), of v]]
      same_component_trans[of ?m] same_component_sym[of ?m]
    show ?lhs by blast
  qed
  then show ?thesis
    unfolding preserve_component_union_def by simp
qed

theorem update_parent_correct: "(update_parent, update_parent_spec)\<in>Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding update_parent_spec_def update_parent_def
  apply refine_vcg
  apply (auto intro: update_parent_new_component
                     update_parent_preserve_component_union
                     update_parent_valid)
  done

subsection \<open>Update rank\<close>
definition update_rank_spec :: "'v union_find \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> ('v union_find) nres"
  where "update_rank_spec m v r \<equiv> do {
    ASSERT (v \<in> dom m \<and> valid_union_find m);
    SPEC (\<lambda>m'. valid_union_find m' \<and> preserve_component m m' \<and> dom m = dom m')
  }"

definition update_rank :: "'v union_find \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> ('v union_find) nres"
  where "update_rank m v r = mop_map_update v \<lparr>
    parent = parent (the (m v)),
    rank = r
  \<rparr> m"

lemma preserve_parents_in_component:
  assumes "dom m = dom m'"
  assumes "\<forall>v' \<in> dom m. parent (the (m v')) = parent (the (m' v'))"
  shows "in_component m v c \<longleftrightarrow> in_component m' v c"
proof
  assume "in_component m v c"
  then show "in_component m' v c" using assms
  proof (induction m v c rule: in_component.induct)
    case (in_component_root m v node)
    then have "v = parent (the (m' v))"
      by force
    with in_component_root in_component.in_component_root[of m' v] show ?case
      by fastforce
  next
    case (in_component_suc m v node p c)
    then have "p = parent (the (m' v))"
      by force
    with in_component_suc in_component.in_component_suc[of m' v _ p] show ?case
      by fastforce
  qed
next
  assume "in_component m' v c"
  then show "in_component m v c" using assms
  proof (induction m' v c rule: in_component.induct)
    case (in_component_root m' v node)
    then have "v = parent (the (m v))"
      by force
    with in_component_root in_component.in_component_root[of m v] show ?case
      by fastforce
  next
    case (in_component_suc m' v node p c)
    then have "p = parent (the (m v))"
      by force
    with in_component_suc in_component.in_component_suc[of m v _ p] show ?case
      by fastforce
  qed
qed

lemma preserve_parents_valid:
  assumes "valid_union_find m"
  assumes "dom m = dom m'"
  assumes "\<forall>v' \<in> dom m. parent (the (m v')) = parent (the (m' v'))"
  shows "valid_union_find m'"
  using assms preserve_parents_in_component[OF assms(2,3)]
  unfolding valid_union_find_def
  by blast

lemma preserve_parents_preserve_component:
  assumes "valid_union_find m"
  assumes "dom m = dom m'"
  assumes "\<forall>v' \<in> dom m. parent (the (m v')) = parent (the (m' v'))"
  shows "preserve_component m m'"
  using preserve_parents_in_component[OF assms(2,3)]
  unfolding valid_union_find_def preserve_component_def
  by blast

lemma update_rank_preserve_parents:
  assumes "valid_union_find m"
  assumes "m v' = Some node"
  assumes "(m(v \<mapsto> \<lparr>parent = parent (the (m v)), rank = r\<rparr>)) v' = Some node'"
  shows "parent node = parent node'"
  using assms by (cases "v = v'") auto

lemma update_rank_valid:
  assumes "valid_union_find m"
  assumes "v \<in> dom m"
  shows "valid_union_find (m(v \<mapsto> \<lparr>parent = parent (the (m v)), rank = r\<rparr>))"
proof -
  from assms(2) have "dom m = dom (m(v \<mapsto> \<lparr>parent = parent (the (m v)), rank = r\<rparr>))"
    by auto
  also from this update_rank_preserve_parents[OF assms(1), of _ "the (m v)" v r]
  have "\<forall>v'\<in>dom m. parent (the (m v')) =
       parent (the ((m(v \<mapsto> \<lparr>parent = parent (the (m v)), rank = r\<rparr>)) v'))"
    by simp
  ultimately show ?thesis using preserve_parents_valid[OF assms(1)]
    by simp
qed

lemma update_rank_preserve_component:
  assumes "valid_union_find m"
  assumes "v \<in> dom m"
  shows "preserve_component m (m(v \<mapsto> \<lparr>parent = parent (the (m v)), rank = r\<rparr>))"
proof -
  from assms(2) have "dom m = dom (m(v \<mapsto> \<lparr>parent = parent (the (m v)), rank = r\<rparr>))"
    by auto
  also from this update_rank_preserve_parents[OF assms(1), of _ "the (m v)" v r]
  have "\<forall>v'\<in>dom m. parent (the (m v')) =
       parent (the ((m(v \<mapsto> \<lparr>parent = parent (the (m v)), rank = r\<rparr>)) v'))"
    by simp
  ultimately show ?thesis using preserve_parents_preserve_component[OF assms(1)]
    by simp
qed

theorem update_rank_correct: "(update_rank, update_rank_spec)\<in>Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding update_rank_spec_def update_rank_def
  by refine_vcg (auto simp: update_rank_valid update_rank_preserve_component)


section \<open>Creating empty data structure\<close>
definition empty_union_find :: "'v union_find"
  where "empty_union_find \<equiv> Map.empty"

lemma empty_union_find_valid[simp]: "valid_union_find empty_union_find"
  unfolding empty_union_find_def valid_union_find_def by simp

lemma empty_union_find_empty[simp]: "dom empty_union_find = {}"
  unfolding empty_union_find_def by simp

section \<open>Add element to data structure\<close>
subsection \<open>Definition\<close>
definition add_node_spec :: "'v union_find \<Rightarrow> 'v \<Rightarrow> ('v union_find) nres"
  where "add_node_spec m v \<equiv> do {
    ASSERT (valid_union_find m \<and> v \<notin> dom m);
    SPEC (\<lambda>m'. valid_union_find m' \<and> preserve_component m m' \<and> dom m' = dom m \<union> {v} \<and> in_component m' v v)
  }"

definition add_node :: "'v union_find \<Rightarrow> 'v \<Rightarrow> ('v union_find) nres"
  where "add_node m v \<equiv> do {
    ASSERT (v \<notin> dom m);
    mop_map_update v \<lparr>parent = v, rank = 0\<rparr> m
  }"

subsection \<open>Helping lemmas\<close>
lemma preserve_add_node:
  assumes "valid_union_find m"
  assumes "v \<notin> dom m"
  shows "preserve_component m (m(v \<mapsto> \<lparr>parent = v, rank = 0\<rparr>))"
proof -
  let ?m' = "m(v \<mapsto> \<lparr>parent = v, rank = 0\<rparr>)"
  have other_dir: "in_component m v' c \<Longrightarrow> in_component ?m' v' c" if v': "v'\<in>dom m" for v' c
  proof -
    assume asm: "in_component m v' c"
    from asm assms(2) show "in_component ?m' v' c"
    proof (induction m v' c rule: in_component.induct)
      case (in_component_root m v' node)
      with in_component.in_component_root[of _ v']
      show ?case by (cases "v' = v") auto
    next
      case (in_component_suc m v' node p c)
      with in_component.in_component_suc[of _ v']
      show ?case by (cases "v' = v") auto
    qed
  qed
  also have "in_component ?m' v' c \<Longrightarrow> in_component m v' c" if v': "v'\<in>dom m" for v' c
  proof -
    assume asm: "in_component ?m' v' c"
    from assms(1) v' obtain c' where c': "in_component m v' c'"
      unfolding valid_union_find_def by auto
    with other_dir v' have "in_component ?m' v' c'"
      by auto
    with asm in_component_unique have "c = c'"
      by force
    with c' show "in_component m v' c"
      by auto
  qed
  ultimately show ?thesis
    unfolding preserve_component_def by blast
qed

lemma add_node_valid:
  assumes "valid_union_find m"
  assumes "v \<notin> dom m"
  shows "valid_union_find (m(v \<mapsto> \<lparr>parent = v, rank = 0\<rparr>))"
proof -
  let ?m' = "m(v \<mapsto> \<lparr>parent = v, rank = 0\<rparr>)"
  have "\<exists>c. in_component ?m' v' c"
    if v': "v'\<in>dom ?m'" for v'
  proof  (cases "v = v'")
    case False
    with assms v' have "v'\<in>dom m"
      by auto
    with assms preserve_add_node[of m] show ?thesis
      unfolding valid_union_find_def preserve_component_def
      by blast
  next
    case True
    with v' in_component_root[of ?m' v "\<lparr>parent = v, rank = 0\<rparr>"]
    show ?thesis by fastforce
  qed
  then show ?thesis
    unfolding valid_union_find_def ..
qed

subsection \<open>Correctness theorem\<close>
theorem add_node_correct: "(add_node, add_node_spec)\<in>Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding add_node_spec_def add_node_def
  apply refine_vcg
  by (auto simp: preserve_add_node add_node_valid)


section \<open>Find element in the data structure\<close>
subsection \<open>Definitions\<close>
definition find_spec :: "'v union_find \<Rightarrow> 'v \<Rightarrow> ('v union_find \<times> 'v) nres"
  where "find_spec m v \<equiv> do {
    ASSERT (v \<in> dom m \<and> valid_union_find m);
    SPEC (\<lambda>(m', p). valid_union_find m' \<and> preserve_component m m' \<and> dom m = dom m' \<and> in_component m v p)
  }"

definition loop_invariant :: "'v union_find \<Rightarrow> 'v \<Rightarrow> 'v union_find \<Rightarrow> 'v \<Rightarrow> bool"
  where "loop_invariant m v m' p \<equiv> preserve_component m m' \<and> 
    valid_union_find m' \<and> p \<in> dom m' \<and> dom m = dom m' \<and> same_component m' v p"

function find_set :: "'v union_find \<Rightarrow> 'v \<Rightarrow> ('v union_find \<times> 'v) nres"
  where "find_set m v = do {
    ASSERT (v \<in> dom m \<and> valid_union_find m);
    let node = the (m v);
    let p = parent node;
    if p \<noteq> v then do {
        (m, p) \<leftarrow> find_set m p;
        m \<leftarrow> update_parent m v p;
        RETURN (m, p)
    } else
        RETURN (m, p)
  }"
  by auto
  termination sorry (* TODO prove termination *)

definition find_set_while :: "'v union_find \<Rightarrow> 'v \<Rightarrow> ('v union_find \<times> 'v) nres"
  where "find_set_while m v \<equiv> do {
    ASSERT (v \<in> dom m \<and> valid_union_find m);
    (m, p) \<leftarrow> WHILEI
      (\<lambda>(m', p). loop_invariant m v m' p)
      (\<lambda>(m', p). parent (the (m' p)) \<noteq> p) (\<lambda>(m', p). RETURN (m', parent (the (m' p)))) (m, v);
    RETURN (m, p)
  }"

subsection \<open>Helping lemmas\<close>
lemma in_component_parent[simp]:
  assumes "in_component m v c"
  shows "in_component m (parent (the (m v))) c"
  using assms by (auto intro:in_component.cases[OF assms])

lemma parent_valid:
  assumes "valid_union_find m"
  assumes "m v = Some node"
  shows "m (parent node) \<noteq> None"
proof -
  from assms obtain c where c: "in_component m v c"
    unfolding valid_union_find_def by auto
  with assms in_component_parent[OF this] have "in_component m (parent node) c"
    by auto
  from in_component_dom(1)[OF this] show ?thesis
    by blast
qed

lemma same_component_root:
  assumes "same_component m v p"
  assumes "parent (the (m p)) = p"
  shows "in_component m v p"
proof -
  from assms(1) obtain c where vc: "in_component m v c" and pc: "in_component m p c"
    unfolding same_component_def by blast
  then have "p \<in> dom m"
    by (auto simp:in_component.cases[OF pc])
  with assms(2) have "in_component m p p"
    by auto
  with vc in_component_unique[OF pc] show ?thesis
    by auto
qed

subsection \<open>Correctness theorem\<close>
theorem find_correct: "(find_set_while, find_spec)\<in>Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding find_spec_def find_set_while_def loop_invariant_def preserve_component_def
  apply refine_vcg
  apply (auto simp: parent_valid)
  apply (simp add: same_component_trans[OF _ same_component_parent])
  apply (simp add: same_component_root)
  done

corollary find_correct': "find_set_while m v \<le> (find_spec m v)"
  using nres_relD[OF fun_relE1[OF fun_relE1[OF find_correct, of _ m]]]
  by auto


section \<open>Union two elements\<close>
subsection \<open>Definitions\<close>
definition union_spec :: "'v union_find \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('v union_find) nres"
  where "union_spec m a b \<equiv> do {
    ASSERT (a \<in> dom m \<and> b \<in> dom m \<and> valid_union_find m);
    SPEC (\<lambda>m'. valid_union_find m' \<and> preserve_component_union m m' a b \<and>  dom m = dom m' \<and> same_component m' a b)
  }"

definition union_sets :: "'v union_find \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('v union_find) nres"
  where "union_sets m a b \<equiv> do {
    ASSERT (a \<in> dom m \<and> b \<in> dom m \<and> valid_union_find m);
    (m', root_a) \<leftarrow> find_set_while m a;
    ASSERT (in_component m' a root_a \<and> valid_union_find m);
    (m'', root_b) \<leftarrow> find_set_while m' b;
    ASSERT (in_component m'' a root_a \<and> in_component m'' b root_b \<and>
            preserve_component m m'' \<and> valid_union_find m'');
    let rank_a = rank (the (m'' root_a));
    let rank_b = rank (the (m'' root_b));
    if root_b = root_a then do {
      RETURN m''
    } else if rank_a < rank_b then
      update_parent m'' root_a root_b
    else if rank_a > rank_b then
      update_parent m'' root_b root_a
    else do {
      m''' \<leftarrow> update_parent m'' root_a root_b;
      ASSERT(valid_union_find m''' \<and> same_component m''' a b \<and>
        preserve_component_union m m''' a b);
      m'''' \<leftarrow> update_rank m''' root_b (rank_b + 1);
      ASSERT(same_component m''' a b);
      RETURN m''''
    }
  }"

definition union_sets' :: "'v union_find \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('v union_find) nres"
  where "union_sets' m a b \<equiv> do {
    ASSERT (a \<in> dom m \<and> b \<in> dom m \<and> valid_union_find m);
    (m', root_a) \<leftarrow> find_spec m a;
    (m'', root_b) \<leftarrow> find_spec m' b;
    ASSERT (in_component m'' a root_a \<and> in_component m'' b root_b \<and>
            preserve_component m m'');
    let rank_a = rank (the (m'' root_a));
    let rank_b = rank (the (m'' root_b));
    if root_b = root_a then do {
      RETURN m''
    } else if rank_a < rank_b then
      update_parent_spec m'' root_a root_b
    else if rank_a > rank_b then
      update_parent_spec m'' root_b root_a
    else do {
      m''' \<leftarrow> update_parent_spec m'' root_a root_b;
      ASSERT(same_component m''' a b);
      m'''' \<leftarrow> update_rank_spec m''' root_b (rank_b + 1);
      RETURN m''''
    }
  }"

subsection \<open>Correctness theorem\<close>
theorem union_refine1: "(union_sets', union_spec)\<in>Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding union_sets'_def union_spec_def find_spec_def update_parent_spec_def update_rank_spec_def
  apply (refine_vcg)
  apply clarsimp_all
  apply (simp add: preserve_component_impl)+
  apply (fast elim: preserve_component_trans)
  apply (simp add: weaker_preserve_component)
  apply (simp add: domD[OF in_component_dom(2)])+
  apply (simp add: in_component_parent_root)+
  apply (simp add: preserve_component_union_trans_roots)
  apply (simp add: preserve_component_union_same)
  apply (simp add: domD[OF in_component_dom(2)])+
  apply (simp add: in_component_parent_root)+
  apply (simp add: preserve_component_union_sym[OF preserve_component_union_trans_roots])
  apply (simp add: same_component_sym[OF preserve_component_union_same])
  apply (simp add: domD[OF in_component_dom(2)])+
  apply (simp add: in_component_parent_root)+
  apply (simp add: preserve_component_union_same)
  apply (simp add: preserve_component_union_trans'[OF preserve_component_union_trans_roots])
  using preserve_component_impl_same
  apply blast
  done

lemma union_refine2: "(union_sets, union_sets')\<in>Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding union_sets_def union_sets'_def
  apply (refine_vcg)
  using find_correct update_parent_correct update_rank_correct
  apply auto
  sorry (* TODO refinement with actual functions *)

theorem union_correct: "(union_sets, union_spec)\<in>Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  using union_refine1 union_refine2
  sorry (* TODO overall correctness  *)

end
