theory Graham
  imports Main
begin

text\<open>
  We define the Knuth arrow as a recursive function:

  arrow a n b \<equiv> a \<up>\<^sup>n b
\<close>

fun arrow :: "nat  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"arrow a (Suc 0) b = a ^ b" |
"arrow a (Suc (Suc m)) 0 = 1" |
"arrow a (Suc (Suc m)) (Suc b) = arrow a (Suc m) (arrow a (Suc (Suc m)) b)"

lemma "arrow 2 1 4 = 16" by eval
lemma "arrow 4 1 3 = 64" by eval
lemma "arrow 2 2 4 = 65536" by eval

section "Proof that G > 0."

text\<open>
  We first prove that a \<up>\<^sup>n b > 0 for a > 0 and n > 0.
  This is done by computation induction.
\<close>

lemma arrow_gt_0: "\<lbrakk> a > 0; n > 0 \<rbrakk> \<Longrightarrow> arrow a n b > 0"
  by (induction a n b rule: arrow.induct) auto

fun g :: "nat \<Rightarrow> nat" where
"g 0 = arrow 3 4 3" |
"g (Suc n) = arrow 3 (g n) 3"

text\<open>
  Prove that g > 0.
\<close>

lemma g_gt_0: "g n > 0"
  using arrow_gt_0 by (induction n) auto

definition G :: nat where
"G \<equiv> g 63"

text\<open>
  Proving that G > 0 follows from the previously established lemmas.
\<close>

theorem G_gt_0: "G > 0"
  using g_gt_0 by (simp add: G_def)

end