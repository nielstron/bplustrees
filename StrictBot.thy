theory StrictBot
imports Main
begin

class sbot =
  fixes sbot :: 'a ("\<bottom>")

class order_sbot = order + sbot +
  assumes sbot_strict_least: "\<bottom> < a"
begin

sublocale sbot: ordering_top greater_eq greater sbot
  apply standard 
  by (simp add: local.order.strict_implies_order local.sbot_strict_least)


lemma le_sbot:
  "a \<le> \<bottom> \<Longrightarrow> a = \<bottom>"
  by (fact sbot.extremum_uniqueI)

lemma sbot_unique:
  "a \<le> \<bottom> \<longleftrightarrow> a = \<bottom>"
  by (fact sbot.extremum_unique)

lemma not_less_sbot:
  "\<not> a < \<bottom>"
  by (fact sbot.extremum_strict)

lemma sbot_less:
  "a \<noteq> \<bottom> \<longleftrightarrow> \<bottom> < a"
  by (fact sbot.not_eq_extremum)

lemma sbot_strict_less[simp]: "\<bottom> < a"
  by (fact sbot_strict_least)

lemma max_sbot[simp]: "max sbot x = x"
by(simp add: max_def sbot_unique)

lemma max_sbot2[simp]: "max x sbot = x"
by(simp add: max_def sbot_unique)

lemma min_sbot[simp]: "min sbot x = sbot"
by(simp add: min_def sbot_unique)

lemma min_sbot2[simp]: "min x sbot = sbot"
by(simp add: min_def sbot_unique)

end

end