theory BreakGlobalInterpretation
imports Main
begin

locale foo =
  fixes a :: "'a \<Rightarrow> 'a"
begin

fun foo where "foo x = a x"

end

locale bar =
  fixes b :: "'a \<Rightarrow> 'a"
begin

fun bar where "bar x = b x"

end

locale foobar = bar a
  for a :: "'a \<Rightarrow> 'a"
begin

fun foobar where 
  "foobar x = bar x"

sublocale foo foobar .

end

global_interpretation foobar_imp: foobar id 
  defines bar_imp = foobar_imp.bar
  and foobar_imp = foobar_imp.foobar
  and foo_imp = foobar_imp.foo
  .

(* these rules only contain the newly defined names *)
thm foobar_imp.bar.simps
thm foobar_imp.foobar.simps
(* evaluation works *)
value "bar_imp (1::nat)"
value "foobar_imp (1::nat)"

(* this rule does not use the declared name foo_imp*)
thm foobar_imp.foo.simps

(* hence evaluation does not work *)
value "foo_imp (1::nat)"

(* workaround *)
lemma [code]: "foo_imp x = foobar_imp x"
  apply(subst foo_imp_def)
  apply(subst foo.foo.simps)
  apply(subst foobar_imp_def)
  ..

value "foo_imp (1::nat)"

end