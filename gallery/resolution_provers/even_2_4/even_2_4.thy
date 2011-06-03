theory even_2_4
imports Main
begin

ML {*
writeln ("Generating the E, SPASS, and Vampire TPTP problems and TSTP \
         \solutions in " ^ quote (getenv "ISABELLE_HOME_USER") ^ ".")
*}

inductive even where
"even 0" |
"even n \<Longrightarrow> even (Suc (Suc n))"

lemma Suc_Suc_0_eq_2: "Suc (Suc 0) = 2"
by (rule semiring_norm(115))

lemma Suc_Suc_2_eq_4: "Suc (Suc 2) = 4"
by (metis Bit0_def Suc_eq_plus1_left add_Pls_right less_add_Suc1
          nat_1_add_number_of not_add_less2 numeral_2_eq_2 succ_Bit0 succ_def
          zadd_assoc)

lemma "even 2 \<and> even 4"
sledgehammer [e spass vampire, overlord, blocking]
             (Suc_Suc_0_eq_2 Suc_Suc_2_eq_4 even.intros)
by (metis Suc_Suc_0_eq_2 Suc_Suc_2_eq_4 even.intros(1) even.intros(2))

end
