theory huntington_id
imports Main
begin

class common_algebra = uminus +
  fixes inf :: "'a => 'a => 'a" (infixl "\<sqinter>" 70)
  fixes sup :: "'a => 'a => 'a" (infixl "\<squnion>" 65)
  fixes bot :: "'a" ("\<bottom>")
  fixes top :: "'a" ("\<top>")
  assumes sup_assoc: "x \<squnion> (y \<squnion> z) = (x \<squnion> y) \<squnion> z"
  assumes sup_comm: "x \<squnion> y = y \<squnion> x"

context common_algebra begin

definition less_eq :: "'a => 'a => bool" (infix "\<sqsubseteq>" 50) where
   "x \<sqsubseteq> y = (x \<squnion> y = y)"
definition less :: "'a => 'a => bool" (infix "\<sqsubset>" 50) where
   "x \<sqsubset> y = (x \<sqsubseteq> y \<and> ~ y \<sqsubseteq> x)"
definition minus :: "'a => 'a => 'a"  (infixl "-" 65) where
   "minus x y = (x \<sqinter> - y)"

definition secret_object1 :: "'a" ("\<iota>") where
  "\<iota> == SOME x. True"

end

class ext_common_algebra = common_algebra +
  assumes inf_eq: "x \<sqinter> y = -(- x \<squnion> - y)"
  assumes top_eq: "\<top> = \<iota> \<squnion> - \<iota>"
  assumes bot_eq: "\<bottom> = -(\<iota> \<squnion> - \<iota>)"

class boolean_algebra_II =
  common_algebra +
  assumes inf_comm: "x \<sqinter> y = y \<sqinter> x"
  assumes inf_assoc: "x \<sqinter> (y \<sqinter> z) = (x \<sqinter> y) \<sqinter> z"
  assumes sup_absorb: "x \<squnion> (x \<sqinter> y) = x"
  assumes inf_absorb: "x \<sqinter> (x \<squnion> y) = x"
  assumes sup_inf_distrib1: "x \<squnion> y \<sqinter> z = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
  assumes sup_compl: "x \<squnion> - x = \<top>"
  assumes inf_compl: "x \<sqinter> - x = \<bottom>"

class huntington_algebra = ext_common_algebra +
  assumes huntington: "- (-x \<squnion> -y) \<squnion> - (-x \<squnion>  y) = x"

class robbins_algebra = ext_common_algebra +
  assumes robbins: "- (- (x \<squnion> y) \<squnion> - (x \<squnion> -y)) = x"

context boolean_algebra_II begin

lemma boolean_II_is_boolean:
   "class.boolean_algebra minus uminus (op \<sqsubseteq>) (op \<sqsubset>) (op \<sqinter>) (op \<squnion>) \<bottom> \<top>"
apply unfold_locales
apply (metis inf_absorb inf_assoc inf_comm inf_compl
             less_def less_eq_def minus_def
             sup_absorb sup_assoc sup_comm
             sup_compl sup_inf_distrib1
             sup_absorb inf_comm)+
done

end

context boolean_algebra begin

lemma boolean_is_boolean_II:
  "class.boolean_algebra_II uminus inf sup bot top"
apply unfold_locales
apply (metis sup_assoc sup_commute sup_inf_absorb sup_compl_top
             inf_assoc inf_commute inf_sup_absorb inf_compl_bot
             sup_inf_distrib1)+
done

end

context boolean_algebra begin
lemma boolean_is_huntington:
  "class.huntington_algebra uminus inf sup bot top"
apply unfold_locales
apply (metis double_compl inf_sup_distrib1 inf_top_right
             compl_inf inf_commute inf_compl_bot
             compl_sup sup_commute sup_compl_top
             sup_compl_top sup_assoc)+
done

end

context boolean_algebra_II begin

lemma boolean_II_is_huntington:
  "class.huntington_algebra uminus (op \<sqinter>) (op \<squnion>) \<bottom> \<top>"
proof -
  interpret boolean:
    boolean_algebra minus uminus "op \<sqsubseteq>" "op \<sqsubset>" "op \<sqinter>" "op \<squnion>" \<bottom> \<top>
      by (fact boolean_II_is_boolean)
   thus ?thesis by (simp add: boolean.boolean_is_huntington)
qed

end

context huntington_algebra begin

text {*
A fairly long chain of rewrites obtained from Waldmeister:
*}

lemma "x \<squnion> -x = -x \<squnion> -(-x)"
(* sledgehammer [remote_waldmeister e] *)
proof -
  have F1: "ALL w v u. u \<squnion> (v \<squnion> w) = w \<squnion> (u \<squnion> v)"
    by (metis sup_assoc sup_comm)
  have "ALL w v u. u \<squnion> (v \<squnion> w) = v \<squnion> u \<squnion> w"
    by (metis sup_assoc sup_comm)
  hence F2: "ALL w v u. u \<squnion> (v \<squnion> w) = v \<squnion> (u \<squnion> w)"
    by (metis sup_assoc)
  have F3: "ALL w v u. u \<squnion> (v \<squnion> w) = w \<squnion> (v \<squnion> u)"
    using F1 by (metis sup_comm)
  have F4: "ALL v u. - (- u \<squnion> v) \<squnion> - (- u \<squnion> - v) = u"
    by (metis huntington sup_comm)
  hence F5: "ALL v u. u = - (v \<squnion> - u) \<squnion> - (- u \<squnion> - v)"
    by (metis sup_comm)
  hence F6: "ALL v u. u = - (v \<squnion> - u) \<squnion> - (- v \<squnion> - u)"
    by (metis sup_comm)
  have F7: "ALL w v u. - (- u \<squnion> v) \<squnion> (- (- u \<squnion> - v) \<squnion> w) = u \<squnion> w"
    using F4 by (metis sup_assoc)
  hence "ALL v u. u \<squnion> - (- u \<squnion> - (- v)) = - (- u \<squnion> v) \<squnion> u"
    using F4 by metis
  hence F8: "ALL v u. u \<squnion> - (- u \<squnion> - (- v)) = u \<squnion> - (- u \<squnion> v)"
    by (metis sup_comm)
  hence "ALL w v u. - (- u \<squnion> - (- v)) \<squnion> (w \<squnion> u) = w \<squnion> (u \<squnion> - (- u \<squnion> v))"
    using F1 by metis
  hence F9: "ALL v w u. u \<squnion> (w \<squnion> - (- u \<squnion> - (- v))) = w \<squnion> (u \<squnion> - (- u \<squnion> v))"
    using F3 by metis
  have "ALL v u. u \<squnion> - (- (- u) \<squnion> - v) = - (- u \<squnion> v) \<squnion> v"
    using F6 F7 by metis
  hence F10: "ALL v u. u \<squnion> - (- (- u) \<squnion> - v) = v \<squnion> - (- u \<squnion> v)"
    by (metis sup_comm)
  have "ALL v u. - u \<squnion> v = - (- u \<squnion> - v \<squnion> - (- u \<squnion> v)) \<squnion> - u"
    using F4 F5 by metis
  hence "ALL v u. - u \<squnion> v = - (- u \<squnion> (- v \<squnion> - (- u \<squnion> v))) \<squnion> - u"
    by (metis sup_assoc)
  hence F11: "ALL v u. - u \<squnion> v = - u \<squnion> - (- u \<squnion> (- v \<squnion> - (- u \<squnion> v)))"
    by (metis sup_comm)
  have "ALL v u. - u \<squnion> - v = - (- u \<squnion> v \<squnion> - (- u \<squnion> - v)) \<squnion> - u"
    using F4 F6 by metis
  hence "ALL v u. - u \<squnion> - v = - (- u \<squnion> (v \<squnion> - (- u \<squnion> - v))) \<squnion> - u"
    by (metis sup_assoc)
  hence "ALL v u. - u \<squnion> - v = - u \<squnion> - (- u \<squnion> (v \<squnion> - (- u \<squnion> - v)))"
    by (metis sup_comm)
  hence "ALL u. - (- u) \<squnion> - (- u) = - (- u) \<squnion> - (- (- u) \<squnion> (- u \<squnion> - (- (- u) \<squnion> u)))"
    using F8 by metis
  hence "ALL u. - (- u) \<squnion> - (- u) = - (- u) \<squnion> u"
    using F11 by metis
  hence "ALL u. - (- u) \<squnion> - (- u) = u \<squnion> - (- u)"
    by (metis sup_comm)
  hence "ALL u. - u \<squnion> - (- u \<squnion> - u) = u \<squnion> - (u \<squnion> - (- u))"
    using F10 by metis
  hence "ALL v u. - u \<squnion> (- (- u \<squnion> - u) \<squnion> v) = u \<squnion> - (u \<squnion> - (- u)) \<squnion> v"
    by (metis sup_assoc)
  hence "ALL v u. - u \<squnion> (- (- u \<squnion> - u) \<squnion> v) = u \<squnion> (- (u \<squnion> - (- u)) \<squnion> v)"
    by (metis sup_assoc)
  hence "ALL u. u \<squnion> (- (u \<squnion> - (- u)) \<squnion> - (- u \<squnion> - (- u))) = - u \<squnion> u"
    using F4 by metis
  hence "ALL u. - (u \<squnion> - (- u)) \<squnion> (u \<squnion> - (- u \<squnion> u)) = - u \<squnion> u"
    using F9 by metis
  hence "ALL u. - (- u \<squnion> u) \<squnion> (u \<squnion> - (u \<squnion> - (- u))) = - u \<squnion> u"
    using F3 by metis
  hence "ALL u. u \<squnion> (- (- u \<squnion> u) \<squnion> - (u \<squnion> - (- u))) = - u \<squnion> u"
    using F2 by metis
  hence "ALL u. u \<squnion> (- (u \<squnion> - u) \<squnion> - (u \<squnion> - (- u))) = - u \<squnion> u"
    by (metis sup_comm)
  hence "ALL u. u \<squnion> (- (u \<squnion> - u) \<squnion> - (u \<squnion> - (- u))) = u \<squnion> - u"
    by (metis sup_comm)
  hence "ALL u. - u \<squnion> - (- u) = - u \<squnion> u"
    using F4 by metis
  thus ?thesis
    by (metis sup_comm)
qed

text {*
A manually restructured version of the above. This is one of many ways of
reorganizing the proof so as to make the underlying structure more apparent.
*}

lemma "x \<squnion> -x = -x \<squnion> -(-x)"
proof -
  have rot_r: "ALL w v u. u \<squnion> (v \<squnion> w) = w \<squnion> (u \<squnion> v)"
    by (metis sup_assoc sup_comm)
  hence rev: "ALL w v u. u \<squnion> (v \<squnion> w) = w \<squnion> (v \<squnion> u)"
    by (metis sup_comm)
  have huntington_comm: "ALL v u. - (- u \<squnion> v) \<squnion> - (- u \<squnion> - v) = u"
    by (metis huntington sup_comm)
  hence huntington_comm2: "ALL v u. u = - (v \<squnion> - u) \<squnion> - (- v \<squnion> - u)"
    by (metis sup_comm)
  have huntington_assoc: "ALL w v u. - (- u \<squnion> v) \<squnion> (- (- u \<squnion> - v) \<squnion> w) = u \<squnion> w"
    using huntington_comm by (metis sup_assoc)

  have "ALL u. - (u \<squnion> - (- u)) \<squnion> (u \<squnion> - (- u \<squnion> u)) = - u \<squnion> u"
  proof -
    have "ALL w v u. - (- u \<squnion> - (- v)) \<squnion> (w \<squnion> u) = w \<squnion> (u \<squnion> - (- u \<squnion> v))"
      using rot_r huntington_assoc by metis
    hence wuuv: "ALL v w u. u \<squnion> (w \<squnion> - (- u \<squnion> - (- v))) = w \<squnion> (u \<squnion> - (- u \<squnion> v))"
      using rev by metis

    have "ALL u. - u \<squnion> - (- u \<squnion> - u) = u \<squnion> - (u \<squnion> - (- u))"
    proof -
      have "ALL v u. u \<squnion> - (- (- u) \<squnion> - v) = - (- u \<squnion> v) \<squnion> v"
        using huntington_comm2 huntington_assoc by metis
      hence vuv: "ALL v u. u \<squnion> - (- (- u) \<squnion> - v) = v \<squnion> - (- u \<squnion> v)"
        by (metis sup_comm)

      have "ALL v u. - u \<squnion> v = - (- u \<squnion> - v \<squnion> - (- u \<squnion> v)) \<squnion> - u"
        using huntington_comm by (metis sup_comm)
      hence "ALL v u. - u \<squnion> v = - (- u \<squnion> (- v \<squnion> - (- u \<squnion> v))) \<squnion> - u"
        by (metis sup_assoc)
      hence uuvuv: "ALL v u. - u \<squnion> v = - u \<squnion> - (- u \<squnion> (- v \<squnion> - (- u \<squnion> v)))"
        by (metis sup_comm)

      have "ALL u. - (- u) \<squnion> - (- u) = - (- u) \<squnion> - (- (- u) \<squnion> (- u \<squnion> - (- (- u) \<squnion> u)))"
      proof -
        have "ALL v u. - u \<squnion> - v = - (- u \<squnion> v \<squnion> - (- u \<squnion> - v)) \<squnion> - u"
          using huntington_comm huntington_comm2 by metis
        hence "ALL v u. - u \<squnion> - v = - (- u \<squnion> (v \<squnion> - (- u \<squnion> - v))) \<squnion> - u"
          by (metis sup_assoc)
        hence uuvuv': "ALL v u. - u \<squnion> - v = - u \<squnion> - (- u \<squnion> (v \<squnion> - (- u \<squnion> - v)))"
          by (metis sup_comm)

        have "ALL v u. u \<squnion> - (- u \<squnion> - (- v)) = - (- u \<squnion> v) \<squnion> u"
          using huntington_comm huntington_assoc by metis
        hence "ALL v u. u \<squnion> - (- u \<squnion> - (- v)) = u \<squnion> - (- u \<squnion> v)"
          by (metis sup_comm)
        thus "ALL u. - (- u) \<squnion> - (- u) = - (- u) \<squnion> - (- (- u) \<squnion> (- u \<squnion> - (- (- u) \<squnion> u)))"
          using uuvuv' by metis
      qed
      hence "ALL u. - (- u) \<squnion> - (- u) = - (- u) \<squnion> u"
        using uuvuv by metis
      hence "ALL u. - (- u) \<squnion> - (- u) = u \<squnion> - (- u)"
        by (metis sup_comm)
      thus ?thesis using vuv by metis
    qed
    hence "ALL v u. - u \<squnion> (- (- u \<squnion> - u) \<squnion> v) = u \<squnion> - (u \<squnion> - (- u)) \<squnion> v"
      by (metis sup_assoc)
    hence "ALL v u. - u \<squnion> (- (- u \<squnion> - u) \<squnion> v) = u \<squnion> (- (u \<squnion> - (- u)) \<squnion> v)"
      by (metis sup_assoc)
    hence "ALL u. u \<squnion> (- (u \<squnion> - (- u)) \<squnion> - (- u \<squnion> - (- u))) = - u \<squnion> u"
      using huntington_comm by metis
    thus ?thesis using wuuv by metis
  qed
  hence "ALL u. - (- u \<squnion> u) \<squnion> (u \<squnion> - (u \<squnion> - (- u))) = - u \<squnion> u"
    using rev by metis
  hence "ALL u. u \<squnion> (- (- u \<squnion> u) \<squnion> - (u \<squnion> - (- u))) = - u \<squnion> u"
    by (metis sup_assoc sup_comm)
  hence "ALL u. u \<squnion> (- (u \<squnion> - u) \<squnion> - (u \<squnion> - (- u))) = - u \<squnion> u"
    by (metis sup_comm)
  hence "ALL u. u \<squnion> (- (u \<squnion> - u) \<squnion> - (u \<squnion> - (- u))) = u \<squnion> - u"
    by (metis sup_comm)
  hence "ALL u. - u \<squnion> - (- u) = - u \<squnion> u"
    using huntington_comm by metis
  thus ?thesis
    by (metis sup_comm)
qed

text {*
The original human-written proof:
*}

lemma "x \<squnion> -x = -x \<squnion> -(-x)"
proof -
  from huntington have
  "x \<squnion> -x = -(-x \<squnion> -(-(-x))) \<squnion> -(-x \<squnion> -(-x)) \<squnion>
             (-(-(-x) \<squnion> -(-(-x))) \<squnion> -(-(-x) \<squnion> -(-x)))"
    by simp
  also from sup_comm have
  "\<dots> = -(-(-x) \<squnion> -(-x)) \<squnion> -(-(-x) \<squnion> -(-(-x))) \<squnion>
        (-(-(-x) \<squnion> -x) \<squnion> -(-(-(-x)) \<squnion> -x))"
    by simp
  also from sup_assoc have
  "\<dots> = -(-(-x) \<squnion> -(-x)) \<squnion>
        (-(-(-x) \<squnion> -(-(-x))) \<squnion> -(-(-x) \<squnion> -x)) \<squnion>
       -(-(-(-x)) \<squnion> -x)"
    by simp
  also from sup_comm have
  "\<dots> = -(-(-x) \<squnion> -(-x)) \<squnion>
        (-(-(-x) \<squnion> -x) \<squnion> -(-(-x) \<squnion> -(-(-x)))) \<squnion>
       -(-(-(-x)) \<squnion> -x)"
    by simp
  also from sup_assoc have
  "\<dots> = -(-(-x) \<squnion> -(-x)) \<squnion> -(-(-x) \<squnion> -x) \<squnion>
        (-(-(-x) \<squnion> -(-(-x))) \<squnion> -(-(-(-x)) \<squnion> -x))"
    by simp
  also from sup_comm have
  "\<dots> = -(-(-x) \<squnion> -(-x)) \<squnion> -(-(-x) \<squnion> -x) \<squnion>
        (-(-(-(-x)) \<squnion> -(-x)) \<squnion> -(-(-(-x)) \<squnion> -x))"
    by simp
  also from huntington have
  "\<dots> = -x \<squnion> -(-x)"
    by simp
  finally show ?thesis by simp
qed

end

end
