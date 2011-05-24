theory map_f_x
imports Main
begin

text {*
Straightforward rendering of the Waldmeister proof. Notice however that the
\texttt{reduction} steps have been turned around.
*}

lemma "map f [x] = [f x]"
proof -
  have 0110: "ALL x. map x [] = []" by (metis map.simps(1))
  have 0120: "ALL x. map x [] = []" using 0110 by metis
  have 0200: "ALL x y z. map x (y # z) = x y # map x z" by (metis map.simps(2))
  have 0210: "ALL x y z. map x (y # z) = x y # map x z" using 0200 by metis
  have 0220: "ALL x y z. x y # map x z = map x (y # z)" using 0210 by metis
  have 0300: "ALL x y. map x [y] = [x y]" using 0220 0120 by metis
  have 0310: "ALL x y. map x [y] = [x y]" using 0300 by metis
  have 0320: "ALL x y. map x [y] = [x y]" using 0310 by metis

  have 1002: "True" by metis
  have 1001: "[f x] = [f x]" using 1002 by metis
  show 1000: "map f [x] = [f x]" using 1001 0320 by metis
qed

text {*
Once we clean up trivial steps and introduce \textbf{hence} and \textbf{thus},
we get the following much nicer proof:
*}

lemma "map f [x] = [f x]"
proof -
  have "ALL x y z. x y # map x z = map x (y # z)" by (metis map.simps(2))
  hence "ALL x y. map x [y] = [x y]" by (metis map.simps(1))
  thus "map f [x] = [f x]" by metis
qed

text {*
We can do better. Observing that the very last step is merely an instance of the
previous step, we can omit the previous step:
*}

lemma "map f [x] = [f x]"
proof -
  have "ALL x y z. x y # map x z = map x (y # z)" by (metis map.simps(2))
  thus "map f [x] = [f x]" by (metis map.simps(1))
qed

end
