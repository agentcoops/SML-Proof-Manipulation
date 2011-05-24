theory map_f_x_y
imports Main
begin

text {*
Short:
*}

lemma "map f [x, y] = [f x, f y]"
proof -
  have "ALL x1 x2. map x1 [x2] = [x1 x2]" by (metis map.simps(1) map.simps(2))
  hence "ALL x1 x2 x3. map x1 [x2, x3] = [x1 x2, x1 x3]" by (metis map.simps(2))
  thus "map f [x, y] = [f x, f y]" by metis
qed

text {*
Even shorter:
*}

lemma "map f [x, y] = [f x, f y]"
proof -
  have "ALL x1 x2. map x1 [x2] = [x1 x2]" by (metis map.simps(1) map.simps(2))
  thus "map f [x, y] = [f x, f y]" by (metis map.simps(2))
qed

end
