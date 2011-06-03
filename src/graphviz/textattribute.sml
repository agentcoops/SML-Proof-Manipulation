(* $Id: textattribute.sml 62 2008-08-20 11:20:33Z tbourke $
 *
 * Copyright (c) 2008 Timothy Bourke (University of NSW and NICTA)
 * All rights reserved.
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the "BSD License" which is distributed with the
 * software in the file LICENSE.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the BSD
 * License for more details.
 *
 * Attributes with minimal type structure.
 *)

structure TextAttribute =
struct
  datatype t = Att of string * string option

  fun name (Att (n, _)) = n

  fun hasValue (Att (_, NONE)) = false
    | hasValue _               = true

  fun value (Att (_, SOME v)) = v
    | value (Att (n, NONE))   = raise Fail ("attribute "^n^" has no value")

end

