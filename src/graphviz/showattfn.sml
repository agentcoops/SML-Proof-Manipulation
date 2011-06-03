(* $Id: showattfn.sml 62 2008-08-20 11:20:33Z tbourke $
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
 *)

functor ShowAttFn (val name : string
                   structure Att : ATTRIBUTE
                         and PPD : PP_DESC) =
struct
  val space = PPD.space 1
  val title = PPD.string name

  fun makeAtt a = PPD.hovBox (PPD.PPS.Rel 1, PPD.string (Att.name a)
      :: (if Att.hasValue a
          then [space, PPD.string "=", space, PPD.string (Att.value a)]
          else []))

  fun makeAttList sep []   = PPD.space 0
    | makeAttList sep atts = let
        fun make [att]       = [makeAtt att]
          | make (att::atts) = makeAtt att:: sep:: space:: make atts
      in PPD.hovBox (PPD.PPS.Rel 0, make atts) end

  fun showBoxedList strm []   = ()
    | showBoxedList strm atts = PPD.description (strm,
        PPD.hovBox (PPD.PPS.Rel 1, [PPD.nbSpace 1, PPD.string "[",
                      makeAttList (PPD.string ",") atts, PPD.string "]"]));

  fun showNamedList strm []   = ()
    | showNamedList strm atts =  (PPD.description (strm,
        PPD.hovBox (PPD.PPS.Rel 1, [title, PPD.nbSpace 1, PPD.string "[",
                      makeAttList (PPD.string ",") atts, PPD.string "]"]));
        PPD.PPS.cut strm)

  fun showList strm []   = ()
    | showList strm atts = (PPD.description (strm,
                             makeAttList (PPD.string ";") atts); PPD.PPS.cut strm)
end

