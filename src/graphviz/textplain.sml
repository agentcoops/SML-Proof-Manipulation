(* $Id: textplain.sml 62 2008-08-20 11:20:33Z tbourke $
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
 * Original code to read labels as plain text.
 *
 * The following forms are accepted:
 *      /[^"[:space:]][^[:space:]]*/      Unquoted, single word identifier
 *      /"([^"]|\\")*"/                   Quoted ("") identifier
 *      /<([^>]|\\>)*">/                  Quoted (<>) identifier
 * Note: General HTML labels (multiple tags) are NOT supported.
 *)

structure TextPlain = PlainFn (
  type id    = string
   and label = string
   and style = string
   and shape = string
   and color = string

  local
    infix >>; fun f >> g = Option.composePartial (g, f)
    fun tochar c = case Char.fromCString (implode [#"\\", c]) of
                     NONE   => if      c = #"l" then SOME [#"l", #"\\"]
                               else if c = #"r" then SOME [#"r", #"\\"]
                               else if c = #"{" then SOME [#"{", #"\\"]
                               else if c = #"}" then SOME [#"}", #"\\"]
                               else if c = #"<" then SOME [#"<", #"\\"]
                               else if c = #">" then SOME [#">", #"\\"]
                               else if c = #"|" then SOME [#"|", #"\\"]
                               else if c = #" " then SOME [#" ", #"\\"]
                               else if c = #"\n" then SOME [#"\n"]
                                       (* Graphviz seems to itself escape and
                                        * wrap lines that are too long. *)
                               else NONE
                   | SOME c => SOME [c]
  in

  (* Work around for delimiter bug in GraphViz.
   * TODO: tidy this up or get rid of it! *)
  fun greedyDelimiterLineScan delim rdr strm = let
      fun findLast ((last, laststrm), curr, strm) = case rdr strm of
          NONE => NONE
        | SOME (c, strm') => if c = delim
                             then findLast ((curr, strm'), c::curr, strm')
                             else if c = #"\n"
                               then SOME (implode (rev last), laststrm)
                               else findLast ((last, laststrm), c::curr, strm')
    in findLast (([], strm), [], strm) end

  fun scanString rdr strm = let
    fun escaped next (str, strm) = let
      fun split (c, strm') = (tochar >> (fn cs=>next (cs @ str, strm'))) c
    in (rdr >> split) strm end
    
    fun nextchar terminator (str, strm) = let
      fun split (c, strm') =
        if c = #"\\" then escaped (nextchar terminator) (str, strm')
        else if c = terminator then SOME (implode (rev str), strm')
        else (nextchar terminator) (c::str, strm')
    in (rdr >> split) strm end
    
    fun readword (str, strm) = let
      fun next (c, strm') =
        if Char.isSpace c then SOME (implode (rev str), strm)
        else readword (c::str, strm')
    in (rdr >> next) strm end

    and quote (c, strm') = if c = #"\"" then nextchar #"\"" ([], strm')
                           (*else if c = #"<" then nextchar #">" ([], strm') * (*XXX*)*)
                           else if c = #"<" then greedyDelimiterLineScan #">" rdr strm'
                           else readword ([c], strm')

  in (rdr >> quote) strm end
  end (* local *)

  val scanId    = scanString
  val scanLabel = scanString
  val scanStyle = scanString
  val scanShape = scanString
  val scanColor = scanString

  fun idToString    x = x
  fun labelToString x = x
  fun styleToString x = x
  fun shapeToString x = x
  fun colorToString x = x
)

