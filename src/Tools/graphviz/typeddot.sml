(* $Id: typeddot.sml 62 2008-08-20 11:20:33Z tbourke $
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

structure TypedDot : DOT = DotFn (
                       structure Id = struct open String; type t = string end
                       structure EdgeAtt  = TypedAttributes.Edge
                       structure NodeAtt  = TypedAttributes.Node
                       structure GraphAtt = TypedAttributes.Graph
                     )

