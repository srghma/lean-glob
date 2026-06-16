module
public import Init.System.IO
public import Lean
public import Lean.Data.RBMap
public import Std.Data.HashSet
public import Lean.Data.RBTree
public import Lean.Elab.Term
public import Init.Meta
public import Lean.Parser.Term
public import NonEmpty.String
public import NonEmpty.List
public import NonEmpty.Aliases.FunctorsAndScalars
public import NonEmpty.List.Upgraders
@[expose] public section

open NonEmpty.String NonEmpty.List NonEmpty.Aliases
open System (FilePath)

-- \f<< -> \f>>
@[inline] def FilePath.Lax.«->L/NES» (p : FilePath) : «L/NES» := NonEmpty.List.FilterMap.«L/S->L/NES» p.components
@[inline] def FilePath.Lax.«->NEL/NES»  (p : FilePath) : Option «NEL/NES» := NonEmpty.List.FilterMap.«L/S->NEL/NES» p.components
@[inline] def FilePath.Strict.«->L/NES» (p : FilePath) : Option «L/NES» := NonEmpty.List.Traverse.«L/S->L/NES» p.components
@[inline] def FilePath.Strict.«->NEL/NES» (p : FilePath) : Option «NEL/NES» := NonEmpty.List.Traverse.«L/S->NEL/NES» p.components
end
