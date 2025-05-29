import Glob.Data.NonEmptyString
import Glob.Data.NonEmptyList
import Batteries.Data.List.Basic

private abbrev L := List
private abbrev NEL := NonEmptyList
private abbrev LS := List String
private abbrev NELS := NonEmptyList String
private abbrev LNES := List NonEmptyString
private abbrev NELNES := NonEmptyList NonEmptyString

namespace ToNE

@[inline] def «L_->NEL_» : L a → Option (NEL a) := NonEmptyList.fromList?
@[inline] def «LNES->NELS»   : LNES → Option NELS := λ xs => NonEmptyList.fromList? (xs.map (·.toString))

-- @[inline] def List.«LS->LNES»     : LS   → LNES          := (·.filterMap NonEmptyString.fromString?)
-- def x : LS := [""]
-- def x2 := x.«LS->LNES»

----------- Upgraders that use filterMap (alternative name is `compact`) (they are lax, e.g. ["", "foo"] to ["foo"])

namespace FilterMap

@[inline] def «LS->LNES»     : LS   → LNES          := (·.filterMap NonEmptyString.fromString?)
@[inline] def «LS->NELNES»   : LS   → Option NELNES := λ xs => NonEmptyList.fromList? («LS->LNES» xs)
@[inline] def «NELS->LNES»   : NELS → LNES          := («LS->LNES» ·.toList)
@[inline] def «NELS->NELNES» : NELS → Option NELNES := λ xs => NonEmptyList.fromList? («LS->LNES» xs.toList)

end FilterMap

----------- Upgraders that use traverse (they are strict, e.g. ["", "foo"] to .none)

namespace Traverse

@[inline] def «LS->LNES»     : LS   → Option LNES   := List.traverse NonEmptyString.fromString?
@[inline] def «LS->NELNES»   : LS   → Option NELNES := NonEmptyList.fromList? <=< «LS->LNES»
@[inline] def «NELS->LNES»   : NELS → Option LNES   := («LS->LNES» ·.toList)
@[inline] def «NELS->NELNES» : NELS → Option NELNES := («LS->NELNES» ·.toList)

end Traverse

end ToNE
----------- Downgraders

namespace FromNE

@[inline] def «LNES->LS»     : LNES →   LS   := (·.map (·.toString))
@[inline] def «NELS->LS»     : NELS →   LS   := (·.toList)
@[inline] def «NELNES->LS»   : NELNES → LS   := (·.toList.map (·.toString))
@[inline] def «NELNES->LNES» : NELNES → LNES := (·.toList)
@[inline] def «NELNES->NELS» : NELNES → NELS := λ xs => ⟨xs.toList.map (·.toString), by
  -- proof that result is non-empty
  have h := xs.property
  simp at h
  intro contra
  have := congrArg List.length contra
  simp_all [List.length_map]⟩

end FromNE

-------------------- Remove? I wanted to generate functions using macros
namespace TName
inductive TName : Type 1 where
  | TName_LS
  | TName_NELS
  | TName_LNES
  | TName_NELNES
  deriving BEq, Repr --, DecidableEq

def TName.toType : TName → Type
  | TName_LS => LS
  | TName_NELS => NELS
  | TName_LNES => LNES
  | TName_NELNES => NELNES

def typesBelow : TName → List TName
  | .TName_LS => []
  | .TName_NELS => [.TName_LS]
  | .TName_LNES => [.TName_LS]
  | .TName_NELNES => [.TName_NELS, .TName_LS, .TName_LNES]

def typesAbove : TName → List TName
  | .TName_LS => [.TName_NELS, .TName_LNES, .TName_NELNES]
  | .TName_NELS => [.TName_NELNES]
  | .TName_LNES => [.TName_NELNES]
  | .TName_NELNES => []

def typesBelowTypes (t : TName) : List Type := (typesBelow t).map (·.toType)
end TName
