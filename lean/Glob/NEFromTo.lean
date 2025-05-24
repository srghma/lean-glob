import Glob.NonEmptyString
import Glob.NonEmptyList
import Batteries.Data.List.Basic

private abbrev LS := List String
private abbrev NELS := NonEmptyList String
private abbrev LNES := List NonEmptyString
private abbrev NELNES := NonEmptyList NonEmptyString

namespace ToNE

----------- Upgraders that use filterMap (alternative name is `compact`)

namespace FilterMap

@[inline] def «LS->LNES»     : LS   → LNES          := (·.filterMap NonEmptyString.fromString?)
@[inline] def «LS->NELS»     : LS   → Option NELS   := NonEmptyList.fromList?
@[inline] def «LS->NELNES»   : LS   → Option NELNES := λ xs => NonEmptyList.fromList? («LS->LNES» xs)
@[inline] def «NELS->LNES»   : NELS → LNES          := («LS->LNES» ·.val)
@[inline] def «NELS->NELNES» : NELS → Option NELNES := λ xs => NonEmptyList.fromList? («LS->LNES» xs.val)
@[inline] def «LNES->NELS»   : LNES → Option NELS   := λ xs => NonEmptyList.fromList? (xs.map (·.val))
@[inline] def «LNES->NELNES» : LNES → Option NELNES := NonEmptyList.fromList?

end FilterMap

----------- Upgraders that use traverse

namespace Traverse

@[inline] def «LS->LNES»     : LS   → Option LNES   := List.traverse NonEmptyString.fromString?
@[inline] def «LS->NELS»     : LS   → Option NELS   := NonEmptyList.fromList?
@[inline] def «LS->NELNES»   : LS   → Option NELNES := NonEmptyList.fromList? <=< «LS->LNES»
@[inline] def «NELS->LNES»   : NELS → Option LNES   := («LS->LNES» ·.val)
@[inline] def «NELS->NELNES» : NELS → Option NELNES := («LS->NELNES» ·.val)
@[inline] def «LNES->NELS»   : LNES → Option NELS   := λ xs => NonEmptyList.fromList? (xs.map (·.val))
@[inline] def «LNES->NELNES» : LNES → Option NELNES := NonEmptyList.fromList?

end Traverse

end ToNE
----------- Downgraders

namespace FromNE

@[inline] def «LNES->LS»     : LNES →   LS   := (·.map (·.val))
@[inline] def «NELS->LS»     : NELS →   LS   := (·.val)
@[inline] def «NELNES->LS»   : NELNES → LS   := (·.val.map (·.val))
@[inline] def «NELNES->LNES» : NELNES → LNES := (·.val)
@[inline] def «NELNES->NELS» : NELNES → NELS := λ xs => ⟨xs.val.map (·.val), by
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
