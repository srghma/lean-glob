module
import TypedPath.PosixPath
meta import TypedPath.PosixPath

namespace Posix.Tests

def checkOkOption {e a} [BEq a] (x : Except e (Option a)) (expected : Option a) : Bool :=
  match x with
  | Except.ok v => v == expected
  | Except.error _ => false

def checkError {e a} [BEq e] (x : Except e a) (expected : e) : Bool :=
  match x with
  | Except.error err => err == expected
  | Except.ok _ => false

def checkOkStringAny (x : Except ParseAutoError AnyPosixPath) (expected : String) : Bool :=
  match x with
  | Except.ok p => toString p.path == expected
  | Except.error _ => false

def checkOkStringRaw (x : Except ParseError (PosixPath true .Abs .File false)) (expected : String) : Bool :=
  match x with
  | Except.ok p => toString p == expected
  | Except.error _ => false

-- --- Component-level: NAME_MAX -----------------------------------------

#guard checkOkOption (parsePathComponentWithConfig .Throw true "var") (some (.normal (PosixNormalComponent.mk! "var")))
#guard checkError (parsePathComponentWithConfig .Throw true ".") (ParseError.InvalidComponent ".")
#guard checkOkOption (parsePathComponentWithConfig .Throw true "..") (some .parent)
#guard checkError (parsePathComponentWithConfig .Throw false "..") ParseError.ParentWasNotAllowedByPresentInInput
#guard checkOkOption (parsePathComponentWithConfig .Skip false "..") none

-- --- Auto Parsing ------------------------------------------------------

#guard checkOkStringAny (parsePosixPathAuto "/var/log/syslog") "/var/log/syslog"
#guard checkOkStringAny (parsePosixPathAuto "config.json") "config.json"
#guard checkOkStringAny (parsePosixPathAuto "./scripts/deploy.sh") "scripts/deploy.sh"
#guard checkOkStringAny (parsePosixPathAuto "../logs/error.log") "../logs/error.log"
#guard checkOkStringAny (parsePosixPathAuto "..") ".."
#guard checkOkStringAny (parsePosixPathAuto "../") "../"
#guard checkOkStringAny (parsePosixPathAuto ".../") ".../"

#guard checkOkStringAny (parsePosixPathAuto ".") "."
#guard checkOkStringAny (parsePosixPathAuto "./") "."
#guard checkError (parsePosixPathAuto "") ParseAutoError.EmptyPath

-- A component that's individually too long fails.
#guard checkError (parsePosixPathAuto ("/" ++ "".pushn 'a' 300)) (ParseAutoError.InvalidComponent ("".pushn 'a' 300))

-- --- Fully validated parsing: PATH_MAX -------------------------------

-- 18 segments of 250 bytes + 17 separators = 4517 bytes > PATH_MAX (4095),
-- even though every individual segment is well under NAME_MAX (255).
def longSeg : String := "".pushn 'a' 250
def tooLongPath : String := "/" ++ String.intercalate "/" (List.replicate 18 longSeg)

#guard checkError (parsePosixPathAuto tooLongPath) ParseAutoError.PathTooLong

-- --- parsePosixPath Explicit Parsing -----------------------------------

def dummyExpected : ExpectedPosixPath := ⟨false, true, .Abs, .File⟩
def dummyConfig : Config := ⟨true, true, .Throw, .Throw, .Throw, .Throw, .Throw, .Throw⟩

#guard checkOkStringRaw (parsePosixPath dummyExpected dummyConfig "/var/log/syslog") "/var/log/syslog"
#guard checkError (parsePosixPath dummyExpected dummyConfig "var/log/syslog") ParseError.RequestedAbsButNoSlash
#guard checkError (parsePosixPath dummyExpected dummyConfig "/var/log/syslog/") ParseError.RequestedFileButTrailingSlash

end Posix.Tests
