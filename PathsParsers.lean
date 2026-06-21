-- ====================================================================
-- Common Definitions & Custom Splitter
-- ====================================================================

inductive PathComponent where
  | current                  -- "."
  | parent                   -- ".."
  | normal (name : String)   -- Standard file/directory name -- TODO: proof that component is nonEmpty and proof that less than 255 bytes. Linux measures this in bytes, not characters[3]. For plain ASCII, this is 255 characters. However, if you are using multi-byte UTF-8 characters (like emojis, Cyrillic, Chinese, or Arabic scripts), each character will consume 2 to 4 bytes, reducing the maximum number of actual characters you can use for a single filename
deriving Repr, DecidableEq

def parsePathComponent (s : String) : PathComponent :=
  if s == "." then .current
  else if s == ".." then .parent
  else .normal s

/-- A version-agnostic splitter that works on any List of characters.
    This bypasses the breaking changes to `String.split` in Lean 4.27+. -/
def splitOnPred (cs : List Char) (p : Char → Bool) : List String :=
  let rec loop (acc : List Char) (res : List String) : List Char → List String
    | [] =>
      if acc.isEmpty then res.reverse
      else (String.ofList acc.reverse :: res).reverse
    | c::rest =>
      if p c then
        if acc.isEmpty then
          loop [] res rest
        else
          loop [] (String.ofList acc.reverse :: res) rest
      else
        loop (c::acc) res rest
  loop [] [] cs


-- ====================================================================
-- Linux (POSIX) Paths
-- ====================================================================

inductive PosixPath where
  | absolute (components : List PathComponent)
  | relative (components : List PathComponent)
deriving Repr, DecidableEq

def parsePosixPath (s : String) : Option PosixPath :=
  if s.isEmpty then
    none
  else if s.startsWith "/" then
    let rest := s.toList.drop 1
    let parts := splitOnPred rest (· == '/')
    some (.absolute (parts.map parsePathComponent))
  else
    let parts := splitOnPred s.toList (· == '/')
    some (.relative (parts.map parsePathComponent))


-- ====================================================================
-- Windows Paths
-- ====================================================================

inductive WindowsPrefix where
  | driveAbsolute (drive : Char)                     -- "C:\"
  | driveRelative (drive : Char)                     -- "D:" (relative to current drive dir)
  | currentDriveAbsolute                             -- "\" (absolute from current drive root)
  | unc (server : String) (share : String)           -- r"\Server\Share"
  | verbatimDisk (drive : Char)                      -- r"\?\C:\" (they should be absolute)
  | verbatimUnc (server : String) (share : String)   -- r"\?\UNC\Server\Share"
  | relative                                         -- Standard relative path (no prefix)
deriving Repr, DecidableEq

structure WindowsPath where
  prefix_ : WindowsPrefix
  components : List PathComponent
deriving Repr, DecidableEq

def isWinSep (c : Char) : Bool :=
  c == '\\' || c == '/'

def isDriveLetter (c : Char) : Bool :=
  (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z')

def runToSep (cs : List Char) : String × List Char :=
  let rec loop (acc : List Char) : List Char → String × List Char
    | [] => (String.ofList acc.reverse, [])
    | c::rest =>
      if isWinSep c then
        (String.ofList acc.reverse, rest)
      else
        loop (c::acc) rest
  loop [] cs

def splitWinComponents (cs : List Char) : List PathComponent :=
  let parts := splitOnPred cs isWinSep
  parts.map parsePathComponent

-- Prefix extraction helpers
def matchVerbatimUnc : List Char → Option (String × String × List Char)
  | s1::s2::'?'::s3::'U'::'N'::'C'::s4::rest =>
    -- Fixed: check 'isWinSep s3' instead of 's3 == '?''
    if isWinSep s1 && isWinSep s2 && isWinSep s3 && isWinSep s4 then
      let (server, rest1) := runToSep rest
      let (share, rest2) := runToSep rest1
      some (server, share, rest2)
    else none
  | _ => none

def matchVerbatimDisk : List Char → Option (Char × List Char)
  | s1::s2::'?'::s3::d::':'::rest => -- Removed 's4' from pattern
    if isWinSep s1 && isWinSep s2 && isWinSep s3 && isDriveLetter d then
      some (d.toUpper, rest)
    else none
  | _ => none

def matchUnc : List Char → Option (String × String × List Char)
  | s1::s2::rest =>
    if isWinSep s1 && isWinSep s2 then
      let (server, rest1) := runToSep rest
      let (share, rest2) := runToSep rest1
      some (server, share, rest2)
    else none
  | _ => none

def matchDriveAbsolute : List Char → Option (Char × List Char)
  | d::':'::s::rest =>
    if isDriveLetter d && isWinSep s then some (d.toUpper, rest) else none
  | _ => none

def matchDriveRelative : List Char → Option (Char × List Char)
  | d::':'::rest =>
    if isDriveLetter d then some (d.toUpper, rest) else none
  | _ => none

def matchCurrentDriveAbsolute : List Char → Option (List Char)
  | s::rest =>
    if isWinSep s then some rest else none
  | _ => none

def parseWinPrefix (cs : List Char) : WindowsPrefix × List Char :=
  match matchVerbatimUnc cs with
  | some (server, share, rest) => (.verbatimUnc server share, rest)
  | none =>
    match matchVerbatimDisk cs with
    | some (d, rest) => (.verbatimDisk d, rest)
    | none =>
      match matchUnc cs with
      | some (server, share, rest) => (.unc server share, rest)
      | none =>
        match matchDriveAbsolute cs with
        | some (d, rest) => (.driveAbsolute d, rest)
        | none =>
          match matchDriveRelative cs with
          | some (d, rest) => (.driveRelative d, rest)
          | none =>
            match matchCurrentDriveAbsolute cs with
            | some rest => (.currentDriveAbsolute, rest)
            | none => (.relative, cs)

def parseWindowsPath (s : String) : Option WindowsPath :=
  if s.isEmpty then none
  else
    let cs := s.toList
    let (prefix_, rest) := parseWinPrefix cs
    some ⟨prefix_, splitWinComponents rest⟩


-- ====================================================================
-- Compile-Time Verification Tests
-- ====================================================================

-- POSIX Tests
#guard parsePosixPath "/var/log/syslog" == some (.absolute [.normal "var", .normal "log", .normal "syslog"])
#guard parsePosixPath "/home/user/documents/report.pdf" == some (.absolute [.normal "home", .normal "user", .normal "documents", .normal "report.pdf"])
#guard parsePosixPath "/etc/nginx/conf.d" == some (.absolute [.normal "etc", .normal "nginx", .normal "conf.d"])
#guard parsePosixPath "/usr/local/bin" == some (.absolute [.normal "usr", .normal "local", .normal "bin"])
#guard parsePosixPath "config.json" == some (.relative [.normal "config.json"])
#guard parsePosixPath "./scripts/deploy.sh" == some (.relative [.current, .normal "scripts", .normal "deploy.sh"])
#guard parsePosixPath "../logs/error.log" == some (.relative [.parent, .normal "logs", .normal "error.log"])
#guard parsePosixPath "projects/website" == some (.relative [.normal "projects", .normal "website"])
#guard parsePosixPath ".." == some (.relative [.parent])
#guard parsePosixPath "../" == some (.relative [.parent])
#guard parsePosixPath ".../" == some (.relative [.normal "..."])
#guard parsePosixPath "." == some (.relative [.current])
#guard parsePosixPath "./" == some (.relative [.current])

-- Windows Tests
#guard parseWindowsPath r"C:\Windows\System32\cmd.exe" == some ⟨.driveAbsolute 'C', [.normal "Windows", .normal "System32", .normal "cmd.exe"]⟩
#guard parseWindowsPath r"C:\Program Files\Java" == some ⟨.driveAbsolute 'C', [.normal "Program Files", .normal "Java"]⟩
#guard parseWindowsPath r"C:\Windows/System32\cmd.exe" == some ⟨.driveAbsolute 'C', [.normal "Windows", .normal "System32", .normal "cmd.exe"]⟩
#guard parseWindowsPath r"C:/Program Files/Java" == some ⟨.driveAbsolute 'C', [.normal "Program Files", .normal "Java"]⟩
#guard parseWindowsPath r"\\Server01\Shared\Reports" == some ⟨.unc "Server01" "Shared", [.normal "Reports"]⟩
#guard parseWindowsPath r"\\?\C:\VeryLongPath\file.txt" == some ⟨.verbatimDisk 'C', [.normal "VeryLongPath", .normal "file.txt"]⟩
-- #guard parseWindowsPath r"\\?\C:VeryLongPath\file.txt" == some ⟨.verbatimDisk 'C', [.normal "VeryLongPath", .normal "file.txt"]⟩ -- TODO: this is a malformed path. should throw during parsing
#guard parseWindowsPath r"\\?\UNC\Server01\Shared\file.txt" == some ⟨.verbatimUnc "Server01" "Shared", [.normal "file.txt"]⟩
#guard parseWindowsPath r"settings.ini" == some ⟨.relative, [.normal "settings.ini"]⟩
#guard parseWindowsPath r".\config\database.db" == some ⟨.relative, [.current, .normal "config", .normal "database.db"]⟩
#guard parseWindowsPath r".\config/database.db" == some ⟨.relative, [.current, .normal "config", .normal "database.db"]⟩
#guard parseWindowsPath r"..\src\main.py" == some ⟨.relative, [.parent, .normal "src", .normal "main.py"]⟩
#guard parseWindowsPath r"\Users\John\Documents" == some ⟨.currentDriveAbsolute, [.normal "Users", .normal "John", .normal "Documents"]⟩
#guard parseWindowsPath r"D:Documents\budget.xlsx" == some ⟨.driveRelative 'D', [.normal "Documents", .normal "budget.xlsx"]⟩
#guard parseWindowsPath r"assets\images" == some ⟨.relative, [.normal "assets", .normal "images"]⟩
#guard parseWindowsPath r".." == some ⟨.relative, [.parent]⟩
#guard parseWindowsPath r"..." == some ⟨.relative, [.normal "..."]⟩
#guard parseWindowsPath r"../" == some ⟨.relative, [.parent]⟩
#guard parseWindowsPath "..\\" == some ⟨.relative, [.parent]⟩

-- Both lowercase 'c' and uppercase 'C' now parse to 'C'
#guard parseWindowsPath r"c:\Windows" == parseWindowsPath r"C:\Windows"
#guard parseWindowsPath "c:Windows" == parseWindowsPath "C:Windows"
#guard parseWindowsPath r"\\?\c:Windows" == parseWindowsPath r"\\?\C:Windows"

-- Consecutive backslashes are collapsed
#guard parseWindowsPath r"C:\\\\\Windows\\System32\\cmd.exe" ==
  parseWindowsPath r"C:\Windows\System32\cmd.exe"

-- Mixed forward/backslashes are collapsed
#guard parseWindowsPath r"C:\/\/\/Windows\System32\cmd.exe" ==
  parseWindowsPath r"C:\Windows\System32\cmd.exe"
