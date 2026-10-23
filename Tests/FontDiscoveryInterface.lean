module

import LeanTex.Cli.FontDiscovery

/-! Font discovery's metadata and filesystem entry points reach an ordinary import without the font
parser or cache rows; nothing here scans the host's fonts. -/

open LeanTex.Core.FontDb
open LeanTex.Cli.FontDiscovery

namespace Tests.FontDiscoveryInterface

example : Repr Face := inferInstance
example : List String := searchDirs
example : IO (List String) := extraDirs
example : String → (String → Bool) → IO (Option ByteArray) := tableImage
example : String → Nat → (String → Bool) → IO (Option ByteArray) := memberImage
example : String → (String → Bool) → IO (Option ByteArray) := faceImage
example : String → IO (Except String ByteArray) := faceBytes
example : String → IO (Option Face) := probe
example : IO (Option System.FilePath) := cacheDir
example : String := probeCacheName
example : String := listingCacheName
example : String → String → ByteArray := encodeTable
example : String → ByteArray → Option String := decodeTable
example : String → IO (Option String) := probeKey
example : List String → IO (List String) := fun dirs => systemRoots dirs
example : Option System.FilePath → List String → IO (Array Face) := scanRootsIn
example : List String → IO (Array Face) := scanRoots
example : Array Face → IO (Option Face) := firstMathFace
example : Array Face → String → IO (Option (Face × Option Pairing)) := pickMathFace
example : Array Face → Array Char → IO (Array (Char × String)) := fallbackPicks
example : (String → Bool) → Array Face → Array Char → IO (Array (Char × String)) :=
  fallbackPicksPreferring

example : True := by
  fail_if_success have := LeanTex.Cli.FontDiscovery.faceLine
  fail_if_success have := LeanTex.Cli.FontDiscovery.parseLine
  fail_if_success have := LeanTex.Cli.FontDiscovery.fileKey
  fail_if_success have := LeanTex.Cli.FontDiscovery.dirsName
  fail_if_success have := LeanTex.Cli.FontDiscovery.dirLine
  fail_if_success have := LeanTex.Cli.FontDiscovery.parseDirLine
  fail_if_success have := LeanTex.Cli.FontDiscovery.readTable
  fail_if_success have := LeanTex.Cli.FontDiscovery.writeTable
  fail_if_success have := LeanTex.Cli.FontDiscovery.walkCached
  fail_if_success have := LeanTex.Cli.FontDiscovery.skipBytes
  fail_if_success have := LeanTex.Cli.FontDiscovery.readAt
  fail_if_success have := LeanTex.Cli.FontDiscovery.facePaths
  fail_if_success have := LeanTex.Core.Font.parse
  trivial

end Tests.FontDiscoveryInterface
