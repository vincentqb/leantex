module

public import LeanTex.Core.PdfObj
import LeanTex.Core.PdfRead
import LeanTex.Core.Flate

/-! The stream filters of ISO 32000-2 §7.4 a figure's streams may name, chained in order, the
ASCII85, run-length, LZW and Flate outputs capped at `PdfRead.maxDecoded`. -/

namespace LeanTex.Core.PdfFilters

open LeanTex.Core.PdfRead (Obj)

/-- What a filter chain leaves: decoded bytes, a JPEG for the viewer to decode, or an undecoded filter. -/
public inductive Decoded where
  | bytes (b : ByteArray)
  | dct (jpeg : ByteArray)
  | refused (feature : String)
  deriving Inhabited

/-- A filter's full name, its inline-image abbreviation read (§8.9.7, Table 92). -/
public def filterName (n : String) : String :=
  if n == "AHx" then "ASCIIHexDecode" else if n == "A85" then "ASCII85Decode"
  else if n == "LZW" then "LZWDecode" else if n == "Fl" then "FlateDecode"
  else if n == "RL" then "RunLengthDecode" else if n == "CCF" then "CCITTFaxDecode"
  else if n == "DCT" then "DCTDecode" else n

/-- ASCIIHexDecode (§7.4.2): digit pairs up to `>`, white space ignored, an odd final digit followed by 0. -/
public def asciiHex (b : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut hi : Option Nat := none
  for c in b do
    let c := c.toNat
    if c == 62 then break
    match PdfLex.hexVal c with
    | some v =>
      match hi with
      | some h =>
        out := out.push (UInt8.ofNat (h * 16 + v))
        hi := none
      | none => hi := some v
    | none => pure ()
  if let some h := hi then out := out.push (UInt8.ofNat (h * 16))
  return out

/-- ASCII85Decode (§7.4.3): five base-85 digits to four bytes, `z` for four zeros, up to `~>`. -/
public def ascii85 (b : ByteArray) (cap : Nat) : Except String ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut group : Array Nat := #[]
  let flush (out : ByteArray) (g : Array Nat) : ByteArray :=
    let n := g.size
    let padded := g ++ Array.replicate (5 - n) 84
    let v := padded.foldl (fun a d => a * 85 + d) 0
    let bytes := #[v / 16777216 % 256, v / 65536 % 256, v / 256 % 256, v % 256]
    (bytes.extract 0 (n - 1)).foldl (fun o x => o.push (UInt8.ofNat x)) out
  for c in b do
    let c := c.toNat
    if c == 126 then break
    if c == 122 && group.isEmpty then
      out := out ++ ⟨#[0, 0, 0, 0]⟩
    else if 33 ≤ c && c ≤ 117 then
      group := group.push (c - 33)
      if group.size == 5 then
        let v := group.foldl (fun a d => a * 85 + d) 0
        if v ≥ 4294967296 then return .error "malformed ASCII85 data: a group exceeds four bytes"
        out := flush out group
        group := #[]
    else if PdfLex.isWs c then pure ()
    else return .error "malformed ASCII85 data: an unexpected character"
    if out.size > cap then return .error "an ASCII85 stream decodes past the size limit"
  if group.size == 1 then return .error "malformed ASCII85 data: a final group of one digit"
  if group.size > 1 then out := flush out group
  if out.size > cap then return .error "an ASCII85 stream decodes past the size limit"
  return .ok out

/-- RunLengthDecode (§7.4.5): a length byte copies `n + 1` bytes or repeats one `257 − n` times; 128 ends. -/
public def runLength (b : ByteArray) (cap : Nat) : Except String ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut i := 0
  for _ in [0:b.size + 1] do
    if i ≥ b.size then break
    let n := ((b[i]?).getD 0).toNat
    if n == 128 then break
    if n < 128 then
      out := out ++ b.extract (i + 1) (i + 2 + n)
      i := i + 2 + n
    else
      let v := (b[i + 1]?).getD 0
      for _ in [0:257 - n] do out := out.push v
      i := i + 2
    if out.size > cap then return .error "a run-length stream decodes past the size limit"
  return .ok out

/-- LZWDecode (§7.4.4): codes of 9 to 12 bits, 256 clearing the table and 257 ending; `early` switches width early. -/
public def lzw (b : ByteArray) (early : Bool) (cap : Nat) : Except String ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut table : Array ByteArray := (Array.range 256).map fun c => ByteArray.empty.push (UInt8.ofNat c)
  table := table.push ByteArray.empty |>.push ByteArray.empty
  let mut width := 9
  let mut prev : Option ByteArray := none
  let mut bitPos := 0
  let totalBits := b.size * 8
  for _ in [0:b.size * 8 / 9 + 2] do
    if bitPos + width > totalBits then break
    let mut code := 0
    for k in [0:width] do
      let bit := (((b[(bitPos + k) / 8]?).getD 0).toNat >>> (7 - (bitPos + k) % 8)) % 2
      code := code * 2 + bit
    bitPos := bitPos + width
    if code == 256 then
      table := table.extract 0 258
      width := 9
      prev := none
    else if code == 257 then break
    else
      let entry? : Option ByteArray :=
        if code < table.size then table[code]?
        else if code == table.size then prev.map fun p => p.push ((p[0]?).getD 0)
        else none
      match entry? with
      | none => return .error "malformed LZW data: a code beyond the table"
      | some entry =>
        out := out ++ entry
        if let some p := prev then
          if table.size < 4096 then table := table.push (p.push ((entry[0]?).getD 0))
        prev := some entry
        let limit := if early then table.size + 1 else table.size
        if limit ≥ 4096 then width := 12
        else if limit ≥ 2048 then width := 12
        else if limit ≥ 1024 then width := 11
        else if limit ≥ 512 then width := 10
        else width := 9
      if out.size > cap then return .error "an LZW stream decodes past the size limit"
  return .ok out

/-- The TIFF predictor (§7.4.4.3, Predictor 2) for 8-bit components. -/
public def tiffUnpredict (data : ByteArray) (columns colors bpc : Nat) : Except String ByteArray := do
  if bpc != 8 then throw s!"the TIFF predictor at {bpc} bits per component is not supported"
  let row := max 1 (columns * colors)
  let mut out := data
  for r in [0:data.size / row] do
    for i in [colors:row] do
      let k := r * row + i
      let v := (((out[k]?).getD 0).toNat + ((out[k - colors]?).getD 0).toNat) % 256
      out := out.set! k (UInt8.ofNat v)
  return out

private def parm (p : Option Obj) (k : String) (d : Int) : Int :=
  ((p.bind (·.get? k)).bind Obj.int?).getD d

private def unpredict (p : Option Obj) (data : ByteArray) : Except String ByteArray := do
  let pred := parm p "Predictor" 1
  if pred ≤ 1 then return data
  let columns := (parm p "Columns" 1).toNat
  let colors := (parm p "Colors" 1).toNat
  let bpc := (parm p "BitsPerComponent" 8).toNat
  if pred == 2 then return ← tiffUnpredict data columns colors bpc
  if pred ≥ 10 then
    let bpp := max 1 (colors * bpc / 8)
    let rowBytes := max 1 ((columns * colors * bpc + 7) / 8)
    let rows := data.size / (rowBytes + 1)
    return ← Flate.pngUnfilter data rows rowBytes bpp
  throw s!"stream predictor {pred} is not supported"

private def applyOne (name : String) (p : Option Obj) (data : ByteArray) (cap : Nat) :
    Except String Decoded := do
  match filterName name with
  | "ASCIIHexDecode" => return .bytes (asciiHex data)
  | "ASCII85Decode" => return .bytes (← ascii85 data cap)
  | "RunLengthDecode" => return .bytes (← runLength data cap)
  | "LZWDecode" => return .bytes (← unpredict p (← lzw data (parm p "EarlyChange" 1 != 0) cap))
  | "FlateDecode" =>
    let out ← Flate.inflate data cap
    return .bytes (← unpredict p out)
  | "DCTDecode" => return .dct data
  | "JBIG2Decode" => return .refused "jbig2"
  | "JPXDecode" => return .refused "jpx"
  | "CCITTFaxDecode" => return .refused "ccitt"
  | "Crypt" => return .refused "crypt"
  | other => return .refused s!"filter-{other}"

/-- A stream's data through its filter chain (§7.4), each filter with its parameters and its output
capped at `cap` bytes; a filter after `DCTDecode` is refused. -/
public def decodeCapped (dict : Obj) (raw : ByteArray) (cap : Nat) : Except String Decoded := do
  let get (k abbr : String) : Option Obj := (dict.get? k).orElse fun _ => dict.get? abbr
  let names : Array String := match get "Filter" "F" with
    | some (.name n) => #[n]
    | some (.arr xs) => xs.filterMap fun x => match x with
      | .name n => some n
      | _ => none
    | _ => #[]
  let parms : Array (Option Obj) := match get "DecodeParms" "DP" with
    | some (.arr xs) => xs.map fun x => match x with
      | .null => none
      | o => some o
    | some (.dict es) => #[some (.dict es)]
    | _ => #[]
  let mut cur : Decoded := .bytes raw
  for h : i in [0:names.size] do
    match cur with
    | .bytes data => cur ← applyOne names[i] (parms[i]?.getD none) data cap
    | .dct _ => return .refused "filter-after-dct"
    | .refused f => return .refused f
  return cur

/-- A stream's data through its filter chain, capped at `PdfRead.maxDecoded`. -/
public def decode (dict : Obj) (raw : ByteArray) : Except String Decoded :=
  decodeCapped dict raw PdfRead.maxDecoded

end LeanTex.Core.PdfFilters
