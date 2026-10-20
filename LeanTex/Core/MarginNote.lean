module

public import LeanTex.Core.Ir
public import LeanTex.Core.Diag

/-! Margin notes where LaTeX sets them: beside a line of the page's own text, never inside a float,
a box, a table, a note or a display, a note standing between paragraphs beside the paragraph
before it. -/

namespace LeanTex.Core.MarginNote

open LeanTex.Core LeanTex.Core.Ir

/-- One sibling run with each margin note in it replaced by its text. -/
-- conserves: none — one sibling step; `flatten_text` states the run's fact.
@[expose] public def flattenStep (acc : Array Inline) (y : Inline) : Array Inline :=
  match y with
  | .marginNote _ b => acc ++ b
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _ | .label _ | .ref _ _ _ _
  | .cite _ _ | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber
  | .pageCount | .linebreak _ | .styled _ _ | .colored _ _ _ | .located _ _ | .role _ _ | .link _ _
  | .decorated _ _ | .onSteps _ _ | .altSteps _ _ _ | .cited _ _ _ | .boxed _ _ | .footnote _ _ =>
    acc.push y

@[expose] public def flatten (ys : Array Inline) : Array Inline := ys.foldl flattenStep #[]

/-- Inline content with each margin note's text set where it stands. -/
@[expose] public def inlineAll (xs : Array Inline) : Array Inline :=
  mapInlines id xs (finish := flatten)

/-- Each margin note inline content holds, named by where it stands. -/
@[expose] public def countIn (where_ : Diag.Noun) (xs : Array Inline) : Array Diag.Noun :=
  (marginNotesIn xs).map fun _ => where_

/-- The block a margin note stands in, as a diagnostic names it. -/
@[expose] public def blockNoun : Block → Diag.Noun
  | .float _ _ _ _ _ => .float
  | .table _ _ _ _ _ _ => .table
  | .columns _ => .box
  | .note _ => .note
  | .equation _ _ => .display
  | .frame _ _ _ _ _ | .framefoot _ | .logo _ | .nav _ _ => .frame
  | .lines _ => .line
  | .verbatim _ _ _ => .listing
  | .algorithm _ _ _ => .listing
  | .bibliography _ _ _ => .bibliography
  | .contents _ _ => .entry
  | .picture _ => .picture
  | .para _ | .section _ _ _ _ | .list _ _ _ | .center _ | .ragged _ _ | .spaced _ _ | .role _ _
  | .link _ _ | .quote _ _ | .abstract _ | .titled _ _ _ | .disclosure _ _ _ | .onSteps _ _
  | .altSteps _ _ _ | .only _ _ | .pagebreak | .setPalette _ | .setTokens _ | .rule _ _ _ => .block

/-- A block with every margin note it holds set in its text, each named by the block. -/
-- conserves: none — the generic map moving margin notes' text inline.
@[expose] public def closeBlock (b : Block) : Block × Array Diag.Noun :=
  let n := foldBlock (fun n _ => n) (fun n x => if x matches .marginNote _ _ then n + 1 else n) 0 b
  if n == 0 then (b, #[]) else
  (mapBlock id id b (finish := flatten), Array.replicate n (blockNoun b))

mutual

/-- A paragraph's run with its margin notes kept where a line of the page's text holds them, and
those inside a note, a box or another margin note set in their text. -/
-- conserves: none — keeps the notes a margin takes, inlines the rest.
@[expose] public def keepOne (x : Inline) : Inline × Array Diag.Noun :=
  match x with
  | .styled st body => let r := keepList #[] #[] body.toList; (.styled st r.1, r.2)
  | .colored c n body => let r := keepList #[] #[] body.toList; (.colored c n r.1, r.2)
  | .located sp body => let r := keepList #[] #[] body.toList; (.located sp r.1, r.2)
  | .role n body => let r := keepList #[] #[] body.toList; (.role n r.1, r.2)
  | .link u body => let r := keepList #[] #[] body.toList; (.link u r.1, r.2)
  | .decorated k body => let r := keepList #[] #[] body.toList; (.decorated k r.1, r.2)
  | .onSteps spec body => let r := keepList #[] #[] body.toList; (.onSteps spec r.1, r.2)
  | .altSteps spec a b =>
    let ra := keepList #[] #[] a.toList
    let rb := keepList #[] #[] b.toList
    (.altSteps spec ra.1 rb.1, ra.2 ++ rb.2)
  | .cited f ks ink => let r := keepList #[] #[] ink.toList; (.cited f ks r.1, r.2)
  | .boxed bx body => (.boxed bx (inlineAll body), countIn .box body)
  | .footnote n body => (.footnote n (inlineAll body), countIn .footnote body)
  | .marginNote m body => (.marginNote m (inlineAll body), countIn .note body)
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _ | .label _ | .ref _ _ _ _
  | .cite _ _ | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber
  | .pageCount | .linebreak _ => (x, #[])

@[expose] public def keepList (out : Array Inline) (n : Array Diag.Noun) :
    List Inline → Array Inline × Array Diag.Noun
  | [] => (out, n)
  | x :: rest => let r := keepOne x; keepList (out.push r.1) (n ++ r.2) rest

end

/-- Whether an inline node is a margin note. -/
@[expose] public def isMarginNote (x : Inline) : Bool := x matches .marginNote _ _

/-- A run's own margin notes before anything else it holds, and the run past them. -/
@[expose] public def leading (c : Array Inline) : Array Inline × Array Inline :=
  ((c.toList.takeWhile isMarginNote).toArray, (c.toList.dropWhile isMarginNote).toArray)

/-- A margin note marked as standing between blocks, beside the block before it. -/
@[expose] public def setBetween (x : Inline) : Inline :=
  if let .marginNote m b := x then .marginNote { m with between := true } b else x

/-- A list whose first item opens with a paragraph, with `pend`'s notes beside that paragraph's
first line, where the notes waiting before the list stand in LaTeX. -/
@[expose] public def leadInto (pend : Array Inline) : Block → Option Block
  | .list o s items => match items.toList with
    | first :: more => match first.toList with
      | .para c :: restB => some (.list o s ((#[Block.para (pend ++ c)] ++ restB.toArray) :: more).toArray)
      | _ => none
    | [] => none
  | .section .. | .para _ | .center _ | .ragged .. | .spaced .. | .role .. | .link ..
  | .quote .. | .abstract _ | .titled .. | .disclosure .. | .equation .. | .verbatim ..
  | .algorithm .. | .columns _ | .onSteps .. | .altSteps .. | .note _ | .only .. | .nav ..
  | .logo _ | .pagebreak | .frame .. | .framefoot _ | .setPalette _ | .setTokens _ | .rule ..
  | .picture _ | .table .. | .float .. | .bibliography .. | .contents .. | .lines _ => none

/-- A block of the flow after the notes waiting for a paragraph: beside its first line where it is a
list opening with one, else the notes set in their text, named, before it. -/
@[expose] public def flushPend (out : Array Block) (pend : Array Inline) (n : Array Diag.Noun)
    (b : Block) : Array Block × Array Diag.Noun :=
  if pend.isEmpty then (out.push b, n) else
  match leadInto pend b with
  | some b' => (out.push b', n)
  | none => ((out.push (.para (inlineAll pend))).push b, n ++ countIn .block pend)

mutual

/-- Blocks a page's own flow sets, their margin notes kept beside their lines, those a paragraph
opens with joined to the paragraph before it as TeX's vertical mode places them, else waiting for
the next (`flushPend`), and every one in a block with no margin set in its text. -/
-- conserves: none — moves margin notes only; a note's text stays in reading order.
@[expose] public def settleList (out : Array Block) (pend : Array Inline) (n : Array Diag.Noun) :
    List Block → Array Block × Array Diag.Noun
  | [] => (if pend.isEmpty then out else out.push (.para (inlineAll pend)), n ++ countIn .block pend)
  | b :: rest =>
    let (b, n) := settleOne b n
    match b with
    | .para c =>
      let (lead, body) := leading c
      match out.back?, lead.isEmpty, pend.isEmpty with
      | some (.para pc), false, true =>
        let out := out.pop.push (.para (pc ++ lead.map setBetween))
        if body.isEmpty then settleList out #[] n rest
        else settleList (out.push (.para body)) #[] n rest
      | _, _, _ =>
        if body.isEmpty && !lead.isEmpty then settleList out (pend ++ lead) n rest
        else settleList (out.push (.para (pend ++ c))) #[] n rest
    | b =>
      let r := flushPend out pend n b
      settleList r.1 #[] r.2 rest

/-- One block of the page's flow, its margin notes settled. -/
@[expose] public def settleOne (b : Block) (n : Array Diag.Noun) : Block × Array Diag.Noun :=
  match b with
  | .para c => let r := keepList #[] #[] c.toList; (.para r.1, n ++ r.2)
  | .section l st num title => (.section l st num (inlineAll title), n ++ countIn .heading title)
  | .list o s items => let r := settleItems #[] n items.toList; (.list o s r.1, r.2)
  | .center body => let r := settleList #[] #[] n body.toList; (.center r.1, r.2)
  | .ragged s body => let r := settleList #[] #[] n body.toList; (.ragged s r.1, r.2)
  | .spaced g body => let r := settleList #[] #[] n body.toList; (.spaced g r.1, r.2)
  | .role nm body => let r := settleList #[] #[] n body.toList; (.role nm r.1, r.2)
  | .link t body => let r := settleList #[] #[] n body.toList; (.link t r.1, r.2)
  | .quote q body => let r := settleList #[] #[] n body.toList; (.quote q r.1, r.2)
  | .abstract body => let r := settleList #[] #[] n body.toList; (.abstract r.1, r.2)
  | .titled k title body =>
    let r := settleList #[] #[] (n ++ countIn .title title) body.toList
    (.titled k (inlineAll title) r.1, r.2)
  | .disclosure summary e body =>
    let r := settleList #[] #[] (n ++ countIn .title summary) body.toList
    (.disclosure (inlineAll summary) e r.1, r.2)
  | .onSteps spec body => let r := settleList #[] #[] n body.toList; (.onSteps spec r.1, r.2)
  | .altSteps spec a c =>
    let ra := settleList #[] #[] n a.toList
    let rc := settleList #[] #[] ra.2 c.toList
    (.altSteps spec ra.1 rc.1, rc.2)
  | .only targets body => let r := settleList #[] #[] n body.toList; (.only targets r.1, r.2)
  | .lines _ | .equation _ _ | .verbatim _ _ _ | .algorithm _ _ _ | .columns _ | .note _
  | .nav _ _ | .logo _ | .pagebreak | .frame _ _ _ _ _ | .framefoot _ | .setPalette _
  | .setTokens _ | .rule _ _ _ | .picture _ | .table _ _ _ _ _ _ | .float _ _ _ _ _
  | .bibliography _ _ _ | .contents _ _ =>
    let r := closeBlock b
    (r.1, n ++ r.2)

@[expose] public def settleItems (out : Array (Array Block)) (n : Array Diag.Noun) :
    List (Array Block) → Array (Array Block) × Array Diag.Noun
  | [] => (out, n)
  | item :: rest =>
    let r := settleList #[] #[] n item.toList
    settleItems (out.push r.1) r.2 rest

end

/-- A document's body with its margin notes settled, every one set in its text where the page has
no margin `room`, and where each one set in its text stood. -/
@[expose] public def settle (room : Bool) (body : Array Block) : Array Block × Array Diag.Noun :=
  if !foldBlocks (fun b _ => b) (fun b x => b || x matches .marginNote _ _) false body then (body, #[])
  else if room then settleList #[] #[] #[] body.toList
  else
    let rs := body.map closeBlock
    (rs.map (·.1), rs.flatMap fun r => r.2.map fun _ => .page)

end LeanTex.Core.MarginNote
