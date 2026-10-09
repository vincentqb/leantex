module

import LeanTex.Core.Picture

/-! Ordinary picture clients can pass source, styles, measurement callbacks,
and placement values through the public API and apply its contracts.
Token scanning, label-recovery state, and macro expansion stay internal. -/

open LeanTex.Core
open LeanTex.Core.Dim
open LeanTex.Core.Picture

namespace Tests.PictureInterface

example : Repr Tok := inferInstance
example : BEq Tok := inferInstance
example : Inhabited Tok := inferInstance
example : Repr Val := inferInstance
example : BEq Val := inferInstance
example : Repr NodeGeom := inferInstance
example : BEq NodeGeom := inferInstance

example (body : List Tok) : Tok := .group body
example (display : Bool) (body : List Parse.Raw) (pos : Pos) : Tok :=
  .math display body pos
example : Array Parse.Raw → Array Tok := ofRaws
example : Int → String := milliString
example : Val → String := Val.text
example : Array PDiag → Bool := namesLoss

example (pal : Ir.Palette)
    (math : Bool → Array Parse.Raw → Ir.Inline × Array PDiag)
    (metric : Ir.Pic.LabelMetric) : Cx :=
  { pal, math, metric }

example (cx : Cx) : Sp × Array (Array Tok) × List (String × Ir.Style) :=
  (cx.toSp cx.scale, cx.opts, cx.argStyles)

example (styles : List (String × Array Tok)) (keys : Array Tok) :
    List (String × Array Tok) × Array (Array Tok) :=
  readStyleList styles keys

example : Array (Array Tok) → List (String × Array Tok) := documentStyles
example : List (String × Array Tok) → Array Tok → Array String := unreadKeys
example : String := nodeFloorPlaceholder
example : List String := phantomCtrl
example : List String := walkCtrls
example : Sp → Sp := innerSep

example (cx : Cx) (env : List (String × Val)) (toks : List Tok) :
    Array LabelLine × Array PDiag :=
  nodeLabel cx env toks

example (lines : Array LabelLine) (named : Bool) (h : named) :
    (0 < (labelFloor lines named).foldl (fun n l => n + l.1.size) 0 : Bool) :=
  labelFloor_accounts lines named h

example (cx : Cx) (env : List (String × Val)) (toks : List Tok) :
    ¬ (nodeLabel cx env toks).2.isEmpty →
      (0 < (nodeLabel cx env toks).1.foldl (fun n l => n + l.1.size) 0 : Bool) :=
  nodeLabel_accounts cx env toks

example (name : String) (value : Val) : LabelInput := .substitution name value
example (input : LabelInput) : LabelOrigin := .source input
example : LabelOrigin := .generated .nodeFloor

example (cx : Cx) (env : List (String × Val)) (toks : List Tok) :
    ∀ line ∈ (nodeLabel cx env toks).1,
      ∀ c ∈ (Ir.plainText line.1).toList,
        ∃ origin : LabelOrigin,
          origin.Permitted env toks (!(nodeLabel cx env toks).2.isEmpty) ∧
          c ∈ (origin.text cx).toList :=
  nodeLabel_mem cx env toks

example (cx : Cx) (env : List (String × Val)) (toks : List Tok)
    (clean : (nodeLabel cx env toks).2.isEmpty = true) :
    ∀ line ∈ (nodeLabel cx env toks).1,
      ∀ c ∈ (Ir.plainText line.1).toList,
        ∃ input ∈ labelInputList env #[] toks, c ∈ (input.text cx).toList :=
  nodeLabel_clean_mem cx env toks clean

example (x y a b : Sp) : NodeGeom := { x, y, a, b }
example (g : NodeGeom) (anchor : NodeAnchor) : Sp × Sp := g.anchorPoint anchor
example (d : Dir) (target : String) (sep : Sp × Sp) : NodePlacement :=
  .relative d target sep
example (name : Option String) (placement : NodePlacement) (shape : NodeGeom) :
    NodePlan :=
  { name, placement, shape }

example (p q : NodePlan) (nodes : List (String × NodeGeom))
    (h : p.Independent q) (name : String) :
    (q.run (p.run nodes).2).2.lookup name =
      (p.run (q.run nodes).2).2.lookup name :=
  NodePlan.place_order_agree p q nodes h name

example (cx : Cx) (statements : List Stmt) (baseline : Option Sp) : Ir.Pic.Picture :=
  (evalFixed cx statements).toPicture baseline

example (pal : Ir.Palette) (raws : Array Parse.Raw)
    (math : Bool → Array Parse.Raw → Ir.Inline × Array PDiag)
    (sets : Array (Array Parse.Raw)) (metric : Ir.Pic.LabelMetric)
    (macros : Array (String × String)) (argStyles : List (String × Ir.Style))
    (ladder : List (String × Nat)) (declStyles : List (String × Ir.Style))
    (bodySize : Sp) : Ir.Pic.Picture × Array PDiag :=
  elabPicture pal raws math sets metric macros argStyles ladder declStyles bodySize

example : String → Ir.Pic.Picture := placeholder

example (gapped : Bool) (what : String)
    (h : (unreachedName gapped what).1 = .W0334) : gapped = true :=
  unreachedName_accounts gapped what h

example : True := by
  fail_if_success
    have : (unreachedName false "").1 = .E0333 := by rfl
  trivial

example : True := by
  fail_if_success have := Picture.styleName_agree
  fail_if_success have := Picture.ofRawList
  fail_if_success have := Picture.ofRawOne
  fail_if_success have := Picture.evalExpr
  fail_if_success have := Picture.evalNum
  fail_if_success have := Picture.pictureMode
  fail_if_success have := Picture.condKindOf
  fail_if_success have := Picture.condTakesNoTest
  fail_if_success have := Picture.subpaths
  fail_if_success have := Picture.parseList
  fail_if_success have := Picture.parseTok
  trivial

example : True := by
  fail_if_success have := Picture.expandBody
  fail_if_success have := Picture.addStyle
  fail_if_success have := Picture.appendStyle
  fail_if_success have := Picture.tipKey
  fail_if_success have := Picture.declareTip
  fail_if_success have := Picture.everyNodeKey
  fail_if_success have := Picture.everyPathKey
  fail_if_success have := Picture.everyTextKey
  fail_if_success have := Picture.readOneDef
  fail_if_success have := Picture.tipName
  fail_if_success have := Picture.arrowTipName
  fail_if_success have := Picture.drawsAsArrow
  fail_if_success have := Picture.setsEngineKey
  fail_if_success have := Picture.expandOpts
  trivial

example : True := by
  fail_if_success have := Picture.innerSepDefault
  fail_if_success have := Picture.nodeAnchorOf
  fail_if_success have := Picture.diag45
  fail_if_success have := Picture.splitAnchor
  fail_if_success have := Picture.Ev.diag
  fail_if_success have := Picture.nodeLineLead
  trivial

example : True := by
  fail_if_success have := Picture.SalMode
  fail_if_success have := Picture.Sal
  fail_if_success have := Picture.Sal.str
  fail_if_success have := Picture.Sal.flush
  fail_if_success have := Picture.Sal.inlines
  fail_if_success have := Picture.Sal.inline
  fail_if_success have := Picture.Sal.addDiags
  fail_if_success have := Picture.Sal.mode0
  fail_if_success have := Picture.Sal.refuse
  fail_if_success have := Picture.Sal.newline
  fail_if_success have := Picture.Sal.sub
  fail_if_success have := Picture.Sal.inner
  fail_if_success have := Picture.Sal.splice
  fail_if_success have := Picture.Sal.inkCount
  fail_if_success have := Picture.Sal.inked
  fail_if_success have := Picture.Sal.settled
  fail_if_success have := Picture.Sal.settle
  fail_if_success have := Picture.salList
  fail_if_success have := Picture.salOne
  trivial

example : True := by
  fail_if_success have := Picture.lineWidthStyles
  fail_if_success have := Picture.readLineWidth
  fail_if_success have := Picture.readFont
  fail_if_success have := Picture.fontLines
  fail_if_success have := Picture.textAlignOf
  fail_if_success have := Picture.alignLabels
  fail_if_success have := Picture.dirOf
  fail_if_success have := Picture.readsPathOpt
  fail_if_success have := Picture.readsNodeOpt
  trivial

example : True := by
  fail_if_success have := Picture.splitRel
  fail_if_success have := Picture.condDrawnWords
  fail_if_success have := Picture.evalList
  fail_if_success have := Picture.evalOne
  fail_if_success have := Picture.evalForeach
  trivial

example : True := by
  fail_if_success have := Picture.Macro
  fail_if_success have := Picture.walkOwns
  fail_if_success have := Picture.boundNames
  fail_if_success have := Picture.expandMacros
  fail_if_success have := Picture.readMacro
  fail_if_success have := Picture.macroTable
  trivial

example : True := by
  fail_if_success have := Picture.Rp
  fail_if_success have := Picture.Mode
  fail_if_success have := Picture.PSt
  fail_if_success have := Picture.Anchor
  fail_if_success have := Picture.DrawOp
  fail_if_success have := Picture.EdgeLabel
  fail_if_success have := Picture.expandList
  fail_if_success have := Picture.expandTok
  trivial

end Tests.PictureInterface
