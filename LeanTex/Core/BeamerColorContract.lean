module

public import LeanTex.Core.BeamerColor
import all LeanTex.Core.BeamerColor
import all LeanTex.Core.DesignRole

/-!
The beamer colour elements the registry binds, held to beamer's own
element table in a leaf, so the kernel's evaluation runs beside the build
rather than in series with the modules that import `BeamerColor`.
-/

namespace LeanTex.Core.BeamerColor

open Ir

/-- **The elements the registry binds are beamer's, channel for channel**
(`_exact`): reading `Row.beamer` off every role yields exactly the elements
beamercolorthemedefault.sty and beamercolorthememoloch.sty paint here, each
channel the role that paints it — the table that was written by hand
before the registry, in the registry's order. -/
public theorem roles_exact : roles =
    [("normal text", some .ink, some .page), ("background canvas", none, some .page),
     ("footline", some .muted, some .footBand), ("page number in head/foot", some .muted, none),
     ("alerted text", some .alert, none), ("example text", some .example, none),
     ("frametitle", some .frameTitleInk, some .frameTitleBar),
     ("headline", some .frameTitleInk, some .frameTitleBar),
     ("framesubtitle", some .frameSubtitleInk, none), ("section title", some .sectionTitleInk, none),
     ("block title", some .blockTitleInk, some .blockTitleBar),
     ("block title alerted", some .alertTitleInk, some .alertTitleBar),
     ("block title example", some .exampleTitleInk, some .exampleTitleBar),
     ("block body", some .blockBodyInk, some .blockBodyGround),
     ("block body alerted", some .alertBodyInk, some .alertBodyGround),
     ("block body example", some .exampleBodyInk, some .exampleBodyGround),
     ("standout", some .standoutInk, some .standoutGround),
     ("title separator", some .separator, none),
     ("progress bar", some .progressFill, some .progressTrack),
     ("progress bar in section page", some .sectionProgressFill, some .sectionProgressTrack)] := by
  decide +kernel

end LeanTex.Core.BeamerColor
