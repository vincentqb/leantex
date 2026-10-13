module

public import LeanTex.Core.BeamerColor
import all LeanTex.Core.BeamerColor
import all LeanTex.Core.DesignRole

/-! The beamer colour elements the registry binds, held to beamer's own element table in a leaf. -/

namespace LeanTex.Core.BeamerColor

open Ir

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
