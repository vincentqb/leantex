module

public import Tests.Support

public section

/-! The SVG boundary and terminal projection as libxml2 and libxslt stated them, the parity oracle's
reference (`scripts/svg-check.lean`); no render path imports it. -/

namespace Tests.SvgLegacy

/-- The narrow support boundary over libxml's parse: fragment references and `data:` rasters only,
plain CSS, and no scripts, foreign objects or animated resources. -/
def supportedSvg : String :=
  let localUrl := "(starts-with(normalize-space(.),'url(#') and " ++
    "substring(normalize-space(.),string-length(normalize-space(.)),1)=')' and " ++
    "string-length(normalize-space(.))>6 and " ++
    "translate(substring(normalize-space(.),6,string-length(normalize-space(.))-6)," ++
    "'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_.:-','')='')"
  let color := "translate(normalize-space(.),'RGBA','rgba')"
  let channels := "substring-before(substring-after(" ++ color ++ ",'('),')')"
  let numericColor :=
    "((local-name()='fill' or local-name()='stroke' or local-name()='color' or " ++
      "local-name()='stop-color' or local-name()='flood-color' or local-name()='lighting-color') and " ++
      "(" ++ color ++ "=concat('rgb('," ++ channels ++ ",')') or " ++
        color ++ "=concat('rgba('," ++ channels ++ ",')')) and " ++
      "string-length(" ++ channels ++ ")>0 and " ++
      "translate(" ++ channels ++ ",'0123456789.%eE+-,/ ','')='')"
  let cssSyntax := "(contains(.,'(') or contains(.,'\\') or contains(.,'@'))"
  let dataRaster := "(local-name()='href' and local-name(..)='image' and " ++
    "(starts-with(normalize-space(.),'data:image/png;base64,') or " ++
    "starts-with(normalize-space(.),'data:image/jpeg;base64,')) and " ++
    "translate(substring-after(normalize-space(.),';base64,')," ++
    "'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/= ','')='')"
  let unsupported :=
    "//processing-instruction() | " ++
    "//*[local-name()='script' or local-name()='foreignObject'] | " ++
    "//@*[local-name()='base' or starts-with(local-name(),'on')] | " ++
    "//@*[local-name()='href' or local-name()='src']" ++
      "[not(starts-with(normalize-space(.),'#') or " ++ dataRaster ++ ")] | " ++
    "//*[local-name()='style'][" ++ cssSyntax ++ "] | " ++
    "//@*[not(local-name()='transform' or local-name()='gradientTransform' or " ++
      "local-name()='patternTransform' or local-name()='begin' or local-name()='end')]" ++
      "[" ++ cssSyntax ++ " and not(" ++ localUrl ++ " or " ++ numericColor ++ ")] | " ++
    "//@*[local-name()='attributeName'][" ++
      "normalize-space(.)='href' or substring-after(normalize-space(.),':')='href' or " ++
      "normalize-space(.)='src' or substring-after(normalize-space(.),':')='src' or " ++
      "normalize-space(.)='base' or substring-after(normalize-space(.),':')='base' or " ++
      "normalize-space(.)='style' or normalize-space(.)='attributeName' or " ++
      "normalize-space(.)='from' or normalize-space(.)='to' or normalize-space(.)='by' or " ++
      "normalize-space(.)='values' or starts-with(normalize-space(.),'on')]"
  "boolean(/*[local-name()='svg' and namespace-uri()='http://www.w3.org/2000/svg']) and " ++
    "not(" ++ unsupported ++ ")"

/-- libxml2's SAX events as the old boundary read them. -/
def saxBoundary (sax : String) : Except String Bool := do
  let events := (sax.splitOn "\n").map (·.trimAscii.toString)
  let has := fun name => events.any (·.startsWith ("SAX." ++ name ++ "("))
  if ["entityDecl", "attributeDecl", "elementDecl", "notationDecl",
      "unparsedEntityDecl", "resolveEntity", "getParameterEntity",
      "getEntity", "reference"].any has then
    throw "SVG resource boundary refuses DTD declarations and external entities"
  if events.any (fun event =>
      event.startsWith "SAX.error:" || event.startsWith "SAX.fatalError:") then
    throw "SVG validation received an XML parser error"
  unless events.contains "SAX.startDocument()" && events.contains "SAX.endDocument()" do
    throw "SVG validation received no complete XML parse"
  return has "internalSubset" || has "externalSubset"

/-- The terminal-pose stylesheet, `SvgPoster.terminal`'s reference. -/
def stylesheet : String := r#"<xsl:stylesheet version="1.0"
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:s="http://www.w3.org/2000/svg" exclude-result-prefixes="s">
<xsl:output method="xml" encoding="UTF-8"/>
<xsl:template match="/">
  <xsl:if test="//*[starts-with(local-name(),'animate') and not(self::s:animate)] or
    //*[local-name()='set' or local-name()='discard'] or
    (//s:animate and (//s:style or //@style))">
    <xsl:message terminate="yes">SVG last poster requires plain attribute animations without CSS, motion, transforms or set elements</xsl:message>
  </xsl:if>
  <xsl:for-each select="//s:animate">
    <xsl:variable name="attribute" select="@attributeName"/>
    <xsl:variable name="duration" select="normalize-space(@dur)"/>
    <xsl:variable name="duration-number" select="substring($duration,1,string-length($duration)-1)"/>
    <xsl:variable name="seconds" select="number($duration-number)"/>
    <xsl:variable name="first-duration" select="normalize-space((//s:animate)[1]/@dur)"/>
    <xsl:variable name="geometry" select="
      (parent::s:rect and contains('|x|y|width|height|rx|ry|',concat('|',$attribute,'|'))) or
      (parent::s:circle and contains('|cx|cy|r|',concat('|',$attribute,'|'))) or
      (parent::s:ellipse and contains('|cx|cy|rx|ry|',concat('|',$attribute,'|'))) or
      (parent::s:line and contains('|x1|y1|x2|y2|',concat('|',$attribute,'|'))) or
      (parent::s:path and ($attribute='d' or $attribute='stroke-dashoffset')) or
      ((parent::s:text or parent::s:tspan) and ($attribute='x' or $attribute='y')) or
      ($attribute='opacity' and (parent::s:g or parent::s:rect or parent::s:circle or
        parent::s:ellipse or parent::s:line or parent::s:path or parent::s:polygon or
        parent::s:polyline or parent::s:text or parent::s:tspan or parent::s:use or parent::s:image))"/>
    <xsl:if test="not($geometry) or
      @*[namespace-uri()!='' or not(local-name()='attributeName' or local-name()='values' or
        local-name()='keyTimes' or local-name()='dur' or local-name()='begin' or
        local-name()='repeatCount' or local-name()='fill' or local-name()='calcMode' or
        local-name()='attributeType')] or
      not(contains(@values,';')) or
      @attributeName=preceding-sibling::s:animate/@attributeName or
      (@begin and not(normalize-space(@begin)='0' or normalize-space(@begin)='0s')) or
      (@repeatCount and not(@repeatCount='1' or @repeatCount='indefinite')) or
      (@fill and not(@fill='freeze' or @fill='remove')) or
      (@calcMode and not(@calcMode='linear' or @calcMode='discrete')) or
      (@attributeType and not(@attributeType='XML' or @attributeType='auto')) or
      substring($duration,string-length($duration))!='s' or
      translate($duration-number,'0123456789.','')!='' or
      not($seconds &gt; 0 and $seconds - $seconds = 0) or
      $seconds!=number(substring($first-duration,1,string-length($first-duration)-1))">
      <xsl:message terminate="yes">SVG last poster requires one linear/discrete values track per shape geometry or opacity attribute, starting at zero with the same finite duration in seconds; other targets or timing require a PDF frame sequence</xsl:message>
    </xsl:if>
  </xsl:for-each>
  <xsl:apply-templates/>
</xsl:template>
<xsl:template match="@*|node()">
  <xsl:copy><xsl:apply-templates select="@*|node()"/></xsl:copy>
</xsl:template>
<xsl:template match="*[s:animate]">
  <xsl:copy>
    <xsl:for-each select="@*">
      <xsl:if test="not(name()=../s:animate/@attributeName)"><xsl:copy/></xsl:if>
    </xsl:for-each>
    <xsl:for-each select="s:animate">
      <xsl:attribute name="{@attributeName}">
        <xsl:call-template name="terminal">
          <xsl:with-param name="values" select="@values"/>
          <xsl:with-param name="times" select="@keyTimes"/>
          <xsl:with-param name="timed" select="boolean(@keyTimes)"/>
          <xsl:with-param name="discrete" select="@calcMode='discrete'"/>
          <xsl:with-param name="shape" select="substring-before(@values,';')"/>
        </xsl:call-template>
      </xsl:attribute>
    </xsl:for-each>
    <xsl:apply-templates select="node()"/>
  </xsl:copy>
</xsl:template>
<xsl:template match="s:animate"/>
<xsl:template name="scalar">
  <xsl:param name="value"/>
  <xsl:variable name="n" select="number($value)"/>
  <xsl:if test="not($n - $n = 0) or translate($value,'-0123456789.','')!=''">
    <xsl:message terminate="yes">SVG last poster requires finite unitless decimal values in every keyframe</xsl:message>
  </xsl:if>
</xsl:template>
<xsl:template name="path">
  <xsl:param name="points"/>
  <xsl:variable name="pair" select="substring-before(concat($points,'L'),'L')"/>
  <xsl:call-template name="scalar">
    <xsl:with-param name="value" select="normalize-space(substring-before($pair,','))"/>
  </xsl:call-template>
  <xsl:call-template name="scalar">
    <xsl:with-param name="value" select="normalize-space(substring-after($pair,','))"/>
  </xsl:call-template>
  <xsl:if test="contains($points,'L')">
    <xsl:call-template name="path">
      <xsl:with-param name="points" select="substring-after($points,'L')"/>
    </xsl:call-template>
  </xsl:if>
</xsl:template>
<xsl:template name="terminal">
  <xsl:param name="values"/><xsl:param name="times"/>
  <xsl:param name="timed"/><xsl:param name="discrete"/><xsl:param name="shape"/>
  <xsl:param name="previous" select="-1"/>
  <xsl:variable name="value" select="normalize-space(substring-before(concat($values,';'),';'))"/>
  <xsl:variable name="time" select="number(normalize-space(substring-before(concat($times,';'),';')))"/>
  <xsl:if test="$value='' or ($timed and
    (not($time &gt;= 0 and $time &lt;= 1 and $time &gt; $previous) or
      ($previous=-1 and $time!=0)))">
    <xsl:message terminate="yes">SVG last poster requires nonempty values and increasing keyTimes from zero</xsl:message>
  </xsl:if>
  <xsl:choose>
    <xsl:when test="@attributeName='d'">
      <xsl:if test="not(starts-with($value,'M')) or
        (not($discrete) and string-length($value)-string-length(translate($value,'L','')) !=
          string-length($shape)-string-length(translate($shape,'L','')))">
        <xsl:message terminate="yes">SVG last poster requires absolute M/L comma-pair paths with matching commands across linear keyframes</xsl:message>
      </xsl:if>
      <xsl:call-template name="path">
        <xsl:with-param name="points" select="substring($value,2)"/>
      </xsl:call-template>
    </xsl:when>
    <xsl:otherwise>
      <xsl:call-template name="scalar"><xsl:with-param name="value" select="$value"/></xsl:call-template>
      <xsl:if test="contains('|width|height|r|rx|ry|',concat('|',@attributeName,'|')) and number($value) &lt; 0">
        <xsl:message terminate="yes">SVG last poster requires nonnegative sizes in every keyframe</xsl:message>
      </xsl:if>
    </xsl:otherwise>
  </xsl:choose>
  <xsl:choose>
    <xsl:when test="contains($values,';')">
      <xsl:if test="$timed and not(contains($times,';'))">
        <xsl:message terminate="yes">SVG last poster requires one keyTime per value</xsl:message>
      </xsl:if>
      <xsl:call-template name="terminal">
        <xsl:with-param name="values" select="substring-after($values,';')"/>
        <xsl:with-param name="times" select="substring-after($times,';')"/>
        <xsl:with-param name="timed" select="$timed"/>
        <xsl:with-param name="discrete" select="$discrete"/>
        <xsl:with-param name="shape" select="$shape"/>
        <xsl:with-param name="previous" select="$time"/>
      </xsl:call-template>
    </xsl:when>
    <xsl:otherwise>
      <xsl:if test="$timed and (contains($times,';') or
        (not($discrete) and $time!=1) or ($discrete and $time=1))">
        <xsl:message terminate="yes">SVG last poster requires one keyTime per value, ending at one for linear tracks or below one for discrete tracks</xsl:message>
      </xsl:if>
      <xsl:value-of select="$value"/>
    </xsl:otherwise>
  </xsl:choose>
</xsl:template>
</xsl:stylesheet>"#

private def run (cmd : String) (args : Array String) : IO IO.Process.Output :=
  IO.Process.output { cmd, args }

/-- The old boundary's verdict: libxml2's SAX pass, then its XPath over the parse. -/
def judge (bytes : ByteArray) : IO (Except String Unit) := IO.FS.withTempDir fun dir => do
  let input := dir / "source.svg"
  IO.FS.writeBinFile input bytes
  let sax ← run "xmllint" #["--nonet", "--nocatalogs", "--sax", input.toString]
  if sax.exitCode != 0 then return .error s!"xmllint exited {sax.exitCode}"
  match saxBoundary sax.stdout with
  | .error e => return .error e
  | .ok _ =>
    let xp ← run "xmllint" #["--nonet", "--nocatalogs", "--xpath", supportedSvg, input.toString]
    if xp.exitCode != 0 then return .error s!"xmllint exited {xp.exitCode}"
    return if xp.stdout.trimAscii.toString == "true" then .ok ()
      else .error "SVG resource boundary refuses the source"

/-- The old projection's terminal pose, as libxslt writes it, or its message. -/
def terminal (bytes : ByteArray) : IO (Except String ByteArray) := IO.FS.withTempDir fun dir => do
  let input := dir / "source.svg"
  let style := dir / "terminal.xsl"
  IO.FS.writeBinFile input bytes
  IO.FS.writeFile style stylesheet
  let out ← run "xsltproc" #["--nonet", "--novalid", "--nodtdattr", "--nowrite", "--nomkdir",
    style.toString, input.toString]
  if out.exitCode != 0 then return .error (out.stdout ++ out.stderr)
  return .ok out.stdout.toUTF8

end Tests.SvgLegacy
