-- ltgrid: each text line of the main vertical list stands a whole number of grid lines below the
-- text line before it, its interline glue moving it to the nearest grid line.
local ltgrid = { leading = 0, on = false, level = 0 }

local glue_id = node.id("glue")
local kern_id = node.id("kern")
local hlist_id = node.id("hlist")
local vlist_id = node.id("vlist")
local rule_id = node.id("rule")
local line_subtype = 1
local tolerance = 655
local ignore_depth = -65536000

local function last_node(head)
  local n = head
  while n and n.next do n = n.next end
  return n
end

local function walk(n, stop, sum)
  while n and n ~= stop do
    local id = n.id
    if id == hlist_id and n.subtype == line_subtype then
      return sum + n.depth, true
    elseif id == glue_id then
      sum = sum + n.width
    elseif id == kern_id then
      sum = sum + n.kern
    elseif id == hlist_id or id == vlist_id or id == rule_id then
      sum = sum + n.height + n.depth
    end
    n = n.prev
  end
  return sum, false
end

local function since_last_line()
  local ptr = tex.nest.ptr
  if ptr > 0 then
    local sum, found = walk(tex.nest[ptr].tail, tex.nest[ptr].head, 0)
    if found then return sum end
    return sum - ltgrid.leading
  end
  local contrib = tex.lists.contrib_head
  local sum, found = walk(tex.nest[0].tail, contrib, 0)
  if found then return sum end
  local page = tex.lists.page_head
  if page == nil or page.next == nil then return nil end
  sum, found = walk(last_node(page), page, sum)
  if found then return sum end
  return sum - tex.topskip.width
end

local function interline(box, prevdepth)
  if prevdepth <= ignore_depth then return nil end
  local bs = tex.baselineskip
  local d = bs.width - prevdepth - box.height
  local g = node.new(glue_id)
  if d < tex.lineskiplimit then
    local ls = tex.lineskip
    g.subtype = 1
    node.setglue(g, ls.width, ls.stretch, ls.shrink, ls.stretch_order, ls.shrink_order)
  else
    g.subtype = 2
    node.setglue(g, d, bs.stretch, bs.shrink, bs.stretch_order, bs.shrink_order)
  end
  return g
end

local function append(box, location, prevdepth, mirrored)
  local g = interline(box, prevdepth)
  local L = ltgrid.leading
  if ltgrid.on and L > 0 and tex.nest.ptr == ltgrid.level and box.id == hlist_id
      and box.subtype == line_subtype then
    local before = since_last_line()
    if before then
      local dist = before + (g and g.width or 0) + box.height
      local off = dist % L
      local delta = 0
      if off > tolerance and L - off > tolerance then
        if 2 * off <= L then delta = -off else delta = L - off end
      end
      if delta ~= 0 then
        if g == nil then
          g = node.new(glue_id)
          g.subtype = 2
        end
        g.width = g.width + delta
      end
    end
  end
  if g then
    g.next = box
    box.prev = g
    return g, box.depth
  end
  return box, box.depth
end

function ltgrid.enable(leading)
  ltgrid.leading = leading
  ltgrid.on = true
end

function ltgrid.disable()
  ltgrid.on = false
end

-- A frame's body box: its lines stand on the grid from one leading below its top.
function ltgrid.frame()
  ltgrid.level = tex.nest.ptr
end

function ltgrid.main()
  ltgrid.level = 0
end

luatexbase.add_to_callback("append_to_vlist_filter", append, "ltgrid.append")

return ltgrid
