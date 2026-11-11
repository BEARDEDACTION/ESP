--[[
    SWANGY ESP  v2.0  (Matcha)
    Generators / Windows / Pallets / Bear Traps

    HOW TO RUN
      Option A: paste this whole file into Matcha and execute it.
      Option B: save it as  swangy_esp.lua  in your Matcha workspace folder, then run:
                    loadstring(readfile("swangy_esp.lua"))()

    - Re-running replaces the old copy automatically (no duplicate drawings).
    - Settings (toggles, ranges, fill, FPS cap) are remembered in swangy_esp.cfg.
    - Menu tab: "Swangy ESP".
    - Console control:  _G.__SWANGY.gen.Toggle()   _G.__SWANGY.SetRange(500)   _G.__SWANGY.unload()
]]

local VERSION = "2.0"
local G = _G

if G.__SWANGY and type(G.__SWANGY.unload) == "function" then pcall(G.__SWANGY.unload) end

local Players    = game:GetService("Players")
local RunService = game:GetService("RunService")
local Workspace  = game:GetService("Workspace")
local lp         = Players.LocalPlayer

local clock = (os and os.clock) or tick
local floor, sqrt, max, abs, huge = math.floor, math.sqrt, math.max, math.abs, math.huge
local sfmt, sfind, slower = string.format, string.find, string.lower
local V2, V3 = Vector2.new, Vector3.new
local wait = (task and task.wait) or wait
local spawn = (task and task.spawn) or spawn

-- ============================================================
-- config
-- ============================================================
local CFG = {
    master = true,
    names  = true,
    drawHz = 0,                       -- 0 = draw every frame, otherwise max draw FPS
    gen  = { on = true, range = 1000, fill = true, fillA = 0.25, thick = 1.6, text = 13, state = true },
    win  = { on = true, range = 1000, fill = true, fillA = 0.20, thick = 1.6, text = 12 },
    pal  = { on = true, range = 1000, fill = true, fillA = 0.20, thick = 1.6, text = 12 },
    trap = { on = true, range = 1000, fill = true, fillA = 0.20, thick = 1.6, text = 12 },
}

local PAL_HZ       = 6      -- pallet state polls per second
local WORLD_DT     = 1      -- seconds between world/map checks
local WIN_BUDGET   = 0.004  -- max seconds of window scanning per worker tick
local LOD_RECT     = 16     -- below this many screen px a box is drawn as a tiny rect
local LOD_NONE     = 3      -- below this the box is skipped (label only)

local rgb = Color3.fromRGB
local function lerpColor(a, b, t)
    if t < 0 then t = 0 elseif t > 1 then t = 1 end
    return Color3.new(a.R + (b.R - a.R) * t, a.G + (b.G - a.G) * t, a.B + (b.B - a.B) * t)
end

local COL = {
    genIdle = rgb(255, 150, 40), genDone = rgb(51, 255, 77),
    genBroken = rgb(255, 120, 120), genPaused = rgb(255, 210, 110),
    win = rgb(255, 230, 0),
    pal = rgb(60, 140, 255), palDropped = rgb(255, 50, 50),
    trapArmed = rgb(80, 255, 120), trapSprung = rgb(255, 60, 60),
}

local FONT
do
    local f = Drawing.Fonts
    if f then FONT = f.SystemBold or f.System end
end

-- ============================================================
-- shared state
-- ============================================================
local S = {
    running = true, dirty = false, camera = nil,
    lastFrame = 0, frameN = 0, fpsMark = clock(), drawFps = 0,
    renderMs = 0, workMs = 0,
    perfLine = "", countLine = "",
    stamp = "none", cnt = 0, cntAt = 0,
    genGeo = {}, genAt = 0, genCursor = 0,
    winGeo = {}, winAt = 0, winJob = nil,
    palIndex = {}, palParts = {}, palGeo = {},
    palFolder = nil, palFolderMap = nil, palMisses = 0,
    trapIndex = {}, trapTrapped = {}, trapVictimAt = 0, trapAt = 0,
    menuFrames = 0,
}

local camX, camY, camZ = 0, 0, 0
local camVpW, camVpH, pxK = 1920, 1080, 770
local fovDeg = 70

local API = {}
local connection

-- ============================================================
-- safe accessors (static functions: no closure allocated per call)
-- ============================================================
local function rawGet(i, k)  return i[k] end
local function rawAttr(i, k) return i:GetAttribute(k) end
local function rawKids(i)    return i:GetChildren() end
local function rawDesc(i)    return i:GetDescendants() end
local function rawFind(i, k) return i:FindFirstChild(k) end

local function prop(i, k)
    if i == nil then return nil end
    local ok, v = pcall(rawGet, i, k)
    if ok then return v end
end
local function attr(i, k)
    if i == nil then return nil end
    local ok, v = pcall(rawAttr, i, k)
    if ok then return v end
end
local function kids(i)
    if i == nil then return nil end
    local ok, v = pcall(rawKids, i)
    if ok and type(v) == "table" then return v end
end
local function descs(i)
    if i == nil then return nil end
    local ok, v = pcall(rawDesc, i)
    if ok and type(v) == "table" then return v end
end
local function child(i, k)
    if i == nil then return nil end
    local ok, v = pcall(rawFind, i, k)
    if ok then return v end
end
local function address(i)
    local a = prop(i, "Address")
    if type(a) == "number" and a ~= 0 then return a end
end
local function attrNum(i, k)
    local v = attr(i, k)
    if type(v) == "number" then return v end
end
local function attrBool(i, k)
    local v = attr(i, k)
    if type(v) == "boolean" then return v end
end

local PART_CLASS = {
    Part = true, MeshPart = true, UnionOperation = true,
    WedgePart = true, CornerWedgePart = true, TrussPart = true,
}
local function isPart(i) return PART_CLASS[prop(i, "ClassName")] == true end

-- ============================================================
-- geometry (everything numeric is cached once per object)
-- ============================================================
local function basisOf(cf)
    if cf then
        local r, u, l = prop(cf, "RightVector"), prop(cf, "UpVector"), prop(cf, "LookVector")
        if r and u and l then
            return r.X, r.Y, r.Z, u.X, u.Y, u.Z, -l.X, -l.Y, -l.Z
        end
    end
    return 1, 0, 0, 0, 1, 0, 0, 0, 1
end

local function makeGeo(pos, hx, hy, hz, cf)
    local g = {
        pos = pos, x = pos.X, y = pos.Y, z = pos.Z,
        hx = hx, hy = hy, hz = hz, rad = sqrt(hx * hx + hy * hy + hz * hz),
    }
    g.rX, g.rY, g.rZ, g.uX, g.uY, g.uZ, g.bX, g.bY, g.bZ = basisOf(cf)
    return g
end

local CORNER = {
    {-1, -1, -1}, { 1, -1, -1}, {-1,  1, -1}, { 1,  1, -1},
    {-1, -1,  1}, { 1, -1,  1}, {-1,  1,  1}, { 1,  1,  1},
}
local EA = {1, 2, 4, 3, 5, 6, 8, 7, 1, 2, 3, 4}
local EB = {2, 4, 3, 1, 6, 8, 7, 5, 5, 6, 7, 8}

local function buildCorners(g)
    local cn = {}
    local x, y, z, hx, hy, hz = g.x, g.y, g.z, g.hx, g.hy, g.hz
    for i = 1, 8 do
        local c = CORNER[i]
        local ax, ay, az = c[1] * hx, c[2] * hy, c[3] * hz
        cn[i] = V3(x + g.rX * ax + g.uX * ay + g.bX * az,
                   y + g.rY * ax + g.uY * ay + g.bY * az,
                   z + g.rZ * ax + g.uZ * ay + g.bZ * az)
    end
    g.cn = cn
    return cn
end

-- ============================================================
-- drawing slots (created lazily, only when something needs one)
-- ============================================================
local function newText(size)
    local t = Drawing.new("Text")
    pcall(function() t.Size = size end)
    pcall(function() t.FontSize = size end)
    t.Outline = true
    t.Center = true
    t.Visible = false
    if FONT then pcall(function() t.Font = FONT end) end
    return t
end

local function newSlot(cat, idx)
    local thick = cat.cfg.thick
    local lines = {}
    for i = 1, 12 do
        local ln = Drawing.new("Line")
        ln.Thickness = thick
        ln.Visible = false
        lines[i] = ln
    end
    local e = {
        lines = lines, tris = {}, triVis = 0,
        lfx = {}, lfy = {}, ltx = {}, lty = {}, lth = {}, lcol = {}, lvis = {},
        tcol = {}, talp = {},
        top = newText(cat.cfg.text), topVis = false, subVis = false, vis = false,
    }
    if cat.hasSub then e.sub = newText(cat.cfg.text - 2) end
    cat.pool[idx] = e
    return e
end

local function getTri(e, i)
    local tr = e.tris[i]
    if not tr then
        tr = Drawing.new("Triangle")
        tr.Thickness = 0
        pcall(function() tr.Filled = true end)
        tr.Visible = false
        e.tris[i] = tr
    end
    return tr
end

local function hideLines(e, from)
    local lv, ls = e.lvis, e.lines
    for i = from, 12 do
        if lv[i] then lv[i] = false; ls[i].Visible = false end
    end
end

local function hideTris(e)
    if e.triVis > 0 then
        for i = 1, e.triVis do e.tris[i].Visible = false end
        e.triVis = 0
    end
end

local function hideSlot(e)
    if not e.vis then return end
    e.vis = false
    hideLines(e, 1)
    hideTris(e)
    if e.topVis then e.topVis = false; e.top.Visible = false end
    if e.subVis then e.subVis = false; e.sub.Visible = false end
end

local function removeSlot(e)
    if not e then return end
    for _, ln in ipairs(e.lines) do pcall(function() ln:Remove() end) end
    for _, tr in pairs(e.tris) do pcall(function() tr:Remove() end) end
    pcall(function() e.top:Remove() end)
    if e.sub then pcall(function() e.sub:Remove() end) end
end

local function setLine(e, i, x1, y1, x2, y2, colour, thick)
    local ln = e.lines[i]
    if e.lfx[i] ~= x1 or e.lfy[i] ~= y1 then
        e.lfx[i], e.lfy[i] = x1, y1
        ln.From = V2(x1, y1)
    end
    if e.ltx[i] ~= x2 or e.lty[i] ~= y2 then
        e.ltx[i], e.lty[i] = x2, y2
        ln.To = V2(x2, y2)
    end
    if e.lth[i] ~= thick then e.lth[i] = thick; ln.Thickness = thick end
    if e.lcol[i] ~= colour then
        e.lcol[i] = colour
        ln.Color = colour
        ln.Transparency = 1
    end
    if not e.lvis[i] then e.lvis[i] = true; ln.Visible = true end
end

-- convex hull of the projected corners (scratch tables, no allocation per frame)
local sx, sy = {}, {}
local ord, hs = {}, {}

local function hullCross(o, a, b)
    return (sx[a] - sx[o]) * (sy[b] - sy[o]) - (sy[a] - sy[o]) * (sx[b] - sx[o])
end

local function buildHull()
    local n = 0
    for i = 1, 8 do
        if sx[i] then n = n + 1; ord[n] = i end
    end
    if n < 3 then return 0 end
    for i = 2, n do                                  -- insertion sort by x, then y
        local v = ord[i]
        local vx, vy = sx[v], sy[v]
        local j = i - 1
        while j >= 1 do
            local u = ord[j]
            local ux, uy = sx[u], sy[u]
            if ux > vx or (ux == vx and uy > vy) then
                ord[j + 1] = u
                j = j - 1
            else
                break
            end
        end
        ord[j + 1] = v
    end
    local k = 0
    for i = 1, n do
        local p = ord[i]
        while k >= 2 and hullCross(hs[k - 1], hs[k], p) <= 0 do k = k - 1 end
        k = k + 1
        hs[k] = p
    end
    local t = k + 1
    for i = n - 1, 1, -1 do
        local p = ord[i]
        while k >= t and hullCross(hs[k - 1], hs[k], p) <= 0 do k = k - 1 end
        k = k + 1
        hs[k] = p
    end
    k = k - 1
    if k < 3 then return 0 end
    return k
end

-- Draws one 3D box. Returns labelX, topY, botY (screen) or nil when nothing is visible.
local function drawBox(e, g, d, colour, fillA, thick)
    local cp, onC = WorldToScreen(g.pos)
    if not (onC and cp) and d > 30 then
        hideSlot(e)
        return nil
    end

    -- level of detail: far / tiny objects don't need 8 projected corners
    if onC and cp then
        local px = g.rad * 2 * pxK / (d > 1 and d or 1)
        if px < LOD_RECT then
            local x, y = cp.X, cp.Y
            e.vis = true
            hideTris(e)
            if px < LOD_NONE then
                hideLines(e, 1)
                return x, y - 3, y + 3
            end
            local h = px * 0.38
            local x1, y1, x2, y2 = x - h, y - h, x + h, y + h
            setLine(e, 1, x1, y1, x2, y1, colour, thick)
            setLine(e, 2, x2, y1, x2, y2, colour, thick)
            setLine(e, 3, x2, y2, x1, y2, colour, thick)
            setLine(e, 4, x1, y2, x1, y1, colour, thick)
            hideLines(e, 5)
            return x, y1, y2
        end
    end

    -- camera inside / touching the box: hide it
    local dx, dy, dz = camX - g.x, camY - g.y, camZ - g.z
    local ox = abs(dx * g.rX + dy * g.rY + dz * g.rZ) - g.hx
    local oy = abs(dx * g.uX + dy * g.uY + dz * g.uZ) - g.hy
    local oz = abs(dx * g.bX + dy * g.bY + dz * g.bZ) - g.hz
    if ox < 0 then ox = 0 end
    if oy < 0 then oy = 0 end
    if oz < 0 then oz = 0 end
    if ox * ox + oy * oy + oz * oz < 1.44 then
        hideSlot(e)
        return nil
    end

    local cn = g.cn or buildCorners(g)
    local frontN = 0
    local minX, maxX, minY, maxY = huge, -huge, huge, -huge
    for i = 1, 8 do
        local sp, ok = WorldToScreen(cn[i])
        if ok and sp then
            local x, y = sp.X, sp.Y
            sx[i], sy[i] = x, y
            frontN = frontN + 1
            if x < minX then minX = x end
            if x > maxX then maxX = x end
            if y < minY then minY = y end
            if y > maxY then maxY = y end
        else
            sx[i] = nil
        end
    end
    if frontN == 0 or (maxX - minX) > camVpW * 4 or (maxY - minY) > camVpH * 4 then
        hideSlot(e)
        return nil
    end

    e.vis = true
    local shown, lv = 0, e.lvis
    for i = 1, 12 do
        local a, b = EA[i], EB[i]
        local x1, x2 = sx[a], sx[b]
        if x1 and x2 then
            setLine(e, i, x1, sy[a], x2, sy[b], colour, thick)
            shown = shown + 1
        elseif lv[i] then
            lv[i] = false
            e.lines[i].Visible = false
        end
    end
    if shown == 0 then
        hideSlot(e)
        return nil
    end

    -- translucent fill (only for fully visible, reasonably large boxes)
    if fillA and frontN == 8 and (maxY - minY) >= 26 then
        local m = buildHull()
        local old, tri = e.triVis, 0
        if m >= 3 then
            local a = hs[1]
            local ax, ay = sx[a], sy[a]
            for i = 2, m - 1 do
                tri = tri + 1
                local tr = getTri(e, tri)
                local b, c = hs[i], hs[i + 1]
                tr.PointA = V2(ax, ay)
                tr.PointB = V2(sx[b], sy[b])
                tr.PointC = V2(sx[c], sy[c])
                if e.tcol[tri] ~= colour then e.tcol[tri] = colour; tr.Color = colour end
                if e.talp[tri] ~= fillA then e.talp[tri] = fillA; tr.Transparency = fillA end
                if tri > old then tr.Visible = true end
            end
        end
        for i = tri + 1, old do e.tris[i].Visible = false end
        e.triVis = tri
    else
        hideTris(e)
    end

    return (minX + maxX) * 0.5, minY, maxY
end

-- ============================================================
-- categories (draw + label logic)
-- ============================================================
local CATS = {
    gen  = { key = "gen",  name = "Generator", cfg = CFG.gen,  cap = 16, off = 18, hasSub = true,  list = {}, pool = {}, shown = 0 },
    win  = { key = "win",  name = "Window",    cfg = CFG.win,  cap = 24, off = 16, hasSub = false, list = {}, pool = {}, shown = 0 },
    pal  = { key = "pal",  name = "Pallet",    cfg = CFG.pal,  cap = 20, off = 16, hasSub = false, list = {}, pool = {}, shown = 0 },
    trap = { key = "trap", name = "Bear Trap", cfg = CFG.trap, cap = 12, off = 16, hasSub = false, list = {}, pool = {}, shown = 0 },
}
local ORDER = { CATS.gen, CATS.win, CATS.pal, CATS.trap }

local function genColour(prog, state)
    if state == "regress" then return COL.genBroken end
    if state == "paused" then return COL.genPaused end
    return lerpColor(COL.genIdle, COL.genDone, (prog or 0) / 100)
end

function CATS.gen.colour(t)
    if t.cP ~= t.prog or t.cS ~= t.state then
        t.cP, t.cS = t.prog, t.state
        t.col = genColour(t.prog, t.state)
    end
    return t.col
end
function CATS.gen.labels(e, t, d)
    local names = CFG.names
    local showState = names and CFG.gen.state
    local pct, dm = floor(t.prog + 0.5), floor(d + 0.5)
    if e.k1 ~= pct or e.k2 ~= dm or e.k3 ~= t.state or e.k4 ~= t.crew
        or e.k5 ~= names or e.k6 ~= showState then
        e.k1, e.k2, e.k3, e.k4, e.k5, e.k6 = pct, dm, t.state, t.crew, names, showState
        if names then e.s1 = sfmt("GEN %d%%   %dm", pct, dm) else e.s1 = sfmt("%d%%", pct) end
        local s2 = ""
        if showState then
            s2 = t.state
            if t.crew > 0 then s2 = s2 .. "  x" .. t.crew end
        end
        e.s2 = s2
    end
    return e.s1, e.s2
end

function CATS.win.colour() return COL.win end
function CATS.win.labels(e, t, d)
    if not CFG.names then return nil end
    local dm = floor(d + 0.5)
    if e.k2 ~= dm then e.k2 = dm; e.s1 = sfmt("WINDOW   %dm", dm) end
    return e.s1
end

function CATS.pal.colour(t) return t.dropped and COL.palDropped or COL.pal end
function CATS.pal.labels(e, t, d)
    if not CFG.names then return nil end
    local dm = floor(d + 0.5)
    if e.k2 ~= dm or e.k3 ~= t.dropped then
        e.k2, e.k3 = dm, t.dropped
        e.s1 = sfmt("%s   %dm", t.dropped and "PALLET DOWN" or "PALLET", dm)
    end
    return e.s1
end

function CATS.trap.colour(t) return (t.armed == false) and COL.trapSprung or COL.trapArmed end
function CATS.trap.labels(e, t, d)
    if not CFG.names then return nil end
    local dm = floor(d + 0.5)
    local vic = (t.armed == false) and (t.victim or "TRAPPED") or false
    if e.k2 ~= dm or e.k3 ~= vic then
        e.k2, e.k3 = dm, vic
        local s = sfmt("BEAR TRAP  %dm", dm)
        if vic then s = s .. "  " .. vic end
        e.s1 = s
    end
    return e.s1
end

local function drawCat(cat, cx, cy, cz)
    local cfg, list, pool = cat.cfg, cat.list, cat.pool
    local r2 = cfg.range * cfg.range
    local fillA = cfg.fill and cfg.fillA or nil
    local thick, off = cfg.thick, cat.off
    local colourOf, labelsOf, hasSub = cat.colour, cat.labels, cat.hasSub
    local cap, n = cat.cap, 0

    for i = 1, #list do
        if n >= cap then break end
        local t = list[i]
        local g = t.g
        if g then
            local dx, dy, dz = g.x - cx, g.y - cy, g.z - cz
            local d2 = dx * dx + dy * dy + dz * dz
            if d2 <= r2 then
                n = n + 1
                local e = pool[n] or newSlot(cat, n)
                local d = sqrt(d2)
                local colour = colourOf(t)
                local lx, topY, botY = drawBox(e, g, d, colour, fillA, thick)
                if lx then
                    local l1, l2 = labelsOf(e, t, d)
                    local tp = e.top
                    if l1 then
                        if e.s1v ~= l1 then e.s1v = l1; tp.Text = l1 end
                        if e.colv ~= colour then
                            e.colv = colour
                            tp.Color = colour
                            if e.sub then e.sub.Color = colour end
                        end
                        local ty = topY - off
                        if e.tx ~= lx or e.ty ~= ty then
                            e.tx, e.ty = lx, ty
                            tp.Position = V2(lx, ty)
                        end
                        if not e.topVis then e.topVis = true; tp.Visible = true end
                    elseif e.topVis then
                        e.topVis = false
                        tp.Visible = false
                    end
                    if hasSub and l1 and l2 and l2 ~= "" then
                        local sb = e.sub
                        if e.s2v ~= l2 then e.s2v = l2; sb.Text = l2 end
                        local by = botY + 2
                        if e.subX ~= lx or e.subY ~= by then
                            e.subX, e.subY = lx, by
                            sb.Position = V2(lx, by)
                        end
                        if not e.subVis then e.subVis = true; sb.Visible = true end
                    elseif e.subVis then
                        e.subVis = false
                        e.sub.Visible = false
                    end
                end
            end
        end
    end

    for i = n + 1, cat.shown do
        local e = pool[i]
        if e then hideSlot(e) end
    end
    cat.shown = n
end

-- ============================================================
-- generators
-- ============================================================
local GEN_SKIP = { "hitbox", "point", "anchor", "handle", "invis" }

local function skippedName(name)
    local n = slower(tostring(name))
    for i = 1, #GEN_SKIP do
        if sfind(n, GEN_SKIP[i], 1, true) then return true end
    end
    return false
end

local function genStateFrom(prog, crew, model)
    if prog >= 100 or attrBool(model, "Completed") == true then return "done" end
    if attrBool(model, "Regressing") == true then return "regress" end
    if attrBool(model, "ProgressPaused") == true then return "paused" end
    if crew > 0 then return "active" end
    return "idle"
end

local function firstPart(model)
    local list = kids(model)
    if not list then return nil end
    for _, c in ipairs(list) do
        if isPart(c) then return c end
    end
    for _, c in ipairs(list) do
        local sub = kids(c)
        if sub then
            for _, s in ipairs(sub) do
                if isPart(s) then return s end
            end
        end
    end
end

local function genGeometry(model)
    local desc = descs(model)
    if not desc then return nil end
    local mnX, mnY, mnZ = huge, huge, huge
    local mxX, mxY, mxZ = -huge, -huge, -huge
    local rotPart, any = nil, false

    for _, part in ipairs(desc) do
        if isPart(part) and not skippedName(prop(part, "Name")) then
            local tr = prop(part, "Transparency")
            local visible = not (type(tr) == "number" and tr > 0.05 and tr <= 1)
            if visible then
                local p, s = prop(part, "Position"), prop(part, "Size")
                if p and s then
                    local hx, hy, hz = s.X * 0.5, s.Y * 0.5, s.Z * 0.5
                    if hx >= 0.02 and hx <= 100 then
                        if p.X - hx < mnX then mnX = p.X - hx end
                        if p.X + hx > mxX then mxX = p.X + hx end
                        if p.Y - hy < mnY then mnY = p.Y - hy end
                        if p.Y + hy > mxY then mxY = p.Y + hy end
                        if p.Z - hz < mnZ then mnZ = p.Z - hz end
                        if p.Z + hz > mxZ then mxZ = p.Z + hz end
                        any = true
                        if not rotPart then rotPart = part end
                    end
                end
            end
        end
    end
    if not any then return nil end

    local hx, hy, hz = (mxX - mnX) * 0.5, (mxY - mnY) * 0.5, (mxZ - mnZ) * 0.5
    if hx < 0.05 or hy < 0.05 then return nil end
    if hx > 7 or hy > 7 or hz > 7 then return nil end
    local center = V3((mnX + mxX) * 0.5, (mnY + mxY) * 0.5, (mnZ + mxZ) * 0.5)
    return makeGeo(center, hx, hy, hz, prop(rotPart, "CFrame"))
end

local function findGenFolder(map, mapKids)
    local lists = { mapKids or {} }
    local res = child(map, "resources")
    if res then
        local sub = kids(res)
        if sub then lists[2] = sub end
    end
    for _, list in ipairs(lists) do
        for _, ch in ipairs(list) do
            if prop(ch, "ClassName") == "Folder" then
                local n = slower(tostring(prop(ch, "Name")))
                if sfind(n, "generator", 1, true) or sfind(n, "gens", 1, true) then
                    local sub = kids(ch)
                    if sub and #sub > 0 then return ch, sub end
                end
            end
        end
    end
end

local function collectGens()
    local out = {}
    local map = Workspace:FindFirstChild("Map")
    if not map then return out end
    local mapKids = kids(map)

    local function note(model)
        local part = child(model, "HitBox") or child(model, "RootPart")
            or child(model, "GeneratorBody") or firstPart(model)
        if not part or not prop(part, "Position") then return end
        local prog = attrNum(model, "RepairProgress") or 0
        local crew = attrNum(model, "PlayersRepairingCount") or 0
        out[#out + 1] = {
            model = model, key = address(model),
            prog = prog, crew = crew, state = genStateFrom(prog, crew, model), stateAt = 0,
        }
    end

    local folder, items = findGenFolder(map, mapKids)
    if folder then
        for _, m in ipairs(items) do
            if attrNum(m, "RepairProgress") or attrNum(m, "PlayersRepairingCount")
                or attrNum(m, "Progress") then
                note(m)
            end
        end
        return out
    end

    if not mapKids then return out end
    for _, ch in ipairs(mapKids) do
        if attrNum(ch, "RepairProgress") or attrNum(ch, "PlayersRepairingCount") then
            note(ch)
        else
            local sub = kids(ch)
            if sub then
                for _, s in ipairs(sub) do
                    if attrNum(s, "RepairProgress") then note(s) end
                end
            end
        end
    end
    return out
end

local function discoverGens(now)
    for k, v in pairs(S.genGeo) do
        if v == false then S.genGeo[k] = nil end      -- retry failed measurements
    end
    local kept = {}
    for _, t in ipairs(collectGens()) do
        local g
        if t.key then
            g = S.genGeo[t.key]
            if g == nil then
                g = genGeometry(t.model) or false
                S.genGeo[t.key] = g
            end
        else
            g = genGeometry(t.model)
        end
        if g then
            t.g = g
            kept[#kept + 1] = t
        end
    end
    CATS.gen.list = kept
    S.genAt = now + (kept[1] and 60 or 3)
end

-- polls one in-range generator per call (round robin)
local function updateGenStates()
    local list = CATS.gen.list
    local n = #list
    if n == 0 then return end
    local now = clock()
    local r2 = CFG.gen.range * CFG.gen.range
    for _ = 1, n do
        S.genCursor = S.genCursor % n + 1
        local t = list[S.genCursor]
        local g = t and t.g
        if g then
            local dx, dy, dz = g.x - camX, g.y - camY, g.z - camZ
            if dx * dx + dy * dy + dz * dz <= r2 then
                local p = attrNum(t.model, "RepairProgress")
                local c = attrNum(t.model, "PlayersRepairingCount")
                if p then t.prog = p end
                if c then t.crew = c end
                if now >= t.stateAt then
                    t.stateAt = now + 1.5
                    t.state = genStateFrom(t.prog, t.crew, t.model)
                end
                return
            end
        end
    end
end

-- ============================================================
-- windows (scanned in small time-sliced chunks so there are no hitches)
-- ============================================================
local function windowEntry(part)
    local key = address(part)
    local g = key and S.winGeo[key]
    if g then return g end
    local pos, size = prop(part, "Position"), prop(part, "Size")
    if not pos or not size then return nil end
    g = makeGeo(pos, size.X * 0.5, size.Y * 0.5, size.Z * 0.5, prop(part, "CFrame"))
    g.g = g
    if key then S.winGeo[key] = g end
    return g
end

local function startWindowJob(now)
    local map = Workspace:FindFirstChild("Map")
    local d = map and descs(map)
    if not d then
        CATS.win.list = {}
        S.winAt = now + 5
        return
    end
    S.winJob = { stage = 1, d = d, i = 1, holders = {}, h = 1, seen = {},
                 cand = {}, bot = {}, anyBottom = false, c = 1, out = {} }
end

local function winStep()
    local job = S.winJob
    if not job then return end
    local t0 = clock()

    if job.stage == 1 then
        local d, holders = job.d, job.holders
        local i, n = job.i, #job.d
        while i <= n do
            local nm = prop(d[i], "Name")
            if type(nm) == "string" and (sfind(nm, "indow", 1, true) or sfind(nm, "INDOW", 1, true)) then
                holders[#holders + 1] = d[i]
            end
            i = i + 1
            if i % 24 == 0 and clock() - t0 > WIN_BUDGET then break end
        end
        job.i = i
        if i > n then job.stage = 2 end

    elseif job.stage == 2 then
        local holders = job.holders
        while job.h <= #holders do
            local sub = descs(holders[job.h])
            job.h = job.h + 1
            if sub then
                for k = 1, #sub do
                    local part = sub[k]
                    if isPart(part) then
                        local key = address(part)
                        if not key or not job.seen[key] then
                            if key then job.seen[key] = true end
                            local nm = prop(part, "Name")
                            local isBottom = type(nm) == "string" and slower(nm) == "bottom"
                            job.cand[#job.cand + 1] = part
                            job.bot[#job.bot + 1] = isBottom
                            if isBottom then job.anyBottom = true end
                        end
                    end
                end
            end
            if clock() - t0 > WIN_BUDGET then break end
        end
        if job.h > #holders then job.stage = 3 end

    else
        local cand = job.cand
        while job.c <= #cand do
            local idx = job.c
            job.c = idx + 1
            if (not job.anyBottom) or job.bot[idx] then
                local g = windowEntry(cand[idx])
                if g then job.out[#job.out + 1] = g end
            end
            if clock() - t0 > WIN_BUDGET then break end
        end
        if job.c > #cand then
            CATS.win.list = job.out
            S.winJob = nil
            S.winAt = clock() + (#job.out > 0 and 90 or 6)
        end
    end
end

-- ============================================================
-- pallets
-- ============================================================
local function palletBin(map)
    if S.palFolder and S.palFolderMap == map and prop(S.palFolder, "Parent") then
        return S.palFolder
    end
    S.palFolder, S.palFolderMap = nil, map

    local parents = { map }
    local res = child(map, "resources")
    if res then parents[2] = res end

    for _, parent in ipairs(parents) do
        local list = kids(parent)
        if list then
            for _, c in ipairs(list) do
                local n = slower(tostring(prop(c, "Name")))
                if n == "pallets" or n == "pallet" then S.palFolder = c; return c end
            end
        end
    end
    for _, parent in ipairs(parents) do
        local list = kids(parent)
        if list then
            for _, c in ipairs(list) do
                if sfind(slower(tostring(prop(c, "Name"))), "pallet", 1, true) then
                    S.palFolder = c
                    return c
                end
            end
        end
    end
    return nil
end

local function palGeometry(part)
    local addr = address(part)
    local cached = addr and S.palGeo[addr]
    if cached then return cached end
    local pos, size, cf = prop(part, "Position"), prop(part, "Size"), prop(part, "CFrame")
    if not pos or not size or not cf then return nil end
    local g = makeGeo(pos, size.X * 0.5, size.Y * 0.5, size.Z * 0.5, cf)
    if addr then S.palGeo[addr] = g end
    return g
end

local function palletMissing()
    S.palMisses = S.palMisses + 1
    S.palFolder = nil
    if S.palMisses >= max(2, floor(PAL_HZ)) then
        S.palIndex, S.palMisses = {}, 0
        return true
    end
    return false
end

local function collectPallets()
    local map = Workspace:FindFirstChild("Map")
    if not map then return palletMissing() and {} or nil end
    local folder = palletBin(map)
    if not folder then return palletMissing() and {} or nil end
    S.palMisses = 0

    local items = kids(folder)
    if not items then return nil end

    local list, newIndex, now = {}, {}, clock()
    local index = S.palIndex
    for _, model in ipairs(items) do
        local modelKey = address(model)
        local parts = modelKey and S.palParts[modelKey]
        if not parts then
            parts = {
                intact = child(child(model, "Intact"), "Pallet"),
                broken = child(child(model, "Broken"), "Pallet_Broken"),
            }
            if modelKey and (parts.intact or parts.broken) then S.palParts[modelKey] = parts end
        end
        local intact, broken = parts.intact, parts.broken
        if intact and broken then
            local key = modelKey or address(intact)
            if key then
                local entry = index[key] or { dropped = false, pending = 0 }

                local near = true
                local eg = entry.g
                if eg then
                    local dx, dy, dz = eg.x - camX, eg.y - camY, eg.z - camZ
                    near = (dx * dx + dy * dy + dz * dz) <= 22500
                end
                local cc
                if near or now >= (entry.stateAt or 0) then
                    entry.stateAt = now + (near and 0 or 0.6)
                    cc = prop(intact, "CanCollide")
                end
                if type(cc) == "boolean" then
                    local want = not cc
                    if want == entry.dropped then
                        entry.pending = 0
                    else
                        entry.pending = (entry.pending or 0) + 1
                        if entry.pending >= 2 then
                            entry.dropped = want
                            entry.pending = 0
                        end
                    end
                end

                local geo = palGeometry(entry.dropped and broken or intact)
                if geo then entry.g = geo end

                if entry.g then
                    entry.miss = 0
                    newIndex[key] = entry
                    list[#list + 1] = entry
                end
            end
        else
            local key = modelKey
            local prev = key and index[key]
            if prev and (prev.miss or 0) < 1 then
                prev.miss = (prev.miss or 0) + 1
                newIndex[key] = prev
                list[#list + 1] = prev
            end
        end
    end

    S.palIndex = newIndex
    return list
end

local function refreshPallets()
    if not CFG.pal.on then
        if CATS.pal.list[1] then CATS.pal.list = {} end
        return
    end
    local ok, list = pcall(collectPallets)
    if ok and list then CATS.pal.list = list end
end

-- ============================================================
-- bear traps
-- ============================================================
local TRAP_VICTIM_ATTRS = {
    "TrappedPlayer", "TrappedUser", "PlayerName", "Player", "Occupant", "User", "Caught",
}

local function trapMeasure(inst)
    local mnX, mnY, mnZ = huge, huge, huge
    local mxX, mxY, mxZ = -huge, -huge, -huge
    local rot, any = nil, false

    local function note(part)
        local p, s = prop(part, "Position"), prop(part, "Size")
        if not p or not s then return end
        local hx, hy, hz = s.X * 0.5, s.Y * 0.5, s.Z * 0.5
        if hx <= 0 or hy <= 0 or hz <= 0 or hx > 8 or hy > 8 or hz > 8 then return end
        if p.X - hx < mnX then mnX = p.X - hx end
        if p.X + hx > mxX then mxX = p.X + hx end
        if p.Y - hy < mnY then mnY = p.Y - hy end
        if p.Y + hy > mxY then mxY = p.Y + hy end
        if p.Z - hz < mnZ then mnZ = p.Z - hz end
        if p.Z + hz > mxZ then mxZ = p.Z + hz end
        any = true
        if not rot then rot = part end
    end

    if isPart(inst) then note(inst) end
    local d = descs(inst)
    if d then
        for _, part in ipairs(d) do
            if part ~= inst and isPart(part) then note(part) end
        end
    end
    if not any then return nil end

    local hx, hy, hz = (mxX - mnX) * 0.5, (mxY - mnY) * 0.5, (mxZ - mnZ) * 0.5
    if hx < 0.05 or hy < 0.02 or hz < 0.05 then return nil end
    local center = V3((mnX + mxX) * 0.5, (mnY + mxY) * 0.5, (mnZ + mxZ) * 0.5)
    return center, hx, hy, hz, prop(rot, "CFrame")
end

local function trapRoots(map)
    local out = {}
    local list = kids(map)
    if list then
        for _, ch in ipairs(list) do
            local n = slower(tostring(prop(ch, "Name")))
            if n == "beartrap" or n == "beartraps" then out[#out + 1] = ch end
        end
    end
    if #out == 0 then
        local ok, found = pcall(function() return map:FindFirstChild("BearTrap", true) end)
        if ok and found then out[1] = found end
    end
    return out
end

local function collectTraps()
    local map = Workspace:FindFirstChild("Map")
    if not map then S.trapIndex = {}; return {} end

    local out, nextIndex, now = {}, {}, clock()

    local function add(inst, armed)
        local id = address(inst)
        local entry = id and S.trapIndex[id] or nil
        if not entry then
            local center, hx, hy, hz, cf = trapMeasure(inst)
            if not center then return end
            entry = makeGeo(center, hx, hy, hz, cf)
            entry.g = entry
        end
        entry.id, entry.model = id, inst
        if entry.armed ~= armed then
            entry.armed = armed
            if armed == false then
                entry.sprungAt = now
                if not entry.probed then
                    entry.probed = true
                    for i = 1, #TRAP_VICTIM_ATTRS do
                        local v = attr(inst, TRAP_VICTIM_ATTRS[i])
                        if type(v) == "string" and v ~= "" then
                            entry.attrVictim = v
                            break
                        end
                    end
                end
            else
                entry.victim = nil
            end
        end
        if id then nextIndex[id] = entry end
        out[#out + 1] = entry
    end

    local function walk(inst, depth)
        if not inst or depth > 3 then return end
        local armed = attrBool(inst, "Armed")
        if armed ~= nil then
            add(inst, armed)
            return
        end
        local list = kids(inst)
        if not list then return end
        for _, k in ipairs(list) do walk(k, depth + 1) end
    end

    for _, r in ipairs(trapRoots(map)) do walk(r, 0) end
    S.trapIndex = nextIndex
    return out
end

local function trapScanTrapped(now)
    if now - S.trapVictimAt < 1.5 then return end
    S.trapVictimAt = now
    local out = {}
    local ok, plist = pcall(function() return Players:GetPlayers() end)
    if not ok or type(plist) ~= "table" then S.trapTrapped = out; return end
    local myId = prop(lp, "UserId")
    for _, plr in ipairs(plist) do
        local char = prop(plr, "Character")
        if char and attr(char, "Trapped") == true then
            local root = child(char, "HumanoidRootPart")
            local pos = root and prop(root, "Position")
            if pos then
                out[#out + 1] = {
                    name = tostring(prop(plr, "Name")), x = pos.X, y = pos.Y, z = pos.Z,
                    self = (myId ~= nil and prop(plr, "UserId") == myId),
                }
            end
        end
    end
    S.trapTrapped = out
end

local function trapVictim(t)
    if t.attrVictim then return t.attrVictim end
    local best, bestD2
    local list = S.trapTrapped
    for i = 1, #list do
        local v = list[i]
        local dx, dy, dz = v.x - t.x, v.y - t.y, v.z - t.z
        local d2 = dx * dx + dy * dy + dz * dz
        if d2 <= 225 and (not bestD2 or d2 < bestD2) then best, bestD2 = v, d2 end
    end
    if not best then return nil end
    return best.self and "you" or best.name
end

local function refreshTraps()
    local C = CATS.trap
    if not CFG.trap.on then
        if C.list[1] then C.list = {} end
        return
    end
    local now = clock()
    if now >= S.trapAt then
        local ok, list = pcall(collectTraps)
        if ok and list then C.list = list end
        S.trapAt = now + ((ok and list and #list > 0) and 1 or 5)
    end
    local list, anySprung = C.list, false
    for i = 1, #list do
        if list[i].armed == false then anySprung = true; break end
    end
    if anySprung then
        trapScanTrapped(now)
        for i = 1, #list do
            local t = list[i]
            if t.armed == false then t.victim = trapVictim(t) end
        end
    end
end

-- ============================================================
-- world refresh / background worker
-- ============================================================
local function refreshWorld()
    local now = clock()
    local map = Workspace:FindFirstChild("Map")
    local stamp = "none"
    if map then
        if now >= S.cntAt then
            S.cntAt = now + 5
            local k = kids(map)
            S.cnt = k and #k or 0
        end
        stamp = tostring(address(map) or "?") .. ":" .. S.cnt
    end

    if stamp ~= S.stamp then                          -- new map / new round: drop caches
        S.stamp = stamp
        S.genGeo, S.winGeo, S.palGeo, S.palParts = {}, {}, {}, {}
        S.genAt, S.winAt, S.winJob = 0, 0, nil
        CATS.win.list = {}
    end

    if CFG.gen.on then
        if now >= S.genAt then discoverGens(now) end
    else
        if CATS.gen.list[1] then CATS.gen.list = {} end
        S.genAt = 0
    end

    if CFG.win.on then
        if not S.winJob and now >= S.winAt then startWindowJob(now) end
    else
        S.winJob = nil
        S.winAt = 0
        if CATS.win.list[1] then CATS.win.list = {} end
    end
end

local function saveConfig() end   -- replaced below (needs the persist table)

local function slowTick()
    local cam = Workspace.CurrentCamera
    if cam then S.camera = cam end
    cam = S.camera
    if cam then
        local vp = prop(cam, "ViewportSize")
        if vp and vp.X > 0 and vp.Y > 0 then camVpW, camVpH = vp.X, vp.Y end
        local fov = prop(cam, "FieldOfView")
        if type(fov) == "number" and fov > 1 and fov < 170 then fovDeg = fov end
        pxK = camVpH / (2 * math.tan(math.rad(fovDeg) * 0.5))
    end
    S.perfLine = sfmt("Draw %.0f fps  |  %.2f ms/frame  |  worker %.1f ms",
        S.drawFps, S.renderMs, S.workMs)
    S.countLine = sfmt("Gens %d   Windows %d   Pallets %d   Traps %d",
        #CATS.gen.list, #CATS.win.list, #CATS.pal.list, #CATS.trap.list)
    if S.dirty then
        S.dirty = false
        saveConfig()
    end
end

local function worker()
    local nWorld, nGen, nPal, nTrap, nSlow = 0, 0, 0, 0, 0
    while S.running do
        local t0 = clock()
        if CFG.master then
            if t0 >= nWorld then nWorld = t0 + WORLD_DT; pcall(refreshWorld) end
            if S.winJob then
                local ok = pcall(winStep)
                if not ok then S.winJob = nil; S.winAt = clock() + 10 end
            end
            if t0 >= nGen then
                nGen = t0 + 0.1
                if CFG.gen.on then pcall(updateGenStates) end
            end
            if t0 >= nPal then nPal = t0 + 1 / PAL_HZ; pcall(refreshPallets) end
            if t0 >= nTrap then nTrap = t0 + 1; pcall(refreshTraps) end
        end
        if t0 >= nSlow then nSlow = t0 + 1; pcall(slowTick) end
        S.workMs = S.workMs * 0.9 + (clock() - t0) * 100
        wait(0.05)
    end
end

-- ============================================================
-- render loop
-- ============================================================
local function onFrame()
    if not S.running then return end
    local now = clock()
    local hz = CFG.drawHz
    if hz > 0 and now - S.lastFrame < 1 / hz then return end
    S.lastFrame = now
    S.frameN = S.frameN + 1
    if now - S.fpsMark >= 1 then
        S.drawFps = S.frameN / (now - S.fpsMark)
        S.frameN, S.fpsMark = 0, now
    end

    local cam = S.camera
    if not cam then return end
    local ccf = prop(cam, "CFrame")
    local p = ccf and prop(ccf, "Position")
    if not p then return end
    camX, camY, camZ = p.X, p.Y, p.Z

    local master = CFG.master
    for i = 1, #ORDER do
        local cat = ORDER[i]
        if master and cat.cfg.on then
            local ok, err = pcall(drawCat, cat, camX, camY, camZ)
            cat.err = (not ok) and tostring(err) or nil
        elseif cat.shown > 0 then
            for j = 1, cat.shown do
                local e = cat.pool[j]
                if e then hideSlot(e) end
            end
            cat.shown = 0
        end
    end
    S.renderMs = S.renderMs * 0.9 + (clock() - now) * 100
end

local function safeFrame()
    local ok, err = pcall(onFrame)
    if not ok then S.err = tostring(err) end
end

-- ============================================================
-- saved settings (swangy_esp.cfg)
-- ============================================================
local CFG_FILE = "swangy_esp.cfg"
local PERSIST = {
    { "master", CFG, "master" }, { "names", CFG, "names" }, { "drawHz", CFG, "drawHz" },
}
for _, cat in ipairs(ORDER) do
    PERSIST[#PERSIST + 1] = { cat.key .. ".on",    cat.cfg, "on" }
    PERSIST[#PERSIST + 1] = { cat.key .. ".range", cat.cfg, "range" }
    PERSIST[#PERSIST + 1] = { cat.key .. ".fill",  cat.cfg, "fill" }
end

saveConfig = function()
    if type(writefile) ~= "function" then return end
    local lines = {}
    for i = 1, #PERSIST do
        local p = PERSIST[i]
        lines[i] = p[1] .. "=" .. tostring(p[2][p[3]])
    end
    pcall(writefile, CFG_FILE, table.concat(lines, "\n"))
end

local function loadConfig()
    if type(readfile) ~= "function" or type(isfile) ~= "function" then return end
    local okf, exists = pcall(isfile, CFG_FILE)
    if not okf or not exists then return end
    local ok, text = pcall(readfile, CFG_FILE)
    if not ok or type(text) ~= "string" then return end
    local byName = {}
    for i = 1, #PERSIST do byName[PERSIST[i][1]] = PERSIST[i] end
    for line in text:gmatch("[^\r\n]+") do
        local k, v = line:match("^([%w_%.]+)=(.*)$")
        local p = k and byName[k]
        if p then
            local cur = p[2][p[3]]
            if type(cur) == "boolean" then
                p[2][p[3]] = (v == "true")
            elseif type(cur) == "number" then
                local n = tonumber(v)
                if n then p[2][p[3]] = n end
            end
        end
    end
end

-- ============================================================
-- public API  (_G.__SWANGY)
-- ============================================================
local function setOn(cat, on)
    cat.cfg.on = on and true or false
    if cat.cfg.on then
        if cat.key == "gen" then S.genAt = 0 end
        if cat.key == "win" then S.winAt = 0 end
        if cat.key == "trap" then S.trapAt = 0 end
    end
    S.dirty = true
    return cat.cfg.on
end

API.version = VERSION
API.cfg = CFG

for _, cat in ipairs(ORDER) do
    local c, api = cat.cfg, {}
    function api.SetEnabled(on) return setOn(cat, on) end
    function api.Toggle() return setOn(cat, not c.on) end
    function api.SetRange(v) c.range = max(1, tonumber(v) or c.range); S.dirty = true end
    function api.GetCount() return #cat.list end
    API[cat.key] = api
end

function API.pal.GetStates()
    local out, list = {}, CATS.pal.list
    for i = 1, #list do out[i] = { dropped = list[i].dropped, pos = list[i].g and list[i].g.pos } end
    return out
end

function API.trap.GetStates()
    local out, list = {}, CATS.trap.list
    for i = 1, #list do
        local t = list[i]
        out[i] = { armed = t.armed, victim = t.armed == false and (t.victim or trapVictim(t)) or nil, pos = t.pos }
    end
    return out
end

function API.SetNames(on) CFG.names = on and true or false; S.dirty = true; return CFG.names end

function API.SetFill(gen, win, pal, trap)
    if gen  ~= nil then CFG.gen.fill  = gen  and true or false end
    if win  ~= nil then CFG.win.fill  = win  and true or false end
    if pal  ~= nil then CFG.pal.fill  = pal  and true or false end
    if trap ~= nil then CFG.trap.fill = trap and true or false end
    S.dirty = true
    return CFG.gen.fill, CFG.win.fill, CFG.pal.fill, CFG.trap.fill
end

function API.SetRange(v)
    v = max(1, tonumber(v) or CFG.gen.range)
    for _, cat in ipairs(ORDER) do cat.cfg.range = v end
    S.dirty = true
    return v
end

function API.SetDrawHz(hz)
    CFG.drawHz = max(0, tonumber(hz) or 0)
    S.dirty = true
    return CFG.drawHz
end

function API.GetConfig()
    return {
        gen = CFG.gen.on, win = CFG.win.on, pal = CFG.pal.on, trap = CFG.trap.on, names = CFG.names,
        genRange = CFG.gen.range, winRange = CFG.win.range,
        palRange = CFG.pal.range, trapRange = CFG.trap.range,
    }
end

function API.Perf()
    return {
        drawHz = CFG.drawHz, drawFps = S.drawFps, renderMs = S.renderMs, workerMs = S.workMs,
        gen = #CATS.gen.list, win = #CATS.win.list, pal = #CATS.pal.list, trap = #CATS.trap.list,
        err = S.err or CATS.gen.err or CATS.win.err or CATS.pal.err or CATS.trap.err,
    }
end

function API.unload()
    if not S.running then return end
    S.running = false
    if connection then pcall(function() connection:Disconnect() end); connection = nil end
    if S.dirty then saveConfig() end
    for _, cat in ipairs(ORDER) do
        for i = 1, #cat.pool do removeSlot(cat.pool[i]) end
        cat.pool, cat.list, cat.shown = {}, {}, 0
    end
    if G.__SWANGY == API then G.__SWANGY = nil end
end
API.stop = API.unload

-- ============================================================
-- Matcha menu
-- ============================================================
local function menuToggle(sec, id, label, tbl, key)
    sec:Toggle(id, label, tbl[key], function(v)
        tbl[key] = v and true or false
        S.dirty = true
    end)
end

function API.menu(tab)
    local main = tab:Section("ESP", "Left")
    menuToggle(main, "swangy_master", "ESP Enabled", CFG, "master")
    for _, cat in ipairs(ORDER) do
        main:Toggle("swangy_" .. cat.key, cat.name .. " ESP", cat.cfg.on, function(v) setOn(cat, v) end)
    end
    menuToggle(main, "swangy_names", "Names / Labels", CFG, "names")
    main:Button("Unload ESP", function() API.unload() end)

    local disp = tab:Section("Display", "Right")
    for _, cat in ipairs(ORDER) do
        menuToggle(disp, "swangy_" .. cat.key .. "_fill", cat.name .. " Fill", cat.cfg, "fill")
    end

    local rng = tab:Section("Ranges", "Right")
    for _, cat in ipairs(ORDER) do
        rng:SliderInt("swangy_" .. cat.key .. "_range", cat.name .. " Range", 50, 1000, cat.cfg.range, function(v)
            cat.cfg.range = v
            S.dirty = true
        end)
    end

    local perf = tab:Section("Performance", "Left")
    perf:SliderInt("swangy_fps", "Max Draw FPS (0 = uncapped)", 0, 240, CFG.drawHz, function(v)
        CFG.drawHz = v
        S.dirty = true
    end)
    perf:Text(S.perfLine ~= "" and S.perfLine or "...")
    perf:Text(S.countLine ~= "" and S.countLine or "...")

    -- make the widgets match the loaded settings once (in case Matcha keeps its own values)
    S.menuFrames = S.menuFrames + 1
    if S.menuFrames == 3 and UI and type(UI.SetValue) == "function" then
        pcall(UI.SetValue, "swangy_master", CFG.master)
        pcall(UI.SetValue, "swangy_names", CFG.names)
        pcall(UI.SetValue, "swangy_fps", CFG.drawHz)
        for _, cat in ipairs(ORDER) do
            pcall(UI.SetValue, "swangy_" .. cat.key, cat.cfg.on)
            pcall(UI.SetValue, "swangy_" .. cat.key .. "_fill", cat.cfg.fill)
            pcall(UI.SetValue, "swangy_" .. cat.key .. "_range", cat.cfg.range)
        end
    end
end

-- one permanent tab; it always renders whichever copy of the script is currently loaded
if UI and type(UI.AddTab) == "function" and not G.__SWANGY_TAB then
    G.__SWANGY_TAB = true
    UI.AddTab("Swangy ESP", function(tab)
        local A = G.__SWANGY
        if A and A.menu then
            A.menu(tab)
        else
            tab:Section("Swangy ESP", "Left"):Text("ESP is unloaded - run the script again")
        end
    end)
end

-- ============================================================
-- boot
-- ============================================================
G.__SWANGY = API
loadConfig()

S.camera = Workspace.CurrentCamera
pcall(slowTick)
pcall(refreshWorld)
pcall(refreshPallets)
pcall(refreshTraps)

local okc, conn = pcall(function() return RunService.RenderStepped:Connect(safeFrame) end)
if okc and conn then
    connection = conn
else
    spawn(function()                       -- fallback if RenderStepped isn't available
        while S.running do
            safeFrame()
            wait(0.016)
        end
    end)
end

spawn(worker)

if type(notify) == "function" then
    notify("generator / window / pallet / bear trap esp", "Swangy ESP", 4)
end

return API
