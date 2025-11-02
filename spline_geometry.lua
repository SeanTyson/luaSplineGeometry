local samplesPerSegment = 24

local spline_geom = {}
spline_geom.samplesPerSegment = 24

 function spline_geom.copyPoints(points)
	local result = {}
	for i, p in ipairs(points) do
		result[i] = { p[1], p[2] }
	end
	return result
end


local function pointInTriangle(px, py, x1, y1, x2, y2, x3, y3)
	local d1 = (px - x2)*(y1 - y2) - (py - y2)*(x1 - x2)
	local d2 = (px - x3)*(y2 - y3) - (py - y3)*(x2 - x3)
	local d3 = (px - x1)*(y3 - y1) - (py - y1)*(x3 - x1)
	local has_neg = (d1 < 0) or (d2 < 0) or (d3 < 0)
	local has_pos = (d1 > 0) or (d2 > 0) or (d3 > 0)
	return not (has_neg and has_pos)
end

local function pointInTriangles(px, py, tris)
	for _, tri in ipairs(tris) do
		-- each tri = {x1, y1, x2, y2, x3, y3}
		if pointInTriangle(px, py, tri[1], tri[2], tri[3], tri[4], tri[5], tri[6]) then
			return true
		end
	end
	return false
end

local function linesIntersect(x1,y1,x2,y2, x3,y3,x4,y4)
	local denom = (y4 - y3)*(x2 - x1) - (x4 - x3)*(y2 - y1)
	if denom == 0 then return false end -- parallel lines
	local ua = ((x4 - x3)*(y1 - y3) - (y4 - y3)*(x1 - x3)) / denom
	local ub = ((x2 - x1)*(y1 - y3) - (y2 - y1)*(x1 - x3)) / denom
	return ua >= 0 and ua <= 1 and ub >= 0 and ub <= 1
end

local function triangleEdges(tri)
	return {
		{tri[1], tri[2], tri[3], tri[4]},
		{tri[3], tri[4], tri[5], tri[6]},
		{tri[5], tri[6], tri[1], tri[2]},
	}
end

local function trianglesIntersect(triA, triB)
	-- Vertex tests
	if pointInTriangle(triA[1], triA[2], triB[1],triB[2],triB[3],triB[4],triB[5],triB[6]) then return true end
	if pointInTriangle(triA[3], triA[4], triB[1],triB[2],triB[3],triB[4],triB[5],triB[6]) then return true end
	if pointInTriangle(triA[5], triA[6], triB[1],triB[2],triB[3],triB[4],triB[5],triB[6]) then return true end

	if pointInTriangle(triB[1], triB[2], triA[1],triA[2],triA[3],triA[4],triA[5],triA[6]) then return true end
	if pointInTriangle(triB[3], triB[4], triA[1],triA[2],triA[3],triA[4],triA[5],triA[6]) then return true end
	if pointInTriangle(triB[5], triB[6], triA[1],triA[2],triA[3],triA[4],triA[5],triA[6]) then return true end

	-- Edge intersection tests
	local edgesA = triangleEdges(triA)
	local edgesB = triangleEdges(triB)
	for _, ea in ipairs(edgesA) do
		for _, eb in ipairs(edgesB) do
			if linesIntersect(ea[1],ea[2],ea[3],ea[4], eb[1],eb[2],eb[3],eb[4]) then
				return true
			end
		end
	end
	return false
end

local function inside(px, py, x1, y1, x2, y2)
	-- returns true if point (px,py) is inside the half-plane defined by edge (x1,y1)-(x2,y2)
	return (x2 - x1)*(py - y1) > (y2 - y1)*(px - x1)
end

local function computeIntersection(x1,y1,x2,y2, x3,y3,x4,y4)
	local dx1, dy1 = x2 - x1, y2 - y1
	local dx2, dy2 = x4 - x3, y4 - y3
	local denom = dx1 * dy2 - dy1 * dx2
	if denom == 0 then return nil end
	local ua = ((x3 - x1) * dy2 - (y3 - y1) * dx2) / denom
	return x1 + ua * dx1, y1 + ua * dy1
end

local function polygonClip(subjectPolygon, clipPolygon)
	local outputList = subjectPolygon
	local cx1, cy1 = clipPolygon[#clipPolygon][1], clipPolygon[#clipPolygon][2]

	for i = 1, #clipPolygon do
		local cx2, cy2 = clipPolygon[i][1], clipPolygon[i][2]
		local inputList = outputList
		outputList = {}
		if #inputList == 0 then break end
		local sx, sy = inputList[#inputList][1], inputList[#inputList][2]

		for j = 1, #inputList do
			local ex, ey = inputList[j][1], inputList[j][2]
			if inside(ex, ey, cx1, cy1, cx2, cy2) then
				if not inside(sx, sy, cx1, cy1, cx2, cy2) then
					local ix, iy = computeIntersection(sx, sy, ex, ey, cx1, cy1, cx2, cy2)
					if ix then table.insert(outputList, {ix, iy}) end
				end
				table.insert(outputList, {ex, ey})
			elseif inside(sx, sy, cx1, cy1, cx2, cy2) then
				local ix, iy = computeIntersection(sx, sy, ex, ey, cx1, cy1, cx2, cy2)
				if ix then table.insert(outputList, {ix, iy}) end
			end
			sx, sy = ex, ey
		end
		cx1, cy1 = cx2, cy2
	end
	return outputList
end

---------------------------------------------------------------
-- Catmull–Rom interpolation
---------------------------------------------------------------
-- ✳ Generates a smooth curve that passes through p1 and p2.
-- ✳ This uses a cubic Hermite polynomial interpolation with 4 points.
-- ✳ t ∈ [0, 1] defines the fraction along the segment between p1 and p2.
local function catmullRom(p0, p1, p2, p3, t)
	local t2, t3 = t * t, t * t * t -- ✳ Precompute powers for efficiency
	-- ✳ The formula below is derived from the Catmull–Rom spline equation:
	-- ✳ P(t) = 0.5 * ((2P1) + (-P0 + P2)t + (2P0 - 5P1 + 4P2 - P3)t² + (-P0 + 3P1 - 3P2 + P3)t³)
	-- ✳ Each coordinate is computed independently.
	local x = 0.5 * ((2 * p1[1])
	+ (-p0[1] + p2[1]) * t
	+ (2*p0[1] - 5*p1[1] + 4*p2[1] - p3[1]) * t2
	+ (-p0[1] + 3*p1[1] - 3*p2[1] + p3[1]) * t3)
	local y = 0.5 * ((2 * p1[2])
	+ (-p0[2] + p2[2]) * t
	+ (2*p0[2] - 5*p1[2] + 4*p2[2] - p3[2]) * t2
	+ (-p0[2] + 3*p1[2] - 3*p2[2] + p3[2]) * t3)
	return { x, y }
end

---------------------------------------------------------------
-- Generate spline points for a given control point list
---------------------------------------------------------------
-- ✳ Converts discrete control points into many interpolated vertices.
-- ✳ Uses modular indexing so the spline loops seamlessly.
function spline_geom:generateSpline(points)
	local spline = {}
	local n = #points
	if n < 3 then return spline end -- ✳ Need at least 3 points to define a curve

	for i = 1, n do
		-- ✳ Wrap indices (mod n) to form a closed loop.
		local p0 = points[((i-2)%n)+1]
		local p1 = points[i]
		local p2 = points[(i%n)+1]
		local p3 = points[((i+1)%n)+1]
		-- ✳ Sample the curve between p1 and p2 in samplesPerSegment increments.
		for s = 0, self.samplesPerSegment-1 do
			table.insert(spline, catmullRom(p0,p1,p2,p3,s/self.samplesPerSegment))
		end
	end
	return spline
end

---------------------------------------------------------------
-- Compute the triangulated area for any given control points
---------------------------------------------------------------
-- ✳ Generates the filled polygon of the spline and computes its area.
-- ✳ Uses triangulation + the shoelace/determinant formula.
local function polygonArea(points)
	local n = #points
	if n < 3 then return 0 end
	local a = 0
	for i = 1, n do
		local x1, y1 = points[i][1], points[i][2]
		local x2, y2 = points[(i % n) + 1][1], points[(i % n) + 1][2]
		a = a + (x1 * y2 - x2 * y1)
	end
	return math.abs(a) / 2
end

function spline_geom.triangulatePolygon(polygon)
	polygon = spline_geom.ensureCounterClockwise(polygon)
	-- polygon: { {x1,y1}, {x2,y2}, ... }
	local n = #polygon
	if n < 3 then return {} end
	if n == 3 then
		return { { polygon[1][1], polygon[1][2],
		polygon[2][1], polygon[2][2],
		polygon[3][1], polygon[3][2] } }
	end

	-- Copy vertices and initialize next/prev indices
	local vertices = {}
	for i, p in ipairs(polygon) do
		vertices[i] = {x = p[1], y = p[2], i = i}
	end

	local function isCCW(a,b,c) -- counter clockwise
		return ((b.x - a.x)*(c.y - a.y) - (b.y - a.y)*(c.x - a.x)) >= 0
	end

	local function isEar(a,b,c, others)
		if not isCCW(a,b,c) then return false end
		for _, p in ipairs(others) do
			if p ~= a and p ~= b and p ~= c then
				if pointInTriangle(p.x,p.y, a.x,a.y, b.x,b.y, c.x,c.y) then
					return false
				end
			end
		end
		return true
	end

	local result = {}
	local V = {}
	for i = 1, #vertices do
		V[i] = vertices[i]
	end

	while #V > 3 do
		local earFound = false
		for i=1,#V do
			local prev = V[(i-2)%#V+1]
			local curr = V[i]
			local next = V[i%#V+1]

			if isEar(prev,curr,next,V) then
				table.insert(result, {prev.x,prev.y, curr.x,curr.y, next.x,next.y})
				table.remove(V,i)
				earFound = true
				break
			end
		end
		if not earFound then
			error("Cannot triangulate polygon: possible self-intersection or degenerate polygon")
		end
	end

	-- Last remaining triangle
	table.insert(result, {V[1].x,V[1].y, V[2].x,V[2].y, V[3].x,V[3].y})

	return result
end

function spline_geom.ensureCounterClockwise(polygon)
	-- Calculate signed area to determine winding
	local area = 0
	local n = #polygon
	for i = 1, n do
		local j = i % n + 1
		area = area + (polygon[j][1] - polygon[i][1]) * (polygon[j][2] + polygon[i][2])
	end

	-- If area is positive, it's clockwise, so reverse
	if area > 0 then
		local reversed = {}
		for i = n, 1, -1 do
			table.insert(reversed, polygon[i])
		end
		return reversed
	end
	return polygon
end


return spline_geom